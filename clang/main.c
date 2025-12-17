// HVM4 CLI Entry Point
// ====================
//
// This file provides the command-line interface for the HVM4 runtime,
// mirroring the structure of main.hs for the Haskell implementation.
//
// Usage: ./main <file.hvm4> [-s] [-C[N]]
//   -s:  Show statistics (interactions, time, performance)
//   -C:  Collapse and flatten (enumerate all superposition branches)
//   -CN: Collapse and flatten, limit to N results

#include "hvm4.c"

// Flatten
// =======
//
// Lazy collapse + extraction via priority queue traversal.
// INC nodes decrease priority (explored earlier), SUP nodes increase priority.
// Integrates collapse_step to handle infinite structures without stack overflow.

fn void flatten(Term term, int limit, int show_itrs) {
  // Priority queue for collapse ordering
  PQueue pq;
  pqueue_init(&pq);

  // Anchor the root term at a heap location
  u32 root_loc = heap_alloc(1);
  HEAP[root_loc] = term;
  pqueue_push(&pq, (PQItem){.pri = 0, .loc = root_loc});

  int count = 0;
  PQItem it;

  while (pqueue_pop(&pq, &it) && (limit < 0 || count < limit)) {
    u32 loc = it.loc;
    u8  pri = it.pri;

    // Lazy collapse: lift SUPs one step at a time
    Term t = collapse_step(HEAP[loc]);
    HEAP[loc] = t;

    // INC fast-path: peel chain of INC wrappers, decrementing priority
    while (term_tag(t) == INC) {
      u32 inc_loc = term_val(t);
      loc = inc_loc;
      t = collapse_step(HEAP[loc]);
      HEAP[loc] = t;
      if (pri > 0) pri--;  // decrement priority, clamped at 0
    }

    if (term_tag(t) == SUP) {
      // SUP at top - enqueue both branches with pri+1
      u32 sup_loc = term_val(t);
      pqueue_push(&pq, (PQItem){.pri = (u8)(pri + 1), .loc = sup_loc + 0});
      pqueue_push(&pq, (PQItem){.pri = (u8)(pri + 1), .loc = sup_loc + 1});
    } else if (term_tag(t) != ERA) {
      // Non-SUP, non-ERA result - normalize and print
      t = snf(t, 0, 1);  // quote=1: use quoted lambdas for collapser
      print_term(t);
      if (show_itrs) {
        printf(" \033[2m#%llu\033[0m", ITRS);
      }
      printf("\n");
      count++;
    }
  }

  pqueue_free(&pq);
}

// CLI
// ===

typedef struct {
  int   stats;
  int   do_collapse;
  int   collapse_limit;  // -1 means no limit
  int   debug;
  int   step_by_step;    // -D: step-by-step reduction mode
  char *file;
} CliOpts;

fn CliOpts parse_opts(int argc, char **argv) {
  CliOpts opts = { .stats = 0, .do_collapse = 0, .collapse_limit = -1, .debug = 0, .step_by_step = 0, .file = NULL };

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-s") == 0) {
      opts.stats = 1;
    } else if (strncmp(argv[i], "-C", 2) == 0) {
      opts.do_collapse = 1;
      if (argv[i][2] != '\0') {
        opts.collapse_limit = atoi(&argv[i][2]);
      }
    } else if (strcmp(argv[i], "-d") == 0) {
      opts.debug = 1;
    } else if (strcmp(argv[i], "-D") == 0) {
      opts.step_by_step = 1;
    } else if (argv[i][0] != '-') {
      if (opts.file == NULL) {
        opts.file = argv[i];
      } else {
        fprintf(stderr, "Error: multiple input files specified\n");
        exit(1);
      }
    } else {
      fprintf(stderr, "Unknown option: %s\n", argv[i]);
      exit(1);
    }
  }

  return opts;
}

// Prelude
// =======

#include "prelude/_.c"

// Main
// ====

int main(int argc, char **argv) {
  // Parse command line
  CliOpts opts = parse_opts(argc, argv);

  if (opts.file == NULL) {
    fprintf(stderr, "Usage: ./main <file.hvm4> [-s] [-C[N]] [-D]\n");
    return 1;
  }

  // Allocate memory
  BOOK  = calloc(BOOK_CAP, sizeof(u32));
  HEAP  = calloc(HEAP_CAP, sizeof(Term));
  STACK = calloc(WNF_CAP, sizeof(Term));
  TABLE = calloc(BOOK_CAP, sizeof(char*));

  if (!BOOK || !HEAP || !STACK || !TABLE) {
    sys_error("Memory allocation failed");
  }

  // Set debug mode
  DEBUG = opts.debug;

  // Parse prelude
  PState ps = {
    .file = "<prelude>",
    .src  = (char*)PRELUDE,
    .pos  = 0,
    .len  = strlen(PRELUDE),
    .line = 1,
    .col  = 1
  };
  parse_def(&ps);

  // Read and parse user file
  char *src = sys_file_read(opts.file);
  if (!src) {
    fprintf(stderr, "Error: could not open '%s'\n", opts.file);
    return 1;
  }

  // Add file to seen list
  char *abs_path = realpath(opts.file, NULL);
  if (abs_path) {
    PARSE_SEEN_FILES[PARSE_SEEN_FILES_LEN++] = abs_path;
  }

  PState s = {
    .file = abs_path ? abs_path : opts.file,
    .src  = src,
    .pos  = 0,
    .len  = strlen(src),
    .line = 1,
    .col  = 1
  };
  parse_def(&s);
  free(src);

  // Get @main id
  u32 main_id = table_find("main", 4);

  // Check @main exists
  if (BOOK[main_id] == 0) {
    fprintf(stderr, "Error: @main not defined\n");
    return 1;
  }

  // Evaluate
  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);

  Term main_ref = term_new_ref(main_id);

  // Set step-by-step mode
  STEP_BY_STEP = opts.step_by_step;

  if (opts.do_collapse) {
    // Lazy collapse + flatten: handles infinite structures
    flatten(main_ref, opts.collapse_limit, opts.stats);
  } else if (opts.step_by_step) {
    // Step-by-step reduction: show each interaction
    ROOT_LOC = heap_alloc(1);
    HEAP[ROOT_LOC] = main_ref;

    // Buffer for measuring line length
    char *line_buf = NULL;
    size_t line_cap = 0;

    // Helper: print term to buffer, output it, then print dashes
    #define PRINT_STEP(t) do { \
      FILE *mem = open_memstream(&line_buf, &line_cap); \
      print_term_to(mem, t); \
      fclose(mem); \
      /* Count visible width (UTF-8 aware) */ \
      u32 width = 0; \
      for (char *p = line_buf; *p; ) { \
        u8 c = (u8)*p; \
        if ((c & 0xC0) != 0x80) width++; /* count non-continuation bytes */ \
        p++; \
      } \
      printf("%s\n", line_buf); \
      for (u32 i = 0; i < width; i++) putchar('-'); \
      putchar('\n'); \
    } while(0)

    // Print initial state
    PRINT_STEP(HEAP[ROOT_LOC]);

    // Step-by-step loop: each iteration does one interaction
    while (1) {
      u64 old_itrs = ITRS;
      ITRS_LIMIT = ITRS + 1;
      Term result = snf(HEAP[ROOT_LOC], 0, 0);
      HEAP[ROOT_LOC] = result;
      ITRS_LIMIT = 0;

      if (ITRS == old_itrs) break;  // no interaction, done

      // Print after this interaction
      PRINT_STEP(HEAP[ROOT_LOC]);
    }

    // Print final result (no dashes after)
    print_term(HEAP[ROOT_LOC]);
    printf("\n");

    free(line_buf);
    #undef PRINT_STEP
  } else {
    // Standard evaluation to strong normal form
    Term result = snf(main_ref, 0, 0);  // quote=0: normal lambdas for printer
    print_term(result);
    printf("\n");
  }

  clock_gettime(CLOCK_MONOTONIC, &end);

  // Print stats if requested
  if (opts.stats) {
    double dt  = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double ips = ITRS / dt;
    printf("- Itrs: %llu interactions\n", ITRS);
    printf("- Time: %.3f seconds\n", dt);
    printf("- Perf: %.2f M interactions/s\n", ips / 1e6);
  }

  // Cleanup
  free(HEAP);
  free(BOOK);
  free(STACK);
  free(TABLE);

  return 0;
}
