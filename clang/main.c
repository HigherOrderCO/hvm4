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
// Extracts all non-SUP leaves from a term via BFS traversal.

fn void flatten(Term term, int limit) {
  // Simple BFS queue
  Term *queue = malloc(sizeof(Term) * 1024 * 1024);
  int   head  = 0;
  int   tail  = 0;
  int   count = 0;

  queue[tail++] = term;

  while (head < tail && (limit < 0 || count < limit)) {
    Term t = queue[head++];

    if (term_tag(t) == SUP) {
      u32 loc = term_val(t);
      queue[tail++] = HEAP[loc + 0];
      queue[tail++] = HEAP[loc + 1];
    } else {
      if (term_tag(t) != ERA) {
        print_term(t);
        printf("\n");
        count++;
      }
    }
  }

  free(queue);
}

// CLI
// ===

typedef struct {
  int   stats;
  int   do_collapse;
  int   collapse_limit;  // -1 means no limit
  int   debug;
  char *file;
} CliOpts;

fn CliOpts parse_opts(int argc, char **argv) {
  CliOpts opts = { .stats = 0, .do_collapse = 0, .collapse_limit = -1, .debug = 0, .file = NULL };

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

static const char *PRELUDE =
  "@add = λ{λx.λ{λy.@@add(x,y)}}\n"
  "@sub = λ{λx.λ{λy.@@sub(x,y)}}\n"
  "@mul = λ{λx.λ{λy.@@mul(x,y)}}\n"
  "@div = λ{λx.λ{λy.@@div(x,y)}}\n"
  "@mod = λ{λx.λ{λy.@@mod(x,y)}}\n"
  "@and = λ{λx.λ{λy.@@and(x,y)}}\n"
  "@or  = λ{λx.λ{λy.@@or(x,y)}}\n"
  "@xor = λ{λx.λ{λy.@@xor(x,y)}}\n"
  "@lsh = λ{λx.λ{λy.@@lsh(x,y)}}\n"
  "@rsh = λ{λx.λ{λy.@@rsh(x,y)}}\n"
  "@not = λ{λx.@@not(x)}\n"
  "@eq  = λ{λx.λ{λy.@@eq(x,y)}}\n"
  "@ne  = λ{λx.λ{λy.@@ne(x,y)}}\n"
  "@lt  = λ{λx.λ{λy.@@lt(x,y)}}\n"
  "@le  = λ{λx.λ{λy.@@le(x,y)}}\n"
  "@gt  = λ{λx.λ{λy.@@gt(x,y)}}\n"
  "@ge  = λ{λx.λ{λy.@@ge(x,y)}}\n"
  "@dup = λ{λl.λ{λv.λ{λf.@@dup(l,v,f)}}}\n"
  "@sup = λ{λl.λ{λa.λ{λb.@@sup(l,a,b)}}}\n"
  "@sp0 = λ{λx.@@and(@@add(@@mul(x,16293),1),65535)}"
  "@sp1 = λ{λx.@@and(@@add(@@mul(x,32677),3),65535)}"
;

// Main
// ====

int main(int argc, char **argv) {
  // Parse command line
  CliOpts opts = parse_opts(argc, argv);

  if (opts.file == NULL) {
    fprintf(stderr, "Usage: ./main <file.hvm4> [-s] [-C[N]]\n");
    return 1;
  }

  // Allocate memory
  BOOK  = calloc(BOOK_CAP, sizeof(u32));
  HEAP  = calloc(HEAP_CAP, sizeof(Term));
  STACK = calloc(WNF_CAP, sizeof(Term));

  if (!BOOK || !HEAP || !STACK) {
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

  // Get @main name hash
  u32 main_name = 0;
  const char *p = "main";
  while (*p) {
    main_name = ((main_name << 6) + nick_letter_to_b64(*p)) & EXT_MASK;
    p++;
  }

  // Check @main exists
  if (BOOK[main_name] == 0) {
    fprintf(stderr, "Error: @main not defined\n");
    return 1;
  }

  // Evaluate
  struct timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);

  Term main_ref = term_new_ref(main_name);
  Term result;
  if (opts.do_collapse) {
    result = snf(collapse(main_ref), 0);
  } else {
    result = snf(main_ref, 0);
  }

  clock_gettime(CLOCK_MONOTONIC, &end);

  // Print result
  if (opts.do_collapse) {
    flatten(result, opts.collapse_limit);
  } else {
    print_term(result);
    printf("\n");
  }

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

  return 0;
}
