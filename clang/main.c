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

#include "prelude/_.c"

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

  if (opts.do_collapse) {
    // Lazy collapse + flatten: handles infinite structures
    collapse_flatten(main_ref, opts.collapse_limit, opts.stats);
  } else {
    // Standard evaluation to strong normal form
    Term result = snf(main_ref, 0, 0);
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
