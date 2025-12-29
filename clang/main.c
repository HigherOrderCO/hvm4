// HVM4 CLI Entry Point
// ====================
//
// This file provides the command-line interface for the HVM4 runtime,
// mirroring the structure of main.hs for the Haskell implementation.
//
// Usage: ./main <file.hvm4> [-s] [-S] [-D] [-C[N]] [-T<N>]
//   -s:  Show statistics (interactions, time, performance)
//   -S:  Silent output (omit term printing)
//   -D:  Step-by-step reduction (print intermediate terms)
//   -C:  Collapse and flatten (enumerate all superposition branches)
//   -CN: Collapse and flatten, limit to N results
//   -T:  Use N threads (e.g. -T4)

#include "hvm4.c"

// CLI
// ===

typedef struct {
  int   stats;
  int   silent;
  int   do_collapse;
  int   collapse_limit;  // -1 means no limit
  int   debug;
  int   step_by_step;
  int   threads;
  char *file;
} CliOpts;

fn CliOpts parse_opts(int argc, char **argv) {
  CliOpts opts = {
    .stats = 0,
    .silent = 0,
    .do_collapse = 0,
    .collapse_limit = -1,
    .debug = 0,
    .step_by_step = 0,
    .threads = 0,
    .file = NULL
  };

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-s") == 0) {
      opts.stats = 1;
    } else if (strcmp(argv[i], "-S") == 0) {
      opts.silent = 1;
    } else if (strncmp(argv[i], "-C", 2) == 0) {
      opts.do_collapse = 1;
      if (argv[i][2] != '\0') {
        opts.collapse_limit = atoi(&argv[i][2]);
      }
    } else if (strncmp(argv[i], "-T", 2) == 0) {
      const char *num = argv[i] + 2;
      if (num[0] == '\0') {
        if (i + 1 >= argc) {
          fprintf(stderr, "Error: missing thread count after -T\n");
          exit(1);
        }
        num = argv[++i];
      }
      opts.threads = atoi(num);
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
    fprintf(stderr, "Usage: ./main <file.hvm4> [-s] [-S] [-D] [-C[N]] [-T<N>]\n");
    return 1;
  }

  if (opts.step_by_step && opts.do_collapse) {
    fprintf(stderr, "Error: -D is not supported with -C\n");
    return 1;
  }

  // Configure threads (default: 1)
  u32 threads = opts.threads > 0 ? (u32)opts.threads : 1;
  if (opts.step_by_step && threads > 1) {
    fprintf(stderr, "Warning: -D forces single-threaded mode\n");
    threads = 1;
  }
  thread_set_count(threads);
  wnf_set_tid(0);

  // Allocate memory
  BOOK  = calloc(BOOK_CAP, sizeof(u32));
  HEAP  = calloc(HEAP_CAP, sizeof(Term));
  TABLE = calloc(BOOK_CAP, sizeof(char*));

  if (!BOOK || !HEAP || !TABLE) {
    sys_error("Memory allocation failed");
  }
  heap_init_slices();

  // Set debug mode
  DEBUG = opts.debug;
  SILENT = opts.silent;
  STEPS_ENABLE = opts.step_by_step;

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
    eval_collapse(main_ref, opts.collapse_limit, opts.stats, opts.silent);
  } else {
    // Standard evaluation to strong normal form
    Term result = eval_normalize(main_ref);
    if (!opts.silent && !opts.step_by_step) {
      print_term(result);
      printf("\n");
    }
  }

  clock_gettime(CLOCK_MONOTONIC, &end);

  wnf_itrs_flush(0);

  // Print stats if requested
  u64 total_itrs = wnf_itrs_total();
  if (opts.stats) {
    double dt  = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double ips = total_itrs / dt;
    printf("- Itrs: %llu interactions\n", total_itrs);
    if (thread_get_count() > 1) {
      for (u32 t = 0; t < thread_get_count(); t++) {
        printf("- Itrs[%u]: %llu interactions\n", t, wnf_itrs_thread(t));
      }
    }
    printf("- Time: %.3f seconds\n", dt);
    printf("- Perf: %.2f M interactions/s\n", ips / 1e6);
  } else if (opts.silent) {
    printf("- Itrs: %llu interactions\n", total_itrs);
  }

  // Cleanup
  free(HEAP);
  free(BOOK);
  free(TABLE);
  wnf_stack_free_all();

  return 0;
}
