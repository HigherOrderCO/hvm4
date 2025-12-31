fn void parse_def(PState *s);

fn void parse_include(PState *s) {
  // Parse filename
  parse_skip(s);
  parse_consume(s, "\"");
  u32 start = s->pos;
  while (parse_peek(s) != '"' && !parse_at_end(s)) {
    parse_advance(s);
  }
  u32 len = s->pos - start;
  parse_consume(s, "\"");

  // Resolve path
  char filename[256], path[1024];
  memcpy(filename, s->src + start, len);
  filename[len] = 0;
  sys_path_join(path, sizeof(path), s->file, filename);

  // Check if already included
  for (u32 i = 0; i < PARSE_SEEN_FILES_LEN; i++) {
    if (strcmp(PARSE_SEEN_FILES[i], path) == 0) {
      return;
    }
  }
  if (PARSE_SEEN_FILES_LEN >= 1024) {
    sys_error("MAX_INCLUDES");
  }
  char *path_copy = strdup(path);
  if (!path_copy) {
    sys_error("out of memory in parse_include");
  }
  PARSE_SEEN_FILES[PARSE_SEEN_FILES_LEN++] = path_copy;

  // Read and parse
  char *src = sys_file_read(path);
  if (!src) {
    fprintf(stderr, "Error: could not open '%s'\n", path);
    exit(1);
  }
  PState sub = {
    .file = PARSE_SEEN_FILES[PARSE_SEEN_FILES_LEN - 1],
    .src  = src,
    .pos  = 0,
    .len  = strlen(src),
    .line = 1,
    .col  = 1
  };
  parse_def(&sub);
  free(src);
}
