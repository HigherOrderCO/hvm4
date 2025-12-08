fn void parse_error_var(const char *fmt, u32 nam) {
  char buf[16];
  nick_to_str(nam, buf, sizeof(buf));
  fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m\n");
  fprintf(stderr, fmt, buf);
  exit(1);
}

fn void parse_error_affine(u32 nam, u32 uses, int is_dup, const char *hint) {
  fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m\n");
  fprintf(stderr, "- %svariable '", is_dup ? "dup " : "");
  print_name(stderr, nam);
  if (is_dup) {
    fprintf(stderr, "' used %d times (max 2 with ₀ and ₁)\n", uses);
  } else {
    fprintf(stderr, "' used %d times (not cloned)\n", uses);
    fprintf(stderr, "- hint: use %s to allow multiple uses\n", hint);
  }
  exit(1);
}

fn void parse_error_affine_side(u32 nam, int side, u32 uses) {
  fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m\n");
  fprintf(stderr, "- dup variable '");
  print_name(stderr, nam);
  fprintf(stderr, "%s' used %d times (not cloned)\n", side == 0 ? "₀" : "₁", uses);
  fprintf(stderr, "- hint: use &");
  print_name(stderr, nam);
  fprintf(stderr, " to allow multiple uses\n");
  exit(1);
}
