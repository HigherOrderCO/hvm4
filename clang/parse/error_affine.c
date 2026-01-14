fn void parse_error_affine(PState *s, u32 nam, u32 side) {
  char nam_buf[16];
  nick_to_str(nam, nam_buf, sizeof(nam_buf));
  fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m (%s:%d:%d)\n", s->file, s->line, s->col);
  fprintf(stderr, "- variable '%s%s' used more than once\n", nam_buf, side == 0 ? "₀" : side == 1 ? "₁" : "");
  fprintf(stderr, "- hint: declare variable as '&%s' to allow multiple uses\n", nam_buf);
  exit(1);
}
