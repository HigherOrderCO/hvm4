fn Term parse_term(PState *s, u32 depth);

fn Term parse_term_str(PState *s, u32 depth) {
  parse_advance(s);
  Term t = term_new_ctr(NAM_NIL, 0, 0);
  u32 cs[4096]; u32 n = 0;
  while (parse_peek(s) != '"') {
    u32 c;
    if (parse_peek(s) == '\\') {
      parse_advance(s);
      c = (u32)(u8)parse_peek(s);
      parse_advance(s);
    } else {
      c = parse_utf8(s);
    }
    if (n >= 4096) {
      parse_error(s, "string too long (max 4096 codepoints)", '"');
    }
    cs[n++] = c;
  }
  parse_advance(s);
  for (int i = n - 1; i >= 0; i--) {
    Term c = term_new_num(cs[i]);
    Term h = term_new_ctr(NAM_CHR, 1, &c);
    Term a[2] = {h, t};
    t = term_new_ctr(NAM_CON, 2, a);
  }
  return t;
}
