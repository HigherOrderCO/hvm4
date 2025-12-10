typedef Term (*TermParser)(PState *s, u32 depth);
fn Term parse_choice(PState *s, u32 depth, TermParser const *alts) {
//   for (size_t i = 0; alts[i] != NULL; i++) {
//     // save initial parser state
//     u32 pos = s->pos;
//     u32 len = s->len;
//     u32 line = s->line;
//     u32 col = s-> col;
//
// // static char  *PARSE_SEEN_FILES[1024];
// // static u32    PARSE_SEEN_FILES_LEN = 0;
// // static PBind  PARSE_BINDS[16384];
// // static u32    PARSE_BINDS_LEN = 0;
// // static u32    PARSE_FRESH_LAB = 0x800000; // start at 2^23 to avoid collision with user labels
// // static int    PARSE_FORK_SIDE = -1;      // -1 = off, 0 = left branch (CO0), 1 = right branch (CO1)
// //
//     // try parser, return if succesful
//     Term t = alts[i](s, depth);
//     if (t) return t;
//
//     // restore initial parser state
//     s->pos = pos;
//     s->len = len;
//     s->line = line;
//     s->col = col;
//   }
//   return 0;

    for (size_t i = 0; alts[i] != NULL; i++) {
      // save initial parser state
      u32 _pos  = s->pos;
      u32 _len  = s->len;
      u32 _line = s->line;
      u32 _col  = s->col;
      u32 _PARSE_BINDS_LEN = PARSE_BINDS_LEN;
      u32 _PARSE_FRESH_LAB = PARSE_FRESH_LAB;
      int _PARSE_FORK_SIDE = PARSE_FORK_SIDE;
      u64 _ALLOC = ALLOC;
      size_t _binds_bytes = _PARSE_BINDS_LEN * sizeof(PBind);
      PBind *_PARSE_BINDS = _binds_bytes ? malloc(_binds_bytes) : NULL;
      if (_binds_bytes && !_PARSE_BINDS) sys_error("out of memory");
      if (_PARSE_BINDS_LEN) memcpy(_PARSE_BINDS, PARSE_BINDS, _binds_bytes);

      // try parser, return if succesful
      Term t = alts[i](s, depth);
      if (t) {
        if (_PARSE_BINDS) free(_PARSE_BINDS);
        return t;
      }

      // restore initial parser state
      s->pos  = _pos;
      s->len  = _len;
      s->line = _line;
      s->col  = _col;
      PARSE_BINDS_LEN = _PARSE_BINDS_LEN;
      if (_PARSE_BINDS_LEN) memcpy(PARSE_BINDS, _PARSE_BINDS, _binds_bytes);
      PARSE_FRESH_LAB = _PARSE_FRESH_LAB;
      PARSE_FORK_SIDE = _PARSE_FORK_SIDE;
      ALLOC = _ALLOC;
      if (_PARSE_BINDS) free(_PARSE_BINDS);
    }
    return 0;

}
