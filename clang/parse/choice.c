typedef Term (*Parser)(Term f, PState *s, u32 depth, int min_prec);

fn Term parse_choice(Term f, PState *s, u32 depth, int min_prec, Parser const *alts) {
    int is_postfix = (f != NONE);

    while (1) {
        parse_skip(s);
        Term result = 0;

        for (size_t i = 0; alts[i] != NULL; i++) {
            // save initial parser state
            u32 _pos  = s->pos;
            u32 _len  = s->len;
            u32 _line = s->line;
            u32 _col  = s->col;
            u32 _PARSE_BINDS_LEN = PARSE_BINDS_LEN;
            u32 _PARSE_FRESH_LAB = PARSE_FRESH_LAB;
            int _PARSE_FORK_SIDE = PARSE_FORK_SIDE;
            size_t _binds_bytes = _PARSE_BINDS_LEN * sizeof(PBind);
            PBind *_PARSE_BINDS = _binds_bytes ? malloc(_binds_bytes) : NULL;
            if (_binds_bytes && !_PARSE_BINDS) sys_error("out of memory");
            if (_PARSE_BINDS_LEN) memcpy(_PARSE_BINDS, PARSE_BINDS, _binds_bytes);
            // save initial heap state
            u64 _ALLOC = ALLOC;

            // try parser, break if successful
            Term t = alts[i](f, s, depth, min_prec);
            if (t) {
                if (_PARSE_BINDS) free(_PARSE_BINDS);
                result = t;
                break;
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
            if (_PARSE_BINDS) free(_PARSE_BINDS);
            // restore initial heap state
            ALLOC = _ALLOC;
        }

        if (!result) return is_postfix ? f : 0;
        if (!is_postfix) return result;
        f = result;
    }
}
