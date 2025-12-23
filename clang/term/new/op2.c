// Op2(opr, x, y): binary operation, strict on x first
// Layout: HEAP[loc+0] = x, HEAP[loc+1] = y
// EXT field = operation code (OP_ADD, OP_MUL, etc.)
fn Term term_new_op2(u32 opr, Term x, Term y) {
  u32 loc = heap_alloc(2);
  HEAP[loc + 0] = x;
  HEAP[loc + 1] = y;
  return term_new(0, OP2, opr, loc);
}
