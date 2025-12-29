// (#a op #b)
// -------------- OP2-NUM-NUM
// #(a opr b)
fn Term wnf_op2_num_num_raw(u32 opr, u32 a, u32 b) {
  ITRS_INC("OP2-NUM-NUM");
  if (__builtin_expect(opr == OP_SUB, 1)) {
    return term_new_num(a - b);
  }
  u32 result;
  switch (opr) {
    case OP_ADD: result = a + b; break;
    case OP_SUB: result = a - b; break;
    case OP_MUL: result = a * b; break;
    case OP_DIV: result = b != 0 ? a / b : 0; break;
    case OP_MOD: result = b != 0 ? a % b : 0; break;
    case OP_AND: result = a & b; break;
    case OP_OR:  result = a | b; break;
    case OP_XOR: result = a ^ b; break;
    case OP_LSH: result = a << b; break;
    case OP_RSH: result = a >> b; break;
    case OP_NOT: result = ~b; break;
    case OP_EQ:  result = a == b ? 1 : 0; break;
    case OP_NE:  result = a != b ? 1 : 0; break;
    case OP_LT:  result = a < b ? 1 : 0; break;
    case OP_LE:  result = a <= b ? 1 : 0; break;
    case OP_GT:  result = a > b ? 1 : 0; break;
    case OP_GE:  result = a >= b ? 1 : 0; break;
    default:     result = 0; break;
  }
  return term_new_num(result);
}

fn Term wnf_op2_num_num(u32 opr, Term x, Term y) {
  return wnf_op2_num_num_raw(opr, term_val(x), term_val(y));
}
