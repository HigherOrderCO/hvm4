// (#a op #b)
// -------------- OP2-NUM-NUM
// #(a opr b)
fn Term wnf_op2_num_num(u32 opr, Term x, Term y) {
  ITRS++;
  u32 a = term_val(x);
  u32 b = term_val(y);
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
