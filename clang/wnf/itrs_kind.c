#ifdef ITRS_BY_KIND
typedef enum {
  WNF_ITRS_AND_ERA,
  WNF_ITRS_AND_INC,
  WNF_ITRS_AND_NUM,
  WNF_ITRS_AND_SUP,
  WNF_ITRS_APP_ERA,
  WNF_ITRS_APP_INC,
  WNF_ITRS_APP_LAM,
  WNF_ITRS_APP_MAT_CTR,
  WNF_ITRS_APP_MAT_SUP,
  WNF_ITRS_APP_RED_CTR,
  WNF_ITRS_APP_RED_DRY,
  WNF_ITRS_APP_RED_ERA,
  WNF_ITRS_APP_RED_INC,
  WNF_ITRS_APP_RED_LAM,
  WNF_ITRS_APP_RED_MAT_CTR,
  WNF_ITRS_APP_RED_MAT_ERA,
  WNF_ITRS_APP_RED_MAT_INC,
  WNF_ITRS_APP_RED_MAT_NUM,
  WNF_ITRS_APP_RED_MAT_SUP,
  WNF_ITRS_APP_RED_NAM,
  WNF_ITRS_APP_RED_RED,
  WNF_ITRS_APP_RED_SUP,
  WNF_ITRS_APP_RED_USE_ERA,
  WNF_ITRS_APP_RED_USE_INC,
  WNF_ITRS_APP_RED_USE_SUP,
  WNF_ITRS_APP_RED_USE_VAL,
  WNF_ITRS_APP_SUP,
  WNF_ITRS_DDU_ERA,
  WNF_ITRS_DDU_INC,
  WNF_ITRS_DDU_NUM,
  WNF_ITRS_DDU_SUP,
  WNF_ITRS_DSU_ERA,
  WNF_ITRS_DSU_INC,
  WNF_ITRS_DSU_NUM,
  WNF_ITRS_DSU_SUP,
  WNF_ITRS_DUP_DRY,
  WNF_ITRS_DUP_LAM,
  WNF_ITRS_DUP_NAM,
  WNF_ITRS_DUP_NOD,
  WNF_ITRS_DUP_RED,
  WNF_ITRS_DUP_SUP,
  WNF_ITRS_EQL_ANY,
  WNF_ITRS_EQL_CTR,
  WNF_ITRS_EQL_DRY,
  WNF_ITRS_EQL_ERA,
  WNF_ITRS_EQL_INC,
  WNF_ITRS_EQL_LAM,
  WNF_ITRS_EQL_MAT,
  WNF_ITRS_EQL_NAM,
  WNF_ITRS_EQL_NUM,
  WNF_ITRS_EQL_SUP,
  WNF_ITRS_EQL_USE,
  WNF_ITRS_MAT_INC,
  WNF_ITRS_OP2_ERA,
  WNF_ITRS_OP2_INC,
  WNF_ITRS_OP2_NUM_ERA,
  WNF_ITRS_OP2_NUM_NUM,
  WNF_ITRS_OP2_NUM_SUP,
  WNF_ITRS_OP2_SUP,
  WNF_ITRS_OR_ERA,
  WNF_ITRS_OR_INC,
  WNF_ITRS_OR_NUM,
  WNF_ITRS_OR_SUP,
  WNF_ITRS_UNS,
  WNF_ITRS_USE_ERA,
  WNF_ITRS_USE_INC,
  WNF_ITRS_USE_SUP,
  WNF_ITRS_USE_VAL,
  WNF_ITRS_MAT_NUM,
  WNF_ITRS_EQL_NEQ,
  WNF_ITRS_KIND_MAX
} WnfItrsKind;

typedef struct __attribute__((aligned(256))) {
  u64 counts[WNF_ITRS_KIND_MAX];
} WnfItrsKindBank;

static WnfItrsKindBank WNF_ITRS_KIND_BANKS[MAX_THREADS] = {{0}};
static _Thread_local WnfItrsKindBank *WNF_ITRS_KIND_PTR = NULL;

static const char *WNF_ITRS_KIND_NAMES[WNF_ITRS_KIND_MAX] = {
  "and_era",
  "and_inc",
  "and_num",
  "and_sup",
  "app_era",
  "app_inc",
  "app_lam",
  "app_mat_ctr",
  "app_mat_sup",
  "app_red_ctr",
  "app_red_dry",
  "app_red_era",
  "app_red_inc",
  "app_red_lam",
  "app_red_mat_ctr",
  "app_red_mat_era",
  "app_red_mat_inc",
  "app_red_mat_num",
  "app_red_mat_sup",
  "app_red_nam",
  "app_red_red",
  "app_red_sup",
  "app_red_use_era",
  "app_red_use_inc",
  "app_red_use_sup",
  "app_red_use_val",
  "app_sup",
  "ddu_era",
  "ddu_inc",
  "ddu_num",
  "ddu_sup",
  "dsu_era",
  "dsu_inc",
  "dsu_num",
  "dsu_sup",
  "dup_dry",
  "dup_lam",
  "dup_nam",
  "dup_nod",
  "dup_red",
  "dup_sup",
  "eql_any",
  "eql_ctr",
  "eql_dry",
  "eql_era",
  "eql_inc",
  "eql_lam",
  "eql_mat",
  "eql_nam",
  "eql_num",
  "eql_sup",
  "eql_use",
  "mat_inc",
  "op2_era",
  "op2_inc",
  "op2_num_era",
  "op2_num_num",
  "op2_num_sup",
  "op2_sup",
  "or_era",
  "or_inc",
  "or_num",
  "or_sup",
  "uns",
  "use_era",
  "use_inc",
  "use_sup",
  "use_val",
  "mat_num",
  "eql_neq"
};

#define ITRS_KIND(id) (WNF_ITRS_KIND_PTR->counts[id]++)

fn u64 wnf_itrs_kind_total(u32 kind) {
  u64 sum = 0;
  u32 threads = thread_get_count();
  for (u32 i = 0; i < threads; i++) {
    sum += WNF_ITRS_KIND_BANKS[i].counts[kind];
  }
  return sum;
}

fn void wnf_itrs_kind_dump(void) {
  for (u32 i = 0; i < WNF_ITRS_KIND_MAX; i++) {
    u64 total = wnf_itrs_kind_total(i);
    if (total == 0) {
      continue;
    }
    printf("- Itrs[%s]: %llu interactions\n", WNF_ITRS_KIND_NAMES[i], total);
  }
}
#else
#define ITRS_KIND(id) ((void)0)
#endif
