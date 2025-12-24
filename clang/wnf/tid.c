static _Thread_local u32 WNF_TID = 0;

fn u32 wnf_tid(void) {
  return WNF_TID;
}

fn void wnf_set_tid(u32 tid) {
  WNF_TID = tid;
  WNF_BANK = &WNF_BANKS[tid];
  WNF_ITRS_PTR = &WNF_ITRS_BANKS[tid].itrs;
#ifdef ITRS_BY_KIND
  WNF_ITRS_KIND_PTR = &WNF_ITRS_KIND_BANKS[tid];
#endif
}
