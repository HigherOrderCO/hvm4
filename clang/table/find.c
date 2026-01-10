// Finds or creates an ID for the given name.
// If the name exists, returns its existing ID.
// If not, assigns a new unique ID and stores the name.
fn u32 table_find(const char *name, u32 len) {
  // Linear scan for existing name
  for (u32 i = 0; i < TABLE_LEN; i++) {
    if (strlen(TABLE[i]) == len && memcmp(TABLE[i], name, len) == 0) {
      return i;
    }
  }
  // Not found - create new entry
  u32  id   = TABLE_LEN++;
  char *copy = malloc(len + 1);
  if (!copy) {
    sys_error("out of memory in table_find");
  }
  memcpy(copy, name, len);
  copy[len] = '\0';
  TABLE[id] = copy;
  return id;
}
