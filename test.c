#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>

#include "arena.h"

int main(void)
{
  const size_t size = 1024 * 1024;
  void *block = malloc(size);
  ns_arena_t *arena = ns_create_arena(block, size);

  // now we allocate space for a string from the arena
  const char s[] = "Hello, World!";

  uintptr_t rp = ns_arena_malloc(arena, sizeof(s));
  char *p = ns_arena_swizzle(arena, rp);

  memcpy(p, s, sizeof(s));

  printf("s(%p): %s, rp(%"PRIu64"), p(%p): %s\n", s, s, rp, p, p);

  return 0;
}
