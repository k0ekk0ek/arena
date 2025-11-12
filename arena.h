/**
 * arena.h -- relative address pool allocator
 *
 * Doug Lea's allocator stripped and modified by to hand out addresses
 * relative to the memory segment.
 *
 * Copyright (c) 2012, Doug Lea
 * Copyright (c) 2025, Jeroen Koekkoek
 *
 * SPDX-License-Identifier: CC0-1.0
 *
 */
#ifndef NS_ARENA_H
#define NS_ARENA_H

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

#include "macros.h"

typedef struct ns_arena ns_arena_t;
struct ns_arena; // purposely opaque

ns_nonnull((1))
static ns_always_inline void *ns_arena_swizzle(
  const ns_arena_t *arena, uintptr_t object)
{
  return (void*)((uintptr_t)arena + object);
}

ns_nonnull((1))
static ns_always_inline uintptr_t ns_arena_unswizzle(
  const ns_arena_t *arena, void *address)
{
  return (uintptr_t)arena - (uintptr_t)address;
}

ns_nonnull((1))
ns_arena_t *ns_create_arena(void *base, size_t size);

ns_nonnull((1))
void ns_destroy_arena(ns_arena_t *arena);

ns_nodiscard ns_nonnull((1))
uintptr_t ns_arena_malloc(ns_arena_t *arena, size_t size);

ns_nonnull((1))
void ns_arena_free(ns_arena_t *arena, uintptr_t object);

ns_nodiscard ns_nonnull((1))
uintptr_t ns_arena_calloc(ns_arena_t *arena, size_t nmemb, size_t size);

ns_nodiscard ns_nonnull((1))
uintptr_t ns_arena_realloc(ns_arena_t *arena, uintptr_t object, size_t size);

#endif // NS_ARENA_H
