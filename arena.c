/**
 * malloc.c - relative address pool allocator
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
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "arena.h"

#define MALLOC_ALIGNMENT ((size_t)(2 * sizeof(void *)))

#define CORRUPTION_ERROR_ACTION(M) abort()
#define USAGE_ERROR_ACTION(m, p) abort()

#if !INSECURE
/* Minimize impact of checks in compilers that support it */
# define RTCHECK(e)  ns_likely(e)
#else
# define RTCHECK(e)  (1)
#endif

/* The maximum possible size_t value has all bits set */
#define MAX_SIZE_T           (~(size_t)0)



typedef ns_arena_t* mstate;


#define swizzle(m_, p_) ns_arena_swizzle(m_, p_)


/* ------------------- size_t and alignment properties -------------------- */

/* The byte and bit size of a size_t */
#define SIZE_T_SIZE         (sizeof(size_t))
#define SIZE_T_BITSIZE      (sizeof(size_t) << 3)

/* Some constants coerced to size_t */
/* Annoying but necessary to avoid errors on some platforms */
#define SIZE_T_ZERO         ((size_t)0)
#define SIZE_T_ONE          ((size_t)1)
#define SIZE_T_TWO          ((size_t)2)
#define SIZE_T_FOUR         ((size_t)4)
#define TWO_SIZE_T_SIZES    (SIZE_T_SIZE<<1)
#define FOUR_SIZE_T_SIZES   (SIZE_T_SIZE<<2)
#define SIX_SIZE_T_SIZES    (FOUR_SIZE_T_SIZES+TWO_SIZE_T_SIZES)
#define HALF_MAX_SIZE_T     (MAX_SIZE_T / 2U)

/* The bit mask value corresponding to MALLOC_ALIGNMENT */
#define CHUNK_ALIGN_MASK    (MALLOC_ALIGNMENT - SIZE_T_ONE)

/* True if address a has acceptable alignment */
#define is_aligned(A)       (((size_t)((A)) & (CHUNK_ALIGN_MASK)) == 0)

/* the number of bytes to offset an address to align it */
#define align_offset(A)\
 ((((size_t)(A) & CHUNK_ALIGN_MASK) == 0)? 0 :\
  ((MALLOC_ALIGNMENT - ((size_t)(A) & CHUNK_ALIGN_MASK)) & CHUNK_ALIGN_MASK))


/* ------------------------ Chunk representations ------------------------- */

struct malloc_chunk {
  size_t    prev_foot;  /* Size of previous chunk (if free).  */
  size_t    head;       /* Size and inuse bits. */
  uintptr_t fd;         /* double links -- used only if free. */
  uintptr_t bk;
};

typedef struct malloc_chunk  mchunk;
typedef struct malloc_chunk* mchunkptr;
typedef struct malloc_chunk* sbinptr;  /* The type of bins of chunks */
typedef unsigned int bindex_t;         /* Described below */
typedef unsigned int binmap_t;         /* Described below */
typedef unsigned int flag_t;           /* The type of various bit flag sets */


/* ------------------- Chunks sizes and alignments ----------------------- */

#define MCHUNK_SIZE         (sizeof(mchunk))

#define CHUNK_OVERHEAD      (TWO_SIZE_T_SIZES)

/* The smallest size we can malloc is an aligned minimal chunk */
#define MIN_CHUNK_SIZE\
  ((MCHUNK_SIZE + CHUNK_ALIGN_MASK) & ~CHUNK_ALIGN_MASK)

/* conversion from malloc headers to user pointers, and back */
#define chunk2mem(p)        ((p) + TWO_SIZE_T_SIZES)
#define mem2chunk(mem)      ((mem) - TWO_SIZE_T_SIZES)
/* chunk associated with aligned address A */
#define align_as_chunk(A)   (mchunkptr)((A) + align_offset(chunk2mem(A)))

/* Bounds on request (not chunk) sizes. */
#define MAX_REQUEST         ((-MIN_CHUNK_SIZE) << 2)
#define MIN_REQUEST         (MIN_CHUNK_SIZE - CHUNK_OVERHEAD - SIZE_T_ONE)

/* pad request bytes into a usable size */
#define pad_request(req) \
   (((req) + CHUNK_OVERHEAD + CHUNK_ALIGN_MASK) & ~CHUNK_ALIGN_MASK)

/* pad request, checking for minimum (but not maximum) */
#define request2size(req) \
  (((req) < MIN_REQUEST)? MIN_CHUNK_SIZE : pad_request(req))


/* ---------------------- Overlaid data structures ----------------------- */

struct malloc_tree_chunk {
  /* The first four fields must be compatible with malloc_chunk */
  size_t    prev_foot;
  size_t    head;
  uintptr_t fd;
  uintptr_t bk;

  uintptr_t child[2];
  uintptr_t parent;
  bindex_t  index;
};

typedef struct malloc_tree_chunk  tchunk;
typedef struct malloc_tree_chunk* tchunkptr;
typedef uintptr_t* tbinptr; /* The type of bins of trees */

/* A little helper macro for trees */
ns_nodiscard
static ns_always_inline uintptr_t leftmost_child(const mstate m, uintptr_t T)
{
  tchunkptr t = swizzle(m, T);
  return t->child[0] != 0 ? t->child[0] : t->child[1];
}

/* ----------------------------- Segments -------------------------------- */

struct malloc_segment {
  char*        base;             /* base address */
  size_t       size;             /* allocated size */
};

typedef struct malloc_segment  msegment;
typedef struct malloc_segment* msegmentptr;


/* ---------------------------- malloc_state ----------------------------- */

/* Bin types, widths and sizes */
#define NSMALLBINS        (32U)
#define NTREEBINS         (32U)
#define SMALLBIN_SHIFT    (3U)
#define SMALLBIN_WIDTH    (SIZE_T_ONE << SMALLBIN_SHIFT)
#define TREEBIN_SHIFT     (8U)
#define MIN_LARGE_SIZE    (SIZE_T_ONE << TREEBIN_SHIFT)
#define MAX_SMALL_SIZE    (MIN_LARGE_SIZE - SIZE_T_ONE)
#define MAX_SMALL_REQUEST (MAX_SMALL_SIZE - CHUNK_ALIGN_MASK - CHUNK_OVERHEAD)

struct ns_arena {
  binmap_t   smallmap;
  binmap_t   treemap;
  size_t     dvsize;
  size_t     topsize;
  uintptr_t  dv;
  uintptr_t  top;
  size_t     trim_check;
  size_t     magic;
  uintptr_t  smallbins[(NSMALLBINS+1)*2];
  uintptr_t  treebins[NTREEBINS];
  flag_t     mflags;
  msegment   seg;
};


/* ------------- Global malloc_state and malloc_params ------------------- */

/*
  malloc_params holds global properties, including those that can be
  dynamically set using mallopt. There is a single instance, mparams,
  initialized in init_mparams. Note that the non-zeroness of "magic"
  also serves as an initialization flag.
*/

struct malloc_params {
  size_t magic;
  size_t page_size;
  size_t granularity;
  size_t mmap_threshold;
  size_t trim_threshold;
  flag_t default_mflags;
};

// FIXME: ensure to initialize on startup, this is used by all arenas
//        it is never written after initialization!
static struct malloc_params mparams;

/* Ensure mparams initialized */
#define ensure_initialization() (void)(mparams.magic != 0 || init_mparams())

#define is_initialized(M)  ((M)->top != 0)


/* -------------------------- system alloc setup ------------------------- */

/*
  TOP_FOOT_SIZE is padding at the end of the segment, including space to
  enstablish a safe margin for single instruction multiple data operations.
*/
#define TOP_FOOT_SIZE\
  (align_offset(chunk2mem(0)) + (size_t)(64 > MIN_CHUNK_SIZE ? 64 : MIN_CHUNK_SIZE))


/* ------------------ Operations on head and foot fields ----------------- */

/*
  The head field of a chunk is or'ed with PINUSE_BIT when previous
  adjacent chunk in use, and or'ed with CINUSE_BIT if this chunk is in
  use.
*/

#define PINUSE_BIT          (SIZE_T_ONE)
#define CINUSE_BIT          (SIZE_T_TWO)
#define INUSE_BITS          (PINUSE_BIT|CINUSE_BIT)
#define FLAG_BITS           (PINUSE_BIT|CINUSE_BIT)

/* Head value for fenceposts */
#define FENCEPOST_HEAD      (INUSE_BITS|SIZE_T_SIZE)

/* extraction of fields from head words */
ns_nodiscard ns_nonnull((1))
static ns_always_inline size_t cinuse(const mstate m, uintptr_t p)
{
  return ((mchunkptr)swizzle(m, p))->head & CINUSE_BIT;
}

ns_nodiscard ns_nonnull((1))
static ns_always_inline size_t pinuse(const mstate m, uintptr_t p)
{
  return ((mchunkptr)swizzle(m, p))->head & PINUSE_BIT;
}

ns_nonnull((1))
static ns_always_inline void clear_pinuse(const mstate m, uintptr_t p)
{
  ((mchunkptr)swizzle(m, p))->head &= ~PINUSE_BIT;
}

ns_nodiscard ns_nonnull((1))
static ns_always_inline bool is_inuse(const mstate m, uintptr_t p)
{
  return (((mchunkptr)swizzle(m, p))->head & INUSE_BITS) != PINUSE_BIT;
}

ns_nodiscard ns_nonnull((1))
static ns_always_inline size_t chunksize(const mstate m, uintptr_t p)
{
  return ((mchunkptr)swizzle(m, p))->head & ~FLAG_BITS;
}

/* Treat space at ptr +/- offset as a chunk */
ns_nodiscard ns_nonnull((1))
static ns_always_inline uintptr_t chunk_plus_offset(
  ns_maybe_unused const mstate m, uintptr_t p, size_t s)
{
  return p + s;
}

ns_nodiscard ns_nonnull((1))
static ns_always_inline uintptr_t chunk_minus_offset(
  ns_maybe_unused const mstate m, uintptr_t p, size_t s)
{
  return p - s;
}

/* Ptr to next or previous physical malloc_chunk. */
ns_nodiscard ns_nonnull((1))
static ns_always_inline uintptr_t next_chunk(const mstate m, uintptr_t p)
{
  return p + (((mchunkptr)swizzle(m, p))->head & ~FLAG_BITS);
}

ns_nodiscard ns_nonnull((1))
static ns_always_inline uintptr_t prev_chunk(const mstate m, uintptr_t p)
{
  return p - ((mchunkptr)swizzle(m, p))->prev_foot;
}

/* extract next chunk's pinuse bit */
ns_nodiscard ns_nonnull((1))
static ns_always_inline size_t next_pinuse(const mstate m, uintptr_t p)
{
  return ((mchunkptr)swizzle(m, next_chunk(m, p)))->head & PINUSE_BIT;
}

/* Set size, pinuse bit, and foot */
ns_nonnull((1))
static ns_always_inline void set_size_and_pinuse_of_free_chunk(
  const mstate m, uintptr_t p, size_t s)
{
  ((mchunkptr)swizzle(m, p))->head = (s|PINUSE_BIT);
  ((mchunkptr)swizzle(m, p + s))->prev_foot = s;
}

/* Set size, pinuse bit, foot, and clear next pinuse */
ns_nonnull((1))
static ns_always_inline void set_free_with_pinuse(
  const mstate m, uintptr_t p, size_t s, uintptr_t n)
{
  clear_pinuse(m, n);
  set_size_and_pinuse_of_free_chunk(m, p, s);
}

/* Get the internal overhead associated with chunk p */
#define overhead_for(p) (CHUNK_OVERHEAD)

/* Return true if malloced space is not necessarily cleared */
#define calloc_must_clear(p) (1)


/* -------------------------- Debugging setup ---------------------------- */

#if !defined(NDEBUG)
# define check_free_chunk(M,P)       do_check_free_chunk(M,P)
# define check_inuse_chunk(M,P)      do_check_inuse_chunk(M,P)
# define check_top_chunk(M,P)        do_check_top_chunk(M,P)
# define check_malloced_chunk(M,P,N) do_check_malloced_chunk(M,P,N)
# define check_mmapped_chunk(M,P)    do_check_mmapped_chunk(M,P)
# define check_malloc_state(M)       do_check_malloc_state(M)

static void do_check_any_chunk(const mstate m, uintptr_t p);
static void do_check_top_chunk(const mstate m, uintptr_t p);
static void do_check_inuse_chunk(const mstate m, uintptr_t p);
static void do_check_free_chunk(const mstate m, uintptr_t p);
static void do_check_malloced_chunk(const mstate m, uintptr_t mem, size_t s);
static void do_check_tree(const mstate m, uintptr_t t);
static void do_check_treebin(const mstate m, bindex_t i);
static void do_check_smallbin(const mstate m, bindex_t i);
static void do_check_malloc_state(const mstate m);
static int bin_find(const mstate m, uintptr_t x);
static size_t traverse_and_check(const mstate m);
#else /* NDEBUG */
# define check_free_chunk(M,P)
# define check_inuse_chunk(M,P)
# define check_malloced_chunk(M,P,N)
# define check_mmapped_chunk(M,P)
# define check_malloc_state(M)
# define check_top_chunk(M,P)
#endif /* NDEBUG */


/* ---------------------------- Indexing Bins ---------------------------- */

#define is_small(s)         (((s) >> SMALLBIN_SHIFT) < NSMALLBINS)
#define small_index(s)      (bindex_t)((s)  >> SMALLBIN_SHIFT)
#define small_index2size(i) ((i)  << SMALLBIN_SHIFT)
#define MIN_SMALL_INDEX     (small_index(MIN_CHUNK_SIZE))

/* addressing by index. See above about smallbin repositioning */
ns_nodiscard
static ns_always_inline uintptr_t smallbin_at(const mstate M, bindex_t i)
{
  const size_t base = offsetof(ns_arena_t, smallbins);
  const size_t size = sizeof(M->smallbins[0]);
  return base + (i << 1) * size;
}

ns_nodiscard
static ns_always_inline uintptr_t *treebin_at(const mstate M, bindex_t i)
{
  return &M->treebins[i];
}

ns_nodiscard
static ns_always_inline bindex_t compute_tree_index(size_t S)
{
  const size_t X = S >> TREEBIN_SHIFT;
  if (X == 0u)
    return 0u;
  if (X > 0xFFFFu)
    return NTREEBINS - 1;
  bindex_t K = (unsigned) sizeof(X)*__CHAR_BIT__ - 1 - (unsigned) __builtin_clzll(X);
  bindex_t I = (bindex_t)((K << 1) + ((S >> (K + (TREEBIN_SHIFT-1)) & 1)));
  return I;
}

/* Shift placing maximum resolved bit in a treebin at i as sign bit */
ns_nodiscard
static ns_always_inline size_t leftshift_for_tree_index(bindex_t i)
{
  return (i == NTREEBINS - 1)
    ? 0 : ((SIZE_T_BITSIZE-SIZE_T_ONE) - (((i) >> 1) + TREEBIN_SHIFT - 2));
}

/* The size of the smallest chunk held in bin with index i */
ns_nodiscard
static ns_always_inline size_t minsize_for_tree_index(bindex_t i)
{
  return ((SIZE_T_ONE << (((i) >> 1) + TREEBIN_SHIFT)) |  \
         (((size_t)((i) & SIZE_T_ONE)) << (((i) >> 1) + TREEBIN_SHIFT - 1)));
}


/* ------------------------ Operations on bin maps ----------------------- */

/* bit corresponding to given index */
#define idx2bit(i)              ((binmap_t)(1) << (i))

/* Mark/Clear bits with given index */
#define mark_smallmap(M,i)      ((M)->smallmap |=  idx2bit(i))
#define clear_smallmap(M,i)     ((M)->smallmap &= ~idx2bit(i))
#define smallmap_is_marked(M,i) ((M)->smallmap &   idx2bit(i))

#define mark_treemap(M,i)       ((M)->treemap  |=  idx2bit(i))
#define clear_treemap(M,i)      ((M)->treemap  &= ~idx2bit(i))
#define treemap_is_marked(M,i)  ((M)->treemap  &   idx2bit(i))

/* isolate the least set bit of a bitmap */
ns_nodiscard
static ns_always_inline binmap_t least_bit(binmap_t x)
{
  return x & -x;
}

/* mask with all bits to left of least bit of x on */
ns_nodiscard
static ns_always_inline binmap_t left_bits(binmap_t x)
{
  return (x<<1) | -(x<<1);
}

ns_nodiscard
static ns_always_inline bindex_t compute_bit2idx(binmap_t X)
{
  // FIXME: use implementation in bits.h?
  return (bindex_t)__builtin_ctz(X);
}


/* ----------------------- Runtime Check Support ------------------------- */

#if !INSECURE
// dlmalloc checks if addresses are at least as high as least_addr, the
// unaligned base address of the mspace, usually a block of memory obtained
// from MORECORE or MMAP. This implementation uses relative addressing and
// supports only one contiguous segment, an address must therefore reside
// within a pre-defined range.
ns_nodiscard
static ns_always_inline bool ok_address(const mstate m, uintptr_t p)
{
  return p > 0 && p <= m->top + m->topsize;
}

/* Check if address of next chunk n is higher than base chunk p */
#define ok_next(p, n)    ((char*)(p) < (char*)(n))
/* Check if p has inuse status */
#define ok_inuse(m, p)     is_inuse(m, p)
/* Check if p has its pinuse bit on */
#define ok_pinuse(m, p)     pinuse(m, p)

#else /* !INSECURE */
#define ok_address(M, a) (1)
#define ok_next(b, n)    (1)
#define ok_inuse(p)      (1)
#define ok_pinuse(p)     (1)
#endif /* !INSECURE */

#define ok_magic(M)      ((M)->magic == mparams.magic)

/* Macros for setting head/foot of non-mmapped chunks */

/* Set foot of inuse chunk to be xor of mstate and seed */
ns_nonnull((1))
static ns_always_inline void mark_inuse_foot(
  const mstate m, uintptr_t p, size_t s)
{
  // dlmalloc sets prev_foot to ((size_t)(M) ^ mparams.magic), as the segment
  // is required to be relocatable, this adaptation must not.
  ((mchunkptr)swizzle(m, p + s))->prev_foot = ((size_t)0ull ^ mparams.magic);
}

ns_nodiscard ns_nonnull((1))
static ns_always_inline mstate get_mstate_for(const mstate m, uintptr_t p)
{
  assert(!(((mchunkptr)swizzle(m, p))->prev_foot ^ mparams.magic));
  return m;
}

/* Set cinuse bit and pinuse bit of next chunk */
ns_nonnull((1))
static ns_always_inline void set_inuse(
  const mstate m, uintptr_t p, size_t s)
{
  const size_t pinuse_bit = ((mchunkptr)swizzle(m, p))->head & PINUSE_BIT;
  ((mchunkptr)swizzle(m, p))->head = (s|pinuse_bit|CINUSE_BIT);
  ((mchunkptr)swizzle(m, p + s))->head |= PINUSE_BIT;
  mark_inuse_foot(m, p, s);
}

/* Set cinuse and pinuse of this chunk and pinuse of next chunk */
ns_nonnull((1))
static ns_always_inline void set_inuse_and_pinuse(
  const mstate m, uintptr_t p, size_t s)
{
  ((mchunkptr)swizzle(m, p))->head = (s|PINUSE_BIT|CINUSE_BIT);
  ((mchunkptr)swizzle(m, p + s))->head |= PINUSE_BIT;
  mark_inuse_foot(m, p, s);
}

/* Set size, cinuse and pinuse bit of this chunk */
ns_nonnull((1))
static ns_always_inline void set_size_and_pinuse_of_inuse_chunk(
  const mstate m, uintptr_t p, size_t s)
{
  ((mchunkptr)swizzle(m, p))->head = (s|PINUSE_BIT|CINUSE_BIT);
  mark_inuse_foot(m, p, s);
}


#if !defined(NDEBUG)
/* ------------------------- Debugging Support --------------------------- */

/* Check properties of any chunk, whether free, inuse, mmapped etc  */
static void do_check_any_chunk(mstate m, uintptr_t p) {
  assert(is_aligned(chunk2mem(p)));
  assert(ok_address(m, p));
}

/* Check properties of top chunk */
static void do_check_top_chunk(const mstate m, uintptr_t p) {
  mchunkptr _p = swizzle(m, p);
  size_t sz = _p->head & ~INUSE_BITS; /* third-lowest bit can be set! */
  assert(is_aligned(chunk2mem(p)));
  assert(ok_address(m, p));
  assert(sz == m->topsize);
  assert(sz > 0);
  /* Addresses and sizes are relative to mstate, not segment. */
  const size_t overhead = (uintptr_t)m - (uintptr_t)m->seg.base;
  assert(sz == ((m->seg.size - overhead) - p) - TOP_FOOT_SIZE);
  assert(pinuse(m, p));
  assert(!pinuse(m, chunk_plus_offset(m, p, sz)));
}

/* Check properties of inuse chunks */
static void do_check_inuse_chunk(const mstate m, uintptr_t p) {
  do_check_any_chunk(m, p);
  assert(is_inuse(m, p));
  assert(next_pinuse(m, p));
  /* If not pinuse and not mmapped, previous chunk has OK offset */
  assert(pinuse(m, p) || next_chunk(m, prev_chunk(m, p)) == p);
}

/* Check properties of free chunks */
static void do_check_free_chunk(const mstate m, uintptr_t p) {
  size_t sz = chunksize(m, p);
  uintptr_t next = chunk_plus_offset(m, p, sz);
  do_check_any_chunk(m, p);
  assert(!is_inuse(m, p));
  assert(!next_pinuse(m, p));
  if (p != m->dv && p != m->top) {
    if (sz >= MIN_CHUNK_SIZE) {
      assert((sz & CHUNK_ALIGN_MASK) == 0);
      assert(is_aligned(chunk2mem(p)));
      const mchunkptr _next = swizzle(m, next);
      assert(_next->prev_foot == sz);
      assert(pinuse(m, p));
      assert (next == m->top || is_inuse(m, next));
      const mchunkptr _p = swizzle(m, p);
      const mchunkptr _fd = swizzle(m, _p->fd);
      const mchunkptr _bk = swizzle(m, _p->bk);
      assert(_fd->bk == p);
      assert(_bk->fd == p);
    }
    else  /* markers are always of size SIZE_T_SIZE */
      assert(sz == SIZE_T_SIZE);
  }
}

static void do_check_malloced_chunk(const mstate m, uintptr_t mem, size_t s) {
  if (mem != 0) {
    uintptr_t p = mem2chunk(mem);
    mchunkptr _p = swizzle(m, p);
    size_t sz = _p->head & ~INUSE_BITS;
    do_check_inuse_chunk(m, p);
    assert((sz & CHUNK_ALIGN_MASK) == 0);
    assert(sz >= MIN_CHUNK_SIZE);
    assert(sz >= s);
    /* unless mmapped, size is less than MIN_CHUNK_SIZE more than request */
    assert(sz < (s + MIN_CHUNK_SIZE));
  }
}

/* Check a tree and its subtrees.  */
static void do_check_tree(const mstate m, uintptr_t t) {
  uintptr_t head = 0;
  const tchunkptr _t = swizzle(m, t);
  uintptr_t u = t;
  bindex_t tindex = _t->index;
  size_t tsize = chunksize(m, t);
  bindex_t idx = compute_tree_index(tsize);
  assert(tindex == idx);
  assert(tsize >= MIN_LARGE_SIZE);
  assert(tsize >= minsize_for_tree_index(idx));
  assert((idx == NTREEBINS-1) || (tsize < minsize_for_tree_index((idx+1))));

  do { /* traverse through chain of same-sized nodes */
    do_check_any_chunk(m, u);
    const tchunkptr _u = swizzle(m, u);
    assert(_u->index == tindex);
    assert(chunksize(m, u) == tsize);
    assert(!is_inuse(m, u));
    assert(!next_pinuse(m, u));
    const tchunkptr _fd = swizzle(m, _u->fd);
    const tchunkptr _bk = swizzle(m, _u->bk);
    assert(_fd->bk == u);
    assert(_bk->fd == u);
    if (_u->parent == 0) {
      assert(_u->child[0] == 0);
      assert(_u->child[1] == 0);
    }
    else {
      assert(head == 0); /* only one node on chain has parent */
      head = u;
      assert(_u->parent != u);
      assert (((const tchunkptr)swizzle(m, _u->parent))->child[0] == u ||
              ((const tchunkptr)swizzle(m, _u->parent))->child[1] == u ||
              _u->parent == u); //*((tbinptr*)(u->parent)) == u); // << give this a good check!
                                // >> needs some more work
      if (_u->child[0] != 0) {
        assert(((const tchunkptr)swizzle(m, _u->child[0]))->parent == u);
        assert(_u->child[0] != u);
        do_check_tree(m, _u->child[0]);
      }
      if (_u->child[1] != 0) {
        assert(((const tchunkptr)swizzle(m, _u->child[1]))->parent == u);
        assert(_u->child[1] != u);
        do_check_tree(m, _u->child[1]);
      }
      if (_u->child[0] != 0 && _u->child[1] != 0) {
        assert(chunksize(m, _u->child[0]) < chunksize(m, _u->child[1]));
      }
    }
    u = _u->fd;
  } while (u != t);
  assert(head != 0);
}

/*  Check all the chunks in a treebin.  */
static void do_check_treebin(const mstate m, bindex_t i) {
  tbinptr tb = treebin_at(m, i);
  uintptr_t t = *tb;
  int empty = (m->treemap & (1U << i)) == 0;
  if (t == 0)
    assert(empty);
  if (!empty)
    do_check_tree(m, t);
}

/*  Check all the chunks in a smallbin.  */
static void do_check_smallbin(const mstate m, bindex_t i) {
  uintptr_t b = smallbin_at(m, i);
  uintptr_t p = ((const mchunkptr)swizzle(m, b))->bk;
  unsigned int empty = (m->smallmap & (1U << i)) == 0;
  if (p == b)
    assert(empty);
  if (!empty) {
    const mchunkptr _p = swizzle(m, p);
    for (; p != b; p = _p->bk) {
      size_t size = chunksize(m, p);
      /* each chunk claims to be free */
      do_check_free_chunk(m, p);
      /* chunk belongs in bin */
      assert(small_index(size) == i);
      assert(_p->bk == b || chunksize(m, _p->bk) == chunksize(m, p));
      /* chunk is followed by an inuse chunk */
      uintptr_t q = next_chunk(m, p);
      do_check_inuse_chunk(m, q);
    }
  }
}

/* Find x in a bin. Used in other check functions. */
static int bin_find(const mstate m, uintptr_t x) {
  size_t size = chunksize(m, x);
  if (is_small(size)) {
    bindex_t sidx = small_index(size);
    uintptr_t b = smallbin_at(m, sidx);
    if (smallmap_is_marked(m, sidx)) {
      uintptr_t p = b;
      mchunkptr _p;
      do {
        _p = swizzle(m, p);
        if (p == x)
          return 1;
      } while ((p = _p->fd) != b);
    }
  }
  else {
    bindex_t tidx = compute_tree_index(size);
    if (treemap_is_marked(m, tidx)) {
      uintptr_t t = *treebin_at(m, tidx);
      size_t sizebits = size << leftshift_for_tree_index(tidx);
      while (t != 0 && chunksize(m, t) != size) {
        const tchunkptr _t = swizzle(m, t);
        t = _t->child[(sizebits >> (SIZE_T_BITSIZE-SIZE_T_ONE)) & 1];
        sizebits <<= 1;
      }
      if (t != 0) {
        uintptr_t u = t;
        const tchunkptr _u = swizzle(m, u);
        do {
          if (u == x)
            return 1;
        } while ((u = _u->fd) != t);
      }
    }
  }
  return 0;
}

/* Traverse each chunk and check it; return total */
static size_t traverse_and_check(const mstate m) {
  size_t sum = 0;
  if (is_initialized(m)) {
    sum += m->topsize + TOP_FOOT_SIZE;
    const mchunkptr _q = align_as_chunk(m->seg.base);
    // Addresses are relative to mstate, not the segment. Subtract overhead
    // correct and initiate loop from second chunk.
    const size_t overhead = (uintptr_t)m - (uintptr_t)m->seg.base;
    uintptr_t q = (_q->head & ~INUSE_BITS) - overhead;
    uintptr_t lastq = q;
    sum += q;
    assert(pinuse(m, q));

    q = next_chunk(m, q);
    while ((q >= lastq && q < m->seg.size) && q != m->top) {
      sum += chunksize(m, q);
      if (is_inuse(m, q)) {
        assert(!bin_find(m, q));
        do_check_inuse_chunk(m, q);
      }
      else {
        assert(q == m->dv || bin_find(m, q));
        assert(lastq == 0 || is_inuse(m, lastq)); /* Not 2 consecutive free */
        do_check_free_chunk(m, q);
      }
      lastq = q;
      q = next_chunk(m, q);
    }
  }
  return sum;
}

/* Check all properties of malloc_state. */
static void do_check_malloc_state(const mstate m) {
  /* check bins */
  for (bindex_t i = 0; i < NSMALLBINS; ++i)
    do_check_smallbin(m, i);
  for (bindex_t i = 0; i < NTREEBINS; ++i)
    do_check_treebin(m, i);

  if (m->dvsize != 0) { /* check dv chunk */
    do_check_any_chunk(m, m->dv);
    assert(m->dvsize == chunksize(m, m->dv));
    assert(m->dvsize >= MIN_CHUNK_SIZE);
    assert(bin_find(m, m->dv) == 0);
  }

  if (m->top != 0) {   /* check top chunk */
    do_check_top_chunk(m, m->top);
    /*assert(m->topsize == chunksize(m->top)); redundant */
    assert(m->topsize > 0);
    assert(bin_find(m, m->top) == 0);
  }

  size_t total = traverse_and_check(m);
  assert(total <= m->seg.size);
}
#endif /* NDEBUG */


/* ---------------------------- setting mparams -------------------------- */
static int init_mparams(void) {
  memset(&mparams, 0, sizeof(mparams));
  // FIXME: implement
  return 1;
}


/* ----------------------- Operations on smallbins ----------------------- */

/*
  Various forms of linking and unlinking are defined as macros.  Even
  the ones for trees, which are very long but have very short typical
  paths.  This is ugly but reduces reliance on inlining support of
  compilers.
*/

/* Link a free chunk into a smallbin */
ns_nonnull((1))
static ns_always_inline void insert_small_chunk(
  mstate M, uintptr_t P, size_t S)
{
  mchunkptr _P = swizzle(M, P);
  bindex_t I = small_index(S);
  uintptr_t B = smallbin_at(M, I);
  uintptr_t F = B;
  assert(S >= MIN_CHUNK_SIZE);
  mchunkptr _B = swizzle(M, B);
  if (!smallmap_is_marked(M, I))
    mark_smallmap(M, I);
  else if (RTCHECK(ok_address(M, _B->fd)))
    F = _B->fd;
  else {
    CORRUPTION_ERROR_ACTION(M);
  }
  mchunkptr _F = swizzle(M, F);
  _B->fd = P;
  _F->bk = P;
  _P->fd = F;
  _P->bk = B;
}

/* Unlink a chunk from a smallbin */
ns_nonnull((1))
static ns_always_inline void unlink_small_chunk(
  mstate M, uintptr_t P, size_t S)
{
  const mchunkptr _P = swizzle(M, P);
  const uintptr_t F = _P->fd;
  const uintptr_t B = _P->bk;
  bindex_t I = small_index(S);
  assert(P != B);
  assert(P != F);
  mchunkptr _F = swizzle(M, F);
  mchunkptr _B = swizzle(M, B);
  assert(chunksize(M, P) == small_index2size(I));
  if (RTCHECK(F == smallbin_at(M,I) || (ok_address(M, F) && _F->bk == P))) {
    if (B == F) {
      clear_smallmap(M, I);
    }
    else if (RTCHECK(B == smallbin_at(M,I) ||
                     (ok_address(M, B) && _B->fd == P))) {
      _F->bk = B;
      _B->fd = F;
    }
    else {
      CORRUPTION_ERROR_ACTION(M);
    }
  }
  else {
    CORRUPTION_ERROR_ACTION(M);
  }
}

/* Unlink the first chunk from a smallbin */
ns_nonnull((1))
static ns_always_inline void unlink_first_small_chunk(
  mstate M, uintptr_t B, uintptr_t P, bindex_t I)
{
  const mchunkptr _P = swizzle(M, P);
  mchunkptr _B = swizzle(M, B);
  const uintptr_t F = _P->fd;
  mchunkptr _F = swizzle(M, F);
  assert(P != B);
  assert(P != F);
  assert(chunksize(M, P) == small_index2size(I));
  if (B == F) {
    clear_smallmap(M, I);
  }
  else if (RTCHECK(ok_address(M, F) && _F->bk == P)) {
    _F->bk = B;
    _B->fd = F;
  }
  else {
    CORRUPTION_ERROR_ACTION(M);
  }
}

/* Replace dv node, binning the old one */
/* Used only when dvsize known to be small */
ns_nonnull((1))
static ns_always_inline void replace_dv(mstate M, uintptr_t P, size_t S)
{
  size_t DVS = M->dvsize;
  assert(is_small(DVS));
  if (DVS != 0) {
    uintptr_t DV = M->dv;
    insert_small_chunk(M, DV, DVS);
  }
  M->dvsize = S;
  M->dv = P;
}

/* ------------------------- Operations on trees ------------------------- */

/* Insert chunk into tree */
ns_nonnull((1))
static void insert_large_chunk(mstate M, uintptr_t X, size_t S)
{
  tchunkptr _X = swizzle(M, X);
  const bindex_t I = compute_tree_index(S);
  tbinptr H = treebin_at(M, I);
  _X->index = I;
  _X->child[0] = _X->child[1] = 0;
  if (!treemap_is_marked(M, I)) {
    mark_treemap(M, I);
    *H = X;
    _X->parent = X;
    _X->fd = _X->bk = X;
  }
  else {
    uintptr_t T = *H;
    tchunkptr _T = swizzle(M, T);
    size_t K = S << leftshift_for_tree_index(I);
    for (;;) {
      if (chunksize(M, T) != S) {
        uintptr_t* C = &(_T->child[(K >> (SIZE_T_BITSIZE-SIZE_T_ONE)) & 1]);
        K <<= 1;
        if (*C != 0)
          T = *C;
        else if (RTCHECK(ok_address(M, *C))) {
          *C = X;
          _X->parent = T;
          _X->fd = _X->bk = X;
          break;
        }
        else {
          CORRUPTION_ERROR_ACTION(M);
          break;
        }
      }
      else {
        uintptr_t F = _T->fd;
        tchunkptr _F = swizzle(M, F);
        if (RTCHECK(ok_address(M, T) && ok_address(M, F))) {
          _T->fd = _F->bk = X;
          _X->fd = F;
          _X->bk = T;
          _X->parent = 0;
          break;
        }
        else {
          CORRUPTION_ERROR_ACTION(M);
          break;
        }
      }
    }
  }
}

/*
  Unlink steps:

  1. If x is a chained node, unlink it from its same-sized fd/bk links
     and choose its bk node as its replacement.
  2. If x was the last node of its size, but not a leaf node, it must
     be replaced with a leaf node (not merely one with an open left or
     right), to make sure that lefts and rights of descendents
     correspond properly to bit masks.  We use the rightmost descendent
     of x.  We could use any other leaf, but this is easy to locate and
     tends to counteract removal of leftmosts elsewhere, and so keeps
     paths shorter than minimally guaranteed.  This doesn't loop much
     because on average a node in a tree is near the bottom.
  3. If x is the base of a chain (i.e., has parent links) relink
     x's parent and children to x's replacement (or null if none).
*/
static ns_always_inline void unlink_large_chunk(mstate M, uintptr_t X)
{
  tchunkptr _X = swizzle(M, X);
  uintptr_t XP = _X->parent;
  uintptr_t R;
  if (_X->bk != X) {
    uintptr_t F = _X->fd;
    tchunkptr _F = swizzle(M, F);
    R = _X->bk;
    tchunkptr _R = swizzle(M, R);
    if (RTCHECK(ok_address(M, F) && _F->bk == X && _R->fd == X)) {
      _F->bk = R;
      _R->fd = F;
    }
    else {
      CORRUPTION_ERROR_ACTION(M);
    }
  }
  else {
    uintptr_t* RP;
    if (((R = *(RP = &(_X->child[1]))) != 0) ||
        ((R = *(RP = &(_X->child[0]))) != 0)) {
      uintptr_t* CP;
      tchunkptr _R = swizzle(M, R);
      while ((*(CP = &(_R->child[1])) != 0) ||
             (*(CP = &(_R->child[0])) != 0)) {
        R = *(RP = CP);
        _R = swizzle(M, R);
      }
      if (RTCHECK(ok_address(M, *RP)))
        *RP = 0;
      else {
        CORRUPTION_ERROR_ACTION(M);
      }
    }
  }
  if (XP != 0) {
    tbinptr H = treebin_at(M, _X->index);
    if (X == *H) {
      if ((*H = R) == 0)
        clear_treemap(M, _X->index);
    }
    else if (RTCHECK(ok_address(M, XP))) {
      tchunkptr _XP = swizzle(M, XP);
      if (_XP->child[0] == X)
        _XP->child[0] = R;
      else
        _XP->child[1] = R;
    }
    else
      CORRUPTION_ERROR_ACTION(M);
    if (R != 0) {
      tchunkptr _R = swizzle(M, R);
      if (RTCHECK(ok_address(M, R))) {
        uintptr_t C0, C1;
        _R->parent = XP;
        if ((C0 = _X->child[0]) != 0) {
          if (RTCHECK(ok_address(M, C0))) {
            _R->child[0] = C0;
            tchunkptr _C0 = swizzle(M, C0);
            _C0->parent = R;
          }
          else
            CORRUPTION_ERROR_ACTION(M);
        }
        if ((C1 = _X->child[1]) != 0) {
          if (RTCHECK(ok_address(M, C1))) {
            _R->child[1] = C1;
            tchunkptr _C1 = swizzle(M, C1);
            _C1->parent = R;
          }
          else
            CORRUPTION_ERROR_ACTION(M);
        }
      }
      else
        CORRUPTION_ERROR_ACTION(M);
    }
  }
}

/* Relays to large vs small bin operations */

ns_nonnull((1))
static ns_always_inline void insert_chunk(mstate M, uintptr_t P, size_t S)
{
  if (is_small(S))
    insert_small_chunk(M, P, S);
  else
    insert_large_chunk(M, P, S);
}

ns_nonnull((1))
static ns_always_inline void unlink_chunk(mstate M, uintptr_t P, size_t S)
{
  if (is_small(S))
    unlink_small_chunk(M, P, S);
  else
    unlink_large_chunk(M, P);
}


/* -------------------------- mspace management -------------------------- */

/* Initialize top chunk and its size */
static void init_top(mstate m, uintptr_t p, size_t psize) {
  /* Ensure alignment */
  size_t offset = align_offset(chunk2mem(p));
  p += offset;
  psize -= offset;

  m->top = p;
  m->topsize = psize;
  mchunkptr _p = swizzle(m, p);
  _p->head = psize | PINUSE_BIT;
  /* set size of fake trailing chunk holding overhead space only once */
  p = chunk_plus_offset(m, p, psize);
  _p = swizzle(m, p);
  _p->head = TOP_FOOT_SIZE;
  m->trim_check = mparams.trim_threshold; /* reset on each update */
}

/* Initialize bins for a new mstate that is otherwise zeroed out */
static void init_bins(mstate m) {
  /* Establish circular links for smallbins */
  for (bindex_t i = 0; i < NSMALLBINS; ++i) {
    uintptr_t bin = smallbin_at(m, i);
    sbinptr _bin = swizzle(m, bin);
    _bin->fd = _bin->bk = bin;
  }
}


/* ---------------------------- malloc --------------------------- */

/* allocate a large request from the best fitting chunk in a treebin */
static uint64_t tmalloc_large(mstate m, size_t nb) {
  uintptr_t v = 0;
  size_t rsize = -nb; /* Unsigned negation */
  uintptr_t t;
  bindex_t idx = compute_tree_index(nb);
  if ((t = *treebin_at(m, idx)) != 0) {
    /* Traverse tree for this bin looking for node with size == nb */
    size_t sizebits = nb << leftshift_for_tree_index(idx);
    uintptr_t rst = 0;  /* The deepest untaken right subtree */
    for (;;) {
      uintptr_t rt;
      size_t trem = chunksize(m, t) - nb;
      if (trem < rsize) {
        v = t;
        if ((rsize = trem) == 0)
          break;
      }
      tchunkptr _t = swizzle(m, t);
      rt = _t->child[1];
      t = _t->child[(sizebits >> (SIZE_T_BITSIZE-SIZE_T_ONE)) & 1];
      if (rt != 0 && rt != t)
        rst = rt;
      if (t == 0) {
        t = rst; /* set t to least subtree holding sizes > nb */
        break;
      }
      sizebits <<= 1;
    }
  }

  if (t == 0 && v == 0) { /* set t to root of next non-empty treebin */
    binmap_t leftbits = left_bits(idx2bit(idx)) & m->treemap;
    if (leftbits != 0) {
      binmap_t leastbit = least_bit(leftbits);
      bindex_t i = compute_bit2idx(leastbit);
      t = *treebin_at(m, i);
    }
  }

  while (t != 0) { /* find smallest of tree or subtree */
    size_t trem = chunksize(m, t) - nb;
    if (trem < rsize) {
      rsize = trem;
      v = t;
    }
    t = leftmost_child(m, t);
  }

  /* If dv is a better fit, return 0 so malloc will use it */
  if (v != 0 && rsize < (size_t)(m->dvsize - nb)) {
    if (RTCHECK(ok_address(m, v))) { /* split */
      uintptr_t r = chunk_plus_offset(m, v, nb);
      assert(chunksize(m, v) == rsize + nb);
      if (RTCHECK(ok_next(v, r))) {
        unlink_large_chunk(m, v);
        if (rsize < MIN_CHUNK_SIZE)
          set_inuse_and_pinuse(m, v, (rsize + nb));
        else {
          set_size_and_pinuse_of_inuse_chunk(m, v, nb);
          set_size_and_pinuse_of_free_chunk(m, r, rsize);
          insert_chunk(m, r, rsize);
        }
        return chunk2mem(v);
      }
    }
    CORRUPTION_ERROR_ACTION(m);
  }
  return 0;
}


/* allocate a small request from the best fitting chunk in a treebin */
static uintptr_t tmalloc_small(mstate m, size_t nb)
{
  uintptr_t t, v;
  size_t rsize;
  binmap_t leastbit = least_bit(m->treemap);
  const bindex_t i = compute_bit2idx(leastbit);
  v = t = *treebin_at(m, i);
  rsize = chunksize(m, t) - nb;

  while ((t = leftmost_child(m, t)) != 0) {
    size_t trem = chunksize(m, t) - nb;
    if (trem < rsize) {
      rsize = trem;
      v = t;
    }
  }

  if (RTCHECK(ok_address(m, v))) {
    uintptr_t r = chunk_plus_offset(m, v, nb);
    assert(chunksize(m, v) == rsize + nb);
    if (RTCHECK(ok_next(v, r))) {
      unlink_large_chunk(m, v);
      if (rsize < MIN_CHUNK_SIZE)
        set_inuse_and_pinuse(m, v, (rsize + nb));
      else {
        set_size_and_pinuse_of_inuse_chunk(m, v, nb);
        set_size_and_pinuse_of_free_chunk(m, r, rsize);
        replace_dv(m, r, rsize);
      }
      return chunk2mem(v);
    }
  }

  CORRUPTION_ERROR_ACTION(m);
  return 0;
}


/* ----------------------------- user mspaces ---------------------------- */

static mstate init_user_mstate(char* tbase, size_t tsize) {
  size_t msize = pad_request(sizeof(struct ns_arena));
  mchunkptr msp = align_as_chunk(tbase);
  mstate m = (mstate)(chunk2mem((char*)msp));
  memset(m, 0, msize);
  msp->head = (msize|INUSE_BITS);
  m->seg.base = tbase;
  m->seg.size = tsize;
  m->magic = mparams.magic;
  m->mflags = mparams.default_mflags;
  init_bins(m);
  /* Addresses and sizes are relative to mstate, not segment. */
  const size_t overhead = (uintptr_t)m - (uintptr_t)tbase;
  const uintptr_t p = msize - overhead;
  const size_t psize = (size_t)((tbase+tsize) - ((char*)msp+msize)) - (size_t)TOP_FOOT_SIZE;
  init_top(m, p, psize);
  check_top_chunk(m, m->top);
  return m;
}

ns_arena_t *ns_create_arena(void *base, size_t capacity)
{
  size_t msize;
  ensure_initialization();
  msize = pad_request(sizeof(ns_arena_t));
  if (capacity > msize + TOP_FOOT_SIZE &&
      capacity < (size_t) -(msize + TOP_FOOT_SIZE + mparams.page_size))
    return init_user_mstate((char*)base, capacity);
  return NULL;
}

void ns_destroy_arena(mstate ms)
{
  assert(ok_magic(ms));
  ms->magic = 0;
}

uintptr_t ns_arena_malloc(mstate ms, size_t bytes)
{
  if (!ok_magic(ms)) {
    USAGE_ERROR_ACTION(ms,ms);
    return 0;
  }

  uintptr_t mem;
  size_t nb;
  if (bytes <= MAX_SMALL_REQUEST) {
    bindex_t idx;
    binmap_t smallbits;
    nb = (bytes < MIN_REQUEST)? MIN_CHUNK_SIZE : pad_request(bytes);
    idx = small_index(nb);
    smallbits = ms->smallmap >> idx;

    if ((smallbits & 0x3U) != 0) { /* Remainderless fit to a smallbin. */
      idx += ~smallbits & 1;       /* Uses next bin if idx empty */
      uintptr_t b = smallbin_at(ms, idx);
      mchunkptr _b = swizzle(ms, b);
      uintptr_t p = _b->fd;
      assert(chunksize(ms, p) == small_index2size(idx));
      unlink_first_small_chunk(ms, b, p, idx);
      set_inuse_and_pinuse(ms, p, small_index2size(idx));
      mem = chunk2mem(p);
      check_malloced_chunk(ms, mem, nb);
      goto postaction;
    }

    else if (nb > ms->dvsize) {
      if (smallbits != 0) { /* Use chunk in next nonempty smallbin */
        binmap_t leftbits = (smallbits << idx) & left_bits(idx2bit(idx));
        binmap_t leastbit = least_bit(leftbits);
        bindex_t i = compute_bit2idx(leastbit);
        uintptr_t b = smallbin_at(ms, i);
        uintptr_t p = next_chunk(ms, b);
        assert(chunksize(ms, p) == small_index2size(i));
        unlink_first_small_chunk(ms, b, p, i);
        size_t rsize = small_index2size(i) - nb;
        /* Fit here cannot be remainderless if 4byte sizes */
        if (SIZE_T_SIZE != 4 && rsize < MIN_CHUNK_SIZE)
          set_inuse_and_pinuse(ms, p, small_index2size(i));
        else {
          set_size_and_pinuse_of_inuse_chunk(ms, p, nb);
          uintptr_t r = chunk_plus_offset(ms, p, nb);
          set_size_and_pinuse_of_free_chunk(ms, r, rsize);
          replace_dv(ms, r, rsize);
        }
        mem = chunk2mem(p);
        check_malloced_chunk(ms, mem, nb);
        goto postaction;
      }

      else if (ms->treemap != 0 && (mem = tmalloc_small(ms, nb)) != 0) {
        check_malloced_chunk(ms, mem, nb);
        goto postaction;
      }
    }
  }
  else if (bytes >= MAX_REQUEST)
    nb = MAX_SIZE_T; /* Too big to allocate. Force failure (in sys alloc) */
  else {
    nb = pad_request(bytes);
    if (ms->treemap != 0 && (mem = tmalloc_large(ms, nb)) != 0) {
      check_malloced_chunk(ms, mem, nb);
      goto postaction;
    }
  }

  if (nb <= ms->dvsize) {
    size_t rsize = ms->dvsize - nb;
    uintptr_t p = ms->dv;
    if (rsize >= MIN_CHUNK_SIZE) { /* split dv */
      uintptr_t r = ms->dv = chunk_plus_offset(ms, p, nb);
      ms->dvsize = rsize;
      set_size_and_pinuse_of_free_chunk(ms, r, rsize);
      set_size_and_pinuse_of_inuse_chunk(ms, p, nb);
    }
    else { /* exhaust dv */
      size_t dvs = ms->dvsize;
      ms->dvsize = 0;
      ms->dv = 0;
      set_inuse_and_pinuse(ms, p, dvs);
    }
    mem = chunk2mem(p);
    check_malloced_chunk(ms, mem, nb);
    goto postaction;
  }

  else if (nb < ms->topsize) { /* Split top */
    size_t rsize = ms->topsize -= nb;
    uintptr_t p = ms->top;
    uintptr_t r = ms->top = chunk_plus_offset(ms, p, nb);
    ((mchunkptr)swizzle(ms, r))->head = rsize | PINUSE_BIT;
    set_size_and_pinuse_of_inuse_chunk(ms, p, nb);
    mem = chunk2mem(p);
    check_top_chunk(ms, ms->top);
    check_malloced_chunk(ms, mem, nb);
    goto postaction;
  }

  // no memory available in arena
  return 0;

postaction:
  return mem;
}

void ns_arena_free(mstate ms, uintptr_t mem)
{
  if (!mem)
    return;

  uintptr_t p  = mem2chunk(mem);
  mstate fm = get_mstate_for(ms, p);
  assert(ms == fm);

  if (!ok_magic(fm)) {
    USAGE_ERROR_ACTION(fm, p);
    return;
  }

  check_inuse_chunk(fm, p);
  if (RTCHECK(ok_address(fm, p) && ok_inuse(fm, p))) {
    size_t psize = chunksize(fm, p);
    uintptr_t next = chunk_plus_offset(fm, p, psize);
    if (!pinuse(fm, p)) {
      mchunkptr _p = swizzle(fm, p);
      size_t prevsize = _p->prev_foot;
      uintptr_t prev = chunk_minus_offset(fm, p, prevsize);
      psize += prevsize;
      p = prev;
      if (RTCHECK(ok_address(fm, prev))) { /* consolidate backward */
        if (p != fm->dv) {
          unlink_chunk(fm, p, prevsize);
        }
        else if ((((mchunkptr)swizzle(fm, next))->head & INUSE_BITS) == INUSE_BITS) {
          fm->dvsize = psize;
          set_free_with_pinuse(fm, p, psize, next);
          goto postaction;
        }
      }
      else
        goto erroraction;
    }

    if (RTCHECK(ok_next(p, next) && ok_pinuse(fm, next))) {
      if (!cinuse(fm, next)) {  /* consolidate forward */
        if (next == fm->top) {
          size_t tsize = fm->topsize += psize;
          fm->top = p;
          mchunkptr _p = swizzle(fm, p);
          _p->head = tsize | PINUSE_BIT;
          if (p == fm->dv) {
            fm->dv = 0;
            fm->dvsize = 0;
          }
          goto postaction;
        }
        else if (next == fm->dv) {
          size_t dsize = fm->dvsize += psize;
          fm->dv = p;
          set_size_and_pinuse_of_free_chunk(fm, p, dsize);
          goto postaction;
        }
        else {
          size_t nsize = chunksize(fm, next);
          psize += nsize;
          unlink_chunk(fm, next, nsize);
          set_size_and_pinuse_of_free_chunk(fm, p, psize);
          if (p == fm->dv) {
            fm->dvsize = psize;
            goto postaction;
          }
        }
      }
      else
        set_free_with_pinuse(fm, p, psize, next);

      if (is_small(psize)) {
        insert_small_chunk(fm, p, psize);
        check_free_chunk(fm, p);
      }
      else {
        insert_large_chunk(fm, p, psize);
        check_free_chunk(fm, p);
      }
      goto postaction;
    }
  }
erroraction:
  USAGE_ERROR_ACTION(fm, p);
postaction:
}

#if 0
void* mspace_calloc(mspace msp, size_t n_elements, size_t elem_size) {
  void* mem;
  size_t req = 0;
  mstate ms = (mstate)msp;
  if (!ok_magic(ms)) {
    USAGE_ERROR_ACTION(ms,ms);
    return 0;
  }
  if (n_elements != 0) {
    req = n_elements * elem_size;
    if (((n_elements | elem_size) & ~(size_t)0xffff) &&
        (req / n_elements != elem_size))
      req = MAX_SIZE_T; /* force downstream failure on overflow */
  }
  mem = internal_malloc(ms, req);
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    memset(mem, 0, req);
  return mem;
}

void* mspace_realloc(mspace msp, void* oldmem, size_t bytes) {
  void* mem = 0;
  if (oldmem == 0) {
    mem = mspace_malloc(msp, bytes);
  }
  else if (bytes >= MAX_REQUEST) {
    MALLOC_FAILURE_ACTION;
  }
#ifdef REALLOC_ZERO_BYTES_FREES
  else if (bytes == 0) {
    mspace_free(msp, oldmem);
  }
#endif /* REALLOC_ZERO_BYTES_FREES */
  else {
    size_t nb = request2size(bytes);
    mchunkptr oldp = mem2chunk(oldmem);
#if ! FOOTERS
    mstate m = (mstate)msp;
#else /* FOOTERS */
    mstate m = get_mstate_for(oldp);
    if (!ok_magic(m)) {
      USAGE_ERROR_ACTION(m, oldmem);
      return 0;
    }
#endif /* FOOTERS */
    if (!PREACTION(m)) {
      mchunkptr newp = try_realloc_chunk(m, oldp, nb, 1);
      POSTACTION(m);
      if (newp != 0) {
        check_inuse_chunk(m, newp);
        mem = chunk2mem(newp);
      }
      else {
        mem = mspace_malloc(m, bytes);
        if (mem != 0) {
          size_t oc = chunksize(oldp) - overhead_for(oldp);
          memcpy(mem, oldmem, (oc < bytes)? oc : bytes);
          mspace_free(m, oldmem);
        }
      }
    }
  }
  return mem;
}
#endif
