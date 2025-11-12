/*
 * macros.h -- compiler macro abstractions
 *
 * Copyright (c) 2025, Jeroen Koekkoek
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */
#ifndef NS_MACROS_H
#define NS_MACROS_H

#if defined __has_attribute
# define ns_has_attribute(x) __has_attribute(x)
#else
# define ns_has_attribute(x) (0)
#endif

#if defined __has_builtin
# define ns_has_builtin(x) __has_builtin(x)
#else
# define ns_has_builtin(x) (0)
#endif

#if ns_has_builtin(__builtin_expect)
# define ns_likely(x) __builtin_expect(!!(x), 1)
# define ns_unlikely(x) __builtin_expect(!!(x), 0)
#endif

#if ns_has_attribute(nonnull)
# define ns_nonnull(x) __attribute__((__nonnull__ x))
# define ns_nonnull_all __attribute__((__nonnull__))
#else
# define ns_nonnull(x)
# define ns_nonnull_all
#endif

#if defined __GNUC__
# define ns_have_gnuc(major, minor) \
((__GNUC__ > major) || (__GNUC__ == major && __GNUC_MINORE__ >= minor))
#else
# define ns_have_gnuc(major, minor) (0)
#endif

#if _MSC_VER
# define ns_always_inline __forceinline
# define ns_never_inline __declspec(noinline)
#else // _MSC_VER
# if (ns_has_attribute(always_inline) || ns_have_gnuc(3, 1)) && ! defined(__NO_INLINE__)
  // Compilation using GCC 4.2.1 without optimizations failes.
  //   sorry, unimplemented: inlining failed in call to ...
  // GCC 4.1.2 and GCC 4.30 compile forward declared functions annotated
  // with __attribute__((always_inline)) without problems. Test if
  // __NO_INLINE__ is defined and define macro accordingly.
#   define ns_always_inline inline __attribute__((always_inline))
# else
#   define ns_always_inline inline
# endif

# if ns_has_attribute(noinline) || ns_have_gnuc(2, 96)
#   define ns_never_inline __attribute__((noinline))
# else
#   define ns_never_inline
# endif
#endif

#if ns_has_attribute(returns_nonnull)
# define ns_returns_nonnull __attribute__((returns_nonnull))
#else
# define ns_returns_nonnull
#endif

#if ns_has_attribute(unused)
# define ns_maybe_unused __attribute__((unused))
#else
# define ns_maybe_unused
#endif

#if ns_has_attribute(warn_unused_result)
# define ns_nodiscard __attribute__((warn_unused_result))
#else
# define ns_nodiscard
#endif

#endif // NS_MACROS_H
