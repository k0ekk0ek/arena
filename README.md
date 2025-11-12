# dlmalloc modified to hand out relative addresses

An modified version of Doug Lea's excelent mspace allocator.

An upcoming project requires an allocator that hands out addresses relative
to a contiguous memory segment. While, for this particular project, a variant
of the slab allocator seems like the best fit (pun intended) and the
Two-Level Segregated Fit (TLSF) allocator a simpler alternative, both
introduce a lot of bookkeeping overhead for many small segments.

__!!DO NOT USE IN PRODUCTION!!__
