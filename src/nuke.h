/*
** The Nuclear Allocator
*/

#ifndef __NUKE_H_
#define __NUKE_H_

#if __STDC_VERSION__ < 201112L
#  ifdef _MSC_VER
#    warning "_Noreturn not available, you will see spurious compiler warnings."
#    define _Noreturn
#  else
#    define _Noreturn __attribute__((noreturn))
#  endif
#endif

#include <stdint.h>
#include <stddef.h>

#define pub
#define MINIMUM_NK_SIZE 128
#define ALIGNMENT 8
#define PAIR_T(_T) Pair##_T
#define DEF_PAIR(_T)                                                    \
    typedef struct PAIR_T(_T) {                                         \
        _T fst;                                                         \
        _T snd;                                                         \
    } PAIR_T(_T);

typedef void* VoidP;
DEF_PAIR(VoidP)

typedef uint16_t NkSz;

pub enum NkColor {
    COLOR_WHITE = 0,
    COLOR_GRAY = 1,
    COLOR_BLACK = 2,
};

pub typedef struct NkAtomMeta {
    pub uint8_t color : 2;
    pub uint8_t typ : 6;
} NkAtomMeta;

pub typedef struct NkAtom {
    pub NkSz sz;
    pub NkAtomMeta meta;
    pub struct NkAtom *next;
    char mem[];
} NkAtom;

pub typedef struct NkRelocArray {
    size_t capacity;
    pub size_t length;
    pub PAIR_T(VoidP) elems[];
} NkRelocArray;

pub typedef struct Nuke {
    char *free;
    size_t grow_num;
    size_t used;
    size_t num_frees;
    size_t num_allocs;
    size_t num_atoms;
    double load_factor;
    size_t load_max;
    NkSz min_block_sz;
    size_t sz;
    uint8_t has_relocated : 1;
    NkRelocArray *reloc;
    NkAtom *last;
    char mem[];
} Nuke;

/**
 * Create a new nuclear allocator of a certain size.
 *
 * @param sz The size of the nk in bytes, and the growth number.
 * @param min The minimum size of blocks you intend to allocate.
 * @param max The maximum size of blocks you intend to allocate.
 * @param load_factor A number in the range [0.0, 1.0] representing the
 *                    amount of memory that can be in use without
 *                    performing a re-allocation during compacting.
 * @return Newly allocated nk, or NULL iff there was an error.
 */
Nuke *nk_new(size_t sz, NkSz min, double load_factor);

/**
 * Deallocate the entire nk.
 */
void nk_destroy(Nuke *nk);

/**
 * Allocate a new block.
 *
 * @return The newly allocated block, or NULL iff there is no space left.
 *
 * If NULL is returned, do the following:
 * 1. Call nk_make_room(Nuke*).
 * 2. Call check_relocation to retrieve the relocated pointers.
 * 3. Update pointers.
 * 4. Call confirm_relocation to reset the relocation array.
 */
void *nk_alloc(Nuke *nk, NkSz sz, uint8_t ty);

/**
 * Compact nk memory, such that there are no empty gaps.
 */
void nk_compact(Nuke *nk);

/**
 * Get the head from which to start a mark-cycle.
 */
NkAtom *nk_gc_cycle_head(Nuke *nk);

/**
 * Get the head block of the nuke.
 */
NkAtom *nk_head(Nuke *nk);

/**
 * Format and print human-readable nk layout to stdout.
 */
void nk_print(Nuke *nk);

/**
 * Make room for more stuff in the Nuke.
 *
 * @return The nuke, or NULL iff there was an error.
 *
 * Note: You'll probably want to panic if this function returns NULL.
 */
Nuke *nk_make_room(Nuke *nk, size_t fit);

/**
 * Check if blocks have been relocated (i.e shifted around.)
 *
 * @returns An array of pairs where (fst, snd) = (original pointer, new pointer)
 */
const NkRelocArray *nk_check_relocation(Nuke *nk);

/**
 * Confirm that the relocation has been handled, by updating pointers
 * to their new values.
 */
void nk_confirm_relocation(Nuke *nk);

/**
 * Compact nk memory, such that there are no empty gaps,
 * the compacting process is perfored during a sweep where
 * NkColor::COLOR_WHITE objects are deallocated.
 */
void nk_sweep_compact(Nuke *nk);

extern void nk_destroy_atom(NkAtom *p);

#endif // __NUKE_H_
