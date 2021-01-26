#include "nuke.h"

#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <stdnoreturn.h>
#include <stdlib.h>

#if DEBUG
#define ASSERT(_what, _msg)                                     \
    do {                                                        \
        if (!(_what)) assertion_abort(__func__, #_what, _msg);  \
    } while (0)

_Noreturn void assertion_abort(const char *func,
                               const char *expr,
                               const char *msg)
{
    printf("[DEFCON-1] %s: %s !(%s)\n", func, msg, expr);
    // TODO: Print backtrace
    abort();
}
#else
#define ASSERT(_what, _msg)
#endif

#define WARN_IF(_what, _msg)                                \
    do {                                                    \
        if (_what) assertion_warn(__func__, #_what, _msg);  \
    } while (0)

static void assertion_warn(const char *func,
                           const char *expr,
                           const char *msg) {
    printf("[DEFCON-3] %s: %s (%s)\n", func, msg, expr);
}

#define PANIC_IF(_what, _msg)                           \
    do {                                                \
        if (_what) nk_panic(__func__, #_what, _msg);    \
    } while (0)

_Noreturn static void nk_panic(const char *func,
                               const char *expr,
                               const char *msg) {
  printf("[DEFCON-0] %s: %s (%s)\n", func, msg, expr);
  abort();
}

static inline size_t max_sz(size_t u, size_t v)
{
    return (u > v) ? u : v;
}

static inline NkAtom *fst(Nuke *nk)
{
    return (NkAtom *) &nk->mem[0];
}

static inline void *align(void *p, intptr_t a)
{
    return (void *) ((((intptr_t) p) + a - 1) & ~(a - 1));
}

static inline NkRelocArray *new_reloc(size_t len)
{
    NkRelocArray *arr;
    size_t sz = sizeof(NkRelocArray) + len*sizeof(arr->elems[0]);
    PANIC_IF((arr = malloc(sz)) == NULL,
             "Relocation array allocation failed.");
    arr->capacity = len;
    arr->length = 0;
    return arr;
}

static inline size_t min_reloc_len(Nuke *nk)
{
    ASSERT(nk != NULL, "null check");

    size_t min_block_sz = sizeof(NkAtom) + nk->min_block_sz;
    return 1 + nk->used / min_block_sz;
}

static inline size_t max_reloc_len(Nuke *nk)
{
    ASSERT(nk != NULL, "null check");

    size_t min_block_sz = sizeof(NkAtom) + nk->min_block_sz;
    return 1 + nk->sz / min_block_sz;
}

static inline void reset_reloc(Nuke *nk)
{
    ASSERT(nk != NULL, "null check");
    ASSERT(nk->reloc, "NkRelocArray missing.");

    nk->reloc->length = 0;
}

static inline NkRelocArray *init_reloc(Nuke *nk)
{
    ASSERT(nk != NULL, "null check");

    size_t min_len = min_reloc_len(nk);
    size_t max_len = max_reloc_len(nk);
    if (nk->reloc != NULL) {
        if (nk->reloc->capacity < min_len) {
            free(nk->reloc);
        } else {
            reset_reloc(nk);
            return nk->reloc;
        }
    }
    return nk->reloc = new_reloc(max_len);
}

static inline void push_reloc(NkRelocArray *restrict reloc,
                              void *restrict from,
                              void *restrict to)
{
    ASSERT(reloc != NULL, "null check");
    ASSERT(reloc->length < reloc->capacity, "NkRelocArray overflow.");

    size_t idx = reloc->length++;
    reloc->elems[idx].fst = from;
    reloc->elems[idx].snd = to;
}

static inline Nuke *nk_copy(Nuke *nk, size_t sz)
{
    ASSERT(nk != NULL, "null check");
    ASSERT(nk->used < sz, "New nk not big enough to hold copy.");

    Nuke *nar = malloc(sizeof(Nuke) + sz);
    PANIC_IF(nar == NULL, "malloc error when allocating new nuke");
    memcpy(nar, nk, sizeof(Nuke));
    nar->sz = sz;
    nar->load_max = (size_t) (nar->load_factor * sz);
    NkRelocArray *reloc = init_reloc(nar);
    nk->reloc = NULL;

    #if DEBUG
    size_t used = 0, num_atoms = 0;
    #endif

    char *mem = &nar->mem[0];
    NkAtom *new_node;
    for (NkAtom *node = fst(nk); node != NULL; node = node->next) {
        size_t sz = sizeof(NkAtom) + node->sz;
        memcpy(mem, node, sz);
        push_reloc(reloc, node, new_node = (NkAtom *) mem);
        new_node->next = (NkAtom *) (mem = align(mem + sz, ALIGNMENT));

        #if DEBUG
        used += sz;
        num_atoms++;
        #endif
    }

    nar->has_relocated = 1;
    nar->free = mem;
    new_node->next = NULL;
    nar->last = new_node;

    ASSERT(num_atoms == nk->num_atoms, "Number of atoms did not match");
    ASSERT(used == nk->used, "Usage count did not match");

    return nar;
}

void nk_sweep_compact(Nuke *restrict nk)
{
    NkRelocArray *restrict reloc = init_reloc(nk);
    char *start = &nk->mem[0];
    NkAtom *node = fst(nk),
           *npos = fst(nk);

    for (;;) {
        NkAtom *next_node;

        {
            NkAtom *restrict n;
            size_t num_frees = 0;
            for (n = node->next; n != NULL; n = n->next) {
                if (n->meta.color == COLOR_WHITE) {
                    nk_destroy_atom(n);
                    nk->used -= sizeof(NkAtom) + n->sz;
                    num_frees++;
                } else {
                    break;
                }
            }
            nk->num_atoms -= num_frees;
            nk->num_frees += num_frees;
            next_node = n;
        }

        size_t sz = sizeof(*node) + node->sz;
        npos = (NkAtom *) start;

        if (npos != node) {
            push_reloc(reloc, node, npos);
            memcpy(npos, node, sz);
        }

        npos->meta.color = COLOR_WHITE;
        start = align(start + sz, ALIGNMENT);

        if (next_node != NULL) {
            npos->next = (NkAtom *) start;
            node = next_node;
        } else {
            npos->next = NULL;
            break;
        }
    }

    nk->last = npos;
    fst(nk)->meta.color = COLOR_BLACK;
    nk->free = start;
    nk->has_relocated = 1;
}

void nk_compact(Nuke *nk)
{
    ASSERT(nk != NULL, "null check");

    NkRelocArray *reloc = init_reloc(nk);
    NkAtom *node = fst(nk),
           *npos;
    char *start = &nk->mem[0];

    for (;;) {
        NkAtom *next_node = node->next;
        npos = (NkAtom *) start;
        size_t sz = sizeof(*node) + node->sz;
        if (npos != node) {
            push_reloc(reloc, node, npos);
            // The memory segments **can be overlapping**, but we're always
            // shifting backwards, so we don't need to use `memmove`.
            memcpy(npos, node, sz);
        }
        start = align(start + sz, ALIGNMENT);
        if (next_node != NULL) {
            npos->next = (NkAtom *) start;
            node = next_node;
        } else {
            break;
        }
    }

    nk->last = npos;
    nk->free = start;
    nk->has_relocated = 1;
}

Nuke *nk_new(size_t sz, NkSz min, double load_factor)
{
    ASSERT(min > 0, "Minimum allocation size cannot be 0.");
    ASSERT(sz >= MINIMUM_NK_SIZE, "Nuke too small");
    ASSERT(load_factor >= 0.5 && load_factor < 1.0,
           "Load factor outside of [0.5, 1.0) range.");

    Nuke *nk = malloc(sizeof(Nuke) + sz);
    PANIC_IF(nk == NULL, "Failed to allocate nuke");

    nk->load_factor = load_factor;
    nk->load_max = (size_t) (load_factor * sz);
    nk->grow_num = sz;
    nk->min_block_sz = min;
    nk->reloc = NULL;
    nk->sz = sz;
    nk->has_relocated = 0;
    nk->num_frees = 0;
    nk->num_allocs = 0;
    nk->last = fst(nk);

    // Set up implicit first block
    nk->free = &nk->mem[sizeof(NkAtom)];
    nk->used = sizeof(NkAtom);
    memset(&nk->mem[0], '\0', sizeof(NkAtom));
    fst(nk)->meta.color = COLOR_BLACK;
    nk->num_atoms = 1;

    return nk;
}

void nk_destroy(Nuke *nk)
{
    ASSERT(nk != NULL, "null check");

    if (nk->reloc != NULL) {
        free(nk->reloc);
    }
    free(nk);
}

Nuke *nk_make_room(Nuke *nk, size_t fit)
{
    ASSERT(nk != NULL, "null check");

    if (nk->used + sizeof(NkAtom) + fit > nk->load_max) {
        size_t new_sz = max_sz(nk->sz << 1,
                               nk->sz + fit + sizeof(NkAtom));
        Nuke *nnk = nk_copy(nk, new_sz);
        nk_destroy(nk);
        return nnk;
    }

    nk_compact(nk);
    return nk;
}

const NkRelocArray *nk_check_relocation(Nuke *nk)
{
    return (nk->has_relocated) ? nk->reloc : NULL;
}

void nk_confirm_relocation(Nuke *nk)
{
    WARN_IF(!nk->has_relocated, "Unnecessary confirmation");
    ASSERT(nk->reloc != NULL, "Relocation array missing.");

    nk->has_relocated = 0;
    reset_reloc(nk);
}

void *nk_alloc(Nuke *nk, NkSz sz, uint8_t ty)
{
    size_t full_sz = sz + sizeof(NkAtom);

    ASSERT(sz >= nk->min_block_sz, "Allocation request smaller than specified minimum.");
    ASSERT(ty < 64, "Type number will not fit in 6 bits.");

    // Check if a re-allocation/compacting is necessary
    char *free = align(nk->free, ALIGNMENT);
    if (free + full_sz >= &nk->mem[nk->sz]) {
        return NULL;
    }

    ASSERT(nk->used + full_sz <= nk->sz, "Overflow");
    NkAtom *cur = (NkAtom *) free;

    NkAtom *last = nk->last;
    nk->last = cur;

    nk->free = ((char *) cur) + full_sz;
    nk->used += full_sz;
    nk->num_atoms++;
    nk->num_allocs++;

    cur->next = NULL;
    cur->sz = sz;
    cur->meta.color = COLOR_BLACK;
    cur->meta.typ = ty;

    last->next = cur;

    return ((char *) cur) + sizeof(NkAtom);
}

NkAtom *nk_gc_cycle_head(Nuke *nk)
{
    // NOTE: For now, we just return the first non-empty block, but later on
    //       we can implement fancy generational GC features (after a few
    //       compact()s)
    return nk_head(nk);
}

NkAtom *nk_head(Nuke *nk)
{
    return fst(nk)->next;
}

void nk_print(Nuke *nk)
{
    printf("Nuke: {\n");
    printf("  sz: %ld\n", nk->sz);
    printf("  used: %ld\n", nk->used);
    printf("  mem: {\n");
    for (NkAtom *node = fst(nk); node != NULL; node = node->next) {
        char *end = ((char *) node) + sizeof(NkAtom) + node->sz;
        printf("    NkAtom: {\n");
        printf("      start: %p\n", (void *) node);
        printf("      end: %p\n", (void *) end);
        printf("      next: %p\n", (void *) node->next);
        printf("      diff: %ld\n", (node->next) ? ((char *) node->next) - end : 0);
        printf("      sz: %d\n", (int) node->sz);
        printf("      mem: {\n");
        printf("        ");
        for (size_t i = 0; i < node->sz; i++) {
            printf("%02x ", node->mem[i] & 0xff);
            if ((i+1) % 10 == 0) {
                printf("\n        ");
            }
        }
        printf("\n");
        printf("      }\n");
        printf("    }\n");
    }
    printf("  }\n");
    printf("}\n");
}
