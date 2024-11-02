#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <string.h>
#include <time.h>

// Constants
#define AIR 0x00
#define VAR 0x01
#define SUB 0x02
#define NUL 0x03
#define ERA 0x04
#define LAM 0x05
#define APP 0x06
#define SUP 0x07
#define DUP 0x08

#define VOID 0x0
#define RBAG 0x100000000

// Types

typedef uint64_t u64;
typedef _Atomic(u64) a64;

typedef struct {
  a64* buff;
  u64 rnod_ini;
  u64 rnod_end;
  u64 rbag_ini;
  u64 rbag_end;
} RHeap;

// Term operations

static inline u64 new_term(u64 tag, u64 lab, u64 loc) {
  return tag | (lab << 8) | (loc << 32);
}

static inline u64 get_tag(u64 term) {
  return term & 0xFF;
}

static inline u64 get_lab(u64 term) {
  return (term >> 8) & 0xFFFFFF;
}

static inline u64 get_loc(u64 term) {
  return (term >> 32) & 0xFFFFFFFF;
}

static inline u64 port(u64 n, u64 x) {
  return n + x;
}

// Memory operations

static inline u64 swap(RHeap* heap, u64 loc, u64 term) {
  return atomic_exchange_explicit(&heap->buff[loc], term, memory_order_relaxed);
}

static inline u64 get(RHeap* heap, u64 loc) {
  return atomic_load_explicit(&heap->buff[loc], memory_order_relaxed);
}

static inline void set(RHeap* heap, u64 loc, u64 term) {
  atomic_store_explicit(&heap->buff[loc], term, memory_order_relaxed);
}

// Allocation
static inline u64 alloc_rnod(RHeap* heap, u64 arity) {
  u64 loc = heap->rnod_end;
  heap->rnod_end += arity;
  return loc;
}

static inline u64 alloc_redex(RHeap* heap) {
  u64 loc = heap->rbag_end;
  heap->rbag_end += 2;
  return RBAG + loc;
}

static inline int next_redex(RHeap* heap, u64* loc) {
  if (heap->rbag_ini < heap->rbag_end) {
    *loc = RBAG + heap->rbag_ini;
    heap->rbag_ini += 2;
    return 1;
  }
  return 0;
}

// Linking
static void move(RHeap* heap, u64 neg_loc, u64 pos);

static void link(RHeap* heap, u64 neg, u64 pos) {
  if (get_tag(pos) == VAR) {
    u64 far = swap(heap, get_loc(pos), neg);
    if (get_tag(far) != SUB) {
      move(heap, get_loc(pos), far);
    }
  } else {
    u64 loc = alloc_redex(heap);
    set(heap, loc + 0, neg);
    set(heap, loc + 1, pos);
  }
}

static void move(RHeap* heap, u64 neg_loc, u64 pos) {
  u64 neg = swap(heap, neg_loc, pos);
  if (get_tag(neg) != SUB) {
    link(heap, neg, pos);
  }
}

// Interaction
static void interact(RHeap* heap, u64 a, u64 b) {
  u64 a_tag = get_tag(a);
  u64 a_lab = get_lab(a);
  u64 a_loc = get_loc(a);
  u64 b_tag = get_tag(b);
  u64 b_lab = get_lab(b);
  u64 b_loc = get_loc(b);
  switch (a_tag) {
    case APP:
      switch (b_tag) {
        case LAM: {
          u64 arg = swap(heap, port(1, a_loc), VOID);
          u64 ret = port(2, a_loc);
          u64 var = port(1, b_loc);
          u64 bod = swap(heap, port(2, b_loc), VOID);
          move(heap, var, arg);
          move(heap, ret, bod);
          break;
        }
        case SUP: {
          u64 arg = swap(heap, port(1, a_loc), VOID);
          u64 ret = port(2, a_loc);
          u64 tm1 = swap(heap, port(1, b_loc), VOID);
          u64 tm2 = swap(heap, port(2, b_loc), VOID);
          u64 dp1 = alloc_rnod(heap, 3);
          u64 dp2 = alloc_rnod(heap, 3);
          u64 cn1 = alloc_rnod(heap, 3);
          u64 cn2 = alloc_rnod(heap, 3);
          set(heap, port(1, dp1), new_term(SUB, 0, port(1, dp1)));
          set(heap, port(2, dp1), new_term(SUB, 0, port(2, dp1)));
          set(heap, port(1, dp2), new_term(VAR, 0, port(2, cn1)));
          set(heap, port(2, dp2), new_term(VAR, 0, port(2, cn2)));
          set(heap, port(1, cn1), new_term(VAR, 0, port(1, dp1)));
          set(heap, port(2, cn1), new_term(SUB, 0, port(2, cn1)));
          set(heap, port(1, cn2), new_term(VAR, 0, port(2, dp1)));
          set(heap, port(2, cn2), new_term(SUB, 0, port(2, cn2)));
          link(heap, new_term(DUP, 0, dp1), arg);
          move(heap, ret, new_term(SUP, 0, dp2));
          link(heap, new_term(APP, 0, cn1), tm1);
          link(heap, new_term(APP, 0, cn2), tm2);
          break;
        }
        case NUL: {
          u64 arg = swap(heap, port(1, a_loc), VOID);
          u64 ret = port(2, a_loc);
          link(heap, new_term(ERA, 0, 0), arg);
          move(heap, ret, new_term(NUL, 0, 0));
          break;
        }
      }
      break;
    case DUP:
      switch (b_tag) {
        case SUP: {
          u64 dp1 = port(1, a_loc);
          u64 dp2 = port(2, a_loc);
          u64 tm1 = swap(heap, port(1, b_loc), VOID);
          u64 tm2 = swap(heap, port(2, b_loc), VOID);
          move(heap, dp1, tm1);
          move(heap, dp2, tm2);
          break;
        }
        case LAM: {
          u64 dp1 = port(1, a_loc);
          u64 dp2 = port(2, a_loc);
          u64 var = port(1, b_loc);
          u64 bod = swap(heap, port(2, b_loc), VOID);
          u64 co1 = alloc_rnod(heap, 3);
          u64 co2 = alloc_rnod(heap, 3);
          u64 du1 = alloc_rnod(heap, 3);
          u64 du2 = alloc_rnod(heap, 3);
          set(heap, port(1, co1), new_term(SUB, 0, port(1, co1)));
          set(heap, port(2, co1), new_term(VAR, 0, port(1, du2)));
          set(heap, port(1, co2), new_term(SUB, 0, port(1, co2)));
          set(heap, port(2, co2), new_term(VAR, 0, port(2, du2)));
          set(heap, port(1, du1), new_term(VAR, 0, port(1, co1)));
          set(heap, port(2, du1), new_term(VAR, 0, port(1, co2)));
          set(heap, port(1, du2), new_term(SUB, 0, port(1, du2)));
          set(heap, port(2, du2), new_term(SUB, 0, port(2, du2)));
          move(heap, dp1, new_term(LAM, 0, co1));
          move(heap, dp2, new_term(LAM, 0, co2));
          move(heap, var, new_term(SUP, 0, du1));
          link(heap, new_term(DUP, 0, du2), bod);
          break;
        }
        case NUL: {
          u64 dp1 = port(1, a_loc);
          u64 dp2 = port(2, a_loc);
          move(heap, dp1, new_term(NUL, 0, 0));
          move(heap, dp2, new_term(NUL, 0, 0));
          break;
        }
      }
      break;
    case ERA:
      switch (b_tag) {
        case LAM: {
          u64 var = port(1, b_loc);
          u64 bod = swap(heap, port(2, b_loc), VOID);
          move(heap, var, new_term(NUL, 0, 0));
          link(heap, new_term(ERA, 0, 0), bod);
          break;
        }
        case SUP: {
          u64 tm1 = swap(heap, port(1, b_loc), VOID);
          u64 tm2 = swap(heap, port(2, b_loc), VOID);
          link(heap, new_term(ERA, 0, 0), tm1);
          link(heap, new_term(ERA, 0, 0), tm2);
          break;
        }
        case NUL:
          break;
      }
      break;
  }
}

// Evaluation
static int eval_one(RHeap* heap) {
  u64 loc;
  if (next_redex(heap, &loc)) {
    u64 neg = get(heap, loc + 0);
    u64 pos = get(heap, loc + 1);
    set(heap, loc + 0, VOID);
    set(heap, loc + 1, VOID);
    interact(heap, neg, pos);
    return 1;
  }
  return 0;
}

static void eval_strict(RHeap* heap) {
  while (eval_one(heap));
}

int main() {
  // Allocate heap with 2^33 elements
  a64* buff = calloc((1ULL << 33), sizeof(a64));

  // TODO: mark the initial time
  struct timespec start;
  clock_gettime(CLOCK_MONOTONIC, &start);

  RHeap heap;
  heap.buff = buff;

  heap.buff[0x000000000] = new_term(VAR,0x000000,0x000000003);
  heap.buff[0x100000000] = new_term(APP,0x000000,0x000000001);
  heap.buff[0x100000001] = new_term(LAM,0x000000,0x00000000A);
  heap.buff[0x100000002] = new_term(DUP,0x000000,0x00000000D);
  heap.buff[0x100000003] = new_term(LAM,0x000000,0x000000016);
  heap.buff[0x100000004] = new_term(DUP,0x000000,0x00000002B);
  heap.buff[0x100000005] = new_term(LAM,0x000000,0x000000034);
  heap.buff[0x100000006] = new_term(DUP,0x000000,0x000000037);
  heap.buff[0x100000007] = new_term(LAM,0x000000,0x000000040);
  heap.buff[0x100000008] = new_term(DUP,0x000000,0x000000043);
  heap.buff[0x100000009] = new_term(LAM,0x000000,0x00000004C);
  heap.buff[0x10000000A] = new_term(DUP,0x000000,0x00000004F);
  heap.buff[0x10000000B] = new_term(LAM,0x000000,0x000000058);
  heap.buff[0x10000000C] = new_term(DUP,0x000000,0x00000005B);
  heap.buff[0x10000000D] = new_term(LAM,0x000000,0x000000064);
  heap.buff[0x10000000E] = new_term(DUP,0x000000,0x000000067);
  heap.buff[0x10000000F] = new_term(LAM,0x000000,0x000000070);
  heap.buff[0x100000010] = new_term(DUP,0x000000,0x000000073);
  heap.buff[0x100000011] = new_term(LAM,0x000000,0x00000007C);
  heap.buff[0x100000012] = new_term(DUP,0x000000,0x00000007F);
  heap.buff[0x100000013] = new_term(LAM,0x000000,0x000000088);
  heap.buff[0x100000014] = new_term(DUP,0x000000,0x00000008B);
  heap.buff[0x100000015] = new_term(LAM,0x000000,0x000000094);
  heap.buff[0x100000016] = new_term(DUP,0x000000,0x000000097);
  heap.buff[0x100000017] = new_term(LAM,0x000000,0x0000000A0);
  heap.buff[0x100000018] = new_term(DUP,0x000000,0x0000000A3);
  heap.buff[0x100000019] = new_term(LAM,0x000000,0x0000000AC);
  heap.buff[0x10000001A] = new_term(DUP,0x000000,0x0000000AF);
  heap.buff[0x10000001B] = new_term(LAM,0x000000,0x0000000B8);
  heap.buff[0x10000001C] = new_term(DUP,0x000000,0x0000000BB);
  heap.buff[0x10000001D] = new_term(LAM,0x000000,0x0000000C4);
  heap.buff[0x10000001E] = new_term(DUP,0x000000,0x0000000C7);
  heap.buff[0x10000001F] = new_term(LAM,0x000000,0x0000000D0);
  heap.buff[0x100000020] = new_term(DUP,0x000000,0x0000000D3);
  heap.buff[0x100000021] = new_term(LAM,0x000000,0x0000000DC);
  heap.buff[0x100000022] = new_term(DUP,0x000000,0x0000000DF);
  heap.buff[0x100000023] = new_term(LAM,0x000000,0x0000000E8);
  heap.buff[0x100000024] = new_term(DUP,0x000000,0x0000000EB);
  heap.buff[0x100000025] = new_term(LAM,0x000000,0x0000000F4);
  heap.buff[0x100000026] = new_term(DUP,0x000000,0x0000000F7);
  heap.buff[0x100000027] = new_term(LAM,0x000000,0x000000100);
  heap.buff[0x100000028] = new_term(DUP,0x000000,0x000000103);
  heap.buff[0x100000029] = new_term(LAM,0x000000,0x00000010C);
  heap.buff[0x10000002A] = new_term(DUP,0x000000,0x00000010F);
  heap.buff[0x10000002B] = new_term(LAM,0x000000,0x000000118);
  heap.buff[0x10000002C] = new_term(DUP,0x000000,0x00000011B);
  heap.buff[0x10000002D] = new_term(LAM,0x000000,0x000000124);
  heap.buff[0x10000002E] = new_term(DUP,0x000000,0x000000127);
  heap.buff[0x10000002F] = new_term(LAM,0x000000,0x000000130);
  heap.buff[0x000000000] = new_term(VAR,0x000000,0x000000003);
  heap.buff[0x000000001] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000002] = new_term(LAM,0x000000,0x000000004);
  heap.buff[0x000000003] = new_term(SUB,0x000000,0x000000003);
  heap.buff[0x000000004] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000005] = new_term(SUB,0x000000,0x000000005);
  heap.buff[0x000000006] = new_term(LAM,0x000000,0x000000007);
  heap.buff[0x000000007] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000008] = new_term(ERA,0x000000,0x000000000);
  heap.buff[0x000000009] = new_term(VAR,0x000000,0x000000005);
  heap.buff[0x00000000A] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000000B] = new_term(SUB,0x000000,0x00000000B);
  heap.buff[0x00000000C] = new_term(VAR,0x000000,0x00000012C);
  heap.buff[0x00000000D] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000000E] = new_term(APP,0x000000,0x000000010);
  heap.buff[0x00000000F] = new_term(APP,0x000000,0x000000013);
  heap.buff[0x000000010] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000011] = new_term(VAR,0x000000,0x000000015);
  heap.buff[0x000000012] = new_term(SUB,0x000000,0x000000012);
  heap.buff[0x000000013] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000014] = new_term(VAR,0x000000,0x000000035);
  heap.buff[0x000000015] = new_term(SUB,0x000000,0x000000015);
  heap.buff[0x000000016] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000017] = new_term(APP,0x000000,0x000000019);
  heap.buff[0x000000018] = new_term(VAR,0x000000,0x000000024);
  heap.buff[0x000000019] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000001A] = new_term(LAM,0x000000,0x00000001C);
  heap.buff[0x00000001B] = new_term(APP,0x000000,0x000000022);
  heap.buff[0x00000001C] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000001D] = new_term(ERA,0x000000,0x000000000);
  heap.buff[0x00000001E] = new_term(LAM,0x000000,0x00000001F);
  heap.buff[0x00000001F] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000020] = new_term(SUB,0x000000,0x000000020);
  heap.buff[0x000000021] = new_term(VAR,0x000000,0x000000020);
  heap.buff[0x000000022] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000023] = new_term(LAM,0x000000,0x000000025);
  heap.buff[0x000000024] = new_term(SUB,0x000000,0x000000024);
  heap.buff[0x000000025] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000026] = new_term(SUB,0x000000,0x000000026);
  heap.buff[0x000000027] = new_term(LAM,0x000000,0x000000028);
  heap.buff[0x000000028] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000029] = new_term(ERA,0x000000,0x000000000);
  heap.buff[0x00000002A] = new_term(VAR,0x000000,0x000000026);
  heap.buff[0x00000002B] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000002C] = new_term(APP,0x000000,0x00000002E);
  heap.buff[0x00000002D] = new_term(APP,0x000000,0x000000031);
  heap.buff[0x00000002E] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000002F] = new_term(VAR,0x000000,0x000000033);
  heap.buff[0x000000030] = new_term(SUB,0x000000,0x000000030);
  heap.buff[0x000000031] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000032] = new_term(VAR,0x000000,0x000000041);
  heap.buff[0x000000033] = new_term(SUB,0x000000,0x000000033);
  heap.buff[0x000000034] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000035] = new_term(SUB,0x000000,0x000000035);
  heap.buff[0x000000036] = new_term(VAR,0x000000,0x000000012);
  heap.buff[0x000000037] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000038] = new_term(APP,0x000000,0x00000003A);
  heap.buff[0x000000039] = new_term(APP,0x000000,0x00000003D);
  heap.buff[0x00000003A] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000003B] = new_term(VAR,0x000000,0x00000003F);
  heap.buff[0x00000003C] = new_term(SUB,0x000000,0x00000003C);
  heap.buff[0x00000003D] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000003E] = new_term(VAR,0x000000,0x00000004D);
  heap.buff[0x00000003F] = new_term(SUB,0x000000,0x00000003F);
  heap.buff[0x000000040] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000041] = new_term(SUB,0x000000,0x000000041);
  heap.buff[0x000000042] = new_term(VAR,0x000000,0x000000030);
  heap.buff[0x000000043] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000044] = new_term(APP,0x000000,0x000000046);
  heap.buff[0x000000045] = new_term(APP,0x000000,0x000000049);
  heap.buff[0x000000046] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000047] = new_term(VAR,0x000000,0x00000004B);
  heap.buff[0x000000048] = new_term(SUB,0x000000,0x000000048);
  heap.buff[0x000000049] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000004A] = new_term(VAR,0x000000,0x000000059);
  heap.buff[0x00000004B] = new_term(SUB,0x000000,0x00000004B);
  heap.buff[0x00000004C] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000004D] = new_term(SUB,0x000000,0x00000004D);
  heap.buff[0x00000004E] = new_term(VAR,0x000000,0x00000003C);
  heap.buff[0x00000004F] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000050] = new_term(APP,0x000000,0x000000052);
  heap.buff[0x000000051] = new_term(APP,0x000000,0x000000055);
  heap.buff[0x000000052] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000053] = new_term(VAR,0x000000,0x000000057);
  heap.buff[0x000000054] = new_term(SUB,0x000000,0x000000054);
  heap.buff[0x000000055] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000056] = new_term(VAR,0x000000,0x000000065);
  heap.buff[0x000000057] = new_term(SUB,0x000000,0x000000057);
  heap.buff[0x000000058] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000059] = new_term(SUB,0x000000,0x000000059);
  heap.buff[0x00000005A] = new_term(VAR,0x000000,0x000000048);
  heap.buff[0x00000005B] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000005C] = new_term(APP,0x000000,0x00000005E);
  heap.buff[0x00000005D] = new_term(APP,0x000000,0x000000061);
  heap.buff[0x00000005E] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000005F] = new_term(VAR,0x000000,0x000000063);
  heap.buff[0x000000060] = new_term(SUB,0x000000,0x000000060);
  heap.buff[0x000000061] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000062] = new_term(VAR,0x000000,0x000000071);
  heap.buff[0x000000063] = new_term(SUB,0x000000,0x000000063);
  heap.buff[0x000000064] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000065] = new_term(SUB,0x000000,0x000000065);
  heap.buff[0x000000066] = new_term(VAR,0x000000,0x000000054);
  heap.buff[0x000000067] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000068] = new_term(APP,0x000000,0x00000006A);
  heap.buff[0x000000069] = new_term(APP,0x000000,0x00000006D);
  heap.buff[0x00000006A] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000006B] = new_term(VAR,0x000000,0x00000006F);
  heap.buff[0x00000006C] = new_term(SUB,0x000000,0x00000006C);
  heap.buff[0x00000006D] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000006E] = new_term(VAR,0x000000,0x00000007D);
  heap.buff[0x00000006F] = new_term(SUB,0x000000,0x00000006F);
  heap.buff[0x000000070] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000071] = new_term(SUB,0x000000,0x000000071);
  heap.buff[0x000000072] = new_term(VAR,0x000000,0x000000060);
  heap.buff[0x000000073] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000074] = new_term(APP,0x000000,0x000000076);
  heap.buff[0x000000075] = new_term(APP,0x000000,0x000000079);
  heap.buff[0x000000076] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000077] = new_term(VAR,0x000000,0x00000007B);
  heap.buff[0x000000078] = new_term(SUB,0x000000,0x000000078);
  heap.buff[0x000000079] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000007A] = new_term(VAR,0x000000,0x000000089);
  heap.buff[0x00000007B] = new_term(SUB,0x000000,0x00000007B);
  heap.buff[0x00000007C] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000007D] = new_term(SUB,0x000000,0x00000007D);
  heap.buff[0x00000007E] = new_term(VAR,0x000000,0x00000006C);
  heap.buff[0x00000007F] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000080] = new_term(APP,0x000000,0x000000082);
  heap.buff[0x000000081] = new_term(APP,0x000000,0x000000085);
  heap.buff[0x000000082] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000083] = new_term(VAR,0x000000,0x000000087);
  heap.buff[0x000000084] = new_term(SUB,0x000000,0x000000084);
  heap.buff[0x000000085] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000086] = new_term(VAR,0x000000,0x000000095);
  heap.buff[0x000000087] = new_term(SUB,0x000000,0x000000087);
  heap.buff[0x000000088] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000089] = new_term(SUB,0x000000,0x000000089);
  heap.buff[0x00000008A] = new_term(VAR,0x000000,0x000000078);
  heap.buff[0x00000008B] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000008C] = new_term(APP,0x000000,0x00000008E);
  heap.buff[0x00000008D] = new_term(APP,0x000000,0x000000091);
  heap.buff[0x00000008E] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000008F] = new_term(VAR,0x000000,0x000000093);
  heap.buff[0x000000090] = new_term(SUB,0x000000,0x000000090);
  heap.buff[0x000000091] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000092] = new_term(VAR,0x000000,0x0000000A1);
  heap.buff[0x000000093] = new_term(SUB,0x000000,0x000000093);
  heap.buff[0x000000094] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000095] = new_term(SUB,0x000000,0x000000095);
  heap.buff[0x000000096] = new_term(VAR,0x000000,0x000000084);
  heap.buff[0x000000097] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000098] = new_term(APP,0x000000,0x00000009A);
  heap.buff[0x000000099] = new_term(APP,0x000000,0x00000009D);
  heap.buff[0x00000009A] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000009B] = new_term(VAR,0x000000,0x00000009F);
  heap.buff[0x00000009C] = new_term(SUB,0x000000,0x00000009C);
  heap.buff[0x00000009D] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000009E] = new_term(VAR,0x000000,0x0000000AD);
  heap.buff[0x00000009F] = new_term(SUB,0x000000,0x00000009F);
  heap.buff[0x0000000A0] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000A1] = new_term(SUB,0x000000,0x0000000A1);
  heap.buff[0x0000000A2] = new_term(VAR,0x000000,0x000000090);
  heap.buff[0x0000000A3] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000A4] = new_term(APP,0x000000,0x0000000A6);
  heap.buff[0x0000000A5] = new_term(APP,0x000000,0x0000000A9);
  heap.buff[0x0000000A6] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000A7] = new_term(VAR,0x000000,0x0000000AB);
  heap.buff[0x0000000A8] = new_term(SUB,0x000000,0x0000000A8);
  heap.buff[0x0000000A9] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000AA] = new_term(VAR,0x000000,0x0000000B9);
  heap.buff[0x0000000AB] = new_term(SUB,0x000000,0x0000000AB);
  heap.buff[0x0000000AC] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000AD] = new_term(SUB,0x000000,0x0000000AD);
  heap.buff[0x0000000AE] = new_term(VAR,0x000000,0x00000009C);
  heap.buff[0x0000000AF] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000B0] = new_term(APP,0x000000,0x0000000B2);
  heap.buff[0x0000000B1] = new_term(APP,0x000000,0x0000000B5);
  heap.buff[0x0000000B2] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000B3] = new_term(VAR,0x000000,0x0000000B7);
  heap.buff[0x0000000B4] = new_term(SUB,0x000000,0x0000000B4);
  heap.buff[0x0000000B5] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000B6] = new_term(VAR,0x000000,0x0000000C5);
  heap.buff[0x0000000B7] = new_term(SUB,0x000000,0x0000000B7);
  heap.buff[0x0000000B8] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000B9] = new_term(SUB,0x000000,0x0000000B9);
  heap.buff[0x0000000BA] = new_term(VAR,0x000000,0x0000000A8);
  heap.buff[0x0000000BB] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000BC] = new_term(APP,0x000000,0x0000000BE);
  heap.buff[0x0000000BD] = new_term(APP,0x000000,0x0000000C1);
  heap.buff[0x0000000BE] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000BF] = new_term(VAR,0x000000,0x0000000C3);
  heap.buff[0x0000000C0] = new_term(SUB,0x000000,0x0000000C0);
  heap.buff[0x0000000C1] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000C2] = new_term(VAR,0x000000,0x0000000D1);
  heap.buff[0x0000000C3] = new_term(SUB,0x000000,0x0000000C3);
  heap.buff[0x0000000C4] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000C5] = new_term(SUB,0x000000,0x0000000C5);
  heap.buff[0x0000000C6] = new_term(VAR,0x000000,0x0000000B4);
  heap.buff[0x0000000C7] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000C8] = new_term(APP,0x000000,0x0000000CA);
  heap.buff[0x0000000C9] = new_term(APP,0x000000,0x0000000CD);
  heap.buff[0x0000000CA] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000CB] = new_term(VAR,0x000000,0x0000000CF);
  heap.buff[0x0000000CC] = new_term(SUB,0x000000,0x0000000CC);
  heap.buff[0x0000000CD] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000CE] = new_term(VAR,0x000000,0x0000000DD);
  heap.buff[0x0000000CF] = new_term(SUB,0x000000,0x0000000CF);
  heap.buff[0x0000000D0] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000D1] = new_term(SUB,0x000000,0x0000000D1);
  heap.buff[0x0000000D2] = new_term(VAR,0x000000,0x0000000C0);
  heap.buff[0x0000000D3] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000D4] = new_term(APP,0x000000,0x0000000D6);
  heap.buff[0x0000000D5] = new_term(APP,0x000000,0x0000000D9);
  heap.buff[0x0000000D6] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000D7] = new_term(VAR,0x000000,0x0000000DB);
  heap.buff[0x0000000D8] = new_term(SUB,0x000000,0x0000000D8);
  heap.buff[0x0000000D9] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000DA] = new_term(VAR,0x000000,0x0000000E9);
  heap.buff[0x0000000DB] = new_term(SUB,0x000000,0x0000000DB);
  heap.buff[0x0000000DC] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000DD] = new_term(SUB,0x000000,0x0000000DD);
  heap.buff[0x0000000DE] = new_term(VAR,0x000000,0x0000000CC);
  heap.buff[0x0000000DF] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000E0] = new_term(APP,0x000000,0x0000000E2);
  heap.buff[0x0000000E1] = new_term(APP,0x000000,0x0000000E5);
  heap.buff[0x0000000E2] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000E3] = new_term(VAR,0x000000,0x0000000E7);
  heap.buff[0x0000000E4] = new_term(SUB,0x000000,0x0000000E4);
  heap.buff[0x0000000E5] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000E6] = new_term(VAR,0x000000,0x0000000F5);
  heap.buff[0x0000000E7] = new_term(SUB,0x000000,0x0000000E7);
  heap.buff[0x0000000E8] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000E9] = new_term(SUB,0x000000,0x0000000E9);
  heap.buff[0x0000000EA] = new_term(VAR,0x000000,0x0000000D8);
  heap.buff[0x0000000EB] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000EC] = new_term(APP,0x000000,0x0000000EE);
  heap.buff[0x0000000ED] = new_term(APP,0x000000,0x0000000F1);
  heap.buff[0x0000000EE] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000EF] = new_term(VAR,0x000000,0x0000000F3);
  heap.buff[0x0000000F0] = new_term(SUB,0x000000,0x0000000F0);
  heap.buff[0x0000000F1] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000F2] = new_term(VAR,0x000000,0x000000101);
  heap.buff[0x0000000F3] = new_term(SUB,0x000000,0x0000000F3);
  heap.buff[0x0000000F4] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000F5] = new_term(SUB,0x000000,0x0000000F5);
  heap.buff[0x0000000F6] = new_term(VAR,0x000000,0x0000000E4);
  heap.buff[0x0000000F7] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000F8] = new_term(APP,0x000000,0x0000000FA);
  heap.buff[0x0000000F9] = new_term(APP,0x000000,0x0000000FD);
  heap.buff[0x0000000FA] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000FB] = new_term(VAR,0x000000,0x0000000FF);
  heap.buff[0x0000000FC] = new_term(SUB,0x000000,0x0000000FC);
  heap.buff[0x0000000FD] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x0000000FE] = new_term(VAR,0x000000,0x00000010D);
  heap.buff[0x0000000FF] = new_term(SUB,0x000000,0x0000000FF);
  heap.buff[0x000000100] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000101] = new_term(SUB,0x000000,0x000000101);
  heap.buff[0x000000102] = new_term(VAR,0x000000,0x0000000F0);
  heap.buff[0x000000103] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000104] = new_term(APP,0x000000,0x000000106);
  heap.buff[0x000000105] = new_term(APP,0x000000,0x000000109);
  heap.buff[0x000000106] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000107] = new_term(VAR,0x000000,0x00000010B);
  heap.buff[0x000000108] = new_term(SUB,0x000000,0x000000108);
  heap.buff[0x000000109] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000010A] = new_term(VAR,0x000000,0x000000119);
  heap.buff[0x00000010B] = new_term(SUB,0x000000,0x00000010B);
  heap.buff[0x00000010C] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000010D] = new_term(SUB,0x000000,0x00000010D);
  heap.buff[0x00000010E] = new_term(VAR,0x000000,0x0000000FC);
  heap.buff[0x00000010F] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000110] = new_term(APP,0x000000,0x000000112);
  heap.buff[0x000000111] = new_term(APP,0x000000,0x000000115);
  heap.buff[0x000000112] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000113] = new_term(VAR,0x000000,0x000000117);
  heap.buff[0x000000114] = new_term(SUB,0x000000,0x000000114);
  heap.buff[0x000000115] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000116] = new_term(VAR,0x000000,0x000000125);
  heap.buff[0x000000117] = new_term(SUB,0x000000,0x000000117);
  heap.buff[0x000000118] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000119] = new_term(SUB,0x000000,0x000000119);
  heap.buff[0x00000011A] = new_term(VAR,0x000000,0x000000108);
  heap.buff[0x00000011B] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000011C] = new_term(APP,0x000000,0x00000011E);
  heap.buff[0x00000011D] = new_term(APP,0x000000,0x000000121);
  heap.buff[0x00000011E] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000011F] = new_term(VAR,0x000000,0x000000123);
  heap.buff[0x000000120] = new_term(SUB,0x000000,0x000000120);
  heap.buff[0x000000121] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000122] = new_term(VAR,0x000000,0x000000131);
  heap.buff[0x000000123] = new_term(SUB,0x000000,0x000000123);
  heap.buff[0x000000124] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000125] = new_term(SUB,0x000000,0x000000125);
  heap.buff[0x000000126] = new_term(VAR,0x000000,0x000000114);
  heap.buff[0x000000127] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000128] = new_term(APP,0x000000,0x00000012A);
  heap.buff[0x000000129] = new_term(APP,0x000000,0x00000012D);
  heap.buff[0x00000012A] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000012B] = new_term(VAR,0x000000,0x00000012F);
  heap.buff[0x00000012C] = new_term(SUB,0x000000,0x00000012C);
  heap.buff[0x00000012D] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x00000012E] = new_term(VAR,0x000000,0x00000000B);
  heap.buff[0x00000012F] = new_term(SUB,0x000000,0x00000012F);
  heap.buff[0x000000130] = new_term(AIR,0x000000,0x000000000);
  heap.buff[0x000000131] = new_term(SUB,0x000000,0x000000131);
  heap.buff[0x000000132] = new_term(VAR,0x000000,0x000000120);
  heap.rbag_ini = 0x0;
  heap.rbag_end = 0x30;
  heap.rnod_ini = 0x0;
  heap.rnod_end = 0x133;

  // Run evaluation
  eval_strict(&heap);

  // Print number of reductions
  printf("ITRS: %llu\n", heap.rbag_end / 2);

  // TODO: print the end time and interactions per second
  struct timespec end;
  clock_gettime(CLOCK_MONOTONIC, &end);
  double time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
  printf("Time: %.6fs\n", time);
  printf("MIPS: %.2f\n", (heap.rbag_end / 2.0 / time) / 1000000.0);

  // Cleanup
  free(buff);
  return 0;
}
