/* stage1_v.c -- independent re-implementation of Stage 1 (written separately from stage1.c).
 *
 * Enumerates, up to the colour-preserving symmetry group {id, T, R180, AT}, all pairs (A,B) of
 * S-subsets of [0,N) (S = N-G) such that for each colour q the bipartite graph
 *   H_q = { (diff line r-x, sum line r+x) : r in A, x in B, r+x = q mod 2 }
 * has a vertex cover using <= z_q difference lines and <= z_q sum lines.
 *
 * Differences from stage1.c (deliberate): decision order inside a group is
 * row t, row N-1-t, col t, col N-1-t; matching maintained with BFS augmenting paths over an
 * explicit edge list; only the matching bound nu_q <= 2 z_q is used for pruning; the exact test at
 * the leaves branches on an uncovered edge (endpoint d or endpoint s); canonical form is lex-min
 * of the group codes (A_t,A_{N-1-t},B_t,B_{N-1-t}), t = 0,1,..., among the 4 images.
 *
 * usage: stage1_v N G z0 [part mod]   -> prints "C A B z0" (hex) per survivor
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define L 64
static int N, G, S, z[2];
static int ord_row[64], ord_idx[64], ndec;
static long long cnt_nodes = 0, cnt_out = 0, cnt_leaf = 0;
static int part = 0, mod = 1; static long long splitid = 0;
#define SPLIT_DEPTH 16

/* graph: adjacency lists diff line -> sum lines, as small arrays */
typedef struct {
  unsigned char deg[L];
  unsigned char nb[L][32];
  signed char md[L], ms[L];   /* matching partner: md[diff] = sum, ms[sum] = diff */
  int size[2];
} G_t;

static int bfs_augment(G_t *g, int root){
  /* BFS from free diff vertex root over alternating paths; augment if a free sum vertex found */
  int prevd[L], viaS[L]; int q[L], qh = 0, qt = 0;
  char seenS[L]; memset(seenS, 0, sizeof seenS);
  for(int i = 0; i < L; i++) prevd[i] = -2;
  q[qt++] = root; prevd[root] = -1;
  while(qh < qt){
    int d = q[qh++];
    for(int k = 0; k < g->deg[d]; k++){
      int s = g->nb[d][k];
      if(seenS[s]) continue;
      seenS[s] = 1; viaS[s] = d;
      if(g->ms[s] < 0){
        /* augment along path ending at s */
        int cs = s;
        while(1){
          int cd = viaS[cs];
          int nexts = g->md[cd];
          g->md[cd] = cs; g->ms[cs] = cd;
          if(prevd[cd] == -1) break;
          cs = nexts;
        }
        return 1;
      }
      int d2 = g->ms[s];
      if(prevd[d2] == -2){ prevd[d2] = d; q[qt++] = d2; }
    }
  }
  return 0;
}

static void add_sq(G_t *g, int r, int x){
  int d = r - x + N - 1, s = r + x;
  g->nb[d][g->deg[d]++] = (unsigned char)s;
}

static void improve(G_t *g){
  int again = 1;
  while(again){
    again = 0;
    for(int d = 0; d < 2*N-1; d++)
      if(g->md[d] < 0 && g->deg[d] > 0 && bfs_augment(g, d)){ g->size[g->md[d] & 1]++; again = 1; }
  }
}

/* exact constrained vertex cover by edge branching */
static int ecover(int ne, const int *ed, const int *es, unsigned long long takenD, unsigned long long takenS, int pd, int ps){
  for(int i = 0; i < ne; i++){
    if((takenD >> ed[i] & 1) || (takenS >> es[i] & 1)) continue;
    /* uncovered edge i */
    if(pd > 0 && ecover(ne, ed, es, takenD | (1ULL << ed[i]), takenS, pd - 1, ps)) return 1;
    if(ps > 0 && ecover(ne, ed, es, takenD, takenS | (1ULL << es[i]), pd, ps - 1)) return 1;
    return 0;
  }
  return 1;
}
static int exact_ok(uint64_t A, uint64_t B){
  for(int col = 0; col < 2; col++){
    int ed[1024], es[1024], ne = 0;
    for(int r = 0; r < N; r++) if(A >> r & 1) for(int x = 0; x < N; x++) if(B >> x & 1)
      if(((r + x) & 1) == col){ ed[ne] = r - x + N - 1; es[ne] = r + x; ne++; }
    if(!ecover(ne, ed, es, 0, 0, z[col], z[col])) return 0;
  }
  return 1;
}

static int code(uint64_t A, uint64_t B, int t, int g){
  int a1 = A >> t & 1, a2 = A >> (N-1-t) & 1, b1 = B >> t & 1, b2 = B >> (N-1-t) & 1;
  switch(g){
    case 0: return a1<<3 | a2<<2 | b1<<1 | b2;       /* (A,B) */
    case 1: return b1<<3 | b2<<2 | a1<<1 | a2;       /* transpose: (B,A) */
    case 2: return a2<<3 | a1<<2 | b2<<1 | b1;       /* rot180: (rev A, rev B) */
    default: return b2<<3 | b1<<2 | a2<<1 | a1;      /* antitranspose: (rev B, rev A) */
  }
}

static void search(int k, uint64_t A, uint64_t B, int na, int nb, G_t *g, int live){
  cnt_nodes++;
  if(k > 0 && (k % 4) == 0){
    int t = k/4 - 1, c0 = code(A, B, t, 0);
    for(int h = 1; h < 4; h++) if(live >> h & 1){
      int c = code(A, B, t, h);
      if(c < c0) return;
      if(c > c0) live &= ~(1 << h);
    }
  }
  if(k == SPLIT_DEPTH){ if((splitid++) % mod != part) return; }
  if(k == ndec){
    cnt_leaf++;
    if(na != S || nb != S) return;
    if(!exact_ok(A, B)) return;
    cnt_out++;
    printf("C %llx %llx %d\n", (unsigned long long)A, (unsigned long long)B, z[0]);
    return;
  }
  int isr = ord_row[k], i = ord_idx[k];
  int have = isr ? na : nb;
  /* undecided count of this type after this one */
  int rest = 0; for(int j = k+1; j < ndec; j++) if(ord_row[j] == isr) rest++;
  /* choice: i not in set */
  if(have + rest >= S) search(k+1, A, B, na, nb, g, live);
  /* choice: i in set */
  if(have < S){
    G_t h = *g;
    uint64_t o = isr ? B : A;
    for(int j = 0; j < N; j++) if(o >> j & 1){ if(isr) add_sq(&h, i, j); else add_sq(&h, j, i); }
    improve(&h);
    if(h.size[0] <= 2*z[0] && h.size[1] <= 2*z[1]){
      if(isr) search(k+1, A | (1ULL << i), B, na+1, nb, &h, live);
      else    search(k+1, A, B | (1ULL << i), na, nb+1, &h, live);
    }
  }
}

int main(int argc, char **argv){
  if(argc < 4){ fprintf(stderr, "usage: stage1_v N G z0 [part mod]\n"); return 1; }
  N = atoi(argv[1]); G = atoi(argv[2]); z[0] = atoi(argv[3]); z[1] = G - z[0]; S = N - G;
  if(argc >= 6){ part = atoi(argv[4]); mod = atoi(argv[5]); }
  if(N % 2 || N > 32){ fprintf(stderr, "N must be even <= 32\n"); return 1; }
  ndec = 0;
  for(int t = 0; t < N/2; t++){
    ord_row[ndec] = 1; ord_idx[ndec++] = t;
    ord_row[ndec] = 1; ord_idx[ndec++] = N-1-t;
    ord_row[ndec] = 0; ord_idx[ndec++] = t;
    ord_row[ndec] = 0; ord_idx[ndec++] = N-1-t;
  }
  G_t g0; memset(&g0, 0, sizeof g0);
  for(int i = 0; i < L; i++){ g0.md[i] = -1; g0.ms[i] = -1; }
  clock_t t0 = clock();
  search(0, 0, 0, 0, 0, &g0, 14);
  fprintf(stderr, "lines_v N=%d G=%d z=(%d,%d) part %d/%d nodes=%lld leaves=%lld out=%lld time=%.2fs\n",
          N, G, z[0], z[1], part, mod, cnt_nodes, cnt_leaf, cnt_out, (double)(clock()-t0)/CLOCKS_PER_SEC);
  return 0;
}
