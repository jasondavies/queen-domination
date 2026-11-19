/* stage1.c -- Stage 1: enumerate pairs (A,B) of s-subsets of [0,N) (A: rows, B: columns), s = N-G,
 * such that the "needy" grid A x B can be covered by the diagonal lines of a queen set with
 * colour classes of sizes z0, z1 = G - z0.
 *
 * Relaxation (necessary condition) -- Lemma 2.2 of the paper:
 *   if D is a dominating set of Q_N with |D| = G and colour classes (z0,z1), and A, B are
 *   s-subsets of the empty rows / empty columns of D, then for each colour q the colour-q squares of
 *   A x B are covered by <= z_q difference lines and <= z_q sum lines of colour q.
 * Bipartite view: vertex set = diff lines (left) and sum lines (right); each square (r,x) is the
 * edge (r-x+N-1, r+x).  The condition is a constrained bipartite vertex cover (CBVC) with budgets
 * (z_q, z_q) in the colour-q component.  During the DFS we prune with
 *   (P1) nu_q > 2 z_q  (nu_q = maximum matching of colour-q squares = max bishop-independent set),
 *   (P2) a colour-q line meeting > z_q needy squares must be in the cover: more than z_q such lines
 *        of one type -> infeasible,
 *   (K) iterated forced lines with decreasing budgets, then the matching bound on the residual graph,
 * and at the leaves we solve CBVC exactly.
 * Rows and columns are decided in the order row0,col0,row(N-1),col(N-1),row1,col1,... .
 * Symmetry: for fixed z0 the colour-preserving symmetries id, transpose (A,B)->(B,A),
 * rot180 (A,B)->(N-1-A,N-1-B), antitranspose (A,B)->(N-1-B,N-1-A) act; we keep (A,B) only if its
 * sequence of group codes gcode(.,t,0), t = 0,1,..., is lexicographically least among its 4 images
 * (canonical2); prefixes are rejected as soon as a completed group t shows an image to be smaller.
 * (The function canonical(), keyed on A<<32|B, is not used.)
 * Splitting: argument "part P M" processes only the subtrees at depth SPLITD whose index = P mod M.
 *
 * usage: stage1 N G z0 [P M [SPLITD]] ; prints "C A B z0" (hex) for survivors, stats on stderr.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef uint64_t u64;
static int N,G,S,Z[2];
static int order_isrow[64], order_idx[64], NDEC;
static long long nodes=0, leaves=0, surv=0, prunedP1=0, prunedP2=0, cbvcfail=0, noncanon=0;
static int KSLACK=2; static int SPLITD=16; static long long splitcount=0; static int PART=0, MOD=1;

typedef struct {
  u64 adj[64];       /* diff line -> bitmask of sum lines (needy squares) */
  int mL[64], mR[64];/* matching: mL[diff]=sum or -1, mR[sum]=diff or -1 */
  int nu[2];
  int degD[64], degS[64];
} state;

static u64 visR;
static int try_aug(state *st, int u){
  u64 cand = st->adj[u] & ~visR;
  while(cand){ int v=__builtin_ctzll(cand); cand&=cand-1;
    if(visR>>v&1) continue; visR|=1ULL<<v;
    if(st->mR[v]<0 || try_aug(st, st->mR[v])){ st->mL[u]=v; st->mR[v]=u; return 1; }
    cand &= ~visR;
  }
  return 0;
}
static void add_edge(state *st, int r, int x){
  int d=r-x+N-1, s=r+x;
  st->adj[d] |= 1ULL<<s; st->degD[d]++; st->degS[s]++;
}
static void rematch(state *st){
  int changed=1;
  while(changed){ changed=0;
    for(int u=0;u<2*N-1;u++) if(st->mL[u]<0 && st->adj[u]){ visR=0; if(try_aug(st,u)){ st->nu[(st->mL[u])&1]++; changed=1; } }
  }
}

/* ---- exact CBVC ---- */
static int cbvc(u64 *adj, int nL, int p, int q){
  /* adj: left->right masks (only colour-q part), budgets p (left), q (right) */
  /* find max degree vertex on either side */
  int bestL=-1,bdL=0; u64 any=0;
  for(int u=0;u<nL;u++){ int dg=__builtin_popcountll(adj[u]); if(dg>bdL){bdL=dg;bestL=u;} any|=adj[u]; }
  if(!any) return 1;
  int bestR=-1,bdR=0;
  { u64 a=any; while(a){ int v=__builtin_ctzll(a); a&=a-1; int dg=0; for(int u=0;u<nL;u++) dg+=(adj[u]>>v)&1; if(dg>bdR){bdR=dg;bestR=v;} } }
  if(p==0 && q==0) return 0;
  u64 save[64];
  if(bdL>=bdR){
    int u=bestL; u64 nb=adj[u];
    /* option 1: take u */
    if(p>0){ memcpy(save,adj,nL*8); adj[u]=0; int ok=cbvc(adj,nL,p-1,q); memcpy(adj,save,nL*8); if(ok) return 1; }
    /* option 2: take all neighbours of u */
    if(bdL<=q){ memcpy(save,adj,nL*8); for(int w=0;w<nL;w++) adj[w]&=~nb; int ok=cbvc(adj,nL,p,q-bdL); memcpy(adj,save,nL*8); if(ok) return 1; }
    return 0;
  } else {
    int v=bestR;
    if(q>0){ memcpy(save,adj,nL*8); for(int w=0;w<nL;w++) adj[w]&=~(1ULL<<v); int ok=cbvc(adj,nL,p,q-1); memcpy(adj,save,nL*8); if(ok) return 1; }
    if(bdR<=p){ memcpy(save,adj,nL*8); for(int w=0;w<nL;w++) if(adj[w]>>v&1) adj[w]=0; int ok=cbvc(adj,nL,p-bdR,q); memcpy(adj,save,nL*8); if(ok) return 1; }
    return 0;
  }
}
static int cbvc_colour(const state *st, int col){
  u64 adj[64]; u64 m = 0; for(int s=0;s<2*N-1;s++) if((s&1)==col) m|=1ULL<<s;
  for(int u=0;u<2*N-1;u++) adj[u]=st->adj[u]&m;
  return cbvc(adj,2*N-1,Z[col],Z[col]);
}

static u64 rev(u64 m){ u64 r=0; for(int i=0;i<N;i++) if(m>>i&1) r|=1ULL<<(N-1-i); return r; }
static int gcode(u64 A,u64 B,int t,int g);
static int canonical2(u64 A,u64 B){ /* lex-min of group sequence among the 4 images */
  for(int g=1;g<4;g++){ for(int t=0;t<N/2;t++){ int c0=gcode(A,B,t,0), cg=gcode(A,B,t,g); if(cg<c0) return 0; if(cg>c0) break; } }
  return 1; }
static int canonical(u64 A, u64 B){
  u64 k=(A<<32)|B;
  u64 Ar=rev(A), Br=rev(B);
  u64 k1=(B<<32)|A, k2=(Ar<<32)|Br, k3=(Br<<32)|Ar;
  return k<=k1 && k<=k2 && k<=k3;
}


/* kernel bound for colour col: iterated forced lines, then max matching of the residual graph */
static long long prunedK=0, prunedSym=0;
static int kernel_ok(const state *st, int col){
  u64 adj[64]; u64 m=0; for(int s=0;s<2*N-1;s++) if((s&1)==col) m|=1ULL<<s;
  int nL=2*N-1;
  for(int u=0;u<nL;u++) adj[u]=st->adj[u]&m;
  int p=Z[col], q=Z[col];
  int changed=1;
  while(changed){ changed=0;
    for(int u=0;u<nL;u++){ int dg=__builtin_popcountll(adj[u]); if(dg>q){ adj[u]=0; p--; changed=1; if(p<0) return 0; } }
    u64 any=0; for(int u=0;u<nL;u++) any|=adj[u];
    u64 a=any; while(a){ int v=__builtin_ctzll(a); a&=a-1; int dg=0; for(int u=0;u<nL;u++) dg+=(adj[u]>>v)&1;
      if(dg>p){ for(int u=0;u<nL;u++) adj[u]&=~(1ULL<<v); q--; changed=1; if(q<0) return 0; } }
  }
  /* matching on residual */
  int mR[64]; for(int i=0;i<64;i++) mR[i]=-1;
  int nu=0;
  for(int u=0;u<nL;u++) if(adj[u]){
    /* iterative-deepening via recursive helper */
    u64 vis=0;
    int stackU[64], sp=0; (void)stackU; (void)sp;
    /* simple recursive augment */
    int aug(int uu){ u64 c=adj[uu]&~vis; while(c){ int v=__builtin_ctzll(c); c&=c-1; if(vis>>v&1) continue; vis|=1ULL<<v;
        if(mR[v]<0 || aug(mR[v])){ mR[v]=uu; return 1; } c&=~vis; } return 0; }
    if(aug(u)){ nu++; if(nu>p+q) return 0; }
  }
  return 1;
}
/* symmetry: sequence per group t: (A_t,B_t,A_{N-1-t},B_{N-1-t}); images: T:(B_t,A_t,B',A'), R:(A',B',A_t,B_t), TR:(B',A',B_t,A_t) */
static int gcode(u64 A,u64 B,int t,int g){
  int a=A>>t&1, b=B>>t&1, a2=A>>(N-1-t)&1, b2=B>>(N-1-t)&1;
  int s0,s1,s2,s3;
  switch(g){ case 0: s0=a;s1=b;s2=a2;s3=b2;break; case 1: s0=b;s1=a;s2=b2;s3=a2;break;
    case 2: s0=a2;s1=b2;s2=a;s3=b;break; default: s0=b2;s1=a2;s2=b;s3=a; }
  return (s0<<3)|(s1<<2)|(s2<<1)|s3;
}

static void dfs(int depth, u64 A, u64 B, int na, int nb, int ra, int rb, state *st, int symst){
  /* ra, rb: rows / cols still undecided */
  nodes++;
  if(depth>0 && depth%4==0){
    int t=depth/4-1;
    int c0=gcode(A,B,t,0);
    for(int g=1;g<4;g++) if(symst>>g&1){ int cg=gcode(A,B,t,g); if(cg<c0){ prunedSym++; return; } if(cg>c0) symst&=~(1<<g); }
  }
  if(depth==SPLITD){ long long id=splitcount++; if(id%MOD!=PART) return; }
  if(depth==NDEC){
    leaves++;
    if(!canonical2(A,B)){ noncanon++; return; }
    if(!cbvc_colour(st,0) || !cbvc_colour(st,1)){ cbvcfail++; return; }
    surv++; printf("C %llx %llx %d\n",(unsigned long long)A,(unsigned long long)B,Z[0]); fflush(stdout);
    return;
  }
  int isrow=order_isrow[depth], i=order_idx[depth];
  int have = isrow? na:nb, left = isrow? ra:rb;
  /* option empty */
  if(have < S){
    state ns=*st;
    u64 other = isrow? B : A;
    u64 o=other; while(o){ int j=__builtin_ctzll(o); o&=o-1; if(isrow) add_edge(&ns,i,j); else add_edge(&ns,j,i); }
    rematch(&ns);
    int bad=0;
    if(ns.nu[0]>2*Z[0] || ns.nu[1]>2*Z[1]){ bad=1; prunedP1++; }
    if(!bad){
      int fD[2]={0,0}, fS[2]={0,0};
      for(int u=0;u<2*N-1;u++){ if(ns.degD[u]>Z[(u+N+1)&1]) fD[(u+N+1)&1]++; if(ns.degS[u]>Z[u&1]) fS[u&1]++; }
      for(int q=0;q<2;q++) if(fD[q]>Z[q]||fS[q]>Z[q]) bad=1;
      if(bad) prunedP2++;
    }
    if(!bad && ((ns.nu[0]>=2*Z[0]-KSLACK && !kernel_ok(&ns,0)) || (ns.nu[1]>=2*Z[1]-KSLACK && !kernel_ok(&ns,1)))){ bad=1; prunedK++; }
    if(!bad){
      if(isrow) dfs(depth+1, A|(1ULL<<i), B, na+1, nb, ra-1, rb, &ns, symst);
      else      dfs(depth+1, A, B|(1ULL<<i), na, nb+1, ra, rb-1, &ns, symst);
    }
  }
  /* option occupied (not in the chosen subset) */
  if(S-have < left){
    if(isrow) dfs(depth+1, A, B, na, nb, ra-1, rb, st, symst);
    else      dfs(depth+1, A, B, na, nb, ra, rb-1, st, symst);
  }
}

int main(int argc, char **argv){
  N=atoi(argv[1]); G=atoi(argv[2]); Z[0]=atoi(argv[3]); Z[1]=G-Z[0]; S=N-G;
  if(argc>=6){ PART=atoi(argv[4]); MOD=atoi(argv[5]); }
  if(argc>=7) SPLITD=atoi(argv[6]);
  if(getenv("KSLACK")) KSLACK=atoi(getenv("KSLACK"));
  NDEC=0;
  for(int t=0;t<(N+1)/2;t++){
    int i1=t, i2=N-1-t;
    order_isrow[NDEC]=1; order_idx[NDEC++]=i1;
    order_isrow[NDEC]=0; order_idx[NDEC++]=i1;
    if(i2!=i1){ order_isrow[NDEC]=1; order_idx[NDEC++]=i2; order_isrow[NDEC]=0; order_idx[NDEC++]=i2; }
  }
  state st; memset(&st,0,sizeof st); for(int i=0;i<64;i++){ st.mL[i]=st.mR[i]=-1; }
  clock_t t0=clock();
  dfs(0,0,0,0,0,N,N,&st,14);
  fprintf(stderr,"N=%d G=%d z=(%d,%d) part %d/%d: K=%lld Sym=%lld nodes=%lld P1=%lld P2=%lld leaves=%lld noncanon=%lld cbvcfail=%lld surv=%lld time=%.2fs\n",
    N,G,Z[0],Z[1],PART,MOD,prunedK,prunedSym,nodes,prunedP1,prunedP2,leaves,noncanon,cbvcfail,surv,(double)(clock()-t0)/CLOCKS_PER_SEC);
  return 0;
}
