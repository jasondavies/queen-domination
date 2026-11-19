/* place.c -- Stage 2: for each candidate (A,B,z0) read from stdin ("C A B z0", hex masks),
 * find ALL dominating sets D of Q_N with |D| = G, colour classes (z0, G-z0), and
 * D contained in (rows not in A) x (columns not in B).
 *
 * Exhaustive branch-and-bound: choose an undominated square u with the fewest available
 * attackers, branch over its attackers p_1..p_m in order; in branch j the attackers p_1..p_{j-1}
 * are forbidden (so the branches partition the solution space).  Pruning: (i) a square with no
 * available attacker; (ii) greedy packing of undominated squares with pairwise disjoint attacker
 * sets: their number is a lower bound on the queens still needed (overall, and per colour for
 * squares all of whose attackers have one colour).
 *
 * Output: "SOL k r0 c0 r1 c1 ..." per solution, "DONE A B z0 nodes" per candidate.
 * usage: place N G < candidates
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef uint64_t u64;
#define W 4                 /* 256-bit sets over allowed cells (<= 256) */
static int N,G,Z[2];
static int np; static int pr[256], pc[256], pcol[256];
static int ncell; static u64 att[1024][W];   /* attackers (allowed cells) of each board square */
static u64 attcolmask[2][W];                 /* allowed cells of colour q */
static int onlycol[1024];                    /* colour if all attackers have one colour, else -1 */
static u64 covers[256][16];                  /* board squares dominated by allowed cell (676<=1024) */
static int NW; /* words for board bitsets */
static long long nodes;
static int sol[64][2];
static long long nsol;

static inline int pc4(const u64 *a, const u64 *b){ int s=0; for(int i=0;i<W;i++) s+=__builtin_popcountll(a[i]&b[i]); return s; }
static inline int attacks(int r1,int c1,int r2,int c2){ return r1==r2||c1==c2||r1-c1==r2-c2||r1+c1==r2+c2; }

static void dfs(int placed, int cnt0, int cnt1, u64 *cov, u64 *avail){
  nodes++;
  int rem=G-placed;
  /* find undominated square with fewest available attackers */
  int best=-1, bestc=1<<30; int nunc=0;
  static int uncl[64][1024]; int *unc=uncl[placed];
  static int ucnt[64][1024]; int *uc=ucnt[placed];
  for(int w=0;w<NW;w++){ u64 m=~cov[w]; if(w==NW-1 && (ncell&63)) m&=(1ULL<<(ncell&63))-1;
    while(m){ int b=__builtin_ctzll(m); m&=m-1; int u=w*64+b;
      int c=pc4(att[u],avail); if(c==0) return;
      unc[nunc]=u; uc[nunc]=c; nunc++;
      if(c<bestc){bestc=c;best=u;} } }
  if(nunc==0){
    if(rem==0){ nsol++; printf("SOL %d",G); for(int i=0;i<G;i++) printf(" %d %d",sol[i][0],sol[i][1]); printf("\n"); }
    /* with rem>0 a smaller dominating set exists -- impossible when G = gamma lower bound; report */
    else { printf("SMALLER %d\n",placed); }
    return;
  }
  if(rem==0) return;
  /* greedy disjoint packing lower bound (squares sorted by attacker count: simple two passes) */
  {
    u64 used[W]={0}; int lb=0, lbq[2]={0,0}; u64 usedq[2][W]; memset(usedq,0,sizeof usedq);
    for(int pass=1; pass<=4 && lb<=rem; pass++){
      int lim = (pass==1)?2:(pass==2)?4:(pass==3)?8:1<<30;
      for(int i=0;i<nunc;i++){ if(uc[i]>lim) continue; int u=unc[i];
        int dis=1; for(int w=0;w<W;w++) if(att[u][w]&avail[w]&used[w]){dis=0;break;}
        if(dis){ lb++; for(int w=0;w<W;w++) used[w]|=att[u][w]&avail[w]; uc[i]=1<<30; }
      }
    }
    if(lb>rem) return;
    /* per colour */
    for(int i=0;i<nunc;i++){ int u=unc[i]; int q=onlycol[u]; if(q<0) continue;
      int dis=1; for(int w=0;w<W;w++) if(att[u][w]&avail[w]&usedq[q][w]){dis=0;break;}
      if(dis){ lbq[q]++; for(int w=0;w<W;w++) usedq[q][w]|=att[u][w]&avail[w]; } }
    if(lbq[0]>Z[0]-cnt0 || lbq[1]>Z[1]-cnt1) return;
  }
  u64 av[W]; memcpy(av,avail,sizeof av);
  u64 cand[W]; for(int w=0;w<W;w++) cand[w]=att[best][w]&avail[w];
  for(int w=0;w<W;w++) while(cand[w]){ int b=__builtin_ctzll(cand[w]); cand[w]&=cand[w]-1; int p=w*64+b;
    if(!((av[w]>>b)&1)) continue;
    int q=pcol[p];
    int n0=cnt0+(q==0), n1=cnt1+(q==1);
    u64 nav[W]; memcpy(nav,av,sizeof nav);
    nav[w]&=~(1ULL<<b);
    if(n0==Z[0]) for(int x=0;x<W;x++) nav[x]&=~attcolmask[0][x];
    if(n1==Z[1]) for(int x=0;x<W;x++) nav[x]&=~attcolmask[1][x];
    u64 ncov[16]; for(int x=0;x<NW;x++) ncov[x]=cov[x]|covers[p][x];
    sol[placed][0]=pr[p]; sol[placed][1]=pc[p];
    dfs(placed+1,n0,n1,ncov,nav);
    av[w]&=~(1ULL<<b);   /* forbid p in later branches */
  }
}

int main(int argc,char**argv){
  N=atoi(argv[1]); G=atoi(argv[2]); ncell=N*N; NW=(ncell+63)/64;
  char line[256]; unsigned long long A,B; int z0;
  long long totnodes=0, ncand=0;
  clock_t t0=clock();
  while(fgets(line,sizeof line,stdin)){
    if(sscanf(line,"C %llx %llx %d",&A,&B,&z0)!=3) continue;
    Z[0]=z0; Z[1]=G-z0;
    np=0;
    for(int r=0;r<N;r++) if(!(A>>r&1)) for(int c=0;c<N;c++) if(!(B>>c&1)){ pr[np]=r; pc[np]=c; pcol[np]=(r+c)&1; np++; }
    if(np>64*W){ fprintf(stderr,"too many allowed cells\n"); return 2; }
    memset(attcolmask,0,sizeof attcolmask);
    for(int p=0;p<np;p++) attcolmask[pcol[p]][p>>6]|=1ULL<<(p&63);
    for(int u=0;u<ncell;u++){ memset(att[u],0,sizeof att[u]); int r=u/N,c=u%N; int c0=0,c1=0;
      for(int p=0;p<np;p++) if(attacks(r,c,pr[p],pc[p])){ att[u][p>>6]|=1ULL<<(p&63); if(pcol[p]) c1++; else c0++; }
      onlycol[u] = (c0&&!c1)?0 : (c1&&!c0)?1 : -1; }
    for(int p=0;p<np;p++){ memset(covers[p],0,sizeof covers[p]);
      for(int u=0;u<ncell;u++) if(attacks(u/N,u%N,pr[p],pc[p])) covers[p][u>>6]|=1ULL<<(u&63); }
    u64 cov[16]={0}; u64 avail[W]={0};
    for(int p=0;p<np;p++) avail[p>>6]|=1ULL<<(p&63);
    if(Z[0]==0) for(int x=0;x<W;x++) avail[x]&=~attcolmask[0][x];
    if(Z[1]==0) for(int x=0;x<W;x++) avail[x]&=~attcolmask[1][x];
    nodes=0; nsol=0;
    dfs(0,0,0,cov,avail);
    printf("DONE %llx %llx %d %lld %lld\n",A,B,z0,nodes,nsol); fflush(stdout);
    totnodes+=nodes; ncand++;
  }
  fprintf(stderr,"place N=%d G=%d: candidates=%lld nodes=%lld time=%.2fs\n",N,G,ncand,totnodes,(double)(clock()-t0)/CLOCKS_PER_SEC);
  return 0;
}
