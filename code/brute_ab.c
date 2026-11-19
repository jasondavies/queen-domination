/* brute_ab.c -- brute force over ALL pairs of S-subsets (A,B); prints those passing the exact
 * constrained vertex cover test (no pruning, no symmetry).  For validating stage 1 on small N. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N,G,S,z[2];
static int ecover(int ne,const int*ed,const int*es,unsigned long long tD,unsigned long long tS,int pd,int ps){
  for(int i=0;i<ne;i++){ if((tD>>ed[i]&1)||(tS>>es[i]&1)) continue;
    if(pd>0&&ecover(ne,ed,es,tD|(1ULL<<ed[i]),tS,pd-1,ps)) return 1;
    if(ps>0&&ecover(ne,ed,es,tD,tS|(1ULL<<es[i]),pd,ps-1)) return 1;
    return 0; }
  return 1; }
int main(int c,char**v){ N=atoi(v[1]);G=atoi(v[2]);z[0]=atoi(v[3]);z[1]=G-z[0];S=N-G;
  uint64_t lim=1ULL<<N;
  for(uint64_t A=(1ULL<<S)-1;A<lim;){ 
    for(uint64_t B=(1ULL<<S)-1;B<lim;){
      int ok=1;
      for(int col=0;col<2&&ok;col++){ int ed[1024],es[1024],ne=0;
        for(int r=0;r<N;r++) if(A>>r&1) for(int x=0;x<N;x++) if(B>>x&1) if(((r+x)&1)==col){ed[ne]=r-x+N-1;es[ne]=r+x;ne++;}
        ok=ecover(ne,ed,es,0,0,z[col],z[col]); }
      if(ok) printf("C %llx %llx %d\n",(unsigned long long)A,(unsigned long long)B,z[0]);
      uint64_t t=B&-B,r=B+t; B=(((r^B)>>2)/t)|r; }
    uint64_t t=A&-A,r=A+t; A=(((r^A)>>2)/t)|r; }
  return 0; }
