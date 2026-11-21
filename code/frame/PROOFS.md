# Frame method: definitions, identities, proofs

(Working notes behind Section 2 of the paper, in the numbering used by the map in lean/README.md.  The
identities were re-derived here from a description of an earlier, uncertified implementation; see the
paper's declaration.  Brute-force tests: code/frame/verify_identities.py.)

## F.0 Setting and definitions

Board: squares (x, y), 0 <= x, y < n; x is the column, y the row.  The *difference diagonal* of (x, y) is
t = y - x, its *sum diagonal* is s = x + y; "diagonal" means either kind, "line" means a row, a column or a
diagonal.  A square is *dominated* by a set D if it is in D or shares a line with a square of D.

Throughout, D is a set of exactly k squares ("queens") and
  R, C, T, S = the sets of rows, columns, difference diagonals, sum diagonals that contain a queen,
  dR = k - |R|, dC = k - |C|, dT = k - |T|, dS = k - |S|        (the *deficits*; all are >= 0).
A row or column is *empty* if it contains no queen.  A square is *needy* if its row and its column are both
empty.  A needy square is not in D and is not attacked along its row or column, so:

  (N) if D dominates the board, every needy square lies on an occupied diagonal (in T or in S).

*Standing assumption*: at least two rows and at least two columns are empty.  (Automatic if k <= n - 2,
since |R|, |C| <= k.)  Let a < b be the least and greatest empty columns, c < d the least and greatest empty
rows; w = b - a >= 1, h = d - c >= 1.  The *box* is {(x, y): a <= x <= b, c <= y <= d}; its *border* is the
set of box squares with x in {a, b} or y in {c, d}; each square of the border is one square, in particular
the four *corners* (a,c), (a,d), (b,c), (b,d) are counted once.  The *vertical sides* are the 2(h+1) border
squares with x in {a, b}, the *horizontal sides* the 2(w+1) border squares with y in {c, d}; the corners
belong to both.  The *margins* are ml = a, mr = n-1-b, mb = c, mt = n-1-d.

Facts used below.
 (E1) Every empty column lies in [a, b] and every empty row in [c, d] (a, b, c, d are extreme).  Columns
      and rows inside the box may be occupied or empty; nothing is assumed about them.  The ml + mr
      columns outside [a, b] and the mb + mt rows outside [c, d] are all occupied, hence
      ml + mr <= |C| = k - dC and mb + mt <= |R| = k - dR.
 (E2) No border square is occupied: a border square lies in column a or b or in row c or d, all empty.
 (E3) Needy border squares.  A square (x, c) or (x, d) of a horizontal side is needy iff column x is empty;
      by (E1) each horizontal side contains exactly n - |C| needy squares.  A square (a, y) or (b, y) of a
      vertical side is needy iff row y is empty; each vertical side contains exactly n - |R| needy squares.
      The four corners are needy and are the only squares in both a vertical and a horizontal side.  So
        the vertical sides contain exactly 2(n - |R|) needy squares, the horizontal sides exactly
        2(n - |C|), and the border exactly  N = 2(n - |R|) + 2(n - |C|) - 4.
 (E4) A diagonal meets the border in at most two squares.  Proof: parametrise the squares of a difference
      diagonal as (x0 + j, y0 + j).  Those in the box are given by the j with a <= x0 + j <= b and
      c <= y0 + j <= d, an interval [j1, j2] of integers (possibly empty).  Such a square is on the border
      iff x0 + j = a or y0 + j = c (possible only for j = j1, because both coordinates increase with j and
      j1 is the least j satisfying both lower bounds) or x0 + j = b or y0 + j = d (possible only for
      j = j2).  So at most the two squares j = j1 and j = j2 are border squares.  For a sum diagonal use
      (x0 + j, y0 - j) in the same way.  []
 (E5) Suppose w >= h.  A diagonal contains at most one square of the vertical sides, except that if w = h
      the difference diagonal u0 := {t = c - a} contains the two corners (a, c), (b, d), and the sum diagonal
      v0 := {s = a + d} contains the two corners (a, d), (b, c).  Proof: a diagonal has exactly one square
      in each column it meets.  If it contains (a, y) and (b, y'), both on the vertical sides, then
      |y' - y| = b - a = w and c <= y, y' <= d, so w <= d - c = h; hence w = h and {y, y'} = {c, d}; for a
      difference diagonal y' = y + w gives (a, c), (b, d), for a sum diagonal y' = y - w gives (a, d),
      (b, c).  []   Symmetrically, if h >= w a diagonal contains at most one square of the horizontal sides,
      except, when w = h, the same two diagonals u0, v0.

## F.1 The three identities

For a set X of border squares put, for a set D as above (dominating or not),
  m(s) = number of occupied diagonals through the square s  (0, 1 or 2),
  beta_X(L) = number of squares of X on the diagonal L,
  U_X = number of needy squares s of X with m(s) = 0.

**Theorem F (frame identity).**  With X = the border,
  sum over occupied diagonals L of (2 - beta_X(L))
  + #{(L, s): L an occupied diagonal, s a non-needy border square on L}
  + #{needy border squares s with m(s) = 2}
  = 8k - 4n + 4 - 2(dR + dC + dT + dS) + U_X.
All three terms on the left are >= 0 (by (E4)), and U_X = 0 if D is dominating (by (N)).  For k = n/2 the
right side is 4 - 2(dR + dC + dT + dS) for dominating D.

*Proof.*  Count the pairs I = #{(L, s): L occupied diagonal, s border square on L} in two ways.
By diagonals: I = sum_L beta_X(L) = 2(|T| + |S|) - sum_L (2 - beta_X(L)), the sums over occupied L.
By squares: I = sum_{s in border} m(s).  A needy square contributes m(s) = 1 + [m(s) = 2] - [m(s) = 0]; the
non-needy squares contribute, in total, the number of pairs (L, s) with L occupied and s non-needy on L.
With (E3): I = N + #{needy, m = 2} - U_X + #{(L, s): s non-needy}.  Equating and substituting
|T| = k - dT, |S| = k - dS, n - |R| = n - k + dR, n - |C| = n - k + dC gives
2(2k - dT - dS) - [2(n - k + dR) + 2(n - k + dC) - 4] = 8k - 4n + 4 - 2(dR + dC + dT + dS).  []

**Theorem V (side identity).**  Assume w >= h and let X = the vertical sides.  Then
  #{occupied diagonals L with beta_X(L) = 0}
  + #{(L, s): L occupied, s a non-needy square of X on L}
  + #{needy squares s of X with m(s) = 2}
  = 4k - 2n - dT - dS - 2 dR + [w = h]([u0 occupied] + [v0 occupied]) + U_X.

*Proof.*  Count I = #{(L, s): L occupied, s in X on L}.  By (E5), beta_X(L) is 0 or 1, except
beta_X(u0) = beta_X(v0) = 2 when w = h; so I = (|T| + |S|) - #{occupied L, beta_X = 0}
+ [w = h]([u0 occupied] + [v0 occupied]).  By squares, as before and with (E3):
I = 2(n - |R|) + #{needy, m = 2} - U_X + #{(L, s): s non-needy}.  Equate and substitute.  []

**Theorem H.**  Assume h >= w and let X = the horizontal sides.  The same identity holds with dC in place of
dR.  (Apply Theorem V to the transposed set.)

Corollaries for a dominating k-set with k <= n - 2:
 (C1) dR + dC + dT + dS <= 4k - 2n + 2.
 (C2) if w >= h:  dT + dS + 2 dR <= 4k - 2n + 2[w = h];   if h >= w:  dT + dS + 2 dC <= 4k - 2n + 2[w = h].
For k = n/2: the deficits sum to at most 2; if w > h then dR = dT = dS = 0 and every term of Theorem V
vanishes: every occupied diagonal passes through exactly one square of the vertical sides, that square is
needy, and no needy vertical-side square lies on two occupied diagonals (so the 2k occupied diagonals and
the 2k needy vertical-side squares correspond bijectively).  This is what makes the case formulas easy.

### Remarks
 * "border" = boundary squares of the box, corners counted once (they are subtracted once in N).
 * The needy counts in (E3) are exact *because* a, b, c, d are extreme (E1); rows/columns inside the box may
   be occupied, and the corresponding border squares are then non-needy and enter the second term.
 * Degenerate boxes: w >= 1 and h >= 1 always (a < b, c < d are distinct lines); w = 1 or h = 1 is allowed
   and all proofs go through ((E4), (E5) do not use w, h >= 2); such boxes occur in the tests
   (29,203 sets with w = 1 or h = 1).  For k = n/2, (E1) gives w, h >= n - k - 1 + deficit >= k - 1.
 * "a diagonal meets the border in at most 2 squares" is (E4); a diagonal may meet it in 0 or 1 squares
   (weights 2 and 1 in the first term), e.g. the sum diagonal through the corner (a, c) meets it only there.
 * "covered": an occupied square is dominated by itself; needy squares are never occupied, and no border
   square is occupied (E2), so the identities never involve an occupied square.
 * The identities as quoted hold verbatim for k = n/2.  General k: the constants are
   8k - 4n + 4 - 2(sum of deficits) for (F) and 4k - 2n - dT - dS - 2dR (resp. 2dC) + [w = h](...) for (V), (H).
 * Gap found: none in the mathematics.  Two points that an implementation must get right: (i) (V) may only be imposed when w >= h and (H) only when h >= w (for
   w < h a diagonal can meet both vertical sides and the identity is false as stated); (ii) under a
   reflection the deficits dT and dS are exchanged, under a transposition dR and dC, so if cases are reduced
   by symmetry the deficit vector must be transformed together with the frame (or, as we do, all admissible
   deficit vectors are run for every canonical frame).

## F.2 Cases and the covering argument

A *case* for (n, k) is (ml, mr, mb, mt; dR, dC, dT, dS).  Every set D of k squares with >= 2 empty rows and
columns has exactly one case, case(D).  The 8 symmetries of the board act on cases (table
geom.case_images, tested against the geometric maps in verify_identities.py): the reflection x -> n-1-x
exchanges ml, mr and dT, dS; y -> n-1-y exchanges mb, mt and dT, dS; the transposition exchanges
(ml, mr) with (mb, mt) and dR with dC; the other symmetries are compositions.  A *frame* is (ml, mr, mb, mt);
a frame is canonical if it is lexicographically least among its (at most 8) images.

A case is *admissible* if: 0 <= each deficit <= k - 1;  ml + mr <= k - dC and mb + mt <= k - dR  (E1);
w = n-1-ml-mr >= 1, h = n-1-mb-mt >= 1;  (C1);  (C2).   Every dominating k-set (k <= n - 2) has an admissible
case, by (E1), Theorem F and Theorems V/H (each deficit is at most k - 1 because at least one line of each
type is occupied).

Case list L(n, k) := all (f; delta) with f a canonical frame and (f; delta) admissible  (geom.cases_by_frame).

**Proposition C.**  Let 1 <= k <= n - 2.  If for every case in L(n, k) the formula Phi(case) of F.3 is
unsatisfiable, then Q_n has no dominating set of size <= k.
*Proof.*  Suppose D dominates with |D| <= k; add squares to get |D| = k (supersets of dominating sets
dominate; k <= n^2).  Then at least n - k >= 2 rows and columns are empty.  Choose a symmetry g such that
the frame of g(D) is canonical (the frame of g(D) is the image of the frame of D, and the least image is
canonical).  g(D) is a dominating k-set, so its case is admissible and lies in L(n, k), and by Lemma E below
g(D) yields a model of Phi(case(g(D))).  Contradiction.  []

## F.3 The formula Phi(case)   (code/frame/enc.py)

Variables q[x][y]; oR[y], oC[x], oT[t], oS[s]; auxiliary e, f (waste) and counter variables.
  DEF   q[x][y] -> oR[y], oC[x], oT[y-x], oS[x+y];   o(L) -> OR of the q on the line L
  DOM   oR[y] v oC[x] v oT[y-x] v oS[x+y]                                    for every square (x, y)
  CARD  exactly k-dR of the oR, k-dC of the oC, k-dT of the oT, k-dS of the oS are true;
        exactly k of the q are true -- omitted if some deficit is 0 (then implied, see below)
  AMO   for every type with deficit 0: no two queens on a line of this type
  FRAME oC[x] for x < a and for x > b; not oC[a]; not oC[b]; oR[y] for y < c, y > d; not oR[c]; not oR[d]
  (F)   waste literals: for every diagonal L, 2 - beta(L) copies of o(L); for every diagonal L and every
        border square s on L that is not a corner, a variable e with (o(L) and nn(s)) -> e, where nn(s) is the
        literal "s is not needy" (oC[x] on a horizontal side, oR[y] on a vertical side); for every border
        square s = (x, y) a variable f with (oT[y-x] and oS[x+y] and not nn(s)) -> f (no nn for corners).
        Constraint: at most 8k - 4n + 4 - 2(dR+dC+dT+dS) waste literals are true.
  (V)   if w >= h: waste literals: o(L) for every diagonal L with no square on the vertical sides; e, f as
        above for the squares of the vertical sides.  Constraint: at most 4k - 2n - dT - dS - 2dR of them
        are true if w > h; if w = h: (number of true waste literals) + [not u0] + [not v0]
        <= 4k - 2n - dT - dS - 2dR + 2.
  (H)   if h >= w: the same for the horizontal sides, with dC.
All cardinality constraints are Sinz sequential counters (enc.atmost; "exactly" = at most + at most on the
negated literals; repeated literals are counted with multiplicity; tested exhaustively in test_enc.py).

**Lemma E (soundness of Phi).**  Let D be a dominating set of exactly k squares, k <= n - 2, with case(D) =
case.  Then Phi(case) is satisfiable.
*Proof.*  Set q = indicator of D, o(L) = [L contains a queen], e = [o(L) and nn(s)], f = [both diagonals of s
occupied and s needy].  DEF holds by definition; DOM because D dominates; CARD by the definition of the
deficits and |D| = k; FRAME by the definition of a, b, c, d and (E1).  AMO: if a type has deficit 0, the k
queens lie on k distinct lines of that type.  (F): the number of true waste literals is exactly the left
side of Theorem F (the nn-literal expresses non-neediness correctly on the border because of (E2)/(E3): on
a horizontal side the row is empty, so the square is needy iff its column is empty; corners are needy), and
U = 0, so it equals the bound.  (V), (H): likewise by Theorems V and H; for w = h the constraint reads
"left side <= 4k - 2n - dT - dS - 2dR + [u0] + [v0]".  A true cardinality constraint extends to the counter
variables (s_{i,j} := "at least j+1 of the first i+1 literals are true").  []
(code/frame/test_waste.py checks on random sets that the number of true waste terms of the encoder equals the
right-hand side of the identity, including the U term for non-dominating sets.)

Remark (why "exactly k of the q" may be dropped).  If, say, dR = 0, CARD makes exactly k rows occupied,
DEF puts a queen in each, AMO at most one: exactly k queens.  This only removes a redundant constraint;
soundness (Lemma E) does not depend on it.

Trust base of a certified run: Theorems F, V, H and Prop. C (above, 2 pages); geom.cases_by_frame and
geom.admissible (the case list); enc.py (the formula; about 150 lines, own sequential counter);
drat-trim.  No colour argument, no result of Weakley, no search program.

## F.4 Odd boards (and any other k)

Theorems F, V, H, the admissibility conditions, Proposition C and Lemma E are stated and proved for
arbitrary n and k <= n - 2; nothing in them uses the parity of n, colours, or k = n/2.  Specialisations:

 * n even, k = n/2:        (F) = 4 - 2(dR+dC+dT+dS);   (V) = -dT - dS - 2dR + [w=h]([u0]+[v0]).
 * n odd, k = (n+1)/2:     (F) = 8 - 2(dR+dC+dT+dS);   (V) = 2 - dT - dS - 2dR + [w=h]([u0]+[v0]);  (H) with dC.
   So the deficits sum to at most 4; for w > h: dT + dS + 2dR <= 2, and at most 2 - dT - dS - 2dR of the
   occupied diagonals fail to end in a needy square of a vertical side (counted with the three terms of
   Theorem V).  The frame has ml + mr <= k - dC and w + 1 >= (n-1)/2 + dC.
 * n odd, k = (n-1)/2:     (F) = -2(dR+dC+dT+dS) (so all deficits are 0 and all three terms of (F) vanish);
   (V) = -2 + [w=h]([u0]+[v0]) - dT - dS - 2dR, which is negative unless w = h and u0, v0 are both
   occupied.  Hence a dominating set of (n-1)/2 queens has a square box, both box diagonals occupied, and
   no waste at all -- the starting point of the known theory of the cases n = 3, 11.
 * n even, k = n/2 + 1:    (F) = 12 - 2(sum), (V) = 4 - dT - dS - 2dR + [w=h](...).

The same code (geom.py, enc.py, run_cases.py) is used for all of these; the symmetry reduction is over the
8 symmetries of the board in every case (no colour argument is involved, so odd n needs no change).
The price for odd n with k = (n+1)/2 is a weaker reduction: 58 deficit vectors instead of at most 9 per
frame (e.g. 128,941 cases for n = 35), and two units of slack in each side identity.

## F.5 Further sound constraints (tested, NOT used in any reported run)

**Lemma P (colour balance).**  -dT <= #(occupied difference diagonals with t even) - #(occupied sum diagonals
with s even) <= dS.   *Proof.*  t = y - x and s = x + y have the parity of x + y, so the E queens on squares
with x + y even lie on the even diagonals of both kinds.  They occupy T_e even difference diagonals, so
E >= T_e, and E - T_e (the number of even queens beyond the first on their difference diagonal) is at most the
total excess k - |T| = dT; likewise 0 <= E - S_e <= dS.  Subtract.  []

**Lemma M (moments).**  If dR = dC = dT = dS = 0, then  sum_{t in T} t = sum_{y in R} y - sum_{x in C} x,
sum_{s in S} s = sum_{y in R} y + sum_{x in C} x,  and  sum_T t^2 + sum_S s^2 = 2 sum_R y^2 + 2 sum_C x^2.
*Proof.*  With all deficits 0 every occupied line of each type carries exactly one queen, so each sum over
occupied lines equals the corresponding sum over the queens, and for one queen t = y - x, s = x + y,
t^2 + s^2 = 2x^2 + 2y^2.  []   (These are the constraints (1), (2) of Weakley 2022.)

Both are available in enc.py (`use_P`, `use_M`; the moment identities are imposed modulo 2, 3, 4, 5, 7, 9, 11, 13
by one-hot chains).  On the hardest zero-deficit square-box cases of odd boards they did not help:
(n, k) = (15, 8), frame (0,1,0,1): 7.9 s without, 6.5 s with P, 12.7 s with M; (19, 10), frame (0,1,0,1): 35.2 /
32.3 s without, 37.6 s with P, 56.6 s with M.  So the hard cases are not hard because of inconsistent line sets.

**Lemma S (side pigeonhole).**  The occupied diagonals that meet one side of the box number at least the needy
squares of that side.  *Proof.*  A side lies in one row or one column, so a diagonal contains at most one of
its squares; each needy square lies on an occupied diagonal (N).  []   (`use_S`; tested, no gain: 8.6 s vs 7.8 s
and 37.2 s vs 35 s on the two cases above.)

## F.6 Residual symmetry and cubes inside one case (code/frame/hard_test.py, run_hard.py; used only for hard cases)

Let c be a case and G_c the set of board symmetries g with g(c) = c in the action of F.2 (computed by
geom.case_images; G_c is a subgroup of the 8 symmetries).  For a set D let v(D) = (oR[0..n-1], oC[0..n-1]) be its
row/column occupancy vector.  For each g there is a fixed coordinate permutation pi_g with v(g(D)) = pi_g(v(D))
(e.g. transposition exchanges the two halves; x -> n-1-x reverses the column half).
SBP(c) := for every g in G_c, v <=_lex pi_g(v) (lex-leader chain: variables e_i = "equal so far").

**Lemma R.**  If some dominating k-set has case c, then Phi(c) and SBP(c) is satisfiable.
*Proof.*  If D is a dominating k-set with case c and g is in G_c, then g(D) is a dominating k-set with case
g(c) = c.  Take g in G_c minimising v(g(D)) lexicographically and put D' = g(D).  For every h in G_c,
pi_h(v(D')) = v(hg(D)) >= v(D') since hg is in G_c.  D' gives a model of Phi(c) by Lemma E, and the chain
variables e_i := "equal so far" satisfy the lex clauses.  []
Proposition C therefore remains valid with Phi(c) and SBP(c) in place of Phi(c) for any subset of the cases.
(code/frame/test_sbp.py: the permutations pi_g agree with the geometric maps on random sets; for all 3,566 cases
with a non-trivial stabiliser of the eight pairs (n,k) from (4,2) to (10,5), the models of Phi and SBP expanded
by G_c are exactly the models of Phi.)

Cubes.  For a case with box [a,b] x [c,d], layer j consists of the four variables oR[c+j], oR[d-j], oC[a+j],
oC[b-j] (defined while c+j < d-j and a+j < b-j).  The 16 assignments of a layer are exhaustive and exclusive, so
a formula is unsatisfiable iff it is unsatisfiable under each of them; run_hard.py solves the formula as it is
and replaces a cube that exceeds the time limit by its 16 children; check_hard.py verifies that the
UNSAT/VERIFIED cubes of each case form such a cover and can rebuild every CNF hash.
