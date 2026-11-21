# Queen domination: Lean 4 formalization of the frame-method reduction (Layer 1)

Lean 4 + Mathlib formalization of the mathematical reduction behind the computer-assisted proofs that
no 16 queens dominate the 32 x 32 board (gamma(Q_32) >= 17) and that no 18 queens dominate the 35 x 35
board (gamma(Q_35) >= 19).  With the explicit dominating sets of 17 resp. 19 queens (checked in Lean)
this gives gamma(Q_32) = 17 and gamma(Q_35) = 19, each modulo the SAT certificates.  The source of the
mathematics is the hand proofs in `../code/frame/PROOFS.md` (sections F.0 - F.2, F.4, F.5, the semantic
parts of F.3 and of Lemma R in F.6; the paper gives the same proofs) and the code `../code/frame/geom.py`,
`../code/frame/enc.py`.  Paths below starting with `frame/` refer to `../code/frame/` (code) and
`../data/frame/` (records, xz-compressed) of this repository.

Scope: **Layer 1 only** - the combinatorial reduction "a dominating k-set yields, after a board
symmetry, a set satisfying the constraints of one case of an explicit case list".  The CNF encoding
of the cases and the SAT/DRAT certificates are **not** formalized (see "What is outside Lean").

Everything is proved for general `n` and `k <= n - 2`; even `n` with `k = n/2`, odd `n` with
`k = (n+1)/2`, and the pairs `(32, 16)`, `(35, 18)` are specialisations (the two concrete pairs share all
code; only the generated case data and one-line instances differ).
No `sorry`, no `admit`, no new axioms, no `native_decide`.

## Build

    lake exe cache get  # downloads the prebuilt Mathlib (about 5 GB in .lake/)
    lake build          # builds the library QueenDom and the axiom report Axioms.lean
    lake env lean Axioms.lean    # prints the axiom report (AXIOMS.txt)

Toolchain `leanprover/lean4:v4.35.0` (installed by elan from `lean-toolchain`), Mathlib `v4.35.0`
(commit 56a005855e, pinned in `lake-manifest.json`).  `python3 scripts/verify.py --lean` in the repository
root runs these steps and checks the axiom report.
Clean build of this project (Mathlib prebuilt): about 9 minutes wall on a loaded machine (12 min CPU),
see "Build time" below.  The slow files are the generated kernel computations `QueenDom/Cases35Pieces.lean` and `QueenDom/Cases32Pieces.lean`.

## Conventions

* Squares are `(x, y) : Fin n × Fin n`, `x` = column, `y` = row (as in PROOFS.md and `geom.py`).
* `dg p = y - x : ℤ` is the difference diagonal, `sm p = x + y : ℕ` the sum diagonal.
* `Attacks p q` = distinct squares on a common line = adjacency of the queen's graph `queenGraph n`.
  `Dominating D` = every square is in `D` or attacked by a square of `D`.
* `occR D, occC D, occT D, occS D` = occupied rows, columns, difference diagonals, sum diagonals;
  `defR D = |D| - |R|` etc. (natural numbers; `occR_card_add_defR : |R| + dR = |D|`).
* `Needy D p` = column and row of `p` are both empty.
* `IsFrame D a b c d` = `a < b` are the least and greatest empty columns, `c < d` the least and
  greatest empty rows.  `box`, `border`, `vsides`, `hsides` as in F.0 (`w = b - a`, `h = d - c`).
* For a set `X` of squares: `betaT X t`, `betaS X s` = number of squares of `X` on a diagonal;
  `wasteF D X = Σ_{L occupied} (2 - β_X(L))`;  `zeros D X = #{L occupied : β_X(L) = 0}`;
  `waste2 D X = #{(L, s) : L occupied, s ∈ X non-needy on L}`;
  `needy2 D X = #{s ∈ X needy, m(s) = 2}`;  `uncov D X = U_X = #{s ∈ X needy, m(s) = 0}`;
  `sqTerm D a b c d = [w = h]([u0 occupied] + [v0 occupied])`, `u0 = {t = c - a}`, `v0 = {s = a + d}`.

## Files

| file | content |
|------|---------|
| `QueenDom/Defs.lean` | all definitions of F.0 / F.1 |
| `QueenDom/Basic.lean` | occupied lines, domination, (N), padding lemma, existence/uniqueness of the frame |
| `QueenDom/Geometry.lean` | (E1)-(E4): margins, border, side and border cardinalities, needy counts, "a diagonal meets the border at most twice" |
| `QueenDom/Identities.lean` | (E5), the double count, Theorems F, V, H |
| `QueenDom/Consequences.lean` | (C1), (C2), the case k = n/2: deficit bound and rigidity |
| `QueenDom/Symmetry.lean` | the 8 symmetries, action on dominating sets and frames, canonical frames |
| `QueenDom/Cases.lean` | `Case`, `Admissible` (decidable), `CaseSat`, case-split completeness theorem, Proposition C |
| `QueenDom/SymmetryCase.lean` | action of the symmetries on deficits and cases (table `geom.case_images`), invariance of admissibility |
| `QueenDom/Enum.lean` | `enumFrames`, `casesOfFrame`, `enumCases` (= `geom.cases_by_frame`), `mem_enumCases`; the split by horizontal margins `casesPQ`, `marginPairs`, `enumCases_eq_pieces` |
| `QueenDom/Main.lean` | `gamma`; final theorems for general (n, k), for even n = 2k, for odd n = 2k - 1; generic statements for an explicit list `L` with `enumCases n k = L` (case split, cover, frames, lower bound) and the table form `enumCases_eq_table` |
| `QueenDom/LemmaR.lean` | F.6, Lemma R (semantic part): `CaseSat.sym`, `SymBreak`, `lemmaR`, Proposition C with symmetry breaking |
| `QueenDom/Cases32Data.lean` | GENERATED: the 11,466 cases of the run log `frame/out/d_32_16.jsonl`, one def per (ml, mr), table `caseCodes32T` |
| `QueenDom/Cases32Pieces.lean` | GENERATED: 153 kernel computations (one per (ml, mr)), assembled to `enumCases 32 16 = decoded table` |
| `QueenDom/Cases32.lean` | n = 32: the case list of the log is `L(32, 16)`; 3321 frames; 17-queen upper bound; final theorems |
| `QueenDom/Cases35Data.lean` | GENERATED: the 128,941 cases of the n = 35 run (`d_35_18.jsonl`, `d_35_18_sq.jsonl`, `h_35_18.jsonl`) |
| `QueenDom/Cases35Pieces.lean` | GENERATED: 190 kernel computations (one per (ml, mr)), assembled to `enumCases 35 18 = decoded table` |
| `QueenDom/Cases35.lean` | n = 35: the case list of the run is `L(35, 18)`; 5050 frames; 19-queen upper bound; final theorems |
| `QueenDom/Examples.lean` | sanity check on the 6 x 6 board |
| `QueenDom/Extras.lean` | F.5: Lemma P (colour balance) and Lemma M (moments), the options `use_P`, `use_M` of `enc.py`; not used in any run |
| `Axioms.lean` | `#print axioms` for 116 theorems, plus a loop over all 343 piece theorems (output in `AXIOMS.txt`) |
| `scripts/runlog.py` | reads the run logs; refutation rule of `frame/final_check35.py` (plain UNSAT + VERIFIED record, or a cover by verified sbp cube records) |
| `scripts/gen_cases.py` | `gen_cases.py N K frame/out QueenDom` generates `Cases<N>Data.lean` and `Cases<N>Pieces.lean` |
| `scripts/check_cases.py` | checks `Cases<N>Data.lean` (read as text) against the run records and against `geom.cases_by_frame(N, K)` |
| `scripts/CrossCheck.lean`, `scripts/crosscheck.py` | compares `enumCases n k` with `geom.cases_by_frame(n, k)` for 31 pairs (n, k), including (35, 18) |

## Map: hand proof (PROOFS.md) -> Lean

### F.0 Setting

| hand proof | Lean |
|------------|------|
| domination via lines (clause DOM) | `dominating_iff`; `dominating_iff_adj` (= domination in `queenGraph n`) |
| (N) needy squares lie on an occupied diagonal | `Dominating.needy_covered`; needy squares are unoccupied: `Needy.not_mem` |
| deficits are >= 0 | `occR_card_le` ... `occS_card_le`, `occR_card_add_defR` ... |
| standing assumption, automatic for k <= n-2 | `exists_isFrame`, `exists_isFrame_of_card`; uniqueness `IsFrame.unique` |
| padding (in the proof of Prop. C) | `Dominating.mono`, `exists_dominating_card_eq` (`|D| <= k <= n*n` gives a dominating set of size exactly `k`) |
| (E1) `ml + mr <= |C|`, `mb + mt <= |R|` | `IsFrame.margin_cols`, `IsFrame.margin_rows`; `IsFrame.width_ge`, `IsFrame.height_ge` (`w + 1 >= n - |C|`) |
| (E2) no border square is occupied | `IsFrame.border_not_mem` |
| sides have 2(h+1), 2(w+1) squares; corners | `card_vsides`, `card_hsides`, `border_eq_union`, `vsides_inter_hsides`, `card_border` (`= 2w + 2h`) |
| (E3) needy iff row (column) empty on a side | `IsFrame.needy_vsides_iff`, `IsFrame.needy_hsides_iff`, `IsFrame.needy_corner` |
| (E3) exact needy counts `2(n-|R|)`, `2(n-|C|)`, `N` | `IsFrame.card_needy_vsides`, `IsFrame.card_needy_hsides`, `IsFrame.card_needy_border` (`N + 4 = 2(n-|R|) + 2(n-|C|)`) |
| (E4) a diagonal meets the border in <= 2 squares | `betaT_border_le_two`, `betaS_border_le_two` (no hypothesis on a, b, c, d at all) |
| (E5), w >= h, vertical sides | `betaT_vsides_le_one`, `betaS_vsides_le_one`; square box: `vsides_filter_u0` (= {(a,c),(b,d)}), `vsides_filter_v0` (= {(a,d),(b,c)}), `betaT_vsides_u0`, `betaS_vsides_v0` (= 2) |
| (E5), h >= w, horizontal sides | `betaT_hsides_le_one`, `betaS_hsides_le_one`, `hsides_filter_u0`, `hsides_filter_v0`, `betaT_hsides_u0`, `betaS_hsides_v0` |

Degenerate boxes: all statements hold for every `a < b`, `c < d` (so `w = 1` or `h = 1` is included);
the square case `w = h` is explicit in (E5) and in `sqTerm`.

### F.1 Identities (exact equalities, any D with a frame, dominating or not)

| hand proof | Lean |
|------------|------|
| double count `I = Σ_L β(L) = Σ_s m(s)` | `sum_betaT`, `sum_betaS`, `incidences_by_squares`, `double_count`; `waste2_eq_card_pairs` (the second term is literally a number of pairs) |
| **Theorem F** | `IsFrame.frame_identity` (in ℤ, verbatim: `... = 8k - 4n + 4 - 2(dR+dC+dT+dS) + U`), `IsFrame.frame_identity_nat` (in ℕ via |R|,|C|,|T|,|S|) |
| **Theorem V** (hypothesis `w >= h`) | `IsFrame.side_identity_V` (ℤ, verbatim), `IsFrame.side_identity_V_nat`; diagonal count `incidences_sides` |
| **Theorem H** (hypothesis `h >= w`) | `IsFrame.side_identity_H`, `IsFrame.side_identity_H_nat` |
| `U = 0` for dominating D | `Dominating.uncov_eq_zero`; `IsFrame.frame_identity_dom`, `IsFrame.side_identity_V_dom`, `IsFrame.side_identity_H_dom` |
| (C1) | `IsFrame.deficit_bound` |
| (C2) | `IsFrame.deficit_bound_V`, `IsFrame.deficit_bound_H` |
| k = n/2: deficits sum to <= 2 | `IsFrame.deficit_sum_le_two`; square box: `IsFrame.deficit_square` |
| k = n/2, w > h: `dR = dT = dS = 0`, all terms of (V) vanish | `IsFrame.rigid_V` (each occupied diagonal has exactly one square on the vertical sides; a vertical-side square on an occupied diagonal is needy; none lies on two occupied diagonals), `IsFrame.rigid_V_needy` (each needy vertical-side square lies on exactly one occupied diagonal), `IsFrame.rigid_V_counts` (2k needy squares, |T| = |S| = k) |
| the same for h > w | `IsFrame.rigid_H`, `IsFrame.rigid_H_needy`, `IsFrame.rigid_H_counts` |

### F.4 Odd boards

All theorems above are for arbitrary `n` and `k <= n - 2`.  The specialisations listed in F.4:

| hand proof | Lean |
|------------|------|
| n odd, k = (n+1)/2: deficits sum to <= 4; for w > h: `dT + dS + 2dR <= 2` (resp. `dC` for h > w) | `IsFrame.deficit_sum_le_four`, `IsFrame.deficit_V_odd`, `IsFrame.deficit_H_odd` |
| n odd, k = (n-1)/2: square box, both box diagonals occupied, all deficits 0, no waste | `IsFrame.odd_minus` (with `sqTerm_eq_two_iff`) |
| n odd, k = (n+1)/2: the admissibility conditions with the constants of F.4 (deficit sum <= 4; `dT + dS + 2dR <= 2` if w > h; `dT + dS + 2dC <= 2` if h > w; both `<= 4` if w = h) | `admissible_odd_iff` |
| n odd, k = (n+1)/2 >= 3: case split and Proposition C | `main_odd`, `odd_lt_gamma_of_cases_unsat` |

### F.2 Cases, symmetries, covering

| hand proof / code | Lean |
|-------------------|------|
| the 8 symmetries (`geom.sym_maps`) | `Sym` (three bits: reflect columns, reflect rows, transpose), `Sym.toEquiv`, `Sym.toEquiv_apply`, `Sym.image`, `Sym.image_eq_map`, `Sym.card_image` |
| symmetries preserve domination | `Dominating.map`, `Dominating.sym` |
| frame of g(D) = image of the frame | `IsFrame.map_reflX`, `IsFrame.map_reflY`, `IsFrame.map_transp`, `HasMargins.sym` (action `Sym.actFrame`) |
| deficits under symmetries; table `geom.case_images` | `defT_map_reflX` etc. (12 lemmas), `Sym.actCase`, `caseImages`, `caseImages_eq`, `HasCase.sym` |
| canonical frame = lex-least among its images | `Canon` (decidable), `canon_iff_forall`, closed form `canon_iff`; every frame has a canonical image: `exists_canon` |
| `geom.admissible` | `Admissible n k cs` (decidable, in ℕ); `admissible_iff_py`: equivalent to the literal transcription `AdmissiblePy` of the Python function; `admissible_half_iff` (k = n/2) |
| every dominating k-set has an admissible case | `admissible_of_frame` |
| `geom.case_of` | `caseOf` |
| case list `L(n, k)` (`geom.cases_by_frame`) | `CanonAdm n k cs`; `enumCases n k` with `mem_enumCases : cs ∈ enumCases n k ↔ CanonAdm n k cs` |
| admissibility is symmetric; the list covers all admissible cases up to symmetry | `Admissible.actCase`, `exists_canonAdm_actCase` |
| **Proposition C** | `no_dominating_of_cases_unsat`, `lt_gamma_of_cases_unsat` |

### F.3 (semantic part of Lemma E only)

`CaseSat n k cs D` is the semantic content of the formula `Φ(case)`; one field per clause group of
`frame/enc.py`:

| clause group of `enc.py` | field of `CaseSat` / `FrameConstraints` |
|--------------------------|------------------------------------------|
| DEF | definitional (`occR` ... are the images of `D`) |
| DOM | `dom : Dominating D` (`dominating_iff` is the clause form) |
| CARD (lines) | `cardR : |R| + dR = k`, `cardC`, `cardT`, `cardS` |
| CARD (queens) | `card : |D| = k` |
| AMO | `amoR : dR = 0 → Set.InjOn Prod.snd D`, `amoC`, `amoT`, `amoS` (`defR_eq_zero_iff` ...) |
| FRAME | `IsFrame D a b c d` with `a = ml`, `b + mr + 1 = n`, `c = mb`, `d + mt + 1 = n` |
| (F) | `wasteF + waste2 + needy2 + 4n + 2(dR+dC+dT+dS) = 8k + 4` on the border |
| (V), if `w >= h` | `zeros + waste2 + needy2 + 2n + dT + dS + 2dR = 4k + sqTerm` on the vertical sides |
| (H), if `h >= w` | the same on the horizontal sides with `dC` |

The CNF imposes (F), (V), (H) as upper bounds on the number of true waste literals; the equalities
above imply these bounds (for `w = h` the CNF adds `[not u0] + [not v0]` on the left and `2` on the
right, which is the same inequality).

| hand proof | Lean |
|------------|------|
| Lemma E, semantic part: a dominating k-set satisfies the constraints of its case | `caseSat_of_frame` |

`CaseSat` mirrors `enc.py` with its default options `use_F`, `use_V`, `use_H`, as used for the n = 32
run (the version with sha256 011c422c... recorded in `frame/out/SHA256SUMS_code_n32run.txt`).

### F.5 Two further sound constraints (not used in any reported run)

`enc.py` was later extended by two optional clause groups (off by default).  The underlying lemmas are
proved in `QueenDom/Extras.lean`; they are not fields of `CaseSat`.

| hand proof (option of `enc.py`) | Lean |
|---------------------------------|------|
| Lemma P (`use_P`), colour balance: `-dT <= |T_even| - |S_even| <= dS`, any D | `colour_balance` |
| Lemma M (`use_M`), all deficits 0: `Σ_T t = Σ_R y - Σ_C x`, `Σ_S s = Σ_R y + Σ_C x`, `Σ_T t² + Σ_S s² = 2Σ_R y² + 2Σ_C x²` | `moment_T`, `moment_S`, `moment_sq` |

### F.6 Residual symmetry breaking (Lemma R, semantic part)

| hand proof | Lean |
|------------|------|
| `G_c` = symmetries fixing the case (`hard_test.stabiliser`) | `g.actCase cs = cs` |
| `v(D) = (oR[0..n-1], oC[0..n-1])`, `SBP(c)`: `v <=lex v(g(D))` for `g in G_c` (`false < true`, as in `sbp_clauses`) | `occVec`, `SymBreak cs D` |
| a set satisfying the constraints of `c` has case `c`; `g(D)` satisfies the constraints of `g(c)` | `CaseSat.hasCase`, `CaseSat.sym` |
| **Lemma R**: if `Φ(c)` has a (semantic) model, then `Φ(c) ∧ SBP(c)` has one | `lemmaR` |
| Proposition C with `Φ ∧ SBP` for any subset of the cases | `lt_gamma_of_cases_unsat_symBreak`, `lt_gamma_of_cases_unsat_mixed` |

The proof of `lemmaR` does not use the group structure of the eight symmetries: the sets reachable from
`D` by repeated application of symmetries fixing `c` form a finite set whose members all satisfy the
constraints of `c` (`CaseSat.sym`); a member with lexicographically least `occVec` is the required model.
Not formalized: that `sbp_clauses` (with the coordinate permutations `π_g` of the code) expresses
`SymBreak` (Layer 2; `frame/test_sbp.py` tests `v(g(D)) = π_g(v(D))`), and the cube splitting of
`run_hard.py` (a purely propositional split: the 16 assignments of four variables are exhaustive, checked
textually by `frame/check_hard.py` / `final_check35.py`).

### Main theorems

| statement | Lean |
|-----------|------|
| **Case-split completeness** (general n, k <= n-2): a dominating k-set has a symmetric image satisfying `CaseSat` for some case with canonical frame and admissible (frame, deficits) | `case_split` |
| the same with the list `enumCases n k` | `case_split_enum` |
| the same for even n = 2k >= 4, and for odd n = 2k - 1 >= 5 | `case_split_half`, `main_even`; `main_odd` |
| UNSAT of all cases implies `γ(Q_n) > k` | `no_dominating_of_cases_unsat`, `lt_gamma_of_cases_unsat`, `half_lt_gamma_of_cases_unsat`, `odd_lt_gamma_of_cases_unsat` |
| an explicit list `L` with `enumCases n k = L`: membership, case split, cover, frames, lower bound | `mem_of_enumCases_eq`, `case_split_of_enumCases_eq`, `cover_of_enumCases_eq`, `frames_of_enumCases_eq`, `card_frames_of_enumCases_eq`, `card_lt_of_enumCases_eq`, `lt_gamma_of_enumCases_eq` |
| lower bound + dominating set of size k + 1 gives `γ = k + 1` | `gamma_eq_of_lt_of_dominating` |
| n = 32: the case list of the run log is `L(32, 16)` | `enumCases_32_16 : enumCases 32 16 = cases32` (kernel computation), `mem_cases32`, `cases32_length` (11,466), `enumFrames_32_16_length`, `enumFrames_32_16_nodup`, `card_frames_cases32` (3321 frames) |
| n = 32: the log covers every admissible (frame, deficits) up to symmetry | `cases32_cover` |
| n = 32: case split | `case_split_32` |
| n = 32: UNSAT of the 11,466 cases implies every dominating set has >= 17 queens | `seventeen_le_card_of_cases32_unsat`, `seventeen_le_gamma_32_of_cases32_unsat` |
| n = 32: 17 queens dominate (`frame/out/plus1_32.json`); `γ(Q_32) = 17` modulo the certificates | `q32_card`, `q32_dominating`, `gamma_32_le`; `gamma_32_eq_17_of_cases32_unsat` |
| n = 35: the case list of the run is `L(35, 18)` | `enumCases_35_18 : enumCases 35 18 = cases35` (190 kernel computations), `mem_cases35`, `cases35_length` (128,941), `enumFrames_35_18_length`, `enumFrames_35_18_nodup`, `card_frames_cases35` (5050 frames) |
| n = 35: the run covers every admissible (frame, deficits) up to symmetry | `cases35_cover` |
| n = 35: case split | `case_split_35` |
| n = 35: UNSAT of the 128,941 cases implies every dominating set has >= 19 queens | `nineteen_le_card_of_cases35_unsat`, `nineteen_le_gamma_35_of_cases35_unsat` |
| n = 35: the same when, for each case, the plain or the symmetry-broken constraints are UNSAT (the form of the run) | `nineteen_le_gamma_35_of_cases35_unsat_mixed` |
| n = 35: 19 queens dominate (`frame/out/q35_19.json`); `γ(Q_35) = 19` modulo the certificates | `q35_card`, `q35_dominating`, `gamma_35_le` (unconditional); `gamma_35_eq_19_of_cases35_unsat`, `gamma_35_eq_19_of_cases35_unsat_mixed` |

The final theorems read

    theorem seventeen_le_gamma_32_of_cases32_unsat
        (H : ∀ cs ∈ cases32, ¬ ∃ D : Finset (Sq 32), CaseSat 32 16 cs D) : 17 ≤ gamma 32
    theorem nineteen_le_gamma_35_of_cases35_unsat
        (H : ∀ cs ∈ cases35, ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) : 19 ≤ gamma 35
    theorem gamma_35_eq_19_of_cases35_unsat
        (H : ∀ cs ∈ cases35, ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) : gamma 35 = 19
    theorem gamma_35_eq_19_of_cases35_unsat_mixed
        (H : ∀ cs ∈ cases35, (¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D) ∨
          ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D ∧ SymBreak cs D) : gamma 35 = 19

(`cases35` = the decoded list of `Cases35Data.lean`; `gamma_35_le : gamma 35 ≤ 19` is unconditional) and,
for general even and odd n,

    theorem main_even {k : ℕ} (hk : 2 ≤ k) (D : Finset (Sq (2 * k))) (hD : Dominating D)
        (hc : D.card = k) :
        ∃ g : Sym, ∃ cs ∈ enumCases (2 * k) k, CaseSat (2 * k) k cs (g.image D)
    theorem main_odd {k : ℕ} (hn : n + 1 = 2 * k) (hk : 3 ≤ k) (D : Finset (Sq n)) (hD : Dominating D)
        (hc : D.card = k) : ∃ g : Sym, ∃ cs ∈ enumCases n k, CaseSat n k cs (g.image D)

## The case lists inside Lean (n = 32 and n = 35)

`scripts/gen_cases.py N K frame/out QueenDom` generates, from the run records, two files:

* `QueenDom/Cases<N>Data.lean`: the refuted cases, each one decimal numeral (two digits per margin, one per
  deficit), one sorted `def caseCodes<N>_<ml>_<mr>` per pair of horizontal margins, and the table
  `caseCodes<N>T` (row `ml`, column `mr`).  The list of the run is `caseCodes<N> = tableList K caseCodes<N>T`
  (concatenation in the order of `marginPairs K`, i.e. lexicographic), `cases<N> = caseCodes<N>.map Case.ofCode`.
* `QueenDom/Cases<N>Pieces.lean`: for every pair `(ml, mr)` with `ml + mr <= K` one theorem
  `piece<N>_<ml>_<mr> : casesPQ N K ml mr = (tableCodes caseCodes<N>T ml mr).map Case.ofCode := by decide +kernel`
  (190 for n = 35, 153 for n = 32; empty pieces included), and the assembly
  `enumCases_<N>_<K>_table` via the generic lemma `enumCases_eq_table` (which rests on the proved
  decomposition `enumCases_eq_pieces : enumCases n k = (marginPairs k).flatMap (casesPQ n k)`).

Why pieces: a single `decide +kernel` for `enumCases 35 18 = cases35` (128,941 cases) used more than 65 GB
of memory after 3.5 minutes (kernel caches) and was abandoned.  Each piece needs < 1 GB and a few seconds,
and the pieces of a file are checked in parallel.  `decide +kernel` adds no axiom; the axiom report checks
all 343 piece theorems.  `mem_enumCases` (a proof, not a computation) identifies the enumeration with the
set of cases with canonical frame and admissible (frame, deficits), for all `n, k`.  So "the 5050 frames /
128,941 cases of the n = 35 run cover every admissible (frame, deficit vector) up to symmetry" is a theorem
(`mem_cases35`, `cases35_cover`, `card_frames_cases35`), and likewise for n = 32.

Checks outside Lean (they tie the Lean text to the records; the first two are the `leandata` step of
`scripts/verify.py`):

    python3 -B scripts/check_cases.py 35 18 QueenDom/Cases35Data.lean ../data/frame ../code/frame
    python3 -B scripts/check_cases.py 32 16 QueenDom/Cases32Data.lean ../data/frame ../code/frame
    lake env lean scripts/CrossCheck.lean | python3 -B scripts/crosscheck.py ../code/frame

`check_cases.py` reads the Lean data file as text, rebuilds `tableList K caseCodes<N>T`, and checks:
(1) table layout and margins of every def, list strictly increasing; (2) the set of case keys occurring in
any record of `d_N_K.jsonl`, `d_N_K_sq.jsonl`, `h_N_K.jsonl` equals the Lean list (nothing missing, nothing
extra); (3) every case of the list is refuted (plain record UNSAT + drat VERIFIED, or a cover of the case by
verified sbp cube records, the rule of `final_check35.py`), no SAT record; (4) the list equals
`geom.cases_by_frame(N, K)` in the same order.  Result for n = 35 (2026-11-21):

    lean_cases 128941, lean_frames 5050, strictly_increasing true
    d_35_18.jsonl     115608 records  sha256 c01d73d0...e1a5
    d_35_18_sq.jsonl   12755 records  sha256 57fac317...c976
    h_35_18.jsonl       1756 records  sha256 257d74c1...0b0f   (hashes as in frame/out/SHA256SUMS_n35.txt)
    case_keys_in_records 128941 = Lean list (missing 0, extra 0)
    refuted_plain 128356, refuted_by_cubes 585 (508 unsplit), sat_records 0
    equal_to_geom_same_order true                                                  -> OK

(the counts 128,356 / 508 / 77 agree with `frame/out/final_check_35_18.json`).  For n = 32: 11,466 cases,
all plain UNSAT + VERIFIED in `d_32_16.jsonl` (sha256 749888e9...9bc5), equal to `geom.cases_by_frame(32, 16)`;
the numerals are the same as in the previous single-list version of `Cases32Data.lean`.  `CrossCheck.lean`
compares the compiled `enumCases n k` with `geom.cases_by_frame(n, k)` for 31 pairs, now including (35, 18).

## What is outside Lean (exactly)

The hypotheses `H` of the final theorems,

    ∀ cs ∈ cases32, ¬ ∃ D : Finset (Sq 32), CaseSat 32 16 cs D
    ∀ cs ∈ cases35, ¬ ∃ D : Finset (Sq 35), CaseSat 35 18 cs D      (or the `_mixed` form with SymBreak)

are not proved in Lean.  They are what the computations establish, in steps that are all outside this
project:

1. **Encoding (rest of Lemma E, F.3; Layer 2).**  For each case `cs`: if some `D` satisfies
   `CaseSat n k cs D` then the CNF `Φ(cs)` written by `frame/enc.py` is satisfiable.  This involves the
   definitional variables, the waste variables `e`, `f` (their forced values are counted by
   `wasteF`/`zeros`, `waste2`, `needy2`; on the border "non-needy" is expressed by a single line literal,
   justified by `IsFrame.needy_vsides_iff`, `IsFrame.needy_hsides_iff`, `IsFrame.needy_corner`), the
   pairwise AMO clauses and the Sinz sequential counters.  Not formalized.  (The n = 35 run used `enc.py`
   sha256 4ad103fb...; with its default options, `use_P = use_M = use_S = False`, it writes the same clauses
   as the n = 32 version 011c422c... for which `CaseSat` was written.)
2. **Encoding of the symmetry breaking and cubes (585 of the n = 35 cases).**  That `hard_test.sbp_clauses`
   expresses `SymBreak` (via the coordinate permutations `π_g`), and that the 16 cubes of a layer are
   exhaustive.  Not formalized; the semantic Lemma R is (`lemmaR`, `..._mixed`).
3. **SAT certificates.**  Each CNF is unsatisfiable: CaDiCaL + DRAT proofs checked by drat-trim (records
   with CNF hashes in `frame/out/d_32_16.jsonl`, `d_35_18.jsonl`, `d_35_18_sq.jsonl`, `h_35_18.jsonl`;
   the CNF hashes were rebuilt by `final_check35.py`).  Not formalized, not re-checked here.

Also outside Lean:

4. The textual link between `Cases<N>Data.lean` and the run records (`scripts/check_cases.py`).  Lean
   proves that the list equals `L(N, K)`, so this check only says that the run has a refuting record (or
   cube cover) for each of these cases and no other case keys.

The upper bounds are in Lean: `gamma_32_le`, `gamma_35_le` (`decide +kernel` over all squares).

## Axioms

`lake build Axioms` prints the axioms of 116 theorems (saved in `AXIOMS.txt`) and runs a loop over all
343 piece theorems `piece32_*`, `piece35_*` of the case lists.  Every one of them depends only on a subset
of `propext`, `Classical.choice`, `Quot.sound`.  No `sorryAx`, no `Lean.ofReduceBool` (`native_decide` is
not used anywhere).

## Remarks on the hand proofs

No mathematical gap was found in PROOFS.md F.0 - F.2, F.4, F.5 or in the semantic parts of F.3 and of Lemma R (F.6); every statement
was formalized as written (the identities with the constants and hypotheses of the hand proof).
Points where the formalization differs from or sharpens the text:

* Theorem H is proved directly (same argument as V with rows and columns exchanged), not by
  transposing; the transposition is formalized separately (`IsFrame.map_transp`, `defR_map_transp`,
  ...).
* Proposition C assumes `1 <= k <= n - 2`.  The lower bound `1 <= k` is not needed as a hypothesis:
  a dominating set of a non-empty board is non-empty (`Dominating.nonempty`), which gives "each
  deficit is at most k - 1".  The Lean theorem assumes only `k + 2 <= n`.
* (E4) needs no assumption on the box at all; (E5) and the exceptional diagonals `u0`, `v0` need
  `a < b` and `c < d` only (so that the two corners are distinct), which holds for every frame.
* The "bijection" remark after (C2) is formalized as three statements (`rigid_V`, `rigid_V_needy`,
  `rigid_V_counts`) rather than as an explicit bijection.
* Remark (ii) at the end of F.1 (deficits must be transformed with the frame) is formalized in
  `SymmetryCase.lean`; the case-split theorem does not need it, because the case list contains every
  admissible deficit vector for every canonical frame - exactly as the text says.
* F.4 (odd n, k = (n+1)/2) needs no new argument: Theorems F, V, H and Proposition C hold for all n, k;
  `admissible_odd_iff` checks the F.4 constants, `main_odd` is the specialisation.
* Lemma R: the hand proof minimises over the group `G_c` and uses `hg ∈ G_c`.  The Lean proof needs no
  group structure (minimum over the finite set of sets reachable from `D` by symmetries fixing `c`).  It
  needs `CaseSat.sym` (the constraints of `c` for `D` imply those of `g(c)` for `g(D)`), which follows from
  `CaseSat.hasCase`, `HasCase.sym` and Lemma E (`caseSat_of_frame`).

## Build time

Clean `lake build` of this project (`.lake/build` deleted, Mathlib prebuilt, `LEAN_NUM_THREADS=3`,
`nice -n 10`, machine under load ~16 from other jobs), 2026-11-21: **9 min 19 s wall, 12 min 25 s CPU
(user 717 s), peak memory 7.1 GB** (resident set including the mapped Mathlib; the kernel computations
themselves need < 1 GB per piece).  Per file:

| file | time |
|------|------|
| `QueenDom/Cases35Pieces.lean` (190 kernel computations, 3 threads) | 408 s |
| `QueenDom/Cases35Data.lean` (elaboration of 128,941 numerals) | 86 s |
| `QueenDom/Cases32Pieces.lean` (153 kernel computations) | 71 s |
| `QueenDom/Cases35.lean` (frames, chain, 19-queen domination) | 49 s |
| `QueenDom/Cases32.lean` | 26 s |
| every other file | 4 - 8 s |

The single-computation alternative for n = 35 (`decide +kernel` on the whole list) was stopped at 65 GB
of memory; see "The case lists inside Lean".  Axiom report: `Axioms.lean`, about 7 s.
