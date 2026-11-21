/-
Enumeration of the case list `L(n, k)` (PROOFS.md F.2; `geom.canonical_frames`, `geom.cases_by_frame`),
with a proof that the enumeration is exactly the set of cases with canonical frame and admissible
(frame, deficits).
-/
module

public import QueenDom.Cases

@[expose] public section

namespace QueenDom

/-- The conditions on a frame used by `geom.canonical_frames`: canonical, `w ≥ 1`, `h ≥ 1`. -/
def FrameOK (n p q r s : ℕ) : Prop := Canon p q r s ∧ p + q + 2 ≤ n ∧ r + s + 2 ≤ n

instance (n p q r s : ℕ) : Decidable (FrameOK n p q r s) := by unfold FrameOK; infer_instance

/-- The canonical frames `(ml, mr, mb, mt)` with `ml + mr ≤ k`, `mb + mt ≤ k`, in lexicographic
order (`sorted(geom.canonical_frames(n, k))`). -/
def enumFrames (n k : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun p => (List.range (k + 1 - p)).flatMap fun q =>
  (List.range (k + 1)).flatMap fun r =>
  ((List.range (k + 1 - r)).filter fun s => decide (FrameOK n p q r s)).map fun s => (p, q, r, s)

theorem mem_enumFrames {n k p q r s : ℕ} :
    (p, q, r, s) ∈ enumFrames n k ↔ p + q ≤ k ∧ r + s ≤ k ∧ FrameOK n p q r s := by
  simp only [enumFrames, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨p', hp, q', hq, r', hr, s', ⟨hs, hok⟩, rfl, rfl, rfl, rfl⟩
    exact ⟨by omega, by omega, hok⟩
  · rintro ⟨hpq, hrs, hok⟩
    exact ⟨p, by omega, q, by omega, r, by omega, s, ⟨by omega, hok⟩, rfl, rfl, rfl, rfl⟩

/-- The admissible deficit vectors of one frame `f = (ml, mr, mb, mt)`, in lexicographic order.  The
deficits are enumerated subject to `dR + dC + dT + dS ≤ 4k - 2n + 2`, which is condition (C1). -/
def casesOfFrame (n k : ℕ) (f : ℕ × ℕ × ℕ × ℕ) : List Case :=
  (List.range (4 * k + 3 - 2 * n)).flatMap fun dR =>
  (List.range (4 * k + 3 - 2 * n - dR)).flatMap fun dC =>
  (List.range (4 * k + 3 - 2 * n - dR - dC)).flatMap fun dT =>
  ((List.range (4 * k + 3 - 2 * n - dR - dC - dT)).filter fun dS =>
      decide (Admissible n k ⟨f.1, f.2.1, f.2.2.1, f.2.2.2, dR, dC, dT, dS⟩)).map
    fun dS => ⟨f.1, f.2.1, f.2.2.1, f.2.2.2, dR, dC, dT, dS⟩

/-- The case list `L(n, k)`: every canonical frame with every admissible deficit vector, in
lexicographic order (`geom.cases_by_frame(n, k)`). -/
def enumCases (n k : ℕ) : List Case := (enumFrames n k).flatMap (casesOfFrame n k)

/-- The enumeration is exactly the set of cases with canonical frame and admissible
(frame, deficits). -/
theorem mem_enumCases {n k : ℕ} {cs : Case} : cs ∈ enumCases n k ↔ CanonAdm n k cs := by
  simp only [enumCases, casesOfFrame, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p, q, r, s⟩, hf, dR, -, dC, -, dT, -, dS, ⟨-, hadm⟩, rfl⟩
    exact ⟨(mem_enumFrames.mp hf).2.2.1, hadm⟩
  · rintro ⟨hcan, hadm⟩
    have hadm' := hadm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := hadm'
    refine ⟨(cs.ml, cs.mr, cs.mb, cs.mt), mem_enumFrames.mpr ⟨by omega, by omega, hcan, h7, h8⟩,
      cs.dR, by omega, cs.dC, by omega, cs.dT, by omega, cs.dS, ⟨by omega, hadm⟩, rfl⟩

/-! ### Splitting the case list by the horizontal margins `(ml, mr)`

For large boards the kernel comparison of `enumCases n k` with an explicit list is split into one
computation per pair `(ml, mr)` (bounded memory, and the pieces are checked in parallel). -/

/-- The canonical frames with horizontal margins `(p, q)`. -/
def enumFramesPQ (n k p q : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun r =>
  ((List.range (k + 1 - r)).filter fun s => decide (FrameOK n p q r s)).map fun s => (p, q, r, s)

/-- The cases of `L(n, k)` with horizontal margins `(p, q)`. -/
def casesPQ (n k p q : ℕ) : List Case := (enumFramesPQ n k p q).flatMap (casesOfFrame n k)

/-- The pairs `(ml, mr)` with `ml + mr ≤ k`, in lexicographic order. -/
def marginPairs (k : ℕ) : List (ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun p => (List.range (k + 1 - p)).map fun q => (p, q)

/-- `L(n, k)` is the concatenation of the pieces `casesPQ n k p q`, `(p, q)` in `marginPairs k`. -/
theorem enumCases_eq_pieces (n k : ℕ) :
    enumCases n k = (marginPairs k).flatMap fun pq => casesPQ n k pq.1 pq.2 := by
  simp only [enumCases, enumFrames, marginPairs, casesPQ, enumFramesPQ, List.flatMap_assoc,
    List.flatMap_map]

end QueenDom
