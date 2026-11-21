/-
Residual symmetry breaking inside one case (PROOFS.md F.6, Lemma R), semantic part.

For a case `cs` let `G_cs = {g | g.actCase cs = cs}` (the stabiliser, `hard_test.stabiliser`), and for a set
`D` let `occVec D = (oR[0..n-1], oC[0..n-1])` be its row/column occupancy vector (`false < true`).
`SymBreak cs D` is the lex-leader condition: `occVec D ≤ occVec (g.image D)` (lexicographic) for every
`g ∈ G_cs`.  Lemma R: if some set satisfies all constraints of `cs`, then some set satisfies all
constraints of `cs` and `SymBreak cs`.  Hence Proposition C stays valid with `CaseSat ∧ SymBreak` in place
of `CaseSat`, for any subset of the cases.

Not formalized here (Layer 2): that the clauses of `hard_test.sbp_clauses` express `SymBreak` (i.e. that the
fixed coordinate permutation `π_g` of the code satisfies `occVec (g.image D) = π_g (occVec D)`, and that the
chain clauses encode `≤lex`), and the cube splitting of `run_hard.py` (a purely propositional case split:
the 16 assignments of one layer of four variables are exhaustive).
-/
module

public import QueenDom.Main

@[expose] public section

namespace QueenDom

open Finset

variable {n k : ℕ} {cs : Case} {D : Finset (Sq n)}

/-- The row/column occupancy vector `(oR[0], ..., oR[n-1], oC[0], ..., oC[n-1])` of `D`. -/
def occVec (D : Finset (Sq n)) : List Bool :=
  (List.finRange n).map (fun y => decide (y ∈ occR D)) ++
    (List.finRange n).map (fun x => decide (x ∈ occC D))

/-- The lex-leader condition `SBP(cs)` of F.6, semantically: `occVec D` is lexicographically at most
`occVec (g(D))` for every symmetry `g` that fixes the case `cs`. -/
def SymBreak (cs : Case) (D : Finset (Sq n)) : Prop :=
  ∀ g : Sym, g.actCase cs = cs → occVec D ≤ occVec (g.image D)

/-- A set satisfying the constraints of `cs` has case `cs`. -/
theorem CaseSat.hasCase (h : CaseSat n k cs D) : HasCase D cs := by
  obtain ⟨a, b, c, d, hF, ha, hb, hc, hd, -⟩ := h.frame
  refine ⟨a, b, c, d, hF, ?_⟩
  have h1 := h.card
  have h2 := h.cardR
  have h3 := h.cardC
  have h4 := h.cardT
  have h5 := h.cardS
  rcases cs with ⟨ml, mr, mb, mt, dR, dC, dT, dS⟩
  simp only [caseOf, defR, defC, defT, defS, Case.mk.injEq] at *
  omega

/-- **The constraints of the cases are compatible with the symmetries**: if `D` satisfies all constraints
of `cs`, then `g(D)` satisfies all constraints of `g(cs)`. -/
theorem CaseSat.sym (h : CaseSat n k cs D) (g : Sym) : CaseSat n k (g.actCase cs) (g.image D) := by
  obtain ⟨a, b, c, d, hF, hcase⟩ := h.hasCase.sym g
  have := caseSat_of_frame (h.dom.sym g) ((g.card_image D).trans h.card) hF
  rwa [hcase] at this

/-- **Lemma R** (F.6, semantic part).  If some set satisfies all constraints of the case `cs`, then some
set satisfies all constraints of `cs` and the lex-leader condition for the stabiliser of `cs`.

The proof avoids the group structure of the symmetries: the sets reachable from `D` by repeated
application of symmetries fixing `cs` form a finite set, all of whose members satisfy the constraints of
`cs`; a member with lexicographically least occupancy vector satisfies the lex-leader condition, because
its images under the stabiliser are again reachable. -/
theorem lemmaR (h : CaseSat n k cs D) : ∃ D' : Finset (Sq n), CaseSat n k cs D' ∧ SymBreak cs D' := by
  let step : Finset (Sq n) → Finset (Sq n) → Prop := fun E F => ∃ g : Sym, g.actCase cs = cs ∧ F = g.image E
  let S : Set (Finset (Sq n)) := {E | Relation.ReflTransGen step D E}
  have hS : ∀ E ∈ S, CaseSat n k cs E := by
    intro E hE
    induction hE with
    | refl => exact h
    | tail _ hst ih =>
      obtain ⟨g, hg, rfl⟩ := hst
      have := ih.sym g
      rwa [hg] at this
  obtain ⟨E, hE, hmin⟩ := S.toFinite.toFinset.exists_min_image occVec
    ⟨D, S.toFinite.mem_toFinset.mpr Relation.ReflTransGen.refl⟩
  rw [Set.Finite.mem_toFinset] at hE
  refine ⟨E, hS E hE, fun g hg => hmin _ ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact Relation.ReflTransGen.tail hE ⟨g, hg, rfl⟩

/-- **Proposition C with symmetry breaking.**  Let `k ≤ n - 2`.  If for every case of the case list no set
satisfies the constraints of the case together with its lex-leader condition, then `γ(Q_n) > k`. -/
theorem lt_gamma_of_cases_unsat_symBreak (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ enumCases n k, ¬ ∃ D : Finset (Sq n), CaseSat n k cs D ∧ SymBreak cs D) :
    k < gamma n :=
  lt_gamma_of_cases_unsat hk fun cs hcs ⟨_, hD⟩ => H cs hcs (lemmaR hD)

/-- The mixed form used by the `n = 35` run: for each case of the list, either the plain constraints or
the constraints with symmetry breaking are unsatisfiable. -/
theorem lt_gamma_of_cases_unsat_mixed (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ enumCases n k, (¬ ∃ D : Finset (Sq n), CaseSat n k cs D) ∨
      ¬ ∃ D : Finset (Sq n), CaseSat n k cs D ∧ SymBreak cs D) :
    k < gamma n :=
  lt_gamma_of_cases_unsat_symBreak hk fun cs hcs hex => by
    rcases H cs hcs with h | h
    · exact h ⟨hex.choose, hex.choose_spec.1⟩
    · exact h hex

end QueenDom
