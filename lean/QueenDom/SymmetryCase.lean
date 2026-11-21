/-
Action of the eight symmetries on cases, including the deficits (PROOFS.md F.2, the table
`geom.case_images`): reflections exchange `dT` and `dS`, the transposition exchanges `dR` and `dC`.

This file is not needed for the case-split theorem (the case list contains every admissible deficit
vector for every canonical frame); it verifies the table and remark (ii) at the end of F.1.
-/
module

public import QueenDom.Cases

@[expose] public section

namespace QueenDom

open Finset

variable {n : ℕ}

/-- Two maps with the same fibres on `s` have images of the same size. -/
theorem card_image_congr {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α) (f : α → β)
    (g : α → γ) (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  have h1 : ((s.image fun x => (f x, g x)).image Prod.fst) = s.image f := by rw [image_image]; rfl
  have h2 : ((s.image fun x => (f x, g x)).image Prod.snd) = s.image g := by rw [image_image]; rfl
  have e1 : ((s.image fun x => (f x, g x)).image Prod.fst).card
      = (s.image fun x => (f x, g x)).card := by
    apply card_image_of_injOn
    intro u hu v hv huv
    rw [mem_coe, mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact Prod.ext huv ((h x hx y hy).mp huv)
  have e2 : ((s.image fun x => (f x, g x)).image Prod.snd).card
      = (s.image fun x => (f x, g x)).card := by
    apply card_image_of_injOn
    intro u hu v hv huv
    rw [mem_coe, mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact Prod.ext ((h x hx y hy).mpr huv) huv
  rw [← h1, ← h2, e1, e2]

section map

variable (D : Finset (Sq n)) (σ : Sq n ≃ Sq n)

theorem occR_map : occR (D.map σ.toEmbedding) = D.image fun p => (σ p).2 := by
  unfold occR; rw [map_eq_image, image_image]; rfl
theorem occC_map : occC (D.map σ.toEmbedding) = D.image fun p => (σ p).1 := by
  unfold occC; rw [map_eq_image, image_image]; rfl
theorem occT_map : occT (D.map σ.toEmbedding) = D.image fun p => dg (σ p) := by
  unfold occT; rw [map_eq_image, image_image]; rfl
theorem occS_map : occS (D.map σ.toEmbedding) = D.image fun p => sm (σ p) := by
  unfold occS; rw [map_eq_image, image_image]; rfl

end map

section deficits

variable (D : Finset (Sq n))

/-! `x ↦ n-1-x`: `dR, dC` are kept, `dT ↔ dS`. -/

theorem defR_map_reflX : defR (D.map reflX.toEmbedding) = defR D := by
  unfold defR; rw [card_map, occR_map]; rfl

theorem defC_map_reflX : defC (D.map reflX.toEmbedding) = defC D := by
  unfold defC; rw [card_map, occC_map]
  congr 1
  exact card_image_congr D _ _ fun p _ q _ => by simp

theorem defT_map_reflX : defT (D.map reflX.toEmbedding) = defS D := by
  unfold defT defS; rw [card_map, occT_map]
  congr 1
  refine card_image_congr D _ _ fun p _ q _ => ?_
  have := p.1.isLt
  have := q.1.isLt
  simp only [dg, sm, reflX_apply, Fin.val_rev]
  omega

theorem defS_map_reflX : defS (D.map reflX.toEmbedding) = defT D := by
  unfold defT defS; rw [card_map, occS_map]
  congr 1
  refine card_image_congr D _ _ fun p _ q _ => ?_
  have := p.1.isLt
  have := q.1.isLt
  simp only [dg, sm, reflX_apply, Fin.val_rev]
  omega

/-! `y ↦ n-1-y`: `dR, dC` are kept, `dT ↔ dS`. -/

theorem defR_map_reflY : defR (D.map reflY.toEmbedding) = defR D := by
  unfold defR; rw [card_map, occR_map]
  congr 1
  exact card_image_congr D _ _ fun p _ q _ => by simp

theorem defC_map_reflY : defC (D.map reflY.toEmbedding) = defC D := by
  unfold defC; rw [card_map, occC_map]; rfl

theorem defT_map_reflY : defT (D.map reflY.toEmbedding) = defS D := by
  unfold defT defS; rw [card_map, occT_map]
  congr 1
  refine card_image_congr D _ _ fun p _ q _ => ?_
  have := p.2.isLt
  have := q.2.isLt
  simp only [dg, sm, reflY_apply, Fin.val_rev]
  omega

theorem defS_map_reflY : defS (D.map reflY.toEmbedding) = defT D := by
  unfold defT defS; rw [card_map, occS_map]
  congr 1
  refine card_image_congr D _ _ fun p _ q _ => ?_
  have := p.2.isLt
  have := q.2.isLt
  simp only [dg, sm, reflY_apply, Fin.val_rev]
  omega

/-! Transposition: `dR ↔ dC`, `dT, dS` are kept. -/

theorem defR_map_transp : defR (D.map transp.toEmbedding) = defC D := by
  unfold defR defC; rw [card_map, occR_map]; rfl

theorem defC_map_transp : defC (D.map transp.toEmbedding) = defR D := by
  unfold defR defC; rw [card_map, occC_map]; rfl

theorem defT_map_transp : defT (D.map transp.toEmbedding) = defT D := by
  unfold defT; rw [card_map, occT_map]
  congr 1
  refine card_image_congr D _ _ fun p _ q _ => ?_
  simp only [dg, transp_apply]
  omega

theorem defS_map_transp : defS (D.map transp.toEmbedding) = defS D := by
  unfold defS; rw [card_map, occS_map]
  congr 1
  refine card_image_congr D _ _ fun p _ q _ => ?_
  simp only [sm, transp_apply]
  omega

end deficits

/-! ### Action on cases -/

/-- Image of a case under `x ↦ n-1-x`: `(mr, ml, mb, mt, dR, dC, dS, dT)`. -/
def Case.swapX (cs : Case) : Case := ⟨cs.mr, cs.ml, cs.mb, cs.mt, cs.dR, cs.dC, cs.dS, cs.dT⟩
/-- Image of a case under `y ↦ n-1-y`: `(ml, mr, mt, mb, dR, dC, dS, dT)`. -/
def Case.swapY (cs : Case) : Case := ⟨cs.ml, cs.mr, cs.mt, cs.mb, cs.dR, cs.dC, cs.dS, cs.dT⟩
/-- Image of a case under the transposition: `(mb, mt, ml, mr, dC, dR, dT, dS)`. -/
def Case.swapT (cs : Case) : Case := ⟨cs.mb, cs.mt, cs.ml, cs.mr, cs.dC, cs.dR, cs.dT, cs.dS⟩

/-- Action of a symmetry on cases. -/
def Sym.actCase (g : Sym) (cs : Case) : Case :=
  let c1 := bif g.fx then cs.swapX else cs
  let c2 := bif g.fy then c1.swapY else c1
  bif g.tr then c2.swapT else c2

/-- The table `geom.case_images(case)`, in the order of `geom.sym_maps`. -/
def caseImages (cs : Case) : List Case :=
  [⟨cs.ml, cs.mr, cs.mb, cs.mt, cs.dR, cs.dC, cs.dT, cs.dS⟩,
   ⟨cs.mr, cs.ml, cs.mb, cs.mt, cs.dR, cs.dC, cs.dS, cs.dT⟩,
   ⟨cs.ml, cs.mr, cs.mt, cs.mb, cs.dR, cs.dC, cs.dS, cs.dT⟩,
   ⟨cs.mr, cs.ml, cs.mt, cs.mb, cs.dR, cs.dC, cs.dT, cs.dS⟩,
   ⟨cs.mb, cs.mt, cs.ml, cs.mr, cs.dC, cs.dR, cs.dT, cs.dS⟩,
   ⟨cs.mt, cs.mb, cs.ml, cs.mr, cs.dC, cs.dR, cs.dS, cs.dT⟩,
   ⟨cs.mb, cs.mt, cs.mr, cs.ml, cs.dC, cs.dR, cs.dS, cs.dT⟩,
   ⟨cs.mt, cs.mb, cs.mr, cs.ml, cs.dC, cs.dR, cs.dT, cs.dS⟩]

/-- The Python table lists exactly the images `g.actCase cs`, `g` one of the eight symmetries. -/
theorem caseImages_eq (cs : Case) :
    caseImages cs =
      [Sym.actCase ⟨false, false, false⟩ cs, Sym.actCase ⟨true, false, false⟩ cs,
       Sym.actCase ⟨false, true, false⟩ cs, Sym.actCase ⟨true, true, false⟩ cs,
       Sym.actCase ⟨false, false, true⟩ cs, Sym.actCase ⟨false, true, true⟩ cs,
       Sym.actCase ⟨true, false, true⟩ cs, Sym.actCase ⟨true, true, true⟩ cs] := rfl

/-- `D` has a frame and its case is `cs` (`geom.case_of(n, D) = cs`). -/
def HasCase (D : Finset (Sq n)) (cs : Case) : Prop :=
  ∃ a b c d : Fin n, IsFrame D a b c d ∧ caseOf D a b c d = cs

variable {D : Finset (Sq n)} {cs : Case}

theorem HasCase.map_reflX (h : HasCase D cs) : HasCase (D.map reflX.toEmbedding) cs.swapX := by
  obtain ⟨a, b, c, d, hF, rfl⟩ := h
  refine ⟨Fin.rev b, Fin.rev a, c, d, hF.map_reflX, ?_⟩
  have := a.isLt
  have := b.isLt
  simp only [caseOf, Case.swapX, Fin.val_rev, Case.mk.injEq, defR_map_reflX, defC_map_reflX,
    defT_map_reflX, defS_map_reflX, and_true]
  omega

theorem HasCase.map_reflY (h : HasCase D cs) : HasCase (D.map reflY.toEmbedding) cs.swapY := by
  obtain ⟨a, b, c, d, hF, rfl⟩ := h
  refine ⟨a, b, Fin.rev d, Fin.rev c, hF.map_reflY, ?_⟩
  have := c.isLt
  have := d.isLt
  simp only [caseOf, Case.swapY, Fin.val_rev, Case.mk.injEq, defR_map_reflY, defC_map_reflY,
    defT_map_reflY, defS_map_reflY, and_true, true_and]
  omega

theorem HasCase.map_transp (h : HasCase D cs) : HasCase (D.map transp.toEmbedding) cs.swapT := by
  obtain ⟨a, b, c, d, hF, rfl⟩ := h
  refine ⟨c, d, a, b, hF.map_transp, ?_⟩
  simp only [caseOf, Case.swapT, defR_map_transp, defC_map_transp, defT_map_transp,
    defS_map_transp]

/-- **The symmetries act on cases by the table `geom.case_images`**: if `D` has case `cs`, its image
under `g` has case `g.actCase cs`. -/
theorem HasCase.sym (h : HasCase D cs) (g : Sym) : HasCase (g.image D) (g.actCase cs) := by
  rcases g with ⟨fx, fy, tr⟩
  have h1 : HasCase (bif fx then D.map QueenDom.reflX.toEmbedding else D)
      (bif fx then cs.swapX else cs) := by
    cases fx
    · exact h
    · exact h.map_reflX
  have h2 : HasCase
      (bif fy then (bif fx then D.map QueenDom.reflX.toEmbedding else D).map
          QueenDom.reflY.toEmbedding
        else (bif fx then D.map QueenDom.reflX.toEmbedding else D))
      (bif fy then (bif fx then cs.swapX else cs).swapY else (bif fx then cs.swapX else cs)) := by
    cases fy
    · exact h1
    · exact h1.map_reflY
  cases tr
  · exact h2
  · exact h2.map_transp

/-! ### Admissibility is invariant; every admissible case has an image in the case list -/

/-- The frame part of `g.actCase cs` is `g.actFrame` of the frame part of `cs`. -/
theorem Sym.actCase_frame (g : Sym) (cs : Case) :
    ((g.actCase cs).ml, (g.actCase cs).mr, (g.actCase cs).mb, (g.actCase cs).mt)
      = g.actFrame (cs.ml, cs.mr, cs.mb, cs.mt) := by
  rcases g with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

theorem Admissible.swapX {n k : ℕ} {cs : Case} (h : Admissible n k cs) : Admissible n k cs.swapX := by
  unfold Admissible Case.swapX at *
  simp only at *
  split_ifs at * <;> omega

theorem Admissible.swapY {n k : ℕ} {cs : Case} (h : Admissible n k cs) : Admissible n k cs.swapY := by
  unfold Admissible Case.swapY at *
  simp only at *
  split_ifs at * <;> omega

theorem Admissible.swapT {n k : ℕ} {cs : Case} (h : Admissible n k cs) : Admissible n k cs.swapT := by
  unfold Admissible Case.swapT at *
  simp only at *
  split_ifs at * <;> omega

/-- Admissibility is invariant under the eight symmetries. -/
theorem Admissible.actCase {n k : ℕ} {cs : Case} (h : Admissible n k cs) (g : Sym) :
    Admissible n k (g.actCase cs) := by
  rcases g with ⟨fx, fy, tr⟩
  have h1 : Admissible n k (bif fx then cs.swapX else cs) := by
    cases fx
    · exact h
    · exact h.swapX
  have h2 : Admissible n k
      (bif fy then (bif fx then cs.swapX else cs).swapY else (bif fx then cs.swapX else cs)) := by
    cases fy
    · exact h1
    · exact h1.swapY
  cases tr
  · exact h2
  · exact h2.swapT

/-- **The case list covers every admissible case up to symmetry.** -/
theorem exists_canonAdm_actCase {n k : ℕ} {cs : Case} (h : Admissible n k cs) :
    ∃ g : Sym, CanonAdm n k (g.actCase cs) := by
  obtain ⟨g, hg⟩ := exists_canon (cs.ml, cs.mr, cs.mb, cs.mt)
  refine ⟨g, ?_, h.actCase g⟩
  rw [← g.actCase_frame cs] at hg
  exact hg

end QueenDom
