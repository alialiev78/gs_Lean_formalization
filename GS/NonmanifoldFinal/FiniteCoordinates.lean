module

public import GS.Nonmanifold.OriginalCompactModel
public import GS.NonmanifoldObstruction.ProductSphere

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Finite coordinates for the actual GS local model

This file only changes coordinates by explicit homeomorphisms. In particular,
Matrix.rank and all induced topologies are retained. No nonmanifold hypothesis
is introduced. The coordinate maps are checked with the pinned Lean toolchain.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldObstruction
open scoped BigOperators
namespace GS.NonmanifoldFinal

variable {ι κ ν : Type*}

/-- Reindex real coordinates; this preserves the product topology. -/
def reindexReal (e : ι ≃ κ) : (ι → ℝ) ≃ₜ (κ → ℝ) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Pack two independent coordinate arrays, without changing either norm. -/
def sumCoordinates : ((ι → ℝ) × (κ → ℝ)) ≃ₜ ((ι ⊕ κ) → ℝ) where
  toFun p := Sum.elim p.1 p.2
  invFun x := (fun i => x (.inl i), fun j => x (.inr j))
  left_inv p := rfl
  right_inv x := by funext i; cases i <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i <;> dsimp <;> fun_prop
  continuous_invFun := by fun_prop

/-- Change column labels in an actual two-row rank cone. -/
def reindexRankCone [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] (e : κ ≃ ν) : RankCone κ ≃ₜ RankCone ν where
  toFun W := ⟨fun i j => W.val i (e.symm j), by
    apply rank_le_one_of_two_column_minors
    intro j k
    exact (rank_le_one_iff_minors W.val).mp W.property (e.symm j) (e.symm k)⟩
  invFun W := ⟨fun i j => W.val i (e j), by
    apply rank_le_one_of_two_column_minors
    intro j k
    exact (rank_le_one_iff_minors W.val).mp W.property (e j) (e k)⟩
  left_inv W := by apply Subtype.ext; ext i j; simp
  right_inv W := by apply Subtype.ext; ext i j; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply (e.symm j)).comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply (e j)).comp
      ((continuous_apply i).comp continuous_subtype_val)

@[simp] theorem reindexRankCone_zero [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] (e : κ ≃ ν) :
    reindexRankCone e coneZero = coneZero := by
  apply Subtype.ext
  rfl

/-- The exact combined type of unconstrained coordinates of the GS model. -/
abbrev FreeIndex (q : ℕ) := Fin q ⊕ (NonzeroIndex q ⊕ UpperIndex q)

def modelFreeCoordinates (q : ℕ) :
    ModelCoordinates q ≃ₜ ConeSpace (FreeIndex q) (UpperIndex q) where
  toFun p := (Sum.elim p.1 (Sum.elim p.2.1 p.2.2.1), p.2.2.2)
  invFun p := (fun i => p.1 (.inl i),
    fun j => p.1 (.inr (.inl j)), fun k => p.1 (.inr (.inr k)), p.2)
  left_inv p := rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      cases i with
      | inl i => rfl
      | inr j => cases j <;> rfl
    · rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      cases i with
      | inl i => dsimp; fun_prop
      | inr j => cases j <;> dsimp <;> fun_prop
    · fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem modelFreeCoordinates_zero (q : ℕ) :
    modelFreeCoordinates q (modelCoordinatesZero q) = productZero := by
  apply Prod.ext
  · funext i
    cases i with
    | inl i => rfl
    | inr j => cases j <;> rfl
  · apply Subtype.ext; rfl

/-- Convert both finite index sets to Fin; the equality is topological, not an
unproved assertion that the default sup norm equals the Frobenius norm. -/
def coneCoordinatesToFin [Fintype ι] [Fintype κ] [DecidableEq κ] :
    ConeSpace ι κ ≃ₜ ConeSpace (Fin (Fintype.card ι)) (Fin (Fintype.card κ)) :=
  (reindexReal (Fintype.equivFin ι)).prodCongr
    (reindexRankCone (Fintype.equivFin κ))

@[simp] theorem coneCoordinatesToFin_zero [Fintype ι] [Fintype κ] [DecidableEq κ] :
    (coneCoordinatesToFin : ConeSpace ι κ ≃ₜ _) productZero = productZero := by
  apply Prod.ext
  · rfl
  · exact reindexRankCone_zero _

def modelToFin (q : ℕ) : ModelCoordinates q ≃ₜ
    ConeSpace (Fin (Fintype.card (FreeIndex q))) (Fin (Fintype.card (UpperIndex q))) :=
  (modelFreeCoordinates q).trans coneCoordinatesToFin

@[simp] theorem modelToFin_zero (q : ℕ) :
    modelToFin q (modelCoordinatesZero q) = productZero := by
  simp [modelToFin]

/-- Relate the product of a cone subtype to the ambient subset in the ORIGINAL
ConeProductNonManifoldGoal, not to a replacement definition of the cone. -/
def flattenConeProduct [Fintype ι] [Fintype κ] [DecidableEq κ] :
    ConeSpace ι κ ≃ₜ
      {p : (ι → ℝ) × Matrix (Fin 2) κ ℝ // p.2.rank ≤ 1} where
  toFun p := ⟨(p.1,p.2.val),p.2.property⟩
  invFun p := (p.val.1,⟨p.val.2,p.property⟩)
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · fun_prop
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _

@[simp] theorem flattenConeProduct_zero [Fintype ι] [Fintype κ] [DecidableEq κ] :
    (flattenConeProduct : ConeSpace ι κ ≃ₜ _) productZero =
      ⟨(0,0),by simp⟩ := rfl

/-- The rank-cone width of the GS model satisfies the OLD goal's lower bound. -/
theorem model_width_ge_three (q : ℕ) (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := three_le_card_upperIndex q hq

/-- Reindex the width as d+2, as required by the explicitly constructed section.
The parameter d here counts EXTRA columns, not the article's total width. -/
def widthEquivExtra (κ : Type*) [Fintype κ] (hκ : 2 ≤ Fintype.card κ) :
    κ ≃ Fin ((Fintype.card κ - 2) + 2) :=
  (Fintype.equivFin κ).trans
    (Equiv.cast (congrArg Fin (Nat.sub_add_cancel hκ).symm))

def coneCoordinatesExtra [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hκ : 2 ≤ Fintype.card κ) :
    ConeSpace ι κ ≃ₜ ConeSpace ι (Fin ((Fintype.card κ - 2) + 2)) :=
  (Homeomorph.refl (ι → ℝ)).prodCongr (reindexRankCone (widthEquivExtra κ hκ))

@[simp] theorem coneCoordinatesExtra_zero [Fintype ι] [Fintype κ]
    [DecidableEq κ] (hκ : 2 ≤ Fintype.card κ) :
    (coneCoordinatesExtra hκ : ConeSpace ι κ ≃ₜ _) productZero = productZero := by
  apply Prod.ext
  · rfl
  · exact reindexRankCone_zero _

end GS.NonmanifoldFinal
