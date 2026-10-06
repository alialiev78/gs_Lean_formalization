module

public import GS.GlobalGeometry.OriginalGImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Polynomial equations and radial algebra for the actual rank-one cone

This module uses Matrix.rank, the inherited Frobenius sum, and the induced
matrix topology. In particular it does not replace the determinantal cone by
a formal type with assumed topological properties.

The two-column-minor lemma and normalized outer-factor existence are reused
from OriginalGImage.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
open scoped BigOperators
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The converse to the two-column-minor lemma, including the zero first row. -/
theorem rank_le_one_of_two_column_minors (W : Matrix (Fin 2) κ ℝ)
    (h : ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j) : W.rank ≤ 1 := by
  by_cases hz : ∀ j, W 0 j = 0
  · have he : W = outer ![0,1] (W 1) := by
      ext i j
      fin_cases i <;> simp [outer, hz]
    rw [he]
    exact rank_outer_le_one _ _
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    let a : ℝ := W 1 j / W 0 j
    have hrow (k : κ) : W 1 k = a * W 0 k := by
      have hm := h j k
      dsimp [a]
      field_simp [hj]
      nlinarith [hm]
    have he : W = outer ![1,a] (W 0) := by
      ext i k
      fin_cases i <;> simp [outer, hrow]
    rw [he]
    exact rank_outer_le_one _ _

theorem rank_le_one_iff_minors (W : Matrix (Fin 2) κ ℝ) :
    W.rank ≤ 1 ↔ ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j :=
  ⟨fun h => rank_le_one_two_column_minor W h, rank_le_one_of_two_column_minors W⟩

/-- Closedness is proved from explicit polynomial equations, not assumed. -/
theorem isClosed_rankOne :
    IsClosed {W : Matrix (Fin 2) κ ℝ | W.rank ≤ 1} := by
  simp only [rank_le_one_iff_minors, Set.setOf_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro k
  exact isClosed_eq (by fun_prop) (by fun_prop)

theorem rank_smul_le_one (t : ℝ) {W : Matrix (Fin 2) κ ℝ}
    (hW : W.rank ≤ 1) : (t • W).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  have h := rank_le_one_two_column_minor W hW j k
  simp only [Matrix.smul_apply, smul_eq_mul]
  nlinarith [congrArg (fun x : ℝ => t^2*x) h]

/-- This is the Frobenius sum; it is not mathlib's default matrix norm. -/
theorem frobSq_smul {ι : Type*} [Fintype ι] (t : ℝ)
    (W : Matrix ι κ ℝ) : frobSq (t • W) = t^2 * frobSq W := by
  simp only [frobSq, frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem frobSq_pos_of_ne_zero {ι : Type*} [Fintype ι]
    {W : Matrix ι κ ℝ} (hW : W ≠ 0) : 0 < frobSq W := by
  have hne : frobSq W ≠ 0 := fun h => hW ((frobSq_eq_zero_iff W).mp h)
  exact lt_of_le_of_ne (frobSq_nonneg W) (Ne.symm hne)

/-- The link is an actual subtype of matrices of Frobenius radius one. -/
abbrev RankOneLink (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1 ∧ frobSq W = 1}

abbrev PuncturedRankOne (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1 ∧ W ≠ 0}

abbrev PositiveRadius := {r : ℝ // 0 < r}

theorem link_ne_zero (W : RankOneLink κ) : (W : Matrix (Fin 2) κ ℝ) ≠ 0 := by
  intro h
  have hz : frobSq (W : Matrix (Fin 2) κ ℝ) = 0 :=
    (frobSq_eq_zero_iff _).mpr h
  linarith [W.property.2]

theorem isClosed_rankOneLink :
    IsClosed {W : Matrix (Fin 2) κ ℝ | W.rank ≤ 1 ∧ frobSq W = 1} := by
  exact isClosed_rankOne.inter (isClosed_eq continuous_frobSq continuous_const)

/-- Compactness of the concrete matrix link via a coordinate box. -/
theorem isCompact_rankOneLink :
    IsCompact {W : Matrix (Fin 2) κ ℝ | W.rank ≤ 1 ∧ frobSq W = 1} := by
  letI : PartialOrder (Matrix (Fin 2) κ ℝ) :=
    inferInstanceAs (PartialOrder (Fin 2 → κ → ℝ))
  letI : CompactIccSpace (Matrix (Fin 2) κ ℝ) :=
    inferInstanceAs (CompactIccSpace (Fin 2 → κ → ℝ))
  let lo : Matrix (Fin 2) κ ℝ := fun _ _ => -1
  let hi : Matrix (Fin 2) κ ℝ := fun _ _ => 1
  have hsub : {W : Matrix (Fin 2) κ ℝ | W.rank ≤ 1 ∧ frobSq W = 1}
      ⊆ Set.Icc lo hi := by
    intro W hW
    have hb (i : Fin 2) (j : κ) : |W i j| ≤ 1 := by
      have hn : frobSq W ≤ (1 : ℝ)^2 := by rw [hW.2]; norm_num
      simpa using abs_entry_le_of_frobSq_le hn i j
    exact ⟨fun i j => (abs_le.mp (hb i j)).1,
      fun i j => (abs_le.mp (hb i j)).2⟩
  exact isCompact_Icc.of_isClosed_subset isClosed_rankOneLink hsub

end GS.Nonmanifold
