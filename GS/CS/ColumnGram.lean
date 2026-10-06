module

public import GS.Core
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Orthogonal completion of a matrix with diagonal column Gram matrix

Zero columns are included: only the normalized nonzero columns are prescribed
when extending to an orthonormal basis. This is the completion step needed in
the cosine-sine decomposition at singular values zero and one.
-/

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators
namespace GS.CS

/-- A square matrix with diagonal column Gram matrix admits an orthogonal
left factor. No diagonal entry is required to be nonzero. -/
theorem exists_orthogonal_mul_diagonal {n : ℕ} (A : Mat n) (d : Fin n → ℝ)
    (hA : Aᵀ * A = diagonal (fun i => d i ^ 2)) :
    ∃ U : Mat n, Orthogonal U ∧ A = U * diagonal d := by
  classical
  let e₀ := EuclideanSpace.basisFun (Fin n) ℝ
  let f : Fin n → EuclideanSpace ℝ (Fin n) := fun j => ∑ k, A k j • e₀ k
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_ℝ = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have hgram (i j : Fin n) : ⟪f i, f j⟫_ℝ = if i = j then d i ^ 2 else 0 := by
    calc
      ⟪f i, f j⟫_ℝ = ∑ k, A k i * A k j := by
        rw [← e₀.sum_inner_mul_inner (f i) (f j)]
        apply Finset.sum_congr rfl
        intro k hk
        rw [real_inner_comm (e₀ k) (f i), hcoords, hcoords]
      _ = (Aᵀ * A) i j := rfl
      _ = _ := by rw [hA]; simp [Matrix.diagonal_apply]
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun j => (d j)⁻¹ • f j
  let s : Set (Fin n) := {i | d i ≠ 0}
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪(d i)⁻¹ • f i, (d j)⁻¹ • f j⟫_ℝ = _
    rw [real_inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have hd : d i ≠ 0 := i.property
      simp [hd, pow_two, ← mul_assoc]
    · have hij' : (i : Fin n) ≠ (j : Fin n) := fun h => hij (Subtype.ext h)
      simp [hij, hij']
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n))
  let U : Mat n := fun i j => ⟪e₀ i, e j⟫_ℝ
  have hU : Orthogonal U := by
    apply Orthogonal.of_transpose_mul
    ext i j
    calc
      (Uᵀ * U) i j = ∑ k, ⟪e i, e₀ k⟫_ℝ * ⟪e₀ k, e j⟫_ℝ := by
        change (∑ k, ⟪e₀ k, e i⟫_ℝ * ⟪e₀ k, e j⟫_ℝ) = _
        apply Finset.sum_congr rfl
        intro k hk
        rw [real_inner_comm (e₀ k) (e i)]
      _ = ⟪e i, e j⟫_ℝ := e₀.sum_inner_mul_inner _ _
      _ = (1 : Mat n) i j := by
        simpa only [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  refine ⟨U, hU, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  by_cases hd : d j = 0
  · have hf : f j = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      exact (hgram j j).trans (by simp [hd])
    rw [hd, mul_zero, ← hcoords, hf, inner_zero_right]
  · have hj : j ∈ s := hd
    change A i j = ⟪e₀ i, e j⟫_ℝ * d j
    rw [he j hj]
    change A i j = ⟪e₀ i, (d j)⁻¹ • f j⟫_ℝ * d j
    rw [inner_smul_right, hcoords]
    field_simp

end GS.CS
