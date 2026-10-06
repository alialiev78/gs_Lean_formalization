module

public import GS.ComplexAlgebra
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Unitary completion of matrices with real diagonal column Gram matrices

Normalized nonzero columns extend to an orthonormal basis. Zero columns are
included, so the subsequent cosine-sine theorem includes both endpoints.
-/

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace GS.UnitaryCS

/-- The unitary equations on an arbitrary finite index type. -/
def IsUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

namespace IsUnitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
theorem of_conjTranspose_mul (h : Aᴴ * A = 1) : IsUnitary A :=
  ⟨h, mul_eq_one_comm.mp h⟩
theorem one : IsUnitary (1 : Matrix ι ι ℂ) := by constructor <;> simp
theorem conjTranspose (h : IsUnitary A) : IsUnitary Aᴴ := by
  constructor
  · simpa using h.2
  · simpa using h.1
theorem mul (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A*B) := by
  constructor
  · calc
      (A*B)ᴴ*(A*B) = Bᴴ*(Aᴴ*A)*B := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hA.1]; simpa using hB.1
  · calc
      (A*B)*(A*B)ᴴ = A*(B*Bᴴ)*Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB.2]; simpa using hA.2
end IsUnitary

/-- A square complex matrix with real diagonal Gram matrix has a unitary
left factor, including at zero diagonal entries. -/
theorem exists_unitary_mul_diagonal {n : ℕ} (A : CMat n) (d : Fin n → ℝ)
    (hA : Aᴴ * A = diagonal (fun i => (d i : ℂ) ^ 2)) :
    ∃ U : CMat n, Unitary U ∧ A = U * diagonal (fun i => (d i : ℂ)) := by
  classical
  let e₀ := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => ∑ k, A k j • e₀ k
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_ℂ = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have hgram (i j : Fin n) : ⟪f i, f j⟫_ℂ = if i = j then (d i : ℂ) ^ 2 else 0 := by
    calc
      ⟪f i, f j⟫_ℂ = ∑ k, conj (A k i) * A k j := by
        rw [← e₀.sum_inner_mul_inner (f i) (f j)]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← inner_conj_symm (f i) (e₀ k), hcoords, hcoords]
      _ = (Aᴴ * A) i j := rfl
      _ = _ := by rw [hA]; simp [Matrix.diagonal_apply]
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun j => ((d j : ℂ))⁻¹ • f j
  let s : Set (Fin n) := {i | d i ≠ 0}
  have hv : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪((d i : ℂ))⁻¹ • f i, ((d j : ℂ))⁻¹ • f j⟫_ℂ = _
    rw [inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have hd : d i ≠ 0 := i.property
      simp [hd, pow_two, ← mul_assoc]
    · have hij' : (i : Fin n) ≠ (j : Fin n) := fun h => hij (Subtype.ext h)
      simp [hij, hij']
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n))
  let U : CMat n := fun i j => ⟪e₀ i, e j⟫_ℂ
  have hU : Unitary U := by
    apply IsUnitary.of_conjTranspose_mul
    ext i j
    calc
      (Uᴴ * U) i j = ∑ k, ⟪e i, e₀ k⟫_ℂ * ⟪e₀ k, e j⟫_ℂ := by
        change (∑ k, star (inner ℂ (e₀ k) (e i)) * inner ℂ (e₀ k) (e j)) = _
        simp only [Complex.star_def, inner_conj_symm]
      _ = ⟪e i, e j⟫_ℂ := e₀.sum_inner_mul_inner _ _
      _ = (1 : CMat n) i j := by
        simpa only [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  refine ⟨U, hU, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  by_cases hd : d j = 0
  · have hf : f j = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      exact (hgram j j).trans (by simp [hd])
    rw [hd]
    simp only [Complex.ofReal_zero, mul_zero, ← hcoords, hf, inner_zero_right]
  · have hj : j ∈ s := hd
    change A i j = ⟪e₀ i, e j⟫_ℂ * (d j : ℂ)
    rw [he j hj]
    change A i j = ⟪e₀ i, ((d j : ℂ))⁻¹ • f j⟫_ℂ * (d j : ℂ)
    rw [inner_smul_right, hcoords]
    have hd' : (d j : ℂ) ≠ 0 := by exact_mod_cast hd
    field_simp

end GS.UnitaryCS
