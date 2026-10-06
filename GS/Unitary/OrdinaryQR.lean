module

public import GS.Unitary.Support
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Ordinary complex QR and the unitary triangular obstruction

The QR construction uses a completed orthonormal basis of the genuine complex
Euclidean space. It applies to singular matrices as well. No phase or positive
diagonal convention is imposed on the triangular factor.
-/

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators

namespace GS.UnitaryGeometry
variable {n : ℕ}

def CUpper (A : CMat n) : Prop := A.BlockTriangular (fun i => i.val)

theorem cSupported_blockTriangular {block : Fin n → ℕ} {A : CMat n}
    (h : CSupported block A) : A.BlockTriangular block := by
  intro i j hij
  exact h i j (Ne.symm (Nat.ne_of_lt hij))

theorem cUpper_blockTriangular_monotone (block : Fin n → ℕ)
    (hb : Monotone block) {A : CMat n} (h : CUpper A) : A.BlockTriangular block := by
  intro i j hij
  apply h
  by_contra hn
  have hle : i ≤ j := Nat.le_of_not_gt hn
  exact (not_lt_of_ge (hb hle)) hij

theorem cUpper_blockTriangular {b : ℕ} {A : CMat n} (h : CUpper A) :
    A.BlockTriangular (fun i : Fin n => i.val / b) :=
  cUpper_blockTriangular_monotone _ (fun _ _ hle => Nat.div_le_div_right hle) h

/-- A unitary matrix upper triangular in block labels is block diagonal. -/
theorem unitary_blockTriangular_supported {block : Fin n → ℕ} {U : CMat n}
    (hU : Unitary U) (htri : U.BlockTriangular block) : CSupported block U := by
  letI : Invertible U :=
    { invOf := Uᴴ, invOf_mul_self := hU.1, mul_invOf_self := hU.2 }
  have hi : U⁻¹.BlockTriangular block :=
    Matrix.blockTriangular_inv_of_blockTriangular htri
  rw [Matrix.inv_eq_left_inv hU.1] at hi
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hz := hi (i := j) (j := i) hlt
    simpa only [Matrix.conjTranspose_apply, star_eq_zero] using hz
  · exact htri hgt

/-- Inversion preserves arbitrary block support for invertible complex matrices. -/
theorem cSupported_inverse {block : Fin n → ℕ} {A : CMat n}
    (hA : CSupported block A) [Invertible A] : CSupported block A⁻¹ := by
  have ha : A.BlockTriangular block := cSupported_blockTriangular hA
  have hat : Aᴴ.BlockTriangular block := cSupported_blockTriangular hA.conjTranspose
  have hi := Matrix.blockTriangular_inv_of_blockTriangular ha
  have hit := Matrix.blockTriangular_inv_of_blockTriangular hat
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hz := hit (i := j) (j := i) hlt
    simpa only [← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply,
      star_eq_zero] using hz
  · exact hi hgt

theorem unitary_det_ne_zero {Q : CMat n} (hQ : Unitary Q) : Q.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det hQ.1
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hz] at h

/-- Ordinary complex square QR, including dependent input columns. -/
theorem exists_ordinary_qr (A : CMat n) :
    ∃ V R : CMat n, Unitary V ∧ CUpper R ∧ A=V*R := by
  let e₀ : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun j => ∑ k, A k j • e₀ k
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let e := gramSchmidtOrthonormalBasis hdim f
  let V : CMat n := fun i j => ⟪e₀ i, e j⟫_ℂ
  let R : CMat n := fun i j => ⟪e i, f j⟫_ℂ
  have ho : Unitary V := by
    have hv : Vᴴ*V = 1 := by
      ext i j
      calc
        (Vᴴ*V) i j = ∑ k, ⟪e i, e₀ k⟫_ℂ * ⟪e₀ k, e j⟫_ℂ := by
          change (∑ k, star (inner ℂ (e₀ k) (e i)) * inner ℂ (e₀ k) (e j)) = _
          apply Finset.sum_congr rfl
          intro k hk
          rw [← inner_conj_symm (e i) (e₀ k)]
          rfl
        _ = ⟪e i, e j⟫_ℂ := e₀.sum_inner_mul_inner _ _
        _ = (1 : CMat n) i j := by
          simpa only [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
    exact ⟨hv,mul_eq_one_comm.mp hv⟩
  have ht : CUpper R := by
    intro i j hij
    exact gramSchmidtOrthonormalBasis_inv_triangular hdim f hij
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_ℂ = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have he : A=V*R := by
    ext i j
    calc
      A i j = ⟪e₀ i, f j⟫_ℂ := (hcoords i j).symm
      _ = ∑ k, ⟪e₀ i, e k⟫_ℂ * ⟪e k, f j⟫_ℂ :=
        (e.sum_inner_mul_inner _ _).symm
      _ = (V*R) i j := rfl
  exact ⟨V,R,ho,ht,he⟩

end GS.UnitaryGeometry
