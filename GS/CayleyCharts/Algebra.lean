module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import GS.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Matrix Cayley algebra in the original GS matrix type

We use c(A) = (1 - A) * (1 + A)⁻¹. This convention is involutive on
{A | det (1 + A) ≠ 0}; its derivative at zero has sign -2.
All inverse identities have explicit determinant hypotheses. No smooth or
manifold structure is assumed here. Supports are the original `GS.Supported`.

-/

noncomputable section
open Matrix
namespace GS.CayleyCharts
variable {n : ℕ}

/-- The actual nonsingular matrix inverse is used, not a chosen inverse. -/
theorem inv_mul (A : Mat n) (hA : A.det ≠ 0) : A⁻¹ * A = 1 := by
  exact Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)

theorem mul_inv (A : Mat n) (hA : A.det ≠ 0) : A * A⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)

theorem cancel_right (A X Y : Mat n) (hA : A.det ≠ 0)
    (h : X * A = Y * A) : X = Y := by
  have h' := congrArg (fun Z : Mat n => Z * A⁻¹) h
  simpa only [Matrix.mul_assoc, mul_inv A hA, Matrix.mul_one] using h'

theorem cancel_left (A X Y : Mat n) (hA : A.det ≠ 0)
    (h : A * X = A * Y) : X = Y := by
  have h' := congrArg (fun Z : Mat n => A⁻¹ * Z) h
  simpa only [← Matrix.mul_assoc, inv_mul A hA, Matrix.one_mul] using h'

/-- Cancelling an invertible congruence does not assume symmetry of X or Y. -/
theorem cancel_congruence (A X Y : Mat n) (hA : A.det ≠ 0)
    (h : Aᵀ * X * A = Aᵀ * Y * A) : X = Y := by
  apply cancel_left Aᵀ X Y (by simpa using hA)
  exact cancel_right A (Aᵀ * X) (Aᵀ * Y) hA h

theorem supported_sub (block : Fin n → ℕ) (A B : Mat n)
    (hA : Supported block A) (hB : Supported block B) :
    Supported block (A - B) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

/-- Fixed points of the original block projection are exactly supported matrices. -/
theorem blockProjection_eq_self (block : Fin n → ℕ) (A : Mat n)
    (hA : Supported block A) : GS.blockProjection block A = A := by
  ext i j
  by_cases h : block i = block j
  · simp [GS.blockProjection, GS.mask, h]
  · simp [GS.blockProjection, GS.mask, h, hA i j h]

theorem supported_of_blockProjection_eq (block : Fin n → ℕ) (A : Mat n)
    (hA : GS.blockProjection block A = A) : Supported block A := by
  intro i j hij
  have h := congrArg (fun M : Mat n => M i j) hA
  simpa [GS.blockProjection, GS.mask, hij] using h.symm

/-- The inverse-support property follows from the already established block
projection multiplication identity. No extra topology or partition is used. -/
theorem supported_inverse (block : Fin n → ℕ) (A : Mat n)
    (hA : Supported block A) (hdet : A.det ≠ 0) : Supported block A⁻¹ := by
  apply supported_of_blockProjection_eq block A⁻¹
  apply cancel_left A _ _ hdet
  calc
    A * GS.blockProjection block A⁻¹ = GS.blockProjection block (A * A⁻¹) :=
      (GS.blockProjection_mul_left block A A⁻¹ hA).symm
    _ = GS.blockProjection block 1 := by rw [mul_inv A hdet]
    _ = 1 := blockProjection_eq_self block 1 (Supported.one (block := block))
    _ = A * A⁻¹ := (mul_inv A hdet).symm

def cayley (A : Mat n) : Mat n := (1 - A) * (1 + A)⁻¹

def admissible (A : Mat n) : Prop := (1 + A).det ≠ 0

theorem cayley_mul (A : Mat n) (hA : admissible A) :
    cayley A * (1 + A) = 1 - A := by
  simp only [cayley, Matrix.mul_assoc, inv_mul (1 + A) hA, Matrix.mul_one]

theorem one_add_cayley_mul (A : Mat n) (hA : admissible A) :
    (1 + cayley A) * (1 + A) = (2 : ℝ) • (1 : Mat n) := by
  rw [Matrix.add_mul, Matrix.one_mul, cayley_mul A hA]
  rw [two_smul ℝ]
  abel

/-- The other Cayley denominator has an explicit right inverse. -/
theorem admissible_cayley (A : Mat n) (hA : admissible A) :
    admissible (cayley A) := by
  have he : (1 + cayley A) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [Matrix.mul_smul, one_add_cayley_mul A hA, smul_smul]
    norm_num
  exact Matrix.det_ne_zero_of_right_inverse he

theorem cayley_involutive (A : Mat n) (hA : admissible A) :
    cayley (cayley A) = A := by
  apply cancel_right (1 + cayley A) _ _ (admissible_cayley A hA)
  rw [cayley_mul (cayley A) (admissible_cayley A hA)]
  apply cancel_right (1 + A) _ _ hA
  calc
    (1 - cayley A) * (1 + A) = (1 + A) - (1 - A) := by
      rw [Matrix.sub_mul, Matrix.one_mul, cayley_mul A hA]
    _ = A * ((2 : ℝ) • (1 : Mat n)) := by rw [two_smul ℝ]; noncomm_ring
    _ = A * ((1 + cayley A) * (1 + A)) := by rw [one_add_cayley_mul A hA]
    _ = A * (1 + cayley A) * (1 + A) := (Matrix.mul_assoc _ _ _).symm

theorem cayley_supported (block : Fin n → ℕ) (A : Mat n)
    (hs : Supported block A) (hA : admissible A) :
    Supported block (cayley A) := by
  exact (supported_sub block 1 A (Supported.one (block := block)) hs).mul
    (supported_inverse block (1 + A) ((Supported.one (block := block)).add hs) hA)

theorem cayley_orthogonal (A : Mat n) (hs : GS.IsSkew A)
    (hA : admissible A) : Orthogonal (cayley A) := by
  apply Orthogonal.of_transpose_mul
  apply cancel_congruence (1 + A) _ 1 hA
  have he := cayley_mul A hA
  have ht : (1 + A)ᵀ * (cayley A)ᵀ = (1 - A)ᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose he
  calc
    (1 + A)ᵀ * ((cayley A)ᵀ * cayley A) * (1 + A) =
        ((1 + A)ᵀ * (cayley A)ᵀ) * (cayley A * (1 + A)) := by noncomm_ring
    _ = (1 - A)ᵀ * (1 - A) := by rw [ht, he]
    _ = (1 + A)ᵀ * (1 : Mat n) * (1 + A) := by
      change Aᵀ = -A at hs
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, hs]
      noncomm_ring

theorem cayley_isSkew (Q : Mat n) (hQ : Orthogonal Q)
    (hd : admissible Q) : GS.IsSkew (cayley Q) := by
  have he := cayley_mul Q hd
  have ht : (1 + Q)ᵀ * (cayley Q)ᵀ = (1 - Q)ᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose he
  have hz : (cayley Q)ᵀ + cayley Q = 0 := by
    apply cancel_congruence (1 + Q) _ 0 hd
    calc
      (1 + Q)ᵀ * ((cayley Q)ᵀ + cayley Q) * (1 + Q) =
          ((1 + Q)ᵀ * (cayley Q)ᵀ) * (1 + Q) +
          (1 + Q)ᵀ * (cayley Q * (1 + Q)) := by noncomm_ring
      _ = (1 - Q)ᵀ * (1 + Q) + (1 + Q)ᵀ * (1 - Q) := by rw [ht, he]
      _ = (2 : ℝ) • (1 - Qᵀ * Q) := by
        simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, two_smul ℝ]
        noncomm_ring
      _ = (1 + Q)ᵀ * (0 : Mat n) * (1 + Q) := by rw [hQ.1]; simp
  exact eq_neg_of_add_eq_zero_left hz

@[simp] theorem admissible_zero : admissible (0 : Mat n) := by
  simp [admissible]

@[simp] theorem cayley_zero : cayley (0 : Mat n) = 1 := by
  simp [cayley]

@[simp] theorem admissible_one : admissible (1 : Mat n) := by
  simpa only [cayley_zero] using admissible_cayley (0 : Mat n) admissible_zero

@[simp] theorem cayley_one : cayley (1 : Mat n) = 0 := by
  simp [cayley]

/-- A domain-specific inverse formula; no global inverse operation on an orbit
is used. -/
theorem cayley_injective : Set.InjOn (cayley : Mat n → Mat n) {A | admissible A} := by
  intro A hA B hB h
  have h' := congrArg cayley h
  simpa only [cayley_involutive A hA, cayley_involutive B hB] using h'

/-- A real skew matrix has identically zero quadratic form. -/
theorem skew_dot_mulVec_zero (A : Mat n) (hA : GS.IsSkew A) (v : Fin n → ℝ) :
    dotProduct v (A *ᵥ v) = 0 := by
  have h : dotProduct v (A *ᵥ v) = -(dotProduct v (A *ᵥ v)) := by
    calc
      dotProduct v (A *ᵥ v) = dotProduct (Aᵀ *ᵥ v) v := by
        rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
      _ = -(dotProduct v (A *ᵥ v)) := by
        rw [hA, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith

/-- The Cayley denominator is invertible for every real skew matrix. -/
theorem admissible_of_isSkew (A : Mat n) (hA : GS.IsSkew A) : admissible A := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det (1 + A)).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : (1 + A) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hd := congrArg (dotProduct (x - y)) hz
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    skew_dot_mulVec_zero A hA, add_zero, dotProduct_zero] at hd
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hd)

end GS.CayleyCharts
