module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import GS.Unitary.Projection
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Matrix Cayley algebra in the original GS matrix type

We use c(A) = (1 - A) * (1 + A)⁻¹. This convention is involutive on
{A | det (1 + A) ≠ 0}; its derivative at zero has sign -2.
All inverse identities have explicit determinant hypotheses. No smooth or
manifold structure is assumed here. Supports are the original `GS.UnitaryGeometry.CSupported`.

All algebraic claims below are proved without extra axioms.
-/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace GS.UnitaryManifold
open GS.UnitaryGeometry
variable {n : ℕ}

/-- The actual nonsingular matrix inverse is used, not a chosen inverse. -/
theorem inv_mul (A : CMat n) (hA : A.det ≠ 0) : A⁻¹ * A = 1 := by
  exact Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)

theorem mul_inv (A : CMat n) (hA : A.det ≠ 0) : A * A⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)

theorem cancel_right (A X Y : CMat n) (hA : A.det ≠ 0)
    (h : X * A = Y * A) : X = Y := by
  have h' := congrArg (fun Z : CMat n => Z * A⁻¹) h
  simpa only [Matrix.mul_assoc, mul_inv A hA, Matrix.mul_one] using h'

theorem cancel_left (A X Y : CMat n) (hA : A.det ≠ 0)
    (h : A * X = A * Y) : X = Y := by
  have h' := congrArg (fun Z : CMat n => A⁻¹ * Z) h
  simpa only [← Matrix.mul_assoc, inv_mul A hA, Matrix.one_mul] using h'

/-- Cancelling an invertible congruence does not assume symmetry of X or Y. -/
theorem cancel_congruence (A X Y : CMat n) (hA : A.det ≠ 0)
    (h : Aᴴ * X * A = Aᴴ * Y * A) : X = Y := by
  apply cancel_left Aᴴ X Y (by simpa only [Matrix.det_conjTranspose, star_ne_zero] using hA)
  exact cancel_right A (Aᴴ * X) (Aᴴ * Y) hA h

theorem supported_sub (block : Fin n → ℕ) (A B : CMat n)
    (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A - B) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

/-- Fixed points of the original block projection are exactly supported matrices. -/
theorem blockProjection_eq_self (block : Fin n → ℕ) (A : CMat n)
    (hA : CSupported block A) : cBlockProjection block A = A := by
  ext i j
  by_cases h : block i = block j
  · simp [cBlockProjection, cMask, h]
  · simp [cBlockProjection, cMask, h, hA i j h]

theorem supported_of_blockProjection_eq (block : Fin n → ℕ) (A : CMat n)
    (hA : cBlockProjection block A = A) : CSupported block A := by
  intro i j hij
  have h := congrArg (fun M : CMat n => M i j) hA
  simpa [cBlockProjection, cMask, hij] using h.symm

/-- The inverse-support property follows from the already established block
projection multiplication identity. No extra topology or partition is used. -/
theorem supported_inverse (block : Fin n → ℕ) (A : CMat n)
    (hA : CSupported block A) (hdet : A.det ≠ 0) : CSupported block A⁻¹ := by
  apply supported_of_blockProjection_eq block A⁻¹
  apply cancel_left A _ _ hdet
  calc
    A * cBlockProjection block A⁻¹ = cBlockProjection block (A * A⁻¹) :=
      (cBlockProjection_mul_left block A A⁻¹ hA).symm
    _ = cBlockProjection block 1 := by rw [mul_inv A hdet]
    _ = 1 := blockProjection_eq_self block 1 (CSupported.one (block := block))
    _ = A * A⁻¹ := (mul_inv A hdet).symm

def cayley (A : CMat n) : CMat n := (1 - A) * (1 + A)⁻¹

def admissible (A : CMat n) : Prop := (1 + A).det ≠ 0

theorem cayley_mul (A : CMat n) (hA : admissible A) :
    cayley A * (1 + A) = 1 - A := by
  simp only [cayley, Matrix.mul_assoc, inv_mul (1 + A) hA, Matrix.mul_one]

theorem one_add_cayley_mul (A : CMat n) (hA : admissible A) :
    (1 + cayley A) * (1 + A) = (2 : ℝ) • (1 : CMat n) := by
  rw [Matrix.add_mul, Matrix.one_mul, cayley_mul A hA]
  rw [two_smul ℝ]
  abel

/-- The other Cayley denominator has an explicit right inverse. -/
theorem admissible_cayley (A : CMat n) (hA : admissible A) :
    admissible (cayley A) := by
  have he : (1 + cayley A) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [Matrix.mul_smul, one_add_cayley_mul A hA, smul_smul]
    norm_num
  exact Matrix.det_ne_zero_of_right_inverse he

theorem cayley_involutive (A : CMat n) (hA : admissible A) :
    cayley (cayley A) = A := by
  apply cancel_right (1 + cayley A) _ _ (admissible_cayley A hA)
  rw [cayley_mul (cayley A) (admissible_cayley A hA)]
  apply cancel_right (1 + A) _ _ hA
  calc
    (1 - cayley A) * (1 + A) = (1 + A) - (1 - A) := by
      rw [Matrix.sub_mul, Matrix.one_mul, cayley_mul A hA]
    _ = A * ((2 : ℝ) • (1 : CMat n)) := by rw [two_smul ℝ]; noncomm_ring
    _ = A * ((1 + cayley A) * (1 + A)) := by rw [one_add_cayley_mul A hA]
    _ = A * (1 + cayley A) * (1 + A) := (Matrix.mul_assoc _ _ _).symm

theorem cayley_supported (block : Fin n → ℕ) (A : CMat n)
    (hs : CSupported block A) (hA : admissible A) :
    CSupported block (cayley A) := by
  exact (supported_sub block 1 A (CSupported.one (block := block)) hs).mul
    (supported_inverse block (1 + A) ((CSupported.one (block := block)).add hs) hA)

theorem cayley_unitary (A : CMat n) (hs : GS.IsSkewHermitian A)
    (hA : admissible A) : Unitary (cayley A) := by
  suffices hh : (cayley A)ᴴ * cayley A = 1 from ⟨hh, mul_eq_one_comm.mp hh⟩
  apply cancel_congruence (1 + A) _ 1 hA
  have he := cayley_mul A hA
  have ht : (1 + A)ᴴ * (cayley A)ᴴ = (1 - A)ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose he
  calc
    (1 + A)ᴴ * ((cayley A)ᴴ * cayley A) * (1 + A) =
        ((1 + A)ᴴ * (cayley A)ᴴ) * (cayley A * (1 + A)) := by noncomm_ring
    _ = (1 - A)ᴴ * (1 - A) := by rw [ht, he]
    _ = (1 + A)ᴴ * (1 : CMat n) * (1 + A) := by
      change Aᴴ = -A at hs
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hs]
      noncomm_ring

theorem cayley_isSkew (Q : CMat n) (hQ : Unitary Q)
    (hd : admissible Q) : GS.IsSkewHermitian (cayley Q) := by
  have he := cayley_mul Q hd
  have ht : (1 + Q)ᴴ * (cayley Q)ᴴ = (1 - Q)ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose he
  have hz : (cayley Q)ᴴ + cayley Q = 0 := by
    apply cancel_congruence (1 + Q) _ 0 hd
    calc
      (1 + Q)ᴴ * ((cayley Q)ᴴ + cayley Q) * (1 + Q) =
          ((1 + Q)ᴴ * (cayley Q)ᴴ) * (1 + Q) +
          (1 + Q)ᴴ * (cayley Q * (1 + Q)) := by noncomm_ring
      _ = (1 - Q)ᴴ * (1 + Q) + (1 + Q)ᴴ * (1 - Q) := by rw [ht, he]
      _ = (2 : ℝ) • (1 - Qᴴ * Q) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, two_smul ℝ]
        noncomm_ring
      _ = (1 + Q)ᴴ * (0 : CMat n) * (1 + Q) := by rw [hQ.1]; simp
  exact eq_neg_of_add_eq_zero_left hz

@[simp] theorem admissible_zero : admissible (0 : CMat n) := by
  simp [admissible]

@[simp] theorem cayley_zero : cayley (0 : CMat n) = 1 := by
  simp [cayley]

@[simp] theorem admissible_one : admissible (1 : CMat n) := by
  simpa only [cayley_zero] using admissible_cayley (0 : CMat n) admissible_zero

@[simp] theorem cayley_one : cayley (1 : CMat n) = 0 := by
  simp [cayley]

/-- A domain-specific inverse formula; no global inverse operation on an orbit
is used. -/
theorem cayley_injective : Set.InjOn (cayley : CMat n → CMat n) {A | admissible A} := by
  intro A hA B hB h
  have h' := congrArg cayley h
  simpa only [cayley_involutive A hA, cayley_involutive B hB] using h'

/-- A skew-Hermitian matrix has an invertible Cayley denominator. -/
theorem admissible_of_isSkew (A : CMat n) (hA : GS.IsSkewHermitian A) : admissible A := by
  have hpos : (1 + Aᴴ * A).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have he : (1 - A) * (1 + A) = 1 + Aᴴ * A := by
    rw [hA]
    noncomm_ring
  have hdet : ((1 - A) * (1 + A)).det ≠ 0 := by
    rw [he]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit)
  rw [Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2

end GS.UnitaryManifold
