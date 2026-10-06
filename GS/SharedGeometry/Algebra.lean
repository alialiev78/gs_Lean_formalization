module

public import GS.GlobalGeometry.SharedAlgebra
public import GS.GlobalGeometry.SharedFactorCurves
public import GS.CayleyCharts.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Inverse and Cayley closure for full physical block sharing

The supported tied matrices form a finite-dimensional unital algebra.  An
invertible element has its inverse in that same algebra: injectivity of left
multiplication implies surjectivity on the algebra.  This avoids an entrywise
inverse formula and works for every within-layer sharing pattern.

Only positive block sizes dividing the matrix dimension are used.  No
smoothness or local lifting property of a shared matrix orbit is assumed.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry GS.CayleyCharts
namespace GS.SharedGeometry
variable {n b : ℕ} {τ : ℕ → ℕ} {A B C : Mat n}

/-- Inverse closure is derived from finite-dimensional linear algebra, not
postulated as a property of the sharing predicate. -/
theorem sharedMatrixSpace_inverse (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hdet : A.det ≠ 0) :
    A⁻¹ ∈ sharedMatrixSpace b τ := by
  let S := sharedMatrixSpace (n := n) b τ
  let m : S →ₗ[ℝ] S :=
    { toFun := fun X => ⟨A * X.val, mul_mem_sharedMatrixSpace hb hbn hA X.property⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        exact Matrix.mul_add A X.val Y.val
      map_smul' := by
        intro a X
        apply Subtype.ext
        change A * (a • X.val) = a • (A * X.val)
        simp only [Matrix.mul_smul] }
  have hm : Function.Injective m := by
    intro X Y h
    apply Subtype.ext
    exact GS.CayleyCharts.cancel_left A X.val Y.val hdet (congrArg Subtype.val h)
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hm)
    (⟨1, one_mem_sharedMatrixSpace b τ⟩ : S)
  have hAX : A * X.val = 1 := congrArg Subtype.val hX
  have he : X.val = A⁻¹ := by
    apply GS.CayleyCharts.cancel_left A X.val A⁻¹ hdet
    rw [hAX, GS.CayleyCharts.mul_inv A hdet]
  rw [← he]
  exact X.property

/-- The original rational Cayley transform preserves all physical block ties. -/
theorem cayley_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (ha : admissible A) :
    cayley A ∈ sharedMatrixSpace b τ := by
  have hplus : 1 + A ∈ sharedMatrixSpace b τ :=
    (sharedMatrixSpace b τ).add_mem (one_mem_sharedMatrixSpace b τ) hA
  have hminus : 1 - A ∈ sharedMatrixSpace b τ :=
    (sharedMatrixSpace b τ).sub_mem (one_mem_sharedMatrixSpace b τ) hA
  exact mul_mem_sharedMatrixSpace hb hbn hminus
    (sharedMatrixSpace_inverse hb hbn hplus ha)

/-- Every shared skew generator gives an actual shared orthogonal factor. -/
theorem cayley_shared (hb : 0 < b) (hbn : b ∣ n)
    (hC : C ∈ sharedSkewSpace b τ) :
    SharedOrthogonalFactor b τ (cayley C) := by
  have ha := admissible_of_isSkew C hC.2.1
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hC.1, hC.2.2⟩ ha
  exact ⟨hm.1, cayley_orthogonal C hC.2.1 ha, hm.2⟩

/-- Inverse Cayley coordinates of a shared orthogonal factor obey the same ties. -/
theorem cayley_sharedSkew (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedOrthogonalFactor b τ A) (ha : admissible A) :
    cayley A ∈ sharedSkewSpace b τ := by
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ha
  exact ⟨hm.1, cayley_isSkew A hA.2.1 ha, hm.2⟩

theorem shared_factor_transpose (hA : SharedOrthogonalFactor b τ A) :
    SharedOrthogonalFactor b τ Aᵀ :=
  ⟨hA.1.transpose, hA.2.1.transpose, hA.2.2.transpose⟩

theorem shared_factor_mul (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedOrthogonalFactor b τ A) (hB : SharedOrthogonalFactor b τ B) :
    SharedOrthogonalFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1,
    TiedEntries.mul hb hbn hA.1 hB.1 hA.2.2 hB.2.2⟩

/-- Conjugation by an actual shared factor preserves the generator space. -/
theorem sharedSkew_conjugate (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedOrthogonalFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    A * C * Aᵀ ∈ sharedSkewSpace b τ := by
  have hm : A * C * Aᵀ ∈ sharedMatrixSpace b τ :=
    mul_mem_sharedMatrixSpace hb hbn
      (mul_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ⟨hC.1, hC.2.2⟩)
      ⟨hA.1.transpose, hA.2.2.transpose⟩
  refine ⟨hm.1, ?_, hm.2⟩
  change (A * C * Aᵀ)ᵀ = -(A * C * Aᵀ)
  have hskew : Cᵀ = -C := hC.2.1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hskew,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- The reverse conjugation is a separate useful form of the same result. -/
theorem sharedSkew_conjugate_transpose (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedOrthogonalFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    Aᵀ * C * A ∈ sharedSkewSpace b τ := by
  simpa only [Matrix.transpose_transpose] using
    sharedSkew_conjugate hb hbn (shared_factor_transpose hA) hC

end GS.SharedGeometry
