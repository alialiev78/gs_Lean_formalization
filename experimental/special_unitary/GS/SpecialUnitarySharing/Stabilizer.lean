module

public import GS.SpecialUnitarySharing.Exponential
public import GS.SpecialUnitarySharing.Directions
public import GS.UnitaryManifold.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The exact infinitesimal stabilizer for SU shared factors

The synthesis kernel is characterized by actual constant one-parameter
matrix-orbit curves, in both directions. This supplies the exponential
stabilizer part of a future SU horizontal-slice construction. It does not
assume that the stabilizer is discrete or that arbitrary image curves lift.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {right left : Pattern n}

def generatorExpWord (X : CMat n) (v : PairGenerator right left) (t : ℝ) : CMat n :=
  cExpLine v.1.val t * X * cExpLine v.2.val t

@[simp] theorem generatorExpWord_zero (X : CMat n) (v : PairGenerator right left) :
    generatorExpWord X v 0 = X := by simp [generatorExpWord]

theorem generatorExpWord_hasDerivAt_zero (X : CMat n) (v : PairGenerator right left) :
    HasDerivAt (generatorExpWord X v) (pointMap right left X v) 0 := by
  have hd := GS.UnitaryManifold.hasDerivAt_matrix_mul
    (GS.UnitaryManifold.hasDerivAt_matrix_mul (cExpLine_hasDerivAt v.1.val 0)
      (hasDerivAt_const (0 : ℝ) X)) (cExpLine_hasDerivAt v.2.val 0)
  simpa only [generatorExpWord, cExpLine_zero, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, add_zero] using hd

theorem generatorExpWord_const_of_kernel (X : CMat n) (v : PairGenerator right left)
    (hv : pointMap right left X v = 0) (t : ℝ) : generatorExpWord X v t = X := by
  have hi : v.1.val * X = X * (-v.2.val) := by
    rw [Matrix.mul_neg]
    exact (pointMap_kernel_iff X v).mp hv
  have hti : (t • v.1.val) * X = X * (t • (-v.2.val)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hi]
  have he := cMatrixExp_intertwine (t • v.1.val) (t • (-v.2.val)) X hti
  change cMatrixExp (t • v.1.val) * X * cMatrixExp (t • v.2.val) = X
  rw [he, Matrix.mul_assoc, smul_neg, cMatrixExp_neg_mul, Matrix.mul_one]

/-- An actual matrix statement equivalent to the kernel condition. -/
theorem pointMap_kernel_iff_exponential_stabilizes (X : CMat n) (v : PairGenerator right left) :
    pointMap right left X v = 0 ↔ ∀ t : ℝ, generatorExpWord X v t = X := by
  constructor
  · exact fun hv t => generatorExpWord_const_of_kernel X v hv t
  · intro h
    have he : generatorExpWord X v = fun _ : ℝ => X := funext h
    have hd := generatorExpWord_hasDerivAt_zero X v
    rw [he] at hd
    exact hd.unique (hasDerivAt_const (0 : ℝ) X)

end GS.SpecialUnitarySharing
