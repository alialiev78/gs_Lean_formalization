module

public import GS.Unitary.GeometryAlgebra
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Real derivatives of complex matrix operations

These statements use the inherited finite-product topology on complex matrices,
viewed as a real vector space.
-/

noncomputable section
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem hasDerivAt_matrix_conjTranspose {f : ℝ → CMat n} {u : CMat n}
    (hf : HasDerivAt f u 0) : HasDerivAt (fun t => (f t)ᴴ) uᴴ 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j)) i).star

theorem hasDerivAt_matrix_mul {f g : ℝ → CMat n} {u v : CMat n}
    (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0) :
    HasDerivAt (fun t => f t * g t) (u * g 0 + f 0 * v) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) k).mul
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k)) j))
  simpa only [Finset.sum_apply, Finset.sum_fn, Pi.mul_apply, Pi.mul_def] using hs

theorem hasDerivAt_product2 (P : CMat n) {f g : ℝ → CMat n} {u v : CMat n}
    (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0) :
    HasDerivAt (fun t => GS.UnitaryGeometry.product2 (f t) P (g t))
      (u * P * g 0 + f 0 * P * v) 0 := by
  simpa only [GS.UnitaryGeometry.product2, Matrix.mul_zero, add_zero] using
    hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hf (hasDerivAt_const 0 P)) hg

end GS.UnitaryManifold
