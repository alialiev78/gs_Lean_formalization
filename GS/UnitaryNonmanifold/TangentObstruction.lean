module

public import GS.UnitaryNonmanifold.BlockInvariant
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# First-order restrictions from commuting Hermitian block Grams

At a scalar base point, pairwise commutation of two matrix curves imposes a
quadratic restriction on their derivatives. This is a restriction on actual
curve velocities, including curves that do not lift differentiably to factors.
-/

noncomputable section
open Matrix Filter
open scoped Topology
namespace GS.UnitaryNonmanifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem derivatives_commute_at_scalars {f g : ℝ → CMat n} {u v : CMat n}
    {a b : ℂ} (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0)
    (hf0 : f 0 = a • 1) (hg0 : g 0 = b • 1)
    (hcomm : ∀ᶠ t in 𝓝 (0 : ℝ), f t * g t = g t * f t) :
    u * v = v * u := by
  have hlimf : Tendsto (fun t : ℝ => t⁻¹ • (f t - f 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 u) := by
    simpa only [zero_add] using hf.tendsto_slope_zero
  have hlimg : Tendsto (fun t : ℝ => t⁻¹ • (g t - g 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
    simpa only [zero_add] using hg.tendsto_slope_zero
  have hm : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (t⁻¹ • (f t-f 0)) * (t⁻¹ • (g t-g 0)) =
      (t⁻¹ • (g t-g 0)) * (t⁻¹ • (f t-f 0)) := by
    filter_upwards [hcomm.filter_mono nhdsWithin_le_nhds] with t ht
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    congr 1
    rw [hf0, hg0]
    simp only [sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one]
    rw [ht]
    have hab : a • (b • (1 : CMat n)) = b • (a • (1 : CMat n)) :=
      smul_comm a b 1
    rw [hab]
    abel
  exact tendsto_nhds_unique_of_eventuallyEq (hlimf.mul hlimg) (hlimg.mul hlimf) hm

theorem derivative_conjTranspose {f : ℝ → CMat n} {u : CMat n}
    (hf : HasDerivAt f u 0) : HasDerivAt (fun t => (f t)ᴴ) uᴴ 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j)) i).star

theorem derivative_matrix_mul {f g : ℝ → CMat n} {u v : CMat n}
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
  simpa only [Finset.sum_fn, Pi.mul_def] using hs

theorem derivative_gram {f : ℝ → CMat n} {u : CMat n}
    (hf : HasDerivAt f u 0) :
    HasDerivAt (fun t => f t * (f t)ᴴ) (u * (f 0)ᴴ + f 0 * uᴴ) 0 := by
  exact derivative_matrix_mul hf (derivative_conjTranspose hf)

theorem derivative_cBlock {q : ℕ} {f : ℝ → CMat (q*2)} {v : CMat (q*2)}
    (hf : HasDerivAt f v 0) (i j : Fin q) :
    HasDerivAt (fun t => cBlock (f t) i j) (cBlock v i j) 0 := by
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf (finProdFinEquiv (i,a))))
    (finProdFinEquiv (j,b))

/-- The linearized Hermitian block Gram at the specified base point. -/
def gramVelocity {q : ℕ} (X V : CMat (q*2)) (i j : Fin q) : CMat 2 :=
  cBlock V i j * (cBlock X i j)ᴴ + cBlock X i j * (cBlock V i j)ᴴ

theorem derivative_rowGram {q : ℕ} {f : ℝ → CMat (q*2)} {v : CMat (q*2)}
    (hf : HasDerivAt f v 0) (i j : Fin q) :
    HasDerivAt (fun t => rowGram (f t) i j) (gramVelocity (f 0) v i j) 0 :=
  derivative_gram (derivative_cBlock hf i j)

/-- Every actual curve in the unitary block-sandwich set obeys this quadratic
velocity constraint whenever the two base Grams are scalar. -/
theorem curve_gramVelocities_commute {q : ℕ} {f : ℝ → CMat (q*2)} {v : CMat (q*2)}
    (hf : HasDerivAt f v 0) (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), BlockSandwich (f t))
    (i j k : Fin q) (a b : ℂ)
    (hj : rowGram (f 0) i j = a • 1) (hk : rowGram (f 0) i k = b • 1) :
    gramVelocity (f 0) v i j * gramVelocity (f 0) v i k =
      gramVelocity (f 0) v i k * gramVelocity (f 0) v i j := by
  apply derivatives_commute_at_scalars (derivative_rowGram hf i j)
    (derivative_rowGram hf i k) hj hk
  exact hmem.mono (fun _ ht => blockSandwich_row_gram_commute ht i j k)

end GS.UnitaryNonmanifold
