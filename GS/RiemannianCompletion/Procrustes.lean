module

public import GS.RiemannianCompletion.ExponentialStep

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The GS Procrustes objective with a real derivative and intrinsic gradient

This specializes the new gradient and descent theorems to the explicit loss
one-half the squared Frobenius distance. The ambient gradient is derived by
calculus, not supplied as a hypothesis. No inner-product instance conflicting
with the default norm on Matrix is introduced.

The gradient and step inequalities below are derived from the explicit loss.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion Filter
open scoped BigOperators Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ}

/-- The exact objective used for the nearest-matrix problem. -/
def procrustesLoss (T X : Mat n) : ℝ := (1 / 2 : ℝ) * frobSq (X - T)

theorem procrustesLoss_smooth (T : Mat n) : ContDiff ℝ ⊤ (procrustesLoss T) := by
  have h : ContDiff ℝ ⊤ (fun X : Mat n => X - T) := contDiff_id.sub contDiff_const
  exact contDiff_const.mul (frobInner_smooth.comp (h.prodMk h))

/-- A scalar derivative of the explicit finite sum. -/
theorem procrustesLoss_line_derivative (T X V : Mat n) :
    HasDerivAt (fun t : ℝ => procrustesLoss T (X + t • V)) (frobInner (X-T) V) 0 := by
  have hc (i j : Fin n) : HasDerivAt
      (fun t : ℝ => ((X + t • V - T) i j) * ((X + t • V - T) i j))
      (2 * (X i j - T i j) * V i j) 0 := by
    have he : HasDerivAt (fun t : ℝ => X i j + t * V i j - T i j) (V i j) 0 := by
      simpa using ((hasDerivAt_const (0 : ℝ) (X i j)).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (V i j))).sub_const (T i j)
    convert he.mul he using 1 <;> simp only [Pi.mul_def, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, zero_mul, add_zero] <;> ring
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ => hc i j))
  have hd := hs.const_mul (1 / 2 : ℝ)
  have hn : (1 / 2 : ℝ) * (∑ i, ∑ j, 2 * (X i j - T i j) * V i j) =
      frobInner (X-T) V := by
    unfold frobInner
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change (1/2 : ℝ) * (2 * (X i j - T i j) * V i j) = (X i j - T i j) * V i j
    ring
  simpa only [procrustesLoss, frobSq, frobInner, hn, Finset.sum_fn] using hd

/-- No formal-gradient assumption: the actual fderiv is identified by comparing
its directional derivatives with the derivative of the explicit polynomial. -/
theorem procrustesLoss_fderiv_apply (T X V : Mat n) :
    fderiv ℝ (procrustesLoss T) X V = frobInner (X-T) V := by
  have hf := ((procrustesLoss_smooth T).differentiable (by simp) X).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => X + t • V) V 0 :=
    hasDerivAt_affine_matrix X V 0
  have hd := hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hd.unique (procrustesLoss_line_derivative T X V)

@[simp] theorem ambientGradient_procrustes (T X : Mat n) :
    ambientGradient (procrustesLoss T) X = X - T := by
  ext i j
  change fderiv ℝ (procrustesLoss T) X (unitEntry i j) = (X-T) i j
  rw [procrustesLoss_fderiv_apply, frobInner_unitEntry_right]

variable {block₁ block₂ : Fin n → ℕ} (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

theorem intrinsicGradient_procrustes (T : Mat n)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    intrinsicGradient σ (procrustesLoss T) X = tangentProjection σ X (X.val - T) := by
  simp only [intrinsicGradient, ambientGradient_procrustes]

/-- The projected residual is the ambient representative of the intrinsic
Procrustes gradient on the actual tangent space. -/
theorem procrustes_gradient_ambient (T : Mat n)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    inclusionDifferential σ X (intrinsicGradient σ (procrustesLoss T) X) =
      pointProjection block₁ block₂ X.val (X.val - T) := by
  rw [intrinsicGradient_ambient, ambientGradient_procrustes]

/-- A matrix's own radial direction is normal to the orthogonal group. This
uses the existing point-only formula, and does not assume no-overlap. -/
theorem pointProjection_radial_zero (block₁ block₂ : Fin n → ℕ)
    (X : Mat n) (hX : Orthogonal X) : pointProjection block₁ block₂ X X = 0 := by
  have hz (block : Fin n → ℕ) : blockSkew block (1 : Mat n) = 0 := by
    ext i j
    simp [blockSkew, maskedSkew, mask, GS.skew, Matrix.one_apply, eq_comm]
  have hl : leftPointProjection block₂ X X = 0 := by
    simp only [leftPointProjection, hX.2, hz, Matrix.zero_mul]
  have hr : rightPointProjection block₁ X X = 0 := by
    simp only [rightPointProjection, hX.1, hz, Matrix.mul_zero]
  have hl0 : leftPointProjection block₂ X (0 : Mat n) = 0 := by
    have hs : blockSkew block₂ (0 : Mat n) = 0 := by
      ext i j
      simp [blockSkew, maskedSkew, mask, GS.skew]
    simp only [leftPointProjection, Matrix.zero_mul, hs]
  simp only [pointProjection, hl, hr, hl0, add_zero, sub_zero]

theorem tangentProjection_radial_zero
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) : tangentProjection σ X X.val = 0 := by
  have hX : Orthogonal X.val := by
    rw [← preferredFactor_product σ X]
    exact (((preferredFactor σ X).1.property.2).mul (perm_orthogonal σ)).mul
      (preferredFactor σ X).2.property.2.transpose
  apply inclusionDifferential_injective σ X
  rw [inclusion_tangentProjection, pointProjection_radial_zero _ _ _ hX, map_zero]

/-- On the orthogonal feasible set only the target contributes to the gradient. -/
theorem intrinsicGradient_procrustes_eq_neg (T : Mat n)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    intrinsicGradient σ (procrustesLoss T) X = -tangentProjection σ X T := by
  rw [intrinsicGradient_procrustes]
  change tangentProjectionLinear σ X (X.val - T) = _
  rw [map_sub]
  change tangentProjection σ X X.val - tangentProjection σ X T = _
  rw [tangentProjection_radial_zero, zero_sub]

/-- Actual manifold stationarity, not merely vanishing parameter gradients. -/
theorem procrustes_stationary_iff (T : Mat n)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => procrustesLoss T Y.val) X = 0
      ↔ pointProjection block₁ block₂ X.val (X.val - T) = 0 := by
  rw [← intrinsicGradient_zero_iff σ (procrustesLoss T) X
    ((procrustesLoss_smooth T).differentiable (by simp) X.val),
    intrinsicGradient_zero_iff_projected, ambientGradient_procrustes]

/-- No differentiability hypothesis remains in this concrete Armijo corollary. -/
theorem procrustes_exponential_armijo (T : Mat n)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (hg : intrinsicGradient σ (procrustesLoss T) X ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      procrustesLoss T (exponentialStep σ X (-intrinsicGradient σ (procrustesLoss T) X) t).val <
        procrustesLoss T X.val - c * t *
          frobSq (pointProjection block₁ block₂ X.val (X.val - T)) := by
  have hh := exponentialStep_armijo σ (procrustesLoss T) X
    ((procrustesLoss_smooth T).differentiable (by simp) X.val) hg c hc hc1
  simpa only [intrinsicGradient_norm, ambientGradient_procrustes] using hh

end GS.RiemannianCompletion
