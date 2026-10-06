module

public import GS.RiemannianCompletion.TangentMetric
public import GS.ManifoldCompletion.OrbitSmooth

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The gradient of an actual restricted loss on the no-overlap orbit

The differential in the Riesz identity is mathlib's mfderiv of f restricted to
MatrixOrbit. The ambient gradient is obtained from the actual fderiv; it is not
an input assumed to represent the derivative. The unique tangent lift of the
old matrix projector defines the vector, and the Riesz identity is PROVED.

No norm instance is installed: the chart norm and the Frobenius metric are
kept distinct. Smooth metric evaluation on the total tangent bundle is proved
in `GS.GlobalGeometry.TangentBundleMetric`.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- Chain rule for the actual manifold differential of the restricted loss.
This follows the preferred-chart reduction already used in TangentBridge and
isolates the version-sensitive unfolding of mfderiv in one place. -/
theorem restricted_loss_mfderiv (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (hf : DifferentiableAt ℝ f X.val) :
    mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => f Y.val) X =
        (fderiv ℝ f X.val).comp (inclusionDifferential σ X) := by
  let g := preferredFactor σ X
  let p := orbitParam g (permMatrix σ)
  have hp0 : p 0 = X.val := by
    change chartInv g.1 0 * permMatrix σ * (chartInv g.2 0)ᵀ = X.val
    rw [chartInv_zero, chartInv_zero]
    exact preferredFactor_product σ X
  have hp : DifferentiableAt ℝ p 0 :=
    (orbitParam_smooth g (permMatrix σ)).differentiable (by simp) 0
  have hf' : DifferentiableAt ℝ f (p 0) := by simpa only [hp0] using hf
  have hc : DifferentiableAt ℝ (fun a => f (p a)) 0 := hf'.comp 0 hp
  have hm : MDifferentiableAt (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => f Y.val) X := by
    rw [mdifferentiableAt_iff]
    refine ⟨hf.continuousAt.comp continuous_subtype_val.continuousAt, ?_⟩
    change DifferentiableWithinAt ℝ
      (fun a : PairModel block₁ block₂ => f (orbitInverse σ g a).val)
      (Set.range (id : PairModel block₁ block₂ → PairModel block₁ block₂))
      (orbitCoordinates σ hno.out g X)
    simpa only [orbitInverse_val, g, orbitCoordinates_preferred, Set.range_id, p] using
      (hc.differentiableWithinAt : DifferentiableWithinAt ℝ
        (fun a => f (p a)) Set.univ 0)
  have hi : inclusionDifferential σ X = fderiv ℝ p 0 :=
    orbit_val_mfderiv_eq σ X
  rw [hi]
  conv_lhs => unfold mfderiv
  rw [if_pos hm]
  change fderivWithin ℝ
    (fun a : PairModel block₁ block₂ => f (orbitInverse σ g a).val)
    (Set.range (id : PairModel block₁ block₂ → PairModel block₁ block₂))
    (orbitCoordinates σ hno.out g X) = _
  simp only [orbitInverse_val, g, orbitCoordinates_preferred, Set.range_id,
    fderivWithin_univ]
  simpa only [Function.comp_def, hp0, p, g] using fderiv_comp 0 hf' hp

/-- This vector inhabits mathlib's TangentSpace for the constructed atlas. -/
def intrinsicGradient (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X :=
  tangentProjection σ X (ambientGradient f X.val)

@[simp] theorem intrinsicGradient_ambient (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    inclusionDifferential σ X (intrinsicGradient σ f X) =
      pointProjection block₁ block₂ X.val (ambientGradient f X.val) :=
  inclusion_tangentProjection σ X _

/-- Riesz characterization against the ACTUAL derivative of f restricted to M. -/
theorem intrinsicGradient_characterization (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X (intrinsicGradient σ f X) v =
      mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => f Y.val) X v := by
  rw [restricted_loss_mfderiv σ f X hf]
  change tangentPairing σ X (intrinsicGradient σ f X) v =
    fderiv ℝ f X.val (inclusionDifferential σ X v)
  rw [ambientGradient_represents]
  exact tangentProjection_pairing σ X _ v

/-- The characterization determines a unique vector, not merely some lift. -/
theorem intrinsicGradient_unique (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X)
    (hw : ∀ v, tangentPairing σ X w v =
      mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => f Y.val) X v) :
    w = intrinsicGradient σ f X := by
  apply tangentProjection_unique σ X (ambientGradient f X.val)
  intro v
  rw [hw, restricted_loss_mfderiv σ f X hf]
  change fderiv ℝ f X.val (inclusionDifferential σ X v) = _
  exact ambientGradient_represents f X.val (inclusionDifferential σ X v)

/-- First-order stationarity is equivalent to the zero projected gradient. -/
theorem intrinsicGradient_zero_iff (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    intrinsicGradient σ f X = 0 ↔
      mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => f Y.val) X = 0 := by
  constructor
  · intro hg
    ext v
    rw [← intrinsicGradient_characterization σ f X hf, hg]
    simp
  · intro hd
    apply (tangentPairing_self_eq_zero_iff σ X _).mp
    rw [intrinsicGradient_characterization σ f X hf, hd]
    rfl

theorem intrinsicGradient_zero_iff_projected (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    intrinsicGradient σ f X = 0 ↔
      pointProjection block₁ block₂ X.val (ambientGradient f X.val) = 0 := by
  constructor
  · intro hg
    rw [← intrinsicGradient_ambient σ f X, hg, map_zero]
  · intro hp
    apply inclusionDifferential_injective σ X
    rw [intrinsicGradient_ambient, hp, map_zero]

/-- The exact norm used by the algorithm is the norm of the internal vector
under the Frobenius pullback, NOT the norm of its Cayley coordinates. -/
theorem intrinsicGradient_norm (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    tangentPairing σ X (intrinsicGradient σ f X) (intrinsicGradient σ f X) =
      frobSq (pointProjection block₁ block₂ X.val (ambientGradient f X.val)) := by
  unfold tangentPairing
  rw [intrinsicGradient_ambient]
  rfl

/-- A scalar quadratic model on the true tangent fiber. -/
def tangentQuadraticModel (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) : ℝ :=
  let df : ℝ := mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ))
    (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => f Y.val) X v
  df + (1 / 2 : ℝ) * tangentPairing σ X v v

/-- Completing the square proves the variational meaning of -grad. -/
theorem tangentQuadraticModel_complete_square (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentQuadraticModel σ f X v =
      (1 / 2 : ℝ) * tangentPairing σ X (v + intrinsicGradient σ f X)
        (v + intrinsicGradient σ f X) -
      (1 / 2 : ℝ) * tangentPairing σ X (intrinsicGradient σ f X)
        (intrinsicGradient σ f X) := by
  unfold tangentQuadraticModel
  rw [← intrinsicGradient_characterization σ f X hf]
  rw [tangentPairing_add_left, tangentPairing_add_right, tangentPairing_add_right,
    tangentPairing_symm σ X v (intrinsicGradient σ f X)]
  ring

theorem tangentQuadraticModel_minimal (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentQuadraticModel σ f X (-intrinsicGradient σ f X) ≤
      tangentQuadraticModel σ f X v := by
  rw [tangentQuadraticModel_complete_square σ f X hf,
    tangentQuadraticModel_complete_square σ f X hf]
  simp only [neg_add_cancel, tangentPairing_zero_left, mul_zero, zero_sub]
  have h := tangentPairing_self_nonneg σ X (v + intrinsicGradient σ f X)
  linarith

theorem tangentQuadraticModel_equality_iff (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentQuadraticModel σ f X v = tangentQuadraticModel σ f X (-intrinsicGradient σ f X)
      ↔ v = -intrinsicGradient σ f X := by
  rw [tangentQuadraticModel_complete_square σ f X hf,
    tangentQuadraticModel_complete_square σ f X hf]
  simp only [neg_add_cancel, tangentPairing_zero_left, mul_zero, zero_sub]
  constructor
  · intro he
    have hz : tangentPairing σ X (v + intrinsicGradient σ f X)
        (v + intrinsicGradient σ f X) = 0 := by linarith
    exact eq_neg_of_add_eq_zero_left ((tangentPairing_self_eq_zero_iff σ X _).mp hz)
  · intro he
    simp only [he, neg_add_cancel, tangentPairing_zero_left, mul_zero, zero_sub]

/-- The bundled derivative preserves the stated regularity, using the
derivative theorem from the pinned mathlib version. -/
theorem smooth_fderiv_of_smooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fderiv ℝ f) := by
  exact hf.fderiv_right (by simp)

/-- No smooth-gradient hypothesis is assumed: it is derived from smoothness of f. -/
theorem ambientGradient_smooth (f : Mat n → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (ambientGradient f) :=
  ambientGradient_smooth_of_fderiv f (smooth_fderiv_of_smooth f hf)

/-- The ambient realization is a genuinely smooth map from the orbit manifold.
Smoothness of the section into the full tangent bundle is a separate theorem. -/
theorem intrinsicGradient_ambient_smooth (f : Mat n → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContMDiff (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n)) ⊤
      (fun X : MatrixOrbit block₁ block₂ (permMatrix σ) =>
        inclusionDifferential σ X (intrinsicGradient σ f X)) := by
  have hh := projected_field_contMDiff (block₁ := block₁) (block₂ := block₂)
    σ (ambientGradient f) (ambientGradient_smooth f hf)
  simpa only [intrinsicGradient_ambient] using hh

end GS.RiemannianCompletion
