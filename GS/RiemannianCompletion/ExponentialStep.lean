module

public import GS.RiemannianCompletion.Gradient
public import GS.Continuation.ExponentialCurves
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exponential updates indexed by genuine tangent vectors

The curve is a map into the original orbit subtype, for all real times. Its
matrix derivative at zero is the actual differential image of the given tangent
vector. The existing normal-acceleration theorem is then transported to the
actual tangent space at every point of the curve. We also prove a first-order
Armijo decrease statement for the negative intrinsic gradient.

No Levi-Civita connection or library geodesic predicate is redefined here. A
normal-acceleration certificate is not labelled as a completed geodesic theorem.
The proofs use the actual tangent atlas and matrix derivatives.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion Filter
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- Cayley coordinate velocities are converted to group generators with the
correct -2,+2 factors. These are definitions of generators, NOT of derivatives. -/
def stepLeftGenerator (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) : Model block₂ :=
  (-2 : ℝ) • v.1

def stepRightGenerator (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) : Model block₁ :=
  (2 : ℝ) • v.2

/-- Concrete orthogonal block factors at every time; no lifting assumption. -/
def stepFactors (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    FactorGroup block₁ block₂ := by
  let g := preferredFactor σ X
  let C := stepLeftGenerator σ X v
  let Ω := stepRightGenerator σ X v
  exact
    (⟨gsExpLeft g.1.val C.val t,
       gsExpLeft_supported _ _ g.1.property.1 C.property.1 t,
       gsExpLeft_orthogonal _ _ g.1.property.2 C.property.2 t⟩,
     ⟨(gsExpRight g.2.valᵀ Ω.val t)ᵀ,
       (gsExpRight_supported _ _ g.2.property.1.transpose Ω.property.1 t).transpose,
       (gsExpRight_orthogonal _ _ g.2.property.2.transpose Ω.property.2 t).transpose⟩)

/-- Global-in-time curve inside the original orbit. Its basepoint uses the
unchanged subtype topology and the new actual tangent space from the atlas. -/
def exponentialStep (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    MatrixOrbit block₁ block₂ (permMatrix σ) :=
  orbitMapToOrbit block₁ block₂ (permMatrix σ) (stepFactors σ X v t)

@[simp] theorem exponentialStep_val (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    (exponentialStep σ X v t).val =
      gsExpCurve (preferredFactor σ X).1.val (permMatrix σ) (preferredFactor σ X).2.valᵀ
        (stepLeftGenerator σ X v).val (stepRightGenerator σ X v).val t := by
  change gsExpLeft _ _ t * permMatrix σ * ((gsExpRight _ _ t)ᵀ)ᵀ = _
  simp only [Matrix.transpose_transpose, gsExpCurve, product2]

@[simp] theorem exponentialStep_zero (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    exponentialStep σ X v 0 = X := by
  apply Subtype.ext
  rw [exponentialStep_val, gsExpCurve_zero, preferredFactor_product]

/-- Initial velocity is the actual mfderiv of the inclusion, not an assumed
identification with a matrix tangent formula. -/
theorem exponentialStep_initial_derivative
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    HasDerivAt (fun t => (exponentialStep σ X v t).val)
      (inclusionDifferential σ X v) 0 := by
  have hd := gsExpCurve_initial_derivative (preferredFactor σ X).1.val
    (permMatrix σ) (preferredFactor σ X).2.valᵀ
    (stepLeftGenerator σ X v).val (stepRightGenerator σ X v).val (perm_orthogonal σ)
  have hi : inclusionDifferential σ X v = tangentParam (preferredFactor σ X).1.val
      (permMatrix σ) (preferredFactor σ X).2.valᵀ
      (stepLeftGenerator σ X v).val (stepRightGenerator σ X v).val := by
    unfold inclusionDifferential
    rw [orbit_val_mfderiv_eq]
    exact orbitParam_fderiv_zero (preferredFactor σ X) (permMatrix σ) v
  simpa only [exponentialStep_val, hi] using hd

/-- The velocity and acceleration are explicit expressions, accompanied below
by proofs that they are the actual first and second derivatives. -/
def stepVelocity (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) : Mat n :=
  gsExpVelocity (preferredFactor σ X).1.val (permMatrix σ) (preferredFactor σ X).2.valᵀ
    (stepLeftGenerator σ X v).val (stepRightGenerator σ X v).val t

def stepAcceleration (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) : Mat n :=
  gsExpAcceleration (preferredFactor σ X).1.val (permMatrix σ) (preferredFactor σ X).2.valᵀ
    (stepLeftGenerator σ X v).val (stepRightGenerator σ X v).val t

theorem exponentialStep_hasDerivAt (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    HasDerivAt (fun s => (exponentialStep σ X v s).val) (stepVelocity σ X v t) t := by
  simpa only [exponentialStep_val, stepVelocity] using
    gsExpCurve_hasDerivAt (preferredFactor σ X).1.val (permMatrix σ)
      (preferredFactor σ X).2.valᵀ (stepLeftGenerator σ X v).val
      (stepRightGenerator σ X v).val (perm_orthogonal σ) t

theorem stepVelocity_hasDerivAt (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    HasDerivAt (stepVelocity σ X v) (stepAcceleration σ X v t) t :=
  gsExpVelocity_hasDerivAt _ _ _ _ _ (perm_orthogonal σ) t

/-- Every actual second derivative is annihilated by the checked point-only
projector. The no-overlap hypothesis is essential here. -/
theorem stepAcceleration_projected_zero
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    pointProjection block₁ block₂ (exponentialStep σ X v t).val
      (stepAcceleration σ X v t) = 0 := by
  let g := preferredFactor σ X
  let C := stepLeftGenerator σ X v
  let Ω := stepRightGenerator σ X v
  rw [exponentialStep_val]
  change pointProjection block₁ block₂
    (product2 (gsExpLeft g.1.val C.val t) (permMatrix σ)
      (gsExpRight g.2.valᵀ Ω.val t)) _ = 0
  apply pointProjection_zero_of_normal block₁ block₂ σ
    (gsExpLeft g.1.val C.val t) (gsExpRight g.2.valᵀ Ω.val t)
    (stepAcceleration σ X v t)
    (gsExpLeft_supported _ _ g.1.property.1 C.property.1 t)
    (gsExpRight_supported _ _ g.2.property.1.transpose Ω.property.1 t)
    (gsExpLeft_orthogonal _ _ g.1.property.2 C.property.2 t)
    (gsExpRight_orthogonal _ _ g.2.property.2.transpose Ω.property.2 t)
  intro Y hY
  exact gsExpCurve_acceleration_normal block₁ block₂ σ _ _ _ _
    (noOverlap_offDiagonalDisjoint σ hno.out) g.1.property.2 g.2.property.2.transpose
    C.property.1 Ω.property.1 C.property.2 Ω.property.2 t Y hY

/-- Normality against every actual tangent vector at the CURRENT point. -/
theorem stepAcceleration_normal_to_tangent
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ)
    (w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) (exponentialStep σ X v t)) :
    frobInner (stepAcceleration σ X v t)
      (inclusionDifferential σ (exponentialStep σ X v t) w) = 0 := by
  rw [← pointProjection_pairing_tangent σ (exponentialStep σ X v t),
    stepAcceleration_projected_zero, frobInner_zero_left]

/-- Fiberwise tangential acceleration vanishes. This is an extrinsic certificate;
no library covariant-derivative or geodesic predicate is asserted by this name. -/
theorem stepAcceleration_tangent_lift_zero
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    tangentProjection σ (exponentialStep σ X v t) (stepAcceleration σ X v t) = 0 := by
  apply inclusionDifferential_injective σ (exponentialStep σ X v t)
  rw [inclusion_tangentProjection, stepAcceleration_projected_zero, map_zero]

theorem stepVelocity_constant_norm
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    frobSq (stepVelocity σ X v t) = tangentPairing σ X v v := by
  let g := preferredFactor σ X
  let C := stepLeftGenerator σ X v
  let Ω := stepRightGenerator σ X v
  change frobSq (gsExpVelocity g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val t) = _
  rw [gsExpCurve_constant_speed block₁ block₂ σ g.1.val g.2.valᵀ C.val Ω.val
    (noOverlap_offDiagonalDisjoint σ hno.out) g.1.property.2 g.2.property.2.transpose
    C.property.1 Ω.property.1 C.property.2 Ω.property.2 t,
    tangentPairing_self_coordinates]
  change frobSq ((-2 : ℝ) • v.1.val) + frobSq ((2 : ℝ) • v.2.val) = _
  rw [frobSq_smul, frobSq_smul]
  ring

/-- The chain rule yields a genuine loss derivative along a feasible curve. -/
theorem loss_along_exponentialStep (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    HasDerivAt (fun t => f (exponentialStep σ X v t).val)
      (tangentPairing σ X (intrinsicGradient σ f X) v) 0 := by
  have hd := ambientGradient_chain hf (exponentialStep_initial_derivative σ X v)
    (congrArg Subtype.val (exponentialStep_zero σ X v))
  simpa only [intrinsicGradient, tangentProjection_pairing] using hd

theorem negative_gradient_loss_derivative (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    HasDerivAt (fun t => f (exponentialStep σ X (-intrinsicGradient σ f X) t).val)
      (-tangentPairing σ X (intrinsicGradient σ f X) (intrinsicGradient σ f X)) 0 := by
  have hd := loss_along_exponentialStep σ f X hf (-intrinsicGradient σ f X)
  have he : tangentPairing σ X (intrinsicGradient σ f X) (-intrinsicGradient σ f X) =
      -tangentPairing σ X (intrinsicGradient σ f X) (intrinsicGradient σ f X) := by
    rw [show (-intrinsicGradient σ f X) = (-1 : ℝ) • intrinsicGradient σ f X by simp,
      tangentPairing_smul_right]
    ring
  rwa [he] at hd

/-- A scalar Armijo lemma proved directly from the derivative limit. It does
not assume a Lipschitz derivative or a convergence theorem for an optimizer. -/
theorem armijo_of_negative_derivative {φ : ℝ → ℝ} {a : ℝ}
    (hd : HasDerivAt φ (-a) 0) (ha : 0 < a) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t < φ 0 - c * t * a := by
  have hlimit := hd.tendsto_slope_zero_right
  have hgap : -a < -c * a := by nlinarith
  have hs : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (φ t - φ 0) < -c * a := by
    simpa only [zero_add, smul_eq_mul] using
      hlimit.eventually (Iio_mem_nhds hgap)
  filter_upwards [hs, self_mem_nhdsWithin] with t ht hpos
  have ht0 : 0 < t := hpos
  have hdiv : (φ t - φ 0) / t < -c * a := by
    simpa only [div_eq_mul_inv, mul_comm] using ht
  have hmul := (div_lt_iff₀ ht0).mp hdiv
  nlinarith

/-- An actual feasible Armijo step exists at all sufficiently small positive
step sizes. This is NOT a fixed-step global convergence assertion. -/
theorem exponentialStep_armijo (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (exponentialStep σ X (-intrinsicGradient σ f X) t).val <
        f X.val - c * t * tangentPairing σ X (intrinsicGradient σ f X)
          (intrinsicGradient σ f X) := by
  have hh := armijo_of_negative_derivative (negative_gradient_loss_derivative σ f X hf)
    (tangentPairing_pos σ X (intrinsicGradient σ f X) hg) c hc hc1
  simpa only [exponentialStep_zero] using hh

end GS.RiemannianCompletion
