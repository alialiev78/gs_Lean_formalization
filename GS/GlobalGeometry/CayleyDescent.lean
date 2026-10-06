module

public import GS.GlobalGeometry.IntrinsicCayley
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic Cayley velocity and certified descent

The Cayley curve is smooth as a map into the actual orbit manifold, and its
mathlib manifold derivative at zero is the prescribed tangent vector. The
negative intrinsic gradient gives an Armijo decrease for every sufficiently
small positive step. These conclusions require only differentiability of the
loss at the current point, with no assumed gradient oracle or convergence claim.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.RiemannianCompletion Filter
open scoped Topology Manifold

namespace GS.GlobalGeometry

variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- Smoothness of the Cayley factors for an arbitrary linear velocity map. -/
private theorem linearCayleyStep_joint_contMDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : FactorGroup b₁ b₂) (Y : Mat n) (D : E →L[ℝ] Mat n) :
    ContMDiff (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, PairModel b₁ b₂)) ⊤
      (fun p : E × ℝ => orbitMapToOrbit b₁ b₂ (permMatrix σ)
        (pointStepFactors g Y (D p.1) p.2)) := by
  have hZ : ContDiff ℝ ⊤ (fun p : E × ℝ => D p.1) :=
    ContDiff.comp (g := fun v : E => D v)
      (f := fun p : E × ℝ => p.1) D.contDiff contDiff_fst
  have hL : ContDiff ℝ ⊤ (fun p : E × ℝ =>
      p.2 • balancedLeft b₁ b₂ Y (D p.1)) :=
    contDiff_snd.smul (ContDiff.comp
      (g := fun q : Mat n × Mat n => balancedLeft b₁ b₂ q.1 q.2)
      (f := fun p : E × ℝ => (Y, D p.1))
      (balancedLeft_smooth b₁ b₂) (contDiff_const.prodMk hZ))
  have hR : ContDiff ℝ ⊤ (fun p : E × ℝ =>
      p.2 • balancedRight b₁ b₂ Y (D p.1)) :=
    contDiff_snd.smul (ContDiff.comp
      (g := fun q : Mat n × Mat n => balancedRight b₁ b₂ q.1 q.2)
      (f := fun p : E × ℝ => (Y, D p.1))
      (balancedRight_smooth b₁ b₂) (contDiff_const.prodMk hZ))
  have hCL := unitCayley_smooth_comp _ hL
    (fun p => isSkew_smul p.2 (balancedLeft_skew b₁ b₂ Y (D p.1)))
  have hCR := unitCayley_smooth_comp _ hR
    (fun p => isSkew_smul p.2 (balancedRight_skew b₁ b₂ Y (D p.1)))
  apply smooth_orbit_of_smooth_factors (b₁ := b₁) (b₂ := b₂) σ (E := E × ℝ)
    (fun p : E × ℝ =>
      pointStepFactors g Y (D p.1) p.2)
  · change ContDiff ℝ ⊤ (fun p : E × ℝ =>
      unitCayley (p.2 • balancedLeft b₁ b₂ Y (D p.1)) * g.1.val)
    exact contDiff_matrix_mul hCL contDiff_const
  · change ContDiff ℝ ⊤ (fun p : E × ℝ =>
      (unitCayley (p.2 • balancedRight b₁ b₂ Y (D p.1)))ᵀ * g.2.val)
    exact contDiff_matrix_mul (contDiff_matrix_transpose hCR) contDiff_const

/-- At a fixed base point the update is jointly smooth in velocity and time.
The source is the chart model of the actual tangent fibre at `X`. -/
theorem cayleyTangentStep_joint_contMDiff
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    ContMDiff (𝓘(ℝ, PairModel b₁ b₂ × ℝ)) (𝓘(ℝ, PairModel b₁ b₂)) ⊤
      (fun p : PairModel b₁ b₂ × ℝ => cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X p.1 p.2) := by
  exact linearCayleyStep_joint_contMDiff (b₁ := b₁) (b₂ := b₂) σ (E := PairModel b₁ b₂)
    (preferredFactor σ X) X.val (inclusionDifferential σ X)

/-- Scaling the tangent vector is equivalent to scaling time. -/
theorem cayleyTangentStep_smul
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) (a t : ℝ) :
    cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X (a • v) t = cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v (t * a) := by
  apply Subtype.ext
  simp only [cayleyTangentStep_val, map_smul, pointCayleyStep,
    balancedLeft_smul, balancedRight_smul, smul_smul]

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def cayleyFibreRetraction (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v 1

@[simp] theorem cayleyFibreRetraction_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X 0 = X :=
  cayleyTangentStep_zero_vector (b₁ := b₁) (b₂ := b₂) σ X 1

theorem cayleyFibreRetraction_contMDiff (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    ContMDiff (𝓘(ℝ, PairModel b₁ b₂)) (𝓘(ℝ, PairModel b₁ b₂)) ⊤
      (fun v : PairModel b₁ b₂ => cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X v) := by
  have hi : ContMDiff (𝓘(ℝ, PairModel b₁ b₂))
      (𝓘(ℝ, PairModel b₁ b₂ × ℝ)) ⊤ (fun v : PairModel b₁ b₂ => (v, (1 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact ContMDiff.comp
    (g := fun p : PairModel b₁ b₂ × ℝ => cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X p.1 p.2)
    (f := fun v : PairModel b₁ b₂ => (v, (1 : ℝ)))
    (cayleyTangentStep_joint_contMDiff (b₁ := b₁) (b₂ := b₂) σ X) hi

/-- Smoothness of the feasible curve in the actual orbit atlas. -/
theorem cayleyTangentStep_contMDiff
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, PairModel b₁ b₂)) ⊤
      (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v) := by
  have hi : ContMDiff (𝓘(ℝ, ℝ))
      (𝓘(ℝ, PairModel b₁ b₂ × ℝ)) ⊤ (fun t : ℝ => (Prod.mk (α := PairModel b₁ b₂) (β := ℝ) v t)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact ContMDiff.comp
    (g := fun p : PairModel b₁ b₂ × ℝ => cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X p.1 p.2)
    (f := fun t : ℝ => (Prod.mk (α := PairModel b₁ b₂) (β := ℝ) v t))
    (cayleyTangentStep_joint_contMDiff (b₁ := b₁) (b₂ := b₂) σ X) hi

/-- The derivative is in mathlib's original tangent space, not only its matrix image. -/
theorem cayleyTangentStep_mfderiv_one
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, PairModel b₁ b₂))
      (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v) 0 (1 : ℝ) = v := by
  apply inclusionDifferential_injective σ X
  have hc := (cayleyTangentStep_contMDiff (b₁ := b₁) (b₂ := b₂) σ X v).mdifferentiable (by simp)
  have hi := (orbit_val_contMDiff (block₁ := b₁) (block₂ := b₂) σ).mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) (hc 0)
    (cayleyTangentStep_at_zero (b₁ := b₁) (b₂ := b₂) σ X v) (1 : ℝ)
  have hmatrix : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Mat n))
      (fun t => (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v t).val) 0 (1 : ℝ) =
        inclusionDifferential σ X v := by
    rw [mfderiv_eq_fderiv]
    exact (cayleyTangentStep_derivative (b₁ := b₁) (b₂ := b₂) σ X v).deriv
  exact hchain.symm.trans hmatrix

/-- Directional form of the retraction derivative at the zero vector. -/
theorem cayleyFibreRetraction_mfderiv_zero_apply
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (v : PairModel b₁ b₂) :
    @Eq (PairModel b₁ b₂)
      (mfderiv (M := PairModel b₁ b₂) (M' := MatrixOrbit b₁ b₂ (permMatrix σ))
        (𝓘(ℝ, PairModel b₁ b₂)) (𝓘(ℝ, PairModel b₁ b₂))
        (fun w : PairModel b₁ b₂ => cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X w)
        (0 : PairModel b₁ b₂) v) v := by
  have hd : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf := (cayleyFibreRetraction_contMDiff (b₁ := b₁) (b₂ := b₂) σ X).mdifferentiable (by simp)
  have hline : (fun t : ℝ => cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X (t • v)) =
      cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v := by
    funext t
    exact (cayleyTangentStep_smul (b₁ := b₁) (b₂ := b₂) σ X v t 1).trans (by rw [one_mul])
  have hlineD : @Eq (PairModel b₁ b₂)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, PairModel b₁ b₂))
        (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  let R : PairModel b₁ b₂ → MatrixOrbit b₁ b₂ (permMatrix σ) :=
    fun w => cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X w
  let DR : PairModel b₁ b₂ →L[ℝ] PairModel b₁ b₂ :=
    mfderiv (𝓘(ℝ, PairModel b₁ b₂)) (𝓘(ℝ, PairModel b₁ b₂)) R (0 : PairModel b₁ b₂)
  let velocity : (ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) → PairModel b₁ b₂ :=
    fun c => mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, PairModel b₁ b₂)) c 0 (1 : ℝ)
  have hchain : @Eq (PairModel b₁ b₂)
      (velocity (fun t : ℝ => R (t • v)))
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, PairModel b₁ b₂))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) :=
    mfderiv_comp_apply_of_eq (0 : ℝ) (hf 0)
      hd.differentiableAt.mdifferentiableAt (zero_smul ℝ v) (1 : ℝ)
  have hright : @Eq (PairModel b₁ b₂)
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, PairModel b₁ b₂))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) (DR v) :=
    congrArg (α := PairModel b₁ b₂) (β := PairModel b₁ b₂) (fun w => DR w) hlineD
  have hcurve : @Eq (PairModel b₁ b₂)
      (velocity (fun t : ℝ => R (t • v)))
      (velocity (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v)) :=
    congrArg (β := PairModel b₁ b₂) velocity hline
  have hvelocity : @Eq (PairModel b₁ b₂)
      (velocity (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v)) v :=
    cayleyTangentStep_mfderiv_one (b₁ := b₁) (b₂ := b₂) σ X v
  exact hright.symm.trans (hchain.symm.trans (hcurve.trans hvelocity))


/-- The derivative of the time-one retraction at the zero vector is the identity. -/
theorem cayleyFibreRetraction_mfderiv_zero
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    mfderiv (M := PairModel b₁ b₂) (M' := MatrixOrbit b₁ b₂ (permMatrix σ))
      (𝓘(ℝ, PairModel b₁ b₂)) (𝓘(ℝ, PairModel b₁ b₂))
      (fun v : PairModel b₁ b₂ => cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X v) (0 : PairModel b₁ b₂) =
        ContinuousLinearMap.id ℝ (PairModel b₁ b₂) := by
  ext v
  exact cayleyFibreRetraction_mfderiv_zero_apply (b₁ := b₁) (b₂ := b₂) σ X v

/-- The loss derivative along the Cayley curve is the intrinsic metric pairing. -/
theorem loss_along_cayleyTangentStep (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) :
    HasDerivAt (fun t => f (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v t).val)
      (tangentPairing σ X (intrinsicGradient σ f X) v) 0 := by
  have hd := ambientGradient_chain hf (cayleyTangentStep_derivative (b₁ := b₁) (b₂ := b₂) σ X v)
    (congrArg Subtype.val (cayleyTangentStep_at_zero (b₁ := b₁) (b₂ := b₂) σ X v))
  simpa only [intrinsicGradient, tangentProjection_pairing] using hd

theorem cayley_negative_gradient_loss_derivative (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    HasDerivAt (fun t => f (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X (-intrinsicGradient σ f X) t).val)
      (-tangentPairing σ X (intrinsicGradient σ f X) (intrinsicGradient σ f X)) 0 := by
  have hd := loss_along_cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ f X hf (-intrinsicGradient σ f X)
  have he : tangentPairing σ X (intrinsicGradient σ f X) (-intrinsicGradient σ f X) =
      -tangentPairing σ X (intrinsicGradient σ f X) (intrinsicGradient σ f X) := by
    rw [show (-intrinsicGradient σ f X) = (-1 : ℝ) • intrinsicGradient σ f X by simp,
      tangentPairing_smul_right]
    ring
  rwa [he] at hd

/-- Backtracking has admissible small steps whenever the gradient is nonzero. -/
theorem cayleyTangentStep_armijo (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X (-intrinsicGradient σ f X) t).val <
        f X.val - c * t * tangentPairing σ X (intrinsicGradient σ f X)
          (intrinsicGradient σ f X) := by
  have hh := armijo_of_negative_derivative
    (cayley_negative_gradient_loss_derivative (b₁ := b₁) (b₂ := b₂) σ f X hf)
    (tangentPairing_pos σ X (intrinsicGradient σ f X) hg) c hc hc1
  simpa only [cayleyTangentStep_at_zero] using hh

/-- Geometric backtracking terminates after finitely many reductions.
No uniform iteration bound is asserted from mere pointwise differentiability. -/
theorem cayley_backtracking_terminates (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X (-intrinsicGradient σ f X) (α * ρ ^ k)).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing σ X (intrinsicGradient σ f X)
          (intrinsicGradient σ f X) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually (cayleyTangentStep_armijo (b₁ := b₁) (b₂ := b₂) σ f X hf hg c hc hc1)).exists

end GS.GlobalGeometry
