module

public import GS.GlobalGeometry.IntrinsicCayley
public import GS.OverlapGeometry.Gradient
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A Cayley retraction on every actual tangent fibre, allowing overlap

The orbit retains the horizontal atlas and inherited matrix topology. The
Cayley curve is globally defined, is smooth jointly in velocity and time at
any fixed base point, and its actual manifold derivative is the prescribed
tangent vector. The time-one map has derivative equal to the identity at zero.
These are fibrewise statements; no total tangent-bundle smoothness is claimed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.GlobalGeometry Filter
open scoped Topology Manifold
namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance retractionHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance retractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- A globally defined curve into the original orbit, indexed by an actual
TangentSpace vector. The factor choice is used only to certify membership. -/
def cayleyTangentStep (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ)
    (pointStepFactors (preferredFactor σ X) X.val (inclusionDifferential b₁ b₂ σ X v) t)

@[simp] theorem cayleyTangentStep_val (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    (cayleyTangentStep b₁ b₂ σ X v t).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) t := by
  let g := preferredFactor σ X
  let U := unitCayley (t • balancedLeft b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v))
  let V := unitCayley (t • balancedRight b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v))
  change (U * g.1.val) * permMatrix σ * (Vᵀ * g.2.val)ᵀ = U * X.val * V
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hg : g.1.val * permMatrix σ * g.2.valᵀ = X.val :=
    congrArg Subtype.val (preferredFactor_spec σ X)
  calc
    (U * g.1.val) * permMatrix σ * (g.2.valᵀ * V) =
        U * (g.1.val * permMatrix σ * g.2.valᵀ) * V := by simp only [Matrix.mul_assoc]
    _ = U * X.val * V := by rw [hg]

@[simp] theorem cayleyTangentStep_at_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) : cayleyTangentStep b₁ b₂ σ X v 0=X := by
  apply Subtype.ext
  simp

@[simp] theorem cayleyTangentStep_zero_vector (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (t : ℝ) : cayleyTangentStep b₁ b₂ σ X 0 t=X := by
  apply Subtype.ext
  simp

theorem cayleyTangentStep_derivative (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) :
    HasDerivAt (fun t => (cayleyTangentStep b₁ b₂ σ X v t).val)
      (inclusionDifferential b₁ b₂ σ X v) 0 := by
  have hd := pointCayleyStep_derivative b₁ b₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ
    (inclusionDifferential b₁ b₂ σ X v)
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose
  dsimp only at hd
  have hfix : pointProjection b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) =
      inclusionDifferential b₁ b₂ σ X v :=
    (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mpr ⟨v,rfl⟩
  rw [preferredFactor_product b₁ b₂ σ X, hfix] at hd
  simpa only [cayleyTangentStep_val] using hd

set_option maxHeartbeats 800000 in
/-- Fixed-base smoothness jointly in the actual tangent coordinate and time. -/
theorem cayleyTangentStep_joint_contMDiff
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ × ℝ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (fun p : HorizontalModel b₁ b₂ σ × ℝ => cayleyTangentStep b₁ b₂ σ X p.1 p.2) := by
  let D : HorizontalModel b₁ b₂ σ →L[ℝ] Mat n := inclusionDifferential b₁ b₂ σ X
  have hd : ContDiff ℝ ⊤ (fun p : HorizontalModel b₁ b₂ σ × ℝ => D p.1) :=
    ContDiff.comp (f := fun p : HorizontalModel b₁ b₂ σ × ℝ => p.1)
      (g := fun v : HorizontalModel b₁ b₂ σ => D v) D.contDiff contDiff_fst
  have hp : ContDiff ℝ ⊤ (fun p : HorizontalModel b₁ b₂ σ × ℝ =>
      pointCayleyStep b₁ b₂ X.val (D p.1) p.2) :=
    ContDiff.comp
      (f := fun p : HorizontalModel b₁ b₂ σ × ℝ => ((X.val, D p.1), p.2))
      (g := fun p : (Mat n × Mat n) × ℝ => pointCayleyStep b₁ b₂ p.1.1 p.1.2 p.2)
      (pointCayleyStep_smooth b₁ b₂) ((contDiff_const.prodMk hd).prodMk contDiff_snd)
  apply (overlap_contMDiff_iff_contDiff b₁ b₂ σ _).mpr
  convert hp using 1
  funext p
  exact cayleyTangentStep_val b₁ b₂ σ X p.1 p.2

/-- Scaling the tangent vector is equivalent to scaling time. -/
theorem cayleyTangentStep_smul
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (a t : ℝ) :
    cayleyTangentStep b₁ b₂ σ X (a • v) t = cayleyTangentStep b₁ b₂ σ X v (t * a) := by
  apply Subtype.ext
  simp only [cayleyTangentStep_val, map_smul, pointCayleyStep,
    balancedLeft_smul, balancedRight_smul, smul_smul]

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def cayleyFibreRetraction (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  cayleyTangentStep b₁ b₂ σ X v 1

@[simp] theorem cayleyFibreRetraction_val (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    (cayleyFibreRetraction b₁ b₂ σ X v).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) 1 :=
  cayleyTangentStep_val b₁ b₂ σ X v 1

@[simp] theorem cayleyFibreRetraction_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    cayleyFibreRetraction b₁ b₂ σ X 0 = X :=
  cayleyTangentStep_zero_vector b₁ b₂ σ X 1

theorem cayleyFibreRetraction_contMDiff (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (fun v : HorizontalModel b₁ b₂ σ => cayleyFibreRetraction b₁ b₂ σ X v) := by
  have hi : ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ × ℝ)) ⊤ (fun v : HorizontalModel b₁ b₂ σ => (v, (1 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel b₁ b₂ σ × ℝ => cayleyTangentStep b₁ b₂ σ X p.1 p.2)
    (f := fun v : HorizontalModel b₁ b₂ σ => (v, (1 : ℝ)))
    (cayleyTangentStep_joint_contMDiff b₁ b₂ σ X) hi

/-- Smoothness of the feasible curve in the actual orbit atlas. -/
theorem cayleyTangentStep_contMDiff
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (cayleyTangentStep b₁ b₂ σ X v) := by
  have hi : ContMDiff (𝓘(ℝ, ℝ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ × ℝ)) ⊤ (fun t : ℝ => (Prod.mk (α := HorizontalModel b₁ b₂ σ) (β := ℝ) v t)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel b₁ b₂ σ × ℝ => cayleyTangentStep b₁ b₂ σ X p.1 p.2)
    (f := fun t : ℝ => (Prod.mk (α := HorizontalModel b₁ b₂ σ) (β := ℝ) v t))
    (cayleyTangentStep_joint_contMDiff b₁ b₂ σ X) hi

/-- The derivative is in mathlib's original tangent space, not only its matrix image. -/
theorem cayleyTangentStep_mfderiv_one
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (cayleyTangentStep b₁ b₂ σ X v) 0 (1 : ℝ) = v := by
  apply inclusionDifferential_injective b₁ b₂ σ X
  have hc := (cayleyTangentStep_contMDiff b₁ b₂ σ X v).mdifferentiable (by simp)
  have hi := (overlap_val_contMDiff b₁ b₂ σ).mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) (hc 0)
    (cayleyTangentStep_at_zero b₁ b₂ σ X v) (1 : ℝ)
  have hmatrix : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Mat n))
      (fun t => (cayleyTangentStep b₁ b₂ σ X v t).val) 0 (1 : ℝ) =
        inclusionDifferential b₁ b₂ σ X v := by
    rw [mfderiv_eq_fderiv]
    exact (cayleyTangentStep_derivative b₁ b₂ σ X v).deriv
  exact hchain.symm.trans hmatrix

/-- Directional form of the retraction derivative at the zero vector. -/
theorem cayleyFibreRetraction_mfderiv_zero_apply
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (v : HorizontalModel b₁ b₂ σ) :
    @Eq (HorizontalModel b₁ b₂ σ)
      (mfderiv (M := HorizontalModel b₁ b₂ σ) (M' := MatrixOrbit b₁ b₂ (permMatrix σ))
        (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun w : HorizontalModel b₁ b₂ σ => cayleyFibreRetraction b₁ b₂ σ X w)
        (0 : HorizontalModel b₁ b₂ σ) v) v := by
  have hd : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf := (cayleyFibreRetraction_contMDiff b₁ b₂ σ X).mdifferentiable (by simp)
  have hline : (fun t : ℝ => cayleyFibreRetraction b₁ b₂ σ X (t • v)) =
      cayleyTangentStep b₁ b₂ σ X v := by
    funext t
    exact (cayleyTangentStep_smul b₁ b₂ σ X v t 1).trans (by rw [one_mul])
  have hlineD : @Eq (HorizontalModel b₁ b₂ σ)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  let R : HorizontalModel b₁ b₂ σ → MatrixOrbit b₁ b₂ (permMatrix σ) :=
    fun w => cayleyFibreRetraction b₁ b₂ σ X w
  let DR : HorizontalModel b₁ b₂ σ →L[ℝ] HorizontalModel b₁ b₂ σ :=
    mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) R (0 : HorizontalModel b₁ b₂ σ)
  let velocity : (ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) → HorizontalModel b₁ b₂ σ :=
    fun c => mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) c 0 (1 : ℝ)
  have hchain : @Eq (HorizontalModel b₁ b₂ σ)
      (velocity (fun t : ℝ => R (t • v)))
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) :=
    mfderiv_comp_apply_of_eq (0 : ℝ) (hf 0)
      hd.differentiableAt.mdifferentiableAt (zero_smul ℝ v) (1 : ℝ)
  have hright : @Eq (HorizontalModel b₁ b₂ σ)
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) (DR v) :=
    congrArg (α := HorizontalModel b₁ b₂ σ) (β := HorizontalModel b₁ b₂ σ) (fun w => DR w) hlineD
  have hcurve : @Eq (HorizontalModel b₁ b₂ σ)
      (velocity (fun t : ℝ => R (t • v)))
      (velocity (cayleyTangentStep b₁ b₂ σ X v)) :=
    congrArg (β := HorizontalModel b₁ b₂ σ) velocity hline
  have hvelocity : @Eq (HorizontalModel b₁ b₂ σ)
      (velocity (cayleyTangentStep b₁ b₂ σ X v)) v :=
    cayleyTangentStep_mfderiv_one b₁ b₂ σ X v
  exact hright.symm.trans (hchain.symm.trans (hcurve.trans hvelocity))


/-- The derivative of the time-one retraction at the zero vector is the identity. -/
theorem cayleyFibreRetraction_mfderiv_zero
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    mfderiv (M := HorizontalModel b₁ b₂ σ) (M' := MatrixOrbit b₁ b₂ (permMatrix σ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (fun v : HorizontalModel b₁ b₂ σ => cayleyFibreRetraction b₁ b₂ σ X v) (0 : HorizontalModel b₁ b₂ σ) =
        ContinuousLinearMap.id ℝ (HorizontalModel b₁ b₂ σ) := by
  ext v
  exact cayleyFibreRetraction_mfderiv_zero_apply b₁ b₂ σ X v

end GS.OverlapGeometry
