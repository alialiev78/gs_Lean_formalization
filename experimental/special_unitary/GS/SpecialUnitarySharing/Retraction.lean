module

public import GS.SpecialUnitarySharing.IntrinsicSmooth
public import GS.SpecialUnitarySharing.Gradient
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A canonical exponential retraction on each actual shared tangent fibre

The map uses only the base matrix and the matrix image of the actual tangent
vector. It is feasible for all real times. The initial matrix derivative is
identified with the manifold derivative using injectivity of the inclusion,
and the fibre differential of the time-one map is the identity.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Filter
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
open GS.SpecialUnitarySharing.Orbit
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Orbit membership is proof data; the value does not inspect a factorization. -/
def expTangentStep (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) (t : ℝ) :
    MatrixOrbit right left P :=
  ⟨expStep right left X.val (inclusionDifferential right left P X v) t,
    expStep_mem_orbit right left P X (inclusionDifferential right left P X v) t⟩

@[simp] theorem expTangentStep_val (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) (t : ℝ) :
    (expTangentStep right left P X v t).val =
      expStep right left X.val (inclusionDifferential right left P X v) t := rfl

@[simp] theorem expTangentStep_at_zero (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    expTangentStep right left P X v 0 = X := by
  apply Subtype.ext
  simp

@[simp] theorem expTangentStep_zero_vector (X : MatrixOrbit right left P) (t : ℝ) :
    expTangentStep right left P X 0 t = X := by
  apply Subtype.ext
  simp

/-- The genuine matrix derivative, for every actual tangent vector. -/
theorem expTangentStep_derivative (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    HasDerivAt (fun t => (expTangentStep right left P X v t).val)
      (inclusionDifferential right left P X v) 0 := by
  have hd := expStep_hasDerivAt_zero right left X.val (inclusionDifferential right left P X v)
  have hfix : pointProjection right left X.val (inclusionDifferential right left P X v) =
      inclusionDifferential right left P X v :=
    (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩
  simpa only [expTangentStep_val, hfix] using hd

/-- Fixed-base smoothness jointly in the true tangent coordinate and time. -/
theorem expTangentStep_joint_contMDiff (X : MatrixOrbit right left P) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P × ℝ))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun p : HorizontalModel right left P × ℝ => expTangentStep right left P X p.1 p.2) := by
  let D := inclusionDifferential right left P X
  have hd : ContDiff ℝ ⊤ (fun p : HorizontalModel right left P × ℝ => D p.1) :=
    D.contDiff.comp contDiff_fst
  have hp : ContDiff ℝ ⊤ (fun p : HorizontalModel right left P × ℝ =>
      expStep right left X.val (D p.1) p.2) :=
    (expStep_fixed_smooth right left X.val).comp (hd.prodMk contDiff_snd)
  apply (sharedOrbit_contMDiff_iff_contDiff right left P _).mpr
  simpa only [expTangentStep_val] using hp

/-- Scaling the tangent vector is equivalent to scaling time. -/
theorem expTangentStep_smul
    (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) (a t : ℝ) :
    expTangentStep right left P X (a • v) t = expTangentStep right left P X v (t * a) := by
  apply Subtype.ext
  simp only [expTangentStep_val, map_smul]
  exact expStep_scaled right left X.val (inclusionDifferential right left P X v) a t

/-- The time-one exponential retraction on the actual tangent fibre. -/
def expFibreRetraction (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    MatrixOrbit right left P :=
  expTangentStep right left P X v 1

@[simp] theorem expFibreRetraction_val (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    (expFibreRetraction right left P X v).val =
      expStep right left X.val (inclusionDifferential right left P X v) 1 :=
  expTangentStep_val right left P X v 1

@[simp] theorem expFibreRetraction_zero (X : MatrixOrbit right left P) :
    expFibreRetraction right left P X 0 = X :=
  expTangentStep_zero_vector right left P X 1

theorem expFibreRetraction_contMDiff (X : MatrixOrbit right left P) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun v : HorizontalModel right left P => expFibreRetraction right left P X v) := by
  have hi : ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, HorizontalModel right left P × ℝ)) ⊤ (fun v : HorizontalModel right left P => (v, (1 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel right left P × ℝ => expTangentStep right left P X p.1 p.2)
    (f := fun v : HorizontalModel right left P => (v, (1 : ℝ)))
    (expTangentStep_joint_contMDiff right left P X) hi

/-- Smoothness of the feasible curve in the actual orbit atlas. -/
theorem expTangentStep_contMDiff
    (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (expTangentStep right left P X v) := by
  have hi : ContMDiff (𝓘(ℝ, ℝ))
      (𝓘(ℝ, HorizontalModel right left P × ℝ)) ⊤ (fun t : ℝ => (Prod.mk (α := HorizontalModel right left P) (β := ℝ) v t)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel right left P × ℝ => expTangentStep right left P X p.1 p.2)
    (f := fun t : ℝ => (Prod.mk (α := HorizontalModel right left P) (β := ℝ) v t))
    (expTangentStep_joint_contMDiff right left P X) hi

/-- The derivative is in mathlib's original tangent space, not only its matrix image. -/
theorem expTangentStep_mfderiv_one
    (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
      (expTangentStep right left P X v) 0 (1 : ℝ) = v := by
  apply inclusionDifferential_injective right left P X
  have hc := (expTangentStep_contMDiff right left P X v).mdifferentiable (by simp)
  have hi := (sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) (hc 0)
    (expTangentStep_at_zero right left P X v) (1 : ℝ)
  have hmatrix : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, CMat n))
      (fun t => (expTangentStep right left P X v t).val) 0 (1 : ℝ) =
        inclusionDifferential right left P X v := by
    rw [mfderiv_eq_fderiv]
    exact (expTangentStep_derivative right left P X v).deriv
  exact hchain.symm.trans hmatrix

/-- Directional form of the retraction derivative at the zero vector. -/
theorem expFibreRetraction_mfderiv_zero_apply
    (X : MatrixOrbit right left P) (v : HorizontalModel right left P) :
    @Eq (HorizontalModel right left P)
      (mfderiv (M := HorizontalModel right left P) (M' := MatrixOrbit right left P)
        (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
        (fun w : HorizontalModel right left P => expFibreRetraction right left P X w)
        (0 : HorizontalModel right left P) v) v := by
  have hd : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf := (expFibreRetraction_contMDiff right left P X).mdifferentiable (by simp)
  have hline : (fun t : ℝ => expFibreRetraction right left P X (t • v)) =
      expTangentStep right left P X v := by
    funext t
    exact (expTangentStep_smul right left P X v t 1).trans (by rw [one_mul])
  have hlineD : @Eq (HorizontalModel right left P)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
        (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  let R : HorizontalModel right left P → MatrixOrbit right left P :=
    fun w => expFibreRetraction right left P X w
  let DR : HorizontalModel right left P →L[ℝ] HorizontalModel right left P :=
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)) R (0 : HorizontalModel right left P)
  let velocity : (ℝ → MatrixOrbit right left P) → HorizontalModel right left P :=
    fun c => mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P)) c 0 (1 : ℝ)
  have hchain : @Eq (HorizontalModel right left P)
      (velocity (fun t : ℝ => R (t • v)))
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) :=
    mfderiv_comp_apply_of_eq (0 : ℝ) (hf 0)
      hd.differentiableAt.mdifferentiableAt (zero_smul ℝ v) (1 : ℝ)
  have hright : @Eq (HorizontalModel right left P)
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) (DR v) :=
    congrArg (α := HorizontalModel right left P) (β := HorizontalModel right left P) (fun w => DR w) hlineD
  have hcurve : @Eq (HorizontalModel right left P)
      (velocity (fun t : ℝ => R (t • v)))
      (velocity (expTangentStep right left P X v)) :=
    congrArg (β := HorizontalModel right left P) velocity hline
  have hvelocity : @Eq (HorizontalModel right left P)
      (velocity (expTangentStep right left P X v)) v :=
    expTangentStep_mfderiv_one right left P X v
  exact hright.symm.trans (hchain.symm.trans (hcurve.trans hvelocity))


/-- The derivative of the time-one retraction at the zero vector is the identity. -/
theorem expFibreRetraction_mfderiv_zero
    (X : MatrixOrbit right left P) :
    mfderiv (M := HorizontalModel right left P) (M' := MatrixOrbit right left P)
      (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => expFibreRetraction right left P X v) (0 : HorizontalModel right left P) =
        ContinuousLinearMap.id ℝ (HorizontalModel right left P) := by
  ext v
  exact expFibreRetraction_mfderiv_zero_apply right left P X v

end GS.SpecialUnitarySharing
