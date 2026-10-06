module

public import GS.UnitaryManifold.PointCayley
public import GS.UnitaryManifold.Gradient
public import GS.OverlapGeometry.ManifoldSmoothMaps
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
The final construction is smooth on mathlib's whole tangent bundle.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry Filter
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance canonicalRetractionHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance canonicalRetractionHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance canonicalRetractionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance canonicalRetractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The matrix value contains no preferred-factor choice. The orbit witness
is a proposition and cannot affect the output of this subtype-valued function. -/
def canonicalCayleyStep (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  ⟨pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) t,
    pointCayleyStep_mem_orbit b₁ b₂ (cPermMatrix σ) X.val
      (inclusionDifferential b₁ b₂ σ X v) X.property t⟩

@[simp] theorem canonicalCayleyStep_val (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    (canonicalCayleyStep b₁ b₂ σ X v t).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) t := rfl

@[simp] theorem canonicalCayleyStep_at_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) : canonicalCayleyStep b₁ b₂ σ X v 0=X := by
  apply Subtype.ext
  simp

@[simp] theorem canonicalCayleyStep_zero_vector (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (t : ℝ) : canonicalCayleyStep b₁ b₂ σ X 0 t=X := by
  apply Subtype.ext
  simp

theorem canonicalCayleyStep_derivative (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) :
    HasDerivAt (fun t => (canonicalCayleyStep b₁ b₂ σ X v t).val)
      (inclusionDifferential b₁ b₂ σ X v) 0 := by
  have hZ : inclusionDifferential b₁ b₂ σ X v ∈ pointTangentSpace b₁ b₂ X.val := by
    apply (pointProjection_fixed_iff b₁ b₂ X.val _).mp
    exact (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mpr ⟨v, rfl⟩
  rw [← preferredFactor_product b₁ b₂ σ X] at hZ
  have hd := pointCayleyStep_tangent_derivative b₁ b₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᴴ
    (inclusionDifferential b₁ b₂ σ X v)
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.conjTranspose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.conjTranspose hZ
  have hp : (preferredFactor σ X).1.val * cPermMatrix σ * (preferredFactor σ X).2.valᴴ = X.val :=
    preferredFactor_product b₁ b₂ σ X
  rw [hp] at hd
  exact hd

set_option maxHeartbeats 800000 in
/-- Fixed-base smoothness jointly in the actual tangent coordinate and time. -/
theorem canonicalCayleyStep_joint_contMDiff
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ × ℝ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (fun p : HorizontalModel b₁ b₂ σ × ℝ => canonicalCayleyStep b₁ b₂ σ X p.1 p.2) := by
  let D : HorizontalModel b₁ b₂ σ →L[ℝ] CMat n := inclusionDifferential b₁ b₂ σ X
  have hd : ContDiff ℝ ⊤ (fun p : HorizontalModel b₁ b₂ σ × ℝ => D p.1) :=
    ContDiff.comp (f := fun p : HorizontalModel b₁ b₂ σ × ℝ => p.1)
      (g := fun v : HorizontalModel b₁ b₂ σ => D v) D.contDiff contDiff_fst
  have hp : ContDiff ℝ ⊤ (fun p : HorizontalModel b₁ b₂ σ × ℝ =>
      pointCayleyStep b₁ b₂ X.val (D p.1) p.2) :=
    ContDiff.comp
      (f := fun p : HorizontalModel b₁ b₂ σ × ℝ => ((X.val, D p.1), p.2))
      (g := fun p : (CMat n × CMat n) × ℝ => pointCayleyStep b₁ b₂ p.1.1 p.1.2 p.2)
      (pointCayleyStep_smooth b₁ b₂) ((contDiff_const.prodMk hd).prodMk contDiff_snd)
  apply (overlap_contMDiff_iff_contDiff b₁ b₂ σ _).mpr
  convert hp using 1 <;> rfl

/-- Scaling the tangent vector is equivalent to scaling time. -/
theorem canonicalCayleyStep_smul
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (a t : ℝ) :
    canonicalCayleyStep b₁ b₂ σ X (a • v) t = canonicalCayleyStep b₁ b₂ σ X v (t * a) := by
  apply Subtype.ext
  simp only [canonicalCayleyStep_val, map_smul, pointCayleyStep,
    balancedLeft_smul, balancedRight_smul, smul_smul]

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def canonicalFibreRetraction (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  canonicalCayleyStep b₁ b₂ σ X v 1

@[simp] theorem canonicalFibreRetraction_val (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    (canonicalFibreRetraction b₁ b₂ σ X v).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) 1 :=
  canonicalCayleyStep_val b₁ b₂ σ X v 1

@[simp] theorem canonicalFibreRetraction_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    canonicalFibreRetraction b₁ b₂ σ X 0 = X :=
  canonicalCayleyStep_zero_vector b₁ b₂ σ X 1

theorem canonicalFibreRetraction_contMDiff (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (fun v : HorizontalModel b₁ b₂ σ => canonicalFibreRetraction b₁ b₂ σ X v) := by
  have hi : ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ × ℝ)) ⊤ (fun v : HorizontalModel b₁ b₂ σ => (v, (1 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel b₁ b₂ σ × ℝ => canonicalCayleyStep b₁ b₂ σ X p.1 p.2)
    (f := fun v : HorizontalModel b₁ b₂ σ => (v, (1 : ℝ)))
    (canonicalCayleyStep_joint_contMDiff b₁ b₂ σ X) hi

/-- Smoothness of the feasible curve in the actual orbit atlas. -/
theorem canonicalCayleyStep_contMDiff
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (canonicalCayleyStep b₁ b₂ σ X v) := by
  have hi : ContMDiff (𝓘(ℝ, ℝ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ × ℝ)) ⊤ (fun t : ℝ => (Prod.mk (α := HorizontalModel b₁ b₂ σ) (β := ℝ) v t)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel b₁ b₂ σ × ℝ => canonicalCayleyStep b₁ b₂ σ X p.1 p.2)
    (f := fun t : ℝ => (Prod.mk (α := HorizontalModel b₁ b₂ σ) (β := ℝ) v t))
    (canonicalCayleyStep_joint_contMDiff b₁ b₂ σ X) hi

/-- The derivative is in mathlib's original tangent space, not only its matrix image. -/
theorem canonicalCayleyStep_mfderiv_one
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (canonicalCayleyStep b₁ b₂ σ X v) 0 (1 : ℝ) = v := by
  apply inclusionDifferential_injective b₁ b₂ σ X
  have hc := (canonicalCayleyStep_contMDiff b₁ b₂ σ X v).mdifferentiable (by simp)
  have hi := (overlap_val_contMDiff b₁ b₂ σ).mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) (hc 0)
    (canonicalCayleyStep_at_zero b₁ b₂ σ X v) (1 : ℝ)
  have hmatrix : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, CMat n))
      (fun t => (canonicalCayleyStep b₁ b₂ σ X v t).val) 0 (1 : ℝ) =
        inclusionDifferential b₁ b₂ σ X v := by
    rw [mfderiv_eq_fderiv]
    exact (canonicalCayleyStep_derivative b₁ b₂ σ X v).deriv
  exact hchain.symm.trans hmatrix

/-- Directional form of the retraction derivative at the zero vector. -/
theorem canonicalFibreRetraction_mfderiv_zero_apply
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (v : HorizontalModel b₁ b₂ σ) :
    @Eq (HorizontalModel b₁ b₂ σ)
      (mfderiv (M := HorizontalModel b₁ b₂ σ) (M' := MatrixOrbit b₁ b₂ (cPermMatrix σ))
        (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun w : HorizontalModel b₁ b₂ σ => canonicalFibreRetraction b₁ b₂ σ X w)
        (0 : HorizontalModel b₁ b₂ σ) v) v := by
  have hd : HasDerivAt (fun t : ℝ => t • (v : HorizontalModel b₁ b₂ σ))
      (v : HorizontalModel b₁ b₂ σ) 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (F := HorizontalModel b₁ b₂ σ) v
  have hf := (canonicalFibreRetraction_contMDiff b₁ b₂ σ X).mdifferentiable (by simp)
  have hline : (fun t : ℝ => canonicalFibreRetraction b₁ b₂ σ X (t • v)) =
      canonicalCayleyStep b₁ b₂ σ X v := by
    funext t
    exact (canonicalCayleyStep_smul b₁ b₂ σ X v t 1).trans (by rw [one_mul])
  have hlineD : @Eq (HorizontalModel b₁ b₂ σ)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  let R : HorizontalModel b₁ b₂ σ → MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
    fun w => canonicalFibreRetraction b₁ b₂ σ X w
  let DR : HorizontalModel b₁ b₂ σ →L[ℝ] HorizontalModel b₁ b₂ σ :=
    mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) R (0 : HorizontalModel b₁ b₂ σ)
  let velocity : (ℝ → MatrixOrbit b₁ b₂ (cPermMatrix σ)) → HorizontalModel b₁ b₂ σ :=
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
      (velocity (canonicalCayleyStep b₁ b₂ σ X v)) :=
    congrArg (β := HorizontalModel b₁ b₂ σ) velocity hline
  have hvelocity : @Eq (HorizontalModel b₁ b₂ σ)
      (velocity (canonicalCayleyStep b₁ b₂ σ X v)) v :=
    canonicalCayleyStep_mfderiv_one b₁ b₂ σ X v
  exact hright.symm.trans (hchain.symm.trans (hcurve.trans hvelocity))


/-- The derivative of the time-one retraction at the zero vector is the identity. -/
theorem canonicalFibreRetraction_mfderiv_zero
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    mfderiv (M := HorizontalModel b₁ b₂ σ) (M' := MatrixOrbit b₁ b₂ (cPermMatrix σ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (fun v : HorizontalModel b₁ b₂ σ => canonicalFibreRetraction b₁ b₂ σ X v) (0 : HorizontalModel b₁ b₂ σ) =
        ContinuousLinearMap.id ℝ (HorizontalModel b₁ b₂ σ) := by
  ext v
  exact canonicalFibreRetraction_mfderiv_zero_apply b₁ b₂ σ X v

/-- The domain is mathlib's actual tangent bundle, with its standard topology
and smooth structure, not a product chosen separately for each base point. -/
def cayleyRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (cPermMatrix σ))) : MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  canonicalFibreRetraction b₁ b₂ σ p.proj p.2

@[simp] theorem cayleyRetraction_val
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (cPermMatrix σ))) :
    (cayleyRetraction b₁ b₂ σ p).val =
      pointCayleyStep b₁ b₂ p.proj.val
        (tangentAmbient b₁ b₂ σ p) 1 :=
  canonicalFibreRetraction_val b₁ b₂ σ p.proj p.2

set_option maxHeartbeats 800000 in
theorem cayleyRetraction_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤ (cayleyRetraction b₁ b₂ σ) := by
  have hp : ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent
      (𝓘(ℝ, CMat n)) ⊤
      (fun p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (MatrixOrbit b₁ b₂ (cPermMatrix σ)) => p.proj.val) :=
    (overlap_val_contMDiff b₁ b₂ σ).comp
      (Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ))))
  have hargs : ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent
      (𝓘(ℝ, (CMat n × CMat n) × ℝ)) ⊤
      (fun p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (MatrixOrbit b₁ b₂ (cPermMatrix σ)) =>
          ((p.proj.val, tangentAmbient b₁ b₂ σ p), (1 : ℝ))) :=
    (hp.prodMk_space (tangentAmbient_contMDiff b₁ b₂ σ)).prodMk_space contMDiff_const
  have ha : ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent (𝓘(ℝ, CMat n)) ⊤
      (fun p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (MatrixOrbit b₁ b₂ (cPermMatrix σ)) =>
          pointCayleyStep b₁ b₂ p.proj.val
            (tangentAmbient b₁ b₂ σ p) 1) :=
    (pointCayleyStep_smooth b₁ b₂).comp_contMDiff
      (f := fun p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (MatrixOrbit b₁ b₂ (cPermMatrix σ)) =>
          ((p.proj.val, tangentAmbient b₁ b₂ σ p), (1 : ℝ))) hargs
  have hav : ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent (𝓘(ℝ, CMat n)) ⊤
      (fun p => (cayleyRetraction b₁ b₂ σ p).val) := by
    simpa only [cayleyRetraction_val] using ha
  exact slice_contMDiff_of_ambient (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent
    (cayleyRetraction b₁ b₂ σ) hav

@[simp] theorem cayleyRetraction_zero_section
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    cayleyRetraction b₁ b₂ σ ⟨X, 0⟩ = X :=
  canonicalFibreRetraction_zero b₁ b₂ σ X

/-- The fibre differential is the actual manifold differential at zero. -/
theorem cayleyRetraction_fibre_mfderiv_zero
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (fun v : HorizontalModel b₁ b₂ σ => cayleyRetraction b₁ b₂ σ ⟨X, v⟩)
      (0 : HorizontalModel b₁ b₂ σ) =
        ContinuousLinearMap.id ℝ (HorizontalModel b₁ b₂ σ) :=
  canonicalFibreRetraction_mfderiv_zero b₁ b₂ σ X


end GS.UnitaryManifold
