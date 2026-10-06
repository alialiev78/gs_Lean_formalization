module

public import GS.OverlapGeometry.GeodesicConnection
public import GS.Continuation.ExponentialCurves

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Block exponential curves in the matrix orbit

The target is the original matrix-orbit subtype, with its inherited topology
and the arbitrary-overlap horizontal atlas. The curve, its actual first and
second derivatives, its genuine tangent velocity and its projected covariant
acceleration are related explicitly. Under no off-diagonal overlap the latter
vanishes for every time. No differential-equation or chart assumptions occur.

The connection operation is the previously established projected derivative
for the induced Frobenius metric. This module does not replace a library
geodesic predicate by a newly defined predicate.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.Geodesics

variable {n : ℕ}

/-- Analytic regularity is transferred through scalar entries, so no matrix
norm is silently identified with the Frobenius or operator norm. -/
theorem expLine_contDiff (C : Mat n) : ContDiff ℝ ⊤ (expLine C) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  letI : NormedAddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.linftyOpNormedSpace
  let ev : Mat n →L[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  have he : ContDiff ℝ ⊤ (NormedSpace.exp : Mat n → Mat n) :=
    contDiff_iff_contDiffAt.mpr (fun A => (NormedSpace.exp_analytic A).contDiffAt)
  have hl : ContDiff ℝ ⊤ (fun t : ℝ => t • C) := contDiff_id.smul contDiff_const
  simpa only [expLine, matrixExp_eq_exp, ev, Function.comp_def,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using
    ev.contDiff.comp (he.comp hl)

theorem gsExpCurve_contDiff (L P R C Ω : Mat n) :
    ContDiff ℝ ⊤ (gsExpCurve L P R C Ω) := by
  exact contDiff_matrix_mul
    (contDiff_matrix_mul (contDiff_matrix_mul contDiff_const (expLine_contDiff C))
      contDiff_const)
    (contDiff_matrix_mul (expLine_contDiff Ω) contDiff_const)

variable (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- Concrete supported orthogonal factors, defined for every real time. The
second group coordinate is transposed because the orbit action is L P R^T. -/
def blockExpFactors (g : FactorGroup b₁ b₂) (C : Model b₂) (Ω : Model b₁)
    (t : ℝ) : FactorGroup b₁ b₂ :=
  (⟨gsExpLeft g.1.val C.val t,
     gsExpLeft_supported _ _ g.1.property.1 C.property.1 t,
     gsExpLeft_orthogonal _ _ g.1.property.2 C.property.2 t⟩,
   ⟨(gsExpRight g.2.valᵀ Ω.val t)ᵀ,
     (gsExpRight_supported _ _ g.2.property.1.transpose Ω.property.1 t).transpose,
     (gsExpRight_orthogonal _ _ g.2.property.2.transpose Ω.property.2 t).transpose⟩)

/-- An actual curve in the original matrix orbit, not a quotient-only curve. -/
def blockExpCurve (g : FactorGroup b₁ b₂) (C : Model b₂) (Ω : Model b₁)
    (t : ℝ) : MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ) (blockExpFactors b₁ b₂ g C Ω t)

@[simp] theorem blockExpCurve_val (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    (blockExpCurve b₁ b₂ σ g C Ω t).val =
      gsExpCurve g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val t := by
  change gsExpLeft _ _ t * permMatrix σ * ((gsExpRight _ _ t)ᵀ)ᵀ = _
  simp only [Matrix.transpose_transpose, gsExpCurve, product2]

@[simp] theorem blockExpCurve_zero (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) :
    blockExpCurve b₁ b₂ σ g C Ω 0 = orbitMapToOrbit b₁ b₂ (permMatrix σ) g := by
  apply Subtype.ext
  simp only [blockExpCurve_val, gsExpCurve_zero]
  rfl

def blockExpVelocity (g : FactorGroup b₁ b₂) (C : Model b₂) (Ω : Model b₁)
    (t : ℝ) : Mat n :=
  gsExpVelocity g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val t

def blockExpAcceleration (g : FactorGroup b₁ b₂) (C : Model b₂) (Ω : Model b₁)
    (t : ℝ) : Mat n :=
  gsExpAcceleration g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val t

theorem blockExpCurve_contMDiff (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (blockExpCurve b₁ b₂ σ g C Ω) := by
  apply (overlap_contMDiff_iff_contDiff b₁ b₂ σ _).mpr
  simpa only [blockExpCurve_val] using
    gsExpCurve_contDiff g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val

theorem blockExpCurve_hasDerivAt (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    HasDerivAt (fun s => (blockExpCurve b₁ b₂ σ g C Ω s).val)
      (blockExpVelocity b₁ b₂ σ g C Ω t) t := by
  simpa only [blockExpCurve_val, blockExpVelocity] using
    gsExpCurve_hasDerivAt g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val
      (perm_orthogonal σ) t

theorem blockExpVelocity_hasDerivAt (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    HasDerivAt (blockExpVelocity b₁ b₂ σ g C Ω)
      (blockExpAcceleration b₁ b₂ σ g C Ω t) t :=
  gsExpVelocity_hasDerivAt _ _ _ _ _ (perm_orthogonal σ) t

/-- The explicit matrix velocity is the inclusion image of mathlib's actual
manifold derivative of this curve. This assertion does not need non-overlap. -/
theorem blockExpCurve_mfderiv_one (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    inclusionDifferential b₁ b₂ σ (blockExpCurve b₁ b₂ σ g C Ω t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (blockExpCurve b₁ b₂ σ g C Ω) t (1 : ℝ)) =
      blockExpVelocity b₁ b₂ σ g C Ω t := by
  have hc := (blockExpCurve_contMDiff b₁ b₂ σ g C Ω).mdifferentiable (by simp)
  have hi := (overlap_val_contMDiff b₁ b₂ σ).mdifferentiable (by simp)
  have hh := mfderiv_comp_apply t (hi (blockExpCurve b₁ b₂ σ g C Ω t)) (hc t) (1 : ℝ)
  have hd : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Mat n))
      (fun s => (blockExpCurve b₁ b₂ σ g C Ω s).val) t (1 : ℝ) =
      blockExpVelocity b₁ b₂ σ g C Ω t := by
    rw [mfderiv_eq_fderiv]
    exact (blockExpCurve_hasDerivAt b₁ b₂ σ g C Ω t).deriv
  exact hh.symm.trans hd

theorem blockExpVelocity_tangent (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    tangentProjection b₁ b₂ σ (blockExpCurve b₁ b₂ σ g C Ω t)
      (blockExpVelocity b₁ b₂ σ g C Ω t) =
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (blockExpCurve b₁ b₂ σ g C Ω) t (1 : ℝ) := by
  rw [← blockExpCurve_mfderiv_one b₁ b₂ σ g C Ω t,
    tangentProjection_of_tangent]

/-- The actual second derivative has zero orthogonal projection to the actual
orbit tangent space at the current point, for all real times. -/
theorem blockExpAcceleration_projected_zero
    (hno : NoOffDiagonalOverlap b₁ b₂ σ) (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    pointProjection b₁ b₂ (blockExpCurve b₁ b₂ σ g C Ω t).val
      (blockExpAcceleration b₁ b₂ σ g C Ω t) = 0 := by
  rw [blockExpCurve_val]
  exact gsExpCurve_projected_acceleration_zero b₁ b₂ σ _ _ _ _
    (noOverlap_offDiagonalDisjoint σ hno)
    g.1.property.1 g.2.property.1.transpose g.1.property.2 g.2.property.2.transpose
    C.property.1 Ω.property.1 C.property.2 Ω.property.2 t

/-- Vanishing covariant velocity in the genuine tangent fibre, for the
established induced-Frobenius projected connection operation. -/
theorem blockExpCurve_covariantVelocity_zero
    (hno : NoOffDiagonalOverlap b₁ b₂ σ) (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    covariantAlong b₁ b₂ σ (blockExpCurve b₁ b₂ σ g C Ω)
      (blockExpVelocity b₁ b₂ σ g C Ω) t = 0 := by
  apply inclusionDifferential_injective b₁ b₂ σ (blockExpCurve b₁ b₂ σ g C Ω t)
  rw [inclusion_covariantAlong,
    (blockExpVelocity_hasDerivAt b₁ b₂ σ g C Ω t).deriv,
    blockExpAcceleration_projected_zero b₁ b₂ σ hno, map_zero]

theorem blockExpCurve_constant_speed
    (hno : NoOffDiagonalOverlap b₁ b₂ σ) (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    frobSq (blockExpVelocity b₁ b₂ σ g C Ω t) = frobSq C.val + frobSq Ω.val :=
  gsExpCurve_constant_speed b₁ b₂ σ _ _ _ _
    (noOverlap_offDiagonalDisjoint σ hno) g.1.property.2 g.2.property.2.transpose
    C.property.1 Ω.property.1 C.property.2 Ω.property.2 t

/-- Every initial vector in the actual tangent space is realized. The factors
are the established preferred factors of the given matrix point, and the
generators have precisely the prescribed block supports. -/
theorem exists_blockExpCurve_of_tangent
    (hno : NoOffDiagonalOverlap b₁ b₂ σ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    ∃ (C : Model b₂) (Ω : Model b₁),
      blockExpCurve b₁ b₂ σ (preferredFactor σ X) C Ω 0 = X ∧
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (blockExpCurve b₁ b₂ σ (preferredFactor σ X) C Ω) 0 (1 : ℝ) = v ∧
      ∀ t : ℝ,
        covariantAlong b₁ b₂ σ (blockExpCurve b₁ b₂ σ (preferredFactor σ X) C Ω)
          (blockExpVelocity b₁ b₂ σ (preferredFactor σ X) C Ω) t = 0 := by
  have hv := (orbit_tangent_image_iff b₁ b₂ σ X
    (inclusionDifferential b₁ b₂ σ X v)).mp ⟨v, rfl⟩
  obtain ⟨C, Ω, hsC, hC, hsΩ, hΩ, hgen⟩ := hv
  let c : Model b₂ := ⟨C, hsC, hC⟩
  let w : Model b₁ := ⟨Ω, hsΩ, hΩ⟩
  have hbase : blockExpCurve b₁ b₂ σ (preferredFactor σ X) c w 0 = X := by
    rw [blockExpCurve_zero]
    exact preferredFactor_spec σ X
  refine ⟨c, w, hbase, ?_, ?_⟩
  · apply inclusionDifferential_injective b₁ b₂ σ X
    have hd := blockExpCurve_mfderiv_one b₁ b₂ σ (preferredFactor σ X) c w 0
    rw [hbase] at hd
    refine hd.trans ?_
    change gsExpVelocity _ _ _ C Ω 0 = _
    rw [gsExpVelocity_zero _ _ _ _ _ (perm_orthogonal σ)]
    exact hgen.symm
  · intro t
    exact blockExpCurve_covariantVelocity_zero b₁ b₂ σ hno (preferredFactor σ X) c w t

end GS.Geodesics
