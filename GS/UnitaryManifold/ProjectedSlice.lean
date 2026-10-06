module

public import GS.UnitaryManifold.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Ambient coordinates on a horizontal slice

The inverse function theorem supplies an ambient smooth left inverse to the
horizontal orbit parametrization near zero. Openness of the slice image in the
whole orbit is established separately by local factor decomposition.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryGeometry GS.OverlapGeometry Set Filter
open scoped Topology
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))

def horizontalValue (h : HorizontalModel b₁ b₂ σ) : CMat n :=
  orbitParam (1 : FactorGroup b₁ b₂) (cPermMatrix σ) h.val

def horizontalPoint (h : HorizontalModel b₁ b₂ σ) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  orbitInverse σ (1 : FactorGroup b₁ b₂) h.val

@[simp] theorem horizontalPoint_val (h : HorizontalModel b₁ b₂ σ) :
    (horizontalPoint b₁ b₂ σ h).val = horizontalValue b₁ b₂ σ h :=
  orbitInverse_val σ 1 h.val

theorem horizontalValue_smooth : ContDiff ℝ ⊤ (horizontalValue b₁ b₂ σ) :=
  (orbitParam_smooth 1 (cPermMatrix σ)).comp
    (horizontalComplement (orbitDerivative b₁ b₂ σ)).subtypeL.contDiff

@[simp] theorem horizontalValue_zero :
    horizontalValue b₁ b₂ σ 0 = cPermMatrix σ := by
  simp [horizontalValue, orbitParam, chartInv_zero]

def horizontalProjected (h : HorizontalModel b₁ b₂ σ) : HorizontalModel b₁ b₂ σ :=
  orbitHorizontalInverse b₁ b₂ σ (horizontalValue b₁ b₂ σ h - cPermMatrix σ)

theorem horizontalProjected_smooth : ContDiff ℝ ⊤ (horizontalProjected b₁ b₂ σ) :=
  (orbitHorizontalInverse b₁ b₂ σ).contDiff.comp
    ((horizontalValue_smooth b₁ b₂ σ).sub contDiff_const)

@[simp] theorem horizontalProjected_zero : horizontalProjected b₁ b₂ σ 0 = 0 := by
  simp [horizontalProjected]

theorem horizontalValue_hasFDerivAt_zero :
    HasFDerivAt (horizontalValue b₁ b₂ σ)
      (horizontalRestriction (orbitDerivative b₁ b₂ σ)) 0 := by
  have hh := ((orbitParam_smooth (1 : FactorGroup b₁ b₂) (cPermMatrix σ)).differentiable
    (by simp) 0).hasFDerivAt
  unfold horizontalValue
  simpa only [Function.comp_def, horizontalValue, horizontalRestriction, orbitDerivative, map_zero] using
    HasFDerivAt.comp (f := fun h : HorizontalModel b₁ b₂ σ => h.val)
      (g := orbitParam (1 : FactorGroup b₁ b₂) (cPermMatrix σ)) 0 hh
      (horizontalComplement (orbitDerivative b₁ b₂ σ)).subtypeL.hasFDerivAt

theorem horizontalProjected_hasFDerivAt_zero :
    HasFDerivAt (horizontalProjected b₁ b₂ σ)
      (ContinuousLinearMap.id ℝ (HorizontalModel b₁ b₂ σ)) 0 := by
  have hh := (orbitHorizontalInverse b₁ b₂ σ).hasFDerivAt.comp 0
    ((horizontalValue_hasFDerivAt_zero b₁ b₂ σ).sub_const (cPermMatrix σ))
  unfold horizontalProjected
  simpa only [Function.comp_def, horizontalProjected, orbitHorizontalInverse, horizontalLeftInverse_comp] using hh

def projectedSliceEquiv : OpenPartialHomeomorph (HorizontalModel b₁ b₂ σ)
    (HorizontalModel b₁ b₂ σ) :=
  (horizontalProjected_smooth b₁ b₂ σ).contDiffAt.toOpenPartialHomeomorph
    (horizontalProjected b₁ b₂ σ)
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel b₁ b₂ σ))
    (horizontalProjected_hasFDerivAt_zero b₁ b₂ σ) (by simp)

@[simp] theorem projectedSliceEquiv_apply (h : HorizontalModel b₁ b₂ σ) :
    projectedSliceEquiv b₁ b₂ σ h = horizontalProjected b₁ b₂ σ h := rfl

theorem projectedSliceEquiv_zero_source : 0 ∈ (projectedSliceEquiv b₁ b₂ σ).source :=
  (horizontalProjected_smooth b₁ b₂ σ).contDiffAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel b₁ b₂ σ))
    (horizontalProjected_hasFDerivAt_zero b₁ b₂ σ) (by simp)

theorem projectedSliceEquiv_zero_target : 0 ∈ (projectedSliceEquiv b₁ b₂ σ).target := by
  simpa only [projectedSliceEquiv_apply, horizontalProjected_zero] using
    (projectedSliceEquiv b₁ b₂ σ).map_source (projectedSliceEquiv_zero_source b₁ b₂ σ)

theorem projectedSliceEquiv_inverse_smooth_zero :
    ContDiffAt ℝ ⊤ (projectedSliceEquiv b₁ b₂ σ).symm 0 := by
  have hh := (horizontalProjected_smooth b₁ b₂ σ).contDiffAt.to_localInverse
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel b₁ b₂ σ))
    (horizontalProjected_hasFDerivAt_zero b₁ b₂ σ) (by simp)
  simpa only [horizontalProjected_zero, ContDiffAt.localInverse, HasStrictFDerivAt.localInverse, ContDiffAt.toOpenPartialHomeomorph, projectedSliceEquiv] using hh

/-- Concrete IFT data, without any assertion that its image is open in the orbit. -/
structure ProjectedSliceData where
  domain : Set (HorizontalModel b₁ b₂ σ)
  coordinates : CMat n → HorizontalModel b₁ b₂ σ
  open_domain : IsOpen domain
  zero_mem : 0 ∈ domain
  left_inverse : ∀ h ∈ domain, coordinates (horizontalValue b₁ b₂ σ h) = h
  coordinates_smooth : ∀ h ∈ domain,
    ContDiffAt ℝ ⊤ coordinates (horizontalValue b₁ b₂ σ h)

theorem exists_projectedSliceData : Nonempty (ProjectedSliceData b₁ b₂ σ) := by
  let e := projectedSliceEquiv b₁ b₂ σ
  have hs : ∀ᶠ y in 𝓝 (0 : HorizontalModel b₁ b₂ σ), ContDiffAt ℝ ⊤ e.symm y :=
    (projectedSliceEquiv_inverse_smooth_zero b₁ b₂ σ).eventually (by simp)
  obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds (projectedSliceEquiv_zero_target b₁ b₂ σ)) hs)
  let V := e.source ∩ horizontalProjected b₁ b₂ σ ⁻¹' W
  let c : CMat n → HorizontalModel b₁ b₂ σ := fun A =>
    e.symm (orbitHorizontalInverse b₁ b₂ σ (A - cPermMatrix σ))
  refine ⟨⟨V, c, e.open_source.inter
    (hWopen.preimage (horizontalProjected_smooth b₁ b₂ σ).continuous),
    ⟨projectedSliceEquiv_zero_source b₁ b₂ σ, ?_⟩, ?_, ?_⟩⟩
  · simpa only [Set.mem_preimage, horizontalProjected_zero] using hWzero
  · intro h hh
    exact e.left_inv hh.1
  · intro h hh
    have hi : ContDiffAt ℝ ⊤ e.symm (horizontalProjected b₁ b₂ σ h) :=
      (hWsub hh.2).2
    exact hi.comp (horizontalValue b₁ b₂ σ h)
      ((orbitHorizontalInverse b₁ b₂ σ).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

def projectedSliceData : ProjectedSliceData b₁ b₂ σ :=
  Classical.choice (exists_projectedSliceData b₁ b₂ σ)

theorem horizontalPoint_injOn :
    Set.InjOn (horizontalPoint b₁ b₂ σ) (projectedSliceData b₁ b₂ σ).domain := by
  intro x hx y hy he
  have hv := congrArg (fun p => (projectedSliceData b₁ b₂ σ).coordinates p.val) he
  simpa only [horizontalPoint_val, (projectedSliceData b₁ b₂ σ).left_inverse x hx,
    (projectedSliceData b₁ b₂ σ).left_inverse y hy] using hv

end GS.UnitaryManifold
