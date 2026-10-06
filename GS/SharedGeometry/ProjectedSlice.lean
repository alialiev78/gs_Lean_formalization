module

public import GS.SharedGeometry.HorizontalModel
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

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Set Filter
open GS.OverlapGeometry (horizontalComplement horizontalRestriction
  horizontalLeftInverse_comp)
open scoped Topology
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)

def horizontalValue (h : HorizontalModel right left P) : Mat n :=
  orbitParam (1 : Factors right left) P h.val

def horizontalPoint (h : HorizontalModel right left P) :
    MatrixOrbit right left P :=
  orbitInverse P (1 : Factors right left) h.val

@[simp] theorem horizontalPoint_val (h : HorizontalModel right left P) :
    (horizontalPoint right left P h).val = horizontalValue right left P h :=
  orbitInverse_val P 1 h.val

theorem horizontalValue_smooth : ContDiff ℝ ⊤ (horizontalValue right left P) :=
  (orbitParam_smooth 1 P).comp
    (horizontalComplement (orbitDerivative right left P)).subtypeL.contDiff

@[simp] theorem horizontalValue_zero :
    horizontalValue right left P 0 = P := by
  simp [horizontalValue, orbitParam_zero, one_smul]

def horizontalProjected (h : HorizontalModel right left P) : HorizontalModel right left P :=
  orbitHorizontalInverse right left P (horizontalValue right left P h - P)

theorem horizontalProjected_smooth : ContDiff ℝ ⊤ (horizontalProjected right left P) :=
  (orbitHorizontalInverse right left P).contDiff.comp
    ((horizontalValue_smooth right left P).sub contDiff_const)

@[simp] theorem horizontalProjected_zero : horizontalProjected right left P 0 = 0 := by
  simp [horizontalProjected]

theorem horizontalValue_hasFDerivAt_zero :
    HasFDerivAt (horizontalValue right left P)
      (horizontalRestriction (orbitDerivative right left P)) 0 := by
  have hh := ((orbitParam_smooth (1 : Factors right left) P).differentiable
    (by simp) 0).hasFDerivAt
  unfold horizontalValue
  simpa only [Function.comp_def, horizontalValue, horizontalRestriction, orbitDerivative, map_zero] using
    HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val)
      (g := orbitParam (1 : Factors right left) P) 0 hh
      (horizontalComplement (orbitDerivative right left P)).subtypeL.hasFDerivAt

theorem horizontalProjected_hasFDerivAt_zero :
    HasFDerivAt (horizontalProjected right left P)
      (ContinuousLinearMap.id ℝ (HorizontalModel right left P)) 0 := by
  have hh := (orbitHorizontalInverse right left P).hasFDerivAt.comp 0
    ((horizontalValue_hasFDerivAt_zero right left P).sub_const P)
  unfold horizontalProjected
  simpa only [Function.comp_def, horizontalProjected, orbitHorizontalInverse, horizontalLeftInverse_comp] using hh

def projectedSliceEquiv : OpenPartialHomeomorph (HorizontalModel right left P)
    (HorizontalModel right left P) :=
  (horizontalProjected_smooth right left P).contDiffAt.toOpenPartialHomeomorph
    (horizontalProjected right left P)
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel right left P))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)

@[simp] theorem projectedSliceEquiv_apply (h : HorizontalModel right left P) :
    projectedSliceEquiv right left P h = horizontalProjected right left P h := rfl

theorem projectedSliceEquiv_zero_source : 0 ∈ (projectedSliceEquiv right left P).source :=
  (horizontalProjected_smooth right left P).contDiffAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel right left P))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)

theorem projectedSliceEquiv_zero_target : 0 ∈ (projectedSliceEquiv right left P).target := by
  simpa only [projectedSliceEquiv_apply, horizontalProjected_zero] using
    (projectedSliceEquiv right left P).map_source (projectedSliceEquiv_zero_source right left P)

theorem projectedSliceEquiv_inverse_smooth_zero :
    ContDiffAt ℝ ⊤ (projectedSliceEquiv right left P).symm 0 := by
  have hh := (horizontalProjected_smooth right left P).contDiffAt.to_localInverse
    (f' := ContinuousLinearEquiv.refl ℝ (HorizontalModel right left P))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)
  simpa only [horizontalProjected_zero, ContDiffAt.localInverse, HasStrictFDerivAt.localInverse, ContDiffAt.toOpenPartialHomeomorph, projectedSliceEquiv] using hh

/-- Concrete IFT data, without any assertion that its image is open in the orbit. -/
structure ProjectedSliceData where
  domain : Set (HorizontalModel right left P)
  coordinates : Mat n → HorizontalModel right left P
  open_domain : IsOpen domain
  zero_mem : 0 ∈ domain
  left_inverse : ∀ h ∈ domain, coordinates (horizontalValue right left P h) = h
  coordinates_smooth : ∀ h ∈ domain,
    ContDiffAt ℝ ⊤ coordinates (horizontalValue right left P h)

theorem exists_projectedSliceData : Nonempty (ProjectedSliceData right left P) := by
  let e := projectedSliceEquiv right left P
  have hs : ∀ᶠ y in 𝓝 (0 : HorizontalModel right left P), ContDiffAt ℝ ⊤ e.symm y :=
    (projectedSliceEquiv_inverse_smooth_zero right left P).eventually (by simp)
  obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds (projectedSliceEquiv_zero_target right left P)) hs)
  let V := e.source ∩ horizontalProjected right left P ⁻¹' W
  let c : Mat n → HorizontalModel right left P := fun A =>
    e.symm (orbitHorizontalInverse right left P (A - P))
  refine ⟨⟨V, c, e.open_source.inter
    (hWopen.preimage (horizontalProjected_smooth right left P).continuous),
    ⟨projectedSliceEquiv_zero_source right left P, ?_⟩, ?_, ?_⟩⟩
  · simpa only [Set.mem_preimage, horizontalProjected_zero] using hWzero
  · intro h hh
    exact e.left_inv hh.1
  · intro h hh
    have hi : ContDiffAt ℝ ⊤ e.symm (horizontalProjected right left P h) :=
      (hWsub hh.2).2
    exact hi.comp (horizontalValue right left P h)
      ((orbitHorizontalInverse right left P).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

def projectedSliceData : ProjectedSliceData right left P :=
  Classical.choice (exists_projectedSliceData right left P)

theorem horizontalPoint_injOn :
    Set.InjOn (horizontalPoint right left P) (projectedSliceData right left P).domain := by
  intro x hx y hy he
  have hv := congrArg (fun p => (projectedSliceData right left P).coordinates p.val) he
  simpa only [horizontalPoint_val, (projectedSliceData right left P).left_inverse x hx,
    (projectedSliceData right left P).left_inverse y hy] using hv

end GS.SharedGeometry
