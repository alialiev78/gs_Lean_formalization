module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# An atlas from ambient smooth slices

This file constructs manifold charts on the inherited topology of a subset of
a real normed space. The input consists of concrete ambient coordinate maps and
parametrizations, with their local inverse identities and open domains. No
manifold or quotient topology on the subset is assumed.

The application to a matrix orbit must independently construct the slice data,
including the relative openness of each slice image.
-/

noncomputable section
open Set Filter
open scoped Topology Manifold

namespace GS.OverlapGeometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth slice of an actual subset, with ambient coordinates and an
explicit parametrization. The source is relatively open in the subset's
original topology. -/
structure SmoothSlice (S : Set F) where
  source : Set S
  target : Set E
  coordinates : F → E
  parametrization : E → S
  open_source : IsOpen source
  open_target : IsOpen target
  coordinates_smooth : ∀ y ∈ source, ContDiffAt ℝ ⊤ coordinates y.val
  parametrization_smooth : ContDiff ℝ ⊤ (fun x => (parametrization x).val)
  maps_source : ∀ y ∈ source, coordinates y.val ∈ target
  maps_target : ∀ x ∈ target, parametrization x ∈ source
  left_inverse : ∀ y ∈ source, parametrization (coordinates y.val) = y
  right_inverse : ∀ x ∈ target, coordinates (parametrization x).val = x

namespace SmoothSlice

variable {S : Set F} (s : SmoothSlice (E := E) S)

/-- The local homeomorphism associated with a slice. -/
def chart : OpenPartialHomeomorph S E where
  toFun := fun y => s.coordinates y.val
  invFun := s.parametrization
  source := s.source
  target := s.target
  map_source' := s.maps_source
  map_target' := s.maps_target
  left_inv' := s.left_inverse
  right_inv' := s.right_inverse
  open_source := s.open_source
  open_target := s.open_target
  continuousOn_toFun := by
    intro y hy
    exact ((s.coordinates_smooth y hy).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := by
    exact s.parametrization_smooth.continuous.subtype_mk
      (fun x => (s.parametrization x).property) |>.continuousOn

@[simp] theorem chart_apply (y : S) :
    s.chart y = s.coordinates y.val := rfl

@[simp] theorem chart_symm_apply (x : E) :
    s.chart.symm x = s.parametrization x := rfl

/-- The transition is the composition of the ambient coordinate map of the
second slice with the smooth parametrization of the first slice. -/
theorem transition_smooth (s t : SmoothSlice (E := E) S) :
    ContDiffOn ℝ ⊤ (s.chart.symm.trans t.chart)
      (s.chart.symm.trans t.chart).source := by
  intro x hx
  change x ∈ s.target ∧ s.parametrization x ∈ t.source at hx
  exact ((t.coordinates_smooth (s.parametrization x) hx.2).comp x
    s.parametrization_smooth.contDiffAt).contDiffWithinAt

/-- Differentiating the local right inverse proves that every slice is
immersive throughout its target. -/
theorem parametrization_fderiv_injective (x : E) (hx : x ∈ s.target) :
    Function.Injective (fderiv ℝ (fun y => (s.parametrization y).val) x) := by
  have hp := (s.parametrization_smooth.differentiable (by simp) x).hasFDerivAt
  have hc := ((s.coordinates_smooth _ (s.maps_target x hx)).differentiableAt
    (by simp)).hasFDerivAt
  have he : (fun y => s.coordinates (s.parametrization y).val) =ᶠ[𝓝 x]
      (id : E → E) := by
    filter_upwards [s.open_target.mem_nhds hx] with y hy
    exact s.right_inverse y hy
  have hd := ((hc.comp x hp).congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id x)
  intro v w hvw
  have hvw' := congrArg (fderiv ℝ s.coordinates (s.parametrization x).val) hvw
  change ((fderiv ℝ s.coordinates (s.parametrization x).val).comp
    (fderiv ℝ (fun y => (s.parametrization y).val) x)) v =
    ((fderiv ℝ s.coordinates (s.parametrization x).val).comp
      (fderiv ℝ (fun y => (s.parametrization y).val) x)) w at hvw'
  simpa only [hd, ContinuousLinearMap.id_apply] using hvw'

end SmoothSlice

/-- The atlas obtained from one concrete slice around each point. -/
def sliceChartedSpace {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) : ChartedSpace E S where
  atlas := Set.range (fun x => (s x).chart)
  chartAt x := (s x).chart
  mem_chart_source x := covers x
  chart_mem_atlas x := ⟨x, rfl⟩

/-- Smoothness of the atlas constructed from slices. In particular, this
construction does not assume an existing manifold structure on the subset. -/
theorem slice_isManifold {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) :
    letI := sliceChartedSpace s covers
    IsManifold (𝓘(ℝ, E)) ⊤ S := by
  letI := sliceChartedSpace s covers
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range (fun x => (s x).chart) at he
  change e' ∈ Set.range (fun x => (s x).chart) at he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using (s x).transition_smooth (s y)

/-- The inclusion of the subset with its constructed atlas is genuinely
manifold-smooth. -/
theorem slice_val_contMDiff {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) :
    letI := sliceChartedSpace s covers
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ⊤ (fun x : S => x.val) := by
  letI := sliceChartedSpace s covers
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤ (fun y : E => ((s x).parametrization y).val)
    (Set.range (id : E → E)) ((s x).coordinates x.val)
  exact (s x).parametrization_smooth.contDiffAt.contDiffWithinAt

/-- The actual manifold derivative of the inclusion is the derivative of the
preferred inverse chart. -/
theorem slice_val_mfderiv_eq {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) (x : S) :
    letI := sliceChartedSpace s covers
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x =
      fderiv ℝ (fun y => ((s x).parametrization y).val) ((s x).coordinates x.val) := by
  letI := sliceChartedSpace s covers
  have hd : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x :=
    (slice_val_contMDiff s covers x).mdifferentiableAt (by simp)
  unfold mfderiv
  rw [if_pos hd]
  change fderivWithin ℝ (fun y => ((s x).parametrization y).val)
    (Set.range (id : E → E)) ((s x).coordinates x.val) = _
  simp only [Set.range_id, fderivWithin_univ]

/-- Every inclusion derivative is injective, with respect to mathlib's actual
manifold tangent space. -/
theorem slice_val_mfderiv_injective {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) (x : S) :
    letI := sliceChartedSpace s covers
    Function.Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x) := by
  letI := sliceChartedSpace s covers
  rw [slice_val_mfderiv_eq s covers x]
  exact (s x).parametrization_fderiv_injective _ ((s x).maps_source x (covers x))

end GS.OverlapGeometry
