module

public import GS.OverlapGeometry.SmoothMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Manifold-valued sources for the ambient slice criterion

The source may be any charted manifold, in particular an actual tangent
bundle. Smoothness into the slice manifold is equivalent to smoothness of
the ambient realization. The subset keeps its inherited topology.
-/

noncomputable section
open scoped Topology Manifold

namespace GS.OverlapGeometry

variable {E F G H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem slice_contMDiff_of_ambient {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (I : ModelWithCorners ℝ G H) (f : M → S)
    (hf : ContMDiff I (𝓘(ℝ, F)) ⊤ (fun x => (f x).val)) :
    letI := sliceChartedSpace s covers
    ContMDiff I (𝓘(ℝ, E)) ⊤ f := by
  letI := sliceChartedSpace s covers
  have hc : Continuous f := hf.continuous.subtype_mk (fun x => (f x).property)
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt, ?_⟩
  change ContMDiffAt I (𝓘(ℝ, E)) ⊤
    (fun y => (s (f x)).coordinates (f y).val) x
  exact ContDiffAt.comp_contMDiffAt
    (I := I) (f := fun y : M => (f y).val) (g := (s (f x)).coordinates)
    ((s (f x)).coordinates_smooth (f x) (covers (f x))) (hf x)

theorem slice_contMDiff_iff_ambient {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (I : ModelWithCorners ℝ G H) (f : M → S) :
    letI := sliceChartedSpace s covers
    ContMDiff I (𝓘(ℝ, E)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, F)) ⊤ (fun x => (f x).val) := by
  letI := sliceChartedSpace s covers
  constructor
  · intro hf
    exact (slice_val_contMDiff s covers).comp hf
  · exact slice_contMDiff_of_ambient s covers I f

end GS.OverlapGeometry
