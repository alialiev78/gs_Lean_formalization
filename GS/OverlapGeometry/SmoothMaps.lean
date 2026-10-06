module

public import GS.OverlapGeometry.SliceAtlas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smoothness into an ambient slice manifold

For the slice atlas, a map into the subset is smooth whenever its ambient
matrix-valued realization is smooth. The proof uses the explicit smooth
ambient coordinate maps, not a chosen factorization of the varying point.
-/

noncomputable section
open scoped Topology Manifold
namespace GS.OverlapGeometry

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem slice_contMDiff_of_contDiff {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (f : G → S) (hf : ContDiff ℝ ⊤ (fun x => (f x).val)) :
    letI := sliceChartedSpace s covers
    ContMDiff (𝓘(ℝ, G)) (𝓘(ℝ, E)) ⊤ f := by
  letI := sliceChartedSpace s covers
  have hc : Continuous f := hf.continuous.subtype_mk (fun x => (f x).property)
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt, ?_⟩
  change ContMDiffAt (𝓘(ℝ, G)) (𝓘(ℝ, E)) ⊤
    (fun y => (s (f x)).coordinates (f y).val) x
  apply (contMDiffAt_iff_contDiffAt).mpr
  exact ((s (f x)).coordinates_smooth (f x) (covers (f x))).comp x hf.contDiffAt

theorem slice_contMDiff_iff_contDiff {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (f : G → S) :
    letI := sliceChartedSpace s covers
    ContMDiff (𝓘(ℝ, G)) (𝓘(ℝ, E)) ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) := by
  letI := sliceChartedSpace s covers
  constructor
  · intro hf
    exact contMDiff_iff_contDiff.mp ((slice_val_contMDiff s covers).comp hf)
  · exact slice_contMDiff_of_contDiff s covers f

end GS.OverlapGeometry
