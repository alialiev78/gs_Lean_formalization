module

public import GS.OverlapGeometry.SliceAtlas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Transporting an ambient smooth slice

The generic construction isolates chart transport from the concrete matrix
models. Its hypotheses are compatibility identities for an actual ambient
linear equivalence and an actual homeomorphism of the inherited subset.
-/
noncomputable section
open Set
namespace GS.OverlapGeometry.SmoothSlice
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F}

/-- Transport of an actual slice along a smooth ambient linear equivalence
and its corresponding homeomorphism of the subset. -/
def transportLinear (s : SmoothSlice (E := E) S) (T : F ≃L[ℝ] F)
    (e : S ≃ₜ S) (he : ∀ x : S, (e x).val = T x.val)
    (hei : ∀ x : S, (e.symm x).val = T.symm x.val) :
    SmoothSlice (E := E) S where
  source := e.symm ⁻¹' s.source
  target := s.target
  coordinates := fun x => s.coordinates (T.symm x)
  parametrization := fun x => e (s.parametrization x)
  open_source := s.open_source.preimage e.symm.continuous
  open_target := s.open_target
  coordinates_smooth := by
    intro x hx
    have hs := s.coordinates_smooth (e.symm x) hx
    rw [hei] at hs
    exact ContDiffAt.comp (f := T.symm) (g := s.coordinates) x.val hs
      T.symm.contDiff.contDiffAt
  parametrization_smooth := by
    simpa only [he, Function.comp_def] using T.contDiff.comp s.parametrization_smooth
  maps_source := by
    intro x hx
    have hs := s.maps_source (e.symm x) hx
    simpa only [hei] using hs
  maps_target := by
    intro x hx
    change e.symm (e (s.parametrization x)) ∈ s.source
    simpa only [e.symm_apply_apply] using s.maps_target x hx
  left_inverse := by
    intro x hx
    rw [← hei, s.left_inverse (e.symm x) hx, e.apply_symm_apply]
  right_inverse := by
    intro x hx
    rw [he, T.symm_apply_apply]
    exact s.right_inverse x hx
end GS.OverlapGeometry.SmoothSlice
