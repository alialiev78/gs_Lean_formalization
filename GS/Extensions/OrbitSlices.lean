module

public import GS.OverlapGeometry.SliceAtlas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth slices from a parametrization and ambient inverse

The constructor keeps the model spaces abstract. Applications supply the
relative openness and smooth inverse data before assembling an orbit atlas.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace GS.Extensions

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F}

def smoothSliceOfParametrization (p : E → S) (c : F → E) (U : Set E)
    (hp : ContDiff ℝ ⊤ (fun x => (p x).val))
    (hU : IsOpen U) (himage : IsOpen (p '' U))
    (hc : ∀ x ∈ U, ContDiffAt ℝ ⊤ c (p x).val)
    (hi : ∀ x ∈ U, c (p x).val = x) :
    GS.OverlapGeometry.SmoothSlice (E := E) S where
  source := p '' U
  target := U
  coordinates := c
  parametrization := p
  open_source := himage
  open_target := hU
  coordinates_smooth := by
    rintro y ⟨x, hx, rfl⟩
    exact hc x hx
  parametrization_smooth := hp
  maps_source := by
    rintro y ⟨x, hx, rfl⟩
    rw [hi x hx]
    exact hx
  maps_target := fun x hx => ⟨x, hx, rfl⟩
  left_inverse := by
    rintro y ⟨x, hx, rfl⟩
    rw [hi x hx]
  right_inverse := hi

def translateSmoothSlice (s : GS.OverlapGeometry.SmoothSlice (E := E) S)
    (f g : F → F) (T U : S → S)
    (hT : ∀ x, (T x).val = f x.val) (hU : ∀ x, (U x).val = g x.val)
    (hTU : ∀ x, T (U x) = x) (hUT : ∀ x, U (T x) = x)
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (hUc : Continuous U) :
    GS.OverlapGeometry.SmoothSlice (E := E) S where
  source := U ⁻¹' s.source
  target := s.target
  coordinates := fun A => s.coordinates (g A)
  parametrization := fun h => T (s.parametrization h)
  open_source := s.open_source.preimage hUc
  open_target := s.open_target
  coordinates_smooth := by
    intro X hX
    have hc := s.coordinates_smooth (U X) hX
    rw [hU] at hc
    exact hc.comp X.val hg.contDiffAt
  parametrization_smooth := by
    simpa only [hT, Function.comp_def] using hf.comp s.parametrization_smooth
  maps_source := by
    intro X hX
    simpa only [hU] using s.maps_source (U X) hX
  maps_target := by
    intro h hh
    change U (T (s.parametrization h)) ∈ s.source
    rw [hUT]
    exact s.maps_target h hh
  left_inverse := by
    intro X hX
    have hi := congrArg T (s.left_inverse (U X) hX)
    simpa only [hU, hTU] using hi
  right_inverse := by
    intro h hh
    change s.coordinates (g (T (s.parametrization h)).val) = h
    rw [← hU, hUT]
    exact s.right_inverse h hh

end GS.Extensions
