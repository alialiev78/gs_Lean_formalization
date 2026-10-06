module

public import GS.Continuation.ExponentialChart

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Pointed homeomorphism of the ORIGINAL compact images

 Compactness, continuity and same fibres are taken
from theorem bodies, not assumptions. Only the two compact images are identified;
coverage of a neighbourhood of the whole GS family and the cone obstruction are
not claimed here.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

/-- Convenient names for the two genuine compact image spaces. -/
abbrev OriginalFImage {q : ℕ} (Q₀ : Mat q) (η : ℝ) :=
  Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val)

abbrev OriginalGImage (q : ℕ) (η : ℝ) :=
  Set.range (fun p : ↥(originalK q η) => originalG p.val)

/-- A basepoint in the F-image with its actual membership witness. -/
def originalFImageBase {q : ℕ} (Q₀ : Mat q) (η : ℝ) (hη : 0 ≤ η) :
    OriginalFImage Q₀ η :=
  ⟨basePoint Q₀,
    ⟨⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩,
      originalF_basePoint Q₀⟩⟩

/-- Its G-image is the zero tuple, not an unspecified marked point. -/
def originalGImageBase (q : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    OriginalGImage q η :=
  ⟨(0, 0, 0, 0),
    ⟨⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩,
      originalG_basePoint q⟩⟩

/-- A concrete compact-image homeomorphism, with both factorization and
basepoint identities. No same-fibres hypothesis is exposed in the conclusion. -/
theorem exists_pointed_original_compact_homeomorphism {q : ℕ}
    (hq : 0 < q) (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ (η : ℝ) (hη : 0 < η),
      ∃ h : OriginalFImage Q₀ η ≃ₜ OriginalGImage q η,
        (∀ p : ↥(originalK q η),
          h ⟨originalF Q₀ p.val, ⟨p, rfl⟩⟩ =
            ⟨originalG p.val, ⟨p, rfl⟩⟩) ∧
        h (originalFImageBase Q₀ η hη.le) = originalGImageBase q η hη.le := by
  obtain ⟨η, hη, hfib⟩ := original_same_fibres hq Q₀ hQ₀ hentries
  obtain ⟨h, hh⟩ := original_compact_homeomorphism Q₀ η
    (fun p hp p' hp' => (hfib p hp p' hp').mp)
  refine ⟨η, hη, h, hh, ?_⟩
  let p₀ : ↥(originalK q η) :=
    ⟨originalBaseParameters q, originalBaseParameters_mem q hη.le⟩
  have he := hh p₀
  have heF : (⟨originalF Q₀ p₀.val, ⟨p₀, rfl⟩⟩ : OriginalFImage Q₀ η) =
      originalFImageBase Q₀ η hη.le := by
    apply Subtype.ext
    exact originalF_basePoint Q₀
  have heG : (⟨originalG p₀.val, ⟨p₀, rfl⟩⟩ : OriginalGImage q η) =
      originalGImageBase q η hη.le := by
    apply Subtype.ext
    exact originalG_basePoint q
  rwa [heF, heG] at he

/-- The singular fibre above M0 is exactly the circle with all other coordinates
zero. The forward implication uses equality with a fixed basepoint, then g. -/
theorem original_base_fibre {q : ℕ} (Q₀ : Mat q) (η : ℝ) (hη : 0 ≤ η)
    (hfib : ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p = originalF Q₀ p' ↔ originalG p = originalG p')
    (ell r : Fin q → ℝ) (c z : Mat q) (u : CircleVector)
    (hp : (ell, r, c, z, u) ∈ originalK q η) :
    originalF Q₀ (ell, r, c, z, u) = basePoint Q₀ ↔
      ell = 0 ∧ r = 0 ∧ c = 0 ∧ z = 0 := by
  have hp₀ := originalBaseParameters_mem q hη
  have hu : OnCircle u := hp.2.2.2.2.2.2.2
  constructor
  · intro he
    have hf : originalF Q₀ (ell, r, c, z, u) =
        originalF Q₀ (originalBaseParameters q) :=
      he.trans (originalF_basePoint Q₀).symm
    have hg := (hfib _ hp _ hp₀).mp hf
    obtain ⟨hell, hr, hc, hz⟩ :=
      (originalG_fibres ell r 0 0 c z 0 0 u circleBase hu circleBase_mem).mp hg
    refine ⟨hell, hr, hc, ?_⟩
    rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩ | ⟨_, hz⟩
    · exact hz
    · exact hz
    · simpa using hz
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    calc
      originalF Q₀ (0, 0, 0, 0, u) = originalF Q₀ (0, 0, 0, 0, circleBase) :=
        originalF_zero_difference Q₀ 0 0 0 u circleBase
      _ = basePoint Q₀ := originalF_basePoint Q₀

/-- The exact singular fibre is obtained on a genuinely constructed small
domain; no same-fibres assumption is required from the caller. -/
theorem exists_original_base_fibre {q : ℕ} (hq : 0 < q) (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ (ell r : Fin q → ℝ) (c z : Mat q) (u : CircleVector),
      (ell, r, c, z, u) ∈ originalK q η →
        (originalF Q₀ (ell, r, c, z, u) = basePoint Q₀ ↔
          ell = 0 ∧ r = 0 ∧ c = 0 ∧ z = 0) := by
  obtain ⟨η, hη, hfib⟩ := original_same_fibres hq Q₀ hQ₀ hentries
  exact ⟨η, hη, fun ell r c z u hp =>
    original_base_fibre Q₀ η hη.le hfib ell r c z u hp⟩

end GS.Continuation
