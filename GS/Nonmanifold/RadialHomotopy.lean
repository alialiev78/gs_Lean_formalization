module

public import GS.Nonmanifold.RadialCone

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit strong deformation of the punctured cone onto the radius-one link

The interval and every continuity/endpoint/fixed-point condition are supplied
below. The data can be packaged into a ContinuousMap.Homotopy later without
changing the mathematical map. No topological invariant is assumed here.
-/
noncomputable section
open Matrix GS
namespace GS.Nonmanifold

abbrev ClosedUnitInterval := {t : ℝ // 0 ≤ t ∧ t ≤ 1}

def timeZero : ClosedUnitInterval := ⟨0,by constructor <;> norm_num⟩
def timeOne : ClosedUnitInterval := ⟨1,by constructor <;> norm_num⟩

def interpolatedRadius (t : ClosedUnitInterval) (r : PositiveRadius) : PositiveRadius :=
  ⟨(1-t.val)*r.val+t.val, by
    by_cases ht : t.val < 1
    · have hm : 0 < (1-t.val)*r.val := mul_pos (sub_pos.mpr ht) r.property
      linarith [t.property.1]
    · have he : t.val=1 := le_antisymm t.property.2 (le_of_not_gt ht)
      simp [he]⟩

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def radialHomotopy (p : ClosedUnitInterval × PuncturedRankOne κ) : PuncturedRankOne κ :=
  scaleLink (interpolatedRadius p.1 (radialCoordinates p.2).1, normalizeRankOne p.2)

theorem continuous_radialHomotopy : Continuous (radialHomotopy : ClosedUnitInterval × PuncturedRankOne κ → PuncturedRankOne κ) := by
  apply continuous_scaleLink.comp
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    have hr : Continuous (fun p : ClosedUnitInterval × PuncturedRankOne κ =>
        frobeniusRadius p.2.val) := continuous_frobeniusRadius.comp (by fun_prop)
    exact ((continuous_const.sub (by fun_prop)).mul hr).add (by fun_prop)
  · exact continuous_normalizeRankOne.comp continuous_snd

theorem radialHomotopy_zero (W : PuncturedRankOne κ) :
    radialHomotopy (timeZero,W) = W := by
  have hr : interpolatedRadius timeZero (radialCoordinates W).1 =
      (radialCoordinates W).1 := by
    apply Subtype.ext
    simp [interpolatedRadius,timeZero]
  unfold radialHomotopy
  rw [hr]
  exact scaleLink_radialCoordinates W

theorem radialHomotopy_one (W : PuncturedRankOne κ) :
    radialHomotopy (timeOne,W) = linkInclusion (normalizeRankOne W) := by
  apply Subtype.ext
  change ((1-(1:ℝ))*frobeniusRadius W.val+1) • (normalizeRankOne W).val =
    (normalizeRankOne W).val
  simp

theorem radialHomotopy_fixes_link (t : ClosedUnitInterval) (W : RankOneLink κ) :
    radialHomotopy (t,linkInclusion W) = linkInclusion W := by
  apply Subtype.ext
  change ((1-t.val)*frobeniusRadius W.val+t.val) •
    (normalizeRankOne (linkInclusion W)).val = W.val
  rw [normalize_linkInclusion, frobeniusRadius_link]
  have he : (1-t.val)*(1:ℝ)+t.val = 1 := by ring
  rw [he,one_smul]

/-- Records an actual strong deformation retraction, with all axioms proved
for the displayed functions rather than supplied by a caller. -/
structure RadialDeformationData (κ : Type*) [Fintype κ] [DecidableEq κ] where
  homotopy : ClosedUnitInterval × PuncturedRankOne κ → PuncturedRankOne κ
  continuous_homotopy : Continuous homotopy
  starts_at_identity : ∀ W, homotopy (timeZero,W) = W
  ends_at_link : ∀ W, homotopy (timeOne,W) = linkInclusion (normalizeRankOne W)
  fixes_link : ∀ t W, homotopy (t,linkInclusion W) = linkInclusion W

def radialDeformation : RadialDeformationData κ where
  homotopy := radialHomotopy
  continuous_homotopy := continuous_radialHomotopy
  starts_at_identity := radialHomotopy_zero
  ends_at_link := radialHomotopy_one
  fixes_link := radialHomotopy_fixes_link

end GS.Nonmanifold
