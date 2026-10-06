module

public import GS.Nonmanifold.CircleRetract

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The punctured determinantal cone is (0,infinity) times its link

All spaces carry their actual subtype/product topologies. Normalization is
performed only away from zero. The radial homeomorphism and the circle retract
below are genuine constructions, but are not a proof of the local homology
calculation at zero or of its shift under a Euclidean product.
-/
noncomputable section
open Matrix GS GS.Extensions
open scoped BigOperators
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def frobeniusRadius (W : Matrix (Fin 2) κ ℝ) : ℝ := Real.sqrt (frobSq W)

theorem continuous_frobeniusRadius : Continuous (frobeniusRadius : Matrix (Fin 2) κ ℝ → ℝ) := by
  exact Real.continuous_sqrt.comp continuous_frobSq

theorem frobeniusRadius_nonneg (W : Matrix (Fin 2) κ ℝ) :
    0 ≤ frobeniusRadius W := Real.sqrt_nonneg _

theorem frobeniusRadius_sq (W : Matrix (Fin 2) κ ℝ) :
    frobeniusRadius W ^ 2 = frobSq W := Real.sq_sqrt (frobSq_nonneg W)

theorem frobeniusRadius_pos {W : Matrix (Fin 2) κ ℝ} (hW : W ≠ 0) :
    0 < frobeniusRadius W := Real.sqrt_pos.2 (frobSq_pos_of_ne_zero hW)

theorem frobeniusRadius_ne_zero {W : Matrix (Fin 2) κ ℝ} (hW : W ≠ 0) :
    frobeniusRadius W ≠ 0 := ne_of_gt (frobeniusRadius_pos hW)

theorem frobeniusRadius_link (W : RankOneLink κ) :
    frobeniusRadius W.val = 1 := by
  simp [frobeniusRadius, W.property.2]

def normalizeRankOne (W : PuncturedRankOne κ) : RankOneLink κ :=
  ⟨(frobeniusRadius W.val)⁻¹ • W.val,
    rank_smul_le_one _ W.property.1, by
      rw [frobSq_smul, ← frobeniusRadius_sq]
      field_simp [frobeniusRadius_ne_zero W.property.2]⟩

theorem continuous_normalizeRankOne :
    Continuous (normalizeRankOne : PuncturedRankOne κ → RankOneLink κ) := by
  apply Continuous.subtype_mk
  have hr : Continuous (fun W : PuncturedRankOne κ => frobeniusRadius W.val) :=
    continuous_frobeniusRadius.comp continuous_subtype_val
  have hi : Continuous (fun W : PuncturedRankOne κ =>
      (frobeniusRadius W.val)⁻¹) :=
    hr.inv₀ (fun W => frobeniusRadius_ne_zero W.property.2)
  exact hi.smul continuous_subtype_val

def scaleLink (p : PositiveRadius × RankOneLink κ) : PuncturedRankOne κ :=
  ⟨p.1.val • p.2.val, rank_smul_le_one _ p.2.property.1, by
    intro hz
    have hh := congrArg (fun W : Matrix (Fin 2) κ ℝ => (p.1.val)⁻¹ • W) hz
    have ht : p.1.val ≠ 0 := ne_of_gt p.1.property
    have he : p.2.val = 0 := by simpa [smul_smul, ht] using hh
    exact link_ne_zero p.2 he⟩

theorem continuous_scaleLink : Continuous (scaleLink : PositiveRadius × RankOneLink κ → PuncturedRankOne κ) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

theorem frobeniusRadius_scaleLink (p : PositiveRadius × RankOneLink κ) :
    frobeniusRadius (scaleLink p).val = p.1.val := by
  have hs := frobeniusRadius_sq (scaleLink p).val
  change frobeniusRadius (scaleLink p).val^2 = frobSq (p.1.val • p.2.val) at hs
  rw [frobSq_smul, p.2.property.2, mul_one] at hs
  have hn := frobeniusRadius_nonneg (scaleLink p).val
  nlinarith [p.1.property]

def radialCoordinates (W : PuncturedRankOne κ) : PositiveRadius × RankOneLink κ :=
  (⟨frobeniusRadius W.val, frobeniusRadius_pos W.property.2⟩, normalizeRankOne W)

theorem continuous_radialCoordinates : Continuous (radialCoordinates : PuncturedRankOne κ → PositiveRadius × RankOneLink κ) := by
  apply Continuous.prodMk
  · exact (continuous_frobeniusRadius.comp continuous_subtype_val).subtype_mk _
  · exact continuous_normalizeRankOne

theorem scaleLink_radialCoordinates (W : PuncturedRankOne κ) :
    scaleLink (radialCoordinates W) = W := by
  apply Subtype.ext
  change frobeniusRadius W.val • ((frobeniusRadius W.val)⁻¹ • W.val) = W.val
  rw [smul_smul, mul_inv_cancel₀ (frobeniusRadius_ne_zero W.property.2), one_smul]

theorem radialCoordinates_scaleLink (p : PositiveRadius × RankOneLink κ) :
    radialCoordinates (scaleLink p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact frobeniusRadius_scaleLink p
  · apply Subtype.ext
    change (frobeniusRadius (scaleLink p).val)⁻¹ • (p.1.val • p.2.val) = p.2.val
    rw [frobeniusRadius_scaleLink, smul_smul,
      inv_mul_cancel₀ (ne_of_gt p.1.property), one_smul]

/-- Radial decomposition in the induced topology, with no compactness assumption. -/
def puncturedConeHomeomorph :
    PuncturedRankOne κ ≃ₜ PositiveRadius × RankOneLink κ where
  toFun := radialCoordinates
  invFun := scaleLink
  left_inv := scaleLink_radialCoordinates
  right_inv := radialCoordinates_scaleLink
  continuous_toFun := continuous_radialCoordinates
  continuous_invFun := continuous_scaleLink

/-- The inclusion of the unit-radius slice into the punctured cone. -/
def linkInclusion (W : RankOneLink κ) : PuncturedRankOne κ :=
  ⟨W.val, W.property.1, link_ne_zero W⟩

theorem continuous_linkInclusion : Continuous (linkInclusion : RankOneLink κ → PuncturedRankOne κ) :=
  continuous_subtype_val.subtype_mk _

theorem normalize_linkInclusion (W : RankOneLink κ) :
    normalizeRankOne (linkInclusion W) = W := by
  apply Subtype.ext
  change (frobeniusRadius W.val)⁻¹ • W.val = W.val
  rw [frobeniusRadius_link, inv_one, one_smul]

/-- A circle retract of the punctured cone, before any homology is introduced. -/
def puncturedConeCircleRetract (d : ℕ) :
    CircleRetractData (PuncturedRankOne (Fin (d+2))) where
  sectionMap := fun v => linkInclusion (circleSection d v)
  retractionMap := fun W => circleRetraction (normalizeRankOne W)
  section_continuous := continuous_linkInclusion.comp (continuous_circleSection d)
  retraction_continuous := continuous_circleRetraction.comp continuous_normalizeRankOne
  retraction_section := by
    intro v
    rw [normalize_linkInclusion, circleRetraction_section]

/-- Every strictly positive radial slice carries the same circle retract. -/
def radiusSliceSection (d : ℕ) (r : PositiveRadius) (v : UnitCircle) :
    PuncturedRankOne (Fin (d+2)) := scaleLink (r, circleSection d v)

theorem continuous_radiusSliceSection (d : ℕ) (r : PositiveRadius) :
    Continuous (radiusSliceSection d r) :=
  continuous_scaleLink.comp (continuous_const.prodMk (continuous_circleSection d))

theorem normalize_scaleLink (r : PositiveRadius) (W : RankOneLink κ) :
    normalizeRankOne (scaleLink (r,W)) = W := by
  exact congrArg Prod.snd (radialCoordinates_scaleLink (r,W))

theorem circleRetraction_radiusSliceSection (d : ℕ) (r : PositiveRadius)
    (v : UnitCircle) :
    circleRetraction (normalizeRankOne (radiusSliceSection d r v)) = v := by
  unfold radiusSliceSection
  rw [normalize_scaleLink, circleRetraction_section]

/-- Quantitative control: the circle section can be placed at any positive radius. -/
theorem frobSq_radiusSliceSection (d : ℕ) (r : PositiveRadius) (v : UnitCircle) :
    frobSq (radiusSliceSection d r v).val = r.val^2 := by
  change frobSq (r.val • (circleSection d v).val) = r.val^2
  rw [frobSq_smul, (circleSection d v).property.2, mul_one]

end GS.Nonmanifold
