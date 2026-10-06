module

public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Continuation.PointedCompactImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Linking the new independent-coordinate model to the unchanged original f/g

This integrates the model-side results with the inherited exponential-chart
and same-fibres theorems. The resulting homeomorphism is still for the selected
compact f-image. It is NOT promoted to a neighbourhood of the full GS family:
OriginalLocalCoverageGoal and parametrization membership must be proved first.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
namespace GS.Nonmanifold

/-- The original g, with its already proved membership in the unbounded model. -/
def originalGAsModel {q : ℕ} {η : ℝ} (p : ↥(originalK q η)) : OriginalModel q :=
  ⟨originalG p.val, originalG_image_subset_model q η ⟨p.val,p.property,rfl⟩⟩

def independentG {q : ℕ} {η : ℝ} (p : ↥(originalK q η)) : ModelCoordinates q :=
  encodeModel (originalGAsModel p)

theorem continuous_originalGAsModel (q : ℕ) (η : ℝ) :
    Continuous (@originalGAsModel q η) :=
  ((continuous_originalG q).comp continuous_subtype_val).subtype_mk _

theorem continuous_independentG (q : ℕ) (η : ℝ) :
    Continuous (@independentG q η) :=
  (continuous_encodeModel q).comp (continuous_originalGAsModel q η)

theorem independentG_eq_iff {q : ℕ} {η : ℝ} (p p' : ↥(originalK q η)) :
    independentG p = independentG p' ↔ originalG p.val = originalG p'.val := by
  constructor
  · intro h
    have he := congrArg decodeModel h
    change decodeModel (encodeModel (originalGAsModel p)) =
      decodeModel (encodeModel (originalGAsModel p')) at he
    rw [decode_encodeModel,decode_encodeModel] at he
    exact congrArg Subtype.val he
  · intro h
    have he : originalGAsModel p = originalGAsModel p' := Subtype.ext h
    exact congrArg encodeModel he

/-- Exact description of the range in the new coordinate model. -/
theorem mem_range_independentG {q : ℕ} {η : ℝ} (x : ModelCoordinates q) :
    x ∈ Set.range (@independentG q η) ↔
      (decodeModel x).val ∈ originalG '' originalK q η := by
  constructor
  · rintro ⟨p,rfl⟩
    change (decodeModel (encodeModel (originalGAsModel p))).val ∈ _
    rw [decode_encodeModel]
    exact ⟨p.val,p.property,rfl⟩
  · rintro ⟨p,hp,he⟩
    refine ⟨⟨p,hp⟩,?_⟩
    have hh : originalGAsModel (⟨p,hp⟩ : ↥(originalK q η)) = decodeModel x :=
      Subtype.ext he
    change encodeModel (originalGAsModel ⟨p,hp⟩) = x
    rw [hh,encode_decodeModel]

/-- Zero in the independent coordinates, including the rank-cone subtype. -/
def modelCoordinatesZero (q : ℕ) : ModelCoordinates q :=
  (0,0,0,⟨0,by simp⟩)

theorem decode_modelCoordinatesZero (q : ℕ) :
    (decodeModel (modelCoordinatesZero q)).val = (0,0,0,0) := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Prod.ext
  · funext j
    simp [decodeModel,modelCoordinatesZero,unpackRight]
  · apply Prod.ext
    · ext i j
      simp [decodeModel,modelCoordinatesZero,unpackSkew]
    · ext r ij
      simp [decodeModel,modelCoordinatesZero,unpackRows,unpackSkew]

/-- The original distinguished parameter maps to the zero coordinate tuple. -/
theorem independentG_basepoint (q : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    independentG (⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩ :
      ↥(originalK q η)) = modelCoordinatesZero q := by
  let p : ↥(originalK q η) := ⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩
  have he : originalGAsModel p = decodeModel (modelCoordinatesZero q) := by
    apply Subtype.ext
    exact (originalG_basePoint q).trans (decode_modelCoordinatesZero q).symm
  change encodeModel (originalGAsModel p) = modelCoordinatesZero q
  rw [he,encode_decodeModel]

/-- The model-coordinate image contains an open neighbourhood of its zero point. -/
theorem independentG_contains_neighbourhood (q : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ U : Set (ModelCoordinates q), IsOpen U ∧ modelCoordinatesZero q ∈ U ∧
      U ⊆ Set.range (@independentG q η) := by
  let U : Set (ModelCoordinates q) :=
    {x | modelRadiusSq (decodeModel x).val < η^2}
  have hc : Continuous (fun x : ModelCoordinates q => modelRadiusSq (decodeModel x).val) :=
    (continuous_modelRadiusSq q).comp
      (continuous_subtype_val.comp (continuous_decodeModel q))
  refine ⟨U,isOpen_lt hc continuous_const,?_,?_⟩
  · change modelRadiusSq (decodeModel (modelCoordinatesZero q)).val < η^2
    rw [decode_modelCoordinatesZero]
    have hz : modelRadiusSq ((0,0,0,0) : OriginalImageCoordinates q) = 0 := by
      simp [modelRadiusSq,frobSq,frobInner]
    rw [hz]
    exact sq_pos_of_pos hη
  · intro x hx
    apply (mem_range_independentG x).mpr
    exact small_modelRadius_mem_originalG hη (decodeModel x).val (decodeModel x).property hx

/-- A constructed compact-image homeomorphism to independent skew coordinates.
There is no supplied same-fibres or chart-injectivity assumption. -/
theorem exists_original_compact_model_homeomorphism {q : ℕ} (hq : 0 < q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ (η : ℝ) (hη : 0 < η),
      ∃ h : OriginalFImage Q₀ η ≃ₜ Set.range (@independentG q η),
        (∀ p : ↥(originalK q η),
          h ⟨originalF Q₀ p.val,⟨p,rfl⟩⟩ = ⟨independentG p,⟨p,rfl⟩⟩) ∧
        (h (originalFImageBase Q₀ η hη.le)).val = modelCoordinatesZero q ∧
        ∃ U : Set (ModelCoordinates q), IsOpen U ∧ modelCoordinatesZero q ∈ U ∧
          U ⊆ Set.range (@independentG q η) := by
  obtain ⟨η,hη,hfib⟩ := original_same_fibres hq Q₀ hQ₀ hentries
  letI : CompactSpace ↥(originalK q η) := isCompact_iff_compactSpace.mp (isCompact_originalK q η)
  have hh : ∀ p p' : ↥(originalK q η),
      originalF Q₀ p.val = originalF Q₀ p'.val ↔ independentG p = independentG p' := by
    intro p p'
    exact (hfib p.val p.property p'.val p'.property).trans (independentG_eq_iff p p').symm
  obtain ⟨h,he⟩ := exists_homeomorph_ranges_of_same_fibres
    (fun p : ↥(originalK q η) => originalF Q₀ p.val) (@independentG q η)
    ((continuous_originalF Q₀).comp continuous_subtype_val)
    (continuous_independentG q η) hh
  have hpoint : (h (originalFImageBase Q₀ η hη.le)).val = modelCoordinatesZero q := by
    let p₀ : ↥(originalK q η) :=
      ⟨originalBaseParameters q, originalBaseParameters_mem q hη.le⟩
    have he' := congrArg Subtype.val (he p₀)
    have hs : (⟨originalF Q₀ p₀.val,⟨p₀,rfl⟩⟩ : OriginalFImage Q₀ η) =
        originalFImageBase Q₀ η hη.le := by
      apply Subtype.ext
      exact originalF_basePoint Q₀
    rw [hs] at he'
    exact he'.trans (independentG_basepoint q η hη.le)
  exact ⟨η,hη,h,he,hpoint,independentG_contains_neighbourhood q η hη⟩

end GS.Nonmanifold
