module

public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryLocalModel.NormalizedPositivity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The full compact unitary local model

The actual matrix image, including all outer factors, is homeomorphic to the
product of the anchored outer unitary group and the bounded rank-one cone.
The proof uses positive-anchor uniqueness and compact equal-fibre maps.
-/
noncomputable section
open Matrix GS GS.UnitaryManifold
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

/-- The positivity properties of the dephased chart needed by outer recovery. -/
def PositiveChartAnchors {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ U, (∀ i, ∃ a : ℝ, 0 < a ∧ ψ x i o / Q i o = a) ∧
    (∀ j, ∃ a : ℝ, 0 < a ∧ ψ x o j / Q o j = a)

theorem chartBlockFamily_positive {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hpos : PositiveChartAnchors Q o ψ U) (p : LocalParameters d)
    (hp : p.1+p.2.1 ∈ U) (hm : p.1-p.2.1 ∈ U) (hu : OnSphere p.2.2) :
    NormalizedPositiveAnchors Q o (chartBlockFamily ψ p) := by
  constructor
  · intro i
    exact middleBlock_ratio_posDef _ _ _ _ hu ((hpos _ hp).1 i) ((hpos _ hm).1 i)
  · intro j
    exact middleBlock_ratio_posDef _ _ _ _ hu ((hpos _ hp).2 j) ((hpos _ hm).2 j)

/-- The full compact parametrization has precisely the outer-plus-cone fibres. -/
theorem fullCompactMiddle_fibres {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψ : Set.InjOn ψ U) (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U)
    (p p' : FullCompactParameters q o d r) :
    fullCompactMiddle ψ o r p = fullCompactMiddle ψ o r p' ↔
      p.1 = p'.1 ∧ parameterCone p.2.val = parameterCone p'.2.val := by
  have hψ' : Set.InjOn (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U := by
    intro x hx y hy he
    apply hψ hx hy
    funext i j
    exact congrFun he (i,j)
  have hh := normalized_chart_fibres_on Q o
    (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U hψ'
    (outerLeft p.1) (outerRight p.1) (outerLeft p'.1) (outerRight p'.1)
    p.2.val.1 p.2.val.2.1 p'.2.val.1 p'.2.val.2.1 p.2.val.2.2 p'.2.val.2.2
    (outerLeft_unitary p.1) (outerRight_unitary p.1)
    (outerLeft_unitary p'.1) (outerRight_unitary p'.1)
    (outerRight_anchor p.1) (outerRight_anchor p'.1)
    (hargs _ p.2.property).1 (hargs _ p.2.property).2
    (hargs _ p'.2.property).1 (hargs _ p'.2.property).2
    p.2.property.2.2 p'.2.property.2.2
    (chartBlockFamily_positive Q o ψ U hpos _
      (hargs _ p.2.property).1 (hargs _ p.2.property).2 p.2.property.2.2)
    (chartBlockFamily_positive Q o ψ U hpos _
      (hargs _ p'.2.property).1 (hargs _ p'.2.property).2 p'.2.property.2.2)
  have hflat : fullCompactMiddle ψ o r p = fullCompactMiddle ψ o r p' ↔
      normalizedBlockImage (outerLeft p.1) (outerRight p.1) (chartBlockFamily ψ p.2.val) =
      normalizedBlockImage (outerLeft p'.1) (outerRight p'.1) (chartBlockFamily ψ p'.2.val) :=
    by
      constructor
      · intro he
        have he' := congrArg (@extractBlockFamily q) he
        unfold normalizedBlockImage
        simpa only [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily,
          normalizedBlockImage] using he'
      · intro he
        exact congrArg (@flattenBlockFamily q) he
  rw [hflat]
  change _ ↔ _ at hh
  rw [show normalizedBlockImage (outerLeft p.1) (outerRight p.1) (chartBlockFamily ψ p.2.val) =
      normalizedBlockImage (outerLeft p'.1) (outerRight p'.1) (chartBlockFamily ψ p'.2.val) ↔
      outerLeft p.1 = outerLeft p'.1 ∧ outerRight p.1 = outerRight p'.1 ∧
      p.2.val.1 = p'.2.val.1 ∧ sphereOuter p.2.val.2.2 p.2.val.2.1 =
        sphereOuter p'.2.val.2.2 p'.2.val.2.1 from hh]
  simp only [parameterCone, Prod.mk.injEq, Subtype.mk.injEq]
  constructor
  · rintro ⟨hL,hR,hc,hz⟩
    exact ⟨outerFactors_ext hL hR,hc,hz⟩
  · rintro ⟨hg,hc,hz⟩
    exact ⟨congrArg outerLeft hg,congrArg outerRight hg,hc,hz⟩

def fullCompactCone {q d : ℕ} {o : Fin q} {r : ℝ}
    (p : FullCompactParameters q o d r) : OuterFactors q o × boundedConeCoordinates d r :=
  (p.1, ⟨parameterCone p.2.val, by
    rw [← parameterCone_image d r]
    exact ⟨p.2.val,p.2.property,rfl⟩⟩)

theorem continuous_fullCompactCone (q d : ℕ) (o : Fin q) (r : ℝ) :
    Continuous (@fullCompactCone q d o r) := by
  apply Continuous.prodMk continuous_fst
  apply Continuous.subtype_mk
  exact (continuous_parameterCone d).comp (continuous_subtype_val.comp continuous_snd)

theorem fullCompactCone_surjective (q d : ℕ) (o : Fin q) (r : ℝ) :
    Function.Surjective (@fullCompactCone q d o r) := by
  rintro ⟨g,w⟩
  have hw : w.val ∈ parameterCone '' localParameterBox d r := by
    simpa only [parameterCone_image] using w.property
  obtain ⟨p,hp,he⟩ := hw
  refine ⟨(g,⟨p,hp⟩),?_⟩
  refine Prod.ext ?_ ?_
  · rfl
  · exact Subtype.ext he

def surjectiveRangeHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : Function.Surjective f) : Set.range f ≃ₜ Y where
  toFun := Subtype.val
  invFun := fun y => ⟨y,hf y⟩
  left_inv := by intro x; rfl
  right_inv := by intro y; rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- A homeomorphism for the full compact matrix image in the original ambient
matrix topology, with its action on every parameter recorded explicitly. -/
theorem exists_full_compact_homeomorphism {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψc : ContinuousOn ψ U) (hψi : Set.InjOn ψ U)
    (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    ∃ h : FullCompactImage ψ o r ≃ₜ
        (OuterFactors q o × boundedConeCoordinates d r),
      ∀ p : FullCompactParameters q o d r,
        h ⟨fullCompactMiddle ψ o r p,⟨p,rfl⟩⟩ = fullCompactCone p := by
  obtain ⟨h,hh⟩ := exists_homeomorph_ranges_of_same_fibres
    (fullCompactMiddle ψ o r) (@fullCompactCone q d o r)
    (continuous_fullCompactMiddle ψ U o r hψc hargs)
    (continuous_fullCompactCone q d o r) (by
      intro p p'
      rw [fullCompactMiddle_fibres Q o ψ U hψi hpos r hargs p p']
      simp only [fullCompactCone, Prod.mk.injEq, Subtype.mk.injEq])
  let e := surjectiveRangeHomeomorph (@fullCompactCone q d o r)
    (fullCompactCone_surjective q d o r)
  refine ⟨h.trans e,?_⟩
  intro p
  change e (h _) = _
  rw [hh p]
  rfl

end GS.UnitaryLocalModel
