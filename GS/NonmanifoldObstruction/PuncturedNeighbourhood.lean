module

public import GS.Topology.SectionPair
public import GS.NonmanifoldObstruction.ProductSphere

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# An actual sphere retract of EVERY punctured open neighbourhood

Compactness puts one sufficiently small spherical section entirely inside a
specified open neighbourhood. The sphere projection is defined on the whole
punctured cone product, so its restriction gives an exact continuous retraction.

No claim is made here that a homology functor has been implemented or applied.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Nonmanifold Filter
open scoped BigOperators Topology
namespace GS.NonmanifoldObstruction

variable {ι : Type*} [Fintype ι]

/-- The explicit auxiliary sphere is compact in the usual product topology. -/
theorem isCompact_planeSphere : IsCompact {p : PlaneSpace ι | planeEnergy p = 1} := by
  classical
  let low : PlaneSpace ι := (fun _ => -1, fun _ => -1)
  let high : PlaneSpace ι := (fun _ => 1, fun _ => 1)
  have hclosed : IsClosed {p : PlaneSpace ι | planeEnergy p = 1} :=
    isClosed_eq continuous_planeEnergy continuous_const
  apply (show IsCompact (Set.Icc low high) from isCompact_Icc).of_isClosed_subset hclosed
  intro p hp
  have hx : ∀ i, |p.1 i| ≤ 1 := by
    intro i
    have hi : p.1 i^2 ≤ vectorSq p.1 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have he : vectorSq p.1 + planeSq p.2 = 1 := hp
    nlinarith [planeSq_nonneg p.2, sq_abs (p.1 i), abs_nonneg (p.1 i)]
  have hy : ∀ i, |p.2 i| ≤ 1 := by
    intro i
    have he : vectorSq p.1 + (p.2 0^2 + p.2 1^2) = 1 := hp
    have hi : (p.2 i)^2 ≤ 1 := by
      fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, id_eq] <;>
        nlinarith [vectorSq_nonneg p.1,
        sq_nonneg (p.2 0), sq_nonneg (p.2 1)]
    nlinarith [sq_abs (p.2 i), abs_nonneg (p.2 i)]
  exact ⟨⟨fun i => (abs_le.mp (hx i)).1, fun i => (abs_le.mp (hy i)).1⟩,
    ⟨fun i => (abs_le.mp (hx i)).2, fun i => (abs_le.mp (hy i)).2⟩⟩

instance planeSphere_compactSpace : CompactSpace (PlaneSphere ι) :=
  isCompact_iff_compactSpace.mp isCompact_planeSphere

/-- A compact-parameter tube lemma proved by closedness of projection.
Unlike pointwise continuity, this gives a SINGLE parameter neighbourhood
working for every point of K. -/
theorem uniform_neighbourhood_of_compact_parameter
    {A K X : Type*} [TopologicalSpace A] [TopologicalSpace K]
    [TopologicalSpace X] [CompactSpace K]
    (F : A × K → X) (hF : Continuous F) (a : A) (U : Set X)
    (hU : IsOpen U) (ha : ∀ k, F (a,k) ∈ U) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ t ∈ V, ∀ k, F (t,k) ∈ U := by
  let C : Set (A × K) := F ⁻¹' Uᶜ
  have hC : IsClosed C := hU.isClosed_compl.preimage hF
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  refine ⟨(Prod.fst '' C)ᶜ, hproj.isOpen_compl, ?_, ?_⟩
  · rintro ⟨⟨t,k⟩, htk, he⟩
    change t = a at he
    subst t
    exact htk (ha k)
  · intro t ht k
    by_contra hn
    exact ht ⟨(t,k), hn, rfl⟩

/-- Jointly continuous even at scale zero. -/
def scaledSectionFamily (d : ℕ) (p : ℝ × PlaneSphere ι) : ConeSpace ι (Fin (d+2)) :=
  productSection d (p.1 • p.2.val)

theorem continuous_scaledSectionFamily (d : ℕ) :
    Continuous (@scaledSectionFamily ι _ d) := by
  exact (continuous_productSection d).comp
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))

@[simp] theorem scaledSectionFamily_zero (d : ℕ) (v : PlaneSphere ι) :
    scaledSectionFamily d (0,v) = productZero := by
  simp [scaledSectionFamily]

/-- Uniform smallness in an ARBITRARY open neighbourhood, not only a round ball. -/
theorem exists_small_sphere_in_open (d : ℕ)
    (U : Set (ConeSpace ι (Fin (d+2)))) (hU : IsOpen U) (hzero : productZero ∈ U) :
    ∃ t : ℝ, 0<t ∧ ∀ v : PlaneSphere ι, productSection d (t • v.val) ∈ U := by
  obtain ⟨V,hV,h0,hsub⟩ := uniform_neighbourhood_of_compact_parameter
    (scaledSectionFamily d) (continuous_scaledSectionFamily d) 0 U hU
    (fun v => by simpa using hzero)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  refine ⟨δ/2, by positivity, ?_⟩
  intro v
  apply hsub (δ/2) (hball ?_) v
  change dist (δ/2) 0 < δ
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0<δ/2)]
  linarith

/-- Explicit continuous maps with a proved left-inverse law, not a homology
or nonmanifold assumption. -/
-- ContinuousSectionPair is imported from GS.Topology.SectionPair.

abbrev PuncturedOpen (d : ℕ) (U : Set (ConeSpace ι (Fin (d+2)))) :=
  {p : ConeSpace ι (Fin (d+2)) // p ∈ U ∧ p ≠ productZero}

/-- The central topological construction. It includes all Euclidean factors
and works for every neighbourhood before assuming any putative manifold chart. -/
theorem punctured_open_has_sphere_retract (d : ℕ)
    (U : Set (ConeSpace ι (Fin (d+2)))) (hU : IsOpen U) (hzero : productZero ∈ U) :
    Nonempty (ContinuousSectionPair (PlaneSphere ι) (PuncturedOpen d U)) := by
  obtain ⟨t,ht,hsmall⟩ := exists_small_sphere_in_open d U hU hzero
  let s : PlaneSphere ι → PuncturedOpen d U := fun v =>
    ⟨(smallSphereSection d t ht v).val, hsmall v,
      (smallSphereSection d t ht v).property⟩
  let j : PuncturedOpen d U → PuncturedProduct ι (Fin (d+2)) :=
    fun p => ⟨p.val,p.property.2⟩
  refine ⟨{
    sectionMap := s
    retractionMap := fun p => sphereProjection (j p)
    section_continuous := ?_
    retraction_continuous := ?_
    retraction_section := ?_ }⟩
  · exact (continuous_subtype_val.comp (continuous_smallSphereSection d t ht)).subtype_mk _
  · exact continuous_sphereProjection.comp (continuous_subtype_val.subtype_mk _)
  · intro v
    exact sphereProjection_smallSphereSection d t ht v

end GS.NonmanifoldObstruction
