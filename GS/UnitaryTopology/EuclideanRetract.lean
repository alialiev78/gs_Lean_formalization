module

public import GS.NonmanifoldObstruction.PuncturedNeighbourhood
public import GS.NonmanifoldClosure.TopologicalClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Isolated-zero Euclidean retracts and punctured neighbourhoods

A continuous Euclidean retract whose projection vanishes only at the marked
point produces a sphere retract in every punctured open neighbourhood. This
criterion is applicable to Clifford contractions of rank-one matrix cones.
-/
noncomputable section
open GS.NonmanifoldObstruction GS.NonmanifoldFinal GS.NonmanifoldClosure
open scoped Topology
namespace GS.UnitaryTopology

structure IsolatedEuclideanRetract (X : Type*) [TopologicalSpace X]
    (x₀ : X) (m : ℕ) where
  sectionMap : Eucl m → X
  projectionMap : X → Eucl m
  section_continuous : Continuous sectionMap
  projection_continuous : Continuous projectionMap
  projection_section : ∀ x, projectionMap (sectionMap x) = x
  section_zero : sectionMap 0 = x₀
  projection_zero_iff : ∀ x, projectionMap x = 0 ↔ x = x₀

variable {X : Type} [TopologicalSpace X] {x₀ : X} {m : ℕ}

theorem IsolatedEuclideanRetract.punctured_sphere
    (r : IsolatedEuclideanRetract X x₀ m)
    (U : Set X) (hU : IsOpen U) (hx : x₀ ∈ U) :
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x₀)) := by
  let F : ℝ × UnitSphere (Fin m) → X := fun p => r.sectionMap (p.1 • p.2.val)
  have hF : Continuous F := r.section_continuous.comp
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V,hV,h0,hVsub⟩ := uniform_neighbourhood_of_compact_parameter F hF 0 U hU
    (fun v => by simpa [F,r.section_zero] using hx)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  let t := δ/2
  have ht : 0<t := by dsimp [t]; positivity
  have htV : t ∈ V := hball (by
    change dist (δ/2) 0 < δ
    rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<δ/2)]
    linarith)
  have hnorm (v : UnitSphere (Fin m)) : ‖v.val‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using v.property
  let s : UnitSphere (Fin m) → PuncturedIn U x₀ := fun v =>
    ⟨r.sectionMap (t • v.val), hVsub t htV v, by
      intro he
      have hp := congrArg r.projectionMap he
      rw [r.projection_section, (r.projection_zero_iff x₀).mpr rfl] at hp
      have hn := congrArg norm hp
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hnorm v,mul_one,norm_zero] at hn
      exact (ne_of_gt ht) hn⟩
  have hne (p : PuncturedIn U x₀) : r.projectionMap p.val ≠ 0 :=
    fun he => p.property.2 ((r.projection_zero_iff p.val).mp he)
  let p : PuncturedIn U x₀ → UnitSphere (Fin m) := fun x =>
    ⟨‖r.projectionMap x.val‖⁻¹ • r.projectionMap x.val, by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hne x))),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne x))]⟩
  refine ⟨{
    sectionMap := s
    retractionMap := p
    section_continuous := ?_
    retraction_continuous := ?_
    retraction_section := ?_ }⟩
  · exact (r.section_continuous.comp
      (continuous_subtype_val.const_smul t)).subtype_mk _
  · apply Continuous.subtype_mk
    exact (((r.projection_continuous.comp continuous_subtype_val).norm).inv₀
      (fun x => norm_ne_zero_iff.mpr (hne x))).smul
      (r.projection_continuous.comp continuous_subtype_val)
  · intro v
    apply Subtype.ext
    change ‖r.projectionMap (r.sectionMap (t • v.val))‖⁻¹ •
      r.projectionMap (r.sectionMap (t • v.val)) = v.val
    rw [r.projection_section,norm_smul,Real.norm_eq_abs,abs_of_pos ht,
      hnorm v,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul]

theorem IsolatedEuclideanRetract.chart_dimension
    (r : IsolatedEuclideanRetract X x₀ m) {n : ℕ}
    (c : OpenEuclideanChart X n) (hc : x₀ ∈ c.source) : n=m := by
  apply GS.NonmanifoldTopology.chart_dimension_of_sphereRetractions
    c x₀ hc Set.univ isOpen_univ (Set.mem_univ _)
  intro U hU hx _
  exact r.punctured_sphere U hU hx

/-- A regular chart of another dimension in every vertex neighbourhood excludes
a Euclidean chart at the vertex. Both ingredients are explicit geometric data. -/
theorem not_euclidean_of_retract_regular_charts
    (r : IsolatedEuclideanRetract X x₀ m) (k : ℕ) (hmk : m ≠ k)
    (hregular : ∀ U : Set X, IsOpen U → x₀ ∈ U →
      ∃ c : OpenEuclideanChart X k, ∃ x : X, x ∈ U ∧ x ∈ c.source) :
    ¬ EuclideanAt x₀ := by
  intro he
  obtain ⟨n,c,hc⟩ := (euclideanAt_iff_chart x₀).mp he
  have hn := r.chart_dimension c hc
  obtain ⟨d,x,hxc,hxd⟩ := hregular c.source c.source_open hc
  have hnk := GS.NonmanifoldTopology.dimensions_of_overlapping_charts c d x hxc hxd
  exact hmk (hn.symm.trans hnk)

end GS.UnitaryTopology
