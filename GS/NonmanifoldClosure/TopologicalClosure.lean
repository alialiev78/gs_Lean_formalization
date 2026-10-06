module

public import GS.Topology.PuncturedSphereObstruction
public import GS.NonmanifoldClosure.ChartRetractions
public import GS.NonmanifoldClosure.RegularConeChart
public import GS.NonmanifoldFinal.ConditionalGS
public import GS.RestrictedNonmanifold.ConditionalReduction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Unconditional topological nonmanifoldness of the cone and the GS family

The geometric retractions and charts are combined with the proved Brouwer
theorem and the proved nullhomotopy theorem for maps into larger spheres.
Neither a sphere-homology profile nor a cone-obstruction premise occurs in
the final statements. The original family and its induced topology are used.
-/

noncomputable section

open Matrix GS GS.Nonmanifold GS.NonmanifoldObstruction GS.NonmanifoldFinal
open GS.NonmanifoldClosure

namespace GS.NonmanifoldTopology

/-- Restrict an actual chart to a punctured ball and use sphere domination. -/
theorem chart_dimension_of_sphereRetractions
    {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (x : X) (hx : x ∈ c.source)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O)
    (hret : SphereRetractionsOn O x m) : n = m := by
  obtain ⟨b, hb⟩ := exists_centeredChart_within c x hx O hO hxO
  obtain ⟨p⟩ := hret b.source b.source_open b.source_point (fun _ h => (hb h).2)
  exact GS.Topology.sphere_retract_ball_dimension m n b.radius_pos
    (transportSectionPair p (Homeomorph.refl _) b.punctured)

/-- The dimensions of two overlapping Euclidean charts agree. -/
theorem dimensions_of_overlapping_charts
    {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (d : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) (hy : x ∈ d.source) : n = m := by
  exact chart_dimension_of_sphereRetractions c x hx d.source d.source_open hy
    (d.sphereRetractions x hy)

/-- No Euclidean open chart exists at the vertex, for every width d ≥ 2. -/
theorem cone_not_euclidean (e d : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAt (productZero : ConeSpace (Fin e) (Fin d)) := by
  intro hE
  obtain ⟨n, c, hc⟩ := (euclideanAt_iff_chart _).mp hE
  have hver : SphereRetractionsOn Set.univ
      (productZero : ConeSpace (Fin e) (Fin d)) ((e + 1) + 1) := by
    intro U hU h0 _
    have hp := every_punctured_cone_open_has_standard_sphere_retract
      (ι := Fin e) (κ := Fin d) (by simpa using hd) U hU h0
    have he : Fintype.card (Fin e) + 2 = (e + 1) + 1 := by rw [Fintype.card_fin]
    rw [he] at hp
    exact hp
  have hn₀ : n = (e + 1) + 1 :=
    chart_dimension_of_sphereRetractions c productZero hc Set.univ isOpen_univ
      (Set.mem_univ _) hver
  let j : Fin d := ⟨0, by omega⟩
  obtain ⟨p, hpc, hpr⟩ := exists_regular_in_open j c.source c.source_open hc
  have hn₁ := dimensions_of_overlapping_charts
    c (pivotProductChart (ι := Fin e) j) p hpc hpr
  simp only [Fintype.card_fin] at hn₁
  omega

/-- The unchanged standalone cone specification is proved without an input premise. -/
theorem coneProductNonManifold : GS.Specifications.ConeProductNonManifoldGoal := by
  intro d e hd hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) := {p | p.2.rank ≤ 1}
  have hz : ((0, 0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by simp [S]
  have hsub : EuclideanAt (⟨(0, 0), hz⟩ : S) :=
    (euclideanAtSubset_iff S (0, 0) hz).mp hE
  let h : ConeSpace (Fin e) (Fin d) ≃ₜ S := flattenConeProduct
  have hpoint : h productZero = ⟨(0, 0), hz⟩ := rfl
  apply cone_not_euclidean e d (by omega)
  apply (euclideanAt_homeomorph h productZero).mpr
  simpa only [hpoint] using hsub

/-- The requested odd-width topological obstruction, now inhabited. -/
theorem oddConeNonManifold : GS.Specifications.OddConeNonManifoldGoal :=
  GS.Specifications.oddConeNonManifold_of_general coneProductNonManifold

/-- The original all-q statement: p = 2 and every q ≥ 3. -/
theorem nonManifold : GS.Specifications.NonManifoldGoal :=
  original_nonManifold_of_cone_goal coneProductNonManifold

/-- In particular, the explicitly narrowed manuscript statement. -/
theorem restrictedNonManifold : GS.Specifications.RestrictedNonManifoldGoal :=
  GS.Specifications.restrictedNonManifold_of_general nonManifold

end GS.NonmanifoldTopology
