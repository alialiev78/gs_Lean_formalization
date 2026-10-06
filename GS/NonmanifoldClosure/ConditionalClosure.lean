module

public import GS.NonmanifoldClosure.SphereProfile
public import GS.NonmanifoldClosure.RegularConeChart
public import GS.NonmanifoldFinal.ConditionalGS

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Close the cone and original GS arguments from ONE standard sphere computation

This file is CONDITIONAL on SphereHomologyProfile. It is not an unconditional
proof of either original goal. Unlike the former reduction, it contains the
entire cone argument, including chart restriction and dimension comparison.
The punctured-ball homology comparison is supplied by the proved explicit
prism construction in BallHomology; the sphere profile remains an explicit input.

No invariance-of-domain, dimension-comparison, punctured-chart-homology,
local-coverage, or nonmanifold hypotheses are added. The sole new argument is
the explicit positive-degree homology profile of Euclidean spheres.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

/-- The chart at the vertex would have dimension e+2. At a regular point of
its same open source it would have dimension e+d+1. Both conclusions are
obtained from explicit retractions and the standard sphere profile. -/
theorem cone_not_euclidean_of_sphereProfile (hS : SphereHomologyProfile)
    (e d : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAt (productZero : ConeSpace (Fin e) (Fin d)) := by
  intro hE
  obtain ⟨n,c,hc⟩ := (euclideanAt_iff_chart _).mp hE
  have hver : SphereRetractionsOn Set.univ
      (productZero : ConeSpace (Fin e) (Fin d)) ((e+1)+1) := by
    intro U hU h0 _
    have hp := every_punctured_cone_open_has_standard_sphere_retract
      (ι := Fin e) (κ := Fin d) (by simpa using hd) U hU h0
    have he : Fintype.card (Fin e) + 2 = (e + 1) + 1 := by
      rw [Fintype.card_fin]
    rw [he] at hp
    exact hp
  have hn₀ : n=(e+1)+1 :=
    chart_dimension_of_sphereRetractions hS (by omega)
      c productZero hc Set.univ isOpen_univ (Set.mem_univ _) hver
  let j : Fin d := ⟨0,by omega⟩
  obtain ⟨p,hpc,hpr⟩ := exists_regular_in_open j c.source c.source_open hc
  have hn₁ := dimensions_of_overlapping_charts hS
    (m := Fintype.card (Fin e) + Fintype.card (Fin d) + 1)
    (by simp only [Fintype.card_fin]; omega)
    c (pivotProductChart (ι := Fin e) j) p hpc hpr
  simp only [Fintype.card_fin] at hn₁
  omega

/-- The standalone OLD cone specification, still with the explicit sphere-profile argument. -/
theorem coneProductNonManifold_of_sphereProfile (hS : SphereHomologyProfile) :
    GS.Specifications.ConeProductNonManifoldGoal := by
  intro d e hd hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) := {p | p.2.rank ≤ 1}
  have hz : ((0,0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by simp [S]
  have hsub : EuclideanAt (⟨(0,0),hz⟩ : S) :=
    (euclideanAtSubset_iff S (0,0) hz).mp hE
  let h : ConeSpace (Fin e) (Fin d) ≃ₜ S := flattenConeProduct
  have hpoint : h productZero = ⟨(0,0),hz⟩ := rfl
  apply cone_not_euclidean_of_sphereProfile hS e d (by omega)
  apply (euclideanAt_homeomorph h productZero).mpr
  simpa only [hpoint] using hsub

/-- Exact original matrix-family conclusion under the standard sphere-profile input.
Do NOT report this as unconditional: hS is not supplied by this project. -/
theorem original_nonManifold_of_sphereProfile (hS : SphereHomologyProfile) :
    GS.Specifications.NonManifoldGoal :=
  original_nonManifold_of_cone_goal (coneProductNonManifold_of_sphereProfile hS)

end GS.NonmanifoldClosure
