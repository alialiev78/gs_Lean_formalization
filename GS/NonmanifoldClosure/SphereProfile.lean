module

public import GS.NonmanifoldClosure.ChartRetractions
public import GS.NonmanifoldClosure.BallHomology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# An optional sphere-homology input for the homological proof route

SphereHomologyProfile is an EXPLICIT UNPROVED INPUT, not an axiom or an
instance installed in the environment. No inhabitant is supplied in this project.
It refers to actual integral singular homology of actual Euclidean unit spheres.
All theorems in this file visibly retain it as an argument.

The imported BallHomology module now proves homotopy invariance and the
punctured-ball homology isomorphism on pinned mathlib v4.19.0. The explicit
sphere computation remains optional input for this homological proof route.

Only positive-degree homology is needed. No homology rank, relative homology,
excision, invariance of domain, or separate invariance-of-dimension hypothesis
is used by the chart comparison below.
-/
noncomputable section
open CategoryTheory GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

/-- Ambient size of UnitSphere(Fin n) is n, so the top degree is n-1.
This structure is an obligation to be proved, not a new mathematical axiom. -/
structure SphereHomologyProfile : Prop where
  top_nontrivial : ∀ k : ℕ, 0 < k →
    Nontrivial (IntegralHomology k (UnitSphere (Fin (k+1))))
  off_top_subsingleton : ∀ n k : ℕ, 0 < k → k+1 ≠ n →
    Subsingleton (IntegralHomology k (UnitSphere (Fin n)))

/-- If S^k retracts from a punctured n-ball, its nonzero top homology forces
n=k+1. Dimension 0 and dimension 1 are covered by the same positive-degree argument. -/
theorem sphere_retract_ball_dimension (hS : SphereHomologyProfile)
    (k n : ℕ) (hk : 0 < k) {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin (k+1)))
      (PuncturedNormBall (Eucl n) r)) : n = k+1 := by
  by_contra hn
  letI : Nontrivial (IntegralHomology k (UnitSphere (Fin (k+1)))) :=
    hS.top_nontrivial k hk
  letI : Subsingleton (IntegralHomology k (UnitSphere (Fin n))) :=
    hS.off_top_subsingleton n k hk (Ne.symm hn)
  letI : Subsingleton (IntegralHomology k (PuncturedNormBall (Eucl n) r)) :=
    subsingleton_of_homologyIso (standardPuncturedBallHomologyIso k n hr)
  exact no_retract_of_homology_profile k ⟨p⟩

/-- Restrict a GIVEN n-dimensional chart to a ball inside O, apply the actual
retraction there, and transport it through the punctured chart. -/
theorem chart_dimension_of_sphereRetractions (hS : SphereHomologyProfile)
    {X : Type} [TopologicalSpace X] {k n : ℕ} (hk : 0 < k)
    (c : OpenEuclideanChart X n) (x : X) (hx : x ∈ c.source)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O)
    (hret : SphereRetractionsOn O x (k+1)) : n = k+1 := by
  obtain ⟨b,hb⟩ := exists_centeredChart_within c x hx O hO hxO
  obtain ⟨p⟩ := hret b.source b.source_open b.source_point (fun _ h => (hb h).2)
  exact sphere_retract_ball_dimension hS k n hk b.radius_pos
    (transportSectionPair p (Homeomorph.refl _) b.punctured)

/-- Dimension agreement follows from the sphere profile, rather than being an
additional input about arbitrary homeomorphisms between Euclidean open sets. -/
theorem dimensions_of_overlapping_charts (hS : SphereHomologyProfile)
    {X : Type} [TopologicalSpace X] {m n : ℕ} (hm : 2 ≤ m)
    (c : OpenEuclideanChart X n) (d : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) (hy : x ∈ d.source) : n = m := by
  have h : (m-1)+1=m := by omega
  have hr : SphereRetractionsOn d.source x ((m-1)+1) := by
    simpa only [h] using d.sphereRetractions x hy
  have he := chart_dimension_of_sphereRetractions hS (k := m-1) (by omega)
    c x hx d.source d.source_open hy hr
  simpa only [h] using he

end GS.NonmanifoldClosure
