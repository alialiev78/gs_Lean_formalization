module

public import GS.NonmanifoldFinal.RetractTransport
public import GS.NonmanifoldFinal.HomologyRetracts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Singular homology of the constructed retract of each punctured cone neighbourhood

These conclusions concern the ACTUAL mathlib singular homology functor and the
ACTUAL rank-constrained matrix subset. They assert a split injection, not the
still missing computation of homology groups of spheres or Euclidean balls.
-/
noncomputable section
open CategoryTheory GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- For every degree, exhibit both induced morphisms and their exact composite. -/
theorem punctured_cone_homology_split (n : ℕ) (hκ : 2 ≤ Fintype.card κ)
    (U : Set (ConeSpace ι κ)) (hU : IsOpen U) (hzero : productZero ∈ U) :
    ∃ (s : IntegralHomology n (UnitSphere (Fin (Fintype.card ι + 2))) ⟶
        IntegralHomology n (PuncturedIn U productZero))
      (r : IntegralHomology n (PuncturedIn U productZero) ⟶
        IntegralHomology n (UnitSphere (Fin (Fintype.card ι + 2)))),
      s ≫ r = 𝟙 _ := by
  obtain ⟨p⟩ := every_punctured_cone_open_has_standard_sphere_retract hκ U hU hzero
  exact ⟨homologySection n p,homologyRetraction n p,homology_retraction_section n p⟩

/-- Nonvanishing propagates from the standard sphere. The source nonvanishing
is explicit and is NOT a theorem proved by this continuation. -/
theorem punctured_cone_homology_nontrivial (n : ℕ)
    (hκ : 2 ≤ Fintype.card κ) (U : Set (ConeSpace ι κ))
    (hU : IsOpen U) (hzero : productZero ∈ U)
    [Nontrivial (IntegralHomology n (UnitSphere (Fin (Fintype.card ι + 2))))] :
    Nontrivial (IntegralHomology n (PuncturedIn U productZero)) := by
  obtain ⟨p⟩ := every_punctured_cone_open_has_standard_sphere_retract hκ U hU hzero
  exact homology_nontrivial_of_retract n p

/-- A checked sphere computation and a checked punctured-chart vanishing
would contradict each other. Both missing inputs are kept visibly explicit. -/
theorem punctured_cone_no_zero_homology (n : ℕ)
    (hκ : 2 ≤ Fintype.card κ) (U : Set (ConeSpace ι κ))
    (hU : IsOpen U) (hzero : productZero ∈ U)
    [Nontrivial (IntegralHomology n (UnitSphere (Fin (Fintype.card ι + 2))))] :
    ¬ Subsingleton (IntegralHomology n (PuncturedIn U productZero)) := by
  intro hzeroHomology
  letI := hzeroHomology
  exact no_retract_of_homology_profile n
    (every_punctured_cone_open_has_standard_sphere_retract hκ U hU hzero)

end GS.NonmanifoldFinal
