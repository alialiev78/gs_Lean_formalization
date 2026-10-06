module

public import GS.Topology.SectionPair
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Actual singular homology applied to a constructed continuous retract

No homology theory is postulated here: integralHomology uses mathlib's
AlgebraicTopology.singularHomologyFunctor. The split identity, injectivity and
zero-object obstruction follow from functoriality. This does NOT compute the
homology of a sphere; that remains a separate obligation.

The coefficient category is explicitly universe zero, matching the domain of
the singular homology functor in pinned mathlib v4.19.0. ModuleCat colimits are
imported explicitly to provide the coproducts used to form singular chains.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

def retractSectionHom (p : ContinuousSectionPair A B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨p.sectionMap,p.section_continuous⟩

def retractProjectionHom (p : ContinuousSectionPair A B) : TopCat.of B ⟶ TopCat.of A :=
  TopCat.ofHom ⟨p.retractionMap,p.retraction_continuous⟩

theorem retract_comp_id (p : ContinuousSectionPair A B) :
    retractSectionHom p ≫ retractProjectionHom p = 𝟙 (TopCat.of A) := by
  ext a
  exact p.retraction_section a

/-- Categorical composition is written in application order: first s, then r. -/
theorem mapped_retract_comp_id {C : Type*} [Category C]
    (F : TopCat ⥤ C) (p : ContinuousSectionPair A B) :
    F.map (retractSectionHom p) ≫ F.map (retractProjectionHom p) =
      𝟙 (F.obj (TopCat.of A)) := by
  rw [← F.map_comp, retract_comp_id, F.map_id]

/-- A nonzero identity on the retract cannot factor through an object whose
identity is zero. No sphere computation is assumed by this lemma. -/
theorem mapped_retract_identity_nonzero {C : Type*} [Category C]
    [HasZeroMorphisms C] (F : TopCat ⥤ C) (p : ContinuousSectionPair A B)
    (hA : (𝟙 (F.obj (TopCat.of A))) ≠ 0) :
    (𝟙 (F.obj (TopCat.of B))) ≠ 0 := by
  intro hB
  apply hA
  calc
    𝟙 (F.obj (TopCat.of A)) =
        F.map (retractSectionHom p) ≫ F.map (retractProjectionHom p) :=
      (mapped_retract_comp_id F p).symm
    _ = F.map (retractSectionHom p) ≫
        (𝟙 (F.obj (TopCat.of B)) ≫ F.map (retractProjectionHom p)) := by simp
    _ = 0 := by rw [hB]; simp

/-- The actual integral singular homology functor, not a substitute interface. -/
def integralHomology (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

abbrev IntegralHomology (n : ℕ) (X : Type) [TopologicalSpace X] :=
  (integralHomology n).obj (TopCat.of X)

def homologySection (n : ℕ) (p : ContinuousSectionPair A B) :
    IntegralHomology n A ⟶ IntegralHomology n B :=
  (integralHomology n).map (retractSectionHom p)

def homologyRetraction (n : ℕ) (p : ContinuousSectionPair A B) :
    IntegralHomology n B ⟶ IntegralHomology n A :=
  (integralHomology n).map (retractProjectionHom p)

theorem homology_retraction_section (n : ℕ) (p : ContinuousSectionPair A B) :
    homologySection n p ≫ homologyRetraction n p = 𝟙 (IntegralHomology n A) :=
  mapped_retract_comp_id (integralHomology n) p

theorem homology_retraction_section_apply (n : ℕ) (p : ContinuousSectionPair A B)
    (a : IntegralHomology n A) :
    homologyRetraction n p (homologySection n p a) = a := by
  have h := homology_retraction_section n p
  exact congrArg (fun f : IntegralHomology n A ⟶ IntegralHomology n A => f a) h

theorem homologySection_injective (n : ℕ) (p : ContinuousSectionPair A B) :
    Function.Injective (homologySection n p) := by
  intro a b hab
  have h := congrArg (fun z => homologyRetraction n p z) hab
  simpa only [homology_retraction_section_apply] using h

theorem homologyRetraction_surjective (n : ℕ) (p : ContinuousSectionPair A B) :
    Function.Surjective (homologyRetraction n p) := by
  intro a
  exact ⟨homologySection n p a,homology_retraction_section_apply n p a⟩

/-- A concrete nonzero class in the source produces a nonzero class in the
punctured neighbourhood. Existence of that source class is NOT assumed globally. -/
theorem homologySection_nonzero (n : ℕ) (p : ContinuousSectionPair A B)
    (a : IntegralHomology n A) (ha : a ≠ 0) : homologySection n p a ≠ 0 := by
  intro hz
  apply ha
  apply homologySection_injective n p
  simpa using hz

theorem homology_nontrivial_of_retract (n : ℕ) (p : ContinuousSectionPair A B)
    [Nontrivial (IntegralHomology n A)] : Nontrivial (IntegralHomology n B) := by
  obtain ⟨a,b,hab⟩ := exists_pair_ne (IntegralHomology n A)
  exact ⟨⟨homologySection n p a,homologySection n p b,
    fun h => hab (homologySection_injective n p h)⟩⟩

/-- The precise contradictory configuration at the final homological step. -/
theorem no_retract_of_homology_profile (n : ℕ)
    [Nontrivial (IntegralHomology n A)] [Subsingleton (IntegralHomology n B)] :
    ¬ Nonempty (ContinuousSectionPair A B) := by
  rintro ⟨p⟩
  obtain ⟨a,b,hab⟩ := exists_pair_ne (IntegralHomology n A)
  exact hab (homologySection_injective n p
    (Subsingleton.elim (homologySection n p a) (homologySection n p b)))

end GS.NonmanifoldFinal
