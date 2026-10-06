module

public import GS.NonmanifoldClosure.PuncturedBall
public import GS.NonmanifoldFinal.HomologyRetracts
public import GS.Topology.EuclideanSphere
public import GS.Topology.SingularHomotopy

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Homology of a punctured norm-ball via explicit maps

No homology computation for spheres is assumed in this file. The two maps
from PuncturedBall are inverse on homology by a constructed homotopy.
The singular homology functor is the existing mathlib functor.

Homotopy invariance is proved in `GS.Topology.SingularHomotopy` by an explicit
prism construction and chain homotopy. This works with the pinned mathlib v4.19.0
and does not assume a homology computation for spheres.
-/
noncomputable section
open CategoryTheory GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

/-- Isolate the library homotopy-invariance interface in a single lemma. -/
theorem integralHomology_map_homotopy (n : ℕ)
    {f g : TopCat.of A ⟶ TopCat.of B} (h : ContinuousMap.Homotopy f.hom g.hom) :
    (integralHomology n).map f = (integralHomology n).map g := by
  exact GS.Topology.SingularHomotopy.singularHomology_map_eq h (ModuleCat.of ℤ ℤ) n

/-- An actual homeomorphism, not merely continuous maps, yields a homology iso. -/
def homologyHomeomorphIso (n : ℕ) (h : A ≃ₜ B) :
    IntegralHomology n A ≅ IntegralHomology n B where
  hom := (integralHomology n).map (TopCat.ofHom ⟨h,h.continuous⟩)
  inv := (integralHomology n).map (TopCat.ofHom ⟨h.symm,h.symm.continuous⟩)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have he : (TopCat.ofHom ⟨h,h.continuous⟩ : TopCat.of A ⟶ TopCat.of B) ≫
        TopCat.ofHom ⟨h.symm,h.symm.continuous⟩ = 𝟙 _ := by
      ext x
      exact h.symm_apply_apply x
    rw [he, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp]
    have he : (TopCat.ofHom ⟨h.symm,h.symm.continuous⟩ : TopCat.of B ⟶ TopCat.of A) ≫
        TopCat.ofHom ⟨h,h.continuous⟩ = 𝟙 _ := by
      ext x
      exact h.apply_symm_apply x
    rw [he, CategoryTheory.Functor.map_id]

/-- Pull back subsingleton homology along an isomorphism using its inverse. -/
theorem subsingleton_of_homologyIso {M N : ModuleCat ℤ} (i : M ≅ N)
    [Subsingleton N] : Subsingleton M := by
  refine ⟨fun x y => ?_⟩
  have h : i.hom x = i.hom y := Subsingleton.elim _ _
  have hh := congrArg (fun z => i.inv z) h
  have hleft (z : M) : i.inv (i.hom z) = z := by
    exact congrArg (fun f : M ⟶ M => f z) i.hom_inv_id
  simpa only [hleft] using hh

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalization followed by the radius-r/2 inclusion induces the identity
on ball homology, because puncturedBallHomotopy is an actual homotopy. -/
theorem ball_homology_other_inverse (n : ℕ) {r : ℝ} (hr : 0 < r) :
    homologyRetraction n (ballSectionPair (E := E) hr) ≫
      homologySection n (ballSectionPair (E := E) hr) =
        𝟙 (IntegralHomology n (PuncturedNormBall E r)) := by
  rw [homologyRetraction, homologySection, ← Functor.map_comp]
  have h : ContinuousMap.Homotopy
      (retractProjectionHom (ballSectionPair (E := E) hr) ≫
        retractSectionHom (ballSectionPair (E := E) hr)).hom
      (TopCat.Hom.hom (𝟙 (TopCat.of (PuncturedNormBall E r)))) := puncturedBallHomotopy hr
  rw [integralHomology_map_homotopy n h, CategoryTheory.Functor.map_id]

/-- The homology of a punctured ball is isomorphic to that of its unit sphere.
This is valid in ambient dimension 0 or 1 as well. -/
def puncturedBallHomologyIso (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegralHomology n (PuncturedNormBall E r) ≅ IntegralHomology n (NormSphere E) where
  hom := homologyRetraction n (ballSectionPair hr)
  inv := homologySection n (ballSectionPair hr)
  hom_inv_id := ball_homology_other_inverse n hr
  inv_hom_id := homology_retraction_section n (ballSectionPair hr)

/-- A public isomorphism for the specified sphere type. -/
def standardPuncturedBallHomologyIso (k n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegralHomology k (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) ≅
      IntegralHomology k (UnitSphere (Fin n)) :=
  (puncturedBallHomologyIso k hr).trans (homologyHomeomorphIso k (normSphereStandard n))

end GS.NonmanifoldClosure
