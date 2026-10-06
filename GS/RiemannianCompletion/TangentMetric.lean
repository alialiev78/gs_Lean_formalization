module

public import GS.RiemannianCompletion.FrobeniusDual
public import GS.ManifoldCompletion.TangentBridge
public import Mathlib.LinearAlgebra.BilinearForm.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Frobenius pullback on the actual mathlib tangent spaces

The topology and atlas are the ones in ManifoldCompletion. No new notion of
"tangent space" is declared. The metric is the pullback of the explicit
Frobenius pairing by the actual mfderiv of the inclusion. We prove positivity,
linearity, and the intrinsic characterization of the existing projector.

This file deliberately does NOT install a normed or inner-product instance on
TangentSpace: its chart-model norm is not the induced Frobenius norm. A smooth
bundle metric evaluation is proved in `GS.GlobalGeometry.TangentBundleMetric`.
The intrinsic length distance is not constructed here.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- Only an abbreviation for mathlib's actual manifold differential. -/
def inclusionDifferential (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X →L[ℝ] Mat n :=
  mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
    (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X

theorem inclusionDifferential_injective (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    Function.Injective (inclusionDifferential σ X) :=
  orbit_val_mfderiv_injective σ X

/-- The requested metric, evaluated on the actual tangent space. -/
def tangentPairing (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) : ℝ :=
  frobInner (inclusionDifferential σ X v) (inclusionDifferential σ X w)

theorem tangentPairing_symm (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X v w = tangentPairing σ X w v :=
  frobInner_comm _ _

theorem tangentPairing_add_left (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (u v w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X (u + v) w = tangentPairing σ X u w + tangentPairing σ X v w := by
  simp only [tangentPairing, map_add, frobInner_add_left]

theorem tangentPairing_add_right (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (u v w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X u (v + w) = tangentPairing σ X u v + tangentPairing σ X u w := by
  simp only [tangentPairing, map_add, frobInner_add_right]

theorem tangentPairing_smul_left (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (a : ℝ) (v w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X (a • v) w = a * tangentPairing σ X v w := by
  simp only [tangentPairing, map_smul, frobInner_smul_left]

theorem tangentPairing_smul_right (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (a : ℝ) (v w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X v (a • w) = a * tangentPairing σ X v w := by
  simp only [tangentPairing, map_smul, frobInner_smul_right]

@[simp] theorem tangentPairing_zero_left (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X 0 v = 0 := by simp [tangentPairing]

@[simp] theorem tangentPairing_zero_right (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X v 0 = 0 := by simp [tangentPairing]

theorem tangentPairing_self_nonneg (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    0 ≤ tangentPairing σ X v v := frobSq_nonneg _

theorem tangentPairing_self_eq_zero_iff (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X v v = 0 ↔ v = 0 := by
  change frobSq (inclusionDifferential σ X v) = 0 ↔ v = 0
  rw [frobSq_eq_zero_iff]
  constructor
  · intro h
    apply inclusionDifferential_injective σ X
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

theorem tangentPairing_pos (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (hv : v ≠ 0) :
    0 < tangentPairing σ X v v := by
  apply frobSq_pos_of_ne_zero
  intro h
  apply hv
  apply inclusionDifferential_injective σ X
  simpa only [map_zero] using h

/-- A real BilinForm, not a new metric axiom or a replacement tangent type. -/
def tangentMetric (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    LinearMap.BilinForm ℝ (TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) where
  toFun v :=
    { toFun := tangentPairing σ X v
      map_add' := tangentPairing_add_right σ X v
      map_smul' := fun a w => tangentPairing_smul_right σ X a v w }
  map_add' u v := by
    ext w
    exact tangentPairing_add_left σ X u v w
  map_smul' a v := by
    ext w
    exact tangentPairing_smul_left σ X a v w

/-- The factor 4 is essential: the chosen Cayley chart has derivative -2 id. -/
theorem tangentPairing_self_coordinates
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X v v = 4 * (frobSq v.1.val + frobSq v.2.val) := by
  change frobSq (inclusionDifferential σ X v) = _
  unfold inclusionDifferential
  rw [orbit_val_mfderiv_eq]
  have he := orbitParam_fderiv_zero_frobSq σ hno.out (preferredFactor σ X) v
  rw [frobSq_smul, frobSq_smul] at he
  convert he using 1 <;> ring

/-- A canonical tangent lift exists because the already-defined point projector
lands in the actual differential image. No choice of a new factorization is made. -/
def tangentProjection (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n) :
    TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X :=
  Classical.choose (pointProjection_unique_tangent_lift σ X Z)

@[simp] theorem inclusion_tangentProjection
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n) :
    inclusionDifferential σ X (tangentProjection σ X Z) =
      pointProjection block₁ block₂ X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift σ X Z)).1

theorem pointProjection_pairing_tangent
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    frobInner (pointProjection block₁ block₂ X.val Z) (inclusionDifferential σ X v) =
      frobInner Z (inclusionDifferential σ X v) := by
  have hfix : pointProjection block₁ block₂ X.val (inclusionDifferential σ X v) =
      inclusionDifferential σ X v :=
    (pointProjection_fixed_iff_tangent_image σ X _).mpr ⟨v, rfl⟩
  have hadj := pointProjection_self_adjoint block₁ block₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z
    (inclusionDifferential σ X v)
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose
  dsimp only at hadj
  rw [preferredFactor_product σ X, hfix] at hadj
  exact hadj

/-- The intrinsic Riesz identity for projecting an ambient Frobenius covector. -/
theorem tangentProjection_pairing
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentPairing σ X (tangentProjection σ X Z) v =
      frobInner Z (inclusionDifferential σ X v) := by
  unfold tangentPairing
  rw [inclusion_tangentProjection]
  exact pointProjection_pairing_tangent σ X Z v

/-- Uniqueness follows from positive definiteness, not from declaring this
identity to be a definition of the gradient. -/
theorem tangentProjection_unique
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n)
    (w : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X)
    (hw : ∀ v, tangentPairing σ X w v = frobInner Z (inclusionDifferential σ X v)) :
    w = tangentProjection σ X Z := by
  have h := hw (w - tangentProjection σ X Z)
  have hg := tangentProjection_pairing σ X Z (w - tangentProjection σ X Z)
  apply sub_eq_zero.mp
  apply (tangentPairing_self_eq_zero_iff σ X _).mp
  change frobInner (inclusionDifferential σ X (w - tangentProjection σ X Z)) _ = 0
  rw [map_sub, frobInner_sub_left]
  apply sub_eq_zero.mpr
  simpa only [tangentPairing, map_sub] using h.trans hg.symm

@[simp] theorem tangentProjection_of_tangent
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    tangentProjection σ X (inclusionDifferential σ X v) = v := by
  apply inclusionDifferential_injective σ X
  rw [inclusion_tangentProjection]
  exact (pointProjection_fixed_iff_tangent_image σ X _).mpr ⟨v, rfl⟩

/-- Linear dependence on the ambient vector, derived from the Riesz identity. -/
theorem tangentProjection_add (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z W : Mat n) :
    tangentProjection σ X (Z + W) = tangentProjection σ X Z + tangentProjection σ X W := by
  symm
  apply tangentProjection_unique σ X (Z + W)
  intro v
  rw [tangentPairing_add_left, tangentProjection_pairing, tangentProjection_pairing,
    frobInner_add_left]

theorem tangentProjection_smul (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (a : ℝ) (Z : Mat n) :
    tangentProjection σ X (a • Z) = a • tangentProjection σ X Z := by
  symm
  apply tangentProjection_unique σ X (a • Z)
  intro v
  rw [tangentPairing_smul_left, tangentProjection_pairing, frobInner_smul_left]

@[simp] theorem tangentProjection_zero (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    tangentProjection σ X (0 : Mat n) = 0 := by
  symm
  apply tangentProjection_unique σ X 0
  intro v
  simp

/-- Actual continuous linear map into each original tangent fiber. The result
is fiberwise; this declaration alone does not assert smoothness of the bundle map. -/
def tangentProjectionLinear (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    Mat n →ₗ[ℝ] TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X where
  toFun := tangentProjection σ X
  map_add' := tangentProjection_add σ X
  map_smul' := tangentProjection_smul σ X

def tangentProjectionCLM (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    Mat n →L[ℝ] TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X :=
  (tangentProjectionLinear σ X).toContinuousLinearMap

end GS.RiemannianCompletion
