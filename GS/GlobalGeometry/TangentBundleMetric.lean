module

public import GS.GlobalGeometry.MetricTopology
public import GS.ManifoldCompletion.OrbitSmooth
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth Frobenius metric on the actual tangent bundle

The existing construction provides a positive definite bilinear form on each
mathlib `TangentSpace`. This module closes the global smoothness step: its
evaluation extends to a smooth scalar function on the product of two actual
tangent bundles. Restricting both arguments to the same fibre recovers exactly
`tangentPairing`. In particular, the energy is smooth on the total tangent bundle.

The proof uses the smooth tangent map of the inclusion. It does not require a
smooth choice of orthogonal factors or a new definition of tangent space.
Mathlib v4.19 does not provide a `RiemannianMetric` structure to register; all
statements here use that version's standard manifold and tangent-bundle types.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open GS.RiemannianCompletion
open scoped Manifold Topology

namespace GS.GlobalGeometry

variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- Ambient realization of a vector in the genuine total tangent bundle. -/
def tangentAmbient
    (p : TangentBundle (𝓘(ℝ, PairModel b₁ b₂)) (MatrixOrbit b₁ b₂ (permMatrix σ))) :
    Mat n :=
  inclusionDifferential σ p.proj p.2

/-- Smoothness includes dependence on both the base point and the tangent vector. -/
theorem tangentAmbient_contMDiff :
    ContMDiff (𝓘(ℝ, PairModel b₁ b₂)).tangent (𝓘(ℝ, Mat n)) ⊤
      (tangentAmbient (b₁ := b₁) (b₂ := b₂) σ) := by
  exact (contMDiff_snd_tangentBundle_modelSpace (Mat n) (𝓘(ℝ, Mat n))).comp
    ((orbit_val_contMDiff (block₁ := b₁) (block₂ := b₂) σ).contMDiff_tangentMap (by simp))

/-- A smooth extension of the metric evaluation, even for different base points. -/
def tangentMetricExtension
    (p : TangentBundle (𝓘(ℝ, PairModel b₁ b₂)) (MatrixOrbit b₁ b₂ (permMatrix σ)) ×
      TangentBundle (𝓘(ℝ, PairModel b₁ b₂)) (MatrixOrbit b₁ b₂ (permMatrix σ))) : ℝ :=
  frobInner (tangentAmbient σ p.1) (tangentAmbient σ p.2)

set_option maxHeartbeats 800000 in
theorem tangentMetricExtension_contMDiff :
    ContMDiff ((𝓘(ℝ, PairModel b₁ b₂)).tangent.prod
      (𝓘(ℝ, PairModel b₁ b₂)).tangent) (𝓘(ℝ, ℝ)) ⊤
      (tangentMetricExtension (b₁ := b₁) (b₂ := b₂) σ) := by
  exact frobInner_smooth.comp_contMDiff
    (((tangentAmbient_contMDiff (b₁ := b₁) (b₂ := b₂) σ).comp
      contMDiff_fst).prodMk_space
      ((tangentAmbient_contMDiff (b₁ := b₁) (b₂ := b₂) σ).comp contMDiff_snd))

@[simp] theorem tangentMetricExtension_same_base
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) :
    tangentMetricExtension σ (⟨X, v⟩, ⟨X, w⟩) = tangentPairing σ X v w := rfl

/-- Squared metric norm, expressed without installing a conflicting chart norm. -/
def tangentEnergy
    (p : TangentBundle (𝓘(ℝ, PairModel b₁ b₂)) (MatrixOrbit b₁ b₂ (permMatrix σ))) :
    ℝ :=
  tangentPairing σ p.proj p.2 p.2

set_option maxHeartbeats 800000 in
theorem tangentEnergy_contMDiff :
    ContMDiff (𝓘(ℝ, PairModel b₁ b₂)).tangent (𝓘(ℝ, ℝ)) ⊤
      (tangentEnergy (b₁ := b₁) (b₂ := b₂) σ) := by
  exact frobInner_smooth.comp_contMDiff
    (g := fun q : Mat n × Mat n => frobInner q.1 q.2)
    (f := fun p : TangentBundle (𝓘(ℝ, PairModel b₁ b₂))
      (MatrixOrbit b₁ b₂ (permMatrix σ)) => (tangentAmbient σ p, tangentAmbient σ p))
    ((tangentAmbient_contMDiff (b₁ := b₁) (b₂ := b₂) σ).prodMk_space
      (tangentAmbient_contMDiff (b₁ := b₁) (b₂ := b₂) σ))

@[simp] theorem tangentEnergy_eq_zero_iff
    (p : TangentBundle (𝓘(ℝ, PairModel b₁ b₂)) (MatrixOrbit b₁ b₂ (permMatrix σ))) :
    tangentEnergy σ p = 0 ↔ p.2 = 0 :=
  tangentPairing_self_eq_zero_iff σ p.proj p.2

theorem tangentEnergy_pos
    (p : TangentBundle (𝓘(ℝ, PairModel b₁ b₂)) (MatrixOrbit b₁ b₂ (permMatrix σ)))
    (hp : p.2 ≠ 0) : 0 < tangentEnergy σ p :=
  tangentPairing_pos σ p.proj p.2 hp

end GS.GlobalGeometry
