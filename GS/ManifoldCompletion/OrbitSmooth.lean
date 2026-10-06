module

public import GS.ManifoldCompletion.OrbitAtlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import GS.Continuation.AmbientProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth inclusion and intrinsic use of the point-only projection formula

The first result uses the constructed atlas on the actual orbit. It is not merely
smoothness with respect to factor parameters. The projector is inherited from
the checked Continuation module. Identifying its range with the image of the
manifold tangent bundle is proved separately in TangentBridge.lean.

-/

noncomputable section
set_option maxHeartbeats 800000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Continuation Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- A genuine ContMDiff statement from the orbit manifold to the ambient
matrix space. Continuity uses the inherited subtype topology. -/
theorem orbit_val_contMDiff :
    ContMDiff (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n)) ⊤
      (fun X : MatrixOrbit block₁ block₂ (permMatrix σ) => X.val) := by
  intro X
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤
    (fun x : PairModel block₁ block₂ => (orbitInverse σ (preferredFactor σ X) x).val)
    (Set.range (id : PairModel block₁ block₂ → PairModel block₁ block₂))
    (orbitCoordinates σ hno.out (preferredFactor σ X) X)
  simpa only [orbitInverse_val] using
    ((orbitParam_smooth (preferredFactor σ X) (permMatrix σ)).contDiffAt :
      ContDiffAt ℝ ⊤ (orbitParam (preferredFactor σ X) (permMatrix σ))
        (orbitCoordinates σ hno.out (preferredFactor σ X) X)).contDiffWithinAt

/-- Restricting a smooth ambient scalar loss now gives a genuine smooth function
on the constructed manifold, not an unproved interpretation of factor AD. -/
theorem ambient_loss_contMDiff (f : Mat n → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContMDiff (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, ℝ)) ⊤
      (fun X : MatrixOrbit block₁ block₂ (permMatrix σ) => f X.val) :=
  hf.comp_contMDiff (orbit_val_contMDiff σ)

/-- Joint manifold smoothness of the original point-only projector (X,Z) ↦ Π_X Z.
The tangent-space characterization is deliberately not part of this theorem. -/
theorem pointProjection_contMDiff_on_orbit :
    ContMDiff ((𝓘(ℝ, PairModel block₁ block₂)).prod (𝓘(ℝ, Mat n)))
      (𝓘(ℝ, Mat n)) ⊤
      (fun t : MatrixOrbit block₁ block₂ (permMatrix σ) × Mat n =>
        pointProjection block₁ block₂ t.1.val t.2) := by
  have hX : ContMDiff ((𝓘(ℝ, PairModel block₁ block₂)).prod (𝓘(ℝ, Mat n)))
      (𝓘(ℝ, Mat n)) ⊤
      (fun t : MatrixOrbit block₁ block₂ (permMatrix σ) × Mat n => t.1.val) :=
    (orbit_val_contMDiff σ).comp contMDiff_fst
  exact ContDiff.comp_contMDiff
    (g := fun p : Mat n × Mat n => pointProjection block₁ block₂ p.1 p.2)
    (f := fun t : MatrixOrbit block₁ block₂ (permMatrix σ) × Mat n => (t.1.val, t.2))
    (pointProjection_smooth block₁ block₂) (hX.prodMk_space contMDiff_snd)

/-- Composition with a smooth ambient vector field. -/
theorem projected_field_contMDiff (Z : Mat n → Mat n) (hZ : ContDiff ℝ ⊤ Z) :
    ContMDiff (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n)) ⊤
      (fun X : MatrixOrbit block₁ block₂ (permMatrix σ) =>
        pointProjection block₁ block₂ X.val (Z X.val)) := by
  exact ContDiff.comp_contMDiff
    (g := fun p : Mat n × Mat n => pointProjection block₁ block₂ p.1 p.2)
    (f := fun X : MatrixOrbit block₁ block₂ (permMatrix σ) => (X.val, Z X.val))
    (pointProjection_smooth block₁ block₂)
    ((orbit_val_contMDiff σ).prodMk_space
      (ContDiff.comp_contMDiff (g := Z)
        (f := fun X : MatrixOrbit block₁ block₂ (permMatrix σ) => X.val)
        hZ (orbit_val_contMDiff σ)))

/-- Fixed boundary transformations remain manifold-smooth in the matrix target.
The source charted-space topology is unchanged. -/
theorem boundary_inclusion_contMDiff (L R : Mat n) :
    ContMDiff (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n)) ⊤
      (fun X : MatrixOrbit block₁ block₂ (permMatrix σ) => L * X.val * R) := by
  have hb : ContDiff ℝ ⊤ (fun X : Mat n => L * X * R) :=
    contDiff_iff_contDiffAt.mpr (fun _ =>
      smooth_mul_at (smooth_mul_at contDiffAt_const contDiffAt_id) contDiffAt_const)
  exact hb.comp_contMDiff (orbit_val_contMDiff σ)

end GS.ManifoldCompletion
