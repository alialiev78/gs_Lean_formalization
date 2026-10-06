module

public import GS.ManifoldCompletion.OrbitDifferential
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual manifold differential of the inclusion

This is the bridge from the constructed orbit atlas to mathlib's mfderiv and
TangentSpace. We unfold the library derivative in the preferred charts; we do
NOT define a substitute tangent space by the formula to be proved. The one
API-sensitive reduction is isolated in orbit_val_mfderiv_eq.

All results require NoOffDiagonalOverlap. None addresses the positive-dimensional
stabilizer case. 
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

@[simp] theorem orbitCoordinates_base (g : FactorGroup block₁ block₂) :
    orbitCoordinates σ hno.out g (orbitMapToOrbit block₁ block₂ (permMatrix σ) g) = 0 := by
  rw [orbitCoordinates_on_factors σ hno.out g g (base_mem_orbitFactorSource g)]
  simp [factorCoordinates]

@[simp] theorem orbitCoordinates_preferred
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    orbitCoordinates σ hno.out (preferredFactor σ X) X = 0 := by
  have he := orbitCoordinates_base σ (preferredFactor σ X)
  simpa only [preferredFactor_spec] using he

/-- Identify mathlib's actual manifold derivative with the Frechet derivative
of the explicit inverse chart. TangentSpace is the library model at the chosen
point, not a newly declared space. -/
theorem orbit_val_mfderiv_eq (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X =
        fderiv ℝ (orbitParam (preferredFactor σ X) (permMatrix σ)) 0 := by
  classical
  have hd : MDifferentiableAt (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X := by
    rw [mdifferentiableAt_iff]
    refine ⟨continuous_subtype_val.continuousAt, ?_⟩
    change DifferentiableWithinAt ℝ
      (fun x : PairModel block₁ block₂ => (orbitInverse σ (preferredFactor σ X) x).val)
      (Set.range (id : PairModel block₁ block₂ → PairModel block₁ block₂))
      (orbitCoordinates σ hno.out (preferredFactor σ X) X)
    simpa only [orbitInverse_val, orbitCoordinates_preferred] using
      ((orbitParam_smooth (preferredFactor σ X) (permMatrix σ)).differentiable
        (by simp) (0 : PairModel block₁ block₂)).differentiableWithinAt
  unfold mfderiv
  rw [if_pos hd]
  change fderivWithin ℝ
      (fun x : PairModel block₁ block₂ => (orbitInverse σ (preferredFactor σ X) x).val)
      (Set.range (id : PairModel block₁ block₂ → PairModel block₁ block₂))
      (orbitCoordinates σ hno.out (preferredFactor σ X) X) = _
  simp only [orbitInverse_val, orbitCoordinates_preferred, Set.range_id, fderivWithin_univ]

/-- The derivative of the smooth inclusion is injective at EVERY point. -/
theorem orbit_val_mfderiv_injective (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    Function.Injective (mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X) := by
  rw [orbit_val_mfderiv_eq]
  exact orbitParam_fderiv_zero_injective σ hno.out (preferredFactor σ X)

/-- The old generator image is now identified with the image of the ACTUAL
manifold tangent space under the inclusion derivative. -/
theorem orbit_tangent_image_iff (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n) :
    (∃ v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X,
      mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X v = Z) ↔
      TwoFactorDirection block₁ block₂ (preferredFactor σ X).1.val (permMatrix σ)
        (preferredFactor σ X).2.valᵀ Z := by
  rw [orbit_val_mfderiv_eq]
  exact orbitParam_fderiv_zero_range (preferredFactor σ X) (permMatrix σ) Z

/-- The preferred factors reconstruct the underlying matrix, with the correct
transpose convention on the right factor. -/
theorem preferredFactor_product (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    product2 (preferredFactor σ X).1.val (permMatrix σ) (preferredFactor σ X).2.valᵀ =
      X.val := by
  exact congrArg Subtype.val (preferredFactor_spec σ X)

/-- No new definition of tangent space: this is a statement about the library
mfderiv from the library TangentSpace of the constructed manifold. -/
theorem pointProjection_fixed_iff_tangent_image
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n) :
    pointProjection block₁ block₂ X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X,
        mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
          (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff]
  rw [← preferredFactor_product σ X]
  exact pointProjection_fixed_iff block₁ block₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose

/-- Existence and uniqueness of the intrinsic tangent vector represented by
an output of the point-only orthogonal projector. -/
theorem pointProjection_unique_tangent_lift
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n) :
    ∃! v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X,
      mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit block₁ block₂ (permMatrix σ) => Y.val) X v =
          pointProjection block₁ block₂ X.val Z := by
  have hid : pointProjection block₁ block₂ X.val
      (pointProjection block₁ block₂ X.val Z) = pointProjection block₁ block₂ X.val Z := by
    rw [← preferredFactor_product σ X]
    exact pointProjection_idempotent block₁ block₂ σ
      (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z
      (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
      (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose
  obtain ⟨v, hv⟩ := (pointProjection_fixed_iff_tangent_image σ X _).mp hid
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact orbit_val_mfderiv_injective σ X (hw.trans hv.symm)

/-- Least-squares certificate against every actual tangent vector. The norm is
explicitly Frobenius, not mathlib's default matrix sup norm. -/
theorem pointProjection_pythagorean_tangent
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    let Y : Mat n := mfderiv (𝓘(ℝ, PairModel block₁ block₂)) (𝓘(ℝ, Mat n))
      (fun W : MatrixOrbit block₁ block₂ (permMatrix σ) => W.val) X v
    frobSq (Z - Y) = frobSq (Z - pointProjection block₁ block₂ X.val Z) +
      frobSq (pointProjection block₁ block₂ X.val Z - Y) := by
  dsimp only
  have hY := (orbit_tangent_image_iff σ X _).mp ⟨v, rfl⟩
  have hp := pointProjection_pythagorean block₁ block₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z _
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose hY
  simpa only [preferredFactor_product] using hp

end GS.ManifoldCompletion
