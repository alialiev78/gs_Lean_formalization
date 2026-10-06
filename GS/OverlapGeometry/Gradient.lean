module

public import GS.OverlapGeometry.TangentBridge
public import GS.OverlapGeometry.Riemannian
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The intrinsic gradient with arbitrary overlap

The ambient orthogonal projector is lifted into the actual tangent space of
our horizontal atlas. Its Frobenius pairing is the manifold derivative of the
restricted loss. The lift, Riesz identity, uniqueness, and stationarity are all
proved without a hypothesis excluding overlap.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion GS.RiemannianCompletion
open scoped Topology Manifold
namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance gradientHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance gradientChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance gradientIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- A canonical tangent lift exists because the already-defined point projector
lands in the actual differential image. No choice of a new factorization is made. -/
def tangentProjection (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X :=
  Classical.choose (pointProjection_unique_tangent_lift b₁ b₂ σ X Z)

@[simp] theorem inclusion_tangentProjection
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n) :
    inclusionDifferential b₁ b₂ σ X (tangentProjection b₁ b₂ σ X Z) =
      pointProjection b₁ b₂ X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift b₁ b₂ σ X Z)).1

theorem pointProjection_pairing_tangent
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    frobInner (pointProjection b₁ b₂ X.val Z) (inclusionDifferential b₁ b₂ σ X v) =
      frobInner Z (inclusionDifferential b₁ b₂ σ X v) := by
  have hfix : pointProjection b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) =
      inclusionDifferential b₁ b₂ σ X v :=
    (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mpr ⟨v, rfl⟩
  have hadj := pointProjection_self_adjoint b₁ b₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z
    (inclusionDifferential b₁ b₂ σ X v)
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose
  dsimp only at hadj
  rw [preferredFactor_product b₁ b₂ σ X, hfix] at hadj
  exact hadj

/-- The intrinsic Riesz identity for projecting an ambient Frobenius covector. -/
theorem tangentProjection_pairing
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X (tangentProjection b₁ b₂ σ X Z) v =
      frobInner Z (inclusionDifferential b₁ b₂ σ X v) := by
  unfold tangentPairing
  rw [inclusion_tangentProjection]
  exact pointProjection_pairing_tangent b₁ b₂ σ X Z v

/-- Uniqueness follows from positive definiteness, not from declaring this
identity to be a definition of the gradient. -/
theorem tangentProjection_unique
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X)
    (hw : ∀ v, tangentPairing b₁ b₂ σ X w v = frobInner Z (inclusionDifferential b₁ b₂ σ X v)) :
    w = tangentProjection b₁ b₂ σ X Z := by
  have h := hw (w - tangentProjection b₁ b₂ σ X Z)
  have hg := tangentProjection_pairing b₁ b₂ σ X Z (w - tangentProjection b₁ b₂ σ X Z)
  apply sub_eq_zero.mp
  apply (tangentPairing_self_eq_zero_iff b₁ b₂ σ X _).mp
  change frobInner (inclusionDifferential b₁ b₂ σ X (w - tangentProjection b₁ b₂ σ X Z)) _ = 0
  rw [map_sub, frobInner_sub_left]
  apply sub_eq_zero.mpr
  simpa only [tangentPairing, map_sub] using h.trans hg.symm

@[simp] theorem tangentProjection_of_tangent
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentProjection b₁ b₂ σ X (inclusionDifferential b₁ b₂ σ X v) = v := by
  apply inclusionDifferential_injective b₁ b₂ σ X
  rw [inclusion_tangentProjection]
  exact (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mpr ⟨v, rfl⟩

/-- Linear dependence on the ambient vector, derived from the Riesz identity. -/
theorem tangentProjection_add (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z W : Mat n) :
    tangentProjection b₁ b₂ σ X (Z + W) = tangentProjection b₁ b₂ σ X Z + tangentProjection b₁ b₂ σ X W := by
  symm
  apply tangentProjection_unique b₁ b₂ σ X (Z + W)
  intro v
  rw [tangentPairing_add_left, tangentProjection_pairing, tangentProjection_pairing,
    frobInner_add_left]

theorem tangentProjection_smul (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (a : ℝ) (Z : Mat n) :
    tangentProjection b₁ b₂ σ X (a • Z) = a • tangentProjection b₁ b₂ σ X Z := by
  symm
  apply tangentProjection_unique b₁ b₂ σ X (a • Z)
  intro v
  rw [tangentPairing_smul_left, tangentProjection_pairing, frobInner_smul_left]

@[simp] theorem tangentProjection_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    tangentProjection b₁ b₂ σ X (0 : Mat n) = 0 := by
  symm
  apply tangentProjection_unique b₁ b₂ σ X 0
  intro v
  simp

/-- The actual manifold chain rule for an ambient loss restricted to the orbit. -/
theorem restricted_loss_mfderiv (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (hf : DifferentiableAt ℝ f X.val) :
    mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => f Y.val) X =
        (fderiv ℝ f X.val).comp (inclusionDifferential b₁ b₂ σ X) := by
  have hi : MDifferentiableAt (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X :=
    ((overlap_val_contMDiff b₁ b₂ σ) X).mdifferentiableAt (by simp)
  have hh := mfderiv_comp X hf.mdifferentiableAt hi
  rw [mfderiv_eq_fderiv] at hh
  convert hh using 1 <;> first | rfl | (ext v <;> rfl)

/-- This vector inhabits mathlib's TangentSpace for the constructed atlas. -/
def intrinsicGradient (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X :=
  tangentProjection b₁ b₂ σ X (ambientGradient f X.val)

@[simp] theorem intrinsicGradient_ambient (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    inclusionDifferential b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) =
      pointProjection b₁ b₂ X.val (ambientGradient f X.val) :=
  inclusion_tangentProjection b₁ b₂ σ X _

/-- Riesz characterization against the ACTUAL derivative of f restricted to M. -/
theorem intrinsicGradient_characterization (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) v =
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => f Y.val) X v := by
  rw [restricted_loss_mfderiv b₁ b₂ σ f X hf]
  change tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) v =
    fderiv ℝ f X.val (inclusionDifferential b₁ b₂ σ X v)
  rw [ambientGradient_represents]
  exact tangentProjection_pairing b₁ b₂ σ X _ v

/-- The characterization determines a unique vector, not merely some lift. -/
theorem intrinsicGradient_unique (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X)
    (hw : ∀ v, tangentPairing b₁ b₂ σ X w v =
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => f Y.val) X v) :
    w = intrinsicGradient b₁ b₂ σ f X := by
  apply tangentProjection_unique b₁ b₂ σ X (ambientGradient f X.val)
  intro v
  rw [hw, restricted_loss_mfderiv b₁ b₂ σ f X hf]
  change fderiv ℝ f X.val (inclusionDifferential b₁ b₂ σ X v) = _
  exact ambientGradient_represents f X.val (inclusionDifferential b₁ b₂ σ X v)

/-- First-order stationarity is equivalent to the zero projected gradient. -/
theorem intrinsicGradient_zero_iff (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    intrinsicGradient b₁ b₂ σ f X = 0 ↔
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => f Y.val) X = 0 := by
  constructor
  · intro hg
    ext v
    rw [← intrinsicGradient_characterization b₁ b₂ σ f X hf, hg]
    simp
  · intro hd
    apply (tangentPairing_self_eq_zero_iff b₁ b₂ σ X _).mp
    rw [intrinsicGradient_characterization b₁ b₂ σ f X hf, hd]
    rfl

theorem intrinsicGradient_zero_iff_projected (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    intrinsicGradient b₁ b₂ σ f X = 0 ↔
      pointProjection b₁ b₂ X.val (ambientGradient f X.val) = 0 := by
  constructor
  · intro hg
    rw [← intrinsicGradient_ambient b₁ b₂ σ f X, hg, map_zero]
  · intro hp
    apply inclusionDifferential_injective b₁ b₂ σ X
    rw [intrinsicGradient_ambient, hp, map_zero]

/-- The exact norm used by the algorithm is the norm of the internal vector
under the Frobenius pullback, NOT the norm of its Cayley coordinates. -/
theorem intrinsicGradient_norm (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X) =
      frobSq (pointProjection b₁ b₂ X.val (ambientGradient f X.val)) := by
  unfold tangentPairing
  rw [intrinsicGradient_ambient]
  rfl


end GS.OverlapGeometry
