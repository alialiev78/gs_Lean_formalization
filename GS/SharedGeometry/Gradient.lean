module

public import GS.SharedGeometry.TangentBridge
public import GS.SharedGeometry.Riemannian
public import GS.SharedGeometry.SmoothProjection
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The intrinsic gradient on the genuine shared orbit

The ambient orthogonal projector is lifted into the actual tangent space of
our horizontal atlas. Its Frobenius pairing is the manifold derivative of the
restricted loss. The lift, Riesz identity, uniqueness, and stationarity are all
proved for actual repeated full blocks, without excluding overlap.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.CayleyCharts GS.Extensions GS.GlobalGeometry
open GS.RiemannianCompletion
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)
local instance gradientHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance gradientChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance gradientIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- A canonical tangent lift exists because the already-defined point projector
lands in the actual differential image. No choice of a new factorization is made. -/
def tangentProjection (X : MatrixOrbit right left P) (Z : Mat n) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  Classical.choose (pointProjection_unique_tangent_lift right left P X Z)

@[simp] theorem inclusion_tangentProjection
    (X : MatrixOrbit right left P) (Z : Mat n) :
    inclusionDifferential right left P X (tangentProjection right left P X Z) =
      pointProjection right left X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift right left P X Z)).1

theorem pointProjection_pairing_tangent
    (X : MatrixOrbit right left P) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    frobInner (pointProjection right left X.val Z) (inclusionDifferential right left P X v) =
      frobInner Z (inclusionDifferential right left P X v) := by
  have hfix : pointProjection right left X.val (inclusionDifferential right left P X v) =
      inclusionDifferential right left P X v :=
    (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩
  rw [pointProjection_self_adjoint, hfix]

/-- The intrinsic Riesz identity for projecting an ambient Frobenius covector. -/
theorem tangentProjection_pairing
    (X : MatrixOrbit right left P) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (tangentProjection right left P X Z) v =
      frobInner Z (inclusionDifferential right left P X v) := by
  unfold tangentPairing
  rw [inclusion_tangentProjection]
  exact pointProjection_pairing_tangent right left P X Z v

/-- Uniqueness follows from positive definiteness, not from declaring this
identity to be a definition of the gradient. -/
theorem tangentProjection_unique
    (X : MatrixOrbit right left P) (Z : Mat n)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X)
    (hw : ∀ v, tangentPairing right left P X w v = frobInner Z (inclusionDifferential right left P X v)) :
    w = tangentProjection right left P X Z := by
  have h := hw (w - tangentProjection right left P X Z)
  have hg := tangentProjection_pairing right left P X Z (w - tangentProjection right left P X Z)
  apply sub_eq_zero.mp
  apply (tangentPairing_self_eq_zero_iff right left P X _).mp
  change frobInner (inclusionDifferential right left P X (w - tangentProjection right left P X Z)) _ = 0
  rw [map_sub, frobInner_sub_left]
  apply sub_eq_zero.mpr
  simpa only [tangentPairing, map_sub] using h.trans hg.symm

@[simp] theorem tangentProjection_of_tangent
    (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentProjection right left P X (inclusionDifferential right left P X v) = v := by
  apply inclusionDifferential_injective right left P X
  rw [inclusion_tangentProjection]
  exact (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩

/-- Linear dependence on the ambient vector, derived from the Riesz identity. -/
theorem tangentProjection_add (X : MatrixOrbit right left P) (Z W : Mat n) :
    tangentProjection right left P X (Z + W) = tangentProjection right left P X Z + tangentProjection right left P X W := by
  symm
  apply tangentProjection_unique right left P X (Z + W)
  intro v
  rw [tangentPairing_add_left, tangentProjection_pairing, tangentProjection_pairing,
    frobInner_add_left]

theorem tangentProjection_smul (X : MatrixOrbit right left P)
    (a : ℝ) (Z : Mat n) :
    tangentProjection right left P X (a • Z) = a • tangentProjection right left P X Z := by
  symm
  apply tangentProjection_unique right left P X (a • Z)
  intro v
  rw [tangentPairing_smul_left, tangentProjection_pairing, frobInner_smul_left]

@[simp] theorem tangentProjection_zero (X : MatrixOrbit right left P) :
    tangentProjection right left P X (0 : Mat n) = 0 := by
  symm
  apply tangentProjection_unique right left P X 0
  intro v
  simp

/-- The actual manifold chain rule for an ambient loss restricted to the orbit. -/
theorem restricted_loss_mfderiv (f : Mat n → ℝ)
    (X : MatrixOrbit right left P)
    (hf : DifferentiableAt ℝ f X.val) :
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit right left P => f Y.val) X =
        (fderiv ℝ f X.val).comp (inclusionDifferential right left P X) := by
  have hi : MDifferentiableAt (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit right left P => Y.val) X :=
    ((sharedOrbit_val_contMDiff right left P) X).mdifferentiableAt (by simp)
  have hh := mfderiv_comp X hf.mdifferentiableAt hi
  rw [mfderiv_eq_fderiv] at hh
  convert hh using 1 <;> first | rfl | (ext v <;> rfl)

/-- This vector inhabits mathlib's TangentSpace for the constructed atlas. -/
def intrinsicGradient (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  tangentProjection right left P X (ambientGradient f X.val)

@[simp] theorem intrinsicGradient_ambient (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) :
    inclusionDifferential right left P X (intrinsicGradient right left P f X) =
      pointProjection right left X.val (ambientGradient f X.val) :=
  inclusion_tangentProjection right left P X _

/-- Riesz characterization against the ACTUAL derivative of f restricted to M. -/
theorem intrinsicGradient_characterization (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (intrinsicGradient right left P f X) v =
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit right left P => f Y.val) X v := by
  rw [restricted_loss_mfderiv right left P f X hf]
  change tangentPairing right left P X (intrinsicGradient right left P f X) v =
    fderiv ℝ f X.val (inclusionDifferential right left P X v)
  rw [ambientGradient_represents]
  exact tangentProjection_pairing right left P X _ v

/-- The characterization determines a unique vector, not merely some lift. -/
theorem intrinsicGradient_unique (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X)
    (hw : ∀ v, tangentPairing right left P X w v =
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit right left P => f Y.val) X v) :
    w = intrinsicGradient right left P f X := by
  apply tangentProjection_unique right left P X (ambientGradient f X.val)
  intro v
  rw [hw, restricted_loss_mfderiv right left P f X hf]
  change fderiv ℝ f X.val (inclusionDifferential right left P X v) = _
  exact ambientGradient_represents f X.val (inclusionDifferential right left P X v)

/-- First-order stationarity is equivalent to the zero projected gradient. -/
theorem intrinsicGradient_zero_iff (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val) :
    intrinsicGradient right left P f X = 0 ↔
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit right left P => f Y.val) X = 0 := by
  constructor
  · intro hg
    ext v
    rw [← intrinsicGradient_characterization right left P f X hf, hg]
    simp
  · intro hd
    apply (tangentPairing_self_eq_zero_iff right left P X _).mp
    rw [intrinsicGradient_characterization right left P f X hf, hd]
    rfl

theorem intrinsicGradient_zero_iff_projected (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) :
    intrinsicGradient right left P f X = 0 ↔
      pointProjection right left X.val (ambientGradient f X.val) = 0 := by
  constructor
  · intro hg
    rw [← intrinsicGradient_ambient right left P f X, hg, map_zero]
  · intro hp
    apply inclusionDifferential_injective right left P X
    rw [intrinsicGradient_ambient, hp, map_zero]

/-- The exact norm used by the algorithm is the norm of the internal vector
under the Frobenius pullback, NOT the norm of its Cayley coordinates. -/
theorem intrinsicGradient_norm (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) :
    tangentPairing right left P X (intrinsicGradient right left P f X) (intrinsicGradient right left P f X) =
      frobSq (pointProjection right left X.val (ambientGradient f X.val)) := by
  unfold tangentPairing
  rw [intrinsicGradient_ambient]
  rfl


/-- For a smooth ambient loss, the matrix realization of its intrinsic
shared-orbit gradient is smooth. This statement does not yet register the
varying-base vector as a smooth section of the total tangent bundle. -/
theorem intrinsicGradient_ambient_contMDiff (f : Mat n → ℝ)
    (hf : ContDiff ℝ ⊤ f) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n)) ⊤
      (fun X : MatrixOrbit right left P =>
        inclusionDifferential right left P X (intrinsicGradient right left P f X)) := by
  have hg : ContDiff ℝ ⊤ (ambientGradient f) :=
    ambientGradient_smooth_of_fderiv f (hf.fderiv_right (by simp))
  have hpair : ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, Mat n))) ⊤
      (fun X : MatrixOrbit right left P => (X, ambientGradient f X.val)) :=
    contMDiff_id.prodMk (hg.comp_contMDiff (sharedOrbit_val_contMDiff right left P))
  simpa only [intrinsicGradient_ambient, Function.comp_def] using
    (pointProjection_contMDiff right left P).comp hpair

end GS.SharedGeometry
