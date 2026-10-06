module

public import GS.OverlapGeometry.OrbitAtlas
public import GS.RiemannianCompletion.FrobeniusDual
public import GS.Extensions.FiniteTopology
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The smooth Frobenius metric with arbitrary overlap

The horizontal atlas gives the actual two-factor orbit its inherited smooth
manifold structure. Pulling the ambient Frobenius pairing back through the
injective manifold derivative of the inclusion defines a positive definite
metric on mathlib's actual tangent spaces. Its evaluation is smooth on the
total tangent bundle. No assumption excluding overlap is used.

The chart norm is retained. No equality between the chart norm and the
Frobenius norm is asserted, and no norm instance is replaced.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open GS.RiemannianCompletion
open scoped Manifold Topology

namespace GS.OverlapGeometry

variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))

-- Cache the existing submodule instance so tangent-bundle elaboration does
-- not unfold the chosen horizontal complement while searching for it.
local instance horizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _

local instance metricChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ

local instance metricIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- Ambient realization of a genuine manifold tangent vector. -/
def inclusionDifferential (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X →L[ℝ] Mat n :=
  mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
    (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X

theorem inclusionDifferential_injective (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    Function.Injective (inclusionDifferential b₁ b₂ σ X) :=
  overlap_val_mfderiv_injective b₁ b₂ σ X

/-- The Frobenius pullback on the true tangent fibre, using the horizontal
atlas and allowing continuous stabilizers. -/
def tangentPairing (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) : ℝ :=
  frobInner (inclusionDifferential b₁ b₂ σ X v)
    (inclusionDifferential b₁ b₂ σ X w)

theorem tangentPairing_symm (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X v w = tangentPairing b₁ b₂ σ X w v :=
  frobInner_comm _ _

theorem tangentPairing_add_left (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (u v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X (u + v) w =
      tangentPairing b₁ b₂ σ X u w + tangentPairing b₁ b₂ σ X v w := by
  unfold tangentPairing
  rw [map_add, frobInner_add_left]

theorem tangentPairing_add_right (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (u v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X u (v + w) =
      tangentPairing b₁ b₂ σ X u v + tangentPairing b₁ b₂ σ X u w := by
  unfold tangentPairing
  rw [map_add, frobInner_add_right]

theorem tangentPairing_smul_left (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (a : ℝ) (v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X (a • v) w = a * tangentPairing b₁ b₂ σ X v w := by
  unfold tangentPairing
  rw [map_smul, frobInner_smul_left]

theorem tangentPairing_smul_right (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (a : ℝ) (v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X v (a • w) = a * tangentPairing b₁ b₂ σ X v w := by
  unfold tangentPairing
  rw [map_smul, frobInner_smul_right]

@[simp] theorem tangentPairing_zero_left (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X 0 v = 0 := by simp [tangentPairing]

@[simp] theorem tangentPairing_zero_right (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X v 0 = 0 := by simp [tangentPairing]

theorem tangentPairing_self_nonneg (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    0 ≤ tangentPairing b₁ b₂ σ X v v := frobSq_nonneg _

theorem tangentPairing_self_eq_zero_iff (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentPairing b₁ b₂ σ X v v = 0 ↔ v = 0 := by
  change frobSq (inclusionDifferential b₁ b₂ σ X v) = 0 ↔ v = 0
  rw [frobSq_eq_zero_iff]
  constructor
  · intro h
    apply inclusionDifferential_injective b₁ b₂ σ X
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

theorem tangentPairing_pos (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (hv : v ≠ 0) :
    0 < tangentPairing b₁ b₂ σ X v v := by
  apply frobSq_pos_of_ne_zero
  intro hz
  apply hv
  apply inclusionDifferential_injective b₁ b₂ σ X
  simpa only [map_zero] using hz

-- These local instances expose the already existing horizontal chart norm.
section Fibrewise

local instance tangentSpaceNormedAddCommGroup (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    NormedAddCommGroup (TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :=
  inferInstanceAs (NormedAddCommGroup (HorizontalModel b₁ b₂ σ))

local instance tangentSpaceNormedSpace (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    NormedSpace ℝ (TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :=
  inferInstanceAs (NormedSpace ℝ (HorizontalModel b₁ b₂ σ))

local instance tangentSpaceFiniteDimensional (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    FiniteDimensional ℝ (TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :=
  inferInstanceAs (FiniteDimensional ℝ (HorizontalModel b₁ b₂ σ))

/-- Fibrewise continuous bilinear metric in the standard nested CLM type. -/
def tangentMetricCLM (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X →L[ℝ]
      TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => LinearMap.toContinuousLinearMap
        { toFun := fun w => tangentPairing b₁ b₂ σ X v w
          map_add' := tangentPairing_add_right b₁ b₂ σ X v
          map_smul' := by
            intro a w
            exact tangentPairing_smul_right b₁ b₂ σ X a v w }
      map_add' := by
        intro v w
        ext u
        exact tangentPairing_add_left b₁ b₂ σ X v w u
      map_smul' := by
        intro a v
        ext u
        exact tangentPairing_smul_left b₁ b₂ σ X a v u }

@[simp] theorem tangentMetricCLM_apply (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentMetricCLM b₁ b₂ σ X v w = tangentPairing b₁ b₂ σ X v w := rfl

private theorem matrix_norm_le_one_of_frobSq_le_one (A : Mat n) (h : frobSq A ≤ 1) :
    ‖A‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  have he := GS.Extensions.abs_entry_le_of_frobSq_le (η := (1 : ℝ))
    (by simpa using h) i j
  simpa only [Real.norm_eq_abs, abs_one] using he

/-- Positive definiteness controls the original horizontal chart norm. The
bound is allowed to depend on the fibre; no false coordinate isometry is used. -/
theorem tangentMetric_unitBall_vonNBounded (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    Bornology.IsVonNBounded ℝ {v | tangentMetricCLM b₁ b₂ σ X v v < 1} := by
  obtain ⟨K, _, hK⟩ := (inclusionDifferential b₁ b₂ σ X).toLinearMap.injective_iff_antilipschitz.mp
    (inclusionDifferential_injective b₁ b₂ σ X)
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨(K : ℝ), ?_⟩
  intro v hv
  have hnorm : ‖inclusionDifferential b₁ b₂ σ X v‖ ≤ 1 :=
    matrix_norm_le_one_of_frobSq_le_one _ (le_of_lt hv)
  calc
    ‖v‖ ≤ K * ‖inclusionDifferential b₁ b₂ σ X v‖ := hK.le_mul_norm (map_zero _) v
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
    _ = K := mul_one _

theorem tangentMetric_compatible_data (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    (∀ v w, tangentMetricCLM b₁ b₂ σ X v w = tangentMetricCLM b₁ b₂ σ X w v) ∧
    (∀ v, v ≠ 0 → 0 < tangentMetricCLM b₁ b₂ σ X v v) ∧
    ContinuousAt (fun v => tangentMetricCLM b₁ b₂ σ X v v) 0 ∧
    Bornology.IsVonNBounded ℝ {v | tangentMetricCLM b₁ b₂ σ X v v < 1} := by
  exact ⟨tangentPairing_symm b₁ b₂ σ X, tangentPairing_pos b₁ b₂ σ X,
    ((tangentMetricCLM b₁ b₂ σ X).continuous.clm_apply continuous_id).continuousAt,
    tangentMetric_unitBall_vonNBounded b₁ b₂ σ X⟩

end Fibrewise

/-- Ambient realization on the actual total tangent bundle. -/
def tangentAmbient
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ))) : Mat n :=
  inclusionDifferential b₁ b₂ σ p.proj p.2

theorem tangentAmbient_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent (𝓘(ℝ, Mat n)) ⊤
      (tangentAmbient b₁ b₂ σ) := by
  exact (contMDiff_snd_tangentBundle_modelSpace (Mat n) (𝓘(ℝ, Mat n))).comp
    ((overlap_val_contMDiff b₁ b₂ σ).contMDiff_tangentMap (by simp))

/-- Smooth metric evaluation, extending to pairs of different fibres. -/
def tangentMetricExtension
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ)) ×
      TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (MatrixOrbit b₁ b₂ (permMatrix σ))) : ℝ :=
  frobInner (tangentAmbient b₁ b₂ σ p.1) (tangentAmbient b₁ b₂ σ p.2)

set_option maxHeartbeats 800000 in
theorem tangentMetricExtension_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent.prod
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent) (𝓘(ℝ, ℝ)) ⊤
      (tangentMetricExtension b₁ b₂ σ) := by
  exact frobInner_smooth.comp_contMDiff
    (((tangentAmbient_contMDiff b₁ b₂ σ).comp contMDiff_fst).prodMk_space
      ((tangentAmbient_contMDiff b₁ b₂ σ).comp contMDiff_snd))

@[simp] theorem tangentMetricExtension_same_base
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    tangentMetricExtension b₁ b₂ σ (⟨X, v⟩, ⟨X, w⟩) =
      tangentPairing b₁ b₂ σ X v w := rfl

def tangentEnergy
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ))) : ℝ :=
  tangentPairing b₁ b₂ σ p.proj p.2 p.2

set_option maxHeartbeats 800000 in
theorem tangentEnergy_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)).tangent (𝓘(ℝ, ℝ)) ⊤
      (tangentEnergy b₁ b₂ σ) := by
  exact frobInner_smooth.comp_contMDiff
    (g := fun q : Mat n × Mat n => frobInner q.1 q.2)
    (f := fun p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ)) =>
        (tangentAmbient b₁ b₂ σ p, tangentAmbient b₁ b₂ σ p))
    ((tangentAmbient_contMDiff b₁ b₂ σ).prodMk_space
      (tangentAmbient_contMDiff b₁ b₂ σ))

@[simp] theorem tangentEnergy_eq_zero_iff
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ))) :
    tangentEnergy b₁ b₂ σ p = 0 ↔ p.2 = 0 :=
  tangentPairing_self_eq_zero_iff b₁ b₂ σ p.proj p.2

theorem tangentEnergy_pos
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ))) (hp : p.2 ≠ 0) :
    0 < tangentEnergy b₁ b₂ σ p :=
  tangentPairing_pos b₁ b₂ σ p.proj p.2 hp

end GS.OverlapGeometry
