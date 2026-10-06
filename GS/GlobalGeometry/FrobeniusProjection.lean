module

public import GS.Sharing
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact Frobenius projection onto any concrete finite-dimensional matrix subspace

We use mathlib's orthogonalProjection on a genuine EuclideanSpace. No inner
product is installed on the entrywise-sup-norm Matrix type. The two linear
encodings below identify the Euclidean inner product with GS.frobInner.
In particular this module does not assume the existence of a projection or
normal-equation solution. These are constructed from the actual submodule.

-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix InnerProductSpace
open scoped BigOperators
namespace GS.GlobalGeometry
variable {n : ℕ}

abbrev FrobCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

def frobBasis (n : ℕ) : OrthonormalBasis (Fin n × Fin n) ℝ (FrobCoordinates n) :=
  EuclideanSpace.basisFun (Fin n × Fin n) ℝ

def encodeFrob : Mat n →ₗ[ℝ] FrobCoordinates n where
  toFun A := ∑ k, A k.1 k.2 • frobBasis n k
  map_add' A B := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a A := by simp [Finset.smul_sum, smul_smul]

def decodeFrob : FrobCoordinates n →ₗ[ℝ] Mat n where
  toFun x i j := ⟪frobBasis n (i,j), x⟫_ℝ
  map_add' x y := by ext i j; exact inner_add_right _ _ _
  map_smul' a x := by ext i j; simp [inner_smul_right, Pi.smul_apply]

@[simp] theorem decode_encode (A : Mat n) : decodeFrob (encodeFrob A) = A := by
  ext i j
  change ⟪frobBasis n (i,j), ∑ k, A k.1 k.2 • frobBasis n k⟫_ℝ = A i j
  simp [inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp (frobBasis n).orthonormal]

@[simp] theorem encode_decode (x : FrobCoordinates n) : encodeFrob (decodeFrob x) = x := by
  exact (frobBasis n).sum_repr' x

theorem encodeFrob_injective : Function.Injective (encodeFrob : Mat n →ₗ[ℝ] FrobCoordinates n) := by
  intro A B h
  simpa using congrArg decodeFrob h

theorem encodeFrob_inner (A B : Mat n) :
    ⟪encodeFrob A, encodeFrob B⟫_ℝ = frobInner A B := by
  calc
    _ = ∑ k : Fin n × Fin n,
        ⟪encodeFrob A, frobBasis n k⟫_ℝ * ⟪frobBasis n k, encodeFrob B⟫_ℝ :=
      ((frobBasis n).sum_inner_mul_inner _ _).symm
    _ = ∑ k : Fin n × Fin n, A k.1 k.2 * B k.1 k.2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have ha := congrFun (congrFun (decode_encode A) k.1) k.2
      have hb := congrFun (congrFun (decode_encode B) k.1) k.2
      change ⟪frobBasis n k, encodeFrob A⟫_ℝ = _ at ha
      change ⟪frobBasis n k, encodeFrob B⟫_ℝ = _ at hb
      rw [real_inner_comm (frobBasis n k) (encodeFrob A), ha, hb]
    _ = _ := by simp [frobInner, Fintype.sum_prod_type]

def encodedSubspace (S : Submodule ℝ (Mat n)) : Submodule ℝ (FrobCoordinates n) :=
  S.map encodeFrob

/-- An actual continuous linear map, constructed from mathlib's projection.
The name orthogonalProjection follows the mathlib 4.19.0 API. -/
def frobProjection (S : Submodule ℝ (Mat n)) : Mat n →L[ℝ] Mat n :=
  ((decodeFrob : FrobCoordinates n →ₗ[ℝ] Mat n).toContinuousLinearMap.comp
    ((encodedSubspace S).subtypeL.comp ((encodedSubspace S).orthogonalProjection))).comp
    (encodeFrob : Mat n →ₗ[ℝ] FrobCoordinates n).toContinuousLinearMap

theorem frobProjection_mem (S : Submodule ℝ (Mat n)) (Z : Mat n) :
    frobProjection S Z ∈ S := by
  have hp := ((encodedSubspace S).orthogonalProjection (encodeFrob Z)).property
  obtain ⟨A, hA, he⟩ := hp
  change decodeFrob ((encodedSubspace S).orthogonalProjection (encodeFrob Z) :
    FrobCoordinates n) ∈ S
  rw [← he, decode_encode]
  exact hA

/-- This is the one API-sensitive projection lemma; all later arguments only
use its matrix conclusion. -/
theorem frobProjection_normal (S : Submodule ℝ (Mat n)) (Z Y : Mat n)
    (hY : Y ∈ S) : frobInner (Z-frobProjection S Z) Y = 0 := by
  have hy : encodeFrob Y ∈ encodedSubspace S := ⟨Y,hY,rfl⟩
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero
    (K := encodedSubspace S) (encodeFrob Z) (encodeFrob Y) hy
  rw [Submodule.starProjection_apply] at h
  rw [← encodeFrob_inner, map_sub]
  change ⟪encodeFrob Z - encodeFrob (decodeFrob
    ((encodedSubspace S).orthogonalProjection (encodeFrob Z) : FrobCoordinates n)),
    encodeFrob Y⟫_ℝ = 0
  rw [encode_decode]
  exact h

theorem frobProjection_pythagorean (S : Submodule ℝ (Mat n)) (Z Y : Mat n)
    (hY : Y ∈ S) :
    frobSq (Z-Y) = frobSq (Z-frobProjection S Z) + frobSq (frobProjection S Z-Y) := by
  have he : Z-Y = (Z-frobProjection S Z)+(frobProjection S Z-Y) := by abel
  rw [he, frobSq_add, frobProjection_normal S Z _ (S.sub_mem (frobProjection_mem S Z) hY)]
  ring

theorem frobProjection_minimizes (S : Submodule ℝ (Mat n)) (Z Y : Mat n)
    (hY : Y ∈ S) : frobSq (Z-frobProjection S Z) ≤ frobSq (Z-Y) := by
  rw [frobProjection_pythagorean S Z Y hY]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

theorem frobProjection_unique_normal (S : Submodule ℝ (Mat n)) (Z Y : Mat n)
    (hY : Y ∈ S) (hn : ∀ W ∈ S, frobInner (Z-Y) W = 0) :
    frobProjection S Z = Y := by
  have hd := S.sub_mem (frobProjection_mem S Z) hY
  have h₁ := frobProjection_normal S Z _ hd
  have h₂ := hn (frobProjection S Z-Y) hd
  apply sub_eq_zero.mp
  apply (frobSq_eq_zero_iff _).mp
  have he : frobProjection S Z-Y = (Z-Y)-(Z-frobProjection S Z) := by abel
  change frobInner (frobProjection S Z-Y) (frobProjection S Z-Y) = 0
  conv_lhs => lhs; rw [he]
  rw [frobInner_sub_left, h₂, h₁, sub_self]

@[simp] theorem frobProjection_of_mem (S : Submodule ℝ (Mat n)) (Y : Mat n)
    (hY : Y ∈ S) : frobProjection S Y = Y := by
  apply frobProjection_unique_normal S Y Y hY
  intro W hW
  simp

@[simp] theorem frobProjection_idempotent (S : Submodule ℝ (Mat n)) (Z : Mat n) :
    frobProjection S (frobProjection S Z) = frobProjection S Z :=
  frobProjection_of_mem S _ (frobProjection_mem S Z)

theorem frobProjection_fixed_iff (S : Submodule ℝ (Mat n)) (Z : Mat n) :
    frobProjection S Z = Z ↔ Z ∈ S := by
  constructor
  · intro h; rw [← h]; exact frobProjection_mem S Z
  · exact frobProjection_of_mem S Z

theorem frobProjection_self_adjoint (S : Submodule ℝ (Mat n)) (A B : Mat n) :
    frobInner (frobProjection S A) B = frobInner A (frobProjection S B) := by
  have ha := frobProjection_normal S A _ (frobProjection_mem S B)
  have hb := frobProjection_normal S B _ (frobProjection_mem S A)
  rw [frobInner_sub_left] at ha hb
  rw [frobInner_comm B, frobInner_comm (frobProjection S B)] at hb
  linarith

theorem frobProjection_smooth (S : Submodule ℝ (Mat n)) :
    ContDiff ℝ ⊤ (frobProjection S) := (frobProjection S).contDiff

end GS.GlobalGeometry
