module

public import GS.Unitary.Frobenius
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Real Frobenius projection on complex matrix subspaces

The matrix space retains its finite-product norm. A separate Euclidean space
carries the real inner product obtained from the complex Hermitian product.
The projector below is constructed using mathlib's orthogonal projection.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix InnerProductSpace
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {n : ℕ}

abbrev CFrobCoordinates (n : ℕ) := EuclideanSpace ℂ (Fin n × Fin n)

instance cFrobCoordinatesRealInner (n : ℕ) : InnerProductSpace ℝ (CFrobCoordinates n) :=
  InnerProductSpace.rclikeToReal ℂ _

def encodeCFrob : CMat n →ₗ[ℝ] CFrobCoordinates n where
  toFun A := (WithLp.equiv 2 _).symm (fun k => A k.1 k.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def decodeCFrob : CFrobCoordinates n →ₗ[ℝ] CMat n where
  toFun x i j := x (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem decode_encode_cFrob (A : CMat n) : decodeCFrob (encodeCFrob A) = A := rfl
@[simp] theorem encode_decode_cFrob (x : CFrobCoordinates n) : encodeCFrob (decodeCFrob x) = x := rfl

theorem encodeCFrob_injective : Function.Injective (encodeCFrob : CMat n →ₗ[ℝ] CFrobCoordinates n) := by
  intro A B h
  simpa using congrArg decodeCFrob h

theorem encodeCFrob_inner (A B : CMat n) :
    ⟪encodeCFrob A, encodeCFrob B⟫_ℝ = cFrobInner A B := by
  change (⟪encodeCFrob A, encodeCFrob B⟫_ℂ).re = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, encodeCFrob, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.re_sum, Complex.mul_re, Pi.star_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
  simp only [cFrobInner, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (B i j).re * (A i j).re + (B i j).im * (A i j).im = _
  ring

def encodedCSubspace (S : Submodule ℝ (CMat n)) : Submodule ℝ (CFrobCoordinates n) :=
  S.map encodeCFrob

/-- An actual continuous linear map, constructed from mathlib's projection.
The name orthogonalProjection follows the mathlib 4.19.0 API. -/
def cFrobProjection (S : Submodule ℝ (CMat n)) : CMat n →L[ℝ] CMat n :=
  ((decodeCFrob : CFrobCoordinates n →ₗ[ℝ] CMat n).toContinuousLinearMap.comp
    ((encodedCSubspace S).subtypeL.comp ((encodedCSubspace S).orthogonalProjection))).comp
    (encodeCFrob : CMat n →ₗ[ℝ] CFrobCoordinates n).toContinuousLinearMap

theorem cFrobProjection_mem (S : Submodule ℝ (CMat n)) (Z : CMat n) :
    cFrobProjection S Z ∈ S := by
  have hp := ((encodedCSubspace S).orthogonalProjection (encodeCFrob Z)).property
  obtain ⟨A, hA, he⟩ := hp
  change decodeCFrob ((encodedCSubspace S).orthogonalProjection (encodeCFrob Z) :
    CFrobCoordinates n) ∈ S
  rw [← he, decode_encode_cFrob]
  exact hA

/-- This is the one API-sensitive projection lemma; all later arguments only
use its matrix conclusion. -/
theorem cFrobProjection_normal (S : Submodule ℝ (CMat n)) (Z Y : CMat n)
    (hY : Y ∈ S) : cFrobInner (Z-cFrobProjection S Z) Y = 0 := by
  have hy : encodeCFrob Y ∈ encodedCSubspace S := ⟨Y,hY,rfl⟩
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero
    (K := encodedCSubspace S) (encodeCFrob Z) (encodeCFrob Y) hy
  rw [Submodule.starProjection_apply] at h
  rw [← encodeCFrob_inner, map_sub]
  change ⟪encodeCFrob Z - encodeCFrob (decodeCFrob
    ((encodedCSubspace S).orthogonalProjection (encodeCFrob Z) : CFrobCoordinates n)),
    encodeCFrob Y⟫_ℝ = 0
  rw [encode_decode_cFrob]
  exact h

theorem cFrobProjection_pythagorean (S : Submodule ℝ (CMat n)) (Z Y : CMat n)
    (hY : Y ∈ S) :
    cFrobSq (Z-Y) = cFrobSq (Z-cFrobProjection S Z) + cFrobSq (cFrobProjection S Z-Y) := by
  have he : Z-Y = (Z-cFrobProjection S Z)+(cFrobProjection S Z-Y) := by abel
  rw [he, cFrobSq_add, cFrobProjection_normal S Z _ (S.sub_mem (cFrobProjection_mem S Z) hY)]
  ring

theorem cFrobProjection_minimizes (S : Submodule ℝ (CMat n)) (Z Y : CMat n)
    (hY : Y ∈ S) : cFrobSq (Z-cFrobProjection S Z) ≤ cFrobSq (Z-Y) := by
  rw [cFrobProjection_pythagorean S Z Y hY]
  exact le_add_of_nonneg_right (cFrobSq_nonneg _)

theorem cFrobProjection_unique_normal (S : Submodule ℝ (CMat n)) (Z Y : CMat n)
    (hY : Y ∈ S) (hn : ∀ W ∈ S, cFrobInner (Z-Y) W = 0) :
    cFrobProjection S Z = Y := by
  have hd := S.sub_mem (cFrobProjection_mem S Z) hY
  have h₁ := cFrobProjection_normal S Z _ hd
  have h₂ := hn (cFrobProjection S Z-Y) hd
  apply sub_eq_zero.mp
  apply (cFrobSq_eq_zero_iff _).mp
  have he : cFrobProjection S Z-Y = (Z-Y)-(Z-cFrobProjection S Z) := by abel
  change cFrobInner (cFrobProjection S Z-Y) (cFrobProjection S Z-Y) = 0
  conv_lhs => lhs; rw [he]
  rw [cFrobInner_sub_left, h₂, h₁, sub_self]

@[simp] theorem cFrobProjection_of_mem (S : Submodule ℝ (CMat n)) (Y : CMat n)
    (hY : Y ∈ S) : cFrobProjection S Y = Y := by
  apply cFrobProjection_unique_normal S Y Y hY
  intro W hW
  simp

@[simp] theorem cFrobProjection_idempotent (S : Submodule ℝ (CMat n)) (Z : CMat n) :
    cFrobProjection S (cFrobProjection S Z) = cFrobProjection S Z :=
  cFrobProjection_of_mem S _ (cFrobProjection_mem S Z)

theorem cFrobProjection_fixed_iff (S : Submodule ℝ (CMat n)) (Z : CMat n) :
    cFrobProjection S Z = Z ↔ Z ∈ S := by
  constructor
  · intro h; rw [← h]; exact cFrobProjection_mem S Z
  · exact cFrobProjection_of_mem S Z

theorem cFrobProjection_self_adjoint (S : Submodule ℝ (CMat n)) (A B : CMat n) :
    cFrobInner (cFrobProjection S A) B = cFrobInner A (cFrobProjection S B) := by
  have ha := cFrobProjection_normal S A _ (cFrobProjection_mem S B)
  have hb := cFrobProjection_normal S B _ (cFrobProjection_mem S A)
  rw [cFrobInner_sub_left] at ha hb
  rw [cFrobInner_comm B, cFrobInner_comm (cFrobProjection S B)] at hb
  linarith

theorem cFrobProjection_smooth (S : Submodule ℝ (CMat n)) :
    ContDiff ℝ ⊤ (cFrobProjection S) := (cFrobProjection S).contDiff


end GS.UnitaryGeometry
