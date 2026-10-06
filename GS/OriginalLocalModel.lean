module

public import GS.Fibres
public import GS.CompactFibres
public import GS.Shuffle
public import GS.Projection
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Original local parameterization (definitions and elementary identities)

This file follows the manuscript's original variables ell, r, c, z, u.
No claim of a smooth manifold structure is used to define the maps. The hard
analytic statements about normalization, fibres, and local coverage remain
explicit goals in Specifications.lean.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

/-- Matrix exponential by its series. The following lemmas identify it with
mathlib's exponential and establish convergence and continuity. -/
def matrixExp {n : ℕ} (A : Mat n) : Mat n :=
  ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • A^k

theorem matrixExp_eq_exp {n : ℕ} (A : Mat n) :
    matrixExp A = NormedSpace.exp A := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  rfl

theorem matrixExp_hasSum {n : ℕ} (A : Mat n) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A^k) (matrixExp A) := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  rw [matrixExp_eq_exp]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A

theorem continuous_matrixExp (n : ℕ) : Continuous (@matrixExp n) := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have he : @matrixExp n = NormedSpace.exp := funext matrixExp_eq_exp
  rw [he]
  exact continuous_iff_continuousAt.mpr (fun A =>
    (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt)

def rotation (t : ℝ) : Mat 2 :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

theorem continuous_rotation : Continuous rotation := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [rotation] <;> fun_prop

theorem rotation_orthogonal (t : ℝ) : Orthogonal (rotation t) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
      Fin.sum_univ_succ] <;> nlinarith [Real.sin_sq_add_cos_sq t]

theorem middleBlock_symmetric (a b : ℝ) (u : CircleVector) :
    (middleBlock a b u)ᵀ = middleBlock a b u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleBlock,T,Matrix.transpose_apply,Matrix.one_apply]

/-- Positivity concerns the normalized scalar components, not raw M_ij. -/
theorem positive_normalized_ratio (a q : ℝ) (hq : q ≠ 0)
    (ha : |a-q| < |q|/2) : 0 < a/q := by
  have hb := abs_lt.mp ha
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · rw [abs_of_neg hneg] at hb
    have haneg : a < 0 := by linarith [hb.2]
    exact div_pos_of_neg_of_neg haneg hneg
  · rw [abs_of_pos hpos] at hb
    have hapos : 0 < a := by linarith [hb.1]
    exact div_pos hapos hpos

/-- Parameters use full skew matrices rather than choosing a basis of so(q).
The later identification with R^(q(q-1)/2) remains a named obligation. -/
abbrev OriginalParameters (q : ℕ) :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Mat q × CircleVector

def originalK (q : ℕ) (η : ℝ) : Set (OriginalParameters q) :=
  {p | let (ell,r,c,z,u) := p
       (∀ i, |ell i| ≤ η) ∧ (∀ j, |r j| ≤ η) ∧
       (∀ j : Fin q, j.val=0 → r j=0) ∧
       IsSkew c ∧ IsSkew z ∧ frobSq c ≤ η^2 ∧ frobSq z ≤ η^2 ∧ OnCircle u}

def originalPsi {q : ℕ} (Q₀ c : Mat q) : Mat q := Q₀ * matrixExp c

theorem continuous_originalPsi {q : ℕ} (Q₀ : Mat q) :
    Continuous (originalPsi Q₀) := by
  exact continuous_const.mul (continuous_matrixExp q)

/-- The exact matrix map f from the original fibre proof. -/
def originalF {q : ℕ} (Q₀ : Mat q) (p : OriginalParameters q) : Mat (q*2) :=
  let (ell,r,c,z,u) := p
  let A := originalPsi Q₀ (c+z)
  let B := originalPsi Q₀ (c-z)
  fun i j =>
    let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
    let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
    (rotation (ell ri.1) * middleBlock (A ri.1 rj.1) (B ri.1 rj.1) u *
      rotation (r rj.1)) ri.2 rj.2

/-- Continuity of the actual matrix-valued parameter map, with its original
exponential definition and the matrix product topology. -/
theorem continuous_originalF {q : ℕ} (Q₀ : Mat q) :
    Continuous (originalF Q₀) := by
  have hpsi := continuous_originalPsi Q₀
  have hrot := continuous_rotation
  have ht := continuous_T
  unfold originalF middleBlock
  fun_prop

/-- The exact quotient coordinates before choosing a basis of skew matrices. -/
def originalG {q : ℕ} (p : OriginalParameters q) :
    (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ :=
  let (ell,r,c,z,u) := p
  (ell,r,c,outer u (fun ij => z ij.1 ij.2))

/-- Continuity of the actual quotient-coordinate map in the manuscript. -/
theorem continuous_originalG (q : ℕ) : Continuous (@originalG q) := by
  unfold originalG outer
  fun_prop

/-- Flattening a matrix into its coordinate-pair function loses no information. -/
theorem matrix_entries_injective {q : ℕ} :
    Function.Injective (fun z : Mat q => fun ij : Fin q × Fin q => z ij.1 ij.2) := by
  intro z w h
  funext i j
  exact congrFun h (i,j)

/-- The full fibre relation of `originalG`, including the collapsed circle at
`z = 0`. Establishing the same relation for `originalF` is a separate task. -/
theorem originalG_fibres {q : ℕ}
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v) :
    originalG (ell,r,c,z,u) = originalG (ell',r',c',w,v) ↔
      ell = ell' ∧ r = r' ∧ c = c' ∧
        ((z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w)) := by
  have heq (x y : Mat q) : (fun ij : Fin q × Fin q => x ij.1 ij.2) =
      (fun ij : Fin q × Fin q => y ij.1 ij.2) ↔ x = y :=
    matrix_entries_injective.eq_iff
  have hz0 : (fun ij : Fin q × Fin q => z ij.1 ij.2) = 0 ↔ z = 0 :=
    heq z 0
  have hw0 : (fun ij : Fin q × Fin q => w ij.1 ij.2) = 0 ↔ w = 0 :=
    heq w 0
  have hzw : (fun ij : Fin q × Fin q => z ij.1 ij.2) =
      (fun ij : Fin q × Fin q => w ij.1 ij.2) ↔ z = w :=
    heq z w
  have hneg : (fun ij : Fin q × Fin q => z ij.1 ij.2) =
      -(fun ij : Fin q × Fin q => w ij.1 ij.2) ↔ z = -w :=
    heq z (-w)
  simp only [originalG, Prod.mk.injEq, outer_fibres hu hv, hz0, hw0, hzw, hneg]

/-- Perfect shuffle with the scalar row-major convention of the manuscript. -/
def scalarShuffle (k b : ℕ) : Equiv.Perm (Fin (k*b)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin k) (Fin b))).trans
    (finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.mul_comm b k))))

def localFamily (q : ℕ) : Set (Mat (q*2)) :=
  let P := permMatrix (scalarShuffle q 2)
  {M | InA3Orth 2 q 2 P Pᵀ M}

def basePoint {q : ℕ} (Q₀ : Mat q) : Mat (q*2) := fun i j =>
  let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
  let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
  Q₀ ri.1 rj.1 * (1 : Mat 2) ri.2 rj.2

/-- Exact local Euclidean-chart property in the induced topology.
The target may be any open Euclidean set; it is not restricted to round balls. -/
def EuclideanAtSubset {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (d : ℕ) (V : Set (EuclideanSpace ℝ (Fin d))), IsOpen V ∧
      Nonempty (↥(S ∩ U) ≃ₜ ↥V)

/-- The actual determinantal cone, not an abstract singularity tag. -/
def rankOneCone (d : ℕ) := {Z : Matrix (Fin 2) (Fin d) ℝ // Matrix.rank Z ≤ 1}

end GS
