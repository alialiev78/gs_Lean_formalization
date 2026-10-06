module

public import GS.GeometryAlgebra
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact m=4 example from the manuscript

Polynomial certificates are expressed as
Lean `linear_combination` proofs, not accepted as external numerical oracles.

The generic necessity proof and non-membership theorem are in M4Necessary.lean.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

def B2 : Mat 6 := !![1, 1, 0, 0, 0, 0;
  1, -3, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0;
  0, 0, 1, (-1/3 : ℝ), 0, 0;
  0, 0, 0, 0, 1, 1;
  0, 0, 0, 0, 1, (1/3 : ℝ)]

def B3 : Mat 6 := !![1, 1, 0, 0, 0, 0;
  1, (1/3 : ℝ), 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0;
  0, 0, 1, (-1/3 : ℝ), 0, 0;
  0, 0, 0, 0, 1, 1;
  0, 0, 0, 0, 1, -3]

def C : Mat 6 := !![1, 1, 1, 0, 1, 0;
  1, 0, -3, 1, 0, 1;
  0, (-1/3 : ℝ), 0, 1, 1, (1/3 : ℝ);
  1, (1/3 : ℝ), 1, 0, (1/3 : ℝ), 0;
  (-1/3 : ℝ), 0, 1, 1, 0, 1;
  0, (-1/3 : ℝ), 0, -3, 1, -1]

def H : Mat 6 := !![(7/4 : ℝ), -3, 0, 0, 0, 0;
  -3, (21/4 : ℝ), 0, 0, 0, 0;
  0, 0, (1/4 : ℝ), (1/3 : ℝ), 0, 0;
  0, 0, (1/3 : ℝ), (1/2 : ℝ), 0, 0;
  0, 0, 0, 0, (3/4 : ℝ), -1;
  0, 0, 0, 0, -1, (3/2 : ℝ)]

def G : Mat 6 := !![2, (-8/3 : ℝ), 0, 0, 0, 0;
  (-8/3 : ℝ), 4, 0, 0, 0, 0;
  0, 0, (4/3 : ℝ), (8/9 : ℝ), 0, 0;
  0, 0, (8/9 : ℝ), (2/3 : ℝ), 0, 0;
  0, 0, 0, 0, (28/9 : ℝ), (-16/3 : ℝ);
  0, 0, 0, 0, (-16/3 : ℝ), (28/3 : ℝ)]

def permutation : Equiv.Perm (Fin 6) where
  toFun := ![0,3,1,4,2,5]
  invFun := ![0,2,4,1,3,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem P_is_permutation : P = permMatrix permutation := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem P_orthogonal : Orthogonal P := by
  rw [P_is_permutation]
  exact perm_orthogonal permutation

def B1Param (s2 s3 s7 : ℝ) : Mat 6 := !![((1/2 : ℝ) * s7), 0, 0, 0, 0, 0;
  ((-6/7 : ℝ) * s7), ((1/14 : ℝ) * s3 * s7), 0, 0, 0, 0;
  0, 0, (1/2 : ℝ), 0, 0, 0;
  0, 0, (2/3 : ℝ), ((1/6 : ℝ) * s2), 0, 0;
  0, 0, 0, 0, ((1/2 : ℝ) * s3), 0;
  0, 0, 0, 0, ((-2/3 : ℝ) * s3), ((1/6 : ℝ) * s2 * s3)]

def B4Param (s2 s3 s7 : ℝ) : Mat 6 := !![((1/2 : ℝ) * s2), 0, 0, 0, 0, 0;
  2, (3/2 : ℝ), 0, 0, 0, 0;
  0, 0, ((1/2 : ℝ) * s3), 0, 0, 0;
  0, 0, (-1 * s2 * s3), ((3/2 : ℝ) * s2 * s3), 0, 0;
  0, 0, 0, 0, ((3/14 : ℝ) * s7), 0;
  0, 0, 0, 0, ((6/7 : ℝ) * s3 * s7), ((1/2 : ℝ) * s3 * s7)]

theorem core_identity : P*B3*P*B2*P = C := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp

theorem metric_identity : C*H*Cᵀ = G := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp

theorem gram_B1 (s2 s3 s7 : ℝ) (h2 : s2^2=2) (h3 : s3^2=3) (h7 : s7^2=7) : B1Param s2 s3 s7 * (B1Param s2 s3 s7)ᵀ = H := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/4 : ℝ) * h7 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (-3/7 : ℝ) * h7 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (-3/7 : ℝ) * h7 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/196 : ℝ) * (s7 ^ 2)) * h3 + (3/4 : ℝ) * h7 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/36 : ℝ) * h2 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/4 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (-1/3 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (-1/3 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/36 : ℝ) * (s3 ^ 2)) * h2 + (1/2 : ℝ) * h3 | nlinarith [h2, h3, h7]

theorem normalize_B4 (s2 s3 s7 : ℝ) (h2 : s2^2=2) (h3 : s3^2=3) (h7 : s7^2=7) : B4Param s2 s3 s7 * G * (B4Param s2 s3 s7)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/2 : ℝ) * h2 | nlinarith [h2, h3, h7]
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/3 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/6 : ℝ) * (s3 ^ 2)) * h2 + (1/3 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/7 : ℝ) * h7 | nlinarith [h2, h3, h7]
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      ring <;> simp
  · norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/21 : ℝ) * (s7 ^ 2)) * h3 + (1/7 : ℝ) * h7 | nlinarith [h2, h3, h7]

def B1 : Mat 6 := B1Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def B4 : Mat 6 := B4Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def Q : Mat 6 := B4*C*B1

theorem sqrt2_sq : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt3_sq : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt7_sq : (Real.sqrt 7)^2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)

theorem Q_orthogonal : Orthogonal Q := by
  exact gram_completion C H G B1 B4 metric_identity
    (gram_B1 _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq)
    (normalize_B4 _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq)

theorem B1_supported : BlockDiagonal 2 B1 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B1,B1Param] at *
theorem B2_supported : BlockDiagonal 2 B2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B2] at *
theorem B3_supported : BlockDiagonal 2 B3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B3] at *
theorem B4_supported : BlockDiagonal 2 B4 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B4,B4Param] at *

theorem Q_factorization : Q = product4 B4 P B3 P B2 P B1 := by
  unfold Q product4
  rw [← core_identity]
  simp only [Matrix.mul_assoc]

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q :=
  ⟨B1,B2,B3,B4,B1_supported,B2_supported,B3_supported,B4_supported,Q_factorization⟩

def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2*i.val+a.val, by omega⟩
def detBlock (M : Mat 6) (i j : Fin 3) : ℝ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)

theorem detBlock_eq_det (M : Mat 6) (i j : Fin 3) :
    detBlock M i j = Matrix.det (M.submatrix (cell i) (cell j)) := by
  rw [Matrix.det_fin_two]
  rfl

def detTable (s2 s3 : ℝ) : Mat 3 := !![((-3/16 : ℝ) * s2 * s3), (1/8 : ℝ), (3/8 : ℝ);
  ((3/16 : ℝ) * s2 * s3), (-3/8 : ℝ), (-1/8 : ℝ);
  (1/16 : ℝ), ((-3/16 : ℝ) * s2 * s3), ((-3/16 : ℝ) * s2 * s3)]

theorem detTable_param (s2 s3 s7 : ℝ) (h2 : s2^2=2) (h3 : s3^2=3) (h7 : s7^2=7) : (fun i j => detBlock (B4Param s2 s3 s7*C*B1Param s2 s3 s7) i j) = detTable s2 s3 := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((-3/112 : ℝ) * s2 * s3) * h7 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination (1/16 : ℝ) * h2 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/16 : ℝ) * (s3 ^ 2)) * h2 + (1/8 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/112 : ℝ) * s2 * s3 * (s7 ^ 2)) * h3 + ((3/112 : ℝ) * s2 * s3) * h7 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((-1/16 : ℝ) * (s3 ^ 2)) * h2 + (-1/8 : ℝ) * h3 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((-1/144 : ℝ) * (s3 ^ 4)) * h2 + ((-1/24 : ℝ) + ((-1/72 : ℝ) * (s3 ^ 2))) * h3 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((1/2352 : ℝ) * (s7 ^ 4)) * h3 + ((1/112 : ℝ) + ((1/784 : ℝ) * (s7 ^ 2))) * h7 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((-3/112 : ℝ) * s2 * s3) * h7 | nlinarith [h2, h3, h7]
  · norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      first | linear_combination ((-1/112 : ℝ) * s2 * s3 * (s7 ^ 2)) * h3 + ((-3/112 : ℝ) * s2 * s3) * h7 | nlinarith [h2, h3, h7]

theorem detTable_Q : (fun i j => detBlock Q i j) = detTable (Real.sqrt 2) (Real.sqrt 3) :=
  detTable_param _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq

/-- Numerical end of the determinant obstruction. This arithmetic alone is
NOT the proof that Q has no orthogonal four-factor representation. -/
theorem obstruction_values_contradict : ¬ ((1-(3/8 : ℝ))*(1-3/8) ≥ (9/16 : ℝ)) := by
  norm_num

end GS.M4
