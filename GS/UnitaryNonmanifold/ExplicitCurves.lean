module

public import GS.UnitaryNonmanifold.TangentObstruction
public import GS.Unitary.RealEmbedding
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Two explicit feasible unitary three-factor curves

The matrices have rational base points and rational change of two-dimensional
basis. Only the scalar sine and cosine curves are used.
-/

noncomputable section
open Matrix Filter GS.UnitaryGeometry
open scoped Topology
namespace GS.UnitaryNonmanifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def witnessQ : Mat 3 :=
  !![1/3, -2/3, -2/3; -2/3, 1/3, -2/3; -2/3, -2/3, 1/3]

def witnessH : Mat 2 := !![3/5, -4/5; 4/5, 3/5]

theorem witnessQ_orthogonal : Orthogonal witnessQ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [witnessQ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem witnessH_orthogonal : Orthogonal witnessH := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [witnessH, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

def rotate01 (t : ℝ) : Mat 3 :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

def rotate02 (t : ℝ) : Mat 3 :=
  !![Real.cos t, 0, -Real.sin t; 0, 1, 0; Real.sin t, 0, Real.cos t]

def skew01 : Mat 3 := !![0,-1,0; 1,0,0; 0,0,0]
def skew02 : Mat 3 := !![0,0,-1; 0,0,0; 1,0,0]

theorem rotate01_orthogonal (t : ℝ) : Orthogonal (rotate01 t) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotate01, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  all_goals nlinarith [Real.sin_sq_add_cos_sq t]

theorem rotate02_orthogonal (t : ℝ) : Orthogonal (rotate02 t) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotate02, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  all_goals nlinarith [Real.sin_sq_add_cos_sq t]

@[simp] theorem rotate01_zero : rotate01 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotate01]
@[simp] theorem rotate02_zero : rotate02 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotate02]

theorem derivative_rotate01 : HasDerivAt rotate01 skew01 0 := by
  have hc : HasDerivAt Real.cos 0 0 := by simpa using Real.hasDerivAt_cos 0
  have hs : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  have hn : HasDerivAt (fun t : ℝ => -Real.sin t) (-1) 0 := by
    simpa only [Pi.neg_def] using hs.neg
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact hc | exact hs | exact hn | exact hasDerivAt_const (0 : ℝ) _

theorem derivative_rotate02 : HasDerivAt rotate02 skew02 0 := by
  have hc : HasDerivAt Real.cos 0 0 := by simpa using Real.hasDerivAt_cos 0
  have hs : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  have hn : HasDerivAt (fun t : ℝ => -Real.sin t) (-1) 0 := by
    simpa only [Pi.neg_def] using hs.neg
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact hc | exact hs | exact hn | exact hasDerivAt_const (0 : ℝ) _

theorem derivative_ofRealMatrix {n : ℕ} {f : ℝ → Mat n} {v : Mat n}
    (hf : HasDerivAt f v 0) :
    HasDerivAt (fun t => ofRealMatrix (f t)) (ofRealMatrix v) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) j).ofReal_comp

def sandwichMatrix {q : ℕ} (H : CMat 2) (A B : CMat q) : CMat (q*2) :=
  fun i j =>
    let x : Fin q × Fin 2 := finProdFinEquiv.symm i
    let y : Fin q × Fin 2 := finProdFinEquiv.symm j
    (H * diagTwo (A x.1 y.1) (B x.1 y.1) * Hᴴ) x.2 y.2

@[simp] theorem cBlock_sandwichMatrix {q : ℕ} (H : CMat 2) (A B : CMat q)
    (i j : Fin q) : cBlock (sandwichMatrix H A B) i j =
    H * diagTwo (A i j) (B i j) * Hᴴ := by
  ext a b
  simp [cBlock, sandwichMatrix]

theorem sandwichMatrix_mem {q : ℕ} (H : CMat 2) (A B : CMat q)
    (hH : Unitary H) (hA : Unitary A) (hB : Unitary B) :
    BlockSandwich (sandwichMatrix H A B) := by
  exact ⟨fun _ => H, fun _ => Hᴴ, A, B, fun _ => hH,
    fun _ => hH.conjTranspose, hA, hB, cBlock_sandwichMatrix H A B⟩

def sandwichCurve (H : CMat 2) (R : ℝ → CMat 3) (t : ℝ) : CMat 6 :=
  sandwichMatrix H (ofRealMatrix witnessQ * R t) (ofRealMatrix witnessQ * R (-t))

def sandwichVelocity (H : CMat 2) (S : CMat 3) : CMat 6 :=
  sandwichMatrix H (ofRealMatrix witnessQ * S) (-(ofRealMatrix witnessQ * S))

def witnessBase : CMat 6 := fun i j =>
  let x : Fin 3 × Fin 2 := finProdFinEquiv.symm i
  let y : Fin 3 × Fin 2 := finProdFinEquiv.symm j
  ofRealMatrix witnessQ x.1 y.1 * (1 : CMat 2) x.2 y.2

@[simp] theorem cBlock_witnessBase (i j : Fin 3) :
    cBlock witnessBase i j = ofRealMatrix witnessQ i j • 1 := by
  ext a b
  simp only [cBlock,witnessBase,Equiv.symm_apply_apply,Matrix.smul_apply,smul_eq_mul]
  congr 1
  exact congrArg₂ (fun a b : Fin 2 => (1 : CMat 2) a b)
    (congrArg Prod.snd ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm_apply_apply (i,a)))
    (congrArg Prod.snd ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm_apply_apply (j,b)))

theorem diagTwo_self (a : ℂ) : diagTwo a a = a • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo]

theorem sandwichCurve_zero (H : CMat 2) (R : ℝ → CMat 3)
    (hH : Unitary H) (hR : R 0 = 1) : sandwichCurve H R 0 = witnessBase := by
  ext i j
  simp only [sandwichCurve, neg_zero, hR, Matrix.mul_one, sandwichMatrix,witnessBase]
  rw [diagTwo_self]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hH.2]
  rfl

theorem derivative_diagTwo {a b : ℝ → ℂ} {u v : ℂ}
    (ha : HasDerivAt a u 0) (hb : HasDerivAt b v 0) :
    HasDerivAt (fun t => diagTwo (a t) (b t)) (diagTwo u v) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp only [diagTwo, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ite_true, ite_false]
  · exact ha
  · exact hasDerivAt_const 0 0
  · exact hasDerivAt_const 0 0
  · exact hb

theorem derivative_sandwichMatrix {q : ℕ} (H : CMat 2)
    {A B : ℝ → CMat q} {U V : CMat q}
    (hA : HasDerivAt A U 0) (hB : HasDerivAt B V 0) :
    HasDerivAt (fun t => sandwichMatrix H (A t) (B t)) (sandwichMatrix H U V) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  let x : Fin q × Fin 2 := finProdFinEquiv.symm i
  let y : Fin q × Fin 2 := finProdFinEquiv.symm j
  have hd := derivative_diagTwo
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA x.1)) y.1)
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hB x.1)) y.1)
  have hh := derivative_matrix_mul (derivative_matrix_mul (hasDerivAt_const 0 H) hd)
    (hasDerivAt_const 0 Hᴴ)
  simpa only [sandwichMatrix, x, y, zero_mul, zero_add, mul_zero, add_zero] using
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hh x.2)) y.2)

theorem derivative_sandwichCurve (H : CMat 2) {R : ℝ → CMat 3} {S : CMat 3}
    (hR : HasDerivAt R S 0) :
    HasDerivAt (sandwichCurve H R) (sandwichVelocity H S) 0 := by
  have hneg : HasDerivAt (fun t : ℝ => R (-t)) (-S) 0 := by
    have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := by
      simpa only [Pi.neg_def, id_eq] using (hasDerivAt_id (0 : ℝ)).neg
    have hr : HasDerivAt R S (-(0 : ℝ)) := by simpa using hR
    simpa only [Function.comp_def, neg_one_smul] using hr.scomp 0 hn
  have hA := derivative_matrix_mul (hasDerivAt_const 0 (ofRealMatrix witnessQ)) hR
  have hB := derivative_matrix_mul (hasDerivAt_const 0 (ofRealMatrix witnessQ)) hneg
  simp only [zero_mul, zero_add, Matrix.mul_neg] at hA hB
  exact derivative_sandwichMatrix H hA hB

end GS.UnitaryNonmanifold
