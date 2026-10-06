module

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Supplementary exact consequences and counterchecks.
These do not replace dimension theory, a cost model, or empirical validation.
 -/

noncomputable section
open Matrix
namespace GS

/-- The dimensional-deficiency polynomial from the CS appendix. -/
theorem dimension_deficit_identity (p q : ℝ) :
    p*q*(p*q-1)/2 - (q*p*(p-1)+p*q*(q-1)/2) = p*q/2*(p-1)*(q-2) := by
  ring

theorem dimension_deficit_positive (p q : ℝ) (hp : 1 < p) (hq : 2 < q) :
    0 < p*q/2*(p-1)*(q-2) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  exact mul_pos (mul_pos (div_pos (mul_pos hp0 hq0) (by norm_num))
    (sub_pos.mpr hp)) (sub_pos.mpr hq)

/-- Parameter-count rewriting, not a formal analysis of PyTorch run time. -/
theorem block_storage_identity (k b n : ℕ) (h : k*b=n) : k*b^2=n*b := by
  rw [pow_two, ← Nat.mul_assoc, h]

/-- Fixed permutations do not make the factor-to-matrix map injective. -/
theorem factor_sign_ambiguity {n : ℕ} (P : Mat n) :
    (- (1 : Mat n))*P*(- (1 : Mat n)) = P := by simp

theorem distinct_factor_signs : (1 : Mat 4) ≠ - (1 : Mat 4) := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [Matrix.one_apply] at he

def nilpotent2 : Mat 2 := !![0,1;0,0]

theorem nilpotent2_sq : nilpotent2*nilpotent2=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotent2,Matrix.mul_apply,Fin.sum_univ_succ]

theorem nilpotent2_ne_zero : nilpotent2 ≠ 0 := by
  intro h
  have he := congrFun (congrFun h 0) 1
  norm_num [nilpotent2] at he

/-- A nonzero square-zero real matrix cannot be similar to a diagonal matrix.
Both inverse equations appear explicitly, rather than assuming arbitrary inverses. -/
theorem square_zero_not_diagonal_similar {n : ℕ} (N : Mat n)
    (hN : N*N=0) (hne : N ≠ 0) :
    ¬ ∃ (U V : Mat n) (d : Fin n → ℝ), U*V=1 ∧ V*U=1 ∧ N=U*Matrix.diagonal d*V := by
  rintro ⟨U,V,d,hUV,hVU,he⟩
  let D := Matrix.diagonal d
  have hD : D=V*N*U := by
    symm
    calc
      V*N*U = (V*U)*D*(V*U) := by rw [he]; simp only [D,Matrix.mul_assoc]
      _ = D := by rw [hVU]; simp
  have hDsq : D*D=0 := by
    calc
      D*D = (V*N*U)*(V*N*U) := by rw [hD]
      _ = V*N*(U*V)*N*U := by simp only [Matrix.mul_assoc]
      _ = V*(N*N)*U := by rw [hUV]; simp [Matrix.mul_assoc]
      _ = 0 := by rw [hN]; simp
  have hd : d=0 := by
    funext i
    have hi := congrFun (congrFun hDsq i) i
    have hsq : d i*d i=0 := by simpa [D,Matrix.mul_apply,Matrix.diagonal] using hi
    exact mul_self_eq_zero.mp hsq
  apply hne
  rw [he,hd]
  change U * Matrix.diagonal (fun _ => (0 : ℝ)) * V = 0
  rw [Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

def invertibleExample4 : Mat 4 := !![1,0,1,0;0,1,0,1;0,1,1,0;0,0,0,1]
def inverseExample4 : Mat 4 := !![1,1,-1,-1;0,1,0,-1;0,-1,1,1;0,0,0,1]

theorem invertibleExample4_inverse :
    invertibleExample4*inverseExample4=1 ∧ inverseExample4*invertibleExample4=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [invertibleExample4,inverseExample4,Matrix.mul_apply,
      Matrix.one_apply,Fin.sum_univ_succ]

/-- Arithmetic check of the eight displayed Euclidean Muon measurements.
This is not a theorem about the outcomes of training or their statistical significance. -/
theorem reported_muon_mean :
    ((86.75+94.72+64.57+90.03+92.17+77.62+88.73+90.59 : ℚ)/8)=85.6475 := by
  norm_num

theorem reported_riemannian_muon_mean :
    ((87.00+95.07+63.56+90.14+92.11+79.06+89.46+90.40 : ℚ)/8)=85.85 := by
  norm_num

end GS
