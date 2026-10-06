module

public import GS.M4Obstruction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Necessity of the four-factor determinant obstruction

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def block2 (A : Mat 6) (i j : Fin 3) : Mat 2 := A.submatrix (cell i) (cell j)

def assemble (A : Fin 3 → Mat 2) : Mat 6 :=
  !![A 0 0 0,A 0 0 1,0,0,0,0;
     A 0 1 0,A 0 1 1,0,0,0,0;
     0,0,A 1 0 0,A 1 0 1,0,0;
     0,0,A 1 1 0,A 1 1 1,0,0;
     0,0,0,0,A 2 0 0,A 2 0 1;
     0,0,0,0,A 2 1 0,A 2 1 1]

theorem block_diagonal_decompose (A : Mat 6) (hA : BlockDiagonal 2 A) :
    A = assemble (fun i => block2 A i i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [assemble,block2,cell] <;> apply hA <;> decide

theorem block2_assemble_diag (A : Fin 3 → Mat 2) (i : Fin 3) :
    block2 (assemble A) i i = A i := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl

theorem block2_outer_assembled (A B : Fin 3 → Mat 2) (C : Mat 6) (i j : Fin 3) :
    block2 (assemble A*C*assemble B) i j = A i * block2 C i j * B j := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [block2,cell,assemble,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] <;> ring

theorem block2_outer (A C B : Mat 6) (hA : BlockDiagonal 2 A)
    (hB : BlockDiagonal 2 B) (i j : Fin 3) :
    block2 (A*C*B) i j = block2 A i i * block2 C i j * block2 B j j := by
  have ha := block_diagonal_decompose A hA
  have hb := block_diagonal_decompose B hB
  conv_lhs => rw [ha,hb]
  exact block2_outer_assembled _ _ _ _ _

theorem block2_orthogonal (A : Mat 6) (hA : BlockDiagonal 2 A)
    (ho : Orthogonal A) (r : Fin 3) : Orthogonal (block2 A r r) := by
  have ha := block_diagonal_decompose A hA
  constructor
  · ext i j
    have h := congrFun (congrFun ho.1 (cell r i)) (cell r j)
    rw [ha] at h
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simpa [block2,cell,assemble,Matrix.mul_apply,Matrix.transpose_apply,
        Matrix.one_apply,Fin.sum_univ_succ] using h
  · ext i j
    have h := congrFun (congrFun ho.2 (cell r i)) (cell r j)
    rw [ha] at h
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simpa [block2,cell,assemble,Matrix.mul_apply,Matrix.transpose_apply,
        Matrix.one_apply,Fin.sum_univ_succ] using h

theorem abs_eq_of_squares_eq (x y : ℝ) (h : x^2=y^2) : |x|=|y| := by
  have hp : (x-y)*(x+y)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with he | he
  · rw [sub_eq_zero.mp he]
  · have hx : x = -y := by linarith
    rw [hx,abs_neg]

theorem abs_det_orthogonal {n : ℕ} (U : Mat n) (hU : Orthogonal U) : |U.det|=1 := by
  have h := congrArg Matrix.det hU.1
  have hs : U.det^2=(1 : ℝ)^2 := by
    simpa [Matrix.det_mul,Matrix.det_transpose,pow_two] using h
  simpa using abs_eq_of_squares_eq U.det 1 hs

theorem absDetBlock_outer (A C B : Mat 6)
    (hA : BlockDiagonal 2 A) (hB : BlockDiagonal 2 B)
    (hoA : Orthogonal A) (hoB : Orthogonal B) (i j : Fin 3) :
    absDetBlock (A*C*B) i j = absDetBlock C i j := by
  unfold absDetBlock
  rw [detBlock_eq_det (A*C*B) i j, detBlock_eq_det C i j]
  change |Matrix.det (block2 (A*C*B) i j)| = |Matrix.det (block2 C i j)|
  rw [block2_outer A C B hA hB i j]
  simp only [Matrix.det_mul,abs_mul]
  rw [abs_det_orthogonal _ (block2_orthogonal A hA hoA i),
    abs_det_orthogonal _ (block2_orthogonal B hB hoB j)]
  simp

/-- Entry identities of a real orthogonal two-by-two block. -/
theorem orthogonal2_abs (W : Mat 2) (hW : Orthogonal W) :
    |W 1 0|=|W 0 1| ∧ |W 1 1|=|W 0 0| ∧ |W 0 0|^2+|W 0 1|^2=1 := by
  have hc0 := congrFun (congrFun hW.1 0) 0
  have hc1 := congrFun (congrFun hW.1 1) 1
  have hr0 := congrFun (congrFun hW.2 0) 0
  norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
    Fin.sum_univ_succ] at hc0 hc1 hr0
  refine ⟨?_,?_,?_⟩
  · apply abs_eq_of_squares_eq
    nlinarith
  · apply abs_eq_of_squares_eq
    nlinarith
  · rw [sq_abs, sq_abs]
    nlinarith [hr0]

def coreDetTable (W Y : Fin 3 → Mat 2) : Mat 3 :=
  !![-W 0 0 1*W 1 0 1*Y 1 0 1*Y 0 1 0,
      W 0 0 0*W 1 0 0*Y 2 0 0*Y 0 0 1,
      W 1 0 0*W 0 0 1*Y 1 0 0*Y 2 0 1;
     -W 2 0 0*W 0 1 0*Y 0 0 0*Y 1 1 1,
     -W 2 0 1*W 0 1 0*Y 0 0 1*Y 2 1 0,
     -W 2 0 1*W 0 1 1*Y 1 0 0*Y 2 1 1;
      W 2 1 0*W 1 1 1*Y 0 1 0*Y 1 1 1,
      W 1 1 1*W 2 1 1*Y 2 1 0*Y 0 1 1,
     -W 1 1 0*W 2 1 0*Y 2 0 1*Y 1 1 0]

theorem core_detTable (W Y : Fin 3 → Mat 2) :
    (fun i j => detBlock (P*assemble W*P*assemble Y*P) i j) = coreDetTable W Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [detBlock,cell,P,assemble,coreDetTable,Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

def canonicalDetTable (a b e f : Fin 3 → ℝ) : Mat 3 :=
  !![b 0*b 1*f 1*f 0, a 0*a 1*e 2*f 0, a 1*b 0*e 1*f 2;
     a 2*b 0*e 0*e 1, b 2*b 0*f 0*f 2, b 2*a 0*e 1*e 2;
     b 2*a 1*f 0*e 1, a 1*a 2*f 2*e 0, b 1*b 2*f 2*f 1]

theorem core_absDetTable (W Y : Fin 3 → Mat 2)
    (hW : ∀ i, Orthogonal (W i)) (hY : ∀ i, Orthogonal (Y i)) :
    absDetBlock (P*assemble W*P*assemble Y*P) =
      canonicalDetTable (fun i => |W i 0 0|) (fun i => |W i 0 1|)
        (fun i => |Y i 0 0|) (fun i => |Y i 0 1|) := by
  ext i j
  have hw0 := orthogonal2_abs (W 0) (hW 0)
  have hw1 := orthogonal2_abs (W 1) (hW 1)
  have hw2 := orthogonal2_abs (W 2) (hW 2)
  have hy0 := orthogonal2_abs (Y 0) (hY 0)
  have hy1 := orthogonal2_abs (Y 1) (hY 1)
  have hy2 := orthogonal2_abs (Y 2) (hY 2)
  have hd := congrFun (congrFun (core_detTable W Y) i) j
  unfold absDetBlock
  rw [hd]
  fin_cases i <;> fin_cases j <;>
    simp [coreDetTable,canonicalDetTable,abs_mul,
      hw0.1,hw0.2.1,hw1.1,hw1.2.1,hw2.1,hw2.2.1,
      hy0.1,hy0.2.1,hy1.1,hy1.2.1,hy2.1,hy2.2.1] <;> ring

theorem canonical_obstruction (a b e f : Fin 3 → ℝ)
    (hW : ∀ i, (a i)^2+(b i)^2=1) (hY : ∀ i, (e i)^2+(f i)^2=1)
    (hden : canonicalDetTable a b e f 2 1 * canonicalDetTable a b e f 1 0 *
      canonicalDetTable a b e f 1 1 ≠ 0) :
    let d := canonicalDetTable a b e f
    (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1 := by
  let d := canonicalDetTable a b e f
  have h32 : d 2 1 ≠ 0 := by
    intro h; apply hden; change d 2 1*d 1 0*d 1 1=0; rw [h]; ring
  have h21 : d 1 0 ≠ 0 := by
    intro h; apply hden; change d 2 1*d 1 0*d 1 1=0; rw [h]; ring
  have h22 : d 1 1 ≠ 0 := by
    intro h; apply hden; change d 2 1*d 1 0*d 1 1=0; rw [h]; ring
  have r1 : d 0 2*d 1 0/d 2 1 = (b 0)^2*(e 1)^2 := by
    apply (div_eq_iff h32).mpr
    simp [d,canonicalDetTable]
    ring
  have r2 : d 0 2*d 2 1/d 1 0 = (a 1)^2*(f 2)^2 := by
    apply (div_eq_iff h21).mpr
    simp [d,canonicalDetTable]
    ring
  have r3 : d 0 0*d 2 2/d 1 1 = (b 1)^2*(f 1)^2 := by
    apply (div_eq_iff h22).mpr
    simp [d,canonicalDetTable]
    ring
  have hb : (b 0)^2 ≤ 1 := by nlinarith [hW 0, sq_nonneg (a 0)]
  have hf : (f 2)^2 ≤ 1 := by nlinarith [hY 2, sq_nonneg (e 2)]
  change (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1
  rw [r1,r2,r3]
  exact scalar_obstruction (a 1) (b 0) (e 1) (f 2) (b 1) (f 1) (hW 1) (hY 1) hb hf

theorem core_necessary (W Y : Fin 3 → Mat 2)
    (hW : ∀ i, Orthogonal (W i)) (hY : ∀ i, Orthogonal (Y i))
    (hden : absDetBlock (P*assemble W*P*assemble Y*P) 2 1 *
      absDetBlock (P*assemble W*P*assemble Y*P) 1 0 *
      absDetBlock (P*assemble W*P*assemble Y*P) 1 1 ≠ 0) :
    determinantObstruction (P*assemble W*P*assemble Y*P) := by
  unfold determinantObstruction
  rw [core_absDetTable W Y hW hY] at hden ⊢
  apply canonical_obstruction _ _ _ _ _ _ hden
  · intro i; exact (orthogonal2_abs (W i) (hW i)).2.2
  · intro i; exact (orthogonal2_abs (Y i) (hY i)).2.2

/-- Universal necessity for the precise m=4 class in the manuscript. -/
theorem necessaryCondition (A : Mat 6) (h : InA4Orth 2 2 2 2 P P P A)
    (hden : absDetBlock A 2 1 * absDetBlock A 1 0 * absDetBlock A 1 1 ≠ 0) :
    determinantObstruction A := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,ho₁,ho₂,ho₃,ho₄,he⟩
  let C₀ := P*B₃*P*B₂*P
  have he' : A=B₄*C₀*B₁ := by
    rw [he]
    simp only [product4,C₀,Matrix.mul_assoc]
  have hd : absDetBlock A=absDetBlock C₀ := by
    funext i j
    rw [he']
    exact absDetBlock_outer B₄ C₀ B₁ hb₄ hb₁ ho₄ ho₁ i j
  unfold determinantObstruction
  rw [hd] at hden ⊢
  have hb₂' := block_diagonal_decompose B₂ hb₂
  have hb₃' := block_diagonal_decompose B₃ hb₃
  have hcore : C₀ = P*assemble (fun i => block2 B₃ i i)*P*
      assemble (fun i => block2 B₂ i i)*P := by
    dsimp [C₀]
    conv_lhs => rw [hb₂',hb₃']
  rw [hcore] at hden ⊢
  exact core_necessary _ _ (block2_orthogonal B₃ hb₃ ho₃)
    (block2_orthogonal B₂ hb₂ ho₂) hden

theorem Q_not_mem_A4Orth : ¬ InA4Orth 2 2 2 2 P P P Q :=
  Q_not_mem_A4Orth_of_necessaryCondition necessaryCondition

/-- Unconditional counterexample for the specified four-factor class. -/
theorem counterexample : InA4 2 2 2 2 P P P Q ∧ Orthogonal Q ∧
    ¬ InA4Orth 2 2 2 2 P P P Q :=
  ⟨Q_mem_A4,Q_orthogonal,Q_not_mem_A4Orth⟩

end GS.M4
