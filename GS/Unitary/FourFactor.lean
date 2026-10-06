module

public import GS.M4Necessary
public import GS.Unitary.RealEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Unitary four-factor insufficiency

The exact real counterexample remains a counterexample when arbitrary complex
unitary blocks are permitted. This does not follow merely from its real
nonfactorization: we prove the determinant-modulus obstruction for all complex
unitary factors, then transfer the exact real certificate through ℝ → ℂ.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryGeometry

def product4 {n : ℕ} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def CInA4 {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

end GS.UnitaryGeometry

namespace GS.UnitaryFour
open GS.UnitaryGeometry
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def P : CMat 6 := ofRealMatrix GS.M4.P
def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2*i.val+a.val, by omega⟩

def detBlock (M : CMat 6) (i j : Fin 3) : ℂ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)

theorem detBlock_eq_det (M : CMat 6) (i j : Fin 3) :
    detBlock M i j = Matrix.det (M.submatrix (cell i) (cell j)) := by
  rw [Matrix.det_fin_two]
  rfl

def normDetBlock (A : CMat 6) (i j : Fin 3) : ℝ := ‖detBlock A i j‖

def determinantObstruction (A : CMat 6) : Prop :=
  let d := normDetBlock A
  (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1

def block2 (A : CMat 6) (i j : Fin 3) : CMat 2 := A.submatrix (cell i) (cell j)

def assemble (A : Fin 3 → CMat 2) : CMat 6 :=
  !![A 0 0 0,A 0 0 1,0,0,0,0;
     A 0 1 0,A 0 1 1,0,0,0,0;
     0,0,A 1 0 0,A 1 0 1,0,0;
     0,0,A 1 1 0,A 1 1 1,0,0;
     0,0,0,0,A 2 0 0,A 2 0 1;
     0,0,0,0,A 2 1 0,A 2 1 1]

theorem block_diagonal_decompose (A : CMat 6) (hA : CBlockDiagonal 2 A) :
    A = assemble (fun i => block2 A i i) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [assemble,block2,cell] <;> apply hA <;> decide

theorem block2_assemble_diag (A : Fin 3 → CMat 2) (i : Fin 3) :
    block2 (assemble A) i i = A i := by
  apply Matrix.ext
  intro a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl

theorem block2_left_assembled (A : Fin 3 → CMat 2) (C : CMat 6) (i j : Fin 3) :
    block2 (assemble A*C) i j = A i * block2 C i j := by
  apply Matrix.ext
  intro a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [block2,cell,assemble,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem block2_right_assembled (C : CMat 6) (B : Fin 3 → CMat 2) (i j : Fin 3) :
    block2 (C*assemble B) i j = block2 C i j * B j := by
  apply Matrix.ext
  intro a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [block2,cell,assemble,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem block2_outer_assembled (A B : Fin 3 → CMat 2) (C : CMat 6) (i j : Fin 3) :
    block2 (assemble A*C*assemble B) i j = A i * block2 C i j * B j := by
  rw [block2_right_assembled, block2_left_assembled]

theorem block2_outer (A C B : CMat 6) (hA : CBlockDiagonal 2 A)
    (hB : CBlockDiagonal 2 B) (i j : Fin 3) :
    block2 (A*C*B) i j = block2 A i i * block2 C i j * block2 B j j := by
  have ha := block_diagonal_decompose A hA
  have hb := block_diagonal_decompose B hB
  conv_lhs => rw [ha,hb]
  exact block2_outer_assembled _ _ _ _ _

theorem block2_unitary (A : CMat 6) (hA : CBlockDiagonal 2 A)
    (ho : Unitary A) (r : Fin 3) : Unitary (block2 A r r) := by
  have ha := block_diagonal_decompose A hA
  constructor
  · apply Matrix.ext
    intro i j
    have h := congrFun (congrFun ho.1 (cell r i)) (cell r j)
    rw [ha] at h
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simpa [block2,cell,assemble,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Matrix.one_apply,Fin.sum_univ_succ] using h
  · apply Matrix.ext
    intro i j
    have h := congrFun (congrFun ho.2 (cell r i)) (cell r j)
    rw [ha] at h
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simpa [block2,cell,assemble,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Matrix.one_apply,Fin.sum_univ_succ] using h

theorem norm_det_unitary {n : ℕ} (U : CMat n) (hU : Unitary U) : ‖U.det‖=1 := by
  have h := congrArg (fun A : CMat n => ‖A.det‖) hU.1
  have hs : ‖U.det‖^2 = (1 : ℝ) := by
    simpa [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, pow_two] using h
  nlinarith [norm_nonneg U.det]

theorem normDetBlock_outer (A C B : CMat 6)
    (hA : CBlockDiagonal 2 A) (hB : CBlockDiagonal 2 B)
    (hoA : Unitary A) (hoB : Unitary B) (i j : Fin 3) :
    normDetBlock (A*C*B) i j = normDetBlock C i j := by
  unfold normDetBlock
  rw [detBlock_eq_det (A*C*B) i j, detBlock_eq_det C i j]
  change ‖Matrix.det (block2 (A*C*B) i j)‖ = ‖Matrix.det (block2 C i j)‖
  rw [block2_outer A C B hA hB i j]
  simp only [Matrix.det_mul,norm_mul]
  rw [norm_det_unitary _ (block2_unitary A hA hoA i),
    norm_det_unitary _ (block2_unitary B hB hoB j)]
  simp

/-- The entry-modulus identities hold for all complex unitary 2×2 blocks. -/
theorem unitary2_norm (W : CMat 2) (hW : Unitary W) :
    ‖W 1 0‖=‖W 0 1‖ ∧ ‖W 1 1‖=‖W 0 0‖ ∧ ‖W 0 0‖^2+‖W 0 1‖^2=1 := by
  have hc0 : ‖W 0 0‖^2 + ‖W 1 0‖^2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using congrArg Complex.re (congrFun (congrFun hW.1 0) 0)
  have hc1 : ‖W 0 1‖^2 + ‖W 1 1‖^2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using congrArg Complex.re (congrFun (congrFun hW.1 1) 1)
  have hr0 : ‖W 0 0‖^2 + ‖W 0 1‖^2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using congrArg Complex.re (congrFun (congrFun hW.2 0) 0)
  refine ⟨?_, ?_, hr0⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith only [hc0, hr0]
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith only [hc1, hr0]

def coreDetTable (W Y : Fin 3 → CMat 2) : CMat 3 :=
  !![-W 0 0 1*W 1 0 1*Y 1 0 1*Y 0 1 0,
      W 0 0 0*W 1 0 0*Y 2 0 0*Y 0 0 1,
      W 1 0 0*W 0 0 1*Y 1 0 0*Y 2 0 1;
     -W 2 0 0*W 0 1 0*Y 0 0 0*Y 1 1 1,
     -W 2 0 1*W 0 1 0*Y 0 0 1*Y 2 1 0,
     -W 2 0 1*W 0 1 1*Y 1 0 0*Y 2 1 1;
      W 2 1 0*W 1 1 1*Y 0 1 0*Y 1 1 1,
      W 1 1 1*W 2 1 1*Y 2 1 0*Y 0 1 1,
     -W 1 1 0*W 2 1 0*Y 2 0 1*Y 1 1 0]

theorem core_detTable (W Y : Fin 3 → CMat 2) :
    (fun i j => detBlock (P*assemble W*P*assemble Y*P) i j) = coreDetTable W Y := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [detBlock,cell,P,GS.M4.P,ofRealMatrix,assemble,coreDetTable,Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

def canonicalDetTable (a b e f : Fin 3 → ℝ) : Mat 3 :=
  !![b 0*b 1*f 1*f 0, a 0*a 1*e 2*f 0, a 1*b 0*e 1*f 2;
     a 2*b 0*e 0*e 1, b 2*b 0*f 0*f 2, b 2*a 0*e 1*e 2;
     b 2*a 1*f 0*e 1, a 1*a 2*f 2*e 0, b 1*b 2*f 2*f 1]

theorem core_normDetTable (W Y : Fin 3 → CMat 2)
    (hW : ∀ i, Unitary (W i)) (hY : ∀ i, Unitary (Y i)) :
    normDetBlock (P*assemble W*P*assemble Y*P) =
      canonicalDetTable (fun i => ‖W i 0 0‖) (fun i => ‖W i 0 1‖)
        (fun i => ‖Y i 0 0‖) (fun i => ‖Y i 0 1‖) := by
  apply Matrix.ext
  intro i j
  have hw0 := unitary2_norm (W 0) (hW 0)
  have hw1 := unitary2_norm (W 1) (hW 1)
  have hw2 := unitary2_norm (W 2) (hW 2)
  have hy0 := unitary2_norm (Y 0) (hY 0)
  have hy1 := unitary2_norm (Y 1) (hY 1)
  have hy2 := unitary2_norm (Y 2) (hY 2)
  have hd := congrFun (congrFun (core_detTable W Y) i) j
  unfold normDetBlock
  rw [hd]
  fin_cases i <;> fin_cases j <;>
    simp [coreDetTable,canonicalDetTable,norm_mul,
      hw0.1,hw0.2.1,hw1.1,hw1.2.1,hw2.1,hw2.2.1,
      hy0.1,hy0.2.1,hy1.1,hy1.2.1,hy2.1,hy2.2.1]

theorem canonical_obstruction (a b e f : Fin 3 → ℝ)
    (hW : ∀ i, (a i)^2+(b i)^2=1) (hY : ∀ i, (e i)^2+(f i)^2=1)
    (hden : canonicalDetTable a b e f 2 1 * canonicalDetTable a b e f 1 0 *
      canonicalDetTable a b e f 1 1 ≠ 0) :
    let d := canonicalDetTable a b e f
    (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1 :=
  GS.M4.canonical_obstruction a b e f hW hY hden

theorem core_necessary (W Y : Fin 3 → CMat 2)
    (hW : ∀ i, Unitary (W i)) (hY : ∀ i, Unitary (Y i))
    (hden : normDetBlock (P*assemble W*P*assemble Y*P) 2 1 *
      normDetBlock (P*assemble W*P*assemble Y*P) 1 0 *
      normDetBlock (P*assemble W*P*assemble Y*P) 1 1 ≠ 0) :
    determinantObstruction (P*assemble W*P*assemble Y*P) := by
  unfold determinantObstruction
  rw [core_normDetTable W Y hW hY] at hden ⊢
  apply canonical_obstruction _ _ _ _ _ _ hden
  · intro i; exact (unitary2_norm (W i) (hW i)).2.2
  · intro i; exact (unitary2_norm (Y i) (hY i)).2.2

/-- Universal necessity for the precise m=4 class in the manuscript. -/
theorem necessaryCondition (A : CMat 6) (h : CInA4Unitary 2 2 2 2 P P P A)
    (hden : normDetBlock A 2 1 * normDetBlock A 1 0 * normDetBlock A 1 1 ≠ 0) :
    determinantObstruction A := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,ho₁,ho₂,ho₃,ho₄,he⟩
  let C₀ := P*B₃*P*B₂*P
  have he' : A=B₄*C₀*B₁ := by
    rw [he]
    simp only [GS.UnitaryGeometry.product4,C₀,Matrix.mul_assoc]
  have hd : normDetBlock A=normDetBlock C₀ := by
    funext i j
    rw [he']
    exact normDetBlock_outer B₄ C₀ B₁ hb₄ hb₁ ho₄ ho₁ i j
  unfold determinantObstruction
  rw [hd] at hden ⊢
  have hb₂' := block_diagonal_decompose B₂ hb₂
  have hb₃' := block_diagonal_decompose B₃ hb₃
  have hcore : C₀ = P*assemble (fun i => block2 B₃ i i)*P*
      assemble (fun i => block2 B₂ i i)*P := by
    dsimp [C₀]
    conv_lhs => rw [hb₂',hb₃']
  rw [hcore] at hden ⊢
  exact core_necessary _ _ (block2_unitary B₃ hb₃ ho₃)
    (block2_unitary B₂ hb₂ ho₂) hden


end GS.UnitaryFour
