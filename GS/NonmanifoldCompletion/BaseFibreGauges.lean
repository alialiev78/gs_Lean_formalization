module

public import GS.NonmanifoldCompletion.BlockExtraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact gauge normalization of every factor tuple above the scalar base matrix

The gauges are fixed diagonal sign matrices. Their values may depend on the
chosen point of the fibre; a continuous global choice on the whole fibre is
neither required nor asserted. This is suited to compact full-fibre coverage.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
open scoped BigOperators
namespace GS.NonmanifoldCompletion

def DiagonalTwo (D : Mat 2) : Prop := D 0 1=0 ∧ D 1 0=0

theorem diagonalTwo_transpose {D : Mat 2} (hD : DiagonalTwo D) : DiagonalTwo Dᵀ :=
  ⟨hD.2,hD.1⟩

theorem diagonalTwo_eq (D : Mat 2) (hD : DiagonalTwo D) :
    D = diagTwo (D 0 0) (D 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTwo,hD.1,hD.2]

theorem diagonalTwo_symmetric (D : Mat 2) (hD : DiagonalTwo D) : Dᵀ=D := by
  rw [diagonalTwo_eq D hD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTwo]

theorem diagonalTwo_mul {D E : Mat 2} (hD : DiagonalTwo D) (hE : DiagonalTwo E) :
    DiagonalTwo (D*E) := by
  constructor <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hD.1,hD.2,hE.1,hE.2]

theorem diagonalTwo_involution {D : Mat 2} (hd : DiagonalTwo D)
    (ho : Orthogonal D) : D*D=1 := by
  simpa only [diagonalTwo_symmetric D hd] using ho.1

theorem diagonalTwo_entry_sq {D : Mat 2} (hd : DiagonalTwo D)
    (ho : Orthogonal D) (a : Fin 2) : (D a a)^2=1 := by
  have h := congrFun (congrFun ho.1 a) a
  fin_cases a <;>
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
      Fin.sum_univ_two,hd.1,hd.2,pow_two] using h

/-- At a nonzero scalar block, the product of the outer factors is diagonal. -/
theorem diagonalTwo_of_scalar_block (U V : Mat 2) (hU : Orthogonal U)
    (hV : Orthogonal V) (a b t : ℝ) (ht : t≠0)
    (he : U * diagTwo a b * V = t • (1 : Mat 2)) : DiagonalTwo (V*U) := by
  have hh := congrArg (fun Z : Mat 2 => Uᵀ * Z * Vᵀ) he
  have hh' : diagTwo a b = t • (Uᵀ*Vᵀ) := by
    calc
      diagTwo a b = Uᵀ*(U*diagTwo a b*V)*Vᵀ := by
        simp only [← Matrix.mul_assoc,hU.1,Matrix.one_mul]
        rw [Matrix.mul_assoc _ V Vᵀ,hV.2,Matrix.mul_one]
      _ = Uᵀ*(t • (1 : Mat 2))*Vᵀ := hh
      _ = t • (Uᵀ*Vᵀ) := by
        simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
  have h01 := congrFun (congrFun hh' 0) 1
  have h10 := congrFun (congrFun hh' 1) 0
  have hz01 : (Uᵀ*Vᵀ) 0 1=0 := by
    have : t*(Uᵀ*Vᵀ) 0 1=0 := by simpa [diagTwo] using h01.symm
    exact (mul_eq_zero.mp this).resolve_left ht
  have hz10 : (Uᵀ*Vᵀ) 1 0=0 := by
    have : t*(Uᵀ*Vᵀ) 1 0=0 := by simpa [diagTwo] using h10.symm
    exact (mul_eq_zero.mp this).resolve_left ht
  have hdiag : DiagonalTwo (Uᵀ*Vᵀ) := ⟨hz01,hz10⟩
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using
    diagonalTwo_transpose hdiag

/-- A row-and-column gauge on a q-by-q middle factor. -/
def gaugeMiddle {q : ℕ} (D E : Fin q → Mat 2) (a : Fin 2) (A : Mat q) : Mat q :=
  Matrix.diagonal (fun i => D i a a) * A * Matrix.diagonal (fun j => E j a a)

@[simp] theorem gaugeMiddle_apply {q : ℕ} (D E : Fin q → Mat 2)
    (a : Fin 2) (A : Mat q) (i j : Fin q) :
    gaugeMiddle D E a A i j = D i a a * A i j * E j a a := by
  simp [gaugeMiddle,Matrix.mul_apply,Matrix.diagonal]

theorem signs_diagonal_orthogonal {q : ℕ} (s : Fin q → ℝ)
    (hs : ∀ i, (s i)^2=1) : Orthogonal (Matrix.diagonal s) := by
  constructor <;> ext i j <;> by_cases hij : i=j
  all_goals simp [Matrix.mul_apply,Matrix.diagonal,Matrix.transpose_apply,
    Matrix.one_apply,hij,eq_comm,← pow_two,hs]

theorem gaugeMiddle_orthogonal {q : ℕ} (D E : Fin q → Mat 2)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (a : Fin 2) (A : Mat q) (hA : Orthogonal A) : Orthogonal (gaugeMiddle D E a A) :=
  ((signs_diagonal_orthogonal _ (fun i => diagonalTwo_entry_sq (hD i).1 (hD i).2 a)).mul hA).mul
    (signs_diagonal_orthogonal _ (fun j => diagonalTwo_entry_sq (hE j).1 (hE j).2 a))

theorem diagonal_gauge_middle (D E : Mat 2) (hD : DiagonalTwo D)
    (hE : DiagonalTwo E) (a b : ℝ) :
    D * diagTwo a b * E = diagTwo (D 0 0*a*E 0 0) (D 1 1*b*E 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTwo,Matrix.mul_apply,Fin.sum_univ_two,hD.1,hD.2,hE.1,hE.2]

/-- Every full-fibre representative admits constant diagonal gauges normalizing
both middle matrices to Q0 and all relative outer matrices to I. -/
theorem normalize_scalar_base_fibre {q : ℕ} (hq : 0<q)
    (Q₀ A B : Mat q) (hentries : ∀ i j, Q₀ i j≠0)
    (U V : Fin q → Mat 2) (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hbase : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q₀ i j • (1 : Mat 2)) :
    ∃ (S : Mat 2) (D E : Fin q → Mat 2), Orthogonal S ∧
      (∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i)) ∧
      (∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j)) ∧
      (∀ i, U i * D i * S = 1) ∧ (∀ j, Sᵀ * E j * V j = 1) ∧
      gaugeMiddle D E 0 A = Q₀ ∧ gaugeMiddle D E 1 B = Q₀ := by
  let i₀ : Fin q := ⟨0,hq⟩
  let S := V i₀
  let D : Fin q → Mat 2 := fun i => S*U i
  let E : Fin q → Mat 2 := fun j => V j*Sᵀ
  have hS : Orthogonal S := hV i₀
  have hdiag (i j : Fin q) : DiagonalTwo (V j*U i) :=
    diagonalTwo_of_scalar_block (U i) (V j) (hU i) (hV j)
      (A i j) (B i j) (Q₀ i j) (hentries i j) (hbase i j)
  have hdD (i : Fin q) : DiagonalTwo (D i) := hdiag i i₀
  have hdE (j : Fin q) : DiagonalTwo (E j) := by
    have he : E j = (V j*U i₀)*(S*U i₀)ᵀ := by
      dsimp [E]
      rw [Matrix.transpose_mul]
      calc
        V j*Sᵀ = V j*(U i₀*(U i₀)ᵀ)*Sᵀ := by rw [(hU i₀).2,Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [he]
    exact diagonalTwo_mul (hdiag i₀ j) (diagonalTwo_transpose (hdiag i₀ i₀))
  have hoD : ∀ i, Orthogonal (D i) := fun i => hS.mul (hU i)
  have hoE : ∀ j, Orthogonal (E j) := fun j => (hV j).mul hS.transpose
  have hleft (i : Fin q) : U i*D i*S=1 := by
    rw [← diagonalTwo_symmetric (D i) (hdD i)]
    dsimp [D]
    rw [Matrix.transpose_mul]
    calc
      U i*((U i)ᵀ*Sᵀ)*S = (U i*(U i)ᵀ)*(Sᵀ*S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hU i).2,hS.1,Matrix.one_mul]
  have hright (j : Fin q) : Sᵀ*E j*V j=1 := by
    rw [← diagonalTwo_symmetric (E j) (hdE j)]
    dsimp [E]
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    calc
      Sᵀ*(S*(V j)ᵀ)*V j = (Sᵀ*S)*((V j)ᵀ*V j) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS.1,(hV j).1,Matrix.one_mul]
  have hmiddle (i j : Fin q) :
      diagTwo (gaugeMiddle D E 0 A i j) (gaugeMiddle D E 1 B i j) =
        Q₀ i j • (1 : Mat 2) := by
    rw [gaugeMiddle_apply,gaugeMiddle_apply,← diagonal_gauge_middle (D i) (E j) (hdD i) (hdE j)]
    change (S*U i)*diagTwo (A i j) (B i j)*(V j*Sᵀ) = _
    calc
      _ = S*(U i*diagTwo (A i j) (B i j)*V j)*Sᵀ := by simp only [Matrix.mul_assoc]
      _ = S*(Q₀ i j • (1 : Mat 2))*Sᵀ := by rw [hbase]
      _ = _ := by simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hS.2]
  refine ⟨S,D,E,hS,fun i => ⟨hdD i,hoD i⟩,fun j => ⟨hdE j,hoE j⟩,
    hleft,hright,?_,?_⟩
  · ext i j
    have h := congrFun (congrFun (hmiddle i j) 0) 0
    simpa [diagTwo,Matrix.one_apply] using h
  · ext i j
    have h := congrFun (congrFun (hmiddle i j) 1) 1
    simpa [diagTwo,Matrix.one_apply] using h

end GS.NonmanifoldCompletion
