module

public import GS.Extensions.OriginalCompact
public import GS.Extensions.MatrixCalculus
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Matrix exponential: structure, orthogonality and actual scalar derivatives

 The exponential is the existing
GS.matrixExp power series, not a new opaque solution of an ODE.

Derivative proofs first export scalar coordinate derivatives from the auxiliary
operator norm and then reconstruct the matrix derivative in its default product
norm. No Frobenius/default/operator norm identification is used.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem supported_pow {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) (k : ℕ) : Supported block (A ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (Supported.one (block := block))
  | succ k ih => simpa only [pow_succ] using ih.mul hA

theorem supported_sum {α : Type*} (s : Finset α) (F : α → Mat n)
    {block : Fin n → ℕ} (hF : ∀ a ∈ s, Supported block (F a)) :
    Supported block (∑ a ∈ s, F a) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty => intro _; simpa using (Supported.zero (block := block))
  | @insert a s ha ih =>
    intro hF
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih (fun b hb => hF b (Finset.mem_insert_of_mem hb)))

/-- Powers and finite sums have the same block support; its closedness passes
that property to the convergent matrix-exponential series. -/
theorem supported_matrixExp {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) : Supported block (matrixExp A) := by
  let F : Finset ℕ → Mat n := fun s => ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k
  have hlim : Tendsto F atTop (𝓝 (matrixExp A)) := matrixExp_hasSum A
  apply (isClosed_supported n block).mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro s
  exact supported_sum s _ (fun k _ => Supported.smul _ (supported_pow hA k))

theorem transpose_pow_eq (A : Mat n) (k : ℕ) : (A ^ k)ᵀ = (Aᵀ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Matrix.transpose_mul, ih, pow_succ']

/-- Transposition commutes with the actual power-series exponential. -/
theorem matrixExp_transpose (A : Mat n) : matrixExp (Aᵀ) = (matrixExp A)ᵀ := by
  simpa only [matrixExp_eq_exp] using Matrix.exp_transpose A

/-- Only commuting exponents are combined. This is valid for real matrix
algebras after temporarily installing the operator norm inside the proof. -/
theorem matrixExp_add_of_commute (A B : Mat n) (h : Commute A B) :
    matrixExp (A + B) = matrixExp A * matrixExp B := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Mat n) := Matrix.linftyOpNormedAlgebra
  simpa only [matrixExp_eq_exp] using
    (NormedSpace.exp_add_of_commute h)

theorem matrixExp_neg_mul (A : Mat n) : matrixExp (-A) * matrixExp A = 1 := by
  have hc : Commute (-A) A := by
    change (-A) * A = A * (-A)
    simp only [Matrix.neg_mul, Matrix.mul_neg]
  have he := matrixExp_add_of_commute (-A) A hc
  simpa only [neg_add_cancel, matrixExp_zero] using he.symm

theorem matrixExp_mul_neg (A : Mat n) : matrixExp A * matrixExp (-A) = 1 := by
  simpa only [neg_neg] using matrixExp_neg_mul (-A)

/-- Orthogonality of exp(skew) is a theorem, not an ODE hypothesis. -/
theorem matrixExp_orthogonal {A : Mat n} (hA : IsSkew A) :
    Orthogonal (matrixExp A) := by
  apply Orthogonal.of_transpose_mul
  rw [← matrixExp_transpose, hA]
  exact matrixExp_neg_mul A

theorem isSkew_smul (t : ℝ) {A : Mat n} (hA : IsSkew A) : IsSkew (t • A) := by
  change (t • A)ᵀ = -(t • A)
  rw [Matrix.transpose_smul, hA, smul_neg]

/-- A named, concrete exponential line. -/
def expLine (C : Mat n) (t : ℝ) : Mat n := matrixExp (t • C)

@[simp] theorem expLine_zero (C : Mat n) : expLine C 0 = 1 := by
  simp only [expLine, zero_smul, matrixExp_zero]

theorem expLine_supported {block : Fin n → ℕ} {C : Mat n}
    (hC : Supported block C) (t : ℝ) : Supported block (expLine C t) :=
  supported_matrixExp (Supported.smul t hC)

theorem expLine_orthogonal {C : Mat n} (hC : IsSkew C) (t : ℝ) :
    Orthogonal (expLine C t) := matrixExp_orthogonal (isSkew_smul t hC)

/-- Scalar coordinate derivative, independent of which matrix norm was used to
apply the Banach-algebra exponential theorem. -/
theorem hasDerivAt_expLine_entry (C : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => expLine C s i j) ((expLine C t * C) i j) t := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let ev : Mat n →L[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) C t
  have hv := ev.hasFDerivAt.comp_hasDerivAt t he
  simpa only [expLine, matrixExp_eq_exp, ev, Function.comp_def, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using hv

/-- Matrix derivative reconstructed in the default matrix product norm. -/
theorem hasDerivAt_expLine (C : Mat n) (t : ℝ) :
    HasDerivAt (expLine C) (expLine C t * C) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_expLine_entry C t i j

theorem hasDerivAt_expLine_entry_left (C : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => expLine C s i j) ((C * expLine C t) i j) t := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let ev : Mat n →L[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) C t
  have hv := ev.hasFDerivAt.comp_hasDerivAt t he
  simpa only [expLine, matrixExp_eq_exp, ev, Function.comp_def, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using hv

theorem hasDerivAt_expLine_left (C : Mat n) (t : ℝ) :
    HasDerivAt (expLine C) (C * expLine C t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_expLine_entry_left C t i j

/-- Exp(tC) commutes with its fixed generator C. -/
theorem expLine_commute (C : Mat n) (t : ℝ) : expLine C t * C = C * expLine C t :=
  (hasDerivAt_expLine C t).unique (hasDerivAt_expLine_left C t)

theorem continuous_expLine (C : Mat n) : Continuous (expLine C) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_expLine C t).continuousAt)

end GS.Continuation
