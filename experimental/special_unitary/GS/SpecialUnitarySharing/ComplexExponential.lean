module

public import GS.SpecialUnitarySharing.BlockAlgebra
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Complex matrix exponential and its determinant on skew-Hermitian matrices

No unproved `det_exp` lemma is imported: the skew-Hermitian case is reduced
by the Hermitian spectral theorem to a diagonal matrix. This is sufficient
for every special-unitary update in this directory. The original matrix norm
is retained; an auxiliary operator-norm type is used only to obtain smoothness.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Filter
open scoped Topology BigOperators
namespace GS.SpecialUnitarySharing
variable {n : ℕ}

def cMatrixExp (A : CMat n) : CMat n :=
  ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • A ^ k

theorem cMatrixExp_eq_exp (A : CMat n) : cMatrixExp A = NormedSpace.exp ℝ A := by
  rw [NormedSpace.exp_eq_tsum]
  rfl

theorem cMatrixExp_hasSum (A : CMat n) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A ^ k) (cMatrixExp A) := by
  letI : SeminormedRing (CMat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (CMat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (CMat n) := Matrix.linftyOpNormedAlgebra
  rw [cMatrixExp_eq_exp]
  exact NormedSpace.exp_series_hasSum_exp' A

@[simp] theorem cMatrixExp_zero : cMatrixExp (0 : CMat n) = 1 := by
  rw [cMatrixExp_eq_exp, NormedSpace.exp_zero]

theorem cMatrixExp_conjTranspose (A : CMat n) : cMatrixExp Aᴴ = (cMatrixExp A)ᴴ := by
  simpa only [cMatrixExp_eq_exp] using Matrix.exp_conjTranspose ℝ A

theorem cMatrixExp_add_of_commute (A B : CMat n) (h : Commute A B) :
    cMatrixExp (A + B) = cMatrixExp A * cMatrixExp B := by
  letI : SeminormedRing (CMat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (CMat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (CMat n) := Matrix.linftyOpNormedAlgebra
  simpa only [cMatrixExp_eq_exp] using NormedSpace.exp_add_of_commute (𝕂 := ℝ) h

theorem cMatrixExp_neg_mul (A : CMat n) : cMatrixExp (-A) * cMatrixExp A = 1 := by
  have hc : Commute (-A) A := by
    change (-A) * A = A * (-A)
    simp only [Matrix.neg_mul, Matrix.mul_neg]
  simpa only [neg_add_cancel, cMatrixExp_zero] using
    (cMatrixExp_add_of_commute (-A) A hc).symm

theorem cMatrixExp_unitary (A : CMat n) (hA : IsSkewHermitian A) : Unitary (cMatrixExp A) := by
  constructor
  · rw [← cMatrixExp_conjTranspose, hA]
    exact cMatrixExp_neg_mul A
  · rw [← cMatrixExp_conjTranspose, hA]
    simpa only [neg_neg] using cMatrixExp_neg_mul (-A)

private def cMulRight (H : CMat n) : CMat n →L[ℝ] CMat n :=
  ({ toFun := fun A => A * H
     map_add' := fun A B => Matrix.add_mul A B H
     map_smul' := by intro a A; simp only [Matrix.smul_mul]
   } : CMat n →ₗ[ℝ] CMat n).toContinuousLinearMap
private def cMulLeft (H : CMat n) : CMat n →L[ℝ] CMat n :=
  ({ toFun := fun A => H * A
     map_add' := Matrix.mul_add H
     map_smul' := by intro a A; simp only [Matrix.mul_smul]
   } : CMat n →ₗ[ℝ] CMat n).toContinuousLinearMap

/-- Intertwining passes through the convergent power series, with no invertibility assumption. -/
theorem cMatrixExp_intertwine (A B H : CMat n) (h : A * H = H * B) :
    cMatrixExp A * H = H * cMatrixExp B := by
  have hp : ∀ k : ℕ, A ^ k * H = H * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = A * (A ^ k * H) := by rw [pow_succ', Matrix.mul_assoc]
        _ = A * (H * B ^ k) := by rw [ih]
        _ = _ := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, ← pow_succ']
  let F (s : Finset ℕ) : CMat n := ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k
  let G (s : Finset ℕ) : CMat n := ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • B ^ k
  have hF : Tendsto F atTop (𝓝 (cMatrixExp A)) := cMatrixExp_hasSum A
  have hG : Tendsto G atTop (𝓝 (cMatrixExp B)) := cMatrixExp_hasSum B
  have hf := (cMulRight H).continuous.continuousAt.tendsto.comp hF
  have hg := (cMulLeft H).continuous.continuousAt.tendsto.comp hG
  have he : (fun s => cMulRight H (F s)) = fun s => cMulLeft H (G s) := by
    funext s
    change cMulRight H (∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k) =
      cMulLeft H (∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • B ^ k)
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun W : CMat n => ((k.factorial : ℝ)⁻¹) • W) (hp k)
  have hf' : Tendsto (fun s => cMulRight H (F s)) atTop
      (𝓝 (cMatrixExp A * H)) := hf
  rw [he] at hf'
  exact tendsto_nhds_unique hf' hg

theorem cMatrixExp_conjugate (Q A : CMat n) (hQ : Unitary Q) :
    cMatrixExp (Q * A * Qᴴ) = Q * cMatrixExp A * Qᴴ := by
  have hi : (Q * A * Qᴴ) * Q = Q * A := by
    rw [Matrix.mul_assoc (Q * A), hQ.1, Matrix.mul_one]
  have he := congrArg (fun W : CMat n => W * Qᴴ) (cMatrixExp_intertwine _ A Q hi)
  simpa only [Matrix.mul_assoc, hQ.2, Matrix.mul_one] using he

private theorem unitary_det_product (Q : CMat n) (hQ : Unitary Q) : Q.det * Qᴴ.det = 1 := by
  rw [← Matrix.det_mul, hQ.2, Matrix.det_one]

/-- Spectral reduction of a skew-Hermitian matrix, with explicitly real eigenvalues. -/
theorem skew_spectral_form (A : CMat n) (hA : IsSkewHermitian A) :
    ∃ (Q : CMat n) (d : Fin n → ℝ), Unitary Q ∧
      A = Q * Matrix.diagonal (fun i => -(Complex.I * (d i : ℂ))) * Qᴴ := by
  let H : CMat n := Complex.I • A
  have hH : H.IsHermitian := by
    change (Complex.I • A)ᴴ = Complex.I • A
    rw [Matrix.conjTranspose_smul, hA]
    simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  let Q : CMat n := hH.eigenvectorUnitary
  let d : Fin n → ℝ := hH.eigenvalues
  have hQ : Unitary Q := by
    apply IsUnitary.of_conjTranspose_mul
    simpa only [Q, Matrix.star_eq_conjTranspose] using
      unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hd : Qᴴ * H * Q = Matrix.diagonal (fun i => (d i : ℂ)) :=
    hH.star_mul_self_mul_eq_diagonal
  have ha : Qᴴ * A * Q = Matrix.diagonal (fun i => -(Complex.I * (d i : ℂ))) := by
    have he := congrArg (fun W : CMat n => (-Complex.I) • W) hd
    have hs : (-Complex.I) • (Complex.I • A) = A := by
      rw [smul_smul]
      norm_num
    have he' : (-Complex.I) • (Qᴴ * H * Q) = Qᴴ * A * Q := by
      dsimp [H]
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hs]
    rw [he'] at he
    rw [he]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  refine ⟨Q, d, hQ, ?_⟩
  rw [← ha]
  calc
    A = (Q * Qᴴ) * A * (Q * Qᴴ) := by rw [hQ.2]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Determinant/exponential identity in the required skew-Hermitian case.
This lemma is proved here rather than assumed as a library theorem. -/
theorem det_cMatrixExp_of_skew (A : CMat n) (hA : IsSkewHermitian A) :
    (cMatrixExp A).det = NormedSpace.exp ℝ (Matrix.trace A) := by
  obtain ⟨Q, d, hQ, he⟩ := skew_spectral_form A hA
  let z : Fin n → ℂ := fun i => -(Complex.I * (d i : ℂ))
  have ht : Matrix.trace A = ∑ i, z i := by
    rw [he, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ.1, Matrix.one_mul]
    simp only [Matrix.trace_diagonal, z]
  rw [he, cMatrixExp_conjugate _ _ hQ, Matrix.det_mul, Matrix.det_mul]
  have hediag : cMatrixExp (Matrix.diagonal z) =
      Matrix.diagonal (fun i => NormedSpace.exp ℝ (z i)) := by
    simpa only [cMatrixExp_eq_exp, Pi.exp_def] using Matrix.exp_diagonal ℝ z
  change Q.det * (cMatrixExp (Matrix.diagonal z)).det * Qᴴ.det = _
  rw [hediag, Matrix.det_diagonal]
  have hsum_all : ∀ s : Finset (Fin n),
      NormedSpace.exp ℝ (∑ i ∈ s, z i) = ∏ i ∈ s, NormedSpace.exp ℝ (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        NormedSpace.exp_add_of_commute (𝕂 := ℝ)
          (show Commute (z a) (∑ i ∈ s, z i) from mul_comm _ _), ih]
  have hsum : NormedSpace.exp ℝ (∑ i, z i) = ∏ i, NormedSpace.exp ℝ (z i) :=
    hsum_all Finset.univ
  have htrace : Matrix.trace
      (Q * Matrix.diagonal (fun i => -(Complex.I * (d i : ℂ))) * Qᴴ) = ∑ i, z i := by
    rw [← he]
    exact ht
  rw [htrace, hsum]
  calc
    Q.det * (∏ i, NormedSpace.exp ℝ (z i)) * Qᴴ.det =
        (Q.det * Qᴴ.det) * ∏ i, NormedSpace.exp ℝ (z i) := by ring
    _ = _ := by rw [unitary_det_product Q hQ, one_mul]

theorem det_cMatrixExp_eq_one (A : CMat n) (hA : IsSkewHermitian A)
    (htr : Matrix.trace A = 0) : (cMatrixExp A).det = 1 := by
  rw [det_cMatrixExp_of_skew A hA, htr, NormedSpace.exp_zero]

/-- A concrete exponential line with the original matrix topology. -/
def cExpLine (A : CMat n) (t : ℝ) : CMat n := cMatrixExp (t • A)
@[simp] theorem cExpLine_zero (A : CMat n) : cExpLine A 0 = 1 := by
  simp only [cExpLine, zero_smul, cMatrixExp_zero]

theorem cExpLine_hasDerivAt (A : CMat n) (t : ℝ) :
    HasDerivAt (cExpLine A) (cExpLine A t * A) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  letI : SeminormedRing (CMat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (CMat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (CMat n) := Matrix.linftyOpNormedAlgebra
  let ev : CMat n →L[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
  have hv := ev.hasFDerivAt.comp_hasDerivAt t he
  simpa only [cExpLine, cMatrixExp_eq_exp, ev, Function.comp_def] using hv

/-- Operator-norm matrix type, used only for transferring a genuine smooth map. -/
private def OpCMat (n : ℕ) := CMat n
private instance (n : ℕ) : Ring (OpCMat n) := inferInstanceAs (Ring (CMat n))
private instance (n : ℕ) : Algebra ℝ (OpCMat n) := inferInstanceAs (Algebra ℝ (CMat n))
private instance (n : ℕ) : NormedRing (OpCMat n) := Matrix.linftyOpNormedRing
private instance (n : ℕ) : NormedAddCommGroup (OpCMat n) := Matrix.linftyOpNormedAddCommGroup
private instance (n : ℕ) : NormedSpace ℝ (OpCMat n) := Matrix.linftyOpNormedSpace
private instance (n : ℕ) : NormedAlgebra ℝ (OpCMat n) := Matrix.linftyOpNormedAlgebra
private instance (n : ℕ) : FiniteDimensional ℝ (OpCMat n) :=
  inferInstanceAs (FiniteDimensional ℝ (CMat n))
private instance (n : ℕ) : CompleteSpace (OpCMat n) := FiniteDimensional.complete ℝ (OpCMat n)

/-- Analyticity transferred through continuous linear identities; no norms are identified. -/
theorem cMatrixExp_contDiff : ContDiff ℝ ⊤ (@cMatrixExp n) := by
  let toOp : CMat n →L[ℝ] OpCMat n :=
    ({ toFun := fun A => A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      CMat n →ₗ[ℝ] OpCMat n).toContinuousLinearMap
  let fromOp : OpCMat n →L[ℝ] CMat n :=
    ({ toFun := fun A => A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      OpCMat n →ₗ[ℝ] CMat n).toContinuousLinearMap
  have he : ContDiff ℝ ⊤ (NormedSpace.exp ℝ : OpCMat n → OpCMat n) :=
    contDiff_iff_contDiffAt.mpr (fun A => (NormedSpace.exp_analytic A).contDiffAt)
  simpa only [toOp, fromOp, Function.comp_def, cMatrixExp_eq_exp] using
    fromOp.contDiff.comp (he.comp toOp.contDiff)

end GS.SpecialUnitarySharing
