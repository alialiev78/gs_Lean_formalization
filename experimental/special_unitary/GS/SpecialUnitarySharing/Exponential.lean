module

public import GS.SpecialUnitarySharing.Algebra
public import GS.SpecialUnitarySharing.ComplexExponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Exact special-unitary exponential factors

Every physical block has determinant one. The proof restricts the actual
matrix power series to each block and invokes the proved skew-Hermitian
spectral determinant identity. No global determinant condition is substituted
for blockwise membership, and there is no Cayley determinant assumption.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Filter
open scoped BigOperators Topology
namespace GS.SpecialUnitarySharing
variable {n : ℕ}

private theorem supported_pow {block : Fin n → ℕ} {A : CMat n}
    (hA : CSupported block A) (k : ℕ) : CSupported block (A ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (CSupported.one (block := block))
  | succ k ih => simpa only [pow_succ] using ih.mul hA

private theorem isClosed_support (block : Fin n → ℕ) :
    IsClosed {A : CMat n | CSupported block A} := by
  simp only [CSupported, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (by fun_prop) continuous_const

/-- Restriction of all powers is justified by support closure. -/
theorem blockMatrix_pow (s : Pattern n) (i : Fin n) (A : CMat n)
    (hA : CSupported s.block A) (k : ℕ) :
    blockMatrix s i (A ^ k) = (blockMatrix s i A) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, blockMatrix_mul s i (A ^ k) A (supported_pow hA k), ih, pow_succ]

/-- Restriction of the convergent series, in the original matrix topology. -/
theorem blockMatrix_cMatrixExp (s : Pattern n) (i : Fin n) (A : CMat n)
    (hA : CSupported s.block A) :
    blockMatrix s i (cMatrixExp A) = cMatrixExp (blockMatrix s i A) := by
  let F (u : Finset ℕ) : CMat n := ∑ k ∈ u, ((k.factorial : ℝ)⁻¹) • A ^ k
  have hF : Tendsto F atTop (𝓝 (cMatrixExp A)) := cMatrixExp_hasSum A
  have hm := (blockMap s i).continuous.continuousAt.tendsto.comp hF
  have he : (fun u => blockMap s i (F u)) =
      fun u : Finset ℕ => ∑ k ∈ u, ((k.factorial : ℝ)⁻¹) • (blockMatrix s i A) ^ k := by
    funext u
    dsimp [F]
    simp only [map_sum, map_smul, blockMap_apply, blockMatrix_pow s i A hA]
  rw [he] at hm
  exact tendsto_nhds_unique hm (cMatrixExp_hasSum (blockMatrix s i A))

/-- The complete shared matrix algebra is closed under the matrix exponential. -/
theorem cMatrixExp_mem_sharedMatrixSpace (s : Pattern n) (A : CMat n)
    (hA : A ∈ GS.UnitarySharing.sharedMatrixSpace s.size s.label) :
    cMatrixExp A ∈ GS.UnitarySharing.sharedMatrixSpace s.size s.label := by
  let S := GS.UnitarySharing.sharedMatrixSpace (n := n) s.size s.label
  have hclosed : IsClosed (S : Set (CMat n)) :=
    (isClosed_support s.block).inter (GS.UnitarySharing.isClosed_tiedEntries s.size s.label)
  have hp : ∀ k : ℕ, A ^ k ∈ S := by
    intro k
    induction k with
    | zero => simpa only [pow_zero] using GS.UnitarySharing.one_mem_sharedMatrixSpace s.size s.label
    | succ k ih =>
      simpa only [pow_succ] using
        GS.UnitarySharing.mul_mem_sharedMatrixSpace s.positive s.divides ih hA
  let F (u : Finset ℕ) : CMat n := ∑ k ∈ u, ((k.factorial : ℝ)⁻¹) • A ^ k
  have hlim : Tendsto F atTop (𝓝 (cMatrixExp A)) := cMatrixExp_hasSum A
  apply hclosed.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro u
  exact S.sum_mem (fun k _ => S.smul_mem _ (hp k))

/-- An actual factor in the SU subgroup, including every repeated physical block. -/
theorem cMatrixExp_special (s : Pattern n) (A : CMat n)
    (hA : A ∈ specialSkewSpace s) : SpecialUnitaryFactor s (cMatrixExp A) := by
  have hm := cMatrixExp_mem_sharedMatrixSpace s A ⟨hA.1.1, hA.1.2.2⟩
  refine ⟨⟨hm.1, cMatrixExp_unitary A hA.1.2.1, hm.2⟩, ?_⟩
  intro i
  rw [blockMatrix_cMatrixExp s i A hA.1.1]
  exact det_cMatrixExp_eq_one _ (blockMatrix_skew s i A hA.1.2.1) (hA.2 i)

theorem cExpLine_special (s : Pattern n) (A : CMat n)
    (hA : A ∈ specialSkewSpace s) (t : ℝ) : SpecialUnitaryFactor s (cExpLine A t) :=
  cMatrixExp_special s (t • A) ((specialSkewSpace s).smul_mem t hA)

def expFactor (s : Pattern n) (A : Generator s) (t : ℝ) : SpecialFactor s :=
  SpecialFactor.ofMatrix (cExpLine A.val t) (cExpLine_special s A.val A.property t)

@[simp] theorem expFactor_matrix (s : Pattern n) (A : Generator s) (t : ℝ) :
    SpecialFactor.matrix (expFactor s A t) = cExpLine A.val t := rfl

@[simp] theorem expFactor_zero (s : Pattern n) (A : Generator s) : expFactor s A 0 = 1 := by
  apply SpecialFactor.matrix_injective
  exact cExpLine_zero A.val

/-- Differentiability is for the actual matrix curve, not just formal series. -/
theorem expFactor_matrix_hasDerivAt (s : Pattern n) (A : Generator s) (t : ℝ) :
    HasDerivAt (fun u => SpecialFactor.matrix (expFactor s A u))
      (cExpLine A.val t * A.val) t := cExpLine_hasDerivAt A.val t

theorem cExpLine_contDiff (A : CMat n) : ContDiff ℝ ⊤ (cExpLine A) :=
  cMatrixExp_contDiff.comp (contDiff_id.smul contDiff_const)

theorem cExpLine_conjugate (Q A : CMat n) (hQ : Unitary Q) (t : ℝ) :
    cExpLine (Q * A * Qᴴ) t = Q * cExpLine A t * Qᴴ := by
  unfold cExpLine
  rw [show t • (Q * A * Qᴴ) = Q * (t • A) * Qᴴ by simp only [Matrix.mul_smul, Matrix.smul_mul]]
  exact cMatrixExp_conjugate Q (t • A) hQ

end GS.SpecialUnitarySharing
