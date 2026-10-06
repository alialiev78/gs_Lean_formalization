module

public import GS.Extensions.CholeskySupport
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Ordinary QR existence and structured QR

Unlike a theorem conditional on StructuredQRGoal,
this file constructs an ordinary QR using mathlib's completed Gram--Schmidt
orthonormal basis, then proves the additional structure with CholeskySupport.

The inner-product-space step uses a genuine EuclideanSpace. It does NOT equip
the raw function type with a misleading pointwise/supremum inner product.
The basis is allowed to complete dependent input columns; ordinary QR exists
also for singular matrices. Invertibility is needed only for support recovery.
-/

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators
namespace GS.Extensions
variable {n : ℕ}

/-- Ordinary real square QR, with no positivity convention imposed on R.
All entries are specified by inner products against orthonormal bases. -/
 theorem exists_ordinary_qr (A : Mat n) :
    ∃ V R : Mat n, Orthogonal V ∧ Upper R ∧ A=V*R := by
  let e₀ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  let f : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun j => ∑ k, A k j • e₀ k
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let e := gramSchmidtOrthonormalBasis hdim f
  let V : Mat n := fun i j => ⟪e₀ i, e j⟫_ℝ
  let R : Mat n := fun i j => ⟪e i, f j⟫_ℝ
  have ho : Orthogonal V := by
    apply Orthogonal.of_transpose_mul
    ext i j
    calc
      (Vᵀ*V) i j = ∑ k, ⟪e i, e₀ k⟫_ℝ * ⟪e₀ k, e j⟫_ℝ := by
        change (∑ k, ⟪e₀ k, e i⟫_ℝ * ⟪e₀ k, e j⟫_ℝ) = _
        apply Finset.sum_congr rfl
        intro k hk
        rw [real_inner_comm (e₀ k) (e i)]
      _ = ⟪e i, e j⟫_ℝ := e₀.sum_inner_mul_inner _ _
      _ = (1 : Mat n) i j := by
        simpa only [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  have ht : Upper R := by
    intro i j hij
    exact gramSchmidtOrthonormalBasis_inv_triangular hdim f hij
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_ℝ = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have he : A=V*R := by
    ext i j
    calc
      A i j = ⟪e₀ i, f j⟫_ℝ := (hcoords i j).symm
      _ = ∑ k, ⟪e₀ i, e k⟫_ℝ * ⟪e k, f j⟫_ℝ :=
        (e.sum_inner_mul_inner _ _).symm
      _ = (V*R) i j := rfl
  exact ⟨V,R,ho,ht,he⟩

/-- No structured QR hypothesis: this theorem proves that specification. -/
 theorem structuredQR : GS.Specifications.StructuredQRGoal := by
  intro n s B σ hB hdetB
  obtain ⟨V,R,hV,ht,he⟩ := exists_ordinary_qr (B*permMatrix σ)
  obtain ⟨hs,ho,hf⟩ := structured_of_ordinary_qr s.size B V R σ hB hdetB hV ht he
  exact ⟨V*(permMatrix σ)ᵀ,R,hs,ho,ht,hf⟩

end GS.Extensions
