module

public import GS.Unitary.CholeskySupport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Unconditional complex structured QR/RQ: the unitary support conditions
are proved from ordinary complex QR and triangular Gram support recovery. -/
noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem structuredQR (block : Fin n → ℕ) (B : CMat n) (σ : Equiv.Perm (Fin n))
    (hB : CSupported block B) (hdetB : IsUnit B.det) :
    ∃ U R : CMat n, CSupported block U ∧ Unitary U ∧ CUpper R ∧
      B*cPermMatrix σ = U*cPermMatrix σ*R := by
  obtain ⟨V,R,hV,ht,he⟩ := exists_ordinary_qr (B*cPermMatrix σ)
  obtain ⟨hs,ho,hf⟩ := structured_of_ordinary_qr block B V R σ hB hdetB hV ht he
  exact ⟨V*(cPermMatrix σ)ᴴ,R,hs,ho,ht,hf⟩

def cReverseIndex {n : ℕ} (i : Fin n) : Fin n := ⟨n-1-i.val, by omega⟩
theorem cReverseIndex_involutive (i : Fin n) : cReverseIndex (cReverseIndex i)=i := by
  ext; simp only [cReverseIndex]; omega
def cReversePerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := cReverseIndex
  invFun := cReverseIndex
  left_inv := cReverseIndex_involutive
  right_inv := cReverseIndex_involutive

theorem upper_reverse_conjTranspose {T : CMat n} (ht : CUpper T) :
    CUpper (cPermMatrix (cReversePerm n)*Tᴴ*(cPermMatrix (cReversePerm n))ᴴ) := by
  intro i j hij
  change j.val < i.val at hij
  rw [cPerm_conjugate_apply]
  change star (T (cReverseIndex j) (cReverseIndex i))=0
  rw [ht (by change n-1-i.val < n-1-j.val; omega), star_zero]

theorem structuredRQ (block : Fin n → ℕ) (B : CMat n) (σ : Equiv.Perm (Fin n))
    (hB : CSupported block B) (hdetB : IsUnit B.det) :
    ∃ U R : CMat n, CSupported block U ∧ Unitary U ∧ CUpper R ∧
      cPermMatrix σ*B = R*cPermMatrix σ*U := by
  let ρ := cReversePerm n
  let P := cPermMatrix σ
  let J := cPermMatrix ρ
  let τ := ρ.trans σ.symm
  have hτ : cPermMatrix τ = Pᴴ*J := by
    simpa only [τ,P,J,cPerm_conjTranspose] using cPerm_trans_matrix ρ σ.symm
  have hbt : CSupported block Bᴴ := hB.conjTranspose
  have hdt : IsUnit Bᴴ.det := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [Matrix.det_conjTranspose, star_ne_zero] using isUnit_iff_ne_zero.mp hdetB
  obtain ⟨V,T,hV,hoV,ht,he⟩ := structuredQR block Bᴴ τ hbt hdt
  let U := Vᴴ
  let R := J*Tᴴ*Jᴴ
  have hJ := cPerm_unitary ρ
  have hJJ : J*Jᴴ=1 := hJ.2
  have hre : P*B=R*P*U := by
    have hh := congrArg (fun X : CMat n => J*Xᴴ) he
    rw [hτ] at hh
    simpa only [R,U,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc,hJJ,Matrix.one_mul] using hh
  exact ⟨U,R,hV.conjTranspose,hoV.conjTranspose,upper_reverse_conjTranspose ht,hre⟩
end GS.UnitaryGeometry
