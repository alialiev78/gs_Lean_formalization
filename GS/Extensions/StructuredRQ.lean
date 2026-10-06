module

public import GS.Extensions.OrdinaryQR

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# RQ from QR and unconditional statements for m=3 and m=2

The conditional three-factor theorem supplies the final implication. The two structured existence
hypotheses are discharged by proofs in these extension modules.
-/

noncomputable section
open Matrix
namespace GS.Extensions

 def reverseIndex {n : ℕ} (i : Fin n) : Fin n := ⟨n-1-i.val, by omega⟩

 theorem reverseIndex_involutive {n : ℕ} (i : Fin n) : reverseIndex (reverseIndex i)=i := by
  ext
  simp only [reverseIndex]
  omega

 def reversePerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := reverseIndex
  invFun := reverseIndex
  left_inv := reverseIndex_involutive
  right_inv := reverseIndex_involutive

 theorem perm_trans_matrix {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permMatrix (σ.trans τ) = permMatrix τ * permMatrix σ := by
  ext i j
  rw [perm_mul_apply]
  change (if i=τ (σ j) then (1:ℝ) else 0) =
    (if τ.symm i=σ j then (1:ℝ) else 0)
  by_cases h : i=τ (σ j)
  · subst i
    simp
  · have hn : τ.symm i ≠ σ j := by
      intro hh
      apply h
      simpa using congrArg τ hh
    simp [h,hn]

 theorem upper_reverse_transpose {n : ℕ} {T : Mat n} (ht : Upper T) :
    Upper (permMatrix (reversePerm n)*Tᵀ*(permMatrix (reversePerm n))ᵀ) := by
  intro i j hij
  change j.val < i.val at hij
  rw [perm_conjugate_apply]
  change T (reverseIndex j) (reverseIndex i)=0
  apply ht
  change n-1-i.val < n-1-j.val
  omega

 theorem structuredRQ_of_QR (hqr : GS.Specifications.StructuredQRGoal) :
    GS.Specifications.StructuredRQGoal := by
  intro n s B σ hB hdetB
  let ρ := reversePerm n
  let P := permMatrix σ
  let J := permMatrix ρ
  let τ := ρ.trans σ.symm
  have hτ : permMatrix τ = Pᵀ*J := by
    simpa only [τ,P,J,perm_transpose] using perm_trans_matrix ρ σ.symm
  have hbt : BlockDiagonal s.size Bᵀ := hB.transpose
  have hdt : IsUnit Bᵀ.det := by simpa only [Matrix.det_transpose] using hdetB
  obtain ⟨V,T,hV,hoV,ht,he⟩ := hqr n s Bᵀ τ hbt hdt
  let U := Vᵀ
  let R := J*Tᵀ*Jᵀ
  have hJ := perm_orthogonal ρ
  have hJJ : J*Jᵀ=1 := hJ.2
  have hre : P*B=R*P*U := by
    have hh := congrArg (fun X : Mat n => J*Xᵀ) he
    rw [hτ] at hh
    simpa only [R,U,Matrix.transpose_mul,Matrix.transpose_transpose,
      ← Matrix.mul_assoc,hJJ,Matrix.one_mul] using hh
  exact ⟨U,R,hV.transpose,hoV.transpose,upper_reverse_transpose ht,hre⟩

 theorem structuredRQ : GS.Specifications.StructuredRQGoal :=
  structuredRQ_of_QR structuredQR

 theorem threeFactorOrthogonalization : GS.Specifications.ThreeFactorOrthogonalizationGoal :=
  GS.Specifications.threeFactorOrthogonalization_of_structured structuredQR structuredRQ

 theorem singleton_block_supported {n : ℕ} {A : Mat n}
    (hA : BlockDiagonal 1 A) (block : Fin n → ℕ) : Supported block A := by
  intro i j hij
  apply hA
  simp only [Nat.div_one]
  intro he
  exact hij (congrArg block (Fin.ext he))

/-- The m=2 equality follows from m=3 with a one-dimensional extra left layer.
The extra orthogonal diagonal factor is absorbed into the existing left blocks. -/
 theorem twoFactorOrthogonalization : GS.Specifications.TwoFactorOrthogonalizationGoal := by
  intro n s₁ s₂ σ A
  have hPI : permMatrix (Equiv.refl (Fin n)) = (1 : Mat n) := by
    ext i j
    by_cases h : i = j <;> simp [permMatrix, Matrix.one_apply, h]
  constructor
  · rintro ⟨⟨B₁,B₂,hb₁,hb₂,he⟩,hA⟩
    let s₃ : BlockSpec n := ⟨1,n,by decide,by simp⟩
    have hmem : InA3 s₁.size s₂.size s₃.size (permMatrix σ)
        (permMatrix (Equiv.refl (Fin n))) A := by
      refine ⟨B₁,B₂,1,hb₁,hb₂,Supported.one,?_⟩
      simpa only [product3,product2,hPI,Matrix.one_mul] using he
    obtain ⟨U₁,U₂,U₃,hu₁,hu₂,hu₃,ho₁,ho₂,ho₃,hprod⟩ :=
      (threeFactorOrthogonalization n s₁ s₂ s₃ σ (Equiv.refl _) A).mp ⟨hmem,hA⟩
    have hu₃' : BlockDiagonal s₂.size U₃ :=
      singleton_block_supported hu₃ (fun i => i.val/s₂.size)
    refine ⟨U₁,U₃*U₂,hu₁,hu₃'.mul hu₂,ho₁,ho₃.mul ho₂,?_⟩
    simpa only [product3,product2,hPI,Matrix.mul_one,Matrix.mul_assoc] using hprod
  · rintro ⟨B₁,B₂,hb₁,hb₂,ho₁,ho₂,he⟩
    refine ⟨⟨B₁,B₂,hb₁,hb₂,he⟩,?_⟩
    rw [he]
    exact (ho₂.mul (perm_orthogonal σ)).mul ho₁

end GS.Extensions
