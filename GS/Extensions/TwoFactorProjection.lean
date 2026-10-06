module

public import GS.Extensions.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Connect the supported-skew projector to the two-factor differential image

No sharing is imposed in this module.
Both overlapping and nonoverlapping supports are treated exactly. The range is
the image of an actual Frechet derivative on specified generator directions;
this module does not yet identify it with an embedded manifold tangent space.
-/

noncomputable section
open Matrix
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 theorem splitLeft_supported (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (A : Mat n) : HasSupport p (splitLeft p q A) := by
  intro i j hij
  simp [splitLeft, hij]

 theorem splitRight_supported (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (A : Mat n) : HasSupport q (splitRight p q A) :=
  splitLeft_supported q p A

 theorem splitLeft_skew (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (hp : MaskSymmetric p) (hq : MaskSymmetric q)
    (A : Mat n) : IsSkew (splitLeft p q A) := by
  ext i j
  have he : skew A j i = -skew A i j :=
    congrFun (congrFun (isSkew_skew A) i) j
  have hpi : p j i ↔ p i j := hp j i
  have hqi : q j i ↔ q i j := hq j i
  by_cases h₁ : p i j <;> by_cases h₂ : q i j <;>
    simp [splitLeft, Matrix.transpose_apply, hpi, hqi, h₁, h₂, he] <;> ring

 theorem splitRight_skew (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (hp : MaskSymmetric p) (hq : MaskSymmetric q)
    (A : Mat n) : IsSkew (splitRight p q A) :=
  splitLeft_skew q p hq hp A

 def tangentUnion (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) : Prop :=
  block₂ i = block₂ j ∨ block₁ (σ.symm i) = block₁ (σ.symm j)

 theorem tangentUnion_symmetric (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : MaskSymmetric (tangentUnion block₁ block₂ σ) := by
  intro i j
  unfold tangentUnion
  constructor <;> intro h <;> rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm
  · exact Or.inl h.symm
  · exact Or.inr h.symm

 def TwoFactorDirection (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ X : Mat n) : Prop :=
  ∃ C Ω : Mat n, Supported block₂ C ∧ IsSkew C ∧
    Supported block₁ Ω ∧ IsSkew Ω ∧ X = tangentParam B₂ P B₁ C Ω

 theorem isSkew_add {C K : Mat n} (hC : IsSkew C) (hK : IsSkew K) :
    IsSkew (C+K) := by
  unfold IsSkew at *
  rw [Matrix.transpose_add, hC, hK]
  abel

 theorem pulled_conjugate_supported (block : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (K : Mat n)
    (hK : Supported (block ∘ σ.symm) K) :
    Supported block ((permMatrix σ)ᵀ*K*permMatrix σ) := by
  intro i j hij
  have he : ((permMatrix σ)ᵀ*K*permMatrix σ) i j = K (σ i) (σ j) := by
    simpa only [perm_transpose, Equiv.symm_symm] using
      perm_conjugate_apply σ.symm K i j
  rw [he]
  apply hK
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hij

 theorem twoFactorDirection_iff_admissible
    (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (B₂ B₁ X : Mat n) :
    TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁ X ↔
    Admissible (tangentUnion block₁ block₂ σ) B₂ (permMatrix σ*B₁) X := by
  classical
  let P := permMatrix σ
  let p := fun i j => block₂ i = block₂ j
  let q := fun i j => block₁ (σ.symm i) = block₁ (σ.symm j)
  have hp : MaskSymmetric p := fun i j => eq_comm
  have hq : MaskSymmetric q := fun i j => eq_comm
  constructor
  · rintro ⟨C,Ω,hsC,hkC,hsΩ,hkΩ,rfl⟩
    refine ⟨C+P*Ω*Pᵀ, ?_, isSkew_add hkC (conjugate_skew P Ω hkΩ), ?_⟩
    · intro i j hij
      have h₁ : block₂ i ≠ block₂ j := fun h => hij (Or.inl h)
      have h₂ : block₁ (σ.symm i) ≠ block₁ (σ.symm j) := fun h => hij (Or.inr h)
      change C i j + (P*Ω*Pᵀ) i j = 0
      rw [hsC i j h₁]
      simp only [P, perm_conjugate_apply, hsΩ _ _ h₂, add_zero]
    · exact tangentParam_factored B₂ P B₁ C Ω (perm_orthogonal σ)
  · rintro ⟨Y,hsY,hkY,hX⟩
    let C := splitLeft p q Y
    let K := splitRight p q Y
    let Ω := Pᵀ*K*P
    have hsC : Supported block₂ C := splitLeft_supported p q Y
    have hkC : IsSkew C := splitLeft_skew p q hp hq Y
    have hsK : Supported (block₁ ∘ σ.symm) K := splitRight_supported p q Y
    have hkK : IsSkew K := splitRight_skew p q hp hq Y
    have hsΩ : Supported block₁ Ω := pulled_conjugate_supported block₁ σ K hsK
    have hkΩ : IsSkew Ω := by
      simpa only [Ω, Matrix.transpose_transpose] using conjugate_skew Pᵀ K hkK
    have hsum : C+K=Y := by
      calc
        C+K = maskedSkew (fun i j => p i j ∨ q i j) Y := split_sum p q Y
        _ = Y := maskedSkew_fixed hsY hkY
    have hback : P*Ω*Pᵀ=K := by
      calc
        P*Ω*Pᵀ = (P*Pᵀ)*K*(P*Pᵀ) := by simp only [Ω, Matrix.mul_assoc]
        _ = K := by rw [(perm_orthogonal σ).2]; simp
    refine ⟨C,Ω,hsC,hkC,hsΩ,hkΩ,?_⟩
    rw [tangentParam_factored B₂ P B₁ C Ω (perm_orthogonal σ), hback, hsum]
    exact hX

 def twoFactorProjection (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z : Mat n) : Mat n := by
  classical
  exact transportedProjection (tangentUnion block₁ block₂ σ) B₂ (permMatrix σ*B₁) Z

 theorem twoFactorProjection_in_direction
    (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z : Mat n) :
    TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁
      (twoFactorProjection block₁ block₂ σ B₂ B₁ Z) := by
  classical
  apply (twoFactorDirection_iff_admissible block₁ block₂ σ B₂ B₁ _).mpr
  exact admissible_projection _ (tangentUnion_symmetric block₁ block₂ σ) _ _ _

 theorem twoFactorProjection_pythagorean
    (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z X : Mat n)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁)
    (hX : TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁ X) :
    frobSq (Z-X) = frobSq (Z-twoFactorProjection block₁ block₂ σ B₂ B₁ Z) +
      frobSq (twoFactorProjection block₁ block₂ σ B₂ B₁ Z-X) := by
  classical
  exact projection_pythagorean _ (tangentUnion_symmetric block₁ block₂ σ) _ _ _ _
    h₂ ((perm_orthogonal σ).mul h₁)
    ((twoFactorDirection_iff_admissible block₁ block₂ σ B₂ B₁ X).mp hX)

 theorem twoFactorProjection_smooth
    (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    ContDiff ℝ ⊤ (fun x : Mat n × Mat n × Mat n =>
      twoFactorProjection block₁ block₂ σ x.1 x.2.1 x.2.2) := by
  classical
  exact twoFactor_projection_factorwise_smooth _ (permMatrix σ)

/-- Relate the explicit generator space to the actual Frechet derivative. -/
 theorem twoFactorDirection_iff_derivative_image
    (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ X : Mat n) :
    TwoFactorDirection block₁ block₂ B₂ P B₁ X ↔
      ∃ C Ω : Mat n, Supported block₂ C ∧ IsSkew C ∧ Supported block₁ Ω ∧ IsSkew Ω ∧
        X = fderiv ℝ (fun p : Mat n × Mat n => product2 p.1 P p.2)
          (B₂,B₁) (B₂*C,Ω*B₁) := by
  simp only [fderiv_product2_generators, TwoFactorDirection]

end GS.Extensions
