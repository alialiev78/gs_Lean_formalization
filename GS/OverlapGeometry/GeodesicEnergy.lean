module

public import GS.OverlapGeometry.GeodesicDynamics
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Energy conservation for the overlap generator equation

The nontrivial commutator correction changes the supported generators but
preserves the Frobenius speed. The conclusions concern actual derivatives
and give equality of energy at any two times for a global solution.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
namespace GS.OverlapGeometry
variable {n : ℕ}

theorem generatorBracket_pairing_sum_zero (C K : Mat n)
    (hC : IsSkew C) (hK : IsSkew K) : frobInner (generatorBracket C K) (C+K) = 0 := by
  have hc : frobInner (C*K) C = frobInner (K*C) C := by
    rw [frobInner_mul_left, frobInner_mul_right]
    rw [hC]
    simp only [Matrix.neg_mul,Matrix.mul_neg]
  have hk : frobInner (C*K) K = frobInner (K*C) K := by
    rw [frobInner_mul_right, frobInner_mul_left]
    rw [hK]
    simp only [Matrix.neg_mul,Matrix.mul_neg]
  simp only [generatorBracket,frobInner_add_right,frobInner_sub_left,hc,hk,sub_self,zero_add]

theorem geodesicResidual_energy_identity
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (C K C' K' : Mat n)
    (hsC : Supported b₂ C) (hsK : Supported (b₁ ∘ σ.symm) K)
    (hC : IsSkew C) (hK : IsSkew K)
    (heq : geodesicResidual b₁ b₂ σ C K C' K' = 0) :
    frobInner (C'+K') (C+K) = 0 := by
  have hs : HasSupport (tangentUnion b₁ b₂ σ) (C+K) := by
    intro i j hij
    have hc : b₂ i ≠ b₂ j := fun h => hij (Or.inl h)
    have hk : b₁ (σ.symm i) ≠ b₁ (σ.symm j) := fun h => hij (Or.inr h)
    simp [hsC i j hc,hsK i j hk]
  have hnormal := maskedSkew_residual_orthogonal (generatorBracket C K) (C+K)
    hs (isSkew_add hC hK)
  rw [frobInner_sub_left,generatorBracket_pairing_sum_zero C K hC hK] at hnormal
  have hpair := congrArg (fun A => frobInner A (C+K)) heq
  change frobInner (C'+K'+maskedSkew (tangentUnion b₁ b₂ σ)
    (generatorBracket C K)) (C+K) = frobInner 0 (C+K) at hpair
  rw [frobInner_add_left,frobInner_zero_left] at hpair
  linarith

theorem geodesicGeneratorEnergy_hasDerivAt
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (C K : ℝ → Mat n)
    {C' K' : Mat n} {t : ℝ}
    (hdC : HasDerivAt C C' t) (hdK : HasDerivAt K K' t)
    (hsC : Supported b₂ (C t)) (hsK : Supported (b₁ ∘ σ.symm) (K t))
    (hC : IsSkew (C t)) (hK : IsSkew (K t))
    (heq : geodesicResidual b₁ b₂ σ (C t) (K t) C' K' = 0) :
    HasDerivAt (fun s => frobSq (C s+K s)) 0 t := by
  have h := hasDerivAt_frobInner (hdC.add hdK) (hdC.add hdK)
  have he := geodesicResidual_energy_identity b₁ b₂ σ (C t) (K t) C' K'
    hsC hsK hC hK heq
  simpa only [Pi.add_def, frobSq,he,frobInner_comm,zero_add] using h

/-- A differentiable solution of the explicit generator equation has constant
Frobenius energy, not merely zero projected acceleration by definition. -/
theorem geodesicGeneratorEnergy_constant
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (C K : ℝ → Mat n)
    (hdC : Differentiable ℝ C) (hdK : Differentiable ℝ K)
    (hsC : ∀ t, Supported b₂ (C t)) (hsK : ∀ t, Supported (b₁ ∘ σ.symm) (K t))
    (hC : ∀ t, IsSkew (C t)) (hK : ∀ t, IsSkew (K t))
    (heq : ∀ t, geodesicResidual b₁ b₂ σ (C t) (K t) (deriv C t) (deriv K t) = 0)
    (s t : ℝ) : frobSq (C s+K s) = frobSq (C t+K t) := by
  have h (r : ℝ) : HasDerivAt (fun a => frobSq (C a+K a)) 0 r :=
    geodesicGeneratorEnergy_hasDerivAt b₁ b₂ σ C K (hdC r).hasDerivAt (hdK r).hasDerivAt
      (hsC r) (hsK r) (hC r) (hK r) (heq r)
  exact is_const_of_deriv_eq_zero (fun r => (h r).differentiableAt) (fun r => (h r).deriv) s t

/-- Energy conservation for the actual derivative of the reconstructed product
curve, using the prescribed Frobenius metric rather than a coordinate norm. -/
theorem movingProduct_speed_constant
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (L R C K : ℝ → Mat n)
    (hdL : ∀ t, HasDerivAt L (L t*C t) t)
    (hdR : ∀ t, HasDerivAt R (K t*R t) t)
    (hL : ∀ t, Orthogonal (L t)) (hR : ∀ t, Orthogonal (R t))
    (hdC : Differentiable ℝ C) (hdK : Differentiable ℝ K)
    (hsC : ∀ t, Supported b₂ (C t)) (hsK : ∀ t, Supported (b₁ ∘ σ.symm) (K t))
    (hC : ∀ t, IsSkew (C t)) (hK : ∀ t, IsSkew (K t))
    (heq : ∀ t, geodesicResidual b₁ b₂ σ (C t) (K t) (deriv C t) (deriv K t) = 0)
    (s t : ℝ) :
    frobSq (deriv (fun r => L r*R r) s) = frobSq (deriv (fun r => L r*R r) t) := by
  rw [(product_curve_velocity L R (C s) (K s) s (hdL s) (hdR s)).deriv,
    (product_curve_velocity L R (C t) (K t) t (hdL t) (hdR t)).deriv]
  change frobInner (lift (L s) (R s) (C s+K s)) (lift (L s) (R s) (C s+K s)) =
    frobInner (lift (L t) (R t) (C t+K t)) (lift (L t) (R t) (C t+K t))
  rw [lift_frobInner _ _ _ _ (hL s) (hR s),lift_frobInner _ _ _ _ (hL t) (hR t)]
  exact geodesicGeneratorEnergy_constant b₁ b₂ σ C K hdC hdK hsC hsK hC hK heq s t

end GS.OverlapGeometry
