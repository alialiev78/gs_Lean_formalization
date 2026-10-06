module

public import GS.Extensions.MatrixCalculus
public import GS.Extensions.TwoFactorProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Extrinsic geodesic certificates without a covering-space theorem

The conclusions below are actual second
velocity identities and Frobenius normality, not a redefinition of intrinsic
geodesics. The bridge from the derivative image to the tangent bundle of a
smooth embedded orbit remains a separate obligation.

The two coordinate block relations must intersect only on the diagonal.
No such claim is made for the singular general three-factor family.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 def OffDiagonalDisjoint (a b : Fin n → ℕ) : Prop :=
  ∀ i j, a i = a j → b i = b j → i = j

 theorem OffDiagonalDisjoint.symm {a b : Fin n → ℕ}
    (h : OffDiagonalDisjoint a b) : OffDiagonalDisjoint b a := by
  intro i j hb ha
  exact h i j ha hb

 theorem frobInner_disjoint_supported_skew {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (A K : Mat n)
    (hA : Supported a A) (hK : Supported b K) (hk : IsSkew K) :
    frobInner A K = 0 := by
  apply frobInner_eq_zero_of_disjoint
  intro i j
  by_cases ha : a i = a j
  · by_cases hb : b i = b j
    · have hij := hab i j ha hb
      subst j
      exact Or.inr (isSkew_diagonal_zero hk i)
    · exact Or.inr (hK i j hb)
  · exact Or.inl (hA i j ha)

 theorem skew_square_symmetric (C : Mat n) (hC : IsSkew C) :
    (C*C)ᵀ = C*C := by
  change Cᵀ = -C at hC
  simp only [Matrix.transpose_mul, hC, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

 theorem symmetric_skew_inner_zero (S K : Mat n)
    (hS : Sᵀ = S) (hK : IsSkew K) : frobInner S K = 0 := by
  have ht := frobInner_transpose S K
  have he : frobInner S (-K) = -frobInner S K := by
    rw [frobInner_comm S (-K), frobInner_neg_left, frobInner_comm K S]
  rw [hS, hK, he] at ht
  linarith

/-- The mixed product has zero pairing with BOTH generator spaces. -/
 theorem mixed_product_normal {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (C K D E : Mat n)
    (hCa : Supported a C) (hKb : Supported b K)
    (hDa : Supported a D) (hEb : Supported b E)
    (hC : IsSkew C) (hK : IsSkew K) :
    frobInner (C*K) (D+E) = 0 := by
  rw [frobInner_add_right]
  have hd : frobInner (C*K) D = 0 := by
    rw [frobInner_mul_left, frobInner_comm]
    exact frobInner_disjoint_supported_skew hab (Cᵀ*D) K
      (hCa.transpose.mul hDa) hKb hK
  have he : frobInner (C*K) E = 0 := by
    rw [frobInner_mul_right, frobInner_comm]
    exact frobInner_disjoint_supported_skew hab.symm (E*Kᵀ) C
      (hEb.mul hKb.transpose) hCa hC
  rw [hd, he, add_zero]

 def accelerationCore (C K : Mat n) : Mat n := C*C + (2:ℝ) • (C*K) + K*K

 theorem accelerationCore_normal {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (C K D E : Mat n)
    (hCa : Supported a C) (hKb : Supported b K)
    (hDa : Supported a D) (hEb : Supported b E)
    (hC : IsSkew C) (hK : IsSkew K) (hD : IsSkew D) (hE : IsSkew E) :
    frobInner (accelerationCore C K) (D+E) = 0 := by
  have hDE : IsSkew (D+E) := isSkew_add hD hE
  unfold accelerationCore
  rw [frobInner_add_left, frobInner_add_left, frobInner_smul_left]
  rw [symmetric_skew_inner_zero _ _ (skew_square_symmetric C hC) hDE,
    symmetric_skew_inner_zero _ _ (skew_square_symmetric K hK) hDE,
    mixed_product_normal hab C K D E hCa hKb hDa hEb hC hK]
  ring

 theorem lifted_acceleration_normal {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (L R C K D E : Mat n)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hCa : Supported a C) (hKb : Supported b K)
    (hDa : Supported a D) (hEb : Supported b E)
    (hC : IsSkew C) (hK : IsSkew K) (hD : IsSkew D) (hE : IsSkew E) :
    frobInner (lift L R (accelerationCore C K)) (lift L R (D+E)) = 0 := by
  rw [lift_frobInner L R _ _ hL hR]
  exact accelerationCore_normal hab C K D E hCa hKb hDa hEb hC hK hD hE

/-- The product curve satisfies the expected velocity formula whenever the
factors satisfy the usual constant-generator ODEs. -/
 theorem product_curve_velocity (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : HasDerivAt L (L t*C) t) (hR : HasDerivAt R (K*R t) t) :
    HasDerivAt (fun s => L s*R s) (lift (L t) (R t) (C+K)) t := by
  have h := hasDerivAt_matrix_mul hL hR
  simpa only [lift, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using h

/-- Differentiating that velocity gives a genuine HasDerivAt certificate for
acceleration. This lemma does not assume or assert a manifold structure. -/
 theorem product_curve_acceleration (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : HasDerivAt L (L t*C) t) (hR : HasDerivAt R (K*R t) t) :
    HasDerivAt (fun s => lift (L s) (R s) (C+K))
      (lift (L t) (R t) (accelerationCore C K)) t := by
  have hleft := hasDerivAt_matrix_mul hL (hasDerivAt_const t (C+K))
  have h := hasDerivAt_matrix_mul hleft hR
  have he : lift (L t) (R t) (accelerationCore C K) =
      (L t * C * (C + K) + L t * 0) * R t + L t * (C + K) * (K * R t) := by
    simp only [lift, accelerationCore, Matrix.mul_zero, add_zero,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact h

/-- A complete pointwise normal-acceleration conclusion under explicit ODE and
orthogonality hypotheses. Matrix exponential solutions can be connected to
these hypotheses independently of the covering-map route. -/
 theorem product_curve_normal_acceleration {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : Orthogonal (L t)) (hR : Orthogonal (R t))
    (hdL : HasDerivAt L (L t*C) t) (hdR : HasDerivAt R (K*R t) t)
    (hCa : Supported a C) (hKb : Supported b K) (hC : IsSkew C) (hK : IsSkew K) :
    HasDerivAt (fun s => lift (L s) (R s) (C+K))
      (lift (L t) (R t) (accelerationCore C K)) t ∧
    ∀ D E : Mat n, Supported a D → Supported b E → IsSkew D → IsSkew E →
      frobInner (lift (L t) (R t) (accelerationCore C K))
        (lift (L t) (R t) (D+E)) = 0 := by
  refine ⟨product_curve_acceleration L R C K t hdL hdR, ?_⟩
  intro D E hDa hEb hD hE
  exact lifted_acceleration_normal hab (L t) (R t) C K D E
    hL hR hCa hKb hDa hEb hC hK hD hE

end GS.Extensions
