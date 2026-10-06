module

public import GS.GlobalGeometry.BalancedLift
public import GS.CayleyCharts.Smooth
public import GS.Continuation.ExponentialBasics

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A globally defined, factorization-independent Cayley update with overlap

This file works in the original matrix type and the original InA2Orth set.
The update is defined from X and Z themselves, not a chosen pair of factors.
Its velocity is the already checked exact pointProjection. For tangent Z this
is Z. All denominators are invertible for ALL real step lengths, not only locally.
The map has a jointly smooth ambient extension. No manifold structure with
positive-dimensional stabilizer is silently assumed.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.CayleyCharts
open scoped Topology
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- This normalization has derivative +id at zero. -/
def unitCayley (A : Mat n) : Mat n := cayley ((-1/2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : Mat n) = 1 := by
  simp [unitCayley]

theorem unitCayley_supported (b : Fin n → ℕ) (A : Mat n)
    (hs : Supported b A) (hk : IsSkew A) : Supported b (unitCayley A) := by
  apply cayley_supported b _ (hs.smul (-1/2))
  exact admissible_of_isSkew _ (isSkew_smul _ hk)

theorem unitCayley_orthogonal (A : Mat n) (hk : IsSkew A) :
    Orthogonal (unitCayley A) :=
  cayley_orthogonal _ (isSkew_smul _ hk)
    (admissible_of_isSkew _ (isSkew_smul _ hk))

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Mat n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, IsSkew (A x)) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  change ContDiffAt ℝ ⊤ (fun y => cayley ((-1 / 2 : ℝ) • A y)) x
  apply smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
  exact admissible_of_isSkew _ (isSkew_smul _ (hk x))

/-- Differentiate c(tA)(I+tA)=I-tA. No derivative of inverse is postulated. -/
theorem cayley_line_derivative (A : Mat n) (hk : IsSkew A) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2 : ℝ) • A) 0 := by
  let f : ℝ → Mat n := fun t => cayley (t • A)
  have hsm : ContDiffAt ℝ ⊤ f 0 := by
    apply smooth_cayley_comp_at ((contDiffAt_id).smul contDiffAt_const)
    simpa using (admissible_zero : admissible (0 : Mat n))
  let V := deriv f 0
  have hd : HasDerivAt f V 0 := (hsm.differentiableAt (by simp)).hasDerivAt
  have hp : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • A) A 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have hm : HasDerivAt (fun t : ℝ => (1 : Mat n) - t • A) (-A) 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have he : (fun t : ℝ => f t * (1 + t • A)) =
      (fun t : ℝ => (1 : Mat n) - t • A) := by
    funext t
    exact cayley_mul _ (admissible_of_isSkew _ (isSkew_smul t hk))
  have hz := hasDerivAt_matrix_mul hd hp
  rw [he] at hz
  have hv : V + A = -A := by
    simpa [f] using hz.unique hm
  have hv' : V = (-2 : ℝ) • A := by
    ext i j
    have hh := congrFun (congrFun hv i) j
    change V i j = (-2 : ℝ) * A i j
    change V i j + A i j = -A i j at hh
    linarith
  simpa only [f, hv'] using hd

theorem unitCayley_line_derivative (A : Mat n) (hk : IsSkew A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := cayley_line_derivative ((-1/2 : ℝ) • A) (isSkew_smul _ hk)
  have hf : (fun t : ℝ => unitCayley (t • A)) =
      (fun t : ℝ => cayley (t • ((-1/2 : ℝ) • A))) := by
    funext t
    unfold unitCayley
    rw [smul_comm]
  rw [hf]
  simpa only [smul_smul, show (-2 : ℝ) * (-1/2) = 1 by norm_num, one_smul] using hd

/-- Globally defined matrix update; Z need not already be tangent. -/
def pointCayleyStep (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) (t : ℝ) : Mat n :=
  unitCayley (t • balancedLeft b₁ b₂ X Z) * X *
    unitCayley (t • balancedRight b₁ b₂ X Z)

@[simp] theorem pointCayleyStep_zero_time (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    pointCayleyStep b₁ b₂ X Z 0 = X := by simp [pointCayleyStep]

@[simp] theorem pointCayleyStep_zero_vector (b₁ b₂ : Fin n → ℕ) (X : Mat n) (t : ℝ) :
    pointCayleyStep b₁ b₂ X 0 t = X := by simp [pointCayleyStep]

/-- All real times and all ambient Z are allowed, also when supports overlap. -/
theorem pointCayleyStep_inA2Orth (b₁ b₂ : ℕ) (P X Z : Mat n)
    (hX : InA2Orth b₁ b₂ P X) (t : ℝ) :
    InA2Orth b₁ b₂ P
      (pointCayleyStep (fun i => i.val / b₁) (fun i => i.val / b₂) X Z t) := by
  rcases hX with ⟨R,L,hsR,hsL,hR,hL,hX⟩
  let a := balancedLeft (fun i => i.val / b₁) (fun i => i.val / b₂) X Z
  let b := balancedRight (fun i => i.val / b₁) (fun i => i.val / b₂) X Z
  let U := unitCayley (t • a)
  let V := unitCayley (t • b)
  have hsU : BlockDiagonal b₂ U :=
    unitCayley_supported _ _ ((balancedLeft_supported _ _ X Z).smul t)
      (isSkew_smul t (balancedLeft_skew _ _ X Z))
  have hsV : BlockDiagonal b₁ V :=
    unitCayley_supported _ _ ((balancedRight_supported _ _ X Z).smul t)
      (isSkew_smul t (balancedRight_skew _ _ X Z))
  have hoU : Orthogonal U := unitCayley_orthogonal _ (isSkew_smul t (balancedLeft_skew _ _ X Z))
  have hoV : Orthogonal V := unitCayley_orthogonal _ (isSkew_smul t (balancedRight_skew _ _ X Z))
  refine ⟨R*V,U*L,hsR.mul hsV,hsU.mul hsL,hR.mul hoV,hoU.mul hL,?_⟩
  change U*X*V = product2 (U*L) P (R*V)
  rw [hX]
  simp only [product2, Matrix.mul_assoc]

/-- The point-only update removes all ambiguity from changing factor representatives. -/
theorem pointCayleyStep_of_product_eq (b₁ b₂ : Fin n → ℕ)
    (L R L' R' P Z : Mat n) (t : ℝ)
    (h : product2 L P R = product2 L' P R') :
    pointCayleyStep b₁ b₂ (product2 L P R) Z t =
      pointCayleyStep b₁ b₂ (product2 L' P R') Z t := by rw [h]

/-- Smooth on the WHOLE ambient (X,Z,t) space, because the balanced
skew generators make every denominator invertible, even for nonorthogonal X. -/
theorem pointCayleyStep_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun p : (Mat n × Mat n) × ℝ =>
      pointCayleyStep b₁ b₂ p.1.1 p.1.2 p.2) := by
  have hl : ContDiff ℝ ⊤ (fun p : (Mat n × Mat n) × ℝ =>
      p.2 • balancedLeft b₁ b₂ p.1.1 p.1.2) :=
    contDiff_snd.smul ((balancedLeft_smooth b₁ b₂).comp contDiff_fst)
  have hr : ContDiff ℝ ⊤ (fun p : (Mat n × Mat n) × ℝ =>
      p.2 • balancedRight b₁ b₂ p.1.1 p.1.2) :=
    contDiff_snd.smul ((balancedRight_smooth b₁ b₂).comp contDiff_fst)
  exact contDiff_matrix_mul
    (contDiff_matrix_mul (unitCayley_smooth_comp _ hl (fun p =>
      isSkew_smul _ (balancedLeft_skew _ _ _ _))) contDiff_fst.fst)
    (unitCayley_smooth_comp _ hr (fun p => isSkew_smul _ (balancedRight_skew _ _ _ _)))

/-- Actual initial derivative equals the existing exact Frobenius projection. -/
theorem pointCayleyStep_derivative (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : Mat n)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R) :
    let X := product2 L (permMatrix σ) R
    HasDerivAt (pointCayleyStep b₁ b₂ X Z) (pointProjection b₁ b₂ X Z) 0 := by
  dsimp only
  let X := product2 L (permMatrix σ) R
  have hl := unitCayley_line_derivative (balancedLeft b₁ b₂ X Z) (balancedLeft_skew _ _ _ _)
  have hr := unitCayley_line_derivative (balancedRight b₁ b₂ X Z) (balancedRight_skew _ _ _ _)
  have hd := hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hl (hasDerivAt_const 0 X)) hr
  have hder : HasDerivAt (pointCayleyStep b₁ b₂ X Z)
      (balancedLeft b₁ b₂ X Z * X + X * balancedRight b₁ b₂ X Z) 0 := by
    unfold pointCayleyStep
    simpa only [zero_smul, unitCayley_zero, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_zero, add_zero] using hd
  simpa only [X, balanced_reconstruct b₁ b₂ σ L R Z hsL hsR hL hR] using hder

/-- Retraction first-order property on every actual generator-image direction,
without assuming a manifold theorem for the overlap case. -/
theorem pointCayleyStep_tangent_derivative (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : Mat n)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hZ : TwoFactorDirection b₁ b₂ L (permMatrix σ) R Z) :
    HasDerivAt (pointCayleyStep b₁ b₂ (product2 L (permMatrix σ) R) Z) Z 0 := by
  have hd := pointCayleyStep_derivative b₁ b₂ σ L R Z hsL hsR hL hR
  dsimp only at hd
  rwa [(pointProjection_fixed_iff b₁ b₂ σ L R Z hsL hsR hL hR).mpr hZ] at hd

end GS.GlobalGeometry
