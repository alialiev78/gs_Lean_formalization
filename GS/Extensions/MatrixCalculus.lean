module

public import GS.Extensions.ProjectionSmooth
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Analytic derivatives, rather than only polynomial Taylor identities

Matrix differentiation is reduced to finite
scalar sums, avoiding the need to silently change the matrix norm instance.
The final AD theorem starts with an actual HasFDerivAt hypothesis for the loss.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 theorem hasDerivAt_matrix_mul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hterm : ∀ k : Fin n,
      HasDerivAt (fun s => A s i k * B s k j)
        (A' i k * B t k j + A t i k * B' k j) t := by
    intro k
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_fn] using hs

 theorem hasDerivAt_matrix_transpose {A : ℝ → Mat n} {A' : Mat n} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s)ᵀ) A'ᵀ t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA j) i

 theorem hasDerivAt_product2 {B₂ B₁ : ℝ → Mat n} (P : Mat n)
    {η₂ η₁ : Mat n} {t : ℝ}
    (h₂ : HasDerivAt B₂ η₂ t) (h₁ : HasDerivAt B₁ η₁ t) :
    HasDerivAt (fun s => product2 (B₂ s) P (B₁ s))
      (η₂ * P * B₁ t + B₂ t * P * η₁) t := by
  have hleft := hasDerivAt_matrix_mul h₂ (hasDerivAt_const t P)
  have h := hasDerivAt_matrix_mul hleft h₁
  simpa only [product2, Matrix.mul_zero, add_zero] using h

 theorem hasDerivAt_affine_matrix (B η : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => B + s • η) η t := by
  have h := (hasDerivAt_id t).smul_const η
  simpa only [Pi.add_apply, Pi.add_def, id_eq, one_smul, zero_add] using (hasDerivAt_const t B).add h

/-- Actual directional evaluation of the Frechet derivative of Phi(B2,B1).
The domain includes all factor variations, not only admissible skew ones. -/
 theorem fderiv_product2_apply (B₂ P B₁ η₂ η₁ : Mat n) :
    fderiv ℝ (fun p : Mat n × Mat n => product2 p.1 P p.2)
      (B₂,B₁) (η₂,η₁) = η₂*P*B₁ + B₂*P*η₁ := by
  have hd : Differentiable ℝ (fun p : Mat n × Mat n => product2 p.1 P p.2) :=
    (product2_smooth P).differentiable (by simp)
  have hc := (hasDerivAt_affine_matrix B₂ η₂ 0).prodMk
    (hasDerivAt_affine_matrix B₁ η₁ 0)
  have hcomp := (hd (B₂,B₁)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    hc (by simp)
  have hactual := hasDerivAt_product2 P
    (hasDerivAt_affine_matrix B₂ η₂ 0) (hasDerivAt_affine_matrix B₁ η₁ 0)
  have hcomp' : HasDerivAt
      (fun s : ℝ => product2 (B₂+s•η₂) P (B₁+s•η₁))
      (fderiv ℝ (fun p : Mat n × Mat n => product2 p.1 P p.2)
        (B₂,B₁) (η₂,η₁)) 0 := by
    simpa only [Function.comp_def] using hcomp
  exact hcomp'.unique (by simpa using hactual)

 theorem fderiv_product2_generators (B₂ P B₁ C Ω : Mat n) :
    fderiv ℝ (fun p : Mat n × Mat n => product2 p.1 P p.2)
      (B₂,B₁) (B₂*C,Ω*B₁) = tangentParam B₂ P B₁ C Ω := by
  rw [fderiv_product2_apply]
  simp only [tangentParam, Matrix.mul_assoc]

/-- First-order retraction property for the product follows from actual
first-order retraction properties of the two factors. This does not prove
factorization-independence of a quotient retraction. -/
 theorem product_retraction_first_order
    (B₂ P B₁ η₂ η₁ : Mat n) (r₂ r₁ : ℝ → Mat n)
    (h₂₀ : r₂ 0 = B₂) (h₁₀ : r₁ 0 = B₁)
    (h₂ : HasDerivAt r₂ η₂ 0) (h₁ : HasDerivAt r₁ η₁ 0) :
    product2 (r₂ 0) P (r₁ 0) = product2 B₂ P B₁ ∧
    HasDerivAt (fun t => product2 (r₂ t) P (r₁ t))
      (η₂*P*B₁+B₂*P*η₁) 0 := by
  refine ⟨by rw [h₂₀,h₁₀], ?_⟩
  simpa only [h₂₀,h₁₀] using hasDerivAt_product2 P h₂ h₁

/-- Necessary tangency equation obtained by differentiating an actual
orthogonal curve, rather than postulating a tangent space. -/
 theorem orthogonal_curve_velocity {A : ℝ → Mat n} {V : Mat n} {t : ℝ}
    (hA : HasDerivAt A V t) (horth : ∀ s, Orthogonal (A s)) :
    (A t)ᵀ*V + Vᵀ*A t = 0 := by
  have hd := hasDerivAt_matrix_mul (hasDerivAt_matrix_transpose hA) hA
  have he : (fun s => (A s)ᵀ*A s) = (fun _ : ℝ => (1 : Mat n)) :=
    funext (fun s => (horth s).1)
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (1 : Mat n))
  simpa only [add_comm] using hz

 theorem orthogonal_curve_left_generator_skew {A : ℝ → Mat n}
    {V : Mat n} {t : ℝ} (hA : HasDerivAt A V t)
    (horth : ∀ s, Orthogonal (A s)) : IsSkew ((A t)ᵀ*V) := by
  have he := orthogonal_curve_velocity hA horth
  unfold IsSkew
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)

 def frobFunctional (Z : Mat n) : Mat n →L[ℝ] ℝ where
  toFun := frobInner Z
  map_add' := frobInner_add_right Z
  map_smul' a X := by
    change frobInner Z (a • X) = a * frobInner Z X
    rw [frobInner_comm Z _, frobInner_smul_left, frobInner_comm X Z]
  cont := by unfold frobInner; fun_prop

/-- Correct adjoint formula for the two tangent-parameter coordinates. -/
 theorem tangentParam_adjoint_pairing (B₂ P B₁ C Ω Z : Mat n) :
    frobInner Z (tangentParam B₂ P B₁ C Ω) =
      frobInner (B₂ᵀ*Z*B₁ᵀ*Pᵀ) C +
      frobInner (Pᵀ*B₂ᵀ*Z*B₁ᵀ) Ω := by
  unfold tangentParam
  rw [frobInner_add_right]
  have h₁ := lift_adjoint B₂ (P*B₁) Z C
  have h₂ := lift_adjoint (B₂*P) B₁ Z Ω
  simp only [lift, pull, Matrix.transpose_mul, Matrix.mul_assoc] at h₁ h₂
  simpa only [Matrix.mul_assoc] using congrArg₂ (fun a b : ℝ => a+b) h₁ h₂

/-- AD along the actual tangent-parameter affine map, formulated as a scalar
chain rule. No assertion about PyTorch's floating-point implementation. -/
 theorem hasDerivAt_loss_tangent_line (f : Mat n → ℝ)
    (X Z B₂ P B₁ C Ω : Mat n)
    (hf : HasFDerivAt f (frobFunctional Z) X) :
    HasDerivAt (fun t : ℝ => f (X+t•tangentParam B₂ P B₁ C Ω))
      (frobInner (B₂ᵀ*Z*B₁ᵀ*Pᵀ) C +
        frobInner (Pᵀ*B₂ᵀ*Z*B₁ᵀ) Ω) 0 := by
  have h := hf.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_affine_matrix X (tangentParam B₂ P B₁ C Ω) 0) (by simp)
  change HasDerivAt (fun t : ℝ => f (X+t•tangentParam B₂ P B₁ C Ω))
    (frobInner Z (tangentParam B₂ P B₁ C Ω)) 0 at h
  rw [tangentParam_adjoint_pairing] at h
  exact h

end GS.Extensions
