module

public import GS.GlobalGeometry.BalancedLift
public import GS.Continuation.FactorCurveVelocities
public import GS.RiemannianCompletion.ExponentialStep

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Projected derivatives along actual matrix curves

The operation is Pi_(gamma(t)) (deriv V t). We prove the linear connection
rules and metric compatibility for differentiable tangent vector fields, and
apply them to the already constructed exponential curves. Actual derivatives
are used throughout. This is NOT registered as mathlib's Levi-Civita connection:
the missing bundle/connection registration and torsion-free identification are
explicitly recorded in the coverage report.

Metric compatibility permits overlap for independent blocks. The exponential
parallel-velocity conclusion retains the original no-overlap hypothesis.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation Filter
open scoped BigOperators Topology Manifold
namespace GS.GlobalGeometry
variable {n : ℕ}

@[simp] theorem leftPointProjection_add (b : Fin n → ℕ) (X A B : Mat n) :
    leftPointProjection b X (A+B) = leftPointProjection b X A+leftPointProjection b X B := by
  simp only [leftPointProjection, Matrix.add_mul, blockSkew_add]

@[simp] theorem rightPointProjection_add (b : Fin n → ℕ) (X A B : Mat n) :
    rightPointProjection b X (A+B) = rightPointProjection b X A+rightPointProjection b X B := by
  simp only [rightPointProjection, Matrix.mul_add, blockSkew_add]

@[simp] theorem leftPointProjection_smul (b : Fin n → ℕ) (X A : Mat n) (a : ℝ) :
    leftPointProjection b X (a•A) = a•leftPointProjection b X A := by
  simp only [leftPointProjection, Matrix.smul_mul, blockSkew_smul]

@[simp] theorem rightPointProjection_smul (b : Fin n → ℕ) (X A : Mat n) (a : ℝ) :
    rightPointProjection b X (a•A) = a•rightPointProjection b X A := by
  simp only [rightPointProjection, Matrix.mul_smul, blockSkew_smul]

theorem pointProjection_add (b₁ b₂ : Fin n → ℕ) (X A B : Mat n) :
    pointProjection b₁ b₂ X (A+B) = pointProjection b₁ b₂ X A+pointProjection b₁ b₂ X B := by
  simp only [pointProjection, leftPointProjection_add, rightPointProjection_add]
  abel

theorem pointProjection_smul (b₁ b₂ : Fin n → ℕ) (X A : Mat n) (a : ℝ) :
    pointProjection b₁ b₂ X (a•A) = a•pointProjection b₁ b₂ X A := by
  simp only [pointProjection, leftPointProjection_smul, rightPointProjection_smul,
    smul_add, smul_sub]

def alongDerivative (b₁ b₂ : Fin n → ℕ) (γ V : ℝ → Mat n) (t : ℝ) : Mat n :=
  pointProjection b₁ b₂ (γ t) (deriv V t)

theorem alongDerivative_add (b₁ b₂ : Fin n → ℕ) (γ V W : ℝ → Mat n)
    {v w : Mat n} {t : ℝ} (hv : HasDerivAt V v t) (hw : HasDerivAt W w t) :
    alongDerivative b₁ b₂ γ (fun s => V s+W s) t =
      alongDerivative b₁ b₂ γ V t+alongDerivative b₁ b₂ γ W t := by
  have hadd : HasDerivAt (fun s => V s + W s) (v+w) t := by
    simpa only [Pi.add_def] using hv.add hw
  simp only [alongDerivative, hadd.deriv, hv.deriv, hw.deriv, pointProjection_add]

theorem alongDerivative_leibniz (b₁ b₂ : Fin n → ℕ) (γ V : ℝ → Mat n)
    (a : ℝ → ℝ) {a' : ℝ} {v : Mat n} {t : ℝ}
    (ha : HasDerivAt a a' t) (hv : HasDerivAt V v t)
    (ht : pointProjection b₁ b₂ (γ t) (V t) = V t) :
    alongDerivative b₁ b₂ γ (fun s => a s • V s) t =
      a' • V t + a t • alongDerivative b₁ b₂ γ V t := by
  have hsmul : HasDerivAt (fun s => a s • V s) (a t • v + a' • V t) t := by
    simpa only [Pi.smul_def'] using ha.smul hv
  simp only [alongDerivative, hsmul.deriv, hv.deriv,
    pointProjection_add, pointProjection_smul, ht]
  exact add_comm _ _

/-- Product rule in the actual Frobenius pairing, not a change of matrix norm. -/
theorem hasDerivAt_frobInner {V W : ℝ → Mat n} {v w : Mat n} {t : ℝ}
    (hv : HasDerivAt V v t) (hw : HasDerivAt W w t) :
    HasDerivAt (fun s => frobInner (V s) (W s))
      (frobInner v (W t)+frobInner (V t) w) t := by
  have hh : HasDerivAt (fun s => ∑ i, ∑ j, V s i j*W s i j)
      (∑ i, ∑ j, (v i j*W t i j+V t i j*w i j)) t := by
    simpa only [Finset.sum_fn, Pi.mul_def] using
      HasDerivAt.sum (u := Finset.univ) (fun i _ =>
        HasDerivAt.sum (u := Finset.univ) (fun j _ =>
          (hasDerivAt_pi.mp (hasDerivAt_pi.mp hv i) j).mul
            (hasDerivAt_pi.mp (hasDerivAt_pi.mp hw i) j)))
  simpa only [frobInner, Finset.sum_add_distrib] using hh

theorem alongDerivative_metric_compatible (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R : Mat n) (γ V W : ℝ → Mat n)
    {v w : Mat n} {t : ℝ}
    (hγ : γ t = product2 L (permMatrix σ) R)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hv : HasDerivAt V v t) (hw : HasDerivAt W w t)
    (htV : pointProjection b₁ b₂ (γ t) (V t)=V t)
    (htW : pointProjection b₁ b₂ (γ t) (W t)=W t) :
    HasDerivAt (fun s => frobInner (V s) (W s))
      (frobInner (alongDerivative b₁ b₂ γ V t) (W t)+
        frobInner (V t) (alongDerivative b₁ b₂ γ W t)) t := by
  have hvp : frobInner (pointProjection b₁ b₂ (γ t) v) (W t) = frobInner v (W t) := by
    have h := pointProjection_self_adjoint b₁ b₂ σ L R v (W t) hsL hsR hL hR
    dsimp only at h
    rw [← hγ, htW] at h
    exact h
  have hwp : frobInner (V t) (pointProjection b₁ b₂ (γ t) w) = frobInner (V t) w := by
    have h := pointProjection_self_adjoint b₁ b₂ σ L R (V t) w hsL hsR hL hR
    dsimp only at h
    rw [← hγ, htV] at h
    exact h.symm
  simpa only [alongDerivative, hv.deriv, hw.deriv, hvp, hwp] using hasDerivAt_frobInner hv hw

/-- Parallel tangent fields have zero derivative of their squared length. -/
theorem alongDerivative_parallel_length (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R : Mat n) (γ V : ℝ → Mat n)
    {v : Mat n} {t : ℝ} (hγ : γ t = product2 L (permMatrix σ) R)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R) (hv : HasDerivAt V v t)
    (htV : pointProjection b₁ b₂ (γ t) (V t)=V t)
    (hp : alongDerivative b₁ b₂ γ V t=0) :
    HasDerivAt (fun s => frobSq (V s)) 0 t := by
  have h := alongDerivative_metric_compatible b₁ b₂ σ L R γ V V hγ
    hsL hsR hL hR hv hv htV htV
  simpa only [hp, frobInner_zero_left, frobInner_zero_right, zero_add, frobSq] using h

/-- A concrete exponential velocity is parallel for the projected operation.
No user-supplied differential equation is assumed. -/
theorem gsExpVelocity_parallel (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R C Ω : Mat n)
    (hno : OffDiagonalDisjoint b₂ (b₁ ∘ σ.symm))
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hsC : Supported b₂ C) (hsΩ : Supported b₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    alongDerivative b₁ b₂ (gsExpCurve L (permMatrix σ) R C Ω)
      (gsExpVelocity L (permMatrix σ) R C Ω) t = 0 := by
  unfold alongDerivative
  rw [(gsExpVelocity_hasDerivAt L (permMatrix σ) R C Ω (perm_orthogonal σ) t).deriv]
  exact gsExpCurve_projected_acceleration_zero b₁ b₂ σ L R C Ω hno
    hsL hsR hL hR hsC hsΩ hC hΩ t

section ActualTangent
open GS.LieAction GS.CayleyCharts GS.ManifoldCompletion GS.RiemannianCompletion
variable {b₁ b₂ : Fin n → ℕ} (σ : Equiv.Perm (Fin n))
variable [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- Pointwise lift of the projected derivative to the genuine tangent fibre.
Smoothness as a connection on the whole bundle is a separate obligation. -/
def tangentAlongDerivative (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ))
    (V : ℝ → Mat n) (t : ℝ) :
    TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) (γ t) :=
  tangentProjection σ (γ t) (deriv V t)

@[simp] theorem inclusion_tangentAlongDerivative
    (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) (V : ℝ → Mat n) (t : ℝ) :
    inclusionDifferential σ (γ t) (tangentAlongDerivative σ γ V t) =
      alongDerivative b₁ b₂ (fun s => (γ s).val) V t :=
  inclusion_tangentProjection σ (γ t) (deriv V t)

theorem exponentialStep_tangentVelocity_parallel
    (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) (t : ℝ) :
    tangentAlongDerivative σ (exponentialStep σ X v) (stepVelocity σ X v) t = 0 := by
  unfold tangentAlongDerivative
  rw [(stepVelocity_hasDerivAt σ X v t).deriv]
  exact stepAcceleration_tangent_lift_zero σ X v t
end ActualTangent
end GS.GlobalGeometry
