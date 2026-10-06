module

public import GS.OverlapGeometry.Gradient
public import GS.GlobalGeometry.ProjectedDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Moving-generator acceleration with arbitrary overlap

The actual second derivative is computed before projection. The result gives
an explicit evolution equation in the fixed sum of the two supported Lie
algebras. The commutator term is retained; it need not vanish with overlap.
The projected operation is also lifted into the actual tangent space of the
horizontal atlas and paired with its established Frobenius metric.

This module does not register a bundled Levi-Civita connection or assert an
existence theorem for solutions of the resulting differential equation.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
open GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.OverlapGeometry

variable {n : ℕ}

def generatorBracket (C K : Mat n) : Mat n := C*K-K*C

def movingAccelerationCore (C K C' K' : Mat n) : Mat n :=
  C'+K'+accelerationCore C K

theorem movingAccelerationCore_eq (C K C' K' : Mat n) :
    movingAccelerationCore C K C' K' =
      (C'+K'+generatorBracket C K) + (C+K)*(C+K) := by
  simp only [movingAccelerationCore, accelerationCore, generatorBracket,
    Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- Actual differentiation of the factor velocity, with time-dependent generators. -/
theorem moving_product_velocity_hasDerivAt
    (L R C K : ℝ → Mat n) {C' K' : Mat n} {t : ℝ}
    (hL : HasDerivAt L (L t*C t) t) (hR : HasDerivAt R (K t*R t) t)
    (hC : HasDerivAt C C' t) (hK : HasDerivAt K K' t) :
    HasDerivAt (fun s => lift (L s) (R s) (C s+K s))
      (lift (L t) (R t) (movingAccelerationCore (C t) (K t) C' K')) t := by
  have hleft := hasDerivAt_matrix_mul hL (hC.add hK)
  have h := hasDerivAt_matrix_mul hleft hR
  simp only [Pi.add_def] at h
  convert h using 1
  all_goals simp only [lift, movingAccelerationCore, accelerationCore,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  all_goals ext i j
  all_goals simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  all_goals ring

theorem maskedSkew_symmetric_zero (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : Mat n) (hA : Aᵀ=A) : maskedSkew p A = 0 := by
  ext i j
  have he : A j i=A i j := congrFun (congrFun hA i) j
  simp [maskedSkew,mask,skew,he]

def geodesicResidual (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (C K C' K' : Mat n) : Mat n := by
  classical
  exact C'+K'+maskedSkew (tangentUnion b₁ b₂ σ) (generatorBracket C K)

theorem movingAccelerationCore_projection
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (C K C' K' : Mat n)
    (hC : IsSkew C) (hK : IsSkew K)
    (hsC' : Supported b₂ C') (hsK' : Supported (b₁ ∘ σ.symm) K')
    (hC' : IsSkew C') (hK' : IsSkew K') :
    maskedSkew (tangentUnion b₁ b₂ σ) (movingAccelerationCore C K C' K') =
      geodesicResidual b₁ b₂ σ C K C' K' := by
  classical
  have hs : HasSupport (tangentUnion b₁ b₂ σ) (C'+K') := by
    intro i j hij
    have hc : b₂ i ≠ b₂ j := fun hh => hij (Or.inl hh)
    have hk : b₁ (σ.symm i) ≠ b₁ (σ.symm j) := fun hh => hij (Or.inr hh)
    simp only [Matrix.add_apply,hsC' i j hc,hsK' i j hk,zero_add]
  rw [movingAccelerationCore_eq,maskedSkew_add,maskedSkew_add,
    maskedSkew_fixed hs (isSkew_add hC' hK'),
    maskedSkew_symmetric_zero _ _ (skew_square_symmetric _ (isSkew_add hC hK)),add_zero]
  rfl

/-- The fixed-coordinate residual equals the existing point-only tangent projector
applied to the actual moving-generator acceleration. No disjointness is assumed. -/
theorem projected_moving_acceleration
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (L R C K C' K' : Mat n)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hC : IsSkew C) (hK : IsSkew K)
    (hsC' : Supported b₂ C') (hsK' : Supported (b₁ ∘ σ.symm) K')
    (hC' : IsSkew C') (hK' : IsSkew K') :
    pointProjection b₁ b₂ (product2 L (permMatrix σ) R)
      (lift L (permMatrix σ*R) (movingAccelerationCore C K C' K')) =
      lift L (permMatrix σ*R) (geodesicResidual b₁ b₂ σ C K C' K') := by
  rw [pointProjection_lift b₁ b₂ σ L R _ hsL hsR hL hR,
    movingAccelerationCore_projection b₁ b₂ σ C K C' K' hC hK hsC' hsK' hC' hK']

theorem projected_moving_acceleration_zero_iff
    (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (L R C K C' K' : Mat n)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hC : IsSkew C) (hK : IsSkew K)
    (hsC' : Supported b₂ C') (hsK' : Supported (b₁ ∘ σ.symm) K')
    (hC' : IsSkew C') (hK' : IsSkew K') :
    pointProjection b₁ b₂ (product2 L (permMatrix σ) R)
      (lift L (permMatrix σ*R) (movingAccelerationCore C K C' K')) = 0 ↔
      geodesicResidual b₁ b₂ σ C K C' K' = 0 := by
  rw [projected_moving_acceleration b₁ b₂ σ L R C K C' K' hsL hsR hL hR
    hC hK hsC' hsK' hC' hK']
  have hinj := lift_injective L (permMatrix σ*R) hL ((perm_orthogonal σ).mul hR)
  have hz : lift L (permMatrix σ*R) (0 : Mat n) = 0 := by simp [lift]
  constructor
  · intro h
    apply hinj
    exact h.trans hz.symm
  · intro h
    rw [h,hz]

section ActualTangent
variable (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance geodesicHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance geodesicChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance geodesicIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

def covariantAlong (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ))
    (V : ℝ → Mat n) (t : ℝ) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (γ t) :=
  tangentProjection b₁ b₂ σ (γ t) (deriv V t)

@[simp] theorem inclusion_covariantAlong
    (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) (V : ℝ → Mat n) (t : ℝ) :
    inclusionDifferential b₁ b₂ σ (γ t) (covariantAlong b₁ b₂ σ γ V t) =
      pointProjection b₁ b₂ (γ t).val (deriv V t) :=
  inclusion_tangentProjection b₁ b₂ σ (γ t) (deriv V t)

/-- The projected derivative is characterized by the actual Frobenius metric
against every genuine tangent vector of the arbitrary-overlap atlas. -/
theorem covariantAlong_pairing
    (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) (V : ℝ → Mat n) (t : ℝ)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (γ t)) :
    tangentPairing b₁ b₂ σ (γ t) (covariantAlong b₁ b₂ σ γ V t) w =
      frobInner (deriv V t) (inclusionDifferential b₁ b₂ σ (γ t) w) :=
  tangentProjection_pairing b₁ b₂ σ (γ t) (deriv V t) w

end ActualTangent
end GS.OverlapGeometry
