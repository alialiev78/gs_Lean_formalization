module

public import GS.LieAction.BlockGroup
public import GS.Frobenius
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Two-sided action, its orbit, and smooth ambient matrix operations

This is an actual mathlib MulAction and ContinuousSMul, not an orbit-shaped
existential definition. ContDiff below is in ambient matrix coordinates.
It does not assert a charted-space structure on BlockO or on its orbit.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.LieAction
variable {n : ℕ}

instance factorMulAction (block₁ block₂ : Fin n → ℕ) :
    MulAction (FactorGroup block₁ block₂) (Mat n) where
  smul g X := g.1.val * X * g.2.valᵀ
  one_smul X := by
    change ((1 : Mat n) * X) * (1 : Mat n)ᵀ = X
    simp
  mul_smul g h X := by
    change ((g.1.val * h.1.val) * X) * (g.2.val * h.2.val)ᵀ =
      (g.1.val * ((h.1.val * X) * h.2.valᵀ)) * g.2.valᵀ
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X : Mat n) :
    g • X = (g.1 : Mat n) * X * (g.2 : Mat n)ᵀ := rfl

instance factorContinuousSMul (block₁ block₂ : Fin n → ℕ) :
    ContinuousSMul (FactorGroup block₁ block₂) (Mat n) where
  continuous_smul := by
    change Continuous (fun p : FactorGroup block₁ block₂ × Mat n =>
      p.1.1.val * p.2 * p.1.2.valᵀ)
    exact continuous_matrix_product
      (continuous_matrix_product
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (continuous_matrix_transpose
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))

/-- The concrete orbit map. P may be any matrix for this definition. -/
def orbitMap (block₁ block₂ : Fin n → ℕ) (P : Mat n) :
    FactorGroup block₁ block₂ → Mat n := fun g => g • P

theorem continuous_orbitMap (block₁ block₂ : Fin n → ℕ) (P : Mat n) :
    Continuous (orbitMap block₁ block₂ P) := by
  exact continuous_id.smul continuous_const

theorem action_preserves_orthogonal {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) {X : Mat n} (hX : Orthogonal X) :
    Orthogonal (g • X) :=
  (g.1.property.2.mul hX).mul g.2.property.2.transpose

theorem orbit_eq_range (block₁ block₂ : Fin n → ℕ) (P : Mat n) :
    MulAction.orbit (FactorGroup block₁ block₂) P =
      Set.range (orbitMap block₁ block₂ P) := rfl

/-- Transposition of the right orthogonal factor connects the group action
with the untransposed factorization in GS.Core. -/
theorem orbit_iff_inA2Orth (b₁ b₂ : ℕ) (P X : Mat n) :
    X ∈ MulAction.orbit
      (FactorGroup (fun i : Fin n => i.val / b₁)
                   (fun i : Fin n => i.val / b₂)) P ↔
      InA2Orth b₁ b₂ P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.2.valᵀ, g.1.val, g.2.property.1.transpose,
      g.1.property.1, g.2.property.2.transpose, g.1.property.2, hg.symm⟩
  · rintro ⟨B₁, B₂, hs₁, hs₂, ho₁, ho₂, hX⟩
    refine ⟨(⟨B₂, hs₂, ho₂⟩, ⟨B₁ᵀ, hs₁.transpose, ho₁.transpose⟩), ?_⟩
    simpa only [action_apply, Matrix.transpose_transpose, product2] using hX.symm

theorem orbit_set_eq_inA2Orth (b₁ b₂ : ℕ) (P : Mat n) :
    MulAction.orbit
      (FactorGroup (fun i : Fin n => i.val / b₁)
                   (fun i : Fin n => i.val / b₂)) P =
      {X : Mat n | InA2Orth b₁ b₂ P X} := by
  ext X
  exact orbit_iff_inA2Orth b₁ b₂ P X

theorem action_frobInner {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X Y : Mat n) :
    frobInner (g • X) (g • Y) = frobInner X Y := by
  change frobInner (g.1.val * X * g.2.valᵀ)
    (g.1.val * Y * g.2.valᵀ) = _
  rw [frobInner_right_orthogonal _ g.2.property.2.transpose,
    frobInner_left_orthogonal _ g.1.property.2]

theorem action_frobDistSq {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X Y : Mat n) :
    frobDistSq (g • X) (g • Y) = frobDistSq X Y :=
  boundary_frobDistSq _ _ g.1.property.2 g.2.property.2.transpose X Y

/-- A fixed group element is a linear equivalence of the ambient matrix space.
No assertion about an inappropriate default matrix norm is made. -/
def actionLinearEquiv {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : Mat n ≃ₗ[ℝ] Mat n where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv X := inv_smul_smul g X
  right_inv X := smul_inv_smul g X
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.smul_mul]

/-- Continuous forward and inverse ambient action maps. -/
def actionHomeomorph {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : Mat n ≃ₜ Mat n where
  toEquiv := (actionLinearEquiv g).toEquiv
  continuous_toFun := continuous_const_smul g
  continuous_invFun := (continuous_const_smul (g⁻¹))

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Smooth multiplication written componentwise so it uses the ordinary
finite-product matrix norm, not an assumed operator-norm inner product. -/
theorem smooth_matrix_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E → Mat n} (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum; intro k _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j)

theorem smooth_matrix_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => (A x)ᵀ) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  exact contDiff_pi.mp (contDiff_pi.mp hA j) i

theorem ambient_action_smooth :
    ContDiff ℝ ⊤ (fun p : Mat n × Mat n × Mat n => p.1 * p.2.1 * p.2.2ᵀ) :=
  smooth_matrix_product (smooth_matrix_product contDiff_fst
    (contDiff_fst.comp contDiff_snd))
    (smooth_matrix_transpose (contDiff_snd.comp contDiff_snd))

theorem fixed_action_smooth {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : ContDiff ℝ ⊤ (fun X : Mat n => g • X) :=
  smooth_matrix_product (smooth_matrix_product contDiff_const contDiff_id) contDiff_const

/-- Any smooth matrix-valued parameterization of the two factors gives a smooth
orbit parameterization. This does not assume a manifold on the image. -/
theorem orbit_in_smooth_parameters {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L R : E → Mat n} (hL : ContDiff ℝ ⊤ L) (hR : ContDiff ℝ ⊤ R) (P : Mat n) :
    ContDiff ℝ ⊤ (fun x => L x * P * (R x)ᵀ) :=
  smooth_matrix_product (smooth_matrix_product hL contDiff_const)
    (smooth_matrix_transpose hR)

end GS.LieAction
