module

public import GS.Unitary.SmoothPointProjection
public import GS.UnitaryManifold.PointProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Joint smoothness of the actual unitary tangent projection as its matrix
base point and ambient direction vary. The orbit has the inherited topology. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance projectorSmoothHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance projectorSmoothHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- Equality is proved using factors, but the resulting formula uses only X. -/
theorem pointProjection_eq_polynomial (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (Z : CMat n) :
    pointProjection b₁ b₂ X.val Z = polynomialPointProjection b₁ b₂ X.val Z := by
  rw [← preferredFactor_product b₁ b₂ σ X]
  exact (polynomialPointProjection_eq b₁ b₂ σ _ _ Z
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.conjTranspose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.conjTranspose).symm

set_option maxHeartbeats 800000 in
/-- The genuine orthogonal projector is smooth in both variables on the orbit. -/
theorem pointProjection_joint_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel b₁ b₂ σ)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n)) ⊤
      (fun p : MatrixOrbit b₁ b₂ (cPermMatrix σ) × CMat n =>
        pointProjection b₁ b₂ p.1.val p.2) := by
  have ha : ContMDiff ((𝓘(ℝ, HorizontalModel b₁ b₂ σ)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n × CMat n)) ⊤
      (fun p : MatrixOrbit b₁ b₂ (cPermMatrix σ) × CMat n => (p.1.val,p.2)) :=
    ((overlap_val_contMDiff b₁ b₂ σ).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hp := (polynomialPointProjection_smooth b₁ b₂).comp_contMDiff ha
  simpa only [pointProjection_eq_polynomial b₁ b₂ σ, Function.comp_def] using hp

end GS.UnitaryManifold
