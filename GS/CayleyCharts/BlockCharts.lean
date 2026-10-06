module

public import GS.CayleyCharts.Smooth
public import GS.LieAction.BlockGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit open charts on the existing `GS.LieAction.BlockO`

No topology is transferred to BlockO. Both sets below use the original subtype
topology. The coordinate target is an OPEN subset of a finite-dimensional real
vector space, not the variety defined by orthogonality equations.

The atlas ingredients are given by actual `Homeomorph`s and `ContDiffAt`
theorems. The mathlib ChartedSpace/IsManifold structures built from these charts are
installed in `GS.CayleyCharts.Atlas`.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

def parameterDomain (block : Fin n → ℕ) : Set (Model block) :=
  {x | admissible x.val}

/-- Skew coordinates require no size restriction: their denominator is always invertible. -/
@[simp] theorem parameterDomain_eq_univ (block : Fin n → ℕ) :
    parameterDomain block = Set.univ := by
  exact Set.eq_univ_iff_forall.mpr (fun x => admissible_model x)

def chartSource (Q : BlockO block) : Set (BlockO block) :=
  {U | admissible (Q.valᵀ * U.val)}

/-- Defined on the ambient matrix space. On the chart source the projection
is the identity on its input; this extension makes smoothness unambiguous. -/
def chartMap (Q : BlockO block) (X : Mat n) : Model block :=
  modelProjection block (cayley (Q.valᵀ * X))

/-- Reconstruction is an actual rational matrix formula. -/
def chartInv (Q : BlockO block) (x : Model block) : Mat n :=
  Q.val * cayley x.val

theorem parameterDomain_open (block : Fin n → ℕ) :
    IsOpen (parameterDomain block) :=
  admissible_open.preimage (modelInclusion block).continuous

theorem chartSource_open (Q : BlockO block) : IsOpen (chartSource Q) :=
  admissible_open.preimage
    (continuous_matrix_product continuous_const continuous_subtype_val)

@[simp] theorem zero_mem_parameterDomain (block : Fin n → ℕ) :
    (0 : Model block) ∈ parameterDomain block := admissible_zero

@[simp] theorem base_mem_chartSource (Q : BlockO block) : Q ∈ chartSource Q := by
  change admissible (Q.valᵀ * Q.val)
  rw [Q.property.2.1]
  exact admissible_one

/-- This membership calculation, not an assumption of a tangent structure,
justifies removing modelProjection in chart identities. -/
theorem centered_cayley_mem_model (Q U : BlockO block) (hU : U ∈ chartSource Q) :
    cayley (Q.valᵀ * U.val) ∈ modelSpace block := by
  exact ⟨cayley_supported block _ (Q.property.1.transpose.mul U.property.1) hU,
    cayley_isSkew _ (Q.property.2.transpose.mul U.property.2) hU⟩

theorem chartMap_val (Q U : BlockO block) (hU : U ∈ chartSource Q) :
    (chartMap Q U.val).val = cayley (Q.valᵀ * U.val) :=
  modelProjection_val_of_mem block _ (centered_cayley_mem_model Q U hU)

theorem chartMap_mem_domain (Q U : BlockO block) (hU : U ∈ chartSource Q) :
    chartMap Q U.val ∈ parameterDomain block := by
  change admissible (chartMap Q U.val).val
  rw [chartMap_val Q U hU]
  exact admissible_cayley _ hU

theorem chartInv_supported (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) : Supported block (chartInv Q x) :=
  Q.property.1.mul (cayley_supported block x.val x.property.1 hx)

theorem chartInv_orthogonal (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) : Orthogonal (chartInv Q x) :=
  Q.property.2.mul (cayley_orthogonal x.val x.property.2 hx)

/-- Both components of O(b), and any product of such components, are allowed. -/
def reconstructBlock (Q : BlockO block) (x : parameterDomain block) : BlockO block :=
  ⟨chartInv Q x.val, chartInv_supported Q x.val x.property,
    chartInv_orthogonal Q x.val x.property⟩

theorem centered_chartInv (Q : BlockO block) (x : Model block) :
    Q.valᵀ * chartInv Q x = cayley x.val := by
  simp only [chartInv, ← Matrix.mul_assoc, Q.property.2.1, Matrix.one_mul]

theorem reconstruct_mem_source (Q : BlockO block) (x : parameterDomain block) :
    reconstructBlock Q x ∈ chartSource Q := by
  change admissible (Q.valᵀ * chartInv Q x.val)
  rw [centered_chartInv]
  exact admissible_cayley _ x.property

theorem chartMap_chartInv (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) : chartMap Q (chartInv Q x) = x := by
  unfold chartMap
  rw [centered_chartInv, cayley_involutive x.val hx]
  exact modelProjection_inclusion block x

theorem chartInv_chartMap (Q U : BlockO block) (hU : U ∈ chartSource Q) :
    chartInv Q (chartMap Q U.val) = U.val := by
  unfold chartInv
  rw [chartMap_val Q U hU, cayley_involutive _ hU]
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

@[simp] theorem chartInv_zero (Q : BlockO block) : chartInv Q 0 = Q.val := by
  simp [chartInv]

@[simp] theorem chartMap_base (Q : BlockO block) : chartMap Q Q.val = 0 := by
  simp [chartMap, Q.property.2.1]

/-- Smoothness is in an open ambient matrix neighbourhood of the point. -/
theorem chartMap_smooth_at (Q : BlockO block) (X : Mat n)
    (hX : admissible (Q.valᵀ * X)) : ContDiffAt ℝ ⊤ (chartMap Q) X := by
  exact (modelProjection block).contDiff.contDiffAt.comp X
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hX)

theorem chartInv_smooth_at (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) : ContDiffAt ℝ ⊤ (chartInv Q) x :=
  smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (modelInclusion block).contDiff.contDiffAt hx)

/-- Reconstruction is smooth on the entire finite-dimensional coordinate space. -/
theorem chartInv_smooth (Q : BlockO block) : ContDiff ℝ ⊤ (chartInv Q) := by
  exact contDiff_iff_contDiffAt.mpr (fun x => chartInv_smooth_at Q x (admissible_model x))

theorem chartInv_smooth_on (Q : BlockO block) :
    ContDiffOn ℝ ⊤ (chartInv Q) (parameterDomain block) := by
  intro x hx
  exact (chartInv_smooth_at Q x hx).contDiffWithinAt

theorem continuous_chartMap_restrict (Q : BlockO block) :
    Continuous (fun U : chartSource Q => chartMap Q U.val.val) := by
  apply continuous_iff_continuousAt.mpr
  intro U
  exact ContinuousAt.comp (f := fun W : chartSource Q => W.val.val) (g := chartMap Q)
    (chartMap_smooth_at Q U.val.val U.property).continuousAt
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

theorem continuous_chartInv_restrict (Q : BlockO block) :
    Continuous (fun x : parameterDomain block => chartInv Q x.val) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (chartInv_smooth_at Q x.val x.property).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- The topology on both sides is inherited; the forward and inverse functions
are the explicit formulas above, not an unspecified bijection. -/
def blockChartHomeomorph (Q : BlockO block) :
    chartSource Q ≃ₜ parameterDomain block where
  toFun U := ⟨chartMap Q U.val.val, chartMap_mem_domain Q U.val U.property⟩
  invFun x := ⟨reconstructBlock Q x, reconstruct_mem_source Q x⟩
  left_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    exact chartInv_chartMap Q U.val U.property
  right_inv x := by
    apply Subtype.ext
    exact chartMap_chartInv Q x.val x.property
  continuous_toFun := (continuous_chartMap_restrict Q).subtype_mk _
  continuous_invFun := ((continuous_chartInv_restrict Q).subtype_mk _).subtype_mk _

@[simp] theorem blockChartHomeomorph_apply (Q : BlockO block) (U : chartSource Q) :
    (blockChartHomeomorph Q U).val = chartMap Q U.val.val := rfl

@[simp] theorem blockChartHomeomorph_symm_apply (Q : BlockO block)
    (x : parameterDomain block) :
    ((blockChartHomeomorph Q).symm x).val.val = chartInv Q x.val := rfl

/-- Local Euclidean structure expressed without relying on a version-specific
manifold constructor. The target is an open subset of `Model block`. -/
theorem blockO_has_open_model_charts (Q : BlockO block) :
    ∃ U : Set (BlockO block), ∃ V : Set (Model block),
      IsOpen U ∧ Q ∈ U ∧ IsOpen V ∧ (0 : Model block) ∈ V ∧
        Nonempty (U ≃ₜ V) :=
  ⟨chartSource Q, parameterDomain block, chartSource_open Q,
    base_mem_chartSource Q, parameterDomain_open block,
    zero_mem_parameterDomain block, ⟨blockChartHomeomorph Q⟩⟩

end GS.CayleyCharts
