module

public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.BlockGroup
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit open charts on the existing `GS.UnitaryManifold.BlockU`

No topology is transferred to BlockU. Both sets below use the original subtype
topology. The coordinate target is an OPEN subset of a finite-dimensional real
vector space, not the variety defined by unitarity equations.

The atlas ingredients are given by actual `Homeomorph`s and `ContDiffAt`
theorems. The mathlib ChartedSpace/IsManifold structures built from these charts are
installed in `GS.UnitaryManifold.CayleyAtlas`.

All constructions use the original complex matrix topology and real calculus.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ} {block : Fin n → ℕ}

def parameterDomain (block : Fin n → ℕ) : Set (Model block) :=
  {x | admissible x.val}

/-- Skew coordinates require no size restriction: their denominator is always invertible. -/
@[simp] theorem parameterDomain_eq_univ (block : Fin n → ℕ) :
    parameterDomain block = Set.univ := by
  exact Set.eq_univ_iff_forall.mpr (fun x => admissible_model x)

def chartSource (Q : BlockU block) : Set (BlockU block) :=
  {U | admissible (Q.valᴴ * U.val)}

/-- Defined on the ambient matrix space. On the chart source the projection
is the identity on its input; this extension makes smoothness unambiguous. -/
def chartMap (Q : BlockU block) (X : CMat n) : Model block :=
  modelProjection block (cayley (Q.valᴴ * X))

/-- Reconstruction is an actual rational matrix formula. -/
def chartInv (Q : BlockU block) (x : Model block) : CMat n :=
  Q.val * cayley x.val

theorem parameterDomain_open (block : Fin n → ℕ) :
    IsOpen (parameterDomain block) :=
  admissible_open.preimage (modelInclusion block).continuous

theorem chartSource_open (Q : BlockU block) : IsOpen (chartSource Q) :=
  admissible_open.preimage
    (continuous_matrix_product continuous_const continuous_subtype_val)

@[simp] theorem zero_mem_parameterDomain (block : Fin n → ℕ) :
    (0 : Model block) ∈ parameterDomain block := admissible_zero

@[simp] theorem base_mem_chartSource (Q : BlockU block) : Q ∈ chartSource Q := by
  change admissible (Q.valᴴ * Q.val)
  rw [Q.property.2.1]
  exact admissible_one

/-- This membership calculation, not an assumption of a tangent structure,
justifies removing modelProjection in chart identities. -/
theorem centered_cayley_mem_model (Q U : BlockU block) (hU : U ∈ chartSource Q) :
    cayley (Q.valᴴ * U.val) ∈ modelSpace block := by
  exact ⟨cayley_supported block _ (Q.property.1.conjTranspose.mul U.property.1) hU,
    cayley_isSkew _ (Q.property.2.conjTranspose.mul U.property.2) hU⟩

theorem chartMap_val (Q U : BlockU block) (hU : U ∈ chartSource Q) :
    (chartMap Q U.val).val = cayley (Q.valᴴ * U.val) :=
  modelProjection_val_of_mem block _ (centered_cayley_mem_model Q U hU)

theorem chartMap_mem_domain (Q U : BlockU block) (hU : U ∈ chartSource Q) :
    chartMap Q U.val ∈ parameterDomain block := by
  change admissible (chartMap Q U.val).val
  rw [chartMap_val Q U hU]
  exact admissible_cayley _ hU

theorem chartInv_supported (Q : BlockU block) (x : Model block)
    (hx : x ∈ parameterDomain block) : CSupported block (chartInv Q x) :=
  Q.property.1.mul (cayley_supported block x.val x.property.1 hx)

theorem chartInv_unitary (Q : BlockU block) (x : Model block)
    (hx : x ∈ parameterDomain block) : Unitary (chartInv Q x) :=
  Q.property.2.mul (cayley_unitary x.val x.property.2 hx)

/-- Every supported unitary factor is represented in its centred chart. -/
def reconstructBlock (Q : BlockU block) (x : parameterDomain block) : BlockU block :=
  ⟨chartInv Q x.val, chartInv_supported Q x.val x.property,
    chartInv_unitary Q x.val x.property⟩

theorem centered_chartInv (Q : BlockU block) (x : Model block) :
    Q.valᴴ * chartInv Q x = cayley x.val := by
  simp only [chartInv, ← Matrix.mul_assoc, Q.property.2.1, Matrix.one_mul]

theorem reconstruct_mem_source (Q : BlockU block) (x : parameterDomain block) :
    reconstructBlock Q x ∈ chartSource Q := by
  change admissible (Q.valᴴ * chartInv Q x.val)
  rw [centered_chartInv]
  exact admissible_cayley _ x.property

theorem chartMap_chartInv (Q : BlockU block) (x : Model block)
    (hx : x ∈ parameterDomain block) : chartMap Q (chartInv Q x) = x := by
  unfold chartMap
  rw [centered_chartInv, cayley_involutive x.val hx]
  exact modelProjection_inclusion block x

theorem chartInv_chartMap (Q U : BlockU block) (hU : U ∈ chartSource Q) :
    chartInv Q (chartMap Q U.val) = U.val := by
  unfold chartInv
  rw [chartMap_val Q U hU, cayley_involutive _ hU]
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

@[simp] theorem chartInv_zero (Q : BlockU block) : chartInv Q 0 = Q.val := by
  simp [chartInv]

@[simp] theorem chartMap_base (Q : BlockU block) : chartMap Q Q.val = 0 := by
  simp [chartMap, Q.property.2.1]

/-- Smoothness is in an open ambient matrix neighbourhood of the point. -/
theorem chartMap_smooth_at (Q : BlockU block) (X : CMat n)
    (hX : admissible (Q.valᴴ * X)) : ContDiffAt ℝ ⊤ (chartMap Q) X := by
  exact (modelProjection block).contDiff.contDiffAt.comp X
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hX)

theorem chartInv_smooth_at (Q : BlockU block) (x : Model block)
    (hx : x ∈ parameterDomain block) : ContDiffAt ℝ ⊤ (chartInv Q) x :=
  smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (modelInclusion block).contDiff.contDiffAt hx)

/-- Reconstruction is smooth on the entire finite-dimensional coordinate space. -/
theorem chartInv_smooth (Q : BlockU block) : ContDiff ℝ ⊤ (chartInv Q) := by
  exact contDiff_iff_contDiffAt.mpr (fun x => chartInv_smooth_at Q x (admissible_model x))

theorem chartInv_smooth_on (Q : BlockU block) :
    ContDiffOn ℝ ⊤ (chartInv Q) (parameterDomain block) := by
  intro x hx
  exact (chartInv_smooth_at Q x hx).contDiffWithinAt

theorem continuous_chartMap_restrict (Q : BlockU block) :
    Continuous (fun U : chartSource Q => chartMap Q U.val.val) := by
  apply continuous_iff_continuousAt.mpr
  intro U
  exact ContinuousAt.comp (f := fun W : chartSource Q => W.val.val) (g := chartMap Q)
    (chartMap_smooth_at Q U.val.val U.property).continuousAt
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

theorem continuous_chartInv_restrict (Q : BlockU block) :
    Continuous (fun x : parameterDomain block => chartInv Q x.val) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (chartInv_smooth_at Q x.val x.property).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- The topology on both sides is inherited; the forward and inverse functions
are the explicit formulas above, not an unspecified bijection. -/
def blockChartHomeomorph (Q : BlockU block) :
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

@[simp] theorem blockChartHomeomorph_apply (Q : BlockU block) (U : chartSource Q) :
    (blockChartHomeomorph Q U).val = chartMap Q U.val.val := rfl

@[simp] theorem blockChartHomeomorph_symm_apply (Q : BlockU block)
    (x : parameterDomain block) :
    ((blockChartHomeomorph Q).symm x).val.val = chartInv Q x.val := rfl

/-- Local Euclidean structure expressed without relying on a version-specific
manifold constructor. The target is an open subset of `Model block`. -/
theorem blockU_has_open_model_charts (Q : BlockU block) :
    ∃ U : Set (BlockU block), ∃ V : Set (Model block),
      IsOpen U ∧ Q ∈ U ∧ IsOpen V ∧ (0 : Model block) ∈ V ∧
        Nonempty (U ≃ₜ V) :=
  ⟨chartSource Q, parameterDomain block, chartSource_open Q,
    base_mem_chartSource Q, parameterDomain_open block,
    zero_mem_parameterDomain block, ⟨blockChartHomeomorph Q⟩⟩


/-- Total reconstruction; skew-Hermitian parameters need no domain restriction. -/
def blockChartInverse (Q : BlockU block) (x : Model block) : BlockU block :=
  ⟨chartInv Q x, chartInv_supported Q x (admissible_model x),
    chartInv_unitary Q x (admissible_model x)⟩

theorem blockChartInverse_val (Q : BlockU block) (x : Model block)
    (_hx : x ∈ parameterDomain block) :
    (blockChartInverse Q x).val = chartInv Q x := rfl

@[simp] theorem blockChartInverse_val_everywhere (Q : BlockU block) (x : Model block) :
    (blockChartInverse Q x).val = chartInv Q x := rfl

theorem continuous_blockChartInverse (Q : BlockU block) :
    Continuous (blockChartInverse Q) := (chartInv_smooth Q).continuous.subtype_mk _

/-- A genuine Cayley partial homeomorphism in the inherited matrix topology. -/
def blockPartialChart (Q : BlockU block) :
    OpenPartialHomeomorph (BlockU block) (Model block) where
  toFun U := chartMap Q U.val
  invFun := blockChartInverse Q
  source := chartSource Q
  target := parameterDomain block
  map_source' U hU := chartMap_mem_domain Q U hU
  map_target' x hx := by
    change admissible (Q.valᴴ * chartInv Q x)
    rw [centered_chartInv]
    exact admissible_cayley x.val hx
  left_inv' U hU := by
    apply Subtype.ext
    exact chartInv_chartMap Q U hU
  right_inv' x hx := chartMap_chartInv Q x hx
  open_source := chartSource_open Q
  open_target := parameterDomain_open block
  continuousOn_toFun := by
    intro U hU
    exact ((chartMap_smooth_at Q U.val hU).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_blockChartInverse Q).continuousOn

@[simp] theorem blockPartialChart_source (Q : BlockU block) :
    (blockPartialChart Q).source = chartSource Q := rfl

@[simp] theorem blockPartialChart_target (Q : BlockU block) :
    (blockPartialChart Q).target = parameterDomain block := rfl

end GS.UnitaryManifold
