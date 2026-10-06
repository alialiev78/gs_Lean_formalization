module

public import GS.CayleyCharts.BlockCharts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth transitions and coordinate expressions of group operations

All domains are explicit determinant-nonvanishing conditions. The transition
formulas are linked to the actual chart inverse identities. Smoothness of a
formal ambient expression is not substituted for the inverse identity.
No `LieGroup` or `IsManifold` instance is postulated here; `Atlas.lean`
constructs the manifold instance from these checked charts.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction Filter
open scoped Topology
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

def transition (Q V : BlockO block) (x : Model block) : Model block :=
  chartMap V (chartInv Q x)

def transitionDomain (Q V : BlockO block) : Set (Model block) :=
  {x | x ∈ parameterDomain block ∧ admissible (V.valᵀ * chartInv Q x)}

theorem transitionDomain_open (Q V : BlockO block) : IsOpen (transitionDomain Q V) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hfirst : parameterDomain block ∈ 𝓝 x :=
    (parameterDomain_open block).mem_nhds hx.1
  have hsecond : {y | admissible (V.valᵀ * chartInv Q y)} ∈ 𝓝 x :=
    (smooth_mul_at contDiffAt_const (chartInv_smooth_at Q x hx.1)).continuousAt.eventually
      (admissible_open.mem_nhds hx.2)
  exact inter_mem hfirst hsecond

theorem transition_smooth_at (Q V : BlockO block) (x : Model block)
    (hx : x ∈ transitionDomain Q V) : ContDiffAt ℝ ⊤ (transition Q V) x :=
  (chartMap_smooth_at V (chartInv Q x) hx.2).comp x (chartInv_smooth_at Q x hx.1)

theorem transition_smooth_on (Q V : BlockO block) :
    ContDiffOn ℝ ⊤ (transition Q V) (transitionDomain Q V) := by
  intro x hx
  exact (transition_smooth_at Q V x hx).contDiffWithinAt

/-- Compatibility with the actual orthogonal matrix, not just a formal
composition of rational expressions. -/
theorem transition_reconstruct (Q V : BlockO block) (x : Model block)
    (hx : x ∈ transitionDomain Q V) :
    chartInv V (transition Q V x) = chartInv Q x := by
  exact chartInv_chartMap V (reconstructBlock Q ⟨x, hx.1⟩) hx.2

theorem transition_mem_reverse (Q V : BlockO block) (x : Model block)
    (hx : x ∈ transitionDomain Q V) :
    transition Q V x ∈ transitionDomain V Q := by
  refine ⟨chartMap_mem_domain V (reconstructBlock Q ⟨x, hx.1⟩) hx.2, ?_⟩
  change admissible (Q.valᵀ * chartInv V (transition Q V x))
  rw [transition_reconstruct Q V x hx, centered_chartInv]
  exact admissible_cayley x.val hx.1

theorem transition_inverse (Q V : BlockO block) (x : Model block)
    (hx : x ∈ transitionDomain Q V) :
    transition V Q (transition Q V x) = x := by
  change chartMap Q (chartInv V (transition Q V x)) = x
  rw [transition_reconstruct Q V x hx]
  exact chartMap_chartInv Q x hx.1

/-- This identity uses a source-point hypothesis rather than an arbitrary
ambient matrix. -/
theorem transition_on_chart (Q V U : BlockO block)
    (hQ : U ∈ chartSource Q) (hV : U ∈ chartSource V) :
    transition Q V (chartMap Q U.val) = chartMap V U.val := by
  unfold transition
  rw [chartInv_chartMap Q U hQ]

def transitionHomeomorph (Q V : BlockO block) :
    transitionDomain Q V ≃ₜ transitionDomain V Q where
  toFun x := ⟨transition Q V x.val, transition_mem_reverse Q V x.val x.property⟩
  invFun y := ⟨transition V Q y.val, transition_mem_reverse V Q y.val y.property⟩
  left_inv x := Subtype.ext (transition_inverse Q V x.val x.property)
  right_inv y := Subtype.ext (transition_inverse V Q y.val y.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (transition_smooth_at Q V x.val x.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (transition_smooth_at V Q y.val y.property).continuousAt.comp
      continuous_subtype_val.continuousAt

/-- Multiplication written in three possibly different base-point charts. -/
def multiplyCoordinates (Q V W : BlockO block) (xy : Model block × Model block) :
    Model block := chartMap W (chartInv Q xy.1 * chartInv V xy.2)

def multiplicationDomain (Q V W : BlockO block) : Set (Model block × Model block) :=
  {xy | xy.1 ∈ parameterDomain block ∧ xy.2 ∈ parameterDomain block ∧
    admissible (W.valᵀ * (chartInv Q xy.1 * chartInv V xy.2))}

theorem multiplyCoordinates_smooth_at (Q V W : BlockO block)
    (xy : Model block × Model block) (hxy : xy ∈ multiplicationDomain Q V W) :
    ContDiffAt ℝ ⊤ (multiplyCoordinates Q V W) xy := by
  apply (chartMap_smooth_at W _ hxy.2.2).comp xy
  exact smooth_mul_at
    ((chartInv_smooth_at Q xy.1 hxy.1).comp xy contDiffAt_fst)
    ((chartInv_smooth_at V xy.2 hxy.2.1).comp xy contDiffAt_snd)

theorem multiplicationDomain_open (Q V W : BlockO block) :
    IsOpen (multiplicationDomain Q V W) := by
  apply isOpen_iff_mem_nhds.mpr
  intro xy hxy
  have h1 : {t : Model block × Model block | t.1 ∈ parameterDomain block} ∈ 𝓝 xy :=
    continuous_fst.continuousAt.eventually ((parameterDomain_open block).mem_nhds hxy.1)
  have h2 : {t : Model block × Model block | t.2 ∈ parameterDomain block} ∈ 𝓝 xy :=
    continuous_snd.continuousAt.eventually ((parameterDomain_open block).mem_nhds hxy.2.1)
  have h3 : {t : Model block × Model block |
      admissible (W.valᵀ * (chartInv Q t.1 * chartInv V t.2))} ∈ 𝓝 xy :=
    (smooth_mul_at contDiffAt_const (smooth_mul_at
      ((chartInv_smooth_at Q xy.1 hxy.1).comp xy contDiffAt_fst)
      ((chartInv_smooth_at V xy.2 hxy.2.1).comp xy contDiffAt_snd))).continuousAt.eventually
        (admissible_open.mem_nhds hxy.2.2)
  exact inter_mem h1 (inter_mem h2 h3)

theorem multiplyCoordinates_mem_domain (Q V W : BlockO block)
    (xy : Model block × Model block) (hxy : xy ∈ multiplicationDomain Q V W) :
    multiplyCoordinates Q V W xy ∈ parameterDomain block := by
  exact chartMap_mem_domain W
    (reconstructBlock Q ⟨xy.1, hxy.1⟩ * reconstructBlock V ⟨xy.2, hxy.2.1⟩) hxy.2.2

theorem multiplyCoordinates_reconstruct (Q V W : BlockO block)
    (xy : Model block × Model block) (hxy : xy ∈ multiplicationDomain Q V W) :
    chartInv W (multiplyCoordinates Q V W xy) = chartInv Q xy.1 * chartInv V xy.2 := by
  exact chartInv_chartMap W
    (reconstructBlock Q ⟨xy.1, hxy.1⟩ * reconstructBlock V ⟨xy.2, hxy.2.1⟩) hxy.2.2

/-- Matrix transpose is group inverse on BlockO. -/
def inverseCoordinates (Q V : BlockO block) (x : Model block) : Model block :=
  chartMap V (chartInv Q x)ᵀ

def inversionDomain (Q V : BlockO block) : Set (Model block) :=
  {x | x ∈ parameterDomain block ∧ admissible (V.valᵀ * (chartInv Q x)ᵀ)}

theorem inverseCoordinates_smooth_at (Q V : BlockO block) (x : Model block)
    (hx : x ∈ inversionDomain Q V) : ContDiffAt ℝ ⊤ (inverseCoordinates Q V) x :=
  (chartMap_smooth_at V _ hx.2).comp x
    (smooth_transpose_at (chartInv_smooth_at Q x hx.1))

theorem inversionDomain_open (Q V : BlockO block) : IsOpen (inversionDomain Q V) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact inter_mem ((parameterDomain_open block).mem_nhds hx.1)
    ((smooth_mul_at contDiffAt_const
      (smooth_transpose_at (chartInv_smooth_at Q x hx.1))).continuousAt.eventually
        (admissible_open.mem_nhds hx.2))

theorem inverseCoordinates_reconstruct (Q V : BlockO block) (x : Model block)
    (hx : x ∈ inversionDomain Q V) :
    chartInv V (inverseCoordinates Q V x) = (chartInv Q x)ᵀ := by
  exact chartInv_chartMap V (reconstructBlock Q ⟨x, hx.1⟩)⁻¹ hx.2

/-- Every group multiplication is covered by a smooth coordinate expression:
choose the output chart centred at the actual product. -/
theorem multiplication_covers_basepoints (Q V : BlockO block) :
    (0, 0) ∈ multiplicationDomain Q V (Q * V) := by
  refine ⟨zero_mem_parameterDomain block, zero_mem_parameterDomain block, ?_⟩
  simp only [chartInv_zero]
  change admissible ((Q * V).valᵀ * (Q * V).val)
  rw [(Q * V).property.2.1]
  exact admissible_one

theorem inversion_covers_basepoints (Q : BlockO block) :
    (0 : Model block) ∈ inversionDomain Q Q⁻¹ := by
  refine ⟨zero_mem_parameterDomain block, ?_⟩
  simp only [chartInv_zero]
  change admissible ((Q⁻¹).valᵀ * (Q⁻¹).val)
  rw [(Q⁻¹).property.2.1]
  exact admissible_one

end GS.CayleyCharts
