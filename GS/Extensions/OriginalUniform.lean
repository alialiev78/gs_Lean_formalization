module

public import GS.Extensions.OriginalFibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Uniform small-domain conditions for the original fibre argument

Scalar sign/angle assumptions are proved uniformly
on K_eta from continuity. The one analytic input that remains is an open
neighbourhood V of zero on which the actual originalPsi is injective.
No neighbourhood COVERAGE of the whole GS family is asserted by this module.
-/

noncomputable section
open Matrix
namespace GS.Extensions

-- Use the coordinatewise maximum norm only in this module.
attribute [local instance] Matrix.normedAddCommGroup

/-- The default product norm is BOUNDED BY a Frobenius radius; it is not
identified with the Frobenius norm. -/
 theorem matrix_norm_le_of_frobSq_le {q : ℕ} {A : Mat q} {η : ℝ}
    (hη : 0≤η) (h : frobSq A≤η^2) : ‖A‖≤η := by
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro j
  simpa only [Real.norm_eq_abs,abs_of_nonneg hη] using abs_entry_le_of_frobSq_le h i j

 theorem originalPsi_positive_domain_open {q : ℕ} (Q₀ : Mat q) :
    IsOpen {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j} := by
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const (by
    have hc := continuous_originalPsi Q₀
    fun_prop)

 theorem exists_uniform_normalized_original {q : ℕ} (Q₀ : Mat q)
    (hQ : ∀ i j, Q₀ i j≠0) (V : Set (Mat q))
    (hV : IsOpen V) (h₀ : (0:Mat q)∈V) :
    ∃ η : ℝ, 0<η ∧ ∀ p ∈ originalK q η, NormalizedOriginal Q₀ V p := by
  let W := V ∩ {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j}
  have hW : IsOpen W := hV.inter (originalPsi_positive_domain_open Q₀)
  have hW₀ : (0:Mat q)∈W := by
    refine ⟨h₀,?_⟩
    intro i j
    rw [originalPsi_zero]
    exact mul_self_pos.mpr (hQ i j)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW 0 hW₀
  let η := min (δ/4) (Real.pi/8)
  have hη : 0<η := lt_min (by positivity) (by positivity)
  have hηδ : η≤δ/4 := min_le_left _ _
  have hηπ : η≤Real.pi/8 := min_le_right _ _
  refine ⟨η,hη,?_⟩
  rintro ⟨ell,r,c,z,u⟩ hp
  rcases hp with ⟨he,hr,hr₀,hc,hz,hcn,hzn,hu⟩
  have hcnorm := matrix_norm_le_of_frobSq_le hη.le hcn
  have hznorm := matrix_norm_le_of_frobSq_le hη.le hzn
  have hcplus : c+z∈W := by
    apply hball
    change dist (c+z) 0 < δ
    rw [dist_zero_right]
    have hn := norm_add_le c z
    linarith
  have hcminus : c-z∈W := by
    apply hball
    change dist (c-z) 0 < δ
    rw [dist_zero_right]
    have hn := norm_sub_le c z
    linarith
  refine ⟨hu,hr₀,?_,?_,hcplus.1,hcminus.1⟩
  · intro i j
    have ha : |ell i+r j|≤2*η :=
      (abs_add_le _ _).trans (by linarith [he i,hr j])
    have hh := abs_le.mp ha
    constructor <;> linarith [Real.pi_pos]
  · intro i j
    have h₁ := hcplus.2 i j
    have h₂ := hcminus.2 i j
    nlinarith

/-- The full same-fibres statement on some compact K_eta now needs only the
standard local exponential-chart input, not separately supplied signs/angles
or an assumption that f and g have the same fibres. -/
 theorem original_same_fibres_of_open_chart {q : ℕ} (hq : 0<q) (Q₀ : Mat q)
    (hQ : ∀ i j, Q₀ i j≠0) (V : Set (Mat q))
    (hV : IsOpen V) (h₀ : (0:Mat q)∈V) (hinj : Set.InjOn (originalPsi Q₀) V) :
    ∃ η : ℝ, 0<η ∧ ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p=originalF Q₀ p' ↔ originalG p=originalG p' := by
  obtain ⟨η,hη,hn⟩ := exists_uniform_normalized_original Q₀ hQ V hV h₀
  exact ⟨η,hη,fun p hp p' hp' => original_same_fibres_normalized hq Q₀ V hinj p p'
    (hn p hp) (hn p' hp')⟩

end GS.Extensions
