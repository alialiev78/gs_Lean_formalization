module

public import GS.UnitarySharing.LocalSections
public import GS.SpecialUnitarySharing.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth SU generator-range projection on the ambient U orbit

On a local smooth factor section the projector is conjugate to the fixed
Frobenius projector at P.  Equivariance makes these formulas agree.  This
proves smoothness on the whole surrounding U-sharing orbit without a global smooth
factor choice, an entrywise overlap mask, or a variable-rank pseudoinverse
assumption.  The carrier P is arbitrary.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set Filter
open scoped Topology Manifold
open GS.UnitarySharing (Factor Factors MatrixOrbit HorizontalModel sharedOrbitChartedSpace sharedOrbitIsManifold localFactors translatedOrbitSlice preferredFactor preferredFactor_spec translatedOrbitSlice_centre_mem localFactors_right_inverse localFactors_left_matrix_smooth_at localFactors_right_matrix_smooth_at sharedOrbit_val_contMDiff action_apply)
namespace GS.SpecialUnitarySharing
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Matrix form of equivariance with arbitrary shared unitary factors. -/
theorem pointProjection_factor_formula (g : Factors right left) (Z : CMat n) :
    pointProjection right left (g • P) Z =
      Factor.matrix g.1 * pointProjection right left P
        ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2) * (Factor.matrix g.2)ᴴ := by
  have h := pointProjection_equivariant g P (g⁻¹ • Z)
  have hi : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_conjTranspose]
  simpa only [smul_inv_smul, hi, action_apply] using h

/-- An ambient smooth extension valid near the source of a fixed slice. -/
def localProjectionFormula (g : Factors right left) (p : CMat n × CMat n) : CMat n :=
  let q := localFactors right left P g p.1
  Factor.matrix q.1 * pointProjection right left P
    ((Factor.matrix q.1)ᴴ * p.2 * Factor.matrix q.2) * (Factor.matrix q.2)ᴴ

theorem localProjectionFormula_eq (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : CMat n) :
    localProjectionFormula right left P g (X.val, Z) =
      pointProjection right left X.val Z := by
  have he : localFactors right left P g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  have h := pointProjection_factor_formula right left P
    (localFactors right left P g X.val) Z
  rw [he] at h
  exact h.symm

theorem localProjectionFormula_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : CMat n) :
    ContDiffAt ℝ ⊤ (localProjectionFormula right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hcore := smooth_mul_at (smooth_mul_at (smooth_conjTranspose_at hL) contDiffAt_snd) hR
  have hproj := (pointProjection right left P).contDiff.contDiffAt.comp (X.val, Z) hcore
  exact smooth_mul_at (smooth_mul_at hL hproj) (smooth_conjTranspose_at hR)

/-- The exact point-only projector is smooth jointly in the orbit point and
ambient vector.  The domain is explicitly the ambient U orbit, not a newly asserted SU atlas. -/
theorem pointProjection_contMDiff_on_unitary_orbit :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : MatrixOrbit right left P × CMat n =>
        pointProjection right left p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n × CMat n)) ⊤ (fun q : MatrixOrbit right left P × CMat n =>
        (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hs := ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × CMat n => (q.1.val, q.2))
    (g := localProjectionFormula right left P g)
    (localProjectionFormula_smooth_at right left P g p.1 h₀ p.2) (hinc p)
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ q : MatrixOrbit right left P × CMat n in 𝓝 p,
      q.1 ∈ (translatedOrbitSlice right left P g).source :=
    (continuous_fst.continuousAt).eventually
      ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hn] with q hq
  exact (localProjectionFormula_eq right left P g q.1 hq q.2).symm

end GS.SpecialUnitarySharing
