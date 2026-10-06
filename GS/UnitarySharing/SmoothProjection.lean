module

public import GS.UnitarySharing.LocalSections
public import GS.UnitarySharing.TangentBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Joint smoothness of the exact shared tangent projector

On a local smooth factor section the projector is conjugate to the fixed
Frobenius projector at P.  Equivariance makes these formulas agree.  This
proves smoothness on the whole actual shared orbit without a global smooth
factor choice, an entrywise overlap mask, or a variable-rank pseudoinverse
assumption.  The carrier P is arbitrary.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set Filter
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance smoothProjectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance smoothProjectionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance smoothProjectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Matrix form of equivariance with arbitrary shared unitary factors. -/
theorem pointProjection_factor_formula (g : Factors right left) (Z : CMat n) :
    pointProjection right left (g • P) Z =
      Factor.matrix g.1 * pointProjection right left P
        ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2) * (Factor.matrix g.2)ᴴ := by
  have h := pointProjection_equivariant g P (g⁻¹ • Z)
  rw [smul_inv_smul] at h
  have hi : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_conjTranspose]
  simpa only [hi, action_apply] using h

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
ambient vector.  The topology and tangent space are those of the new atlas. -/
theorem pointProjection_contMDiff :
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

end GS.UnitarySharing
