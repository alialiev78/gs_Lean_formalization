module

public import GS.SpecialUnitarySharing.OrbitAtlas
public import GS.OverlapGeometry.ManifoldSmoothMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Local smooth sections of the shared orbit map

Each translated slice yields an actual local choice of shared factors.  The
choice is smooth on its stated open neighbourhood and reconstructs every point
there.  No global section and no unique factorization are asserted.  In
particular, ambient-smooth orbit curves now admit local smooth factor lifts.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Set Filter
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
open GS.SpecialUnitarySharing.Orbit
variable {n : ℕ} (right left : Pattern n) (P : CMat n)

/-- Total extension of a local section; its right-inverse identity is asserted
only on the open source of the translated slice. -/
def localFactors (g : SpecialFactors right left) (A : CMat n) : SpecialFactors right left :=
  factorLift g ((translatedOrbitSlice right left P g).coordinates A).val

theorem localFactors_orbit (g : SpecialFactors right left) (A : CMat n) :
    orbitMapToOrbit right left P (localFactors right left P g A) =
      (translatedOrbitSlice right left P g).parametrization
        ((translatedOrbitSlice right left P g).coordinates A) := by
  apply Subtype.ext
  change orbitParam g P ((translatedOrbitSlice right left P g).coordinates A).val =
    g • orbitParam (1 : SpecialFactors right left) P
      ((translatedOrbitSlice right left P g).coordinates A).val
  exact orbitParam_eq_translate g P _

/-- Every nearby matrix in the full shared orbit is reconstructed. -/
theorem localFactors_right_inverse (g : SpecialFactors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    orbitMapToOrbit right left P (localFactors right left P g X.val) = X := by
  rw [localFactors_orbit]
  exact (translatedOrbitSlice right left P g).left_inverse X hX

theorem localFactors_centre (g : SpecialFactors right left) :
    localFactors right left P g (g • P) = g := by
  have hc := translatedOrbitSlice_centre_coordinates right left P g
  change (translatedOrbitSlice right left P g).coordinates (g • P) = 0 at hc
  unfold localFactors
  rw [hc]
  exact factorLift_zero g

theorem localFactors_left_matrix_smooth_at (g : SpecialFactors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : CMat n => SpecialFactor.matrix (localFactors right left P g A).1) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hl := contDiffAt_fst.comp X.val hv
  exact (reconstruct_matrix_smooth g.1).contDiffAt.comp X.val hl

theorem localFactors_right_matrix_smooth_at (g : SpecialFactors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : CMat n => SpecialFactor.matrix (localFactors right left P g A).2) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hr := contDiffAt_snd.comp X.val hv
  exact (reconstruct_matrix_smooth g.2).contDiffAt.comp X.val hr

/-- Smoothness into the previously constructed factor manifold, not just a
continuity statement about a quotient. -/
theorem localFactors_left_contMDiffAt (g : SpecialFactors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContMDiffAt (𝓘(ℝ, CMat n)) (𝓘(ℝ, Generator left)) ⊤
      (fun A : CMat n => (localFactors right left P g A).1) X.val :=
  contMDiffAt_factor_of_matrix
    ((contMDiffAt_iff_contDiffAt).mpr (localFactors_left_matrix_smooth_at right left P g X hX))

theorem localFactors_right_contMDiffAt (g : SpecialFactors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContMDiffAt (𝓘(ℝ, CMat n)) (𝓘(ℝ, Generator right)) ⊤
      (fun A : CMat n => (localFactors right left P g A).2) X.val :=
  contMDiffAt_factor_of_matrix
    ((contMDiffAt_iff_contDiffAt).mpr (localFactors_right_matrix_smooth_at right left P g X hX))

/-- A local section exists at every point, with an open domain in the original
orbit topology.  The supplied factor maps always satisfy all block ties. -/
theorem exists_local_smooth_factor_section (X : MatrixOrbit right left P) :
    ∃ U : Set (MatrixOrbit right left P), IsOpen U ∧ X ∈ U ∧
      ∃ s : CMat n → SpecialFactors right left,
        (∀ Y ∈ U, orbitMapToOrbit right left P (s Y.val) = Y) ∧
        (∀ Y ∈ U, ContMDiffAt (𝓘(ℝ, CMat n)) (𝓘(ℝ, Generator left)) ⊤
          (fun A : CMat n => (s A).1) Y.val) ∧
        (∀ Y ∈ U, ContMDiffAt (𝓘(ℝ, CMat n)) (𝓘(ℝ, Generator right)) ⊤
          (fun A : CMat n => (s A).2) Y.val) := by
  let g := preferredFactor P X
  refine ⟨(translatedOrbitSlice right left P g).source,
    (translatedOrbitSlice right left P g).open_source, ?_,
    localFactors right left P g, localFactors_right_inverse right left P g,
    localFactors_left_contMDiffAt right left P g,
    localFactors_right_contMDiffAt right left P g⟩
  simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g

/-- Every ambient-smooth orbit curve has genuine local smooth shared factors.
The right-hand matrix is conjugate-transposed to match the original product2 convention.
No differentiable factor-lifting hypothesis is used. -/
theorem exists_local_smooth_factor_curve (c : ℝ → MatrixOrbit right left P) (t₀ : ℝ)
    (hc : ContDiffAt ℝ ⊤ (fun t => (c t).val) t₀) :
    ∃ L R : ℝ → CMat n,
      (∀ t, SpecialUnitaryFactor left (L t)) ∧
      (∀ t, SpecialUnitaryFactor right (R t)) ∧
      ContDiffAt ℝ ⊤ L t₀ ∧ ContDiffAt ℝ ⊤ R t₀ ∧
      ∀ᶠ t in 𝓝 t₀, product2 (L t) P (R t) = (c t).val := by
  let g := preferredFactor P (c t₀)
  have h₀ : c t₀ ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  let L : ℝ → CMat n := fun t => SpecialFactor.matrix (localFactors right left P g (c t).val).1
  let R : ℝ → CMat n := fun t => (SpecialFactor.matrix (localFactors right left P g (c t).val).2)ᴴ
  refine ⟨L, R, (fun t => SpecialFactor.matrix_special _),
    (fun t => special_factor_conjTranspose _ (SpecialFactor.matrix_special _)),
    (localFactors_left_matrix_smooth_at right left P g (c t₀) h₀).comp t₀ hc,
    smooth_conjTranspose_at ((localFactors_right_matrix_smooth_at right left P g (c t₀) h₀).comp t₀ hc), ?_⟩
  have hc' : ContinuousAt c t₀ := tendsto_subtype_rng.mpr hc.continuousAt
  have hnear : ∀ᶠ t in 𝓝 t₀, c t ∈ (translatedOrbitSlice right left P g).source :=
    hc'.eventually ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hnear] with t ht
  exact congrArg Subtype.val (localFactors_right_inverse right left P g (c t) ht)

/-- The section also lifts curves that are only differentiable at the given
parameter. In particular, differentiable factor lifting is a conclusion, not
an extra premise of the tangent-image result. -/
theorem exists_local_differentiable_factor_curve (c : ℝ → MatrixOrbit right left P)
    (t₀ : ℝ) (hc : DifferentiableAt ℝ (fun t => (c t).val) t₀) :
    ∃ L R : ℝ → CMat n,
      (∀ t, SpecialUnitaryFactor left (L t)) ∧
      (∀ t, SpecialUnitaryFactor right (R t)) ∧
      DifferentiableAt ℝ L t₀ ∧ DifferentiableAt ℝ R t₀ ∧
      ∀ᶠ t in 𝓝 t₀, product2 (L t) P (R t) = (c t).val := by
  let g := preferredFactor P (c t₀)
  have h₀ : c t₀ ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  let L : ℝ → CMat n := fun t => SpecialFactor.matrix (localFactors right left P g (c t).val).1
  let R : ℝ → CMat n := fun t => (SpecialFactor.matrix (localFactors right left P g (c t).val).2)ᴴ
  have hL := (localFactors_left_matrix_smooth_at right left P g (c t₀) h₀).differentiableAt (by simp)
  have hR := (smooth_conjTranspose_at
    (localFactors_right_matrix_smooth_at right left P g (c t₀) h₀)).differentiableAt (by simp)
  refine ⟨L, R, (fun t => SpecialFactor.matrix_special _),
    (fun t => special_factor_conjTranspose _ (SpecialFactor.matrix_special _)),
    hL.comp t₀ hc, hR.comp t₀ hc, ?_⟩
  have hc' : ContinuousAt c t₀ := tendsto_subtype_rng.mpr hc.continuousAt
  have hnear : ∀ᶠ t in 𝓝 t₀, c t ∈ (translatedOrbitSlice right left P g).source :=
    hc'.eventually ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hnear] with t ht
  exact congrArg Subtype.val (localFactors_right_inverse right left P g (c t) ht)

end GS.SpecialUnitarySharing
