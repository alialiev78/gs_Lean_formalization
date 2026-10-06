module

public import GS.Nonmanifold.NormalizationEstimates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Small skew logarithms for all orthogonal matrices near Q0

The older ExponentialChart exports only local injectivity. Here both inverse
identities and continuity of the inverse are obtained from the inverse function
theorem. They imply the existence of small skew logarithms for ALL orthogonal
matrices in a genuine open neighbourhood, not just for points of exp's image.

The operator norm is used only inside the inverse-function-theorem proof.
Exported statements use the original matrix topology and the explicit frobSq.

-/
noncomputable section
open Matrix Filter GS GS.Extensions GS.Continuation GS.Nonmanifold
open scoped Topology
namespace GS.NonmanifoldCompletion

/-- A local inverse of the actual matrix exponential, constructed using IFT. -/
theorem exists_continuous_local_matrix_log (q : ℕ) :
    ∃ log : Mat q → Mat q,
      log 1 = 0 ∧ ContinuousAt log 1 ∧
      (∀ᶠ H in 𝓝 (0 : Mat q), log (matrixExp H) = H) ∧
      (∀ᶠ A in 𝓝 (1 : Mat q), matrixExp (log A) = A) := by
  letI : SeminormedRing (Mat q) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat q) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat q → Mat q)
      (ContinuousLinearEquiv.refl ℝ (Mat q) : Mat q →L[ℝ] Mat q) 0 := by
    simpa only [ContinuousLinearMap.one_def, ContinuousLinearEquiv.coe_refl] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat q))
  obtain ⟨g,hleft,hright,hcontinuous⟩ :
      ∃ g : Mat q → Mat q,
        (∀ᶠ H in 𝓝 (0 : Mat q), g (matrixExp H) = H) ∧
        (∀ᶠ A in 𝓝 (1 : Mat q), matrixExp (g A) = A) ∧ ContinuousAt g 1 := by
    exact ⟨_,
      by simpa only [matrixExp_eq_exp] using hd.eventually_left_inverse,
      by simpa [matrixExp_eq_exp] using hd.eventually_right_inverse,
      by simpa using hd.localInverse_continuousAt⟩
  have hzero : g 1 = 0 := by
    simpa only [matrixExp_zero] using hleft.self_of_nhds
  exact ⟨g,hzero,hcontinuous,hleft,hright⟩

/-- An arbitrary prescribed open restriction on the logarithm can be enforced.
Skewness follows from orthogonality of A and local injectivity; it is not assumed.
-/
theorem exists_open_small_skew_log {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    (D : Set (Mat q)) (hD : IsOpen D) (hD0 : (0 : Mat q) ∈ D) :
    ∃ U : Set (Mat q), IsOpen U ∧ Q₀ ∈ U ∧
      ∀ A ∈ U, Orthogonal A →
        ∃ H ∈ D, IsSkew H ∧ originalPsi Q₀ H = A := by
  obtain ⟨g,hg0,hgc,_hleft,hright⟩ := exists_continuous_local_matrix_log q
  obtain ⟨V,hV,hV0,hdetect⟩ := exists_open_exp_skew_detection q
  have hlog : ∀ᶠ A in 𝓝 (1 : Mat q), g A ∈ D ∩ V := by
    have hnh : D ∩ V ∈ 𝓝 (g (1 : Mat q)) := by
      rw [hg0]
      exact (hD.inter hV).mem_nhds ⟨hD0,hV0⟩
    exact hgc.tendsto.eventually hnh
  obtain ⟨U,hsub,hU,h1⟩ := mem_nhds_iff.mp (hright.and hlog)
  let W : Set (Mat q) := (fun A : Mat q => Q₀ᵀ*A) ⁻¹' U
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hQmem : Q₀ ∈ W := by
    change Q₀ᵀ*Q₀ ∈ U
    simpa only [hQ₀.1] using h1
  refine ⟨W,hW,hQmem,?_⟩
  intro A hA ho
  obtain ⟨he,hD',hV'⟩ := hsub hA
  refine ⟨g (Q₀ᵀ*A),hD',?_,?_⟩
  · apply hdetect _ hV'
    rw [he]
    exact hQ₀.transpose.mul ho
  · change Q₀ * matrixExp (g (Q₀ᵀ*A)) = A
    rw [he,← Matrix.mul_assoc,hQ₀.2,Matrix.one_mul]

/-- Uniform small-log existence in the exact Frobenius coordinates of K_eta. -/
theorem exists_open_frob_small_skew_log {q : ℕ} (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (η : ℝ) (hη : 0 < η) :
    ∃ U : Set (Mat q), IsOpen U ∧ Q₀ ∈ U ∧
      ∀ A ∈ U, Orthogonal A →
        ∃ H : Mat q, IsSkew H ∧ frobSq H < η^2 ∧ originalPsi Q₀ H = A := by
  let D : Set (Mat q) := {H | frobSq H < η^2}
  have hD : IsOpen D := isOpen_lt continuous_frobSq continuous_const
  have hD0 : (0 : Mat q) ∈ D := by
    change frobSq (0 : Mat q) < η^2
    simpa [frobSq,frobInner] using sq_pos_of_pos hη
  obtain ⟨U,hU,hbase,hlog⟩ := exists_open_small_skew_log Q₀ hQ₀ D hD hD0
  refine ⟨U,hU,hbase,?_⟩
  intro A hA ho
  obtain ⟨H,hH,hsk,he⟩ := hlog A hA ho
  exact ⟨H,hsk,hH,he⟩

end GS.NonmanifoldCompletion
