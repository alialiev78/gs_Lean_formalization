module

public import GS.ManifoldCompletion.OrbitSmooth
public import GS.CayleyCharts.Differential
public import GS.Extensions.GeodesicNormal

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Coordinate differential of the orbit inclusion

We differentiate the actual Cayley formula. Its derivative is not defined by
fiat. At the centre, the derivative of cayley is -2 times the identity; the
right transpose changes that sign. In the no-overlap case the Frobenius
identity gives an injective differential. The exact range equals the checked
TwoFactorDirection predicate.

This is a coordinate fderiv theorem. The mfderiv/TangentSpace bridge is in
TangentBridge.lean. No IsImmersion predicate is redefined here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- Obtain the derivative from the identity c(A)(1+A)=1-A, rather than using
an unverified formula for differentiation of matrix inverse. -/
theorem chartInv_line_hasDerivAt_zero (Q : BlockO block) (v : Model block) :
    HasDerivAt (fun t : ℝ => chartInv Q (t • v)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  let V := fderiv ℝ (chartInv Q) 0 v
  have hd : HasDerivAt (fun t : ℝ => chartInv Q (t • v)) V 0 := by
    have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hi.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • v.val) v.val 0 := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hm : HasDerivAt (fun t : ℝ => (1 : Mat n) - t • v.val) (-v.val) 0 := by
    simpa only [Pi.sub_def, id_eq, zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hleft := hasDerivAt_matrix_mul hd hp
  have hright := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) hm
  have hid : (fun t : ℝ => chartInv Q (t • v) * (1 + t • v.val)) =
      (fun t : ℝ => Q.val * (1 - t • v.val)) := by
    funext t
    change Q.val * cayley ((t • v).val) * (1 + (t • v).val) = _
    rw [Matrix.mul_assoc, cayley_mul _ (admissible_model (t • v))]
    rfl
  rw [hid] at hleft
  have hv : V + Q.val * v.val = -(Q.val * v.val) := by
    simpa only [zero_smul, add_zero, sub_zero, chartInv_zero, Matrix.mul_one,
      Matrix.zero_mul, zero_add, Matrix.mul_neg] using hleft.unique hright
  have he : V = (-2 : ℝ) • (Q.val * v.val) := by
    ext i j
    have hh := congrFun (congrFun hv i) j
    change V i j + (Q.val * v.val) i j = -(Q.val * v.val) i j at hh
    change V i j = (-2 : ℝ) * (Q.val * v.val) i j
    linarith
  rwa [he] at hd

/-- Exact Frechet derivative of the actual matrix-valued orbit chart at its
centre. The coefficients reflect the chosen Cayley convention. -/
theorem orbitParam_fderiv_zero (g : FactorGroup block₁ block₂) (P : Mat n)
    (v : PairModel block₁ block₂) :
    fderiv ℝ (orbitParam g P) 0 v =
      tangentParam g.1.val P g.2.valᵀ ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := chartInv_line_hasDerivAt_zero g.1 v.1
  have hdR := hasDerivAt_matrix_transpose (chartInv_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (g.2.val * v.2.val))ᵀ =
      (2 : ℝ) • (v.2.val * g.2.valᵀ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, v.2.property.2,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := hasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (tangentParam g.1.val P g.2.valᵀ ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, product2, zero_smul, Prod.smul_fst, Prod.smul_snd,
      chartInv_zero, tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- Translate the factor-side injectivity condition into the original
left-coordinate disjoint-support condition. -/
theorem noOverlap_offDiagonalDisjoint (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm) := by
  intro i j h₂ h₁
  apply σ.symm.injective
  apply hn
  apply Prod.ext
  · exact h₁
  · simpa only [Equiv.apply_symm_apply] using h₂

/-- This norm identity is for the actual fderiv, not merely a formal generator. -/
theorem orbitParam_fderiv_zero_frobSq (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (v : PairModel block₁ block₂) :
    frobSq (fderiv ℝ (orbitParam g (permMatrix σ)) 0 v) =
      frobSq ((-2 : ℝ) • v.1.val) + frobSq ((2 : ℝ) • v.2.val) := by
  rw [orbitParam_fderiv_zero]
  apply tangentParam_frobSq _ _ _ _ _ g.1.property.2
    (perm_orthogonal σ) g.2.property.2.transpose
  have hC : Supported block₂ ((-2 : ℝ) • v.1.val) := Supported.smul (-2) v.1.property.1
  have hΩ : Supported block₁ ((2 : ℝ) • v.2.val) := Supported.smul 2 v.2.property.1
  have hsΩ : IsSkew ((2 : ℝ) • v.2.val) := by
    change (((2 : ℝ) • v.2.val)ᵀ) = -((2 : ℝ) • v.2.val)
    rw [Matrix.transpose_smul, v.2.property.2, smul_neg]
  exact frobInner_disjoint_supported_skew (noOverlap_offDiagonalDisjoint σ hn)
    _ _ hC ((supported_perm_conjugate_iff block₁ σ _).mpr hΩ)
    (conjugate_skew (permMatrix σ) _ hsΩ)

theorem orbitParam_fderiv_zero_kernel (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (v : PairModel block₁ block₂)
    (hv : fderiv ℝ (orbitParam g (permMatrix σ)) 0 v = 0) : v = 0 := by
  have he := orbitParam_fderiv_zero_frobSq σ hn g v
  have hzero : frobSq (0 : Mat n) = 0 := by simp [frobSq]
  rw [hv, hzero] at he
  have ha : frobSq ((-2 : ℝ) • v.1.val) = 0 := by
    have := frobSq_nonneg ((2 : ℝ) • v.2.val)
    have := frobSq_nonneg ((-2 : ℝ) • v.1.val)
    linarith
  have hb : frobSq ((2 : ℝ) • v.2.val) = 0 := by
    linarith
  have hA := (frobSq_eq_zero_iff _).mp ha
  have hB := (frobSq_eq_zero_iff _).mp hb
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    have hh := congrFun (congrFun hA i) j
    change (-2 : ℝ) * v.1.val i j = 0 at hh
    change v.1.val i j = 0
    linarith
  · apply Subtype.ext
    ext i j
    have hh := congrFun (congrFun hB i) j
    change (2 : ℝ) * v.2.val i j = 0 at hh
    change v.2.val i j = 0
    linarith

/-- Every preferred orbit chart is immersive at its centre. -/
theorem orbitParam_fderiv_zero_injective (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂) :
    Function.Injective (fderiv ℝ (orbitParam g (permMatrix σ)) 0) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply orbitParam_fderiv_zero_kernel σ hn g (v - w)
  rw [map_sub, hvw, sub_self]

/-- The image of the actual coordinate differential is exactly the space used
by the checked projection formula. This also holds before using no-overlap. -/
theorem orbitParam_fderiv_zero_range (g : FactorGroup block₁ block₂) (P X : Mat n) :
    (∃ v : PairModel block₁ block₂, fderiv ℝ (orbitParam g P) 0 v = X) ↔
      TwoFactorDirection block₁ block₂ g.1.val P g.2.valᵀ X := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [orbitParam_fderiv_zero]
    let hc : Model block₂ := (-2 : ℝ) • v.1
    let hΩ : Model block₁ := (2 : ℝ) • v.2
    exact ⟨hc.val, hΩ.val, hc.property.1, hc.property.2,
      hΩ.property.1, hΩ.property.2, rfl⟩
  · rintro ⟨C, Ω, hsC, hC, hsΩ, hΩ, rfl⟩
    let c : Model block₂ := ⟨C, hsC, hC⟩
    let w : Model block₁ := ⟨Ω, hsΩ, hΩ⟩
    refine ⟨((-1 / 2 : ℝ) • c, (1 / 2 : ℝ) • w), ?_⟩
    rw [orbitParam_fderiv_zero]
    change tangentParam g.1.val P g.2.valᵀ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul]

end GS.ManifoldCompletion
