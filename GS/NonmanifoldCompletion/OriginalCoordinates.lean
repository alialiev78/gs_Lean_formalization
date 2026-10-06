module

public import GS.NonmanifoldCompletion.OriginalMembership
public import GS.NonmanifoldCompletion.BaseFibreGauges
public import GS.NonmanifoldCompletion.LocalAngles
public import GS.NonmanifoldCompletion.SmallLogarithms

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Constructing the original ell,r,c,z,u coordinates near a normalized factor tuple

All sign gauges are fixed diagonal orthogonal matrices. Small angles are
obtained from LocalAngles and small logarithms from SmallLogarithms. The
right angle is anchored at coordinate zero exactly as in originalK.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.Nonmanifold
namespace GS.NonmanifoldCompletion

private theorem orthogonal_cancel_left (S : Mat 2) (hS : Orthogonal S) (X : Mat 2) :
    S*(Sᵀ*X)=X := by rw [← Matrix.mul_assoc,hS.2,Matrix.one_mul]

private theorem involution_cancel_left (D : Mat 2) (hD : D*D=1) (X : Mat 2) :
    D*(D*X)=X := by rw [← Matrix.mul_assoc,hD,Matrix.one_mul]

/-- Conjugating the fixed reflection gives T(u) for an actual unit vector u. -/
theorem conjugate_reflection_coordinates (C : Mat 2) (hC : Orthogonal C) :
    ∃ u : CircleVector, OnCircle u ∧
      ∀ a b : ℝ, middleBlock a b u = Cᵀ * diagTwo a b * C := by
  let F := diagTwo 1 (-1)
  have hF : Orthogonal F := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [F,diagTwo,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,Matrix.one_apply]
  let K := Cᵀ*F*C
  have hK : Orthogonal K := (hC.transpose.mul hF).mul hC
  have hs : Kᵀ=K := by
    dsimp [K]
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
    have hf : Fᵀ=F := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hf,Matrix.mul_assoc]
  have hr0 := congrFun (congrFun hC.2 0) 0
  have hr1 := congrFun (congrFun hC.2 1) 1
  norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,Matrix.one_apply] at hr0 hr1
  have htrace : K 1 1 = -K 0 0 := by
    dsimp [K,F]
    simp [diagTwo,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
    nlinarith [hr0,hr1]
  let u : CircleVector := ![K 0 0,K 0 1]
  have he : T u = K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T,u,htrace]
    exact (congrFun (congrFun hs 0) 1).symm
  have hu : OnCircle u := by
    have hh := congrFun (congrFun hK.2 0) 0
    simpa [OnCircle,u,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,
      Matrix.one_apply,pow_two] using hh
  refine ⟨u,hu,?_⟩
  intro a b
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hC.1]
  change ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • T u =
    ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • K
  rw [he]

/-- Anchoring the right angle changes the common reflection coordinate only. -/
theorem anchored_block_formula (S : Mat 2) (α β β₀ a b : ℝ) (u : CircleVector)
    (hu : middleBlock a b u =
      (S*rotation β₀)ᵀ * diagTwo a b * (S*rotation β₀)) :
    rotation (α+β₀)*middleBlock a b u*rotation (β-β₀) =
      rotation α*Sᵀ*diagTwo a b*S*rotation β := by
  rw [hu,rotation_add,Matrix.transpose_mul]
  have htail : rotation β₀*rotation (β-β₀)=rotation β := by
    rw [← rotation_add]
    congr 1
    ring
  simp only [Matrix.mul_assoc,
    orthogonal_cancel_left (rotation β₀) (rotation_orthogonal β₀),htail]

/-- Diagonal sign gauges do not change the output block. -/
theorem gauged_block_formula (U V D E S : Mat 2)
    (hD : DiagonalTwo D ∧ Orthogonal D) (hE : DiagonalTwo E ∧ Orthogonal E)
    (hS : Orthogonal S) (a b : ℝ) :
    (U*D*S)*Sᵀ*diagTwo (D 0 0*a*E 0 0) (D 1 1*b*E 1 1)*S*(Sᵀ*E*V) =
      U*diagTwo a b*V := by
  rw [← diagonal_gauge_middle D E hD.1 hE.1]
  simp only [Matrix.mul_assoc,orthogonal_cancel_left S hS,
    involution_cancel_left D (diagonalTwo_involution hD.1 hD.2),
    involution_cancel_left E (diagonalTwo_involution hE.1 hE.2)]

/-- Exact change from two small skew logarithms to c,z; all Frobenius bounds
refer to the full matrices, not unweighted upper-triangle coordinates. -/
theorem symmetric_log_coordinates {q : ℕ} (H K : Mat q) (η : ℝ)
    (hH : IsSkew H) (hK : IsSkew K) (hHn : frobSq H < η^2) (hKn : frobSq K < η^2) :
    ∃ c z : Mat q, IsSkew c ∧ IsSkew z ∧
      frobSq c < η^2 ∧ frobSq z < η^2 ∧ c+z=H ∧ c-z=K := by
  let c := (1/2 : ℝ) • (H+K)
  let z := (1/2 : ℝ) • (H-K)
  have hc : IsSkew c := by
    apply isSkew_smul
    change (H+K)ᵀ = -(H+K)
    rw [Matrix.transpose_add,hH,hK]
    abel
  have hz : IsSkew z := by
    apply isSkew_smul
    change (H-K)ᵀ = -(H-K)
    rw [Matrix.transpose_sub,hH,hK]
    abel
  have hsum : frobSq c+frobSq z=(frobSq H+frobSq K)/2 := by
    have hscale (A : Mat q) :
        frobSq ((1/2 : ℝ) • A) = (1/2 : ℝ)^2 * frobSq A := by
      unfold frobSq
      rw [frobInner_smul_left,frobInner_comm A ((1/2 : ℝ) • A),frobInner_smul_left]
      ring
    dsimp [c,z]
    rw [hscale,hscale,frobSq_add,frobSq_sub]
    ring
  refine ⟨c,z,hc,hz,?_,?_,?_,?_⟩
  · linarith [frobSq_nonneg z]
  · linarith [frobSq_nonneg c]
  · ext i j; simp [c,z]; ring
  · ext i j; simp [c,z]; ring

/-- Local normal-form reconstruction with explicitly stated smallness inputs.
The caller below constructs these inputs on an OPEN neighbourhood of each full
fibre representative; no coverage conclusion is assumed here. -/
theorem original_coordinates_of_gauged_near {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (η : ℝ) (hη : 0<η)
    (L : Set (Mat q))
    (hlog : ∀ A ∈ L, Orthogonal A → ∃ H : Mat q,
      IsSkew H ∧ frobSq H < η^2 ∧ originalPsi Q₀ H=A)
    (S : Mat 2) (D E : Fin q → Mat 2) (hS : Orthogonal S)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (U V : Fin q → Mat 2) (A B : Mat q)
    (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hA : Orthogonal A) (hB : Orthogonal B)
    (hUl : ∀ i, U i*D i*S ∈ rotationChartDomain (η/4))
    (hVr : ∀ j, Sᵀ*E j*V j ∈ rotationChartDomain (η/4))
    (hAL : gaugeMiddle D E 0 A ∈ L) (hBL : gaugeMiddle D E 1 B ∈ L) :
    ∃ p ∈ originalK q η, originalF Q₀ p =
      flattenBlocks (blockMatrix U*centralPair A B*blockMatrix V) := by
  let i₀ : Fin q := ⟨0,hq⟩
  let α : Fin q → ℝ := fun i => localRotationAngle (U i*D i*S)
  let β : Fin q → ℝ := fun j => localRotationAngle (Sᵀ*E j*V j)
  have hα (i : Fin q) : rotation (α i)=U i*D i*S :=
    rotation_localRotationAngle _ (((hU i).mul (hD i).2).mul hS) (hUl i).1 (hUl i).2.1
  have hβ (j : Fin q) : rotation (β j)=Sᵀ*E j*V j :=
    rotation_localRotationAngle _ ((hS.transpose.mul (hE j).2).mul (hV j)) (hVr j).1 (hVr j).2.1
  obtain ⟨H,hH,hHn,hHA⟩ := hlog _ hAL (gaugeMiddle_orthogonal D E hD hE 0 A hA)
  obtain ⟨K,hK,hKn,hKB⟩ := hlog _ hBL (gaugeMiddle_orthogonal D E hD hE 1 B hB)
  obtain ⟨c,z,hc,hz,hcn,hzn,hplus,hminus⟩ := symmetric_log_coordinates H K η hH hK hHn hKn
  obtain ⟨u,hu,hconj⟩ := conjugate_reflection_coordinates (S*rotation (β i₀))
    (hS.mul (rotation_orthogonal (β i₀)))
  let ell : Fin q → ℝ := fun i => α i+β i₀
  let r : Fin q → ℝ := fun j => β j-β i₀
  have hell (i : Fin q) : |ell i| ≤ η := by
    have h1 : |α i| < η/4 := (hUl i).2.2
    have h2 : |β i₀| < η/4 := (hVr i₀).2.2
    dsimp [ell]
    linarith [abs_add_le (α i) (β i₀)]
  have hr (j : Fin q) : |r j| ≤ η := by
    have h1 : |β j| < η/4 := (hVr j).2.2
    have h2 : |β i₀| < η/4 := (hVr i₀).2.2
    dsimp [r]
    linarith [abs_sub (β j) (β i₀)]
  have hr0 (j : Fin q) (hj : j.val=0) : r j=0 := by
    have he : j=i₀ := Fin.ext hj
    subst j
    simp [r]
  refine ⟨(ell,r,c,z,u),⟨hell,hr,hr0,hc,hz,hcn.le,hzn.le,hu⟩,?_⟩
  ext i j
  let x : Fin q × Fin 2 := finProdFinEquiv.symm i
  let y : Fin q × Fin 2 := finProdFinEquiv.symm j
  change (rotation (ell x.1)*middleBlock
    (originalPsi Q₀ (c+z) x.1 y.1) (originalPsi Q₀ (c-z) x.1 y.1) u*
    rotation (r y.1)) x.2 y.2 =
    (blockMatrix U*centralPair A B*blockMatrix V) x y
  rw [small_block_sandwich,hplus,hminus,hHA,hKB]
  have he := anchored_block_formula S (α x.1) (β y.1) (β i₀)
    (gaugeMiddle D E 0 A x.1 y.1) (gaugeMiddle D E 1 B x.1 y.1) u (hconj _ _)
  change _ = (U x.1*diagTwo (A x.1 y.1) (B x.1 y.1)*V y.1) x.2 y.2
  rw [show ell x.1=α x.1+β i₀ from rfl,show r y.1=β y.1-β i₀ from rfl,
    he,hα,hβ,gaugeMiddle_apply,gaugeMiddle_apply,
    gauged_block_formula _ _ _ _ S (hD x.1) (hE y.1) hS]

end GS.NonmanifoldCompletion
