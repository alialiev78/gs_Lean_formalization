module

public import GS.Extensions.TransportedProjection
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smoothness of the actual projection formulas in factor coordinates

All derivatives use the explicit entrywise sup norm, which induces the ordinary
finite-dimensional topology of matrices. Exact Frobenius optimality is proved
separately; no identification of these two norms is used.

These are real-analytic (hence C-infinity) statements on ambient factor-coordinate
spaces: in this mathlib version `ContDiff ℝ ⊤` denotes analytic regularity. Descending
the formulas to an abstract quotient manifold, and constructing the manifold,
are separate obligations, not implicit assumptions in the names below.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem contDiff_matrix_mul {A B : E → Mat n}
    (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro k _
  exact ((contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j))

 theorem contDiff_matrix_transpose {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => (A x)ᵀ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_pi.mp (contDiff_pi.mp hA j) i

 theorem contDiff_skew {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => skew (A x)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact ((contDiff_pi.mp (contDiff_pi.mp hA i) j).sub
    (contDiff_pi.mp (contDiff_pi.mp hA j) i)).div_const 2

 theorem contDiff_mask (p : Fin n → Fin n → Prop) [DecidableRel p]
    {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => mask p (A x)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  by_cases hp : p i j
  · simpa only [mask, if_pos hp] using contDiff_pi.mp (contDiff_pi.mp hA i) j
  · simpa only [mask, if_neg hp] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : E => (0 : ℝ)))

 theorem contDiff_maskedSkew (p : Fin n → Fin n → Prop) [DecidableRel p]
    {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => maskedSkew p (A x)) :=
  contDiff_mask p (contDiff_skew hA)

 theorem contDiff_splitLeft (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => splitLeft p q (A x)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hs := contDiff_pi.mp (contDiff_pi.mp (contDiff_skew hA) i) j
  by_cases hp : p i j <;> by_cases hq : q i j
  · simpa only [splitLeft, if_pos hp, if_pos hq] using hs.div_const 2
  · simpa only [splitLeft, if_pos hp, if_neg hq] using hs
  · simpa only [splitLeft, if_neg hp] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : E => (0 : ℝ)))
  · simpa only [splitLeft, if_neg hp] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : E => (0 : ℝ)))

 theorem contDiff_splitRight (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] {A : E → Mat n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun x => splitRight p q (A x)) :=
  contDiff_splitLeft q p hA

 theorem contDiff_lift {L R X : E → Mat n}
    (hL : ContDiff ℝ ⊤ L) (hR : ContDiff ℝ ⊤ R) (hX : ContDiff ℝ ⊤ X) :
    ContDiff ℝ ⊤ (fun x => lift (L x) (R x) (X x)) :=
  contDiff_matrix_mul (contDiff_matrix_mul hL hX) hR

 theorem contDiff_pull {L R X : E → Mat n}
    (hL : ContDiff ℝ ⊤ L) (hR : ContDiff ℝ ⊤ R) (hX : ContDiff ℝ ⊤ X) :
    ContDiff ℝ ⊤ (fun x => pull (L x) (R x) (X x)) :=
  contDiff_matrix_mul (contDiff_matrix_mul (contDiff_matrix_transpose hL) hX)
    (contDiff_matrix_transpose hR)

 theorem contDiff_transportedProjection (p : Fin n → Fin n → Prop) [DecidableRel p]
    {L R Z : E → Mat n} (hL : ContDiff ℝ ⊤ L)
    (hR : ContDiff ℝ ⊤ R) (hZ : ContDiff ℝ ⊤ Z) :
    ContDiff ℝ ⊤ (fun x => transportedProjection p (L x) (R x) (Z x)) :=
  contDiff_lift hL hR (contDiff_maskedSkew p (contDiff_pull hL hR hZ))

/-- All three arguments vary: smoothness is not restricted to fixed L,R. -/
 theorem transportedProjection_joint_smooth
    (p : Fin n → Fin n → Prop) [DecidableRel p] :
    ContDiff ℝ ⊤ (fun x : Mat n × Mat n × Mat n =>
      transportedProjection p x.1 x.2.1 x.2.2) :=
  contDiff_transportedProjection p contDiff_fst contDiff_snd.fst contDiff_snd.snd

 theorem twoFactor_projection_factorwise_smooth
    (p : Fin n → Fin n → Prop) [DecidableRel p] (P : Mat n) :
    ContDiff ℝ ⊤ (fun x : Mat n × Mat n × Mat n =>
      transportedProjection p x.1 (P*x.2.1) x.2.2) :=
  contDiff_transportedProjection p contDiff_fst
    (contDiff_matrix_mul contDiff_const contDiff_snd.fst) contDiff_snd.snd

 theorem product2_smooth (P : Mat n) :
    ContDiff ℝ ⊤ (fun x : Mat n × Mat n => product2 x.1 P x.2) :=
  contDiff_matrix_mul (contDiff_matrix_mul contDiff_fst contDiff_const) contDiff_snd

 theorem product3_smooth (P₂ P₁ : Mat n) :
    ContDiff ℝ ⊤ (fun x : Mat n × Mat n × Mat n =>
      product3 x.1 P₂ x.2.1 P₁ x.2.2) :=
  contDiff_matrix_mul (contDiff_matrix_mul
    (contDiff_matrix_mul (contDiff_matrix_mul contDiff_fst contDiff_const)
      contDiff_snd.fst) contDiff_const) contDiff_snd.snd

 theorem tangentParam_joint_smooth (P : Mat n) :
    ContDiff ℝ ⊤ (fun x : Mat n × Mat n × Mat n × Mat n =>
      tangentParam x.1 P x.2.1 x.2.2.1 x.2.2.2) := by
  unfold tangentParam
  exact (contDiff_matrix_mul (contDiff_matrix_mul
    (contDiff_matrix_mul contDiff_fst contDiff_snd.snd.fst) contDiff_const) contDiff_snd.fst).add
    (contDiff_matrix_mul (contDiff_matrix_mul
      (contDiff_matrix_mul contDiff_fst contDiff_const) contDiff_snd.snd.snd) contDiff_snd.fst)

/-- A genuine linear map, not a formula merely described as linear. -/
 def maskedSkewLinearMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    Mat n →ₗ[ℝ] Mat n where
  toFun := maskedSkew p
  map_add' := maskedSkew_add p
  map_smul' a A := by
    change maskedSkew p (a • A) = a • maskedSkew p A
    exact maskedSkew_smul p a A

 def maskedSkewCLM (p : Fin n → Fin n → Prop) [DecidableRel p] :
    Mat n →L[ℝ] Mat n where
  toLinearMap := maskedSkewLinearMap p
  cont := (contDiff_maskedSkew p contDiff_id).continuous

/-- Frechet derivative of the fixed supported-skew projection. -/
 theorem hasFDerivAt_maskedSkew (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : Mat n) : HasFDerivAt (maskedSkew p) (maskedSkewCLM p) A :=
  (maskedSkewCLM p).hasFDerivAt

end GS.Extensions
