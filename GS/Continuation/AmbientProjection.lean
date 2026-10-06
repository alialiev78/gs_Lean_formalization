module

public import GS.Extensions.TwoFactorProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A point-only, globally smooth extension of the m=2 projector

For X = B2 P B1, define
  L_X Z = blockSkew_2 (Z X^T) X,
  R_X Z = X blockSkew_1 (X^T Z),
  Pi_X Z = L_X Z + R_X Z - L_X (R_X Z).

In factor coordinates, L_X and R_X are commuting supported-skew projections.
Thus Pi equals the existing union-mask projector, including overlap. This yields
smoothness in the actual base matrix X, not only smoothness in a chosen pair of
factors. It does NOT establish that the orbit is an embedded manifold, nor does
it assert that Pi_X is a projector for arbitrary nonorthogonal ambient X.

No parameter sharing is imposed. Arbitrary sharing+overlap is NOT covered.
This point-only formula is an auxiliary derived identity, not a quotation from
the manuscript. All original definitions and theorems remain unchanged.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def blockSkew (block : Fin n → ℕ) (A : Mat n) : Mat n :=
  maskedSkew (fun i j => block i = block j) A

theorem skew_conjugation (U A : Mat n) :
    skew (U * A * Uᵀ) = U * skew A * Uᵀ := by
  simp only [skew_eq_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]

/-- Conjugation within a block algebra commutes with its skew projection.
Orthogonality of U is not required for this algebraic identity. -/
theorem blockSkew_conjugation (block : Fin n → ℕ) (U A : Mat n)
    (hU : Supported block U) :
    blockSkew block (U * A * Uᵀ) = U * blockSkew block A * Uᵀ := by
  change blockProjection block (skew (U * A * Uᵀ)) =
    U * blockProjection block (skew A) * Uᵀ
  rw [skew_conjugation, blockProjection_mul_right block (U * skew A) Uᵀ hU.transpose,
    blockProjection_mul_left block U (skew A) hU]

/-- The right support is transported by the same permutation as its matrix. -/
theorem blockSkew_permutation (block : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (A : Mat n) :
    permMatrix σ * blockSkew block ((permMatrix σ)ᵀ * A * permMatrix σ) *
      (permMatrix σ)ᵀ =
        maskedSkew (fun i j => block (σ.symm i) = block (σ.symm j)) A := by
  classical
  ext i j
  rw [perm_conjugate_apply]
  simp [blockSkew, maskedSkew, mask, skew, perm_transpose]

theorem maskedSkew_composition (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (hq : MaskSymmetric q) (A : Mat n) :
    maskedSkew p (maskedSkew q A) = maskedSkew (fun i j => p i j ∧ q i j) A := by
  classical
  have hk : IsSkew (maskedSkew q A) := mask_isSkew hq (isSkew_skew A)
  change mask p (skew (maskedSkew q A)) = _
  rw [skew_of_isSkew hk]
  ext i j
  by_cases hpij : p i j <;> by_cases hqij : q i j <;>
    simp [maskedSkew, mask, hpij, hqij]

/-- Inclusion-exclusion for two commuting coordinate-skew projectors. -/
theorem maskedSkew_union (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (hq : MaskSymmetric q) (A : Mat n) :
    maskedSkew (fun i j => p i j ∨ q i j) A =
      maskedSkew p A + maskedSkew q A - maskedSkew p (maskedSkew q A) := by
  classical
  rw [maskedSkew_composition p q hq]
  ext i j
  by_cases hpij : p i j <;> by_cases hqij : q i j <;>
    simp [maskedSkew, mask, hpij, hqij]

def leftPointProjection (block : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  blockSkew block (Z * Xᵀ) * X

def rightPointProjection (block : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  X * blockSkew block (Xᵀ * Z)

/-- Polynomial ambient extension. On the GS orbit this is its generator-image
Frobenius projector; outside the orbit no idempotence is claimed. -/
def pointProjection (block₁ block₂ : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  leftPointProjection block₂ X Z + rightPointProjection block₁ X Z -
    leftPointProjection block₂ X (rightPointProjection block₁ X Z)

theorem lift_add (L R A B : Mat n) :
    lift L R (A + B) = lift L R A + lift L R B := by
  simp only [lift, Matrix.mul_add, Matrix.add_mul]

theorem leftPointProjection_lift (block : Fin n → ℕ) (L R W : Mat n)
    (hsL : Supported block L) (hL : Orthogonal L) (hR : Orthogonal R) :
    leftPointProjection block (L * R) (lift L R W) =
      lift L R (blockSkew block W) := by
  have hinput : lift L R W * (L * R)ᵀ = L * W * Lᵀ := by
    calc
      lift L R W * (L * R)ᵀ = L * W * (R * Rᵀ) * Lᵀ := by
        simp only [lift, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = L * W * Lᵀ := by rw [hR.2]; simp
  unfold leftPointProjection
  rw [hinput, blockSkew_conjugation block L W hsL]
  calc
    (L * blockSkew block W * Lᵀ) * (L * R) =
        L * blockSkew block W * (Lᵀ * L) * R := by
      simp only [Matrix.mul_assoc]
    _ = lift L R (blockSkew block W) := by rw [hL.1]; simp [lift]

theorem rightPointProjection_lift (block : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L B W : Mat n)
    (hsB : Supported block B) (hL : Orthogonal L) (hB : Orthogonal B) :
    rightPointProjection block (product2 L (permMatrix σ) B)
      (lift L (permMatrix σ * B) W) =
    lift L (permMatrix σ * B)
      (maskedSkew (fun i j => block (σ.symm i) = block (σ.symm j)) W) := by
  let P := permMatrix σ
  have hP : Orthogonal P := perm_orthogonal σ
  have hinput : (product2 L P B)ᵀ * lift L (P * B) W =
      Bᵀ * (Pᵀ * W * P) * B := by
    calc
      (product2 L P B)ᵀ * lift L (P * B) W =
          Bᵀ * Pᵀ * (Lᵀ * L) * W * P * B := by
        simp only [product2, lift, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Bᵀ * (Pᵀ * W * P) * B := by rw [hL.1]; simp [Matrix.mul_assoc]
  have hsk : blockSkew block (Bᵀ * (Pᵀ * W * P) * B) =
      Bᵀ * blockSkew block (Pᵀ * W * P) * B := by
    simpa only [Matrix.transpose_transpose] using
      blockSkew_conjugation block Bᵀ (Pᵀ * W * P) hsB.transpose
  have hbase : rightPointProjection block (product2 L P B) (lift L (P * B) W) =
      lift L (P * B) (P * blockSkew block (Pᵀ * W * P) * Pᵀ) := by
    unfold rightPointProjection
    rw [hinput, hsk]
    calc
      product2 L P B * (Bᵀ * blockSkew block (Pᵀ * W * P) * B) =
          L * P * (B * Bᵀ) * blockSkew block (Pᵀ * W * P) * B := by
        simp only [product2, Matrix.mul_assoc]
      _ = L * P * blockSkew block (Pᵀ * W * P) * B := by rw [hB.2]; simp
      _ = L * P * blockSkew block (Pᵀ * W * P) * (Pᵀ * P) * B := by
        rw [hP.1]; simp
      _ = lift L (P * B) (P * blockSkew block (Pᵀ * W * P) * Pᵀ) := by
        simp only [lift, Matrix.mul_assoc]
  rw [blockSkew_permutation block σ W] at hbase
  exact hbase

/-- The point-only formula becomes the union mask after the orthogonal change
of coordinates already used in the manuscript. -/
theorem pointProjection_lift (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ W : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁) :
    pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁)
      (lift B₂ (permMatrix σ * B₁) W) =
    lift B₂ (permMatrix σ * B₁) (maskedSkew (tangentUnion block₁ block₂ σ) W) := by
  classical
  let P := permMatrix σ
  let p := fun i j : Fin n => block₂ i = block₂ j
  let q := fun i j : Fin n => block₁ (σ.symm i) = block₁ (σ.symm j)
  have hq : MaskSymmetric q := fun _ _ => eq_comm
  have hl : ∀ T : Mat n,
      leftPointProjection block₂ (product2 B₂ P B₁) (lift B₂ (P * B₁) T) =
        lift B₂ (P * B₁) (maskedSkew p T) := by
    intro T
    simpa only [product2, Matrix.mul_assoc, blockSkew] using
      leftPointProjection_lift block₂ B₂ (P * B₁) T hs₂ h₂ ((perm_orthogonal σ).mul h₁)
  have hr : ∀ T : Mat n,
      rightPointProjection block₁ (product2 B₂ P B₁) (lift B₂ (P * B₁) T) =
        lift B₂ (P * B₁) (maskedSkew q T) := by
    intro T
    exact rightPointProjection_lift block₁ σ B₂ B₁ T hs₁ h₂ h₁
  change pointProjection block₁ block₂ (product2 B₂ P B₁) (lift B₂ (P * B₁) W) = _
  simp only [pointProjection, hl, hr]
  rw [← lift_add, ← lift_sub, ← maskedSkew_union p q hq]
  apply congrArg (lift B₂ (permMatrix σ * B₁))
  ext i j
  by_cases hij : block₂ i = block₂ j ∨ block₁ (σ.symm i) = block₁ (σ.symm j)
  all_goals simp [maskedSkew, mask, tangentUnion, p, q, hij]

/-- Equivalence to the existing exact factor-coordinate projector. -/
theorem pointProjection_eq_factorProjection (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁) :
    pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z =
      twoFactorProjection block₁ block₂ σ B₂ B₁ Z := by
  classical
  let R := permMatrix σ * B₁
  let W := pull B₂ R Z
  have hi : lift B₂ R W = Z := lift_pull B₂ R Z h₂ ((perm_orthogonal σ).mul h₁)
  calc
    pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z =
        pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) (lift B₂ R W) :=
      congrArg (pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁)) hi.symm
    _ = lift B₂ R (maskedSkew (tangentUnion block₁ block₂ σ) W) :=
      pointProjection_lift block₁ block₂ σ B₂ B₁ W hs₂ hs₁ h₂ h₁
    _ = twoFactorProjection block₁ block₂ σ B₂ B₁ Z := rfl

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_leftPointProjection (block : Fin n → ℕ) {X Z : E → Mat n}
    (hX : ContDiff ℝ ⊤ X) (hZ : ContDiff ℝ ⊤ Z) :
    ContDiff ℝ ⊤ (fun t => leftPointProjection block (X t) (Z t)) :=
  contDiff_matrix_mul
    (contDiff_maskedSkew _ (contDiff_matrix_mul hZ (contDiff_matrix_transpose hX))) hX

theorem contDiff_rightPointProjection (block : Fin n → ℕ) {X Z : E → Mat n}
    (hX : ContDiff ℝ ⊤ X) (hZ : ContDiff ℝ ⊤ Z) :
    ContDiff ℝ ⊤ (fun t => rightPointProjection block (X t) (Z t)) :=
  contDiff_matrix_mul hX
    (contDiff_maskedSkew _ (contDiff_matrix_mul (contDiff_matrix_transpose hX) hZ))

theorem contDiff_pointProjection (block₁ block₂ : Fin n → ℕ) {X Z : E → Mat n}
    (hX : ContDiff ℝ ⊤ X) (hZ : ContDiff ℝ ⊤ Z) :
    ContDiff ℝ ⊤ (fun t => pointProjection block₁ block₂ (X t) (Z t)) := by
  have hl := contDiff_leftPointProjection block₂ hX hZ
  have hr := contDiff_rightPointProjection block₁ hX hZ
  exact (hl.add hr).sub (contDiff_leftPointProjection block₂ hX hr)

end Smooth

/-- C-infinity in (X,Z) on the full ambient matrix space, before any manifold
structure on the GS image is constructed. -/
theorem pointProjection_smooth (block₁ block₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun t : Mat n × Mat n => pointProjection block₁ block₂ t.1 t.2) :=
  contDiff_pointProjection block₁ block₂ contDiff_fst contDiff_snd

/-- The restriction is continuous on the actual GS subset with its induced
Euclidean topology. No choice of representative factors is made. -/
theorem pointProjection_continuous_on_A2 (b₁ b₂ : ℕ) (P : Mat n) :
    Continuous (fun t : {X : Mat n // InA2Orth b₁ b₂ P X} × Mat n =>
      pointProjection (fun i => i.val / b₁) (fun i => i.val / b₂) t.1.val t.2) := by
  have hv : Continuous
      (fun t : {X : Mat n // InA2Orth b₁ b₂ P X} × Mat n => (t.1.val, t.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hp : Continuous (fun t : Mat n × Mat n =>
      pointProjection (fun i => i.val / b₁) (fun i => i.val / b₂) t.1 t.2) :=
    (pointProjection_smooth _ _).continuous
  have hcomp := hp.comp hv
  simpa only [Function.comp_def] using hcomp

/-- Exact least-squares certificate transferred to the point-only formula. -/
theorem pointProjection_pythagorean (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z Y : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁)
    (hY : TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁ Y) :
    frobSq (Z - Y) =
      frobSq (Z - pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z) +
      frobSq (pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z - Y) := by
  rw [pointProjection_eq_factorProjection block₁ block₂ σ B₂ B₁ Z hs₂ hs₁ h₂ h₁]
  exact twoFactorProjection_pythagorean block₁ block₂ σ B₂ B₁ Z Y h₂ h₁ hY

theorem pointProjection_in_direction (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁) :
    TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁
      (pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z) := by
  rw [pointProjection_eq_factorProjection block₁ block₂ σ B₂ B₁ Z hs₂ hs₁ h₂ h₁]
  exact twoFactorProjection_in_direction block₁ block₂ σ B₂ B₁ Z

/-- The point-only expression does not depend on representative factors,
since their product is its literal argument. This also rederives the equality
of the two older factor-coordinate formulas. -/
theorem factorProjection_eq_of_product_eq (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R L' R' Z : Mat n)
    (hsL : Supported block₂ L) (hsR : Supported block₁ R)
    (hsL' : Supported block₂ L') (hsR' : Supported block₁ R')
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hL' : Orthogonal L') (hR' : Orthogonal R')
    (he : product2 L (permMatrix σ) R = product2 L' (permMatrix σ) R') :
    twoFactorProjection block₁ block₂ σ L R Z =
      twoFactorProjection block₁ block₂ σ L' R' Z := by
  rw [← pointProjection_eq_factorProjection block₁ block₂ σ L R Z hsL hsR hL hR,
    ← pointProjection_eq_factorProjection block₁ block₂ σ L' R' Z hsL' hsR' hL' hR', he]

/-- Fixed points of the point-only operator are exactly the original explicit
supported-skew generator image. This is not a new definition of tangent space. -/
theorem pointProjection_fixed_iff (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Y : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁) :
    pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Y = Y ↔
      TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁ Y := by
  classical
  constructor
  · intro he
    rw [← he]
    exact pointProjection_in_direction block₁ block₂ σ B₂ B₁ Y hs₂ hs₁ h₂ h₁
  · intro hY
    rw [pointProjection_eq_factorProjection block₁ block₂ σ B₂ B₁ Y hs₂ hs₁ h₂ h₁]
    exact projection_fixed B₂ (permMatrix σ * B₁) Y h₂ ((perm_orthogonal σ).mul h₁)
      ((twoFactorDirection_iff_admissible block₁ block₂ σ B₂ B₁ Y).mp hY)

theorem pointProjection_idempotent (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁) :
    let X := product2 B₂ (permMatrix σ) B₁
    pointProjection block₁ block₂ X (pointProjection block₁ block₂ X Z) =
      pointProjection block₁ block₂ X Z := by
  apply (pointProjection_fixed_iff block₁ block₂ σ B₂ B₁ _ hs₂ hs₁ h₂ h₁).mpr
  exact pointProjection_in_direction block₁ block₂ σ B₂ B₁ Z hs₂ hs₁ h₂ h₁

/-- The actual supported-skew generator image is independent of the chosen
orthogonal block factors of a point. This does not presume a manifold or a
smooth lifting theorem: it follows from the common point-only projector. -/
theorem twoFactorDirection_iff_of_product_eq (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R L' R' Y : Mat n)
    (hsL : Supported block₂ L) (hsR : Supported block₁ R)
    (hsL' : Supported block₂ L') (hsR' : Supported block₁ R')
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hL' : Orthogonal L') (hR' : Orthogonal R')
    (he : product2 L (permMatrix σ) R = product2 L' (permMatrix σ) R') :
    TwoFactorDirection block₁ block₂ L (permMatrix σ) R Y ↔
      TwoFactorDirection block₁ block₂ L' (permMatrix σ) R' Y := by
  rw [← pointProjection_fixed_iff block₁ block₂ σ L R Y hsL hsR hL hR,
    ← pointProjection_fixed_iff block₁ block₂ σ L' R' Y hsL' hsR' hL' hR', he]

theorem pointProjection_self_adjoint (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z W : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁) :
    let X := product2 B₂ (permMatrix σ) B₁
    frobInner (pointProjection block₁ block₂ X Z) W =
      frobInner Z (pointProjection block₁ block₂ X W) := by
  classical
  dsimp only
  rw [pointProjection_eq_factorProjection block₁ block₂ σ B₂ B₁ Z hs₂ hs₁ h₂ h₁,
    pointProjection_eq_factorProjection block₁ block₂ σ B₂ B₁ W hs₂ hs₁ h₂ h₁]
  exact projection_self_adjoint (tangentUnion block₁ block₂ σ)
    (tangentUnion_symmetric block₁ block₂ σ) B₂ (permMatrix σ * B₁) Z W
      h₂ ((perm_orthogonal σ).mul h₁)

/-- Frobenius normality annihilates the actual polynomial projection. -/
theorem pointProjection_zero_of_normal (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ Z : Mat n)
    (hs₂ : Supported block₂ B₂) (hs₁ : Supported block₁ B₁)
    (h₂ : Orthogonal B₂) (h₁ : Orthogonal B₁)
    (hn : ∀ Y, TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁ Y →
      frobInner Z Y = 0) :
    pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z = 0 := by
  classical
  let Y := pointProjection block₁ block₂ (product2 B₂ (permMatrix σ) B₁) Z
  have hY : TwoFactorDirection block₁ block₂ B₂ (permMatrix σ) B₁ Y :=
    pointProjection_in_direction block₁ block₂ σ B₂ B₁ Z hs₂ hs₁ h₂ h₁
  have hz : frobInner Z Y = 0 := hn Y hY
  have hr : frobInner (Z - Y) Y = 0 := by
    dsimp [Y]
    rw [pointProjection_eq_factorProjection block₁ block₂ σ B₂ B₁ Z hs₂ hs₁ h₂ h₁]
    exact projection_residual_orthogonal B₂ (permMatrix σ * B₁) Z _ h₂
      ((perm_orthogonal σ).mul h₁)
      ((twoFactorDirection_iff_admissible block₁ block₂ σ B₂ B₁ _).mp
        (twoFactorProjection_in_direction block₁ block₂ σ B₂ B₁ Z))
  have hzero : frobSq Y = 0 := by
    rw [frobInner_sub_left, hz] at hr
    unfold frobSq
    linarith
  exact (frobSq_eq_zero_iff Y).mp hzero

end GS.Continuation
