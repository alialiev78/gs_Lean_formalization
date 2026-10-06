module

public import GS.Unitary.PointProjection
public import GS.Unitary.ProjectionRegularity
public import GS.Unitary.Permutations
public import GS.UnitaryManifold.Action

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Canonical supported skew-Hermitian generators depending only on the
base matrix and ambient vector. Arbitrary overlap of independent blocks is allowed. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.UnitaryManifold
namespace GS.UnitaryGeometry
variable {n : ℕ}

def cLift (L R W : CMat n) : CMat n := L * W * R
def cPull (L R W : CMat n) : CMat n := Lᴴ * W * Rᴴ

theorem cLift_cPull (L R W : CMat n) (hL : Unitary L) (hR : Unitary R) :
    cLift L R (cPull L R W) = W := by
  simpa [cLift, cPull] using unitary_boundary_cancel Lᴴ Rᴴ W hL.conjTranspose hR.conjTranspose

def blockSkew (block : Fin n → ℕ) (A : CMat n) : CMat n :=
  maskedSkewHermitian (fun i j => block i = block j) A

theorem skew_conjugation (U A : CMat n) :
    skewHermitianPart (U * A * Uᴴ) = U * skewHermitianPart A * Uᴴ := by
  simp only [skewHermitianPart_eq_real_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]

/-- Conjugation within a block algebra commutes with its skew-Hermitian projection.
Unitarity of U is not required for this algebraic identity. -/
theorem blockSkew_conjugation (block : Fin n → ℕ) (U A : CMat n)
    (hU : CSupported block U) :
    blockSkew block (U * A * Uᴴ) = U * blockSkew block A * Uᴴ := by
  change cBlockProjection block (skewHermitianPart (U * A * Uᴴ)) =
    U * cBlockProjection block (skewHermitianPart A) * Uᴴ
  rw [skew_conjugation, cBlockProjection_mul_right block (U * skewHermitianPart A) Uᴴ hU.conjTranspose,
    cBlockProjection_mul_left block U (skewHermitianPart A) hU]

/-- The right support is transported by the same permutation as its matrix. -/
theorem blockSkew_permutation (block : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (A : CMat n) :
    cPermMatrix σ * blockSkew block ((cPermMatrix σ)ᴴ * A * cPermMatrix σ) *
      (cPermMatrix σ)ᴴ =
        maskedSkewHermitian (fun i j => block (σ.symm i) = block (σ.symm j)) A := by
  classical
  ext i j
  rw [cPerm_conjugate_apply]
  simp [blockSkew, maskedSkewHermitian, cMask, skewHermitianPart, cPerm_conjTranspose]

theorem maskedSkewHermitian_composition (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (hq : CMaskSymmetric q) (A : CMat n) :
    maskedSkewHermitian p (maskedSkewHermitian q A) = maskedSkewHermitian (fun i j => p i j ∧ q i j) A := by
  classical
  have hk : IsSkewHermitian (maskedSkewHermitian q A) := maskedSkewHermitian_isSkewHermitian hq A
  change cMask p (skewHermitianPart (maskedSkewHermitian q A)) = _
  rw [skewHermitianPart_fixed hk]
  ext i j
  by_cases hpij : p i j <;> by_cases hqij : q i j <;>
    simp [maskedSkewHermitian, cMask, hpij, hqij]

/-- Inclusion-exclusion for two commuting coordinate skew-Hermitian projectors. -/
theorem maskedSkewHermitian_union (p q : Fin n → Fin n → Prop)
    [DecidableRel p] [DecidableRel q] (hq : CMaskSymmetric q) (A : CMat n) :
    maskedSkewHermitian (fun i j => p i j ∨ q i j) A =
      maskedSkewHermitian p A + maskedSkewHermitian q A - maskedSkewHermitian p (maskedSkewHermitian q A) := by
  classical
  rw [maskedSkewHermitian_composition p q hq]
  ext i j
  by_cases hpij : p i j <;> by_cases hqij : q i j <;>
    simp [maskedSkewHermitian, cMask, hpij, hqij]

def leftPointProjection (block : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  blockSkew block (Z * Xᴴ) * X

def rightPointProjection (block : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  X * blockSkew block (Xᴴ * Z)

/-- Polynomial ambient extension. On the GS orbit this is its generator-image
Frobenius projector; outside the orbit no idempotence is claimed. -/
def polynomialPointProjection (block₁ block₂ : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  leftPointProjection block₂ X Z + rightPointProjection block₁ X Z -
    leftPointProjection block₂ X (rightPointProjection block₁ X Z)

theorem cLift_add (L R A B : CMat n) :
    cLift L R (A + B) = cLift L R A + cLift L R B := by
  simp only [cLift, Matrix.mul_add, Matrix.add_mul]

theorem leftPointProjection_lift (block : Fin n → ℕ) (L R W : CMat n)
    (hsL : CSupported block L) (hL : Unitary L) (hR : Unitary R) :
    leftPointProjection block (L * R) (cLift L R W) =
      cLift L R (blockSkew block W) := by
  have hinput : cLift L R W * (L * R)ᴴ = L * W * Lᴴ := by
    calc
      cLift L R W * (L * R)ᴴ = L * W * (R * Rᴴ) * Lᴴ := by
        simp only [cLift, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = L * W * Lᴴ := by rw [hR.2]; simp
  unfold leftPointProjection
  rw [hinput, blockSkew_conjugation block L W hsL]
  calc
    (L * blockSkew block W * Lᴴ) * (L * R) =
        L * blockSkew block W * (Lᴴ * L) * R := by
      simp only [Matrix.mul_assoc]
    _ = cLift L R (blockSkew block W) := by rw [hL.1]; simp [cLift]

theorem rightPointProjection_lift (block : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L B W : CMat n)
    (hsB : CSupported block B) (hL : Unitary L) (hB : Unitary B) :
    rightPointProjection block (product2 L (cPermMatrix σ) B)
      (cLift L (cPermMatrix σ * B) W) =
    cLift L (cPermMatrix σ * B)
      (maskedSkewHermitian (fun i j => block (σ.symm i) = block (σ.symm j)) W) := by
  let P := cPermMatrix σ
  have hP : Unitary P := cPerm_unitary σ
  have hinput : (product2 L P B)ᴴ * cLift L (P * B) W =
      Bᴴ * (Pᴴ * W * P) * B := by
    calc
      (product2 L P B)ᴴ * cLift L (P * B) W =
          Bᴴ * Pᴴ * (Lᴴ * L) * W * P * B := by
        simp only [product2, cLift, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * (Pᴴ * W * P) * B := by rw [hL.1]; simp [Matrix.mul_assoc]
  have hsk : blockSkew block (Bᴴ * (Pᴴ * W * P) * B) =
      Bᴴ * blockSkew block (Pᴴ * W * P) * B := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      blockSkew_conjugation block Bᴴ (Pᴴ * W * P) hsB.conjTranspose
  have hbase : rightPointProjection block (product2 L P B) (cLift L (P * B) W) =
      cLift L (P * B) (P * blockSkew block (Pᴴ * W * P) * Pᴴ) := by
    unfold rightPointProjection
    rw [hinput, hsk]
    calc
      product2 L P B * (Bᴴ * blockSkew block (Pᴴ * W * P) * B) =
          L * P * (B * Bᴴ) * blockSkew block (Pᴴ * W * P) * B := by
        simp only [product2, Matrix.mul_assoc]
      _ = L * P * blockSkew block (Pᴴ * W * P) * B := by rw [hB.2]; simp
      _ = L * P * blockSkew block (Pᴴ * W * P) * (Pᴴ * P) * B := by
        rw [hP.1]; simp
      _ = cLift L (P * B) (P * blockSkew block (Pᴴ * W * P) * Pᴴ) := by
        simp only [cLift, Matrix.mul_assoc]
  rw [blockSkew_permutation block σ W] at hbase
  exact hbase


@[simp] theorem blockSkew_add (b : Fin n → ℕ) (A B : CMat n) :
    blockSkew b (A+B) = blockSkew b A + blockSkew b B :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_add A B

@[simp] theorem blockSkew_smul (b : Fin n → ℕ) (a : ℝ) (A : CMat n) :
    blockSkew b (a • A) = a • blockSkew b A :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_smul a A

@[simp] theorem blockSkew_zero (b : Fin n → ℕ) : blockSkew b (0 : CMat n) = 0 :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_zero

theorem blockSkew_sub (b : Fin n → ℕ) (A B : CMat n) :
    blockSkew b (A-B) = blockSkew b A - blockSkew b B :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_sub A B

theorem blockSkew_supported (b : Fin n → ℕ) (A : CMat n) :
    CSupported b (blockSkew b A) := maskedSkewHermitian_hasSupport _ _

theorem blockSkew_skew (b : Fin n → ℕ) (A : CMat n) :
    IsSkewHermitian (blockSkew b A) := maskedSkewHermitian_isSkewHermitian (fun _ _ => eq_comm) _

theorem maskedSkewHermitian_commutes (p q : Fin n → Fin n → Prop)
    (hp : CMaskSymmetric p) (hq : CMaskSymmetric q) (A : CMat n) :
    maskedSkewHermitian p (maskedSkewHermitian q A) = maskedSkewHermitian q (maskedSkewHermitian p A) := by
  rw [maskedSkewHermitian_composition p q hq, maskedSkewHermitian_composition q p hp]
  ext i j
  simp only [maskedSkewHermitian, cMask, and_comm]

/-- The common part of the two actual orbit projectors. This is false for
arbitrary unrelated subspace projectors; here the factor-coordinate masks prove it. -/
theorem pointProjectors_commute (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : CMat n)
    (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R) :
    let X := product2 L (cPermMatrix σ) R
    leftPointProjection b₂ X (rightPointProjection b₁ X Z) =
      rightPointProjection b₁ X (leftPointProjection b₂ X Z) := by
  classical
  dsimp only
  let P := cPermMatrix σ
  let W := cPull L (P*R) Z
  let p := fun i j : Fin n => b₂ i = b₂ j
  let q := fun i j : Fin n => b₁ (σ.symm i) = b₁ (σ.symm j)
  have hl (A : CMat n) :
      leftPointProjection b₂ (product2 L P R) (cLift L (P*R) A) =
        cLift L (P*R) (maskedSkewHermitian p A) := by
    simpa only [product2, Matrix.mul_assoc, blockSkew, p] using
      leftPointProjection_lift b₂ L (P*R) A hsL hL ((cPerm_unitary σ).mul hR)
  have hr (A : CMat n) :
      rightPointProjection b₁ (product2 L P R) (cLift L (P*R) A) =
        cLift L (P*R) (maskedSkewHermitian q A) :=
    rightPointProjection_lift b₁ σ L R A hsR hL hR
  have hz : Z = cLift L (P*R) W :=
    (cLift_cPull L (P*R) Z hL ((cPerm_unitary σ).mul hR)).symm
  change leftPointProjection b₂ (product2 L P R)
      (rightPointProjection b₁ (product2 L P R) Z) = _
  rw [hz, hr, hl, hl, hr]
  apply congrArg (cLift L (P*R))
  rw [maskedSkewHermitian_composition p q (fun _ _ => eq_comm),
    maskedSkewHermitian_composition q p (fun _ _ => eq_comm)]
  ext i j
  simp only [maskedSkewHermitian, cMask, and_comm]

/-- Left ambient generator, in the Lie algebra of the LEFT physical blocks. -/
def balancedLeft (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  blockSkew b₂ ((Z - (1/2 : ℝ) • rightPointProjection b₁ X Z) * Xᴴ)

/-- Right ambient generator, in the Lie algebra of the RIGHT physical blocks. -/
def balancedRight (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  blockSkew b₁ (Xᴴ * (Z - (1/2 : ℝ) • leftPointProjection b₂ X Z))

theorem balancedLeft_supported (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    CSupported b₂ (balancedLeft b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedRight_supported (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    CSupported b₁ (balancedRight b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedLeft_skew (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    IsSkewHermitian (balancedLeft b₁ b₂ X Z) := blockSkew_skew _ _

theorem balancedRight_skew (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    IsSkewHermitian (balancedRight b₁ b₂ X Z) := blockSkew_skew _ _

@[simp] theorem balancedLeft_zero (b₁ b₂ : Fin n → ℕ) (X : CMat n) :
    balancedLeft b₁ b₂ X 0 = 0 := by
  simp [balancedLeft, rightPointProjection]

@[simp] theorem balancedRight_zero (b₁ b₂ : Fin n → ℕ) (X : CMat n) :
    balancedRight b₁ b₂ X 0 = 0 := by
  simp [balancedRight, leftPointProjection]

/-- The balanced lift is linear in the ambient direction. -/
@[simp] theorem balancedLeft_smul (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) (a : ℝ) :
    balancedLeft b₁ b₂ X (a • Z) = a • balancedLeft b₁ b₂ X Z := by
  simp [balancedLeft, rightPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sub_mul, blockSkew_sub, smul_sub, smul_smul, mul_comm]

@[simp] theorem balancedRight_smul (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) (a : ℝ) :
    balancedRight b₁ b₂ X (a • Z) = a • balancedRight b₁ b₂ X Z := by
  simp [balancedRight, leftPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, blockSkew_sub, smul_sub, smul_smul, mul_comm]

theorem balancedLeft_mul (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    balancedLeft b₁ b₂ X Z * X =
      leftPointProjection b₂ X Z - (1/2 : ℝ) •
        leftPointProjection b₂ X (rightPointProjection b₁ X Z) := by
  simp only [balancedLeft, Matrix.sub_mul, Matrix.smul_mul, blockSkew_sub,
    blockSkew_smul, leftPointProjection]

theorem mul_balancedRight (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    X * balancedRight b₁ b₂ X Z =
      rightPointProjection b₁ X Z - (1/2 : ℝ) •
        rightPointProjection b₁ X (leftPointProjection b₂ X Z) := by
  simp only [balancedRight, Matrix.mul_sub, Matrix.mul_smul, blockSkew_sub,
    blockSkew_smul, rightPointProjection]


theorem balanced_reconstruct_polynomial (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : CMat n)
    (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R) :
    let X := product2 L (cPermMatrix σ) R
    balancedLeft b₁ b₂ X Z * X + X * balancedRight b₁ b₂ X Z =
      polynomialPointProjection b₁ b₂ X Z := by
  dsimp only
  rw [balancedLeft_mul, mul_balancedRight,
    ← pointProjectors_commute b₁ b₂ σ L R Z hsL hsR hL hR]
  unfold polynomialPointProjection
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

theorem leftPointProjection_add (b : Fin n → ℕ) (X Z W : CMat n) :
    leftPointProjection b X (Z+W) = leftPointProjection b X Z + leftPointProjection b X W := by
  simp [leftPointProjection, Matrix.add_mul]

theorem rightPointProjection_add (b : Fin n → ℕ) (X Z W : CMat n) :
    rightPointProjection b X (Z+W) = rightPointProjection b X Z + rightPointProjection b X W := by
  simp [rightPointProjection, Matrix.mul_add]

theorem leftPointProjection_fixed (b : Fin n → ℕ) (X C : CMat n)
    (hX : Unitary X) (hC : C ∈ supportedSkewSpace b) :
    leftPointProjection b X (C*X) = C*X := by
  have he : C*X*Xᴴ = C := by rw [Matrix.mul_assoc, hX.2, Matrix.mul_one]
  simp only [leftPointProjection, he, blockSkew,
    maskedSkewHermitian_fixed hC.1 hC.2]

theorem rightPointProjection_fixed (b : Fin n → ℕ) (X Ω : CMat n)
    (hX : Unitary X) (hΩ : Ω ∈ supportedSkewSpace b) :
    rightPointProjection b X (X*Ω) = X*Ω := by
  have he : Xᴴ*(X*Ω) = Ω := by rw [← Matrix.mul_assoc, hX.1, Matrix.one_mul]
  simp only [rightPointProjection, he, blockSkew,
    maskedSkewHermitian_fixed hΩ.1 hΩ.2]

/-- Every actual tangent matrix is exactly reconstructed. The generators are
polynomials of the matrix point and tangent vector, with no chosen factors. -/
theorem balanced_reconstruct_tangent (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : CMat n)
    (hsL : CSupported b₂ L) (hsR : CSupported b₁ R)
    (hL : Unitary L) (hR : Unitary R)
    (hZ : Z ∈ pointTangentSpace b₁ b₂ (L*cPermMatrix σ*R)) :
    let X := L*cPermMatrix σ*R
    balancedLeft b₁ b₂ X Z * X + X * balancedRight b₁ b₂ X Z = Z := by
  dsimp only
  have hb := balanced_reconstruct_polynomial b₁ b₂ σ L R Z hsL hsR hL hR
  dsimp only [product2] at hb
  rw [hb]
  obtain ⟨C, hC, Ω, hΩ, rfl⟩ := (mem_pointTangentSpace_iff b₁ b₂ _ Z).mp hZ
  let X := product2 L (cPermMatrix σ) R
  have hX : Unitary X := (hL.mul (cPerm_unitary σ)).mul hR
  have hl : leftPointProjection b₂ X (C*X) = C*X := leftPointProjection_fixed b₂ X C hX hC
  have hr : rightPointProjection b₁ X (X*Ω) = X*Ω := rightPointProjection_fixed b₁ X Ω hX hΩ
  have hc : leftPointProjection b₂ X (rightPointProjection b₁ X (C*X)) =
      rightPointProjection b₁ X (C*X) := by
    rw [pointProjectors_commute b₁ b₂ σ L R (C*X) hsL hsR hL hR, hl]
  change polynomialPointProjection b₁ b₂ X (C*X+X*Ω) = C*X+X*Ω
  simp only [polynomialPointProjection, rightPointProjection_add, leftPointProjection_add,
    hl, hr, hc]
  abel

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_leftPointProjection (b : Fin n → ℕ) {X Z : E → CMat n}
    (hX : ContDiff ℝ ⊤ X) (hZ : ContDiff ℝ ⊤ Z) :
    ContDiff ℝ ⊤ (fun t => leftPointProjection b (X t) (Z t)) :=
  smooth_matrix_product ((maskedSkewHermitian_contDiff _).comp
    (smooth_matrix_product hZ (smooth_matrix_conjTranspose hX))) hX

theorem contDiff_rightPointProjection (b : Fin n → ℕ) {X Z : E → CMat n}
    (hX : ContDiff ℝ ⊤ X) (hZ : ContDiff ℝ ⊤ Z) :
    ContDiff ℝ ⊤ (fun t => rightPointProjection b (X t) (Z t)) :=
  smooth_matrix_product hX ((maskedSkewHermitian_contDiff _).comp
    (smooth_matrix_product (smooth_matrix_conjTranspose hX) hZ))
end Smooth

theorem balancedLeft_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun t : CMat n × CMat n => balancedLeft b₁ b₂ t.1 t.2) := by
  unfold balancedLeft blockSkew
  exact (maskedSkewHermitian_contDiff _).comp (smooth_matrix_product
    (contDiff_snd.sub ((contDiff_rightPointProjection b₁ contDiff_fst contDiff_snd).const_smul (1 / 2 : ℝ)))
    (smooth_matrix_conjTranspose contDiff_fst))

theorem balancedRight_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun t : CMat n × CMat n => balancedRight b₁ b₂ t.1 t.2) := by
  unfold balancedRight blockSkew
  exact (maskedSkewHermitian_contDiff _).comp (smooth_matrix_product
    (smooth_matrix_conjTranspose contDiff_fst)
    (contDiff_snd.sub ((contDiff_leftPointProjection b₂ contDiff_fst contDiff_snd).const_smul (1 / 2 : ℝ))))

end GS.UnitaryGeometry
