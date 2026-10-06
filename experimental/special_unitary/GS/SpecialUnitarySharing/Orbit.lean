module

public import GS.SpecialUnitarySharing.Algebra
public import GS.UnitaryManifold.OrbitTopology
public import GS.LieAction.CompactQuotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The genuine special-unitary shared matrix orbit

This compact homogeneous space is formed from the determinant-one subgroup,
not from the larger U-sharing group. Quotient and matrix-subspace topologies
are compared explicitly. No SU manifold structure is assumed or installed.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.SpecialUnitarySharing.Orbit
variable {n : ℕ} {right left : Pattern n}

/-- Each physical block of both factors lies in its special-unitary group. -/
def InSharedA2SU (right left : Pattern n) (P X : CMat n) : Prop :=
  ∃ L R : CMat n, SpecialUnitaryFactor left L ∧ SpecialUnitaryFactor right R ∧
    X = L * P * R

instance factorsMulAction (right left : Pattern n) :
    MulAction (SpecialFactors right left) (CMat n) where
  smul g X := SpecialFactor.matrix g.1 * X * (SpecialFactor.matrix g.2)ᴴ
  one_smul X := by
    change (1 : CMat n) * X * (1 : CMat n)ᴴ = X
    simp
  mul_smul g h X := by
    change (SpecialFactor.matrix g.1 * SpecialFactor.matrix h.1) * X *
      (SpecialFactor.matrix g.2 * SpecialFactor.matrix h.2)ᴴ =
      SpecialFactor.matrix g.1 * (SpecialFactor.matrix h.1 * X * (SpecialFactor.matrix h.2)ᴴ) *
        (SpecialFactor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : SpecialFactors right left) (X : CMat n) :
    g • X = SpecialFactor.matrix g.1 * X * (SpecialFactor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern n) :
    ContinuousSMul (SpecialFactors right left) (CMat n) where
  continuous_smul := by
    change Continuous (fun p : SpecialFactors right left × CMat n =>
      SpecialFactor.matrix p.1.1 * p.2 * (SpecialFactor.matrix p.1.2)ᴴ)
    exact GS.UnitaryManifold.continuous_matrix_product
      (GS.UnitaryManifold.continuous_matrix_product
        (SpecialFactor.continuous_matrix.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (GS.UnitaryManifold.continuous_matrix_conjTranspose
        (SpecialFactor.continuous_matrix.comp (continuous_snd.comp continuous_fst)))

def orbitMap (right left : Pattern n) (P : CMat n) : SpecialFactors right left → CMat n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Pattern n) (P : CMat n) :=
  ↥(MulAction.orbit (SpecialFactors right left) P)

abbrev PointStabilizer (right left : Pattern n) (P : CMat n) :=
  MulAction.stabilizer (SpecialFactors right left) P

abbrev OrbitCosets (right left : Pattern n) (P : CMat n) :=
  SpecialFactors right left ⧸ PointStabilizer right left P

theorem continuous_orbitMap (P : CMat n) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : CMat n) :
    X ∈ MulAction.orbit (SpecialFactors right left) P ↔
      InSharedA2SU right left P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨SpecialFactor.matrix g.1, (SpecialFactor.matrix g.2)ᴴ, SpecialFactor.matrix_special g.1,
      special_factor_conjTranspose _ (SpecialFactor.matrix_special g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(SpecialFactor.ofMatrix L hL, SpecialFactor.ofMatrix Rᴴ (special_factor_conjTranspose _ hR)), ?_⟩
    simpa only [action_apply, SpecialFactor.matrix_ofMatrix, Matrix.conjTranspose_conjTranspose,
      product2] using hX.symm

theorem orbit_set_eq_inShared (P : CMat n) :
    MulAction.orbit (SpecialFactors right left) P =
      {X | InSharedA2SU right left P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern n) (P : CMat n) :
    SpecialFactors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : CMat n) :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_orbitMap P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : CMat n) :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem compact_matrixOrbit (P : CMat n) :
    IsCompact (MulAction.orbit (SpecialFactors right left) P) := by
  change IsCompact (Set.range (orbitMap right left P))
  simpa only [Set.image_univ] using
    (isCompact_univ.image (continuous_orbitMap (right := right) (left := left) P))

theorem closed_matrixOrbit (P : CMat n) :
    IsClosed (MulAction.orbit (SpecialFactors right left) P) := (compact_matrixOrbit P).isClosed

instance matrixOrbitCompactSpace (P : CMat n) : CompactSpace (MatrixOrbit right left P) :=
  isCompact_iff_compactSpace.mp (compact_matrixOrbit P)

theorem action_preserves_unitary (g : SpecialFactors right left) {X : CMat n}
    (hX : Unitary X) : Unitary (g • X) :=
  ((SpecialFactor.matrix_unitary g.1).mul hX).mul (SpecialFactor.matrix_unitary g.2).conjTranspose

theorem matrixOrbit_unitary (P : CMat n) (hP : Unitary P)
    (X : MatrixOrbit right left P) : Unitary X.val := by
  obtain ⟨g, hg⟩ := X.property
  rw [← hg]
  exact action_preserves_unitary g hP

theorem action_cFrobInner (g : SpecialFactors right left) (X Y : CMat n) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y :=
  GS.UnitaryManifold.action_cFrobInner (g.1.val.val, g.2.val.val) X Y

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv (g : SpecialFactors right left) : CMat n ≃ₗ[ℝ] CMat n :=
  GS.UnitaryManifold.actionLinearEquiv (g.1.val.val, g.2.val.val)

@[simp] theorem actionLinearEquiv_apply (g : SpecialFactors right left) (X : CMat n) :
    actionLinearEquiv g X = g • X := rfl

/-- The stabilizer is the genuine intersection of the two tied groups after
conjugation.  It need not be discrete or a coordinatewise diagonal group. -/
theorem stabilizer_iff (P : CMat n) (hP : Unitary P) (g : SpecialFactors right left) :
    g ∈ PointStabilizer right left P ↔
      SpecialFactor.matrix g.1 = P * SpecialFactor.matrix g.2 * Pᴴ :=
  GS.UnitaryManifold.stabilizer_iff P hP (g.1.val.val, g.2.val.val)

theorem pointStabilizer_isClosed (P : CMat n) :
    IsClosed (PointStabilizer right left P : Set (SpecialFactors right left)) :=
  isClosed_eq (continuous_orbitMap P) continuous_const

theorem orbit_fibre_iff (P : CMat n) (g h : SpecialFactors right left) :
    orbitMap right left P g = orbitMap right left P h ↔
      g⁻¹ * h ∈ PointStabilizer right left P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [MulAction.mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : CMat n => g • X) he
    have hh : h • P = g • P := by
      simpa only [MulAction.mul_smul, smul_inv_smul] using he'
    exact hh.symm

def cosetEquivOrbit (P : CMat n) : OrbitCosets right left P ≃ MatrixOrbit right left P :=
  (MulAction.orbitEquivQuotientStabilizer (SpecialFactors right left) P).symm

@[simp] theorem cosetEquivOrbit_mk (P : CMat n) (g : SpecialFactors right left) :
    ((cosetEquivOrbit (right := right) (left := left) P)
      (g : OrbitCosets right left P)).val = g • P :=
  MulAction.orbitEquivQuotientStabilizer_symm_apply (SpecialFactors right left) P g

theorem continuous_cosetEquivOrbit (P : CMat n) :
    Continuous (cosetEquivOrbit (right := right) (left := left) P) := by
  apply (QuotientGroup.isQuotientMap_mk (PointStabilizer right left P)).continuous_iff.mpr
  have he : (fun g : SpecialFactors right left =>
      cosetEquivOrbit P (g : OrbitCosets right left P)) = orbitMapToOrbit right left P := by
    funext g
    apply Subtype.ext
    exact cosetEquivOrbit_mk P g
  change Continuous (fun g : SpecialFactors right left =>
    cosetEquivOrbit P (g : OrbitCosets right left P))
  rw [he]
  exact continuous_orbitMapToOrbit P

/-- Both topologies are the pre-existing quotient/subspace topologies. -/
def quotientOrbitHomeomorph (P : CMat n) :
    OrbitCosets right left P ≃ₜ MatrixOrbit right left P := by
  let e := cosetEquivOrbit (right := right) (left := left) P
  have he : Continuous e := continuous_cosetEquivOrbit P
  have hi : Continuous e.symm := GS.continuous_descend_compact e (fun x => x) e.symm
    he continuous_id e.surjective (fun x => e.symm_apply_apply x)
  exact { toEquiv := e, continuous_toFun := he, continuous_invFun := hi }

theorem continuous_iff_after_orbitMap (P : CMat n)
    {Y : Type*} [TopologicalSpace Y] (f : MatrixOrbit right left P → Y) :
    Continuous f ↔ Continuous (f ∘ orbitMapToOrbit right left P) := by
  constructor
  · intro hf
    exact hf.comp (continuous_orbitMapToOrbit P)
  · intro hf
    exact GS.continuous_descend_compact (orbitMapToOrbit right left P)
      (f ∘ orbitMapToOrbit right left P) f (continuous_orbitMapToOrbit P) hf
      (surjective_orbitMapToOrbit P) (fun _ => rfl)

theorem closed_of_orbit_preimage_closed (P : CMat n)
    (s : Set (MatrixOrbit right left P))
    (hs : IsClosed (orbitMapToOrbit right left P ⁻¹' s)) : IsClosed s := by
  have he : s = orbitMapToOrbit right left P '' (orbitMapToOrbit right left P ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      exact ⟨g, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  rw [he]
  exact (hs.isCompact.image (continuous_orbitMapToOrbit P)).isClosed

theorem orbit_saturation (P : CMat n) (s : Set (SpecialFactors right left)) :
    orbitMapToOrbit right left P ⁻¹' (orbitMapToOrbit right left P '' s) =
      ⋃ h : PointStabilizer right left P,
        (fun g : SpecialFactors right left => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf : orbitMap right left P g = orbitMap right left P h :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer right left P := ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change g * (g⁻¹ * h) ∈ s
    simpa only [mul_inv_cancel_left] using hh
  · intro hg
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
    refine ⟨g * h.val, hh, ?_⟩
    apply Subtype.ext
    change (g * h.val) • P = g • P
    rw [MulAction.mul_smul, show h.val • P = P from h.property]

/-- Images of factor neighbourhoods are orbit neighbourhoods.  No continuous
or smooth section of the orbit map is asserted by this openness result. -/
theorem orbitMapToOrbit_isOpenMap (P : CMat n) :
    IsOpenMap (orbitMapToOrbit right left P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit right left P ⁻¹'
      (orbitMapToOrbit right left P '' s)) := by
    rw [orbit_saturation]
    exact isOpen_iUnion (fun h => hs.preimage (continuous_id.mul continuous_const))
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit right left P '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl

/-- A genuine inclusion, not an identification of the two orbits. -/
theorem inSharedA2SU_implies_unitary_family (P X : CMat n)
    (hX : InSharedA2SU right left P X) :
    GS.UnitarySharing.InSharedA2Unitary right.size left.size right.label left.label P X := by
  obtain ⟨L, R, hL, hR, he⟩ := hX
  exact ⟨L, R, hL.1, hR.1, he⟩

/-- Membership remains true after multiplication by genuine SU shared factors. -/
theorem inSharedA2SU_mul (P X A B : CMat n)
    (hX : InSharedA2SU right left P X)
    (hA : SpecialUnitaryFactor left A) (hB : SpecialUnitaryFactor right B) :
    InSharedA2SU right left P (A * X * B) := by
  obtain ⟨L, R, hL, hR, rfl⟩ := hX
  refine ⟨A * L, R * B, special_factor_mul _ _ hA hL,
    special_factor_mul _ _ hR hB, ?_⟩
  simp only [Matrix.mul_assoc]

/-- The smaller orbit embeds in the known U orbit with the same matrix topology. -/
def toUnitaryOrbit (P : CMat n) (X : MatrixOrbit right left P) :
    GS.UnitarySharing.MatrixOrbit right left P :=
  ⟨X.val, (GS.UnitarySharing.orbit_iff_inShared P X.val).mpr
    (inSharedA2SU_implies_unitary_family P X.val ((orbit_iff_inShared P X.val).mp X.property))⟩

@[simp] theorem toUnitaryOrbit_val (P : CMat n) (X : MatrixOrbit right left P) :
    (toUnitaryOrbit P X).val = X.val := rfl

theorem toUnitaryOrbit_continuous (P : CMat n) :
    Continuous (toUnitaryOrbit (right := right) (left := left) P) :=
  continuous_subtype_val.subtype_mk _

end GS.SpecialUnitarySharing.Orbit
