module

public import GS.LieAction.Stabilizer
public import GS.CompactFibres
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The orbit is the topological homogeneous quotient G / Stab(P)

The set-level orbit-stabilizer equivalence is reused from mathlib. Compactness
and the Hausdorff subspace topology on matrices upgrade it to a homeomorphism.
This is a topological result; no IsManifold conclusion is smuggled in.

-/

noncomputable section
open Matrix
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

abbrev MatrixOrbit (block₁ block₂ : Fin n → ℕ) (P : Mat n) :=
  ↥(MulAction.orbit (FactorGroup block₁ block₂) P)

abbrev OrbitCosets (block₁ block₂ : Fin n → ℕ) (P : Mat n) :=
  FactorGroup block₁ block₂ ⧸ PointStabilizer block₁ block₂ P

def orbitMapToOrbit (block₁ block₂ : Fin n → ℕ) (P : Mat n) :
    FactorGroup block₁ block₂ → MatrixOrbit block₁ block₂ P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : Mat n) :
    Continuous (orbitMapToOrbit block₁ block₂ P) :=
  (continuous_orbitMap block₁ block₂ P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : Mat n) :
    Function.Surjective (orbitMapToOrbit block₁ block₂ P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem compact_matrixOrbit (P : Mat n) :
    IsCompact (MulAction.orbit (FactorGroup block₁ block₂) P) := by
  simpa only [orbit_eq_range, Set.image_univ] using
    (isCompact_univ.image (continuous_orbitMap block₁ block₂ P))

theorem closed_matrixOrbit (P : Mat n) :
    IsClosed (MulAction.orbit (FactorGroup block₁ block₂) P) :=
  (compact_matrixOrbit P).isClosed

instance matrixOrbitCompactSpace (P : Mat n) :
    CompactSpace (MatrixOrbit block₁ block₂ P) :=
  isCompact_iff_compactSpace.mp (compact_matrixOrbit P)

/-- Reuse mathlib rather than reprove the algebraic orbit-stabilizer theorem. -/
def cosetEquivOrbit (P : Mat n) :
    OrbitCosets block₁ block₂ P ≃ MatrixOrbit block₁ block₂ P :=
  (MulAction.orbitEquivQuotientStabilizer (FactorGroup block₁ block₂) P).symm

@[simp] theorem cosetEquivOrbit_mk (P : Mat n) (g : FactorGroup block₁ block₂) :
    ((cosetEquivOrbit (block₁ := block₁) (block₂ := block₂) P)
      (g : OrbitCosets block₁ block₂ P)).val = g • P := by
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply
    (FactorGroup block₁ block₂) P g

/-- Continuity out of the quotient is proved using its actual coinduced
(topological quotient) topology, without assuming that quotient is a manifold. -/
theorem continuous_cosetEquivOrbit (P : Mat n) :
    Continuous (cosetEquivOrbit (block₁ := block₁) (block₂ := block₂) P) := by
  have hc : Continuous (fun g : FactorGroup block₁ block₂ =>
      cosetEquivOrbit P (g : OrbitCosets block₁ block₂ P)) := by
    have he : (fun g : FactorGroup block₁ block₂ =>
        cosetEquivOrbit P (g : OrbitCosets block₁ block₂ P)) =
        orbitMapToOrbit block₁ block₂ P := by
      funext g
      apply Subtype.ext
      exact cosetEquivOrbit_mk P g
    rw [he]
    exact continuous_orbitMapToOrbit P
  exact (QuotientGroup.isQuotientMap_mk
    (PointStabilizer block₁ block₂ P)).continuous_iff.mpr hc

/-- A genuine homeomorphism of the standard quotient and subspace topologies. -/
def quotientOrbitHomeomorph (P : Mat n) :
    OrbitCosets block₁ block₂ P ≃ₜ MatrixOrbit block₁ block₂ P := by
  let e := cosetEquivOrbit (block₁ := block₁) (block₂ := block₂) P
  have he : Continuous e := continuous_cosetEquivOrbit P
  have hei : Continuous e.symm :=
    GS.continuous_descend_compact e (fun x => x) e.symm he continuous_id
      e.surjective (fun x => e.symm_apply_apply x)
  exact { toEquiv := e, continuous_toFun := he, continuous_invFun := hei }

@[simp] theorem quotientOrbitHomeomorph_mk (P : Mat n)
    (g : FactorGroup block₁ block₂) :
    ((quotientOrbitHomeomorph (block₁ := block₁) (block₂ := block₂) P)
      (g : OrbitCosets block₁ block₂ P)).val = g • P :=
  cosetEquivOrbit_mk P g

/-- The homogeneous-space statement in exactly the original InA2Orth set. -/
def quotientA2Homeomorph (b₁ b₂ : ℕ) (P : Mat n) :
    OrbitCosets (fun i : Fin n => i.val / b₁)
                (fun i : Fin n => i.val / b₂) P ≃ₜ
      {X : Mat n // InA2Orth b₁ b₂ P X} :=
  (quotientOrbitHomeomorph P).trans
    (Homeomorph.setCongr (orbit_set_eq_inA2Orth b₁ b₂ P))

theorem quotientA2Homeomorph_mk (b₁ b₂ : ℕ) (P : Mat n)
    (g : FactorGroup (fun i : Fin n => i.val / b₁)
                    (fun i : Fin n => i.val / b₂)) :
    ((quotientA2Homeomorph b₁ b₂ P)
      (g : OrbitCosets (fun i : Fin n => i.val / b₁)
                      (fun i : Fin n => i.val / b₂) P)).val =
      g.1.val * P * g.2.valᵀ := by
  exact quotientOrbitHomeomorph_mk P g

/-- The orbit map detects continuity; this is its quotient-map property stated
without depending on the name of a version-specific IsQuotientMap class. -/
theorem continuous_iff_after_orbitMap (P : Mat n)
    {Y : Type*} [TopologicalSpace Y] (f : MatrixOrbit block₁ block₂ P → Y) :
    Continuous f ↔ Continuous (f ∘ orbitMapToOrbit block₁ block₂ P) := by
  constructor
  · intro hf
    exact hf.comp (continuous_orbitMapToOrbit P)
  · intro hf
    exact GS.continuous_descend_compact (orbitMapToOrbit block₁ block₂ P)
      (f ∘ orbitMapToOrbit block₁ block₂ P) f
      (continuous_orbitMapToOrbit P) hf (surjective_orbitMapToOrbit P) (fun _ => rfl)

theorem closed_of_orbit_preimage_closed (P : Mat n)
    (s : Set (MatrixOrbit block₁ block₂ P))
    (hs : IsClosed (orbitMapToOrbit block₁ block₂ P ⁻¹' s)) : IsClosed s := by
  have he : s = orbitMapToOrbit block₁ block₂ P ''
      (orbitMapToOrbit block₁ block₂ P ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      exact ⟨g, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  rw [he]
  exact (hs.isCompact.image (continuous_orbitMapToOrbit P)).isClosed

theorem orbit_saturation (P : Mat n) (s : Set (FactorGroup block₁ block₂)) :
    orbitMapToOrbit block₁ block₂ P ⁻¹' (orbitMapToOrbit block₁ block₂ P '' s) =
      ⋃ h : PointStabilizer block₁ block₂ P,
        (fun g : FactorGroup block₁ block₂ => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf : orbitMap block₁ block₂ P g = orbitMap block₁ block₂ P h :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer block₁ block₂ P :=
      ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change g * (g⁻¹ * h) ∈ s
    simpa only [mul_inv_cancel_left] using hh
  · intro hg
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
    refine ⟨g * h.val, hh, ?_⟩
    apply Subtype.ext
    change (g * h.val) • P = g • P
    rw [mul_smul, show h.val • P = P from h.property]

/-- The orbit map is open onto its matrix orbit, including when the stabilizer
has positive dimension. This is stronger than compactness of its image. -/
theorem orbitMapToOrbit_isOpenMap (P : Mat n) :
    IsOpenMap (orbitMapToOrbit block₁ block₂ P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit block₁ block₂ P ⁻¹'
      (orbitMapToOrbit block₁ block₂ P '' s)) := by
    rw [orbit_saturation]
    apply isOpen_iUnion
    intro h
    exact hs.preimage (continuous_id.mul continuous_const)
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit block₁ block₂ P '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl

end GS.LieAction
