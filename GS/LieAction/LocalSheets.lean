module

public import GS.LieAction.Nonoverlap

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit local sheets for the non-overlap O-block orbit

The open sheet at the identity consists of factor pairs with strictly positive
right-factor diagonal. A diagonal sign in the stabilizer cannot identify two
points of this sheet. Openness of the full orbit map turns injectivity on the
sheet into an actual homeomorphism onto an open subset of the matrix orbit.

These are topological local sheets and continuous local sections. No smoothness
of the inverse or Lie-group manifold structure is assumed or concluded.

-/

noncomputable section
open Matrix
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- A concrete open identity neighbourhood; no choice of coordinates on O(n)
is needed for this set. -/
def positiveRightSheet (block₁ block₂ : Fin n → ℕ) :
    Set (FactorGroup block₁ block₂) :=
  {g | ∀ i : Fin n, 0 < g.2.val i i}

theorem positiveRightSheet_open (block₁ block₂ : Fin n → ℕ) :
    IsOpen (positiveRightSheet block₁ block₂) := by
  change IsOpen {g : FactorGroup block₁ block₂ | ∀ i : Fin n, 0 < g.2.val i i}
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const
    ((continuous_apply i).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_snd)))

@[simp] theorem one_mem_positiveRightSheet (block₁ block₂ : Fin n → ℕ) :
    (1 : FactorGroup block₁ block₂) ∈ positiveRightSheet block₁ block₂ := by
  intro i
  change (0 : ℝ) < (1 : Mat n) i i
  simp

/-- The entire discrete factorization ambiguity is eliminated locally by
positivity of the right-factor diagonal. -/
theorem orbit_injective_positiveRightSheet (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    Set.InjOn (orbitMap block₁ block₂ (permMatrix σ))
      (positiveRightSheet block₁ block₂) := by
  intro g hg h hh he
  let k : PointStabilizer block₁ block₂ (permMatrix σ) :=
    ⟨g⁻¹ * h, (orbit_fibre_iff (permMatrix σ) g h).mp he⟩
  let T := rightFromStabilizer (permMatrix σ) (perm_orthogonal σ) k
  have hd : k.val.2.val = Matrix.diagonal (fun i => k.val.2.val i i) :=
    commonRight_diagonal σ hn T
  have hright : h.2.val = g.2.val * k.val.2.val := by
    have hk : h = g * k.val := by simp [k]
    exact congrArg (fun a : FactorGroup block₁ block₂ => a.2.val) hk
  have hdiag : ∀ i : Fin n, k.val.2.val i i = 1 := by
    intro i
    rcases orthogonal_diagonal_sign k.val.2.property.2 hd i with hp | hm
    · exact hp
    · have heq : h.2.val i i = -(g.2.val i i) := by
        rw [hright, hd]
        simp [Matrix.mul_apply, Matrix.diagonal, hm]
      have hg' := hg i
      have hh' := hh i
      linarith
  have hR : k.val.2.val = 1 := by
    rw [hd]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply, hdiag]
  have hL : k.val.1.val = 1 := by
    rw [(stabilizer_iff (permMatrix σ) (perm_orthogonal σ) k.val).mp k.property, hR]
    simpa using (perm_orthogonal σ).2
  have hk : k.val = 1 := Prod.ext (Subtype.ext hL) (Subtype.ext hR)
  have hgh : h = g := by
    calc
      h = g * k.val := by simp [k]
      _ = g := by rw [hk]; exact mul_one g
  exact hgh.symm

/-- The same sheet translated to an arbitrary factor pair. -/
def translatedSheet (g₀ : FactorGroup block₁ block₂) :
    Set (FactorGroup block₁ block₂) :=
  (fun g => g₀⁻¹ * g) ⁻¹' positiveRightSheet block₁ block₂

theorem translatedSheet_open (g₀ : FactorGroup block₁ block₂) :
    IsOpen (translatedSheet g₀) :=
  (positiveRightSheet_open block₁ block₂).preimage
    (continuous_const.mul continuous_id)

@[simp] theorem mem_translatedSheet_self (g₀ : FactorGroup block₁ block₂) :
    g₀ ∈ translatedSheet g₀ := by
  change g₀⁻¹ * g₀ ∈ positiveRightSheet block₁ block₂
  simp

theorem orbit_injective_translatedSheet (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (g₀ : FactorGroup block₁ block₂) :
    Set.InjOn (orbitMap block₁ block₂ (permMatrix σ)) (translatedSheet g₀) := by
  intro g hg h hh he
  have he' : orbitMap block₁ block₂ (permMatrix σ) (g₀⁻¹ * g) =
      orbitMap block₁ block₂ (permMatrix σ) (g₀⁻¹ * h) := by
    change (g₀⁻¹ * g) • permMatrix σ = (g₀⁻¹ * h) • permMatrix σ
    simp only [mul_smul]
    exact congrArg (fun X : Mat n => g₀⁻¹ • X) he
  have hgh := orbit_injective_positiveRightSheet σ hn hg hh he'
  have hc := congrArg (fun a : FactorGroup block₁ block₂ => g₀ * a) hgh
  simpa only [mul_inv_cancel_left] using hc

/-- A local topological statement used below: continuous open maps restrict to
homeomorphisms on open injectivity sets. Its conclusion uses actual subspace
topologies, not a newly transferred topology on the image. -/
def homeomorphOnOpenInjectivitySet
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (ho : IsOpenMap f)
    (s : Set X) (hs : IsOpen s) (hi : Set.InjOn f s) :
    s ≃ₜ (f '' s) := by
  let F : s → f '' s := fun x => ⟨f x.val, ⟨x.val, x.property, rfl⟩⟩
  have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
  have hFO : IsOpenMap F := by
    apply (ho s hs).isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    exact ho.comp hs.isOpenMap_subtype_val
  have hFI : Function.Injective F := by
    intro x y hxy
    exact Subtype.ext (hi x.property y.property (congrArg Subtype.val hxy))
  have hFS : Function.Surjective F := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : s ≃ (f '' s) := Equiv.ofBijective F ⟨hFI, hFS⟩
  have he : Continuous e := hF
  have hei : Continuous e.symm := by
    apply continuous_def.mpr
    intro t ht
    have heq : e.symm ⁻¹' t = e '' t := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        simpa only [Set.mem_preimage, e.symm_apply_apply] using hx
    rw [heq]
    exact hFO t ht
  exact { toEquiv := e, continuous_toFun := he, continuous_invFun := hei }

/-- A genuine local sheet of the actual orbit map, at any factorization. -/
def localOrbitHomeomorph (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (g₀ : FactorGroup block₁ block₂) :
    translatedSheet g₀ ≃ₜ
      (orbitMapToOrbit block₁ block₂ (permMatrix σ) '' translatedSheet g₀) :=
  homeomorphOnOpenInjectivitySet
    (orbitMapToOrbit block₁ block₂ (permMatrix σ))
    (continuous_orbitMapToOrbit (permMatrix σ))
    (orbitMapToOrbit_isOpenMap (permMatrix σ))
    (translatedSheet g₀) (translatedSheet_open g₀)
    (fun _ hg _ hh he => orbit_injective_translatedSheet σ hn g₀ hg hh
      (congrArg Subtype.val he))

@[simp] theorem localOrbitHomeomorph_apply (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (g₀ : FactorGroup block₁ block₂) (g : translatedSheet g₀) :
    ((localOrbitHomeomorph σ hn g₀) g).val =
      orbitMapToOrbit block₁ block₂ (permMatrix σ) g.val := rfl

theorem local_sheet_image_open (σ : Equiv.Perm (Fin n))
    (g₀ : FactorGroup block₁ block₂) :
    IsOpen (orbitMapToOrbit block₁ block₂ (permMatrix σ) '' translatedSheet g₀) :=
  orbitMapToOrbit_isOpenMap (permMatrix σ) _ (translatedSheet_open g₀)

/-- Every point of the orbit has a continuous local factorization. This does
NOT say that the factorization is differentiable. -/
theorem exists_continuous_local_section (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    ∃ V : Set (MatrixOrbit block₁ block₂ (permMatrix σ)),
      IsOpen V ∧ X ∈ V ∧
        ∃ s : V → FactorGroup block₁ block₂, Continuous s ∧
          ∀ y : V, orbitMapToOrbit block₁ block₂ (permMatrix σ) (s y) = y.val := by
  obtain ⟨g₀, rfl⟩ := surjective_orbitMapToOrbit (permMatrix σ) X
  let V := orbitMapToOrbit block₁ block₂ (permMatrix σ) '' translatedSheet g₀
  let e := localOrbitHomeomorph σ hn g₀
  refine ⟨V, local_sheet_image_open σ g₀,
    ⟨g₀, mem_translatedSheet_self g₀, rfl⟩,
    (fun y => (e.symm y).val), continuous_subtype_val.comp e.symm.continuous, ?_⟩
  intro y
  have hy := congrArg Subtype.val (e.apply_symm_apply y)
  exact hy

end GS.LieAction
