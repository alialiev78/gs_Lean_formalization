module

public import GS.Fibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A section of the simultaneous-antipodal quotient projection

This is the algebraic quotient/retraction step in the new all-parity argument.
It constructs the section, rather than assuming that one exists, for
(S¹ × S^(d+1))/± → S¹/±, for every d : Nat. The equatorial map between
spheres is also proved continuous below.

This file does NOT prove the singular/local homology computation, the quotient
identification with the rank-one link, or the nonmanifold theorem. In particular,
a set-theoretic split surjection alone is not a homological obstruction.
The missing topological steps are recorded as goals, not imported as assumptions.

-/
noncomputable section
open scoped BigOperators
namespace GS.Revision.Projective

structure Involution (X : Type*) where
  flip : X → X
  twice : Function.Involutive flip

variable {X Y : Type*}

def orbitSetoid (J : Involution X) : Setoid X where
  r x y := y = x ∨ y = J.flip x
  iseqv := {
    refl := fun x => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (J.twice x).symm
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | hxy
      · simpa only [hxy] using hyz
      · rcases hyz with hyz | hyz
        · exact Or.inr (hyz.trans hxy)
        · left
          rw [hyz, hxy]
          exact J.twice x }

abbrev Orbit (J : Involution X) := Quotient (orbitSetoid J)

def orbitMap (J : Involution X) (K : Involution Y) (f : X → Y)
    (hf : ∀ x, f (J.flip x) = K.flip (f x)) : Orbit J → Orbit K :=
  Quotient.map f (by
    intro x y h
    change y = x ∨ y = J.flip x at h
    change f y = f x ∨ f y = K.flip (f x)
    rcases h with h | h
    · exact Or.inl (congrArg f h)
    · right; rw [h, hf])

def productInvolution (J : Involution X) (K : Involution Y) : Involution (X × Y) where
  flip p := (J.flip p.1, K.flip p.2)
  twice p := by
    apply Prod.ext
    · exact J.twice p.1
    · exact K.twice p.2

def quotientProjection (J : Involution X) (K : Involution Y) :
    Orbit (productInvolution J K) → Orbit J :=
  orbitMap (productInvolution J K) J Prod.fst (fun _ => rfl)

def quotientSection (J : Involution X) (K : Involution Y) (j : X → Y)
    (hj : ∀ x, j (J.flip x) = K.flip (j x)) :
    Orbit J → Orbit (productInvolution J K) :=
  orbitMap J (productInvolution J K) (fun x => (x, j x)) (by
    intro x
    apply Prod.ext
    · rfl
    · exact hj x)

theorem projection_section (J : Involution X) (K : Involution Y) (j : X → Y)
    (hj : ∀ x, j (J.flip x) = K.flip (j x)) (q : Orbit J) :
    quotientProjection J K (quotientSection J K j hj q) = q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

theorem quotientSection_injective (J : Involution X) (K : Involution Y) (j : X → Y)
    (hj : ∀ x, j (J.flip x) = K.flip (j x)) :
    Function.Injective (quotientSection J K j hj) := by
  intro u v h
  have hp := congrArg (quotientProjection J K) h
  simpa only [projection_section] using hp

theorem quotientProjection_surjective (J : Involution X) (K : Involution Y) (j : X → Y)
    (hj : ∀ x, j (J.flip x) = K.flip (j x)) :
    Function.Surjective (quotientProjection J K) := by
  intro q
  exact ⟨quotientSection J K j hj q, projection_section J K j hj q⟩

/-- Unit spheres use the squared Euclidean norm, not the default Pi sup norm. -/
abbrev UnitVector (n : ℕ) := {u : Fin n → ℝ // ∑ i, (u i)^2 = 1}

def sphereInvolution (n : ℕ) : Involution (UnitVector n) where
  flip u := ⟨-u.val, by simpa using u.property⟩
  twice u := by apply Subtype.ext; simp

/-- Pad a unit circle vector with d zero coordinates. -/
def circleEquator (d : ℕ) (u : UnitVector 2) : UnitVector (d + 2) :=
  ⟨Fin.cases (u.val 0) (Fin.cases (u.val 1) (fun _ : Fin d => 0)), by
    have hu := u.property
    simpa [Fin.sum_univ_succ] using hu⟩

theorem circleEquator_equivariant (d : ℕ) (u : UnitVector 2) :
    circleEquator d ((sphereInvolution 2).flip u) =
      (sphereInvolution (d + 2)).flip (circleEquator d u) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · rfl
  · rfl
  · simp [circleEquator, sphereInvolution]

theorem continuous_circleEquator (d : ℕ) : Continuous (circleEquator d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · change Continuous (fun u : UnitVector 2 => u.val 0)
    exact (continuous_apply 0).comp continuous_subtype_val
  · change Continuous (fun u : UnitVector 2 => u.val 1)
    exact (continuous_apply 1).comp continuous_subtype_val
  · change Continuous (fun _ : UnitVector 2 => (0 : ℝ))
    exact continuous_const

/-- The actual circle-to-link section for every sphere dimension at least one. -/
def circleLinkSection (d : ℕ) :
    Orbit (sphereInvolution 2) →
      Orbit (productInvolution (sphereInvolution 2) (sphereInvolution (d + 2))) :=
  quotientSection _ _ (circleEquator d) (circleEquator_equivariant d)

theorem circleLink_projection_section (d : ℕ) (q : Orbit (sphereInvolution 2)) :
    quotientProjection (sphereInvolution 2) (sphereInvolution (d + 2))
      (circleLinkSection d q) = q :=
  projection_section _ _ _ _ q

end GS.Revision.Projective
