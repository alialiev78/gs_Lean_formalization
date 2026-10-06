module

public import GS.SharedGeometry.Directions
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical continuous projector on each shared orbit

The projector is a function of the matrix point and ambient vector, not of a
chosen factorization.  It equals the existing exact coupled shared projection
at every valid factor pair.  Joint continuity on the actual matrix orbit is
proved by descent through the open orbit map; no continuous choice of factors
and no smooth shared-orbit atlas is assumed.

These statements concern the actual generator range.  Calling it the full
manifold tangent space still requires the shared-orbit atlas.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (right left : Pattern n) (X : Mat n) : Mat n →L[ℝ] Mat n :=
  frobProjection (pointDirections right left X)

theorem pointProjection_mem (X Z : Mat n) :
    pointProjection right left X Z ∈ pointDirections right left X :=
  frobProjection_mem _ _

theorem pointProjection_of_mem (X Y : Mat n)
    (hY : Y ∈ pointDirections right left X) : pointProjection right left X Y = Y :=
  frobProjection_of_mem _ _ hY

theorem pointProjection_normal (X Z Y : Mat n)
    (hY : Y ∈ pointDirections right left X) :
    frobInner (Z - pointProjection right left X Z) Y = 0 :=
  frobProjection_normal _ _ _ hY

theorem pointProjection_self_adjoint (X Z Y : Mat n) :
    frobInner (pointProjection right left X Z) Y =
      frobInner Z (pointProjection right left X Y) :=
  frobProjection_self_adjoint _ _ _

@[simp] theorem pointProjection_idempotent (X Z : Mat n) :
    pointProjection right left X (pointProjection right left X Z) =
      pointProjection right left X Z :=
  pointProjection_of_mem X _ (pointProjection_mem X Z)

/-- The full factor-based least-squares solution descends to the matrix point. -/
theorem exactSharedProjection_eq_pointProjection (P L R Z : Mat n)
    (hP : Orthogonal P)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R) :
    exactSharedProjection right.size left.size right.label left.label P L R Z =
      pointProjection right left (product2 L P R) Z := by
  let X := product2 L P R
  let Y := exactSharedProjection right.size left.size right.label left.label P L R Z
  let p := pointProjection right left X Z
  have hY : Y ∈ pointDirections right left X :=
    (sharedDirection_iff_pointDirections P L R Y hL hR).mp
      (exactSharedProjection_in_direction right.size left.size right.label left.label
        P L R Z hP hL.2.1 hR.2.1)
  have hp : p ∈ pointDirections right left X := pointProjection_mem X Z
  have hmin : frobSq (Z - Y) ≤ frobSq (Z - p) :=
    exactSharedProjection_minimizes right.size left.size right.label left.label
      P L R Z p hP hL.2.1 hR.2.1
      ((sharedDirection_iff_pointDirections P L R p hL hR).mpr hp)
  have hpy : frobSq (Z - Y) = frobSq (Z - p) + frobSq (p - Y) :=
    frobProjection_pythagorean (pointDirections right left X) Z Y hY
  have hz : frobSq (p - Y) = 0 := by linarith [frobSq_nonneg (p - Y)]
  exact (sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hz)).symm

/-- No minimum-norm lift or representative selection is needed for uniqueness
of the synthesized projection, including simultaneous sharing and overlap. -/
theorem exactSharedProjection_factor_independent (P L R L' R' Z : Mat n)
    (hP : Orthogonal P)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R)
    (hL' : SharedOrthogonalFactor left.size left.label L')
    (hR' : SharedOrthogonalFactor right.size right.label R')
    (hX : product2 L P R = product2 L' P R') :
    exactSharedProjection right.size left.size right.label left.label P L R Z =
      exactSharedProjection right.size left.size right.label left.label P L' R' Z := by
  rw [exactSharedProjection_eq_pointProjection P L R Z hP hL hR,
    exactSharedProjection_eq_pointProjection P L' R' Z hP hL' hR', hX]

/-- Equivariance follows from the actual action isometry and the full range,
not an entrywise overlap mask. -/
theorem pointProjection_equivariant (g : Factors right left) (X Z : Mat n) :
    pointProjection right left (g • X) (g • Z) =
      g • pointProjection right left X Z := by
  apply frobProjection_unique_normal (pointDirections right left (g • X)) (g • Z)
  · exact action_mem_pointDirections g X _ (pointProjection_mem X Z)
  · intro Y hY
    have hback : g⁻¹ • Y ∈ pointDirections right left X := by
      simpa only [inv_smul_smul] using
        action_mem_pointDirections g⁻¹ (g • X) Y hY
    have he := action_frobInner g (Z - pointProjection right left X Z) (g⁻¹ • Y)
    rw [show g • (Z - pointProjection right left X Z) =
        g • Z - g • pointProjection right left X Z from
          (actionLinearEquiv g).map_sub _ _, smul_inv_smul] at he
    rw [he]
    exact pointProjection_normal X Z _ hback

/-- Agreement with the smooth formula upstairs on the shared factor group. -/
theorem pointProjection_on_factors (P : Mat n) (hP : Orthogonal P)
    (g : Factors right left) (Z : Mat n) :
    pointProjection right left (g • P) Z =
      exactSharedProjection right.size left.size right.label left.label
        P (Factor.matrix g.1) (Factor.matrix g.2)ᵀ Z := by
  exact (exactSharedProjection_eq_pointProjection P _ _ Z hP
    (Factor.matrix_shared g.1) (shared_factor_transpose (Factor.matrix_shared g.2))).symm

/-- Descent on orbit x ambient matrices.  The open quotient argument avoids
any unproved continuous or smooth local choice of a factorization. -/
theorem continuous_pointProjection (P : Mat n) (hP : Orthogonal P) :
    Continuous (fun p : MatrixOrbit right left P × Mat n =>
      pointProjection right left p.1.val p.2) := by
  let q : Factors right left × Mat n → MatrixOrbit right left P × Mat n :=
    Prod.map (orbitMapToOrbit right left P) id
  have hqc : Continuous q := (continuous_orbitMapToOrbit P).prodMap continuous_id
  have hqo : IsOpenMap q := (orbitMapToOrbit_isOpenMap P).prodMap IsOpenMap.id
  have hqs : Function.Surjective q := by
    rintro ⟨X, Z⟩
    obtain ⟨g, hg⟩ := surjective_orbitMapToOrbit P X
    exact ⟨(g, Z), Prod.ext hg rfl⟩
  apply (hqo.isQuotientMap hqc hqs).continuous_iff.mpr
  have hc : Continuous (fun p : Factors right left × Mat n =>
      (Factor.matrix p.1.1, ((Factor.matrix p.1.2)ᵀ, p.2))) :=
    (Factor.continuous_matrix.comp (continuous_fst.comp continuous_fst)).prodMk
      ((GS.LieAction.continuous_matrix_transpose
        (Factor.continuous_matrix.comp (continuous_snd.comp continuous_fst))).prodMk
        continuous_snd)
  have hf := (exactSharedProjection_smooth right.size left.size
    right.label left.label P).continuous.comp hc
  have he : ((fun p : MatrixOrbit right left P × Mat n =>
      pointProjection right left p.1.val p.2) ∘ q) =
      (fun p : Factors right left × Mat n => exactSharedProjection right.size left.size
        right.label left.label P (Factor.matrix p.1.1) (Factor.matrix p.1.2)ᵀ p.2) := by
    funext p
    exact pointProjection_on_factors P hP p.1 p.2
  rw [he]
  exact hf

/-- The canonical projector is realized by differentiable tied factors based
at any chosen representative of the same point. -/
theorem pointProjection_is_factor_velocity (P L R Z : Mat n)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R) :
    SharedFactorVelocity right.size left.size right.label left.label P L R
      (pointProjection right left (product2 L P R) Z) :=
  (sharedFactorVelocity_iff_pointDirections P L R _ hL hR).mpr
    (pointProjection_mem _ _)

end GS.SharedGeometry
