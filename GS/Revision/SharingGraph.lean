module

public import GS.Sharing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Grounded incidence systems for tied scalar parameters

Rows describe the actual four possibilities: no parameter, only a left
parameter, only a right parameter, or one of each. Every row is retained.
Negating the right parameters turns the synthesis matrix into an incidence
matrix with a distinguished ground vertex.

The matrix/energy/kernel results below concern this explicit row model. They
do not silently identify arbitrary matrix-sharing patterns with unsigned
incidence data: that indexing bridge must provide these rows and their signs.
In particular, a general permutation can introduce signs absent for the
order-preserving within-block perfect shuffle.

New scripts; no Lean compiler was available in the current execution.
-/
noncomputable section
open scoped BigOperators
namespace GS.Revision.SharingGraph

inductive Row (α β : Type*) where
  | empty : Row α β
  | left : α → Row α β
  | right : β → Row α β
  | both : α → β → Row α β

variable {α β ε : Type*}

abbrev Vertex (α β : Type*) := Option (Sum α β)

def source : Row α β → Vertex α β
  | .empty => none
  | .left i => some (.inl i)
  | .right _ => none
  | .both i _ => some (.inl i)

def target : Row α β → Vertex α β
  | .empty => none
  | .left _ => none
  | .right j => some (.inr j)
  | .both _ j => some (.inr j)

def potential (x : Sum α β → ℝ) : Vertex α β → ℝ
  | none => 0
  | some v => x v

def sharedEval (r : Row α β) (x : Sum α β → ℝ) : ℝ :=
  match r with
  | .empty => 0
  | .left i => x (.inl i)
  | .right j => x (.inr j)
  | .both i j => x (.inl i) + x (.inr j)

def flipRight (x : Sum α β → ℝ) : Sum α β → ℝ
  | .inl i => x (.inl i)
  | .inr j => -x (.inr j)

def incidenceEval (r : Row α β) (x : Sum α β → ℝ) : ℝ :=
  potential x (source r) - potential x (target r)

theorem flipRight_involutive (x : Sum α β → ℝ) : flipRight (flipRight x) = x := by
  funext v
  cases v <;> simp [flipRight]

/-- This change of variables preserves the full objective, not just overlap rows. -/
theorem shared_flip_eq_incidence (r : Row α β) (x : Sum α β → ℝ) :
    sharedEval r (flipRight x) = incidenceEval r x := by
  cases r <;> simp [sharedEval, flipRight, incidenceEval, potential, source, target,
    sub_eq_add_neg]

theorem incidence_add (r : Row α β) (x y : Sum α β → ℝ) :
    incidenceEval r (x + y) = incidenceEval r x + incidenceEval r y := by
  cases r <;> simp [incidenceEval, potential, source, target] <;> ring

theorem incidence_smul (r : Row α β) (a : ℝ) (x : Sum α β → ℝ) :
    incidenceEval r (a • x) = a * incidenceEval r x := by
  cases r <;> simp [incidenceEval, potential, source, target] <;> ring

def synthesis (rows : ε → Row α β) : (Sum α β → ℝ) →ₗ[ℝ] (ε → ℝ) where
  toFun x e := incidenceEval (rows e) x
  map_add' x y := by funext e; exact incidence_add _ _ _
  map_smul' a x := by funext e; exact incidence_smul _ _ _

section Finite
variable [Fintype α] [Fintype β] [Fintype ε]
variable [DecidableEq α] [DecidableEq β]

def indicator (u : Vertex α β) (v : Sum α β) : ℝ :=
  if u = some v then 1 else 0

def coefficient (r : Row α β) (v : Sum α β) : ℝ :=
  indicator (source r) v - indicator (target r) v

theorem indicator_sum (u : Vertex α β) (x : Sum α β → ℝ) :
    (∑ v, indicator u v * x v) = potential x u := by
  cases u with
  | none => simp [indicator, potential]
  | some v => simp [indicator, potential]

theorem incidence_as_sum (r : Row α β) (x : Sum α β → ℝ) :
    incidenceEval r x = ∑ v, coefficient r v * x v := by
  simp only [coefficient, sub_mul, Finset.sum_sub_distrib]
  rw [indicator_sum, indicator_sum]
  rfl

def incidenceMatrix (rows : ε → Row α β) : Matrix ε (Sum α β) ℝ :=
  fun e v => coefficient (rows e) v

theorem incidenceMatrix_mulVec (rows : ε → Row α β) (x : Sum α β → ℝ) :
    (incidenceMatrix rows).mulVec x = synthesis rows x := by
  funext e
  exact (incidence_as_sum (rows e) x).symm

def adjoint (rows : ε → Row α β) (y : ε → ℝ) : Sum α β → ℝ :=
  fun v => ∑ e, coefficient (rows e) v * y e

theorem adjoint_identity (rows : ε → Row α β)
    (x : Sum α β → ℝ) (y : ε → ℝ) :
    (∑ v, x v * adjoint rows y v) =
      ∑ e, incidenceEval (rows e) x * y e := by
  simp only [adjoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [incidence_as_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  ring

def laplacian (rows : ε → Row α β) (x : Sum α β → ℝ) : Sum α β → ℝ :=
  adjoint rows (synthesis rows x)

def energy (rows : ε → Row α β) (x : Sum α β → ℝ) : ℝ :=
  ∑ e, (incidenceEval (rows e) x)^2

theorem energy_identity (rows : ε → Row α β) (x : Sum α β → ℝ) :
    (∑ v, x v * laplacian rows x v) = energy rows x := by
  rw [laplacian, adjoint_identity]
  change (∑ e, incidenceEval (rows e) x * incidenceEval (rows e) x) =
    ∑ e, (incidenceEval (rows e) x)^2
  simp only [pow_two]

theorem energy_nonnegative (rows : ε → Row α β) (x : Sum α β → ℝ) :
    0 ≤ energy rows x :=
  Finset.sum_nonneg (fun e _ => sq_nonneg _)

theorem energy_zero_iff (rows : ε → Row α β) (x : Sum α β → ℝ) :
    energy rows x = 0 ↔ ∀ e, incidenceEval (rows e) x = 0 := by
  constructor
  · intro h e
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e (_ : e ∈ (Finset.univ : Finset ε)) =>
        sq_nonneg (incidenceEval (rows e) x))).mp h e (Finset.mem_univ e)
    exact sq_eq_zero_iff.mp hh
  · intro h
    simp [energy, h]

theorem laplacian_kernel_iff (rows : ε → Row α β) (x : Sum α β → ℝ) :
    laplacian rows x = 0 ↔ ∀ e, incidenceEval (rows e) x = 0 := by
  constructor
  · intro h
    apply (energy_zero_iff rows x).mp
    rw [← energy_identity, h]
    simp
  · intro h
    funext v
    simp [laplacian, adjoint, synthesis, h]

/-- Weighted parameter norms, used for multiplicities, are unchanged by
negating the right-hand variables. No positivity is needed for this identity. -/
theorem flipRight_weighted_sq (w : Sum α β → ℝ) (x : Sum α β → ℝ) :
    (∑ v, w v * (flipRight x v)^2) = ∑ v, w v * (x v)^2 := by
  apply Finset.sum_congr rfl
  intro v hv
  cases v <;> simp [flipRight]

/-- Full residual objective: left-only and right-only rows remain present. -/
theorem objective_change_of_variables (rows : ε → Row α β)
    (z : ε → ℝ) (x : Sum α β → ℝ) :
    (∑ e, (z e - sharedEval (rows e) (flipRight x))^2) =
      ∑ e, (z e - incidenceEval (rows e) x)^2 := by
  simp only [shared_flip_eq_incidence]

end Finite

/-- The undirected connectivity relation generated by all rows, including
edges to the ground vertex. -/
inductive ConnectedBy (rows : ε → Row α β) : Vertex α β → Vertex α β → Prop where
  | refl (u) : ConnectedBy rows u u
  | edge (e) : ConnectedBy rows (source (rows e)) (target (rows e))
  | symm {u v} : ConnectedBy rows u v → ConnectedBy rows v u
  | trans {u v w} : ConnectedBy rows u v → ConnectedBy rows v w → ConnectedBy rows u w

theorem equal_potential_of_connected (rows : ε → Row α β) (x : Sum α β → ℝ)
    (hx : ∀ e, incidenceEval (rows e) x = 0)
    {u v : Vertex α β} (h : ConnectedBy rows u v) :
    potential x u = potential x v := by
  induction h with
  | refl u => rfl
  | edge e => exact sub_eq_zero.mp (hx e)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A grounded connected pattern has no infinitesimal gauge ambiguity. -/
theorem zero_of_all_grounded (rows : ε → Row α β) (x : Sum α β → ℝ)
    (hx : ∀ e, incidenceEval (rows e) x = 0)
    (hg : ∀ v, ConnectedBy rows (some v) none) : x = 0 := by
  funext v
  exact equal_potential_of_connected rows x hx (hg v)

end GS.Revision.SharingGraph
