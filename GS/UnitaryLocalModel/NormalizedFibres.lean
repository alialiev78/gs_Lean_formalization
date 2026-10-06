module

public import GS.UnitaryLocalModel.PolarTwo
public import GS.UnitaryLocalModel.ChartFibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact fibres including the normalized outer unitary factors

Positive first-row and first-column middle blocks determine every outer unitary
factor, once the right anchor is fixed to the identity. The residual equality
is exactly equality of the complete middle family. These statements retain
all outer factors and do not restrict the image to a selected middle slice.
-/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

variable {q : ℕ}

/-- Reconstruct the entire block array from normalized factors. -/
def normalizedBlockImage (L R : Fin q → CMat 2)
    (N : Fin q → Fin q → CMat 2) : Fin q → Fin q → CMat 2 :=
  fun i j => L i * N i j * R j

/-- Positivity is measured relative to the reference anchor entries. -/
def NormalizedPositiveAnchors (Q : CMat q) (o : Fin q)
    (N : Fin q → Fin q → CMat 2) : Prop :=
  (∀ i, ((Q i o)⁻¹ • N i o).PosDef) ∧
  (∀ j, ((Q o j)⁻¹ • N o j).PosDef)

private theorem cancel_unitary_left (U A B : CMat 2) (hU : GS.Unitary U)
    (he : U*A = U*B) : A = B := by
  have h := congrArg (fun T => Uᴴ*T) he
  simpa only [← Matrix.mul_assoc, hU.1, Matrix.one_mul] using h

private theorem cancel_unitary_right (U A B : CMat 2) (hU : GS.Unitary U)
    (he : A*U = B*U) : A = B := by
  have h := congrArg (fun T => T*Uᴴ) he
  simpa only [Matrix.mul_assoc, hU.2, Matrix.mul_one] using h

/-- Recover both complete outer tuples and every middle block from the image. -/
theorem normalized_outer_fibres (Q : CMat q) (o : Fin q)
    (L R L' R' : Fin q → CMat 2) (N N' : Fin q → Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
    (hL' : ∀ i, GS.Unitary (L' i)) (hR' : ∀ j, GS.Unitary (R' j))
    (hRo : R o = 1) (hRo' : R' o = 1)
    (hN : NormalizedPositiveAnchors Q o N)
    (hN' : NormalizedPositiveAnchors Q o N')
    (he : normalizedBlockImage L R N = normalizedBlockImage L' R' N') :
    L = L' ∧ R = R' ∧ N = N' := by
  have hblocks (i j : Fin q) : L i * N i j * R j = L' i * N' i j * R' j :=
    congrFun (congrFun he i) j
  have hLL : L = L' := by
    funext i
    have hi : L i * N i o = L' i * N' i o := by
      simpa only [hRo, hRo', Matrix.mul_one] using hblocks i o
    have hscaled : L i * ((Q i o)⁻¹ • N i o) =
        L' i * ((Q i o)⁻¹ • N' i o) := by
      simpa only [Matrix.mul_smul] using congrArg (fun T => (Q i o)⁻¹ • T) hi
    exact (positive_polar_unique _ _ _ _ (hL i) (hL' i) (hN.1 i) (hN'.1 i) hscaled).1
  have hRR : R = R' := by
    funext j
    have hj : N o j * R j = N' o j * R' j := by
      apply cancel_unitary_left (L o) _ _ (hL o)
      simpa only [Matrix.mul_assoc, hLL] using hblocks o j
    have hscaled : ((Q o j)⁻¹ • N o j) * R j =
        ((Q o j)⁻¹ • N' o j) * R' j := by
      simpa only [Matrix.smul_mul] using congrArg (fun T => (Q o j)⁻¹ • T) hj
    exact (positive_polar_unique_right _ _ _ _ (hR j) (hR' j)
      (hN.2 j) (hN'.2 j) hscaled).1
  refine ⟨hLL, hRR, ?_⟩
  funext i j
  apply cancel_unitary_right (R j) _ _ (hR j)
  apply cancel_unitary_left (L i) _ _ (hL i)
  simpa only [Matrix.mul_assoc, hLL, hRR] using hblocks i j

/-- The full normalized fibre relation, including all outer coordinates. -/
theorem normalized_outer_fibres_iff (Q : CMat q) (o : Fin q)
    (L R L' R' : Fin q → CMat 2) (N N' : Fin q → Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
    (hL' : ∀ i, GS.Unitary (L' i)) (hR' : ∀ j, GS.Unitary (R' j))
    (hRo : R o = 1) (hRo' : R' o = 1)
    (hN : NormalizedPositiveAnchors Q o N)
    (hN' : NormalizedPositiveAnchors Q o N') :
    normalizedBlockImage L R N = normalizedBlockImage L' R' N' ↔
      L = L' ∧ R = R' ∧ N = N' := by
  constructor
  · exact normalized_outer_fibres Q o L R L' R' N N' hL hR hL' hR' hRo hRo' hN hN'
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Exact outer-plus-cone coordinates after any injective local middle chart. -/
theorem normalized_chart_fibres_on {d : ℕ}
    (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → (Fin q × Fin q → ℂ))
    (U : Set (Fin d → ℝ)) (hψ : Set.InjOn ψ U)
    (L R L' R' : Fin q → CMat 2) (c z c' z' : Fin d → ℝ)
    (u v : AxisVector)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
    (hL' : ∀ i, GS.Unitary (L' i)) (hR' : ∀ j, GS.Unitary (R' j))
    (hRo : R o = 1) (hRo' : R' o = 1)
    (hcp : c+z ∈ U) (hcm : c-z ∈ U)
    (hcp' : c'+z' ∈ U) (hcm' : c'-z' ∈ U)
    (hu : OnSphere u) (hv : OnSphere v)
    (hN : NormalizedPositiveAnchors Q o (fun i j => chartMiddle ψ c z u (i,j)))
    (hN' : NormalizedPositiveAnchors Q o (fun i j => chartMiddle ψ c' z' v (i,j))) :
    normalizedBlockImage L R (fun i j => chartMiddle ψ c z u (i,j)) =
        normalizedBlockImage L' R' (fun i j => chartMiddle ψ c' z' v (i,j)) ↔
      L = L' ∧ R = R' ∧ c = c' ∧ sphereOuter u z = sphereOuter v z' := by
  rw [normalized_outer_fibres_iff Q o L R L' R' _ _ hL hR hL' hR' hRo hRo' hN hN']
  have he : (fun i j => chartMiddle ψ c z u (i,j)) =
      (fun i j => chartMiddle ψ c' z' v (i,j)) ↔
      chartMiddle ψ c z u = chartMiddle ψ c' z' v := by
    constructor
    · intro h
      funext p
      exact congrFun (congrFun h p.1) p.2
    · intro h
      exact congrArg (fun F => fun i j => F (i,j)) h
  rw [he, chartMiddle_fibres_on ψ U hψ c z c' z' hcp hcm hcp' hcm' hu hv]

end GS.UnitaryLocalModel
