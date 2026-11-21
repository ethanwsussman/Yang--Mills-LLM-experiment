import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
def siteCube (r : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r
def bondCube (r : ℕ) : Finset IntBond := siteCube r ×ˢ Finset.univ
def plaquetteCube (r : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
  siteCube r ×ˢ Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2
def siteForwardDiff (d : Fin 4) (g : (Fin 4 → ℤ) → ℝ) (y : Fin 4 → ℤ) : ℝ := g (y + Pi.single d 1) - g y
def siteForwardDiffs (l : List (Fin 4)) (g : (Fin 4 → ℤ) → ℝ) : (Fin 4 → ℤ) → ℝ := l.foldr siteForwardDiff g
def plaquetteForwardDiff (d : Fin 4) (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) (p : (Fin 4 → ℤ) × Fin 4 × Fin 4) : ℝ :=
  F (p.1 + Pi.single d 1, p.2) - F p
def plaquetteForwardDiffs (l : List (Fin 4)) (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) :
    (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ := l.foldr plaquetteForwardDiff F
def kernelResidual (Q : IntBond → IntBond → ℝ) (v : IntBond → ℝ) (b' : IntBond) : ℝ :=
  ∑ᶠ b, v b * Q b b'
def bondCubeCard (r : ℕ) : ℝ := 4 * (2 * (r : ℝ) + 1) ^ 4
def energyStepError (c C : ℝ) (ρ r M t : ℕ) (W ε : ℝ) : ℝ :=
  bondCubeCard r * ((4 ^ M * W) * (2 ^ M * ε)) +
    bondCubeCard r * (bondCubeCard (ρ + M) * ((4 ^ M * W) ^ 2 * (C * Real.exp (-(c * t)))))
structure IsGradientBlindKernel (cK c C : ℝ) (Q : IntBond → IntBond → ℝ) : Prop where
  symm : ∀ b b', Q b b' = Q b' b
  shift_invariant : ∀ (d : Fin 4) (b b' : IntBond),
    Q (b.1 + Pi.single d 1, b.2) (b'.1 + Pi.single d 1, b'.2) = Q b b'
  decay : ∀ b b', |Q b b'| ≤ C * Real.exp (-(c * bondSupDist b b'))
  kills_gradients : ∀ (b : IntBond) (φ : (Fin 4 → ℤ) →₀ ℝ),
    HasSum (fun b' : IntBond => Q b b' * (φ b'.1 - φ (b'.1 + Pi.single b'.2 1))) 0
  coercive : ∀ (v : IntBond →₀ ℝ) (P : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4)), (∀ p ∈ P, p.2.1 < p.2.2) →
    2 * cK * ∑ p ∈ P, intCurl v p ^ 2 ≤ ∑ b ∈ v.support, ∑ b' ∈ v.support, v b * Q b b' * v b'
end YangMills.Construction.LimitForms
end
