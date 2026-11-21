import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearAlgebra.DecayingInverse
def inverseDecayRate (δ γ C c : ℝ) : ℝ :=
  min (δ / 4) (γ * δ / (4 * C * c))
def InverseEntriesDecay : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    (S : Matrix X X ℝ) (γ C δ c : ℝ),
    S.IsSymm → 0 < γ → (S - γ • (1 : Matrix X X ℝ)).PosSemidef →
    0 < δ → (∀ x x' : X, |S x x'| ≤ C * Real.exp (-δ * dist x x')) →
    (∀ x : X, ∑ x' : X, Real.exp (-(δ / 2) * dist x x') ≤ c) →
    ∀ x x' : X, |S⁻¹ x x'| ≤ 2 / γ * Real.exp (-inverseDecayRate δ γ C c * dist x x')
end YangMills.Construction.LinearAlgebra.DecayingInverse
