import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def DualLatticeDensity.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ a b : ℕ, 1 ≤ a → a ≤ b →
      (dualLattice (2 * L ^ a) : Set InfiniteLattice.AmbientSpace) ⊆ dualLattice (2 * L ^ b)) ∧
    Dense (⋃ (n : ℕ) (_ : 1 ≤ n), (dualLattice (2 * L ^ n) : Set InfiniteLattice.AmbientSpace)) ∧
    ∀ (f : InfiniteLattice.AmbientSpace → ℂ) (a : ℕ) (e : ℕ → ℝ), Continuous f → 1 ≤ a →
      (∀ n, a ≤ n → 0 ≤ e n) → Tendsto e atTop (𝓝 0) →
      (∀ n, a ≤ n → ∀ q ∈ dualLattice (2 * L ^ n), ‖f q‖ ≤ e n) →
      (∀ x, f x = 0) ∧
      ∀ (w : ℝ) (F : (Fin 4 → ℂ) → ℂ), 0 < w →
        (∃ U : Set (Coordinates.ComplexCoordinates 4), imStrip w ⊆ U ∧
          Coordinates.ComplexCoordinates.IsHolomorphicIn U
            fun (z : Coordinates.ComplexCoordinates 4) (_ : Fin 1) => F z) →
        (∀ x, F (toComplexVec x) = f x) →
        ∀ z ∈ imStrip w, F z = 0
end YangMills.Construction.PeriodicOperators
end
