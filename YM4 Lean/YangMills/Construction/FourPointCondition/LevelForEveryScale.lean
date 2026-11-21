import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.PeriodicLattice YangMills.Construction.TorusLumps
namespace YangMills.Construction.FourPointBounds
def ScaleLevelExists : Prop :=
  ∀ (q : StepParameters) (X n₀ d : ℝ) (K : ℕ) (x : ℕ → ℝ), q.Admissible → 16 ≤ X → q.B ≤ X → 1 ≤ n₀ →
    (∀ u : ℝ, X ≤ u → 2 ^ 14 * (q.side : ℝ) ^ 2 * (clusterRange u : ℝ) ≤ u ^ ((1 : ℝ) / 90)) →
    2 * X + 4 * q.B ≤ x 0 →
    (∀ t : ℕ, (∀ j ≤ t, X ≤ x j) → |x (t + 1) - x t| ≤ 2 * q.B) →
    n₀ ≤ d / meshSize q.side (K : ℤ) →
    (∀ t : ℕ, (∀ j ≤ t, X ≤ x j) → x (t + 1) < X →
      d / meshSize q.side ((K : ℤ) - (t : ℤ)) < 2 ^ 12 * (q.side : ℝ) * (clusterRange (x t) : ℝ)) →
    ∃ (k : ℕ) (e : ℝ), (∀ j ≤ k, X ≤ x j) ∧
      ((2 ^ 12 * (q.side : ℝ) * (clusterRange (x k) : ℝ) ≤ d / meshSize q.side ((K : ℤ) - (k : ℤ)) ∧
          d / meshSize q.side ((K : ℤ) - (k : ℤ)) ≤ x k ^ ((1 : ℝ) / 90) ∧ e = 0) ∨
        (k = 0 ∧ 1 ≤ d / meshSize q.side ((K : ℤ) - (k : ℤ)) ∧
          d / meshSize q.side ((K : ℤ) - (k : ℤ)) ≤ x k ^ ((1 : ℝ) / 90) ∧
          e = 1 / (d / meshSize q.side ((K : ℤ) - (k : ℤ))))) ∧
      0 ≤ e ∧ e ≤ 1 / n₀ ∧ e ≤ meshSize q.side (K : ℤ) / d
end YangMills.Construction.FourPointBounds
end
