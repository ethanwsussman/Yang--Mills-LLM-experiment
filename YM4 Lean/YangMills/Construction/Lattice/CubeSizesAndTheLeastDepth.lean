import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ComponentsOnWhichTheOperationActs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
def CubeSizesAndMinimalDelay : Prop :=
  ∀ (c : ChoiceUpToDegreeConstants) (K : ℕ) (x : ℕ → ℝ),
    Conventions.IsAdmissibleBlockingFactor c.L → 2 ≤ c.r → (∀ i ≤ K, 1 < x i) →
    (∀ k ≤ K,
      (∃ b : ℕ, Thresholds.minBlockSize c.L c.r x k = c.L ^ b) ∧
      1 ≤ Thresholds.minBlockSize c.L c.r x k ∧
      (1 ≤ k → Thresholds.minBlockSize c.L c.r x k ≤ Thresholds.minBlockSize c.L c.r x (k - 1))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ K → HasEnoughScales c x k →
      let N₀ : ℕ := Thresholds.minDelay c.L c.r x k
      let h : ℤ := (k : ℤ) - (delayAt c x k : ℤ)
      let k₀ : ℤ := Thresholds.delayLevel c.L c.r x k
      2 ≤ N₀ ∧ 0 ≤ h ∧ h < k₀ ∧ k₀ + 1 < (k : ℤ) ∧
      Thresholds.minBlockSize c.L c.r x (k₀ + 1).toNat = c.L ^ (N₀ - 1) ∧
      c.L ≤ c.L ^ (N₀ - 1) ∧
      ∀ j : ℕ, (j : ℤ) ≤ k₀ + 1 →
        Thresholds.minBlockSize c.L c.r x (k₀ + 1).toNat ≤ Thresholds.minBlockSize c.L c.r x j)
end PeriodicLattice.CubesOfStep
end YangMills.Construction
