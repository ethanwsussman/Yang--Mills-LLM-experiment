import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.SharedGasOfTwoGrounds
import YangMills.Construction.ResponseInTheExpansion.ComparisonAtOscillations
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusFields
def blockSumConstant (ρ : ℝ) : ℝ := (2 / (1 - Real.exp (-(ρ / 4)))) ^ 4
def twoGroundsOscillationComparison : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n n' : ℕ) [NeZero n] [NeZero n']
      (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ)
      (A : Finset (TorusSite n)) (A' : Finset (TorusSite n')),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * R.frameReach ≤ N →
      GroundsAgreeNear G G' Y Y' N → BlockSetsAgreeNear A A' Y Y' N →
      ∃ g : SharedInnerGas G G' Y Y' N (N - R.frameReach - 1) A A',
        (∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
          G'.pairConstraint.IsAdmissible (g.extendSecond τ)) ∧
        ∀ (F : G.Config → ℝ) (F' : G'.Config → ℝ) (K a : ℝ), 0 ≤ a →
          G.pairConstraint.OscillationControlled (G.coreWeightFrom Y) K F →
          G'.pairConstraint.OscillationControlled (G'.coreWeightFrom Y') K F' →
          (∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
            |F (g.extendFirst τ) - F' (g.extendSecond τ)| ≤ a) →
          F G.allVacant = F' G'.allVacant →
          |G.expectation A F - G'.expectation A' F'| ≤
            (16 * K * Real.exp (-(2 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) +
              a * Real.exp (T.rt / 2 ^ 8 * (N : ℝ))) *
              (Real.exp (-(8 * T.gasRate * R.coupling)) * blockSumConstant (T.rt / 2 ^ 8))
end YangMills.Construction.ResponseInTheExpansion
end
