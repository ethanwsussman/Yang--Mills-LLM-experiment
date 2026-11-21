import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def SecondDerivAlongWaveNearResponseHessian : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ n in atTop,
      ∀ (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (B : Tower.edgeFormSpace L n k k),
        (B : Tower.Edge L n k k → Matrices.ComplexMatrix2) = planeWaveValues L n k f →
        |SlopeCoefficient.secondDerivAlong (SlopeCoefficient.chainLogarithm a ρ L k) (2 * L ^ n)
              (planeWaveOnTorus f) -
            hessianOfFreeEnergy a
              (backgroundOnlyTriple (Tower.CriticalBranchResponse.meshScaledResponse L n k B))
              (backgroundOnlyTriple (Tower.CriticalBranchResponse.meshScaledResponse L n k B))| ≤
          C * (Real.sqrt (topFormNormSq (Tower.CriticalBranchResponse.periodicDefect L n k B)) *
                Real.sqrt (Real.sqrt (topFormNormSq (Tower.CriticalBranchResponse.periodicDefect L n k B)) *
                  Real.sqrt (topFormNormSq B)) +
              Real.exp (-(c * (2 * (L : ℝ) ^ n))) *
                Real.sqrt (tripleNormSq
                  (backgroundOnlyTriple (Tower.CriticalBranchResponse.meshScaledResponse L n k B))) *
                Real.sqrt (topFormNormSq (Tower.CriticalBranchResponse.periodicDefect L n k B)) +
              topFormNormSq (Tower.CriticalBranchResponse.periodicDefect L n k B))
end YangMills.Construction.RunningCouplingSlope
end
