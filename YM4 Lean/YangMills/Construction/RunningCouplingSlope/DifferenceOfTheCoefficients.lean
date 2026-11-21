import YangMills.Construction.OneLoopLaw.OneLoopLawForTheNormalisers
import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def CoefficientDifferenceIsSecondMoment : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ κ : (Fin 4 → ℤ) → ℝ, IsDifferenceKernelLimit a L k κ →
      ∀ ρ v : ℝ, 0 < ρ → ρ ≤ 1 →
        SlopeCoefficient.HasSlopeCoefficient Filter.atTop (SlopeCoefficient.chainLogarithm a ρ L k) v →
        HasSum (fun x : Fin 4 → ℤ => -(1 / 2) * κ x * ((x 0 : ℤ) : ℝ) ^ 2)
          (v - ∑ i ∈ Finset.range k, OneLoopLaw.NormaliserLaw.normaliserStiffness hL i)
end YangMills.Construction.RunningCouplingSlope
end
