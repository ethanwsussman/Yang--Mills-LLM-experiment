import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BlockOrder
open TorusFields MarkedIntegrals
def RandomOrderFacts : Prop :=
  ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (randomOrderLaw n) ∧
    (∀ᵐ u ∂randomOrderLaw n, Function.Injective u) ∧
    (∀ (f : Finset (TorusSite n) → ℝ) (Y : TorusSite n),
      Integrable (fun u => f (precedingBlocks u Y)) (randomOrderLaw n)) ∧
    ∀ (K : Type) [Fintype K] (κ : K → TorusSite n), Function.Injective κ →
      Measure.map (fun u : TorusSite n → ℝ => u ∘ κ) (randomOrderLaw n) =
        Measure.pi fun _ : K => volume.restrict (Set.Icc (0 : ℝ) 1)
end YangMills.Construction.BlockOrder
end
