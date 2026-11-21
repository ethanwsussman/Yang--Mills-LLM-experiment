import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepSettings
open TorusFields TorusLumps
def coarseStatesSumStatement : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ V : TorusField n,
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, ENNReal.ofReal (coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      ENNReal.ofReal (kernelImage R.params R.coupling R.functional n V)
end YangMills.Construction.StepSettings
end
