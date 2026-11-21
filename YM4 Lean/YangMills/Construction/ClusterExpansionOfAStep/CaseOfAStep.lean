import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts
variable (S : StepSetup) {n : ℕ} [NeZero n]
open Classical in
def configurationWeight (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * S.params.side)))
    (Y : Finset (TorusSite (n * S.params.side))) (b : BaseChoice S.params.side n)
    (W : TorusField (n * S.params.side)) (ω : Y → S.labels.Ω) : ENNReal :=
  if IsHullState S.params S.range W Y then ENNReal.ofReal (stepWeight S C V W Y ω bad b) else 0
open Classical in
def configurationMass (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * S.params.side)))
    (Y : Finset (TorusSite (n * S.params.side))) (b : BaseChoice S.params.side n)
    (q : CoarseState S n) : ENNReal :=
  ∫⁻ W, ∫⁻ ν : q.unlabelled Y → S.labels.Ω,
      (if IsHullState S.params S.range (q.fieldWithStoredLinks W) Y ∧
          coarseStateOf S C (q.fieldWithStoredLinks W) Y (q.fillLabels Y ν) bad b = q then
        ENNReal.ofReal (stepWeight S C V (q.fieldWithStoredLinks W) Y (q.fillLabels Y ν) bad b) else 0)
      ∂(Measure.pi fun _ => S.labels.μ) ∂(fieldHaar (n * S.params.side))
end ClusterExpansionOfAStep
end YangMills.Construction
end
