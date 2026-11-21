import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def IsEnergyMinimizerOver (a : ℝ) (L t n : ℕ) (V : TorusFields.TorusField n)
    (W : (TorusFields.torusFrame L t n).GaugeField (TorusFields.torusFrame L t n).depth) : Prop :=
  ∀ W' : (TorusFields.torusFrame L t n).GaugeField (TorusFields.torusFrame L t n).depth,
    BlockAverages.blockEnergy a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (TorusFields.torusFrame L t n).depth W
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) ≤
      BlockAverages.blockEnergy a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (TorusFields.torusFrame L t n).depth W'
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V)
def MinimizerUniqueUpToGauge : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ᶠ n in atTop, ∀ᶠ V in 𝓝 (TorusFields.trivialField n),
      (∃ w, BlockAverages.IsMinimizingChart a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) ρ w) ∧
      ∀ W, IsEnergyMinimizerOver a L t n V W →
        ∃ γ : (TorusFields.torusFrame L t n).Site (TorusFields.torusFrame L t n).depth → BlockAverages.UnitQuaternion,
          (∀ z : (TorusFields.torusFrame L t n).Cell, γ (BlockAverages.cellCentre _ z) = 1) ∧
          W = BlockAverages.gaugeTransform γ
            (ColdStepAtMirrorFrames.fieldAboveFrame (F := TorusFields.torusFrame L t n) true a ρ 0
              (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) 0)
end YangMills.Construction.RunningCouplingSlope
end
