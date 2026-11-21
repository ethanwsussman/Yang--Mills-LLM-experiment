import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses
open YangMills.Construction.StepSettings YangMills.Construction.StepGas
open YangMills.Construction.LumpContours YangMills.Construction.RenormalizationStepParameters
def stageGround {p : StepParameters} (T : StageTower p) (j m : ℕ) [NeZero m] (v : MarkedSample p (j + 1) m) :
    GasGround (T.stage j).toStepSetup m :=
  ⟨Finset.univ \ thickening lumpRange (torusHotSites p v.2.2.1), hotCoreSites (T.stage j).toStepSetup v.2.2.1, v.2.2.1,
    (stageState T (j + 1) m v).2⟩
def supportsPresent {R : StepSetup} {m : ℕ} [NeZero m] (G : GasGround R m)
    (Θ : Finset (ClusterSupport R.params.side m)) : Set G.Config :=
  {σ | ∀ θ ∈ Θ, ∃ i : G.GasSpin, i.1 = θ ∧ σ i ≠ Sum.inl ()}
def stepGivenStateIsGasStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j : ℕ),
    IsTowerAtParametersMeasurable Tb y T β (j + 1) →
    ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (Tb.stepParameters y) m →
      ∀ (Θ : Finset (ClusterSupport (Tb.stepParameters y).side m)) (A : Set (MarkedSample (Tb.stepParameters y) (j + 1) m)),
        MeasurableSet[stageSigma T (j + 1) m] A →
        markedSampleLaw T β (j + 1) m (A ∩ {v | Θ ⊆ freeSupportsAt T j m v}) =
          ∫⁻ v in A, (stageGround T j m v).gibbsLaw ∅ (supportsPresent (stageGround T j m v) Θ)
            ∂(markedSampleLaw T β (j + 1) m)
end YangMills.Construction.CellWindows
end
