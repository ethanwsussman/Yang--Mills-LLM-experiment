import YangMills.Construction.TotalDensitiesGiveASystem.TheTotalDensitiesGiveASystem
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters TorusLumps SystemsWithFiveBounds LimitTheorem
def ErgodicConclusionsFor (ϑ : ℝ) (Y : FiveBoundSystem) : Prop :=
  ∃ K : ℝ → LimitConstants, ∀ g ∈ Ioc 0 Y.top,
    (K g).Valid ∧
    (∃ (Q : PairSequence Y.L (Y.IsPair g)) (S : CumulantFamily), Q.Defines S) ∧
    (∀ Q : PairSequence Y.L (Y.IsPair g), ∃ (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop)
      (S : CumulantFamily), (Q.subseq φ hφ).Defines S) ∧
    ∀ (Q : PairSequence Y.L (Y.IsPair g)) (S : CumulantFamily), Q.Defines S →
      ErgodicDecompositionConclusion Y.M ϑ (Y.consts g).lawScale (Y.consts g).lawError (K g) Q S
def TopAtParameters (T : ParameterAssignment) (y : ℝ) : Prop :=
  T.floorMin ≤ y ∧ (T.stepParameters y).Admissible ∧ FlowIsChainLaw (T.stepParameters y) ∧
    ∀ Bs : ℝ, 2 * T.B ≤ Bs → ∃ c₅ lam top : ℝ, 0 ≤ c₅ ∧ 0 < lam ∧ 0 < top ∧
      (∀ g ∈ Ioc 0 top, y ≤ g ^ (-2 : ℤ) ∧
        TotalDensitiesGiveASystem.PassageWindowData (T.stepParameters y) Bs c₅ lam g ∧
        ExpansionFlowEqTotalFlowAt (T.stepParameters y) Bs g ∧ FourPointLawOnWindowAt (T.stepParameters y) Bs g) ∧
      ∀ (m : ℕ) (ϑ : ℝ), ϑ ∈ Ioc (0 : ℝ) 1 →
        ∃ Y : FiveBoundSystem,
          IsSystemOfFlow Y (T.stepParameters y) Bs top ((T.side : ℝ) ^ m) (min ϑ TwoPoints.Shapes.shapeConst) ∧
          (∀ g ∈ Ioc 0 top, FourPointLawInLimitsAt Y.L (Y.IsPair g)) ∧ ErgodicConclusionsFor ϑ Y
def topAtAdmissibleParamsStatement : Prop := HoldsAtAdmissibleParameters TopAtParameters
end YangMills.Construction.TotalDensities
end
