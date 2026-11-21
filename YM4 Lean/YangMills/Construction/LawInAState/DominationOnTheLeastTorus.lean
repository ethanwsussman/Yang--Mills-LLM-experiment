import YangMills.Construction.ChessboardTori.MirrorGridsAtTheCutoff
import YangMills.Construction.LawInAState.AveragesInACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters ResponseInTheExpansion ChessboardTori
def cellDominationStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ Xi : ℝ, (Tb.stepParameters y).y₁ + 2 * (Tb.stepParameters y).B ≤ Xi →
    ∃ Rn : ℝ, 1 ≤ Rn ∧
    ∀ D : ChessboardSetup, D.L = (Tb.stepParameters y).side → IsFlowDatum (Tb.stepParameters y) Xi D.K D.β →
    ∀ g : ReflectionGrid D, g.q = 0 → ∀ G : D.GaugeField → ℝ,
      (fun U => (G U : ℂ)) ∈ D.openCellAlgebra (g.cell 0) →
      ∀ μ : Measure D.GaugeField, IsAdmissibleState D.L D.K D.β μ →
        |∫ U, G U ∂μ| ≤ Rn * CellAverages.reflectionNorm g G
end YangMills.Construction.StateLaws
end
