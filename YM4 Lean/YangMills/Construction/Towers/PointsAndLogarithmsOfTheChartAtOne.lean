import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open IdentityExpChart
variable {L n k j : ℕ}
def identityChartPoint (y : PositiveEdge L n k j → Matrices.ComplexMatrix2.LieElement) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  expForm (ofValues y)
def identityChartLog (V : Edge L n k j → Matrices.ComplexMatrix2) :
    PositiveEdge L n k j → Matrices.ComplexMatrix2.LieElement :=
  formValues (Tower.extendOddly fun c => (1 / Complex.I) • Matrices.ComplexMatrix2.logSeries (V c))
end Tower
end YangMills.Construction
end
