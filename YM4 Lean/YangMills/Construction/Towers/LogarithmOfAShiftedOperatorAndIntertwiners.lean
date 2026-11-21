import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
def LogShiftedAndIntertwiners : Prop :=
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (z : ℝ), 0 < z →
    LogShiftedProps H z ∧ LogEqIntegralIoi H z ∧ LogCommIntertwiner H H' z
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
