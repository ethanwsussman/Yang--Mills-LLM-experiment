import YangMills.Construction.Averaging.ComplexOneStepStandingData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def complexReferenceStepRadius (L : ℕ) : ℝ := Averaging.ComplexStepSetting.bondRadius L / 16
end YangMills.Construction.PeriodicLattice
end
