import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def SobolevDecayToSmoothStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], FiniteSobolevDecayImpliesSmooth J
end YangMills.Construction.SpinHarmonics
end
