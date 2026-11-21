import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def SmoothToSobolevDecayStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], SmoothHasFiniteSobolevDecay J
end YangMills.Construction.SpinHarmonics
end
