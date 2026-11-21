import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def DifferentiableOnFamiliesAnalytic : Prop :=
  ∀ (ι : Type) [Fintype ι] (U : Set (ι → ComplexMatrix2)) (F : (ι → ComplexMatrix2) → ComplexMatrix2),
    IsOpen U → DifferentiableOn ℂ F U → AnalyticOnNhd ℂ F U
end YangMills.Construction.Matrices.ComplexMatrix2
