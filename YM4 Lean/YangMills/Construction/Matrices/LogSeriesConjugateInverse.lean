import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace Matrices.ComplexMatrix2
def LogSeriesConjugateInverse : Prop :=
  ∀ X g : ComplexMatrix2, IsUnit X → IsUnit g → operatorNorm (X - 1) < 1 →
    operatorNorm (g * X⁻¹ * g⁻¹ - 1) < 1 →
    logSeries (g * X⁻¹ * g⁻¹) = -(g * logSeries X * g⁻¹)
end Matrices.ComplexMatrix2
end YangMills.Construction
