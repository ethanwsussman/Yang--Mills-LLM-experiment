import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.MatrixIdentities
def Statement : Prop :=
  InvTraceIdentity ∧ HalfTraceInPauliCoords ∧ (∀ ι : Type, HermitianSeriesAbsConv ι) ∧
    ∀ g ∈ PeriodicLattice.compactGaugeGroup, ∀ X ∈ Matrices.ComplexMatrix2.traceless,
      ∀ Y ∈ Matrices.ComplexMatrix2.traceless,
        halfTraceProduct (Matrices.ComplexMatrix2.conjugateBy g X)
          (Matrices.ComplexMatrix2.conjugateBy g Y) = halfTraceProduct X Y
end YangMills.Construction.Tower.LeftChartAlgebra.MatrixIdentities
end
