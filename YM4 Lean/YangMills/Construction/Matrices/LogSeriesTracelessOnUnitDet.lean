import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
namespace YangMills.Construction.Matrices.ComplexMatrix2
def LogSeriesTracelessOfUnitDet : Prop :=
  ∀ A : ComplexMatrix2, A ∈ unitDeterminant → A ∈ logBall → logSeries A ∈ traceless
end YangMills.Construction.Matrices.ComplexMatrix2
