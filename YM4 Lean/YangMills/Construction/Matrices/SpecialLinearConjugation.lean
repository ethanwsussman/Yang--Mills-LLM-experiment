import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def symplecticUnit : ComplexMatrix2 := !![0, 1; -1, 0]
def conjEntries (m : ComplexMatrix2) : ComplexMatrix2 := m.map (starRingEnd ℂ)
end YangMills.Construction.Matrices.ComplexMatrix2
