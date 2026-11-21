import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PeriodicForm
open YangMills.Construction.PeriodicOperators (colourEdges)
open YangMills.Construction.LocalKernels (projPositiveEdge)
def coeffsOnEdges (L n k j : ℕ) (A : Edge L n k j → Matrices.ComplexMatrix2) :
    (colourEdges L k j).Carrier → ℂ :=
  fun ι => toPauliCoeffs (restrictToPositiveEdges A) (ι.1, projPositiveEdge L n k j ι.2)
end YangMills.Construction.Tower.PeriodicForm
end
