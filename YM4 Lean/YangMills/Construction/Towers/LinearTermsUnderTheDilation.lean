import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices (ComplexMatrix2)
namespace CoboundaryScaling
def Statement : Prop :=
  ∀ (L n k j : ℕ) (hpos : 0 < L) (hle : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ j →
    (∀ l ≤ j, ∀ B : Edge L n k l → ComplexMatrix2,
      edgeCoboundary (transportTotal (scaleEdge hpos hle l) B) =
        transportTotal (scaleFace hpos hle l) (edgeCoboundary B)) ∧
    ∀ i < j, ∀ B : Edge L n k i → ComplexMatrix2,
      traceFinsumNorm (fineOnlyContourAverage L (scaledExponent n k j) j i
          (transportTotal (scaleEdge hpos hle i) B)) =
        traceFinsumNorm (fineOnlyContourAverage L n k i B)
end CoboundaryScaling
end YangMills.Construction.Tower
end
