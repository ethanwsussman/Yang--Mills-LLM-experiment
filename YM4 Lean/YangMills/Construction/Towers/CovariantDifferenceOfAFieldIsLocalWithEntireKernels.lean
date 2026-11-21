import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferences
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace FullSpace
variable {L : ℕ}
def covDiffKernelOfField (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) :
    PeriodicOperators.KernelMatrix (Fin 3 × Vertex L 0 0) (Fin 3 × PositiveEdge (meshAt L 0 0)) :=
  CovDiffTransposes.matrixKernel (vertexCoordinate (Vertex L 0 0)) (edgePauliCoordinates L 0 0)
    (covDiff (expField ζ))
end FullSpace
def CovDiffKernelLocalEntire : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ ρ : ℝ, 0 < ρ →
      PeriodicOperators.IsLocalWith (PeriodicOperators.colourEdges L 0 0)
        (PeriodicOperators.colourVertices L 0 0) (PeriodicOperators.colourEdges L 0 0)
        FullSpace.covDiffKernelOfField ρ 2) ∧
    PeriodicOperators.HasEntireKernelEntries (PeriodicOperators.colourEdges L 0 0)
      (PeriodicOperators.colourVertices L 0 0) (PeriodicOperators.colourEdges L 0 0)
      FullSpace.covDiffKernelOfField ∧
    ∀ (ζ : (PeriodicOperators.colourEdges L 0 0).Carrier → ℂ)
      (a : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))
      (b : Fin 3 × FullSpace.Vertex L 0 0),
      b.2 ≠ a.2.1.terminal → b.2 ≠ a.2.1.initial → FullSpace.covDiffKernelOfField ζ a b = 0
end YangMills.Construction.Tower
end
