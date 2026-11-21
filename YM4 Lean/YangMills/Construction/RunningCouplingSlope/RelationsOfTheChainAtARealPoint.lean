import YangMills.Construction.Lattice.InvertibleContourVariables
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Matrices Tower
variable {L n k : ℕ}
def LevelCurvaturesSmall (X : ChainPoint L n k) : Prop :=
  ∀ j, j < k → ∀ p : Face L n k j,
    ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy (levelField X j) p - 1) <
      PeriodicLattice.averagingRadiusCap L
def ChainRelationsAtCompactPoint : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ X : ChainPoint L n k, IsCompactValued X → LevelCurvaturesSmall X →
      IsTopDeriv X (topDeriv X) ∧ IsGaugeOrbitMap X (gaugeOrbitMap X) ∧
      IsShiftedGaugeMap X (shiftedGaugeMap X) ∧ IsChainDriftMap X (chainDriftMap X) ∧
      Function.Surjective (topDeriv X) ∧
      ∀ ξ : vertexFunctionSpace L n k 0, ∀ j, j ≤ k →
        tangentTransport X (gaugeOrbitMap X ξ) j =
            covDiff (levelField X j) (restrictVertexFunction j (ξ : Vertex L n k 0 → ComplexMatrix2)) ∧
          composedCubeAverage X j ξ =
            restrictVertexFunction j (ξ : Vertex L n k 0 → ComplexMatrix2) +
              chainDrift X (gaugeOrbitMap X ξ) j
end YangMills.Construction.RunningCouplingSlope
end
