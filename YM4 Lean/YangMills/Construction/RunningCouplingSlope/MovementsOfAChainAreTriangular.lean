import YangMills.Construction.RunningCouplingSlope.SlotsAreCoordinatesOfTheChainTangent
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def TransportCoordsTriangular : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ P : ChainPoint L n (k + 1), IsCompactValued P →
      ∃ N : Matrix (ChainCoord L n (k + 1)) (ChainCoord L n (k + 1)) ℝ,
        (∀ e e', coordLevel e ≤ coordLevel e' → N e e' = 0) ∧
        (∀ ξ, slotCoords ξ =
          transportCoords P ξ - Matrix.mulVec N (transportCoords P ξ)) ∧
        ∀ ξ, slotCoords ξ = 0 → topDeriv P ξ = finalNoise ξ
end YangMills.Construction.RunningCouplingSlope
end
