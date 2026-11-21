import YangMills.Construction.Towers.IndicesNearAPointOfTheFinestLattice
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CovariantDifferenceCoeffs
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
def CovariantDifferenceCoeffsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ c : ℝ, 0 ≤ c ∧ ∀ k : ℕ, 1 ≤ k →
    CoeffsLocallyBounded (I := colourVertices L k 0) (J := colourEdges L k 0) L k
      (fun f => (FullSpace.rescaledOperators L k (gaugeFieldOfForm L k f)).D) c
end YangMills.Construction.Tower.FullSpace.CovariantDifferenceCoeffs
end
