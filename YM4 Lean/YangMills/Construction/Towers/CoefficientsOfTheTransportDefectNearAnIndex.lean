import YangMills.Construction.Towers.IndicesNearAPointOfTheFinestLattice
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def HolonomyDefectCoeffsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ c : ℝ, 0 ≤ c ∧ ∀ k : ℕ, 1 ≤ k →
    FinestLatticeNeighbours.CoeffsLocallyBounded (I := PeriodicOperators.colourEdges L k 0)
      (J := PeriodicOperators.colourFaces L k 0) L k
      (fun f => holonomyDefectKernel L k (BackgroundJets.gaugeFieldOfForm L k f)) c
end YangMills.Construction.Tower.FullSpace
end
