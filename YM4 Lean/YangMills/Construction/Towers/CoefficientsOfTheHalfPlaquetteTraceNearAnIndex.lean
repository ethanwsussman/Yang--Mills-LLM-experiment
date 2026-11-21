import YangMills.Construction.Towers.IndicesNearAPointOfTheFinestLattice
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex
open PeriodicOperators
open BackgroundJets
open FinestLatticeNeighbours
def HalfFaceTraceCoeffsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ c : ℝ, 0 ≤ c ∧ ∀ k : ℕ, 1 ≤ k →
    CoeffsLocallyBounded (I := colourFaces L k 0) (J := colourFaces L k 0) L k
      (fun f => halfFaceTraceKernel L k (gaugeFieldOfForm L k f)) c
end YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex
end
