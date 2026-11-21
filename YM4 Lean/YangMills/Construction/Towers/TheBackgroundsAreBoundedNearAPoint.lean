import YangMills.Construction.Towers.IndicesNearAPointOfTheFinestLattice
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundsBoundedNearPoint
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, 1 ≤ k →
    ∀ q ∈ momentumPolydisc stripHalfWidth,
      ∀ (μ : Fin 4) (y : YangMills.Construction.InfiniteLattice.AmbientSpace),
      FieldBoundedNear L k y
        (phaseField (Tower.remainderIndex L k) q (responseAmplitude L k q μ) y) M
end YangMills.Construction.Tower.FullSpace.BackgroundsBoundedNearPoint
end
