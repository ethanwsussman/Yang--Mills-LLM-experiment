import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
def ConstantJetComponents : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ μPlus μMinus : Fin 4,
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ κ ∈ imStrip (2 * stripHalfWidth),
      (covDerivDefectJet L k p μPlus μMinus).f00 κ = 0 ∧
        (holonomyDefectJet L k p μPlus μMinus).f00 κ = 0 ∧
        (halfFaceTraceJet L k p μPlus μMinus).f00 κ = LinearMap.id ∧
        (curvatureJet L k p μPlus μMinus).f00 κ = 0
end YangMills.Construction.Tower.FullSpace
end
