import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ThreeLocalOperators
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
def LocalEntireOperators : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLocalEntire L k (colourEdges L k 0) (colourEdges L k 0)
      (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).H) ∧
    IsLocalEntire L k (colourEdges L k 0) (colourEdges L k 0)
      (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).K) ∧
    IsLocalEntire L k (colourVertices L k 0) (colourVertices L k 0)
      (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Delta)
end YangMills.Construction.Tower.FullSpace.ThreeLocalOperators
end
