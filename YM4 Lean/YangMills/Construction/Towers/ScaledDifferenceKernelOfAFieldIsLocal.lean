import YangMills.Construction.Towers.EntireCoordinatesOfAField
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality
def RescaledDifferenceKernelIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    Tower.FullSpace.EntireDependence.IsLocalAllRadii L k
      (PeriodicOperators.colourVertices L k 0) (PeriodicOperators.colourEdges L k 0)
      (fun ζ => (Tower.FullSpace.rescaledOperators L k
        (Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k ζ)).D)
end YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality
end
