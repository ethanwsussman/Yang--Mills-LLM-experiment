import YangMills.Construction.Towers.EntireCoordinatesOfAField
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality
open PeriodicOperators
open EntireDependence
open BackgroundJets (gaugeFieldOfForm)
def KernelIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLocalAllRadii L k (colourEdges L k 0) (colourFaces L k 0)
      (fun ζ => holonomyDefectKernel L k (gaugeFieldOfForm L k ζ))
end YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality
end
