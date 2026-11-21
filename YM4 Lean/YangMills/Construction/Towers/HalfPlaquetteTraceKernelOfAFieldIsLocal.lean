import YangMills.Construction.Towers.EntireCoordinatesOfAField
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality
def HalfFaceTraceKernelIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    Tower.FullSpace.EntireDependence.IsLocalAllRadii L k
      (PeriodicOperators.colourFaces L k 0) (PeriodicOperators.colourFaces L k 0)
      (fun ζ => Tower.FullSpace.halfFaceTraceKernel L k
        (Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k ζ))
end YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality
end
