import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledKernelsLocal
def FourKernelsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    Tower.FullSpace.ScaledOperatorFunctions.IsLocalEntire L k
      (PeriodicOperators.colourVertices L k 0) (PeriodicOperators.colourEdges L k 0)
      (fun ζ => (Tower.FullSpace.rescaledOperators L k
        (Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k ζ)).D) ∧
    Tower.FullSpace.ScaledOperatorFunctions.IsLocalEntire L k
      (PeriodicOperators.colourEdges L k 0) (PeriodicOperators.colourFaces L k 0)
      (fun ζ => Tower.FullSpace.holonomyDefectKernel L k
        (Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k ζ)) ∧
    Tower.FullSpace.ScaledOperatorFunctions.IsLocalEntire L k
      (PeriodicOperators.colourFaces L k 0) (PeriodicOperators.colourFaces L k 0)
      (fun ζ => Tower.FullSpace.halfFaceTraceKernel L k
        (Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k ζ)) ∧
    Tower.FullSpace.ScaledOperatorFunctions.IsLocalEntire L k
      (PeriodicOperators.colourEdges L k 0) (PeriodicOperators.colourEdges L k 0)
      (fun ζ => Tower.FullSpace.curvatureKernel
        (Tower.FullSpace.BackgroundJets.gaugeFieldOfForm L k ζ))
end YangMills.Construction.Tower.FullSpace.ScaledKernelsLocal
end
