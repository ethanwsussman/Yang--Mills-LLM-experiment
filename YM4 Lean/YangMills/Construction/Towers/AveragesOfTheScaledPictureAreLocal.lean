import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledMeansLocality
open PeriodicOperators
open ScaledOperatorFunctions
open BackgroundJets (gaugeFieldOfForm)
def MeansAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ ρ C : ℝ, Tower.IteratedSmallFieldMeans.AdmissibleConstants L ρ C →
      IsLocalBelowNorm L k (colourEdges L k 0) (colourEdges L k k)
        (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q) (finestMesh L k * ρ) ∧
      IsLocalBelowNorm L k (colourVertices L k 0) (colourVertices L k k)
        (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R) (finestMesh L k * ρ)
end YangMills.Construction.Tower.FullSpace.ScaledMeansLocality
end
