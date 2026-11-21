import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction
namespace ConvexObservables
def normalizedBallLaw {ι : Type} [Fintype ι] (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) :
    Measure (BondField ι) :=
  volume.withDensity fun η => ENNReal.ofReal (ballDensity r Ψ η / ∫ ζ, ballDensity r Ψ ζ)
def cellsDiameter {F : BlockFrame} {M : ℕ} (Z : Fin M → F.Cell) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => cellSupDist (Z i) (Z j)
end ConvexObservables
end YangMills.Construction
end
