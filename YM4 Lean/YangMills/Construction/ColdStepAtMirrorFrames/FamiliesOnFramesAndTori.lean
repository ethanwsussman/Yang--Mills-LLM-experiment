import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def restrictToTorus {j : ℕ} (n : ℕ) (W : F.GaugeField j) : TorusField n :=
  fun x i => W (siteOfCoords j fun k => ((x k).cast : ℤ)) i
def localFamilyOfDensity (f : LocalDensity) : LocalFamily :=
  fun F y W => f (F.period F.depth 0) (toTorusSite _ y) (restrictToTorus _ W)
def densityOfTopFamily (L t : ℕ) (g : (F : BlockFrame) → F.Cell → F.GaugeField F.top → ℝ) : LocalDensity :=
  fun n Y V => g (torusFrame L t n) (siteOfCoords (torusFrame L t n).top fun k => ((Y k).cast : ℤ))
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
end YangMills.Construction.ColdStepAtMirrorFrames
end
