import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def readInChart {E : Type} (G : F.GaugeField F.depth → E) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : E :=
  G (chartedField (fun x i => w x i + stepCoordinates η x i) V)
def gapExcessSum (A : ℝ) (W : F.GaugeField F.depth) : ℝ :=
  ∑ c ∈ innerBonds (finiteCells F) F.top, (haarGap (A * ‖contourAverage W c‖) - haarGap A)
def haarExcessSum (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (w b.1.1 b.1.2 + stepCoordinates η b.1.1 b.1.2)
def centredExpansionSum (f : LocalFamily) (W : F.GaugeField F.depth) : ℝ :=
  ∑ y ∈ sitesOfCells (finiteCells F) F.depth, subtractTrivial f F y W
def expansionDecayKernel (F : BlockFrame) (δ : ℝ) (b b' : ↥(chordBonds (finiteCells F))) : ℝ :=
  ∑ y ∈ sitesOfCells (finiteCells F) F.depth, Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) +
    siteSupDist y b'.1.1 + siteSupDist b.1.1 b'.1.1)))
structure HasDecayingDerivs (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) : Prop where
  smooth : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth),
    IsSmallCurvature σ W → ContDiffThreeAlongBonds (f F y) W
  decay : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (k : ℕ)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature σ W →
    1 ≤ k → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (f F y) W c X| ≤ (if k = 3 then E₃ else E) / torusDecayFactor L δ (bondSpan y c)
def exponentInChart (a x : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (f : LocalFamily) (ν : ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : ℝ :=
  x * (chartedEnergyAt a w V η - chartedEnergyAt a w V 0) - readInChart (gapExcessSum (a * x)) w V η -
    haarExcessSum w η - ν * readInChart (centredExpansionSum f) w V η
end ColdStepAtMirrorFrames
end YangMills.Construction
end
