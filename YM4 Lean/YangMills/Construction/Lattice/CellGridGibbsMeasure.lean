import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CellGrid
variable {L : ℕ} {κ : ℤ}
def boltzmannFactor (d : CellGrid L κ) (β : ℝ) (U : d.GaugeConfig) : ℝ :=
  Real.exp (-β * d.wilsonAction U)
def normalizingIntegral (d : CellGrid L κ) (β : ℝ) : ℝ :=
  ∫ U, d.boltzmannFactor β U ∂(BoxTorus.haarConfigMeasure L κ d.sideLengths)
def gibbsMeasure (d : CellGrid L κ) (β : ℝ) : Measure d.GaugeConfig :=
  (ENNReal.ofReal (d.normalizingIntegral β))⁻¹ •
    (BoxTorus.haarConfigMeasure L κ d.sideLengths).withDensity fun U =>
      ENNReal.ofReal (d.boltzmannFactor β U)
def gibbsMean (d : CellGrid L κ) (β : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : d.GaugeConfig → E) : E :=
  ∫ U, F U ∂d.gibbsMeasure β
end YangMills.Construction.CellGrid
end
