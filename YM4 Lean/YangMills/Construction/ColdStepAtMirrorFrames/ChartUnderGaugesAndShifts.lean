import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def blockConstantGauge (γ : F.Cell → UnitQuaternion) : F.Site F.depth → UnitQuaternion :=
  fun x => γ (enclosingCell x)
structure ChartEquivariance (F : BlockFrame) (a : ℝ) : Prop where
  energy_gaugeTransform : ∀ (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth) (V : F.GaugeField F.top),
    blockEnergy a (finiteCells F) F.depth (gaugeTransform (blockConstantGauge γ) W) (gaugeTransform γ V) =
      blockEnergy a (finiteCells F) F.depth W V
  chartedField_gaugeTransform : ∀ (γ : F.Cell → UnitQuaternion)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    chartedField (fun x i => adjointAction (γ (enclosingCell x)) (w x i)) (gaugeTransform γ V) =
      gaugeTransform (blockConstantGauge γ) (chartedField w V)
  norm_contourAverage_gaugeTransform : ∀ (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth)
    (c : F.Site F.top × Fin 4),
    ‖contourAverage (gaugeTransform (blockConstantGauge γ) W) c‖ = ‖contourAverage W c‖
  energy_translate : ∀ (h : F.Cell) (W : F.GaugeField F.depth) (V : F.GaugeField F.top),
    blockEnergy a (finiteCells F) F.depth (translateField (cellCentre F.depth h) W) (translateField h V) =
      blockEnergy a (finiteCells F) F.depth W V
  chartedField_translate : ∀ (h : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top),
    chartedField (fun x i => w (x - cellCentre F.depth h) i) (translateField h V) =
      translateField (cellCentre F.depth h) (chartedField w V)
  contourAverage_translate : ∀ (h : F.Cell) (W : F.GaugeField F.depth) (c : F.Site F.top × Fin 4),
    contourAverage (translateField (cellCentre F.depth h) W) c = contourAverage W (c.1 - h, c.2)
  chordBonds_translate : ∀ (h : F.Cell) (b : F.Site F.depth × Fin 4),
    (b.1 + cellCentre F.depth h, b.2) ∈ chordBonds (finiteCells F) ↔ b ∈ chordBonds (finiteCells F)
  enclosingCell_translate : ∀ (h : F.Cell) (x : F.Site F.depth),
    enclosingCell (x + cellCentre F.depth h) = enclosingCell x + h
  sitesOfCells_translate : ∀ (h : F.Cell) (x : F.Site F.depth),
    x + cellCentre F.depth h ∈ sitesOfCells (finiteCells F) F.depth ↔ x ∈ sitesOfCells (finiteCells F) F.depth
  innerBonds_translate : ∀ (h : F.Cell) (c : F.Site F.top × Fin 4),
    (c.1 + h, c.2) ∈ innerBonds (finiteCells F) F.top ↔ c ∈ innerBonds (finiteCells F) F.top
  mem_chordBonds_of_not_tree : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → b ∈ chordBonds (finiteCells F)
def chartEquivarianceStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → ChartEquivariance F a
end ColdStepAtMirrorFrames
end YangMills.Construction
end
