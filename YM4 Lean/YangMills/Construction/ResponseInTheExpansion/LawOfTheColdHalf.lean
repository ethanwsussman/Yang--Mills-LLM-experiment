import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation MeasureTheory
variable {F : BlockFrame}
structure ColdHalfLaw where
  a : ℝ
  chartRadius : ℝ
  ballRadius : ℝ
  coupling : ℝ
  rate : ℝ
  mirrorRadius : ℕ
  cutoff : ℝ → ℝ
  family : LocalFamily
abbrev AboveFrames (F : BlockFrame) : Type := StepVariable (finiteCells F) → F.GaugeField F.top → ℝ
namespace ColdHalfLaw
variable (Q : ColdHalfLaw)
def exponent (V : F.GaugeField F.top) : StepVariable (finiteCells F) → ℝ :=
  familyLawExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Q.family V
def radialWeight : ℝ → ℝ := cutoffFactor Q.ballRadius Q.cutoff
def expectation (V : F.GaugeField F.top) (H : StepVariable (finiteCells F) → ℝ) : ℝ :=
  ballExpectation Q.radialWeight (Q.exponent V) H
def covariance (V : F.GaugeField F.top) (H H' : StepVariable (finiteCells F) → ℝ) : ℝ :=
  ballCovariance Q.radialWeight (Q.exponent V) H H'
def expectationOf (K : AboveFrames F) (V : F.GaugeField F.top) : ℝ := Q.expectation V fun η => K η V
def HasSize (Cq : ℕ → ℝ) (V : F.GaugeField F.top) (h : ℝ) (Y : F.Cell)
    (H : StepVariable (finiteCells F) → ℝ) : Prop :=
  HasLocalSize Q.ballRadius Q.radialWeight (Q.exponent V) Cq Q.coupling Q.rate h
    (fun b => cellSupDist (enclosingCell b.1.1) Y) H
def blockCost (Y : F.Cell) : AboveFrames F := fun η V =>
  cellEnergyShare Q.a Y (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V
def totalCost : AboveFrames F := fun η V =>
  chartedEnergy Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V
def blockIncrement (Y : F.Cell) : AboveFrames F := fun η V => Q.blockCost Y η V - Q.blockCost Y 0 V
open Classical in
def linearBlockPart (Y : F.Cell) : AboveFrames F := fun η V =>
  Q.coupling * ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
    ∫ v in (0 : ℝ)..1, chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V (v • η)) V b.1
      (toImaginary (η b)) else 0
def contourAverageSize (c : F.Site F.top × Fin 4) : AboveFrames F := fun η V =>
  ‖contourAverage (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η) c‖
def liftedExpansion (g : F.Site F.depth → F.GaugeField F.depth → ℝ) (y : F.Site F.depth) : AboveFrames F :=
  fun η V => g y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η)
open Classical in
def blockSum (g : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell) : AboveFrames F :=
  fun η V => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    Q.liftedExpansion g y η V
open Classical in
def weightedShareIncrement (w : F.Site F.depth → ℝ) (Y : F.Cell) : AboveFrames F := fun η V =>
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    w y * (minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η) -
      minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V 0))
end ColdHalfLaw
end WeightedResponses
end YangMills.Construction
end
