import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def stepFrame (star : Bool) (a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    imaginaryQuaternions :=
  if star then minimizingBondCoordinate a ρA (finiteCells F) b V else bondFrameCoord a ρA m b V
def chartedEnergy (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) : ℝ :=
  blockEnergy a (finiteCells F) F.depth (chartedField w V) V
def ancestorSite (l : ℕ) {j : ℕ} (x : F.Site j) : F.Site l :=
  siteOfCoords l fun i => (siteCoords x i + ((F.blockSide : ℤ) ^ (l - j) - 1) / 2) / (F.blockSide : ℤ) ^ (l - j)
def chainActionBelow (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) : ℝ :=
  wilsonAction S (X 0) + a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), blockFit (X j) (X (j + 1)) c
def IsMinimizingChainBelow (a : ℝ) (S : Finset F.Cell) (W : F.GaugeField F.depth) (X : F.FieldChain) : Prop :=
  X F.depth = W ∧ ∀ X' : F.FieldChain, X' F.depth = W → chainActionBelow a S X ≤ chainActionBelow a S X'
open Classical in
def chainSiteShare (a : ℝ) (S : Finset F.Cell) (y : F.Site F.depth) (X : F.FieldChain) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, (∑ x ∈ plaquetteCorners p, if ancestorSite F.depth x = y then (1 / 4 : ℝ) else 0) *
      (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
      ((if ancestorSite F.depth c.1 = y then (1 / 2 : ℝ) else 0) +
        (if ancestorSite F.depth (c.1 + unitStep (j + 1) c.2) = y then (1 / 2 : ℝ) else 0)) *
      blockFit (X j) (X (j + 1)) c
open Classical in
def minimalSiteShare (a : ℝ) (y : F.Site F.depth) (W : F.GaugeField F.depth) : ℝ :=
  if h : ∃ X, IsMinimizingChainBelow a (finiteCells F) W X then
    chainSiteShare a (finiteCells F) y h.choose else 0
open Classical in
def cellEnergyShare (a : ℝ) (Y : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) : ℝ :=
  (∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y,
      minimalSiteShare a y (chartedField w V)) +
    a / 2 * ∑ c ∈ (innerBonds (finiteCells F) F.top).filter
        (fun c => c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y),
      blockFit (chartedField w V) V c
def coordsAboveFrame (star : Bool) (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => stepFrame star a ρA m (x, i) V + stepCoordinates η x i
def fieldAboveFrame (star : Bool) (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : F.GaugeField F.depth :=
  chartedField (coordsAboveFrame star a ρA m V η) V
def centredExpansion (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  subtractTrivial f F y (fieldAboveFrame star a ρA m V η)
open Classical in
def cellCentredExpansion (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    centredExpansion star a ρA m f y η V
def haarRadialDensity (u : ℝ) : ℝ :=
  if u < Real.pi then (Real.sinc u) ^ 2 / (2 * Real.pi ^ 2) else 0
def haarLogRatio (w : imaginaryQuaternions) : ℝ :=
  Real.log (haarRadialDensity ‖w‖ / haarRadialDensity 0)
def haarGapExcess (a x : ℝ) (W : F.GaugeField F.depth) (c : F.Site F.top × Fin 4) : ℝ :=
  haarGap (a * x * ‖contourAverage W c‖) - haarGap (a * x)
def stepExponent (star : Bool) (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  x * (chartedEnergy a (coordsAboveFrame star a ρA m V η) V -
      chartedEnergy a (coordsAboveFrame star a ρA m V 0) V) -
    (∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame star a ρA m V η) c) -
    (∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2)) -
    ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m f y η V
def cutoffWeight (ρ : ℝ) (p : ℝ → ℝ) (η : StepVariable (finiteCells F)) : ℝ :=
  ∏ b : ↥(chordBonds (finiteCells F)), cutoffFactor ρ p ‖η b‖
def cutoffMean (ρ : ℝ) (p : ℝ → ℝ) (Ψ H : StepVariable (finiteCells F) → ℝ) : ℝ :=
  (∫ η, H η * (cutoffWeight ρ p η * Real.exp (- Ψ η))) / ∫ η, cutoffWeight ρ p η * Real.exp (- Ψ η)
def cellQuadratic (lam x : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then x * lam / 2 * ‖η b‖ ^ 2 else 0
def totalQuadratic (lam x : ℝ) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), x * lam / 2 * ‖η b‖ ^ 2
def chartedSlope (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) : ℝ :=
  deriv (fun u : ℝ => chartedEnergy a (Function.update w b.1 (Function.update (w b.1) b.2
    (w b.1 b.2 + u • e))) V) 0
open Classical in
def cellExponent (star : Bool) (a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  x * (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      ∫ v in (0 : ℝ)..1, chartedSlope a (coordsAboveFrame star a ρA m V (v • η)) V b.1
        (toImaginary (η b)) else 0) -
    (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      haarGapExcess a x (fieldAboveFrame star a ρA m V η) c) -
    (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2) else 0)
def interactionDensity (star : Bool) (a ρA ρ lam x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily)
    (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  - ∫ τ in (0 : ℝ)..1, cutoffMean ρ p
    (fun η => τ * stepExponent star a ρA x m f 0 V η + (1 - τ) * totalQuadratic lam x η)
    (fun η => cellExponent star a ρA x m Y V η - cellQuadratic lam x Y η)
def expansionDensity (star : Bool) (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  ∫ ν in (0 : ℝ)..1, cutoffMean ρ p (stepExponent star a ρA x m f ν V) fun η =>
    cellCentredExpansion star a ρA m f Y η V
def frameDensity (star : Bool) (a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  - x * (cellEnergyShare a Y (fun z i => stepFrame star a ρA m (z, i) V) V -
    minimalCellShare a (finiteCells F) Y V)
def gaussianMass (ρ lam x : ℝ) (p : ℝ → ℝ) (F : BlockFrame) : ℝ :=
  ∫ η : StepVariable (finiteCells F), cutoffWeight ρ p η * Real.exp (- totalQuadratic lam x η)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
