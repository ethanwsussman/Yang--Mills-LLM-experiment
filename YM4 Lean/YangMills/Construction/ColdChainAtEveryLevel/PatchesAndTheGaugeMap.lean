import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormula
import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.LatticeFractionalIntegration
namespace GaugeMap
variable {F : BlockFrame}
def cellSideLength (F : BlockFrame) : ℤ := (F.blockSide : ℤ) ^ F.top
def patchSite (S : Finset F.Cell) (z : F.Cell) (x : Lattice4) : F.Site 0 :=
  cellCentre 0 z + siteOfCoords 0 fun i => closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)
def patchChart (S : Finset F.Cell) (z : F.Cell) (s : F.Site 0) : Lattice4 :=
  fun i => closedOrthant S z i * ((s - cellCentre 0 z) i).valMinAbs + (cellSideLength F - 1) / 2
def patchCorners (S : Finset F.Cell) (z : F.Cell) : Finset Lattice4 :=
  (cellBall S z 10).image fun y i => closedOrthant S z i * cellDisplacement z y i * cellSideLength F
open Classical in
def patchDomain (S : Finset F.Cell) (z : F.Cell) : Finset Lattice4 :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(10 * cellSideLength F)) (21 * cellSideLength F - 1)).filter
    fun x => ∃ a ∈ patchCorners S z, ∀ i, a i ≤ x i
def cellTransport (S : Finset F.Cell) (V : F.GaugeField F.top) (z y : F.Cell) : UnitQuaternion :=
  pathHolonomy V y (axisPath (fun i => 21 * closedOrthant S z i - cellDisplacement z y i) 1)
def transportVector (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (s : F.Site 0) :
    F.Cell → ℍ[ℝ] :=
  fun y => Real.sqrt (cellPartition S s y) • ((cellTransport S V z y : UnitQuaternion) : ℍ[ℝ])
def frameChange (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (s : F.Site 0) : UnitQuaternion :=
  polarUnit (quaternionPairing S (leadingFrame S V s) (transportVector S V z s))
def localForm (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → ℍ[ℝ]) : Lattice4 → Fin 4 → ℍ[ℝ] :=
  fun x i =>
    let s := patchSite S z x
    let s' := patchSite S z (x + basisVector i)
    adjointAction (frameChange S V z s)⁻¹
      (if closedOrthant S z i = 1 then u s i else - adjointAction (R s' i)⁻¹ (u s' i))
def localPotential (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → ℍ[ℝ]) : Lattice4 → ℍ[ℝ] :=
  randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (localForm S V R z u)
def cellOffsets (F : BlockFrame) : Finset Lattice4 :=
  Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) (cellSideLength F)
def localPotentialMean (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F, localPotential S V R z u x
def gluedPotential (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (u : F.Site 0 → Fin 4 → ℍ[ℝ]) : F.Site 0 → ℍ[ℝ] :=
  fun s => ∑ z ∈ S, cellPartition S s z • adjointAction (frameChange S V z s)
    (localPotential S V R z u (patchChart S z s) - localPotentialMean S V R z u)
def frameCellMean (S : Finset F.Cell) (V : F.GaugeField F.top) (y : F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F,
    adjointAction (frameChange S V y (patchSite S y x))⁻¹ (ξ (patchSite S y x))
def interiorBump (s : F.Site 0) (y : F.Cell) : ℝ :=
  ∏ i, cutoffProfile (5 / 2 * (((s - cellCentre 0 y) i).valMinAbs : ℝ) / (cellSideLength F : ℝ))
def normalizedBump (S : Finset F.Cell) (s : F.Site 0) (y : F.Cell) : ℝ :=
  interiorBump s y / ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y)
def gaugeMap (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (u : F.Site 0 → Fin 4 → ℍ[ℝ]) : F.Site 0 → ℍ[ℝ] :=
  fun s => gluedPotential S V R u s - ∑ y ∈ S, normalizedBump S s y •
    adjointAction (frameChange S V y s) (frameCellMean S V y (gluedPotential S V R u))
def InGaugeSlice (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : Prop :=
  ∀ s ∈ sitesOfCells S 0, gaugeMap S V R (fun x i => u x i) s = 0
def CellMeanFree (S : Finset F.Cell) (V : F.GaugeField F.top) (ξ : F.Site 0 → ℍ[ℝ]) : Prop :=
  ∀ y ∈ S, frameCellMean S V y ξ = 0
end GaugeMap
end YangMills.Construction
end
