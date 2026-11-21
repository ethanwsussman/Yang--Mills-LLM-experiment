import YangMills.Construction.ColdChainAtEveryLevel.ChartOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.FramingFromAGaugeOfLevelZero
import YangMills.Construction.ColdChainAtEveryLevel.PinnedQuarticGauge
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheCriticalChainOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def latticeFormAtSites (S : Finset F.Cell) (z : F.Cell) (ν : LatticeFractionalIntegration.Lattice4 → Fin 4 → ℍ[ℝ]) :
    F.Site 0 → Fin 4 → ℍ[ℝ] :=
  fun t i => if closedOrthant S z i = 1 then ν (GaugeMap.patchChart S z t) i
    else - ν (GaugeMap.patchChart S z (t + unitStep 0 i)) i
open Classical in
def lineAverage (S : Finset F.Cell) (z : F.Cell) (y y' : F.Cell)
    (ν : LatticeFractionalIntegration.Lattice4 → Fin 4 → ℍ[ℝ]) : ℍ[ℝ] :=
  if h : ∃ i, y' = y + unitStep F.top i then iteratedBlockAverage (latticeFormAtSites S z ν) F.top y h.choose else 0
def pinnedTopCorrection (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k : F.SiteGauge) (γ : LatticeFractionalIntegration.Lattice4 → UnitQuaternion) (y : F.Cell) :
    UnitQuaternion :=
  (patchFrame S V z y)⁻¹ *
    topCorrection W kW X k (pinnedGaugeOfBase W kW X k (PatchLatticeChart.siteGaugeOfLatticeGauge S V z γ)) y *
    patchFrame S V z y
def pinnedGaugeDataOfPatch (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge) : PinnedGauge.PinnedGaugeData where
  scale := 9 * (GaugeMap.cellSideLength F).toNat
  cellSide := F.blockSide ^ F.top
  corner := fun _ => 12 * GaugeMap.cellSideLength F
  region := GaugeMap.patchDomain S z
  field := PatchLatticeChart.latticeField S z (X 0)
  target := PatchLatticeChart.framedLatticeField S V z (W 0)
  CellIndex := F.Cell
  cells := patchCells S z
  cellSites := fun y => by
    classical exact (centredCube (F.blockSide ^ F.top)).image fun h =>
      GaugeMap.patchChart S z (cellCentre 0 y + siteOfCoords 0 h)
  base := z
  Adj := fun y y' => ∃ i, y' = y + unitStep F.top i
  bondAverage := fun y y' ν => lineAverage S z y y' ν
  pin := pinnedTopCorrection S V z W kW X k
end YangMills.Construction.BlockAverages
end
