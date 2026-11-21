import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvature
import YangMills.Construction.HoleBesideASecondHole.LegsInABlockAgreeWithATree
import YangMills.Construction.HoleBesideASecondHole.PathsAndHolonomies
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BondMeans
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
variable {F : BlockFrame}
def baseLeg (b : F.Cell → F.Site F.depth) (y : F.Cell) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : List PathStep :=
  axisPath (minimalOffset (b y) (cellCentre F.depth y + siteOfCoords F.depth e.1)) e.2
def legRotation (Wt Wp : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (y : F.Cell)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : UnitQuaternion :=
  pathHolonomy Wt (b y) (baseLeg b y e) * (pathHolonomy Wp (cellCentre F.depth y) (axisPath e.1 e.2))⁻¹
def cellRotation (Wt Wp : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (y : F.Cell) : UnitQuaternion :=
  GroupMeans.meanDirection (allContours F) (legRotation Wt Wp b y)
def baseContourHolonomy (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : UnitQuaternion :=
  pathHolonomy W (b c.1) (contourPath b c e.1 e.2)
open Classical in
structure BondBesideHoles (Wt Wp W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4)
    (G : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4))) (Ds : Finset (F.Site F.depth)) (κ K τ : ℝ) (N : ℕ) :
    Prop where
  base_mem : b c.1 ∈ sitesBelow F.depth c.1
  base_mem' : b (c.1 + unitStep F.top c.2) ∈ sitesBelow F.depth (c.1 + unitStep F.top c.2)
  contours_subset : G ⊆ allContours F
  contours_nonempty : G.Nonempty
  defect_le : BlockTrees.blockCurvatureNorm Wt c.1 ≤ κ
  defect_le' : BlockTrees.blockCurvatureNorm Wt (c.1 + unitStep F.top c.2) ≤ κ
  pairDefect_le : ∑ p ∈ BondContours.blockPairPlaquettes c, plaquetteDefect Wp p ^ 2 ≤ κ ^ 2
  links_close : PathHolonomy.LinksClose Wp Wt Ds
    (sitesBelow F.depth c.1 ∪ sitesBelow F.depth (c.1 + unitStep F.top c.2)) K
  coords_card_le : ∀ k, (Ds.image fun z => z k).card ≤ N
  holonomy_eq : ∀ e ∈ G, baseContourHolonomy Wt b c e = baseContourHolonomy W b c e
  missing_le : ((allContours F \ G).card : ℝ) ≤ τ * (allContours F).card
def BondMeanEstimate : Prop :=
  ∀ (F : BlockFrame) (Wt Wp W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4)
    (G : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4))) (Ds : Finset (F.Site F.depth)) (κ K τ : ℝ) (N : ℕ),
    Odd F.blockSide → (∀ i, 64 ≤ F.extent i) → 0 ≤ κ → 0 ≤ K → BondBesideHoles Wt Wp W b c G Ds κ K τ N →
    72 * (F.blockSide : ℝ) * κ + 16 * N * K ≤ 1 / 8 →
    ‖(((cellRotation Wt Wp b c.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          GroupMeans.quatAverage G (fun e => (baseContourHolonomy W b c e : ℍ[ℝ])) *
          ((cellRotation Wt Wp b (c.1 + unitStep F.top c.2) : UnitQuaternion) : ℍ[ℝ]) - contourAverage Wp c‖ ≤
        2 * (N : ℝ) ^ 4 * K / (F.blockSide : ℝ) ^ 3 + 12 * (72 * (F.blockSide : ℝ) * κ + 16 * N * K) ^ 2 +
          14 * (72 * (F.blockSide : ℝ) * κ + 16 * N * K) * τ ∧
      1 - ‖contourAverage Wp c‖ ≤ (72 * (F.blockSide : ℝ) * κ + 16 * N * K) ^ 2
end YangMills.Construction.BondMeans
end
