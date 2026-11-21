import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds
namespace HoleSavings
structure HoleData (F : BlockFrame) {L : ℕ} (g : LumpGrid L) (a s θ : ℝ) (J₀ : ℕ) where
  cells : Finset F.Cell
  topField : F.GaugeField F.top
  fineField : F.GaugeField F.depth
  base : F.Cell → F.Site F.depth
  chain : F.FieldChain
  chain_top : chain F.depth = fineField
  chain_minimal : cutChainEnergy a F.depth
      (cutBelow F.depth cells \ lumpsNeighbourhood (hotLumps g s (cutBelow F.depth cells) fineField)) chain =
    cutEffectiveAction a F.depth
      (cutBelow F.depth cells \ lumpsNeighbourhood (hotLumps g s (cutBelow F.depth cells) fineField)) fineField
  wall_free : HasLumpWall cells (hotLumps g s (cutBelow F.depth cells) fineField)
  isBaseChoice : IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth cells) fineField) base
namespace HoleData
variable {F : BlockFrame} {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
def hotFineLumps : Finset (Finset (F.Site F.depth)) := hotLumps g s (cutBelow F.depth D.cells) D.fineField
def hotTopLumps : Finset (Finset F.Cell) := hotLumps g θ D.cells D.topField
def keptCells : Finset F.Cell := D.cells \ lumpsNeighbourhood D.hotTopLumps
def chainSites : Finset (F.Site F.depth) := cutBelow F.depth D.cells \ lumpsNeighbourhood D.hotFineLumps
def topBondFit (c : F.Cell × Fin 4) : ℝ := contourFit J₀ D.hotFineLumps D.base D.fineField D.topField c
def energyOn (X : Finset F.Cell) : ℝ :=
  cutChainEnergy a F.depth (D.chainSites ∩ cutBelow F.depth X) D.chain + a * ∑ c ∈ cutBonds X, D.topBondFit c
def totalEnergy : ℝ := D.energyOn D.cells
open Classical in
def energyOver (B : Finset F.Cell) : ℝ :=
  ∑ p ∈ cutPlaquettes (cutBelow 0 D.chainSites),
      (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B then plaquetteEnergy (D.chain 0) p else 0) +
    a * ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) D.chainSites),
      (if c.1 ∈ cutBelow (i + 1) B ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B
        then blockFit (D.chain i) (D.chain (i + 1)) c else 0) +
    a * ∑ c ∈ cutBonds D.cells, (if c.1 ∈ B ∨ c.1 + unitStep F.top c.2 ∈ B then D.topBondFit c else 0)
open Classical in
def excitedCells (C : ℝ) : Finset F.Cell := D.cells.filter fun y => C * s ^ 2 ≤ D.energyOver (cellBall y 3)
open Classical in
def crowdedCells : Finset F.Cell := D.cells.filter fun y => IsCrowded J₀ D.hotFineLumps y
open Classical in
def badCells (C : ℝ) : Finset F.Cell := D.excitedCells C ∪ D.crowdedCells
open Classical in
def coreCells (C : ℝ) (k : ℕ) : Finset F.Cell :=
  D.cells.filter fun y => ∀ z ∈ D.badCells C, k ≤ cellSupDist y z
def HasCoreHotLumps (C : ℝ) (v : ℕ) : Prop :=
  ∃ (h1 : Finset (Finset F.Cell)) (p : Finset F.Cell → F.Cell × Fin 4 × Fin 4),
    h1 ⊆ D.hotTopLumps ∧ h1.card = v ∧
      (∀ l ∈ h1, p l ∈ cutPlaquettes D.cells ∧ θ ≤ BlockAverages.plaquetteDefect D.topField (p l) ∧
        plaquetteCorners (p l) ⊆ D.coreCells C 5 ∧ ∃ x ∈ plaquetteCorners (p l), x ∈ l)
def IsAdmissibleDomain : Prop :=
  (∃ H : Finset (Finset F.Cell), (∀ l ∈ H, IsLump g l) ∧ L ∣ F.extent 0 ∧ D.cells = cellsOffLumps F H) ∨
    (D.cells = torusCells F ∧ IsCold D.cells F.top θ D.topField)
open Classical in
def nearbyFineLumps (X : Finset F.Cell) : Finset (Finset (F.Site F.depth)) :=
  D.hotFineLumps.filter fun l => ∃ x ∈ X, ∃ y, cellSupDist x y ≤ 3 ∧ l ⊆ sitesBelow F.depth y
def IsFillingChain (C ε CJ : ℝ) (U2 : F.FieldChain) : Prop :=
  U2 F.top = D.topField ∧
  (∀ X ⊆ D.coreCells C 5,
    cutChainEnergy a F.top X U2 ≤ D.energyOn X + ε * s ^ 2 * (D.nearbyFineLumps X).card) ∧
  (∀ y ∈ D.coreCells C 6, ∀ X ⊆ cellBall y 1 ∩ D.coreCells C 5, cutChainEnergy a F.top X U2 ≤ CJ * s ^ 2) ∧
  ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)), nearbyLumps D.hotFineLumps (enclosingCell b.1) = ∅ →
    nearbyLumps D.hotFineLumps (enclosingCell (b.1 + unitStep F.depth b.2)) = ∅ →
    U2 F.depth b.1 b.2 = D.fineField b.1 b.2
end HoleData
def thickening {F : BlockFrame} (S Δ : Finset F.Cell) (m : ℕ) : Finset F.Cell := by
  classical exact S.filter fun z => ∃ d ∈ Δ, cellSupDist z d ≤ m
end HoleSavings
end YangMills.Construction
end
