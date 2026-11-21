import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFields
abbrev OffsetBox : Type := (Fin 4 → ℤ) × (Fin 4 → ℤ)
variable {F F' : BlockFrame}
def siteAtOffset (y : F.Cell) (z : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth y + siteOfCoords F.depth z
def boxAtOffset (y : F.Cell) (q : OffsetBox) : Finset (F.Site F.depth) :=
  (boxSites F.depth q.1 q.2).image fun x => cellCentre F.depth y + x
open Classical in
def baseSitesAt (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) : Finset (F.Site F.depth) :=
  if nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y then {cellCentre F.depth y}
  else (sitesBelow F.depth y).filter fun b => ∀ B ∈ excludedBoxes J₀ h y, ∀ x ∈ B, ∀ i, x i ≠ b i
def SameNearbyLumps (h : Finset (Finset (F.Site F.depth))) (h' : Finset (Finset (F'.Site F'.depth)))
    (y : F.Cell) (y' : F'.Cell) : Prop :=
  ∃ Q : Finset OffsetBox,
    (∀ q ∈ Q, ∀ i, -(3 * (F.blockSide : ℤ)) ≤ q.1 i ∧ q.1 i ≤ q.2 i ∧ q.2 i ≤ 3 * (F.blockSide : ℤ) ∧
      q.2 i - q.1 i + 1 < 2 ^ 15) ∧
    nearbyLumps h y = Q.image (boxAtOffset y) ∧ nearbyLumps h' y' = Q.image (boxAtOffset y')
variable {n : ℕ}
abbrev fineLevelField (ℓ : StepParameters) (n : ℕ) (W : TorusField (n * ℓ.side)) :
    (stepBlockFrame ℓ.side n).GaugeField 0 :=
  readAtLevel (stepBlockFrame ℓ.side n) 0 W
abbrev coarseLevelField (ℓ : StepParameters) (n : ℕ) (V : TorusField n) :
    (stepBlockFrame ℓ.side n).GaugeField 1 :=
  readAtLevel (stepBlockFrame ℓ.side n) 1 V
abbrev fineHotLumps (ℓ : StepParameters) (W : (stepBlockFrame ℓ.side n).GaugeField 0) :
    Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)) :=
  hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W
def cellCentreOnTorus (L : ℕ) (y : (stepBlockFrame L n).Cell) : TorusSite (n * L) :=
  toTorusSite (n * L) (cellCentre 0 y)
def blockConstantGauge (L : ℕ) (g : TorusSite n → UnitQuaternion) : TorusSite (n * L) → UnitQuaternion :=
  fun x => g (parentBlock L x)
end YangMills.Construction.TorusLumps
end
