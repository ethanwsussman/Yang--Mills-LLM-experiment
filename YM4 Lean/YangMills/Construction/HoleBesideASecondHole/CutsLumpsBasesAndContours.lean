import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LumpContours
open BlockAverages
variable {F : BlockFrame}
def sitesBelow (i : ℕ) {j : ℕ} (x : F.Site j) : Finset (F.Site i) :=
  (centredCube (F.blockSide ^ (j - i))).image fun h => siteOfCoords i fun k => (F.blockSide : ℤ) ^ (j - i) * siteCoords x k + h k
def cutBelow (i : ℕ) {j : ℕ} (X : Finset (F.Site j)) : Finset (F.Site i) :=
  X.biUnion (sitesBelow i)
def cutBonds {j : ℕ} (X : Finset (F.Site j)) : Finset (F.Site j × Fin 4) :=
  (X ×ˢ Finset.univ).filter fun b => b.1 + unitStep j b.2 ∈ X
def cutPlaquettes {j : ℕ} (X : Finset (F.Site j)) : Finset (F.Site j × Fin 4 × Fin 4) :=
  (X ×ˢ Finset.univ ×ˢ Finset.univ).filter fun p => p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ X
def plaquetteEnergy (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  1 - ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]).re
def cutChainEnergy (a : ℝ) (j : ℕ) (X : Finset (F.Site j)) (U : F.FieldChain) : ℝ :=
  ∑ p ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) p +
    a * ∑ i ∈ Finset.range j, ∑ c ∈ cutBonds (cutBelow (i + 1) X), blockFit (U i) (U (i + 1)) c
def cutEffectiveAction (a : ℝ) (j : ℕ) (X : Finset (F.Site j)) (V : F.GaugeField j) : ℝ :=
  ⨅ U : {U : F.FieldChain // U j = V}, cutChainEnergy a j X U.1
def plainBlockEnergy (a : ℝ) (X : Finset F.Cell) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) : ℝ :=
  cutEffectiveAction a F.depth (cutBelow F.depth X) W + a * ∑ c ∈ cutBonds X, blockFit W V c
def supDist {j : ℕ} (x y : F.Site j) : ℕ := Finset.univ.sup fun i => ((x i - y i).valMinAbs).natAbs
def AreWithin {j : ℕ} (r : ℕ) (X Y : Finset (F.Site j)) : Prop := ∃ x ∈ X, ∃ y ∈ Y, supDist x y ≤ r
def boxSites (j : ℕ) (lo hi : Fin 4 → ℤ) : Finset (F.Site j) :=
  (Fintype.piFinset fun i => Finset.Icc (lo i) (hi i)).image (siteOfCoords j)
def thicken {j : ℕ} (m : ℕ) (X : Finset (F.Site j)) : Finset (F.Site j) :=
  X.biUnion fun x => (centredCube (2 * m + 1)).image fun h => x + siteOfCoords j h
def lumpRange : ℕ := 2 ^ 12
def lumpNeighbourhood {j : ℕ} (l : Finset (F.Site j)) : Finset (F.Site j) := thicken lumpRange l
def lumpsNeighbourhood {j : ℕ} (H : Finset (Finset (F.Site j))) : Finset (F.Site j) := H.biUnion lumpNeighbourhood
def lumpCollar {j : ℕ} (l : Finset (F.Site j)) : Finset (F.Site j) := thicken (lumpRange + 2) l
structure LumpGrid (L : ℕ) where
  lower : ℤ → ℤ
  upper : ℤ → ℤ
  mem_interval : ∀ o, |o| ≤ ((L : ℤ) - 1) / 2 →
    -(((L : ℤ) - 1) / 2) ≤ lower o ∧ lower o ≤ o ∧ o ≤ upper o ∧ upper o ≤ ((L : ℤ) - 1) / 2
  interval_eq : ∀ o o', |o| ≤ ((L : ℤ) - 1) / 2 → lower o ≤ o' → o' ≤ upper o →
    lower o' = lower o ∧ upper o' = upper o
  interval_length : ∀ o, |o| ≤ ((L : ℤ) - 1) / 2 → 2 ^ 14 ≤ upper o - lower o + 1 ∧ upper o - lower o + 1 < 2 ^ 15
  lower_neg : ∀ o, |o| ≤ ((L : ℤ) - 1) / 2 → lower (-o) = - upper o
def offsetFromCentre (L : ℕ) (c : ℤ) : ℤ := (c + ((L : ℤ) - 1) / 2) % (L : ℤ) - ((L : ℤ) - 1) / 2
def lumpOf {L : ℕ} (g : LumpGrid L) {j : ℕ} (x : F.Site j) : Finset (F.Site j) :=
  boxSites j (fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) + g.lower (offsetFromCentre L (siteCoords x i)))
    (fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) + g.upper (offsetFromCentre L (siteCoords x i)))
def IsLump {L : ℕ} (g : LumpGrid L) {j : ℕ} (l : Finset (F.Site j)) : Prop := ∃ x, l = lumpOf g x
open Classical in
def hotLumps {L : ℕ} (g : LumpGrid L) (s : ℝ) {j : ℕ} (X : Finset (F.Site j)) (W : F.GaugeField j) :
    Finset (Finset (F.Site j)) :=
  ((cutPlaquettes X).filter fun p => s ≤ plaquetteDefect W p).biUnion fun p => (plaquetteCorners p).image (lumpOf g)
def torusCells (F : BlockFrame) : Finset F.Cell := boxSites F.top 0 fun i => (F.extent i : ℤ) - 1
def cellBall (y : F.Cell) (r : ℕ) : Finset F.Cell := (centredCube (2 * r + 1)).image fun h => y + siteOfCoords F.top h
open Classical in
def nearbyLumps (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) : Finset (Finset (F.Site F.depth)) :=
  h.filter fun l => l ⊆ cutBelow F.depth (cellBall y 2)
def IsCrowded (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) : Prop :=
  J₀ ≤ (nearbyLumps h y).card
def IsSmallBox (F : BlockFrame) {j : ℕ} (B : Finset (F.Site j)) : Prop :=
  ∃ lo hi : Fin 4 → ℤ, (∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 < F.blockSide) ∧ B = boxSites j lo hi
def IsSeparatedCover {j : ℕ} (seeds Z : Finset (Finset (F.Site j))) : Prop :=
  (∀ B ∈ Z, IsSmallBox F B) ∧ (∀ l ∈ seeds, ∃ B ∈ Z, l ⊆ B) ∧
    ∀ B ∈ Z, ∀ B' ∈ Z, B ≠ B' → ¬ AreWithin 2 B B'
def IsLeastSeparatedCover {j : ℕ} (seeds Z : Finset (Finset (F.Site j))) : Prop :=
  IsSeparatedCover seeds Z ∧ ∀ Z', IsSeparatedCover seeds Z' → ∀ B ∈ Z, ∃ B' ∈ Z', B ⊆ B'
open Classical in
def mergedBoxes {j : ℕ} (seeds : Finset (Finset (F.Site j))) : Finset (Finset (F.Site j)) :=
  if h : ∃ Z, IsLeastSeparatedCover seeds Z then h.choose else ∅
open Classical in
def excludedBoxes (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    Finset (Finset (F.Site F.depth)) :=
  if IsCrowded J₀ h y then ∅ else mergedBoxes ((nearbyLumps h y).image lumpCollar)
def IsBaseChoice (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) : Prop :=
  ∀ y, ((nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) → b y = cellCentre F.depth y) ∧
    (¬ (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) → b y ∈ sitesBelow F.depth y ∧
      ∀ B ∈ excludedBoxes J₀ h y, ∀ x ∈ B, ∀ i, x i ≠ b y i)
def minimalOffset {j : ℕ} (x x' : F.Site j) : Fin 4 → ℤ := fun i => ((x' - x) i).valMinAbs
def contourPath (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    List PathStep :=
  axisPath (minimalOffset (b c.1) (cellCentre F.depth c.1 + siteOfCoords F.depth ξ)) π ++ List.replicate F.blockSide (c.2, true) ++
    reversePath (axisPath (minimalOffset (b (c.1 + unitStep F.top c.2))
      (cellCentre F.depth (c.1 + unitStep F.top c.2) + siteOfCoords F.depth ξ)) π)
def pathSites {j : ℕ} : F.Site j → List PathStep → List (F.Site j)
  | x, [] => [x]
  | x, st :: r => x :: pathSites (x + stepDisplacement j st) r
def IsGoodContour (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : Prop :=
  ∀ x ∈ pathSites (b c.1) (contourPath b c ξ π),
    ∀ B ∈ excludedBoxes J₀ h c.1 ∪ excludedBoxes J₀ h (c.1 + unitStep F.top c.2), x ∉ B
def allContours (F : BlockFrame) : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) := centredCube F.blockSide ×ˢ Finset.univ
open Classical in
def usedContours (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4) : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :=
  if IsCrowded J₀ h c.1 ∨ IsCrowded J₀ h (c.1 + unitStep F.top c.2) ∨
      ((allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2) = ∅
  then allContours F
  else (allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2
def contourMean (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth)
    (c : F.Cell × Fin 4) : ℍ[ℝ] :=
  (1 / ((usedContours J₀ h b c).card : ℝ)) • ∑ e ∈ usedContours J₀ h b c,
    ((pathHolonomy W (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])
def contourFit (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Cell × Fin 4) : ℝ :=
  ‖contourMean J₀ h b W c‖ - (contourMean J₀ h b W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re
open Classical in
def minimalLog (g : UnitQuaternion) : imaginaryQuaternions :=
  if h : ∃ w : imaginaryQuaternions, expUnit w = g ∧ ∀ w' : imaginaryQuaternions, expUnit w' = g → ‖(w : ℍ[ℝ])‖ ≤ ‖(w' : ℍ[ℝ])‖
  then h.choose else 0
def axialGauge (π : Equiv.Perm (Fin 4)) (W : F.GaugeField F.depth) (x : F.Site F.depth) : UnitQuaternion :=
  pathHolonomy W (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) π)
open Classical in
def bondCoordinate (π : Equiv.Perm (Fin 4)) (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) : imaginaryQuaternions :=
  if IsCrossingBond b then minimalLog (gaugeTransform (axialGauge π W) W b.1 b.2 * (V (enclosingCell b.1) b.2)⁻¹)
  else minimalLog (gaugeTransform (axialGauge π W) W b.1 b.2)
def IsMinimizingField (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (Wl : F.GaugeField F.depth) : Prop :=
  ∀ W', plainBlockEnergy a S Wl V ≤ plainBlockEnergy a S W' V
end LumpContours
end YangMills.Construction
end
