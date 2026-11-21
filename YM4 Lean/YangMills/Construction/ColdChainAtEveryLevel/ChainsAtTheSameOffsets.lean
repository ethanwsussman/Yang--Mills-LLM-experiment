import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfAgreeingPairs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.SameOffsets
open LatticePaths LatticeFractionalIntegration
variable {F F' : BlockFrame} {j : ℕ}
section Sites
def siteAtOffset (Y : F.Cell) (j : ℕ) (p : Lattice4) : F.Site j := cellCentre j Y + siteOfCoords j p
def scaleOffset (L : ℕ) (p : Lattice4) : Lattice4 := fun i => (L : ℤ) * p i
theorem siteAtOffset_add (Y : F.Cell) (j : ℕ) (p a : Lattice4) :
    siteAtOffset Y j (p + a) = siteAtOffset Y j p + siteOfCoords j a := by
  simp only [siteAtOffset, siteOfCoords_add, add_assoc]
theorem siteAtOffset_add_stepDisplacement (Y : F.Cell) (j : ℕ) (p : Lattice4) (st : PathStep) :
    siteAtOffset Y j p + BlockAverages.stepDisplacement j st =
      siteAtOffset Y j (p + FlatPairing.stepDisplacement st) := by
  rw [siteAtOffset_add, ChartCoordinates.stepDisplacement_eq_siteOfCoords]
theorem siteAtOffset_add_unitStep (Y : F.Cell) (j : ℕ) (p : Lattice4) (i : Fin 4) :
    siteAtOffset Y j p + unitStep j i = siteAtOffset Y j (p + basisVector i) := by
  rw [siteAtOffset_add, unitStep_eq]
theorem refineSite_siteAtOffset (hj : j + 1 ≤ F.top) (Y : F.Cell) (p : Lattice4) :
    refineSite (siteAtOffset Y (j + 1) p) = siteAtOffset Y j (scaleOffset F.blockSide p) := by
  simp only [siteAtOffset]
  rw [refineSite_add j hj, ChartCoordinates.refineSite_cellCentre j hj]
  rfl
def IsSmallOffset (F : BlockFrame) (j : ℕ) (p : Lattice4) : Prop :=
  ∀ i, |p i| < 32 * (F.blockSide : ℤ) ^ (F.top - j)
theorem valMinAbs_siteOfCoords (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {p : Lattice4}
    (hp : IsSmallOffset F j p) (i : Fin 4) :
    ((siteOfCoords (F := F) j p) i).valMinAbs = p i := by
  refine valMinAbs_intCast_of_small ?_
  rcases hamb with h | h
  · left
    simp [BlockFrame.period, h i]
  · right
    have h1 := hp i
    have hk : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := by positivity
    have h2 : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h i
    simp only [BlockFrame.period]
    push_cast
    nlinarith
theorem siteAtSameOffset_siteAtOffset (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) (Y : F.Cell)
    (Y' : F'.Cell) {p : Lattice4} (hp : IsSmallOffset F j p) :
    siteAtSameOffset Y Y' (siteAtOffset Y j p) = siteAtOffset Y' j p := by
  unfold siteAtSameOffset siteAtOffset
  congr 2
  funext i
  rw [add_sub_cancel_left]
  exact valMinAbs_siteOfCoords hamb hL hp i
theorem siteAtOffset_inj_of_small (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) (Y : F.Cell)
    {p q : Lattice4} (hp : IsSmallOffset F j p) (hq : IsSmallOffset F j q)
    (h : siteAtOffset Y j p = siteAtOffset Y j q) : p = q := by
  have h1 : siteOfCoords (F := F) j p = siteOfCoords j q := add_left_cancel h
  funext i
  rw [← valMinAbs_siteOfCoords hamb hL hp i, h1, valMinAbs_siteOfCoords hamb hL hq i]
def IsNearCells (Y : F.Cell) (D : Finset F.Cell) : Prop :=
  ∀ y ∈ D, ∃ a : Lattice4, (∀ i, |a i| ≤ 1) ∧ y = Y + siteOfCoords F.top a
def IsRegionOffset (Y : F.Cell) (D : Finset F.Cell) (j : ℕ) (p : Lattice4) : Prop :=
  siteAtOffset Y j p ∈ sitesOfCells D j ∧ IsSmallOffset F j p
theorem abs_offset_le_of_region (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hj : j ≤ F.top)
    {Y : F.Cell} {D : Finset F.Cell} (hD : IsNearCells Y D) {p : Lattice4} (hp : IsRegionOffset Y D j p)
    (i : Fin 4) : |p i| ≤ 2 * (F.blockSide : ℤ) ^ (F.top - j) := by
  obtain ⟨y, hy, g, hg, e⟩ := mem_sitesOfCells.1 hp.1
  obtain ⟨a, ha, rfl⟩ := hD y hy
  set K : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hK
  have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast hodd.pos)
  have hgc := (mem_centredCube_iff _ _).1 hg
  have hcast : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = K := by
    rw [hK]
    push_cast
    rfl
  rw [hcast] at hgc
  have hgb : ∀ i, |g i| ≤ K := fun i => by
    have := hgc i
    rw [abs_le]
    constructor <;> omega
  rw [cellCentre_add j hj, add_assoc, ← siteOfCoords_add] at e
  have hq : IsSmallOffset F j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) := fun i => by
    have h1 := ha i
    have h2 := hgb i
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j))]
    rw [← hK]
    nlinarith
  have hpq := siteAtOffset_inj_of_small hamb hodd.pos Y hp.2 hq e
  rw [hpq]
  simp only [Pi.add_apply]
  refine (abs_add_le _ _).trans ?_
  have h1 := ha i
  have h2 := hgb i
  rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j)), ← hK]
  nlinarith
end Sites
section Holonomy
theorem allAlong_of_translate {P : Lattice4 → Prop} (v₀ : Lattice4) : ∀ (l : List PathStep) (u : Lattice4),
    AllAlong (fun v => P (v₀ + v)) u l → AllAlong P (v₀ + u) l := by
  intro l
  induction l with
  | nil => intro u h; exact h
  | cons st r ih =>
    intro u h
    refine ⟨h.1, ?_⟩
    have := ih _ h.2
    rwa [← add_assoc] at this
theorem allAlong_and {P Q : Lattice4 → Prop} : ∀ (l : List PathStep) (u : Lattice4), AllAlong P u l →
    AllAlong Q u l → AllAlong (fun v => P v ∧ Q v) u l := by
  intro l
  induction l with
  | nil => intro u h1 h2; exact ⟨h1, h2⟩
  | cons st r ih =>
    intro u h1 h2
    exact ⟨⟨h1.1, h2.1⟩, ih _ h1.2 h2.2⟩
theorem pathHolonomy_eq_of_agree {X : F.GaugeField j} {X' : F'.GaugeField j} {Y : F.Cell} {Y' : F'.Cell}
    {P : Lattice4 → Prop}
    (H : ∀ p i, P p → P (p + basisVector i) → X (siteAtOffset Y j p) i = X' (siteAtOffset Y' j p) i) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong P v l →
      pathHolonomy X (siteAtOffset Y j v) l = pathHolonomy X' (siteAtOffset Y' j v) l := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons st r ih =>
    intro v hp
    simp only [pathHolonomy]
    rw [siteAtOffset_add_stepDisplacement, siteAtOffset_add_stepDisplacement, ih _ hp.2]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · have e0 : v + FlatPairing.stepDisplacement (i, false) = v - basisVector i := by
        simp [FlatPairing.stepDisplacement, sub_eq_add_neg]
      have hn : P (v + FlatPairing.stepDisplacement (i, false)) := allAlong_head hp.2
      have e1 : ∀ {G : BlockFrame} (Z : G.Cell),
          siteAtOffset Z j v - unitStep j i = siteAtOffset Z j (v + FlatPairing.stepDisplacement (i, false)) := by
        intro G Z
        rw [e0, sub_eq_add_neg v, siteAtOffset_add, siteOfCoords_neg, unitStep_eq, sub_eq_add_neg]
      simp only [linkValue, Bool.false_eq_true, if_false]
      rw [e1, e1, H _ i hn (by rw [e0, sub_add_cancel]; exact hp.1)]
    · have hn : P (v + FlatPairing.stepDisplacement (i, true)) := allAlong_head hp.2
      have e0 : v + FlatPairing.stepDisplacement (i, true) = v + basisVector i := by
        simp [FlatPairing.stepDisplacement]
      simp only [linkValue, if_true]
      exact H v i hp.1 (e0 ▸ hn)
end Holonomy
section Means
variable {Y : F.Cell} {Y' : F'.Cell} {D : Finset F.Cell}
def AgreeOnRegion (Y : F.Cell) (Y' : F'.Cell) (D : Finset F.Cell) (j : ℕ) (X : F.GaugeField j)
    (X' : F'.GaugeField j) : Prop :=
  ∀ p i, IsRegionOffset Y D j p → IsRegionOffset Y D j (p + basisVector i) →
    X (siteAtOffset Y j p) i = X' (siteAtOffset Y' j p) i
theorem pathHolonomy_refineSite_eq (hL : F'.blockSide = F.blockSide) (hj : j + 1 ≤ F.top)
    (hj' : j + 1 ≤ F'.top) {X : F.GaugeField j} {X' : F'.GaugeField j} (h : AgreeOnRegion Y Y' D j X X')
    {q : Lattice4} {l : List PathStep}
    (hp : AllAlong (fun v => IsRegionOffset Y D j (scaleOffset F.blockSide q + v)) 0 l) :
    pathHolonomy X (refineSite (siteAtOffset Y (j + 1) q)) l =
      pathHolonomy X' (refineSite (siteAtOffset Y' (j + 1) q)) l := by
  rw [refineSite_siteAtOffset hj, refineSite_siteAtOffset hj', hL]
  have h1 := allAlong_of_translate (P := IsRegionOffset Y D j) (scaleOffset F.blockSide q) l 0 hp
  rw [add_zero] at h1
  exact pathHolonomy_eq_of_agree h l _ h1
theorem isSmallOffset_scaleOffset_add (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hj : j + 1 ≤ F.top) (hD : IsNearCells Y D) {q : Lattice4} (hq : IsRegionOffset Y D (j + 1) q)
    {v : Lattice4} (hv : ∀ i, |v i| ≤ 2 * (F.blockSide : ℤ)) :
    IsSmallOffset F j (scaleOffset F.blockSide q + v) := by
  intro i
  have h1 := abs_offset_le_of_region hamb hodd hj hD hq i
  have h2 := hv i
  have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have e : (F.blockSide : ℤ) ^ (F.top - j) = (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ (F.top - (j + 1)) := by
    have : F.top - j = (F.top - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  set K : ℤ := (F.blockSide : ℤ) ^ (F.top - (j + 1)) with hK
  have hK1 : 1 ≤ K := one_le_pow₀ hL1
  rw [e]
  simp only [Pi.add_apply, scaleOffset]
  refine (abs_add_le _ _).trans_lt ?_
  rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < (F.blockSide : ℤ))]
  nlinarith
theorem abs_le_of_betweenOrigin (hodd : Odd F.blockSide) {h v : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (hv : BetweenOrigin h v) (i : Fin 4) : |v i| ≤ 2 * (F.blockSide : ℤ) := by
  have h1 := (mem_centredCube_iff _ _).1 hh i
  have h2 := hv i
  have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have a1 : min 0 (h i) ≥ -(((F.blockSide : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h i) ≤ ((F.blockSide : ℤ) - 1) / 2 := max_le (by omega) h1.2
  rw [abs_le]
  constructor <;> omega
theorem abs_le_of_mem_twoBlockHull (hodd : Odd F.blockSide) {i : Fin 4} {v : Lattice4}
    (hv : v ∈ FlatPairing.twoBlockHull F.blockSide i) (μ : Fin 4) : |v μ| ≤ 2 * (F.blockSide : ℤ) := by
  have h1 := hv μ
  have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  rw [abs_le]
  split_ifs at h1 <;> constructor <;> omega
theorem allAlong_axisPath_region (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    (hD : IsNearCells Y D) {q : Lattice4} (hq : IsRegionOffset Y D (j + 1) q) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => IsRegionOffset Y D j (scaleOffset F.blockSide q + v)) 0 (axisPath h π) := by
  have h1 := ChartCoordinates.allAlong_axisPath hodd hj hq.1 hh π
  have h2 := (axisPath_spec h π).1
  refine allAlong_mono (fun v hv => ⟨?_, isSmallOffset_scaleOffset_add hamb hodd hj hD hq
    (abs_le_of_betweenOrigin hodd hh hv.2)⟩) (allAlong_and _ _ h1 h2)
  rw [siteAtOffset_add, ← refineSite_siteAtOffset hj]
  exact hv.1
theorem allAlong_bondContour_region (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hj : j + 1 ≤ F.top) (hD : IsNearCells Y D) {q : Lattice4} {i : Fin 4} (hq : IsRegionOffset Y D (j + 1) q)
    (hq' : IsRegionOffset Y D (j + 1) (q + basisVector i)) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => IsRegionOffset Y D j (scaleOffset F.blockSide q + v)) 0
      (bondContour F.blockSide h π i) := by
  have hc : ((siteAtOffset Y (j + 1) q, i) : F.Site (j + 1) × Fin 4) ∈ innerBonds D (j + 1) :=
    ChartCoordinates.mem_innerBonds hq.1 (by rw [siteAtOffset_add_unitStep]; exact hq'.1)
  have h1 := ChartCoordinates.allAlong_bondContour hodd hj hc hh π
  have h2 := (bondContour_spec π i hodd.pos hh).1
  refine allAlong_mono (fun v hv => ⟨?_, isSmallOffset_scaleOffset_add hamb hodd hj hD hq
    (fun μ => abs_le_of_mem_twoBlockHull hodd hv.2 μ)⟩) (allAlong_and _ _ h1 h2)
  rw [siteAtOffset_add, ← refineSite_siteAtOffset hj]
  exact hv.1
theorem relativePathAverage_eq_of_agree (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) (hD : IsNearCells Y D)
    {X R : F.GaugeField j} {X' R' : F'.GaugeField j} (hX : AgreeOnRegion Y Y' D j X X')
    (hR : AgreeOnRegion Y Y' D j R R') {q : Lattice4} (hq : IsRegionOffset Y D (j + 1) q) :
    relativePathAverage X R (siteAtOffset Y (j + 1) q) = relativePathAverage X' R' (siteAtOffset Y' (j + 1) q) := by
  unfold relativePathAverage
  rw [hL]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  have hp := allAlong_axisPath_region hamb hodd hj hD hq hh π
  rw [pathHolonomy_refineSite_eq hL hj hj' hX hp, pathHolonomy_refineSite_eq hL hj hj' hR hp]
theorem balancingGauge_eq_of_agree (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) (hD : IsNearCells Y D)
    {X R : F.GaugeField j} {X' R' : F'.GaugeField j} (hX : AgreeOnRegion Y Y' D j X X')
    (hR : AgreeOnRegion Y Y' D j R R') {q : Lattice4} (hq : IsRegionOffset Y D (j + 1) q) :
    balancingGauge X R (siteAtOffset Y (j + 1) q) = balancingGauge X' R' (siteAtOffset Y' (j + 1) q) := by
  unfold balancingGauge
  rw [relativePathAverage_eq_of_agree hamb hodd hL hj hj' hD hX hR hq]
theorem contourAverage_eq_of_agree (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) (hD : IsNearCells Y D)
    {X : F.GaugeField j} {X' : F'.GaugeField j} (hX : AgreeOnRegion Y Y' D j X X') {q : Lattice4} {i : Fin 4}
    (hq : IsRegionOffset Y D (j + 1) q) (hq' : IsRegionOffset Y D (j + 1) (q + basisVector i)) :
    contourAverage X ((siteAtOffset Y (j + 1) q, i) : F.Site (j + 1) × Fin 4) =
      contourAverage X' ((siteAtOffset Y' (j + 1) q, i) : F'.Site (j + 1) × Fin 4) := by
  unfold contourAverage
  rw [hL]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  simp only
  rw [pathHolonomy_refineSite_eq hL hj hj' hX (allAlong_bondContour_region hamb hodd hj hD hq hq' hh π)]
end Means
section Fields
variable {Y : F.Cell} {Y' : F'.Cell} {D : Finset F.Cell}
theorem chartField_agree (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hn : F'.top = F.top) (hD : IsNearCells Y D) (R : F.FieldChain)
    (R' : F'.FieldChain) (U' : ChainChart F')
    (hR : ∀ j, j < F.top → AgreeOnRegion Y Y' D j (R j) (R' j)) :
    ∀ j, j < F.top → AgreeOnRegion Y Y' D j (chartField R (chartAtSameOffsets Y Y' U') j)
      (chartField R' U' j) := by
  intro j
  induction j with
  | zero =>
    intro h0 p i hp hp'
    simp only [chartField, chartAtSameOffsets]
    rw [siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hp.2, hR 0 h0 p i hp hp']
  | succ j ih =>
    intro hj p i hp hp'
    have hj1 : j < F.top := by omega
    have hj2 : j + 1 ≤ F.top := by omega
    have hj3 : j + 1 ≤ F'.top := by omega
    have hX := ih hj1
    have hRj := hR j hj1
    simp only [chartField]
    have e0 : (chartAtSameOffsets Y Y' U').coarse j (siteAtOffset Y (j + 1) p) i =
        U'.coarse j (siteAtOffset Y' (j + 1) p) i := by
      show U'.coarse j (siteAtSameOffset Y Y' (siteAtOffset Y (j + 1) p)) i = _
      rw [siteAtSameOffset_siteAtOffset hamb hodd.pos Y Y' hp.2]
    have e1 : referenceDefect R j (siteAtOffset Y (j + 1) p, i) =
        referenceDefect R' j (siteAtOffset Y' (j + 1) p, i) := by
      unfold referenceDefect
      simp only
      rw [hR (j + 1) hj p i hp hp', contourAverage_eq_of_agree hamb hodd hL hj2 hj3 hD hRj hp hp']
    have e2 : gaugedContourAverage (chartField R (chartAtSameOffsets Y Y' U') j)
          (balancingGauge (chartField R (chartAtSameOffsets Y Y' U') j) (R j)) (siteAtOffset Y (j + 1) p, i) =
        gaugedContourAverage (chartField R' U' j) (balancingGauge (chartField R' U' j) (R' j))
          (siteAtOffset Y' (j + 1) p, i) := by
      unfold gaugedContourAverage
      simp only
      have k2 : balancingGauge (chartField R (chartAtSameOffsets Y Y' U') j) (R j)
            (siteAtOffset Y (j + 1) p + unitStep (j + 1) i) =
          balancingGauge (chartField R' U' j) (R' j) (siteAtOffset Y' (j + 1) p + unitStep (j + 1) i) := by
        rw [siteAtOffset_add_unitStep, siteAtOffset_add_unitStep]
        exact balancingGauge_eq_of_agree hamb hodd hL hj2 hj3 hD hX hRj hp'
      rw [balancingGauge_eq_of_agree hamb hodd hL hj2 hj3 hD hX hRj hp, k2,
        contourAverage_eq_of_agree hamb hodd hL hj2 hj3 hD hX hp hp']
    rw [e0, e1, e2]
theorem chartGauge_eq_of_agree (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hn : F'.top = F.top) (hD : IsNearCells Y D) (R : F.FieldChain)
    (R' : F'.FieldChain) (U' : ChainChart F') (hR : ∀ j, j < F.top → AgreeOnRegion Y Y' D j (R j) (R' j))
    {j : ℕ} (hj : j < F.top) {q : Lattice4} (hq : IsRegionOffset Y D (j + 1) q) :
    chartGauge R (chartAtSameOffsets Y Y' U') (j + 1) (siteAtOffset Y (j + 1) q) =
      chartGauge R' U' (j + 1) (siteAtOffset Y' (j + 1) q) :=
  balancingGauge_eq_of_agree hamb hodd hL (by omega) (by omega) hD
    (chartField_agree hamb hodd hL hn hD R R' U' hR j hj) (hR j hj) hq
theorem isInnerOffset_of_region (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hD : IsNearCells Y D)
    {r : ℕ} (hr : 102 ≤ r) {j : ℕ} (hj : j ≤ F.top) {p : Lattice4} (hp : IsRegionOffset Y D j p) :
    IsInnerOffset F.blockSide F.top r j p := by
  intro i
  have h1 := abs_offset_le_of_region hamb hodd hj hD hp i
  have hL1 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have e : (F.blockSide : ℤ) ^ F.top = (F.blockSide : ℤ) ^ j * (F.blockSide : ℤ) ^ (F.top - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hj0 : (0 : ℤ) < (F.blockSide : ℤ) ^ j := by positivity
  have hk0 : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by positivity
  have h2 : (F.blockSide : ℤ) ^ j * |p i| ≤ 2 * (F.blockSide : ℤ) ^ F.top := by
    rw [e]
    nlinarith
  nlinarith
theorem referenceFieldChain_agree (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hn : F'.top = F.top)
    (hD : IsNearCells Y D) {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {r : ℕ} (hr : 102 ≤ r) (hDS : D ⊆ S)
    (hlines : ∀ (j : ℕ) (p : Fin 4 → ℤ) (i : Fin 4), j < F.top → IsInnerOffset F.blockSide F.top r j p →
      IsInnerOffset F.blockSide F.top r j (p + Pi.single i 1) →
      (cellCentre j Y + siteOfCoords j p, i) ∈ innerBonds S j →
      referenceGaugeField S V j (cellCentre j Y + siteOfCoords j p) i =
        referenceGaugeField S' V' j (cellCentre j Y' + siteOfCoords j p) i) :
    ∀ j, j < F.top → AgreeOnRegion Y Y' D j (referenceFieldChain S V j) (referenceFieldChain S' V' j) := by
  classical
  intro j hj p i hp hp'
  have e1 : referenceFieldChain S V j = referenceGaugeField S V j := by
    unfold referenceFieldChain
    exact Function.update_of_ne (by omega) _ _
  have e2 : referenceFieldChain S' V' j = referenceGaugeField S' V' j := by
    unfold referenceFieldChain
    exact Function.update_of_ne (by omega) _ _
  rw [e1, e2]
  have hsub : ∀ {x : F.Site j}, x ∈ sitesOfCells D j → x ∈ sitesOfCells S j := fun hx => by
    obtain ⟨y, hy, g, hg, e⟩ := mem_sitesOfCells.1 hx
    exact mem_sitesOfCells.2 ⟨y, hDS hy, g, hg, e⟩
  have hb : (cellCentre j Y + siteOfCoords j p, i) ∈ innerBonds S j :=
    ChartCoordinates.mem_innerBonds (hsub hp.1) (by
      have := siteAtOffset_add_unitStep Y j p i
      have h2 := hsub hp'.1
      rw [← this] at h2
      exact h2)
  exact hlines j p i hj (isInnerOffset_of_region hamb hodd hD hr hj.le hp)
    (isInnerOffset_of_region hamb hodd hD hr hj.le hp')
    hb
end Fields
end YangMills.Construction.BlockAverages.SameOffsets
end
