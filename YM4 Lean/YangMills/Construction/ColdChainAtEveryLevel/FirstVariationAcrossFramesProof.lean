import YangMills.Construction.ColdChainAtEveryLevel.BondsAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.ChainsAtTheSameOffsets
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.FramedFirstVariation
open BlockAverages LatticePaths LatticeFractionalIntegration BlockAverages.Offsets BlockAverages.ChartCoordinates
  BlockAverages.ComplexChartCoordinates
variable {F F' : BlockFrame} {j : ℕ}
theorem siteAtOffset_add (Y : F.Cell) (j : ℕ) (p a : Lattice4) :
    siteAtOffset j Y (p + a) = siteAtOffset j Y p + siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.siteAtOffset_add <;> assumption
theorem siteAtOffset_add_stepDisplacement (Y : F.Cell) (j : ℕ) (p : Lattice4) (st : PathStep) :
    siteAtOffset j Y p + stepDisplacement j st = siteAtOffset j Y (p + FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.siteAtOffset_add_stepDisplacement <;> assumption
theorem siteAtOffset_add_unitStep (Y : F.Cell) (j : ℕ) (p : Lattice4) (i : Fin 4) :
    siteAtOffset j Y p + unitStep j i = siteAtOffset j Y (p + basisVector i) := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.siteAtOffset_add_unitStep <;> assumption
def scaleOffset (L : ℕ) (p : Lattice4) : Lattice4 := fun i => (L : ℤ) * p i
theorem refineSite_siteAtOffset (hj : j + 1 ≤ F.top) (Y : F.Cell) (p : Lattice4) :
    _root_.YangMills.Construction.BlockAverages.refineSite (siteAtOffset (j + 1) Y p) = siteAtOffset j Y (scaleOffset F.blockSide p) := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.refineSite_siteAtOffset <;> assumption
theorem siteAtOffset_sub_unitStep (Y : F.Cell) (j : ℕ) (v : Lattice4) (i : Fin 4) :
    siteAtOffset j Y v - unitStep j i = siteAtOffset j Y (v + FlatPairing.stepDisplacement (i, false)) := by
  have e0 : v + FlatPairing.stepDisplacement (i, false) = v - basisVector i := by
    simp [FlatPairing.stepDisplacement, sub_eq_add_neg]
  rw [e0, sub_eq_add_neg v, siteAtOffset_add, siteOfCoords_neg, unitStep_eq, sub_eq_add_neg]
theorem pathHolonomy_eq_of_agree {X : F.GaugeField j} {X' : F'.GaugeField j} {Y : F.Cell} {Y' : F'.Cell}
    {P : Lattice4 → Prop}
    (H : ∀ p i, P p → P (p + basisVector i) → X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong P v l →
      pathHolonomy X (siteAtOffset j Y v) l = pathHolonomy X' (siteAtOffset j Y' v) l := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.pathHolonomy_eq_of_agree <;> assumption
theorem complexPathHolonomy_eq_of_agree {X : F.ComplexField j} {X' : F'.ComplexField j} {Y : F.Cell} {Y' : F'.Cell}
    {P : Lattice4 → Prop}
    (H : ∀ p i, P p → P (p + basisVector i) → X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong P v l →
      complexPathHolonomy X (siteAtOffset j Y v) l = complexPathHolonomy X' (siteAtOffset j Y' v) l := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons st r ih =>
    intro v hp
    simp only [complexPathHolonomy]
    rw [siteAtOffset_add_stepDisplacement, siteAtOffset_add_stepDisplacement, ih _ hp.2]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · have e0 : v + FlatPairing.stepDisplacement (i, false) = v - basisVector i := by
        simp [FlatPairing.stepDisplacement, sub_eq_add_neg]
      have hn : P (v + FlatPairing.stepDisplacement (i, false)) := allAlong_head hp.2
      simp only [complexLinkValue, Bool.false_eq_true, if_false]
      rw [siteAtOffset_sub_unitStep, siteAtOffset_sub_unitStep, H _ i hn (by rw [e0, sub_add_cancel]; exact hp.1)]
    · have hn : P (v + FlatPairing.stepDisplacement (i, true)) := allAlong_head hp.2
      have e0 : v + FlatPairing.stepDisplacement (i, true) = v + basisVector i := by
        simp [FlatPairing.stepDisplacement]
      simp only [complexLinkValue, if_true]
      exact H v i hp.1 (e0 ▸ hn)
def InLevelBall (L j : ℕ) (ρ : ℤ) (p : Lattice4) : Prop := ∀ i, (L : ℤ) ^ j * |p i| ≤ ρ
theorem allAlong_translate {P : Lattice4 → Prop} (v₀ : Lattice4) : ∀ (l : List PathStep) (u : Lattice4),
    AllAlong (fun v => P (v₀ + v)) u l → AllAlong P (v₀ + u) l := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.allAlong_of_translate <;> assumption
theorem abs_le_of_betweenOrigin (hodd : Odd F.blockSide) {h v : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (hv : BetweenOrigin h v) (i : Fin 4) : |v i| ≤ 2 * (F.blockSide : ℤ) := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.abs_le_of_betweenOrigin <;> assumption
theorem abs_le_of_mem_twoBlockHull (hodd : Odd F.blockSide) {i : Fin 4} {v : Lattice4}
    (hv : v ∈ FlatPairing.twoBlockHull F.blockSide i) (μ : Fin 4) : |v μ| ≤ 2 * (F.blockSide : ℤ) := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.abs_le_of_mem_twoBlockHull <;> assumption
theorem inLevelBall_refine (hL0 : (0 : ℤ) < F.blockSide) {ρ ρ' : ℤ} {q v : Lattice4}
    (hq : InLevelBall F.blockSide (j + 1) ρ' q) (hv : ∀ i, |v i| ≤ 2 * (F.blockSide : ℤ))
    (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ) :
    InLevelBall F.blockSide j ρ (scaleOffset F.blockSide q + v) := by
  intro i
  have h1 := hq i
  have h2 := hv i
  have hp : (0 : ℤ) < (F.blockSide : ℤ) ^ j := pow_pos hL0 j
  have h3 : |(scaleOffset F.blockSide q + v) i| ≤ (F.blockSide : ℤ) * |q i| + 2 * (F.blockSide : ℤ) := by
    simp only [Pi.add_apply, scaleOffset]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hL0]
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hp.le
  have e : (F.blockSide : ℤ) ^ j * ((F.blockSide : ℤ) * |q i| + 2 * (F.blockSide : ℤ)) =
      (F.blockSide : ℤ) ^ (j + 1) * |q i| + 2 * (F.blockSide : ℤ) ^ (j + 1) := by
    rw [pow_succ]
    ring
  rw [e] at h4
  linarith
def InRegion (S : Finset F.Cell) (Y : F.Cell) (j : ℕ) (ρ : ℤ) (p : Lattice4) : Prop :=
  InLevelBall F.blockSide j ρ p ∧ siteAtOffset j Y p ∈ sitesOfCells S j
section Averages
variable {Y : F.Cell} {Y' : F'.Cell}
theorem pathHolonomy_refine_eq (hL : F'.blockSide = F.blockSide) (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top)
    {P : Lattice4 → Prop} {X : F.GaugeField j} {X' : F'.GaugeField j}
    (H : ∀ p i, P p → P (p + basisVector i) → X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i) {q : Lattice4}
    {l : List PathStep} (hp : AllAlong (fun v => P (scaleOffset F.blockSide q + v)) 0 l) :
    pathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite (siteAtOffset (j + 1) Y q)) l =
      pathHolonomy X' (_root_.YangMills.Construction.BlockAverages.refineSite (siteAtOffset (j + 1) Y' q)) l := by
  rw [refineSite_siteAtOffset hj, refineSite_siteAtOffset hj', hL]
  have h1 := allAlong_translate (P := P) (scaleOffset F.blockSide q) l 0 hp
  rw [add_zero] at h1
  exact pathHolonomy_eq_of_agree H l _ h1
theorem complexPathHolonomy_refine_eq (hL : F'.blockSide = F.blockSide) (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top)
    {P : Lattice4 → Prop} {X : F.ComplexField j} {X' : F'.ComplexField j}
    (H : ∀ p i, P p → P (p + basisVector i) → X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i) {q : Lattice4}
    {l : List PathStep} (hp : AllAlong (fun v => P (scaleOffset F.blockSide q + v)) 0 l) :
    complexPathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite (siteAtOffset (j + 1) Y q)) l =
      complexPathHolonomy X' (_root_.YangMills.Construction.BlockAverages.refineSite (siteAtOffset (j + 1) Y' q)) l := by
  rw [refineSite_siteAtOffset hj, refineSite_siteAtOffset hj', hL]
  have h1 := allAlong_translate (P := P) (scaleOffset F.blockSide q) l 0 hp
  rw [add_zero] at h1
  exact complexPathHolonomy_eq_of_agree H l _ h1
theorem allAlong_and {P Q : Lattice4 → Prop} : ∀ (l : List PathStep) (u : Lattice4), AllAlong P u l →
    AllAlong Q u l → AllAlong (fun v => P v ∧ Q v) u l := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.allAlong_and <;> assumption
variable {S : Finset F.Cell}
theorem refineSite_siteAtOffset_add (hj : j + 1 ≤ F.top) (Y : F.Cell) (q v : Lattice4) :
    _root_.YangMills.Construction.BlockAverages.refineSite (siteAtOffset (j + 1) Y q) + siteOfCoords j v = siteAtOffset j Y (scaleOffset F.blockSide q + v) := by
  rw [refineSite_siteAtOffset hj, siteAtOffset_add]
theorem allAlong_axisPath_region (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {ρ ρ' : ℤ} {q : Lattice4}
    (hq : InLevelBall F.blockSide (j + 1) ρ' q) (hy : siteAtOffset (j + 1) Y q ∈ sitesOfCells S (j + 1))
    (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => InRegion S Y j ρ (scaleOffset F.blockSide q + v)) 0 (axisPath h π) := by
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have h1 := allAlong_mono (q := fun v => InLevelBall F.blockSide j ρ (scaleOffset F.blockSide q + v))
    (fun v hv => inLevelBall_refine hL0 hq (abs_le_of_betweenOrigin hodd hh hv) hρ) (axisPath_spec h π).1
  have h2 := allAlong_mono (q := fun v => siteAtOffset j Y (scaleOffset F.blockSide q + v) ∈ sitesOfCells S j)
    (fun v hv => by
      rw [← refineSite_siteAtOffset_add hj]
      exact Finset.mem_coe.1 hv) (allAlong_axisPath hodd hj hy hh π)
  exact allAlong_and _ _ h1 h2
theorem allAlong_bondContour_region (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {ρ ρ' : ℤ} {q : Lattice4}
    (hq : InLevelBall F.blockSide (j + 1) ρ' q) {i : Fin 4}
    (hc : (siteAtOffset (j + 1) Y q, i) ∈ innerBonds S (j + 1)) (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => InRegion S Y j ρ (scaleOffset F.blockSide q + v)) 0 (bondContour F.blockSide h π i) := by
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have h1 := allAlong_mono (q := fun v => InLevelBall F.blockSide j ρ (scaleOffset F.blockSide q + v))
    (fun v hv => inLevelBall_refine hL0 hq (abs_le_of_mem_twoBlockHull hodd hv) hρ)
    (bondContour_spec π i hodd.pos hh).1
  have h2 := allAlong_mono (q := fun v => siteAtOffset j Y (scaleOffset F.blockSide q + v) ∈ sitesOfCells S j)
    (fun v hv => by
      rw [← refineSite_siteAtOffset_add hj]
      exact Finset.mem_coe.1 hv) (allAlong_bondContour hodd hj hc hh π)
  exact allAlong_and _ _ h1 h2
theorem complexRelativePathAverage_eq_of_agree (hodd : Odd F.blockSide) (hL : F'.blockSide = F.blockSide)
    (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) {ρ ρ' : ℤ}
    {X : F.ComplexField j} {X' : F'.ComplexField j} {R : F.GaugeField j} {R' : F'.GaugeField j}
    (hX : ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
      X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i)
    (hR : ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
      R (siteAtOffset j Y p) i = R' (siteAtOffset j Y' p) i)
    {q : Lattice4} (hq : InLevelBall F.blockSide (j + 1) ρ' q)
    (hy : siteAtOffset (j + 1) Y q ∈ sitesOfCells S (j + 1)) (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ) :
    complexRelativePathAverage X R (siteAtOffset (j + 1) Y q) =
      complexRelativePathAverage X' R' (siteAtOffset (j + 1) Y' q) := by
  unfold complexRelativePathAverage contourWeight
  rw [hL]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  have hp := allAlong_axisPath_region hodd hj hq hy hρ hh π
  rw [complexPathHolonomy_refine_eq hL hj hj' hX hp, pathHolonomy_refine_eq hL hj hj' hR hp]
theorem complexBalancingGauge_eq_of_agree (hodd : Odd F.blockSide) (hL : F'.blockSide = F.blockSide)
    (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) {ρ ρ' : ℤ}
    {X : F.ComplexField j} {X' : F'.ComplexField j} {R : F.GaugeField j} {R' : F'.GaugeField j}
    (hX : ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
      X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i)
    (hR : ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
      R (siteAtOffset j Y p) i = R' (siteAtOffset j Y' p) i)
    {q : Lattice4} (hq : InLevelBall F.blockSide (j + 1) ρ' q)
    (hy : siteAtOffset (j + 1) Y q ∈ sitesOfCells S (j + 1)) (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ) :
    complexBalancingGauge X R (siteAtOffset (j + 1) Y q) = complexBalancingGauge X' R' (siteAtOffset (j + 1) Y' q) := by
  unfold complexBalancingGauge
  rw [complexRelativePathAverage_eq_of_agree hodd hL hj hj' hX hR hq hy hρ]
theorem complexContourAverage_eq_of_agree (hodd : Odd F.blockSide) (hL : F'.blockSide = F.blockSide)
    (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) {ρ ρ' : ℤ}
    {X : F.ComplexField j} {X' : F'.ComplexField j}
    (hX : ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
      X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i)
    {q : Lattice4} (hq : InLevelBall F.blockSide (j + 1) ρ' q) {i : Fin 4}
    (hc : (siteAtOffset (j + 1) Y q, i) ∈ innerBonds S (j + 1)) (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ) :
    complexContourAverage X ((siteAtOffset (j + 1) Y q, i) : F.Site (j + 1) × Fin 4) =
      complexContourAverage X' ((siteAtOffset (j + 1) Y' q, i) : F'.Site (j + 1) × Fin 4) := by
  unfold complexContourAverage contourWeight
  rw [hL]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  simp only
  rw [complexPathHolonomy_refine_eq hL hj hj' hX (allAlong_bondContour_region hodd hj hq hc hρ hh π)]
theorem contourAverage_eq_of_agree (hodd : Odd F.blockSide) (hL : F'.blockSide = F.blockSide)
    (hj : j + 1 ≤ F.top) (hj' : j + 1 ≤ F'.top) {ρ ρ' : ℤ}
    {X : F.GaugeField j} {X' : F'.GaugeField j}
    (hX : ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
      X (siteAtOffset j Y p) i = X' (siteAtOffset j Y' p) i)
    {q : Lattice4} (hq : InLevelBall F.blockSide (j + 1) ρ' q) {i : Fin 4}
    (hc : (siteAtOffset (j + 1) Y q, i) ∈ innerBonds S (j + 1)) (hρ : ρ' + 2 * (F.blockSide : ℤ) ^ (j + 1) ≤ ρ) :
    _root_.YangMills.Construction.BlockAverages.contourAverage X ((siteAtOffset (j + 1) Y q, i) : F.Site (j + 1) × Fin 4) =
      _root_.YangMills.Construction.BlockAverages.contourAverage X' ((siteAtOffset (j + 1) Y' q, i) : F'.Site (j + 1) × Fin 4) := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [hL]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  simp only
  rw [pathHolonomy_refine_eq hL hj hj' hX (allAlong_bondContour_region hodd hj hq hc hρ hh π)]
end Averages
section Fields
variable {Y : F.Cell} {Y' : F'.Cell} {S : Finset F.Cell}
theorem InLevelBall.mono {L j : ℕ} {ρ ρ' : ℤ} (h : ρ ≤ ρ') {p : Lattice4} (hp : InLevelBall L j ρ p) :
    InLevelBall L j ρ' p :=
  fun i => (hp i).trans h
theorem InRegion.mono {j : ℕ} {ρ ρ' : ℤ} (h : ρ ≤ ρ') {p : Lattice4} (hp : InRegion S Y j ρ p) :
    InRegion S Y j ρ' p :=
  ⟨InLevelBall.mono h hp.1, hp.2⟩
def agreementRadius (L : ℕ) (ρ : ℤ) (j : ℕ) : ℤ := ρ - 6 * (L : ℤ) ^ j
theorem agreementRadius_succ_add_le {L : ℕ} (hL : 3 ≤ L) (ρ : ℤ) (j : ℕ) :
    agreementRadius L ρ (j + 1) + 2 * (L : ℤ) ^ (j + 1) ≤ agreementRadius L ρ j := by
  unfold agreementRadius
  have h0 : (0 : ℤ) < (L : ℤ) ^ j := pow_pos (by omega) j
  rw [pow_succ]
  nlinarith
structure ChartsAgree (S : Finset F.Cell) (Y : F.Cell) (Y' : F'.Cell) (ρ : ℤ) (R : F.FieldChain)
    (R' : F'.FieldChain) (W : ComplexChainChart F) (W' : ComplexChainChart F') : Prop where
  fine : ∀ p i, InLevelBall F.blockSide 0 ρ p →
    W.re.fine (siteAtOffset 0 Y p) i = W'.re.fine (siteAtOffset 0 Y' p) i ∧
    W.im.fine (siteAtOffset 0 Y p) i = W'.im.fine (siteAtOffset 0 Y' p) i
  coarse : ∀ j p i, j + 1 < F.top → InLevelBall F.blockSide (j + 1) ρ p →
    W.re.coarse j (siteAtOffset (j + 1) Y p) i = W'.re.coarse j (siteAtOffset (j + 1) Y' p) i ∧
    W.im.coarse j (siteAtOffset (j + 1) Y p) i = W'.im.coarse j (siteAtOffset (j + 1) Y' p) i
  reference : ∀ j, j < F.top → ∀ p i, InRegion S Y j ρ p → InRegion S Y j ρ (p + basisVector i) →
    R j (siteAtOffset j Y p) i = R' j (siteAtOffset j Y' p) i
theorem complexChartField_eq_of_chartsAgree (hodd : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hn : F'.top = F.top) {R : F.FieldChain} {R' : F'.FieldChain}
    {W : ComplexChainChart F} {W' : ComplexChainChart F'} {ρ : ℤ} (h : ChartsAgree S Y Y' ρ R R' W W') :
    ∀ j, j < F.top → ∀ p i, InRegion S Y j (agreementRadius F.blockSide ρ j) p →
      InRegion S Y j (agreementRadius F.blockSide ρ j) (p + basisVector i) →
      complexChartField R W j (siteAtOffset j Y p) i = complexChartField R' W' j (siteAtOffset j Y' p) i := by
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hle : ∀ j, agreementRadius F.blockSide ρ j ≤ ρ := fun j => by
    unfold agreementRadius
    have := pow_pos hLz j
    omega
  intro j
  induction j with
  | zero =>
    intro _ p i hp hp'
    obtain ⟨a1, a2⟩ := h.fine p i (InLevelBall.mono (hle 0) hp.1)
    have hR0 := h.reference 0 (Nat.succ_pos _) p i (InRegion.mono (hle 0) hp) (InRegion.mono (hle 0) hp')
    simp only [complexChartField]
    rw [a1, a2, hR0]
  | succ j ih =>
    intro hj p i hp hp'
    have hj1 : j < F.top := by omega
    have hj2 : j + 1 ≤ F.top := by omega
    have hj3 : j + 1 ≤ F'.top := by omega
    have hX := ih hj1
    have hRj : ∀ p i, InRegion S Y j (agreementRadius F.blockSide ρ j) p →
        InRegion S Y j (agreementRadius F.blockSide ρ j) (p + basisVector i) →
        R j (siteAtOffset j Y p) i = R' j (siteAtOffset j Y' p) i := fun p i h1 h2 =>
      h.reference j hj1 p i (InRegion.mono (hle j) h1) (InRegion.mono (hle j) h2)
    have hstep := agreementRadius_succ_add_le hL3 ρ j
    have hb : (siteAtOffset (j + 1) Y p, i) ∈ innerBonds S (j + 1) := by
      refine ChartCoordinates.mem_innerBonds hp.2 ?_
      rw [siteAtOffset_add_unitStep]
      exact hp'.2
    obtain ⟨a1, a2⟩ := h.coarse j p i hj (InLevelBall.mono (hle _) hp.1)
    have e1 : referenceDefect R j (siteAtOffset (j + 1) Y p, i) =
        referenceDefect R' j (siteAtOffset (j + 1) Y' p, i) := by
      unfold referenceDefect
      simp only
      rw [h.reference (j + 1) hj p i (InRegion.mono (hle _) hp) (InRegion.mono (hle _) hp'),
        contourAverage_eq_of_agree hodd hL hj2 hj3 hRj hp.1 hb hstep]
    have e2 : complexGaugedContourAverage (complexChartField R W j)
        (complexBalancingGauge (complexChartField R W j) (R j)) (siteAtOffset (j + 1) Y p, i) =
        complexGaugedContourAverage (complexChartField R' W' j)
          (complexBalancingGauge (complexChartField R' W' j) (R' j)) (siteAtOffset (j + 1) Y' p, i) := by
      unfold complexGaugedContourAverage
      simp only
      have k2 : complexBalancingGauge (complexChartField R W j) (R j)
          (siteAtOffset (j + 1) Y p + unitStep (j + 1) i) =
          complexBalancingGauge (complexChartField R' W' j) (R' j)
            (siteAtOffset (j + 1) Y' p + unitStep (j + 1) i) := by
        rw [siteAtOffset_add_unitStep, siteAtOffset_add_unitStep]
        exact complexBalancingGauge_eq_of_agree hodd hL hj2 hj3 hX hRj hp'.1 hp'.2 hstep
      rw [complexBalancingGauge_eq_of_agree hodd hL hj2 hj3 hX hRj hp.1 hp.2 hstep, k2,
        complexContourAverage_eq_of_agree hodd hL hj2 hj3 hX hp.1 hb hstep]
    simp only [complexChartField]
    rw [a1, a2, e1, e2]
theorem complexChainOverTop_of_eq_top {F : BlockFrame} {k : ℕ} (hk : k = F.top) (R : F.FieldChain)
    (W : ComplexChainChart F) (T : F.ComplexField F.top) (Y : F.Cell) (p : Lattice4) (i : Fin 4) :
    complexChainOverTop R W T k (siteAtOffset k Y p) i = T (siteAtOffset F.top Y p) i := by
  subst hk
  rw [complexChainOverTop_top]
theorem complexBondTermOverTop_eq_of_chartsAgree (hodd : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hn : F'.top = F.top) {R : F.FieldChain} {R' : F'.FieldChain}
    {W : ComplexChainChart F} {W' : ComplexChainChart F'} {T : F.ComplexField F.top} {T' : F'.ComplexField F'.top}
    {ρ : ℤ} (h : ChartsAgree S Y Y' ρ R R' W W')
    (hT : ∀ (p : Lattice4) (i : Fin 4), InLevelBall F.blockSide F.top ρ p →
      T (siteAtOffset F.top Y p) i = T' (siteAtOffset F'.top Y' p) i)
    {j : ℕ} (hj : j < F.top) {p : Lattice4} {i : Fin 4}
    (hp : InRegion S Y (j + 1) (agreementRadius F.blockSide ρ (j + 1)) p)
    (hp' : InRegion S Y (j + 1) (agreementRadius F.blockSide ρ (j + 1)) (p + basisVector i)) :
    complexBondTermOverTop R W T j (siteAtOffset (j + 1) Y p, i) =
      complexBondTermOverTop R' W' T' j (siteAtOffset (j + 1) Y' p, i) := by
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hle : ∀ j, agreementRadius F.blockSide ρ j ≤ ρ := fun j => by
    unfold agreementRadius
    have := pow_pos hLz j
    omega
  have hj2 : j + 1 ≤ F.top := by omega
  have hj3 : j + 1 ≤ F'.top := by omega
  have hX := complexChartField_eq_of_chartsAgree hodd hL3 hL hn h j hj
  have hRj : ∀ p i, InRegion S Y j (agreementRadius F.blockSide ρ j) p →
      InRegion S Y j (agreementRadius F.blockSide ρ j) (p + basisVector i) →
      R j (siteAtOffset j Y p) i = R' j (siteAtOffset j Y' p) i := fun p i h1 h2 =>
    h.reference j hj p i (InRegion.mono (hle j) h1) (InRegion.mono (hle j) h2)
  have hstep := agreementRadius_succ_add_le hL3 ρ j
  have hj' : j < F'.top := by omega
  have hb : (siteAtOffset (j + 1) Y p, i) ∈ innerBonds S (j + 1) := by
    refine ChartCoordinates.mem_innerBonds hp.2 ?_
    rw [siteAtOffset_add_unitStep]
    exact hp'.2
  unfold complexBondTermOverTop
  rw [complexChainOverTop_of_lt R W T hj, complexChainOverTop_of_lt R' W' T' hj']
  have e2 : complexGaugedContourAverage (complexChartField R W j) (complexBalancingGauges R W (j + 1))
      (siteAtOffset (j + 1) Y p, i) =
      complexGaugedContourAverage (complexChartField R' W' j) (complexBalancingGauges R' W' (j + 1))
        (siteAtOffset (j + 1) Y' p, i) := by
    unfold complexGaugedContourAverage
    simp only [complexBalancingGauges]
    have k2 : complexBalancingGauge (complexChartField R W j) (R j)
        (siteAtOffset (j + 1) Y p + unitStep (j + 1) i) =
        complexBalancingGauge (complexChartField R' W' j) (R' j)
          (siteAtOffset (j + 1) Y' p + unitStep (j + 1) i) := by
      rw [siteAtOffset_add_unitStep, siteAtOffset_add_unitStep]
      exact complexBalancingGauge_eq_of_agree hodd hL hj2 hj3 hX hRj hp'.1 hp'.2 hstep
    rw [complexBalancingGauge_eq_of_agree hodd hL hj2 hj3 hX hRj hp.1 hp.2 hstep, k2,
      complexContourAverage_eq_of_agree hodd hL hj2 hj3 hX hp.1 hb hstep]
  rw [e2]
  congr 1
  by_cases htop : j + 1 = F.top
  · have htop' : j + 1 = F'.top := by omega
    have hbl : InLevelBall F.blockSide F.top ρ p := by
      rw [← htop]
      exact InLevelBall.mono (hle _) hp.1
    exact (complexChainOverTop_of_eq_top htop R W T Y p i).trans
      ((hT p i hbl).trans (complexChainOverTop_of_eq_top htop' R' W' T' Y' p i).symm)
  · have h1 : j + 1 < F.top := by omega
    have h2 : j + 1 < F'.top := by omega
    rw [complexChainOverTop_of_lt R W T h1, complexChainOverTop_of_lt R' W' T' h2]
    exact complexChartField_eq_of_chartsAgree hodd hL3 hL hn h (j + 1) h1 p i hp hp'
end Fields
section Terms
variable {S : Finset F.Cell} {Y : F.Cell} {Y' : F'.Cell}
theorem complexChainOverTop_eq_of_eq_top {F : BlockFrame} {k : ℕ} (hk : k = F.top) (R : F.FieldChain)
    (W₁ W₂ : ComplexChainChart F) (T : F.ComplexField F.top) :
    complexChainOverTop R W₁ T k = complexChainOverTop R W₂ T k := by
  subst hk
  rw [complexChainOverTop_top, complexChainOverTop_top]
theorem terms_eq_of_chartAgreeOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (R : F.FieldChain)
    {W₁ W₂ : ComplexChainChart F} (T : F.ComplexField F.top) {z : F.Cell}
    (h1 : ChartEqOnBonds (cellBall S z 1) W₁.re W₂.re) (h2 : ChartEqOnBonds (cellBall S z 1) W₁.im W₂.im) :
    (∀ p ∈ plaquettesOver S {z} 0,
      complexPlaquetteTerm (complexChartField R W₁ 0) p = complexPlaquetteTerm (complexChartField R W₂ 0) p) ∧
    ∀ j, j < F.top → ∀ c ∈ bondsOver S {z} (j + 1),
      complexBondTermOverTop R W₁ T j c = complexBondTermOverTop R W₂ T j c := by
  classical
  have hF := complexChartField_congr hodd R h1 h2
  refine ⟨fun q hq => ?_, fun j hj c hc => ?_⟩
  · obtain ⟨b1, b2, b3, b4⟩ := PlaquettesNearCell.plaquette_bonds_mem_innerBonds hamb hodd hq
    have hq1 := (CoordinateSeminorms.mem_plaquettesOver.1 hq).1
    have hq2 := (Finset.mem_filter.1 hq1).2.1
    have s0 := (innerBonds_ends b1).1
    have s1 := (innerBonds_ends b1).2
    have s2 := (innerBonds_ends b4).2
    have s3 := (innerBonds_ends b2).2
    have hqB : q ∈ innerPlaquettes (cellBall S z 1) 0 := by
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨s0, Finset.mem_univ _⟩, hq2, fun x hx => ?_⟩
      simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact s0
      · exact s1
      · exact s2
      · exact s3
    unfold complexPlaquetteTerm
    rw [complexPlaquetteHolonomy_congr (hF 0 (Nat.succ_pos _)) hqB]
  · have hcB : c ∈ innerBonds (cellBall S z 1) (j + 1) :=
      BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z (by omega) hc
    have hj' : j + 1 ≤ F.top := by omega
    unfold complexBondTermOverTop
    rw [complexChainOverTop_of_lt R W₁ T hj, complexChainOverTop_of_lt R W₂ T hj]
    have e1 : complexGaugedContourAverage (complexChartField R W₁ j) (complexBalancingGauges R W₁ (j + 1)) c =
        complexGaugedContourAverage (complexChartField R W₂ j) (complexBalancingGauges R W₂ (j + 1)) c :=
      complexGaugedContourAverage_congr hodd hj' (R j) (hF j hj) hcB
    rw [e1]
    congr 1
    by_cases htop : j + 1 = F.top
    · rw [complexChainOverTop_eq_of_eq_top htop R W₁ W₂ T]
    · have h3 : j + 1 < F.top := by omega
      rw [complexChainOverTop_of_lt R W₁ T h3, complexChainOverTop_of_lt R W₂ T h3]
      exact hF (j + 1) h3 c.1 c.2 (innerBonds_ends hcB).1 (innerBonds_ends hcB).2
theorem complexTotalOverTop_sub_eq_local (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (R : F.FieldChain) {W₁ W₂ : ComplexChainChart F} (T : F.ComplexField F.top) (Y : F.Cell) (d : ℕ)
    (hfar : ∀ z ∈ S, d < cellSupDist z Y → ChartEqOnBonds (cellBall S z 1) W₁.re W₂.re ∧
      ChartEqOnBonds (cellBall S z 1) W₁.im W₂.im) :
    complexTotalOverTop a S R W₁ T - complexTotalOverTop a S R W₂ T =
      ∑ p ∈ plaquettesOver S (cellBall S Y d) 0,
        (complexPlaquetteTerm (complexChartField R W₁ 0) p - complexPlaquetteTerm (complexChartField R W₂ 0) p) +
      (a : ℂ) * ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S (cellBall S Y d) (j + 1),
        (complexBondTermOverTop R W₁ T j c - complexBondTermOverTop R W₂ T j c) := by
  classical
  have hcell : ∀ {k : ℕ} {x : F.Site k}, x ∈ sitesOfCells S k → enclosingCell x ∉ cellBall S Y d →
      d < cellSupDist (enclosingCell x) Y := by
    intro k x hx hn
    have hc : enclosingCell x ∈ S := CoordinateSeminorms.enclosingCell_mem hodd hx
    by_contra hle
    refine hn (Finset.mem_filter.2 ⟨hc, ?_⟩)
    rw [CoordinateSeminorms.cellSupDist_comm]
    omega
  have ep : ∑ p ∈ innerPlaquettes S 0, complexPlaquetteTerm (complexChartField R W₁ 0) p -
      ∑ p ∈ innerPlaquettes S 0, complexPlaquetteTerm (complexChartField R W₂ 0) p =
      ∑ p ∈ plaquettesOver S (cellBall S Y d) 0,
        (complexPlaquetteTerm (complexChartField R W₁ 0) p - complexPlaquetteTerm (complexChartField R W₂ 0) p) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (fun q hq => (CoordinateSeminorms.mem_plaquettesOver.1 hq).1)
      fun q hq hn => ?_).symm
    have hq0 : q.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).1
    have hnot : enclosingCell q.1 ∉ cellBall S Y d := fun hc =>
      hn (CoordinateSeminorms.mem_plaquettesOver.2 ⟨hq, hc⟩)
    have hd := hcell hq0 hnot
    obtain ⟨s1, s2⟩ := hfar _ (CoordinateSeminorms.enclosingCell_mem hodd hq0) hd
    rw [(terms_eq_of_chartAgreeOn hamb hodd R T s1 s2).1 q
      (CoordinateSeminorms.mem_plaquettesOver.2 ⟨hq, by simp⟩), sub_self]
  have eb : ∀ j, j ∈ Finset.range F.top →
      ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W₁ T j c -
        ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W₂ T j c =
      ∑ c ∈ bondsOver S (cellBall S Y d) (j + 1),
        (complexBondTermOverTop R W₁ T j c - complexBondTermOverTop R W₂ T j c) := by
    intro j hj
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (fun c hc => (CoordinateSeminorms.mem_bondsOver.1 hc).1) fun c hc hn => ?_).symm
    have hc0 : c.1 ∈ sitesOfCells S (j + 1) := (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
    have hnot : enclosingCell c.1 ∉ cellBall S Y d := fun h =>
      hn (CoordinateSeminorms.mem_bondsOver.2 ⟨hc, h⟩)
    have hd := hcell hc0 hnot
    obtain ⟨s1, s2⟩ := hfar _ (CoordinateSeminorms.enclosingCell_mem hodd hc0) hd
    rw [(terms_eq_of_chartAgreeOn hamb hodd R T s1 s2).2 j (Finset.mem_range.1 hj) c
      (CoordinateSeminorms.mem_bondsOver.2 ⟨hc, by simp⟩), sub_self]
  unfold complexTotalOverTop
  have e2 : ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S (cellBall S Y d) (j + 1),
      (complexBondTermOverTop R W₁ T j c - complexBondTermOverTop R W₂ T j c) =
      ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W₁ T j c -
        ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), complexBondTermOverTop R W₂ T j c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j hj => (eb j hj).symm
  rw [e2, ← ep]
  ring
theorem chartAgreeOn_chartMove_of_far {F : BlockFrame} {S : Finset F.Cell} {Y : F.Cell} (hodd : Odd F.blockSide)
    {B : ChainChart F} {ρ' d : ℕ} (hB : SupportedNear S Y ρ' B) (hd : ρ' < d) (A : ChainChart F) (τ : ℝ)
    {z : F.Cell} (hz : d < cellSupDist z Y) :
    ChartEqOnBonds (cellBall S z 1) (chartMove A B τ) A := by
  have hfar : ∀ {j : ℕ} {x : F.Site j}, x ∈ sitesOfCells (cellBall S z 1) j →
      ρ' < cellSupDist (enclosingCell x) Y := by
    intro j x hx
    have hc := CoordinateSeminorms.enclosingCell_mem hodd hx
    have h1 : cellSupDist z (enclosingCell x) ≤ 1 := (Finset.mem_filter.1 hc).2
    have h2 := CoordinateSeminorms.cellSupDist_triangle z (enclosingCell x) Y
    omega
  refine ⟨fun x hx => ?_, fun j hj x hx => ?_⟩
  · have hxS : x ∈ innerBonds S 0 := BlockLines.innerBonds_mono (BlockLines.cellBall_subset S z 1) 0 hx
    have h0 := hB.fine x hxS (hfar (innerBonds_ends hx).1)
    show A.fine x.1 x.2 + τ • B.fine x.1 x.2 = _
    rw [h0, smul_zero, add_zero]
  · have hxS : x ∈ innerBonds S (j + 1) :=
      BlockLines.innerBonds_mono (BlockLines.cellBall_subset S z 1) (j + 1) hx
    have h0 := hB.coarse j hj x hxS (hfar (innerBonds_ends hx).1)
    show A.coarse j x.1 x.2 + τ • B.coarse j x.1 x.2 = _
    rw [h0, smul_zero, add_zero]
theorem allAlong_plaquette_unitBall {μ ν : Fin 4} (hne : μ ≠ ν) :
    AllAlong (fun v : Lattice4 => ∀ i, |v i| ≤ 1) 0 [(μ, true), (ν, true), (μ, false), (ν, false)] := by
  have hs : ∀ (a l : Fin 4), |basisVector a l| ≤ 1 := fun a l => PlaquettesNearCell.abs_basisVector_le_one a l
  have e1 : (0 : Lattice4) + FlatPairing.stepDisplacement (μ, true) = basisVector μ := by
    simp [FlatPairing.stepDisplacement]
  have e2 : basisVector μ + FlatPairing.stepDisplacement (ν, true) = basisVector μ + basisVector ν := by
    simp [FlatPairing.stepDisplacement]
  have e3 : basisVector μ + basisVector ν + FlatPairing.stepDisplacement (μ, false) = basisVector ν := by
    simp [FlatPairing.stepDisplacement]
  have e4 : basisVector ν + FlatPairing.stepDisplacement (ν, false) = 0 := by
    simp [FlatPairing.stepDisplacement]
  refine ⟨fun i => by simp, ?_⟩
  rw [e1]
  refine ⟨hs μ, ?_⟩
  rw [e2]
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, basisVector]
    by_cases a : i = μ
    · subst a
      simp [hne]
    · by_cases b : i = ν
      · subst b
        simp [a]
      · simp [a, b]
  rw [e3]
  refine ⟨hs ν, ?_⟩
  rw [e4]
  exact fun i => by simp
theorem complexPlaquetteTerm_eq_of_chartsAgree (hodd : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hL : F'.blockSide = F.blockSide) (hn : F'.top = F.top) {R : F.FieldChain} {R' : F'.FieldChain}
    {W : ComplexChainChart F} {W' : ComplexChainChart F'} {ρ : ℤ} (h : ChartsAgree S Y Y' ρ R R' W W')
    {p : Lattice4} {μ ν : Fin 4} (hq : (siteAtOffset 0 Y p, μ, ν) ∈ innerPlaquettes S 0)
    (hp : ∀ i, |p i| + 1 ≤ agreementRadius F.blockSide ρ 0) :
    complexPlaquetteTerm (complexChartField R W 0) (siteAtOffset 0 Y p, μ, ν) =
      complexPlaquetteTerm (complexChartField R' W' 0) (siteAtOffset 0 Y' p, μ, ν) := by
  have hne : μ ≠ ν := (Finset.mem_filter.1 hq).2.1.ne
  have hp1 := allAlong_plaquette hq
  have hp2 := allAlong_plaquette_unitBall hne
  have hp3 := allAlong_and _ _ hp1 hp2
  have hp4 : AllAlong (fun v => InRegion S Y 0 (agreementRadius F.blockSide ρ 0) (p + v)) 0
      [(μ, true), (ν, true), (μ, false), (ν, false)] := by
    refine allAlong_mono (fun v hv => ⟨fun i => ?_, ?_⟩) hp3
    · have h1 := hv.2 i
      rw [pow_zero, one_mul]
      simp only [Pi.add_apply]
      have h2 := abs_add_le (p i) (v i)
      have h3 := hp i
      omega
    · have h1 := hv.1
      rw [siteAtOffset_add]
      exact Finset.mem_coe.1 h1
  have hp5 := allAlong_translate (P := InRegion S Y 0 (agreementRadius F.blockSide ρ 0)) p _ 0 hp4
  rw [add_zero] at hp5
  have hH := complexPathHolonomy_eq_of_agree (Y := Y) (Y' := Y') (X := complexChartField R W 0)
    (X' := complexChartField R' W' 0) (P := InRegion S Y 0 (agreementRadius F.blockSide ρ 0))
    (complexChartField_eq_of_chartsAgree hodd hL3 hL hn h 0 (Nat.succ_pos _)) _ p hp5
  unfold complexPlaquetteTerm complexPlaquetteHolonomy
  simp only
  rw [hH]
end Terms
open CellTransport in
set_option maxHeartbeats 2000000 in
theorem firstVariationAcrossFrames_holds (hLines : agreeingPairsLocalityStatement)
    (hSt : sitesOfCellsAcrossFramesStatement) : firstVariationAcrossFramesStatement := by
  obtain ⟨c, hc, hl⟩ := hLines
  refine ⟨c, hc, ?_⟩
  intro F F' a m S S' s V V' Y Y' r ρ hL ht hodd hL3 hamb hamb' hm hreg hreg' hs hsc hcold hcold' hagree hρ10 hρ
    W W' T T' B B' h1 h2 h3 h4 h5 h6
  have tS : FramePairing S S' Y Y' r := ⟨hodd, hL, ht, hagree.1, hagree.2.1, hagree.2.2.1⟩
  have hn := tS.top_eq
  have hrefs := (hl F F' m S S' s V V' Y Y' r hL ht hodd hamb hamb' hm hreg hreg' hs hsc hcold hcold' hagree).2
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  set N : ℤ := (F.blockSide : ℤ) ^ F.top with hN
  have hN0 : 0 < N := pow_pos hL0 _
  set ρb : ℤ := (ρ : ℤ) * N with hρb
  set d : ℕ := ρ - 8 with hd
  have hlev : ∀ {j : ℕ}, j ≤ F.top → (F.blockSide : ℤ) ^ j ≤ N := fun hj => pow_le_pow_right₀ (by omega) hj
  have hρ1 : ((d + 1 : ℕ) : ℤ) = (ρ : ℤ) - 7 := by omega
  have hrel : ∀ {j : ℕ}, j ≤ F.top → ((d + 1 : ℕ) : ℤ) * N ≤ agreementRadius F.blockSide ρb j := by
    intro j hj
    unfold agreementRadius
    rw [hρ1, hρb]
    have := hlev hj
    nlinarith
  have hRchain : ∀ j, j < F.top → referenceFieldChain S V j = referenceGaugeField S V j := fun j hj => by
    unfold referenceFieldChain
    exact Function.update_of_ne hj.ne _ _
  have hRchain' : ∀ j, j < F.top → referenceFieldChain S' V' j = referenceGaugeField S' V' j := fun j hj => by
    unfold referenceFieldChain
    exact Function.update_of_ne (by omega) _ _
  have hρr : (ρ : ℤ) ≤ (r : ℤ) - 100 := by
    have : ((ρ + 110 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hρ
    push_cast at this
    omega
  have href : ∀ j, j < F.top → ∀ p i, InRegion S Y j ρb p → InRegion S Y j ρb (p + basisVector i) →
      referenceFieldChain S V j (siteAtOffset j Y p) i = referenceFieldChain S' V' j (siteAtOffset j Y' p) i := by
    intro j hj p i hp hp'
    rw [hRchain j hj, hRchain' j hj]
    have hin : ∀ x : Lattice4, InLevelBall F.blockSide j ρb x → IsInnerOffset F.blockSide F.top r j x :=
      fun x hx l => (hx l).trans (mul_le_mul_of_nonneg_right hρr hN0.le)
    have hb : (siteAtOffset j Y p, i) ∈ innerBonds S j := by
      refine ChartCoordinates.mem_innerBonds hp.2 ?_
      rw [siteAtOffset_add_unitStep]
      exact hp'.2
    exact hrefs j p i hj (hin _ hp.1) (hin _ hp'.1) hb
  have hAgree : ∀ τ : ℂ, ChartsAgree S Y Y' ρb (referenceFieldChain S V) (referenceFieldChain S' V')
      (complexChartMove W B τ) (complexChartMove W' B' τ) := by
    intro τ
    refine ⟨fun p i hp => ?_, fun j p i hj hp => ?_, href⟩
    · have hw : WithinCellRadius F.blockSide F.top ρ 0 p := hp
      constructor
      · show W.re.fine _ i + τ.re • B.fine _ i = W'.re.fine _ i + τ.re • B'.fine _ i
        rw [h1.fine p i hw, h4.fine p i hw]
      · show W.im.fine _ i + τ.im • B.fine _ i = W'.im.fine _ i + τ.im • B'.fine _ i
        rw [h2.fine p i hw, h4.fine p i hw]
    · have hw : WithinCellRadius F.blockSide F.top ρ (j + 1) p := hp
      constructor
      · show W.re.coarse j _ i + τ.re • B.coarse j _ i = W'.re.coarse j _ i + τ.re • B'.coarse j _ i
        rw [h1.coarse j p i hj hw, h4.coarse j p i hj hw]
      · show W.im.coarse j _ i + τ.im • B.coarse j _ i = W'.im.coarse j _ i + τ.im • B'.coarse j _ i
        rw [h2.coarse j p i hj hw, h4.coarse j p i hj hw]
  have hAgree0 : ChartsAgree S Y Y' ρb (referenceFieldChain S V) (referenceFieldChain S' V') W W' :=
    ⟨fun p i hp => ⟨h1.fine p i hp, h2.fine p i hp⟩,
      fun j p i hj hp => ⟨h1.coarse j p i hj hp, h2.coarse j p i hj hp⟩, href⟩
  have hboxes : MatchedCells (cellBall S Y d) (cellBall S' Y' d) Y Y' d := by
    refine ⟨fun y hy => ?_, fun y hy => ?_, fun o ho => ?_⟩
    · rw [CoordinateSeminorms.cellSupDist_comm]
      exact (Finset.mem_filter.1 hy).2
    · rw [CoordinateSeminorms.cellSupDist_comm]
      exact (Finset.mem_filter.1 hy).2
    · have hin : WithinRadius r o := fun i => by
        have := ho i
        omega
      have e1 : cellSupDist Y (Y + siteOfCoords F.top o) ≤ d := by
        rw [CoordinateSeminorms.cellSupDist_comm]
        exact cellSupDist_add_siteOfCoords_le Y o ho
      have e2 : cellSupDist Y' (Y' + siteOfCoords F'.top o) ≤ d := by
        rw [CoordinateSeminorms.cellSupDist_comm]
        exact cellSupDist_add_siteOfCoords_le Y' o ho
      constructor
      · intro hy
        exact Finset.mem_filter.2 ⟨(hagree.2.2.1 o hin).1 (Finset.mem_filter.1 hy).1, e2⟩
      · intro hy
        exact Finset.mem_filter.2 ⟨(hagree.2.2.1 o hin).2 (Finset.mem_filter.1 hy).1, e1⟩
  have hdr : d + 110 ≤ r := by omega
  have hS : ∀ (j k : ℕ), j ≤ F.top → k + 2 ≤ r → ∀ q : Lattice4, WithinCellRadius F.blockSide F.top k j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j) :=
    fun j k hj hk q hq => hSt F F' S S' V V' Y Y' r k j hL ht hodd hj hagree hk q hq
  have hbond : ∀ (A : ComplexChainChart F) (A' : ComplexChainChart F'),
      ChartsAgree S Y Y' ρb (referenceFieldChain S V) (referenceFieldChain S' V') A A' → ∀ j, j < F.top →
      ∑ x ∈ bondsOver S (cellBall S Y d) (j + 1), complexBondTermOverTop (referenceFieldChain S V) A T j x =
        ∑ x ∈ bondsOver S' (cellBall S' Y' d) (j + 1),
          complexBondTermOverTop (referenceFieldChain S' V') A' T' j x := by
    intro A A' hA j hj
    refine sum_bondsOver_eq tS hboxes hdr (by omega) (hS (j + 1) (d + 2) (by omega) (by omega)) _ _
      fun p i hp hb => ?_
    have hj1 : j + 1 ≤ F.top := by omega
    have hN1 : (F.blockSide : ℤ) ^ (j + 1) > 0 := pow_pos hL0 _
    have hball : ∀ l, (F.blockSide : ℤ) ^ (j + 1) * |(p + basisVector i) l| ≤
        agreementRadius F.blockSide ρb (j + 1) ∧
        (F.blockSide : ℤ) ^ (j + 1) * |p l| ≤ agreementRadius F.blockSide ρb (j + 1) := by
      intro l
      have h7 := hp l
      have h8 := hrel hj1
      have h9 : |(p + basisVector i) l| ≤ |p l| + 1 := by
        simp only [Pi.add_apply]
        refine (abs_add_le _ _).trans ?_
        linarith [PlaquettesNearCell.abs_basisVector_le_one i l]
      have h10 := mul_le_mul_of_nonneg_left h9 hN1.le
      have h11 : (F.blockSide : ℤ) ^ (j + 1) * |p l| ≤ (F.blockSide : ℤ) ^ (j + 1) * (|p l| + 1) :=
        mul_le_mul_of_nonneg_left (by omega) hN1.le
      exact ⟨(h10.trans h7).trans h8, (h11.trans h7).trans h8⟩
    have hpb := innerBonds_ends hb
    refine complexBondTermOverTop_eq_of_chartsAgree hodd hL3 hL hn hA (fun p i hp => h3 p i hp) hj
      ⟨fun l => (hball l).2, hpb.1⟩ ⟨fun l => (hball l).1, ?_⟩
    rw [← siteAtOffset_add_unitStep]
    exact hpb.2
  have hplaq : ∀ (A : ComplexChainChart F) (A' : ComplexChainChart F'),
      ChartsAgree S Y Y' ρb (referenceFieldChain S V) (referenceFieldChain S' V') A A' →
      ∑ x ∈ plaquettesOver S (cellBall S Y d) 0,
        complexPlaquetteTerm (complexChartField (referenceFieldChain S V) A 0) x =
        ∑ x ∈ plaquettesOver S' (cellBall S' Y' d) 0,
          complexPlaquetteTerm (complexChartField (referenceFieldChain S' V') A' 0) x := by
    intro A A' hA
    refine sum_plaquettesOver_eq tS hboxes hdr (hS 0 (d + 3) (Nat.zero_le _) (by omega)) _ _
      fun p μ ν hp hq => ?_
    refine complexPlaquetteTerm_eq_of_chartsAgree hodd hL3 hL hn hA hq fun i => (hp i).trans ?_
    exact hrel (Nat.zero_le _)
  have hfarS : ∀ (τ : ℂ), ∀ z ∈ S, d < cellSupDist z Y →
      ChartEqOnBonds (cellBall S z 1) (complexChartMove W B τ).re W.re ∧
      ChartEqOnBonds (cellBall S z 1) (complexChartMove W B τ).im W.im := fun τ z _ hz =>
    ⟨chartAgreeOn_chartMove_of_far hodd h5 (by omega) W.re τ.re hz,
      chartAgreeOn_chartMove_of_far hodd h5 (by omega) W.im τ.im hz⟩
  have hfarS' : ∀ (τ : ℂ), ∀ z ∈ S', d < cellSupDist z Y' →
      ChartEqOnBonds (cellBall S' z 1) (complexChartMove W' B' τ).re W'.re ∧
      ChartEqOnBonds (cellBall S' z 1) (complexChartMove W' B' τ).im W'.im := fun τ z _ hz =>
    ⟨chartAgreeOn_chartMove_of_far (hL ▸ hodd) h6 (by omega) W'.re τ.re hz,
      chartAgreeOn_chartMove_of_far (hL ▸ hodd) h6 (by omega) W'.im τ.im hz⟩
  have hcmp : ∀ τ : ℂ, complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W B τ) T -
      complexTotalOverTop a S (referenceFieldChain S V) W T =
      complexTotalOverTop a S' (referenceFieldChain S' V') (complexChartMove W' B' τ) T' -
        complexTotalOverTop a S' (referenceFieldChain S' V') W' T' := by
    intro τ
    rw [complexTotalOverTop_sub_eq_local hamb hodd a _ T Y d (hfarS τ),
      complexTotalOverTop_sub_eq_local hamb' (hL ▸ hodd) a _ T' Y' d (hfarS' τ)]
    have hrange : Finset.range F'.top = Finset.range F.top := by rw [hn]
    rw [hrange]
    simp only [Finset.sum_sub_distrib]
    have e2 := Finset.sum_congr (s₁ := Finset.range F.top) rfl fun j hj =>
      hbond _ _ (hAgree τ) j (Finset.mem_range.1 hj)
    have e3 := Finset.sum_congr (s₁ := Finset.range F.top) rfl fun j hj =>
      hbond _ _ hAgree0 j (Finset.mem_range.1 hj)
    rw [hplaq _ _ (hAgree τ), hplaq _ _ hAgree0, e2, e3]
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W B τ) T) =
      fun τ : ℂ => complexTotalOverTop a S' (referenceFieldChain S' V') (complexChartMove W' B' τ) T' +
        (complexTotalOverTop a S (referenceFieldChain S V) W T -
          complexTotalOverTop a S' (referenceFieldChain S' V') W' T') := by
    funext τ
    have := hcmp τ
    linear_combination this
  rw [e, deriv_add_const]
end YangMills.Construction.FramedFirstVariation
end
