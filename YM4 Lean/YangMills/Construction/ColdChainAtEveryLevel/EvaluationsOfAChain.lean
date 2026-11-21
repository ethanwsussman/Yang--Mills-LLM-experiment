import YangMills.Construction.ColdChainAtEveryLevel.AveragesAndLocalSizesOfALevelProof
import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
open LatticePaths LatticeFractionalIntegration
def ChartIsRegular {F : BlockFrame} (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) : Prop :=
  ∀ j, j < F.top → (∀ y ∈ sitesOfCells S (j + 1), relativePathAverage (chartField R U j) (R j) y ≠ 0) ∧
    ∀ c ∈ innerBonds S (j + 1),
      gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c ≠ 0
namespace ChartCoordinates
variable {F : BlockFrame}
theorem stepDisplacement_eq_siteOfCoords (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by
  rcases st with ⟨i, b⟩
  cases b
  · simp [stepDisplacement, FlatPairing.stepDisplacement, unitStep_eq, siteOfCoords_neg]
  · simp [stepDisplacement, FlatPairing.stepDisplacement, unitStep_eq]
theorem scale_add_mem_centredCube {L k : ℕ} (hodd : Odd L) {h a : Lattice4} (hh : h ∈ centredCube (L ^ k))
    (ha : a ∈ centredCube L) : (fun i => (L : ℤ) * h i + a i) ∈ centredCube (L ^ (k + 1)) := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, ((L ^ k : ℕ) : ℤ) = 2 * A + 1 := by
    obtain ⟨A, hA⟩ := hodd.pow (n := k)
    exact ⟨A, by rw [hA]; push_cast; ring⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, (L : ℤ) = 2 * B + 1 := by
    obtain ⟨B, hB⟩ := hodd
    exact ⟨B, by rw [hB]; push_cast; ring⟩
  have eA : (((L ^ k : ℕ) : ℤ) - 1) / 2 = A := by rw [hA]; omega
  have eB : ((L : ℤ) - 1) / 2 = B := by rw [hB]; omega
  have eAB : (((L ^ (k + 1) : ℕ) : ℤ) - 1) / 2 = 2 * A * B + A + B := by
    have e1 : ((L ^ (k + 1) : ℕ) : ℤ) = (2 * A + 1) * (2 * B + 1) := by
      rw [pow_succ]; push_cast; push_cast at hA; rw [hA, hB]
    have e2 : (2 * A + 1) * (2 * B + 1) - 1 = 2 * (2 * A * B + A + B) := by ring
    rw [e1, e2]; simp
  rw [mem_centredCube_iff] at hh ha ⊢
  intro i
  have h1 := hh i
  have h2 := ha i
  rw [eA] at h1
  rw [eB] at h2
  rw [eAB]
  have hB0 : 0 ≤ (L : ℤ) := by positivity
  have m1 := mul_le_mul_of_nonneg_left h1.2 hB0
  have m2 := mul_le_mul_of_nonneg_left h1.1 hB0
  rw [hB] at m1 m2 ⊢
  constructor <;> nlinarith [h2.1, h2.2]
theorem refineSite_cellCentre (j : ℕ) (hj : j + 1 ≤ F.top) (z : F.Cell) :
    refineSite (cellCentre (j + 1) z) = cellCentre j z := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_cellCentre <;> assumption
theorem refineSite_add_mem_sitesOfCells {S : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j + 1 ≤ F.top) {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1)) {a : Lattice4}
    (ha : a ∈ centredCube F.blockSide) : refineSite y + siteOfCoords j a ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_add_mem_sitesOfCells <;> assumption
theorem refineSite_add_mem_of_mem_twoBlockHull {S : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) {a : Lattice4}
    (ha : a ∈ FlatPairing.twoBlockHull F.blockSide c.2) :
    refineSite c.1 + siteOfCoords j a ∈ sitesOfCells S j := by
  have hb := Finset.mem_filter.1 hc
  have h1 : c.1 ∈ sitesOfCells S (j + 1) := (Finset.mem_product.1 hb.1).1
  have h2 := hb.2
  by_cases hcase : a c.2 ≤ ((F.blockSide : ℤ) - 1) / 2
  · refine refineSite_add_mem_sitesOfCells hodd hj h1 ((mem_centredCube_iff _ _).2 fun μ => ?_)
    have := ha μ
    by_cases hμ : μ = c.2
    · subst hμ
      simp only [if_true] at this
      exact ⟨this.1, hcase⟩
    · simpa [hμ] using this
  · have e : refineSite c.1 + siteOfCoords j a =
        refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j (a - (F.blockSide : ℤ) • basisVector c.2) := by
      rw [unitStep_eq, refineSite_add j hj, add_assoc, ← siteOfCoords_add]
      congr 2
      funext μ
      simp [basisVector]
    rw [e]
    refine refineSite_add_mem_sitesOfCells hodd hj h2 ((mem_centredCube_iff _ _).2 fun μ => ?_)
    have := ha μ
    obtain ⟨m, hm⟩ := hodd
    have hL : ((F.blockSide : ℤ) - 1) / 2 = m := by rw [hm]; push_cast; omega
    have hL2 : (F.blockSide : ℤ) = 2 * m + 1 := by rw [hm]; push_cast; ring
    rw [hL] at this hcase ⊢
    by_cases hμ : μ = c.2
    · subst hμ
      simp only [if_true] at this
      simp [basisVector]
      constructor <;> omega
    · simp only [hμ, if_false] at this
      simp [basisVector, hμ]
      simpa using this
section Congr
variable {j : ℕ} {D : Set (F.Site j)}
theorem pathHolonomy_congr {X X' : F.GaugeField j}
    (h : ∀ x i, x ∈ D → x + unitStep j i ∈ D → X x i = X' x i)
    (x0 : F.Site j) : ∀ (l : List PathStep) (v : Lattice4), AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l →
      pathHolonomy X (x0 + siteOfCoords j v) l = pathHolonomy X' (x0 + siteOfCoords j v) l := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hv : x0 + siteOfCoords j v ∈ D := hp.1
    have hw : x0 + siteOfCoords j v + stepDisplacement j st ∈ D := by
      rw [hnext]; exact allAlong_head hp.2
    simp only [pathHolonomy]
    rw [hnext, ih _ hp.2]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have e : x0 + siteOfCoords j v + stepDisplacement j (i, false) = x0 + siteOfCoords j v - unitStep j i := by
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e] at hw
      rw [h _ i hw (by rw [sub_add_cancel]; exact hv)]
    · simp only [linkValue, if_true]
      have e : x0 + siteOfCoords j v + stepDisplacement j (i, true) = x0 + siteOfCoords j v + unitStep j i := by
        simp [stepDisplacement]
      rw [e] at hw
      rw [h _ i hv hw]
end Congr
section Reads
variable {S : Finset F.Cell}
def GaugeAgreeOnBonds (S : Finset F.Cell) (j : ℕ) (X X' : F.GaugeField j) : Prop :=
  ∀ x i, x ∈ sitesOfCells S j → x + unitStep j i ∈ sitesOfCells S j → X x i = X' x i
theorem allAlong_axisPath {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1)) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => refineSite y + siteOfCoords j v ∈ (sitesOfCells S j : Set (F.Site j))) 0 (axisPath h π) := by
  refine allAlong_mono (fun v hv => ?_) (axisPath_spec h π).1
  refine refineSite_add_mem_sitesOfCells hodd hj hy ((mem_centredCube_iff _ _).2 fun μ => ?_)
  have h1 := ((mem_centredCube_iff _ _).1 hh) μ
  have h2 := hv μ
  have a1 : min 0 (h μ) ≥ -(((F.blockSide : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((F.blockSide : ℤ) - 1) / 2 := max_le (by omega) h1.2
  omega
theorem allAlong_bondContour {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => refineSite c.1 + siteOfCoords j v ∈ (sitesOfCells S j : Set (F.Site j))) 0
      (bondContour F.blockSide h π c.2) :=
  allAlong_mono (fun _ hv => refineSite_add_mem_of_mem_twoBlockHull hodd hj hc hv)
    (bondContour_spec π c.2 hodd.pos hh).1
theorem add_siteOfCoords_zero {j : ℕ} (x : F.Site j) : x + siteOfCoords j (0 : Lattice4) = x := by
  rw [siteOfCoords_zero, add_zero]
theorem relativePathAverage_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X X' : F.GaugeField j}
    (R : F.GaugeField j) (h : GaugeAgreeOnBonds S j X X') {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1)) :
    relativePathAverage X R y = relativePathAverage X' R y := by
  unfold relativePathAverage
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have := pathHolonomy_congr (D := (sitesOfCells S j : Set (F.Site j))) (fun x i hx hx' => h x i hx hx')
    (refineSite y) _ 0 (allAlong_axisPath hodd hj hy ha π)
  rw [add_siteOfCoords_zero] at this
  rw [this]
theorem balancingGauge_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X X' : F.GaugeField j}
    (R : F.GaugeField j) (h : GaugeAgreeOnBonds S j X X') {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1)) :
    balancingGauge X R y = balancingGauge X' R y := by
  unfold balancingGauge
  rw [relativePathAverage_congr hodd hj R h hy]
theorem contourAverage_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X X' : F.GaugeField j}
    (h : GaugeAgreeOnBonds S j X X') {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    contourAverage X c = contourAverage X' c := by
  unfold contourAverage
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have := pathHolonomy_congr (D := (sitesOfCells S j : Set (F.Site j))) (fun x i hx hx' => h x i hx hx')
    (refineSite c.1) _ 0 (allAlong_bondContour hodd hj hc ha π)
  rw [add_siteOfCoords_zero] at this
  rw [this]
theorem innerBonds_ends {j : ℕ} {c : F.Site j × Fin 4} (hc : c ∈ innerBonds S j) :
    c.1 ∈ sitesOfCells S j ∧ c.1 + unitStep j c.2 ∈ sitesOfCells S j := by
  have hb := Finset.mem_filter.1 hc
  exact ⟨(Finset.mem_product.1 hb.1).1, hb.2⟩
theorem mem_innerBonds {j : ℕ} {x : F.Site j} {i : Fin 4} (h1 : x ∈ sitesOfCells S j)
    (h2 : x + unitStep j i ∈ sitesOfCells S j) : (x, i) ∈ innerBonds S j :=
  Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩, h2⟩
theorem gaugedContourAverage_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X X' : F.GaugeField j}
    (R : F.GaugeField j) (h : GaugeAgreeOnBonds S j X X') {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) :
    gaugedContourAverage X (balancingGauge X R) c = gaugedContourAverage X' (balancingGauge X' R) c := by
  unfold gaugedContourAverage
  rw [contourAverage_congr hodd hj h hc, balancingGauge_congr hodd hj R h (innerBonds_ends hc).1,
    balancingGauge_congr hodd hj R h (innerBonds_ends hc).2]
theorem chartField_congr (hodd : Odd F.blockSide) (R : F.FieldChain) {U U' : ChainChart F}
    (h : ChartEqOnBonds S U U') : ∀ j, j < F.top →
    GaugeAgreeOnBonds S j (chartField R U j) (chartField R U' j) := by
  intro j
  induction j with
  | zero =>
    intro _ x i hx hx'
    simp only [chartField]
    rw [h.1 (x, i) (mem_innerBonds hx hx')]
  | succ j ih =>
    intro hj x i hx hx'
    have hb := mem_innerBonds hx hx'
    have e := gaugedContourAverage_congr hodd (by omega) (R j) (ih (by omega)) hb
    simp only [chartField]
    rw [e, h.2 j hj (x, i) hb]
theorem allAlong_plaquette {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    AllAlong (fun v => p.1 + siteOfCoords 0 v ∈ (sitesOfCells S 0 : Set (F.Site 0))) 0
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
  have hc := (Finset.mem_filter.1 hp).2.2
  have c1 : p.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : p.1 + unitStep 0 p.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : p.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have e1 : p.1 + siteOfCoords 0 (0 : Lattice4) = p.1 := add_siteOfCoords_zero _
  have e2 : p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true)) =
      p.1 + unitStep 0 p.2.1 := by
    simp [FlatPairing.stepDisplacement, unitStep_eq]
  have e3 : p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) +
      FlatPairing.stepDisplacement (p.2.2, true)) = p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 := by
    simp [FlatPairing.stepDisplacement, unitStep_eq, siteOfCoords_add, add_assoc]
  have e4 : p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) +
      FlatPairing.stepDisplacement (p.2.2, true) + FlatPairing.stepDisplacement (p.2.1, false)) =
      p.1 + unitStep 0 p.2.2 := by
    have : (0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) + FlatPairing.stepDisplacement (p.2.2, true) +
        FlatPairing.stepDisplacement (p.2.1, false) = basisVector p.2.2 := by
      simp [FlatPairing.stepDisplacement]
    rw [this]; rfl
  have e5 : p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) +
      FlatPairing.stepDisplacement (p.2.2, true) + FlatPairing.stepDisplacement (p.2.1, false) +
      FlatPairing.stepDisplacement (p.2.2, false)) = p.1 := by
    have : (0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) + FlatPairing.stepDisplacement (p.2.2, true) +
        FlatPairing.stepDisplacement (p.2.1, false) + FlatPairing.stepDisplacement (p.2.2, false) = 0 := by
      simp [FlatPairing.stepDisplacement]
    rw [this]; exact add_siteOfCoords_zero _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show p.1 + siteOfCoords 0 (0 : Lattice4) ∈ sitesOfCells S 0
    rw [e1]; exact c1
  · show p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true)) ∈ sitesOfCells S 0
    rw [e2]; exact c2
  · show p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) +
      FlatPairing.stepDisplacement (p.2.2, true)) ∈ sitesOfCells S 0
    rw [e3]; exact c4
  · show p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) +
      FlatPairing.stepDisplacement (p.2.2, true) + FlatPairing.stepDisplacement (p.2.1, false)) ∈ sitesOfCells S 0
    rw [e4]; exact c3
  · show p.1 + siteOfCoords 0 ((0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) +
      FlatPairing.stepDisplacement (p.2.2, true) + FlatPairing.stepDisplacement (p.2.1, false) +
      FlatPairing.stepDisplacement (p.2.2, false)) ∈ sitesOfCells S 0
    rw [e5]; exact c1
theorem wilsonAction_congr {X X' : F.GaugeField 0} (h : GaugeAgreeOnBonds S 0 X X') :
    wilsonAction S X = wilsonAction S X' := by
  unfold wilsonAction
  refine Finset.sum_congr rfl fun p hp => ?_
  have := pathHolonomy_congr (D := (sitesOfCells S 0 : Set (F.Site 0))) (fun x i hx hx' => h x i hx hx') p.1 _ 0
    (allAlong_plaquette hp)
  rw [add_siteOfCoords_zero] at this
  unfold plaquetteHolonomy
  rw [this]
theorem chartChain_of_lt (R : F.FieldChain) (U : ChainChart F) (W : F.GaugeField F.top) {j : ℕ} (hj : j < F.top) :
    chartChain R U W j = chartField R U j := by
  unfold chartChain
  rw [Function.update_of_ne (by omega)]
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (W : F.GaugeField F.top) :
    chartChain R U W F.top = W := by
  unfold chartChain
  rw [Function.update_self]
theorem chartAction_congr (hodd : Odd F.blockSide) (a : ℝ) (R : F.FieldChain) (W : F.GaugeField F.top)
    {U U' : ChainChart F} (h : ChartEqOnBonds S U U') :
    chartAction a S R U W = chartAction a S R U' W := by
  have hf := chartField_congr hodd R h
  unfold chartAction gaugedChainAction
  have h0 : 0 < F.top := Nat.succ_pos _
  rw [chartChain_of_lt R U W h0, chartChain_of_lt R U' W h0, wilsonAction_congr (hf 0 h0)]
  refine congrArg (fun r => _ + a * r) (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_)
  have hjn : j < F.top := Finset.mem_range.1 hj
  rw [chartChain_of_lt R U W hjn, chartChain_of_lt R U' W hjn]
  unfold gaugedBlockFit chartGauge
  rw [show gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c =
    gaugedContourAverage (chartField R U' j) (balancingGauge (chartField R U' j) (R j)) c from
      gaugedContourAverage_congr hodd hjn (R j) (hf j hjn) hc]
  by_cases htop : j + 1 < F.top
  · rw [chartChain_of_lt R U W htop, chartChain_of_lt R U' W htop,
      hf (j + 1) htop c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2]
  · obtain rfl : j = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    rw [chartChain_top R U W, chartChain_top R U' W]
end Reads
section Diff
variable {S : Finset F.Cell} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P}
def starCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  ⟨{ toFun := star, map_add' := star_add, map_smul' := fun r q => quaternion_star_real_smul r q }, continuous_star⟩
theorem differentiableAt_expUnit {w : P → imaginaryQuaternions} (hw : DifferentiableAt ℝ w p₀) :
    DifferentiableAt ℝ (fun p => ((expUnit (w p) : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  have h1 : DifferentiableAt ℝ (fun p => ((w p : imaginaryQuaternions) : ℍ[ℝ])) p₀ :=
    (Submodule.subtypeL imaginaryQuaternions).differentiableAt.comp p₀ hw
  exact ((NormedSpace.exp_analytic (𝕂 := ℝ) _).differentiableAt).comp p₀ h1
theorem differentiableAt_polarUnit {q : P → ℍ[ℝ]} (hq : DifferentiableAt ℝ q p₀) (h0 : q p₀ ≠ 0) :
    DifferentiableAt ℝ (fun p => ((polarUnit (q p) : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  have hne : ∀ᶠ p in nhds p₀, q p ≠ 0 := hq.continuousAt.eventually_ne h0
  have e : (fun p => ((polarUnit (q p) : UnitQuaternion) : ℍ[ℝ])) =ᶠ[nhds p₀] fun p => ‖q p‖⁻¹ • q p := by
    filter_upwards [hne] with p hp
    exact coe_polarUnit hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ e
  exact ((hq.norm ℝ h0).inv (norm_ne_zero_iff.2 h0)).smul hq
theorem differentiableAt_unitQuaternion_inv {g : P → UnitQuaternion}
    (hg : DifferentiableAt ℝ (fun p => ((g p : UnitQuaternion) : ℍ[ℝ])) p₀) :
    DifferentiableAt ℝ (fun p => (((g p)⁻¹ : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  simp only [coe_unitQuaternion_inv]
  exact starCLM.differentiableAt.comp p₀ hg
theorem differentiableAt_unitQuaternion_mul {g g' : P → UnitQuaternion}
    (hg : DifferentiableAt ℝ (fun p => ((g p : UnitQuaternion) : ℍ[ℝ])) p₀)
    (hg' : DifferentiableAt ℝ (fun p => ((g' p : UnitQuaternion) : ℍ[ℝ])) p₀) :
    DifferentiableAt ℝ (fun p => ((g p * g' p : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  simp only [Submonoid.coe_mul]
  exact hg.mul hg'
variable {j : ℕ}
def GaugeDifferentiableOn (X : P → F.GaugeField j) (p₀ : P) (D : Set (F.Site j)) : Prop :=
  ∀ x i, x ∈ D → x + unitStep j i ∈ D →
    DifferentiableAt ℝ (fun p => ((X p x i : UnitQuaternion) : ℍ[ℝ])) p₀
theorem differentiableAt_pathHolonomy {D : Set (F.Site j)} {X : P → F.GaugeField j}
    (h : GaugeDifferentiableOn X p₀ D) (x0 : F.Site j) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l →
      DifferentiableAt ℝ (fun p => ((pathHolonomy (X p) (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  intro l
  induction l with
  | nil =>
    intro v _
    simp only [pathHolonomy]
    exact differentiableAt_const _
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hv : x0 + siteOfCoords j v ∈ D := hp.1
    have hw : x0 + siteOfCoords j v + stepDisplacement j st ∈ D := by
      rw [hnext]; exact allAlong_head hp.2
    simp only [pathHolonomy]
    rw [hnext]
    refine differentiableAt_unitQuaternion_mul ?_ (ih _ hp.2)
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have e : x0 + siteOfCoords j v + stepDisplacement j (i, false) = x0 + siteOfCoords j v - unitStep j i := by
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e] at hw
      exact differentiableAt_unitQuaternion_inv (h _ i hw (by rw [sub_add_cancel]; exact hv))
    · simp only [linkValue, if_true]
      have e : x0 + siteOfCoords j v + stepDisplacement j (i, true) = x0 + siteOfCoords j v + unitStep j i := by
        simp [stepDisplacement]
      rw [e] at hw
      exact h _ i hv hw
theorem differentiableAt_relativePathAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X : P → F.GaugeField j}
    (R : F.GaugeField j) (h : GaugeDifferentiableOn X p₀ (sitesOfCells S j : Set (F.Site j))) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1)) :
    DifferentiableAt ℝ (fun p => relativePathAverage (X p) R y) p₀ := by
  unfold relativePathAverage
  refine (differentiableAt_const (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ)).smul ?_
  apply DifferentiableAt.fun_sum
  intro a ha
  apply DifferentiableAt.fun_sum
  intro π _
  have := differentiableAt_pathHolonomy h (refineSite y) _ 0 (allAlong_axisPath hodd hj hy ha π)
  rw [add_siteOfCoords_zero] at this
  exact differentiableAt_unitQuaternion_mul this (differentiableAt_const _)
theorem differentiableAt_balancingGauge (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X : P → F.GaugeField j}
    (R : F.GaugeField j) (h : GaugeDifferentiableOn X p₀ (sitesOfCells S j : Set (F.Site j))) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1)) (h0 : relativePathAverage (X p₀) R y ≠ 0) :
    DifferentiableAt ℝ (fun p => ((balancingGauge (X p) R y : UnitQuaternion) : ℍ[ℝ])) p₀ :=
  differentiableAt_unitQuaternion_inv
    (differentiableAt_polarUnit (differentiableAt_relativePathAverage hodd hj R h hy) h0)
theorem differentiableAt_contourAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {X : P → F.GaugeField j}
    (h : GaugeDifferentiableOn X p₀ (sitesOfCells S j : Set (F.Site j))) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) :
    DifferentiableAt ℝ (fun p => contourAverage (X p) c) p₀ := by
  unfold contourAverage
  refine (differentiableAt_const (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ)).smul ?_
  apply DifferentiableAt.fun_sum
  intro a ha
  apply DifferentiableAt.fun_sum
  intro π _
  have := differentiableAt_pathHolonomy h (refineSite c.1) _ 0 (allAlong_bondContour hodd hj hc ha π)
  rw [add_siteOfCoords_zero] at this
  exact this
theorem differentiableAt_gaugedContourAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} (R : F.GaugeField j)
    (h : GaugeDifferentiableOn X p₀ (sitesOfCells S j : Set (F.Site j))) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) (h1 : relativePathAverage (X p₀) R c.1 ≠ 0)
    (h2 : relativePathAverage (X p₀) R (c.1 + unitStep (j + 1) c.2) ≠ 0) :
    DifferentiableAt ℝ (fun p => gaugedContourAverage (X p) (balancingGauge (X p) R) c) p₀ := by
  unfold gaugedContourAverage
  exact ((differentiableAt_balancingGauge hodd hj R h (innerBonds_ends hc).1 h1).mul
    (differentiableAt_contourAverage hodd hj h hc)).mul
    (differentiableAt_unitQuaternion_inv (differentiableAt_balancingGauge hodd hj R h (innerBonds_ends hc).2 h2))
theorem chartField_differentiableOn (hodd : Odd F.blockSide) (R : F.FieldChain) {C : P → ChainChart F}
    (hu : ∀ b ∈ innerBonds S 0, DifferentiableAt ℝ (fun p => (C p).fine b.1 b.2) p₀)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      DifferentiableAt ℝ (fun p => (C p).coarse j b.1 b.2) p₀)
    (hreg : ChartIsRegular S R (C p₀)) : ∀ j, j < F.top →
    GaugeDifferentiableOn (fun p => chartField R (C p) j) p₀ (sitesOfCells S j : Set (F.Site j)) := by
  intro j
  induction j with
  | zero =>
    intro _ x i hx hx'
    have hb := mem_innerBonds hx hx'
    simp only [chartField]
    exact differentiableAt_unitQuaternion_mul (differentiableAt_expUnit (hu _ hb)) (differentiableAt_const _)
  | succ j ih =>
    intro hj x i hx hx'
    have hb := mem_innerBonds hx hx'
    have hj' : j < F.top := by omega
    have hfr := differentiableAt_gaugedContourAverage hodd hj' (R j) (ih hj') hb ((hreg j hj').1 _ hx)
      ((hreg j hj').1 _ hx')
    simp only [chartField]
    exact differentiableAt_unitQuaternion_mul
      (differentiableAt_unitQuaternion_mul (differentiableAt_expUnit (hmu j hj _ hb)) (differentiableAt_const _))
      (differentiableAt_polarUnit hfr ((hreg j hj').2 _ hb))
def reCLM : ℍ[ℝ] →L[ℝ] ℝ := ⟨QuaternionAlgebra.reₗ _ _ _, Quaternion.continuous_re⟩
theorem differentiableAt_re {q : P → ℍ[ℝ]} (hq : DifferentiableAt ℝ q p₀) :
    DifferentiableAt ℝ (fun p => (q p).re) p₀ :=
  reCLM.differentiableAt.comp p₀ hq
theorem differentiableAt_wilsonAction {X : P → F.GaugeField 0}
    (h : GaugeDifferentiableOn X p₀ (sitesOfCells S 0 : Set (F.Site 0))) :
    DifferentiableAt ℝ (fun p => wilsonAction S (X p)) p₀ := by
  unfold wilsonAction
  refine DifferentiableAt.fun_sum fun q hq => ?_
  refine (differentiableAt_const _).sub (differentiableAt_re ?_)
  have := differentiableAt_pathHolonomy h q.1 _ 0 (allAlong_plaquette hq)
  rw [add_siteOfCoords_zero] at this
  exact this
theorem differentiableAt_chartAction (hodd : Odd F.blockSide) (a : ℝ) (R : F.FieldChain) (W : F.GaugeField F.top)
    {C : P → ChainChart F}
    (hu : ∀ b ∈ innerBonds S 0, DifferentiableAt ℝ (fun p => (C p).fine b.1 b.2) p₀)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      DifferentiableAt ℝ (fun p => (C p).coarse j b.1 b.2) p₀)
    (hreg : ChartIsRegular S R (C p₀)) :
    DifferentiableAt ℝ (fun p => chartAction a S R (C p) W) p₀ := by
  have hf := chartField_differentiableOn hodd R hu hmu hreg
  unfold chartAction gaugedChainAction
  have h0 : 0 < F.top := Nat.succ_pos _
  simp only [chartChain_of_lt R _ W h0]
  refine (differentiableAt_wilsonAction (hf 0 h0)).add (DifferentiableAt.const_mul
    (DifferentiableAt.fun_sum fun k hk => DifferentiableAt.fun_sum fun c hc => ?_) a)
  have hjn : k < F.top := Finset.mem_range.1 hk
  simp only [chartChain_of_lt R _ W hjn]
  unfold gaugedBlockFit chartGauge
  have hfr := differentiableAt_gaugedContourAverage hodd hjn (R k) (hf k hjn) hc
    ((hreg k hjn).1 _ (innerBonds_ends hc).1) ((hreg k hjn).1 _ (innerBonds_ends hc).2)
  refine (hfr.norm ℝ ((hreg k hjn).2 _ hc)).sub (differentiableAt_re (hfr.mul ?_))
  by_cases htop : k + 1 < F.top
  · simp only [chartChain_of_lt R _ W htop]
    exact differentiableAt_unitQuaternion_inv (hf (k + 1) htop _ _ (innerBonds_ends hc).1 (innerBonds_ends hc).2)
  · obtain rfl : k = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartChain_top R _ W]
    exact differentiableAt_const _
end Diff
section Read
abbrev ChartValues (S : Finset F.Cell) : Type :=
  (↥(innerBonds S 0) → imaginaryQuaternions) × ((j : Fin F.depth) → ↥(innerBonds S (j.val + 1)) → imaginaryQuaternions)
def chartValues (S : Finset F.Cell) (A : ChainChart F) : ChartValues S :=
  (fun b => A.fine b.1.1 b.1.2, fun j b => A.coarse j.val b.1.1 b.1.2)
open Classical in
def chartOfValues (S : Finset F.Cell) (U : ChainChart F) (e : ChartValues S) : ChainChart F :=
  ⟨fun x i => if h : (x, i) ∈ innerBonds S 0 then e.1 ⟨(x, i), h⟩ else U.fine x i,
    fun j y i => if hj : j < F.depth then
        if h : (y, i) ∈ innerBonds S (j + 1) then e.2 ⟨j, hj⟩ ⟨(y, i), h⟩ else U.coarse j y i
      else U.coarse j y i⟩
variable {S : Finset F.Cell}
theorem chartOfValues_agreeOn (U : ChainChart F) (A : ChainChart F) :
    ChartEqOnBonds S (chartOfValues S U (chartValues S A)) A := by
  refine ⟨fun b hb => ?_, fun j hj b hb => ?_⟩
  · simp only [chartOfValues, chartValues]
    rw [dif_pos (show (b.1, b.2) ∈ innerBonds S 0 from hb)]
  · have hj' : j < F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartOfValues, chartValues]
    rw [dif_pos hj', dif_pos (show (b.1, b.2) ∈ innerBonds S (j + 1) from hb)]
theorem chartOfValues_chartValues (U : ChainChart F) : chartOfValues S U (chartValues S U) = U := by
  obtain ⟨u, mu⟩ := U
  simp only [chartOfValues, chartValues]
  congr 1
  · funext x i
    split_ifs <;> rfl
  · funext j y i
    split_ifs <;> rfl
theorem chartValues_congr {A B : ChainChart F} (h : ChartEqOnBonds S A B) : chartValues S A = chartValues S B := by
  refine Prod.ext ?_ ?_
  · funext b
    exact h.1 b.1 b.2
  · funext j b
    have hj : j.val + 1 < F.top := by
      have hn : F.top = F.depth + 1 := rfl
      have := j.2
      omega
    exact h.2 j.val hj b.1 b.2
theorem differentiableAt_chartOfValues_fine (U : ChainChart F) (e₀ : ChartValues S) {b : F.Site 0 × Fin 4}
    (hb : b ∈ innerBonds S 0) :
    DifferentiableAt ℝ (fun e : ChartValues S => (chartOfValues S U e).fine b.1 b.2) e₀ := by
  have e : (fun e : ChartValues S => (chartOfValues S U e).fine b.1 b.2) = fun e => e.1 ⟨b, hb⟩ := by
    funext e
    simp only [chartOfValues]
    rw [dif_pos (show (b.1, b.2) ∈ innerBonds S 0 from hb)]
  rw [e]
  have h1 : DifferentiableAt ℝ (fun e : ChartValues S => e.1) e₀ := differentiableAt_id.fst
  exact (differentiableAt_pi.1 h1) ⟨b, hb⟩
theorem differentiableAt_chartOfValues_coarse (U : ChainChart F) (e₀ : ChartValues S) {j : ℕ} (hj : j + 1 < F.top)
    {b : F.Site (j + 1) × Fin 4} (hb : b ∈ innerBonds S (j + 1)) :
    DifferentiableAt ℝ (fun e : ChartValues S => (chartOfValues S U e).coarse j b.1 b.2) e₀ := by
  have hj' : j < F.depth := by
    have hn : F.top = F.depth + 1 := rfl
    omega
  have e : (fun e : ChartValues S => (chartOfValues S U e).coarse j b.1 b.2) = fun e => e.2 ⟨j, hj'⟩ ⟨b, hb⟩ := by
    funext e
    simp only [chartOfValues]
    rw [dif_pos hj', dif_pos (show (b.1, b.2) ∈ innerBonds S (j + 1) from hb)]
  rw [e]
  have h1 : DifferentiableAt ℝ (fun e : ChartValues S => e.2) e₀ := differentiableAt_id.snd
  have h2 := (differentiableAt_pi.1 h1) ⟨j, hj'⟩
  exact (differentiableAt_pi.1 h2) ⟨b, hb⟩
end Read
end ChartCoordinates
end BlockAverages
end YangMills.Construction
end
