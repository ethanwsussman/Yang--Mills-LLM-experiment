import YangMills.Construction.ColdChainAtEveryLevel.CellContexts
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.ComplexRemainders
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Metric
namespace YangMills.Construction.ComplexChart
open BlockAverages ComplexifiedQuaternions ComplexContours ComplexChainStep ComplexRemainders
  LatticeFractionalIntegration LatticePaths
variable {F : BlockFrame}
def complexTreeHolonomy (X : F.ComplexField F.depth) (x : F.Site F.depth) : ComplexQuat :=
  complexPathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
open Classical in
def complexGaugedBondElement (X : F.ComplexField F.depth) (k : F.Cell → ComplexQuat) (T : ComplexQuat)
    (b : F.Site F.depth × Fin 4) : ComplexQuat :=
  k (enclosingCell b.1) * complexTreeHolonomy X b.1 * X b.1 b.2 *
    Matrix.adjugate (complexTreeHolonomy X (b.1 + unitStep F.depth b.2)) *
    Matrix.adjugate (k (enclosingCell (b.1 + unitStep F.depth b.2))) *
      if IsCrossingBond b then Matrix.adjugate T else 1
theorem complexTreeHolonomy_complexify (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    complexTreeHolonomy (complexifyField X) x = ofUnit (treeHolonomy X x) :=
  complexPathHolonomy_complexify X _ _
theorem complexGaugedBondElement_complexify (X : F.GaugeField F.depth) (k : F.Cell → UnitQuaternion)
    (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4) :
    complexGaugedBondElement (complexifyField X) (fun y => ofUnit (k y)) (ofUnit (V (enclosingCell b.1) b.2)) b =
      ofUnit (gaugedBondElement X k V b) := by
  classical
  simp only [complexGaugedBondElement, gaugedBondElement, complexTreeHolonomy_complexify, ofUnit_mul, ← ofUnit_inv]
  by_cases h : IsCrossingBond b
  · simp only [if_pos h, ← ofUnit_inv]
    rfl
  · simp only [if_neg h, ofUnit_one]
    rfl
theorem exists_analytic_log_near_one : ∃ (Lg : ComplexQuat → ComplexQuat) (r : ℝ), 0 < r ∧
    AnalyticOnNhd ℂ Lg (ball 1 r) ∧
    (∀ E ∈ ball (1 : ComplexQuat) r, ‖Lg E‖ ≤ 1) ∧ ∀ A : ComplexQuat, ‖A‖ < r → Lg (NormedSpace.exp A) = A := by
  let e : ComplexQuat ≃L[ℂ] ComplexQuat := ContinuousLinearEquiv.refl ℂ ComplexQuat
  have hs : HasStrictFDerivAt (NormedSpace.exp : ComplexQuat → ComplexQuat) (e : ComplexQuat →L[ℂ] ComplexQuat) 0 := by
    have := hasStrictFDerivAt_exp_zero_of_radius_pos (𝕂 := ℂ) (𝔸 := ComplexQuat)
      (NormedSpace.expSeries_radius_pos _ _)
    exact this
  let P := hs.toOpenPartialHomeomorph NormedSpace.exp
  have h0 : (0 : ComplexQuat) ∈ P.source := hs.mem_toOpenPartialHomeomorph_source
  have hP0 : P 0 = 1 := by
    show NormedSpace.exp (0 : ComplexQuat) = 1
    exact NormedSpace.exp_zero
  have han : AnalyticAt ℂ P.symm (P 0) :=
    P.analyticAt_symm' (i := e) h0 (NormedSpace.exp_analytic (𝕂 := ℂ) 0) hs.hasFDerivAt.fderiv
  rw [hP0] at han
  have hsym : P.symm 1 = 0 := by
    rw [← hP0]
    exact P.left_inv h0
  have h1 : ∀ᶠ E in nhds (1 : ComplexQuat), AnalyticAt ℂ P.symm E := han.eventually_analyticAt
  have h2 : ∀ᶠ E in nhds (1 : ComplexQuat), ‖P.symm E‖ < 1 := by
    have hc : ContinuousAt (fun E => ‖P.symm E‖) 1 := han.continuousAt.norm
    have : (fun E => ‖P.symm E‖) 1 < 1 := by simp [hsym]
    exact hc.eventually_lt_const this
  have h3 : ∀ᶠ A in nhds (0 : ComplexQuat), P.symm (NormedSpace.exp A) = A :=
    P.eventually_left_inverse h0
  obtain ⟨r1, hr1, h12⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  obtain ⟨r3, hr3, h33⟩ := Metric.eventually_nhds_iff_ball.1 h3
  refine ⟨P.symm, min r1 r3, lt_min hr1 hr3, fun E hE => (h12 E (ball_subset_ball (min_le_left _ _) hE)).1,
    fun E hE => (h12 E (ball_subset_ball (min_le_left _ _) hE)).2.le, fun A hA => h33 A ?_⟩
  rw [mem_ball_zero_iff]
  exact hA.trans_le (min_le_right _ _)
theorem unitLog_eq_unitQuaternionLog {g : UnitQuaternion} (h : 0 ≤ (g : ℍ[ℝ]).re) :
    ((unitLog g : imaginaryQuaternions) : ℍ[ℝ]) = unitQuaternionLog g := by
  by_cases hp : pureComponent (g : ℍ[ℝ]) = 0
  · simp [unitLog, unitQuaternionLog, hp, h]
  · have hs := re_sq_add_norm_pureComponent_sq g
    have e : Real.arccos (g : ℍ[ℝ]).re = Real.arcsin ‖pureComponent (g : ℍ[ℝ])‖ := by
      rw [Real.arccos_eq_arcsin h]
      congr 1
      rw [show 1 - (g : ℍ[ℝ]).re ^ 2 = ‖pureComponent (g : ℍ[ℝ])‖ ^ 2 by linarith]
      exact Real.sqrt_sq (norm_nonneg _)
    simp [unitLog, unitQuaternionLog, hp, e]
theorem exp_ofQuat_unitLog {g : UnitQuaternion} (h : 0 ≤ (g : ℍ[ℝ]).re) :
    NormedSpace.exp (ofQuat ((unitLog g : imaginaryQuaternions) : ℍ[ℝ])) = ofUnit g := by
  rw [← ofQuat_exp, unitLog_eq_unitQuaternionLog h, exp_unitQuaternionLog]
  rfl
theorem re_nonneg_of_norm_sub_one_le_one {g : UnitQuaternion} (h : ‖(g : ℍ[ℝ]) - 1‖ ≤ 1) :
    0 ≤ (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockLines.re_nonneg_of_norm_sub_one_le <;> assumption
theorem norm_ofQuat_unitLog_le {g : UnitQuaternion} (h : 0 ≤ (g : ℍ[ℝ]).re) :
    ‖ofQuat ((unitLog g : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by
  rw [norm_ofQuat, unitLog_eq_unitQuaternionLog h]
  exact norm_unitQuaternionLog_le_two_mul g
theorem norm_ofUnit_sub_one (g : UnitQuaternion) : ‖ofUnit g - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.CellContexts.norm_ofUnit_sub_one <;> assumption
namespace BlockGeometry
section Blocks
def cellSite (y : F.Cell) (h : Lattice4) : F.Site F.depth := cellCentre F.depth y + siteOfCoords F.depth h
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem enclosingCell_cellCentre_add_siteOfCoords (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_cellSite (hL : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : enclosingCell (cellSite y h) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem valMinAbs_siteOfCoords (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {A : Lattice4}
    (hA : ∀ i, |A i| < 32 * (F.blockSide : ℤ)) (i : Fin 4) :
    ((siteOfCoords F.depth A : F.Site F.depth) i).valMinAbs = A i := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.valMinAbs_siteOfCoords <;> assumption
theorem abs_lt_of_mem_centredCube (hL : 0 < F.blockSide) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (i : Fin 4) : |h i| < 32 * (F.blockSide : ℤ) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.abs_lt_of_mem_centredCube <;> assumption
theorem cellOffset_cellSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : cellOffset (cellSite y h) = h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.cellOffset_blockPoint <;> assumption
theorem cellSite_add_unitStep (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    cellSite y h + unitStep F.depth i = cellSite y (h + basisVector i) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem cellSite_add_basisVector (y : F.Cell) (h : Lattice4) (i : Fin 4) :
    cellSite (y + siteOfCoords F.top (basisVector i)) h = cellSite y (h + (F.blockSide : ℤ) • basisVector i) := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_neighbour <;> assumption
theorem cellSite_mem_sitesOfCells {S : Finset F.Cell} {y : F.Cell} (hy : y ∈ S) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : cellSite y h ∈ sitesOfCells S F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_mem <;> assumption
theorem exists_cellSite_eq {S : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    ∃ y ∈ S, ∃ h ∈ centredCube F.blockSide, x = cellSite y h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_blockPoint <;> assumption
theorem mem_innerBonds_iff {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4} :
    b ∈ innerBonds S j ↔ b.1 ∈ sitesOfCells S j ∧ b.1 + unitStep j b.2 ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_innerBonds <;> assumption
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem cellCentre_add_mem_innerBonds {D : Finset F.Cell} {y : F.Cell} (hy : y ∈ D) {v : Lattice4} {k : Fin 4}
    (hv : v ∈ centredCube F.blockSide) (hk : v + Pi.single k 1 ∈ centredCube F.blockSide) :
    ((cellCentre F.depth y + siteOfCoords F.depth v, k) : F.Site F.depth × Fin 4) ∈ innerBonds D F.depth := by
  refine mem_innerBonds_iff.2 ⟨cellSite_mem_sitesOfCells hy hv, ?_⟩
  show cellSite y v + unitStep F.depth k ∈ sitesOfCells D F.depth
  rw [cellSite_add_unitStep]
  exact cellSite_mem_sitesOfCells hy hk
end Blocks
section Near
variable {D : Finset F.Cell} {X : F.ComplexField F.depth} {R : F.GaugeField F.depth} {tt : ℝ}
theorem complexTreeHolonomy_eq_relativeHolonomy_mul (X : F.ComplexField F.depth) (R : F.GaugeField F.depth)
    (x : F.Site F.depth) :
    complexTreeHolonomy X x =
      relativeHolonomy X R (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1) *
        ofUnit (treeHolonomy R x) := by
  rw [complexTreeHolonomy, relativeHolonomy, treeHolonomy, mul_assoc, ofUnit_inv_mul, mul_one]
theorem norm_relativeHolonomy_axisPath_sub_one_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hg : ∀ b ∈ innerBonds D F.depth, BondNearReal X R tt b.1 b.2)
    (ht : 0 ≤ tt) (hsm : 4 * (F.blockSide : ℝ) * tt ≤ 1) {x : F.Site F.depth} (hx : x ∈ sitesOfCells D F.depth) :
    ‖relativeHolonomy X R (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1) - 1‖ ≤
      4 * (F.blockSide : ℝ) * tt := by
  obtain ⟨y, hy, h, hh, rfl⟩ := exists_cellSite_eq hx
  rw [enclosingCell_cellSite hodd y hh, cellOffset_cellSite hamb hodd y hh]
  have hp : PathNearReal X R tt (cellCentre F.depth y) (axisPath h 1) :=
    pathNearReal_axisPath _ hodd.pos (fun v hv k hk =>
      hg (cellCentre F.depth y + siteOfCoords F.depth v, k) (cellCentre_add_mem_innerBonds hy hv hk)) hh 1
  have := norm_relativeHolonomy_sub_one_le_of_length_le ht hp (length_axisPath_le F.blockSide h hh 1)
    (by push_cast; linarith)
  refine this.trans (le_of_eq ?_)
  push_cast
  ring
theorem norm_complexBalancingGauge_sub_one_le (hodd : Odd F.blockSide)
    (hg : ∀ b ∈ innerBonds D F.depth, BondNearReal X R tt b.1 b.2) (ht : 0 ≤ tt)
    (hsm : 4 * (F.blockSide : ℝ) * tt ≤ 1 / 8) {y : F.Cell} (hy : y ∈ D) :
    ‖complexBalancingGauge X R y - 1‖ ≤ 20 * (F.blockSide : ℝ) * tt := by
  have hp : ∀ h ∈ centredCube F.blockSide, ∀ π, PathNearReal X R tt (refineSite y) (axisPath h π) := fun h hh π => by
    rw [refineSite_eq_cellCentre]
    exact pathNearReal_axisPath _ hodd.pos (fun v hv k hk =>
      hg (cellCentre F.depth y + siteOfCoords F.depth v, k) (cellCentre_add_mem_innerBonds hy hv hk)) hh π
  have h1 := norm_complexRelativePathAverage_sub_one_le hodd ht (by linarith) hp
  set e := complexRelativePathAverage X R y - 1 with he
  have h2 : complexRelativePathAverage X R y = 1 + e := by rw [he, add_sub_cancel]
  have h3 := norm_unitPart_one_add_sub_le (e := e) (h1.trans hsm)
  have h4 : ‖unitPart (1 + e) - 1‖ ≤ 5 * ‖e‖ := by
    have e1 : unitPart (1 + e) - 1 = (unitPart (1 + e) - 1 - purePart e) + purePart e := by abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h5 := norm_purePart_le e
    have h6 : ‖e‖ ≤ 1 / 8 := h1.trans hsm
    nlinarith [norm_nonneg e]
  have h7 : complexBalancingGauge X R y - 1 = Matrix.adjugate (unitPart (1 + e) - 1) := by
    rw [adjugate_map_sub, adjugate_one_complexQuat, complexBalancingGauge, h2]
  rw [h7, norm_adjugate]
  refine h4.trans ?_
  nlinarith [norm_nonneg e]
theorem norm_mul_seven_sub_one_le {a b c d e f g : ComplexQuat} {δ : ℝ} (h0 : 0 ≤ δ) (hδ : 14 * δ ≤ 1)
    (ha : ‖a - 1‖ ≤ δ) (hb : ‖b - 1‖ ≤ δ) (hc : ‖c - 1‖ ≤ δ) (hd : ‖d - 1‖ ≤ δ) (he : ‖e - 1‖ ≤ δ)
    (hf : ‖f - 1‖ ≤ δ) (hg : ‖g - 1‖ ≤ δ) : ‖a * b * c * d * e * f * g - 1‖ ≤ 14 * δ := by
  have step : ∀ (p q : ComplexQuat) (k : ℕ), ‖p - 1‖ ≤ (1 + δ) ^ k - 1 → ‖q - 1‖ ≤ δ →
      ‖p * q - 1‖ ≤ (1 + δ) ^ (k + 1) - 1 := by
    intro p q k hp hq
    refine (norm_mul_sub_one_le_complexQuat p q).trans ?_
    rw [pow_succ]
    have h1 : 1 + ‖p - 1‖ ≤ (1 + δ) ^ k := by linarith
    have h2 : 1 + ‖q - 1‖ ≤ 1 + δ := by linarith
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith
  have s1 : ‖a - 1‖ ≤ (1 + δ) ^ 1 - 1 := by simpa using ha
  have s7 := step _ g 6 (step _ f 5 (step _ e 4 (step _ d 3 (step _ c 2 (step _ b 1 s1 hb) hc) hd) he) hf) hg
  have := one_add_pow_sub_one_le_two_mul h0 7 (by push_cast; linarith)
  push_cast at this
  have e7 : (1 + δ) ^ (6 + 1) = (1 + δ) ^ 7 := rfl
  rw [e7] at s7
  linarith
theorem ofUnit_mul_adjugate_mul_ofUnit (P v : UnitQuaternion) (w : ComplexQuat) :
    ofUnit P * Matrix.adjugate (w * ofUnit v) = ofUnit (P * v⁻¹) * Matrix.adjugate w := by
  rw [Matrix.adjugate_mul_distrib, ofUnit_mul, mul_assoc, ofUnit_inv]
theorem norm_mul_six_sub_one_le {a b c d e f : ComplexQuat} {δ : ℝ} (h0 : 0 ≤ δ) (hδ : 14 * δ ≤ 1)
    (ha : ‖a - 1‖ ≤ δ) (hb : ‖b - 1‖ ≤ δ) (hc : ‖c - 1‖ ≤ δ) (hd : ‖d - 1‖ ≤ δ) (he : ‖e - 1‖ ≤ δ)
    (hf : ‖f - 1‖ ≤ δ) : ‖a * b * c * d * e * f - 1‖ ≤ 14 * δ := by
  have hone : ‖(1 : ComplexQuat) - 1‖ ≤ δ := by
    rw [sub_self, norm_zero]
    exact h0
  have h7 := norm_mul_seven_sub_one_le h0 hδ ha hb hc hd he hf hone
  rwa [mul_one] at h7
theorem norm_complexGaugedBondElement_sub_one_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hg : ∀ b ∈ innerBonds D F.depth, BondNearReal X R tt b.1 b.2)
    (ht : 0 ≤ tt) (hsm : 4 * (F.blockSide : ℝ) * tt ≤ 1 / 8) {V : F.GaugeField F.top} {τ : ComplexQuat} {δ : ℝ}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds D F.depth)
    (hδ : 20 * (F.blockSide : ℝ) * tt + ‖τ‖ +
      ‖((gaugedBondElement R (fun _ => 1) V b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ)
    (hδ1 : 14 * δ ≤ 1) :
    ‖complexGaugedBondElement X (complexBalancingGauge X R) ((1 + τ) * ofUnit (V (enclosingCell b.1) b.2)) b - 1‖ ≤
      14 * δ := by
  classical
  obtain ⟨x, i⟩ := b
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hb
  simp only at hx hx' hδ ⊢
  set x' := x + unitStep F.depth i with hx'd
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hLt : 0 ≤ (F.blockSide : ℝ) * tt := by positivity
  have hτ0 := norm_nonneg τ
  have hG0 := norm_nonneg (((gaugedBondElement R (fun _ => 1) V (x, i) : UnitQuaternion) : ℍ[ℝ]) - 1)
  set B := relativeHolonomy X R (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1) with hB
  set B' := relativeHolonomy X R (cellCentre F.depth (enclosingCell x')) (axisPath (cellOffset x') 1) with hB'
  set T₁ := treeHolonomy R x with hT₁
  set T₂ := treeHolonomy R x' with hT₂
  set g := linkDeviation X R x i with hgd
  set P₂ : UnitQuaternion := T₁ * R x i * T₂⁻¹ with hP₂
  have hyD : enclosingCell x ∈ D := by
    obtain ⟨y, hy, h, hh, e⟩ := exists_cellSite_eq hx
    rw [e, enclosingCell_cellSite hodd y hh]
    exact hy
  have hyD' : enclosingCell x' ∈ D := by
    obtain ⟨y, hy, h, hh, e⟩ := exists_cellSite_eq hx'
    rw [e, enclosingCell_cellSite hodd y hh]
    exact hy
  set a := complexBalancingGauge X R (enclosingCell x) with ha
  set a' := complexBalancingGauge X R (enclosingCell x') with ha'
  have hT : complexTreeHolonomy X x = B * ofUnit T₁ := complexTreeHolonomy_eq_relativeHolonomy_mul X R x
  have hT' : complexTreeHolonomy X x' = B' * ofUnit T₂ := complexTreeHolonomy_eq_relativeHolonomy_mul X R x'
  have hXb : X x i = (1 + g) * ofUnit (R x i) := field_eq_one_add_linkDeviation_mul X R x i
  have hadj : Matrix.adjugate (complexTreeHolonomy X x') = ofUnit T₂⁻¹ * Matrix.adjugate B' := by
    rw [hT', Matrix.adjugate_mul_distrib, ofUnit_inv]
  have hPg : ofUnit P₂ = ofUnit T₁ * (ofUnit (R x i) * ofUnit T₂⁻¹) := by
    rw [hP₂, ofUnit_mul, ofUnit_mul, mul_assoc]
  have hmain : ∀ tl : ComplexQuat, a * complexTreeHolonomy X x * X x i *
      Matrix.adjugate (complexTreeHolonomy X x') * Matrix.adjugate a' * tl =
      a * B * conjByUnit T₁ (1 + g) * conjByUnit P₂ (Matrix.adjugate B') *
        conjByUnit P₂ (Matrix.adjugate a') * (ofUnit P₂ * tl) := by
    intro tl
    rw [hT, hXb, hadj]
    simp only [conjByUnit, mul_assoc, ofUnit_inv_mul_cancel_left]
    rw [hPg]
    simp only [mul_assoc, ofUnit_inv_mul_cancel_left]
  have hBn : ‖B - 1‖ ≤ 4 * (F.blockSide : ℝ) * tt :=
    norm_relativeHolonomy_axisPath_sub_one_le hamb hodd hg ht (by linarith) hx
  have hBn' : ‖B' - 1‖ ≤ 4 * (F.blockSide : ℝ) * tt :=
    norm_relativeHolonomy_axisPath_sub_one_le hamb hodd hg ht (by linarith) hx'
  have han : ‖a - 1‖ ≤ 20 * (F.blockSide : ℝ) * tt := norm_complexBalancingGauge_sub_one_le hodd hg ht hsm hyD
  have han' : ‖a' - 1‖ ≤ 20 * (F.blockSide : ℝ) * tt := norm_complexBalancingGauge_sub_one_le hodd hg ht hsm hyD'
  have hgn : ‖g‖ ≤ tt := (hg (x, i) hb).1
  have hadj1 : ∀ e : ComplexQuat, ‖Matrix.adjugate e - 1‖ = ‖e - 1‖ := fun e => by
    have : Matrix.adjugate e - 1 = Matrix.adjugate (e - 1) := by
      rw [adjugate_map_sub, adjugate_one_complexQuat]
    rw [this, norm_adjugate]
  have hcAd1 : ∀ (w : UnitQuaternion) (e : ComplexQuat), ‖conjByUnit w e - 1‖ = ‖e - 1‖ := fun w e => by
    have : conjByUnit w e - 1 = conjByUnit w (e - 1) := by rw [conjByUnit_sub, conjByUnit_one]
    rw [this, norm_conjByUnit]
  have hδ0 : 0 ≤ δ := by linarith
  have b1 : ‖a - 1‖ ≤ δ := by linarith
  have b2 : ‖B - 1‖ ≤ δ := by linarith
  have b3 : ‖conjByUnit T₁ (1 + g) - 1‖ ≤ δ := by
    rw [hcAd1, add_sub_cancel_left]
    nlinarith
  have b4 : ‖conjByUnit P₂ (Matrix.adjugate B') - 1‖ ≤ δ := by
    rw [hcAd1, hadj1]
    linarith
  have b5 : ‖conjByUnit P₂ (Matrix.adjugate a') - 1‖ ≤ δ := by
    rw [hcAd1, hadj1]
    linarith
  have hGd : ‖ofUnit (gaugedBondElement R (fun _ => 1) V (x, i)) - 1‖ ≤ δ := by
    rw [norm_ofUnit_sub_one]
    linarith
  have hel : gaugedBondElement R (fun _ => 1) V (x, i) =
      P₂ * if IsCrossingBond (x, i) then (V (enclosingCell x) i)⁻¹ else 1 := by
    unfold gaugedBondElement
    simp only [one_mul, inv_one, mul_one]
    rfl
  have hE : complexGaugedBondElement X (complexBalancingGauge X R) ((1 + τ) * ofUnit (V (enclosingCell x) i)) (x, i) =
      a * complexTreeHolonomy X x * X x i * Matrix.adjugate (complexTreeHolonomy X x') * Matrix.adjugate a' *
        if IsCrossingBond (x, i) then Matrix.adjugate ((1 + τ) * ofUnit (V (enclosingCell x) i)) else 1 := rfl
  rw [hE, hmain]
  clear_value a a' B B' P₂ g
  by_cases hcr : IsCrossingBond (x, i)
  · rw [if_pos hcr]
    rw [if_pos hcr] at hel
    have e1 : ofUnit P₂ * Matrix.adjugate ((1 + τ) * ofUnit (V (enclosingCell x) i)) =
        ofUnit (gaugedBondElement R (fun _ => 1) V (x, i)) * Matrix.adjugate (1 + τ) := by
      rw [hel]
      exact ofUnit_mul_adjugate_mul_ofUnit _ _ _
    rw [e1, ← mul_assoc]
    refine norm_mul_seven_sub_one_le hδ0 hδ1 b1 b2 b3 b4 b5 hGd ?_
    rw [hadj1, add_sub_cancel_left]
    linarith
  · rw [if_neg hcr]
    rw [if_neg hcr, mul_one] at hel
    rw [mul_one]
    have hGd' : ‖ofUnit P₂ - 1‖ ≤ δ := by
      rw [← hel]
      exact hGd
    exact norm_mul_six_sub_one_le hδ0 hδ1 b1 b2 b3 b4 b5 hGd'
end Near
end BlockGeometry
end YangMills.Construction.ComplexChart
end
