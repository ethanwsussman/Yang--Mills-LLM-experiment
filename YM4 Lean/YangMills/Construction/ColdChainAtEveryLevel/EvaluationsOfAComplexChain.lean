import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages.ComplexChartCoordinates
open LatticePaths ChartCoordinates ComplexifiedQuaternions FiniteDifferences LatticeFractionalIntegration
variable {F : BlockFrame}
section Congr
variable {j : ℕ} {D : Set (F.Site j)}
theorem complexPathHolonomy_congr {X X' : F.ComplexField j}
    (h : ∀ x i, x ∈ D → x + unitStep j i ∈ D → X x i = X' x i)
    (x₀ : F.Site j) : ∀ (l : List PathStep) (v : Lattice4),
      AllAlong (fun v => x₀ + siteOfCoords j v ∈ D) v l →
      complexPathHolonomy X (x₀ + siteOfCoords j v) l = complexPathHolonomy X' (x₀ + siteOfCoords j v) l := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons s r ih =>
    intro v hp
    have hnext : x₀ + siteOfCoords j v + stepDisplacement j s =
        x₀ + siteOfCoords j (v + FlatPairing.stepDisplacement s) := by
      rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hv : x₀ + siteOfCoords j v ∈ D := hp.1
    have hw : x₀ + siteOfCoords j v + stepDisplacement j s ∈ D := by
      rw [hnext]; exact allAlong_head hp.2
    simp only [complexPathHolonomy]
    rw [hnext, ih _ hp.2]
    congr 1
    rcases s with ⟨i, b⟩
    cases b
    · simp only [complexLinkValue, Bool.false_eq_true, if_false]
      have e : x₀ + siteOfCoords j v + stepDisplacement j (i, false) =
          x₀ + siteOfCoords j v - unitStep j i := by
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e] at hw
      rw [h _ i hw (by rw [sub_add_cancel]; exact hv)]
    · simp only [complexLinkValue, if_true]
      have e : x₀ + siteOfCoords j v + stepDisplacement j (i, true) =
          x₀ + siteOfCoords j v + unitStep j i := by
        simp [stepDisplacement]
      rw [e] at hw
      rw [h _ i hv hw]
end Congr
section Reads
variable {S : Finset F.Cell}
def ComplexAgreeOnBonds (S : Finset F.Cell) (j : ℕ) (X X' : F.ComplexField j) : Prop :=
  ∀ x i, x ∈ sitesOfCells S j → x + unitStep j i ∈ sitesOfCells S j → X x i = X' x i
theorem complexRelativePathAverage_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X X' : F.ComplexField j} (R : F.GaugeField j)
    (h : ComplexAgreeOnBonds S j X X') {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1)) :
    complexRelativePathAverage X R y = complexRelativePathAverage X' R y := by
  unfold complexRelativePathAverage
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have := complexPathHolonomy_congr (D := (sitesOfCells S j : Set (F.Site j)))
    (fun x i hx hx' => h x i hx hx') (refineSite y) _ 0 (allAlong_axisPath hodd hj hy ha π)
  rw [add_siteOfCoords_zero] at this
  rw [this]
theorem complexBalancingGauge_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X X' : F.ComplexField j} (R : F.GaugeField j)
    (h : ComplexAgreeOnBonds S j X X') {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1)) :
    complexBalancingGauge X R y = complexBalancingGauge X' R y := by
  unfold complexBalancingGauge
  rw [complexRelativePathAverage_congr hodd hj R h hy]
theorem complexContourAverage_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X X' : F.ComplexField j}
    (h : ComplexAgreeOnBonds S j X X') {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    complexContourAverage X c = complexContourAverage X' c := by
  unfold complexContourAverage
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have := complexPathHolonomy_congr (D := (sitesOfCells S j : Set (F.Site j)))
    (fun x i hx hx' => h x i hx hx') (refineSite c.1) _ 0 (allAlong_bondContour hodd hj hc ha π)
  rw [add_siteOfCoords_zero] at this
  rw [this]
theorem complexGaugedContourAverage_congr {j : ℕ} (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X X' : F.ComplexField j} (R : F.GaugeField j)
    (h : ComplexAgreeOnBonds S j X X') {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    complexGaugedContourAverage X (complexBalancingGauge X R) c =
      complexGaugedContourAverage X' (complexBalancingGauge X' R) c := by
  unfold complexGaugedContourAverage
  rw [complexContourAverage_congr hodd hj h hc, complexBalancingGauge_congr hodd hj R h (innerBonds_ends hc).1,
    complexBalancingGauge_congr hodd hj R h (innerBonds_ends hc).2]
theorem complexChartField_congr (hodd : Odd F.blockSide) (R : F.FieldChain) {W W' : ComplexChainChart F}
    (h₁ : ChartEqOnBonds S W.re W'.re) (h₂ : ChartEqOnBonds S W.im W'.im) : ∀ j, j < F.top →
    ComplexAgreeOnBonds S j (complexChartField R W j) (complexChartField R W' j) := by
  intro j
  induction j with
  | zero =>
    intro _ x i hx hx'
    simp only [complexChartField]
    rw [h₁.1 (x, i) (mem_innerBonds hx hx'), h₂.1 (x, i) (mem_innerBonds hx hx')]
  | succ j ih =>
    intro hj x i hx hx'
    have hb := mem_innerBonds hx hx'
    have e := complexGaugedContourAverage_congr hodd (by omega) (R j) (ih (by omega)) hb
    simp only [complexChartField]
    rw [e, h₁.2 j hj (x, i) hb, h₂.2 j hj (x, i) hb]
theorem complexPlaquetteHolonomy_congr {X X' : F.ComplexField 0} (h : ComplexAgreeOnBonds S 0 X X')
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    complexPlaquetteHolonomy X p = complexPlaquetteHolonomy X' p := by
  have := complexPathHolonomy_congr (D := (sitesOfCells S 0 : Set (F.Site 0)))
    (fun x i hx hx' => h x i hx hx') p.1 _ 0 (allAlong_plaquette hp)
  rw [add_siteOfCoords_zero] at this
  exact this
theorem complexChainOverTop_of_lt (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top)
    {j : ℕ} (hj : j < F.top) :
    complexChainOverTop R W T j = complexChartField R W j := by
  unfold complexChainOverTop
  rw [Function.update_of_ne (by omega)]
theorem complexChainOverTop_top (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top) :
    complexChainOverTop R W T F.top = T := by
  unfold complexChainOverTop
  rw [Function.update_self]
theorem complexTotalOverTop_congr (hodd : Odd F.blockSide) (a : ℝ) (R : F.FieldChain) (T : F.ComplexField F.top)
    {W W' : ComplexChainChart F} (h₁ : ChartEqOnBonds S W.re W'.re) (h₂ : ChartEqOnBonds S W.im W'.im) :
    complexTotalOverTop a S R W T = complexTotalOverTop a S R W' T := by
  have hf := complexChartField_congr hodd R h₁ h₂
  unfold complexTotalOverTop
  have h0 : 0 < F.top := Nat.succ_pos _
  have e₁ : ∑ p ∈ innerPlaquettes S 0, complexPlaquetteTerm (complexChartField R W 0) p =
      ∑ p ∈ innerPlaquettes S 0, complexPlaquetteTerm (complexChartField R W' 0) p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    unfold complexPlaquetteTerm
    rw [complexPlaquetteHolonomy_congr (hf 0 h0) hp]
  have e₂ : ∀ j ∈ Finset.range F.top, ∀ c ∈ innerBonds S (j + 1),
      complexBondTermOverTop R W T j c = complexBondTermOverTop R W' T j c := by
    intro j hj c hc
    have hjn : j < F.top := Finset.mem_range.1 hj
    have hm : complexGaugedContourAverage (complexChartField R W j)
        (complexBalancingGauge (complexChartField R W j) (R j)) c =
      complexGaugedContourAverage (complexChartField R W' j)
        (complexBalancingGauge (complexChartField R W' j) (R j)) c :=
        complexGaugedContourAverage_congr hodd hjn (R j) (hf j hjn) hc
    have hl : ∀ W₀ : ComplexChainChart F,
        complexBalancingGauges R W₀ (j + 1) = complexBalancingGauge (complexChartField R W₀ j) (R j) :=
      fun _ => rfl
    unfold complexBondTermOverTop
    rw [complexChainOverTop_of_lt R W T hjn, complexChainOverTop_of_lt R W' T hjn, hl, hl, hm]
    by_cases htop : j + 1 < F.top
    · rw [complexChainOverTop_of_lt R W T htop, complexChainOverTop_of_lt R W' T htop,
        hf (j + 1) htop c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2]
    · obtain rfl : j = F.depth := by
        have hn : F.top = F.depth + 1 := rfl
        omega
      rw [complexChainOverTop_top R W T, complexChainOverTop_top R W' T]
  rw [e₁, Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl (e₂ j hj)]
end Reads
section Real
variable {S : Finset F.Cell}
theorem complexPlaquetteHolonomy_complexify (X : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    complexPlaquetteHolonomy (complexifyField X) p = ofUnit (plaquetteHolonomy X p) :=
  complexPathHolonomy_complexify X p.1 _
theorem complexPlaquetteTerm_complexify (X : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    complexPlaquetteTerm (complexifyField X) p =
      ((1 - ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]).re : ℝ) : ℂ) := by
  unfold complexPlaquetteTerm
  rw [complexPlaquetteHolonomy_complexify, ofUnit, trace_ofQuat]
  push_cast
  ring
theorem complexBlockFit_ofQuat_ofUnit {q : ℍ[ℝ]} (hq : q ≠ 0) (g : UnitQuaternion) :
    complexBlockFit (ofQuat q) (ofUnit g) = ((‖q‖ - (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re : ℝ) : ℂ) := by
  have hn : 0 < ‖q‖ := norm_pos_iff.2 hq
  have e : ofQuat q * Matrix.adjugate (ofUnit g) = ofQuat (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    rw [← ofUnit_inv]
    exact (ofQuat_mul _ _).symm
  unfold complexBlockFit
  rw [det_ofQuat, principalSqrt_ofReal_sq hn, e, trace_ofQuat]
  push_cast
  ring
theorem complexBalancingGauges_realChart (R : F.FieldChain) (U : ChainChart F) (j : ℕ) :
    complexBalancingGauges R (realChart U) (j + 1) = fun y => ofUnit (chartGauge R U (j + 1) y) := by
  funext y
  simp only [complexBalancingGauges, chartGauge, complexChartField_realChart, complexBalancingGauge_complexify]
theorem complexChainOverTop_realChart (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (j : ℕ) :
    complexChainOverTop R (realChart U) (complexifyField V) j = complexifyField (chartChain R U V j) := by
  by_cases h : j = F.top
  · subst h
    have h₁ : chartChain R U V F.top = V := by
      unfold chartChain
      rw [Function.update_self]
    rw [complexChainOverTop_top, h₁]
  · have h₁ : chartChain R U V j = chartField R U j := by
      unfold chartChain
      rw [Function.update_of_ne h]
    have h₂ : complexChainOverTop R (realChart U) (complexifyField V) j = complexChartField R (realChart U) j := by
      unfold complexChainOverTop
      rw [Function.update_of_ne h]
    rw [h₁, h₂, complexChartField_realChart]
theorem complexTotalOverTop_realChart (a : ℝ) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (hreg : ChartIsRegular S R U) :
    complexTotalOverTop a S R (realChart U) (complexifyField V) = (chartAction a S R U V : ℂ) := by
  have h0 : 0 < F.top := Nat.succ_pos _
  unfold complexTotalOverTop chartAction gaugedChainAction wilsonAction
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [complexChartField_realChart, complexPlaquetteTerm_complexify]
    rw [show chartChain R U V 0 = chartField R U 0 from by
      unfold chartChain
      rw [Function.update_of_ne (by omega)]]
    push_cast
    rfl
  · congr 1
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_
    have hjn : j < F.top := Finset.mem_range.1 hj
    unfold complexBondTermOverTop gaugedBlockFit
    rw [complexChainOverTop_realChart, complexChainOverTop_realChart, complexBalancingGauges_realChart]
    have e₁ : chartChain R U V j = chartField R U j := by
      unfold chartChain
      rw [Function.update_of_ne (by omega)]
    have hne : gaugedContourAverage (chartChain R U V j) (chartGauge R U (j + 1)) c ≠ 0 := by
      rw [e₁]
      exact (hreg j hjn).2 c hc
    rw [complexGaugedContourAverage_complexify]
    have := complexBlockFit_ofQuat_ofUnit hne (chartChain R U V (j + 1) c.1 c.2)
    simp only [complexifyField]
    rw [this]
theorem complexTwistedTop_ofReal {k : ℕ} (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : Fin k → ℝ) (V : F.GaugeField F.top) :
    complexTwistedTop b X (fun l => (ζ l : ℂ)) V = complexifyField (rotatedField (bondSpread b X ζ) V) := by
  funext y i
  simp only [complexTwistedTop, complexifyField, rotatedField, bondSpread, ofUnit_mul]
  congr 1
  have h : (∑ l, if b l = (y, i) then ((ζ l : ℝ) : ℂ) • ofQuat (X l : ℍ[ℝ]) else 0) =
      ofQuat (((∑ l, if b l = (y, i) then ζ l • X l else 0 : imaginaryQuaternions)) : ℍ[ℝ]) := by
    have h₁ : (((∑ l, if b l = (y, i) then ζ l • X l else 0 : imaginaryQuaternions)) : ℍ[ℝ]) =
        ∑ l, if b l = (y, i) then ζ l • (X l : ℍ[ℝ]) else 0 := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    rw [h₁, ofQuat_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [ofQuat_smul]
    · rw [ofQuat_zero]
  rw [h, ← ofQuat_exp]
  rfl
theorem complexChartMove_realChart (U A : ChainChart F) (τ : ℝ) :
    complexChartMove (realChart U) A (τ : ℂ) = realChart (chartMove U A τ) := by
  have h : chartMove (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) A 0 = ⟨fun _ _ => 0, fun _ _ _ => 0⟩ := by
    simp [chartMove]
  simp only [complexChartMove, realChart, Complex.ofReal_re, Complex.ofReal_im, h]
open Filter Topology in
theorem complexFirstVariation_real (a : ℝ) (R : F.FieldChain) (U A : ChainChart F) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℂ
      (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove (realChart U) A τ) (complexifyField V)) 0)
    (hreg : ∀ᶠ τ : ℝ in 𝓝 0, ChartIsRegular S R (chartMove U A τ)) :
    HasDerivAt (fun τ : ℝ => chartAction a S R (chartMove U A τ) V)
        (complexFirstVariation a S R (realChart U) (complexifyField V) A).re 0 ∧
      (complexFirstVariation a S R (realChart U) (complexifyField V) A).im = 0 := by
  set f : ℂ → ℂ := fun τ => complexTotalOverTop a S R (complexChartMove (realChart U) A τ) (complexifyField V)
    with hf
  have h₁ : HasDerivAt f (deriv f 0) (((0 : ℝ)) : ℂ) := by
    simpa using hd.hasDerivAt
  have hc : HasDerivAt (fun τ : ℝ => f (τ : ℂ)) (deriv f 0) 0 := h₁.comp_ofReal
  have hev : ∀ᶠ τ : ℝ in 𝓝 0, f (τ : ℂ) = (chartAction a S R (chartMove U A τ) V : ℂ) := by
    filter_upwards [hreg] with τ hτ
    simp only [hf]
    rw [complexChartMove_realChart, complexTotalOverTop_realChart a R _ V hτ]
  have hre : HasDerivAt (fun τ : ℝ => (f (τ : ℂ)).re) (deriv f 0).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have him : HasDerivAt (fun τ : ℝ => (f (τ : ℂ)).im) (deriv f 0).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  refine ⟨hre.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hev] with τ hτ
    rw [hτ]
    simp
  · have h0 : HasDerivAt (fun τ : ℝ => (f (τ : ℂ)).im) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with τ hτ
      rw [hτ]
      simp
    exact him.unique h0
end Real
end YangMills.Construction.BlockAverages.ComplexChartCoordinates
end
