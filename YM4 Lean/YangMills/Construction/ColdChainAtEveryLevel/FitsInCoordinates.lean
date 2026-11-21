import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACellProof
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.ChartFits
open VariationRates
variable {F : BlockFrame}
theorem chartChain_of_lt (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ} (hj : j < F.top) :
    chartChain R U V j = chartField R U j := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_of_lt <;> assumption
theorem chartChain_top_eq (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.top = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem norm_smul_polarUnit (q : ℍ[ℝ]) : ‖q‖ • ((polarUnit q : UnitQuaternion) : ℍ[ℝ]) = q := by
  by_cases h : q = 0
  · subst h
    simp
  · rw [coe_polarUnit h, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]
theorem re_coe_inv (g : UnitQuaternion) :
    (((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ((g : UnitQuaternion) : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.TorusFields.re_unitQuaternion_inv <;> assumption
theorem re_mul_coe_inv_mul_polarUnit (q : ℍ[ℝ]) (g : UnitQuaternion) :
    (q * (((g * polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ‖q‖ * ((g : UnitQuaternion) : ℍ[ℝ]).re := by
  have e1 : (((g * polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (((polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [mul_inv_rev]
    rfl
  have e2 : q * (((polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (‖q‖ : ℝ) • (1 : ℍ[ℝ]) := by
    have h : (‖q‖ • ((polarUnit q : UnitQuaternion) : ℍ[ℝ])) * (((polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        (‖q‖ : ℝ) • (1 : ℍ[ℝ]) := by
      rw [smul_mul_assoc, coe_mul_coe_inv]
    rwa [norm_smul_polarUnit] at h
  rw [e1, ← mul_assoc, e2, smul_mul_assoc, one_mul]
  simp only [Quaternion.re_smul, smul_eq_mul, re_coe_inv]
theorem gaugedBlockFit_of_lt (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ}
    (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c =
      ‖gaugedBondAverage R U j c‖ *
        (1 - ((expUnit (U.coarse j c.1 c.2) * referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]).re) := by
  rw [chartChain_of_lt R U V hj, chartChain_of_lt R U V (by omega : j < F.top)]
  unfold gaugedBlockFit
  have e : chartField R U (j + 1) c.1 c.2 =
      (expUnit (U.coarse j c.1 c.2) * referenceDefect R j c) * polarUnit (gaugedBondAverage R U j c) := rfl
  rw [e]
  have h := re_mul_coe_inv_mul_polarUnit (gaugedBondAverage R U j c)
    (expUnit (U.coarse j c.1 c.2) * referenceDefect R j c)
  have e2 : gaugedContourAverage (chartField R U j) (chartGauge R U (j + 1)) c = gaugedBondAverage R U j c := rfl
  rw [e2, h]
  ring
theorem gaugedBlockFit_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (hV : R F.top = V)
    (c : F.Site (F.depth + 1) × Fin 4) :
    gaugedBlockFit (chartChain R U V F.depth) (chartGauge R U (F.depth + 1)) (chartChain R U V (F.depth + 1)) c =
      ‖gaugedBondAverage R U F.depth c‖ *
        (1 - ((bondAverageGap R U F.depth c * (referenceDefect R F.depth c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
  rw [chartChain_of_lt R U V (by simp : F.depth < F.top)]
  have e1 : chartChain R U V (F.depth + 1) = V := chartChain_top_eq R U V
  rw [e1]
  unfold gaugedBlockFit
  have e2 : gaugedContourAverage (chartField R U F.depth) (chartGauge R U (F.depth + 1)) c =
      gaugedBondAverage R U F.depth c := rfl
  rw [e2]
  set Y := gaugedBondAverage R U F.depth c with hY
  set u0 := polarUnit (contourAverage (R F.depth) c) with hu0
  set m := referenceDefect R F.depth c with hm
  have hVc : V c.1 c.2 = m * u0 := by
    have : m = R (F.depth + 1) c.1 c.2 * u0⁻¹ := rfl
    rw [this, inv_mul_cancel_right]
    exact (congrFun (congrFun hV c.1) c.2).symm
  have e3 : bondAverageGap R U F.depth c = polarUnit Y * u0⁻¹ := rfl
  rw [hVc, e3]
  have e4 : ((m * u0)⁻¹ : UnitQuaternion) = u0⁻¹ * m⁻¹ := mul_inv_rev _ _
  rw [e4]
  have e5 : Y * (((u0⁻¹ * m⁻¹ : UnitQuaternion)) : ℍ[ℝ]) =
      ‖Y‖ • ((polarUnit Y * u0⁻¹ * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have h : (‖Y‖ • ((polarUnit Y : UnitQuaternion) : ℍ[ℝ])) * (((u0⁻¹ * m⁻¹ : UnitQuaternion)) : ℍ[ℝ]) =
        ‖Y‖ • ((polarUnit Y * u0⁻¹ * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [smul_mul_assoc]
      congr 1
      simp only [Submonoid.coe_mul, mul_assoc]
    rwa [norm_smul_polarUnit] at h
  rw [e5]
  simp only [Quaternion.re_smul, smul_eq_mul]
  ring
theorem normalized_sum_one (hodd : Odd F.blockSide) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugedCriticality.average_one <;> assumption
theorem polarUnit_one : polarUnit (1 : ℍ[ℝ]) = 1 := by
  apply Subtype.ext
  rw [coe_polarUnit one_ne_zero]
  simp
theorem balancingGauge_self (hodd : Odd F.blockSide) {j : ℕ} (X : F.GaugeField j) (y : F.Site (j + 1)) :
    balancingGauge X X y = 1 := by
  unfold balancingGauge relativePathAverage
  simp only [mul_inv_cancel, OneMemClass.coe_one]
  rw [normalized_sum_one hodd, polarUnit_one, inv_one]
theorem gaugedContourAverage_one {j : ℕ} (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    gaugedContourAverage X (fun _ => 1) c = contourAverage X c := by
  simp [gaugedContourAverage]
theorem chartField_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ) :
    chartField R (zeroChart F) j = R j := by
  induction j with
  | zero =>
    funext x i
    show expUnit ((zeroChart F).fine x i) * R 0 x i = R 0 x i
    simp [zeroChart, expUnit_zero]
  | succ j ih =>
    funext y i
    show expUnit ((zeroChart F).coarse j y i) * referenceDefect R j (y, i) *
      polarUnit (gaugedContourAverage (chartField R (zeroChart F) j)
        (balancingGauge (chartField R (zeroChart F) j) (R j)) (y, i)) = R (j + 1) y i
    rw [ih]
    have e : balancingGauge (R j) (R j) = fun _ => 1 := funext (balancingGauge_self hodd (R j))
    rw [e, gaugedContourAverage_one]
    simp [zeroChart, expUnit_zero, referenceDefect]
theorem chartGap_zero (R : F.FieldChain) (U : ChainChart F) (x : F.Site 0) (i : Fin 4) :
    chartGap R U 0 x i = expUnit (U.fine x i) := by apply _root_.YangMills.Construction.LevelGaps.chartGap_zero <;> assumption
def innerFit (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  ‖gaugedBondAverage R U j c‖ *
    (1 - ((expUnit (U.coarse j c.1 c.2) * referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]).re)
def topFit (R : F.FieldChain) (U : ChainChart F) (c : F.Site (F.depth + 1) × Fin 4) : ℝ :=
  ‖gaugedBondAverage R U F.depth c‖ *
    (1 - ((bondAverageGap R U F.depth c * (referenceDefect R F.depth c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re)
theorem chartAction_eq_sum (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) (hV : R F.top = V) :
    chartAction a S R U V = wilsonAction S (chartField R U 0) +
      a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), innerFit R U j c +
        ∑ c ∈ innerBonds S (F.depth + 1), topFit R U c) := by
  unfold chartAction gaugedChainAction
  rw [chartChain_of_lt R U V (by simp : 0 < F.top)]
  congr 2
  rw [show F.top = F.depth + 1 from rfl, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_
    exact gaugedBlockFit_of_lt R U V (by have := Finset.mem_range.1 hj; simp only [BlockFrame.top]; omega) c
  · exact Finset.sum_congr rfl fun c _ => gaugedBlockFit_top R U V hV c
theorem holonomyRate_plaquetteBoundary (X : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    holonomyRate X u p.1 (plaquetteBoundary p) = linearizedCurl X u p := by
  obtain ⟨x, μ, ν⟩ := p
  have e1 : x + unitStep 0 μ + unitStep 0 ν - unitStep 0 μ = x + unitStep 0 ν := by abel
  have e2 : x + unitStep 0 μ + unitStep 0 ν + -unitStep 0 μ = x + unitStep 0 ν := by abel
  have e3 : x + unitStep 0 ν - unitStep 0 ν = x := by abel
  have e4 : x + unitStep 0 ν + -unitStep 0 ν = x := by abel
  have m1 : ∀ (g h : UnitQuaternion) (w : ℍ[ℝ]), _root_.YangMills.Construction.BlockAverages.adjointAction (g * h) w = _root_.YangMills.Construction.BlockAverages.adjointAction g (_root_.YangMills.Construction.BlockAverages.adjointAction h w) := by
    intro g h w
    simp only [_root_.YangMills.Construction.BlockAverages.adjointAction, mul_inv_rev, Submonoid.coe_mul, mul_assoc]
  have hz : ∀ g : UnitQuaternion, _root_.YangMills.Construction.BlockAverages.adjointAction g 0 = 0 := fun g => by simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
  simp only [plaquetteBoundary, holonomyRate, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    e1, e2, e3, e4, linearizedCurl, m1, _root_.YangMills.Construction.BlockAverages.VariationRates.adjointAction_add, _root_.YangMills.Construction.BlockAverages.VariationRates.adjointAction_neg, hz, add_zero]
  abel
theorem hasDerivAt_wilsonAction_chartMove (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) :
    HasDerivAt (fun τ : ℝ => wilsonAction S (chartField R (chartMove (zeroChart F) A τ) 0))
      (∑ p ∈ innerPlaquettes S 0,
        - (linearizedCurl (R 0) A.fine p * ((plaquetteHolonomy (R 0) p : UnitQuaternion) : ℍ[ℝ])).re) 0 := by
  have h0 : (fun τ : ℝ => chartField R (chartMove (zeroChart F) A τ) 0) 0 = R 0 := by
    funext x i
    show expUnit ((0 : imaginaryQuaternions) + (0 : ℝ) • A.fine x i) * R 0 x i = R 0 x i
    simp [expUnit_zero]
  have hd : ∀ x i, HasDerivAt
      (fun τ : ℝ => ((chartField R (chartMove (zeroChart F) A τ) 0 x i : UnitQuaternion) : ℍ[ℝ]))
      ((A.fine x i : ℍ[ℝ]) * (R 0 x i : ℍ[ℝ])) 0 := by
    intro x i
    have h1 := (hasDerivAt_expUnit_smul (A.fine x i)).mul_const ((R 0 x i : UnitQuaternion) : ℍ[ℝ])
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    show ((expUnit ((0 : imaginaryQuaternions) + τ • A.fine x i) * R 0 x i : UnitQuaternion) : ℍ[ℝ]) = _
    simp
  unfold wilsonAction
  refine HasDerivAt.fun_sum fun p _ => ?_
  have hh := hasDerivAt_pathHolonomy (Xc := fun τ : ℝ => chartField R (chartMove (zeroChart F) A τ) 0) h0 hd p.1
    (plaquetteBoundary p)
  have hr := (ChartCoordinates.reCLM).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hh
  have := hr.const_sub (1 : ℝ)
  rw [holonomyRate_plaquetteBoundary] at this
  exact this
end YangMills.Construction.BlockAverages.ChartFits
end
