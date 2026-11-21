import YangMills.Construction.ColdChainAtEveryLevel.FitsInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfAPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.RealChartTerms
open BlockAverages ComplexLevels ComplexContours ComplexRemainders ComplexDifferences ComplexifiedQuaternions
  PlaquetteSecondDifference LatticePaths
variable {F : BlockFrame} {j : ℕ}
theorem chartField_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ) :
    chartField R (zeroChart F) j = R j := by apply _root_.YangMills.Construction.BlockAverages.ChartFits.chartField_zeroChart <;> assumption
theorem levelDeviation_realChart (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (x : F.Site j) (i : Fin 4) :
    levelDeviation R (realChart U) j x i = ofUnit (chartField R U j x i) * ofUnit (R j x i)⁻¹ - 1 := by
  simp only [levelDeviation, linkDeviation, complexChartField_realChart]
  rfl
theorem levelDeviation_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ) :
    levelDeviation R (realChart (zeroChart F)) j = 0 := by
  funext x i
  rw [levelDeviation_realChart, chartField_zeroChart hodd, ofUnit_mul_inv, sub_self]
  rfl
theorem holdsOnHull_det_realChart (R : F.FieldChain) (U : ChainChart F) (c : F.Site (j + 1) × Fin 4) :
    HoldsOnHull c (fun b i => (complexChartField R (realChart U) j b i).det = 1) := by
  have h : ∀ b i, (complexChartField R (realChart U) j b i).det = 1 := by
    intro b i
    rw [complexChartField_realChart]
    exact det_ofUnit _
  exact ⟨fun g _ k _ => ⟨h _ _, h _ _⟩, fun g _ r _ => h _ _⟩
theorem liftedBondMean_realChart (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (U : ChainChart F) (c : F.Site (j + 1) × Fin 4) :
    liftedBondMean (R j) c (levelDeviation R (realChart U) j) = ofQuat (gaugedBondAverage R U j c) := by
  have h := complexGaugedContourAverage_eq_liftedBondMean hodd hj (X := complexChartField R (realChart U) j)
    (R := R j) (c := c) (holdsOnHull_det_realChart R U c)
  rw [levelDeviation, ← h, complexChartField_realChart]
  have e : complexBalancingGauge (complexifyField (chartField R U j)) (R j) =
      fun y => ofUnit (balancingGauge (chartField R U j) (R j) y) := by
    funext y
    rw [complexBalancingGauge_complexify]
  rw [e, complexGaugedContourAverage_complexify]
  rfl
theorem linearizedUnit_realChart (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (U : ChainChart F) (c : F.Site (j + 1) × Fin 4) :
    linearizedUnit (R j) c (levelDeviation R (realChart U) j) = ofUnit (bondAverageGap R U j c) := by
  simp only [linearizedUnit, unitRemainder, liftedBondMean_realChart hodd hj, unitPart_ofQuat,
    bondAverageGap, ofUnit_mul]
  abel
theorem sqrtRemainder_realChart (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) (R : F.FieldChain)
    (U : ChainChart F) (c : F.Site (j + 1) × Fin 4) (h : gaugedBondAverage R U j c ≠ 0) :
    sqrtRemainder (R j) c (levelDeviation R (realChart U) j) =
      ((‖gaugedBondAverage R U j c‖ - ‖contourAverage (R j) c‖ : ℝ) : ℂ) := by
  have hn : 0 < ‖gaugedBondAverage R U j c‖ := norm_pos_iff.2 h
  simp only [sqrtRemainder, liftedBondMean_realChart hodd hj, det_ofQuat, principalSqrt_ofReal_sq hn]
  push_cast
  rfl
theorem quaternion_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem chartChain_of_ne_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ}
    (hj : j ≠ F.top) : chartChain R U V j = chartField R U j := by
  simp [chartChain, Function.update_of_ne hj]
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.top = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem eq_norm_smul_polarUnit {q : ℍ[ℝ]} (h : q ≠ 0) : q = ‖q‖ • ((polarUnit q : UnitQuaternion) : ℍ[ℝ]) := by
  rw [coe_polarUnit h, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]
theorem gaugedBlockFit_chartChain_of_lt_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) (h : gaugedBondAverage R U j c ≠ 0) :
    gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c =
      ‖gaugedBondAverage R U j c‖ *
        (1 - ((expUnit (-(U.coarse j c.1 c.2)) * (referenceDefect R j c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
  have e1 : chartChain R U V j = chartField R U j := chartChain_of_ne_top R U V (by omega)
  have e2 : chartChain R U V (j + 1) = chartField R U (j + 1) := chartChain_of_ne_top R U V (by omega)
  rw [e1, e2]
  set m := gaugedBondAverage R U j c with hm
  have em : gaugedContourAverage (chartField R U j) (chartGauge R U (j + 1)) c = m := rfl
  have hX : chartField R U (j + 1) c.1 c.2 = expUnit (U.coarse j c.1 c.2) * referenceDefect R j c * polarUnit m :=
    rfl
  simp only [gaugedBlockFit, em, hX]
  have hq := eq_norm_smul_polarUnit h
  set u := polarUnit m with hu
  set g := expUnit (U.coarse j c.1 c.2) with hg
  set μ := referenceDefect R j c with hμ
  have e3 : m * ((g * μ * u)⁻¹ : UnitQuaternion) = ‖m‖ • (((μ⁻¹ * g⁻¹ : UnitQuaternion)) : ℍ[ℝ]) := by
    conv_lhs => rw [hq]
    rw [smul_mul_assoc]
    congr 1
    have : u * (g * μ * u)⁻¹ = μ⁻¹ * g⁻¹ := by group
    exact congrArg (fun x : UnitQuaternion => (x : ℍ[ℝ])) this
  rw [e3, Quaternion.re_smul, expUnit_neg_eq_inv]
  have e4 : (((g⁻¹ * μ⁻¹ : UnitQuaternion)) : ℍ[ℝ]).re = (((μ⁻¹ * g⁻¹ : UnitQuaternion)) : ℍ[ℝ]).re :=
    quaternion_re_mul_comm _ _
  rw [e4, smul_eq_mul]
  ring
theorem gaugedBlockFit_chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (hV : R F.top = V) (hj : j + 1 = F.top) (c : F.Site (j + 1) × Fin 4) (h : gaugedBondAverage R U j c ≠ 0) :
    gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c =
      ‖gaugedBondAverage R U j c‖ *
        (1 - ((bondAverageGap R U j c * (referenceDefect R j c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
  obtain rfl : j = F.depth := by
    have : j + 1 = F.depth + 1 := hj
    omega
  subst hV
  have e1 : chartChain R U (R F.top) F.depth = chartField R U F.depth := chartChain_of_ne_top R U _ (by omega)
  have e2 : chartChain R U (R F.top) (F.depth + 1) = R F.top := chartChain_top R U _
  rw [e1, e2]
  set m := gaugedBondAverage R U F.depth c with hm
  have em : gaugedContourAverage (chartField R U F.depth) (chartGauge R U (F.depth + 1)) c = m := rfl
  simp only [gaugedBlockFit, em]
  have hq := eq_norm_smul_polarUnit h
  set u := polarUnit m with hu
  set w := polarUnit (contourAverage (R F.depth) c) with hw
  set μ := referenceDefect R F.depth c with hμ
  have hV' : R F.top c.1 c.2 = μ * w := by
    simp only [hμ, referenceDefect, hw, inv_mul_cancel_right]
  have eE : bondAverageGap R U F.depth c = u * w⁻¹ := rfl
  rw [eE, hV']
  have e3 : m * ((μ * w)⁻¹ : UnitQuaternion) = ‖m‖ • (((u * w⁻¹ * μ⁻¹ : UnitQuaternion)) : ℍ[ℝ]) := by
    conv_lhs => rw [hq]
    rw [smul_mul_assoc]
    congr 1
    have : u * (μ * w)⁻¹ = u * w⁻¹ * μ⁻¹ := by group
    exact congrArg (fun x : UnitQuaternion => (x : ℍ[ℝ])) this
  rw [e3, Quaternion.re_smul, smul_eq_mul]
  ring
end YangMills.Construction.RealChartTerms
end
