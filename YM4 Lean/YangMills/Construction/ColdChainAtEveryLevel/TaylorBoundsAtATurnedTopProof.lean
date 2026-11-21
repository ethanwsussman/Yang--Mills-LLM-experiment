import YangMills.Construction.ColdChainAtEveryLevel.LocalFirstVariationProof
import YangMills.Construction.ColdChainAtEveryLevel.CellSecondDifference
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChainIsAnalytic
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationAtTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationsOnASpan
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfAPlaquette
import YangMills.Construction.ColdChainAtEveryLevel.TaylorBoundsAtATurnedTop
import YangMills.Construction.ColdChainAtEveryLevel.TopMeanInAWeight
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtComplexCoordinates
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator Topology
open Filter Metric
namespace YangMills.Construction
open BlockAverages ComplexifiedQuaternions CoordinateSeminorms BlockAverages.ComplexChartCoordinates
  PlaquetteSecondDifference ComplexAnalyticity ComplexDifferences
namespace RotatedTop
section Splitting
variable {F : BlockFrame} {k m : ℕ}
theorem complexBlockFit_sub (M Y Y' : ComplexQuat) : complexBlockFit M Y - complexBlockFit M Y' =
    -(1 / 2 : ℂ) * (M * (Matrix.adjugate Y - Matrix.adjugate Y')).trace := by
  simp only [complexBlockFit, mul_sub, Matrix.trace_sub]
  ring
theorem complexBondTermOverTop_depth (R : F.FieldChain) (W : ComplexChainChart F) (T : F.ComplexField F.top)
    (e : F.Site (F.depth + 1) × Fin 4) :
    complexBondTermOverTop R W T F.depth e = complexBlockFit (topBondGaugedAverage R W e) (T e.1 e.2) := by apply _root_.YangMills.Construction.CellFirstVariation.complexBondTermOverTop_depth <;> assumption
theorem complexBondTermOverTop_below (R : F.FieldChain) (W : ComplexChainChart F) (T T' : F.ComplexField F.top)
    {j : ℕ} (hj : j + 1 < F.top) (e : F.Site (j + 1) × Fin 4) :
    complexBondTermOverTop R W T j e = complexBondTermOverTop R W T' j e := by
  have hj' : j < F.top := by omega
  simp only [complexBondTermOverTop, complexChainOverTop_of_lt R W T hj', complexChainOverTop_of_lt R W T' hj',
    complexChainOverTop_of_lt R W T hj, complexChainOverTop_of_lt R W T' hj]
theorem complexTotalOverTop_sub (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (T T' : F.ComplexField F.top) :
    complexTotalOverTop a S R W T - complexTotalOverTop a S R W T' =
      -((a : ℂ) / 2) * ∑ e ∈ innerBonds S F.top,
        (topBondGaugedAverage R W e * (Matrix.adjugate (T e.1 e.2) - Matrix.adjugate (T' e.1 e.2))).trace := by
  unfold complexTotalOverTop
  have hn : Finset.range F.top = Finset.range (F.depth + 1) := rfl
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
  have hlow : ∑ j ∈ Finset.range F.depth, ∑ e ∈ innerBonds S (j + 1), complexBondTermOverTop R W T j e =
      ∑ j ∈ Finset.range F.depth, ∑ e ∈ innerBonds S (j + 1), complexBondTermOverTop R W T' j e := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun e _ =>
      complexBondTermOverTop_below R W _ _ ?_ e
    have h1 := Finset.mem_range.1 hj
    have : F.top = F.depth + 1 := rfl
    omega
  have htop : ∑ e ∈ innerBonds S (F.depth + 1), complexBondTermOverTop R W T F.depth e -
      ∑ e ∈ innerBonds S (F.depth + 1), complexBondTermOverTop R W T' F.depth e =
      -(1 / 2 : ℂ) * ∑ e ∈ innerBonds S F.top,
        (topBondGaugedAverage R W e * (Matrix.adjugate (T e.1 e.2) - Matrix.adjugate (T' e.1 e.2))).trace := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [complexBondTermOverTop_depth, complexBondTermOverTop_depth, complexBlockFit_sub]
  linear_combination (a : ℂ) * htop + (a : ℂ) * hlow
def twistAt (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℂ)
    (e : F.Site F.top × Fin 4) : ComplexQuat :=
  ∑ l, if b l = e then ζ l • ofQuat (X l : ℍ[ℝ]) else 0
def adjugateChangeAt (V : F.GaugeField F.top) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ζ : Fin k → ℂ) (e : F.Site F.top × Fin 4) : ComplexQuat :=
  Matrix.adjugate (NormedSpace.exp (twistAt b X ζ e) * ofUnit (V e.1 e.2)) - Matrix.adjugate (ofUnit (V e.1 e.2))
theorem complexTotalOverTop_twisted (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (V : F.GaugeField F.top) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℂ) :
    complexTotalOverTop a S R W (complexTwistedTop b X ζ V) = complexTotalOverTop a S R W (complexifyField V) -
      ((a : ℂ) / 2) * ∑ e ∈ innerBonds S F.top, (topBondGaugedAverage R W e * adjugateChangeAt V b X ζ e).trace := by
  have h := complexTotalOverTop_sub a S R W (complexTwistedTop b X ζ V) (complexifyField V)
  have hy : ∀ e : F.Site F.top × Fin 4, Matrix.adjugate (complexTwistedTop b X ζ V e.1 e.2) -
      Matrix.adjugate (complexifyField V e.1 e.2) = adjugateChangeAt V b X ζ e := fun e => rfl
  simp only [hy] at h
  linear_combination h
theorem norm_twistAt_le {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) (ζ : Fin k → ℂ) (e : F.Site F.top × Fin 4) :
    ‖twistAt b X ζ e‖ ≤ ∑ l, if b l = e then ‖ζ l‖ else 0 := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs
  · rw [norm_smul, norm_ofQuat]
    have : ‖(X l : ℍ[ℝ])‖ = 1 := hX l
    rw [this, mul_one]
  · simp
theorem sum_norm_twistAt_le {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) (ζ : Fin k → ℂ) (B : Finset (F.Site F.top × Fin 4)) :
    ∑ e ∈ B, ‖twistAt b X ζ e‖ ≤ ∑ l, ‖ζ l‖ := by
  classical
  refine (Finset.sum_le_sum fun e _ => norm_twistAt_le hX ζ e).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs
  · exact le_rfl
  · exact norm_nonneg _
theorem norm_twistAt_le_sum {b : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) (ζ : Fin k → ℂ) (e : F.Site F.top × Fin 4) : ‖twistAt b X ζ e‖ ≤ ∑ l, ‖ζ l‖ := by
  refine (norm_twistAt_le hX ζ e).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs
  · exact le_rfl
  · exact norm_nonneg _
theorem adjugateChangeAt_eq (V : F.GaugeField F.top) (b : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℂ) (e : F.Site F.top × Fin 4) :
    adjugateChangeAt V b X ζ e = ofUnit (V e.1 e.2)⁻¹ * Matrix.adjugate (NormedSpace.exp (twistAt b X ζ e) - 1) := by
  unfold adjugateChangeAt
  rw [Matrix.adjugate_mul_distrib, adjugate_map_sub, Matrix.adjugate_one, mul_sub, mul_one, ofUnit_inv]
theorem norm_adjugateChangeAt_le (V : F.GaugeField F.top) (b : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℂ) (e : F.Site F.top × Fin 4) (h : ‖twistAt b X ζ e‖ ≤ 1) :
    ‖adjugateChangeAt V b X ζ e‖ ≤ 2 * ‖twistAt b X ζ e‖ := by
  rw [adjugateChangeAt_eq, norm_ofUnit_mul, norm_adjugate]
  have h1 := norm_exp_sub_one_sub_le h
  have h2 : NormedSpace.exp (twistAt b X ζ e) - 1 =
      (NormedSpace.exp (twistAt b X ζ e) - 1 - twistAt b X ζ e) + twistAt b X ζ e := by abel
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  have := norm_nonneg (twistAt b X ζ e)
  nlinarith
end Splitting
section Lines
variable {F : BlockFrame} {k m : ℕ}
theorem analyticAt_exp (x : ComplexQuat) : AnalyticAt ℂ (NormedSpace.exp : ComplexQuat → ComplexQuat) x :=
  NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ) x (by
    rw [NormedSpace.expSeries_radius_eq_top ℂ ComplexQuat]
    exact edist_lt_top _ _)
theorem norm_exp_le_three {x : ComplexQuat} (hx : ‖x‖ ≤ 1) : ‖NormedSpace.exp x‖ ≤ 3 := by
  have h1 := norm_exp_sub_one_sub_le hx
  have e : NormedSpace.exp x = (NormedSpace.exp x - 1 - x) + 1 + x := by abel
  rw [e]
  have h2 := norm_add_le ((NormedSpace.exp x - 1 - x) + 1) x
  have h3 := norm_add_le (NormedSpace.exp x - 1 - x) (1 : ComplexQuat)
  rw [CStarRing.norm_one] at h3
  have := norm_nonneg x
  nlinarith
theorem hasDerivAt_ofReal_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℂ → E} {g' : E} {u : ℝ}
    (h : HasDerivAt g g' (u : ℂ)) : HasDerivAt (fun u : ℝ => g (u : ℂ)) g' u := by
  have hl : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
  have h3 := (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u hl
  simpa [Function.comp_def] using h3
theorem norm_exp_sub_exp_le {x y : ComplexQuat} (hx : ‖x‖ ≤ 1 / 2) (hy : ‖y‖ ≤ 1 / 2) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ ≤ 6 * ‖x - y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  set h := x - y with hh
  have hn : 0 < ‖h‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set g : ℂ → ComplexQuat := fun w => NormedSpace.exp (y + w • h) with hg
  have hline : ∀ w : ℂ, AnalyticAt ℂ (fun w : ℂ => y + w • h) w := fun w =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hgan : ∀ w : ℂ, AnalyticAt ℂ g w := fun w =>
    AnalyticAt.comp (g := NormedSpace.exp) (f := fun w : ℂ => y + w • h) (analyticAt_exp _) (hline w)
  set r : ℝ := 1 / (2 * ‖h‖) with hr
  have hr0 : 0 < r := by positivity
  have hrn : r * ‖h‖ = 1 / 2 := by
    rw [hr]
    field_simp
  have hbd : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖deriv g (u : ℂ)‖ ≤ 6 * ‖h‖ := by
    intro u hu
    have hC : ∀ w ∈ sphere (u : ℂ) r, ‖g w‖ ≤ 3 := by
      intro w hw
      have hw' : ‖w - (u : ℂ)‖ = r := by simpa [dist_eq_norm] using hw
      refine norm_exp_le_three ?_
      have e : y + w • h = ((1 - u : ℝ) : ℂ) • y + (u : ℂ) • x + (w - (u : ℂ)) • h := by
        simp only [hh]
        push_cast
        module
      rw [e]
      have h1 := norm_add_le (((1 - u : ℝ) : ℂ) • y + (u : ℂ) • x) ((w - (u : ℂ)) • h)
      have h2 := norm_add_le (((1 - u : ℝ) : ℂ) • y) ((u : ℂ) • x)
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hu.2]), abs_of_nonneg hu.1] at h2
      rw [norm_smul (w - (u : ℂ)) h, hw', hrn] at h1
      have h3 : (1 - u) * ‖y‖ ≤ (1 - u) * (1 / 2) := mul_le_mul_of_nonneg_left hy (by linarith [hu.2])
      have h4 : u * ‖x‖ ≤ u * (1 / 2) := mul_le_mul_of_nonneg_left hx hu.1
      linarith
    have hdiff : DifferentiableOn ℂ g (closedBall (u : ℂ) r) := fun w _ =>
      (hgan w).differentiableAt.differentiableWithinAt
    have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 (hdiff.diffContOnCl_ball subset_rfl) hC
    refine h1.trans (le_of_eq ?_)
    rw [hr]
    field_simp
    ring
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hm := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun u : ℝ => g (u : ℂ))
    (f' := fun u : ℝ => deriv g (u : ℂ)) (C := 6 * ‖h‖) (x := 0) (y := 1)
    (fun u _ => (hasDerivAt_ofReal_comp (hgan (u : ℂ)).differentiableAt.hasDerivAt).hasDerivWithinAt) hbd
    (by simp) (by simp)
  have e1 : g ((1 : ℝ) : ℂ) = NormedSpace.exp x := by
    simp [hg, hh]
  have e0 : g ((0 : ℝ) : ℂ) = NormedSpace.exp y := by
    simp [hg]
  simp only [e1, e0, sub_zero, norm_one, mul_one] at hm
  exact hm
theorem complexSpan_line (W : ComplexChainChart F) (A : ChainChart F) (τ : ℂ) :
    complexSpan ![W.re, W.im, A] ![1, Complex.I, τ] = complexChartMove W A τ := by
  unfold complexSpan complexChartMove
  congr 1
  · apply chainChart_ext
    · funext p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three]
    · funext j p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three]
  · apply chainChart_ext
    · funext p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three]
    · funext j p i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_three]
theorem complexChartMove_zero (W : ComplexChainChart F) (A : ChainChart F) : complexChartMove W A 0 = W := by apply _root_.YangMills.Construction.SpanVariations.complexChartMove_zero <;> assumption
theorem analyticAt_lineCoefficients : AnalyticAt ℂ (fun τ : ℂ => (![1, Complex.I, τ] : Fin 3 → ℂ)) 0 := by
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_id
variable {a θ δ c C : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem differentiableAt_total_line (hB : ComplexChartBounds a θ δ c C S V) {W : ComplexChainChart F}
    (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c) (A : ChainChart F) :
    DifferentiableAt ℂ
      (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A τ) (complexifyField V)) 0 := by
  have h0 := hB.analyticAt_total 3 ![W.re, W.im, A] ![1, Complex.I, 0]
    (by rw [complexSpan_line, complexChartMove_zero]; exact hW)
  have h1 := AnalyticAt.comp (g := fun q : Fin 3 → ℂ =>
    complexTotalOverTop a S (referenceFieldChain S V) (complexSpan ![W.re, W.im, A] q) (complexifyField V))
    (f := fun τ : ℂ => (![1, Complex.I, τ] : Fin 3 → ℂ)) (x := (0 : ℂ)) h0 analyticAt_lineCoefficients
  have e : (fun τ : ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexChartMove W A τ)
      (complexifyField V)) =
      (fun q : Fin 3 → ℂ => complexTotalOverTop a S (referenceFieldChain S V) (complexSpan ![W.re, W.im, A] q)
        (complexifyField V)) ∘ fun τ : ℂ => (![1, Complex.I, τ] : Fin 3 → ℂ) := by
    funext τ
    simp only [Function.comp, complexSpan_line]
  rw [e]
  exact h1.differentiableAt
theorem differentiableAt_average_line (hB : ComplexChartBounds a θ δ c C S V) {W : ComplexChainChart F}
    (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c) (A : ChainChart F)
    {b : F.Site F.top × Fin 4} (hb : b ∈ innerBonds S F.top) :
    DifferentiableAt ℂ (fun τ : ℂ => topBondGaugedAverage (referenceFieldChain S V) (complexChartMove W A τ) b) 0 := by
  have h0 := hB.analyticAt_average b hb 3 ![W.re, W.im, A] ![1, Complex.I, 0]
    (by rw [complexSpan_line, complexChartMove_zero]; exact hW)
  have h1 := AnalyticAt.comp (g := fun q : Fin 3 → ℂ =>
    topBondGaugedAverage (referenceFieldChain S V) (complexSpan ![W.re, W.im, A] q) b)
    (f := fun τ : ℂ => (![1, Complex.I, τ] : Fin 3 → ℂ)) (x := (0 : ℂ)) h0 analyticAt_lineCoefficients
  have e : (fun τ : ℂ => topBondGaugedAverage (referenceFieldChain S V) (complexChartMove W A τ) b) =
      (fun q : Fin 3 → ℂ => topBondGaugedAverage (referenceFieldChain S V) (complexSpan ![W.re, W.im, A] q) b) ∘
        fun τ : ℂ => (![1, Complex.I, τ] : Fin 3 → ℂ) := by
    funext τ
    simp only [Function.comp, complexSpan_line]
  rw [e]
  exact h1.differentiableAt
def traceMulRight (Y : ComplexQuat) : ComplexQuat →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap (Fin 2) ℂ ℂ) ∘ₗ (LinearMap.mulRight ℂ Y))
theorem complexFirstVariation_twisted (hB : ComplexChartBounds a θ δ c C S V) {W : ComplexChainChart F}
    (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c) (b : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℂ) (A : ChainChart F) :
    complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A =
      complexFirstVariation a S (referenceFieldChain S V) W (complexifyField V) A -
        ((a : ℂ) / 2) * ∑ e ∈ innerBonds S F.top,
          (topBondAverageVelocity (referenceFieldChain S V) W A e * adjugateChangeAt V b X ζ e).trace := by
  set R := referenceFieldChain S V with hR
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A τ) (complexTwistedTop b X ζ V)) =
      fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A τ) (complexifyField V) -
        ((a : ℂ) / 2) * ∑ e ∈ innerBonds S F.top,
          (topBondGaugedAverage R (complexChartMove W A τ) e * adjugateChangeAt V b X ζ e).trace := by
    funext τ
    exact complexTotalOverTop_twisted a S R _ V b X ζ
  rw [e]
  have h1 := (differentiableAt_total_line hB hW A).hasDerivAt
  have h2 : HasDerivAt (fun τ : ℂ => ∑ e ∈ innerBonds S F.top,
      (topBondGaugedAverage R (complexChartMove W A τ) e * adjugateChangeAt V b X ζ e).trace)
      (∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ e).trace) 0 :=
    HasDerivAt.fun_sum fun e he =>
      (traceMulRight (adjugateChangeAt V b X ζ e)).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
        (differentiableAt_average_line hB hW A he).hasDerivAt
  exact (h1.sub (h2.const_mul ((a : ℂ) / 2))).deriv
theorem analyticAt_twistAt (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (e : F.Site F.top × Fin 4) (ζ₀ : Fin k → ℂ) : AnalyticAt ℂ (fun ζ => twistAt b X ζ e) ζ₀ := by
  unfold twistAt
  refine Finset.analyticAt_fun_sum _ fun l _ => ?_
  by_cases h : b l = e
  · simp only [h, if_true]
    exact AnalyticAt.smul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) l).analyticAt ζ₀)
      (analyticAt_const (v := ofQuat (X l : ℍ[ℝ])))
  · simp only [h, if_false]
    exact analyticAt_const
theorem analyticAt_adjugateChangeAt (V : F.GaugeField F.top) (b : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (e : F.Site F.top × Fin 4) (ζ₀ : Fin k → ℂ) :
    AnalyticAt ℂ (fun ζ => adjugateChangeAt V b X ζ e) ζ₀ := by
  unfold adjugateChangeAt
  refine AnalyticAt.sub (analyticAt_adjugate (AnalyticAt.mul ?_ analyticAt_const)) analyticAt_const
  exact AnalyticAt.comp (g := NormedSpace.exp) (f := fun ζ => twistAt b X ζ e) (analyticAt_exp _)
    (analyticAt_twistAt b X e ζ₀)
end Lines
section Fields
variable {F : BlockFrame} {k : ℕ}
variable {a θ δ c C : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} {b : Fin k → F.Site F.top × Fin 4}
  {X : Fin k → imaginaryQuaternions}
set_option maxHeartbeats 1000000 in
theorem firstVariation_twisted_sub_le (ha : 0 ≤ a) (hC : 0 ≤ C) (hB : ComplexChartBounds a θ δ c C S V)
    (hX : AreUnitVectors X) {W W' : ComplexChainChart F} {ζ : Fin k → ℂ}
    (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c)
    (hW' : complexSupWeightedNorm S δ (referenceFieldChain S V) W' ≤ c)
    (hζ : ∑ l, ‖ζ l‖ ≤ 1) {φ : F.Cell → ℝ} {θ' : ℝ} (p : F.Site 0) (hθ' : θ' = θ ∨ θ' = 0 ∨ θ' = -θ)
    (hφ : ∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') (A : ChainChart F)
    (hn : 0 ≤ complexSupWeightedNorm S δ (referenceFieldChain S V) W)
    (hn' : 0 ≤ complexSupWeightedNorm S δ (referenceFieldChain S V) W') :
    ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
        complexFirstVariation a S (referenceFieldChain S V) W' (complexTwistedTop b X ζ V) A -
        complexReferenceSecondDeriv a S (referenceFieldChain S V) V (complexChartSub W W') A‖ ≤
      (C * (1 + 2 * a)) * (complexSupWeightedNorm S δ (referenceFieldChain S V) W +
          complexSupWeightedNorm S δ (referenceFieldChain S V) W' + ∑ l, ‖ζ l‖) *
        complexWeightedNorm S (referenceFieldChain S V) (complexChartSub W W') (classWeight F φ θ' p) *
        _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p)) := by
  set R := referenceFieldChain S V with hR
  set Nw := complexWeightedNorm S R (complexChartSub W W') (classWeight F φ θ' p) with hNw
  set Na := _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights (classWeight F φ θ' p)) with hNa
  have hNw0 : 0 ≤ Nw := add_nonneg (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
  have hNa0 : 0 ≤ Na := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _
  set ξ := ∑ l, ‖ζ l‖ with hξ
  rw [complexFirstVariation_twisted hB hW, complexFirstVariation_twisted hB hW']
  have hbase := hB.firstVariation_sub_le W W' hW hW' φ θ' p hθ' hφ A
  have hterm : ∀ e ∈ innerBonds S F.top, ‖(topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ e).trace -
      (topBondAverageVelocity R W' A e * adjugateChangeAt V b X ζ e).trace‖ ≤
      4 * (C * Nw * Na) * ‖twistAt b X ζ e‖ := by
    intro d hd
    rw [← Matrix.trace_sub, ← sub_mul]
    refine (norm_trace_le _).trans ?_
    have h1 := hB.velocity_sub_le d hd W W' hW hW' φ θ' p hθ' hφ A
    have h2 := norm_adjugateChangeAt_le V b X ζ d ((norm_twistAt_le_sum hX ζ d).trans hζ)
    have h3 := norm_mul_le (topBondAverageVelocity R W A d - topBondAverageVelocity R W' A d)
      (adjugateChangeAt V b X ζ d)
    have h4 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    nlinarith
  have hsum : ‖∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ e).trace -
      ∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W' A e * adjugateChangeAt V b X ζ e).trace‖ ≤
      4 * (C * Nw * Na) * ξ := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_norm_twistAt_le hX ζ _) (by positivity)
  set B₀ := complexFirstVariation a S R W (complexifyField V) A -
    complexFirstVariation a S R W' (complexifyField V) A -
    complexReferenceSecondDeriv a S R V (complexChartSub W W') A with hB₀
  set D := ∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ e).trace -
    ∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W' A e * adjugateChangeAt V b X ζ e).trace with hD
  have e : complexFirstVariation a S R W (complexifyField V) A -
        ((a : ℂ) / 2) * ∑ e ∈ innerBonds S F.top,
          (topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ e).trace -
      (complexFirstVariation a S R W' (complexifyField V) A -
        ((a : ℂ) / 2) * ∑ e ∈ innerBonds S F.top,
          (topBondAverageVelocity R W' A e * adjugateChangeAt V b X ζ e).trace) -
      complexReferenceSecondDeriv a S R V (complexChartSub W W') A = B₀ - ((a : ℂ) / 2) * D := by
    rw [hB₀, hD]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hn2 : ‖((a : ℂ) / 2)‖ = a / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    simp
  rw [norm_mul, hn2]
  have h5 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ a / 2)
  have hq : 0 ≤ C * a * (complexSupWeightedNorm S δ R W + complexSupWeightedNorm S δ R W') * (Nw * Na) := by
    positivity
  have hr : 0 ≤ C * ξ * (Nw * Na) := by positivity
  calc _ ≤ C * (complexSupWeightedNorm S δ R W + complexSupWeightedNorm S δ R W') * Nw * Na +
        a / 2 * (4 * (C * Nw * Na) * ξ) := add_le_add hbase h5
    _ ≤ _ := by nlinarith
set_option maxHeartbeats 1000000 in
theorem firstVariation_twist_sub_le (ha : 0 ≤ a) (hC : 0 ≤ C) (hB : ComplexChartBounds a θ δ c C S V)
    (hX : AreUnitVectors X) {W : ComplexChainChart F} {ζ ζ' : Fin k → ℂ} {l : Fin k}
    (hW : complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c) (hζ : ∑ l, ‖ζ l‖ ≤ 1 / 2)
    (hζ' : ∑ l, ‖ζ' l‖ ≤ 1 / 2) (hne : ∀ l', l' ≠ l → ζ l' = ζ' l') (A : ChainChart F) :
    ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) A -
        complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ' V) A‖ ≤
      (6 * a * C) * ‖ζ l - ζ' l‖ * localNorm S (referenceFieldChain S V) A (constOneWeights F) (b l).1 := by
  classical
  set R := referenceFieldChain S V with hR
  rw [complexFirstVariation_twisted hB hW, complexFirstVariation_twisted hB hW]
  have hv : ∀ d, d ≠ b l → twistAt b X ζ d = twistAt b X ζ' d := by
    intro d hd
    unfold twistAt
    refine Finset.sum_congr rfl fun l' _ => ?_
    by_cases h : b l' = d
    · have hl : l' ≠ l := fun e => hd (by rw [← h, e])
      simp only [h, if_true, hne l' hl]
    · simp only [h, if_false]
  have hy : ∀ d, d ≠ b l → adjugateChangeAt V b X ζ d = adjugateChangeAt V b X ζ' d := by
    intro d hd
    unfold adjugateChangeAt
    rw [hv d hd]
  have hvl : twistAt b X ζ (b l) - twistAt b X ζ' (b l) = (ζ l - ζ' l) • ofQuat (X l : ℍ[ℝ]) := by
    unfold twistAt
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l]
    · simp [sub_smul]
    · intro l' _ hl'
      by_cases h : b l' = b l
      · simp only [h, if_true, hne l' hl', sub_self]
      · simp only [h, if_false, sub_self]
    · simp
  have hnv : ‖twistAt b X ζ (b l) - twistAt b X ζ' (b l)‖ = ‖ζ l - ζ' l‖ := by
    rw [hvl, norm_smul, norm_ofQuat]
    have : ‖(X l : ℍ[ℝ])‖ = 1 := hX l
    rw [this, mul_one]
  have hY : ‖adjugateChangeAt V b X ζ (b l) - adjugateChangeAt V b X ζ' (b l)‖ ≤ 6 * ‖ζ l - ζ' l‖ := by
    rw [adjugateChangeAt_eq, adjugateChangeAt_eq, ← mul_sub, ← adjugate_map_sub, norm_ofUnit_mul, norm_adjugate,
      sub_sub_sub_cancel_right, ← hnv]
    exact norm_exp_sub_exp_le ((norm_twistAt_le_sum hX ζ _).trans hζ) ((norm_twistAt_le_sum hX ζ' _).trans hζ')
  set Su₁ := ∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ e).trace
    with hSu₁
  set Su₂ := ∑ e ∈ innerBonds S F.top, (topBondAverageVelocity R W A e * adjugateChangeAt V b X ζ' e).trace
    with hSu₂
  have e : complexFirstVariation a S R W (complexifyField V) A - ((a : ℂ) / 2) * Su₁ -
      (complexFirstVariation a S R W (complexifyField V) A - ((a : ℂ) / 2) * Su₂) =
      -(((a : ℂ) / 2) * (Su₁ - Su₂)) := by ring
  rw [e, norm_neg, norm_mul]
  have hn2 : ‖((a : ℂ) / 2)‖ = a / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    simp
  rw [hn2]
  have hnear0 : 0 ≤ localNorm S R A (constOneWeights F) (b l).1 := Real.sqrt_nonneg _
  by_cases hbl : b l ∈ innerBonds S F.top
  · have e1 : Su₁ - Su₂ = (topBondAverageVelocity R W A (b l) *
        (adjugateChangeAt V b X ζ (b l) - adjugateChangeAt V b X ζ' (b l))).trace := by
      rw [hSu₁, hSu₂, ← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem (b l) hbl]
      · rw [mul_sub, Matrix.trace_sub]
      · intro d _ hd
        rw [hy d hd, sub_self]
    rw [e1]
    have h1 := norm_trace_le (topBondAverageVelocity R W A (b l) *
      (adjugateChangeAt V b X ζ (b l) - adjugateChangeAt V b X ζ' (b l)))
    have h2 := norm_mul_le (topBondAverageVelocity R W A (b l))
      (adjugateChangeAt V b X ζ (b l) - adjugateChangeAt V b X ζ' (b l))
    have h3 := hB.norm_velocity_le (b l) hbl W hW A
    rw [enclosingCell_top] at h3
    have h4 := mul_le_mul h3 hY (norm_nonneg _) (by positivity)
    have h5 : ‖(topBondAverageVelocity R W A (b l) *
        (adjugateChangeAt V b X ζ (b l) - adjugateChangeAt V b X ζ' (b l))).trace‖ ≤
        2 * (C * localNorm S R A (constOneWeights F) (b l).1 * (6 * ‖ζ l - ζ' l‖)) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ a / 2)
    refine h6.trans (le_of_eq ?_)
    ring
  · have e1 : Su₁ = Su₂ := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hy d fun h => hbl (h ▸ hd)]
    rw [e1, sub_self, norm_zero, mul_zero]
    positivity
end Fields
section RealDirections
variable {F : BlockFrame} {k : ℕ}
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem parallelAverage_sub_smul {j : ℕ} (Y : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ]) (τ : ℝ)
    (e : F.Site (j + 1) × Fin 4) :
    parallelAverage Y (fun y d => f y d - τ • g y d) e = parallelAverage Y f e - τ • parallelAverage Y g e := by apply _root_.YangMills.Construction.BlockAverages.FirstVariation.parallelAverage_sub_smul <;> assumption
theorem linearPart_chartShift (R : F.FieldChain) (U A : ChainChart F) (t : ℝ) :
    ∀ (j : ℕ) (x : F.Site j) (i : Fin 4),
      linearPart R (chartMove U A t) j x i = linearPart R U j x i + t • linearPart R A j x i
  | 0, x, i => rfl
  | j + 1, x, i => by
    have e1 : linearPart R (chartMove U A t) j =
        fun y d => linearPart R U j y d - (-t) • linearPart R A j y d := by
      funext y d
      rw [linearPart_chartShift R U A t j y d]
      simp
    show parallelAverage (R j) (linearPart R (chartMove U A t) j) (x, i) +
        (if j + 1 < F.top then (((chartMove U A t).coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) else 0) =
      (parallelAverage (R j) (linearPart R U j) (x, i) +
        (if j + 1 < F.top then ((U.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) else 0)) +
      t • (parallelAverage (R j) (linearPart R A j) (x, i) +
        (if j + 1 < F.top then ((A.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) else 0))
    rw [e1, parallelAverage_sub_smul]
    split_ifs with hc
    · have e2 : (((chartMove U A t).coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) =
          ((U.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) + t • ((A.coarse j x i : imaginaryQuaternions) : ℍ[ℝ]) :=
        rfl
      rw [e2, smul_add, neg_smul]
      abel
    · simp
theorem linearPart_zeroChart (R : F.FieldChain) (j : ℕ) (x : F.Site j) (i : Fin 4) :
    linearPart R (zeroChart F) j x i = 0 := by
  have h := linearPart_chartShift R (zeroChart F) (zeroChart F) (-1) j x i
  have e : chartMove (zeroChart F) (zeroChart F) (-1) = zeroChart F := by
    apply chainChart_ext
    · funext p d
      simp [chartMove, zeroChart]
    · funext l p d
      simp [chartMove, zeroChart]
  rw [e] at h
  have h2 : (-1 : ℝ) • linearPart R (zeroChart F) j x i = 0 := by
    have := congrArg (fun q => q - linearPart R (zeroChart F) j x i) h
    simpa using this.symm
  simpa using h2
theorem topBondGaugedAverage_realChart (R : F.FieldChain) (U : ChainChart F) (e : F.Site F.top × Fin 4) :
    topBondGaugedAverage R (realChart U) e = ofQuat (gaugedBondAverage R U F.depth e) := by
  unfold topBondGaugedAverage gaugedBondAverage
  rw [complexChartField_realChart]
  have hg : complexBalancingGauge (complexifyField (chartField R U F.depth)) (R F.depth) =
      fun y => ofUnit (balancingGauge (chartField R U F.depth) (R F.depth) y) := by
    funext y
    exact complexBalancingGauge_complexify _ _ y
  rw [hg]
  exact complexGaugedContourAverage_complexify _ _ e
def ofQuatCLM : ℍ[ℝ] →L[ℝ] ComplexQuat :=
  LinearMap.toContinuousLinearMap
    { toFun := ofQuat
      map_add' := ofQuat_add
      map_smul' := fun r q => by
        rw [ofQuat_smul]
        rfl }
def toQuat (M : ComplexQuat) : ℍ[ℝ] := ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩
def toQuatCLM : ComplexQuat →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := toQuat
      map_add' := fun M N => by
        ext <;> simp [toQuat] <;> rfl
      map_smul' := fun r M => by
        ext <;> simp [toQuat] <;> rfl }
theorem toQuatCLM_ofQuat (q : ℍ[ℝ]) : toQuatCLM (ofQuat q) = q := by
  show toQuat (ofQuat q) = q
  ext <;> simp [toQuat, ofQuat]
variable {a θ δ c C : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem exists_real_velocity (hB : ComplexChartBounds a θ δ c C S V)
    (h0 : complexSupWeightedNorm S δ (referenceFieldChain S V) (realChart (zeroChart F)) ≤ c) (A : ChainChart F)
    {d : F.Site F.top × Fin 4} (hd : d ∈ innerBonds S F.top) :
    ∃ q : ℍ[ℝ], HasDerivAt
        (fun τ : ℝ => gaugedBondAverage (referenceFieldChain S V) (chartMove (zeroChart F) A τ) F.depth d) q 0 ∧
      topBondAverageVelocity (referenceFieldChain S V) (realChart (zeroChart F)) A d = ofQuat q := by
  set R := referenceFieldChain S V with hR
  have hf := (differentiableAt_average_line hB h0 A hd).hasDerivAt
  have hf' : HasDerivAt (fun τ : ℂ => topBondGaugedAverage R (complexChartMove (realChart (zeroChart F)) A τ) d)
      (topBondAverageVelocity R (realChart (zeroChart F)) A d) (((0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact hf
  have h1 := hasDerivAt_ofReal_comp hf'
  have e : (fun u : ℝ => topBondGaugedAverage R (complexChartMove (realChart (zeroChart F)) A (u : ℂ)) d) =
      fun τ : ℝ => ofQuat (gaugedBondAverage R (chartMove (zeroChart F) A τ) F.depth d) := by
    funext τ
    rw [complexChartMove_realChart, topBondGaugedAverage_realChart]
  rw [e] at h1
  have h2 : HasDerivAt (fun τ : ℝ => gaugedBondAverage R (chartMove (zeroChart F) A τ) F.depth d)
      (toQuatCLM (topBondAverageVelocity R (realChart (zeroChart F)) A d)) 0 := by
    have h3 := toQuatCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def, toQuatCLM_ofQuat] using h3
  refine ⟨_, h2, ?_⟩
  have h4 := ofQuatCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  exact h1.unique h4
end RealDirections
section LinearPartBound
variable {F : BlockFrame} {k : ℕ}
variable {a θ δ c C : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} {b : Fin k → F.Site F.top × Fin 4}
  {X : Fin k → imaginaryQuaternions}
theorem twistAt_ofReal (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℝ)
    (d : F.Site F.top × Fin 4) :
    twistAt b X (fun l => (ζ l : ℂ)) d = ofQuat ((bondSpread b X ζ d.1 d.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
  have h1 : ((bondSpread b X ζ d.1 d.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      ∑ l, if b l = d then ζ l • (X l : ℍ[ℝ]) else 0 := by
    simp only [bondSpread]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [h1, BlockAverages.ofQuat_sum]
  unfold twistAt
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [ofQuat_smul]
  · rw [ofQuat_zero]
theorem adjugateChangeAt_ofReal (V : F.GaugeField F.top) (b : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℝ) (d : F.Site F.top × Fin 4) :
    adjugateChangeAt V b X (fun l => (ζ l : ℂ)) d = ofQuat ((((V d.1 d.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      ((((expUnit (bondSpread b X ζ d.1 d.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)) := by
  have h1 : NormedSpace.exp (twistAt b X (fun l => (ζ l : ℂ)) d) * ofUnit (V d.1 d.2) =
      ofUnit (expUnit (bondSpread b X ζ d.1 d.2) * V d.1 d.2) := by
    have h2 := congrFun (congrFun (complexTwistedTop_ofReal b X ζ V) d.1) d.2
    exact h2
  unfold adjugateChangeAt
  rw [h1, ← ofUnit_inv, ← ofUnit_inv, mul_inv_rev]
  simp only [ofUnit]
  rw [mul_sub, mul_one, ofQuat_sub_eq]
  rfl
set_option maxHeartbeats 1000000 in
theorem norm_bond_linearization_le {a' : ℝ} (ha : 0 ≤ a') {q ν : ℍ[ℝ]} {g w : UnitQuaternion}
    {v : imaginaryQuaternions} (hv : ‖(v : ℍ[ℝ])‖ ≤ 1) (hg : g = expUnit v) :
    ‖-((a' : ℂ) / 2) * (ofQuat q * ofQuat (((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1))).trace -
        ((a' * (ν * (v : ℍ[ℝ])).re : ℝ) : ℂ)‖ ≤
      a' * (‖q * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ν‖ * ‖(v : ℍ[ℝ])‖ + ‖ν‖ * ‖(v : ℍ[ℝ])‖ ^ 2) := by
  set x : ℍ[ℝ] := ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 with hx
  set qd : ℍ[ℝ] := q * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hqd
  have ht : (ofQuat q * ofQuat (((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) * x)).trace = ((2 * (qd * x).re : ℝ) : ℂ) := by
    rw [← ofQuat_mul, trace_ofQuat, ← mul_assoc]
  rw [ht]
  have e : -((a' : ℂ) / 2) * ((2 * (qd * x).re : ℝ) : ℂ) - ((a' * (ν * (v : ℍ[ℝ])).re : ℝ) : ℂ) =
      ((-(a' * ((qd - ν) * x).re + a' * (ν * (x + (v : ℍ[ℝ]))).re) : ℝ) : ℂ) := by
    have e1 : (qd * x).re = ((qd - ν) * x).re + (ν * x).re := by
      rw [sub_mul]
      simp
    have e2 : (ν * (x + (v : ℍ[ℝ]))).re = (ν * x).re + (ν * (v : ℍ[ℝ])).re := by
      rw [mul_add]
      simp
    rw [e1, e2]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hgv : ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(v : ℍ[ℝ])‖ := by
    rw [hg]
    exact norm_coe_expUnit_sub_one_le v
  have hxn : ‖x‖ ≤ ‖(v : ℍ[ℝ])‖ := by
    rw [hx, norm_coe_inv_sub_one]
    exact hgv
  have hxv : ‖x + (v : ℍ[ℝ])‖ ≤ ‖(v : ℍ[ℝ])‖ ^ 2 := by
    have e3 : x + (v : ℍ[ℝ]) = star (((g : UnitQuaternion) : ℍ[ℝ]) - 1 - (v : ℍ[ℝ])) := by
      have e4 : (((g⁻¹ : UnitQuaternion)) : ℍ[ℝ]) = star ((g : UnitQuaternion) : ℍ[ℝ]) := rfl
      rw [hx, e4, star_sub, star_sub, star_one, star_coe_imaginary]
      abel
    rw [e3, norm_star, hg]
    exact norm_expUnit_sub_one_sub_le hv
  have h1 : |((qd - ν) * x).re| ≤ ‖qd - ν‖ * ‖(v : ℍ[ℝ])‖ := by
    refine (abs_re_le_norm _).trans ((norm_mul_le _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
  have h2 : |(ν * (x + (v : ℍ[ℝ]))).re| ≤ ‖ν‖ * ‖(v : ℍ[ℝ])‖ ^ 2 := by
    refine (abs_re_le_norm _).trans ((norm_mul_le _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left hxv (norm_nonneg _)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg ha]
  calc _ ≤ a' * (‖qd - ν‖ * ‖(v : ℍ[ℝ])‖) + a' * (‖ν‖ * ‖(v : ℍ[ℝ])‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 ha)
    _ = _ := by ring
theorem supWeightedNorm_zeroChart {S : Finset F.Cell} (hL : 0 < F.blockSide) (δ : ℝ) (R : F.FieldChain) :
    supWeightedNorm S δ R (zeroChart F) = 0 := by
  have h := supWeightedNorm_smul S hL δ R (zeroChart F) 0
  have e : chartMove (zeroChart F) (zeroChart F) 0 = zeroChart F := by
    apply chainChart_ext
    · funext p i
      simp [chartMove, zeroChart]
    · funext j p i
      simp [chartMove, zeroChart]
  rw [e] at h
  simpa using h
theorem complexTwistedTop_zero (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) : complexTwistedTop b X 0 V = complexifyField V := by
  funext y i
  simp [complexTwistedTop, complexifyField]
set_option maxHeartbeats 2000000 in
theorem firstVariation_real_twist_linearization (ha : 0 ≤ a) (hL : 0 < F.blockSide) (hc0 : 0 ≤ c)
    (hB : ComplexChartBounds a θ δ c C S V) (hX : AreUnitVectors X)
    {K Cv s : ℝ} (hK : 0 ≤ K) (hCv : 0 ≤ Cv) (hs : 0 < s) (hθ0 : 0 ≤ θ) (hθ8 : θ ≤ 1 / 8)
    (hV : ∀ (A : ChainChart F) (θ' : ℝ) (p : F.Site 0) (y0 : F.Cell), 0 ≤ θ' → θ' ≤ 1 / 8 →
      ∀ d ∈ innerBonds S F.top,
        ‖linearPart (referenceFieldChain S V) A F.top d.1 d.2‖ ≤
          K * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F δ θ' p y0)) ∧
        ∀ q : ℍ[ℝ], HasDerivAt
            (fun τ : ℝ => gaugedBondAverage (referenceFieldChain S V) (chartMove (zeroChart F) A τ) F.depth d) q 0 →
          ‖q * (((V d.1 d.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - linearPart (referenceFieldChain S V) A F.top d.1 d.2‖ ≤
            Cv * s * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F δ θ' p y0)))
    (ζ : Fin k → ℝ) (hζ : ∑ l, |ζ l| ≤ 1) :
    ∃ l1 : ChainChart F → ℝ,
      (∀ A A', l1 (chartMove A A' 1) = l1 A + l1 A') ∧
      (∀ (t : ℝ) A, l1 (chartMove (zeroChart F) A t) = t * l1 A) ∧
      ∀ (A : ChainChart F) (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
        |l1 A| ≤ (a * K) * (∑ l, |ζ l|) * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
          (invertedWeights (decayWeights F δ θ' p y0)) ∧
        ‖complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
              (complexTwistedTop b X (fun l => (ζ l : ℂ)) V) A -
            complexFirstVariation a S (referenceFieldChain S V) (realChart (zeroChart F))
              (complexTwistedTop b X 0 V) A -
            (l1 A : ℂ)‖ ≤
          (a * (Cv + K)) * (s + ∑ l, |ζ l|) ^ 2 * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A
            (invertedWeights (decayWeights F δ θ' p y0)) := by
  set R := referenceFieldChain S V with hR
  set ξ := ∑ l, |ζ l| with hξ
  have hξ0 : 0 ≤ ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set v : F.Site F.top × Fin 4 → imaginaryQuaternions := fun d => bondSpread b X ζ d.1 d.2 with hv
  have hvn : ∀ d, ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖twistAt b X (fun l => (ζ l : ℂ)) d‖ := fun d => by
    rw [twistAt_ofReal, norm_ofQuat]
  have hnorm : ∑ l, ‖((ζ l : ℝ) : ℂ)‖ = ξ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, hξ]
  have hv1 : ∀ d, ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ξ := fun d => by
    rw [hvn, ← hnorm]
    exact norm_twistAt_le_sum hX _ d
  have hvsum : ∑ d ∈ innerBonds S F.top, ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ξ := by
    simp only [hvn]
    rw [← hnorm]
    exact sum_norm_twistAt_le hX _ _
  set l1 : ChainChart F → ℝ := fun A =>
    a * ∑ d ∈ innerBonds S F.top, (linearPart R A F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re
    with hl1
  have h00 : complexSupWeightedNorm S δ R (realChart (zeroChart F)) ≤ c := by
    have e : complexSupWeightedNorm S δ R (realChart (zeroChart F)) =
        supWeightedNorm S δ R (zeroChart F) + supWeightedNorm S δ R (zeroChart F) := rfl
    rw [e, supWeightedNorm_zeroChart hL]
    simpa using hc0
  refine ⟨l1, ?_, ?_, ?_⟩
  · intro A A'
    simp only [hl1]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [linearPart_chartShift, add_mul]
    simp
  · intro t A
    have e : ∀ d : F.Site F.top × Fin 4,
        (linearPart R (chartMove (zeroChart F) A t) F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re =
        t * (linearPart R A F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re := fun d => by
      rw [linearPart_chartShift, linearPart_zeroChart, zero_add, smul_mul_assoc]
      simp
    simp only [hl1, e]
    rw [← Finset.mul_sum]
    ring
  intro A p y0 θ' hθ'
  have h0 : 0 ≤ θ' := by
    rcases hθ' with h | h
    · rw [h]
      exact hθ0
    · exact h.ge
  have h8 : θ' ≤ 1 / 8 := by
    rcases hθ' with h | h
    · rw [h]
      exact hθ8
    · rw [h]
      norm_num
  set N := _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (invertedWeights (decayWeights F δ θ' p y0)) with hN
  have hN0 : 0 ≤ N := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _
  have hb := hV A θ' p y0 h0 h8
  refine ⟨?_, ?_⟩
  · have h1 : ∀ d ∈ innerBonds S F.top,
        |(linearPart R A F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re| ≤
        (K * N) * ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ := fun d hd => by
      refine (abs_re_le_norm _).trans ((norm_mul_le _ _).trans ?_)
      exact mul_le_mul_of_nonneg_right (hb d hd).1 (norm_nonneg _)
    simp only [hl1]
    rw [abs_mul, abs_of_nonneg ha]
    have h2 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h1)
    rw [← Finset.mul_sum] at h2
    have h3 := h2.trans (mul_le_mul_of_nonneg_left hvsum (by positivity))
    have h4 := mul_le_mul_of_nonneg_left h3 ha
    refine h4.trans (le_of_eq ?_)
    ring
  · rw [complexTwistedTop_zero, complexFirstVariation_twisted hB h00 b X]
    set W₀ := realChart (zeroChart F) with hW₀
    have hterm : ∀ d ∈ innerBonds S F.top,
        ‖-((a : ℂ) / 2) * (topBondAverageVelocity R W₀ A d * adjugateChangeAt V b X (fun l => (ζ l : ℂ)) d).trace -
          ((a * (linearPart R A F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re : ℝ) : ℂ)‖ ≤
        a * ((Cv * s * N) * ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ +
          (K * N) * (ξ * ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖)) := by
      intro d hd
      obtain ⟨q, hq, hqe⟩ := exists_real_velocity hB h00 A hd
      rw [hqe, adjugateChangeAt_ofReal]
      have hvle := (hv1 d).trans hζ
      have h1 := norm_bond_linearization_le (q := q) (ν := linearPart R A F.top d.1 d.2) (g := expUnit (v d))
        (w := V d.1 d.2) (v := v d) ha hvle rfl
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ ha)
      have h3 := (hb d hd).2 q hq
      have h4 := (hb d hd).1
      have n0 := norm_nonneg ((v d : imaginaryQuaternions) : ℍ[ℝ])
      refine add_le_add (mul_le_mul_of_nonneg_right h3 n0) ?_
      have h5 : ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 ≤ ξ * ‖((v d : imaginaryQuaternions) : ℍ[ℝ])‖ := by
        have := mul_le_mul_of_nonneg_right (hv1 d) n0
        nlinarith
      exact mul_le_mul h4 h5 (by positivity) (by positivity)
    have e : complexFirstVariation a S R W₀ (complexifyField V) A -
          ((a : ℂ) / 2) * ∑ d ∈ innerBonds S F.top,
            (topBondAverageVelocity R W₀ A d * adjugateChangeAt V b X (fun l => (ζ l : ℂ)) d).trace -
          complexFirstVariation a S R W₀ (complexifyField V) A - (l1 A : ℂ) =
        ∑ d ∈ innerBonds S F.top, (-((a : ℂ) / 2) *
          (topBondAverageVelocity R W₀ A d * adjugateChangeAt V b X (fun l => (ζ l : ℂ)) d).trace -
          ((a * (linearPart R A F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re : ℝ) : ℂ)) := by
      have hl : ((l1 A : ℝ) : ℂ) = ∑ d ∈ innerBonds S F.top,
          ((a * (linearPart R A F.top d.1 d.2 * ((v d : imaginaryQuaternions) : ℍ[ℝ])).re : ℝ) : ℂ) := by
        simp only [hl1]
        rw [Finset.mul_sum]
        push_cast
        rfl
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hl]
      ring
    rw [e]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs1 : 0 ≤ Cv * s * N := by positivity
    have hs2 : 0 ≤ K * N := by positivity
    have t1 := mul_le_mul_of_nonneg_left hvsum hs1
    have t2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvsum hξ0) hs2
    have t3 := mul_le_mul_of_nonneg_left (add_le_add t1 t2) ha
    refine t3.trans ?_
    have e9 : a * (Cv * s * N * ξ + K * N * (ξ * ξ)) = a * (Cv * N * (s * ξ) + K * N * (ξ * ξ)) := by ring
    rw [e9]
    have u1 : s * ξ ≤ (s + ξ) ^ 2 := by nlinarith
    have u2 : ξ * ξ ≤ (s + ξ) ^ 2 := by nlinarith
    have hCN : 0 ≤ Cv * N := by positivity
    have v1 := mul_le_mul_of_nonneg_left u1 hCN
    have v2 := mul_le_mul_of_nonneg_left u2 hs2
    have v3 := mul_le_mul_of_nonneg_left (add_le_add v1 v2) ha
    refine v3.trans (le_of_eq ?_)
    ring
end LinearPartBound
end RotatedTop
open RotatedTop in
set_option maxHeartbeats 2000000 in
theorem BlockAverages.rotatedTopTaylorBounds (hT : complexChartBoundsStatement)
    (hM : topAverageInDecayWeightStatement) : rotatedTopTaylorBoundsStatement := by
  intro a θ δ ha hθ0 hθ8 hδ hδ8
  obtain ⟨K, hK, LM, hLM⟩ := hM δ hδ hδ8
  obtain ⟨LT, hLT⟩ := hT
  refine ⟨a * K, by positivity, max LM LT, fun L hodd hL => ?_⟩
  obtain ⟨cM, Cv, hcM, hCv, hMb⟩ := hLM L hodd ((le_max_left _ _).trans hL)
  obtain ⟨cT, CT, hcT, hCT, hTb⟩ := hLT L a θ δ hodd ((le_max_right _ _).trans hL) ha hθ0 hθ8 hδ hδ8
  set c := min (min cM cT) (1 / 2) with hc
  have hc0 : 0 < c := lt_min (lt_min hcM hcT) (by norm_num)
  have c1 : c ≤ cM := (min_le_left _ _).trans (min_le_left _ _)
  have c2 : c ≤ cT := (min_le_left _ _).trans (min_le_right _ _)
  have c3 : c ≤ 1 / 2 := min_le_right _ _
  set Cf := CT * (1 + 2 * a) + 6 * a * CT + a * (Cv + K) + 1 with hCf
  have hCf0 : 0 < Cf := by positivity
  refine ⟨c, Cf, hc0, hCf0, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold k b X hX
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hB := hTb F m S hFL hamb hm hreg s V hs (hsc.trans c2) hcold
  have hVb := hMb F m S hFL hamb hm hreg s V hs (hsc.trans c1) hcold
  set R := referenceFieldChain S V with hR
  have nS : ∀ U : ChainChart F, 0 ≤ supWeightedNorm S δ R U := fun U => supWeightedNorm_nonneg _ _ _ _
  have nC : ∀ W : ComplexChainChart F, 0 ≤ complexSupWeightedNorm S δ R W := fun W => add_nonneg (nS _) (nS _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m' A t ζ hW hζ
    have hWc := hW.trans c2
    have e : (fun q : (Fin m' → ℂ) × (Fin k → ℂ) =>
        complexTotalOverTop a S R (complexSpan A q.1) (complexTwistedTop b X q.2 V)) =
        fun q => complexTotalOverTop a S R (complexSpan A q.1) (complexifyField V) -
          ((a : ℂ) / 2) * ∑ d ∈ innerBonds S F.top,
            (topBondGaugedAverage R (complexSpan A q.1) d * adjugateChangeAt V b X q.2 d).trace := by
      funext q
      exact complexTotalOverTop_twisted a S R _ V b X q.2
    rw [e]
    refine AnalyticAt.sub ?_ (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun d hd => ?_))
    · exact AnalyticAt.comp (g := fun q : Fin m' → ℂ => complexTotalOverTop a S R (complexSpan A q) (complexifyField V))
        (f := fun q : (Fin m' → ℂ) × (Fin k → ℂ) => q.1) (hB.analyticAt_total m' A t hWc) analyticAt_fst
    · refine analyticAt_trace (AnalyticAt.mul ?_ ?_)
      · exact AnalyticAt.comp (g := fun q : Fin m' → ℂ => topBondGaugedAverage R (complexSpan A q) d)
          (f := fun q : (Fin m' → ℂ) × (Fin k → ℂ) => q.1) (hB.analyticAt_average d hd m' A t hWc) analyticAt_fst
      · exact AnalyticAt.comp (g := fun ζ' => adjugateChangeAt V b X ζ' d)
          (f := fun q : (Fin m' → ℂ) × (Fin k → ℂ) => q.2) (analyticAt_adjugateChangeAt V b X d ζ) analyticAt_snd
  · intro W W' ζ hW hW' hζ φ θ' p hθ' hφ A
    have h1 := firstVariation_twisted_sub_le (b := b) ha.le hCT.le hB hX (hW.trans c2) (hW'.trans c2)
      (hζ.trans (by linarith)) p hθ' hφ A (nC W) (nC W')
    refine h1.trans ?_
    have hX0 : 0 ≤ complexWeightedNorm S R (complexChartSub W W') (classWeight F φ θ' p) :=
      add_nonneg (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
    have hA0 := _root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg S R A (invertedWeights (classWeight F φ θ' p))
    have hζ0 : 0 ≤ ∑ l, ‖ζ l‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hs0 : 0 ≤ complexSupWeightedNorm S δ R W + complexSupWeightedNorm S δ R W' + ∑ l, ‖ζ l‖ :=
      add_nonneg (add_nonneg (nC W) (nC W')) hζ0
    have hle : CT * (1 + 2 * a) ≤ Cf := by
      have : 0 ≤ a * CT := by positivity
      have : 0 ≤ a * (Cv + K) := by positivity
      rw [hCf]
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hs0) hX0) hA0
  · intro W ζ ζ' l hW hζ hζ' hne A
    have h1 := firstVariation_twist_sub_le (b := b) ha.le hCT.le hB hX (hW.trans c2) (hζ.trans c3) (hζ'.trans c3)
      hne A
    refine h1.trans ?_
    have hle : 6 * a * CT ≤ Cf := by
      have : 0 ≤ CT * (1 + 2 * a) := by positivity
      have : 0 ≤ a * (Cv + K) := by positivity
      rw [hCf]
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) (Real.sqrt_nonneg _)
  · intro ζ hζ
    obtain ⟨l1, e1, e2, e3⟩ := firstVariation_real_twist_linearization ha.le hoddF.pos hcT.le hB hX hK.le hCv.le hs
      hθ0 hθ8 (fun A θ' p y0 h0 h8 d hd => hVb A θ' p y0 h0 h8 d hd) ζ (hζ.trans (by linarith))
    refine ⟨l1, e1, e2, fun A p y0 θ' hθ' => ?_⟩
    obtain ⟨f1, f2⟩ := e3 A p y0 θ' hθ'
    refine ⟨f1, f2.trans ?_⟩
    have hle : a * (Cv + K) ≤ Cf := by
      have : 0 ≤ CT * (1 + 2 * a) := by positivity
      have : 0 ≤ 6 * a * CT := by positivity
      rw [hCf]
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (by positivity)) (_root_.YangMills.Construction.CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
end YangMills.Construction
end
