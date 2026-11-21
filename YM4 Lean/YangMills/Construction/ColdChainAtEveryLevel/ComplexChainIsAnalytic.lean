import YangMills.Construction.ColdChainAtEveryLevel.ComplexDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexAnalyticity
open BlockAverages ComplexContours ComplexRemainders ComplexChainStep ComplexLevels ComplexDifferences
variable {F : BlockFrame} {j : ℕ}
section Operations
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  {f : P → ComplexifiedQuaternions.ComplexQuat} {z : P}
theorem analyticAt_const_smul_complexQuat (c : ℂ) (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (fun w => c • f w) z := by
  have hcomp := ((c • ContinuousLinearMap.id ℂ ComplexifiedQuaternions.ComplexQuat).analyticAt (f z)).comp hf
  simpa [Function.comp_def] using hcomp
theorem analyticAt_trace (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun w => (f w).trace) z :=
  ((LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).analyticAt _).comp hf
theorem analyticAt_adjugate (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (fun w => Matrix.adjugate (f w)) z := by
  have heq : (fun w => Matrix.adjugate (f w)) =
      fun w => (f w).trace • (1 : ComplexifiedQuaternions.ComplexQuat) - f w := by
    funext w
    exact ComplexifiedQuaternions.adjugate_eq_trace_smul_sub _
  rw [heq]
  exact ((analyticAt_trace hf).smul analyticAt_const).sub hf
theorem analyticAt_det (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun w => (f w).det) z := by
  have heq : (fun w => (f w).det) = fun w => (f w * Matrix.adjugate (f w)).trace / 2 := by
    funext w
    exact det_eq_trace_mul_adjugate_div_two _
  rw [heq]
  exact (analyticAt_trace (hf.mul (analyticAt_adjugate hf))).div_const
theorem analyticAt_invSqrt {g : P → ℂ} (hg : AnalyticAt ℂ g z) (hs : g z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w => ComplexifiedQuaternions.invSqrt (g w)) z := by
  unfold ComplexifiedQuaternions.invSqrt
  exact (analyticAt_const.mul (hg.clog hs)).cexp
theorem analyticAt_unitPart (hf : AnalyticAt ℂ f z) (hne : f z ≠ 0)
    (hs : (f z).det ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w => ComplexifiedQuaternions.unitPart (f w)) z := by
  have hev : (fun w => ComplexifiedQuaternions.unitPart (f w)) =ᶠ[nhds z]
      fun w => ComplexifiedQuaternions.invSqrt (f w).det • f w := by
    have hnear : ∀ᶠ w in nhds z, f w ≠ 0 := hf.continuousAt.eventually_ne hne
    filter_upwards [hnear] with w hw
    rw [ComplexifiedQuaternions.unitPart, if_neg hw]
  refine AnalyticAt.congr ?_ hev.symm
  exact (analyticAt_invSqrt (analyticAt_det hf) hs).smul hf
theorem analyticAt_unitExp (hf : AnalyticAt ℂ f z) (hsmall : ‖f z‖ ≤ 1 / 16) :
    AnalyticAt ℂ (fun w => unitExp (f w)) z := by
  have hnn := norm_nonneg (f z)
  have hrem := norm_exp_sub_one_sub_le (x := f z) (by linarith)
  have hclose : ‖NormedSpace.exp (f z) - 1‖ ≤ 1 / 8 := by
    have hsplit : NormedSpace.exp (f z) - 1 = (NormedSpace.exp (f z) - 1 - f z) + f z := by abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  obtain ⟨hne, hslit⟩ := one_add_ne_zero_and_det_mem_slitPlane hclose
  rw [add_sub_cancel] at hne hslit
  have hexp : AnalyticAt ℂ (fun w => NormedSpace.exp (f w)) z := by
    have hball := NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ) (f z) (by
      rw [NormedSpace.expSeries_radius_eq_top ℂ ComplexifiedQuaternions.ComplexQuat]
      exact edist_lt_top _ _)
    exact hball.comp hf
  exact analyticAt_unitPart hexp hne hslit
theorem analyticAt_complexPathHolonomy {X : P → F.ComplexField j} {x : F.Site j} {l : List PathStep}
    (hbonds : PathBondsSatisfy (fun b i => AnalyticAt ℂ (fun w => X w b i) z) x l) :
    AnalyticAt ℂ (fun w => complexPathHolonomy (X w) x l) z := by
  induction l generalizing x with
  | nil =>
    simp only [complexPathHolonomy]
    exact analyticAt_const
  | cons st rest ih =>
    simp only [complexPathHolonomy]
    refine AnalyticAt.mul ?_ (ih hbonds.2)
    rcases hs : st.2 with _ | _
    · have hfirst := hbonds.1
      simp only [crossedBond, hs, Bool.false_eq_true, if_false] at hfirst
      simp only [complexLinkValue, hs, Bool.false_eq_true, if_false]
      exact analyticAt_adjugate hfirst
    · have hfirst := hbonds.1
      simp only [crossedBond, hs, if_true] at hfirst
      simp only [complexLinkValue, hs, if_true]
      exact hfirst
theorem analyticAt_complexBalancingGauge (hodd : Odd F.blockSide) {X : P → F.ComplexField j}
    (R : F.GaugeField j) {y : F.Site (j + 1)} {t : ℝ}
    (ht : 0 ≤ t) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 8)
    (hlegs : ∀ h ∈ centredCube F.blockSide, ∀ π,
      AnalyticAt ℂ (fun w => complexPathHolonomy (X w) (refineSite y) (axisPath h π)) z)
    (hnear : ∀ h ∈ centredCube F.blockSide, ∀ π, PathNearReal (X z) R t (refineSite y) (axisPath h π)) :
    AnalyticAt ℂ (fun w => complexBalancingGauge (X w) R y) z := by
  have hbound := norm_complexRelativePathAverage_sub_one_le hodd ht (by linarith) hnear
  have hclose : ‖complexRelativePathAverage (X z) R y - 1‖ ≤ 1 / 8 := hbound.trans hτ
  obtain ⟨hne, hslit⟩ := one_add_ne_zero_and_det_mem_slitPlane hclose
  rw [add_sub_cancel] at hne hslit
  simp only [complexBalancingGauge]
  refine analyticAt_adjugate (analyticAt_unitPart ?_ hne hslit)
  simp only [complexRelativePathAverage]
  have hsum : AnalyticAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      complexPathHolonomy (X w) (refineSite y) (axisPath h π) *
        ofUnit (pathHolonomy R (refineSite y) (axisPath h π))⁻¹) z := by
    refine Finset.analyticAt_fun_sum _ fun h hh => Finset.analyticAt_fun_sum _ fun π _ => ?_
    exact (hlegs h hh π).mul analyticAt_const
  exact analyticAt_const_smul_complexQuat _ hsum
theorem analyticAt_unitPart_complexGaugedContourAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.ComplexField j} (R : F.GaugeField j)
    {c : F.Site (j + 1) × Fin 4} {t σ : ℝ} (ht : 0 ≤ t) (hσ : σ ≤ 1 / 64)
    (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024) (hgood : ContoursNearReal (X z) R t σ c)
    (hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => X w b i) z)) :
    AnalyticAt ℂ (fun w => ComplexifiedQuaternions.unitPart
      (complexGaugedContourAverage (X w) (complexBalancingGauge (X w) R) c)) z := by
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π,
      AnalyticAt ℂ (fun w => complexPathHolonomy (X w) (refineSite c.1) (axisPath h π)) z :=
    fun h hh π => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).1) hh π)
  have hfar : ∀ h ∈ centredCube F.blockSide, ∀ π, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)) z :=
    fun h hh π => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).2) hh π)
  have hline : ∀ h ∈ centredCube F.blockSide, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite c.1 + siteOfCoords j h)
        (List.replicate F.blockSide (c.2, true))) z :=
    fun h hh => analyticAt_complexPathHolonomy
      (pathBondsSatisfy_replicate _ _ _ fun r hr => hX.2 h hh r hr)
  have hmean : AnalyticAt ℂ (fun w => complexContourAverage (X w) c) z := by
    simp only [complexContourAverage]
    have hsum : AnalyticAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        complexPathHolonomy (X w) (refineSite c.1) (bondContour F.blockSide h π c.2)) z := by
      refine Finset.analyticAt_fun_sum _ fun h hh => Finset.analyticAt_fun_sum _ fun π _ => ?_
      simp only [complexPathHolonomy_bondContour hj]
      exact ((hleg h hh π).mul (hline h hh)).mul (analyticAt_adjugate (hfar h hh π))
    exact analyticAt_const_smul_complexQuat _ hsum
  have hτ8 : 4 * (F.blockSide : ℝ) * t ≤ 1 / 8 := by linarith
  have hgauge := analyticAt_complexBalancingGauge hodd R ht hτ8 hleg hgood.nearLegs
  have hgauge' := analyticAt_complexBalancingGauge hodd R ht hτ8 hfar hgood.nearFarLegs
  have hM : AnalyticAt ℂ (fun w => complexGaugedContourAverage (X w) (complexBalancingGauge (X w) R) c) z := by
    simp only [complexGaugedContourAverage]
    exact (hgauge.mul hmean).mul (analyticAt_adjugate hgauge')
  obtain ⟨hdet, -, -⟩ := unitPart_and_sqrt_near hodd hj ht hσ hτ hgood
  have hne : complexGaugedContourAverage (X z) (complexBalancingGauge (X z) R) c ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  exact analyticAt_unitPart hM hne (Or.inl hdet)
end Operations
section Chain
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {z : P}
theorem analyticAt_complexChartField (hodd : Odd F.blockSide) (R : F.FieldChain) {D : Finset F.Cell}
    {W : P → ComplexChainChart F}
    {t σ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hσ : σ ≤ 1 / 64) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024)
    (hfine : ∀ b ∈ innerBonds D 0, AnalyticAt ℂ
      (fun w => complexifiedImaginary ((W w).re.fine b.1 b.2) ((W w).im.fine b.1 b.2)) z)
    (hfine1 : ∀ b ∈ innerBonds D 0,
      ‖complexifiedImaginary ((W z).re.fine b.1 b.2) ((W z).im.fine b.1 b.2)‖ ≤ 1 / 16)
    (hcoarse : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds D (j + 1), AnalyticAt ℂ
      (fun w => complexifiedImaginary ((W w).re.coarse j b.1 b.2) ((W w).im.coarse j b.1 b.2)) z)
    (hcoarse1 : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds D (j + 1),
      ‖complexifiedImaginary ((W z).re.coarse j b.1 b.2) ((W z).im.coarse j b.1 b.2)‖ ≤ 1 / 16)
    (hdev : ∀ j, j < F.top → ∀ b ∈ innerBonds D j, ‖levelDeviation R (W z) j b.1 b.2‖ ≤ t)
    (hreal : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds D (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) :
    ∀ j, j < F.top → ∀ b ∈ innerBonds D j,
      AnalyticAt ℂ (fun w => complexChartField R (W w) j b.1 b.2) z := by
  intro j
  induction j with
  | zero =>
    intro _ b hb
    simp only [complexChartField]
    exact (analyticAt_unitExp (hfine b hb) (hfine1 b hb)).mul analyticAt_const
  | succ j ih =>
    intro hj c hc
    have hj' : j < F.top := by omega
    have hnear : ∀ b ∈ innerBonds D j, BondNearReal (complexChartField R (W z) j) (R j) t b.1 b.2 :=
      fun b hb => ⟨hdev j hj' b hb, det_complexChartField_of_norm_lt_one R (W z) j _ _
        (lt_of_le_of_lt (hdev j hj' b hb) ht1)⟩
    have hhull : HoldsOnHull c (fun b i => BondNearReal (complexChartField R (W z) j) (R j) t b i) :=
      holdsOnHull_of_innerBonds hj' hodd hc hnear
    have hcontours : ContoursNearReal (complexChartField R (W z) j) (R j) t σ c :=
      ⟨fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).1) hh π,
        fun h hh => pathNearReal_replicate _ _ _ fun r hr => hhull.2 h hh r hr,
        fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).2) hh π,
        fun h hh π => hreal j (by omega) c hc h hh π⟩
    have hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) j b i) z) :=
      holdsOnHull_of_innerBonds hj' hodd hc fun b hb => ih hj' b hb
    have hU := analyticAt_unitPart_complexGaugedContourAverage
      (X := fun w => complexChartField R (W w) j) hodd (by omega) (R j) ht hσ hτ hcontours hX
    simp only [complexChartField]
    exact ((analyticAt_unitExp (hcoarse j hj c hc) (hcoarse1 j hj c hc)).mul analyticAt_const).mul hU
end Chain
end YangMills.Construction.ComplexAnalyticity
end
