import YangMills.Construction.ColdChainAtEveryLevel.CellContexts
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChainIsAnalytic
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAComplexChain
import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativeFromSecondDifferences
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.ColdChainAtEveryLevel.TermsAtACellAreAnalytic
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtComplexCoordinates
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator Topology
open Metric Filter
namespace YangMills.Construction.ComplexChartEstimates
section Nested
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def dirDeriv (f : E → ℂ) (a : E) : E → ℂ := fun t => fderiv ℂ f t a
theorem analyticAt_dirDeriv [CompleteSpace E] {f : E → ℂ} {t : E} (h : AnalyticAt ℂ f t) (a : E) :
    AnalyticAt ℂ (dirDeriv f a) t :=
  ((ContinuousLinearMap.apply ℂ ℂ a).analyticAt _).comp h.fderiv
theorem iteratedFDeriv_two_eq_dirDeriv {f : E → ℂ} {p : E} (h : AnalyticAt ℂ f p) (a b : E) :
    iteratedFDeriv ℂ 2 f p ![b, a] = dirDeriv (dirDeriv f a) b p := by
  have hc : ContDiffAt ℂ (2 : ℕ) f p := h.contDiffAt
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ 1 f) p :=
    hc.differentiableAt_iteratedFDeriv (m := 1) (by norm_num)
  have e : dirDeriv f a = fun t => iteratedFDeriv ℂ 1 f t ![a] := by
    funext t
    simp [dirDeriv, iteratedFDeriv_one_apply]
  have h3 : HasFDerivAt (fun t => iteratedFDeriv ℂ 1 f t ![a])
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin 1 => E) ℂ ![a]).comp (fderiv ℂ (iteratedFDeriv ℂ 1 f) p)) p :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin 1 => E) ℂ ![a]).hasFDerivAt.comp p hd.hasFDerivAt
  rw [iteratedFDeriv_succ_apply_left]
  show _ = fderiv ℂ (dirDeriv f a) p b
  rw [e, h3.fderiv]
  simp
theorem iteratedFDeriv_three_eq_dirDeriv {f : E → ℂ} {p : E} (h : AnalyticAt ℂ f p) (a b c : E) :
    iteratedFDeriv ℂ 3 f p ![c, b, a] = dirDeriv (dirDeriv (dirDeriv f a) b) c p := by
  have hc : ContDiffAt ℂ (3 : ℕ) f p := h.contDiffAt
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ 2 f) p :=
    hc.differentiableAt_iteratedFDeriv (m := 2) (by norm_num)
  have e : dirDeriv (dirDeriv f a) b =ᶠ[𝓝 p] fun t => iteratedFDeriv ℂ 2 f t ![b, a] := by
    filter_upwards [h.eventually_analyticAt] with t ht
    exact (iteratedFDeriv_two_eq_dirDeriv ht a b).symm
  have h3 : HasFDerivAt (fun t => iteratedFDeriv ℂ 2 f t ![b, a])
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin 2 => E) ℂ ![b, a]).comp (fderiv ℂ (iteratedFDeriv ℂ 2 f) p)) p :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin 2 => E) ℂ ![b, a]).hasFDerivAt.comp p hd.hasFDerivAt
  rw [iteratedFDeriv_succ_apply_left]
  show _ = fderiv ℂ (dirDeriv (dirDeriv f a) b) p c
  rw [e.fderiv_eq, h3.fderiv]
  simp [Fin.tail_def]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E]
theorem dirDeriv_comp_affine_eventuallyEq (p₀ : E) (T : E' →L[ℂ] E) {f : E → ℂ} {x₀ : E'}
    (h : AnalyticAt ℂ f (p₀ + T x₀)) (v : E') :
    dirDeriv (fun x => f (p₀ + T x)) v =ᶠ[𝓝 x₀] fun x => dirDeriv f (T v) (p₀ + T x) := by
  have hcont : ContinuousAt (fun x : E' => p₀ + T x) x₀ := by fun_prop
  filter_upwards [hcont.eventually h.eventually_analyticAt] with x hx
  have hA : HasFDerivAt (fun x : E' => p₀ + T x) T x := T.hasFDerivAt.const_add p₀
  have h1 := hx.differentiableAt.hasFDerivAt.comp x hA
  show fderiv ℂ (fun x => f (p₀ + T x)) x v = _
  have h2 : fderiv ℂ (fun x => f (p₀ + T x)) x = (fderiv ℂ f (p₀ + T x)).comp T := h1.fderiv
  rw [h2]
  rfl
theorem dirDeriv_two_comp_affine_eventuallyEq (p₀ : E) (T : E' →L[ℂ] E) {f : E → ℂ} {x₀ : E'}
    (h : AnalyticAt ℂ f (p₀ + T x₀)) (v w : E') :
    dirDeriv (dirDeriv (fun x => f (p₀ + T x)) v) w =ᶠ[𝓝 x₀]
      fun x => dirDeriv (dirDeriv f (T v)) (T w) (p₀ + T x) := by
  have h1 := dirDeriv_comp_affine_eventuallyEq p₀ T h v
  have h2 := dirDeriv_comp_affine_eventuallyEq p₀ T (analyticAt_dirDeriv h (T v)) w
  have h3 : ∀ᶠ x in 𝓝 x₀, dirDeriv (dirDeriv (fun x => f (p₀ + T x)) v) w x =
      dirDeriv (fun x => dirDeriv f (T v) (p₀ + T x)) w x := by
    filter_upwards [h1.eventually_nhds] with x hx
    have hx' : dirDeriv (fun x => f (p₀ + T x)) v =ᶠ[𝓝 x] fun x => dirDeriv f (T v) (p₀ + T x) := hx
    show fderiv ℂ _ x w = fderiv ℂ _ x w
    rw [hx'.fderiv_eq]
  filter_upwards [h2, h3] with x a b
  rw [b, a]
theorem dirDeriv_three_comp_affine (p₀ : E) (T : E' →L[ℂ] E) {f : E → ℂ} {x₀ : E'}
    (h : AnalyticAt ℂ f (p₀ + T x₀)) (v w u : E') :
    dirDeriv (dirDeriv (dirDeriv (fun x => f (p₀ + T x)) v) w) u x₀ =
      dirDeriv (dirDeriv (dirDeriv f (T v)) (T w)) (T u) (p₀ + T x₀) := by
  have h1 := dirDeriv_two_comp_affine_eventuallyEq p₀ T h v w
  have h2 := dirDeriv_comp_affine_eventuallyEq p₀ T (analyticAt_dirDeriv (analyticAt_dirDeriv h (T v)) (T w)) u
  show fderiv ℂ _ x₀ u = _
  rw [h1.fderiv_eq]
  exact h2.self_of_nhds
theorem dirDeriv_two_comp_affine (p₀ : E) (T : E' →L[ℂ] E) {f : E → ℂ} {x₀ : E'}
    (h : AnalyticAt ℂ f (p₀ + T x₀)) (v w : E') :
    dirDeriv (dirDeriv (fun x => f (p₀ + T x)) v) w x₀ = dirDeriv (dirDeriv f (T v)) (T w) (p₀ + T x₀) :=
  (dirDeriv_two_comp_affine_eventuallyEq p₀ T h v w).self_of_nhds
end Nested
section Segments
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem hasDerivAt_real_line {f : E → ℂ} {e d : E} {x : ℝ} (h : DifferentiableAt ℂ f (e + (x : ℂ) • d)) :
    HasDerivAt (fun x' : ℝ => f (e + (x' : ℂ) • d)) (fderiv ℂ f (e + (x : ℂ) • d) d) x := by
  have h1 : HasDerivAt (fun x' : ℝ => e + (x' : ℂ) • d) d x := by
    have h2 : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    simpa using (h2.smul_const d).const_add e
  exact (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x h1
theorem norm_sub_le_of_dirDeriv_le {f : E → ℂ} {e d : E} {B : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ f (e + (x : ℂ) • d))
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℂ f (e + (x : ℂ) • d) d‖ ≤ B) : ‖f (e + d) - f e‖ ≤ B := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun x' : ℝ => f (e + (x' : ℂ) • d))
    (f' := fun x => fderiv ℂ f (e + (x : ℂ) • d) d) (C := B) (x := 0) (y := 1)
    (fun y hy => (hasDerivAt_real_line (hf y hy)).hasDerivWithinAt) (fun y hy => hB y hy) (by simp) (by simp)
  simpa using h
theorem norm_taylor_remainder_le {f : E → ℂ} {e' d a : E} {B : ℝ}
    (han : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℂ f ((u : ℂ) • (e' + (x : ℂ) • d)))
    (hB : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖dirDeriv (dirDeriv (dirDeriv f a) d) (e' + (x : ℂ) • d) ((u : ℂ) • (e' + (x : ℂ) • d))‖ ≤ B) :
    ‖dirDeriv f a (e' + d) - dirDeriv f a e' - dirDeriv (dirDeriv f a) d 0‖ ≤ B := by
  have hF : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖dirDeriv (dirDeriv f a) d (e' + (x : ℂ) • d) - dirDeriv (dirDeriv f a) d 0‖ ≤ B := by
    intro x hx
    have h := norm_sub_le_of_dirDeriv_le (f := dirDeriv (dirDeriv f a) d) (e := 0) (d := e' + (x : ℂ) • d) (B := B)
      (fun u hu => by
        rw [zero_add]
        exact (analyticAt_dirDeriv (analyticAt_dirDeriv (han u hu x hx) a) d).differentiableAt)
      (fun u hu => by
        rw [zero_add]
        exact hB u hu x hx)
    simpa using h
  have hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℂ f (e' + (x : ℂ) • d) := fun x hx => by
    simpa using han 1 (by simp) x hx
  have hd3 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun x' : ℝ => dirDeriv f a (e' + (x' : ℂ) • d) - (x' : ℂ) * dirDeriv (dirDeriv f a) d 0)
      (dirDeriv (dirDeriv f a) d (e' + (x : ℂ) • d) - dirDeriv (dirDeriv f a) d 0) x := fun x hx => by
    have h1 := hasDerivAt_real_line (f := dirDeriv f a) (e := e') (d := d) (x := x)
      (analyticAt_dirDeriv (hd x hx) a).differentiableAt
    have h2 : HasDerivAt (fun x' : ℝ => (x' : ℂ) * dirDeriv (dirDeriv f a) d 0) (dirDeriv (dirDeriv f a) d 0) x := by
      have h3 : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      simpa using h3.mul_const (dirDeriv (dirDeriv f a) d 0)
    exact h1.sub h2
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x' : ℝ => dirDeriv f a (e' + (x' : ℂ) • d) - (x' : ℂ) * dirDeriv (dirDeriv f a) d 0)
    (f' := fun x => dirDeriv (dirDeriv f a) d (e' + (x : ℂ) • d) - dirDeriv (dirDeriv f a) d 0) (C := B) (x := 0) (y := 1)
    (fun y hy => (hd3 y hy).hasDerivWithinAt) (fun y hy => hF y hy) (by simp) (by simp)
  simp only [Complex.ofReal_one, one_smul, one_mul, Complex.ofReal_zero, zero_smul, add_zero, zero_mul, sub_zero,
    norm_one, mul_one] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ring
end Segments
section Cells
open BlockAverages
variable {F : BlockFrame} {m : ℕ}
def spanNorm (S : Finset F.Cell) (R : F.FieldChain) (d : Fin m → ChainChart F) (z : F.Cell) (t : Fin m → ℂ) : ℝ :=
  ∑ l, ‖t l‖ * localNorm S R (d l) (constOneWeights F) z
theorem spanNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (d : Fin m → ChainChart F) (z : F.Cell)
    (t : Fin m → ℂ) : 0 ≤ spanNorm S R d z t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
theorem spanNorm_add_le (S : Finset F.Cell) (R : F.FieldChain) (d : Fin m → ChainChart F) (z : F.Cell)
    (t t' : Fin m → ℂ) : spanNorm S R d z (t + t') ≤ spanNorm S R d z t + spanNorm S R d z t' := by
  unfold spanNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)
theorem spanNorm_smul (S : Finset F.Cell) (R : F.FieldChain) (d : Fin m → ChainChart F) (z : F.Cell) (c : ℂ)
    (t : Fin m → ℂ) : spanNorm S R d z (c • t) = ‖c‖ * spanNorm S R d z t := by
  unfold spanNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring
theorem spanNorm_single (S : Finset F.Cell) (R : F.FieldChain) (d : Fin m → ChainChart F) (z : F.Cell) (l : Fin m) :
    spanNorm S R d z (Pi.single l 1) = localNorm S R (d l) (constOneWeights F) z := by
  classical
  unfold spanNorm
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
theorem spanLocalNorm_zeroChart (S : Finset F.Cell) (R : F.FieldChain) (d : Fin m → ChainChart F) (z : F.Cell)
    (t : Fin m → ℂ) : CellSpans.spanLocalNorm S R (zeroChart F) d t z = spanNorm S R d z t := by
  unfold CellSpans.spanLocalNorm spanNorm
  have h0 : localNorm S R (zeroChart F) (constOneWeights F) z = 0 := by
    unfold localNorm localNormSq
    simp [zeroChart, linearizedCurl, adjointAction]
  rw [h0, zero_add]
abbrev cellTermsOnSpan (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (d : Fin m → ChainChart F) (z : F.Cell) : (Fin m → ℂ) → ℂ :=
  fun t => complexCellTerms a S R (CellSpans.spanChart (zeroChart F) d t) V z
theorem analyticAt_affine_sum (c₀ : ComplexifiedQuaternions.ComplexQuat) (c : Fin m → ComplexifiedQuaternions.ComplexQuat)
    (t₀ : Fin m → ℂ) : AnalyticAt ℂ (fun w : Fin m → ℂ => c₀ + ∑ l, w l • c l) t₀ := by
  refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun l _ => ?_)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) l).analyticAt t₀).smul analyticAt_const
set_option maxHeartbeats 1000000 in
theorem analyticAt_cellTermsOnSpan_of_sourceBounds (han : complexCellTermsAnalyticStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ} (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (d : Fin m → ChainChart F) {t₀ : Fin m → ℂ}
    (hsz : CellNormBounds.SourceBounds S z R (CellSpans.spanChart (zeroChart F) d t₀) y) :
    AnalyticAt ℂ (cellTermsOnSpan a S R V d z) t₀ := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  obtain ⟨hss, hball⟩ := CellSources.deviationBall_of_finsetLpNorm_le
    (ctx.level_le (CellSpans.spanChart (zeroChart F) d t₀)) hsz.base_le hsz.upper_le (by linarith)
  have hH0 := ComplexCells.hullBondCount_nonneg F.blockSide
  have ha := hy.count_le_radius
  have hsmall : 8 * (F.blockSide : ℝ) * (ComplexLevels.hullBondCount F.blockSide * (8 * y)) ≤ 1 / 1024 := by
    have h1 : 48 * (48 * ComplexLevels.hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) ≤ 1 := by
      unfold ComplexDifferences.hullBallRadius at ha
      rw [le_div_iff₀ (by positivity)] at ha
      exact ha
    have h2 : 0 ≤ ComplexLevels.hullBondCount F.blockSide * y * F.blockSide := by positivity
    have e1 : 48 * (48 * ComplexLevels.hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) =
        48 * 48 * 8192 * (ComplexLevels.hullBondCount F.blockSide * y * F.blockSide) +
          48 * 8192 * (y * F.blockSide) := by ring
    have h3 : 0 ≤ y * (F.blockSide : ℝ) := by positivity
    have e2 : 8 * (F.blockSide : ℝ) * (ComplexLevels.hullBondCount F.blockSide * (8 * y)) =
        64 * (ComplexLevels.hullBondCount F.blockSide * y * F.blockSide) := by ring
    rw [e2]
    rw [e1] at h1
    linarith
  refine (han F S R V a hodd hamb).2 m (CellSpans.spanChart (zeroChart F) d) t₀ z (8 * y) (C₀ * s) (by positivity)
    (by linarith) ((ctx.const_mul_scale_le).trans (by linarith)) hsmall ?_ ?_ ?_ ?_ hball.norm_deviation_le ?_
  · intro b _
    have e : (fun w => complexifiedImaginary ((CellSpans.spanChart (zeroChart F) d w).re.fine b.1 b.2)
        ((CellSpans.spanChart (zeroChart F) d w).im.fine b.1 b.2)) =
        fun w => ComplexifiedQuaternions.ofQuat ((zeroChart F).fine b.1 b.2 : ℍ[ℝ]) +
          ∑ l, w l • ComplexifiedQuaternions.ofQuat ((d l).fine b.1 b.2 : ℍ[ℝ]) := by
      funext w
      exact CellSpans.baseSource_spanChart (zeroChart F) d w b.1 b.2
    rw [e]
    exact analyticAt_affine_sum _ _ _
  · intro b hb
    exact (hss.base_le b hb).trans (by norm_num)
  · intro j _ b _
    have e : (fun w => complexifiedImaginary ((CellSpans.spanChart (zeroChart F) d w).re.coarse j b.1 b.2)
        ((CellSpans.spanChart (zeroChart F) d w).im.coarse j b.1 b.2)) =
        fun w => ComplexifiedQuaternions.ofQuat ((zeroChart F).coarse j b.1 b.2 : ℍ[ℝ]) +
          ∑ l, w l • ComplexifiedQuaternions.ofQuat ((d l).coarse j b.1 b.2 : ℍ[ℝ]) := by
      funext w
      exact CellSpans.upperSource_spanChart (zeroChart F) d w ⟨j, b⟩
    rw [e]
    exact analyticAt_affine_sum _ _ _
  · intro j hj b hb
    exact (hss.upper_le _ (CellSources.mem_lowerBonds hj hb)).trans (by norm_num)
  · intro j hj c hc h hh π
    refine (ctx.near j hj c hc h hh π).trans ?_
    have hCs : 0 ≤ C₀ * s := mul_nonneg ctx.const_pos.le ctx.scale_pos.le
    have h3 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (ComplexLevels.inv_pow_le_one hodd.pos _)
    exact mul_le_of_le_one_right hCs h3
theorem analyticAt_cellTermsOnSpan (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top)
    {C₀ s y : ℝ} (ctx : CellSpans.CellHypotheses S z R C₀ s y) (d : Fin m → ChainChart F) {t₀ : Fin m → ℂ}
    (h0 : spanNorm S R d z t₀ ≤ y) : AnalyticAt ℂ (cellTermsOnSpan a S R V d z) t₀ :=
  analyticAt_cellTermsOnSpan_of_sourceBounds han hamb hodd a V ctx d
    (CellSpans.sourceBounds_spanChart (S := S) (z := z) (y := y) hodd R (zeroChart F) d t₀
      (by rw [spanLocalNorm_zeroChart]; exact h0))
theorem sourceBounds_of_localNorm_pair (hodd : Odd F.blockSide) {S : Finset F.Cell} {z : F.Cell} (R : F.FieldChain)
    (W : ComplexChainChart F) {y : ℝ}
    (h : localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z ≤ y) :
    CellNormBounds.SourceBounds S z R W y := by
  have e : CellSpans.spanChart W.re ![W.im] ![Complex.I] = W := by
    unfold CellSpans.spanChart
    cases W with
    | mk re im =>
      congr 1
      · apply CoordinateSeminorms.chainChart_ext
        · funext x i
          simp [chartShiftMulti]
        · funext j x i
          simp [chartShiftMulti]
      · apply CoordinateSeminorms.chainChart_ext
        · funext x i
          simp [chartShiftMulti, zeroChart]
        · funext j x i
          simp [chartShiftMulti, zeroChart]
  have h1 := CellSpans.sourceBounds_spanChart (S := S) (z := z) (y := y) hodd R W.re ![W.im] ![Complex.I] (by
    unfold CellSpans.spanLocalNorm
    simpa using h)
  rwa [e] at h1
def secondDiffBound (L : ℕ) (a del : ℝ) : ℝ :=
  CellBounds.cellSecondDiffConst (HullBounds.hullFactor L) (200000 * (L : ℝ) ^ 2)
    (1 / (2 * (200000 * (L : ℝ) ^ 2))) a * 9 * Real.exp (2 * del)
theorem secondDiffBound_nonneg {L : ℕ} (hL : Odd L) (a del : ℝ) : 0 ≤ secondDiffBound L a del := by
  have hF := ComplexCells.hullFactor_nonneg L
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL.pos
  unfold secondDiffBound CellBounds.cellSecondDiffConst CellBounds.secondDiffConst
  positivity
theorem exists_norm_second_diff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    (a : ℝ) {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ}
    (ctx : CellSpans.CellHypotheses S z R C₀ s y) (d : Fin m → ChainChart F) {l1 l2 : Fin m} {φ : F.Cell → ℝ}
    {del θ : ℝ} (hdel : 0 ≤ del) (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8)
    (p : F.Site 0) {t : Fin m → ℂ} (ht : spanNorm S R d z t ≤ 3 * y / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ₁ τ₂ : ℂ, ‖τ₁‖ < δ → ‖τ₂‖ < δ →
      ‖cellTermsOnSpan a S R V d z (t + τ₁ • (Pi.single l1 1 : Fin m → ℂ) + τ₂ • (Pi.single l2 1 : Fin m → ℂ)) -
          cellTermsOnSpan a S R V d z (t + τ₁ • (Pi.single l1 1 : Fin m → ℂ)) -
          cellTermsOnSpan a S R V d z (t + τ₂ • (Pi.single l2 1 : Fin m → ℂ)) + cellTermsOnSpan a S R V d z t‖ ≤
        secondDiffBound F.blockSide a del * localNorm S R (d l1) (classWeight F φ θ p) z *
          localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z * ‖τ₁‖ * ‖τ₂‖ := by
  have hy0 : 0 < y := ctx.small.pos
  set n1 := localNorm S R (d l1) (constOneWeights F) z with hn1
  set n2 := localNorm S R (d l2) (constOneWeights F) z with hn2
  have hn10 : 0 ≤ n1 := Real.sqrt_nonneg _
  have hn20 : 0 ≤ n2 := Real.sqrt_nonneg _
  refine ⟨y / (8 * (n1 + n2 + 1)), by positivity, fun τ₁ τ₂ h₁ h₂ => ?_⟩
  have hδ₁ : ‖τ₁‖ * n1 ≤ y / 8 := by
    have h3 : n1 ≤ n1 + n2 + 1 := by linarith
    calc ‖τ₁‖ * n1 ≤ y / (8 * (n1 + n2 + 1)) * (n1 + n2 + 1) := mul_le_mul h₁.le h3 hn10 (by positivity)
      _ = y / 8 := by field_simp
  have hδ₂ : ‖τ₂‖ * n2 ≤ y / 8 := by
    have h3 : n2 ≤ n1 + n2 + 1 := by linarith
    calc ‖τ₂‖ * n2 ≤ y / (8 * (n1 + n2 + 1)) * (n1 + n2 + 1) := mul_le_mul h₂.le h3 hn20 (by positivity)
      _ = y / 8 := by field_simp
  have s1 : ∀ (t' : Fin m → ℂ) (τ : ℂ) (l : Fin m),
      spanNorm S R d z (t' + τ • (Pi.single l 1 : Fin m → ℂ)) ≤
        spanNorm S R d z t' + ‖τ‖ * localNorm S R (d l) (constOneWeights F) z := fun t' τ l => by
    refine (spanNorm_add_le S R d z _ _).trans ?_
    rw [spanNorm_smul, spanNorm_single]
  have m₁ := s1 t τ₁ l1
  have m₂ := s1 t τ₂ l2
  have m₃ := s1 (t + τ₁ • (Pi.single l1 1 : Fin m → ℂ)) τ₂ l2
  have hb := CellSpans.norm_second_diff_complexCellTerms_le hamb hodd h2 a V ctx (zeroChart F) d t τ₁ τ₂ l1 l2
    (by rw [spanLocalNorm_zeroChart]; linarith) (by rw [spanLocalNorm_zeroChart]; linarith)
    (by rw [spanLocalNorm_zeroChart]; linarith) (by rw [spanLocalNorm_zeroChart]; linarith) hdel hφ hθ p
  refine hb.trans (le_of_eq ?_)
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  have eN : ((F.blockSide : ℝ) ^ F.top) ^ (-θ) * ((F.blockSide : ℝ) ^ F.top) ^ θ = 1 := by
    rw [← Real.rpow_add hN]
    simp
  have eE : Real.exp (del - φ z) * Real.exp (del + φ z) = Real.exp (2 * del) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold secondDiffBound
  calc _ = CellBounds.cellSecondDiffConst (HullBounds.hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
        (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a * 9 *
        (Real.exp (del - φ z) * Real.exp (del + φ z)) *
        (((F.blockSide : ℝ) ^ F.top) ^ (-θ) * ((F.blockSide : ℝ) ^ F.top) ^ θ) *
        (‖τ₁‖ * localNorm S R (d l1) (classWeight F φ θ p) z) *
        (‖τ₂‖ * localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z) := by ring
    _ = _ := by
      rw [eN, eE]
      ring
end Cells
section Mixed
open BlockAverages
variable {F : BlockFrame} {m : ℕ}
def scaledTriple {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (r₀ r₁ r₂ : ℂ) (q e₁ e₂ : E) :
    (Fin 3 → ℂ) →L[ℂ] E :=
  (r₀ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).smulRight q +
    (r₁ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 1).smulRight e₁ +
    (r₂ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).smulRight e₂
theorem scaledTriple_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (r₀ r₁ r₂ : ℂ) (q e₁ e₂ : E)
    (x : Fin 3 → ℂ) : scaledTriple r₀ r₁ r₂ q e₁ e₂ x = (r₀ * x 0) • q + (r₁ * x 1) • e₁ + (r₂ * x 2) • e₂ := by
  simp [scaledTriple]
def scaledPair {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (r₁ r₂ : ℂ) (e₁ e₂ : E) : (Fin 2 → ℂ) →L[ℂ] E :=
  (r₁ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight e₁ +
    (r₂ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight e₂
theorem scaledPair_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (r₁ r₂ : ℂ) (e₁ e₂ : E)
    (x : Fin 2 → ℂ) : scaledPair r₁ r₂ e₁ e₂ x = (r₁ * x 0) • e₁ + (r₂ * x 1) • e₂ := by
  simp [scaledPair]
variable {a : ℝ} {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
theorem norm_dirDeriv_two_le (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top) (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (d : Fin m → ChainChart F) (l1 l2 : Fin m) {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {p₀ : Fin m → ℂ}
    (hp : spanNorm S R d z p₀ ≤ y / 2) :
    ‖dirDeriv (dirDeriv (cellTermsOnSpan a S R V d z) (Pi.single l2 1)) (Pi.single l1 1) p₀‖ ≤
      Analytic.cauchyHalvingConstant 0 * (secondDiffBound F.blockSide a del *
        localNorm S R (d l1) (classWeight F φ θ p) z *
        localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z) := by
  have hy0 : 0 < y := ctx.small.pos
  set e₁ : Fin m → ℂ := Pi.single l1 1 with he₁
  set e₂ : Fin m → ℂ := Pi.single l2 1 with he₂
  set n1 := localNorm S R (d l1) (constOneWeights F) z with hn1
  set n2 := localNorm S R (d l2) (constOneWeights F) z with hn2
  have hn10 : 0 ≤ n1 := Real.sqrt_nonneg _
  have hn20 : 0 ≤ n2 := Real.sqrt_nonneg _
  set r₁ : ℝ := y / (8 * (n1 + 1)) with hr₁
  set r₂ : ℝ := y / (8 * (n2 + 1)) with hr₂
  have hr₁0 : 0 < r₁ := by positivity
  have hr₂0 : 0 < r₂ := by positivity
  set T := scaledPair (r₁ : ℂ) (r₂ : ℂ) e₁ e₂ with hT
  set G := cellTermsOnSpan a S R V d z with hG
  set M := secondDiffBound F.blockSide a del * localNorm S R (d l1) (classWeight F φ θ p) z *
    localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z with hM
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg (secondDiffBound_nonneg hodd _ _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hnear : ∀ x ∈ ball (0 : Fin 2 → ℂ) 1, spanNorm S R d z (p₀ + T x) ≤ 3 * y / 4 := by
    intro x hx
    have hx1 : ‖x‖ < 1 := by simpa using hx
    have b0 : ‖x 0‖ ≤ 1 := (norm_le_pi_norm x 0).trans hx1.le
    have b1 : ‖x 1‖ ≤ 1 := (norm_le_pi_norm x 1).trans hx1.le
    rw [hT, scaledPair_apply]
    have t1 := spanNorm_add_le S R d z p₀ (((r₁ : ℂ) * x 0) • e₁ + ((r₂ : ℂ) * x 1) • e₂)
    have t2 := spanNorm_add_le S R d z (((r₁ : ℂ) * x 0) • e₁) (((r₂ : ℂ) * x 1) • e₂)
    rw [spanNorm_smul, spanNorm_smul, he₁, he₂, spanNorm_single, spanNorm_single, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr₁0,
      abs_of_pos hr₂0] at t2
    have c1 : r₁ * ‖x 0‖ * n1 ≤ y / 8 := by
      calc r₁ * ‖x 0‖ * n1 ≤ r₁ * 1 * (n1 + 1) := by gcongr; linarith
        _ = y / 8 := by rw [hr₁]; field_simp
    have c2 : r₂ * ‖x 1‖ * n2 ≤ y / 8 := by
      calc r₂ * ‖x 1‖ * n2 ≤ r₂ * 1 * (n2 + 1) := by gcongr; linarith
        _ = y / 8 := by rw [hr₂]; field_simp
    linarith
  have hGan : ∀ x ∈ ball (0 : Fin 2 → ℂ) 1, AnalyticAt ℂ G (p₀ + T x) := fun x hx =>
    analyticAt_cellTermsOnSpan han hamb hodd a V ctx d ((hnear x hx).trans (by linarith))
  set Gt : (Fin 2 → ℂ) → ℂ := fun x => G (p₀ + T x) with hGt
  have hGtan : AnalyticOnNhd ℂ Gt (ball 0 1) := fun x hx => by
    have hA : AnalyticAt ℂ (fun x : Fin 2 → ℂ => p₀ + T x) x := analyticAt_const.add (T.analyticAt x)
    exact AnalyticAt.comp (g := G) (f := fun x : Fin 2 → ℂ => p₀ + T x) (hGan x hx) hA
  set v : Fin 2 → Fin 2 → ℂ := ![Pi.single 0 ((r₁ : ℂ)⁻¹), Pi.single 1 ((r₂ : ℂ)⁻¹)] with hv
  have c₁ : (r₁ : ℂ) ≠ 0 := by exact_mod_cast hr₁0.ne'
  have c₂ : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr₂0.ne'
  have hT0 : T (v 0) = e₁ := by
    rw [hT, scaledPair_apply]
    simp [hv, c₁]
  have hT1 : T (v 1) = e₂ := by
    rw [hT, scaledPair_apply]
    simp [hv, c₂]
  have hsd : ∀ t ∈ ball (0 : Fin 2 → ℂ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ τ₁ τ₂ : ℂ, ‖τ₁‖ < δ → ‖τ₂‖ < δ →
      ‖Gt (t + τ₁ • v 0 + τ₂ • v 1) - Gt (t + τ₁ • v 0) - Gt (t + τ₂ • v 1) + Gt t‖ ≤ M * ‖τ₁‖ * ‖τ₂‖ := by
    intro t ht
    obtain ⟨δ, hδ, hb⟩ := exists_norm_second_diff_le hamb hodd h2 a V ctx d (l1 := l1) (l2 := l2) hdel hφ hθ p
      (hnear t ht)
    refine ⟨δ, hδ, fun τ₁ τ₂ h₁ h₂ => ?_⟩
    have e1 : p₀ + T (t + τ₁ • v 0 + τ₂ • v 1) = p₀ + T t + τ₁ • e₁ + τ₂ • e₂ := by
      rw [map_add, map_add, map_smul, map_smul, hT0, hT1]
      abel
    have e2 : p₀ + T (t + τ₁ • v 0) = p₀ + T t + τ₁ • e₁ := by
      rw [map_add, map_smul, hT0]
      abel
    have e3 : p₀ + T (t + τ₂ • v 1) = p₀ + T t + τ₂ • e₂ := by
      rw [map_add, map_smul, hT1]
      abel
    simp only [hGt, e1, e2, e3]
    exact hb τ₁ τ₂ h₁ h₂
  have hm := hmix 2 0 Gt 1 M v 0 1 (by decide) one_pos hM0 hGtan hsd
  have h0 : (0 : Fin 2 → ℂ) ∈ ball (0 : Fin 2 → ℂ) 1 := by simp
  have hv2 : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have e5 : iteratedFDeriv ℂ 2 Gt 0 v = dirDeriv (dirDeriv G e₂) e₁ p₀ := by
    rw [hv2, iteratedFDeriv_two_eq_dirDeriv (hGtan 0 h0)]
    have := dirDeriv_two_comp_affine (x₀ := (0 : Fin 2 → ℂ)) p₀ T (f := G) (hGan 0 h0) (v 1) (v 0)
    simpa [hT0, hT1] using this
  rw [← e5]
  refine hm.trans (le_of_eq ?_)
  have e6 : ((Finset.univ : Finset (Fin 2)).erase 0).erase 1 = ∅ := by decide
  simp [e6]
set_option maxHeartbeats 1000000 in
theorem norm_dirDeriv_three_le_add (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top) (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (d : Fin m → ChainChart F) (l1 l2 : Fin m) {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {p₀ : Fin m → ℂ}
    (hp : spanNorm S R d z p₀ ≤ y / 2) (q : Fin m → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖dirDeriv (dirDeriv (dirDeriv (cellTermsOnSpan a S R V d z) (Pi.single l2 1)) (Pi.single l1 1)) q p₀‖ ≤
      Analytic.cauchyHalvingConstant 1 * (secondDiffBound F.blockSide a del *
        localNorm S R (d l1) (classWeight F φ θ p) z *
        localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z) * (12 / y * (spanNorm S R d z q + ε)) := by
  have hy0 : 0 < y := ctx.small.pos
  set e₁ : Fin m → ℂ := Pi.single l1 1 with he₁
  set e₂ : Fin m → ℂ := Pi.single l2 1 with he₂
  set n0 := spanNorm S R d z q with hn0d
  set n1 := localNorm S R (d l1) (constOneWeights F) z with hn1
  set n2 := localNorm S R (d l2) (constOneWeights F) z with hn2
  have hn00 : 0 ≤ n0 := spanNorm_nonneg _ _ _ _ _
  have hn10 : 0 ≤ n1 := Real.sqrt_nonneg _
  have hn20 : 0 ≤ n2 := Real.sqrt_nonneg _
  set r₀ : ℝ := y / (12 * (n0 + ε)) with hr₀
  set r₁ : ℝ := y / (12 * (n1 + 1)) with hr₁
  set r₂ : ℝ := y / (12 * (n2 + 1)) with hr₂
  have hr₀0 : 0 < r₀ := by positivity
  have hr₁0 : 0 < r₁ := by positivity
  have hr₂0 : 0 < r₂ := by positivity
  set T := scaledTriple (r₀ : ℂ) (r₁ : ℂ) (r₂ : ℂ) q e₁ e₂ with hT
  set G := cellTermsOnSpan a S R V d z with hG
  set M := secondDiffBound F.blockSide a del * localNorm S R (d l1) (classWeight F φ θ p) z *
    localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z with hM
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg (secondDiffBound_nonneg hodd _ _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hnear : ∀ x ∈ ball (0 : Fin 3 → ℂ) 1, spanNorm S R d z (p₀ + T x) ≤ 3 * y / 4 := by
    intro x hx
    have hx1 : ‖x‖ < 1 := by simpa using hx
    have b0 : ‖x 0‖ ≤ 1 := (norm_le_pi_norm x 0).trans hx1.le
    have b1 : ‖x 1‖ ≤ 1 := (norm_le_pi_norm x 1).trans hx1.le
    have b2 : ‖x 2‖ ≤ 1 := (norm_le_pi_norm x 2).trans hx1.le
    rw [hT, scaledTriple_apply]
    have t1 := spanNorm_add_le S R d z p₀ (((r₀ : ℂ) * x 0) • q + ((r₁ : ℂ) * x 1) • e₁ + ((r₂ : ℂ) * x 2) • e₂)
    have t2 := spanNorm_add_le S R d z (((r₀ : ℂ) * x 0) • q + ((r₁ : ℂ) * x 1) • e₁) (((r₂ : ℂ) * x 2) • e₂)
    have t3 := spanNorm_add_le S R d z (((r₀ : ℂ) * x 0) • q) (((r₁ : ℂ) * x 1) • e₁)
    rw [spanNorm_smul, he₂, spanNorm_single, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₂0] at t2
    rw [spanNorm_smul, spanNorm_smul, he₁, spanNorm_single, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr₀0, abs_of_pos hr₁0] at t3
    have c0 : r₀ * ‖x 0‖ * n0 ≤ y / 12 := by
      calc r₀ * ‖x 0‖ * n0 ≤ r₀ * 1 * (n0 + ε) := by gcongr; linarith
        _ = y / 12 := by rw [hr₀]; field_simp
    have c1 : r₁ * ‖x 1‖ * n1 ≤ y / 12 := by
      calc r₁ * ‖x 1‖ * n1 ≤ r₁ * 1 * (n1 + 1) := by gcongr; linarith
        _ = y / 12 := by rw [hr₁]; field_simp
    have c2 : r₂ * ‖x 2‖ * n2 ≤ y / 12 := by
      calc r₂ * ‖x 2‖ * n2 ≤ r₂ * 1 * (n2 + 1) := by gcongr; linarith
        _ = y / 12 := by rw [hr₂]; field_simp
    linarith
  have hGan : ∀ x ∈ ball (0 : Fin 3 → ℂ) 1, AnalyticAt ℂ G (p₀ + T x) := fun x hx =>
    analyticAt_cellTermsOnSpan han hamb hodd a V ctx d ((hnear x hx).trans (by linarith))
  set Gt : (Fin 3 → ℂ) → ℂ := fun x => G (p₀ + T x) with hGt
  have hGtan : AnalyticOnNhd ℂ Gt (ball 0 1) := fun x hx => by
    have hA : AnalyticAt ℂ (fun x : Fin 3 → ℂ => p₀ + T x) x := analyticAt_const.add (T.analyticAt x)
    exact AnalyticAt.comp (g := G) (f := fun x : Fin 3 → ℂ => p₀ + T x) (hGan x hx) hA
  set v : Fin 3 → Fin 3 → ℂ :=
    ![Pi.single 0 ((r₀ : ℂ)⁻¹), Pi.single 1 ((r₁ : ℂ)⁻¹), Pi.single 2 ((r₂ : ℂ)⁻¹)] with hv
  have c₀ : (r₀ : ℂ) ≠ 0 := by exact_mod_cast hr₀0.ne'
  have c₁ : (r₁ : ℂ) ≠ 0 := by exact_mod_cast hr₁0.ne'
  have c₂ : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr₂0.ne'
  have hT0 : T (v 0) = q := by
    rw [hT, scaledTriple_apply]
    simp [hv, c₀]
  have hT1 : T (v 1) = e₁ := by
    rw [hT, scaledTriple_apply]
    simp [hv, c₁]
  have hT2 : T (v 2) = e₂ := by
    rw [hT, scaledTriple_apply]
    simp [hv, c₂]
  have hsd : ∀ t ∈ ball (0 : Fin 3 → ℂ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ τ₁ τ₂ : ℂ, ‖τ₁‖ < δ → ‖τ₂‖ < δ →
      ‖Gt (t + τ₁ • v 1 + τ₂ • v 2) - Gt (t + τ₁ • v 1) - Gt (t + τ₂ • v 2) + Gt t‖ ≤ M * ‖τ₁‖ * ‖τ₂‖ := by
    intro t ht
    obtain ⟨δ, hδ, hb⟩ := exists_norm_second_diff_le hamb hodd h2 a V ctx d (l1 := l1) (l2 := l2) hdel hφ hθ p
      (hnear t ht)
    refine ⟨δ, hδ, fun τ₁ τ₂ h₁ h₂ => ?_⟩
    have e1 : p₀ + T (t + τ₁ • v 1 + τ₂ • v 2) = p₀ + T t + τ₁ • e₁ + τ₂ • e₂ := by
      rw [map_add, map_add, map_smul, map_smul, hT1, hT2]
      abel
    have e2 : p₀ + T (t + τ₁ • v 1) = p₀ + T t + τ₁ • e₁ := by
      rw [map_add, map_smul, hT1]
      abel
    have e3 : p₀ + T (t + τ₂ • v 2) = p₀ + T t + τ₂ • e₂ := by
      rw [map_add, map_smul, hT2]
      abel
    simp only [hGt, e1, e2, e3]
    exact hb τ₁ τ₂ h₁ h₂
  have hm := hmix 3 1 Gt 1 M v 1 2 (by decide) one_pos hM0 hGtan hsd
  have h0 : (0 : Fin 3 → ℂ) ∈ ball (0 : Fin 3 → ℂ) 1 := by simp
  have hv3 : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  have e5 : iteratedFDeriv ℂ 3 Gt 0 v = dirDeriv (dirDeriv (dirDeriv G e₂) e₁) q p₀ := by
    rw [hv3, iteratedFDeriv_three_eq_dirDeriv (hGtan 0 h0)]
    have := dirDeriv_three_comp_affine (x₀ := (0 : Fin 3 → ℂ)) p₀ T (f := G) (hGan 0 h0) (v 2) (v 1) (v 0)
    simpa [hT0, hT1, hT2] using this
  rw [← e5]
  refine hm.trans (le_of_eq ?_)
  have e6 : ((Finset.univ : Finset (Fin 3)).erase 1).erase 2 = {0} := by decide
  have e7 : ‖v 0‖ = r₀⁻¹ := by
    simp only [hv, Matrix.cons_val_zero]
    rw [Pi.norm_single, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀0]
  rw [e6, Finset.prod_singleton, e7, hr₀]
  simp only [one_pow, div_one]
  rw [inv_div]
  congr 1
  field_simp
theorem norm_dirDeriv_three_le (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top) (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (d : Fin m → ChainChart F) (l1 l2 : Fin m) {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {p₀ : Fin m → ℂ}
    (hp : spanNorm S R d z p₀ ≤ y / 2) (q : Fin m → ℂ) :
    ‖dirDeriv (dirDeriv (dirDeriv (cellTermsOnSpan a S R V d z) (Pi.single l2 1)) (Pi.single l1 1)) q p₀‖ ≤
      Analytic.cauchyHalvingConstant 1 * (secondDiffBound F.blockSide a del *
        localNorm S R (d l1) (classWeight F φ θ p) z *
        localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z) * (12 / y * (spanNorm S R d z q + 0)) := by
  set B := Analytic.cauchyHalvingConstant 1 * (secondDiffBound F.blockSide a del *
    localNorm S R (d l1) (classWeight F φ θ p) z *
    localNorm S R (d l2) (invertedWeights (classWeight F φ θ p)) z) with hB
  have hcont : Continuous fun ε : ℝ => B * (12 / y * (spanNorm S R d z q + ε)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => B * (12 / y * (spanNorm S R d z q + ε))) (𝓝[>] 0)
      (𝓝 (B * (12 / y * (spanNorm S R d z q + 0)))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_dirDeriv_three_le_add hmix han hamb hodd h2 V ctx d l1 l2 hdel hφ hθ p hp q hε
end Mixed
section Sums
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem dirDeriv_sum {ι : Type} (T : Finset ι) (f : ι → E → ℂ) {t : E} (a : E)
    (h : ∀ i ∈ T, DifferentiableAt ℂ (f i) t) :
    dirDeriv (fun t => ∑ i ∈ T, f i t) a t = ∑ i ∈ T, dirDeriv (f i) a t := by
  unfold dirDeriv
  rw [fderiv_fun_sum h]
  simp
theorem dirDeriv_two_sum {ι : Type} (T : Finset ι) (f : ι → E → ℂ) {t : E} (a b : E)
    (h : ∀ i ∈ T, AnalyticAt ℂ (f i) t) :
    dirDeriv (dirDeriv (fun t => ∑ i ∈ T, f i t) a) b t = ∑ i ∈ T, dirDeriv (dirDeriv (f i) a) b t := by
  have h1 : ∀ᶠ t' in 𝓝 t, ∀ i ∈ T, AnalyticAt ℂ (f i) t' :=
    (Filter.eventually_all_finset T).2 fun i hi => (h i hi).eventually_analyticAt
  have h2 : dirDeriv (fun t => ∑ i ∈ T, f i t) a =ᶠ[𝓝 t] fun t => ∑ i ∈ T, dirDeriv (f i) a t := by
    filter_upwards [h1] with t' ht'
    exact dirDeriv_sum T f a fun i hi => (ht' i hi).differentiableAt
  show fderiv ℂ _ t b = _
  rw [h2.fderiv_eq]
  exact dirDeriv_sum T (fun i => dirDeriv (f i) a) b fun i hi => (analyticAt_dirDeriv (h i hi) a).differentiableAt
theorem dirDeriv_two_add_smul {f : E → ℂ} {t : E} (e₂ e₃ b : E) (h : AnalyticAt ℂ f t) (w : ℂ) :
    dirDeriv (dirDeriv f (e₂ + w • e₃)) b t = dirDeriv (dirDeriv f e₂) b t + w * dirDeriv (dirDeriv f e₃) b t := by
  have e : dirDeriv f (e₂ + w • e₃) = fun t => dirDeriv f e₂ t + w * dirDeriv f e₃ t := by
    funext t
    simp [dirDeriv]
  rw [e]
  have h1 := (analyticAt_dirDeriv h e₂).differentiableAt
  have h2 := (analyticAt_dirDeriv h e₃).differentiableAt
  show fderiv ℂ (fun t => dirDeriv f e₂ t + w * dirDeriv f e₃ t) t b = _
  rw [fderiv_fun_add h1 (h2.const_mul w), fderiv_const_mul h2]
  simp [dirDeriv]
theorem dirDeriv_three_add_smul {f : E → ℂ} {t : E} (a e₂ e₃ c : E) (h : AnalyticAt ℂ f t) (w : ℂ) :
    dirDeriv (dirDeriv (dirDeriv f a) (e₂ + w • e₃)) c t =
      dirDeriv (dirDeriv (dirDeriv f a) e₂) c t + w * dirDeriv (dirDeriv (dirDeriv f a) e₃) c t :=
  dirDeriv_two_add_smul e₂ e₃ c (analyticAt_dirDeriv h a) w
end Sums
section RealForm
theorem hasDerivAt_re_of_ofReal_eventuallyEq {h : ℝ → ℝ} {k : ℝ → ℂ} {c : ℂ} (hk : HasDerivAt k c 0)
    (he : ∀ᶠ τ in 𝓝 (0 : ℝ), (h τ : ℂ) = k τ) : HasDerivAt h c.re 0 ∧ ((c.re : ℝ) : ℂ) = c := by
  have hre : HasDerivAt (fun τ => (k τ).re) c.re 0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hk
  have him : HasDerivAt (fun τ => (k τ).im) c.im 0 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hk
  have h0 : HasDerivAt (fun τ => (k τ).im) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [he] with τ hτ
    rw [← hτ]
    simp
  refine ⟨hre.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [he] with τ hτ
    rw [← hτ]
    simp
  · apply Complex.ext
    · simp
    · simp [him.unique h0]
end RealForm
section Family
open BlockAverages
variable {F : BlockFrame} {m : ℕ}
def totalOnSpan (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (d : Fin m → ChainChart F) :
    (Fin m → ℂ) → ℂ :=
  fun t => complexTotalOverTop a S R (CellSpans.spanChart (zeroChart F) d t) (complexifyField V)
theorem totalOnSpan_eq_sum (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (d : Fin m → ChainChart F) :
    totalOnSpan a S R V d = fun t => ∑ z ∈ S, cellTermsOnSpan a S R V d z t := by
  funext t
  exact (han F S R V a hodd hamb).1 _
abbrev basisVec (l : Fin m) : Fin m → ℂ := Pi.single l 1
theorem spanChart_two_real (d : Fin m → ChainChart F) (l1 l2 : Fin m) (τ σ : ℝ) :
    CellSpans.spanChart (zeroChart F) d ((τ : ℂ) • basisVec l1 + (σ : ℂ) • basisVec l2) =
      realChart (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ (d l1) τ) (d l2) σ) := by
  classical
  have hre : ∀ l, (((τ : ℂ) • basisVec l1 + (σ : ℂ) • basisVec l2 : Fin m → ℂ) l).re =
      (if l = l1 then τ else 0) + (if l = l2 then σ else 0) := by
    intro l
    simp only [basisVec, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have him : ∀ l, (((τ : ℂ) • basisVec l1 + (σ : ℂ) • basisVec l2 : Fin m → ℂ) l).im = 0 := by
    intro l
    simp only [basisVec, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  unfold CellSpans.spanChart realChart
  congr 1
  · apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp only [chartShiftMulti, zeroChart, chartMove, hre, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add]
    · funext j x i
      simp only [chartShiftMulti, zeroChart, chartMove, hre, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add]
  · apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp only [chartShiftMulti, zeroChart, him, zero_smul]
      simp
    · funext j x i
      simp only [chartShiftMulti, zeroChart, him, zero_smul]
      simp
theorem supWeightedNorm_two_chartMove_le {S : Finset F.Cell} (hL : 0 < F.blockSide) {del : ℝ} (hdel : 0 ≤ del)
    (R : F.FieldChain) (X B : ChainChart F) (τ σ : ℝ) :
    supWeightedNorm S del R (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ X τ) B σ) ≤
      |τ| * supWeightedNorm S del R X + |σ| * supWeightedNorm S del R B := by
  have h1 := CoordinateSeminorms.supWeightedNorm_chartMove_le S hL del hdel R
    (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ X τ) B σ
  have h2 := CoordinateSeminorms.supWeightedNorm_smul S hL del R X τ
  have e : (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) = zeroChart F := rfl
  rw [e] at h1 ⊢
  rw [h2] at h1
  exact h1
theorem dirDeriv_two_totalOnSpan_zero {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {V : F.GaugeField F.top}
    {del c₂ : ℝ} (hL : 0 < F.blockSide) (hdel : 0 ≤ del) (hc₂ : 0 < c₂)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ → ChartIsRegular S R U)
    (d : Fin m → ChainChart F) (l1 l2 : Fin m) (hg : AnalyticAt ℂ (totalOnSpan a S R V d) 0) :
    dirDeriv (dirDeriv (totalOnSpan a S R V d) (basisVec l2)) (basisVec l1) 0 =
      (referenceSecondDeriv a S R V (d l1) (d l2) : ℂ) := by
  set g := totalOnSpan a S R V d with hgd
  set X := d l1 with hX
  set B := d l2 with hB
  have hnX : 0 ≤ supWeightedNorm S del R X := CoordinateSeminorms.supWeightedNorm_nonneg _ _ _ _
  have hnB : 0 ≤ supWeightedNorm S del R B := CoordinateSeminorms.supWeightedNorm_nonneg _ _ _ _
  set ρ := c₂ / (2 * (supWeightedNorm S del R X + supWeightedNorm S del R B + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsmall : ∀ τ σ : ℝ, |τ| < ρ → |σ| < ρ →
      ChartIsRegular S R (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ X τ) B σ) := by
    intro τ σ h1 h2
    refine hreg _ ((supWeightedNorm_two_chartMove_le hL hdel R X B τ σ).trans ?_)
    have h3 : (|τ| + |σ|) * (supWeightedNorm S del R X + supWeightedNorm S del R B + 1) ≤
        (2 * ρ) * (supWeightedNorm S del R X + supWeightedNorm S del R B + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : (2 * ρ) * (supWeightedNorm S del R X + supWeightedNorm S del R B + 1) = c₂ := by
      rw [hρ]
      field_simp
    have := abs_nonneg τ
    have := abs_nonneg σ
    nlinarith
  have hcontE : ∀ᶠ τ : ℝ in 𝓝 0, AnalyticAt ℂ g ((τ : ℂ) • basisVec l1) := by
    have hc : ContinuousAt (fun τ : ℝ => ((τ : ℂ) • basisVec l1 : Fin m → ℂ)) 0 := by fun_prop
    have h0 : (fun τ : ℝ => ((τ : ℂ) • basisVec l1 : Fin m → ℂ)) 0 = 0 := by simp
    refine hc.eventually ?_
    rw [h0]
    exact hg.eventually_analyticAt
  have hinner : ∀ τ : ℝ, |τ| < ρ → AnalyticAt ℂ g ((τ : ℂ) • basisVec l1) →
      ((deriv (fun σ : ℝ => chartAction a S R
        (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ X τ) B σ) V) 0 : ℝ) : ℂ) =
        dirDeriv g (basisVec l2) ((τ : ℂ) • basisVec l1) := by
    intro τ hτ han
    have h1 := hasDerivAt_real_line (f := g) (e := (τ : ℂ) • basisVec l1) (d := basisVec l2) (x := 0)
      (by simpa using han.differentiableAt)
    have e0 : ((τ : ℂ) • basisVec l1 + (((0 : ℝ) : ℂ)) • basisVec l2 : Fin m → ℂ) = (τ : ℂ) • basisVec l1 := by simp
    rw [e0] at h1
    have hev : ∀ᶠ σ : ℝ in 𝓝 0, (chartAction a S R
        (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ X τ) B σ) V : ℂ) =
        g ((τ : ℂ) • basisVec l1 + (σ : ℂ) • basisVec l2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ0] with σ hσ
      have hσ' : |σ| < ρ := by simpa [Real.dist_eq] using hσ
      simp only [hgd, totalOnSpan]
      rw [spanChart_two_real, ComplexChartCoordinates.complexTotalOverTop_realChart a R _ V (hsmall τ σ hτ hσ')]
    obtain ⟨h3, h4⟩ := hasDerivAt_re_of_ofReal_eventuallyEq h1 hev
    rw [h3.deriv, h4]
    rfl
  have hkd := hasDerivAt_real_line (f := dirDeriv g (basisVec l2)) (e := (0 : Fin m → ℂ)) (d := basisVec l1) (x := 0)
    (by simpa using (analyticAt_dirDeriv hg (basisVec l2)).differentiableAt)
  simp only [zero_add, Complex.ofReal_zero, zero_smul] at hkd
  have hev : ∀ᶠ τ : ℝ in 𝓝 0, ((deriv (fun σ : ℝ => chartAction a S R
      (chartMove (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ X τ) B σ) V) 0 : ℝ) : ℂ) =
      dirDeriv g (basisVec l2) ((τ : ℂ) • basisVec l1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ0, hcontE] with τ hτ han
    exact hinner τ (by simpa [Real.dist_eq] using hτ) han
  obtain ⟨h3, h4⟩ := hasDerivAt_re_of_ofReal_eventuallyEq hkd hev
  unfold referenceSecondDeriv
  rw [h3.deriv, h4]
  rfl
end Family
section Five
open BlockAverages
variable {F : BlockFrame}
def fiveDirections (W W' : ComplexChainChart F) (A : ChainChart F) : Fin 5 → ChainChart F :=
  ![W'.re, W'.im, (complexChartSub W W').re, (complexChartSub W W').im, A]
def basePoint : Fin 5 → ℂ := basisVec 0 + Complex.I • basisVec 1
def stepVector : Fin 5 → ℂ := basisVec 2 + Complex.I • basisVec 3
theorem spanChart_basePoint (W W' : ComplexChainChart F) (A : ChainChart F) (τ : ℂ) :
    CellSpans.spanChart (zeroChart F) (fiveDirections W W' A) (basePoint + τ • basisVec 4) =
      complexChartMove W' A τ := by
  unfold CellSpans.spanChart complexChartMove
  congr 1
  · apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, basisVec]
    · funext j x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, basisVec]
  · apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, basisVec]
    · funext j x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, basisVec]
theorem spanChart_basePoint_add_step (W W' : ComplexChainChart F) (A : ChainChart F) (τ : ℂ) :
    CellSpans.spanChart (zeroChart F) (fiveDirections W W' A) (basePoint + stepVector + τ • basisVec 4) =
      complexChartMove W A τ := by
  unfold CellSpans.spanChart complexChartMove
  congr 1
  · apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, stepVector, basisVec,
        complexChartSub]
      module
    · funext j x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, stepVector, basisVec,
        complexChartSub]
      module
  · apply CoordinateSeminorms.chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, stepVector, basisVec,
        complexChartSub]
      module
    · funext j x i
      simp [chartShiftMulti, zeroChart, chartMove, Fin.sum_univ_five, fiveDirections, basePoint, stepVector, basisVec,
        complexChartSub]
      module
variable {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
def pairLocalSize (S : Finset F.Cell) (R : F.FieldChain) (W W' : ComplexChainChart F) (z : F.Cell) : ℝ :=
  localNorm S R W'.re (constOneWeights F) z + localNorm S R W'.im (constOneWeights F) z +
    localNorm S R (complexChartSub W W').re (constOneWeights F) z +
    localNorm S R (complexChartSub W W').im (constOneWeights F) z
theorem pairLocalSize_nonneg (S : Finset F.Cell) (R : F.FieldChain) (W W' : ComplexChainChart F) (z : F.Cell) :
    0 ≤ pairLocalSize S R W W' z := by
  unfold pairLocalSize localNorm
  positivity
theorem spanNorm_basePoint_le (W W' : ComplexChainChart F) (A : ChainChart F) (z : F.Cell) :
    spanNorm S R (fiveDirections W W' A) z basePoint ≤
      localNorm S R W'.re (constOneWeights F) z + localNorm S R W'.im (constOneWeights F) z := by
  refine (spanNorm_add_le S R _ z _ _).trans ?_
  rw [spanNorm_smul, spanNorm_single, spanNorm_single]
  simp [fiveDirections]
theorem spanNorm_stepVector_le (W W' : ComplexChainChart F) (A : ChainChart F) (z : F.Cell) :
    spanNorm S R (fiveDirections W W' A) z stepVector ≤
      localNorm S R (complexChartSub W W').re (constOneWeights F) z +
        localNorm S R (complexChartSub W W').im (constOneWeights F) z := by
  refine (spanNorm_add_le S R _ z _ _).trans ?_
  rw [spanNorm_smul, spanNorm_single, spanNorm_single]
  simp [fiveDirections]
theorem spanNorm_segment_le (W W' : ComplexChainChart F) (A : ChainChart F) (z : F.Cell) {u x : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    spanNorm S R (fiveDirections W W' A) z ((u : ℂ) • (basePoint + (x : ℂ) • stepVector)) ≤
      pairLocalSize S R W W' z := by
  rw [spanNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
  have h1 := spanNorm_add_le S R (fiveDirections W W' A) z basePoint ((x : ℂ) • stepVector)
  rw [spanNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] at h1
  have h2 := spanNorm_basePoint_le (S := S) (R := R) W W' A z
  have h3 := spanNorm_stepVector_le (S := S) (R := R) W W' A z
  have h4 := spanNorm_nonneg S R (fiveDirections W W' A) z stepVector
  have h5 : x * spanNorm S R (fiveDirections W W' A) z stepVector ≤
      1 * spanNorm S R (fiveDirections W W' A) z stepVector :=
    mul_le_mul_of_nonneg_right hx.2 h4
  have h6 : spanNorm S R (fiveDirections W W' A) z (basePoint + (x : ℂ) • stepVector) ≤
      pairLocalSize S R W W' z := by
    unfold pairLocalSize
    linarith
  have h7 := spanNorm_nonneg S R (fiveDirections W W' A) z (basePoint + (x : ℂ) • stepVector)
  calc u * _ ≤ 1 * spanNorm S R (fiveDirections W W' A) z (basePoint + (x : ℂ) • stepVector) :=
        mul_le_mul_of_nonneg_right hu.2 h7
    _ ≤ _ := by linarith
theorem spanNorm_line_le (W W' : ComplexChainChart F) (A : ChainChart F) (z : F.Cell) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    spanNorm S R (fiveDirections W W' A) z (basePoint + (x : ℂ) • stepVector) ≤ pairLocalSize S R W W' z := by
  have := spanNorm_segment_le (S := S) (R := R) W W' A z (u := 1) (by simp) hx
  simpa using this
def thirdDiffBound (L : ℕ) (a del y : ℝ) : ℝ :=
  Analytic.cauchyHalvingConstant 1 * secondDiffBound L a del * (12 / y)
set_option maxHeartbeats 1000000 in
theorem norm_cellTerms_firstVariation_sub_le (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top) {z : F.Cell} (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (W W' : ComplexChainChart F) (A : ChainChart F) {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8) (p : F.Site 0)
    (hs : pairLocalSize S R W W' z ≤ y / 2) :
    ‖dirDeriv (cellTermsOnSpan a S R V (fiveDirections W W' A) z) (basisVec 4) (basePoint + stepVector) -
        dirDeriv (cellTermsOnSpan a S R V (fiveDirections W W' A) z) (basisVec 4) basePoint -
        dirDeriv (dirDeriv (cellTermsOnSpan a S R V (fiveDirections W W' A) z) (basisVec 4)) stepVector 0‖ ≤
      thirdDiffBound F.blockSide a del y * pairLocalSize S R W W' z *
        (localNorm S R (complexChartSub W W').re (classWeight F φ θ p) z +
          localNorm S R (complexChartSub W W').im (classWeight F φ θ p) z) *
        localNorm S R A (invertedWeights (classWeight F φ θ p)) z := by
  have hy0 : 0 < y := ctx.small.pos
  set d := fiveDirections W W' A with hd
  set G := cellTermsOnSpan a S R V d z with hG
  set Nz := pairLocalSize S R W W' z with hNz
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      spanNorm S R d z ((u : ℂ) • (basePoint + (x : ℂ) • stepVector)) ≤ y / 2 := fun u hu x hx =>
    (spanNorm_segment_le W W' A z hu hx).trans hs
  have han' : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℂ G ((u : ℂ) • (basePoint + (x : ℂ) • stepVector)) :=
    fun u hu x hx => analyticAt_cellTermsOnSpan han hamb hodd a V ctx d ((hpt u hu x hx).trans (by linarith))
  have ht := norm_taylor_remainder_le (f := G) (e' := basePoint) (d := stepVector) (a := basisVec 4)
    (B := thirdDiffBound F.blockSide a del y * Nz *
      (localNorm S R (complexChartSub W W').re (classWeight F φ θ p) z +
        localNorm S R (complexChartSub W W').im (classWeight F φ θ p) z) *
      localNorm S R A (invertedWeights (classWeight F φ θ p)) z) han' ?_
  · exact ht
  intro u hu x hx
  have hq := spanNorm_line_le (S := S) (R := R) W W' A z hx
  set q := basePoint + (x : ℂ) • stepVector with hqd
  have hcomb := dirDeriv_three_add_smul (f := G) (t := (u : ℂ) • q) (basisVec 4) (basisVec 2) (basisVec 3) q
    (han' u hu x hx) Complex.I
  have e0 : dirDeriv (dirDeriv (dirDeriv G (basisVec 4)) stepVector) q ((u : ℂ) • q) =
      dirDeriv (dirDeriv (dirDeriv G (basisVec 4)) (basisVec 2)) q ((u : ℂ) • q) +
        Complex.I * dirDeriv (dirDeriv (dirDeriv G (basisVec 4)) (basisVec 3)) q ((u : ℂ) • q) := hcomb
  rw [e0]
  have b2 := norm_dirDeriv_three_le (a := a) hmix han hamb hodd h2 V ctx d 2 4 hdel hφ hθ p (hpt u hu x hx) q
  have b3 := norm_dirDeriv_three_le (a := a) hmix han hamb hodd h2 V ctx d 3 4 hdel hφ hθ p (hpt u hu x hx) q
  have hs0 := secondDiffBound_nonneg hodd a del
  have hc1 := Analytic.cauchyHalvingConstant_pos 1
  have nn : ∀ (U : ChainChart F) (w : F.SiteWeights), 0 ≤ localNorm S R U w z := fun _ _ => Real.sqrt_nonneg _
  have hfac : (12 / y * (spanNorm S R d z q + 0)) ≤ 12 / y * Nz := by
    rw [add_zero]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have b2' : ‖dirDeriv (dirDeriv (dirDeriv G (basisVec 4)) (basisVec 2)) q ((u : ℂ) • q)‖ ≤
      thirdDiffBound F.blockSide a del y * Nz * localNorm S R (complexChartSub W W').re (classWeight F φ θ p) z *
        localNorm S R A (invertedWeights (classWeight F φ θ p)) z := by
    refine b2.trans ?_
    have h3 := mul_le_mul_of_nonneg_left hfac (mul_nonneg hc1.le
      (mul_nonneg (mul_nonneg hs0 (nn (d 2) (classWeight F φ θ p))) (nn (d 4) (invertedWeights (classWeight F φ θ p)))))
    refine h3.trans (le_of_eq ?_)
    have e2 : d 2 = (complexChartSub W W').re := rfl
    have e4 : d 4 = A := rfl
    rw [e2, e4]
    unfold thirdDiffBound
    ring
  have b3' : ‖dirDeriv (dirDeriv (dirDeriv G (basisVec 4)) (basisVec 3)) q ((u : ℂ) • q)‖ ≤
      thirdDiffBound F.blockSide a del y * Nz * localNorm S R (complexChartSub W W').im (classWeight F φ θ p) z *
        localNorm S R A (invertedWeights (classWeight F φ θ p)) z := by
    refine b3.trans ?_
    have h3 := mul_le_mul_of_nonneg_left hfac (mul_nonneg hc1.le
      (mul_nonneg (mul_nonneg hs0 (nn (d 3) (classWeight F φ θ p))) (nn (d 4) (invertedWeights (classWeight F φ θ p)))))
    refine h3.trans (le_of_eq ?_)
    have e2 : d 3 = (complexChartSub W W').im := rfl
    have e4 : d 4 = A := rfl
    rw [e2, e4]
    unfold thirdDiffBound
    ring
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  calc _ ≤ _ := add_le_add b2' b3'
    _ = _ := by ring
end Five
section Total
open BlockAverages
variable {F : BlockFrame}
variable {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
theorem hasDerivAt_complex_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → ℂ} {t : E} (a₀ : E)
    (h : DifferentiableAt ℂ g t) : HasDerivAt (fun τ : ℂ => g (t + τ • a₀)) (dirDeriv g a₀ t) 0 := by
  have hl : HasDerivAt (fun τ : ℂ => t + τ • a₀) a₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const a₀).const_add t
  have e : t + (0 : ℂ) • a₀ = t := by simp
  have hf : HasFDerivAt g (fderiv ℂ g t) (t + (0 : ℂ) • a₀) := by
    rw [e]
    exact h.hasFDerivAt
  exact hf.comp_hasDerivAt (0 : ℂ) hl
set_option maxHeartbeats 1000000 in
theorem norm_total_firstVariation_sub_le (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top)
    (hctx : ∀ z ∈ S, CellSpans.CellHypotheses S z R C₀ s y) (hy : 0 < y)
    (W W' : ComplexChainChart F) (A : ChainChart F) {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {Ns : ℝ}
    (hNs0 : 0 ≤ Ns) (hNs : ∀ z ∈ S, pairLocalSize S R W W' z ≤ Ns) (hsm : Ns ≤ y / 2) :
    ‖dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4) (basePoint + stepVector) -
        dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4) basePoint -
        dirDeriv (dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4)) stepVector 0‖ ≤
      thirdDiffBound F.blockSide a del y * Ns * complexWeightedNorm S R (complexChartSub W W') (classWeight F φ θ p) *
        weightedNorm S R A (invertedWeights (classWeight F φ θ p)) := by
  classical
  set d := fiveDirections W W' A with hd
  have hpt : ∀ z ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℂ (cellTermsOnSpan a S R V d z) ((u : ℂ) • (basePoint + (x : ℂ) • stepVector)) := fun z hz u hu x hx =>
    analyticAt_cellTermsOnSpan han hamb hodd a V (hctx z hz) d
      (((spanNorm_segment_le W W' A z hu hx).trans (hNs z hz)).trans (by linarith))
  have h11 : ∀ z ∈ S, AnalyticAt ℂ (cellTermsOnSpan a S R V d z) (basePoint + stepVector) := fun z hz => by
    simpa using hpt z hz 1 (by simp) 1 (by simp)
  have h10 : ∀ z ∈ S, AnalyticAt ℂ (cellTermsOnSpan a S R V d z) basePoint := fun z hz => by
    simpa using hpt z hz 1 (by simp) 0 (by simp)
  have h00 : ∀ z ∈ S, AnalyticAt ℂ (cellTermsOnSpan a S R V d z) 0 := fun z hz => by
    simpa using hpt z hz 0 (by simp) 0 (by simp)
  rw [totalOnSpan_eq_sum han hamb hodd, dirDeriv_sum S _ _ fun z hz => (h11 z hz).differentiableAt,
    dirDeriv_sum S _ _ fun z hz => (h10 z hz).differentiableAt, dirDeriv_two_sum S _ _ _ h00,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  set w := classWeight F φ θ p with hw
  set wi := invertedWeights w with hwi
  set X := (complexChartSub W W').re with hX
  set Y := (complexChartSub W W').im with hY
  have hthird : 0 ≤ thirdDiffBound F.blockSide a del y := by
    have h1 := Analytic.cauchyHalvingConstant_pos 1
    have h3 := secondDiffBound_nonneg hodd a del
    unfold thirdDiffBound
    positivity
  have hterm : ∀ z ∈ S, ‖dirDeriv (cellTermsOnSpan a S R V d z) (basisVec 4) (basePoint + stepVector) -
      dirDeriv (cellTermsOnSpan a S R V d z) (basisVec 4) basePoint -
      dirDeriv (dirDeriv (cellTermsOnSpan a S R V d z) (basisVec 4)) stepVector 0‖ ≤
        thirdDiffBound F.blockSide a del y * Ns *
          (localNorm S R X w z * localNorm S R A wi z + localNorm S R Y w z * localNorm S R A wi z) := by
    intro z hz
    have h1 := norm_cellTerms_firstVariation_sub_le (a := a) hmix han hamb hodd h2 V (hctx z hz) W W' A hdel hφ hθ p
      ((hNs z hz).trans hsm)
    refine h1.trans ?_
    have h3 : 0 ≤ (localNorm S R X w z + localNorm S R Y w z) * localNorm S R A wi z :=
      mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hNs z hz) hthird) h3
    calc _ = thirdDiffBound F.blockSide a del y * pairLocalSize S R W W' z *
          ((localNorm S R X w z + localNorm S R Y w z) * localNorm S R A wi z) := by
          ring
      _ ≤ _ := h4
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have c1 : ∑ z ∈ S, localNorm S R X w z * localNorm S R A wi z ≤ weightedNorm S R X w * weightedNorm S R A wi :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have c2 : ∑ z ∈ S, localNorm S R Y w z * localNorm S R A wi z ≤ weightedNorm S R Y w * weightedNorm S R A wi :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h5 := mul_le_mul_of_nonneg_left (add_le_add c1 c2) (mul_nonneg hthird hNs0)
  refine h5.trans (le_of_eq ?_)
  have e : complexWeightedNorm S R (complexChartSub W W') w = weightedNorm S R X w + weightedNorm S R Y w := rfl
  rw [e]
  ring
theorem complexFirstVariation_eq_dirDeriv_top {V : F.GaugeField F.top} (W W' : ComplexChainChart F) (A : ChainChart F)
    (h : DifferentiableAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) (basePoint + stepVector)) :
    complexFirstVariation a S R W (complexifyField V) A =
      dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4) (basePoint + stepVector) := by
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W A τ) (complexifyField V)) =
      fun τ : ℂ => totalOnSpan a S R V (fiveDirections W W' A) (basePoint + stepVector + τ • basisVec 4) := by
    funext τ
    simp only [totalOnSpan, spanChart_basePoint_add_step]
  rw [e]
  exact (hasDerivAt_complex_line (basisVec 4) h).deriv
theorem complexFirstVariation_eq_dirDeriv_base {V : F.GaugeField F.top} (W W' : ComplexChainChart F) (A : ChainChart F)
    (h : DifferentiableAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) basePoint) :
    complexFirstVariation a S R W' (complexifyField V) A =
      dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4) basePoint := by
  unfold complexFirstVariation
  have e : (fun τ : ℂ => complexTotalOverTop a S R (complexChartMove W' A τ) (complexifyField V)) =
      fun τ : ℂ => totalOnSpan a S R V (fiveDirections W W' A) (basePoint + τ • basisVec 4) := by
    funext τ
    simp only [totalOnSpan, spanChart_basePoint]
  rw [e]
  exact (hasDerivAt_complex_line (basisVec 4) h).deriv
theorem dirDeriv_two_stepVector_eq_referenceForm {V : F.GaugeField F.top} {del c₂ : ℝ} (hL : 0 < F.blockSide)
    (hdel : 0 ≤ del) (hc₂ : 0 < c₂)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ → ChartIsRegular S R U)
    (W W' : ComplexChainChart F) (A : ChainChart F)
    (hg : AnalyticAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) 0) :
    dirDeriv (dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4)) stepVector 0 =
      complexReferenceSecondDeriv a S R V (complexChartSub W W') A := by
  have h2 := dirDeriv_two_totalOnSpan_zero hL hdel hc₂ hreg (fiveDirections W W' A) 2 4 hg
  have h3 := dirDeriv_two_totalOnSpan_zero hL hdel hc₂ hreg (fiveDirections W W' A) 3 4 hg
  have e : dirDeriv (dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4)) stepVector 0 =
      dirDeriv (dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4)) (basisVec 2) 0 +
        Complex.I * dirDeriv (dirDeriv (totalOnSpan a S R V (fiveDirections W W' A)) (basisVec 4)) (basisVec 3) 0 := by
    simp [dirDeriv, stepVector]
  rw [e, h2, h3]
  rfl
end Total
section Basis
open BlockAverages
theorem mem_unitary_of_sum_sq {q : ℍ[ℝ]} (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    q ∈ unitary ℍ[ℝ] := by
  refine ⟨?_, ?_⟩
  · rw [Quaternion.star_mul_self, Quaternion.normSq_def', h]
    simp
  · rw [Quaternion.self_mul_star, Quaternion.normSq_def', h]
    simp
def quatI : UnitQuaternion := ⟨⟨0, 1, 0, 0⟩, mem_unitary_of_sum_sq (by simp)⟩
def quatJ : UnitQuaternion := ⟨⟨0, 0, 1, 0⟩, mem_unitary_of_sum_sq (by simp)⟩
def quatK : UnitQuaternion := ⟨⟨0, 0, 0, 1⟩, mem_unitary_of_sum_sq (by simp)⟩
def quatBasis : Fin 4 → UnitQuaternion := ![1, quatI, quatJ, quatK]
theorem ofUnit_neg (g : UnitQuaternion) : ofUnit (-g) = -ofUnit g := by
  have h : ComplexifiedQuaternions.ofQuat (-(g : ℍ[ℝ])) = -ComplexifiedQuaternions.ofQuat (g : ℍ[ℝ]) := by
    have := ComplexifiedQuaternions.ofQuat_smul (-1) (g : ℍ[ℝ])
    simpa using this
  have e : ((-g : UnitQuaternion) : ℍ[ℝ]) = -(g : ℍ[ℝ]) := rfl
  simp only [ofUnit, e, h]
theorem eq_smul_sum_trace_mul_adjugate (M : ComplexifiedQuaternions.ComplexQuat) :
    M = (1 / 2 : ℂ) • ∑ r, (M * Matrix.adjugate (ofUnit (quatBasis r))).trace • ofUnit (quatBasis r) := by
  have e0 : ofUnit (quatBasis 0) = !![1, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofUnit, ComplexifiedQuaternions.ofQuat, quatBasis, Complex.ext_iff]
  have e1 : ofUnit (quatBasis 1) = !![Complex.I, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofUnit, ComplexifiedQuaternions.ofQuat, quatBasis, quatI, Complex.ext_iff]
  have e2 : ofUnit (quatBasis 2) = !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofUnit, ComplexifiedQuaternions.ofQuat, quatBasis, quatJ, Complex.ext_iff]
  have e3 : ofUnit (quatBasis 3) = !![0, Complex.I; Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofUnit, ComplexifiedQuaternions.ofQuat, quatBasis, quatK, Complex.ext_iff]
  rw [Fin.sum_univ_four, e0, e1, e2, e3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp <;> ring
end Basis
section Means
open BlockAverages
variable {F : BlockFrame} {m : ℕ}
variable {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
def updateBond (V : F.GaugeField F.top) (b : F.Site F.top × Fin 4) (g : UnitQuaternion) : F.GaugeField F.top := by
  classical exact fun y i => if (y, i) = b then g else V y i
theorem complexBondTerm_eq_of_lt_top (R : F.FieldChain) (W : ComplexChainChart F) (V V' : F.GaugeField F.top) {j : ℕ}
    (hj₁ : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) :
    complexBondTerm R W V j c = complexBondTerm R W V' j c := by
  have hj' : j ≠ F.top := by omega
  have hj : j + 1 ≠ F.top := by omega
  simp only [complexBondTerm, ComplexBondTerms.complexFieldChain_of_ne R W V hj',
    ComplexBondTerms.complexFieldChain_of_ne R W V' hj', ComplexBondTerms.complexFieldChain_of_ne R W V hj,
    ComplexBondTerms.complexFieldChain_of_ne R W V' hj]
theorem complexBondTerm_depth (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top)
    (c : F.Site (F.depth + 1) × Fin 4) :
    complexBondTerm R W V F.depth c = complexBlockFit (topBondGaugedAverage R W c) (ofUnit (V c.1 c.2)) := by
  have hne : F.depth ≠ F.top := by
    have : F.top = F.depth + 1 := rfl
    omega
  have e : complexFieldChain R W V (F.depth + 1) = complexifyField V := by
    show complexFieldChain R W V F.top = complexifyField V
    simp [complexFieldChain]
  simp only [complexBondTerm, ComplexBondTerms.complexFieldChain_of_ne R W V hne, e]
  rfl
theorem complexCellTerms_updateBond_sub (a : ℝ) (R : F.FieldChain) (W : ComplexChainChart F) (V : F.GaugeField F.top)
    {b : F.Site F.top × Fin 4} {z : F.Cell} (hb : b ∈ bondsOver S {z} F.top) (g g' : UnitQuaternion) :
    complexCellTerms a S R W (updateBond V b g') z - complexCellTerms a S R W (updateBond V b g) z =
      a * (complexBlockFit (topBondGaugedAverage R W b) (ofUnit g') -
        complexBlockFit (topBondGaugedAverage R W b) (ofUnit g)) := by
  classical
  unfold complexCellTerms
  have hn : Finset.range F.top = Finset.range (F.depth + 1) := rfl
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
  have hlow : ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTerm R W (updateBond V b g') j c =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1), complexBondTerm R W (updateBond V b g) j c := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => complexBondTerm_eq_of_lt_top R W _ _ ?_ c
    have h1 := Finset.mem_range.1 hj
    have : F.top = F.depth + 1 := rfl
    omega
  have htop : ∑ c ∈ bondsOver S {z} (F.depth + 1), complexBondTerm R W (updateBond V b g') F.depth c -
      ∑ c ∈ bondsOver S {z} (F.depth + 1), complexBondTerm R W (updateBond V b g) F.depth c =
      complexBlockFit (topBondGaugedAverage R W b) (ofUnit g') -
        complexBlockFit (topBondGaugedAverage R W b) (ofUnit g) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem b hb]
    · rw [complexBondTerm_depth, complexBondTerm_depth]
      have e1 : ∀ g₀ : UnitQuaternion, updateBond V b g₀ b.1 b.2 = g₀ := fun g₀ => by
        simp [updateBond]
      rw [e1, e1]
    · intro c _ hc
      rw [complexBondTerm_depth, complexBondTerm_depth]
      have e1 : ∀ g₀ : UnitQuaternion, updateBond V b g₀ c.1 c.2 = V c.1 c.2 := fun g₀ => by
        have : (c.1, c.2) ≠ b := hc
        simp [updateBond, this]
      rw [e1, e1, sub_self]
  linear_combination (a : ℂ) * htop + (a : ℂ) * hlow
theorem complexBlockFit_neg_sub (M : ComplexifiedQuaternions.ComplexQuat) (g : UnitQuaternion) :
    complexBlockFit M (ofUnit (-g)) - complexBlockFit M (ofUnit g) = (M * Matrix.adjugate (ofUnit g)).trace := by
  have e : Matrix.adjugate (-ofUnit g) = -Matrix.adjugate (ofUnit g) := by
    have := ComplexifiedQuaternions.adjugate_map_smul (-1) (ofUnit g)
    simpa using this
  simp only [complexBlockFit, ofUnit_neg, e, mul_neg, Matrix.trace_neg]
  ring
def traceProbe (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (d : Fin m → ChainChart F)
    (z : F.Cell) (b : F.Site F.top × Fin 4) (r : Fin 4) : (Fin m → ℂ) → ℂ :=
  fun t => (a : ℂ)⁻¹ * (cellTermsOnSpan a S R (updateBond V b (-quatBasis r)) d z t -
    cellTermsOnSpan a S R (updateBond V b (quatBasis r)) d z t)
theorem topBondGaugedAverage_eq_sum_traceProbe (ha : a ≠ 0) (V : F.GaugeField F.top) (d : Fin m → ChainChart F)
    {z : F.Cell} {b : F.Site F.top × Fin 4} (hb : b ∈ bondsOver S {z} F.top) (t : Fin m → ℂ) :
    topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d t) b =
      (1 / 2 : ℂ) • ∑ r, traceProbe a S R V d z b r t • ofUnit (quatBasis r) := by
  have h := eq_smul_sum_trace_mul_adjugate (topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d t) b)
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have e : ∀ r, (topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d t) b *
      Matrix.adjugate (ofUnit (quatBasis r))).trace = traceProbe a S R V d z b r t := by
    intro r
    unfold traceProbe
    have h1 := complexCellTerms_updateBond_sub (S := S) a R (CellSpans.spanChart (zeroChart F) d t) V hb
      (quatBasis r) (-quatBasis r)
    rw [complexBlockFit_neg_sub] at h1
    simp only [cellTermsOnSpan]
    rw [h1]
    field_simp
  simp only [e] at h
  exact h
theorem analyticAt_traceProbe (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (V : F.GaugeField F.top) {z : F.Cell} (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (d : Fin m → ChainChart F) (b : F.Site F.top × Fin 4) (r : Fin 4) {t₀ : Fin m → ℂ}
    (hsz : CellNormBounds.SourceBounds S z R (CellSpans.spanChart (zeroChart F) d t₀) y) :
    AnalyticAt ℂ (traceProbe a S R V d z b r) t₀ :=
  analyticAt_const.mul ((analyticAt_cellTermsOnSpan_of_sourceBounds han hamb hodd a _ ctx d hsz).sub
    (analyticAt_cellTermsOnSpan_of_sourceBounds han hamb hodd a _ ctx d hsz))
theorem analyticAt_topBondGaugedAverage (ha : a ≠ 0) (han : complexCellTermsAnalyticStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (V : F.GaugeField F.top) {z : F.Cell}
    (ctx : CellSpans.CellHypotheses S z R C₀ s y) (d : Fin m → ChainChart F) {b : F.Site F.top × Fin 4}
    (hb : b ∈ bondsOver S {z} F.top) {t₀ : Fin m → ℂ}
    (hsz : CellNormBounds.SourceBounds S z R (CellSpans.spanChart (zeroChart F) d t₀) y) :
    AnalyticAt ℂ (fun t => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d t) b) t₀ := by
  have e : (fun t => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d t) b) =
      fun t => (1 / 2 : ℂ) • ∑ r, traceProbe a S R V d z b r t • ofUnit (quatBasis r) :=
    funext fun t => topBondGaugedAverage_eq_sum_traceProbe ha V d hb t
  rw [e]
  refine ComplexAnalyticity.analyticAt_const_smul_complexQuat (1 / 2 : ℂ)
    (Finset.analyticAt_fun_sum _ fun r _ => ?_)
  exact AnalyticAt.smul (analyticAt_traceProbe han hamb hodd V ctx d b r hsz)
    (analyticAt_const (v := ofUnit (quatBasis r)))
theorem hasDerivAt_topBondGaugedAverage (ha : a ≠ 0) (V : F.GaugeField F.top) (d : Fin m → ChainChart F)
    {z : F.Cell} {b : F.Site F.top × Fin 4} (hb : b ∈ bondsOver S {z} F.top) (t e : Fin m → ℂ)
    (hd : ∀ r, DifferentiableAt ℂ (traceProbe a S R V d z b r) t) :
    HasDerivAt (fun τ : ℂ => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d (t + τ • e)) b)
      ((1 / 2 : ℂ) • ∑ r, dirDeriv (traceProbe a S R V d z b r) e t • ofUnit (quatBasis r)) 0 := by
  have e1 : (fun τ : ℂ => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d (t + τ • e)) b) =
      fun τ : ℂ => (1 / 2 : ℂ) • ∑ r, traceProbe a S R V d z b r (t + τ • e) • ofUnit (quatBasis r) :=
    funext fun τ => topBondGaugedAverage_eq_sum_traceProbe ha V d hb _
  rw [e1]
  have hs : HasDerivAt (fun τ : ℂ => ∑ r, traceProbe a S R V d z b r (t + τ • e) • ofUnit (quatBasis r))
      (∑ r, dirDeriv (traceProbe a S R V d z b r) e t • ofUnit (quatBasis r)) 0 :=
    HasDerivAt.fun_sum fun r _ => (hasDerivAt_complex_line e (hd r)).smul_const (ofUnit (quatBasis r))
  exact hs.const_smul (1 / 2 : ℂ)
theorem dirDeriv_const_mul_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f₁ f₂ : E → ℂ} (c : ℂ) (e : E)
    {t : E} (h₁ : DifferentiableAt ℂ f₁ t) (h₂ : DifferentiableAt ℂ f₂ t) :
    dirDeriv (fun t => c * (f₂ t - f₁ t)) e t = c * (dirDeriv f₂ e t - dirDeriv f₁ e t) := by
  have hf : HasFDerivAt (fun t => c * (f₂ t - f₁ t)) (c • (fderiv ℂ f₂ t - fderiv ℂ f₁ t)) t :=
    (h₂.hasFDerivAt.sub h₁.hasFDerivAt).const_mul c
  show fderiv ℂ (fun t => c * (f₂ t - f₁ t)) t e = _
  rw [hf.fderiv]
  simp [dirDeriv]
theorem dirDeriv_two_const_mul_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f₁ f₂ : E → ℂ} (c : ℂ) (e e' : E) {t : E} (h₁ : AnalyticAt ℂ f₁ t) (h₂ : AnalyticAt ℂ f₂ t) :
    dirDeriv (dirDeriv (fun t => c * (f₂ t - f₁ t)) e) e' t =
      c * (dirDeriv (dirDeriv f₂ e) e' t - dirDeriv (dirDeriv f₁ e) e' t) := by
  have h : dirDeriv (fun t => c * (f₂ t - f₁ t)) e =ᶠ[𝓝 t] fun t => c * (dirDeriv f₂ e t - dirDeriv f₁ e t) := by
    filter_upwards [h₁.eventually_analyticAt, h₂.eventually_analyticAt] with t' a₁ a₂
    exact dirDeriv_const_mul_sub c e a₁.differentiableAt a₂.differentiableAt
  show fderiv ℂ _ t e' = _
  rw [h.fderiv_eq]
  exact dirDeriv_const_mul_sub c e' (analyticAt_dirDeriv h₁ e).differentiableAt
    (analyticAt_dirDeriv h₂ e).differentiableAt
theorem norm_dirDeriv_two_stepVector_le (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top) {z : F.Cell} (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    (W W' : ComplexChainChart F) (A : ChainChart F) {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) {p₀ : Fin 5 → ℂ}
    (hp : spanNorm S R (fiveDirections W W' A) z p₀ ≤ y / 2) :
    ‖dirDeriv (dirDeriv (cellTermsOnSpan a S R V (fiveDirections W W' A) z) (basisVec 4)) stepVector p₀‖ ≤
      Analytic.cauchyHalvingConstant 0 * secondDiffBound F.blockSide a del *
        (localNorm S R (complexChartSub W W').re (classWeight F φ θ p) z +
          localNorm S R (complexChartSub W W').im (classWeight F φ θ p) z) *
        localNorm S R A (invertedWeights (classWeight F φ θ p)) z := by
  set G := cellTermsOnSpan a S R V (fiveDirections W W' A) z with hG
  have e : dirDeriv (dirDeriv G (basisVec 4)) stepVector p₀ =
      dirDeriv (dirDeriv G (basisVec 4)) (basisVec 2) p₀ +
        Complex.I * dirDeriv (dirDeriv G (basisVec 4)) (basisVec 3) p₀ := by
    simp [dirDeriv, stepVector]
  rw [e]
  have b2 := norm_dirDeriv_two_le (a := a) hmix han hamb hodd h2 V ctx (fiveDirections W W' A) 2 4 hdel hφ hθ p hp
  have b3 := norm_dirDeriv_two_le (a := a) hmix han hamb hodd h2 V ctx (fiveDirections W W' A) 3 4 hdel hφ hθ p hp
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  calc _ ≤ _ := add_le_add b2 b3
    _ = _ := by
      have e2 : fiveDirections W W' A 2 = (complexChartSub W W').re := rfl
      have e3 : fiveDirections W W' A 3 = (complexChartSub W W').im := rfl
      have e4 : fiveDirections W W' A 4 = A := rfl
      rw [e2, e3, e4]
      ring
end Means
section Bounds
open BlockAverages
variable {F : BlockFrame} {m : ℕ}
variable {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
set_option maxHeartbeats 1000000 in
theorem norm_topBondGaugedAverage_le (hodd : Odd F.blockSide) {z : F.Cell}
    (ctx : CellSpans.CellHypotheses S z R C₀ s y) {W : ComplexChainChart F}
    (hsz : CellNormBounds.SourceBounds S z R W y) {b : F.Site (F.depth + 1) × Fin 4}
    (hb : b ∈ innerBonds (cellBall S z 1) (F.depth + 1)) :
    ‖topBondGaugedAverage R W b‖ ≤ 9 := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  obtain ⟨-, hball⟩ := CellSources.deviationBall_of_finsetLpNorm_le (ctx.level_le W) hsz.base_le hsz.upper_le
    (by linarith)
  have hH0 := ComplexCells.hullBondCount_nonneg F.blockSide
  set yv := ComplexLevels.levelDeviation R W F.depth with hyv
  set h := ComplexRemainders.bondHullNorm b yv with hh
  have hh0 : 0 ≤ h := ComplexRemainders.bondHullSum_nonneg _ fun _ _ => norm_nonneg _
  have hhle : h ≤ ComplexLevels.hullBondCount F.blockSide * (8 * y) :=
    hball.bondHullNorm_le hodd (by positivity) (Nat.lt_succ_self _) hb
  have ha := hy.count_le_radius
  have hsmall : 8 * (F.blockSide : ℝ) * (ComplexLevels.hullBondCount F.blockSide * (8 * y)) ≤ 1 / 1024 := by
    have h1 : 48 * (48 * ComplexLevels.hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) ≤ 1 := by
      unfold ComplexDifferences.hullBallRadius at ha
      rw [le_div_iff₀ (by positivity)] at ha
      exact ha
    have h2 : 0 ≤ ComplexLevels.hullBondCount F.blockSide * y * F.blockSide := by positivity
    have e1 : 48 * (48 * ComplexLevels.hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) =
        48 * 48 * 8192 * (ComplexLevels.hullBondCount F.blockSide * y * F.blockSide) +
          48 * 8192 * (y * F.blockSide) := by ring
    have h3 : 0 ≤ y * (F.blockSide : ℝ) := by positivity
    have e2 : 8 * (F.blockSide : ℝ) * (ComplexLevels.hullBondCount F.blockSide * (8 * y)) =
        64 * (ComplexLevels.hullBondCount F.blockSide * y * F.blockSide) := by ring
    rw [e2]
    rw [e1] at h1
    linarith
  have hsm : 8 * (F.blockSide : ℝ) * h ≤ 1 / 1024 :=
    (mul_le_mul_of_nonneg_left hhle (by positivity)).trans hsmall
  have e0 : (1 / (F.blockSide : ℝ)) ^ (F.top - (F.depth + 1)) = 1 := by
    have : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
    rw [this, pow_zero]
  set σ := C₀ * s with hσd
  have hσ0 : 0 ≤ σ := mul_nonneg ctx.const_pos.le ctx.scale_pos.le
  have hσy : σ ≤ y := ctx.const_mul_scale_le
  have hσ : σ ≤ 1 / 64 := by linarith
  have href : ∀ g ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R F.depth) (refineSite b.1) (bondContour F.blockSide g π b.2) *
        (polarUnit (contourAverage (R F.depth) b))⁻¹) - 1‖ ≤ σ := fun g hg π => by
    have h1 := ctx.near F.depth le_rfl b hb g hg π
    rw [e0] at h1
    simpa using h1
  obtain ⟨hpos, hq, hρ⟩ := ComplexRemainders.remainder_bounds hodd le_rfl hσ hsm href
  set K : ℝ := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hKH : K * h ≤ 1 / 72 := by
    have h1 := hy.scaled_count_le
    have h2 : K * h ≤ K * (ComplexLevels.hullBondCount F.blockSide * (8 * y)) := mul_le_mul_of_nonneg_left hhle hK0
    have h3 : 0 ≤ K * y := by positivity
    nlinarith
  have hh1 : h ≤ 1 / 8 := by
    have h1 := hy.count_le
    nlinarith
  have hKs : K * (h ^ 2 + σ * h) ≤ 1 := by
    have e : K * (h ^ 2 + σ * h) = (K * h) * (h + σ) := by ring
    rw [e]
    have h2 : 0 ≤ K * h := by positivity
    have h3 : h + σ ≤ 1 := by linarith
    have h4 : 0 ≤ h + σ := by positivity
    nlinarith
  have hd : ComplexLevels.HoldsOnHull b (fun x i => (complexChartField R W F.depth x i).det = 1) :=
    ComplexLevels.holdsOnHull_of_innerBonds (Nat.lt_succ_self _) hodd hb fun b' hb' =>
      ComplexLevels.det_complexChartField_of_norm_lt_one R W F.depth _ _
        (lt_of_le_of_lt (hball.norm_deviation_le F.depth (Nat.lt_succ_self _) b' hb') (by linarith))
  have hM : topBondGaugedAverage R W b = ComplexRemainders.liftedBondMean (R F.depth) b yv :=
    ComplexLevels.complexGaugedContourAverage_eq_liftedBondMean hodd le_rfl hd
  set M := ComplexRemainders.liftedBondMean (R F.depth) b yv with hMd
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  set r₀ : ℝ := ‖contourAverage (R F.depth) b‖ with hr₀
  set w : UnitQuaternion := polarUnit (contourAverage (R F.depth) b) with hw
  set q := ComplexRemainders.unitRemainder (R F.depth) b yv with hqd
  set ρ := ComplexRemainders.sqrtRemainder (R F.depth) b yv with hρd
  set P := ComplexifiedQuaternions.purePart (ComplexContours.transportedAverage (R F.depth) yv b) with hP
  have e1 : ComplexifiedQuaternions.unitPart M * ofUnit w⁻¹ = 1 + P + q := by
    rw [hqd, ComplexRemainders.unitRemainder]
    abel
  have e2 : ComplexifiedQuaternions.principalSqrt M.det = (r₀ : ℂ) + ρ := by
    rw [hρd, ComplexRemainders.sqrtRemainder]
    abel
  have e4 : M * ofUnit w⁻¹ = ((r₀ : ℂ) + ρ) • (1 + P + q) := by
    calc M * ofUnit w⁻¹ =
          (ComplexifiedQuaternions.principalSqrt M.det • ComplexifiedQuaternions.unitPart M) * ofUnit w⁻¹ := by
          rw [ComplexChainStep.principalSqrt_det_smul_unitPart hM0]
      _ = ComplexifiedQuaternions.principalSqrt M.det • (ComplexifiedQuaternions.unitPart M * ofUnit w⁻¹) :=
          smul_mul_assoc _ _ _
      _ = _ := by rw [e1, e2]
  have hP1 : ‖P‖ ≤ h :=
    (ComplexifiedQuaternions.norm_purePart_le _).trans ((ComplexChainStep.norm_transportedAverage_le hodd _ _ b).trans
      (ComplexDifferences.lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) b))
  have hr1 : |r₀ - 1| ≤ σ := ComplexChainStep.abs_norm_contourAverage_sub_one_le hodd href
  have hr2 : ‖(r₀ : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := abs_le.1 hr1
    rw [abs_le]
    constructor <;> linarith
  have hX : ‖1 + P + q‖ ≤ 3 := by
    have h1 := norm_add_le (1 + P) q
    have h2 := norm_add_le (1 : ComplexifiedQuaternions.ComplexQuat) P
    rw [CStarRing.norm_one] at h2
    linarith
  have hR : ‖(r₀ : ℂ) + ρ‖ ≤ 3 := by
    have := norm_add_le (r₀ : ℂ) ρ
    linarith
  rw [hM]
  have h5 : ‖M‖ = ‖M * ofUnit w⁻¹‖ := (norm_mul_ofUnit _ _).symm
  rw [h5, e4, norm_smul]
  have := mul_le_mul hR hX (norm_nonneg _) (by norm_num)
  linarith
theorem norm_ofUnit_quatBasis (r : Fin 4) : ‖ofUnit (quatBasis r)‖ = 1 := by
  rw [ofUnit, ComplexifiedQuaternions.norm_ofQuat]
  exact CStarRing.norm_coe_unitary _
set_option maxHeartbeats 1000000 in
theorem norm_topBondAverageVelocity_sub_le (ha : 0 < a) (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (V : F.GaugeField F.top) {z : F.Cell} (ctx : CellSpans.CellHypotheses S z R C₀ s y)
    {b : F.Site F.top × Fin 4} (hb : b ∈ bondsOver S {z} F.top) (W W' : ComplexChainChart F) (A : ChainChart F)
    {φ : F.Cell → ℝ} {del θ : ℝ} (hdel : 0 ≤ del) (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y')
    (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) (hs : pairLocalSize S R W W' z ≤ y / 2) :
    ‖topBondAverageVelocity R W A b - topBondAverageVelocity R W' A b‖ ≤
      4 * a⁻¹ * (Analytic.cauchyHalvingConstant 0 * secondDiffBound F.blockSide a del) *
        (localNorm S R (complexChartSub W W').re (classWeight F φ θ p) z +
          localNorm S R (complexChartSub W W').im (classWeight F φ θ p) z) *
        localNorm S R A (invertedWeights (classWeight F φ θ p)) z := by
  have hy0 : 0 < y := ctx.small.pos
  set d := fiveDirections W W' A with hd
  have hsize : ∀ {t : Fin 5 → ℂ}, spanNorm S R d z t ≤ y →
      CellNormBounds.SourceBounds S z R (CellSpans.spanChart (zeroChart F) d t) y := fun h =>
    CellSpans.sourceBounds_spanChart (S := S) (z := z) (y := y) hodd R (zeroChart F) d _
      (by rw [spanLocalNorm_zeroChart]; exact h)
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1, spanNorm S R d z (basePoint + (x : ℂ) • stepVector) ≤ y / 2 := fun x hx =>
    (spanNorm_line_le W W' A z hx).trans hs
  have hPf : ∀ r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℂ (traceProbe a S R V d z b r) (basePoint + (x : ℂ) • stepVector) := fun r x hx =>
    analyticAt_traceProbe han hamb hodd V ctx d b r (hsize ((hpt x hx).trans (by linarith)))
  have hP1 : ∀ r, AnalyticAt ℂ (traceProbe a S R V d z b r) (basePoint + stepVector) := fun r => by
    simpa using hPf r 1 (by simp)
  have hP0 : ∀ r, AnalyticAt ℂ (traceProbe a S R V d z b r) basePoint := fun r => by
    simpa using hPf r 0 (by simp)
  have vt : topBondAverageVelocity R W A b = (1 / 2 : ℂ) • ∑ r,
      dirDeriv (traceProbe a S R V d z b r) (basisVec 4) (basePoint + stepVector) • ofUnit (quatBasis r) := by
    unfold topBondAverageVelocity
    have e : (fun τ : ℂ => topBondGaugedAverage R (complexChartMove W A τ) b) =
        fun τ : ℂ => topBondGaugedAverage R
          (CellSpans.spanChart (zeroChart F) d (basePoint + stepVector + τ • basisVec 4)) b := by
      funext τ
      rw [hd, spanChart_basePoint_add_step]
    rw [e]
    exact (hasDerivAt_topBondGaugedAverage ha.ne' V d hb _ _ fun r => (hP1 r).differentiableAt).deriv
  have vb : topBondAverageVelocity R W' A b = (1 / 2 : ℂ) • ∑ r,
      dirDeriv (traceProbe a S R V d z b r) (basisVec 4) basePoint • ofUnit (quatBasis r) := by
    unfold topBondAverageVelocity
    have e : (fun τ : ℂ => topBondGaugedAverage R (complexChartMove W' A τ) b) =
        fun τ : ℂ => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d (basePoint + τ • basisVec 4)) b := by
      funext τ
      rw [hd, spanChart_basePoint]
    rw [e]
    exact (hasDerivAt_topBondGaugedAverage ha.ne' V d hb _ _ fun r => (hP0 r).differentiableAt).deriv
  set B₂ := Analytic.cauchyHalvingConstant 0 * secondDiffBound F.blockSide a del *
      (localNorm S R (complexChartSub W W').re (classWeight F φ θ p) z +
        localNorm S R (complexChartSub W W').im (classWeight F φ θ p) z) *
      localNorm S R A (invertedWeights (classWeight F φ θ p)) z with hB₂
  have hseg : ∀ r, ‖dirDeriv (traceProbe a S R V d z b r) (basisVec 4) (basePoint + stepVector) -
      dirDeriv (traceProbe a S R V d z b r) (basisVec 4) basePoint‖ ≤ a⁻¹ * (2 * B₂) := by
    intro r
    refine norm_sub_le_of_dirDeriv_le (f := dirDeriv (traceProbe a S R V d z b r) (basisVec 4)) (e := basePoint)
      (d := stepVector) (fun x hx => (analyticAt_dirDeriv (hPf r x hx) _).differentiableAt) fun x hx => ?_
    have hp := hpt x hx
    have g₁ := analyticAt_cellTermsOnSpan (a := a) han hamb hodd (updateBond V b (quatBasis r)) ctx d
      (hp.trans (by linarith))
    have g₂ := analyticAt_cellTermsOnSpan (a := a) han hamb hodd (updateBond V b (-quatBasis r)) ctx d
      (hp.trans (by linarith))
    have e := dirDeriv_two_const_mul_sub (a : ℂ)⁻¹ (basisVec 4) stepVector g₁ g₂
    have e' : fderiv ℂ (dirDeriv (traceProbe a S R V d z b r) (basisVec 4)) (basePoint + (x : ℂ) • stepVector)
        stepVector =
        dirDeriv (dirDeriv (traceProbe a S R V d z b r) (basisVec 4)) stepVector (basePoint + (x : ℂ) • stepVector) :=
      rfl
    rw [e']
    have e'' : dirDeriv (dirDeriv (traceProbe a S R V d z b r) (basisVec 4)) stepVector
        (basePoint + (x : ℂ) • stepVector) =
        (a : ℂ)⁻¹ * (dirDeriv (dirDeriv (cellTermsOnSpan a S R (updateBond V b (-quatBasis r)) d z) (basisVec 4))
          stepVector (basePoint + (x : ℂ) • stepVector) -
          dirDeriv (dirDeriv (cellTermsOnSpan a S R (updateBond V b (quatBasis r)) d z) (basisVec 4)) stepVector
            (basePoint + (x : ℂ) • stepVector)) := e
    rw [e'', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha.le)
    have b₁ := norm_dirDeriv_two_stepVector_le (a := a) hmix han hamb hodd h2 (updateBond V b (quatBasis r)) ctx
      W W' A hdel hφ hθ p hp
    have b₂ := norm_dirDeriv_two_stepVector_le (a := a) hmix han hamb hodd h2 (updateBond V b (-quatBasis r)) ctx
      W W' A hdel hφ hθ p hp
    refine (norm_sub_le _ _).trans ?_
    linarith
  rw [vt, vb, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  have hsum : ‖∑ r, (dirDeriv (traceProbe a S R V d z b r) (basisVec 4) (basePoint + stepVector) •
      ofUnit (quatBasis r) -
      dirDeriv (traceProbe a S R V d z b r) (basisVec 4) basePoint • ofUnit (quatBasis r))‖ ≤
      4 * (a⁻¹ * (2 * B₂)) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ r ∈ (Finset.univ : Finset (Fin 4)),
        ‖dirDeriv (traceProbe a S R V d z b r) (basisVec 4) (basePoint + stepVector) • ofUnit (quatBasis r) -
        dirDeriv (traceProbe a S R V d z b r) (basisVec 4) basePoint • ofUnit (quatBasis r)‖ ≤ a⁻¹ * (2 * B₂) := by
      intro r _
      rw [← sub_smul, norm_smul, norm_ofUnit_quatBasis, mul_one]
      exact hseg r
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
    simp
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hn]
  have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine this.trans (le_of_eq ?_)
  rw [hB₂]
  ring
set_option maxHeartbeats 1000000 in
theorem norm_topBondAverageVelocity_le_add (ha : 0 < a) (han : complexCellTermsAnalyticStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (V : F.GaugeField F.top) {z : F.Cell}
    (ctx : CellSpans.CellHypotheses S z R C₀ s y) {b : F.Site F.top × Fin 4} (hb : b ∈ bondsOver S {z} F.top)
    (hbD : b ∈ innerBonds (cellBall S z 1) (F.depth + 1)) (W : ComplexChainChart F) (A : ChainChart F)
    (hs : localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z ≤ y / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ‖topBondAverageVelocity R W A b‖ ≤ 36 / y * (localNorm S R A (constOneWeights F) z + ε) := by
  have hy0 : 0 < y := ctx.small.pos
  set d := fiveDirections W W A with hd
  set nA := localNorm S R A (constOneWeights F) z with hnA
  have hnA0 : 0 ≤ nA := Real.sqrt_nonneg _
  set ρ : ℝ := y / (4 * (nA + ε)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsize : ∀ {t : Fin 5 → ℂ}, spanNorm S R d z t ≤ y →
      CellNormBounds.SourceBounds S z R (CellSpans.spanChart (zeroChart F) d t) y := fun h =>
    CellSpans.sourceBounds_spanChart (S := S) (z := z) (y := y) hodd R (zeroChart F) d _
      (by rw [spanLocalNorm_zeroChart]; exact h)
  have hline : ∀ τ : ℂ, ‖τ‖ ≤ ρ → spanNorm S R d z (basePoint + τ • basisVec 4) ≤ y := by
    intro τ hτ
    have h1 := spanNorm_add_le S R d z basePoint (τ • basisVec 4)
    rw [spanNorm_smul, spanNorm_single] at h1
    have h3 := spanNorm_basePoint_le (S := S) (R := R) W W A z
    have h4 : ‖τ‖ * nA ≤ y / 4 := by
      calc ‖τ‖ * nA ≤ ρ * (nA + ε) := mul_le_mul hτ (by linarith) hnA0 hρ0.le
        _ = y / 4 := by rw [hρ]; field_simp
    have e4 : localNorm S R (d 4) (constOneWeights F) z = nA := rfl
    rw [e4] at h1
    linarith
  set f : ℂ → ComplexifiedQuaternions.ComplexQuat :=
    fun τ => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d (basePoint + τ • basisVec 4)) b with hf
  have hf0 : topBondAverageVelocity R W A b = deriv f 0 := by
    have e : (fun τ : ℂ => topBondGaugedAverage R (complexChartMove W A τ) b) = f := by
      funext τ
      simp only [hf]
      rw [hd, spanChart_basePoint]
    unfold topBondAverageVelocity
    rw [e]
  have hline_an : ∀ τ : ℂ, AnalyticAt ℂ (fun τ : ℂ => (basePoint + τ • basisVec 4 : Fin 5 → ℂ)) τ := fun τ => by
    have hs1 : AnalyticAt ℂ (fun τ : ℂ => τ • (basisVec 4 : Fin 5 → ℂ)) τ := analyticAt_id.smul analyticAt_const
    exact analyticAt_const.add hs1
  have hfan : ∀ τ : ℂ, ‖τ‖ ≤ ρ → AnalyticAt ℂ f τ := fun τ hτ =>
    AnalyticAt.comp (g := fun t => topBondGaugedAverage R (CellSpans.spanChart (zeroChart F) d t) b)
      (f := fun τ : ℂ => (basePoint + τ • basisVec 4 : Fin 5 → ℂ))
      (analyticAt_topBondGaugedAverage ha.ne' han hamb hodd V ctx d hb (hsize (hline τ hτ))) (hline_an τ)
  have hdiff : DifferentiableOn ℂ f (closedBall 0 ρ) := fun τ hτ =>
    (hfan τ (by simpa using hτ)).differentiableAt.differentiableWithinAt
  have hC : ∀ τ ∈ sphere (0 : ℂ) ρ, ‖f τ‖ ≤ 9 := fun τ hτ => by
    have hτ' : ‖τ‖ = ρ := by simpa using hτ
    exact norm_topBondGaugedAverage_le hodd ctx (hsize (hline τ hτ'.le)) hbD
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 (hdiff.diffContOnCl_ball subset_rfl) hC
  rw [hf0]
  refine h1.trans (le_of_eq ?_)
  rw [hρ]
  field_simp
  ring
theorem norm_topBondAverageVelocity_le (ha : 0 < a) (han : complexCellTermsAnalyticStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (V : F.GaugeField F.top) {z : F.Cell}
    (ctx : CellSpans.CellHypotheses S z R C₀ s y) {b : F.Site F.top × Fin 4} (hb : b ∈ bondsOver S {z} F.top)
    (hbD : b ∈ innerBonds (cellBall S z 1) (F.depth + 1)) (W : ComplexChainChart F) (A : ChainChart F)
    (hs : localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z ≤ y / 2) :
    ‖topBondAverageVelocity R W A b‖ ≤ 36 / y * (localNorm S R A (constOneWeights F) z + 0) := by
  have hcont : Continuous fun ε : ℝ => 36 / y * (localNorm S R A (constOneWeights F) z + ε) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => 36 / y * (localNorm S R A (constOneWeights F) z + ε)) (𝓝[>] 0)
      (𝓝 (36 / y * (localNorm S R A (constOneWeights F) z + 0))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_topBondAverageVelocity_le_add ha han hamb hodd V ctx hb hbD W A hs hε
end Bounds
section Assembly
open BlockAverages
variable {F : BlockFrame} {m : ℕ}
def chartBoundConst (L : ℕ) (a del y : ℝ) : ℝ :=
  4 * thirdDiffBound L a del y + 4 * a⁻¹ * (Analytic.cauchyHalvingConstant 0 * secondDiffBound L a del) + 36 / y + 1
theorem chartBoundConst_pos {L : ℕ} (hL : Odd L) {a del y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    0 < chartBoundConst L a del y := by
  have h1 := Analytic.cauchyHalvingConstant_pos 0
  have h3 := Analytic.cauchyHalvingConstant_pos 1
  have h4 := secondDiffBound_nonneg hL a del
  unfold chartBoundConst thirdDiffBound
  positivity
set_option maxHeartbeats 2000000 in
theorem complexChartBounds_of_cellHypotheses (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a θ del c c₂ C₀ s y : ℝ} (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ8 : θ ≤ 1 / 8) (hdel : 0 < del)
    {S : Finset F.Cell} {V : F.GaugeField F.top}
    (hctx : ∀ z ∈ S, CellSpans.CellHypotheses S z (referenceFieldChain S V) C₀ s y) (hy : 0 < y)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del (referenceFieldChain S V) U ≤ c₂ →
      ChartIsRegular S (referenceFieldChain S V) U ∧
      ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤
        2 * supWeightedNorm S del (referenceFieldChain S V) U)
    (hc0 : 0 < c) (hcy : 32 * c ≤ y) (hcc : 4 * c ≤ c₂) :
    ComplexChartBounds a θ del c (chartBoundConst F.blockSide a del y) S V := by
  set R := referenceFieldChain S V with hR
  have hL := hodd.pos
  have hdel0 := hdel.le
  have hc₂ : 0 < c₂ := by linarith
  have nS : ∀ U : ChainChart F, 0 ≤ supWeightedNorm S del R U := fun U =>
    CoordinateSeminorms.supWeightedNorm_nonneg _ _ _ _
  have part : ∀ {W : ComplexChainChart F}, complexSupWeightedNorm S del R W ≤ c →
      supWeightedNorm S del R W.re ≤ c ∧ supWeightedNorm S del R W.im ≤ c := fun {W} hW => by
    have h1 := nS W.re
    have h3 := nS W.im
    have e : complexSupWeightedNorm S del R W = supWeightedNorm S del R W.re + supWeightedNorm S del R W.im := rfl
    rw [e] at hW
    constructor <;> linarith
  have nearP : ∀ {U : ChainChart F} {z : F.Cell}, z ∈ S → supWeightedNorm S del R U ≤ c₂ →
      localNorm S R U (constOneWeights F) z ≤ 2 * supWeightedNorm S del R U := fun hz hU => (hreg _ hU).2 _ hz
  have pairNear : ∀ {W : ComplexChainChart F} {z : F.Cell}, z ∈ S → complexSupWeightedNorm S del R W ≤ c →
      localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z ≤ y / 2 :=
    fun {W z} hz hW => by
    obtain ⟨h1, h3⟩ := part hW
    have h4 := nearP hz (h1.trans (by linarith))
    have h5 := nearP hz (h3.trans (by linarith))
    have e : complexSupWeightedNorm S del R W = supWeightedNorm S del R W.re + supWeightedNorm S del R W.im := rfl
    rw [e] at hW
    linarith
  have sizeAt : ∀ {W : ComplexChainChart F} {z : F.Cell}, z ∈ S → complexSupWeightedNorm S del R W ≤ c →
      CellNormBounds.SourceBounds S z R W y :=
    fun hz hW => sourceBounds_of_localNorm_pair hodd R _ ((pairNear hz hW).trans (by linarith))
  have hbond : ∀ b ∈ innerBonds S F.top, enclosingCell b.1 ∈ S ∧ b ∈ bondsOver S {enclosingCell b.1} F.top ∧
      b ∈ innerBonds (cellBall S (enclosingCell b.1) 1) (F.depth + 1) := fun b hbS => by
    have hz : enclosingCell b.1 ∈ S :=
      CoordinateSeminorms.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hbS).1).1
    have h1 : b ∈ bondsOver S {enclosingCell b.1} F.top := CoordinateSeminorms.mem_bondsOver.2 ⟨hbS, by simp⟩
    exact ⟨hz, h1, BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S _ le_rfl h1⟩
  have hsize2 : ∀ (W W' : ComplexChainChart F), complexSupWeightedNorm S del R W ≤ c →
      complexSupWeightedNorm S del R W' ≤ c → ∀ z ∈ S,
      pairLocalSize S R W W' z ≤ 4 * (complexSupWeightedNorm S del R W + complexSupWeightedNorm S del R W') := by
    intro W W' hW hW' z hz
    obtain ⟨r1, i1⟩ := part hW
    obtain ⟨r2, i2⟩ := part hW'
    have t1 : supWeightedNorm S del R (complexChartSub W W').re ≤
        supWeightedNorm S del R W.re + supWeightedNorm S del R W'.re := by
      have h := CoordinateSeminorms.supWeightedNorm_chartMove_le S hL del hdel0 R W.re W'.re (-1)
      have e : (complexChartSub W W').re = chartMove W.re W'.re (-1) := rfl
      rw [e]
      simpa using h
    have t2 : supWeightedNorm S del R (complexChartSub W W').im ≤
        supWeightedNorm S del R W.im + supWeightedNorm S del R W'.im := by
      have h := CoordinateSeminorms.supWeightedNorm_chartMove_le S hL del hdel0 R W.im W'.im (-1)
      have e : (complexChartSub W W').im = chartMove W.im W'.im (-1) := rfl
      rw [e]
      simpa using h
    have n1 := nearP (U := W'.re) hz (r2.trans (by linarith))
    have n2 := nearP (U := W'.im) hz (i2.trans (by linarith))
    have n3 := nearP (U := (complexChartSub W W').re) hz (t1.trans (by linarith))
    have n4 := nearP (U := (complexChartSub W W').im) hz (t2.trans (by linarith))
    have e1 : complexSupWeightedNorm S del R W = supWeightedNorm S del R W.re + supWeightedNorm S del R W.im := rfl
    have e2 : complexSupWeightedNorm S del R W' = supWeightedNorm S del R W'.re + supWeightedNorm S del R W'.im := rfl
    unfold pairLocalSize
    rw [e1, e2]
    have := nS W.re
    have := nS W.im
    have := nS W'.re
    have := nS W'.im
    linarith
  have hsum4 : ∀ (W W' : ComplexChainChart F), complexSupWeightedNorm S del R W ≤ c →
      complexSupWeightedNorm S del R W' ≤ c →
      4 * (complexSupWeightedNorm S del R W + complexSupWeightedNorm S del R W') ≤ y / 2 := fun W W' hW hW' => by
    linarith
  have hthird : 0 ≤ thirdDiffBound F.blockSide a del y := by
    have h1 := Analytic.cauchyHalvingConstant_pos 1
    have h3 := secondDiffBound_nonneg hodd a del
    unfold thirdDiffBound
    positivity
  have hcf0 : 0 ≤ 4 * a⁻¹ * (Analytic.cauchyHalvingConstant 0 * secondDiffBound F.blockSide a del) := by
    have h1 := Analytic.cauchyHalvingConstant_pos 0
    have h3 := secondDiffBound_nonneg hodd a del
    positivity
  have h36 : 0 ≤ 36 / y := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k A t hW
    have e : (fun q : Fin k → ℂ => complexTotalOverTop a S R (complexSpan A q) (complexifyField V)) =
        totalOnSpan a S R V A := rfl
    rw [e, totalOnSpan_eq_sum han hamb hodd]
    exact Finset.analyticAt_fun_sum _ fun z hz =>
      analyticAt_cellTermsOnSpan_of_sourceBounds han hamb hodd a V (hctx z hz) A (sizeAt hz hW)
  · intro b hbS k A t hW
    obtain ⟨hz, h1, -⟩ := hbond b hbS
    exact analyticAt_topBondGaugedAverage ha.ne' han hamb hodd V (hctx _ hz) A h1 (sizeAt hz hW)
  · intro W W' hW hW' φ θ' p hθ' hφ A
    have habs : |θ'| ≤ 1 / 8 := by
      rcases hθ' with h | h | h
      · rw [h, abs_of_nonneg hθ0]
        exact hθ8
      · rw [h]
        norm_num
      · rw [h, abs_neg, abs_of_nonneg hθ0]
        exact hθ8
    set n := complexSupWeightedNorm S del R W with hn
    set n' := complexSupWeightedNorm S del R W' with hn'
    have hn0 : 0 ≤ n := add_nonneg (nS _) (nS _)
    have hn'0 : 0 ≤ n' := add_nonneg (nS _) (nS _)
    have hsN := hsize2 W W' hW hW'
    have hsm := hsum4 W W' hW hW'
    have hl := norm_total_firstVariation_sub_le (a := a) hmix han hamb hodd h2 V hctx hy W W' A hdel0 hφ habs p
      (by positivity) hsN hsm
    have hpt : ∀ z ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        AnalyticAt ℂ (cellTermsOnSpan a S R V (fiveDirections W W' A) z)
          ((u : ℂ) • (basePoint + (x : ℂ) • stepVector)) := fun z hz u hu x hx =>
      analyticAt_cellTermsOnSpan han hamb hodd a V (hctx z hz) _
        (((spanNorm_segment_le W W' A z hu hx).trans (hsN z hz)).trans (by linarith))
    have hT : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        AnalyticAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) ((u : ℂ) • (basePoint + (x : ℂ) • stepVector)) :=
      fun u hu x hx => by
      rw [totalOnSpan_eq_sum han hamb hodd]
      exact Finset.analyticAt_fun_sum _ fun z hz => hpt z hz u hu x hx
    have h11 : AnalyticAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) (basePoint + stepVector) := by
      simpa using hT 1 (by simp) 1 (by simp)
    have h10 : AnalyticAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) basePoint := by
      simpa using hT 1 (by simp) 0 (by simp)
    have h00 : AnalyticAt ℂ (totalOnSpan a S R V (fiveDirections W W' A)) 0 := by
      simpa using hT 0 (by simp) 0 (by simp)
    rw [complexFirstVariation_eq_dirDeriv_top W W' A h11.differentiableAt,
      complexFirstVariation_eq_dirDeriv_base W W' A h10.differentiableAt,
      ← dirDeriv_two_stepVector_eq_referenceForm hL hdel0 hc₂ (fun U hU => (hreg U hU).1) W W' A h00]
    refine hl.trans ?_
    have hX : 0 ≤ complexWeightedNorm S R (complexChartSub W W') (classWeight F φ θ' p) :=
      add_nonneg (CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (CoordinateSeminorms.weightedNorm_nonneg _ _ _ _)
    have hA := CoordinateSeminorms.weightedNorm_nonneg S R A (invertedWeights (classWeight F φ θ' p))
    have hs : 0 ≤ n + n' := by positivity
    have hCb : 4 * thirdDiffBound F.blockSide a del y ≤ chartBoundConst F.blockSide a del y := by
      unfold chartBoundConst
      linarith
    have e : thirdDiffBound F.blockSide a del y * (4 * (n + n')) *
        complexWeightedNorm S R (complexChartSub W W') (classWeight F φ θ' p) *
        weightedNorm S R A (invertedWeights (classWeight F φ θ' p)) =
        (4 * thirdDiffBound F.blockSide a del y) *
          ((n + n') * complexWeightedNorm S R (complexChartSub W W') (classWeight F φ θ' p) *
          weightedNorm S R A (invertedWeights (classWeight F φ θ' p))) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hCb (mul_nonneg (mul_nonneg hs hX) hA)
    refine this.trans (le_of_eq ?_)
    ring
  · intro b hbS W W' hW hW' φ θ' p hθ' hφ A
    obtain ⟨hz, h1, -⟩ := hbond b hbS
    have habs : |θ'| ≤ 1 / 8 := by
      rcases hθ' with h | h | h
      · rw [h, abs_of_nonneg hθ0]
        exact hθ8
      · rw [h]
        norm_num
      · rw [h, abs_neg, abs_of_nonneg hθ0]
        exact hθ8
    have hl := norm_topBondAverageVelocity_sub_le ha hmix han hamb hodd h2 V (hctx _ hz) h1 W W' A hdel0 hφ habs p
      (((hsize2 W W' hW hW') _ hz).trans (hsum4 W W' hW hW'))
    refine hl.trans ?_
    set w := classWeight F φ θ' p with hw
    have c1 := CoordinateSeminorms.localNorm_le_weightedNorm S R (complexChartSub W W').re w (enclosingCell b.1)
    have c2 := CoordinateSeminorms.localNorm_le_weightedNorm S R (complexChartSub W W').im w (enclosingCell b.1)
    have c3 := CoordinateSeminorms.localNorm_le_weightedNorm S R A (invertedWeights w) (enclosingCell b.1)
    have e : complexWeightedNorm S R (complexChartSub W W') w =
        weightedNorm S R (complexChartSub W W').re w + weightedNorm S R (complexChartSub W W').im w := rfl
    rw [e]
    have hN1 : 0 ≤ localNorm S R (complexChartSub W W').re w (enclosingCell b.1) +
        localNorm S R (complexChartSub W W').im w (enclosingCell b.1) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hN2 : 0 ≤ localNorm S R A (invertedWeights w) (enclosingCell b.1) := Real.sqrt_nonneg _
    have hC : 4 * a⁻¹ * (Analytic.cauchyHalvingConstant 0 * secondDiffBound F.blockSide a del) ≤
        chartBoundConst F.blockSide a del y := by
      unfold chartBoundConst
      linarith
    have h3 : (localNorm S R (complexChartSub W W').re w (enclosingCell b.1) +
        localNorm S R (complexChartSub W W').im w (enclosingCell b.1)) *
        localNorm S R A (invertedWeights w) (enclosingCell b.1) ≤
        (weightedNorm S R (complexChartSub W W').re w + weightedNorm S R (complexChartSub W W').im w) *
          weightedNorm S R A (invertedWeights w) :=
      mul_le_mul (add_le_add c1 c2) c3 hN2
        (add_nonneg (CoordinateSeminorms.weightedNorm_nonneg _ _ _ _) (CoordinateSeminorms.weightedNorm_nonneg _ _ _ _))
    have hB0 : 0 ≤ chartBoundConst F.blockSide a del y := (chartBoundConst_pos hodd ha hy).le
    calc _ = 4 * a⁻¹ * (Analytic.cauchyHalvingConstant 0 * secondDiffBound F.blockSide a del) *
          ((localNorm S R (complexChartSub W W').re w (enclosingCell b.1) +
            localNorm S R (complexChartSub W W').im w (enclosingCell b.1)) *
          localNorm S R A (invertedWeights w) (enclosingCell b.1)) := by ring
      _ ≤ chartBoundConst F.blockSide a del y *
          ((weightedNorm S R (complexChartSub W W').re w + weightedNorm S R (complexChartSub W W').im w) *
          weightedNorm S R A (invertedWeights w)) := mul_le_mul hC h3 (mul_nonneg hN1 hN2) hB0
      _ = _ := by ring
  · intro b hbS W hW A
    obtain ⟨hz, h1, h3⟩ := hbond b hbS
    have hl := norm_topBondAverageVelocity_le ha han hamb hodd V (hctx _ hz) h1 h3 W A (pairNear hz hW)
    refine hl.trans ?_
    rw [add_zero]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    unfold chartBoundConst
    linarith
end Assembly
open BlockAverages in
theorem complexChartBounds_holds (hrec : UniformQuarticBoundAcrossLevels) (hbd : referenceBoundsStatement)
    (hsm : smallChartIsRegularStatement) (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) : complexChartBoundsStatement := by
  obtain ⟨C, L1, hC, hctx⟩ := CellContexts.cellHypotheses_of_referenceBounds hrec hbd
  obtain ⟨Lr, hregL⟩ := hsm
  refine ⟨max (max L1 Lr) 5, ?_⟩
  intro L a θ del hodd hL ha hθ0 hθ8 hd0 hd8
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLr : Lr ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have h5 : 5 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨c₁, y₀, hc₁, hy₀, hc⟩ := hctx L hodd hL1 h5
  obtain ⟨c₂, hc₂, hr⟩ := hregL L hodd hLr del hd0 hd8
  set c := min (min c₁ (c₂ / 4)) (min (y₀ / 32) (y₀ / (26 * C))) with hcd
  have hc0 : 0 < c := lt_min (lt_min hc₁ (by positivity)) (lt_min (by positivity) (by positivity))
  have hc_c₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hc_c₂ : c ≤ c₂ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hc_y : c ≤ y₀ / 32 := (min_le_right _ _).trans (min_le_left _ _)
  have hc_s : c ≤ y₀ / (26 * C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, chartBoundConst L a del y₀, hc0, chartBoundConst_pos hodd ha hy₀, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold
  have h26 : 26 * C * s ≤ y₀ := by
    have h1 : s ≤ y₀ / (26 * C) := hsc.trans hc_s
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have h2F : 2 ≤ F.blockSide := by omega
  have hreg' := fun W hW => hr F m S hFL hamb hm hreg s V hs (hsc.trans (hc_c₂.trans (by linarith))) hcold W hW
  have hct : ∀ z ∈ S, CellSpans.CellHypotheses S z (referenceFieldChain S V) C s y₀ := fun z _ =>
    hc F m S hFL hamb hm hreg s V hs (hsc.trans hc_c₁) hcold z y₀ h26 le_rfl
  have := complexChartBounds_of_cellHypotheses hmix han hamb hoddF h2F ha hθ0 hθ8 hd0 hct hy₀ hreg' hc0
    (by linarith) (by linarith)
  rwa [hFL] at this
end YangMills.Construction.ComplexChartEstimates
end
