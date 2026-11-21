import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.LawOnABoxOfTheFlow.CurlOnTheSliceIsGaussian
import YangMills.Construction.LawOnABoxOfTheFlow.MeanUnderAnEventOfGaussianMass
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.ResponseInTheExpansion.ComparisonFromBoundsOfAMoveProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion NNReal
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.ResponseInTheExpansion
private theorem norm_sq_eq_sum_imaginaryComponent (v : imaginaryQuaternions) :
    ‖v‖ ^ 2 = ∑ i : Fin 3, imaginaryComponent i v ^ 2 := by apply _root_.YangMills.SharedProofs.p8485 <;> assumption
private def imaginaryComponentLinear (i : Fin 3) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun := imaginaryComponent i
  map_add' := by
    intro a b
    fin_cases i <;> simp [imaginaryComponent]
  map_smul' := by
    intro c a
    fin_cases i <;> simp [imaginaryComponent]
private theorem continuous_imaginaryComponent_local (i : Fin 3) : Continuous (imaginaryComponent i) := by apply _root_.YangMills.Construction.BoxGaussian.continuous_imaginaryComponent <;> assumption
private theorem colourPairing_single {n : ℕ} [NeZero n] (S : Finset (TorusSite n)) (i : Fin 3)
    (w : TorusPlaquette n → ℝ) (F : TorusPlaquette n → imaginaryQuaternions) :
    colourPairing S (fun p j => if j = i then w p else 0) F =
      imaginaryComponent i (∑ p ∈ plaquettesIn S, w p • F p) := by
  have h : imaginaryComponent i (∑ p ∈ plaquettesIn S, w p • F p) =
      ∑ p ∈ plaquettesIn S, w p * imaginaryComponent i (F p) := by
    change imaginaryComponentLinear i (∑ p ∈ plaquettesIn S, w p • F p) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [h]
  unfold colourPairing
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
private theorem gaussianReal_abs_ge_le (v : ℝ≥0) (t : ℝ) (ht : 0 < t) :
    (gaussianReal 0 v).real {y : ℝ | t ≤ |y|} ≤ (v : ℝ) / t ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := gaussianReal 0 v) (X := id) (memLp_id_gaussianReal 2) ht
  have hi : ∫ y, id y ∂gaussianReal 0 v = 0 := integral_id_gaussianReal
  rw [variance_id_gaussianReal, hi] at h
  simp only [id, sub_zero] at h
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
private theorem exists_mem_forall_abs_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Fin 3 → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (v : Fin 3 → ℝ≥0)
    (hlaw : ∀ i, μ.map (f i) = gaussianReal 0 (v i))
    (t : ℝ) (ht : 0 < t) (hv : ∀ i, (v i : ℝ) ≤ t ^ 2 / 10) (E : Set Ω) (hE : (0.6 : ℝ) ≤ μ.real E) :
    ∃ ω ∈ E, ∀ i, |f i ω| < t := by
  have hone : μ Set.univ = 1 := by
    have h := hlaw 0
    have h' : (μ.map (f 0)) Set.univ = (gaussianReal 0 (v 0)) Set.univ := by rw [h]
    rw [Measure.map_apply (hf 0) MeasurableSet.univ] at h'
    simpa using h'
  have : IsProbabilityMeasure μ := ⟨hone⟩
  have hset : MeasurableSet {y : ℝ | t ≤ |y|} :=
    measurableSet_le measurable_const (continuous_abs.measurable)
  have hbad : ∀ i, μ.real (f i ⁻¹' {y : ℝ | t ≤ |y|}) ≤ 1 / 10 := by
    intro i
    have h1 : μ.real (f i ⁻¹' {y : ℝ | t ≤ |y|}) = (μ.map (f i)).real {y : ℝ | t ≤ |y|} :=
      (map_measureReal_apply (hf i) hset).symm
    rw [h1, hlaw i]
    refine (gaussianReal_abs_ge_le (v i) t ht).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have := hv i
    linarith
  by_contra hno
  push Not at hno
  have hsub : E ⊆ ⋃ i, f i ⁻¹' {y : ℝ | t ≤ |y|} := fun ω hω => by
    obtain ⟨i, hi⟩ := hno ω hω
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have h1 : μ.real E ≤ μ.real (⋃ i, f i ⁻¹' {y : ℝ | t ≤ |y|}) := measureReal_mono hsub
  have h2 : μ.real (⋃ i, f i ⁻¹' {y : ℝ | t ≤ |y|}) ≤ ∑ i, μ.real (f i ⁻¹' {y : ℝ | t ≤ |y|}) :=
    measureReal_iUnion_fintype_le _
  rw [Fin.sum_univ_three] at h2
  have := hbad 0
  have := hbad 1
  have := hbad 2
  norm_num at hE
  linarith
private theorem rpow_neg_half_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by apply _root_.YangMills.Construction.WeightedResponses.GradientMoves.rpow_neg_half_sq <;> assumption
private theorem lieFormCurl_eq_of_critical {n : ℕ} [NeZero n] {o : TorusSite n} {R : ℕ}
    {A B B₀ : TorusBond n → imaginaryQuaternions}
    {S : Finset (TorusSite n)}
    {Q : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hlin : ∀ (a : ℝ) (u u' v : TorusBond n → imaginaryQuaternions),
      Q (a • u + u') v = a * Q u v + Q u' v)
    (hco : ∀ v : TorusBond n → imaginaryQuaternions, 2 * c * curlNormSq S v ≤ Q v v)
    (hB : B - A ∈ gaugeSlice o R A) (hB₀ : B₀ - A ∈ gaugeSlice o R A)
    (hq : ∀ η : TorusBond n → imaginaryQuaternions,
      (∀ b, b ∉ bondsTouching o R → η b = 0) → Q B η = 0)
    (hq₀ : ∀ η : TorusBond n → imaginaryQuaternions,
      (∀ b, b ∉ bondsTouching o R → η b = 0) → Q B₀ η = 0) :
    ∀ p ∈ plaquettesIn S, lieFormCurl B p = lieFormCurl B₀ p := by
  have hDs : B - B₀ ∈ gaugeSlice o R A := by
    have h := (gaugeSlice o R A).sub_mem hB hB₀
    rwa [sub_sub_sub_cancel_right] at h
  have hoff : ∀ b, b ∉ bondsTouching o R → (B - B₀) b = 0 :=
    (show (∀ b, b ∉ bondsTouching o R → (B - B₀) b = 0) ∧ _ from hDs).1
  have h0 : Q (B - B₀) (B - B₀) = 0 := by
    have h := hlin (-1) B₀ B (B - B₀)
    rw [hq _ hoff, hq₀ _ hoff] at h
    have e : (-1 : ℝ) • B₀ + B = B - B₀ := by
      funext b
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
      module
    rw [e] at h
    simpa using h
  have h1 := hco (B - B₀)
  rw [h0] at h1
  have h2 : curlNormSq S (B - B₀) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < 2 * c * curlNormSq S (B - B₀) := by positivity
    linarith
  have h3 : ∑ p ∈ plaquettesIn S, ‖lieFormCurl (B - B₀) p‖ ^ 2 = 0 :=
    le_antisymm h2 (Finset.sum_nonneg fun _ _ => by positivity)
  intro p hp
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 h3 p hp
  have h5 : lieFormCurl (B - B₀) p = 0 := by simpa using h4
  have h6 : lieFormCurl (B - B₀) p = lieFormCurl B p - lieFormCurl B₀ p := by
    simp only [lieFormCurl, Pi.sub_apply]
    abel
  rw [h6] at h5
  exact sub_eq_zero.1 h5
private theorem measurable_colourPairing_shift {n : ℕ} [NeZero n] (S : Finset (TorusSite n))
    (u : TorusPlaquette n → Fin 3 → ℝ) (A : TorusBond n → imaginaryQuaternions)
    (G : TorusPlaquette n → imaginaryQuaternions) :
    Measurable fun ζ : TorusBond n → imaginaryQuaternions =>
      colourPairing S u fun p => lieFormCurl (A + ζ) p - G p := by
  refine Continuous.measurable ?_
  unfold colourPairing
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun p _ =>
    continuous_const.mul ((continuous_imaginaryComponent_local i).comp ?_)
  simp only [lieFormCurl, Pi.add_apply]
  fun_prop
theorem criticalCurlBoundFromLargeEvent (hG : sliceCurlGaussianStatement)
    (hT : curlCovarianceBoundsStatement) (hQ : cubeHessianStatement) :
    criticalCurlBoundFromLargeEventStatement := by
  intro Tb hTb κ₀ h27 h21
  obtain ⟨C, xs, hmain⟩ := hG Tb hTb κ₀ h27 h21
  obtain ⟨R₁, hker⟩ := hT Tb hTb
  obtain ⟨CQ, R₂, -, hform⟩ := hQ Tb hTb
  have hcK : 0 < Tb.coercivity := hTb.cK_pos
  have hκ : 0 < κ₀ := by linarith
  have hV : 0 < (2 * Tb.coercivity)⁻¹ := by positivity
  have hM : 0 < Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) := Real.sqrt_pos.2 (by positivity)
  have hM2 : Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) ^ 2 = 10 * (2 * Tb.coercivity)⁻¹ :=
    Real.sq_sqrt (by positivity)
  refine ⟨2 * Real.sqrt (10 * (2 * Tb.coercivity)⁻¹), max (max xs 1) (((max R₁ R₂ : ℕ) : ℝ) ^ (1 / κ₀)), ?_⟩
  intro x R k n _ o A B hx hR hn hA hBs hBq E w b hE hw hmass hEb
  have hxs : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hRm : max R₁ R₂ ≤ R := by
    have h2 : ((max R₁ R₂ : ℕ) : ℝ) ^ (1 / κ₀) ≤ x := (le_max_right _ _).trans hx
    have h1 : ((max R₁ R₂ : ℕ) : ℝ) ≤ x ^ κ₀ := by
      calc ((max R₁ R₂ : ℕ) : ℝ) = (((max R₁ R₂ : ℕ) : ℝ) ^ (1 / κ₀)) ^ κ₀ := by
            rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hκ.ne', Real.rpow_one]
        _ ≤ x ^ κ₀ := Real.rpow_le_rpow (by positivity) h2 hκ.le
    have h3 : x ^ κ₀ ≤ (R : ℝ) := by
      rw [hR]
      exact Nat.le_ceil _
    exact_mod_cast h1.trans h3
  have hR₁ : R₁ ≤ R := (le_max_left _ _).trans hRm
  have hR₂ : R₂ ≤ R := (le_max_right _ _).trans hRm
  obtain ⟨B₀, hB₀s, hB₀q, -, -, -, hlaw⟩ := hmain x R k n o A hxs hR hn hA
  obtain ⟨-, -, -, hlin, hcoer, -, -⟩ := hform k n o R hR₂ hn
  obtain ⟨-, -, hvar⟩ := hker k n o R hR₁ hn
  have hsame := lieFormCurl_eq_of_critical hcK hlin (fun v => (hcoer v).1) hBs hB₀s hBq hB₀q
  have hpair : ∀ (i : Fin 3) (ζ : TorusBond n → imaginaryQuaternions),
      colourPairing (supBall o (2 * R)) (fun p j => if j = i then w p else 0)
          (fun p => lieFormCurl (A + ζ) p - lieFormCurl B₀ p) =
        imaginaryComponent i (∑ p ∈ plaquettesIn (supBall o (2 * R)),
          w p • (lieFormCurl (A + ζ) p - lieFormCurl B₀ p)) :=
    fun i ζ => colourPairing_single _ i w _
  have ht : 0 < Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ)) :=
    mul_pos hM (Real.rpow_pos_of_pos hx0 _)
  have ht2 : (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ))) ^ 2 =
      10 * (2 * Tb.coercivity)⁻¹ * x⁻¹ := by
    rw [mul_pow, hM2, rpow_neg_half_sq hx0]
  have hvar' : ∀ i : Fin 3,
      (((x⁻¹ * curlQuadForm Tb.coupling Tb.side k o R (fun p j => if j = i then w p else 0)).toNNReal :
          ℝ≥0) : ℝ) ≤
        (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ))) ^ 2 / 10 := by
    intro i
    obtain ⟨h0, h1⟩ := hvar (fun p j => if j = i then w p else 0)
    have hs : ∑ j : Fin 3, ∑ p ∈ plaquettesIn (supBall o (2 * R)), (if j = i then w p else 0) ^ 2 =
        ∑ p ∈ plaquettesIn (supBall o (2 * R)), w p ^ 2 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [hs] at h1
    have hxi : 0 < x⁻¹ := by positivity
    rw [Real.coe_toNNReal _ (by positivity), ht2]
    have h2 : curlQuadForm Tb.coupling Tb.side k o R (fun p j => if j = i then w p else 0) ≤
        (2 * Tb.coercivity)⁻¹ :=
      h1.trans (by nlinarith)
    nlinarith
  obtain ⟨ζ, hζE, hζ⟩ := exists_mem_forall_abs_lt (sliceGaussian Tb.coupling Tb.side k o R x A)
    (fun i ζ => colourPairing (supBall o (2 * R)) (fun p j => if j = i then w p else 0)
      (fun p => lieFormCurl (A + ζ) p - lieFormCurl B₀ p))
    (fun i => measurable_colourPairing_shift _ _ A _) _ (fun i => hlaw _) _ ht hvar' E hmass
  have hΔ : ‖∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • (lieFormCurl (A + ζ) p - lieFormCurl B₀ p)‖ ≤
      2 * (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ))) := by
    have hsq : ∀ i : Fin 3, imaginaryComponent i
        (∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • (lieFormCurl (A + ζ) p - lieFormCurl B₀ p)) ^ 2 ≤
        (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ))) ^ 2 := by
      intro i
      have h := hζ i
      simp only [hpair] at h
      exact sq_le_sq' (by linarith [(abs_lt.1 h).1]) (abs_lt.1 h).2.le
    have h4 : ‖∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • (lieFormCurl (A + ζ) p - lieFormCurl B₀ p)‖ ^ 2 ≤
        (2 * (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ)))) ^ 2 := by
      rw [norm_sq_eq_sum_imaginaryComponent, Fin.sum_univ_three]
      nlinarith [hsq 0, hsq 1, hsq 2,
        sq_nonneg (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ)))]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4
  have heq : ∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • lieFormCurl B p =
      ∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • lieFormCurl (A + ζ) p -
        ∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • (lieFormCurl (A + ζ) p - lieFormCurl B₀ p) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hsame p hp, smul_sub]
    abel
  rw [heq]
  have h5 := hEb ζ hζE
  calc _ ≤ ‖∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • lieFormCurl (A + ζ) p‖ +
        ‖∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • (lieFormCurl (A + ζ) p - lieFormCurl B₀ p)‖ :=
          norm_sub_le _ _
    _ ≤ b + 2 * (Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ))) := add_le_add h5 hΔ
    _ = b + 2 * Real.sqrt (10 * (2 * Tb.coercivity)⁻¹) * x ^ (-(1 / 2 : ℝ)) := by ring
end YangMills.Construction.BoxGaussian
end
