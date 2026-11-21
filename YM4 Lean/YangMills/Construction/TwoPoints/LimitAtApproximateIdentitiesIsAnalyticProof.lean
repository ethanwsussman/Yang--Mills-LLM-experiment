import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSumProof
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreePropertiesProof
import YangMills.Construction.TwoPoints.LimitAtApproximateIdentitiesIsAnalytic
import YangMills.Construction.TwoPoints.LocalKernelOfAFormProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace MollifierLimit
theorem euclidNorm_eq_norm_toLp (x : AmbientSpace) :
    euclidNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_eq_norm_toLp <;> assumption
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.euclidNorm_add_le <;> assumption
theorem euclidNorm_neg (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem euclidNorm_sub_le (x y : AmbientSpace) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem euclidNorm_half_smul (x : AmbientSpace) :
    euclidNorm ((1 / 2 : ℝ) • x) = euclidNorm x / 2 := by
  simp only [euclidNorm_eq_norm_toLp, WithLp.toLp_smul, norm_smul]
  norm_num
  ring
theorem euclidNorm_pos {v : AmbientSpace} (hv : v ≠ 0) : 0 < euclidNorm v := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_pos <;> assumption
theorem norm_le_euclidNorm (x : AmbientSpace) : ‖x‖ ≤ euclidNorm x := by apply _root_.YangMills.Construction.TwoPoints.AdmissibleFormConsequences.norm_le_euclidNorm <;> assumption
theorem isOpen_euclidOpenBall (c : AmbientSpace) (r : ℝ) : IsOpen (euclidOpenBall c r) := by apply _root_.YangMills.Construction.TwoPoints.LocalFormKernel.isOpen_euclidOpenBall <;> assumption
theorem ne_zero_of_mem_euclidOpenBall {a v : AmbientSpace} (ha : a ≠ 0)
    (hv : v ∈ euclidOpenBall a (2 * (euclidNorm a / 32))) : v ≠ 0 := by
  rintro rfl
  have h : euclidNorm ((0 : AmbientSpace) - a) < 2 * (euclidNorm a / 32) := hv
  rw [zero_sub, euclidNorm_neg] at h
  linarith [euclidNorm_pos ha]
theorem self_mem_euclidOpenBall {v : AmbientSpace} (hv : v ≠ 0) :
    v ∈ euclidOpenBall v (2 * (euclidNorm v / 32)) := by
  show euclidNorm (v - v) < _
  have h0 : euclidNorm (0 : AmbientSpace) = 0 := by simp [euclidNorm]
  rw [sub_self, h0]
  linarith [euclidNorm_pos hv]
theorem integral_norm_eq_one_of_nonneg {p : AmbientSpace → ℂ} (hp : Integrable p)
    (hn : ∀ x, IsRealNonneg (p x)) (h1 : lebesgueIntegral p = 1) : ∫ x, ‖p x‖ = 1 := by
  have h2 : ∀ x, ‖p x‖ = (p x).re := by
    intro x
    have hx : p x = (((p x).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using (hn x).1)
    rw [hx, Complex.norm_real, Real.norm_of_nonneg (by simpa using (hn x).2)]
    simp
  have h3 : ∫ x, (p x).re = (∫ x, p x).re :=
    (Complex.reCLM.integral_comp_comm hp)
  have h4 : ∫ x, p x = 1 := h1
  simp only [h2]
  rw [h3, h4]
  simp
theorem norm_iteratedIntegral_sub_le {p q G : AmbientSpace → ℂ} {c : ℂ} {η : ℝ}
    (hp : Continuous p) (hq : Continuous q) (hpc : IsCompact (tsupport p))
    (hqc : IsCompact (tsupport q)) (hpn : ∀ x, IsRealNonneg (p x))
    (hqn : ∀ x, IsRealNonneg (q x)) (hp1 : lebesgueIntegral p = 1)
    (hq1 : lebesgueIntegral q = 1) (hη : 0 ≤ η)
    (hG : ∀ y₁ ∈ tsupport p, ∀ y₂ ∈ tsupport q,
      ContinuousAt G (y₂ - y₁) ∧ ‖G (y₂ - y₁) - c‖ ≤ η) :
    ‖lebesgueIntegral (fun y₂ : AmbientSpace =>
      lebesgueIntegral fun y₁ : AmbientSpace => p y₁ * q y₂ * G (y₂ - y₁)) - c‖ ≤ η := by
  let Φ : AmbientSpace × AmbientSpace → ℂ := fun z => p z.2 * q z.1 * G (z.1 - z.2)
  let W : AmbientSpace × AmbientSpace → ℂ := fun z => q z.1 * p z.2
  have hclosed : IsClosed (tsupport q ×ˢ tsupport p) :=
    (isClosed_tsupport q).prod (isClosed_tsupport p)
  have hzero : ∀ z : AmbientSpace × AmbientSpace, z ∉ tsupport q ×ˢ tsupport p → W z = 0 := by
    intro z hz
    by_cases h1 : z.1 ∈ tsupport q
    · have h2 : z.2 ∉ tsupport p := fun h2 => hz ⟨h1, h2⟩
      simp [W, image_eq_zero_of_notMem_tsupport h2]
    · simp [W, image_eq_zero_of_notMem_tsupport h1]
  have hΦW : ∀ z, Φ z = W z * G (z.1 - z.2) := by
    intro z
    simp only [Φ, W]
    ring
  have hsubΦ : tsupport Φ ⊆ tsupport q ×ˢ tsupport p := by
    refine closure_minimal ?_ hclosed
    intro z hz
    by_contra hc
    exact hz (by rw [hΦW, hzero z hc, zero_mul])
  have hsubW : tsupport W ⊆ tsupport q ×ˢ tsupport p := by
    refine closure_minimal ?_ hclosed
    intro z hz
    by_contra hc
    exact hz (hzero z hc)
  have hcompact : IsCompact (tsupport q ×ˢ tsupport p) := hqc.prod hpc
  have hΦc : Continuous Φ := by
    refine continuous_of_tsupport fun z hz => ?_
    have hz' := hsubΦ hz
    have hGz : ContinuousAt G (z.1 - z.2) := (hG z.2 hz'.2 z.1 hz'.1).1
    have hsub : ContinuousAt (fun w : AmbientSpace × AmbientSpace => w.1 - w.2) z :=
      continuous_fst.continuousAt.sub continuous_snd.continuousAt
    have hcomp : ContinuousAt (fun w : AmbientSpace × AmbientSpace => G (w.1 - w.2)) z :=
      ContinuousAt.comp (f := fun w : AmbientSpace × AmbientSpace => w.1 - w.2) hGz hsub
    exact ((hp.comp continuous_snd).continuousAt.mul
      (hq.comp continuous_fst).continuousAt).mul hcomp
  have hWc : Continuous W := (hq.comp continuous_fst).mul (hp.comp continuous_snd)
  have hΦi : Integrable Φ ((volume : Measure AmbientSpace).prod volume) :=
    hΦc.integrable_of_hasCompactSupport
      (hcompact.of_isClosed_subset (isClosed_tsupport _) hsubΦ)
  have hWi : Integrable W ((volume : Measure AmbientSpace).prod volume) :=
    hWc.integrable_of_hasCompactSupport
      (hcompact.of_isClosed_subset (isClosed_tsupport _) hsubW)
  have hpi : Integrable p :=
    hp.integrable_of_hasCompactSupport hpc
  have hqi : Integrable q :=
    hq.integrable_of_hasCompactSupport hqc
  have hI : lebesgueIntegral (fun y₂ : AmbientSpace =>
      lebesgueIntegral fun y₁ : AmbientSpace => p y₁ * q y₂ * G (y₂ - y₁)) =
      ∫ z, Φ z ∂((volume : Measure AmbientSpace).prod volume) :=
    (integral_prod Φ hΦi).symm
  have hW1 : ∫ z, W z ∂((volume : Measure AmbientSpace).prod volume) = 1 := by
    have h := integral_prod_mul (μ := (volume : Measure AmbientSpace))
      (ν := (volume : Measure AmbientSpace)) q p
    have hq1' : ∫ x, q x = 1 := hq1
    have hp1' : ∫ x, p x = 1 := hp1
    rw [hq1', hp1', one_mul] at h
    exact h
  have hdiff : (∫ z, Φ z ∂((volume : Measure AmbientSpace).prod volume)) - c =
      ∫ z, (Φ z - c * W z) ∂((volume : Measure AmbientSpace).prod volume) := by
    rw [integral_sub hΦi (hWi.const_mul c), integral_const_mul, hW1, mul_one]
  have hbi : Integrable (fun z : AmbientSpace × AmbientSpace => η * (‖q z.1‖ * ‖p z.2‖))
      ((volume : Measure AmbientSpace).prod volume) :=
    (hqi.norm.mul_prod hpi.norm).const_mul η
  have hbound : ∀ z : AmbientSpace × AmbientSpace,
      ‖Φ z - c * W z‖ ≤ η * (‖q z.1‖ * ‖p z.2‖) := by
    intro z
    have hfac : Φ z - c * W z = W z * (G (z.1 - z.2) - c) := by
      rw [hΦW]
      ring
    by_cases hz : z ∈ tsupport q ×ˢ tsupport p
    · have hle := (hG z.2 hz.2 z.1 hz.1).2
      rw [hfac, norm_mul]
      have hW : ‖W z‖ = ‖q z.1‖ * ‖p z.2‖ := norm_mul _ _
      rw [hW, mul_comm]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    · rw [hfac, hzero z hz, zero_mul, norm_zero]
      positivity
  have hmass : ∫ z : AmbientSpace × AmbientSpace, η * (‖q z.1‖ * ‖p z.2‖)
      ∂((volume : Measure AmbientSpace).prod volume) = η := by
    rw [integral_const_mul]
    have h := integral_prod_mul (μ := (volume : Measure AmbientSpace))
      (ν := (volume : Measure AmbientSpace)) (fun x => ‖q x‖) (fun x => ‖p x‖)
    rw [h, integral_norm_eq_one_of_nonneg hqi hqn hq1, integral_norm_eq_one_of_nonneg hpi hpn hp1]
    ring
  rw [hI, hdiff, ← hmass]
  exact norm_integral_le_of_norm_le hbi (Eventually.of_forall hbound)
theorem translateFun_mem_ccInfIn {a : AmbientSpace → ℂ} {ρ r : ℝ} {v c : AmbientSpace}
    (ha : ContDiff ℝ ∞ a) (hc : IsCompact (tsupport a))
    (hs : tsupport a ⊆ euclidOpenBall (0 : AmbientSpace) ρ)
    (h : ρ + euclidNorm (v - c) ≤ r) : translateFun v a ∈ ccInfIn (euclidOpenBall c r) := by
  have ht : tsupport (translateFun v a) = (Homeomorph.subRight v) ⁻¹' tsupport a :=
    tsupport_comp_eq_preimage a (Homeomorph.subRight v)
  show ContDiff ℝ ∞ (translateFun v a) ∧ IsCompact (tsupport (translateFun v a)) ∧
    tsupport (translateFun v a) ⊆ euclidOpenBall c r
  refine ⟨ha.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
  · rw [ht]
    exact (Homeomorph.subRight v).isCompact_preimage.2 hc
  · intro x hx
    rw [ht] at hx
    have h1 : euclidNorm ((x - v) - 0) < ρ := hs hx
    rw [sub_zero] at h1
    have h2 : x - c = (x - v) + (v - c) := by abel
    show euclidNorm (x - c) < r
    rw [h2]
    linarith [euclidNorm_add_le (x - v) (v - c)]
theorem mem_compactC1Real_of_ccInfIn {f : AmbientSpace → ℂ} {O : Set AmbientSpace}
    (hf : f ∈ ccInfIn O) (him : ∀ x, (f x).im = 0) : f ∈ compactC1Real := by
  have hm : ContDiff ℝ ∞ f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O := hf
  show (ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ univ) ∧ ∀ x, (f x).im = 0
  exact ⟨⟨hm.1.of_le (by exact_mod_cast le_top), hm.2.1, subset_univ _⟩, him⟩
theorem actOn_addRight (v : AmbientSpace) (f : AmbientSpace → ℂ) :
    actOn (Equiv.addRight v) f = translateFun v f := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.actOn_addRight <;> assumption
theorem addRight_mem_euclideanMotions (v : AmbientSpace) : Equiv.addRight v ∈ euclideanMotions := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.addRight_mem_euclideanMotions <;> assumption
theorem tendsto_of_localKernel {St : FixedScale}
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} (hS : IsDisjointForm S)
    (hP : IsAdmissibleForm St S) (hA : MollifierTranslatesDisjoint.Statement)
    {a v : AmbientSpace} {F : AmbientSpace → ℂ} (ha : a ≠ 0)
    (hF : AnalyticOnNhd ℝ F (euclidOpenBall a (2 * (euclidNorm a / 32))))
    (hk : IsLocalKernelNear S a F) (hv : v ∈ euclidOpenBall a (2 * (euclidNorm a / 32)))
    {j : ℕ → AmbientSpace → ℂ} (hj : IsMollifierSeq j) :
    Tendsto (fun n : ℕ => ((S (j n) (translateFun v (j n)) : ℝ) : ℂ)) atTop (𝓝 (F v)) := by
  have hv0 : v ≠ 0 := ne_zero_of_mem_euclidOpenBall ha hv
  have hd : euclidNorm (v - a) < 2 * (euclidNorm a / 32) := hv
  obtain ⟨ε, hε⟩ : ∃ ε, ε = euclidNorm a / 32 := ⟨_, rfl⟩
  rw [← hε] at hd
  obtain ⟨d, hdd⟩ : ∃ d, d = euclidNorm (v - a) := ⟨_, rfl⟩
  rw [← hdd] at hd
  obtain ⟨w, hw⟩ : ∃ w : AmbientSpace, w = -((1 / 2 : ℝ) • (v - a)) := ⟨_, rfl⟩
  have hwn : euclidNorm (w - 0) = d / 2 := by
    rw [sub_zero, hw, euclidNorm_neg, euclidNorm_half_smul, hdd]
  have hwvn : euclidNorm ((w + v) - a) = d / 2 := by
    have h : (w + v) - a = (1 / 2 : ℝ) • (v - a) := by
      rw [hw]
      funext μ
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, euclidNorm_half_smul, hdd]
  have hr : 0 < ε - d / 2 := by linarith
  have hcont : ContinuousAt F v := (hF v hv).continuousAt
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hcont (η / 2) (half_pos hη)
  have ev1 : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < min (ε - d / 2) (δ / 2) :=
    Filter.Tendsto.eventually_lt_const (lt_min hr (half_pos hδ))
      tendsto_one_div_atTop_nhds_zero_nat
  have ev2 : ∀ᶠ n : ℕ in atTop, 2 / euclidNorm v ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have ev3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [ev1, ev2, ev3] with n h1 h2 h3
  have h1r : 1 / (n : ℝ) < ε - d / 2 := lt_of_lt_of_le h1 (min_le_left _ _)
  have h1δ : 1 / (n : ℝ) < δ / 2 := lt_of_lt_of_le h1 (min_le_right _ _)
  have hm : ContDiff ℝ ∞ (j n) ∧ IsCompact (tsupport (j n)) ∧
      tsupport (j n) ⊆ euclidOpenBall (0 : AmbientSpace) (1 / (n : ℝ)) := (hj n h3).1.1
  have him : ∀ x, (j n x).im = 0 := (hj n h3).1.2
  have hnn : ∀ x, IsRealNonneg (j n x) := (hj n h3).2.1
  have hint : lebesgueIntegral (j n) = 1 := (hj n h3).2.2
  obtain ⟨hsm, hcpt, hsup⟩ := hm
  obtain ⟨hja, hjb, hdis⟩ := hA.2 v hv0 j hj n h2
  have hk₁ : translateFun w (j n) ∈ ccInfIn (euclidOpenBall (0 : AmbientSpace) ε) :=
    translateFun_mem_ccInfIn hsm hcpt hsup (by rw [hwn]; linarith)
  have hk₂ : translateFun (w + v) (j n) ∈ ccInfIn (euclidOpenBall a ε) :=
    translateFun_mem_ccInfIn hsm hcpt hsup (by rw [hwvn]; linarith)
  have hk₁r : translateFun w (j n) ∈ compactC1Real :=
    mem_compactC1Real_of_ccInfIn hk₁ fun x => him _
  have hk₂r : translateFun (w + v) (j n) ∈ compactC1Real :=
    mem_compactC1Real_of_ccInfIn hk₂ fun x => him _
  have hinv := hP.invariantPositive.1 (Equiv.addRight w) (addRight_mem_euclideanMotions w)
    (j n) hja (translateFun v (j n)) hjb hdis
  have hdouble : translateFun w (translateFun v (j n)) = translateFun (w + v) (j n) := by
    funext x
    simp only [translateFun, sub_sub]
  rw [actOn_addRight, actOn_addRight, hdouble] at hinv
  have hrep := hk (translateFun w (j n)) (hε ▸ hk₁) (translateFun (w + v) (j n)) (hε ▸ hk₂)
  rw [hS.complexifyForm_of_mem_compactC1Real hk₁r hk₂r, hinv] at hrep
  have hcj : Continuous (j n) := hsm.continuous
  have hts : ∀ u : AmbientSpace, tsupport (translateFun u (j n)) =
      (Homeomorph.subRight u) ⁻¹' tsupport (j n) := fun u =>
    tsupport_comp_eq_preimage (j n) (Homeomorph.subRight u)
  have hcptu : ∀ u : AmbientSpace, IsCompact (tsupport (translateFun u (j n))) := fun u => by
    rw [hts]
    exact (Homeomorph.subRight u).isCompact_preimage.2 hcpt
  have hintu : ∀ u : AmbientSpace, lebesgueIntegral (translateFun u (j n)) = 1 := fun u => by
    rw [← hint]
    exact integral_sub_right_eq_self (j n) u
  have hbound := norm_iteratedIntegral_sub_le (p := translateFun w (j n))
    (q := translateFun (w + v) (j n)) (G := F) (c := F v) (η := η / 2)
    (hcj.comp (continuous_id.sub continuous_const))
    (hcj.comp (continuous_id.sub continuous_const)) (hcptu _) (hcptu _)
    (fun x => hnn _) (fun x => hnn _) (hintu _) (hintu _) (half_pos hη).le ?_
  · rw [dist_eq_norm, hrep]
    linarith
  · intro y₁ hy₁ y₂ hy₂
    rw [hts] at hy₁ hy₂
    have a₁ : euclidNorm ((y₁ - w) - 0) < 1 / (n : ℝ) := hsup hy₁
    have a₂ : euclidNorm ((y₂ - (w + v)) - 0) < 1 / (n : ℝ) := hsup hy₂
    rw [sub_zero] at a₁ a₂
    have hy : y₂ - y₁ - v = (y₂ - (w + v)) - (y₁ - w) := by abel
    have hyv : euclidNorm (y₂ - y₁ - v) < 2 / (n : ℝ) := by
      have e : (2 : ℝ) / n = 1 / n + 1 / n := by ring
      rw [hy, e]
      linarith [euclidNorm_sub_le (y₂ - (w + v)) (y₁ - w)]
    have e2 : (2 : ℝ) / n = 2 * (1 / n) := by ring
    have hball : y₂ - y₁ ∈ euclidOpenBall a (2 * (euclidNorm a / 32)) := by
      show euclidNorm (y₂ - y₁ - a) < _
      have h4 : y₂ - y₁ - a = (y₂ - y₁ - v) + (v - a) := by abel
      rw [h4, ← hε]
      have := euclidNorm_add_le (y₂ - y₁ - v) (v - a)
      rw [← hdd] at this
      rw [e2] at hyv
      linarith
    refine ⟨(hF _ hball).continuousAt, ?_⟩
    have hdist : dist (y₂ - y₁) v < δ := by
      rw [dist_eq_norm]
      have := norm_le_euclidNorm (y₂ - y₁ - v)
      rw [e2] at hyv
      linarith
    have := hδF hdist
    rw [dist_eq_norm] at this
    exact this.le
end MollifierLimit
open MollifierLimit in
theorem mollifierLimitAnalytic_of_localFormKernel (hLocal : LocalFormKernel.Statement)
    (hA : MollifierTranslatesDisjoint.Statement) : MollifierLimitAnalytic := by
  intro St S hS hP
  have hex := fun (v : AmbientSpace) (hv : v ≠ 0) => hLocal St S hS hP v hv
  choose! F hFan hFk using hex
  obtain ⟨j₀, hj₀⟩ := hA.1
  have hlim : ∀ a : AmbientSpace, a ≠ 0 → ∀ v ∈ euclidOpenBall a (2 * (euclidNorm a / 32)),
      ∀ j : ℕ → AmbientSpace → ℂ, IsMollifierSeq j →
        Tendsto (fun n : ℕ => ((S (j n) (translateFun v (j n)) : ℝ) : ℂ)) atTop (𝓝 (F a v)) :=
    fun a ha v hv j hj => tendsto_of_localKernel hS hP hA ha (hFan a ha) (hFk a ha) hv hj
  let K : AmbientSpace → ℝ := fun v => (F v v).re
  have hreal : ∀ v : AmbientSpace, v ≠ 0 → ((K v : ℝ) : ℂ) = F v v := by
    intro v hv
    have h := (Complex.continuous_im.tendsto _).comp
      (hlim v hv v (self_mem_euclidOpenBall hv) j₀ hj₀)
    have h0 : Tendsto (Complex.im ∘ fun n : ℕ =>
        ((S (j₀ n) (translateFun v (j₀ n)) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have he : (Complex.im ∘ fun n : ℕ => ((S (j₀ n) (translateFun v (j₀ n)) : ℝ) : ℂ)) =
          fun _ => (0 : ℝ) := by
        funext n
        simp
      rw [he]
      exact tendsto_const_nhds
    have him : (F v v).im = 0 := tendsto_nhds_unique h h0
    exact Complex.ext (by simp [K]) (by simp [him])
  have hagree : ∀ a : AmbientSpace, a ≠ 0 → ∀ v ∈ euclidOpenBall a (2 * (euclidNorm a / 32)),
      F a v = ((K v : ℝ) : ℂ) := by
    intro a ha v hv
    have hv0 := ne_zero_of_mem_euclidOpenBall ha hv
    rw [hreal v hv0]
    exact tendsto_nhds_unique (hlim a ha v hv j₀ hj₀)
      (hlim v hv0 v (self_mem_euclidOpenBall hv0) j₀ hj₀)
  refine ⟨K, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v ≠ 0 := hv
    have hnhds : euclidOpenBall v (2 * (euclidNorm v / 32)) ∈ 𝓝 v :=
      (isOpen_euclidOpenBall _ _).mem_nhds (self_mem_euclidOpenBall hv')
    refine (hFan v hv' v (self_mem_euclidOpenBall hv')).congr ?_
    filter_upwards [hnhds] with y hy using hagree v hv' y hy
  · intro v hv j hj
    have h := hlim v hv v (self_mem_euclidOpenBall hv) j hj
    rw [← hreal v hv] at h
    have h2 := (Complex.continuous_re.tendsto _).comp h
    simpa [Function.comp_def] using h2
  · intro v hv k₁ hk₁ k₂ hk₂
    rw [hFk v hv k₁ hk₁ k₂ hk₂]
    have hs₁ : tsupport k₁ ⊆ euclidOpenBall (0 : AmbientSpace) (euclidNorm v / 32) :=
      (show ContDiff ℝ ∞ k₁ ∧ IsCompact (tsupport k₁) ∧
        tsupport k₁ ⊆ euclidOpenBall (0 : AmbientSpace) (euclidNorm v / 32) from hk₁).2.2
    have hs₂ : tsupport k₂ ⊆ euclidOpenBall v (euclidNorm v / 32) :=
      (show ContDiff ℝ ∞ k₂ ∧ IsCompact (tsupport k₂) ∧
        tsupport k₂ ⊆ euclidOpenBall v (euclidNorm v / 32) from hk₂).2.2
    refine congrArg lebesgueIntegral (funext fun y₂ =>
      congrArg lebesgueIntegral (funext fun y₁ => ?_))
    by_cases h₁ : y₁ ∈ tsupport k₁
    · by_cases h₂ : y₂ ∈ tsupport k₂
      · have a₁ : euclidNorm (y₁ - 0) < euclidNorm v / 32 := hs₁ h₁
        have a₂ : euclidNorm (y₂ - v) < euclidNorm v / 32 := hs₂ h₂
        rw [sub_zero] at a₁
        have hball : y₂ - y₁ ∈ euclidOpenBall v (2 * (euclidNorm v / 32)) := by
          show euclidNorm (y₂ - y₁ - v) < _
          have h4 : y₂ - y₁ - v = (y₂ - v) - y₁ := by abel
          rw [h4]
          linarith [euclidNorm_sub_le (y₂ - v) y₁]
        rw [hagree v hv _ hball]
      · simp [image_eq_zero_of_notMem_tsupport h₂]
    · simp [image_eq_zero_of_notMem_tsupport h₁]
end YangMills.Construction.TwoPoints
end
