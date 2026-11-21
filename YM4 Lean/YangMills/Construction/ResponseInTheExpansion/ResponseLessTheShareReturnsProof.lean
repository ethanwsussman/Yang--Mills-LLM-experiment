import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ResponseInTheExpansion.GasPartHasItsBoundsProof
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheTotalOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseLessTheShareReturns
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ResponseInTheExpansion
namespace ResponseSubShare
open TorusFields
section Calculus
variable {n k : ℕ}
theorem mixedDeriv_const (a : ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (hk : 1 ≤ k) :
    mixedDeriv (fun _ : TorusField n => a) W c X = 0 := by
  unfold mixedDeriv
  rw [iteratedFDeriv_const_of_ne (by omega)]
  rfl
theorem mixedDeriv_zero (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField n => (0 : ℝ)) W c X = 0 := by apply _root_.YangMills.Construction.WilsonExpansion.mixedDeriv_zero <;> assumption
variable [NeZero n]
theorem mixedDeriv_congr_of_isCold (hc : ColdNearStatement) {s : ℝ} {G H : TorusField n → ℝ}
    {W : TorusField n} (hW : IsCold s W)
    (h : ∀ V, IsCold s V → G V = H V) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) :
    mixedDeriv G W c X = mixedDeriv H W c X := by
  have hev : (fun t : Fin k → ℝ => G (perturb c X t W)) =ᶠ[𝓝 0] fun t => H (perturb c X t W) := by
    have h0 : IsCold s (perturb c X (0 : Fin k → ℝ) W) := by rwa [perturb_zero]
    filter_upwards [hc n W k c X 0 s h0] with t ht
    exact h _ ht
  unfold mixedDeriv
  have e : iteratedFDeriv ℝ k (fun t : Fin k → ℝ => G (perturb c X t W)) 0 =
      iteratedFDeriv ℝ k (fun t : Fin k → ℝ => H (perturb c X t W)) 0 := by
    rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
    exact Filter.EventuallyEq.iteratedFDerivWithin_eq (by rwa [nhdsWithin_univ]) (Filter.EventuallyEq.eq_of_nhds hev) k
  rw [e]
theorem contDiffThreeAt_congr_of_isCold (hc : ColdNearStatement) {s : ℝ} {G H : TorusField n → ℝ}
    {W : TorusField n} (hW : IsCold s W)
    (h : ∀ V, IsCold s V → G V = H V) (hH : ContDiffThreeAt H W) : ContDiffThreeAt G W := by
  intro k c X
  have hev : (fun t : Fin k → ℝ => G (perturb c X t W)) =ᶠ[𝓝 0] fun t => H (perturb c X t W) := by
    have h0 : IsCold s (perturb c X (0 : Fin k → ℝ) W) := by rwa [perturb_zero]
    filter_upwards [hc n W k c X 0 s h0] with t ht
    exact h _ ht
  exact (hH k c X).congr_of_eventuallyEq hev
end Calculus
section Terms
variable {ℓ : TorusLumps.StepParameters} {e e₃ c e' e₃' c' : ℝ} {g g' : TorusLumps.LocalDensity}
theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
theorem TermBounds.add (h : TermBounds ℓ e e₃ c g) (h' : TermBounds ℓ e' e₃' c' g') :
    TermBounds ℓ (e + e') (e₃ + e₃') (c + c') fun n y W => g n y W + g' n y W := by apply _root_.YangMills.Construction.ResponseInTheExpansion.TermCalculus.termBounds_add <;> assumption
theorem termBounds_of_siteConstant (κ : (n : ℕ) → TorusSite n → ℝ)
    (hκ : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ y u : TorusSite n, κ n y = κ n (y + u)) :
    TermBounds ℓ 0 0 0 fun n y _ => κ n y := by
  refine ⟨⟨fun n _ hn y W hW k cc X => contDiffAt_const, fun _ _ _ _ _ _ _ => rfl, fun n _ hn y u W _ => hκ n hn y u⟩,
    fun n _ hn y W hW k cc X hk1 hk3 hX => ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k b X hk hb hu => ?_⟩
  · rw [mixedDeriv_const _ W cc X hk1]
    simp
  · have e0 : ∀ (p : ℕ) (z : TorusSite p), TorusLumps.centeredFamily (fun n y _ => κ n y) p z = fun _ => 0 := by
      intro p z
      funext V
      simp [TorusLumps.centeredFamily, TorusLumps.centered]
    rw [e0, e0, mixedDeriv_zero, mixedDeriv_zero]
    simp
theorem halfDensityBounds_of_termBounds (hc : ColdNearStatement) (hσ : 0 < ℓ.threshold)
    {F G : TorusLumps.LocalDensity} {E η₃ : ℝ}
    (h : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W → F n y W = G n y W)
    (hG : TermBounds ℓ e e₃ c G) (he : e ≤ 1 / 2 * E) (he₃ : e₃ ≤ 1 / 2 * (E / η₃)) (hcc : c ≤ 1 / 2 * E) :
    WeightedResponses.HalfDensityBounds ℓ E η₃ F := by
  refine ⟨⟨fun n _ hn y W hW => ?_, fun n _ hn y γ W hW => ?_, fun n _ hn y u W hW => ?_⟩,
    fun n _ hn y W hW k cc X hk1 hk3 hX => ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k b X hk hb hu => ?_⟩
  · exact contDiffThreeAt_congr_of_isCold hc hW (fun V hV => h n hn y V hV) (hG.admissible.smooth n hn y W hW)
  · have hg : IsCold ℓ.threshold (_root_.YangMills.Construction.TorusFields.gaugeTransform γ W) := fun x μ ν hμ => by
      rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
      exact hW x μ ν hμ
    rw [h n hn y _ hg, h n hn y _ hW, hG.admissible.gauge n hn y γ W hW]
  · have hs : IsCold ℓ.threshold (TorusFields.translate u W) := fun x μ ν hμ => by
      rw [curvature_translate]
      exact hW _ μ ν hμ
    rw [h n hn y _ hs, h n hn (y + u) _ hW, hG.admissible.translation n hn y u W hW]
  · rw [mixedDeriv_congr_of_isCold hc hW (fun V hV => h n hn y V hV)]
    refine (hG.derivDecay n hn y W hW k cc X hk1 hk3 hX).trans ?_
    have hw := weight_pos ℓ (supportDiam y cc)
    refine div_le_div_of_nonneg_right ?_ hw.le
    split_ifs
    · exact he₃
    · exact he
  · have centered_eq : ∀ {p : ℕ} [NeZero p] (hp : ℓ.n₀ ≤ p) (z : TorusSite p) (V : TorusField p),
        IsCold ℓ.threshold V →
        TorusLumps.centeredFamily F p z V = TorusLumps.centeredFamily G p z V := by
      intro p _ hp z V hV
      simp only [TorusLumps.centeredFamily, TorusLumps.centered]
      rw [h p hp z V hV, h p hp z _ (trivialField_isCold hσ p)]
    rw [mixedDeriv_congr_of_isCold hc cW (fun V hV => centered_eq hn y V hV),
      mixedDeriv_congr_of_isCold hc cW' (fun V hV => centered_eq hn' y' V hV)]
    refine (hG.centered_compare n n' hn hn' y y' W W' m h2 h2' cW cW' ag k b X hk hb hu).trans ?_
    have hw := weight_pos ℓ m
    have : c / ℓ.weight m ≤ 1 / 2 * E / ℓ.weight m := div_le_div_of_nonneg_right hcc hw.le
    exact this
end Terms
section BlockConstants
variable {R : StepSettings.StepSetup} {n : ℕ}
theorem blockConstantTerm_translate {A : WeightedResponses.ResponseSetup R} (hr : A.IsAdmissible)
    (hσ : 0 < R.params.threshold) [NeZero n] (hn : R.params.n₀ ≤ n) (Y u : TorusSite n) :
    blockConstantTerm A n Y = blockConstantTerm A n (Y + u) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.GasTermBounds.blockConstantTerm_add <;> assumption
end BlockConstants
section Arithmetic
theorem rpow_neg_half_le_two_mul {x x' : ℝ} (hx : 0 < x) (hx' : 0 < x') (h : x' ≤ 4 * x) :
    x ^ (-(1 / 2) : ℝ) ≤ 2 * x' ^ (-(1 / 2) : ℝ) := by
  have e : ∀ {u : ℝ}, 0 < u → u ^ (-(1 / 2) : ℝ) = (Real.sqrt u)⁻¹ := fun {u} hu => by
    rw [Real.rpow_neg hu.le, Real.sqrt_eq_rpow]
  rw [e hx, e hx']
  have s0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.sqrt x' ≤ 2 * Real.sqrt x := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hx.le
    nlinarith
  rw [inv_le_comm₀ s0 (by positivity)]
  have : (2 * (Real.sqrt x')⁻¹)⁻¹ = Real.sqrt x' / 2 := by
    field_simp
  rw [this]
  linarith
theorem termBounds_sum_le_half {C Ka x x' η ε : ℝ} (hx : 1 ≤ x) (hx' : 0 < x') (h4 : x' ≤ 4 * x) (hC : 0 ≤ C)
    (hK : 32 * C ≤ Ka) (hKa : 0 < Ka)
    (hη : 0 < η) (hη1 : η ≤ 1) (he : ε = Ka * x ^ (-(1 / 2) : ℝ)) :
    (((C * x ^ (-(3 / 2) : ℝ) + C * x ^ (-(1 / 2) : ℝ) + 2⁻¹ ^ 4 * ε) + C * x ^ (-(3 / 2) : ℝ)) + C * x ^ (-(3 / 2) : ℝ)) + 0 ≤
        1 / 2 * (Ka * x' ^ (-(1 / 2) : ℝ)) ∧
      (((C * x ^ (-(3 / 2) : ℝ) + C * x ^ (-(1 / 2) : ℝ) + 2⁻¹ ^ 5 * (ε / η)) + C * x ^ (-(3 / 2) : ℝ)) + C * x ^ (-(3 / 2) : ℝ)) + 0 ≤
        1 / 2 * (Ka * x' ^ (-(1 / 2) : ℝ) / η) := by
  have hx0 : 0 < x := by linarith
  set s : ℝ := x ^ (-(1 / 2) : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have h32 : x ^ (-(3 / 2) : ℝ) ≤ s := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hroot : s ≤ 2 * x' ^ (-(1 / 2) : ℝ) := rpow_neg_half_le_two_mul hx0 hx' h4
  set s' : ℝ := x' ^ (-(1 / 2) : ℝ) with hs'
  have hC3 : C * x ^ (-(3 / 2) : ℝ) ≤ C * s := mul_le_mul_of_nonneg_left h32 hC
  have hCs : 4 * (C * s) ≤ Ka * s / 8 := by nlinarith
  have hKs : Ka * s / 4 ≤ 1 / 2 * (Ka * s') := by nlinarith
  subst he
  have t4 : (2⁻¹ : ℝ) ^ 4 = 1 / 16 := by norm_num
  have t5 : (2⁻¹ : ℝ) ^ 5 = 1 / 32 := by norm_num
  rw [t4, t5]
  constructor
  · have hq : 0 < Ka * s := mul_pos hKa hs0
    linarith
  · have hinv : 1 ≤ 1 / η := by
      rw [le_div_iff₀ hη]
      linarith
    have hq : 0 < Ka * s := mul_pos hKa hs0
    have e1 : Ka * s / η = Ka * s * (1 / η) := by ring
    have e2 : 1 / 2 * (Ka * s' / η) = 1 / 2 * (Ka * s') * (1 / η) := by ring
    have h5 : Ka * s / 8 ≤ Ka * s * (1 / η) / 8 := by
      have := mul_le_mul_of_nonneg_left hinv hq.le
      linarith
    have h6 : Ka * s / 4 * (1 / η) ≤ 1 / 2 * (Ka * s') * (1 / η) :=
      mul_le_mul_of_nonneg_right hKs (by positivity)
    rw [e1, e2]
    set Kq : ℝ := Ka * s * (1 / η) with hKq
    have h7 : Ka * s / 4 * (1 / η) = Kq / 4 := by
      rw [hKq]
      ring
    rw [h7] at h6
    linarith
end Arithmetic
end ResponseSubShare
open TorusFields ResponseSubShare in
theorem responseSubShareBoundsStatement_holds (hone : imageOfOneAtBlockStatement)
    (hparts : responseTermDecompositionStatement)
    (hfam : meanOfFamilyAtStepStatement) (hcar : WeightedResponses.remaindersInvariantUnderIsometries)
    (hc : ColdNearStatement) : responseSubShareBoundsStatement := by
  intro a ha
  obtain ⟨L₀, r₁, hr₁, g₁⟩ := hparts a ha
  obtain ⟨r₂, hr₂, g₂⟩ := hone
  refine ⟨L₀, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), fun T hTa hL hT hC hOn hrt => ?_⟩
  obtain ⟨C, hC0, g₁⟩ := g₁ T hTa hL hT hC hOn (hrt.trans (min_le_left _ _))
  obtain ⟨C', y₃, hC'0, g₃⟩ := hfam T hT hOn
  refine ⟨max (32 * C) 1, fun K hKa hKb => ?_⟩
  obtain ⟨y₁, g₁⟩ := g₁ K hKb
  obtain ⟨y₂, g₂⟩ := g₂ T hT (hrt.trans (min_le_right _ _)) K
  refine ⟨max y₁ (max y₂ (max y₃ (max T.floorMin (2 * T.B + 1)))), fun y hy R A hK hA hArr => ?_⟩
  have e₁ : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have u₁ := le_trans (le_max_right _ _) hy
  have e₂ : y₂ ≤ y := le_trans (le_max_left _ _) u₁
  have u₂ := le_trans (le_max_right _ _) u₁
  have e₃ : y₃ ≤ y := le_trans (le_max_left _ _) u₂
  have u₃ := le_trans (le_max_right _ _) u₂
  have e₄ : T.floorMin ≤ y := le_trans (le_max_left _ _) u₃
  have e₅ : 2 * T.B + 1 ≤ y := le_trans (le_max_right _ _) u₃
  have hOn' := hA.onFamily
  have hB1 : 1 ≤ T.B := hT.B_ge
  have hxy : y ≤ R.coupling := hOn'.le_coupling
  have hmv := abs_le.1 hA.abs_sub_le
  have hx1 : 1 ≤ R.coupling := by linarith
  have hx'0 : 0 < R.nextCoupling := by linarith [hmv.1]
  have hx'4 : R.nextCoupling ≤ 4 * R.coupling := by linarith [hmv.2]
  have hσ : 0 < R.params.threshold := by
    rw [hOn'.params_eq]
    exact hT.σ_pos
  have hfit : R.params.Admissible := by
    rw [hOn'.params_eq]
    exact hT.fits y e₄
  have hr := hA.admissible
  have hKf : K.Admissible R.params := hK ▸ hr.params_admissible
  have hE : 0 < R.params.E := by
    rw [hOn'.params_eq]
    show 0 < T.E
    show 0 < 4 * T.B
    linarith
  have hη : K.η₃ = T.η₃ := by
    have h1 := hKf.E₃_eq
    have h2 : R.params.E₃ = R.params.E / T.η₃ := by
      rw [hOn'.params_eq]
      rfl
    rw [h2] at h1
    have h3 := hKf.η₃_pos
    have h4 := hT.η₃_pos
    exact mul_left_cancel₀ hE.ne' ((div_eq_div_iff h4.ne' h3.ne').1 h1)
  have hKa0 : 0 < K.Ka := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hKa)
  have hK32 : 32 * C ≤ K.Ka := (le_max_left _ _).trans hKa
  set ε : ℝ := K.Ka * R.coupling ^ (-(1 / 2) : ℝ) with hε
  have hε0 : 0 < ε := mul_pos hKa0 (Real.rpow_pos_of_pos (by linarith) _)
  have hfam₁ : WeightedResponses.ColdDensityBounds R.params ε (ε / T.η₃) A.siteRemainder := by
    have := hr.bounds.site_family
    rw [hK, hη] at this
    exact this
  have hcRa : TorusLumps.SumInvariantUnderIsometries R.params A.siteRemainder := (hcar T hT y e₄ R A hOn' hr).2
  have hF := (g₃ y e₃ R hOn' ε A.siteRemainder hε0 hfam₁ hcRa).1
  have hP := g₁ y e₁ R A hK hA hArr
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hOn'.params_eq]; rfl
  have part := ResponseSubShare.TermBounds.add (ResponseSubShare.TermBounds.add (ResponseSubShare.TermBounds.add
    (ResponseSubShare.TermBounds.add (ResponseSubShare.TermBounds.add hP.frame_bounds hP.increment_bounds) hF)
      hP.scoreTail_bounds) hP.gas_bounds)
    (termBounds_of_siteConstant (ℓ := R.params) (blockConstantTerm A) fun n _ hn y u =>
      blockConstantTerm_translate hr hσ hn y u)
  obtain ⟨r₁', r₂'⟩ := termBounds_sum_le_half (C := C) (Ka := K.Ka) (x := R.coupling) (x' := R.nextCoupling)
    (η := T.η₃) (ε := ε) hx1 hx'0 hx'4 hC0 hK32 hKa0 hT.η₃_pos hT.η₃_le hε
  rw [hη]
  refine halfDensityBounds_of_termBounds hc hσ (fun n _ hn Y W hW => ?_) part ?_ r₂' ?_
  · have h := g₂ y e₂ R A hK hA hC n hn Y W hW
    unfold WeightedResponses.responseSubShare WeightedResponses.responseAtOne ShareFamilies.levelShareFamily
    rw [dif_neg (NeZero.ne n), dif_neg (NeZero.ne n), h]
    have hl : R.params.coupling = T.coupling := by rw [hOn'.params_eq]; rfl
    ring
  · refine le_trans ?_ r₁'
    have : (2⁻¹ : ℝ) ^ 5 * ε ≤ 2⁻¹ ^ 4 * ε := by
      have : (2⁻¹ : ℝ) ^ 5 ≤ 2⁻¹ ^ 4 := by norm_num
      exact mul_le_mul_of_nonneg_right this hε0.le
    linarith
  · exact r₁'
end YangMills.Construction.ResponseInTheExpansion
end
