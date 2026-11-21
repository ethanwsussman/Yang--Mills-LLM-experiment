import YangMills.Construction.CellOfTheFlow.MomentsOfTheClassesNearABox
import YangMills.Construction.ResponseInTheExpansion.LevelsBelowATupleProof
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALawProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusLumps RenormalizationStepParameters TorusFields CellWindows FreeEnergies ClusterExpansionOfAStep
variable {ℓ : TorusLumps.StepParameters}
private theorem coarseLabelScore_const_mul {Ω : Type} {L : ℕ} (c s₁ : ℝ) (f g : Ω → ℝ) (h : ∀ w, f w = c * g w)
    (w : CoarseLabel Ω L) :
    coarseLabelScore (c * s₁) f w = c * coarseLabelScore s₁ g w := by
  rcases w with _ | st
  · rfl
  · show c * s₁ + ∑ o : BlockOffset L, Sum.elim (fun _ => 0) f (st.siteLabel o) =
      c * (s₁ + ∑ o : BlockOffset L, Sum.elim (fun _ => 0) g (st.siteLabel o))
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    rcases st.siteLabel o with _ | a
    · simp
    · simpa using h a
private theorem labelMajorant_const_mul (T : StageTower ℓ) (c s : ℝ) :
    ∀ (t : ℕ) (w : (T.stage t).labels.Ω), labelMajorant T 0 (c * s) t w = c * labelMajorant T 0 s t w := by
  intro t
  induction t with
  | zero =>
    intro w
    show (0 : ℝ) = c * 0
    simp
  | succ t ih =>
    intro w
    exact coarseLabelScore_const_mul c s _ _ ih w
private theorem score_eq_labelMajorant {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {k : ℕ}
    (hS : S.FollowsFlow β k) : ∀ t ≤ k, (S.setup t).score = labelMajorant T 0 S.params.s₁ t := by
  intro t
  induction t with
  | zero =>
    intro _
    funext w
    exact hS.score_zero w
  | succ t ih =>
    intro ht
    rw [hS.score_succ t (by omega), ih (by omega)]
    rfl
private theorem isTowerOnParameters_of_followsFlow {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {k : ℕ}
    (hS : S.FollowsFlow β k) : IsTowerAtParameters Tb y T β k := by
  refine ⟨hS.startsAtWilson, fun j hj => ?_, fun j hj => (hS.isFlowStep j hj).onFamily⟩
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · exact (hS.isFlowStep j (by omega)).coupling_eq
  · have e : j = k + 1 := by omega
    subst e
    exact (hS.isFlowStep k le_rfl).nextCoupling_eq
private theorem siteScore_nonneg {Ω : Type} {n : ℕ} [NeZero n] (s : Ω → ℝ) (hs : ∀ w, 0 ≤ s w)
    (Y : Finset (TorusSite n)) (ω : Y → Ω)
    (z : TorusSite n) : 0 ≤ siteScore s Y ω z := by
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
private theorem siteMajorant_le_majorantNearBox (T : StageTower ℓ) (s₁ : ℝ) (k n : ℕ) [NeZero n]
    (hs : ∀ w : (T.stage k).labels.Ω, 0 ≤ labelMajorant T 0 s₁ k w) (u : MarkedSample ℓ k n) (z : TorusSite n) :
    siteMajorant T 0 s₁ k n u z ≤ majorantNearBox T 0 s₁ k n u z 1 := by
  classical
  have hn : ∀ y, 0 ≤ siteMajorant T 0 s₁ k n u y := fun y => siteScore_nonneg _ hs _ _ _
  have hinner : ∀ X : Finset (TorusSite n), 0 ≤ ∑ y ∈ X, siteMajorant T 0 s₁ k n u y := fun X =>
    Finset.sum_nonneg fun y _ => hn y
  unfold majorantNearBox
  by_cases hz : z ∈ stageHull T k n u
  · have hcov : z ∈ (chainComponents (stageRange T k) (stageHull T k n u)).biUnion id := by
      rw [biUnion_chainComponents]
      exact hz
    obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.1 hcov
    have hXn : X ∈ componentsNearBox T k n u z 1 := by
      refine Finset.mem_filter.2 ⟨hX, z, hzX, z, ?_, ?_⟩
      · rw [supDist_self]
        norm_num
      · rw [supDist_self]
        exact Nat.zero_le _
    calc siteMajorant T 0 s₁ k n u z ≤ ∑ y ∈ X, siteMajorant T 0 s₁ k n u y :=
          Finset.single_le_sum (f := fun y => siteMajorant T 0 s₁ k n u y) (fun y _ => hn y) hzX
      _ ≤ _ := Finset.single_le_sum (f := fun X => ∑ y ∈ X, siteMajorant T 0 s₁ k n u y) (fun X _ => hinner X) hXn
  · have e : siteMajorant T 0 s₁ k n u z = 0 := by
      unfold siteMajorant siteScore
      exact dif_neg hz
    rw [e]
    exact Finset.sum_nonneg fun X _ => hinner X
private theorem measurable_majorantNearBox (hSt : StageStatesMeasurableStatement) (hfit : ℓ.Admissible)
    (T : StageTower ℓ) (s₁ : ℝ) (k n : ℕ)
    [NeZero n] (hm : Measurable (labelMajorant T 0 s₁ k)) (z : TorusSite n) (R : ℝ) :
    Measurable fun u : MarkedSample ℓ k n => majorantNearBox T 0 s₁ k n u z R := by
  classical
  let H : (Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω)) → ℝ := fun q =>
    ∑ X ∈ (chainComponents (stageRange T k) q.1).filter
        (fun X => ∃ z' ∈ X, ∃ w, (supDist w z : ℝ) ≤ R ∧ supDist z' w ≤ 1),
      ∑ y ∈ X, siteScore (labelMajorant T 0 s₁ k) q.1 q.2 y
  have hH : Measurable H := by
    refine fun _ ht => MeasurableSpace.measurableSet_iInf.2 fun Y => ?_
    have hY : Measurable fun ω : Y → (T.stage k).labels.Ω => H ⟨Y, ω⟩ := by
      show Measurable fun ω : Y → (T.stage k).labels.Ω =>
        ∑ X ∈ (chainComponents (stageRange T k) Y).filter
            (fun X => ∃ z' ∈ X, ∃ w, (supDist w z : ℝ) ≤ R ∧ supDist z' w ≤ 1),
          ∑ y ∈ X, siteScore (labelMajorant T 0 s₁ k) Y ω y
      refine Finset.measurable_sum _ fun X _ => Finset.measurable_sum _ fun y _ => ?_
      by_cases hy : y ∈ Y
      · have e : (fun ω : Y → (T.stage k).labels.Ω => siteScore (labelMajorant T 0 s₁ k) Y ω y) =
            fun ω => labelMajorant T 0 s₁ k (ω ⟨y, hy⟩) := by
          funext ω
          simp [siteScore, hy]
        show Measurable fun ω : Y → (T.stage k).labels.Ω => siteScore (labelMajorant T 0 s₁ k) Y ω y
        rw [e]
        exact hm.comp (measurable_pi_apply _)
      · have e : (fun ω : Y → (T.stage k).labels.Ω => siteScore (labelMajorant T 0 s₁ k) Y ω y) = fun _ => 0 := by
          funext ω
          simp [siteScore, hy]
        show Measurable fun ω : Y → (T.stage k).labels.Ω => siteScore (labelMajorant T 0 s₁ k) Y ω y
        rw [e]
        exact measurable_const
    exact hY ht
  have h2 : Measurable fun u : MarkedSample ℓ k n => (stageState T k n u).2 :=
    measurable_snd.comp (hSt ℓ hfit T k n)
  exact hH.comp h2
private theorem one_add_pow_le_two_pow_mul (b : ℝ) (hb : 0 ≤ b) (P : ℕ) : (1 + b) ^ P ≤ 2 ^ P * (1 + b ^ P) := by apply _root_.YangMills.SharedProofs.p7069 <;> assumption
private theorem one_add_mean_pow_le {ι : Type} (A : Finset ι) (a : ι → ℝ) (ha : ∀ z, 0 ≤ a z) (P : ℕ) (hP : 1 ≤ P) :
    (1 + ((A.card : ℝ))⁻¹ * ∑ z ∈ A, a z) ^ P ≤ 2 ^ P * (1 + ((A.card : ℝ))⁻¹ * ∑ z ∈ A, a z ^ P) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
    exact one_le_pow₀ (by norm_num)
  have hb : 0 ≤ ((A.card : ℝ))⁻¹ * ∑ z ∈ A, a z := by
    have : 0 ≤ ∑ z ∈ A, a z := Finset.sum_nonneg fun z _ => ha z
    positivity
  refine (one_add_pow_le_two_pow_mul _ hb P).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hj := Real.pow_arith_mean_le_arith_mean_pow A (fun _ => ((A.card : ℝ))⁻¹) a (fun _ _ => by positivity)
    (by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp) (fun z _ => ha z) P
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
  linarith
private theorem integrable_and_integral_le_of_lintegral_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ) (hm : Measurable F)
    (h0 : ∀ u, 0 ≤ F u) (c : ℝ) (hc : 0 ≤ c) (hb : ∫⁻ u, ENNReal.ofReal (F u) ∂μ ≤ ENNReal.ofReal c) :
    Integrable F μ ∧ ∫ u, F u ∂μ ≤ c := by apply _root_.YangMills.SharedProofs.p45438 <;> assumption
private theorem lintegral_pow_le_of_le_one_add_mean {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Finset ι)
    (N : Ω → ℝ) (a : ι → Ω → ℝ) (P : ℕ) (hP : 1 ≤ P) (h0 : ∀ z u, 0 ≤ a z u) (hN0 : ∀ u, 0 ≤ N u)
    (hN : ∀ u, N u ≤ 1 + ((A.card : ℝ))⁻¹ * ∑ z ∈ A, a z u)
    (hi : ∀ z, Integrable (fun u => a z u ^ P) μ) (B : ℝ) (hB : ∀ z, ∫ u, a z u ^ P ∂μ ≤ B) (hB0 : 0 ≤ B) :
    ∫⁻ u, ENNReal.ofReal (N u ^ P) ∂μ ≤ ENNReal.ofReal (2 ^ P * (1 + B)) := by
  classical
  let G : Ω → ℝ := fun u => 2 ^ P * (1 + ((A.card : ℝ))⁻¹ * ∑ z ∈ A, a z u ^ P)
  have hGi : Integrable G μ :=
    ((integrable_const 1).add ((integrable_finset_sum _ fun z _ => hi z).const_mul _)).const_mul _
  have hG0 : 0 ≤ᵐ[μ] G := Filter.Eventually.of_forall fun u => by
    have : 0 ≤ ∑ z ∈ A, a z u ^ P := Finset.sum_nonneg fun z _ => pow_nonneg (h0 z u) P
    show 0 ≤ G u
    simp only [G]
    positivity
  have hle : ∀ u, N u ^ P ≤ G u := fun u =>
    (pow_le_pow_left₀ (hN0 u) (hN u) P).trans (one_add_mean_pow_le A (fun z => a z u) (fun z => h0 z u) P hP)
  have hint : ∫ u, G u ∂μ ≤ 2 ^ P * (1 + B) := by
    have e : ∫ u, G u ∂μ = 2 ^ P * (1 + ((A.card : ℝ))⁻¹ * ∑ z ∈ A, ∫ u, a z u ^ P ∂μ) := by
      simp only [G]
      rw [integral_const_mul, integral_add (integrable_const 1) ((integrable_finset_sum _ fun z _ => hi z).const_mul _),
        integral_const_mul, integral_finset_sum _ fun z _ => hi z]
      simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 : ∑ z ∈ A, ∫ u, a z u ^ P ∂μ ≤ (A.card : ℝ) * B := by
      calc _ ≤ ∑ _z ∈ A, B := Finset.sum_le_sum fun z _ => hB z
        _ = _ := by simp
    have h3 : ((A.card : ℝ))⁻¹ * ∑ z ∈ A, ∫ u, a z u ^ P ∂μ ≤ B := by
      rcases A.eq_empty_or_nonempty with rfl | hA
      · simpa using hB0
      have hc : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
      rw [inv_mul_le_iff₀ hc]
      exact h2
    linarith
  calc ∫⁻ u, ENNReal.ofReal (N u ^ P) ∂μ ≤ ∫⁻ u, ENNReal.ofReal (G u) ∂μ :=
        lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hle u)
    _ = ENNReal.ofReal (∫ u, G u ∂μ) := (ofReal_integral_eq_lintegral_ofReal hGi hG0).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hint
private theorem two_pow_mul_one_add_le (C Λ : ℝ) (P : ℕ) (hP : 1 ≤ P) (hΛ : 1 ≤ Λ) :
    2 ^ P * (1 + 16 ^ P * (|C| * Λ ^ P)) ≤ (2 * 17 * (1 + |C|) * Λ) ^ P := by
  have hC := abs_nonneg C
  have hΛP : (1 : ℝ) ≤ Λ ^ P := one_le_pow₀ hΛ
  have h16 : (1 : ℝ) ≤ 16 ^ P := one_le_pow₀ (by norm_num)
  have h1 : 1 + 16 ^ P * (|C| * Λ ^ P) ≤ 16 ^ P * Λ ^ P * (1 + |C|) := by
    have h2 : (1 : ℝ) ≤ 16 ^ P * Λ ^ P := one_le_mul_of_one_le_of_one_le h16 hΛP
    have e : 16 ^ P * Λ ^ P * (1 + |C|) = 16 ^ P * Λ ^ P + 16 ^ P * (|C| * Λ ^ P) := by ring
    rw [e]
    linarith
  have h3 : 1 + |C| ≤ (1 + |C|) ^ P := le_self_pow₀ (by linarith) (by omega)
  have h4 : (0 : ℝ) ≤ 16 ^ P * Λ ^ P := by positivity
  calc 2 ^ P * (1 + 16 ^ P * (|C| * Λ ^ P)) ≤ 2 ^ P * (16 ^ P * Λ ^ P * (1 + |C|) ^ P) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 h4)) (by positivity)
    _ = (2 * 16 * (1 + |C|) * Λ) ^ P := by
        rw [mul_pow, mul_pow, mul_pow]
        ring
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ P
        have : 0 ≤ (1 + |C|) * Λ := by positivity
        nlinarith
private theorem siteScore_const_mul {Ω : Type} {n : ℕ} [NeZero n] (c : ℝ) (s : Ω → ℝ) (Y : Finset (TorusSite n))
    (ω : Y → Ω) (z : TorusSite n) :
    siteScore (fun w => c * s w) Y ω z = c * siteScore s Y ω z := by
  unfold siteScore
  split_ifs <;> simp
theorem meanScoreMoments_holds (hCell : majorantNearBoxMomentsStatement)
    (hSt : StageStatesMeasurableStatement) (hTwo : TwoPointByTotalCovarianceStatement) :
    meanScoreMomentsStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := hCell a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hodd hL Tb hTa hTL hD hcs hOn hrt' hC K
  obtain ⟨y₀, hy₀⟩ := h L hodd hL Tb hTa hTL hD hcs hOn hrt' hC 0 (|K.s₁| / 16) le_rfl (by positivity)
  refine ⟨max y₀ Tb.floorMin, fun y hy hR => ?_⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y ((le_max_right _ _).trans hy)
  have hcell := hy₀ y ((le_max_left _ _).trans hy) hR.returns_at hR.wilson_expansion
  refine ⟨Real.exp 1, fun P hP => ?_⟩
  obtain ⟨Cp, hCp, -⟩ := hcell 1 P le_rfl hP
  refine ⟨2 * 17 * (1 + |Cp|), ?_, ?_⟩
  · have := abs_nonneg Cp
    nlinarith
  intro T S β k m g hK hS hR' hx hside
  have hresp := hS.isAdmissible k le_rfl
  have hlet : (S.setup k).responseParams = K := (hS.params_eq k).trans hK
  have hKfit : K.Admissible (Tb.stepParameters y) := hlet ▸ hresp.params_admissible
  have hs₁ : 0 ≤ K.s₁ := by
    rw [hKfit.s₁_eq, hKfit.C₀_eq]
    have h1 := hfit.a_ge
    have h2 := hKfit.N₀_nonneg
    have h3 := hKfit.Kc_ge
    positivity
  set s' : ℝ := |K.s₁| / 16 with hs'
  have hs16 : 16 * s' = S.params.s₁ := by
    rw [hs', abs_of_nonneg hs₁, hK]
    ring
  have hmajt : ∀ t ≤ k, (S.setup t).score = fun w => 16 * labelMajorant T 0 s' t w := by
    intro t ht
    rw [score_eq_labelMajorant hS t ht, ← hs16]
    funext w
    exact labelMajorant_const_mul T 16 s' t w
  have hmaj := hmajt k le_rfl
  have hcarry : PaysMajorant Tb y T (16 * 0) (16 * s') k := by
    intro t ht
    rw [mul_zero, hs16, ← score_eq_labelMajorant hS t ht]
    exact (hS.isAdmissible t ht).price
  have hScaleFlow : IsTowerAtParametersMeasurable Tb y T β k := ⟨isTowerOnParameters_of_followsFlow hS, hS.marksMeasurable⟩
  have hcoup : (T.stage k).coupling = flowCoupling (Tb.stepParameters y) β k := (hS.isFlowStep k le_rfl).coupling_eq
  have hb : ∀ z, ∫⁻ u, ENNReal.ofReal (majorantNearBox T 0 s' k _ u z 1 ^ P)
      ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤
      ENNReal.ofReal (Cp * ((stageRange T k : ℝ) ^ 4 * Real.log (T.stage k).coupling) ^ P) := fun z =>
    hCp T β 0 k hScaleFlow le_rfl (by simp) hcarry m hside z
  obtain ⟨hprob, -⟩ := hTwo (Tb.stepParameters y) hfit hfit.depth_lt T hS.isCutoff_bottom hS.marksMeasurable β
    S.coeffs k (2 * (Tb.stepParameters y).side ^ m)
  have hs0 : ∀ w, 0 ≤ labelMajorant T 0 s' k w := by
    intro w
    have h1 := hresp.price.nonneg w
    rw [hmaj] at h1
    simp only at h1
    linarith
  have hsm : Measurable (labelMajorant T 0 s' k) := by
    have h1 := hresp.price.borel
    rw [hmaj] at h1
    have h2 := h1.const_mul (16⁻¹ : ℝ)
    have e : (fun w => (16⁻¹ : ℝ) * (16 * labelMajorant T 0 s' k w)) = labelMajorant T 0 s' k := by
      funext w
      ring
    rw [e] at h2
    exact h2
  have hSg0 : ∀ z (u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m)),
      0 ≤ majorantNearBox T 0 s' k _ u z 1 := fun z u =>
    Finset.sum_nonneg fun X _ => Finset.sum_nonneg fun y' _ => siteScore_nonneg _ hs0 _ _ _
  have hmeas : ∀ z, Measurable fun u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m) =>
      majorantNearBox T 0 s' k _ u z 1 := fun z => measurable_majorantNearBox hSt hfit T s' k _ hsm z 1
  set Λ : ℝ := (clusterRange (flowCoupling (Tb.stepParameters y) β k) : ℝ) ^ 4 *
    Real.log (flowCoupling (Tb.stepParameters y) β k) with hΛ
  have hx1 : Real.exp 1 ≤ flowCoupling (Tb.stepParameters y) β k := hx
  have hxpos : 0 < flowCoupling (Tb.stepParameters y) β k := lt_of_lt_of_le (Real.exp_pos 1) hx1
  have hlog : 1 ≤ Real.log (flowCoupling (Tb.stepParameters y) β k) := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact hx1
  have hr1 : (1 : ℝ) ≤ (clusterRange (flowCoupling (Tb.stepParameters y) β k) : ℝ) := by
    have hxge : 1 ≤ flowCoupling (Tb.stepParameters y) β k := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h1 : 1 ≤ flowCoupling (Tb.stepParameters y) β k ^ ((1 : ℝ) / 100) := Real.one_le_rpow hxge (by norm_num)
    exact h1.trans (Nat.le_ceil _)
  have hΛ1 : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr1) hlog
  have hb' : ∀ z, ∫⁻ u, ENNReal.ofReal (majorantNearBox T 0 s' k _ u z 1 ^ P)
      ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤
      ENNReal.ofReal (|Cp| * Λ ^ P) := by
    intro z
    refine (hb z).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : (stageRange T k : ℝ) ^ 4 * Real.log (T.stage k).coupling = Λ := by
      rw [hΛ, ← hcoup]
      rfl
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity)
  have hone : ∀ z, Integrable (fun u => majorantNearBox T 0 s' k _ u z 1 ^ P)
      (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ∧
      ∫ u, majorantNearBox T 0 s' k _ u z 1 ^ P ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤
        |Cp| * Λ ^ P := fun z =>
    integrable_and_integral_le_of_lintegral_le _ _ ((hmeas z).pow_const P) (fun u => pow_nonneg (hSg0 z u) P) _
      (by positivity) (hb' z)
  have hmean := lintegral_pow_le_of_le_one_add_mean (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m))
    (functionSites (Tb.stepParameters y).side g k (2 * (Tb.stepParameters y).side ^ m))
    (fun u => scoreMeanOver S g k (2 * (Tb.stepParameters y).side ^ m) (stageState T k _ u))
    (fun z u => 16 * majorantNearBox T 0 s' k _ u z 1) P hP (fun z u => by have := hSg0 z u; positivity)
    (fun u => ?_) (fun u => ?_) (fun z => ?_) (16 ^ P * (|Cp| * Λ ^ P)) (fun z => ?_) (by positivity)
  · refine hmean.trans (ENNReal.ofReal_le_ofReal ?_)
    have e : 2 * 17 * (1 + |Cp|) * (clusterRange (flowCoupling (Tb.stepParameters y) β k) : ℝ) ^ 4 *
        Real.log (flowCoupling (Tb.stepParameters y) β k) = 2 * 17 * (1 + |Cp|) * Λ := by
      rw [hΛ]
      ring
    rw [e]
    exact two_pow_mul_one_add_le Cp Λ P hP hΛ1
  · have h0 : ∀ z, 0 ≤ siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z := fun z =>
      siteScore_nonneg _ hresp.price.nonneg _ _ _
    unfold scoreMeanOver meanSiteScore
    have : 0 ≤ ∑ z ∈ functionSites (Tb.stepParameters y).side g k (2 * (Tb.stepParameters y).side ^ m),
        siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z :=
      Finset.sum_nonneg fun z _ => h0 z
    positivity
  · unfold scoreMeanOver meanSiteScore
    have hz : ∀ z, siteScore (S.setup k).score (stageState T k _ u).2.1 (stageState T k _ u).2.2 z ≤
        16 * majorantNearBox T 0 s' k _ u z 1 := by
      intro z
      rw [hmaj, siteScore_const_mul]
      exact mul_le_mul_of_nonneg_left (siteMajorant_le_majorantNearBox T s' k _ hs0 u z) (by norm_num)
    have h2 := Finset.sum_le_sum
      (s := functionSites (Tb.stepParameters y).side g k (2 * (Tb.stepParameters y).side ^ m)) fun z _ => hz z
    have h3 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0 : ℝ) ≤
        ((functionSites (Tb.stepParameters y).side g k (2 * (Tb.stepParameters y).side ^ m)).card : ℝ)⁻¹)
    linarith
  · have e : (fun u => (16 * majorantNearBox T 0 s' k _ u z 1) ^ P) =
        fun u => 16 ^ P * majorantNearBox T 0 s' k (2 * (Tb.stepParameters y).side ^ m) u z 1 ^ P := by
      funext u
      rw [mul_pow]
    rw [e]
    exact (hone z).1.const_mul _
  · have e : (fun u => (16 * majorantNearBox T 0 s' k _ u z 1) ^ P) =
        fun u => 16 ^ P * majorantNearBox T 0 s' k (2 * (Tb.stepParameters y).side ^ m) u z 1 ^ P := by
      funext u
      rw [mul_pow]
    simp only [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hone z).2 (by positivity)
end YangMills.Construction.ResponseInTheExpansion
end
