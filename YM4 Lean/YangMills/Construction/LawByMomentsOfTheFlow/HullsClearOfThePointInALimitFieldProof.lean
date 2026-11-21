import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open MomentMethod RenormalizationStepParameters TorusLumps TorusFields HullTrees ChainNoise WeightedResponses ResponseInTheExpansion LevelTestFunctions
section Reals
private theorem hullDecayRate_pos {Tb : ParameterAssignment} (h : Tb.Admissible) : 0 < hullDecayRate Tb := by
  have hL : (1 : ℝ) < Tb.side := by
    have : 2 ^ 40 ≤ Tb.side := h.L_ge
    have h2 : (2 : ℝ) ^ 40 ≤ (Tb.side : ℝ) := by exact_mod_cast this
    linarith
  have hu : 0 < unitDecayRate Tb := by
    unfold unitDecayRate
    have h1 : 0 < Tb.κ * Tb.threshold ^ 2 := mul_pos h.κ_pos (pow_pos h.σ_pos 2)
    have := lt_min h1 h.cE_pos
    linarith
  have hB : (0 : ℝ) < Tb.B := lt_of_lt_of_le one_pos h.B_ge
  have hp : 0 < separatedUnitRate Tb := by
    unfold separatedUnitRate
    have : (0 : ℝ) < (Tb.side : ℝ) := by linarith
    positivity
  unfold hullDecayRate
  refine lt_min (by positivity) (div_pos (Real.log_pos hL) (by positivity))
abbrev _root_.YangMills.SharedProofs.p22298 := @hullDecayRate_pos
private theorem exists_count_bound (b c : ℝ) (hb : 0 < b) :
    ∃ X : ℝ, ∀ x, X ≤ x → 1 ≤ x ∧ c * Real.log x ≤ x / 2 ∧
      (2 * (⌈4 * Real.log x⌉₊ : ℝ) + 5) * (2 * (clusterRange x : ℝ) ^ 3 + 1) ^ 4 * Real.exp (-(b * x)) ≤ 1 := by
  have h1 : ∀ᶠ x : ℝ in atTop, c * Real.log x ≤ x / 2 := by
    have hc : 0 < 1 / (2 * (|c| + 1)) := by positivity
    have := Real.isLittleO_log_id_atTop.def hc
    filter_upwards [this, eventually_ge_atTop 1] with x hx h1
    simp only [id, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
    have h2 : c * Real.log x ≤ |c| * |Real.log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h3 : |c| * |Real.log x| ≤ |c| * (1 / (2 * (|c| + 1)) * x) := mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    have h4 : |c| * (1 / (2 * (|c| + 1)) * x) ≤ x / 2 := by
      have h5 : |c| / (|c| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have : |c| * (1 / (2 * (|c| + 1)) * x) = (|c| / (|c| + 1)) * (x / 2) := by
        field_simp
      rw [this]
      have hx0 : 0 ≤ x / 2 := by linarith
      nlinarith
    linarith
  have ht : Tendsto (fun x : ℝ => (b * x) ^ 13 * Real.exp (-(b * x))) atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 13).comp (tendsto_id.const_mul_atTop hb)
  have ht' : Tendsto (fun x : ℝ => (15 * 17 ^ 4 / b ^ 13) * ((b * x) ^ 13 * Real.exp (-(b * x)))) atTop (nhds 0) := by
    simpa using ht.const_mul (15 * 17 ^ 4 / b ^ 13)
  have h2 : ∀ᶠ x : ℝ in atTop, (2 * (⌈4 * Real.log x⌉₊ : ℝ) + 5) * (2 * (clusterRange x : ℝ) ^ 3 + 1) ^ 4 * Real.exp (-(b * x)) ≤ 1 := by
    filter_upwards [ht'.eventually (gt_mem_nhds (zero_lt_one' ℝ)), eventually_ge_atTop 1] with x hx h1
    have hx0 : 0 < x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg h1
    have hlog' : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
    have hN : (⌈4 * Real.log x⌉₊ : ℝ) ≤ 4 * Real.log x + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hA : 2 * (⌈4 * Real.log x⌉₊ : ℝ) + 5 ≤ 15 * x := by linarith
    have hpow : x ^ ((1 : ℝ) / 100) ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1 : ℝ) / 100 ≤ 1)
      simpa using this
    have hr : (clusterRange x : ℝ) ≤ 2 * x := by
      have : (clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have hr0 : (0 : ℝ) ≤ (clusterRange x : ℝ) := Nat.cast_nonneg _
    have hr3 : (clusterRange x : ℝ) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hr0 hr 3
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ h1
    have hB : 2 * (clusterRange x : ℝ) ^ 3 + 1 ≤ 17 * x ^ 3 := by nlinarith
    have hB4 : (2 * (clusterRange x : ℝ) ^ 3 + 1) ^ 4 ≤ (17 * x ^ 3) ^ 4 := pow_le_pow_left₀ (by positivity) hB 4
    have hprod : (2 * (⌈4 * Real.log x⌉₊ : ℝ) + 5) * (2 * (clusterRange x : ℝ) ^ 3 + 1) ^ 4 ≤ 15 * x * (17 * x ^ 3) ^ 4 :=
      mul_le_mul hA hB4 (by positivity) (by positivity)
    have he := (Real.exp_pos (-(b * x))).le
    have hbne : b ≠ 0 := hb.ne'
    have heq : 15 * x * (17 * x ^ 3) ^ 4 * Real.exp (-(b * x)) =
        (15 * 17 ^ 4 / b ^ 13) * ((b * x) ^ 13 * Real.exp (-(b * x))) := by
      field_simp
    calc _ ≤ 15 * x * (17 * x ^ 3) ^ 4 * Real.exp (-(b * x)) := mul_le_mul_of_nonneg_right hprod he
      _ = _ := heq
      _ ≤ 1 := hx.le
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((h1.and h2).and (eventually_ge_atTop 1))
  exact ⟨X, fun x hx => ⟨(hX x hx).2, (hX x hx).1.1, (hX x hx).1.2⟩⟩
abbrev _root_.YangMills.SharedProofs.p58793 := @exists_count_bound
end Reals
section Limits
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_le_of_limit (hX : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J) (A C : (Fin l → ℝ) → ℝ) (hA : Continuous A) (hC : Continuous C)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), A (fun c => X (a c) i ω) ≤ C (fun c => X (a c) i ω)) :
    ∀ᵐ v ∂P, A (fun c => v (a c, 0)) ≤ C (fun c => v (a c, 0)) := by apply _root_.YangMills.SharedProofs.p29837 <;> assumption
private theorem condMean_le_of_limit (hX : IsJointLimitLaw T X P) (hint : ∀ j, Integrable (evalAtZero j) P) {α : Type} (I : Finset α) (a : α → J)
    (j₀ j₁ : J) {c₀ c₁ c₂ b b₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), X j₀ i ω ≤ c₀ + c₁ * ∑ e ∈ I, X (a e) i ω + c₂ * X j₁ i ω)
    (hb : ∀ e ∈ I, ∀ᵐ v ∂P, invariantCondExp P (evalAtZero (a e)) v ≤ b)
    (hb₁ : ∀ᵐ v ∂P, invariantCondExp P (evalAtZero j₁) v ≤ b₁) :
    ∀ᵐ v ∂P, invariantCondExp P (evalAtZero j₀) v ≤ c₀ + c₁ * ((I.card : ℝ) * b) + c₂ * b₁ := by apply _root_.YangMills.SharedProofs.p37250 <;> assumption
end Limits
section Sums
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
end Sums
section Point
variable {Λ : MomentParameters}
private theorem markedSampleLaw_cast (T : StageTower Λ.stepParams) (β : ℝ) {K K' : ℕ} (h : K = K') (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) = markedSampleLaw T β K' n := by apply _root_.YangMills.SharedProofs.p48114 <;> assumption
private structure MomentPointFacts (S : MomentPoint Λ) : Prop where
  window_le : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel
  measurable_state : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n)
  sample_below : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
    Measure.map (sampleBelow Λ.stepParams s d n) (markedSampleLaw S.tower S.β (s + d) n) = markedSampleLaw S.tower S.β s (fineSide Λ.stepParams.side d n)
namespace MomentPoint
variable (S : MomentPoint Λ)
private theorem measurable_sampleAtLevel (h : MomentPointFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) : Measurable (S.sampleAtLevel u hu) := by
  have hc := markedSampleLaw_cast S.tower S.β (Nat.add_sub_of_le hu).symm (S.data.period Λ.stepParams.side)
  exact (h.sample_below u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)).1.comp hc.1
private theorem measurable_stateAtLevel (h : MomentPointFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) : Measurable (S.stateAtLevel u hu) :=
  (h.measurable_state u (S.sideAtLevel u)).comp (S.measurable_sampleAtLevel h u hu)
private theorem measurableSet_mem_stateAtLevel (h : MomentPointFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) (y : TorusSite (S.sideAtLevel u)) :
    MeasurableSet {w | y ∈ (S.stateAtLevel u hu w).2.1} := by
  have e : {w | y ∈ (S.stateAtLevel u hu w).2.1} =
      ⋃ a ∈ {a : Finset (TorusSite (S.sideAtLevel u)) | y ∈ a}, {w | (S.stateAtLevel u hu w).2.1 = a} := by
    ext w
    simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (measurable_snd.comp (S.measurable_stateAtLevel h u hu)) (measurableSet_sigma_fst_eq a)
open Classical in
private theorem largeHullIndicator_eq {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    largeHullIndicator u z 0 S w = if S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1 then 1 else 0 := by apply _root_.YangMills.SharedProofs.p14364 <;> assumption
private theorem notClearIndicator_nonneg (u : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ notClearIndicator u S w := by
  classical
  unfold notClearIndicator
  split_ifs <;> norm_num
private theorem largeHullIndicator_nonneg (u : ℕ) (z : Fin 4 → ℤ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : 0 ≤ largeHullIndicator u z 0 S w := by apply _root_.YangMills.SharedProofs.p20972 <;> assumption
private theorem abs_largeHullIndicator_le (u : ℕ) (z : Fin 4 → ℤ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : |largeHullIndicator u z 0 S w| ≤ 1 := by apply _root_.YangMills.SharedProofs.p33608 <;> assumption
private theorem measurable_largeHullIndicator (h : MomentPointFacts S) (u : ℕ) (z : Fin 4 → ℤ) : Measurable (largeHullIndicator u z 0 S) := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · have e : largeHullIndicator u z 0 S = fun w => if S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1 then 1 else 0 := by
      funext w
      exact S.largeHullIndicator_eq hu z w
    rw [e]
    exact Measurable.ite (S.measurableSet_mem_stateAtLevel h u hu _) measurable_const measurable_const
  · have e : largeHullIndicator u z 0 S = fun _ => 0 := by
      funext w
      unfold largeHullIndicator
      rw [dif_neg hu]
    rw [e]
    exact measurable_const
end MomentPoint
private def windowOffsets (N R : ℕ) : Finset (ℕ × (Fin 4 → ℤ)) :=
  Finset.range (2 * N + 4) ×ˢ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ))
private theorem windowOffsets_card (N R : ℕ) : (windowOffsets N R).card = (2 * N + 4) * (2 * R + 1) ^ 4 := by
  unfold windowOffsets
  rw [Finset.card_product, Fintype.card_piFinset, Finset.card_range]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
  rw [h2]
private theorem notClearIndicator_le_sum (S : MomentPoint Λ) {t N R u : ℕ} (ht : S.lastSeparated = t) (hN : S.logIndex = N)
    (hR : R = S.range ^ 3) (hu : t ≤ u)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) {z : ℝ} :
    notClearIndicator u S w ≤ 0 + 1 * ∑ e ∈ windowOffsets N R, largeHullIndicator (t + e.1) e.2 0 S w + 0 * z := by
  classical
  have hS0 : 0 ≤ ∑ e ∈ windowOffsets N R, largeHullIndicator (t + e.1) e.2 0 S w :=
    Finset.sum_nonneg fun e _ => S.largeHullIndicator_nonneg _ _ _
  by_cases hC : S.IsClearFrom u w
  · have hn : notClearIndicator u S w = 0 := if_pos hC
    rw [hn]
    linarith
  · have hn : notClearIndicator u S w = 1 := if_neg hC
    rw [hn]
    unfold MomentPoint.IsClearFrom at hC
    push Not at hC
    obtain ⟨u', hK, h1, h2, h3⟩ := hC
    obtain ⟨y, hy, hb⟩ := Finset.not_disjoint_iff.1 h3
    have hd : (TorusFields.supDist y (S.originSite u' (S.sideAtLevel u')) : ℝ) ≤ (S.range : ℝ) ^ 3 := (Finset.mem_filter.mp hb).2
    have hd' : TorusFields.supDist y (S.originSite u' (S.sideAtLevel u')) ≤ R := by
      rw [hR]
      exact_mod_cast hd
    have hz : (fun i => (y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs) ∈
        Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
      refine Fintype.mem_piFinset.2 fun i => ?_
      have h4 : ((y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs).natAbs ≤ R :=
        (Finset.le_sup (f := fun i => ((y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hd'
      rw [Finset.mem_Icc]
      show -(R : ℤ) ≤ (y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs ∧
        (y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs ≤ (R : ℤ)
      omega
    have hmem : ((u' - t, fun i => (y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs) : ℕ × (Fin 4 → ℤ)) ∈ windowOffsets N R := by
      refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, hz⟩
      show u' - t < 2 * N + 4
      rw [ht, hN] at h2
      omega
    have h5 := Finset.single_le_sum (f := fun e : ℕ × (Fin 4 → ℤ) => largeHullIndicator (t + e.1) e.2 0 S w)
      (fun e _ => S.largeHullIndicator_nonneg _ _ _) hmem
    have e1 : t + (u' - t) = u' := by omega
    have hsite : S.siteAt u' (fun i => (y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs) = y := by
      funext i
      show S.originSite u' (S.sideAtLevel u') i + ((y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs : ZMod (S.sideAtLevel u')) = y i
      rw [ZMod.coe_valMinAbs]
      ring
    have h6 : largeHullIndicator u' (fun i => (y i - S.originSite u' (S.sideAtLevel u') i).valMinAbs) 0 S w = 1 := by
      rw [S.largeHullIndicator_eq hK, hsite, if_pos hy]
    simp only [e1, h6] at h5
    linarith
end Point
section Field
variable {Λ : MomentParameters}
private theorem period_facts (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by apply _root_.YangMills.SharedProofs.p32373 <;> assumption
private theorem hasBoundedMoments_of_bound {T : TranslatedLaws} {X : T.Family} (hp : ∀ i, IsProbabilityMeasure (T.μ i))
    (hb : ∀ i, AEMeasurable (X i) (T.μ i))
    {C : ℝ} (hC : ∀ i, ∀ᵐ ω ∂(T.μ i), |X i ω| ≤ C) : TranslatedLaws.HasBoundedMoments X := by apply _root_.YangMills.SharedProofs.p39822 <;> assumption
private def offsetHullObservable (e : ℕ × (Fin 4 → ℤ)) : SampleObservable Λ := largeHullIndicator e.1 e.2 0
private structure SubsequenceFacts (rule : NoiseRule Λ.stepParams) (Sq : ℕ → MomentPoint Λ) (p : ℕ) : Prop where
  preserving : (translatedTori Sq p).IsPreserving
  pointFacts : ∀ i, MomentPointFacts (Sq i)
  sample : ∀ i, Measurable ((Sq i).sampleOf rule) ∧
    (Sq i).sampleLaw.map ((Sq i).sampleOf rule) = (Sq i).law (Sq i).data.windowLevel ((Sq i).data.period Λ.stepParams.side)
private theorem offsetHullObservable_moments {rule : NoiseRule Λ.stepParams} {Sq : ℕ → MomentPoint Λ} {p : ℕ}
    (h : SubsequenceFacts rule Sq p) (e : ℕ × (Fin 4 → ℤ)) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (offsetHullObservable e)) :=
  hasBoundedMoments_of_bound h.preserving.isProbability
    (fun i => (((Sq i).measurable_largeHullIndicator (h.pointFacts i) e.1 e.2).comp (h.sample i).1).aemeasurable)
    (fun i => ae_of_all _ fun _ => (Sq i).abs_largeHullIndicator_le e.1 e.2 _)
private theorem points_numbers (S : MomentPoint Λ) (F : LimitLawAtPoint S) (i : ℕ) :
    (F.points i).scaleCoupling = S.scaleCoupling ∧ (F.points i).range = S.range ∧ (F.points i).logIndex = S.logIndex ∧
      (F.points i).data.windowLevel = S.data.windowLevel ∧ ∀ u, (F.points i).coupling u = S.coupling u := by
  obtain ⟨a, b, e⟩ := F.points_eq i
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
private theorem condMean_notClear_le {S : MomentPoint Λ} (F : LimitLawAtPoint S) {t : ℕ} {b : ℝ}
    (ht : ∀ i, (F.points i).lastSeparated = t) (hint : ∀ j, Integrable (evalAtZero j) F.law) (jw : ℕ × (Fin 4 → ℤ) → F.Index)
    (hjw : ∀ e, F.observables (jw e) = offsetHullObservable e)
    (hb : ∀ e ∈ windowOffsets S.logIndex (S.range ^ 3), ∀ᵐ v ∂F.law, F.condMeanAt (jw (t + e.1, e.2)) v ≤ b) (u : ℕ) (hu : t ≤ u)
    (j : F.Index) (hj : F.observables j = notClearIndicator u) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ 0 + 1 * (((windowOffsets S.logIndex (S.range ^ 3)).card : ℝ) * b) + 0 * b := by
  have hs := condMean_le_of_limit F.isJointLimitLaw hint (windowOffsets S.logIndex (S.range ^ 3)) (fun e => jw (t + e.1, e.2)) j (jw (t, 0))
    (c₀ := 0) (c₁ := 1) (c₂ := 0) (b₁ := b) zero_le_one le_rfl ?_ hb ?_
  · exact hs
  · refine Eventually.of_forall fun i => ae_of_all _ fun ω => ?_
    have h := notClearIndicator_le_sum (F.points i) (u := u) (ht i) (points_numbers S F i).2.2.1 (R := S.range ^ 3)
      (by rw [(points_numbers S F i).2.1]) hu
      ((F.points i).sampleOf F.rule ω) (z := sampleFamily F.rule F.points F.period (F.observables (jw (t, 0))) i ω)
    simp only [sampleFamily, hj, hjw] at h ⊢
    exact h
  · have hm : ((0, 0) : ℕ × (Fin 4 → ℤ)) ∈ windowOffsets S.logIndex (S.range ^ 3) := by
      refine Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_⟩
      simp
    exact hb (0, 0) hm
private theorem condMean_le_of_extension (hExt : jointLimitExtendStatement) (hMn : jointLimitPropertiesStatement) {S : MomentPoint Λ}
    (F : LimitLawAtPoint S)
    (hSeq : ∀ φ : ℕ → ℕ, StrictMono φ → SubsequenceFacts F.rule (fun i => F.points (φ i)) F.period) {t : ℕ}
    (ht : ∀ i, (F.points i).lastSeparated = t) (j : F.Index) {b : ℝ}
    (hnn : ∀ i w, 0 ≤ F.observables j (F.points i) w)
    (main : ∀ F' : LimitLawAtPoint S, (∀ i, (F'.points i).lastSeparated = t) → (∀ j' : F'.Index, Integrable (evalAtZero j') F'.law) →
      ∀ jw : ℕ × (Fin 4 → ℤ) → F'.Index, (∀ e, F'.observables (jw e) = offsetHullObservable e) →
        ∀ j' : F'.Index, F'.observables j' = F.observables j → ∀ᵐ v ∂F'.law, F'.condMeanAt j' v ≤ b) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ b := by
  classical
  have hcount := F.countable_index
  have hq₀ := hSeq id strictMono_id
  have hXf : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule (fun i => F.points (id i)) F.period (F.observables j)) :=
    F.hasBoundedMoments
  have hlim₀ : IsJointLimitLaw (translatedTori (fun i => F.points (id i)) F.period)
      (fun j => sampleFamily F.rule (fun i => F.points (id i)) F.period (F.observables j)) F.law := F.isJointLimitLaw
  obtain ⟨sub, P', hsub, hlim, -, htr⟩ := hExt (translatedTori (fun i => F.points (id i)) F.period) F.Index (ℕ × (Fin 4 → ℤ))
    (fun j => sampleFamily F.rule (fun i => F.points (id i)) F.period (F.observables j))
    (fun c => sampleFamily F.rule (fun i => F.points (id i)) F.period (offsetHullObservable c)) F.law hq₀.preserving hXf
    (offsetHullObservable_moments hq₀) hlim₀
  have hq := hSeq sub hsub
  have hlim' : IsJointLimitLaw (translatedTori (fun i => F.points (sub i)) F.period)
      (fun c => sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables offsetHullObservable c)) P' := by
    have e1 : (fun c => sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables offsetHullObservable c)) =
        fun c i => Sum.elim (fun j => sampleFamily F.rule (fun i => F.points (id i)) F.period (F.observables j))
          (fun c => sampleFamily F.rule (fun i => F.points (id i)) F.period (offsetHullObservable c)) c (sub i) := by
      funext c
      rcases c with c | c <;> rfl
    rw [e1]
    exact hlim
  let F' : LimitLawAtPoint S :=
    { rule := F.rule, rule_admissible := F.rule_admissible, period := F.period, one_le_period := F.one_le_period,
      exponents := fun i => F.exponents (sub i), strictMono_exponents := fun _ _ h => F.strictMono_exponents (hsub h),
      points := fun i => F.points (sub i), points_eq := fun i => F.points_eq _, Index := F.Index ⊕ (ℕ × (Fin 4 → ℤ)),
      countable_index := inferInstance,
      observables := Sum.elim F.observables offsetHullObservable,
      hasBoundedMoments := by
        rintro (j | c)
        · exact ⟨fun i => (hXf j).aemeasurable (sub i), fun q => by
            obtain ⟨C, hC⟩ := (hXf j).moment_bound q
            exact ⟨C, fun i => hC (sub i)⟩⟩
        · exact offsetHullObservable_moments hq c
      law := P', isJointLimitLaw := hlim' }
  have hint' : ∀ j' : F'.Index, Integrable (evalAtZero j') F'.law := by
    intro j'
    have hcount' : Countable F'.Index := F'.countable_index
    have hMean := hMn (translatedTori F'.points F'.period) F'.Index (fun j => sampleFamily F'.rule F'.points F'.period (F'.observables j))
      F'.law hq.preserving F'.hasBoundedMoments F'.isJointLimitLaw
    have h1 := (hMean.2.1 1 (fun _ => (j', 0))).1
    have e1 : (fun v : TranslateValues F'.Index => ∏ _c : Fin 1, v (j', 0)) = evalAtZero j' := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h1
  have hb : ∀ᵐ v ∂P', invariantCondExp P' (evalAtZero (Sum.inl j)) v ≤ b :=
    main F' (fun i => ht _) hint' Sum.inr (fun _ => rfl) (Sum.inl j) rfl
  have hprob := hlim'.isProbability
  have hnn' : ∀ᵐ v ∂P', 0 ≤ (evalAtZero (Sum.inl j) : TranslateValues (F.Index ⊕ (ℕ × (Fin 4 → ℤ))) → ℝ) v := by
    have h1 := ae_le_of_limit hlim' (fun _ : Fin 1 => (Sum.inl j : F.Index ⊕ (ℕ × (Fin 4 → ℤ)))) (fun _ => 0) (fun w => w 0)
      continuous_const (continuous_apply 0)
      (Eventually.of_forall fun i => ae_of_all _ fun ω => hnn _ _)
    exact h1
  have hlow : 0 ≤ᵐ[P'] invariantCondExp P' (evalAtZero (Sum.inl j)) := condExp_nonneg hnn'
  have hMean := hMn (translatedTori (fun i => F.points (id i)) F.period) F.Index
    (fun j => sampleFamily F.rule (fun i => F.points (id i)) F.period (F.observables j)) F.law
    hq₀.preserving hXf hlim₀
  have hY : Integrable (evalAtZero j) F.law := by
    have h1 := (hMean.2.1 1 (fun _ => (j, 0))).1
    have e1 : (fun v : TranslateValues F.Index => ∏ _c : Fin 1, v (j, 0)) = evalAtZero j := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h1
  have h2 := htr (evalAtZero j) 0 b hY (by
    filter_upwards [hb, hlow] with v h1 h3
    exact ⟨h3, h1⟩)
  filter_upwards [h2] with v hv
  exact hv.2
end Field
section Final
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ∀ Λ, Q₁ Λ → Q₂ Λ) (h₁ : ForAllHullParameters Q₁) :
    ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p16214 <;> assumption
private theorem forAllHullParameters_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
theorem hullsClearLimitStatement_holds (h₁ : limitHullBoundsStatement) (h₂ : jointLimitExtendStatement)
    (h₃ : jointLimitPropertiesStatement) (h₄ : largerToriStatement) (h₅ : scaleWindowStatement)
    (h₆ : StageStatesMeasurableStatement) (h₇ : sampleBelowLawStatement) (h₈ : ruleDrawsChainStatement) :
    hullsClearLimitStatement := by
  unfold limitHullBoundsStatement at h₁
  unfold largerToriStatement at h₄
  unfold scaleWindowStatement ForAllPoints at h₅
  unfold hullsClearLimitStatement
  refine forAllHullParameters_mono ?_ (forAllHullParameters_and h₁ (forAllHullParameters_and h₄
    (forAllHullParameters_and (forAllHullParameters_of_forAll h₅) (forAllHullParameters_of_forAll forAllParameters_admissible))))
  rintro Λ ⟨⟨CHl, _, HH⟩, hP, ⟨Cw, _, XW, _, _, HW⟩, hD, hy⟩
  have hfit : Λ.stepParams.Admissible := hD.fits Λ.floor hy
  have hL : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side := hD.L_gt
  have hc5 : 0 < hullDecayRate Λ.table := hullDecayRate_pos hD
  obtain ⟨X, hX⟩ := exists_count_bound (hullDecayRate Λ.table / 4) (Cw 0) (by positivity)
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = max X (max XW Λ.floor) := ⟨_, rfl⟩
  have eX : X ≤ X₀ := by rw [hX₀]; simp
  have eW : XW ≤ X₀ := by rw [hX₀]; simp
  have ey : Λ.floor ≤ X₀ := by rw [hX₀]; simp
  refine ⟨1, hullDecayRate Λ.table / 4, X₀, by positivity, ey, ?_⟩
  intro S F t hx ht u j hu hj
  obtain ⟨hx1, hlog, hcount⟩ := hX S.scaleCoupling (eX.trans hx)
  have hxi : ∀ i, X₀ ≤ (F.points i).scaleCoupling := fun i => by
    rw [(points_numbers S F i).1]
    exact hx
  have hPF : ∀ i, MomentPointFacts (F.points i) := fun i =>
    { window_le := (HW (F.points i) (eW.trans (hxi i))).2.2.2.2.2.1
      measurable_state := fun u n _ => h₆ Λ.stepParams hfit (F.points i).tower u n
      sample_below := fun s d n _ => (h₇ Λ.stepParams hfit hL (F.points i).tower (F.points i).isCutoff (F.points i).marksMeasurable
        (F.points i).β (fun _ => 0)).1 s d n }
  have hSeq : ∀ φ : ℕ → ℕ, StrictMono φ → SubsequenceFacts F.rule (fun i => F.points (φ i)) F.period := by
    intro φ hφ
    have hmom := (hP S).2.2.2 F.rule (fun i => F.exponents (φ i)) (fun i => F.points (φ i)) F.period F.rule_admissible F.one_le_period
      (fun _ _ h => F.strictMono_exponents (hφ h)) (fun i => F.points_eq _)
    refine { preserving := hmom.1, pointFacts := fun i => hPF _, sample := fun i => ?_ }
    obtain ⟨a, b, e⟩ := F.points_eq (φ i)
    have hr : F.rule.IsAdmissible (F.points (φ i)).tower := by
      rw [e]
      exact F.rule_admissible
    obtain ⟨d1, d2⟩ := period_facts (F.points (φ i)) hfit
    exact h₈ Λ.stepParams hfit (F.points (φ i)).tower F.rule (F.points (φ i)).β (F.points (φ i)).isCutoff (F.points (φ i)).marksMeasurable hr
      (F.points (φ i)).data.windowLevel _ d1 d2
  obtain ⟨Ec, hEc⟩ : ∃ Ec : ℝ, Ec = Real.exp (-(hullDecayRate Λ.table / 4 * S.scaleCoupling)) := ⟨_, rfl⟩
  have hEc0 : 0 < Ec := hEc ▸ Real.exp_pos _
  have hcc : Ec * Ec = Real.exp (-(hullDecayRate Λ.table * (S.scaleCoupling / 2))) := by
    rw [hEc, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨_, _, _, _, _, hwin, hall⟩ := HW (F.points 0) (eW.trans (hxi 0))
  obtain ⟨n1, n2, n3, n4, n5⟩ := points_numbers S F 0
  rw [ht 0, n3] at hwin
  refine condMean_le_of_extension h₂ h₃ F hSeq ht j (fun i w => ?_) fun F' ht' hint jw hjw j' hj' => ?_
  · rw [hj]
    exact (F.points i).notClearIndicator_nonneg u w
  · have hb : ∀ e ∈ windowOffsets S.logIndex (S.range ^ 3), ∀ᵐ v ∂F'.law, F'.condMeanAt (jw (t + e.1, e.2)) v ≤ Ec * Ec := by
      intro e he
      have ha : e.1 < 2 * S.logIndex + 4 := Finset.mem_range.1 (Finset.mem_product.1 he).1
      have hv := (HH S F' (t + e.1) e.2 (by rw [← n4]; omega)).1 0 (jw (t + e.1, e.2)) le_rfl (hjw _)
      filter_upwards [hv] with v h0
      refine h0.trans ?_
      have hxv : S.scaleCoupling / 2 ≤ S.coupling (t + e.1) := by
        have h3 := (hall (t + e.1) (by rw [ht 0]; omega) (by rw [ht 0, n3]; omega)).1
        rw [n5, n1] at h3
        have := abs_le.1 (h3.trans hlog)
        linarith [this.1]
      rw [hcc, Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_left hxv hc5.le
      simp only [zero_div, add_zero, mul_one]
      linarith
    have hres := condMean_notClear_le F' ht' hint jw hjw hb u hu j' (hj'.trans hj)
    filter_upwards [hres] with v hv
    refine hv.trans ?_
    have hN : ((S.logIndex : ℕ) : ℝ) = (⌈4 * Real.log S.scaleCoupling⌉₊ : ℝ) := rfl
    have hR : (S.range : ℝ) = (clusterRange S.scaleCoupling : ℝ) := rfl
    rw [← hN, ← hR, ← hEc] at hcount
    rw [windowOffsets_card]
    push_cast
    have h0 : (0 : ℝ) ≤ (S.logIndex : ℝ) := Nat.cast_nonneg _
    have h1 : (2 * (S.logIndex : ℝ) + 4) * (2 * (S.range : ℝ) ^ 3 + 1) ^ 4 * Ec ≤ 1 := by
      refine le_trans ?_ hcount
      have : 0 ≤ (2 * (S.range : ℝ) ^ 3 + 1) ^ 4 := by positivity
      gcongr
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hEc0.le
    nlinarith
end Final
end YangMills.Construction.MomentLaw
end
