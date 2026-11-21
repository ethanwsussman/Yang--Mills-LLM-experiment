import YangMills.Construction.HilbertSpaces.LimitsSeriesIntegralsAndTheLogarithmOfBoundedOperators
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory
noncomputable section
namespace YangMills.Construction
open OneLoopNotation Tower.UnitLatticeL2
namespace OperatorCalculus
section Elementary
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem addScalar_apply (T : BddOp H) (s : ℝ) (f : H) :
    addScalar T s f = T f + (s : ℂ) • f := by
  simp [addScalar, scalarOp]
theorem norm_scalarOp_le (c : ℂ) : ‖(scalarOp c : BddOp H)‖ ≤ ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun x => ?_
  simp [scalarOp, norm_smul]
theorem sum_fin_succ_sub_castSucc {E : Type} [AddCommGroup E] :
    ∀ (k : ℕ) (g : Fin (k + 1) → E),
      ∑ i : Fin k, (g i.succ - g i.castSucc) = g (Fin.last k) - g 0 := by
  intro k
  induction k with
  | zero => intro g; simp
  | succ k ih =>
    intro g
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => g i.castSucc)
    simp only [Fin.succ_castSucc] at *
    rw [h]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    abel
end Elementary
section Requirements
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem inner_apply_left_of_isSelfAdjointOp {T : BddOp H} (hT : IsSelfAdjointOp T)
    (x y : H) : inner ℂ (T x) y = inner ℂ x (T y) := by
  have h := ContinuousLinearMap.adjoint_inner_left T y x
  have e : ContinuousLinearMap.adjoint T = T := hT
  rwa [e] at h
theorem addScalarClaim_holds : AddScalarClaim H := by
  intro T hT s s'
  refine ⟨?_, ?_⟩
  · have h : addScalar T s = ContinuousLinearMap.adjoint (addScalar T s) := by
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [addScalar_apply, addScalar_apply, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, inner_apply_left_of_isSelfAdjointOp hT, Complex.conj_ofReal]
    exact h.symm
  · intro h ψ
    have e : inner ℂ ψ (addScalar T s ψ) - (((s' + s : ℝ)) : ℂ) * inner ℂ ψ ψ =
        inner ℂ ψ (T ψ) - (s' : ℂ) * inner ℂ ψ ψ := by
      rw [addScalar_apply, inner_add_right, inner_smul_right]
      push_cast
      ring
    rw [e]
    exact h ψ
omit [CompleteSpace H] in
theorem opCompleteness_holds : OpCompleteness H H' := by
  intro 𝒳 ε h hε
  have hsub : ∀ n, 1 ≤ n → ∀ k, n ≤ k → 𝒳 k ⊆ 𝒳 n := by
    intro n hn k hk
    induction k, hk using Nat.le_induction with
    | base => exact subset_rfl
    | succ k hk ih => exact ((h k (hn.trans hk)).2.2.1).trans ih
  have hne : ∀ n : ℕ, (𝒳 (n + 1)).Nonempty := fun n => (h (n + 1) (by omega)).1
  choose x hx using hne
  have hxmem : ∀ n, 1 ≤ n → ∀ k, n ≤ k → x k ∈ 𝒳 n := fun n hn k hk =>
    hsub n hn (k + 1) (by omega) (hx k)
  have hcau : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hε.eventually (gt_mem_nhds hδ))
    refine ⟨N + 1, fun n hn => ?_⟩
    have h1 : 1 ≤ N + 1 := by omega
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ((h (N + 1) h1).2.2.2 _ (hxmem _ h1 n hn) _ (hxmem _ h1 _ le_rfl)) ?_
    exact hN _ (by omega)
  obtain ⟨X, hX⟩ := cauchySeq_tendsto_of_complete hcau
  have hXbound : ∀ n, 1 ≤ n → ∀ X' ∈ 𝒳 n, ‖X - X'‖ ≤ ε n := by
    intro n hn X' hX'
    have ht : Tendsto (fun k => ‖x k - X'‖) atTop (nhds ‖X - X'‖) := (hX.sub_const X').norm
    exact le_of_tendsto ht (eventually_atTop.2
      ⟨n, fun k hk => (h n hn).2.2.2 _ (hxmem n hn k hk) _ hX'⟩)
  refine ⟨X, hXbound, fun Y hY => ?_⟩
  have hle : ∀ n : ℕ, ‖Y - X‖ ≤ 2 * ε (n + 1) := by
    intro n
    have h1 : 1 ≤ n + 1 := by omega
    have a := hY _ h1 _ (hx n)
    have b := hXbound _ h1 _ (hx n)
    calc ‖Y - X‖ = ‖(Y - x n) - (X - x n)‖ := by congr 1; abel
      _ ≤ ‖Y - x n‖ + ‖X - x n‖ := norm_sub_le _ _
      _ ≤ 2 * ε (n + 1) := by linarith
  have ht : Tendsto (fun n : ℕ => 2 * ε (n + 1)) atTop (nhds (2 * 0)) :=
    ((tendsto_add_atTop_iff_nat 1).2 hε).const_mul 2
  rw [mul_zero] at ht
  have h0 : ‖Y - X‖ ≤ 0 := ge_of_tendsto' ht hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
omit [CompleteSpace H] in
theorem absSummableSeries_holds : AbsSummableSeries H H' := by
  intro N _ _ Y hY
  have hsum : Summable Y := hY.of_norm
  have hF : ∀ F : Finset N, ‖(∑' ν, Y ν) - ∑ ν ∈ F, Y ν‖ ≤ ∑' ν : {ν // ν ∉ F}, ‖Y ν‖ := by
    intro F
    have e := hsum.sum_add_tsum_subtype_compl F
    have e' : (∑' ν, Y ν) - ∑ ν ∈ F, Y ν = ∑' ν : {ν // ν ∉ F}, Y ν := by
      rw [← e]; abel
    rw [e']
    exact norm_tsum_le_tsum_norm (hY.subtype _)
  refine ⟨∑' ν, Y ν, hF, ?_, norm_tsum_le_tsum_norm hY, ?_⟩
  · intro X' hX'
    have h1 : Tendsto (fun F : Finset N => ∑ ν ∈ F, Y ν) atTop (nhds (∑' ν, Y ν)) := hsum.hasSum
    have h2 : Tendsto (fun F : Finset N => ∑' ν : {ν // ν ∉ F}, ‖Y ν‖) atTop (nhds 0) :=
      tendsto_tsum_compl_atTop_zero (fun ν => ‖Y ν‖)
    have h3 : Tendsto (fun F : Finset N => ∑ ν ∈ F, Y ν) atTop (nhds X') := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) h2
      rw [norm_sub_rev]
      exact hX' F
    exact tendsto_nhds_unique h3 h1
  · intro e
    have hs : HasSum (fun l : ℕ+ => Y (e l)) (∑' ν, Y ν) := (e.hasSum_iff).2 hsum.hasSum
    have hmono : Tendsto (fun n : ℕ+ => Finset.Icc 1 n) atTop atTop := by
      refine tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun x => ⟨x, ?_⟩)
      · exact Finset.Icc_subset_Icc le_rfl hab
      · exact Finset.mem_Icc.2 ⟨one_le, le_rfl⟩
    exact hs.comp hmono
theorem neumannClaim_holds : NeumannClaim H := by
  intro A q hA hq
  have hq0 : 0 ≤ q := (norm_nonneg A).trans hA
  have hA1 : ‖A‖ < 1 := hA.trans_lt hq
  have hpow : ∀ l : ℕ, ‖A ^ l‖ ≤ q ^ l := by
    intro l
    induction l with
    | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ l ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hA (norm_nonneg _) (pow_nonneg hq0 _))
  have hsum : Summable (fun l : ℕ => A ^ l) := summable_geometric_of_norm_lt_one hA1
  refine ⟨∑' l : ℕ, A ^ l, ?_, ⟨mul_neg_geom_series A hA1, geom_series_mul_neg A hA1⟩, ?_⟩
  · have h := hsum.hasSum.tendsto_sum_nat
    exact (tendsto_add_atTop_iff_nat 1).2 h
  · exact tsum_of_norm_bounded (hasSum_geometric_of_lt_one hq0 hq) hpow
omit [CompleteSpace H] in
theorem continuousOn_of_normContinuousOn {T : ℝ → BddOp H} {m m' : ℝ}
    (h : NormContinuousOn T m m') : ContinuousOn T (Icc m m') := by
  intro w hw
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨υ, hυ, hb⟩ := h w hw (ε / 2) (by positivity)
  refine ⟨υ, hυ, fun y hy hd => ?_⟩
  have h1 := hb y hy (by rw [abs_sub_comm, ← Real.dist_eq]; exact hd.le)
  rw [dist_comm, dist_eq_norm]
  linarith
omit [CompleteSpace H] in
theorem normContinuousOn_of_continuousOn {T : ℝ → BddOp H} {m m' : ℝ}
    (h : ContinuousOn T (Icc m m')) : NormContinuousOn T m m' := by
  intro w hw ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousWithinAt_iff.1 (h w hw) ε hε
  refine ⟨δ / 2, by positivity, fun w' hw' hd => ?_⟩
  have h1 := hb hw' (by rw [Real.dist_eq, abs_sub_comm]; linarith)
  rw [dist_comm, dist_eq_norm] at h1
  exact h1.le
omit [CompleteSpace H] in
theorem uniformlyNormContinuousOn_of_normContinuousOn {T : ℝ → BddOp H} {m m' : ℝ}
    (h : NormContinuousOn T m m') : UniformlyNormContinuousOn T m m' := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous (continuousOn_of_normContinuousOn h)
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  refine ⟨δ / 2, by positivity, fun w hw w' hw' hd => ?_⟩
  have h1 := hb w hw w' hw' (by rw [Real.dist_eq]; linarith)
  rw [dist_eq_norm] at h1
  exact h1.le
theorem norm_markedSum_sub_integral_le {T : ℝ → BddOp H} {m m' υ ε : ℝ}
    (hT : ContinuousOn T (Icc m m'))
    (hu : ∀ w ∈ Icc m m', ∀ w' ∈ Icc m m', |w - w'| ≤ υ → ‖T w - T w'‖ ≤ ε)
    (P : MarkedPartition m m')
    (hmesh : ∀ i : Fin P.card, P.node i.succ - P.node i.castSucc ≤ υ) :
    ‖P.sum T - ∫ w in m..m', T w‖ ≤ ε * (m' - m) := by
  have hmem : ∀ i, P.node i ∈ Icc m m' := fun i =>
    ⟨P.node_zero.ge.trans (P.node_mono (Fin.zero_le i)), (P.node_mono (Fin.le_last i)).trans P.node_last.le⟩
  have hstep : ∀ i : Fin P.card, P.node i.castSucc ≤ P.node i.succ := fun i =>
    P.node_mono (Fin.castSucc_lt_succ).le
  have hmm : m ≤ m' := (hmem 0).1.trans (hmem 0).2
  have hii : ∀ a ∈ Icc m m', ∀ b ∈ Icc m m', IntervalIntegrable T volume a b := by
    intro a ha b hb
    have h0 : IntervalIntegrable T volume m m' := hT.intervalIntegrable_of_Icc hmm
    exact h0.mono_set (by rw [uIcc_of_le hmm]; exact uIcc_subset_Icc ha hb)
  obtain ⟨F, hF⟩ : ∃ F : ℝ → BddOp H, ∀ x, F x = ∫ w in m..x, T w := ⟨_, fun _ => rfl⟩
  have hI : ∫ w in m..m', T w =
      ∑ i : Fin P.card, (F (P.node i.succ) - F (P.node i.castSucc)) := by
    have hs := sum_fin_succ_sub_castSucc P.card (fun i => F (P.node i))
    simp only [P.node_last, P.node_zero] at hs
    rw [hs, hF, hF]
    simp
  have key : ∀ a b t, a ∈ Icc m m' → b ∈ Icc m m' → a ≤ b → t ∈ Icc a b → b - a ≤ υ →
      ‖(b - a) • T t - (F b - F a)‖ ≤ ε * (b - a) := by
    intro a b t ha hb hab htag hm
    have ht : t ∈ Icc m m' := ⟨ha.1.trans htag.1, htag.2.trans hb.2⟩
    have e : F b - F a = ∫ w in a..b, T w := by
      rw [hF, hF]
      exact intervalIntegral.integral_interval_sub_left (hii m ⟨le_rfl, hmm⟩ b hb)
        (hii m ⟨le_rfl, hmm⟩ a ha)
    have e2 : (b - a) • T t - ∫ w in a..b, T w = ∫ w in a..b, (T t - T w) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hii a ha b hb),
        intervalIntegral.integral_const]
    rw [e, e2]
    have hb' : ‖∫ w in a..b, (T t - T w)‖ ≤ ε * |b - a| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun w hw => ?_
      rw [uIoc_of_le hab] at hw
      have hwm : w ∈ Icc m m' := ⟨ha.1.trans hw.1.le, hw.2.trans hb.2⟩
      refine hu t ht w hwm ?_
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2, htag.1, htag.2]
    rwa [abs_of_nonneg (sub_nonneg.2 hab)] at hb'
  have hterm : ∀ i : Fin P.card,
      ‖(P.node i.succ - P.node i.castSucc) • T (P.sample i) -
        (F (P.node i.succ) - F (P.node i.castSucc))‖ ≤
        ε * (P.node i.succ - P.node i.castSucc) := fun i =>
    key _ _ _ (hmem _) (hmem _) (hstep i) (P.sample_mem i) (hmesh i)
  calc ‖P.sum T - ∫ w in m..m', T w‖
      = ‖∑ i : Fin P.card, ((P.node i.succ - P.node i.castSucc) • T (P.sample i) -
          (F (P.node i.succ) - F (P.node i.castSucc)))‖ := by
        rw [hI, MarkedPartition.sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin P.card, ‖(P.node i.succ - P.node i.castSucc) • T (P.sample i) -
          (F (P.node i.succ) - F (P.node i.castSucc))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.card, ε * (P.node i.succ - P.node i.castSucc) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ε * (m' - m) := by
        rw [← Finset.mul_sum, sum_fin_succ_sub_castSucc P.card P.node, P.node_last, P.node_zero]
omit [CompleteSpace H] in
theorem exists_isRiemannSumWithMeshLE (T : ℝ → BddOp H) {m m' υ : ℝ} (hmm : m < m')
    (hυ : 0 < υ) : ∃ R, IsRiemannSumWithMeshLE T m m' υ R := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((m' - m) / υ)
  have hd0 : 0 < m' - m := sub_pos.2 hmm
  have hN0 : (0 : ℝ) < N := (div_pos hd0 hυ).trans hN
  have hNn : 0 < N := by exact_mod_cast hN0
  have hd : 0 < (m' - m) / N := div_pos hd0 hN0
  have hle : (m' - m) / N ≤ υ := by
    rw [div_lt_iff₀ hυ] at hN
    rw [div_le_iff₀ hN0]
    linarith [mul_comm υ (N : ℝ)]
  obtain ⟨pt, hpt⟩ : ∃ pt : Fin (N + 1) → ℝ, ∀ i, pt i = m + ((i : ℕ) : ℝ) * ((m' - m) / N) :=
    ⟨_, fun _ => rfl⟩
  have hstrict : StrictMono pt := by
    intro i j hij
    have h1 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    rw [hpt, hpt]
    have := mul_lt_mul_of_pos_right h1 hd
    linarith
  have hstep : ∀ i : Fin N, pt i.succ - pt i.castSucc ≤ υ := by
    intro i
    rw [hpt, hpt]
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    linarith
  have hz : pt 0 = m := by rw [hpt]; simp
  have hl : pt (Fin.last N) = m' := by
    rw [hpt]
    simp only [Fin.val_last]
    field_simp
    ring
  let P : MarkedPartition m m' :=
    { card := N
      node := pt
      sample := fun i => pt i.castSucc
      node_mono := hstrict.monotone
      node_zero := hz
      node_last := hl
      sample_mem := fun i => ⟨le_rfl, hstrict.monotone (Fin.castSucc_lt_succ).le⟩ }
  exact ⟨_, ⟨P, hNn, hstrict, hstep, rfl⟩⟩
theorem riemannSumsTendsto_integral {T : ℝ → BddOp H} {m m' : ℝ} (hmm : m < m')
    (h : NormContinuousOn T m m') : RiemannSumsTendsto T m m' (∫ w in m..m', T w) := by
  intro ε hε
  have hd : 0 < m' - m := sub_pos.2 hmm
  obtain ⟨υ, hυ, hb⟩ := uniformlyNormContinuousOn_of_normContinuousOn h (ε / (m' - m))
    (div_pos hε hd)
  refine ⟨υ, hυ, ?_⟩
  rintro R ⟨P, -, -, hmesh, rfl⟩
  have h1 := norm_markedSum_sub_integral_le (continuousOn_of_normContinuousOn h) hb P hmesh
  rwa [div_mul_cancel₀ _ hd.ne'] at h1
omit [CompleteSpace H] in
theorem riemannSumsTendsto_unique {T : ℝ → BddOp H} {m m' : ℝ}
    {X Y : BddOp H} (hmm : m < m') (hX : RiemannSumsTendsto T m m' X)
    (hY : RiemannSumsTendsto T m m' Y) : X = Y := by
  refine sub_eq_zero.1 (norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_))
  obtain ⟨υ₁, h₁, b₁⟩ := hX (ε / 2) (by positivity)
  obtain ⟨υ₂, h₂, b₂⟩ := hY (ε / 2) (by positivity)
  obtain ⟨R, hR⟩ := exists_isRiemannSumWithMeshLE T hmm (lt_min h₁ h₂)
  have hmono : ∀ υ, min υ₁ υ₂ ≤ υ → IsRiemannSumWithMeshLE T m m' υ R := by
    intro υ hle
    obtain ⟨P, a, b, c, d⟩ := hR
    exact ⟨P, a, b, fun i => (c i).trans hle, d⟩
  have c₁ := b₁ R (hmono _ (min_le_left _ _))
  have c₂ := b₂ R (hmono _ (min_le_right _ _))
  calc ‖X - Y‖ = ‖(R - Y) - (R - X)‖ := by congr 1; abel
    _ ≤ ‖R - Y‖ + ‖R - X‖ := norm_sub_le _ _
    _ ≤ 0 + ε := by linarith
theorem opIntegral_eq_integral {T : ℝ → BddOp H} {m m' : ℝ} (hmm : m < m')
    (h : NormContinuousOn T m m') : opIntegral T m m' = ∫ w in m..m', T w := by
  have h1 : RiemannSumsTendsto T m m' (opIntegral T m m') :=
    Classical.epsilon_spec (p := fun X => RiemannSumsTendsto T m m' X)
      ⟨_, riemannSumsTendsto_integral hmm h⟩
  exact riemannSumsTendsto_unique hmm h1 (riemannSumsTendsto_integral hmm h)
theorem compactIntervalIntegral_holds : CompactIntervalIntegral H := by
  intro m m' T hmm h
  have hc := continuousOn_of_normContinuousOn h
  have hmono : ∀ a b, m ≤ a → b ≤ m' → NormContinuousOn T a b := by
    intro a b ha hb w hw ε hε
    obtain ⟨υ, hυ, hbd⟩ := h w ⟨ha.trans hw.1, hw.2.trans hb⟩ ε hε
    exact ⟨υ, hυ, fun w' hw' => hbd w' ⟨ha.trans hw'.1, hw'.2.trans hb⟩⟩
  refine ⟨uniformlyNormContinuousOn_of_normContinuousOn h,
    ⟨_, riemannSumsTendsto_integral hmm h,
      fun Y hY => riemannSumsTendsto_unique hmm hY (riemannSumsTendsto_integral hmm h)⟩,
    ?_, hc.norm, ?_, ?_⟩
  · rw [opIntegral_eq_integral hmm h]
    exact riemannSumsTendsto_integral hmm h
  · rw [opIntegral_eq_integral hmm h]
    exact intervalIntegral.norm_integral_le_integral_norm hmm.le
  · intro m'' h1 h2
    have c1 := continuousOn_of_normContinuousOn (hmono m m'' le_rfl h2.le)
    have c2 := continuousOn_of_normContinuousOn (hmono m'' m' h1.le le_rfl)
    rw [opIntegral_eq_integral hmm h,
      opIntegral_eq_integral h1 (hmono _ _ le_rfl h2.le),
      opIntegral_eq_integral h2 (hmono _ _ h1.le le_rfl)]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (c1.intervalIntegrable_of_Icc h1.le) (c2.intervalIntegrable_of_Icc h2.le)).symm
theorem halfLineIntegral_holds : HalfLineIntegral H := by
  intro T hT hI
  obtain ⟨l, hl⟩ := hI
  have hl' : Tendsto (fun x : ℝ => ∫ w in (0 : ℝ)..x, ‖T w‖) atTop (nhds l) := by
    simpa using hl
  have hb : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hint : IntegrableOn T (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto l 0 (fun n => ?_) hb (hl'.comp hb)
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact ((continuousOn_of_normContinuousOn (hT _ hpos)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hconv : TendstoInOpNorm atTop (fun m : ℝ => opIntegral T 0 m)
      (∫ w in Ioi 0, T w) := by
    unfold TendstoInOpNorm
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact (opIntegral_eq_integral hm (hT m hm)).symm
  exact ⟨_, hconv, fun Y hY => tendsto_nhds_unique hY hconv⟩
omit [CompleteSpace H] in
theorem inverseOp_eq {X B : BddOp H} (h : IsTwoSidedInverse X B) :
    inverseOp X = B := by
  have h1 : IsTwoSidedInverse X (inverseOp X) :=
    Classical.epsilon_spec (p := fun B => IsTwoSidedInverse X B) ⟨B, h⟩
  calc inverseOp X = inverseOp X * (X * B) := by rw [h.1, mul_one]
    _ = (inverseOp X * X) * B := (mul_assoc _ _ _).symm
    _ = B := by rw [h1.2, one_mul]
theorem inverse_of_isBoundedBelowBy {T : BddOp H} {a : ℝ} (ha : 0 < a)
    (hT : IsBoundedBelowBy T a) :
    IsTwoSidedInverse T (inverseOp T) ∧ ‖inverseOp T‖ ≤ a⁻¹ := by
  have hlow : ∀ x : H, ‖x‖ ^ 2 * a ≤ ‖inner ℂ (T x) x‖ := by
    intro x
    have h2 := (hT x).2
    have e1 : (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [e1, Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re] at h2
    have h3 : (inner ℂ x (T x)).re ≤ ‖inner ℂ x (T x)‖ := Complex.re_le_norm _
    have e2 : ‖inner ℂ (T x) x‖ = ‖inner ℂ x (T x)‖ := norm_inner_symm _ _
    rw [e2]
    linarith
  have hbelow : ∀ x : H, a * ‖x‖ ≤ ‖T x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 := (hlow x).trans (norm_inner_le_norm _ _)
    have h2 : ‖x‖ * (a * ‖x‖) ≤ ‖x‖ * ‖T x‖ := by nlinarith
    exact le_of_mul_le_mul_left h2 hx'
  have hunit : IsUnit T :=
    ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (c := ⟨a, ha.le⟩) T
      (NNReal.coe_pos.1 ha) hlow
  obtain ⟨u, hu⟩ := hunit
  have hB : IsTwoSidedInverse T (↑u⁻¹ : BddOp H) :=
    ⟨by rw [← hu]; exact u.mul_inv, by rw [← hu]; exact u.inv_mul⟩
  rw [inverseOp_eq hB]
  refine ⟨hB, ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 ha.le) fun g => ?_⟩
  have h1 := hbelow ((↑u⁻¹ : BddOp H) g)
  have e : T ((↑u⁻¹ : BddOp H) g) = g := DFunLike.congr_fun hB.1 g
  rw [e] at h1
  rw [inv_mul_eq_div, le_div_iff₀ ha]
  linarith
theorem resolvent_inverse_and_norm {S : BddOp H} {c w : ℝ} (hS : IsSelfAdjointOp S)
    (hc : 0 < c) (hSc : IsBoundedBelowBy S c) (hw : 0 ≤ w) :
    IsTwoSidedInverse (addScalar S w) (inverseOp (addScalar S w)) ∧
      ‖inverseOp (addScalar S w)‖ ≤ (c + w)⁻¹ :=
  inverse_of_isBoundedBelowBy (by linarith) ((addScalarClaim_holds S hS w c).2 hSc)
theorem sub_eq_mul_sub_mul_of_inverse {M : Type} [Ring M] {A A' B B' : M}
    (h : IsTwoSidedInverse A B) (h' : IsTwoSidedInverse A' B') : B - B' = B * (A' - A) * B' := by
  rw [mul_sub, sub_mul, mul_assoc, h'.1, mul_one, h.2, one_mul]
omit [CompleteSpace H] in
theorem addScalar_sub_addScalar (S : BddOp H) (w w' : ℝ) :
    addScalar S w' - addScalar S w = scalarOp (((w' - w : ℝ)) : ℂ) := by
  ext f
  rw [sub_apply, addScalar_apply, addScalar_apply]
  simp [scalarOp, sub_smul]
theorem norm_resolvent_sub_le {S : BddOp H} {c w w' : ℝ}
    (hS : IsSelfAdjointOp S) (hc : 0 < c) (hSc : IsBoundedBelowBy S c) (hw : 0 ≤ w)
    (hw' : 0 ≤ w') :
    ‖inverseOp (addScalar S w) - inverseOp (addScalar S w')‖ ≤
      c⁻¹ * c⁻¹ * |w - w'| := by
  have h := resolvent_inverse_and_norm hS hc hSc hw
  have h' := resolvent_inverse_and_norm hS hc hSc hw'
  have b : ‖inverseOp (addScalar S w)‖ ≤ c⁻¹ :=
    h.2.trans (inv_anti₀ hc (by linarith))
  have b' : ‖inverseOp (addScalar S w')‖ ≤ c⁻¹ :=
    h'.2.trans (inv_anti₀ hc (by linarith))
  have hn : ‖(scalarOp (((w' - w : ℝ)) : ℂ) : BddOp H)‖ ≤ |w - w'| := by
    refine (norm_scalarOp_le _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  rw [sub_eq_mul_sub_mul_of_inverse h.1 h'.1, addScalar_sub_addScalar]
  calc _ ≤ ‖inverseOp (addScalar S w) * scalarOp (((w' - w : ℝ)) : ℂ)‖ *
        ‖inverseOp (addScalar S w')‖ := norm_mul_le _ _
    _ ≤ (‖inverseOp (addScalar S w)‖ * ‖(scalarOp (((w' - w : ℝ)) : ℂ) :
          BddOp H)‖) * ‖inverseOp (addScalar S w')‖ := by
        gcongr
        exact norm_mul_le _ _
    _ ≤ (c⁻¹ * |w - w'|) * c⁻¹ := by gcongr
    _ = c⁻¹ * c⁻¹ * |w - w'| := by ring
theorem continuousOn_resolventDiff {S : BddOp H} {c : ℝ}
    (hS : IsSelfAdjointOp S) (hc : 0 < c) (hSc : IsBoundedBelowBy S c) :
    ContinuousOn (resolventDiff S) (Ici 0) := by
  have h1 : ContinuousOn (fun w : ℝ => inverseOp (addScalar S w)) (Ici 0) := by
    have hl : LipschitzOnWith (Real.toNNReal (c⁻¹ * c⁻¹))
        (fun w : ℝ => inverseOp (addScalar S w)) (Ici 0) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      exact norm_resolvent_sub_le hS hc hSc hx hy
    exact hl.continuousOn
  have h2 : ContinuousOn
      (fun w : ℝ => (scalarOp (((1 + w)⁻¹ : ℝ) : ℂ) : BddOp H)) (Ici 0) := by
    unfold scalarOp
    have h3 : ContinuousOn (fun w : ℝ => 1 + w) (Ici 0) := continuousOn_const.add continuousOn_id
    have h4 : ContinuousOn (fun w : ℝ => (1 + w)⁻¹) (Ici 0) := by
      refine h3.inv₀ fun w hw => ?_
      have hw0 : (0 : ℝ) ≤ w := hw
      exact (by linarith : (0 : ℝ) < 1 + w).ne'
    have h5 : ContinuousOn (fun w : ℝ => (((1 + w)⁻¹ : ℝ) : ℂ)) (Ici 0) :=
      Complex.continuous_ofReal.comp_continuousOn h4
    exact h5.smul continuousOn_const
  exact h2.sub h1
theorem norm_resolventDiff_le {S : BddOp H} {c w : ℝ}
    (hS : IsSelfAdjointOp S) (hc : 0 < c) (hSc : IsBoundedBelowBy S c) (hw : 0 ≤ w) :
    ‖resolventDiff S w‖ ≤ (1 + c⁻¹) * ‖S - 1‖ * (1 + w ^ 2)⁻¹ := by
  have h := resolvent_inverse_and_norm hS hc hSc hw
  have hw1 : 0 < 1 + w := by linarith
  have hcw : 0 < c + w := by linarith
  obtain ⟨R, hR⟩ : ∃ R, R = inverseOp (addScalar S w) := ⟨_, rfl⟩
  rw [← hR] at h
  have e1 : S - 1 = addScalar S w - (((1 + w : ℝ)) : ℂ) • (1 : BddOp H) := by
    ext f
    rw [sub_apply, sub_apply, addScalar_apply]
    simp [add_smul]
  have e2 : R * (S - 1) = 1 - (((1 + w : ℝ)) : ℂ) • R := by
    rw [e1, mul_sub, h.1.2, mul_smul_comm, mul_one]
  have e3 : resolventDiff S w = ((((1 + w)⁻¹ : ℝ)) : ℂ) • (R * (S - 1)) := by
    have hone : ((((1 + w)⁻¹ : ℝ)) : ℂ) * (((1 + w : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hw1.ne', Complex.ofReal_one]
    rw [e2, smul_sub, smul_smul, hone, one_smul, hR]
    rfl
  have hnorm : ‖R * (S - 1)‖ ≤ (c + w)⁻¹ * ‖S - 1‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h.2 (norm_nonneg _))
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hk : 1 + w ≤ (1 + c⁻¹) * (c + w) := by
    have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc.ne'
    nlinarith [mul_nonneg hci.le hw]
  have hk2 : 1 + w ^ 2 ≤ (1 + c⁻¹) * ((1 + w) * (c + w)) := by
    nlinarith [mul_le_mul_of_nonneg_left hk hw1.le]
  have hsq : 0 < 1 + w ^ 2 := by positivity
  have hs : (1 + w)⁻¹ * (c + w)⁻¹ ≤ (1 + c⁻¹) * (1 + w ^ 2)⁻¹ := by
    rw [← mul_inv, inv_le_iff_one_le_mul₀ (mul_pos hw1 hcw), mul_comm (1 + c⁻¹), mul_assoc,
      inv_mul_eq_div, one_le_div hsq]
    exact hk2
  rw [e3, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hw1)]
  calc (1 + w)⁻¹ * ‖R * (S - 1)‖ ≤ (1 + w)⁻¹ * ((c + w)⁻¹ * ‖S - 1‖) := by gcongr
    _ = ((1 + w)⁻¹ * (c + w)⁻¹) * ‖S - 1‖ := by ring
    _ ≤ ((1 + c⁻¹) * (1 + w ^ 2)⁻¹) * ‖S - 1‖ := by gcongr
    _ = (1 + c⁻¹) * ‖S - 1‖ * (1 + w ^ 2)⁻¹ := by ring
theorem logExists_holds : LogExists H := by
  intro S c hS hc hSc
  have hcont := continuousOn_resolventDiff hS hc hSc
  have hnc : ∀ x : ℝ, NormContinuousOn (resolventDiff S) 0 x := fun x =>
    normContinuousOn_of_continuousOn (hcont.mono fun w hw => hw.1)
  have hnorm : ContinuousOn (fun w => ‖resolventDiff S w‖) (Ici 0) := hcont.norm
  have hint : IntegrableOn (fun w => ‖resolventDiff S w‖) (Ioi 0) := by
    have hg : IntegrableOn (fun w : ℝ => (1 + c⁻¹) * ‖S - 1‖ * (1 + w ^ 2)⁻¹) (Ioi 0) :=
      (integrable_inv_one_add_sq.const_mul _).integrableOn
    refine Integrable.mono' hg
      ((hnorm.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    rw [norm_norm]
    exact norm_resolventDiff_le hS hc hSc (le_of_lt hw)
  have hhalf : IntegrableOnHalfLine (fun w => ‖resolventDiff S w‖) := by
    refine ⟨∫ w in Ioi (0 : ℝ), ‖resolventDiff S w‖, ?_⟩
    have h1 := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    simpa using h1
  have hlog : ∃! X, IsLogOf S X :=
    halfLineIntegral_holds (resolventDiff S) (fun m _ => hnc m) hhalf
  refine ⟨fun w hw => resolvent_inverse_and_norm hS hc hSc hw, fun x _ => hnc x, hnorm, hhalf,
    fun m hm => ?_, hlog, ?_⟩
  · exact (compactIntervalIntegral_holds 0 m _ hm (hnc m)).2.1
  · exact Classical.epsilon_spec (p := fun X => IsLogOf S X) hlog.exists
end Requirements
theorem Calculus.statement_holds : Calculus.Statement := by
  intro H H' _ _ _ _ _ _
  exact ⟨addScalarClaim_holds, opCompleteness_holds, absSummableSeries_holds,
    neumannClaim_holds, compactIntervalIntegral_holds, halfLineIntegral_holds,
    logExists_holds⟩
end OperatorCalculus
end YangMills.Construction
end
