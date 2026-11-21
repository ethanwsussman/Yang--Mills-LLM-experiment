import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import Mathlib
set_option autoImplicit false
open Filter Topology Finset
open scoped NNReal
namespace YangMills.Construction.RealAnalyticity
noncomputable def coordMonomial {N : ℕ} (y : Fin N → ℝ) (m : Fin N → ℕ) : ℂ :=
  ∏ j, (y j : ℂ) ^ m j
theorem hasSum_sum_piAntidiag_of_hasSum {N : ℕ} {E : Type} [NormedAddCommGroup E]
    [CompleteSpace E] {f : (Fin N → ℕ) → E} {S : E} (h : HasSum f S) :
    HasSum (fun n : ℕ => ∑ m ∈ piAntidiag univ n, f m) S := by
  have key := h.tsum_fiberwise (fun m : Fin N → ℕ => ∑ j, m j)
  convert key using 2 with n
  rw [_root_.tsum_subtype, tsum_eq_sum (s := piAntidiag univ n)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Set.indicator_of_mem]
    simpa using hm
  · intro m hm
    rw [Set.indicator_of_notMem]
    simpa using hm
theorem exists_multilinear_diag_eq_coordMonomial {N : ℕ} (m : Fin N → ℕ) (n : ℕ)
    (hm : ∑ j, m j = n) :
    ∃ M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin N → ℝ) ℂ,
      ‖M‖ ≤ 1 ∧ ∀ y, M (fun _ => y) = coordMonomial y m := by
  subst hm
  let e := finSigmaFinEquiv (m := N) (n := m)
  let σ : Fin (∑ j, m j) → Fin N := fun k => (e.symm k).1
  refine ⟨(ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin (∑ j, m j)) ℂ).compContinuousLinearMap
    fun k => Complex.ofRealCLM.comp (ContinuousLinearMap.proj (σ k)), ?_, ?_⟩
  · refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, norm_prod, Complex.norm_real,
      one_mul]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => norm_le_pi_norm (v k) (σ k)
  · intro y
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, coordMonomial]
    rw [Fintype.prod_equiv e.symm (fun k => (y (σ k) : ℂ)) (fun x => (y x.1 : ℂ))
      (fun _ => rfl), Fintype.prod_sigma]
    simp
theorem analyticAt_of_hasSum_coordMonomial {N : ℕ} (g : (Fin N → ℝ) → ℂ) (u₀ : Fin N → ℝ)
    (c : (Fin N → ℕ) → ℂ)
    (h : ∀ᶠ u in 𝓝 u₀, HasSum (fun m => coordMonomial (u - u₀) m * c m) (g u)) :
    AnalyticAt ℝ g u₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = δ / 2 := ⟨⟨δ / 2, by positivity⟩, rfl⟩
  have hrpos : 0 < (r : ℝ) := by rw [hr]; positivity
  have hrδ : (r : ℝ) < δ := by rw [hr]; linarith
  have hdist : dist (u₀ + fun _ => (r : ℝ)) u₀ < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hrpos.le).2 fun _ => by
      simp [abs_of_pos hrpos]) hrδ
  have hw : Summable fun m : Fin N → ℕ => ‖c m‖ * (r : ℝ) ^ ∑ j, m j := by
    have h1 := (hball hdist).summable.norm
    refine h1.congr fun m => ?_
    rw [add_sub_cancel_left, norm_mul, coordMonomial, norm_prod]
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
      Finset.prod_pow_eq_pow_sum]
    ring
  have hdeg := (hasSum_sum_piAntidiag_of_hasSum hw.hasSum).summable
  have hex : ∀ (n : ℕ) (m : Fin N → ℕ),
      ∃ M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin N → ℝ) ℂ,
        ∑ j, m j = n → ‖M‖ ≤ 1 ∧ ∀ y, M (fun _ => y) = coordMonomial y m := by
    intro n m
    by_cases hm : ∑ j, m j = n
    · obtain ⟨M, hM⟩ := exists_multilinear_diag_eq_coordMonomial m n hm
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h' => absurd h' hm⟩
  choose M hM using hex
  let p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℂ :=
    fun n => ∑ m ∈ piAntidiag univ n, c m • M n m
  have hdegree : ∀ n : ℕ, ∀ m ∈ piAntidiag (univ : Finset (Fin N)) n, ∑ j, m j = n := by
    intro n m hm
    exact (mem_piAntidiag.1 hm).1
  have hpapply : ∀ n y, p n (fun _ => y) = ∑ m ∈ piAntidiag univ n, coordMonomial y m * c m := by
    intro n y
    simp only [p, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [(hM n m (hdegree n m hm)).2 y, smul_eq_mul, mul_comm]
  have hpnorm : ∀ n, ‖p n‖ ≤ ∑ m ∈ piAntidiag univ n, ‖c m‖ := by
    intro n
    refine norm_sum_le_of_le _ fun m hm => ?_
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hM n m (hdegree n m hm)).1
  have hrad : (r : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm (Summable.of_nonneg_of_le
      (fun n => by positivity) (fun n => ?_) hdeg)
    calc ‖p n‖ * (r : ℝ) ^ n ≤ (∑ m ∈ piAntidiag univ n, ‖c m‖) * (r : ℝ) ^ n := by
          gcongr
          exact hpnorm n
      _ = ∑ m ∈ piAntidiag univ n, ‖c m‖ * (r : ℝ) ^ ∑ j, m j := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m hm => by rw [hdegree n m hm]
  have hseries : HasFPowerSeriesOnBall g p u₀ (r : ENNReal) := by
    refine ⟨hrad, by simpa using hrpos, fun {y} hy => ?_⟩
    have hy' : ‖y‖ < r := by simpa using hy
    have hd : dist (u₀ + y) u₀ < δ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hy'.trans hrδ
    have key := hasSum_sum_piAntidiag_of_hasSum (hball hd)
    simp only [add_sub_cancel_left] at key
    simpa only [hpapply] using key
  exact hseries.analyticAt
theorem exists_hasSum_coordMonomial_of_analyticAt {N : ℕ} (g : (Fin N → ℝ) → ℂ)
    (u₀ : Fin N → ℝ) (h : AnalyticAt ℝ g u₀) :
    ∃ c : (Fin N → ℕ) → ℂ,
      ∀ᶠ u in 𝓝 u₀, HasSum (fun m => coordMonomial (u - u₀) m * c m) (g u) := by
  obtain ⟨p, r, hp⟩ := h
  obtain ⟨r', hr'0, hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hlt : (r' : ENNReal) < p.radius := lt_of_lt_of_le hr'r hp.r_le
  have hr'pos : 0 < (r' : ℝ) := by exact_mod_cast hr'0
  obtain ⟨C, hC0, hC⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr'pos hlt
  set ρ : ℝ := r' / (2 * ((N : ℝ) + 1)) with hρ
  have hN : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
  have hρpos : 0 < ρ := div_pos hr'pos hN
  have hρr : ρ < r' := by
    rw [hρ, div_lt_iff₀ hN]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hq : (N : ℝ) * (ρ / r') ≤ 1 / 2 := by
    have : ρ / r' = 1 / (2 * ((N : ℝ) + 1)) := by
      rw [hρ]
      field_simp
    rw [this, mul_one_div, div_le_iff₀ hN]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  let a : (Σ n : ℕ, (Fin n → Fin N)) → ℂ := fun t => p t.1 fun i => Pi.single (t.2 i) 1
  let F : (Fin N → ℝ) → (Σ n : ℕ, (Fin n → Fin N)) → ℂ :=
    fun y t => (∏ i, (y (t.2 i) : ℂ)) * a t
  let κ : (Σ n : ℕ, (Fin n → Fin N)) → Fin N → ℕ :=
    fun t j => #{i | t.2 i = j}
  have hexpand : ∀ (n : ℕ) (y : Fin N → ℝ),
      p n (fun _ => y) = ∑ s : Fin n → Fin N, F y ⟨n, s⟩ := by
    intro n y
    have hy : (fun _ : Fin n => y) =
        fun _ => ∑ j, y j • (Pi.single j 1 : Fin N → ℝ) := by
      funext _ k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hy, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [F, a]
    rw [Complex.real_smul]
    push_cast
    rfl
  have hbound : ∀ (y : Fin N → ℝ), ‖y‖ ≤ ρ → ∀ t, ‖F y t‖ ≤ C * (ρ / r') ^ t.1 := by
    intro y hy t
    have h1 : ‖∏ i, (y (t.2 i) : ℂ)‖ ≤ ρ ^ t.1 := by
      rw [norm_prod]
      calc ∏ i, ‖(y (t.2 i) : ℂ)‖ ≤ ∏ _i : Fin t.1, ρ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by
              rw [Complex.norm_real]
              exact (norm_le_pi_norm y _).trans hy
        _ = ρ ^ t.1 := by simp
    have h2 : ‖a t‖ ≤ C / (r' : ℝ) ^ t.1 := by
      refine le_trans ((p t.1).le_opNorm _) ?_
      have h3 : ∏ i, ‖(Pi.single (t.2 i) 1 : Fin N → ℝ)‖ ≤ 1 := by
        refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
        rw [Pi.norm_single]
        simp
      calc ‖p t.1‖ * _ ≤ ‖p t.1‖ * 1 := by gcongr
        _ ≤ C / (r' : ℝ) ^ t.1 := by rw [mul_one]; exact hC _
    calc ‖F y t‖ = ‖∏ i, (y (t.2 i) : ℂ)‖ * ‖a t‖ := norm_mul _ _
      _ ≤ ρ ^ t.1 * (C / (r' : ℝ) ^ t.1) := by gcongr
      _ = C * (ρ / r') ^ t.1 := by rw [div_pow]; ring
  have hB : Summable fun t : (Σ n : ℕ, (Fin n → Fin N)) => C * (ρ / r') ^ t.1 := by
    refine (summable_sigma_of_nonneg fun t => by positivity).2 ⟨fun n => Summable.of_finite, ?_⟩
    have hgeo : Summable fun n : ℕ => C * ((N : ℝ) * (ρ / r')) ^ n :=
      (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left C
    refine hgeo.congr fun n => ?_
    rw [tsum_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, mul_pow]
    ring
  have hF : ∀ (y : Fin N → ℝ), ‖y‖ ≤ ρ → HasSum (F y) (g (u₀ + y)) := by
    intro y hy
    have hsum : Summable (F y) := Summable.of_norm_bounded hB (hbound y hy)
    have hS := hsum.hasSum
    have hn := hS.sigma fun n => hasSum_fintype _
    have hyball : y ∈ Metric.eball (0 : Fin N → ℝ) r := by
      refine lt_of_le_of_lt ?_ hr'r
      rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hy.trans hρr.le)
    have hg := hp.hasSum hyball
    have hn' : HasSum (fun n => p n fun _ => y) (∑' t, F y t) := by
      simpa only [hexpand] using hn
    rw [← hn'.unique hg]
    exact hS
  have hprod : ∀ (y : Fin N → ℝ) (t : Σ n : ℕ, (Fin n → Fin N)),
      ∏ i, (y (t.2 i) : ℂ) = coordMonomial y (κ t) := by
    intro y t
    rw [coordMonomial, ← Finset.prod_fiberwise univ t.2]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => (y j : ℂ)) (fun i hi => by
      rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
  refine ⟨fun m => ∑' b : κ ⁻¹' {m}, a b, ?_⟩
  have hnear : ∀ᶠ u in 𝓝 u₀, ‖u - u₀‖ ≤ ρ := by
    filter_upwards [Metric.closedBall_mem_nhds u₀ hρpos] with u hu
    simpa [dist_eq_norm] using hu
  filter_upwards [hnear] with u hu
  have key := (hF (u - u₀) hu).tsum_fiberwise κ
  rw [add_sub_cancel] at key
  have hterm : ∀ m, ∑' b : κ ⁻¹' {m}, F (u - u₀) b =
      coordMonomial (u - u₀) m * ∑' b : κ ⁻¹' {m}, a b := by
    intro m
    rw [← tsum_mul_left]
    refine tsum_congr fun b => ?_
    have hb : κ b.1 = m := b.2
    simp only [F]
    rw [hprod, hb]
  simp only [hterm] at key
  exact key
theorem coordRealAnalyticIffAnalytic_holds : CoordRealAnalyticIffAnalytic := by
  intro N D G hD
  let ι : (Fin N → ℝ) → Coordinates.ComplexCoordinates N := fun u j => (u j : ℂ)
  have hι : Topology.IsEmbedding ι :=
    Function.LeftInverse.isEmbedding (f := fun (z : Coordinates.ComplexCoordinates N) j => (z j).re)
      (fun u => by funext j; simp [ι]) (by fun_prop) (by fun_prop)
  have hrange : Set.range ι = Coordinates.ComplexCoordinates.realLocus N := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩ j
      simp [ι]
    · intro hz
      refine ⟨fun j => (z j).re, ?_⟩
      funext j
      exact Complex.ext (by simp [ι]) (by simpa [ι] using (hz j).symm)
  have hnhds : ∀ u, 𝓝[Coordinates.ComplexCoordinates.realLocus N] ι u = map ι (𝓝 u) := fun u => by
    rw [← hrange, hι.isInducing.map_nhds_eq]
  have hmono : ∀ (u v : Fin N → ℝ) (m : Fin N → ℕ),
      ∏ j, (ι v j - ι u j) ^ m j = coordMonomial (v - u) m := by
    intro u v m
    simp [coordMonomial, ι]
  constructor
  · rintro ⟨⟨O, hO, hDO⟩, hser⟩
    have hpre : ι ⁻¹' D = ι ⁻¹' O := by
      ext u
      have hu : ι u ∈ Coordinates.ComplexCoordinates.realLocus N := hrange ▸ Set.mem_range_self u
      simp [hDO, hu]
    refine ⟨hpre ▸ hO.preimage hι.continuous, fun u hu => ?_⟩
    obtain ⟨c, hc⟩ := hser (ι u) hu
    rw [hnhds, eventually_map] at hc
    refine analyticAt_of_hasSum_coordMonomial _ u (fun m => c m 0) (hc.mono fun v hv => ?_)
    have h0 := Pi.hasSum.1 hv 0
    simpa only [Pi.smul_apply, hmono, smul_eq_mul] using h0
  · rintro ⟨hopen, han⟩
    obtain ⟨O, hO, hOD⟩ := hι.isInducing.isOpen_iff.1 hopen
    refine ⟨⟨O, hO, ?_⟩, fun a ha => ?_⟩
    · ext z
      constructor
      · intro hz
        obtain ⟨u, rfl⟩ := (hrange ▸ hD hz : z ∈ Set.range ι)
        have : u ∈ ι ⁻¹' O := hOD ▸ hz
        exact ⟨this, hD hz⟩
      · rintro ⟨hzO, hz⟩
        obtain ⟨u, rfl⟩ := (hrange ▸ hz : z ∈ Set.range ι)
        have : u ∈ ι ⁻¹' D := hOD ▸ hzO
        exact this
    · obtain ⟨u, rfl⟩ := (hrange ▸ hD ha : a ∈ Set.range ι)
      obtain ⟨c, hc⟩ := exists_hasSum_coordMonomial_of_analyticAt _ u (han u ha)
      refine ⟨fun m _ => c m, ?_⟩
      rw [hnhds, eventually_map]
      refine hc.mono fun v hv => Pi.hasSum.2 fun _ => ?_
      simpa only [Pi.smul_apply, hmono, smul_eq_mul] using hv
end YangMills.Construction.RealAnalyticity
