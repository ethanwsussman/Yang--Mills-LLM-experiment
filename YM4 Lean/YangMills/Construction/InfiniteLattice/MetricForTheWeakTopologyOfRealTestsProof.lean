import YangMills.Construction.InfiniteLattice.MetricForTheWeakTopologyOfRealTests
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.WeaklyConvergentSubsequencesOfStates
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
namespace RealWeakState
variable {a : ℝ}
theorem continuous_value (G : C(GaugeField a, ℝ)) :
    Continuous fun ν : RealWeakState a => ν.value G :=
  continuous_iInf_dom (i := G) continuous_induced_dom
theorem abs_value_sub_le_norm [CompactSpace (GaugeField a)] (ν : RealWeakState a)
    (G H : C(GaugeField a, ℝ)) : |ν.value G - ν.value H| ≤ ‖G - H‖ := by
  have hGi := (BoundedContinuousFunction.mkOfCompact G).integrable ν.measure
  have hHi := (BoundedContinuousFunction.mkOfCompact H).integrable ν.measure
  have hdiff : ν.value G - ν.value H = ∫ x, (G - H) x ∂ν.measure := by
    have := integral_sub hGi hHi
    simpa [value, CutoffLattice.integralAgainst] using this.symm
  rw [hdiff, ← Real.norm_eq_abs]
  have hbound := norm_integral_le_of_norm_le_const (μ := ν.measure) (f := fun x => (G - H) x)
    (C := ‖G - H‖) (Eventually.of_forall fun x => (G - H).norm_coe_le_norm x)
  simpa using hbound
theorem hasSum_two_zpow_neg_pnat : HasSum (fun k : ℕ+ => (2 : ℝ) ^ (-((k : ℕ) : ℤ))) 1 := by
  rw [← Equiv.pnatEquivNat.symm.hasSum_iff]
  convert hasSum_geometric_two' (1 : ℝ) using 1
  funext n
  have hn : ((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) = n + 1 := rfl
  simp only [Function.comp_apply, hn, zpow_neg, zpow_natCast, pow_succ]
  field_simp
variable (F : ℕ+ → C(GaugeField a, ℝ))
theorem weakMetricTerm_nonneg (μ ν : RealWeakState a) (k : ℕ+) : 0 ≤ weakMetricTerm F μ ν k :=
  mul_nonneg (by positivity) (le_min zero_le_one (abs_nonneg _))
theorem weakMetricTerm_le (μ ν : RealWeakState a) (k : ℕ+) :
    weakMetricTerm F μ ν k ≤ (2 : ℝ) ^ (-((k : ℕ) : ℤ)) :=
  mul_le_of_le_one_right (by positivity) (min_le_left _ _)
theorem summable_weakMetricTerm (μ ν : RealWeakState a) : Summable (weakMetricTerm F μ ν) :=
  Summable.of_nonneg_of_le (weakMetricTerm_nonneg F μ ν) (weakMetricTerm_le F μ ν)
    hasSum_two_zpow_neg_pnat.summable
theorem weakMetric_nonneg (μ ν : RealWeakState a) : 0 ≤ weakMetric F μ ν :=
  tsum_nonneg (weakMetricTerm_nonneg F μ ν)
theorem weakMetric_le_one (μ ν : RealWeakState a) : weakMetric F μ ν ≤ 1 :=
  hasSum_le (weakMetricTerm_le F μ ν) (summable_weakMetricTerm F μ ν).hasSum
    hasSum_two_zpow_neg_pnat
theorem weakMetricTerm_le_weakMetric (μ ν : RealWeakState a) (k : ℕ+) :
    weakMetricTerm F μ ν k ≤ weakMetric F μ ν :=
  le_hasSum (summable_weakMetricTerm F μ ν).hasSum k fun j _ => weakMetricTerm_nonneg F μ ν j
theorem continuous_weakMetric_left (ν : RealWeakState a) :
    Continuous fun μ => weakMetric F μ ν := by
  unfold weakMetric
  refine continuous_tsum (fun k => ?_) hasSum_two_zpow_neg_pnat.summable fun k μ => ?_
  · unfold weakMetricTerm
    exact continuous_const.mul
      (continuous_const.min ((continuous_value (F k)).sub continuous_const).abs)
  · rw [Real.norm_of_nonneg (weakMetricTerm_nonneg F μ ν k)]
    exact weakMetricTerm_le F μ ν k
theorem weakMetric_self (μ : RealWeakState a) : weakMetric F μ μ = 0 := by
  simp [weakMetric, weakMetricTerm]
theorem weakMetric_comm (μ ν : RealWeakState a) :
    weakMetric F μ ν = weakMetric F ν μ := by
  unfold weakMetric weakMetricTerm
  exact tsum_congr fun k => by rw [abs_sub_comm]
theorem weakMetric_triangle (μ ν ρ : RealWeakState a) :
    weakMetric F μ ρ ≤ weakMetric F μ ν + weakMetric F ν ρ := by
  refine hasSum_le (fun k => ?_) (summable_weakMetricTerm F μ ρ).hasSum
    ((summable_weakMetricTerm F μ ν).hasSum.add (summable_weakMetricTerm F ν ρ).hasSum)
  have hmin : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → min 1 (s + t) ≤ min 1 s + min 1 t := by
    intro s t hs ht
    simp only [min_def]
    split_ifs <;> linarith
  have htri := abs_sub_le (μ.value (F k)) (ν.value (F k)) (ρ.value (F k))
  have hw : (0 : ℝ) ≤ (2 : ℝ) ^ (-((k : ℕ) : ℤ)) := by positivity
  unfold weakMetricTerm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    ((min_le_min_left 1 htri).trans (hmin _ _ (abs_nonneg _) (abs_nonneg _))) hw
variable {F}
theorem IsSupNormDenseSeq.exists_norm_sub_lt [CompactSpace (GaugeField a)]
    (hF : IsSupNormDenseSeq F) (H : C(GaugeField a, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, ‖H - F k‖ < ε := by
  obtain ⟨k, hk⟩ := hF H ε hε
  exact ⟨k, by rwa [CutoffLattice.supNorm_eq_norm] at hk⟩
theorem tendsto_value_of_tendsto_weakMetric {μ : ℕ → RealWeakState a} {ν : RealWeakState a}
    (h : Tendsto (fun i => weakMetric F (μ i) ν) atTop (𝓝 0)) (k : ℕ+) :
    Tendsto (fun i => (μ i).value (F k)) atTop (𝓝 (ν.value (F k))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hw : (0 : ℝ) < (2 : ℝ) ^ (-((k : ℕ) : ℤ)) := by positivity
  have hδ : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h _ (mul_pos hw hδ)
  refine ⟨N, fun i hi => ?_⟩
  have h1 := hN i hi
  rw [Real.dist_0_eq_abs, abs_of_nonneg (weakMetric_nonneg F _ _)] at h1
  have h2 := (weakMetricTerm_le_weakMetric F (μ i) ν k).trans_lt h1
  have h3 := lt_of_mul_lt_mul_left h2 hw.le
  rw [Real.dist_eq]
  rcases min_lt_iff.1 (lt_min_iff.1 h3).1 with h4 | h4
  · rcases min_lt_iff.1 (lt_min_iff.1 h3).2 with h5 | h5
    · exact absurd h5 (lt_irrefl 1)
    · exact h5.trans h4
  · exact h4
theorem tendstoWeakly_of_tendsto_weakMetric [CompactSpace (GaugeField a)]
    (hF : IsSupNormDenseSeq F) {μ : ℕ → RealWeakState a} {ν : RealWeakState a}
    (h : Tendsto (fun i => weakMetric F (μ i) ν) atTop (𝓝 0)) : TendstoWeakly μ ν := by
  intro G
  change Tendsto (fun i => (μ i).value G) atTop (𝓝 (ν.value G))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := hF.exists_norm_sub_lt G (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_value_of_tendsto_weakMetric h k) (ε / 3)
    (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  have h1 := abs_lt.1 (hN i hi |>.trans_eq' (Real.dist_eq _ _).symm)
  have h2 := abs_le.1 (abs_value_sub_le_norm (μ i) G (F k))
  have h3 := abs_le.1 (abs_value_sub_le_norm ν G (F k))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
theorem tendsto_weakMetric_iff [CompactSpace (GaugeField a)] (hF : IsSupNormDenseSeq F)
    (μ : ℕ → RealWeakState a) (ν : RealWeakState a) :
    Tendsto (fun i => weakMetric F (μ i) ν) atTop (𝓝 0) ↔ TendstoWeakly μ ν := by
  refine ⟨tendstoWeakly_of_tendsto_weakMetric hF, fun h => ?_⟩
  have h1 := ((continuous_weakMetric_left F ν).tendsto ν).comp
    ((tendstoWeakly_iff_tendsto μ ν).1 h)
  rwa [weakMetric_self] at h1
theorem eq_of_weakMetric_eq_zero [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)] (hF : IsSupNormDenseSeq F)
    {μ ν : RealWeakState a} (h : weakMetric F μ ν = 0) : μ = ν := by
  have hk : ∀ k, μ.value (F k) = ν.value (F k) := by
    intro k
    have h1 := weakMetricTerm_le_weakMetric F μ ν k
    rw [h] at h1
    have hw : (0 : ℝ) < (2 : ℝ) ^ (-((k : ℕ) : ℤ)) := by positivity
    have h2 : min 1 |μ.value (F k) - ν.value (F k)| ≤ 0 := by
      by_contra hc
      exact absurd h1 (not_le.2 (mul_pos hw (not_le.1 hc)))
    rcases min_le_iff.1 h2 with h3 | h3
    · exact absurd h3 (by norm_num)
    · exact sub_eq_zero.1 (abs_nonpos_iff.1 h3)
  have hG : ∀ G : C(GaugeField a, ℝ), μ.value G = ν.value G := by
    intro G
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨k, hk'⟩ := hF.exists_norm_sub_lt G (show 0 < ε / 2 by positivity)
    have h2 := abs_le.1 (abs_value_sub_le_norm μ G (F k))
    have h3 := abs_le.1 (abs_value_sub_le_norm ν G (F k))
    have h4 := hk k
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  let := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  have hm : μ.measure = ν.measure :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => hG ⟨f, f.continuous⟩
  exact Subtype.ext hm
theorem exists_metricSpace_weakMetric [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)] (hF : IsSupNormDenseSeq F) :
    ∃ M : MetricSpace (RealWeakState a),
      (∀ μ ν, M.dist μ ν = weakMetric F μ ν) ∧
        M.toUniformSpace.toTopologicalSpace = RealWeakState.weakTopology := by
  refine ⟨MetricSpace.ofDistTopology (weakMetric F) (weakMetric_self F)
    (weakMetric_comm F) (weakMetric_triangle F) (fun s => ?_)
    (fun _ _ h => eq_of_weakMetric_eq_zero hF h), fun _ _ => rfl, rfl⟩
  constructor
  · intro hs x hx
    by_contra hc
    push Not at hc
    choose y hy hys using fun n : ℕ => hc (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    have ht : Tendsto (fun n => weakMetric F (y n) x) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => weakMetric_nonneg F _ _) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [weakMetric_comm]
      exact (hy n).le
    have hw := (tendstoWeakly_iff_tendsto y x).1 (tendstoWeakly_of_tendsto_weakMetric hF ht)
    obtain ⟨n, hn⟩ := (hw.eventually (hs.mem_nhds hx)).exists
    exact hys n hn
  · intro h
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨ε, hε, hb⟩ := h x hx
    have ho : IsOpen {y | weakMetric F y x < ε} :=
      isOpen_lt (continuous_weakMetric_left F x) continuous_const
    refine Filter.mem_of_superset (ho.mem_nhds ?_) fun y hy => hb y ?_
    · simpa [weakMetric_self] using hε
    · rw [weakMetric_comm]
      exact hy
theorem exists_strictMono_tendstoWeakly
    (hseq : ∀ μ : ℕ+ → RealWeakState a, ∃ (i : ℕ+ → ℕ+) (ν : RealWeakState a), StrictMono i ∧
      ∀ G : C(GaugeField a, ℝ),
        Tendsto (fun k : ℕ+ => (μ (i k)).value G) atTop (𝓝 (ν.value G)))
    (x : ℕ → RealWeakState a) :
    ∃ (ν : RealWeakState a) (φ : ℕ → ℕ), StrictMono φ ∧ TendstoWeakly (x ∘ φ) ν := by
  obtain ⟨i, ν, hi, hν⟩ := hseq fun k => x k
  have hsucc : Tendsto Nat.succPNat atTop atTop :=
    Nat.succPNat_strictMono.monotone.tendsto_atTop_atTop fun b =>
      ⟨b, by rw [← PNat.coe_le_coe, Nat.succPNat_coe]; exact Nat.le_succ _⟩
  refine ⟨ν, fun n => (i n.succPNat : ℕ), fun m n hmn => ?_, fun G => ?_⟩
  · exact hi (Nat.succPNat_strictMono hmn)
  · exact (hν G).comp hsucc
end RealWeakState
open RealWeakState in
theorem weakMetricStatement_holds
    (hcompact : EveryStateSequenceHasWeaklyConvergentSubsequence.Statement)
    (hspace : GaugeFieldSpace.Statement) :
    WeakMetricStatement := by
  intro L K hL hK F hF
  have hsp := (hspace
    { L := L, isAdmissible := hL, K := ⟨K, hK⟩, m := 1, coupling := 1,
      coupling_pos := one_pos }).1
  have : CompactSpace (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) := hsp.2.2.2.2.1
  have : TopologicalSpace.MetrizableSpace (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :=
    hsp.2.2.2.2.2
  obtain ⟨M, hMd, hMt⟩ := exists_metricSpace_weakMetric hF
  have hmet : TopologicalSpace.MetrizableSpace
      (RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) := by
    rw [← hMt]
    infer_instance
  have hs : IsSeqCompact
      (Set.univ : Set (RealWeakState (PeriodicLattice.meshSize L (K : ℤ)))) := by
    intro x _
    obtain ⟨ν, φ, hφ, hν⟩ := exists_strictMono_tendstoWeakly (fun μ => hcompact ⟨L, hL, ⟨K, hK⟩, 1⟩ μ) x
    exact ⟨ν, Set.mem_univ _, φ, hφ, (tendstoWeakly_iff_tendsto _ _).1 hν⟩
  exact ⟨fun μ ν => ⟨summable_weakMetricTerm F μ ν, weakMetric_nonneg F μ ν,
    weakMetric_le_one F μ ν⟩, continuous_weakMetric_left F, tendsto_weakMetric_iff hF,
    ⟨M, hMd, hMt⟩, ⟨hs.isCompact⟩, hmet⟩
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
