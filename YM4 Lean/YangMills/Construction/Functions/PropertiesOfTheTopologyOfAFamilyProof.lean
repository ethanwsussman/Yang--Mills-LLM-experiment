import YangMills.Construction.Functions.FamilyDistanceSeries
import YangMills.Construction.Functions.PropertiesOfTheTopologyOfAFamily
import Mathlib
set_option autoImplicit false
open scoped Topology
open YangMills.Construction.FamilyTopology YangMills.Construction.PeriodicSpace
noncomputable section
namespace YangMills.Construction.FamilyTopology.Properties
section Members
variable {X 𝔄 : Type}
theorem continuous_familyTopology_apply (f : 𝔄 → X → ℝ) (b : 𝔄) :
    Continuous[familyTopology f, inferInstance] (f b) := by
  refine @Continuous.mk _ _ (familyTopology f) _ _ fun V hV => ?_
  show f b ⁻¹' V ∈ familyOpens f
  refine ⟨{f b ⁻¹' V}, ?_, by simp⟩
  rintro C rfl
  exact ⟨1, fun _ => b, fun _ => V, fun _ => hV, by ext y; simp⟩
theorem familyTopology_isOpen_of_forall_continuous (f : 𝔄 → X → ℝ) (τ : TopologicalSpace X)
    (hτ : ∀ b, Continuous[τ, inferInstance] (f b)) (W : Set X)
    (hW : IsOpen[familyTopology f] W) : IsOpen[τ] W := by
  have hW' : W ∈ familyOpens f := hW
  obtain ⟨𝒞, h𝒞, rfl⟩ := hW'
  refine isOpen_sUnion fun C hC => ?_
  obtain ⟨k, c, V, hV, rfl⟩ := h𝒞 C hC
  have hC' : {y | ∀ i, f (c i) y ∈ V i} = ⋂ i, f (c i) ⁻¹' V i := by
    ext y
    simp
  rw [hC']
  exact isOpen_iInter_of_finite fun i => (hτ (c i)).isOpen_preimage _ (hV i)
theorem familyTopology_eq_iInf_induced (f : 𝔄 → X → ℝ) :
    familyTopology f = ⨅ b, TopologicalSpace.induced (f b) inferInstance := by
  apply le_antisymm
  · exact le_iInf fun b => continuous_iff_le_induced.1 (continuous_familyTopology_apply f b)
  · rw [TopologicalSpace.le_def]
    exact familyTopology_isOpen_of_forall_continuous f _
      fun b => continuous_iff_le_induced.2 (iInf_le _ b)
end Members
section Limits
variable {J : Set ℕ+} {hJ : J.Infinite}
theorem realTendstoAlong_iff (u : J → ℝ) (w : ℝ) :
    RealTendstoAlong J hJ u w ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℤ, ∀ j : J, n ≤ (((j : ℕ+) : ℕ) : ℤ) → ‖u j - w‖ < ε := by
  constructor
  · intro h ε hε
    obtain ⟨n, hn⟩ := h ε hε
    refine ⟨n, fun j hj => ?_⟩
    obtain ⟨_, hlt⟩ := hn j.1 j.2 hj
    exact hlt
  · intro h ε hε
    obtain ⟨n, hn⟩ := h ε hε
    exact Exists.intro n fun j hj hle => ⟨hj, hn ⟨j, hj⟩ hle⟩
theorem tendstoAlong_real_iff (u : J → ℝ) (w : ℝ) :
    TendstoAlong inferInstance J hJ u w ↔ RealTendstoAlong J hJ u w := by
  rw [realTendstoAlong_iff]
  constructor
  · intro h ε hε
    obtain ⟨n, hn⟩ := h (Metric.ball w ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
    exact ⟨n, fun j hj => mem_ball_iff_norm.1 (hn j hj)⟩
  · intro h W hW hw
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW w hw
    obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun j hj => hball (mem_ball_iff_norm.2 (hn j hj))⟩
end Limits
section Metric
variable {X 𝔄 : Type}
theorem min_one_abs_sub_le_add (a b c : ℝ) :
    min 1 |a - c| ≤ min 1 |a - b| + min 1 |b - c| := by
  have hle := abs_sub_le a b c
  have hp := abs_nonneg (a - b)
  have hq := abs_nonneg (b - c)
  have hone : min 1 |a - c| ≤ 1 := min_le_left _ _
  rcases le_total 1 |a - b| with h | h
  · have : 0 ≤ min 1 |b - c| := le_min zero_le_one hq
    rw [min_eq_left h]
    linarith
  · rcases le_total 1 |b - c| with h' | h'
    · have : 0 ≤ min 1 |a - b| := le_min zero_le_one hp
      rw [min_eq_left h']
      linarith
    · rw [min_eq_right h, min_eq_right h']
      exact (min_le_right _ _).trans hle
theorem summable_two_zpow_neg : Summable fun s : ℕ+ => (2 : ℝ) ^ (-((s : ℕ) : ℤ)) := by
  refine (summable_geometric_two.comp_injective PNat.coe_injective).congr fun s => ?_
  simp [zpow_neg]
variable (hS : FamilySeries.FamilySeriesTerms) (f : 𝔄 → X → ℝ) (g : ℕ+ → 𝔄)
  (hg : Function.Surjective g)
include hS hg
theorem seriesTerm_nonneg (y y' : X) (s : ℕ+) :
    0 ≤ FamilySeries.seriesTerm f g y y' s :=
  ((hS X 𝔄 f g hg y y').1 s).1
theorem isMetricFunction_familyDistance (hsep : SeparatesPoints f) :
    IsMetricFunction (familyDistance f g hg) where
  nonneg y y' := hasSum_le (seriesTerm_nonneg hS f g hg y y') hasSum_zero (hS X 𝔄 f g hg y y').2
  eq_zero_iff y y' := by
    constructor
    · intro h0
      by_contra hne
      obtain ⟨b, hb⟩ := hsep y y' hne
      obtain ⟨s, rfl⟩ := hg b
      have hs := (hS X 𝔄 f g hg y y').2
      rw [h0, hasSum_zero_iff_of_nonneg (seriesTerm_nonneg hS f g hg y y')] at hs
      have hzero : FamilySeries.seriesTerm f g y y' s = 0 := congrFun hs s
      have hpos : 0 < FamilySeries.seriesTerm f g y y' s :=
        mul_pos (zpow_pos (by norm_num) _)
          (lt_min one_pos (abs_pos.2 (sub_ne_zero.2 hb)))
      exact hpos.ne' hzero
    · rintro rfl
      simp [familyDistance]
  symm y y' := by
    unfold familyDistance
    exact tsum_congr fun s => by rw [abs_sub_comm]
  triangle y y' y'' := by
    refine hasSum_le (fun s => ?_) (hS X 𝔄 f g hg y y'').2
      ((hS X 𝔄 f g hg y y').2.add (hS X 𝔄 f g hg y' y'').2)
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-((s : ℕ) : ℤ)) := (zpow_pos (by norm_num) _).le
    have := mul_le_mul_of_nonneg_left
      (min_one_abs_sub_le_add (f (g s) y) (f (g s) y') (f (g s) y'')) hpow
    rw [mul_add] at this
    exact this
theorem familyTopology_isOpen_openBallOf (y : X) (r : ℝ) :
    IsOpen[familyTopology f] (openBallOf (familyDistance f g hg) y r) := by
  let _ : TopologicalSpace X := familyTopology f
  have hc : Continuous fun y' => ∑' s : ℕ+, FamilySeries.seriesTerm f g y y' s := by
    refine continuous_tsum (fun s => ?_) summable_two_zpow_neg fun s y' => ?_
    · have hm : Continuous (f (g s)) := continuous_familyTopology_apply f (g s)
      exact continuous_const.mul (continuous_const.min (continuous_const.sub hm).abs)
    · have hb := (hS X 𝔄 f g hg y y').1 s
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
  exact isOpen_lt hc continuous_const
theorem exists_openBallOf_subset_preimage (y : X) (b : 𝔄) (V : Set ℝ) (hV : IsOpen V)
    (hy : f b y ∈ V) :
    ∃ r : ℝ, 0 < r ∧ openBallOf (familyDistance f g hg) y r ⊆ f b ⁻¹' V := by
  obtain ⟨s, rfl⟩ := hg b
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV _ hy
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-((s : ℕ) : ℤ)) := zpow_pos (by norm_num) _
  have hδ : 0 < min ε 1 := lt_min hε one_pos
  refine ⟨(2 : ℝ) ^ (-((s : ℕ) : ℤ)) * min ε 1, mul_pos hpow hδ, fun y' hy' => ?_⟩
  have hterm : FamilySeries.seriesTerm f g y y' s ≤ familyDistance f g hg y y' :=
    le_hasSum (hS X 𝔄 f g hg y y').2 s fun j _ => seriesTerm_nonneg hS f g hg y y' j
  have hlt : (2 : ℝ) ^ (-((s : ℕ) : ℤ)) * min 1 |f (g s) y - f (g s) y'| <
      (2 : ℝ) ^ (-((s : ℕ) : ℤ)) * min ε 1 := lt_of_le_of_lt hterm hy'
  have hmin : min 1 |f (g s) y - f (g s) y'| < min ε 1 := lt_of_mul_lt_mul_left hlt hpow.le
  have habs : |f (g s) y - f (g s) y'| < ε := by
    rcases min_lt_iff.1 hmin with h | h
    · exact absurd (h.trans_le (min_le_right _ _)) (lt_irrefl _)
    · exact h.trans_le (min_le_left _ _)
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  exact habs
theorem exists_openBallOf_subset (W : Set X) (hW : W ∈ familyOpens f) (y : X) (hy : y ∈ W) :
    ∃ r : ℝ, 0 < r ∧ openBallOf (familyDistance f g hg) y r ⊆ W := by
  obtain ⟨𝒞, h𝒞, rfl⟩ := hW
  obtain ⟨C, hC, hyC⟩ := hy
  obtain ⟨k, c, V, hV, rfl⟩ := h𝒞 C hC
  have hi : ∀ i, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      openBallOf (familyDistance f g hg) y r ⊆ f (c i) ⁻¹' V i := by
    intro i
    obtain ⟨r, hr, hsub⟩ := exists_openBallOf_subset_preimage hS f g hg y (c i) (V i) (hV i) (hyC i)
    filter_upwards [Ioo_mem_nhdsGT hr] with r' hr' z hz
    exact hsub (lt_trans hz hr'.2)
  obtain ⟨r, hall, hr⟩ := ((Filter.eventually_all.2 hi).and self_mem_nhdsWithin).exists
  exact ⟨r, hr, fun z hz => ⟨_, hC, fun i => hall i hz⟩⟩
theorem isUnionOfBalls_iff_mem_familyOpens (hsep : SeparatesPoints f) (W : Set X) :
    IsUnionOfBalls (familyDistance f g hg) W ↔ W ∈ familyOpens f := by
  have hd := isMetricFunction_familyDistance hS f g hg hsep
  constructor
  · rintro ⟨𝒞, h𝒞, rfl⟩
    exact show IsOpen[familyTopology f] (⋃₀ 𝒞) from by
      let _ : TopologicalSpace X := familyTopology f
      refine isOpen_sUnion fun C hC => ?_
      obtain ⟨y, r, -, rfl⟩ := h𝒞 C hC
      exact familyTopology_isOpen_openBallOf hS f g hg y r
  · intro hW
    refine ⟨{C | C ⊆ W ∧ ∃ y, ∃ r : ℝ, 0 < r ∧ C = openBallOf (familyDistance f g hg) y r},
      fun C hC => hC.2, ?_⟩
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨r, hr, hsub⟩ := exists_openBallOf_subset hS f g hg W hW y hy
      refine ⟨_, ⟨hsub, y, r, hr, rfl⟩, ?_⟩
      show familyDistance f g hg y y < r
      rw [(hd.eq_zero_iff y y).2 rfl]
      exact hr
    · exact Set.sUnion_subset fun C hC => hC.1
end Metric
theorem topologyProperties_of_familySeriesTerms (hS : FamilySeries.FamilySeriesTerms) :
    TopologyProperties := by
  have hind : InducedEqRestrictedFamily := by
    intro X 𝔄 f E
    show TopologicalSpace.induced Subtype.val (familyTopology f) = _
    rw [familyTopology_eq_iInf_induced, familyTopology_eq_iInf_induced, induced_iInf]
    simp only [induced_compose]
    rfl
  refine ⟨?_, ?_, ⟨?_, ?_⟩, hind, ?_, ?_⟩
  · intro X 𝔄 f
    exact ⟨fun W => Iff.rfl, continuous_familyTopology_apply f, fun τ hτ W hW =>
      familyTopology_isOpen_of_forall_continuous f τ hτ W hW⟩
  · intro X 𝔄 Z f τZ φ
    rw [familyTopology_eq_iInf_induced, continuous_iInf_rng]
    simp only [continuous_induced_rng]
  · intro X 𝔄 f J hJ x y
    constructor
    · intro h b
      refine (tendstoAlong_real_iff _ _).1 fun W hW hy => ?_
      exact h (f b ⁻¹' W) (@Continuous.isOpen_preimage _ _ (familyTopology f) _ _ (continuous_familyTopology_apply f b) W hW) hy
    · intro h W hW hy
      have hW' : W ∈ familyOpens f := hW
      obtain ⟨𝒞, h𝒞, rfl⟩ := hW'
      obtain ⟨C, hC, hyC⟩ := hy
      obtain ⟨k, c, V, hV, rfl⟩ := h𝒞 C hC
      have hi : ∀ i, ∃ n : ℤ, ∀ j : J, n ≤ (((j : ℕ+) : ℕ) : ℤ) → f (c i) (x j) ∈ V i :=
        fun i => (tendstoAlong_real_iff _ _).2 (h (c i)) (V i) (hV i) (hyC i)
      choose n hn using hi
      obtain ⟨N, hN⟩ := Finite.exists_le n
      exact ⟨N, fun j hj => ⟨_, hC, fun i => hn i j ((hN i).trans hj)⟩⟩
  · intro J hJ u w
    exact tendstoAlong_real_iff u w
  · intro X 𝔄 f _ _ hsep g hg
    have hsepE : ∀ E : Set X, SeparatesPoints fun b (y : E) => f b y :=
      fun E y y' hne => hsep y y' fun h => hne (Subtype.ext h)
    have hopen : ∀ W : Set X, IsUnionOfBalls (familyDistance f g hg) W ↔
        W ∈ familyOpens f := isUnionOfBalls_iff_mem_familyOpens hS f g hg hsep
    have hd := isMetricFunction_familyDistance hS f g hg hsep
    refine ⟨hd, hopen, ⟨_, hd, fun W => (hopen W).symm⟩, fun E => ?_⟩
    have hdE : IsMetricFunction fun y y' : E => familyDistance f g hg y y' :=
      isMetricFunction_familyDistance hS (fun b (y : E) => f b y) g hg (hsepE E)
    have hopenE : ∀ W : Set E,
        IsUnionOfBalls (fun y y' : E => familyDistance f g hg y y') W ↔
          IsOpen[restrictTopology (familyTopology f) E] W := by
      intro W
      rw [hind X 𝔄 f E]
      exact isUnionOfBalls_iff_mem_familyOpens hS (fun b (y : E) => f b y) g hg (hsepE E) W
    exact ⟨hdE, hopenE, ⟨_, hdE, fun W => (hopenE W).symm⟩⟩
  · intro Z τZ u v hv hlim
    refine TendstoUniformly.continuous (F := v) (p := Filter.atTop) ?_
      (Filter.Eventually.of_forall hv).frequently
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    have hev : ∀ᶠ s in Filter.atTop, (⨆ z, ENNReal.ofReal |u z - v s z|) < ENNReal.ofReal ε :=
      hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
    filter_upwards [hev] with s hs z
    have hz : ENNReal.ofReal |u z - v s z| < ENNReal.ofReal ε :=
      lt_of_le_of_lt (le_iSup (fun z => ENNReal.ofReal |u z - v s z|) z) hs
    rw [Real.dist_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hz
end YangMills.Construction.FamilyTopology.Properties
