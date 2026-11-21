import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusCounting TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters
namespace FarBlocks
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem field_extendByZero_of_not_mem (s : ChartSetting R n) (N : Finset (TorusSite n))
    (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) {x : TorusSite (n * R.params.side)} (i : Fin 4)
    (hx : parentBlock R.params.side x ∉ N) : s.field (s.extendByZero N ζ) x i = s.field 0 x i := by
  classical
  unfold ChartSetting.field
  by_cases h : (x, i) ∈ s.free
  · have e : s.extendByZero N ζ ⟨(x, i), h⟩ = (0 : FreeCoords s.free) ⟨(x, i), h⟩ := by
      have hn : (⟨(x, i), h⟩ : s.free) ∉ s.freeNear N := by
        intro hm
        exact hx (Finset.mem_filter.mp hm).2
      simp only [ChartSetting.extendByZero]
      rw [dif_neg hn]
      rfl
    rw [dif_pos h, dif_pos h, e]
  · rw [dif_neg h, dif_neg h]
theorem lt_supDist_of_not_mem_blocksNear {L : ℕ} [NeZero L] {r : ℕ} {K : Finset (TorusSite (n * L))}
    {y k : TorusSite (n * L)} (hy : parentBlock L y ∉ blocksNear L r K) (hk : k ∈ K) :
    5 * r < _root_.YangMills.Construction.TorusFields.supDist y k := by
  classical
  by_contra h
  push_neg at h
  apply hy
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simp [sitesInBlocks]
  · exact (mem_thickening _ _ _).2 ⟨k, hk, h⟩
theorem lt_supDist_of_mem_chainComponents_of_ne {M : ℕ} [NeZero M] {r : ℕ}
    {Y X X' : Finset (TorusSite M)} (hX : X ∈ chainComponents r Y)
    (hX' : X' ∈ chainComponents r Y) (hne : X ≠ X') {z z' : TorusSite M} (hz : z ∈ X) (hz' : z' ∈ X') :
    r < _root_.YangMills.Construction.TorusFields.supDist z z' := by
  classical
  by_contra h
  push_neg at h
  exact hne (eq_of_chainConnected_of_mem_chainComponents hX hX' hz hz'
    (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX hz)
      (subset_of_mem_chainComponents hX' hz') h))
theorem le_supDist_support_of_near (s : ChartSetting R n) (c : SettingCore R n)
    {𝒦 : Finset (Finset (TorusSite (n * R.params.side)))}
    (h𝒦 : 𝒦 ⊆ s.storedComponents c) (hLr : R.params.side ≤ R.range) (hr : 4 ≤ R.range)
    {y w z : TorusSite (n * R.params.side)}
    (hy : parentBlock R.params.side y ∉ blocksNear R.params.side R.range (𝒦.biUnion id))
    (hw : parentBlock R.params.side w ∈ blocksNear R.params.side R.range (𝒦.biUnion id))
    (hd : _root_.YangMills.Construction.TorusFields.supDist y w < R.range / 64 + 3)
    (hz : z ∈ s.support) : R.range ≤ _root_.YangMills.Construction.TorusFields.supDist y z := by
  classical
  have hzs : z ∈ c.badBonds.image Prod.fst ∪ s.support ∪ sitesInBlocks R.params.side c.core :=
    Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * R.range) hzs
  by_cases hXK : X ∈ 𝒦
  · have := lt_supDist_of_not_mem_blocksNear hy
      (Finset.mem_biUnion.mpr ⟨X, hXK, hzX⟩ : z ∈ 𝒦.biUnion id)
    omega
  · obtain ⟨w', hw'⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw'
    obtain ⟨k, hk, hkd⟩ := (mem_thickening _ _ _).1 hw2
    obtain ⟨X', hX'K, hkX'⟩ := Finset.mem_biUnion.mp hk
    have hbl : parentBlock R.params.side w' = parentBlock R.params.side w := by
      simpa [sitesInBlocks] using hw1
    have hww : _root_.YangMills.Construction.TorusFields.supDist w' w ≤ R.params.side := _root_.YangMills.Construction.TorusCounting.supDist_le_of_parentBlock_eq hbl
    have hne : X ≠ X' := fun e => hXK (e ▸ hX'K)
    have hfar : 10 * R.range < _root_.YangMills.Construction.TorusFields.supDist z k :=
      lt_supDist_of_mem_chainComponents_of_ne hX (h𝒦 hX'K) hne hzX hkX'
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z y k
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y w k
    have t3 := _root_.YangMills.Construction.TorusFields.supDist_triangle w w' k
    have e1 : _root_.YangMills.Construction.TorusFields.supDist z y = _root_.YangMills.Construction.TorusFields.supDist y z := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    have e2 : _root_.YangMills.Construction.TorusFields.supDist w w' = _root_.YangMills.Construction.TorusFields.supDist w' w := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
    omega
section BlockDensities
variable (s : ChartSetting R n) (c : SettingCore R n)
theorem inBalls_zero (hρ : 0 ≤ R.ballRadius) : s.InBalls 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GainMean.inBalls_zero <;> assumption
theorem card_sitesInBlocks_le (N : Finset (TorusSite n)) :
    (sitesInBlocks R.params.side N).card ≤ N.card * (2 * R.params.side + 1) ^ 4 := by
  classical
  have hsub : sitesInBlocks R.params.side N ⊆ N.biUnion fun Y => sitesInBlocks R.params.side {Y} := by
    intro x hx
    have hb : parentBlock R.params.side x ∈ N := by simpa [sitesInBlocks] using hx
    exact Finset.mem_biUnion.mpr ⟨_, hb, by simp [sitesInBlocks]⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul _ _ _ fun Y _ => card_sitesInBlocks_singleton_le Y)
set_option maxHeartbeats 1600000 in
theorem sum_abs_blockDensity_sub_le
    (hhull : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hs : s.IsAdmissible) (hρ : 0 ≤ R.ballRadius)
    (hE : 0 ≤ R.params.E)
    (h22 : ∀ (W : TorusField (n * R.params.side)) (y : TorusSite (n * R.params.side)),
      IsHullState R.params R.range W s.support →
      (∀ X ∈ chainComponents R.range s.support, R.clusterFactor (n * R.params.side) W s.support s.labelling X ≠ 0) →
      (∀ z ∈ s.support, (R.range : ℝ) / 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y z) →
        |R.siteDensity (n * R.params.side) y W s.support s.labelling| ≤ 2 * R.params.E)
    {𝒦 : Finset (Finset (TorusSite (n * R.params.side)))} (h𝒦 : 𝒦 ⊆ s.storedComponents c)
    (hLr : R.params.side ≤ R.range)
    (hr : 4 ≤ R.range) {N : Finset (TorusSite n)}
    (hN : N = blocksNear R.params.side R.range (𝒦.biUnion id))
    (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) {η : FreeCoords s.free} (hηd : η = s.extendByZero N ζ)
    (hζ : s.InBalls η) {f : ℝ} (hfdef : f = R.params.decayRate) (hf : 0 < f) :
    ∑ Y ∈ Finset.univ \ N, |s.blockDensity (s.field η) Y - s.blockDensity (s.field 0) Y| ≤
      ((N.card * (2 * R.params.side + 1) ^ 4 : ℕ) : ℝ) *
        (4 * R.params.E * ((2 * (R.range / 64 + 3) + 1) ^ 4 : ℕ) +
          Real.exp (2 * f) * expSumOnInt (f / 4) ^ 4) := by
  classical
  let LN := sitesInBlocks R.params.side N
  have hLN : LN = sitesInBlocks R.params.side N := rfl
  have h0 := inBalls_zero s hρ
  let g : TorusSite (n * R.params.side) → ℝ := fun y =>
    |R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling -
      R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling|
  have h1 : ∀ Y, |s.blockDensity (s.field η) Y - s.blockDensity (s.field 0) Y| ≤
      ∑ y ∈ sitesInBlocks R.params.side {Y}, g y := by
    intro Y
    unfold ChartSetting.blockDensity
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  let D₀ := R.range / 64 + 3
  let G : TorusSite (n * R.params.side) → ℝ := fun y =>
    (if ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀ then 4 * R.params.E else 0) +
      Real.exp (2 * f) * ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w))
  have hGnn : ∀ y, 0 ≤ G y := by
    intro y
    have h2 : 0 ≤ ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)) :=
      Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    have h3 : (0 : ℝ) ≤ if ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀ then 4 * R.params.E else 0 := by
      split_ifs
      · positivity
      · exact le_rfl
    have := Real.exp_pos (2 * f)
    positivity
  have hG : ∀ y, parentBlock R.params.side y ∉ N → g y ≤ G y := by
    intro y hy
    by_cases hnear : ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀
    · obtain ⟨w, hw, hd⟩ := hnear
      have hwN : parentBlock R.params.side w ∈ N := by simpa [hLN, sitesInBlocks] using hw
      have hz : ∀ z ∈ s.support, (R.range : ℝ) / 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y z := by
        intro z hz
        have h3 : R.range ≤ _root_.YangMills.Construction.TorusFields.supDist y z :=
          le_supDist_support_of_near s c h𝒦 hLr hr (hN ▸ hy) (hN ▸ hwN) hd hz
        have h4 : (R.range : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist y z := by exact_mod_cast h3
        have h5 : (0 : ℝ) ≤ R.range := Nat.cast_nonneg _
        linarith
      have a1 := h22 (s.field η) y (hs.isHull η hζ) (hs.factor_ne_zero η hζ) hz
      have a2 := h22 (s.field 0) y (hs.isHull 0 h0) (hs.factor_ne_zero 0 h0) hz
      have h6 : g y ≤ 4 * R.params.E := by
        have := abs_sub (R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling)
          (R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling)
        show |_ - _| ≤ _
        linarith
      have h7 : 0 ≤ Real.exp (2 * f) * ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)) :=
        mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
      have h8 : G y = 4 * R.params.E + Real.exp (2 * f) * ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)) := by
        show (if ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀ then 4 * R.params.E else 0) + _ = _
        rw [if_pos ⟨w, hw, hd⟩]
      linarith
    · push_neg at hnear
      by_cases hne : LN.Nonempty
      · obtain ⟨w₀, hw₀, hmin⟩ := Finset.exists_min_image LN (fun w => _root_.YangMills.Construction.TorusFields.supDist y w) hne
        have hD : D₀ ≤ _root_.YangMills.Construction.TorusFields.supDist y w₀ := hnear w₀ hw₀
        set D := _root_.YangMills.Construction.TorusFields.supDist y w₀ with hDdef
        have hhalf : 2 * D ≤ n * R.params.side := by
          have hb : ∀ i, ((y i - w₀ i).valMinAbs).natAbs ≤ (n * R.params.side) / 2 := fun i =>
            ZMod.natAbs_valMinAbs_le _
          have := (_root_.YangMills.Construction.TorusFields.supDist_le_iff y w₀ _).2 hb
          omega
        have hm64 : (R.range : ℝ) / 64 ≤ ((D - 2 : ℕ) : ℝ) := by
          have h2 : R.range / 64 + 1 ≤ D - 2 := by
            have : D₀ = R.range / 64 + 3 := rfl
            omega
          have h3 : ((R.range / 64 + 1 : ℕ) : ℝ) ≤ ((D - 2 : ℕ) : ℝ) := by exact_mod_cast h2
          have h4 : (R.range : ℝ) / 64 ≤ ((R.range / 64 + 1 : ℕ) : ℝ) := by
            have h5 : R.range ≤ 64 * (R.range / 64 + 1) := by omega
            have h6 : (R.range : ℝ) ≤ 64 * ((R.range / 64 + 1 : ℕ) : ℝ) := by exact_mod_cast h5
            linarith
          linarith
        have hfields : FieldsAgreeNear (s.field η) (s.field 0) y y (D - 2) := by
          intro b hb
          have hnot : parentBlock R.params.side (bondFrom y b).1 ∉ N := by
            intro hm
            have hx : (bondFrom y b).1 ∈ LN := by simpa [hLN, sitesInBlocks] using hm
            have h5 := hmin _ hx
            have h6 : _root_.YangMills.Construction.TorusFields.supDist y (bondFrom y b).1 ≤ D - 2 :=
              _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y b.1 (D - 2) fun i => by
                have := hb.1 i
                rw [abs_le] at this
                omega
            have : D₀ = R.range / 64 + 3 := rfl
            omega
          rw [hηd]
          exact field_extendByZero_of_not_mem s N ζ _ hnot
        have hst : StatesAgreeNear R.params (s.field η) (s.field 0) s.support s.support s.labelling
            s.labelling y y (D - 2) := by
          have hD3 : 3 ≤ D := by
            have : D₀ = R.range / 64 + 3 := rfl
            omega
          refine ⟨by omega, by omega, hfields, fun _ _ => Iff.rfl, ?_, fun _ _ => ?_⟩
          · intro h _ hz hz' _
            rfl
          · simp
        have hb := hhull.forget (n * R.params.side) (n * R.params.side) hside hside (s.field η) (s.field 0)
          s.support s.support s.labelling s.labelling y y (D - 2) (hs.isHull η hζ) (hs.isHull 0 h0)
          (hs.factor_ne_zero η hζ) (hs.factor_ne_zero 0 h0) hm64 hst
        rw [← hfdef] at hb
        have h7 : Real.exp (-f * ((D - 2 : ℕ) : ℝ)) ≤
            Real.exp (2 * f) * Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w₀)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hD3 : 2 ≤ D := by
            have : D₀ = R.range / 64 + 3 := rfl
            omega
          rw [Nat.cast_sub hD3]
          push_cast
          nlinarith
        have h8 : Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w₀)) ≤ ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)) :=
          Finset.single_le_sum (f := fun w => Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)))
            (fun _ _ => (Real.exp_pos _).le) hw₀
        have h9 : (0 : ℝ) ≤ if ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀ then 4 * R.params.E else 0 := by
          split_ifs
          · positivity
          · exact le_rfl
        have h10 := mul_le_mul_of_nonneg_left h8 (Real.exp_pos (2 * f)).le
        show |_ - _| ≤ (if ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀ then 4 * R.params.E else 0) + _
        linarith
      · have hall : ∀ (x : TorusSite (n * R.params.side)) (i : Fin 4), s.field η x i = s.field 0 x i := by
          intro x i
          rw [hηd]
          refine field_extendByZero_of_not_mem s N ζ i fun hm => hne ⟨x, ?_⟩
          simpa [hLN, sitesInBlocks] using hm
        have hfeq : s.field η = s.field 0 := by
          funext x i
          exact hall x i
        have : g y = 0 := by
          show |_ - _| = 0
          rw [hfeq, sub_self, abs_zero]
        rw [this]
        exact hGnn y
  have hsum : ∑ Y ∈ Finset.univ \ N, ∑ y ∈ sitesInBlocks R.params.side {Y}, g y =
      ∑ y ∈ Finset.univ.filter (fun y => parentBlock R.params.side y ∉ N), g y := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun y => parentBlock R.params.side y ∉ N)
      (t := Finset.univ \ N) (g := fun y => parentBlock R.params.side y)
      (fun y hy => by simpa using (Finset.mem_filter.mp hy).2)]
    refine Finset.sum_congr rfl fun Y hY => Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    have hYN : Y ∉ N := by simpa using hY
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact ⟨by rw [h]; exact hYN, h⟩
    · exact fun h => h.2
  have hnear_count : ((Finset.univ.filter fun y : TorusSite (n * R.params.side) =>
      ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀).card : ℝ) ≤ (LN.card * (2 * D₀ + 1) ^ 4 : ℕ) := by
    have : (Finset.univ.filter fun y : TorusSite (n * R.params.side) => ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀) ⊆
        thickening D₀ LN := by
      intro y hy
      obtain ⟨w, hw, hd⟩ := (Finset.mem_filter.mp hy).2
      exact (mem_thickening _ _ _).2 ⟨w, hw, hd.le⟩
    exact_mod_cast (Finset.card_le_card this).trans (card_thickening_le D₀ LN)
  have hfar_sum : ∑ y : TorusSite (n * R.params.side), ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)) ≤
      (LN.card : ℝ) * expSumOnInt (f / 4) ^ 4 := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _w ∈ LN, expSumOnInt (f / 4) ^ 4 :=
          Finset.sum_le_sum fun w _ => sum_exp_neg_supDist_le hf w
      _ = _ := by simp
  have hGsum : ∑ y, G y ≤ (LN.card : ℝ) *
      (4 * R.params.E * ((2 * D₀ + 1) ^ 4 : ℕ) + Real.exp (2 * f) * expSumOnInt (f / 4) ^ 4) := by
    have e1 : ∑ y, G y = 4 * R.params.E *
        ((Finset.univ.filter fun y : TorusSite (n * R.params.side) => ∃ w ∈ LN, _root_.YangMills.Construction.TorusFields.supDist y w < D₀).card : ℝ) +
        Real.exp (2 * f) * ∑ y : TorusSite (n * R.params.side), ∑ w ∈ LN, Real.exp (-(f * _root_.YangMills.Construction.TorusFields.supDist y w)) := by
      simp only [G]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
        add_zero, nsmul_eq_mul]
      ring
    rw [e1]
    have hE4 : 0 ≤ 4 * R.params.E := by positivity
    have e2 := mul_le_mul_of_nonneg_left hnear_count hE4
    have e3 := mul_le_mul_of_nonneg_left hfar_sum (Real.exp_pos (2 * f)).le
    push_cast at e2 ⊢
    nlinarith
  have hcard : (LN.card : ℝ) ≤ ((N.card * (2 * R.params.side + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast card_sitesInBlocks_le N
  have hbr : 0 ≤ 4 * R.params.E * ((2 * D₀ + 1) ^ 4 : ℕ) + Real.exp (2 * f) * expSumOnInt (f / 4) ^ 4 := by
    have := expSumOnInt_nonneg (f / 4)
    have := Real.exp_pos (2 * f)
    positivity
  calc ∑ Y ∈ Finset.univ \ N, |s.blockDensity (s.field η) Y - s.blockDensity (s.field 0) Y|
      ≤ ∑ Y ∈ Finset.univ \ N, ∑ y ∈ sitesInBlocks R.params.side {Y}, g y :=
        Finset.sum_le_sum fun Y _ => h1 Y
    _ = ∑ y ∈ Finset.univ.filter (fun y => parentBlock R.params.side y ∉ N), g y := hsum
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y => parentBlock R.params.side y ∉ N), G y :=
        Finset.sum_le_sum fun y hy => hG y (Finset.mem_filter.mp hy).2
    _ ≤ ∑ y, G y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun y _ _ => hGnn y
    _ ≤ _ := hGsum
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hbr
end BlockDensities
section LogJacobians
variable (s : ChartSetting R n)
theorem toTorusSite_torusSiteInFrame (Y : TorusSite n) :
    (toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y :
      (stepBlockFrame R.params.side n).Cell) : TorusSite n) = Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.toTorusSite_torusSiteInFrame <;> assumption
theorem parentBlock_cellCentreOnTorus (y : (stepBlockFrame R.params.side n).Cell) :
    parentBlock R.params.side (cellCentreOnTorus R.params.side y) = toTorusSite n y := by
  have h := TorusContours.parentBlock_siteAtOffset (L := R.params.side) (n := n) y
    (TorusContours.zero_mem_centredCube (Nat.pos_of_ne_zero (NeZero.ne R.params.side)))
  have e : (siteAtOffset y 0 : (stepBlockFrame R.params.side n).Site 0) = cellCentre 0 y := by
    rw [siteAtOffset, TorusContours.siteOfCoords_zero, add_zero]
    rfl
  rw [e] at h
  exact h
theorem fieldsAgreeNear_of_far (N : Finset (TorusSite n)) (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3))
    (y : (stepBlockFrame R.params.side n).Cell) (Y : TorusSite n) (hd : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite n y) Y ≤ 1)
    (hY : ∀ Y' ∈ N, 8 < _root_.YangMills.Construction.TorusFields.supDist Y Y') (m : ℕ) (hm : m ≤ 3 * R.params.side) :
    FieldsAgreeNear (s.field (s.extendByZero N ζ)) (s.field 0) (cellCentreOnTorus R.params.side y)
      (cellCentreOnTorus R.params.side y) m := by
  intro b hb
  refine field_extendByZero_of_not_mem s N ζ _ fun hm' => ?_
  have h1 : _root_.YangMills.Construction.TorusFields.supDist (cellCentreOnTorus R.params.side y)
      (bondFrom (cellCentreOnTorus R.params.side y) b).1 ≤ 3 * R.params.side :=
    (_root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ b.1 m fun i => by
      have := hb.1 i
      rw [abs_le] at this
      omega).trans hm
  have h2 := _root_.YangMills.Construction.TorusCounting.supDist_parentBlock_le (L := R.params.side) (cellCentreOnTorus R.params.side y)
    (bondFrom (cellCentreOnTorus R.params.side y) b).1
  rw [parentBlock_cellCentreOnTorus] at h2
  have h3 : _root_.YangMills.Construction.TorusFields.supDist (cellCentreOnTorus R.params.side y)
      (bondFrom (cellCentreOnTorus R.params.side y) b).1 / R.params.side ≤ 3 := by
    have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    calc _ ≤ (3 * R.params.side) / R.params.side := Nat.div_le_div_right h1
      _ = 3 := Nat.mul_div_cancel _ hL
  have h4 := hY _ hm'
  have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y (toTorusSite n y)
    (parentBlock R.params.side (bondFrom (cellCentreOnTorus R.params.side y) b).1)
  have h6 : _root_.YangMills.Construction.TorusFields.supDist Y (toTorusSite n y) = _root_.YangMills.Construction.TorusFields.supDist (toTorusSite n y) Y := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
  omega
theorem meanNorm_extendByZero_of_far (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hLgt : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (hn : 16 ≤ n) (hs : s.IsAdmissible)
    (N : Finset (TorusSite n)) (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) (Y : TorusSite n)
    (hY : ∀ Y' ∈ N, 8 < _root_.YangMills.Construction.TorusFields.supDist Y Y') (i : Fin 4) :
    meanNorm R.params (s.field (s.extendByZero N ζ)) s.bases (Y, i) =
      meanNorm R.params (s.field 0) s.bases (Y, i) := by
  set W := s.field (s.extendByZero N ζ) with hW
  set W' := s.field (0 : FreeCoords s.free) with hW'
  let y : (stepBlockFrame R.params.side n).Cell := torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y
  have hyY : (toTorusSite n y : TorusSite n) = Y := toTorusSite_torusSiteInFrame Y
  have hy1 : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite n y) Y ≤ 1 := by rw [hyY, _root_.YangMills.Construction.TorusFields.supDist_self]; omega
  let e : (stepBlockFrame R.params.side n).Cell := BlockAverages.unitStep 1 i
  have hsum : (toTorusSite n (y + e) : TorusSite n) = Y + TorusFields.unitStep n i := by
    have h1 := TorusContours.toTorusSite_add (F := stepBlockFrame R.params.side n) (j := 1) (m := n)
      (fun k => TorusContours.stepBlockFrame_period_one k) y e
    have h2 := TorusContours.toTorusSite_unitStep (F := stepBlockFrame R.params.side n) (j := 1) (m := n)
      (fun k => TorusContours.stepBlockFrame_period_one k) i
    exact h1.trans (congrArg₂ (· + ·) hyY h2)
  have hy2 : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite n (y + e)) Y ≤ 1 := by
    rw [hsum, _root_.YangMills.Construction.TorusFields.supDist_comm]
    exact _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le Y i
  have hL1 : 1 ≤ (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  obtain ⟨z₀, hz₀, hb₀⟩ := TorusContours.exists_centredCube_of_isBaseChoice hL1 hs.isBaseChoice y
  obtain ⟨z₁, hz₁, hb₁⟩ := TorusContours.exists_centredCube_of_isBaseChoice hL1 hs.isBaseChoice (y + e)
  have l1 := (hloc R.params hfit hLgt n n hn hn W W' y y).2.1
    (fieldsAgreeNear_of_far s N ζ y Y hy1 hY _ le_rfl)
  have l2 := (hloc R.params hfit hLgt n n hn hn W W' (y + e) (y + e)).2.1
    (fieldsAgreeNear_of_far s N ζ _ Y hy2 hY _ le_rfl)
  have l3 := (hloc R.params hfit hLgt n n hn hn W W' y y).2.2.2 i 0 (fun _ _ => 1) (fun _ _ => 1)
    s.bases s.bases z₀ z₁ hz₀ hz₁ hb₀ hb₀ hb₁ hb₁
    (fieldsAgreeNear_of_far s N ζ y Y hy1 hY _ (by omega)) l1 l2
  exact congrArg norm l3.1
theorem logJacobian_extendByZero_of_far (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hLgt : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (hn : 16 ≤ n) (hs : s.IsAdmissible)
    (N : Finset (TorusSite n)) (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) (Y : TorusSite n)
    (hY : ∀ Y' ∈ N, 8 < _root_.YangMills.Construction.TorusFields.supDist Y Y') :
    s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y = s.logJacobian (s.field 0) 0 Y := by
  classical
  have hYN : Y ∉ N := fun h => by
    have := hY Y h
    rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
    omega
  have h1 : ∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling *
        meanNorm R.params (s.field (s.extendByZero N ζ)) s.bases (Y, i)) =
      ∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling *
        meanNorm R.params (s.field 0) s.bases (Y, i)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [meanNorm_extendByZero_of_far s hloc hfit hLgt hn hs N ζ Y hY i]
  have h2 : (∑ b : s.free, if bondBlock (R := R) b.1 = Y then
        Real.log (haarLogDensity (toCoords (s.frame b.1) + s.extendByZero N ζ b)) else 0) =
      ∑ b : s.free, if bondBlock (R := R) b.1 = Y then
        Real.log (haarLogDensity (toCoords (s.frame b.1) + (0 : FreeCoords s.free) b)) else 0 := by
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : bondBlock (R := R) b.1 = Y
    · rw [if_pos h, if_pos h]
      have hn' : b ∉ s.freeNear N := fun hm => hYN (h ▸ (Finset.mem_filter.mp hm).2)
      have e : s.extendByZero N ζ b = (0 : FreeCoords s.free) b := by
        simp only [ChartSetting.extendByZero]
        rw [dif_neg hn']
        rfl
      rw [e]
    · rw [if_neg h, if_neg h]
  exact congrArg₂ (· + ·) h1 h2
theorem sum_abs_logJacobian_sub_le (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hLgt : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (hn : 16 ≤ n) (hs : s.IsAdmissible)
    (N : Finset (TorusSite n)) (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) (C : ℝ) (hC0 : 0 ≤ C)
    (h1 : ∀ Y, |s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y| ≤ C)
    (h2 : ∀ Y, |s.logJacobian (s.field 0) 0 Y| ≤ C) :
    ∑ Y ∈ Finset.univ \ N, |s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y -
        s.logJacobian (s.field 0) 0 Y| ≤
      ((N.card * (2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * C) := by
  classical
  have hb : ∀ Y, |s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y -
      s.logJacobian (s.field 0) 0 Y| ≤ if Y ∈ thickening 8 N then 2 * C else 0 := by
    intro Y
    by_cases hY : Y ∈ thickening 8 N
    · rw [if_pos hY]
      have := abs_sub (s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y)
        (s.logJacobian (s.field 0) 0 Y)
      linarith [h1 Y, h2 Y]
    · rw [if_neg hY]
      have hfar : ∀ Y' ∈ N, 8 < _root_.YangMills.Construction.TorusFields.supDist Y Y' := fun Y' hY' => by
        by_contra h
        push_neg at h
        exact hY ((mem_thickening _ _ _).2 ⟨Y', hY', h⟩)
      rw [logJacobian_extendByZero_of_far s hloc hfit hLgt hn hs N ζ Y hfar, sub_self, abs_zero]
  calc _ ≤ ∑ Y ∈ Finset.univ \ N, (if Y ∈ thickening 8 N then 2 * C else 0) :=
        Finset.sum_le_sum fun Y _ => hb Y
    _ ≤ ∑ Y : TorusSite n, (if Y ∈ thickening 8 N then 2 * C else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun Y _ _ => by
          split_ifs
          · positivity
          · exact le_rfl
    _ = ((thickening 8 N).card : ℝ) * (2 * C) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_thickening_le 8 N
end LogJacobians
end FarBlocks
namespace StepSettings
open FarBlocks in
set_option maxHeartbeats 1600000 in
theorem farBlockDensityVariationBound_holds (h3 : ExpansionBasicBounds) (hloc : BondKernelLocality)
    (hj : ClusterExpansionOfAStep.LogJacobianLeLog) : farBlockDensityVariationBound := by
  classical
  intro T hT
  obtain ⟨Cj, yj, hCj, hj⟩ := hj T hT
  have hrt := hT.rt_pos
  set f : ℝ := T.rt / 2 ^ 12 with hf
  have hf0 : 0 < f := by positivity
  set M : ℝ := expSumOnInt (f / 4) ^ 4 with hM
  have hE1 : 1 ≤ T.E := by
    have := hT.B_ge
    unfold ParameterAssignment.E
    linarith
  set C₁ : ℝ := (2 * (T.side : ℝ) + 1) ^ 4 * (4 * T.E * 7 ^ 4 + Real.exp (2 * f) * M) with hC₁
  set r₀ : ℕ := 4 * T.n₀ + 2 ^ 16 + T.side + 64 with hr₀
  refine ⟨C₁ + ((2 * 8 + 1) ^ 4 : ℕ) * (2 * Cj) + 1,
    max yj (max T.floorMin (max (Real.exp 1) ((r₀ : ℝ) ^ 100))),
    by positivity, fun y hy R hR n _ hn s c hs hc 𝒦 h𝒦 ζ hζ => ?_⟩
  have hy1 : yj ≤ y := (le_max_left _ _).trans hy
  have hy2 : T.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : Real.exp 1 ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy4 : (r₀ : ℝ) ^ 100 ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hx1 : 1 ≤ R.coupling := ((Real.one_le_exp (by norm_num)).trans hy3).trans hR.le_coupling
  have hlog : 1 ≤ Real.log R.coupling := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hy3.trans hR.le_coupling
  have hr : r₀ ≤ R.range := le_clusterRange_of_pow_le (hy4.trans hR.le_coupling)
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hy2
  have hEl : R.params.E = T.E := by rw [hR.params_eq]; rfl
  have hLl : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hnl : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hJl : R.params.baseDepth = T.baseDepth := by rw [hR.params_eq]; rfl
  have hfl : R.params.decayRate = f := by
    unfold TorusLumps.StepParameters.decayRate
    rw [hR.params_eq]
    rfl
  have hρ : 0 ≤ R.ballRadius := by
    unfold StepSetup.ballRadius
    have := hfit.σ_pos
    positivity
  obtain ⟨⟨hcold, hhull⟩, -⟩ := hR.isStep
  have hside : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ (hnl ▸ hn)
  have hfacts := h3 R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity hfit (hEl ▸ hE1) (by linarith)
    (by
      have : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range := by
        rw [hnl]
        omega
      exact this) hcold hhull
  have h22 : ∀ (W : TorusField (n * R.params.side)) (y' : TorusSite (n * R.params.side)),
      IsHullState R.params R.range W s.support →
      (∀ X ∈ chainComponents R.range s.support,
        R.clusterFactor (n * R.params.side) W s.support s.labelling X ≠ 0) →
      (∀ z ∈ s.support, (R.range : ℝ) / 4 ≤ _root_.YangMills.Construction.TorusFields.supDist y' z) →
        |R.siteDensity (n * R.params.side) y' W s.support s.labelling| ≤ 2 * R.params.E :=
    fun W y' h1 h2 h4 => hfacts.2.1 (n * R.params.side) hside W s.support s.labelling y' h1 h2 h4
  have hLr : R.params.side ≤ R.range := by
    rw [hLl]
    omega
  have hr4 : 4 ≤ R.range := by omega
  have hφ := sum_abs_blockDensity_sub_le s c hhull hside hs hρ (by rw [hEl]; linarith) h22 h𝒦 hLr hr4 rfl
    ζ rfl hζ hfl.symm hf0
  generalize hN : blocksNear R.params.side R.range (𝒦.biUnion id) = N at ζ hζ hφ ⊢
  have h0 := inBalls_zero s hρ
  have hJ1 : ∀ Y, |s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y| ≤
      Cj * Real.log R.coupling :=
    fun Y => hj y hy1 R hR n hn s hs _ hζ Y
  have hJ2 : ∀ Y, |s.logJacobian (s.field 0) 0 Y| ≤ Cj * Real.log R.coupling :=
    fun Y => hj y hy1 R hR n hn s hs _ h0 Y
  have hn16 : 16 ≤ n := by
    have := hT.n₀_ge
    omega
  have hLgt : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side := by
    rw [hJl, hLl]
    exact hT.L_gt
  have hjs := sum_abs_logJacobian_sub_le s hloc hfit hLgt hn16 hs N ζ (Cj * Real.log R.coupling)
    (by positivity) hJ1 hJ2
  have hrR : (1 : ℝ) ≤ R.range := by
    have : 1 ≤ R.range := by omega
    exact_mod_cast this
  have hr4R : (1 : ℝ) ≤ (R.range : ℝ) ^ 4 := one_le_pow₀ hrR
  have hD : ((2 * (R.range / 64 + 3) + 1 : ℕ) : ℝ) ≤ 7 * R.range := by
    have : 2 * (R.range / 64 + 3) + 1 ≤ 7 * R.range := by omega
    exact_mod_cast this
  set rl : ℝ := (R.range : ℝ) ^ 4 * Real.log R.coupling with hrl
  have hrl1 : 1 ≤ rl := by
    rw [hrl]
    nlinarith
  have e1 : ∑ Y ∈ Finset.univ \ N,
      |s.blockDensity (s.field (s.extendByZero N ζ)) Y - s.blockDensity (s.field 0) Y| ≤
      (N.card : ℝ) * (C₁ * rl) := by
    refine hφ.trans ?_
    rw [hEl]
    have hLr' : ((R.params.side : ℕ) : ℝ) = (T.side : ℝ) := by exact_mod_cast hLl
    push_cast
    rw [hLr']
    have hb1 : ((2 * ((R.range / 64 : ℕ) + 3 : ℝ) + 1) ^ 4) ≤ 7 ^ 4 * (R.range : ℝ) ^ 4 := by
      have h5 : (2 * ((R.range / 64 : ℕ) + 3 : ℝ) + 1) ≤ 7 * R.range := by
        have := hD
        push_cast at this
        exact this
      calc _ ≤ (7 * (R.range : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h5 4
        _ = _ := by ring
    have hb2 : 4 * T.E * (2 * ((R.range / 64 : ℕ) + 3 : ℝ) + 1) ^ 4 + Real.exp (2 * f) * M ≤
        (4 * T.E * 7 ^ 4 + Real.exp (2 * f) * M) * rl := by
      have h6 : (R.range : ℝ) ^ 4 ≤ rl := by
        rw [hrl]
        nlinarith
      have h7 : 0 ≤ Real.exp (2 * f) * M := by positivity
      have h8 : 4 * T.E * (2 * ((R.range / 64 : ℕ) + 3 : ℝ) + 1) ^ 4 ≤ 4 * T.E * (7 ^ 4 * rl) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hb1.trans (mul_le_mul_of_nonneg_left h6 (by positivity))
      have h9 : Real.exp (2 * f) * M ≤ Real.exp (2 * f) * M * rl := le_mul_of_one_le_right h7 hrl1
      have h10 : (4 * T.E * 7 ^ 4 + Real.exp (2 * f) * M) * rl =
          4 * T.E * (7 ^ 4 * rl) + Real.exp (2 * f) * M * rl := by ring
      rw [h10]
      exact add_le_add h8 h9
    calc _ ≤ (N.card : ℝ) * (2 * (T.side : ℝ) + 1) ^ 4 *
          ((4 * T.E * 7 ^ 4 + Real.exp (2 * f) * M) * rl) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = _ := by rw [hC₁]; ring
  have e2 : ((N.card * (2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * (Cj * Real.log R.coupling)) ≤
      (N.card : ℝ) * ((((2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * Cj) * rl) := by
    have hlr : Real.log R.coupling ≤ rl := by
      rw [hrl]
      nlinarith
    have h11 : Cj * Real.log R.coupling ≤ Cj * rl := mul_le_mul_of_nonneg_left hlr hCj.le
    have hc0 : (0 : ℝ) ≤ ((N.card * (2 * 8 + 1) ^ 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h12 := mul_le_mul_of_nonneg_left
      (show 2 * (Cj * Real.log R.coupling) ≤ 2 * (Cj * rl) by linarith only [h11]) hc0
    have e : ((N.card * (2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * (Cj * rl)) =
        (N.card : ℝ) * ((((2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * Cj) * rl) := by
      rw [Nat.cast_mul]
      ring
    linarith only [h12, e]
  have hfin : (N.card : ℝ) * (C₁ * rl) + (N.card : ℝ) * ((((2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * Cj) * rl) ≤
      (C₁ + ((2 * 8 + 1) ^ 4 : ℕ) * (2 * Cj) + 1) * (R.range : ℝ) ^ 4 * Real.log R.coupling *
        (N.card : ℝ) := by
    have e : (C₁ + ((2 * 8 + 1) ^ 4 : ℕ) * (2 * Cj) + 1) * (R.range : ℝ) ^ 4 * Real.log R.coupling *
        (N.card : ℝ) =
        (N.card : ℝ) * (C₁ * rl) + (N.card : ℝ) * ((((2 * 8 + 1) ^ 4 : ℕ) : ℝ) * (2 * Cj) * rl) +
          (N.card : ℝ) * rl := by
      rw [hrl]
      ring
    rw [e]
    have h13 : 0 ≤ (N.card : ℝ) * rl := by positivity
    linarith only [h13]
  linarith only [e1, e2, hjs, hfin]
end StepSettings
end YangMills.Construction
end
