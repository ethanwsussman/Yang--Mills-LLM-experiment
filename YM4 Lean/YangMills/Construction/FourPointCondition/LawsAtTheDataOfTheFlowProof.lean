import YangMills.Construction.FourPointCondition.ConnectedLawOfAPair
import YangMills.Construction.FourPointCondition.LawsAtTheDataOfTheFlow
import YangMills.Construction.FourPointCondition.LawsWithNoDatum
import YangMills.Construction.Lattice.ConnectedFunctionsAndTheCentredIdentityAtArbitraryFunctions
import YangMills.Construction.Lattice.SumsNormsAndKernelsOfTestFunctionsAreFormed
import YangMills.Construction.ParameterData.RatioOfBetaToTheLogarithmOfTheCutoffProof
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import YangMills.Construction.ResponseInTheExpansion.ComparisonFromBoundsOfAMoveProof
import YangMills.Construction.ResponseInTheExpansion.NumbersOfTheChainAreOne
import YangMills.Construction.ResponseInTheExpansion.TheFreeKernelAtAPairIsPositive
import YangMills.Construction.Towers.CrossingAverageOfATowerIsAMapOfPeriodicFunctionsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set Topology TestFunctions PeriodicLattice TorusMetric ResponseInTheExpansion WeightedResponses TorusLumps RenormalizationStepParameters
open scoped ENNReal
namespace FourPointCondition
namespace FlowDataLaws
private theorem monotone_majorant_near_zero (u : ℝ → ℝ) (hu : Tendsto u (𝓝[>] 0) (𝓝 0)) (c : ℝ) (hc : 0 < c) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ v : ℝ → ℝ, MonotoneOn v (Ioc 0 d₀) ∧
      (∀ d ∈ Ioc (0 : ℝ) d₀, |u d| ≤ v d ∧ 0 ≤ v d ∧ v d ≤ c) ∧
      Tendsto v (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ ε > 0, ∃ δ > 0, ∀ d ∈ Ioc (0 : ℝ) δ, |u d| ≤ ε := by
    intro ε hε
    have h1 : ∀ᶠ d in 𝓝[>] (0 : ℝ), |u d| < ε := by
      have h2 : Tendsto (fun d => |u d|) (𝓝[>] 0) (𝓝 0) := by simpa using hu.abs
      exact h2.eventually (gt_mem_nhds hε)
    obtain ⟨δ, hδ, h⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 h1
    exact ⟨δ, hδ, fun d hd => (h hd).le⟩
  obtain ⟨d₀, hd₀, h₀⟩ := hev c hc
  let v : ℝ → ℝ := fun d => sSup ((fun e => |u e|) '' Ioc 0 (min d d₀))
  have hbdd : ∀ d, BddAbove ((fun e => |u e|) '' Ioc 0 (min d d₀)) := by
    intro d
    refine ⟨c, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact h₀ e ⟨he.1, he.2.trans (min_le_right _ _)⟩
  have hnon : ∀ d, 0 ≤ v d := fun d => Real.sSup_nonneg (by
    rintro _ ⟨e, -, rfl⟩
    exact abs_nonneg _)
  refine ⟨d₀, hd₀, v, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    refine csSup_le_csSup (hbdd b) ?_ (image_mono (Ioc_subset_Ioc_right (min_le_min_right _ hab)))
    exact ⟨_, a, ⟨ha.1, le_min le_rfl ha.2⟩, rfl⟩
  · intro d hd
    refine ⟨?_, hnon d, ?_⟩
    · exact le_csSup (hbdd d) ⟨d, ⟨hd.1, le_min le_rfl hd.2⟩, rfl⟩
    · refine Real.sSup_le ?_ hc.le
      rintro _ ⟨e, he, rfl⟩
      exact h₀ e ⟨he.1, he.2.trans (min_le_right _ _)⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hev (ε / 2) (by positivity)
    refine ⟨min δ d₀, lt_min hδ hd₀, fun d hd hdist => ?_⟩
    have hd' : 0 < d := hd
    have hlt : d < min δ d₀ := by simpa [Real.dist_eq, abs_of_pos hd'] using hdist
    have hle : v d ≤ ε / 2 := by
      refine Real.sSup_le ?_ (by positivity)
      rintro _ ⟨e, he, rfl⟩
      exact h e ⟨he.1, he.2.trans ((min_le_left _ _).trans (hlt.le.trans (min_le_left _ _)))⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnon d)]
    linarith
private theorem abs_mul_sub_one_le_three {a c E : ℝ} (hE : E ≤ 1) (ha : |a - 1| ≤ E) (hc : |c - 1| ≤ E) :
    |a * c - 1| ≤ 3 * E := by
  have h0 : 0 ≤ E := (abs_nonneg _).trans ha
  have h1 : |(a - 1) * (c - 1)| ≤ E := by
    rw [abs_mul]
    calc |a - 1| * |c - 1| ≤ E * 1 := mul_le_mul ha (hc.trans hE) (abs_nonneg _) h0
      _ = E := mul_one E
  have h2 : a * c - 1 = (a - 1) * (c - 1) + (a - 1) + (c - 1) := by ring
  rw [h2]
  calc _ ≤ |(a - 1) * (c - 1) + (a - 1)| + |c - 1| := abs_add_le _ _
    _ ≤ |(a - 1) * (c - 1)| + |a - 1| + |c - 1| := by gcongr; exact abs_add_le _ _
    _ ≤ 3 * E := by linarith
private theorem abs_sq_ratio_mul_sub_one_le {a b c p q E : ℝ} (hE : E ≤ 1 / 100) (ha : |a - 1| ≤ E) (hb : |b - 1| ≤ E)
    (hc : |c - 1| ≤ E) (hp : |p - 1| ≤ E) (hq : |q - 1| ≤ E) :
    |(a * c / (b * p)) ^ 2 * q - 1| ≤ 100 * E := by
  have h0 : 0 ≤ E := (abs_nonneg _).trans ha
  have hE1 : E ≤ 1 := by linarith
  have hac := abs_mul_sub_one_le_three hE1 ha hc
  have hbp := abs_mul_sub_one_le_three hE1 hb hp
  have hbp' := abs_le.1 hbp
  have hac' := abs_le.1 hac
  have hpos : 0 < b * p := by linarith [hbp'.1]
  set r := a * c / (b * p) with hr
  have hr1 : |r - 1| ≤ 12 * E := by
    have h1 : r - 1 = (a * c - b * p) / (b * p) := by rw [hr, sub_div, div_self hpos.ne']
    rw [h1, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h3 : |a * c - b * p| ≤ 6 * E := by
      rw [abs_le]; constructor <;> linarith [hbp'.1, hbp'.2, hac'.1, hac'.2]
    nlinarith
  have hr1' := abs_le.1 hr1
  have hq' := abs_le.1 hq
  have hrp : |r + 1| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hr1'.1, hr1'.2]
  have hqa : |q| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hq'.1, hq'.2]
  have h4 : r ^ 2 * q - 1 = (r - 1) * (r + 1) * q + (q - 1) := by ring
  rw [h4]
  have h5 : |(r - 1) * (r + 1) * q| ≤ 12 * E * 3 * 2 := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hr1 hrp (abs_nonneg _) (by positivity)) hqa (abs_nonneg _) (by positivity)
  calc _ ≤ |(r - 1) * (r + 1) * q| + |q - 1| := abs_add_le _ _
    _ ≤ 100 * E := by linarith
private theorem abs_one_div_sub_one_le {c E : ℝ} (hE : E ≤ 1 / 100) (hc : |c - 1| ≤ E) :
    |1 / c - 1| ≤ 2 * E := by
  have h := abs_le.1 hc
  have hpos : 0 < c := by linarith [h.1]
  have h1 : 1 / c - 1 = (1 - c) / c := by field_simp
  rw [h1, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_sub_comm]
  nlinarith [h.1]
private theorem eventually_mul_ceil_rpow_le (A c : ℝ) :
    ∀ᶠ u : ℝ in atTop, A * (⌈(u + c) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ u ^ ((1 : ℝ) / 90) := by
  have h1 : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 900)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [h1.eventually_ge_atTop (3 * |A| + 1), eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop |c|] with u hu hu1 huc
  have hu0 : 0 < u := by linarith
  have hc0 : 0 ≤ u + c := by linarith [neg_abs_le c]
  have hc2 : u + c ≤ 2 * u := by linarith [le_abs_self c]
  have hp : 1 ≤ u ^ ((1 : ℝ) / 100) := Real.one_le_rpow hu1 (by norm_num)
  have h2 : (u + c) ^ ((1 : ℝ) / 100) ≤ 2 * u ^ ((1 : ℝ) / 100) := by
    calc (u + c) ^ ((1 : ℝ) / 100) ≤ (2 * u) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow hc0 hc2 (by norm_num)
      _ = 2 ^ ((1 : ℝ) / 100) * u ^ ((1 : ℝ) / 100) := Real.mul_rpow (by norm_num) hu0.le
      _ ≤ 2 * u ^ ((1 : ℝ) / 100) := by
          gcongr
          calc (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have h3 : (⌈(u + c) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ 3 * u ^ ((1 : ℝ) / 100) := by
    have h9 : (⌈(u + c) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) < (u + c) ^ ((1 : ℝ) / 100) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hc0 _)
    linarith
  have h4 : u ^ ((1 : ℝ) / 90) = u ^ ((1 : ℝ) / 100) * u ^ ((1 : ℝ) / 900) := by
    rw [← Real.rpow_add hu0]; norm_num
  rw [h4]
  have hn : 0 ≤ (⌈(u + c) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := Nat.cast_nonneg _
  calc A * (⌈(u + c) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ |A| * (3 * u ^ ((1 : ℝ) / 100)) := by
        refine (mul_le_mul_of_nonneg_right (le_abs_self A) hn).trans ?_
        gcongr
    _ = u ^ ((1 : ℝ) / 100) * (3 * |A|) := by ring
    _ ≤ u ^ ((1 : ℝ) / 100) * u ^ ((1 : ℝ) / 900) := by
        gcongr
        linarith
private theorem eventually_log_mul_pow_three_le (A : ℝ) (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, Real.log (A * t) ^ 3 ≤ t := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop (1 / A) 0 3 (by positivity)
  have h2 : Tendsto (fun t : ℝ => A * t) atTop atTop := tendsto_id.const_mul_atTop hA
  have h3 := h1.comp h2
  have h4 : ∀ᶠ t : ℝ in atTop, Real.log (A * t) ^ 3 / (1 / A * (A * t) + 0) < 1 :=
    h3.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [h4, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have h5 : 1 / A * (A * t) + 0 = t := by field_simp; ring
  rw [h5, div_lt_one ht0] at ht
  exact ht.le
private theorem tendsto_log_one_add_mul_div_nat (c : ℝ) (hc : 0 < c) :
    Tendsto (fun s : ℕ => Real.log (1 + c * s) / s) atTop (𝓝 0) := by apply _root_.YangMills.SharedProofs.p26208 <;> assumption
private theorem exists_level_of_scale {L : ℕ} (hL : 2 ≤ L) (x : ℕ → ℝ) (K s : ℕ) (d Cs c₅ lamR : ℝ)
    (hd : 0 < d) (hd1 : d < 1) (hsK : s ≤ K) (hCs : 1 ≤ Cs) (hroom : Cs ≤ d * (L : ℝ) ^ s)
    (hlam : 0 ≤ lamR) (hc₅ : 0 ≤ c₅) (hpos : ∀ j ≤ K, 0 < x j)
    (hslope : ∀ i j : ℕ, i ≤ j → j ≤ K → lamR * ((j : ℝ) - i) - c₅ ≤ x i - x j)
    (hbig : ∀ j ≤ K, 1 ≤ d * (L : ℝ) ^ (K - j) →
      2 ^ 12 * (L : ℝ) ^ 2 * (⌈(x j + c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ x j ^ ((1 : ℝ) / 90)) :
    ∃ (k : ℕ) (e : ℝ), k ≤ K ∧ 1 ≤ d * (L : ℝ) ^ (K - k) ∧
      ((2 ^ 12 * (L : ℝ) * (⌈x k ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ d * (L : ℝ) ^ (K - k) ∧
          d * (L : ℝ) ^ (K - k) ≤ x k ^ ((1 : ℝ) / 90) ∧ e = 0) ∨
        (k = 0 ∧ 1 ≤ d * (L : ℝ) ^ (K - k) ∧ d * (L : ℝ) ^ (K - k) ≤ x k ^ ((1 : ℝ) / 90) ∧
          e = 1 / (d * (L : ℝ) ^ (K - k)))) ∧ 0 ≤ e ∧ e ≤ 1 / Cs := by
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hCs0 : 0 < Cs := by linarith
  have hr1 : ∀ j ≤ K, (1 : ℝ) ≤ (⌈x j ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by
    intro j hj
    have : 0 < x j ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos (hpos j hj) _
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by simpa [Nat.ceil_eq_zero, not_le] using this)
  let P : ℕ → Prop := fun j => 2 ^ 12 * (L : ℝ) * (⌈x j ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ d * (L : ℝ) ^ (K - j)
  by_cases hex : ∃ j ≤ K, P j
  · obtain ⟨j, hj, hPj⟩ := hex
    have hPk : P (Nat.findGreatest P K) := Nat.findGreatest_spec hj hPj
    have hkK : Nat.findGreatest P K ≤ K := Nat.findGreatest_le K
    set k := Nat.findGreatest P K with hk
    have h1n : 1 ≤ d * (L : ℝ) ^ (K - k) := by
      have h2 : (1 : ℝ) ≤ 2 ^ 12 * (L : ℝ) * (⌈x k ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by
        have := hr1 k hkK
        nlinarith [mul_le_mul hL1 this (by norm_num) (by linarith)]
      exact h2.trans hPk
    have hkneK : k ≠ K := by
      intro hkK'
      rw [hkK', Nat.sub_self, pow_zero, mul_one] at h1n
      linarith
    have hlt : k < K := lt_of_le_of_ne hkK hkneK
    have hnot : ¬ P (k + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hlt
    have hnot' : d * (L : ℝ) ^ (K - (k + 1)) <
        2 ^ 12 * (L : ℝ) * (⌈x (k + 1) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := not_le.1 hnot
    have hstep : x (k + 1) ≤ x k + c₅ := by
      have := hslope k (k + 1) (by omega) hlt
      push_cast at this
      nlinarith
    have hceil : (⌈x (k + 1) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ (⌈(x k + c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_mono (Real.rpow_le_rpow (hpos _ hlt).le hstep (by norm_num))
    have hpow : (L : ℝ) ^ (K - k) = L * (L : ℝ) ^ (K - (k + 1)) := by
      rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]; ring
    have hup : d * (L : ℝ) ^ (K - k) ≤ x k ^ ((1 : ℝ) / 90) := by
      refine le_trans ?_ (hbig k hkK h1n)
      rw [hpow]
      calc d * (L * (L : ℝ) ^ (K - (k + 1))) = L * (d * (L : ℝ) ^ (K - (k + 1))) := by ring
        _ ≤ L * (2 ^ 12 * (L : ℝ) * (⌈x (k + 1) ^ ((1 : ℝ) / 100)⌉₊ : ℝ)) := by gcongr
        _ ≤ L * (2 ^ 12 * (L : ℝ) * (⌈(x k + c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ)) := by gcongr
        _ = _ := by ring
    exact ⟨k, 0, hkK, h1n, Or.inl ⟨hPk, hup, rfl⟩, le_rfl, by positivity⟩
  · have hP0 : ¬ P 0 := fun h => hex ⟨0, Nat.zero_le _, h⟩
    have hn0 : d * (L : ℝ) ^ (K - 0) < 2 ^ 12 * (L : ℝ) * (⌈x 0 ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := not_le.1 hP0
    have hCn : Cs ≤ d * (L : ℝ) ^ (K - 0) := by
      refine hroom.trans ?_
      gcongr
      · omega
    have h1n : 1 ≤ d * (L : ℝ) ^ (K - 0) := hCs.trans hCn
    have hceil : (⌈x 0 ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤ (⌈(x 0 + c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by
      have hx0 := hpos 0 (Nat.zero_le _)
      exact_mod_cast Nat.ceil_mono (Real.rpow_le_rpow hx0.le (by linarith) (by norm_num))
    have hup : d * (L : ℝ) ^ (K - 0) ≤ x 0 ^ ((1 : ℝ) / 90) := by
      refine hn0.le.trans (le_trans ?_ (hbig 0 (Nat.zero_le _) h1n))
      calc 2 ^ 12 * (L : ℝ) * (⌈x 0 ^ ((1 : ℝ) / 100)⌉₊ : ℝ)
          ≤ 2 ^ 12 * (L : ℝ) * (⌈(x 0 + c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by gcongr
        _ ≤ 2 ^ 12 * (L : ℝ) ^ 2 * (⌈(x 0 + c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by
            gcongr
            nlinarith
    refine ⟨0, 1 / (d * (L : ℝ) ^ (K - 0)), Nat.zero_le _, h1n,
      Or.inr ⟨rfl, h1n, hup, rfl⟩, by positivity, ?_⟩
    exact one_div_le_one_div_of_le hCs0 hCn
private theorem tsupport_smul_of_ne_zero {X : Type*} [TopologicalSpace X] {a : ℝ} (ha : a ≠ 0) (f : X → ℝ) :
    tsupport (a • f) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support, ha]
private theorem exists_choose_congr {α : Type*} {P Q : α → Prop} (hP : ∃ a, P a) (hQ : ∃ a, Q a) (h : P = Q) :
    hP.choose = hQ.choose := by apply _root_.YangMills.Construction.Tower.UnitScale.CrossingSmoothingPeriodic.exists_choose_congr <;> assumption
private theorem inverseEighthKernelTorus_smul {S a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (f h : Torus4 S → ℝ) :
    inverseEighthKernelTorus (a • f) (b • h) = a * b * inverseEighthKernelTorus f h := by
  have hP : (fun q : (Fin 4 → ℝ) × ℝ => IsKernelBallTorus (a • f) (b • h) q.1 q.2) =
      fun q => IsKernelBallTorus f h q.1 q.2 := by
    funext q
    simp only [IsKernelBallTorus, tsupport_smul_of_ne_zero ha, tsupport_smul_of_ne_zero hb]
  unfold inverseEighthKernelTorus
  by_cases H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f h q.1 q.2
  · have H' : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus (a • f) (b • h) q.1 q.2 := by
      have := congrArg (fun P : (Fin 4 → ℝ) × ℝ → Prop => ∃ q, P q) hP
      simpa using this.mpr H
    rw [dif_pos H, dif_pos H', exists_choose_congr H' H hP]
    unfold inverseEighthKernel
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [liftToBall, Set.indicator, Function.comp, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  · have H' : ¬ ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus (a • f) (b • h) q.1 q.2 := by
      have := congrArg (fun P : (Fin 4 → ℝ) × ℝ → Prop => ∃ q, P q) hP
      intro h'
      exact H (by simpa using this.mp h')
    rw [dif_neg H, dif_neg H', mul_zero]
private theorem cumulantReal_pair_im_and_smul
    (hC : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (D : ConnectedFunctions.CouplingData) (g h g' h' : D.Torus → ℝ) (a b : ℝ) (hg : g' = a • g)
    (hh : h' = b • h) :
    (D.cumulantReal ![g, h]).im = 0 ∧
      D.cumulantReal ![g', h'] = ((a * b : ℝ) : ℂ) * D.cumulantReal ![g, h] := by
  subst hg hh
  obtain ⟨-, hn, -⟩ := hC D
  obtain ⟨⟨hreal, -, -, hhom⟩, -⟩ := (hn 2 le_rfl).1
  have e : ∀ F : Fin 2 → D.Torus → ℝ, D.connected (D.ofRealTuple F) = D.cumulantReal F :=
    fun F => D.connected_ofReal F
  refine ⟨?_, ?_⟩
  · rw [← e]
    exact hreal _ fun _ => mem_univ _
  · have h1 := hhom ![g, h] (fun _ => mem_univ _) 0 g a (mem_univ _)
    have h2 := hhom ![a • g, h] (fun _ => mem_univ _) 1 h b (mem_univ _)
    have u1 : Function.update ![g, h] 0 (a • g) = ![a • g, h] := by
      funext i; fin_cases i <;> simp
    have u2 : Function.update ![g, h] 0 g = ![g, h] := by
      funext i; fin_cases i <;> simp
    have u3 : Function.update ![a • g, h] 1 (b • h) = ![a • g, b • h] := by
      funext i; fin_cases i <;> simp
    have u4 : Function.update ![a • g, h] 1 h = ![a • g, h] := by
      funext i; fin_cases i <;> simp
    rw [u1, u2, e, e] at h1
    rw [u3, u4, e, e] at h2
    rw [h2, h1]
    push_cast
    ring
private theorem uniformNorm_smul_of_nonneg {X : Type*} {a : ℝ} (ha : 0 ≤ a) (f : X → ℝ) :
    uniformNorm (a • f) = a * uniformNorm f := by
  unfold uniformNorm
  rw [Real.mul_iSup_of_nonneg ha]
  congr 1
  funext x
  simp [abs_of_nonneg ha]
private theorem setEuclidDist_le_comm {S : ℝ} (A B : Set (Torus4 S)) :
    setEuclidDist A B ≤ setEuclidDist B A := by
  unfold setEuclidDist
  refine le_iInf₂ fun b hb => le_iInf₂ fun a ha => ?_
  rw [AmbientPoints.torusEuclidNorm_sub_comm b a]
  exact (iInf₂_le a ha).trans (iInf₂_le b hb)
private theorem euclidDistTorus_le_of_mem_closedBall {S d : ℝ} {c u v : Torus4 S} (hu : u ∈ closedBallTorus c d)
    (hv : v ∈ closedBallTorus c d) : euclidDistTorus u v ≤ 2 * d := by
  have h1 : torusEuclidNorm (u - c) ≤ d := hu
  have h2 : torusEuclidNorm (v - c) ≤ d := hv
  have h3 := AmbientPoints.torusEuclidNorm_sub_le u c v
  rw [AmbientPoints.torusEuclidNorm_sub_comm c v] at h3
  show torusEuclidNorm (u - v) ≤ 2 * d
  linarith
private theorem euclidDistTorus_le_of_setEuclidDist_le {S d : ℝ} {x₁ x₂ : Torus4 S} {A B : Set (Torus4 S)} (hd : 0 < d)
    (hA : A ⊆ closedBallTorus x₁ d) (hB : B ⊆ closedBallTorus x₂ d) (h : setEuclidDist A B ≤ ENNReal.ofReal (6 * d)) :
    ∀ u ∈ A, ∀ v ∈ B, euclidDistTorus u v ≤ 10 * d := by
  intro u hu v hv
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : setEuclidDist A B < ENNReal.ofReal (6 * d + ε) :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  simp only [setEuclidDist, iInf_lt_iff] at hlt
  obtain ⟨p, hp, q, hq, hpq⟩ := hlt
  have hpq' : torusEuclidNorm (p - q) < 6 * d + ε := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hpq
  have h1 : euclidDistTorus u p ≤ 2 * d := euclidDistTorus_le_of_mem_closedBall (hA hu) (hA hp)
  have h2 : euclidDistTorus q v ≤ 2 * d := euclidDistTorus_le_of_mem_closedBall (hB hq) (hB hv)
  have h3 := AmbientPoints.torusEuclidNorm_sub_le u p v
  have h4 := AmbientPoints.torusEuclidNorm_sub_le p q v
  have h1' : torusEuclidNorm (u - p) ≤ 2 * d := h1
  have h2' : torusEuclidNorm (q - v) ≤ 2 * d := h2
  show torusEuclidNorm (u - v) ≤ 10 * d + ε
  linarith
private theorem IsShapedBump.normalize (hS : ObjectsAreWellFormed) {L m : ℕ} (hL : 0 < L)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {x : FourTorus L m} {f : FourTorus L m → ℝ}
    (hf : IsShapedBump euclidDistTorus closedBallTorus (torusVolumeIntegral (torusSide L m)) d vt x f) :
    0 < uniformNorm f ∧ uniformNorm ((uniformNorm f)⁻¹ • f) = 1 ∧
      IsShapedBump euclidDistTorus closedBallTorus (torusVolumeIntegral (torusSide L m)) d vt x ((uniformNorm f)⁻¹ • f) ∧
      lipConstTorus ((uniformNorm f)⁻¹ • f) ≤ 1 / (vt * d) := by
  obtain ⟨-, hNorm, hLipC, hBd, -, -, -, -, -⟩ := hS
  obtain ⟨hLip, hnn, ⟨y, hy⟩, hsup, hint, hlc⟩ := hf
  have hB := hBd L m ℝ f hL hLip
  have hA : 0 < uniformNorm f := by
    have h1 := (hNorm (FourTorus L m) ℝ f hB).1 y
    have h2 : 0 < ‖f y‖ := norm_pos_iff.2 hy
    linarith
  set A := uniformNorm f with hAdef
  have hA' : 0 < A⁻¹ := inv_pos.2 hA
  have hdist : ∀ u v : FourTorus L m, 0 ≤ euclidDistTorus u v := fun u v => by
    have h := AmbientPoints.torusEuclidNorm_sub_le u v u
    rw [AmbientPoints.torusEuclidNorm_sub_comm v u, AmbientPoints.torusEuclidNorm_sub_self] at h
    show 0 ≤ torusEuclidNorm (u - v)
    linarith
  obtain ⟨hL0, hL1, -⟩ := hLipC (FourTorus L m) ℝ euclidDistTorus f hdist hLip
  have hnorm : ∀ u v, ‖(A⁻¹ • f) u - (A⁻¹ • f) v‖ = A⁻¹ * ‖f u - f v‖ := fun u v => by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos hA']
  have hFL : IsLipschitzFor euclidDistTorus (A⁻¹ • f) := by
    obtain ⟨C, hC0, hC⟩ := hLip
    refine ⟨A⁻¹ * C, by positivity, fun u v => ?_⟩
    rw [hnorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC u v) hA'.le
  have hlip : bestLipschitzConstant euclidDistTorus (A⁻¹ • f) ≤ 1 / (vt * d) := by
    obtain ⟨-, -, h3⟩ := hLipC (FourTorus L m) ℝ euclidDistTorus (A⁻¹ • f) hdist hFL
    refine (h3 (A⁻¹ * bestLipschitzConstant euclidDistTorus f) (by positivity) fun u v => ?_).trans ?_
    · rw [hnorm, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hL1 u v) hA'.le
    · calc A⁻¹ * bestLipschitzConstant euclidDistTorus f ≤ A⁻¹ * (A / (vt * d)) :=
            mul_le_mul_of_nonneg_left hlc hA'.le
        _ = 1 / (vt * d) := by field_simp
  have hnorm1 : uniformNorm (A⁻¹ • f) = 1 := by
    rw [uniformNorm_smul_of_nonneg hA'.le, inv_mul_cancel₀ hA.ne']
  refine ⟨hA, hnorm1, ⟨hFL, fun u => ?_, ⟨y, ?_⟩, ?_, ?_, ?_⟩, hlip⟩
  · exact mul_nonneg hA'.le (hnn u)
  · simpa using ⟨hA.ne', hy⟩
  · rwa [tsupport_smul_of_ne_zero hA'.ne']
  · rw [hnorm1]
    have h1 : torusVolumeIntegral (torusSide L m) (A⁻¹ • f) = A⁻¹ * torusVolumeIntegral (torusSide L m) f := by
      unfold TestFunctions.torusVolumeIntegral
      rw [← MeasureTheory.integral_const_mul]
      rfl
    rw [h1]
    calc vt * 1 * d ^ 4 = A⁻¹ * (vt * A * d ^ 4) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hint hA'.le
  · rw [hnorm1]
    exact hlip
private theorem exists_normalized_separated_pair (hS : ObjectsAreWellFormed)
    (hP : gaussianTwoPointPair) (hF : LinearResponse.FreeKernelPositiveOnSeparatedPairs)
    (hC : ConnectedFunctions.CentredIdentityAtAllFunctions)
    (ℓ : StepParameters) (hodd : Odd ℓ.side) (h13 : 13 ≤ ℓ.side) {m : ℕ} (hm : 0 < m) (K : ℕ+) {β : ℝ} (hβ : 0 < β)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) (hvt1 : vt ≤ 1) (hside : 40 * d ≤ torusSide ℓ.side m)
    {f h : FourTorus ℓ.side m → ℝ} (hfh : (f, h) ∈ separatedPairsFourTorus ℓ.side m d vt) :
    ∃ (A κ r : ℝ) (F : Fin (1 + 1) → FourTorus ℓ.side m → ℝ), 0 < A ∧ 1 / 10 ^ 8 * vt ^ 2 ≤ κ ∧
      IsSeparatedTestTuple ℓ m d vt F ∧ inverseEighthKernelTorus (ℓ := torusSide ℓ.side m) f h = A * κ ∧
      gaussianCumulantLimit (q := 1) (torusSide ℓ.side m) F = 9 / Real.pi ^ 4 * κ ∧
      torusUrsellFunction ℓ.side m K β F = (r : ℂ) ∧
      torusUrsellFunction ℓ.side m K β ![f, h] = ((A * r : ℝ) : ℂ) := by
  have hL : 0 < ℓ.side := by omega
  obtain ⟨x₁, x₂, hf, hh, hsep, hnear⟩ := hfh
  change ENNReal.ofReal d ≤ setEuclidDist (tsupport f) (tsupport h) at hsep
  change setEuclidDist (tsupport f) (tsupport h) ≤ ENNReal.ofReal (6 * d) at hnear
  obtain ⟨hA, hAn, hfb, hfl⟩ := IsShapedBump.normalize hS hL hd hvt hf
  obtain ⟨hB, hBn, hhb, hhl⟩ := IsShapedBump.normalize hS hL hd hvt hh
  set A := uniformNorm f with hAdef
  set B := uniformNorm h with hBdef
  have hA' : A⁻¹ ≠ 0 := (inv_pos.2 hA).ne'
  have hB' : B⁻¹ ≠ 0 := (inv_pos.2 hB).ne'
  have hts1 : tsupport (A⁻¹ • f) = tsupport f := tsupport_smul_of_ne_zero hA' f
  have hts2 : tsupport (B⁻¹ • h) = tsupport h := tsupport_smul_of_ne_zero hB' h
  have hcl : (A⁻¹ • f, B⁻¹ • h) ∈ separatedPairsFourTorus ℓ.side m d vt := by
    refine ⟨x₁, x₂, hfb, hhb, ?_, ?_⟩
    · show ENNReal.ofReal d ≤ setEuclidDist (tsupport (A⁻¹ • f)) (tsupport (B⁻¹ • h))
      rwa [hts1, hts2]
    · show setEuclidDist (tsupport (A⁻¹ • f)) (tsupport (B⁻¹ • h)) ≤ ENNReal.ofReal (6 * d)
      rwa [hts1, hts2]
  have hball1 : tsupport f ⊆ closedBallTorus x₁ d := hf.2.2.2.1
  have hball2 : tsupport h ⊆ closedBallTorus x₂ d := hh.2.2.2.1
  have hnear1 := euclidDistTorus_le_of_setEuclidDist_le hd hball1 hball2 hnear
  have htuple : IsSeparatedTestTuple ℓ m d vt (p := 2) ![A⁻¹ • f, B⁻¹ • h] := by
    refine ⟨?_, ?_, ?_, ⟨hd, ?_⟩, ?_⟩
    · intro i; fin_cases i
      · exact hAn
      · exact hBn
    · intro i; fin_cases i
      · exact hfb.1
      · exact hhb.1
    · intro i; fin_cases i
      · exact hfl
      · exact hhl
    · intro i k hik
      fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · show ENNReal.ofReal d ≤ setEuclidDist (tsupport (A⁻¹ • f)) (tsupport (B⁻¹ • h))
        rwa [hts1, hts2]
      · show ENNReal.ofReal d ≤ setEuclidDist (tsupport (B⁻¹ • h)) (tsupport (A⁻¹ • f))
        rw [hts1, hts2]
        exact hsep.trans (setEuclidDist_le_comm _ _)
      · exact absurd rfl hik
    · intro i j
      fin_cases i <;> fin_cases j
      · intro u hu v hv
        have := euclidDistTorus_le_of_mem_closedBall (hball1 (hts1 ▸ hu)) (hball1 (hts1 ▸ hv))
        show euclidDistTorus u v ≤ 10 * d
        linarith
      · intro u hu v hv
        exact hnear1 u (hts1 ▸ hu) v (hts2 ▸ hv)
      · intro u hu v hv
        have h1 := hnear1 v (hts1 ▸ hv) u (hts2 ▸ hu)
        have h2 : euclidDistTorus u v = euclidDistTorus v u := AmbientPoints.torusEuclidNorm_sub_comm u v
        rw [h2]
        exact h1
      · intro u hu v hv
        have := euclidDistTorus_le_of_mem_closedBall (hball2 (hts2 ▸ hu)) (hball2 (hts2 ▸ hv))
        show euclidDistTorus u v ≤ 10 * d
        linarith
  let D : ConnectedFunctions.CouplingData :=
    { L := ℓ.side, isAdmissible := ⟨hodd, h13⟩, K := K, m := ⟨m, hm⟩, coupling := β, coupling_pos := hβ }
  have hf1 : A • A⁻¹ • f = f := by rw [smul_smul, mul_inv_cancel₀ hA.ne', one_smul]
  have hh1 : B • B⁻¹ • h = h := by rw [smul_smul, mul_inv_cancel₀ hB.ne', one_smul]
  obtain ⟨him, hsm⟩ := cumulantReal_pair_im_and_smul hC D (A⁻¹ • f) (B⁻¹ • h) f h A B hf1.symm hh1.symm
  have hK := inverseEighthKernelTorus_smul (S := torusSide ℓ.side m) hA.ne' hB.ne' (A⁻¹ • f) (B⁻¹ • h)
  rw [hf1, hh1] at hK
  have h1 : D.cumulantReal ![A⁻¹ • f, B⁻¹ • h] =
      ((D.cumulantReal ![A⁻¹ • f, B⁻¹ • h]).re : ℂ) := Complex.ext rfl (by simpa using him)
  refine ⟨A * B, inverseEighthKernelTorus (ℓ := torusSide ℓ.side m) (A⁻¹ • f) (B⁻¹ • h),
    (D.cumulantReal ![A⁻¹ • f, B⁻¹ • h]).re, ![A⁻¹ • f, B⁻¹ • h], by positivity, ?_, htuple, hK, ?_, ?_, ?_⟩
  · exact hF ℓ.side m d vt hd hvt hvt1 hside _ _ hcl hAn hBn
  · exact hP ℓ.side m d vt hL hd hside _ _ hcl
  · exact h1
  · show D.cumulantReal ![f, h] = _
    rw [hsm, h1]
    push_cast
    simp
private theorem tendsto_ratio_of_subexp {C G : ℕ → ℝ} {lL sl : ℝ} (hlL : 0 < lL) (hsl : 0 < sl)
    (hC : Tendsto (fun s : ℕ => Real.log (C s) / s) atTop (𝓝 0))
    (hG : Tendsto (fun s : ℕ => G s / s) atTop (𝓝 0)) :
    Tendsto (fun s : ℕ => (G s + sl * (lL + Real.log (C s))) / (sl * (((s : ℝ) - 1) * lL - Real.log (C s))))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℕ => (sl * lL) / (s : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hn : Tendsto (fun s : ℕ => G s / s + (sl * lL) / s + sl * (Real.log (C s) / s)) atTop (𝓝 0) := by
    simpa using (hG.add h1).add (hC.const_mul sl)
  have hd : Tendsto (fun s : ℕ => sl * lL - (sl * lL) / s - sl * (Real.log (C s) / s)) atTop (𝓝 (sl * lL)) := by
    simpa using (tendsto_const_nhds.sub h1).sub (hC.const_mul sl)
  have h2 := hn.div hd (by positivity)
  rw [zero_div] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have e1 : G s / s + (sl * lL) / s + sl * (Real.log (C s) / s) = (G s + sl * (lL + Real.log (C s))) / s := by
    field_simp
    ring
  have e2 : sl * lL - (sl * lL) / s - sl * (Real.log (C s) / s) =
      (sl * (((s : ℝ) - 1) * lL - Real.log (C s))) / s := by
    field_simp
  simp only [Pi.div_apply] at *
  rw [e1, e2, div_div_div_cancel_right₀ hs']
private theorem scaleDepth_bounds {L : ℕ} (hL : 2 ≤ L) {C : ℕ → ℝ} (hC : RoomFunctions.IsSubexpGrowth C) {d : ℝ}
    (hd : 0 < d) (hd1 : d < 1) :
    1 ≤ RoomFunctions.scaleDepth L C d ∧
      C (RoomFunctions.scaleDepth L C d) ≤ d * (L : ℝ) ^ RoomFunctions.scaleDepth L C d ∧
      Real.log (1 / d) ≤ (RoomFunctions.scaleDepth L C d : ℝ) * Real.log L - Real.log (C (RoomFunctions.scaleDepth L C d)) ∧
      ((RoomFunctions.scaleDepth L C d : ℝ) - 1) * Real.log L - Real.log (C (RoomFunctions.scaleDepth L C d)) ≤
        Real.log (1 / d) := by
  set s := RoomFunctions.scaleDepth L C d with hs
  have h0 : C s * meshSize L (s : ℤ) ≤ d := RoomFunctions.mul_meshSize_scaleDepth_le hC hL hd
  have hCpos : ∀ u, 0 < C u := fun u => lt_of_lt_of_le one_pos (hC.one_le_apply u)
  have hs1 : 1 ≤ s := by
    by_contra hne
    have hs0 : s = 0 := by omega
    rw [hs0, RoomFunctions.meshSize_natCast_eq] at h0
    have := hC.one_le_apply 0
    simp at h0
    linarith
  have hlogd : Real.log (1 / d) = - Real.log d := by rw [one_div, Real.log_inv]
  refine ⟨hs1, ?_, ?_, ?_⟩
  · rw [RoomFunctions.meshSize_natCast_eq] at h0
    calc C s = C s * ((L : ℝ) ^ s)⁻¹ * (L : ℝ) ^ s := by field_simp
      _ ≤ d * (L : ℝ) ^ s := by gcongr
  · have h1 := Real.log_le_log (mul_pos (hCpos s) (RoomFunctions.meshSize_natCast_pos hL s)) h0
    rw [RoomFunctions.log_mul_meshSize hL (hCpos s)] at h1
    rw [hlogd]
    linarith
  · have hnot : ¬ C (s - 1) * meshSize L ((s - 1 : ℕ) : ℤ) ≤ d := by
      have : (s - 1) ∉ {u : ℕ | C u * meshSize L u ≤ d} := Nat.notMem_of_lt_sInf (by
        show s - 1 < RoomFunctions.scaleDepth L C d
        omega)
      exact this
    have h2 : d < C (s - 1) * meshSize L ((s - 1 : ℕ) : ℤ) := not_le.1 hnot
    have h3 := Real.log_lt_log hd h2
    rw [RoomFunctions.log_mul_meshSize hL (hCpos _)] at h3
    have h4 : Real.log (C (s - 1)) ≤ Real.log (C s) :=
      Real.log_le_log (hCpos _) (hC.mono (by omega))
    have h5 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub hs1]; simp
    rw [h5] at h3
    rw [hlogd]
    linarith
private theorem abs_coupling_div_log_sub_one_le {x' xK Xi gp lL sl t lC s : ℝ} (hsl : 0 < sl)
    (hline : |x' - xK - sl * lL * s| ≤ gp) (hxK : 0 ≤ xK) (hxK' : xK ≤ Xi) (hlC : 0 ≤ lC)
    (ht1 : t ≤ s * lL - lC) (ht2 : (s - 1) * lL - lC ≤ t) (hden : 0 < (s - 1) * lL - lC) :
    |x' / (sl * t) - 1| ≤ (Xi + gp + sl * (lL + lC)) / (sl * ((s - 1) * lL - lC)) := by
  have ht : 0 < t := lt_of_lt_of_le hden ht2
  have hst : 0 < sl * t := by positivity
  have h1 : x' / (sl * t) - 1 = (x' - sl * t) / (sl * t) := by rw [sub_div, div_self hst.ne']
  have hl := abs_le.1 hline
  have h2 : |x' - sl * t| ≤ Xi + gp + sl * (lL + lC) := by
    have e1 : sl * (s * lL - t) ≤ sl * (lL + lC) := by
      apply mul_le_mul_of_nonneg_left _ hsl.le
      linarith
    have e2 : 0 ≤ sl * (s * lL - t) := mul_nonneg hsl.le (by linarith)
    rw [abs_le]
    constructor <;> nlinarith [hl.1, hl.2]
  rw [h1, abs_div, abs_of_pos hst]
  have hnum : 0 ≤ Xi + gp + sl * (lL + lC) := (abs_nonneg _).trans h2
  calc |x' - sl * t| / (sl * t) ≤ (Xi + gp + sl * (lL + lC)) / (sl * t) := by gcongr
    _ ≤ (Xi + gp + sl * (lL + lC)) / (sl * ((s - 1) * lL - lC)) := by
        apply div_le_div_of_nonneg_left hnum (by positivity)
        exact mul_le_mul_of_nonneg_left ht2 hsl.le
private theorem rpow_neg_half_sq_eq_inv {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2) : ℝ)) ^ 2 = x⁻¹ := by apply _root_.YangMills.Construction.WeightedResponses.GradientMoves.rpow_neg_half_sq <;> assumption
private theorem rpow_neg_half_pow_four_eq {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2) : ℝ)) ^ 4 = (x ^ 2)⁻¹ := by
  have h : (x ^ (-(1 / 2) : ℝ)) ^ 4 = ((x ^ (-(1 / 2) : ℝ)) ^ 2) ^ 2 := by ring
  rw [h, rpow_neg_half_sq_eq_inv hx, inv_pow]
private theorem exists_relative_error_of_bounds {x x' w al ζ b κ r A Bd E : ℝ} (hw : 0 < w) (hb : 0 < b) (hκ : 0 < κ)
    (hE : E ≤ 1 / 100) (h1 : |al - 1| ≤ E) (h2 : |ζ - 1| ≤ E) (h3 : |x' / w - 1| ≤ E) (h4 : |x / w - 1| ≤ E)
    (h5 : |x ^ 2 * r - al ^ 2 * (b * κ)| ≤ Bd) (h6 : Bd ≤ E * (al ^ 2 * (b * κ))) :
    ∃ ε : ℝ, |ε| ≤ 100 * E ∧ A * r = ζ ^ 2 * b * (x' ^ (-(1 / 2) : ℝ)) ^ 4 * (A * κ) * (1 + ε) := by
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  have h3' := abs_le.1 h3
  have h4' := abs_le.1 h4
  have hal : 0 < al := by linarith [h1'.1]
  have hζ : 0 < ζ := by linarith [h2'.1]
  have hx'w : 0 < x' / w := by linarith [h3'.1]
  have hxw : 0 < x / w := by linarith [h4'.1]
  have hx' : 0 < x' := by
    have := mul_pos hx'w hw
    rwa [div_mul_cancel₀ _ hw.ne'] at this
  have hx : 0 < x := by
    have := mul_pos hxw hw
    rwa [div_mul_cancel₀ _ hw.ne'] at this
  have hM : 0 < al ^ 2 * (b * κ) := by positivity
  set q := x ^ 2 * r / (al ^ 2 * (b * κ)) with hq
  have hq1 : |q - 1| ≤ E := by
    have e : q - 1 = (x ^ 2 * r - al ^ 2 * (b * κ)) / (al ^ 2 * (b * κ)) := by
      rw [hq, sub_div, div_self hM.ne']
    rw [e, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    exact h5.trans h6
  refine ⟨(al * (x' / w) / (ζ * (x / w))) ^ 2 * q - 1, abs_sq_ratio_mul_sub_one_le hE h1 h2 h3 h4 hq1, ?_⟩
  rw [rpow_neg_half_pow_four_eq hx', hq]
  field_simp
  ring
private theorem IsFirstPassageIndex.unique {B g : ℝ} {x : ℕ → ℝ} {K K' : ℕ}
    (h : SequencePassage.IsFirstPassageIndex B g x K)
    (h' : SequencePassage.IsFirstPassageIndex B g x K') : K = K' := by apply _root_.YangMills.SharedProofs.p54782 <;> assumption
private theorem levelMesh_eq_inv_pow {L K k : ℕ} (hk : k ≤ K) : levelMesh L K k = ((L : ℝ) ^ (K - k))⁻¹ := by
  unfold levelMesh meshSize
  rw [show -((K : ℤ) - (k : ℤ)) = -((K - k : ℕ) : ℤ) by rw [Nat.cast_sub hk], zpow_neg, zpow_natCast]
private theorem zpow_sub_eq_inv_pow {L K k : ℕ} (hk : k ≤ K) :
    (L : ℝ) ^ ((k : ℤ) - (K : ℤ)) = ((L : ℝ) ^ (K - k))⁻¹ := by
  rw [show (k : ℤ) - (K : ℤ) = -((K - k : ℕ) : ℤ) by rw [Nat.cast_sub hk]; ring, zpow_neg, zpow_natCast]
set_option maxHeartbeats 4000000 in
private theorem fourPointLaws_of_trajectoryData
    (hS : ObjectsAreWellFormed) (hP : gaussianTwoPointPair)
    (hF : LinearResponse.FreeKernelPositiveOnSeparatedPairs)
    (hC : ConnectedFunctions.CentredIdentityAtAllFunctions)
    {T : ParameterAssignment} {y : ℝ} (D : TrajectoryData.TrajectoryParameters T y) (hH : D.Admissible)
    (hD : TrajectoryData.HasTrajectoryData D) (al : ℝ → ℕ → ℝ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (hnear : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, y ≤ D.coupling β j) → |al β k - 1| ≤ Ca * D.coupling β k ^ (-(1 / 2) : ℝ))
    (vt : ℝ) (hvt : 0 < vt) (hvt1 : vt ≤ 1) (C X : ℝ)
    (hlaw : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, X ≤ D.coupling β j) → (∀ j ≤ k, y ≤ D.coupling β j) → ∀ (K m : ℕ) (d e : ℝ),
      Real.exp (Real.log (D.coupling β k) ^ 3) ≤ torusSide T.side m / levelMesh T.side K k →
      IsLevelWindow (T.stepParameters y) (D.coupling β k) k (d / levelMesh T.side K k) e →
      CumulantLawsOnTorus (T.stepParameters y) vt C (D.coupling β k) (al β k) e β K m d)
    (g : ℝ) (hg : 0 < g) (hgy : D.floorStar ≤ g ^ (-2 : ℤ)) (room : ℕ → ℝ)
    (hroom : RoomFunctions.IsSubexpGrowth room) :
    ∃ (d₀ : ℝ) (ηBar εBar : ℝ → ℝ),
      EvaluationLaws (flowProfile (T.stepParameters y) g D.shift room al) T.side vt D.lam (D.lam + D.c₅) d₀ 1 ∧
      SharpEvaluationLaws (flowProfile (T.stepParameters y) g D.shift room al) T.side vt d₀ 1 ηBar (fun _ => εBar) := by
  have hb := hH.errorMargin
  have hfit := hb.admissible
  have hL16 : 2 ^ 16 ≤ T.side := hfit.L_ge
  have hL2 : 2 ≤ T.side := by norm_num at hL16; omega
  have hL13 : 13 ≤ T.side := by norm_num at hL16; omega
  have hodd : Odd T.side := hfit.L_odd
  have hLr : (1 : ℝ) < T.side := by exact_mod_cast (by omega : 1 < T.side)
  have hLr0 : (0 : ℝ) < T.side := by linarith
  have hlL : 0 < Real.log T.side := Real.log_pos hLr
  have hsl : 0 < TrajectoryData.logSlope := by
    unfold TrajectoryData.logSlope
    positivity
  set sl := TrajectoryData.logSlope with hsldef
  have hc₀ : D.c₀ = sl * Real.log T.side := rfl
  have hc₀pos : 0 < D.c₀ := by rw [hc₀]; positivity
  have hlamR : D.rateBound = 3 / 4 * (sl * Real.log T.side) := rfl
  have hcH : 0 ≤ D.cH := by
    have h := (hb.drop_two_sided 0 0 0 le_rfl (fun l hl => absurd hl (Nat.not_lt_zero _))).1
    simp only [Nat.cast_zero, sub_self, mul_zero, zero_sub] at h
    linarith
  have hc₅ : 0 ≤ D.c₅ := by
    show 0 ≤ 2 * D.cH
    linarith
  have hX₀ : 8 ≤ D.X₀ := hb.floor_ge
  have hyX : y ≤ D.X₀ := hb.floor_le
  have hXy : D.X₀ ≤ D.floorStar := (le_max_left _ _).trans (le_max_left _ _)
  have hg2 : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
  have hBs : 0 ≤ D.shift := by
    have := hfit.B_pos
    have h2 := hH.shift_ge
    have h3 : 0 < T.B := this
    linarith
  obtain ⟨e₂, he₂, hdist⟩ := hD.distance g hg hgy (1 / 90) (by norm_num)
  have hb9 : TwoPointFunction.amplitudeConstant = 9 / Real.pi ^ 4 := by
    norm_num [TwoPointFunction.amplitudeConstant, ParameterChoice.colorNumber]
  have hbpos : 0 < TwoPointFunction.amplitudeConstant := by rw [hb9]; positivity
  have haN : oneLoopCoeff = 1 / sl := by
    simp only [oneLoopCoeff, hsldef, TrajectoryData.logSlope, ParameterChoice.colorNumber]
    field_simp
    norm_num
  have haNpos : 0 < oneLoopCoeff := by rw [haN]; positivity
  let G : ℕ → ℝ := fun s => D.threshold g + D.lineGap s
  have hG : Tendsto (fun s : ℕ => G s / s) atTop (𝓝 0) := by
    have hcpos : 0 < 3 * D.c₀ / (4 * D.X₀) := by
      have : 0 < D.X₀ := by linarith
      positivity
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat (D.threshold g + 2 * D.cH + D.Cr)).add
      ((tendsto_log_one_add_mul_div_nat _ hcpos).const_mul (8 * D.Md / (3 * D.c₀)))
    simp only [mul_zero, add_zero] at h1
    refine h1.congr fun s => ?_
    simp only [G, TrajectoryData.TrajectoryParameters.lineGap]
    rw [show 1 + 3 * D.c₀ * (s : ℝ) / (4 * D.X₀) = 1 + 3 * D.c₀ / (4 * D.X₀) * s by ring]
    ring
  let φ : ℕ → ℝ := fun s =>
    (G s + sl * (Real.log T.side + Real.log (room s))) / (sl * (((s : ℝ) - 1) * Real.log T.side - Real.log (room s)))
  have hφ : Tendsto φ atTop (𝓝 0) := tendsto_ratio_of_subexp hlL hsl hroom.tendsto_log_div_nat hG
  have ht : Tendsto (fun d : ℝ => Real.log (1 / d)) (𝓝[>] 0) atTop := by
    refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun d => ?_
    simp [one_div, Real.log_inv]
  let W : ℝ → ℝ := fun d => sl * Real.log (1 / d)
  have hW : Tendsto W (𝓝[>] 0) atTop := ht.const_mul_atTop hsl
  have hW2 : Tendsto (fun d => W d / 2) (𝓝[>] 0) atTop := hW.atTop_div_const (by norm_num)
  have hdep : Tendsto (RoomFunctions.scaleDepth T.side room) (𝓝[>] 0) atTop :=
    RoomFunctions.tendsto_scaleDepth hroom hL2
  have hroomS : Tendsto (fun d => room (RoomFunctions.scaleDepth T.side room d)) (𝓝[>] 0) atTop :=
    hroom.tendsto_atTop_atTop.comp hdep
  let c₁ : ℝ := 9 / 16 * TwoPointFunction.amplitudeConstant * (1 / 10 ^ 8 * vt ^ 2)
  have hc₁ : 0 < c₁ := by positivity
  let Aa : ℝ := |C| / c₁
  have hAa : 0 ≤ Aa := by positivity
  let E : ℝ → ℝ := fun d => |e₂ d| + |φ (RoomFunctions.scaleDepth T.side room d)| + Ca * (W d / 2) ^ (-(1 / 2) : ℝ) +
    Aa * ((W d / 2) ^ (-(1 / 100) : ℝ) + 1 / room (RoomFunctions.scaleDepth T.side room d))
  have hE : Tendsto E (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun d => (W d / 2) ^ (-(1 / 2) : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp hW2
    have h2 : Tendsto (fun d => (W d / 2) ^ (-(1 / 100) : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp hW2
    have h3 : Tendsto (fun d => 1 / room (RoomFunctions.scaleDepth T.side room d)) (𝓝[>] 0) (𝓝 0) :=
      hroomS.const_div_atTop 1
    have h4 : Tendsto (fun d => |φ (RoomFunctions.scaleDepth T.side room d)|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hφ.comp hdep).abs
    have h5 : Tendsto (fun d => |e₂ d|) (𝓝[>] 0) (𝓝 0) := by simpa using he₂.abs
    have h6 := ((h5.add h4).add (h1.const_mul Ca)).add ((h2.add h3).const_mul Aa)
    rw [show (0 : ℝ) + 0 + Ca * 0 + Aa * (0 + 0) = 0 by ring] at h6
    exact h6
  have hE0 : ∀ d, 0 ≤ room (RoomFunctions.scaleDepth T.side room d) := fun d =>
    zero_le_one.trans (hroom.one_le_apply _)
  obtain ⟨d₁, hd₁, v, hvm, hvb, hv0⟩ := monotone_majorant_near_zero E hE (1 / 200) (by norm_num)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (eventually_mul_ceil_rpow_le (2 ^ 12 * (T.side : ℝ) ^ 2) D.c₅)
  let Y : ℝ := max (max X₁ (X + D.c₅)) 1
  have hYX₁ : X₁ ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
  have hYX : X + D.c₅ ≤ Y := (le_max_right _ _).trans (le_max_left _ _)
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hgood : ∀ᶠ d in 𝓝[>] (0 : ℝ), Y + D.c₅ ≤ 3 / 4 * W d ∧ D.c₅ ≤ W d / 4 ∧
      Real.log (2 * sl * Real.log (1 / d)) ^ 3 ≤ Real.log (1 / d) ∧
      0 < ((RoomFunctions.scaleDepth T.side room d : ℝ) - 1) * Real.log T.side -
        Real.log (room (RoomFunctions.scaleDepth T.side room d)) := by
    have hden : ∀ᶠ s : ℕ in atTop, 0 < ((s : ℝ) - 1) * Real.log T.side - Real.log (room s) := by
      have h1 : ∀ᶠ s : ℕ in atTop, Real.log (room s) / s < Real.log T.side / 2 :=
        hroom.tendsto_log_div_nat.eventually (gt_mem_nhds (by positivity))
      have h2 : ∀ᶠ s : ℕ in atTop, (3 : ℝ) ≤ s := tendsto_natCast_atTop_atTop.eventually_ge_atTop 3
      filter_upwards [h1, h2] with s hs h3
      have hs0 : (0 : ℝ) < s := by linarith
      rw [div_lt_iff₀ hs0] at hs
      have h5 := mul_pos hlL (by linarith : (0 : ℝ) < (s : ℝ) / 2 - 1)
      linarith
    filter_upwards [hW.eventually_ge_atTop (4 / 3 * (Y + D.c₅)), hW.eventually_ge_atTop (4 * D.c₅),
      ht.eventually (eventually_log_mul_pow_three_le (2 * sl) (by positivity)), hdep.eventually hden] with d h1 h2 h3 h4
    exact ⟨by linarith, by linarith, h3, h4⟩
  obtain ⟨d₂, hd₂, hgood₂⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hgood
  let d₀ : ℝ := min d₁ (min d₂ (1 / 20))
  have hd₀ : 0 < d₀ := lt_min hd₁ (lt_min hd₂ (by norm_num))
  have hd₀₁ : d₀ ≤ d₁ := min_le_left _ _
  have hd₀₂ : d₀ ≤ d₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hd₀₃ : d₀ ≤ 1 / 20 := (min_le_right _ _).trans (min_le_right _ _)
  have hEparts : ∀ d, 0 < W d → |e₂ d| ≤ E d ∧ |φ (RoomFunctions.scaleDepth T.side room d)| ≤ E d ∧
      Ca * (W d / 2) ^ (-(1 / 2) : ℝ) ≤ E d ∧
      Aa * ((W d / 2) ^ (-(1 / 100) : ℝ) + 1 / room (RoomFunctions.scaleDepth T.side room d)) ≤ E d := by
    intro d hWd
    have n1 := abs_nonneg (e₂ d)
    have n2 := abs_nonneg (φ (RoomFunctions.scaleDepth T.side room d))
    have hW0 : 0 ≤ W d / 2 := by positivity
    have n3 : 0 ≤ Ca * (W d / 2) ^ (-(1 / 2) : ℝ) := mul_nonneg hCa (Real.rpow_nonneg hW0 _)
    have n4 : 0 ≤ Aa * ((W d / 2) ^ (-(1 / 100) : ℝ) + 1 / room (RoomFunctions.scaleDepth T.side room d)) :=
      mul_nonneg hAa (add_nonneg (Real.rpow_nonneg hW0 _) (one_div_nonneg.2 (hE0 d)))
    have hEd : E d = |e₂ d| + |φ (RoomFunctions.scaleDepth T.side room d)| + Ca * (W d / 2) ^ (-(1 / 2) : ℝ) +
      Aa * ((W d / 2) ^ (-(1 / 100) : ℝ) + 1 / room (RoomFunctions.scaleDepth T.side room d)) := rfl
    rw [hEd]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hWv : ∀ d ∈ Ioc (0 : ℝ) d₀, 0 < W d ∧ E d ≤ v d ∧ 0 ≤ v d ∧ v d ≤ 1 / 200 ∧ d < 1 ∧
      Y + D.c₅ ≤ 3 / 4 * W d ∧ D.c₅ ≤ W d / 4 ∧
      Real.log (2 * sl * Real.log (1 / d)) ^ 3 ≤ Real.log (1 / d) ∧
      0 < ((RoomFunctions.scaleDepth T.side room d : ℝ) - 1) * Real.log T.side -
        Real.log (room (RoomFunctions.scaleDepth T.side room d)) := by
    intro d hd
    obtain ⟨g1, g2, g3, g4⟩ : Y + D.c₅ ≤ 3 / 4 * W d ∧ D.c₅ ≤ W d / 4 ∧
      Real.log (2 * sl * Real.log (1 / d)) ^ 3 ≤ Real.log (1 / d) ∧
      0 < ((RoomFunctions.scaleDepth T.side room d : ℝ) - 1) * Real.log T.side -
        Real.log (room (RoomFunctions.scaleDepth T.side room d)) := hgood₂ ⟨hd.1, hd.2.trans hd₀₂⟩
    obtain ⟨v1, v2, v3⟩ := hvb d ⟨hd.1, hd.2.trans hd₀₁⟩
    refine ⟨by linarith, (le_abs_self _).trans v1, v2, v3, ?_, g1, g2, g3, g4⟩
    have := hd.2.trans hd₀₃
    linarith
  have hdatum : ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g →
      (∀ j ≤ K, g ^ (-2 : ℤ) < D.coupling β j) ∧ D.coupling β K ≤ D.threshold g ∧ TrajectoryData.IsFirstPassage D g β K := by
    intro K β hw
    have hw' : SequencePassage.passageThreshold D.shift g ≤ β ∧
        SequencePassage.IsFirstPassageIndex D.shift g (D.coupling β) K := hw
    obtain ⟨K', hp⟩ := hD.passage g hg hgy β hw'.1
    have hKK := IsFirstPassageIndex.unique hw'.2 hp.isFirstPassageIndex
    subst hKK
    exact ⟨hp.coupling_gt, hw'.2.1, hp⟩
  have hfl : ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ j ≤ K, y ≤ D.coupling β j := by
    intro K β hw j hj
    have := (hdatum K β hw).1 j hj
    linarith
  have hdepth : ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ d ∈ Ioc (0 : ℝ) d₀,
      RoomFunctions.scaleDepth T.side room d + 1 ≤ K →
      |D.coupling β (K - RoomFunctions.scaleDepth T.side room d) / W d - 1| ≤ v d := by
    intro K β hw d hd hK
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hWv d hd
    obtain ⟨hs1, hCs, ht1, ht2⟩ := scaleDepth_bounds hL2 hroom hd.1 w5
    obtain ⟨hab, hxK, -⟩ := hdatum K β hw
    set s := RoomFunctions.scaleDepth T.side room d with hs
    have hline := hD.line g hg hgy K β hw (K - s) (Nat.sub_le _ _)
    have hsub : K - (K - s) = s := by omega
    have hcast : (K : ℝ) - ((K - s : ℕ) : ℝ) = s := by rw [Nat.cast_sub (by omega)]; ring
    rw [hsub, hcast, hc₀] at hline
    have hlogC : 0 ≤ Real.log (room s) := Real.log_nonneg (hroom.one_le_apply s)
    have hxK0 : 0 ≤ D.coupling β K := (hg2.trans (hab K le_rfl)).le
    have h := abs_coupling_div_log_sub_one_le hsl hline hxK0 hxK hlogC ht1 ht2 w9
    refine h.trans ?_
    show φ s ≤ v d
    exact (le_abs_self _).trans (((hEparts d w1).2.1).trans w2)
  have hlevel : ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ d ∈ Ioc (0 : ℝ) d₀,
      RoomFunctions.scaleDepth T.side room d + 1 ≤ K →
      ∃ (k : ℕ) (e : ℝ), k ≤ K ∧ (∀ j ≤ k, X ≤ D.coupling β j) ∧
        (∀ m, Real.exp (Real.log (D.coupling β k) ^ 3) ≤ torusSide T.side m / levelMesh T.side K k) ∧
        IsLevelWindow (T.stepParameters y) (D.coupling β k) k (d / levelMesh T.side K k) e ∧
        |D.coupling β k / W d - 1| ≤ v d ∧ W d / 2 ≤ D.coupling β k ∧ 0 ≤ e ∧
        e ≤ 1 / room (RoomFunctions.scaleDepth T.side room d) := by
    intro K β hw d hd hK
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hWv d hd
    have hd0 : 0 < d := hd.1
    obtain ⟨hs1, hCs, ht1, ht2⟩ := scaleDepth_bounds hL2 hroom hd0 w5
    obtain ⟨hab, hxK, -⟩ := hdatum K β hw
    have hslope := hD.slope g hg hgy K β hw
    have hpos : ∀ j ≤ K, 0 < D.coupling β j := fun j hj => hg2.trans (hab j hj)
    have hlam : 0 ≤ D.rateBound := by rw [hlamR]; positivity
    have hlow : ∀ j ≤ K, 1 ≤ d * (T.side : ℝ) ^ (K - j) → 3 / 4 * W d - D.c₅ ≤ D.coupling β j := by
      intro j hj h1
      have h2 : Real.log (1 / d) ≤ ((K - j : ℕ) : ℝ) * Real.log T.side := by
        have h3 : 1 / d ≤ (T.side : ℝ) ^ (K - j) := by
          rw [div_le_iff₀ hd0]
          linarith
        have h4 := Real.log_le_log (by positivity) h3
        rwa [Real.log_pow] at h4
      have h3 := hslope j K hj le_rfl
      have h4 := hpos K le_rfl
      have hcast : ((K - j : ℕ) : ℝ) = (K : ℝ) - j := by rw [Nat.cast_sub hj]
      rw [hcast] at h2
      have h5 : sl * Real.log (1 / d) ≤ sl * (((K : ℝ) - j) * Real.log T.side) :=
        mul_le_mul_of_nonneg_left h2 hsl.le
      rw [hlamR] at h3
      show 3 / 4 * (sl * Real.log (1 / d)) - D.c₅ ≤ D.coupling β j
      linarith only [h3, h4, h5]
    have hbig : ∀ j ≤ K, 1 ≤ d * (T.side : ℝ) ^ (K - j) →
        2 ^ 12 * (T.side : ℝ) ^ 2 * (⌈(D.coupling β j + D.c₅) ^ ((1 : ℝ) / 100)⌉₊ : ℝ) ≤
          D.coupling β j ^ ((1 : ℝ) / 90) := by
      intro j hj h1
      exact hX₁ _ (by linarith [hlow j hj h1])
    obtain ⟨k, e, hkK, h1n, hwin, he0, he1⟩ := exists_level_of_scale hL2 (D.coupling β) K
      (RoomFunctions.scaleDepth T.side room d) d (room (RoomFunctions.scaleDepth T.side room d)) D.c₅ D.rateBound hd0 w5
      (by omega) (hroom.one_le_apply _) hCs hlam hc₅ hpos hslope hbig
    have hxk := hlow k hkK h1n
    have hn : d / levelMesh T.side K k = d * (T.side : ℝ) ^ (K - k) := by
      rw [levelMesh_eq_inv_pow hkK, div_inv_eq_mul]
    have hn2 : d / (T.side : ℝ) ^ ((k : ℤ) - (K : ℤ)) = d * (T.side : ℝ) ^ (K - k) := by
      rw [zpow_sub_eq_inv_pow hkK, div_inv_eq_mul]
    have hupper : d * (T.side : ℝ) ^ (K - k) ≤ D.coupling β k ^ ((1 : ℝ) / 90) := by
      rcases hwin with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ <;> exact h2
    have h2K : 2 ≤ K := by omega
    have hd' := hdist K β h2K hw k hkK d (by linarith) (by rw [hn2]; exact h1n) (by rw [hn2]; exact hupper)
    have hrat : |D.coupling β k / W d - 1| ≤ v d :=
      hd'.trans ((le_abs_self _).trans (((hEparts d w1).1).trans w2))
    refine ⟨k, e, hkK, ?_, ?_, ?_, hrat, by linarith, he0, he1⟩
    · intro j hj
      have h3 := hslope j k hj hkK
      have hnn : 0 ≤ D.rateBound * ((k : ℝ) - j) :=
        mul_nonneg hlam (sub_nonneg.2 (by exact_mod_cast hj))
      linarith
    · intro m
      rw [levelMesh_eq_inv_pow hkK, div_inv_eq_mul]
      have hxk1 : 1 ≤ D.coupling β k := by linarith
      have hr := abs_le.1 hrat
      have hx2 : D.coupling β k ≤ 2 * sl * Real.log (1 / d) := by
        have h4 : D.coupling β k / W d ≤ 2 := by linarith [hr.2]
        rw [div_le_iff₀ w1] at h4
        have h5 : W d = sl * Real.log (1 / d) := rfl
        rw [h5] at h4
        linarith
      have hlog : Real.log (D.coupling β k) ≤ Real.log (2 * sl * Real.log (1 / d)) :=
        Real.log_le_log (by linarith) hx2
      have hcube : Real.log (D.coupling β k) ^ 3 ≤ Real.log (1 / d) :=
        (pow_le_pow_left₀ (Real.log_nonneg hxk1) hlog 3).trans w8
      have h1d : 0 < 1 / d := by positivity
      have hsd : (1 : ℝ) ≤ torusSide T.side m := by
        have : (1 : ℝ) ≤ (T.side : ℝ) ^ m := one_le_pow₀ hLr.le
        unfold torusSide
        linarith
      calc Real.exp (Real.log (D.coupling β k) ^ 3) ≤ Real.exp (Real.log (1 / d)) := Real.exp_le_exp.2 hcube
        _ = 1 / d := Real.exp_log h1d
        _ ≤ (T.side : ℝ) ^ (K - k) := by
            rw [div_le_iff₀ hd0]
            linarith
        _ ≤ torusSide T.side m * (T.side : ℝ) ^ (K - k) := le_mul_of_one_le_left (by positivity) hsd
    · unfold IsLevelWindow
      rw [hn]
      rcases hwin with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩
      · exact Or.inl ⟨a1, a2, a3⟩
      · exact Or.inr ⟨a1, a2, a3, a4⟩
  have hnum : ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ k ≤ K,
      W d / 2 ≤ D.coupling β k → |al β k - 1| ≤ v d := by
    intro K β hw d hd k hkK hxk
    obtain ⟨w1, w2, -⟩ := hWv d hd
    have h1 := hnear β k fun j hj => hfl K β hw j (hj.trans hkK)
    have h2 : D.coupling β k ^ (-(1 / 2) : ℝ) ≤ (W d / 2) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hCa).trans (((hEparts d w1).2.2.1).trans w2))
  have hdeep : ∀ (K : ℕ+) (d : ℝ), (flowProfile (T.stepParameters y) g D.shift room al).IsDeepEnough T.side K 1 d →
      RoomFunctions.scaleDepth T.side room d + 1 ≤ (K : ℕ) := by
    intro K d h
    have h' : ((1 : ℕ) : ℤ) ≤ ((K : ℕ) : ℤ) - (RoomFunctions.scaleDepth T.side room d : ℤ) := h
    omega
  have hhalf : ∀ (K : ℕ) (β : ℝ), β ∈ D.passageWindow K g → ∀ d ∈ Ioc (0 : ℝ) d₀,
      RoomFunctions.scaleDepth T.side room d + 1 ≤ K →
      W d / 2 ≤ D.coupling β (K - RoomFunctions.scaleDepth T.side room d) := by
    intro K β hw d hd hK
    obtain ⟨w1, w2, w3, w4, -⟩ := hWv d hd
    have h1 := abs_le.1 (hdepth K β hw d hd hK)
    have h2 : 1 / 2 ≤ D.coupling β (K - RoomFunctions.scaleDepth T.side room d) / W d := by linarith [h1.1]
    rw [le_div_iff₀ w1] at h2
    linarith
  have hlawp : ∀ (K : ℕ+) (β : ℝ), (flowProfile (T.stepParameters y) g D.shift room al).IsFirstPassage K β → ∀ m : ℕ,
      torusSide T.side m ∈ (flowProfile (T.stepParameters y) g D.shift room al).sides → ∀ d ∈ Ioc (0 : ℝ) d₀,
      (flowProfile (T.stepParameters y) g D.shift room al).IsDeepEnough T.side K 1 d →
      ∀ f h : FourTorus T.side m → ℝ, (f, h) ∈ separatedPairsFourTorus T.side m d vt → ∃ ε : ℝ, |ε| ≤ 100 * v d ∧
        torusUrsellFunction T.side m K β ![f, h] =
          (((flowProfile (T.stepParameters y) g D.shift room al).fieldNorm K β d ^ 2 *
            TwoPointFunction.amplitudeConstant * (flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 4 *
            inverseEighthKernelTorus (ℓ := torusSide T.side m) f h * (1 + ε) : ℝ) : ℂ) := by
    intro K β hw m hm d hd hdp f h hfh
    have hw' : β ∈ D.passageWindow K g := hw
    have hK := hdeep K d hdp
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hWv d hd
    obtain ⟨k, e, hkK, hXk, hside, hwin, hrat, hxk, he0, he1⟩ := hlevel K β hw' d hd hK
    have hrat' := hdepth K β hw' d hd hK
    have hhalf' := hhalf K β hw' d hd hK
    obtain ⟨m', hm'0, hm'⟩ : ∃ m' : ℕ, 0 < m' ∧ torusSide T.side m = torusSide T.side m' := hm
    have hmm : m = m' := by
      have h2 : (T.side : ℝ) ^ m = (T.side : ℝ) ^ m' := by
        unfold torusSide at hm'
        linarith
      exact pow_right_injective₀ hLr0 hLr.ne' h2
    have hm0 : 0 < m := hmm ▸ hm'0
    have hβ : 0 < β := by
      have h1 : SequencePassage.passageThreshold D.shift g ≤ β := hw'.1
      have h2 : SequencePassage.passageThreshold D.shift g = g ^ (-2 : ℤ) + D.shift := rfl
      linarith
    have hlt : 40 * d ≤ torusSide (T.stepParameters y).side m := by
      have h1 : (1 : ℝ) ≤ (T.side : ℝ) ^ m := one_le_pow₀ hLr.le
      have h2 := hd.2.trans hd₀₃
      show 40 * d ≤ 2 * (T.side : ℝ) ^ m
      linarith
    obtain ⟨A, κ, r, F, hA, hκ, hT, hKf, hLaw, hr, hS2⟩ :=
      exists_normalized_separated_pair hS hP hF hC (T.stepParameters y) hodd hL13 hm0 K hβ hd.1 hvt hvt1 hlt hfh
    have hlw := hlaw β k hXk (fun j hj => hfl K β hw' j (hj.trans hkK)) K m d e (hside m) hwin 1 (Or.inl rfl) F hT
    rw [hr, hLaw] at hlw
    have hnorm : ‖(((D.coupling β k ^ (1 + 1) : ℝ)) : ℂ) * (r : ℂ) -
        ((al β k ^ (1 + 1) * (9 / Real.pi ^ 4 * κ) : ℝ) : ℂ)‖ =
        |D.coupling β k ^ 2 * r - al β k ^ 2 * (TwoPointFunction.amplitudeConstant * κ)| := by
      rw [hb9, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hlw
    have h1 := hnum K β hw' d hd k hkK hxk
    have h2 := hnum K β hw' d hd _ (Nat.sub_le _ _) hhalf'
    have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκ
    have hal : 3 / 4 ≤ al β k := by
      have := abs_le.1 h1
      linarith [this.1]
    have hxpow : D.coupling β k ^ (-(1 / 100) : ℝ) ≤ (W d / 2) ^ (-(1 / 100) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
    have hu : D.coupling β k ^ (-(1 / 100 : ℝ)) + e ≤
        (W d / 2) ^ (-(1 / 100) : ℝ) + 1 / room (RoomFunctions.scaleDepth T.side room d) := by
      have h3 : (-(1 / 100 : ℝ)) = (-(1 / 100) : ℝ) := rfl
      linarith
    have hu0 : 0 ≤ D.coupling β k ^ (-(1 / 100 : ℝ)) + e :=
      add_nonneg (Real.rpow_nonneg (by linarith) _) he0
    have hCle : C * (D.coupling β k ^ (-(1 / 100 : ℝ)) + e) ≤ |C| * (D.coupling β k ^ (-(1 / 100 : ℝ)) + e) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hu0
    have hAc : |C| = Aa * c₁ := by
      show |C| = |C| / c₁ * c₁
      field_simp
    have h6 : |C| * (D.coupling β k ^ (-(1 / 100 : ℝ)) + e) ≤
        v d * (al β k ^ 2 * (TwoPointFunction.amplitudeConstant * κ)) := by
      have h3 : Aa * ((W d / 2) ^ (-(1 / 100) : ℝ) + 1 / room (RoomFunctions.scaleDepth T.side room d)) ≤ v d :=
        ((hEparts d w1).2.2.2).trans w2
      have h4 : Aa * (D.coupling β k ^ (-(1 / 100 : ℝ)) + e) ≤ v d :=
        (mul_le_mul_of_nonneg_left hu hAa).trans h3
      have h5 : c₁ ≤ al β k ^ 2 * (TwoPointFunction.amplitudeConstant * κ) := by
        have h7 : (9 / 16 : ℝ) ≤ al β k ^ 2 := by
          have h8 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hal 2
          linarith only [h8]
        show 9 / 16 * TwoPointFunction.amplitudeConstant * (1 / 10 ^ 8 * vt ^ 2) ≤ _
        calc 9 / 16 * TwoPointFunction.amplitudeConstant * (1 / 10 ^ 8 * vt ^ 2)
            = 9 / 16 * (TwoPointFunction.amplitudeConstant * (1 / 10 ^ 8 * vt ^ 2)) := by ring
          _ ≤ al β k ^ 2 * (TwoPointFunction.amplitudeConstant * κ) := by gcongr
      calc |C| * (D.coupling β k ^ (-(1 / 100 : ℝ)) + e) = Aa * (D.coupling β k ^ (-(1 / 100 : ℝ)) + e) * c₁ := by
            rw [hAc]; ring
        _ ≤ v d * c₁ := mul_le_mul_of_nonneg_right h4 hc₁.le
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 w3
    obtain ⟨ε, hε, heq⟩ := exists_relative_error_of_bounds (A := A) w1 hbpos hκ0 (by linarith) h1 h2 hrat' hrat
      (hlw.trans (hCle)) h6
    refine ⟨ε, hε, ?_⟩
    have e1 : torusUrsellFunction T.side m K β ![f, h] = ((A * r : ℝ) : ℂ) := hS2
    have e2 : inverseEighthKernelTorus (ℓ := torusSide T.side m) f h = A * κ := hKf
    rw [e1, e2]
    exact congrArg (fun t : ℝ => (t : ℂ)) heq
  have hmono : MonotoneOn v (Ioc 0 d₀) := hvm.mono (Ioc_subset_Ioc_right hd₀₁)
  have hsharp : SharpEvaluationLaws (flowProfile (T.stepParameters y) g D.shift room al) T.side vt d₀ 1
      (fun d => 2 * v d) (fun _ d => 100 * v d) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlawp, ?_, ?_⟩
    · intro a ha b hb hab
      have := hmono ha hb hab
      show 2 * v a ≤ 2 * v b
      linarith
    · intro _ a ha b hb hab
      have := hmono ha hb hab
      show 100 * v a ≤ 100 * v b
      linarith
    · intro d hd
      obtain ⟨-, -, w3, w4, -⟩ := hWv d hd
      exact ⟨by positivity, by linarith⟩
    · intro _ d hd
      obtain ⟨-, -, w3, w4, -⟩ := hWv d hd
      exact ⟨by positivity, by linarith⟩
    · simpa using hv0.const_mul 2
    · intro _
      simpa using hv0.const_mul 100
    · intro K β hw d hd hdp
      have hK := hdeep K d hdp
      obtain ⟨-, -, w3, -⟩ := hWv d hd
      have h := hnum K β hw d hd _ (Nat.sub_le _ _) (hhalf K β hw d hd hK)
      show |al β ((K : ℕ) - RoomFunctions.scaleDepth T.side room d) - 1| ≤ 2 * v d
      linarith
    · intro K β hw d hd hdp
      have hK := hdeep K d hdp
      obtain ⟨w1, -, w3, w4, -⟩ := hWv d hd
      have h := hdepth K β hw d hd hK
      have hc := abs_one_div_sub_one_le (by linarith) h
      have hxp : 0 < D.coupling β ((K : ℕ) - RoomFunctions.scaleDepth T.side room d) := by
        have := hhalf K β hw d hd hK
        linarith
      have e1 : (flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 * Real.log (1 / d) /
          oneLoopCoeff - 1 = 1 / (D.coupling β ((K : ℕ) - RoomFunctions.scaleDepth T.side room d) / W d) - 1 := by
        have e2 : (flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 =
            (D.coupling β ((K : ℕ) - RoomFunctions.scaleDepth T.side room d))⁻¹ := rpow_neg_half_sq_eq_inv hxp
        rw [e2, haN]
        show _ = 1 / (_ / (sl * Real.log (1 / d))) - 1
        field_simp
      rw [e1]
      exact hc
  refine ⟨d₀, fun d => 2 * v d, fun d => 100 * v d, ?_, hsharp⟩
  refine ⟨hroom, fun M => ⟨M + 1, by omega, M + 1, by omega, rfl⟩, hH.lam_pos,
    ⟨hd₀, by linarith⟩, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro K β hw
    have hw' : β ∈ D.passageWindow K g := hw
    obtain ⟨-, -, hp⟩ := hdatum K β hw'
    have hlam := hH.lam_pos
    have hup := hp.upper_bound
    have h1 : ((K : ℕ) : ℝ) - 1 ≤ (β - g ^ (-2 : ℤ) - D.shift + D.c₅) / D.lam := by linarith
    rw [le_div_iff₀ hlam] at h1
    rw [le_div_iff₀ hlam]
    linarith only [h1, hg2, hBs]
  · intro K β hw d hd hdp
    have hK := hdeep K d hdp
    obtain ⟨w1, -⟩ := hWv d hd
    have h3 := hhalf K β hw d hd hK
    have hxp : 0 < D.coupling β ((K : ℕ) - RoomFunctions.scaleDepth T.side room d) := by linarith
    exact Real.rpow_pos_of_pos hxp _
  · intro K β hw d hd hdp
    have hh : |(flowProfile (T.stepParameters y) g D.shift room al).fieldNorm K β d - 1| ≤ 2 * v d :=
      hsharp.fieldNorm_le K β hw d hd hdp
    obtain ⟨-, -, w3, w4, -⟩ := hWv d hd
    have h2 := abs_le.1 hh
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro K β hw m hm d hd hdp f h hfh
    obtain ⟨ε, hε, heq⟩ := hlawp K β hw m hm d hd hdp f h hfh
    obtain ⟨-, -, w3, w4, -⟩ := hWv d hd
    exact ⟨ε, by linarith, heq⟩
  · intro K β hw d hd hdp
    have hh : |(flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 * Real.log (1 / d) /
        oneLoopCoeff - 1| ≤ 2 * v d := hsharp.log_le K β hw d hd hdp
    obtain ⟨-, -, w3, w4, -⟩ := hWv d hd
    have h2 := abs_le.1 hh
    have h3 : (flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 * Real.log (1 / d) =
        ((flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 * Real.log (1 / d) /
          oneLoopCoeff) * oneLoopCoeff := by field_simp
    rw [h3]
    refine ⟨?_, ?_⟩
    · have : 2 / 3 ≤ (flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 * Real.log (1 / d) /
          oneLoopCoeff := by linarith [h2.1]
      exact mul_le_mul_of_nonneg_right this haNpos.le
    · have : (flowProfile (T.stepParameters y) g D.shift room al).coupling K β d ^ 2 * Real.log (1 / d) /
          oneLoopCoeff ≤ 4 / 3 := by linarith [h2.2]
      exact mul_le_mul_of_nonneg_right this haNpos.le
private theorem coldResponseChain_congr (ℓ : StepParameters) (β : ℝ) (x : ℕ → ℝ) {a a' : ℕ → ℝ} (t : ℕ)
    (h : ∀ i < t, a i = a' i) : coldResponseChain ℓ β x a t = coldResponseChain ℓ β x a' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [coldResponseChain]
    rw [ih fun i hi => h i (by omega), h t (by omega)]
private theorem IsChainResponseCoeff.congr {ℓ : StepParameters} {Kr : ResponseParameters} {β : ℝ} {k : ℕ}
    {a a' : ℕ → ℝ} (h : IsChainResponseCoeff ℓ Kr β k a) (hh : ∀ i ≤ k, a i = a' i) :
    IsChainResponseCoeff ℓ Kr β k a' := by
  refine ⟨by rw [← hh 0 (Nat.zero_le _)]; exact h.zero_eq, fun j hj => ?_⟩
  rw [← hh j hj, ← coldResponseChain_congr ℓ β (flowCouplings ℓ β) j fun i hi => hh i (by omega)]
  exact h.bounds j hj
private theorem IsChainResponseCoeff.of_le {ℓ : StepParameters} {Kr : ResponseParameters} {β : ℝ} {k j : ℕ}
    {a : ℕ → ℝ} (h : IsChainResponseCoeff ℓ Kr β k a) (hj : j ≤ k) : IsChainResponseCoeff ℓ Kr β j a :=
  ⟨h.zero_eq, fun i hi => h.bounds i (hi.trans hj)⟩
end FlowDataLaws
open FlowDataLaws in
theorem lawsAtFlowData_holds (hN : cumulantLawsAlongFlow) (hP : gaussianTwoPointPair)
    (hT : TrajectoryData.responseCoeffNearOneStatement) (hU : ResponseInTheExpansion.chainResponseCoeffsUnique)
    (hS : ObjectsAreWellFormed) (hF : LinearResponse.FreeKernelPositiveOnSeparatedPairs)
    (hC : ConnectedFunctions.CentredIdentityAtAllFunctions) :
    lawsAtFlowDataStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hN a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hT a ha
  obtain ⟨L₃, r₃, C₃, hr₃, H₃⟩ := hU a ha
  refine ⟨max (max L₁ L₂) (max L₃ 2), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hL hLL Tb hTa hTL hTd hTc hTh hTrt hTC
  have l1 : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hLL)
  have l2 : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hLL)
  have l3 : L₃ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLL)
  have l4 : 2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLL)
  have t1 := hTrt.trans (min_le_left _ _)
  have t2 := hTrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t3 := hTrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  have c1 := (le_max_left C₁ (max C₂ C₃)).trans hTC
  have c2 := ((le_max_left C₂ C₃).trans (le_max_right C₁ _)).trans hTC
  have c3 := ((le_max_right C₂ C₃).trans (le_max_right C₁ _)).trans hTC
  obtain ⟨y₁, Y₁⟩ := H₁ L hL l1 Tb hTa hTL hTd hTc hTh t1 c1
  obtain ⟨Kr, hKr, y₂, Y₂⟩ := H₂ L hL l2 Tb hTa hTL hTd hTc hTh t2 c2
  obtain ⟨y₃, Y₃⟩ := H₃ L hL l3 Tb hTa hTL hTd hTc hTh t3 c3
  refine ⟨max y₁ (max y₂ y₃), fun y hy hR hW => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : y₃ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  obtain ⟨Kr₁, hKr₁, hlaws⟩ := Y₁ y hy1 hR hW
  have hnear := Y₂ y hy2 hR hW
  have huniq := Y₃ y hy3 hR hW
  refine ⟨Kr, hKr y, fun D hDw => ?_⟩
  have hLr : (1 : ℝ) < Tb.side := by
    rw [hTL]
    exact_mod_cast (by omega : 1 < L)
  have hslope : 0 < CouplingFlow.slopeConst Tb.side := by
    have h1 : 0 < Real.log Tb.side := Real.log_pos hLr
    unfold CouplingFlow.slopeConst
    positivity
  have hlamR : 0 < D.rateBound := by
    show 0 < 3 / 4 * CouplingFlow.slopeConst Tb.side
    positivity
  have hhold := (hDw (2 * Tb.B) D.rateBound le_rfl hlamR le_rfl).1
  have hyX : y ≤ D.X₀ := hhold.errorMargin.floor_le
  have hXy : D.X₀ ≤ D.floorStar := (le_max_left _ _).trans (le_max_left _ _)
  classical
  let Ca : ℝ := 6 * Kr.Cstar / (3 / 4 * CouplingFlow.slopeConst Tb.side)
  have hCa : 0 ≤ Ca := by
    have := (hKr y).Cstar_nonneg
    positivity
  let Pk : ℝ → ℕ → Prop := fun β k => ∀ j ≤ k, y ≤ flowCouplings (Tb.stepParameters y) β j
  let pick : ℝ → ℕ → ℕ → ℝ := fun β k => if h : Pk β k then (hnear β k h).choose else fun _ => 0
  have hpick : ∀ β k, Pk β k → IsChainResponseCoeff (Tb.stepParameters y) Kr β k (pick β k) ∧
      |pick β k k - 1| ≤ Ca * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2) : ℝ) := by
    intro β k h
    have e : pick β k = (hnear β k h).choose := dif_pos h
    rw [e]
    exact ⟨(hnear β k h).choose_spec.1, (hnear β k h).choose_spec.2.1⟩
  let al : ℝ → ℕ → ℝ := fun β j => pick β j j
  have hPj : ∀ β k, Pk β k → ∀ j ≤ k, Pk β j := fun β k h j hj i hi => h i (hi.trans hj)
  have hagree : ∀ β k, Pk β k → ∀ j ≤ k, pick β k j = al β j := by
    intro β k h j hj
    exact huniq Kr Kr (hKr y) (hKr y) β j _ _ (hPj β k h j hj)
      (IsChainResponseCoeff.of_le (hpick β k h).1 hj) (hpick β j (hPj β k h j hj)).1 j le_rfl
  have hchain : ∀ β k, Pk β k → IsChainResponseCoeff (Tb.stepParameters y) Kr β k (al β) := fun β k h =>
    IsChainResponseCoeff.congr (hpick β k h).1 (hagree β k h)
  refine ⟨al, fun β k h => hchain β k fun j hj => ?_, ?_⟩
  · have h1 : D.floorStar ≤ (couplingFlow (Tb.stepParameters y) β j).1 := h j hj
    exact hyX.trans (hXy.trans h1)
  · intro Bs lam hBs hl hlr vt hvt hvt1 g hg hgy room hroom
    obtain ⟨hHold, hData⟩ := hDw Bs lam hBs hl hlr
    obtain ⟨C, X, hCX⟩ := hlaws vt hvt hvt1
    have hnear' : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, y ≤ (D.withShift Bs lam).coupling β j) →
        |al β k - 1| ≤ Ca * (D.withShift Bs lam).coupling β k ^ (-(1 / 2) : ℝ) := fun β k h => (hpick β k h).2
    have hlaw' : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, X ≤ (D.withShift Bs lam).coupling β j) →
        (∀ j ≤ k, y ≤ (D.withShift Bs lam).coupling β j) → ∀ (K m : ℕ) (d e : ℝ),
        Real.exp (Real.log ((D.withShift Bs lam).coupling β k) ^ 3) ≤ torusSide Tb.side m / levelMesh Tb.side K k →
        IsLevelWindow (Tb.stepParameters y) ((D.withShift Bs lam).coupling β k) k (d / levelMesh Tb.side K k) e →
        CumulantLawsOnTorus (Tb.stepParameters y) vt C ((D.withShift Bs lam).coupling β k) (al β k) e β K m d := by
      intro β k hX hy' K m d e h1 h2
      obtain ⟨a', ha', -, -, hl'⟩ := hCX β k hX
      have heq : a' k = al β k :=
        huniq Kr₁ Kr hKr₁ (hKr y) β k _ _ hy' ha' (hchain β k hy') k le_rfl
      rw [← heq]
      exact hl' K m d e h1 h2
    obtain ⟨d₀, η, ε, h1, h2⟩ := fourPointLaws_of_trajectoryData hS hP hF hC (D.withShift Bs lam) hHold hData al Ca hCa
      hnear' vt hvt hvt1 C X hlaw' g hg hgy room hroom
    refine ⟨d₀, η, ε, h1, h2, fun K₀ => ?_⟩
    obtain ⟨K, hK, -, β, hβ⟩ := (hData.members g hg hgy).2.2 K₀
    exact ⟨⟨K, by omega⟩, β, hK, hβ⟩
end FourPointCondition
end YangMills.Construction
end
