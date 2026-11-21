import YangMills.Construction.CellOfTheFlow.LongClassesAreRareProof
import YangMills.Construction.LawInAState.MarksOnTheBoxProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusLumps StepReturn ResponseInTheExpansion Filter Topology
private theorem expansionCoupling_spec {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem couplingFlow_hasExpansion {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ) :
    (∀ j < t, ℓ.y₁ ≤ flowCouplings ℓ β j) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.SharedProofs.p48744 <;> assumption
private theorem abs_flowCouplings_succ_sub_le {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) {K : ℕ} (hfl : ∀ j ≤ K, ℓ.y₁ ≤ flowCouplings ℓ β j)
    {t : ℕ} (ht : t < K) : |flowCouplings ℓ β (t + 1) - flowCouplings ℓ β t| ≤ 2 * ℓ.B :=
  (expansionCoupling_spec hR (hfl t ht.le)
    (couplingFlow_hasExpansion hR h0 t fun j hj => hfl j (hj.trans ht).le)).2
private theorem clusterRange_mono {x z : ℝ} (hx : 0 ≤ x) (h : x ≤ z) :
    clusterRange x ≤ clusterRange z := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem clusterRange_pos {x : ℝ} (hx : 0 < x) : 0 < clusterRange x := by
  unfold clusterRange
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx _)
private theorem clusterRange_le_two_mul {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (h : z ≤ 2 ^ 100 * x) :
    clusterRange z ≤ 2 * clusterRange x := by
  have h2 : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h1 : z ^ ((1 : ℝ) / 100) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
    calc z ^ ((1 : ℝ) / 100) ≤ (2 ^ 100 * x) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow hz h (by norm_num)
      _ = 2 * x ^ ((1 : ℝ) / 100) := by
          rw [Real.mul_rpow (by positivity) hx, h2]
  unfold clusterRange
  rw [Nat.ceil_le]
  push_cast
  have := Nat.le_ceil (x ^ ((1 : ℝ) / 100))
  linarith
private theorem clusterRange_le_add_one {z : ℝ} (hz : 1 ≤ z) : (clusterRange z : ℝ) ≤ z + 1 := by apply _root_.YangMills.SharedProofs.p37996 <;> assumption
private theorem exists_clusterRange_le_pow {L : ℕ} (hL : 2 ≤ L) {Ξ B d : ℝ} (hΞ : 1 ≤ Ξ) (hB : 0 < B)
    (hd : 0 < d) : ∃ i : ℕ, 2 ^ 12 * (clusterRange (Ξ + 2 * B * i) : ℝ) ≤ d * (L : ℝ) ^ i := by
  set A : ℝ := 2 ^ 12 * (Ξ + 1 + 2 * B) / d with hA
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := (2 : ℝ)) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ 1 / (2 : ℝ) ^ n) < 1 / (A + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨i, hi, hi1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  refine ⟨i, ?_⟩
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hpow : (0 : ℝ) < 2 ^ i := by positivity
  have hAi : (A + 1) * i < 2 ^ i := by
    rw [pow_one, div_lt_div_iff₀ hpow (by positivity)] at hi
    linarith
  have hLi : (2 : ℝ) ^ i ≤ (L : ℝ) ^ i :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL) i
  have hz : 1 ≤ Ξ + 2 * B * i := by
    have : 0 ≤ 2 * B * (i : ℝ) := by positivity
    linarith
  have hr := clusterRange_le_add_one hz
  have hstep : Ξ + 2 * B * i + 1 ≤ (Ξ + 1 + 2 * B) * i := by
    nlinarith
  have hAd : A * d = 2 ^ 12 * (Ξ + 1 + 2 * B) := by
    rw [hA]; field_simp
  calc 2 ^ 12 * (clusterRange (Ξ + 2 * B * i) : ℝ) ≤ 2 ^ 12 * ((Ξ + 1 + 2 * B) * i) := by
        have : (clusterRange (Ξ + 2 * B * i) : ℝ) ≤ (Ξ + 1 + 2 * B) * i := hr.trans hstep
        linarith
    _ = d * (A * i) := by rw [← mul_assoc, ← hAd]; ring
    _ ≤ d * (L : ℝ) ^ i := by
        apply mul_le_mul_of_nonneg_left _ hd.le
        have : A * i ≤ (A + 1) * i := by nlinarith
        linarith
open Classical in
private theorem separationLevel_spec_of_admissible {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (hBy : ℓ.B ≤ ℓ.y₁) (hR : ExpansionReturnsAt ℓ)
    {Ξ d : ℝ} (hΞ : ℓ.y₁ + 2 * ℓ.B ≤ Ξ) (hd0 : 0 < d) (hd1 : d < 1) {K : ℕ} {β : ℝ}
    (hdat : IsFlowDatum ℓ Ξ K β) (hcut : minimalCutoff ℓ Ξ d ≤ K)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    IsSeparatedAt ℓ β K d (separationLevel ℓ β K d) ∧ separationLevel ℓ β K d < K ∧
      lengthInSites ℓ.side K (separationLevel ℓ β K d) d ≤
        2 ^ 13 * (ℓ.side : ℝ) * (clusterRange (couplingAtSeparation ℓ β K d) : ℝ) := by
  have hy1 : 1 ≤ ℓ.y₁ := hfit.y₁_ge
  have hB0 : 0 < ℓ.B := hfit.B_pos
  have hL2 : 2 ≤ ℓ.side := le_trans (by norm_num) hfit.L_ge
  have hLpos : (0 : ℝ) < ℓ.side := by
    have : (2 : ℝ) ≤ ℓ.side := by exact_mod_cast hL2
    linarith
  have hΞ1 : 1 ≤ Ξ := by linarith
  have hstep : ∀ {t : ℕ}, t < K → |flowCouplings ℓ β (t + 1) - flowCouplings ℓ β t| ≤ 2 * ℓ.B :=
    fun ht => abs_flowCouplings_succ_sub_le hR h0 hdat.le_coupling ht
  have hne : {i : ℕ | 2 ^ 12 * (clusterRange (Ξ + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i}.Nonempty :=
    exists_clusterRange_le_pow hL2 hΞ1 hB0 hd0
  obtain ⟨i, hidef⟩ : ∃ i, i = sInf {i : ℕ | 2 ^ 12 * (clusterRange (Ξ + 2 * ℓ.B * i) : ℝ) ≤
      d * (ℓ.side : ℝ) ^ i} :=
    ⟨_, rfl⟩
  have hi : 2 ^ 12 * (clusterRange (Ξ + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i := by
    rw [hidef]; exact Nat.sInf_mem hne
  have hiK : i ≤ K := by
    rw [hidef]; exact le_trans (le_max_right _ _) hcut
  have hdown : ∀ j : ℕ, j ≤ K → flowCouplings ℓ β (K - j) ≤ flowCouplings ℓ β K + 2 * ℓ.B * j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep (t := K - (j + 1)) (by omega)
      have e : K - (j + 1) + 1 = K - j := by omega
      rw [e] at h2
      have h3 := (abs_le.mp h2).1
      push_cast
      linarith
  have hfar : IsSeparatedAt ℓ β K d (K - i) := by
    have hx0 : 0 ≤ flowCouplings ℓ β (K - i) := by
      have := hdat.le_coupling (K - i) (Nat.sub_le _ _)
      linarith
    have hle : flowCouplings ℓ β (K - i) ≤ Ξ + 2 * ℓ.B * i := by
      have := hdown i hiK
      have := hdat.coupling_le_top
      linarith
    have hr : (clusterRange (flowCouplings ℓ β (K - i)) : ℝ) ≤ clusterRange (Ξ + 2 * ℓ.B * i) := by
      exact_mod_cast clusterRange_mono hx0 hle
    unfold IsSeparatedAt lengthInSites
    have e : K - (K - i) = i := by omega
    rw [e]
    linarith
  have hk : IsSeparatedAt ℓ β K d (separationLevel ℓ β K d) := by
    unfold separationLevel
    exact Nat.findGreatest_spec (Nat.sub_le K i) hfar
  have hkle : separationLevel ℓ β K d ≤ K := by
    unfold separationLevel
    exact Nat.findGreatest_le K
  have hlt : separationLevel ℓ β K d < K := by
    rcases hkle.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h] at hk
      unfold IsSeparatedAt lengthInSites at hk
      have hxK : 0 < flowCouplings ℓ β K := by
        have := hdat.le_coupling K le_rfl
        linarith
      have hr : (1 : ℝ) ≤ clusterRange (flowCouplings ℓ β K) := by
        exact_mod_cast clusterRange_pos hxK
      simp only [Nat.sub_self, pow_zero, mul_one] at hk
      linarith
  refine ⟨hk, hlt, ?_⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = separationLevel ℓ β K d := ⟨_, rfl⟩
  have hnot : ¬ IsSeparatedAt ℓ β K d (k + 1) := by
    rw [hkdef]
    unfold separationLevel
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hlt
  unfold couplingAtSeparation
  rw [← hkdef] at hlt ⊢
  have hfail : lengthInSites ℓ.side K (k + 1) d <
      2 ^ 12 * (clusterRange (flowCouplings ℓ β (k + 1)) : ℝ) := by
    unfold IsSeparatedAt at hnot
    exact not_le.mp hnot
  have hsites : lengthInSites ℓ.side K k d = (ℓ.side : ℝ) * lengthInSites ℓ.side K (k + 1) d := by
    unfold lengthInSites
    have e : K - k = (K - (k + 1)) + 1 := by omega
    rw [e, pow_succ]
    ring
  have hxk : ℓ.y₁ ≤ flowCouplings ℓ β k := hdat.le_coupling k hlt.le
  have hxk1 : ℓ.y₁ ≤ flowCouplings ℓ β (k + 1) := hdat.le_coupling (k + 1) hlt
  have hup := (abs_le.mp (hstep hlt)).2
  have hdouble : (clusterRange (flowCouplings ℓ β (k + 1)) : ℝ) ≤
      2 * clusterRange (flowCouplings ℓ β k) := by
    have hbig : flowCouplings ℓ β (k + 1) ≤ 2 ^ 100 * flowCouplings ℓ β k := by
      have h3 : flowCouplings ℓ β (k + 1) ≤ 3 * flowCouplings ℓ β k := by linarith
      have h4 : 0 ≤ flowCouplings ℓ β k := by linarith
      have h5 : (3 : ℝ) ≤ 2 ^ 100 := by norm_num
      nlinarith
    exact_mod_cast clusterRange_le_two_mul (by linarith) (by linarith) hbig
  rw [hsites]
  calc (ℓ.side : ℝ) * lengthInSites ℓ.side K (k + 1) d
      ≤ (ℓ.side : ℝ) * (2 ^ 12 * (clusterRange (flowCouplings ℓ β (k + 1)) : ℝ)) :=
        mul_le_mul_of_nonneg_left hfail.le hLpos.le
    _ ≤ (ℓ.side : ℝ) * (2 ^ 12 * (2 * clusterRange (flowCouplings ℓ β k))) := by
        apply mul_le_mul_of_nonneg_left _ hLpos.le
        linarith
    _ = 2 ^ 13 * (ℓ.side : ℝ) * (clusterRange (flowCouplings ℓ β k) : ℝ) := by ring
theorem separationLevelStatement_holds : separationLevelStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hT _ _ _ _
  refine ⟨max T.floorMin T.B, ?_⟩
  intro y hy hret hwil Ξ hΞ d hd0 hd1 K β hdat hcut
  have hfit : (T.stepParameters y).Admissible := hT.fits y (le_trans (le_max_left _ _) hy)
  have hBy : (T.stepParameters y).B ≤ (T.stepParameters y).y₁ := le_trans (le_max_right _ _) hy
  have hβ : y ≤ β := hdat.le_coupling 0 (Nat.zero_le _)
  exact separationLevel_spec_of_admissible hfit hBy hret hΞ hd0 hd1 hdat hcut (hwil β hβ)
end YangMills.Construction.StateLaws
end
