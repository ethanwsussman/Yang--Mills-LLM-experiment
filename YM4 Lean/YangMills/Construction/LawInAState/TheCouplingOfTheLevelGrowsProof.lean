import YangMills.Construction.CellOfTheFlow.LongClassesAreRareProof
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusLumps StepReturn RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
private theorem expansionCoupling_spec {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem hasExpansion_couplingFlow {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    ∀ t : ℕ, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.SharedProofs.p3977 <;> assumption
private theorem couplingFlow_sub_le {ℓ : StepParameters} {β : ℝ} {K : ℕ}
    (hstep : ∀ t < K, |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B) :
    ∀ i ≤ K, (couplingFlow ℓ β (K - i)).1 ≤ (couplingFlow ℓ β K).1 + 2 * ℓ.B * i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hm : K - i = (K - (i + 1)) + 1 := by omega
    have h2 := hstep (K - (i + 1)) (by omega)
    rw [← hm] at h2
    have h3 := (abs_le.mp h2).1
    push_cast
    linarith
private theorem clusterRange_mono {x x' : ℝ} (h0 : 0 ≤ x) (h : x ≤ x') : clusterRange x ≤ clusterRange x' := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem one_le_clusterRange {x : ℝ} (h : 0 < x) : 1 ≤ clusterRange x :=
  Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos h _)
private theorem clusterRange_le {x : ℝ} (h : 1 ≤ x) : (clusterRange x : ℝ) ≤ x + 1 := by apply _root_.YangMills.SharedProofs.p37996 <;> assumption
private theorem exists_separating_depth {L : ℕ} (hL : 2 ≤ L) {Xi B d : ℝ} (hXi : 1 ≤ Xi) (hB : 0 ≤ B)
    (hd : 0 < d) :
    ∃ i : ℕ, 2 ^ 12 * (clusterRange (Xi + 2 * B * i) : ℝ) ≤ d * (L : ℝ) ^ i := by
  have hr : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have t0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  have t1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have t := (t0.const_mul (2 ^ 12 * (Xi + 1))).add (t1.const_mul (2 ^ 12 * (2 * B)))
  simp only [mul_zero, add_zero] at t
  obtain ⟨i, hi⟩ := (t.eventually (gt_mem_nhds hd)).exists
  refine ⟨i, ?_⟩
  have hp : (0 : ℝ) < (L : ℝ) ^ i := by positivity
  have hi' : 2 ^ 12 * (Xi + 1) + 2 ^ 12 * (2 * B) * (i : ℝ) < d * (L : ℝ) ^ i := by
    have e : 2 ^ 12 * (Xi + 1) * ((i : ℝ) ^ 0 / (L : ℝ) ^ i) +
        2 ^ 12 * (2 * B) * ((i : ℝ) ^ 1 / (L : ℝ) ^ i) =
        (2 ^ 12 * (Xi + 1) + 2 ^ 12 * (2 * B) * (i : ℝ)) / (L : ℝ) ^ i := by
      field_simp
    rw [e] at hi
    exact (div_lt_iff₀ hp).mp hi
  have hx : 1 ≤ Xi + 2 * B * i := by
    have : 0 ≤ 2 * B * (i : ℝ) := by positivity
    linarith
  have hrange := clusterRange_le hx
  nlinarith
private theorem isSeparatedAt_separationLevel {ℓ : StepParameters} {Xi d : ℝ} {K : ℕ} {β : ℝ}
    (hy : 1 ≤ ℓ.y₁) (hB : 0 ≤ ℓ.B) (hL : 2 ≤ ℓ.side) (hd : 0 < d) (hR : ExpansionReturnsAt ℓ)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (hXi : ℓ.y₁ + 2 * ℓ.B ≤ Xi) (hD : IsFlowDatum ℓ Xi K β)
    (hK : minimalCutoff ℓ Xi d ≤ K) :
    IsSeparatedAt ℓ β K d (separationLevel ℓ β K d) := by
  have hne : {i : ℕ | 2 ^ 12 * (clusterRange (Xi + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i}.Nonempty :=
    exists_separating_depth hL (by linarith) hB hd
  have hmem := Nat.sInf_mem hne
  have hiK : sInf {i : ℕ | 2 ^ 12 * (clusterRange (Xi + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i} ≤ K :=
    (le_max_right _ _).trans hK
  generalize sInf {i : ℕ | 2 ^ 12 * (clusterRange (Xi + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i} = i
    at hmem hiK
  have hmem' : 2 ^ 12 * (clusterRange (Xi + 2 * ℓ.B * i) : ℝ) ≤ d * (ℓ.side : ℝ) ^ i := hmem
  have hstep : ∀ t < K, |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := fun t ht =>
    (expansionCoupling_spec hR (hD.le_coupling t ht.le)
      (hasExpansion_couplingFlow hR h0 t fun j hj => hD.le_coupling j (hj.le.trans ht.le))).2
  have hbelow := couplingFlow_sub_le hstep i hiK
  have htop : (couplingFlow ℓ β K).1 ≤ Xi := hD.coupling_le_top
  have hpos : 0 ≤ flowCouplings ℓ β (K - i) := by
    have := hD.le_coupling (K - i) (Nat.sub_le K i)
    linarith
  have hmono : clusterRange (flowCouplings ℓ β (K - i)) ≤ clusterRange (Xi + 2 * ℓ.B * i) :=
    clusterRange_mono hpos (by show (couplingFlow ℓ β (K - i)).1 ≤ _; linarith)
  have hfar : IsSeparatedAt ℓ β K d (K - i) := by
    unfold IsSeparatedAt lengthInSites
    rw [Nat.sub_sub_self hiK]
    have : (clusterRange (flowCouplings ℓ β (K - i)) : ℝ) ≤ clusterRange (Xi + 2 * ℓ.B * i) := by
      exact_mod_cast hmono
    linarith
  unfold separationLevel
  classical exact Nat.findGreatest_spec (Nat.sub_le K i) hfar
private theorem le_couplingAtSeparation {ℓ : StepParameters} {lam c₅ : ℝ} (hlam : 0 < lam) (hy : 1 ≤ ℓ.y₁)
    (hB : 0 ≤ ℓ.B) (hL : 2 ≤ ℓ.side) (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β))
    (hs : HasLinearDescent ℓ lam c₅) (Xi : ℝ) (hXi : ℓ.y₁ + 2 * ℓ.B ≤ Xi) (X : ℝ) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ d : ℝ, 0 < d → d ≤ d₁ → ∀ (K : ℕ) (β : ℝ), IsFlowDatum ℓ Xi K β →
      minimalCutoff ℓ Xi d ≤ K → X ≤ couplingAtSeparation ℓ β K d := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((X + c₅ - ℓ.y₁) / lam)
  have hL1 : (1 : ℝ) ≤ ℓ.side := by exact_mod_cast (by omega : 1 ≤ ℓ.side)
  refine ⟨1 / (2 * (ℓ.side : ℝ) ^ N), by positivity, ?_⟩
  intro d hd hd₁ K β hD hK
  have hβ : ℓ.y₁ ≤ β := hD.le_coupling 0 (Nat.zero_le K)
  have hfar := isSeparatedAt_separationLevel hy hB hL hd hR (hW β hβ) hXi hD hK
  have hkK : separationLevel ℓ β K d ≤ K := by
    unfold separationLevel
    classical exact Nat.findGreatest_le K
  unfold couplingAtSeparation
  generalize separationLevel ℓ β K d = k at hfar hkK
  have hxk : 0 < flowCouplings ℓ β k := by
    have := hD.le_coupling k hkK
    linarith
  have hr1 : (1 : ℝ) ≤ clusterRange (flowCouplings ℓ β k) := by exact_mod_cast one_le_clusterRange hxk
  have hbig : 1 ≤ d * (ℓ.side : ℝ) ^ (K - k) := by
    unfold IsSeparatedAt lengthInSites at hfar
    linarith
  have hNk : N ≤ K - k := by
    by_contra hlt
    have hle : (ℓ.side : ℝ) ^ (K - k) ≤ (ℓ.side : ℝ) ^ N := pow_le_pow_right₀ hL1 (by omega)
    have h2 : d * (2 * (ℓ.side : ℝ) ^ N) ≤ 1 := (le_div_iff₀ (by positivity)).mp hd₁
    have h3 : d * (ℓ.side : ℝ) ^ (K - k) ≤ d * (ℓ.side : ℝ) ^ N := mul_le_mul_of_nonneg_left hle hd.le
    linarith
  have hsl := hs β hβ K (fun j hj => hD.le_coupling j hj.le) k hkK
  have hcast : (N : ℝ) ≤ (K : ℝ) - k := by
    rw [← Nat.cast_sub hkK]
    exact_mod_cast hNk
  have hlamN : X + c₅ - ℓ.y₁ ≤ lam * N := by
    have := (div_le_iff₀ hlam).mp hN
    linarith
  have hmul : lam * N ≤ lam * ((K : ℝ) - k) := mul_le_mul_of_nonneg_left hcast hlam.le
  have hfloor : ℓ.y₁ ≤ (couplingFlow ℓ β K).1 := hD.le_coupling K le_rfl
  show X ≤ (couplingFlow ℓ β k).1
  linarith
theorem couplingAtSeparation_tendsto (hS : FlowDescendsLinearly) :
    couplingAtSeparation_tendsto_statement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, hS'⟩ := hS a ha
  refine ⟨L₀, rt₀, 0, hrt, ?_⟩
  intro L hLodd hL₀ T hTa hTL hD _ _ hrtT _
  obtain ⟨lam, c₅, hlam, hT⟩ := hS' L hLodd hL₀
  obtain ⟨y₀, hy₀⟩ := hT T hTa hTL hD hrtT
  refine ⟨max y₀ 1, ?_⟩
  intro y hy hR hW Xi hXi X
  have hslope := hy₀ y ((le_max_left _ _).trans hy) hR hW
  have hy1 : 1 ≤ (T.stepParameters y).y₁ := (le_max_right _ _).trans hy
  have hB : 0 ≤ (T.stepParameters y).B := le_trans zero_le_one hD.B_ge
  have hL : 2 ≤ (T.stepParameters y).side := le_trans (by norm_num) hD.L_ge
  exact le_couplingAtSeparation hlam hy1 hB hL hR hW hslope Xi hXi X
end YangMills.Construction.StateLaws
end
