import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheLocalExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace LocalExpansion
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem torusDecayFactor_div_le {L : ℕ} {δ x x' : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxx' : 2 * x ≤ x') :
    torusDecayFactor L δ x / torusDecayFactor L δ x' ≤ Real.exp (-(δ * x)) := by
  have hroot : 0 < (L : ℝ) ^ (1 / 640 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hle : x ≤ x' := by linarith
  have hmax : max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) ≤ max 1 ((x' / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
    max_le_max le_rfl (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hle hroot.le) _)
  have hmaxpos : (0 : ℝ) < max 1 ((x' / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [div_le_iff₀ (torusDecayFactor_pos _ _ _)]
  unfold torusDecayFactor
  have heq : Real.exp (-(δ * x)) * (max 1 ((x' / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) * Real.exp (δ * x')) =
      max 1 ((x' / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) * Real.exp (δ * x' - δ * x) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [heq]
  refine mul_le_mul hmax (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hmaxpos.le
  nlinarith
theorem pow_mul_exp_neg_eventually_le (p : ℕ) {b q ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → q * ((r : ℝ) ^ p * Real.exp (-(b * r))) ≤ ε := by
  have hlim : Filter.Tendsto (fun x : ℝ => x ^ p * Real.exp (-(b * x))) Filter.atTop (𝓝 0) := by
    have hcomp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp (Filter.tendsto_id.const_mul_atTop hb)
    have hscaled := hcomp.const_mul ((b ^ p)⁻¹)
    simp only [mul_zero] at hscaled
    refine hscaled.congr fun x => ?_
    simp only [Function.comp, id]
    rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hnat := (hlim.comp tendsto_natCast_atTop_atTop).const_mul q
  simp only [mul_zero] at hnat
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hnat.eventually (gt_mem_nhds hε))
  exact ⟨N, fun r hr => (hN r hr).le⟩
end LocalExpansion
set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
open LocalExpansion in
theorem localExpansionParametersEventually_holds : LocalExpansionParametersEventually := by
  intro A a _
  refine ⟨16, fun L _ hL c hc => ?_⟩
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct _ => ⟨c.δ₂, hδ₂, fun κ hκ hκ0 => ⟨1, one_pos, fun η₃ hη _ _ => ?_⟩⟩⟩
  have hL1 : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  set δ : ℝ := κ / 2 ^ 10 with hδdef
  have hδ : 0 < δ := by positivity
  set Aa : ℝ := A a L c Ct with hAa
  set q : ℝ := (L : ℝ) ^ 4 * |Aa| with hq
  have hq0 : 0 ≤ q := by positivity
  have h512 : (0 : ℝ) < 2⁻¹ ^ 9 := by positivity
  obtain ⟨N₁, hN₁⟩ := pow_mul_exp_neg_eventually_le 0 (q := q) hδ h512
  obtain ⟨N₂, hN₂⟩ := pow_mul_exp_neg_eventually_le 16004 (b := c.δ₂ / 16) (q := q * (1 / η₃) * (7 * (L : ℝ)) ^ 4) (by positivity) h512
  obtain ⟨N₃, hN₃⟩ := pow_mul_exp_neg_eventually_le 0 (b := c.δ₂ / 8) (q := Ct) (ε := 1 / 64) (by positivity) (by norm_num)
  have key : ∀ r : ℕ, max (max 16 N₁) (max N₂ N₃) ≤ r → 16 ≤ r ∧ Ct * Real.exp (-(c.δ₂ / 8 * r)) ≤ 1 / 64 ∧
      (L : ℝ) ^ 4 * Aa * (1 / torusDecayFactor L δ ((L * (r / 4) : ℕ) : ℝ) +
        (1 / η₃) * (2 * ((L * (r / 4) : ℕ) : ℝ) + 5) ^ 4 * Real.exp (-(c.δ₂ / 8 * r))) ≤
        2⁻¹ ^ 8 / torusDecayFactor L δ r := by
    intro r hr
    have h16 : 16 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
    have hr1 : N₁ ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
    have hr2 : N₂ ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
    have hr3 : N₃ ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
    refine ⟨h16, ?_, ?_⟩
    · have := hN₃ r hr3
      simpa using this
    · set Rr : ℕ := L * (r / 4) with hRr
      have hRr2 : 2 * r ≤ Rr := by
        have h1 : 16 * (r / 4) ≤ L * (r / 4) := Nat.mul_le_mul_right _ hL
        have h2 : r ≤ 4 * (r / 4) + 3 := by omega
        omega
      have hrR : (2 : ℝ) * r ≤ (Rr : ℝ) := by exact_mod_cast hRr2
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
      set D := torusDecayFactor L δ r with hD
      set Dr := torusDecayFactor L δ (Rr : ℝ) with hDr
      have hDp : 0 < D := torusDecayFactor_pos _ _ _
      have hDrp : 0 < Dr := torusDecayFactor_pos _ _ _
      set e₁ := Real.exp (-(c.δ₂ / 8 * r)) with he₁
      have he₁p : 0 < e₁ := Real.exp_pos _
      have hη1 : 0 < 1 / η₃ := by positivity
      have h1 : q * (D / Dr) ≤ 2⁻¹ ^ 9 := by
        have a1 := torusDecayFactor_div_le hL1 hδ.le hr0 hrR
        have a2 := hN₁ r hr1
        simp only [pow_zero, one_mul] at a2
        exact (mul_le_mul_of_nonneg_left a1 hq0).trans a2
      have hRle : 2 * (Rr : ℝ) + 5 ≤ 7 * (L : ℝ) * r := by
        have h3 : (Rr : ℝ) ≤ (L : ℝ) * r := by
          have : Rr ≤ L * r := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
          exact_mod_cast this
        nlinarith
      have hP : (2 * (Rr : ℝ) + 5) ^ 4 ≤ (7 * (L : ℝ)) ^ 4 * (r : ℝ) ^ 4 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hRle 4
      have hn1 : 1 ≤ (L : ℝ) ^ (1 / 640 : ℝ) := Real.one_le_rpow hLr (by norm_num)
      have hDle : D ≤ (r : ℝ) ^ 16000 * Real.exp (δ * r) := by
        rw [hD]
        unfold torusDecayFactor
        refine mul_le_mul_of_nonneg_right (max_le (one_le_pow₀ hr1') ?_) (Real.exp_pos _).le
        refine pow_le_pow_left₀ (by positivity) ?_ _
        exact div_le_self hr0 hn1
      have hexp : Real.exp (δ * r) * e₁ ≤ Real.exp (-(c.δ₂ / 16 * r)) := by
        rw [he₁, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith
      have h2 : q * ((1 / η₃) * (2 * (Rr : ℝ) + 5) ^ 4 * e₁) * D ≤ 2⁻¹ ^ 9 := by
        have a2 := hN₂ r hr2
        refine le_trans ?_ a2
        have b1 : (2 * (Rr : ℝ) + 5) ^ 4 * (D * e₁) ≤
            ((7 * (L : ℝ)) ^ 4 * (r : ℝ) ^ 4) * ((r : ℝ) ^ 16000 * Real.exp (-(c.δ₂ / 16 * r))) := by
          refine mul_le_mul hP ?_ (mul_nonneg hDp.le he₁p.le) (by positivity)
          calc D * e₁ ≤ ((r : ℝ) ^ 16000 * Real.exp (δ * r)) * e₁ := mul_le_mul_of_nonneg_right hDle he₁p.le
            _ = (r : ℝ) ^ 16000 * (Real.exp (δ * r) * e₁) := by ring
            _ ≤ (r : ℝ) ^ 16000 * Real.exp (-(c.δ₂ / 16 * r)) :=
                mul_le_mul_of_nonneg_left hexp (pow_nonneg hr0 _)
        have e2 : q * (1 / η₃) * (7 * (L : ℝ)) ^ 4 * ((r : ℝ) ^ 16004 * Real.exp (-(c.δ₂ / 16 * r))) =
            q * (1 / η₃) * (((7 * (L : ℝ)) ^ 4 * (r : ℝ) ^ 4) * ((r : ℝ) ^ 16000 * Real.exp (-(c.δ₂ / 16 * r)))) := by
          have : (r : ℝ) ^ 16004 = (r : ℝ) ^ 4 * (r : ℝ) ^ 16000 := by rw [← pow_add]
          rw [this]
          ring
        rw [e2]
        calc q * ((1 / η₃) * (2 * (Rr : ℝ) + 5) ^ 4 * e₁) * D = q * (1 / η₃) * ((2 * (Rr : ℝ) + 5) ^ 4 * (D * e₁)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left b1 (mul_nonneg hq0 hη1.le)
      rw [le_div_iff₀ hDp]
      have hS0 : 0 ≤ 1 / Dr + (1 / η₃) * (2 * (Rr : ℝ) + 5) ^ 4 * e₁ :=
        add_nonneg (div_nonneg zero_le_one hDrp.le) (mul_nonneg (mul_nonneg hη1.le (pow_nonneg (by positivity) _)) he₁p.le)
      have hAq : (L : ℝ) ^ 4 * Aa ≤ q := by
        rw [hq]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      calc (L : ℝ) ^ 4 * Aa * (1 / Dr + (1 / η₃) * (2 * (Rr : ℝ) + 5) ^ 4 * e₁) * D
          ≤ q * (1 / Dr + (1 / η₃) * (2 * (Rr : ℝ) + 5) ^ 4 * e₁) * D :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAq hS0) hDp.le
        _ = q * (D / Dr) + q * ((1 / η₃) * (2 * (Rr : ℝ) + 5) ^ 4 * e₁) * D := by
            field_simp
        _ ≤ 2⁻¹ ^ 9 + 2⁻¹ ^ 9 := add_le_add h1 h2
        _ = 2⁻¹ ^ 8 := by norm_num
  refine ⟨max (max 16 N₁) (max N₂ N₃), fun blockIndex hn => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ =>
    ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩
  intro r hr
  exact key r (hn.trans hr)
end YangMills.Construction.ColdStepAtMirrorFrames
end
