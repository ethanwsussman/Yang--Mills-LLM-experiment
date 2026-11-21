import YangMills.ContinuumLimit.RunAboveTheFloor
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import YangMills.Construction.WindowOfTheParameters.FirstPassageOfASequenceForm
set_option autoImplicit false

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.ResponseInTheExpansion

def IsTunedAt (T : RenormalizationStepParameters.ParameterAssignment) (y P : ℝ) (K : ℕ) (β : ℝ) : Prop :=
  (y ≤ β ∧ ∀ j < K, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) ∧
    TotalDensityFlow.coupling (T.stepParameters y) β K = P

def runDepth (lam c₅ : ℝ) : ℕ := ⌈|c₅| / lam⌉₊ + 1

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : WeightedResponses.ResponseParameters} {lam c₅ : ℝ}

namespace FirstPassageOfATunedPair

theorem abs_le_mul_ceil (hlam : 0 < lam) : |c₅| ≤ lam * (⌈|c₅| / lam⌉₊ : ℝ) := by
  have h1 : |c₅| / lam ≤ (⌈|c₅| / lam⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hlam] at h1
  linarith

theorem lt_mul_runDepth (hlam : 0 < lam) : c₅ < lam * (runDepth lam c₅ : ℝ) := by
  have h2 := abs_le_mul_ceil (c₅ := c₅) hlam
  have h3 : c₅ ≤ |c₅| := le_abs_self c₅
  unfold runDepth
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  linarith

theorem sub_lt_runDepth (hlam : 0 < lam) {K K' : ℕ} (hle : K' ≤ K)
    (h : lam * ((K : ℝ) - K') - c₅ ≤ 0) : K - K' < runDepth lam c₅ := by
  have hc : ((K - K' : ℕ) : ℝ) = (K : ℝ) - K' := by
    rw [Nat.cast_sub hle]
  have h1 : ((K - K' : ℕ) : ℝ) ≤ |c₅| / lam := by
    rw [le_div_iff₀ hlam, hc]
    have := le_abs_self c₅
    linarith
  have h2 : K - K' ≤ ⌈|c₅| / lam⌉₊ := by
    exact_mod_cast h1.trans (Nat.le_ceil _)
  unfold runDepth
  omega

end FirstPassageOfATunedPair

theorem tuned_first_passage_index (hGives : TotalDensityFlow.ExpansionGivesFlow)
    (hUniq : TotalDensityFlow.FlowIsUnique) (h : RunTable T y Kr lam c₅) {P : ℝ} {K : ℕ} {β : ℝ}
    (hβ : IsTunedAt T y P K β) (hK : runDepth lam c₅ ≤ K) (Bs g : ℝ)
    (hP : SequencePassage.passageThreshold Bs g = P) :
    ∃ K' : ℕ, 1 ≤ K' ∧ K' ≤ K ∧ K - K' < runDepth lam c₅ ∧
      TotalDensitySystem.IsFirstPassageDatum (T.stepParameters y) Bs g K' β := by
  classical
  subst hP
  obtain ⟨hcl, hKP⟩ := hβ
  have hA : Above T y β K := (above_iff_total hGives hUniq h).mp hcl
  have heK := (total_flow_of_above_total hGives hUniq h hcl).2
  have hxK : flowCouplings (T.stepParameters y) β K = SequencePassage.passageThreshold Bs g := by
    rw [← heK K le_rfl]
    exact hKP
  have hdesc : ∀ i ≤ K, lam * ((K : ℝ) - i) - c₅ ≤
      flowCouplings (T.stepParameters y) β i - SequencePassage.passageThreshold Bs g := by
    intro i hi
    have hd := h.descent β hA.1 K hA.2 i hi
    rw [← hxK]
    exact hd
  have hpos : c₅ < lam * K := by
    have h1 := FirstPassageOfATunedPair.lt_mul_runDepth (c₅ := c₅) h.lam_pos
    have hK' : (runDepth lam c₅ : ℝ) ≤ K := by exact_mod_cast hK
    have h2 := mul_le_mul_of_nonneg_left hK' h.lam_pos.le
    linarith
  have h0 := hdesc 0 (Nat.zero_le K)
  have hx0 : flowCouplings (T.stepParameters y) β 0 = β := rfl
  rw [hx0, Nat.cast_zero, sub_zero] at h0
  have hβP : SequencePassage.passageThreshold Bs g < β := by linarith
  have hc0 : TotalDensityFlow.coupling (T.stepParameters y) β 0 = β := by
    rw [heK 0 (Nat.zero_le K)]
    exact hx0
  have hex : ∃ k, TotalDensityFlow.coupling (T.stepParameters y) β k ≤ SequencePassage.passageThreshold Bs g :=
    ⟨K, hKP.le⟩
  obtain ⟨K', hK'spec, hK'min⟩ : ∃ K', TotalDensityFlow.coupling (T.stepParameters y) β K' ≤
      SequencePassage.passageThreshold Bs g ∧
      ∀ k < K', SequencePassage.passageThreshold Bs g < TotalDensityFlow.coupling (T.stepParameters y) β k :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_le.mp (Nat.find_min hex hk)⟩
  have hK'le : K' ≤ K := by
    by_contra hlt
    have := hK'min K (not_le.mp hlt)
    rw [hKP] at this
    exact lt_irrefl _ this
  have hK'one : 1 ≤ K' := by
    by_contra hlt
    have hK'0 : K' = 0 := by omega
    rw [hK'0, hc0] at hK'spec
    linarith
  have hdK' := hdesc K' hK'le
  have hxK' : flowCouplings (T.stepParameters y) β K' ≤ SequencePassage.passageThreshold Bs g := by
    rw [← heK K' hK'le]
    exact hK'spec
  have hdef : TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β K' :=
    (total_flow_of_above_total hGives hUniq h
      ⟨hcl.1, fun j hj => hcl.2 j (lt_of_lt_of_le hj hK'le)⟩).1
  refine ⟨K', hK'one, hK'le, FirstPassageOfATunedPair.sub_lt_runDepth h.lam_pos hK'le (by linarith), ?_⟩
  unfold TotalDensitySystem.IsFirstPassageDatum SequencePassage.definedPassageWindow
    SequencePassage.passageWindow SequencePassage.IsFirstPassageIndex
  simp only [Set.mem_ofPred_eq]
  exact ⟨hdef, hβP.le, hK'spec, hK'min⟩

end YangMills.ContinuumLimit

end
