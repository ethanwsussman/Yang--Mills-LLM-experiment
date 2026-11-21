import Mathlib
import YangMills.ContinuumLimit.TuningAtEveryCutoff
import YangMills.Construction.WindowOfTheParameters.FirstPassageOfASequenceForm
set_option autoImplicit false

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion

def OneStepDrops (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (t₀ : ℕ) (X₁ : ℝ) : Prop :=
  ∀ (β : ℝ) (t : ℕ), t₀ ≤ t → Run T y β t → X₁ ≤ flowCouplings (T.stepParameters y) β t →
    flowCouplings (T.stepParameters y) β (t + 1) < flowCouplings (T.stepParameters y) β t

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : ResponseParameters} {lam c₅ : ℝ}

namespace TunedPairsAreFirstPassages

theorem lt_of_drops {x : ℕ → ℝ} {t₀ K : ℕ} (hstep : ∀ l, t₀ ≤ l → l < K → x (l + 1) < x l)
    {k : ℕ} (hk : t₀ ≤ k) (hkK : k < K) : x K < x k := by
  have key : ∀ m, k + 1 ≤ m → m ≤ K → x m < x k := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun _ => hstep k hk hkK
    | succ m hm ih =>
      intro hmK
      have h1 := ih (by omega)
      have h2 := hstep m (by omega) (by omega)
      linarith
  exact key K (by omega) le_rfl

end TunedPairsAreFirstPassages

theorem tuned_is_first_passage (hGives : TotalDensityFlow.ExpansionGivesFlow)
    (hUniq : TotalDensityFlow.FlowIsUnique) (h : RunTable T y Kr lam c₅) {t₀ : ℕ} {X₁ : ℝ}
    (hdrop : OneStepDrops T y t₀ X₁) {K : ℕ} (hK : t₀ + runDepth lam c₅ ≤ K) {P : ℝ}
    (hP : X₁ + |c₅| ≤ P) {β : ℝ} (hβ : IsTunedAt T y P K β) (Bs g : ℝ)
    (hPg : SequencePassage.passageThreshold Bs g = P) :
    TotalDensitySystem.IsFirstPassageDatum (T.stepParameters y) Bs g K β := by
  obtain ⟨hcl, hKP⟩ := hβ
  have hA : Above T y β K := (above_iff_total hGives hUniq h).mp hcl
  have heK := (total_flow_of_above_total hGives hUniq h hcl).2
  have hdef := (total_flow_of_above_total hGives hUniq h hcl).1
  have hxK : flowCouplings (T.stepParameters y) β K = P := by
    rw [← heK K le_rfl]
    exact hKP
  have hdesc : ∀ i ≤ K, lam * ((K : ℝ) - i) - c₅ ≤ flowCouplings (T.stepParameters y) β i - P := by
    intro i hi
    have hd := h.descent β hA.1 K hA.2 i hi
    rw [← hxK]
    exact hd
  have hstep : ∀ l, t₀ ≤ l → l < K →
      flowCouplings (T.stepParameters y) β (l + 1) < flowCouplings (T.stepParameters y) β l := by
    intro l hl hlK
    have hrun : Run T y β l := fun j hj => hA.2 j (lt_of_le_of_lt hj hlK)
    have hd := hdesc l hlK.le
    have hKl : (0 : ℝ) ≤ (K : ℝ) - l := sub_nonneg.mpr (by exact_mod_cast hlK.le)
    have hm := mul_nonneg h.lam_pos.le hKl
    have hc := le_abs_self c₅
    exact hdrop β l hl hrun (by linarith)
  have habove : ∀ k < K, P < flowCouplings (T.stepParameters y) β k := by
    intro k hk
    by_cases hkt : t₀ ≤ k
    · have := TunedPairsAreFirstPassages.lt_of_drops hstep hkt hk
      rw [hxK] at this
      exact this
    · have hd := hdesc k hk.le
      have hlt := FirstPassageOfATunedPair.lt_mul_runDepth (c₅ := c₅) h.lam_pos
      have hr : (runDepth lam c₅ : ℝ) ≤ (K : ℝ) - k := by
        have h1 : runDepth lam c₅ ≤ K - k := by omega
        have h2 : ((K - k : ℕ) : ℝ) = (K : ℝ) - k := Nat.cast_sub hk.le
        rw [← h2]
        exact_mod_cast h1
      have hm := mul_le_mul_of_nonneg_left hr h.lam_pos.le
      linarith
  have hK1 : 0 < K := by
    have : 1 ≤ runDepth lam c₅ := by unfold runDepth; omega
    omega
  have hβP : P < β := habove 0 hK1
  show TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β K ∧
    (SequencePassage.passageThreshold Bs g ≤ β ∧
      (TotalDensityFlow.coupling (T.stepParameters y) β K ≤ SequencePassage.passageThreshold Bs g ∧
        ∀ k < K, SequencePassage.passageThreshold Bs g < TotalDensityFlow.coupling (T.stepParameters y) β k))
  rw [hPg]
  refine ⟨hdef, hβP.le, hKP.le, fun k hk => ?_⟩
  rw [heK k hk.le]
  exact habove k hk

theorem exists_unique_tuned_first_passage (hKd : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (hGives : TotalDensityFlow.ExpansionGivesFlow) (hUniq : TotalDensityFlow.FlowIsUnique)
    (h : RunTable T y Kr lam c₅) {t₀ : ℕ} {X₁ : ℝ} (hdrop : OneStepDrops T y t₀ X₁) {K : ℕ}
    (hK : t₀ + runDepth lam c₅ ≤ K) (Bs g : ℝ)
    (hP : max (runFloor T y c₅) (X₁ + |c₅|) ≤ SequencePassage.passageThreshold Bs g) :
    ∃! β, IsTunedAt T y (SequencePassage.passageThreshold Bs g) K β ∧
      TotalDensitySystem.IsFirstPassageDatum (T.stepParameters y) Bs g K β := by
  obtain ⟨⟨β, hβ, hu⟩, -⟩ :=
    (tuned_at_runFloor hKd hT hS hL hR hA hGives hUniq h K).2.2.2.1 _ (le_of_max_le_left hP)
  exact ⟨β, ⟨hβ, tuned_is_first_passage hGives hUniq h hdrop hK (le_of_max_le_right hP) hβ Bs g rfl⟩,
    fun β' hβ' => hu β' hβ'.1⟩

end YangMills.ContinuumLimit

end
