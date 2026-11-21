import Mathlib
import YangMills.ContinuumLimit.SlopeOfTheRun
import YangMills.ContinuumLimit.RunAboveTheFloor
import YangMills.ContinuumLimit.FamiliesOfIncreasingFunctions
import YangMills.ContinuumLimit.FirstPassageOfATunedPair
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion

def runFloor (T : RenormalizationStepParameters.ParameterAssignment) (y c₅ : ℝ) : ℝ :=
  y + 2 * T.B + |c₅| + 1

def TunedAtEveryCutoff (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∃ X₀ : ℝ, y ≤ X₀ ∧ ∀ K : ℕ,
    (∀ β : ℝ, (y ≤ β ∧ ∀ j < K, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) →
      TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β K ∧
        ∀ j ≤ K, TotalDensityFlow.coupling (T.stepParameters y) β j =
          flowCouplings (T.stepParameters y) β j) ∧
    ∃ I : Set ℝ,
      (IsOpen I ∧ IsUpperSet I ∧ I.Nonempty ∧
        (∀ β ∈ I, y ≤ β ∧ ∀ j < K + 1, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) ∧
        ∀ β ∈ I, TotalDensityFlow.coupling (T.stepParameters y) β K =
          flowCouplings (T.stepParameters y) β K) ∧
      (ContDiffOn ℝ 1 (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) I ∧
        StrictMonoOn (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) I ∧
        ∀ β ∈ I, 3 / 4 ≤ deriv (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) β ∧
          deriv (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) β ≤ 5 / 4) ∧
      ∀ P : ℝ, X₀ ≤ P → (∃! β, IsTunedAt T y P K β) ∧ ∀ β, IsTunedAt T y P K β → β ∈ I

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : ResponseParameters} {lam c₅ : ℝ}

namespace TuningAtEveryCutoff

theorem floor_lt (h : RunTable T y Kr lam c₅) : y < y + 2 * T.B := by
  have hB : 1 ≤ T.B := h.adm.B_ge
  linarith

theorem le_runFloor (h : RunTable T y Kr lam c₅) : y ≤ runFloor T y c₅ := by
  have hB : 1 ≤ T.B := h.adm.B_ge
  have hc : 0 ≤ |c₅| := abs_nonneg c₅
  unfold runFloor
  linarith

theorem run_descends (h : RunTable T y Kr lam c₅) :
    ∀ K β, stayingAbove y (runFlow T y) K β → ∀ i ≤ K, runFlow T y K β ≤ runFlow T y i β + c₅ := by
  intro K β hβ i hi
  have hd : lam * ((K : ℝ) - i) - c₅ ≤
      flowCouplings (T.stepParameters y) β i - flowCouplings (T.stepParameters y) β K :=
    h.descent β hβ.1 K hβ.2 i hi
  have hki : (0 : ℝ) ≤ (K : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hi)
  have hm := mul_nonneg h.lam_pos.le hki
  show flowCouplings (T.stepParameters y) β K ≤ flowCouplings (T.stepParameters y) β i + c₅
  linarith

theorem run_slope_near_one (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (h : RunTable T y Kr lam c₅) (j : ℕ) :
    HasSlopeNearOneAboveFloor (y + 2 * T.B) (runFlow T y) j :=
  ⟨fun β => runSlope T y Kr β j, (run_has_slope hK hT hS hL hR hA h j).2.2.2.1⟩

theorem isTunedAt_iff (hGives : TotalDensityFlow.ExpansionGivesFlow)
    (hUniq : TotalDensityFlow.FlowIsUnique) (h : RunTable T y Kr lam c₅) {P : ℝ} {K : ℕ} {β : ℝ} :
    IsTunedAt T y P K β ↔ stayingAbove y (runFlow T y) K β ∧ runFlow T y K β = P := by
  unfold IsTunedAt
  constructor
  · rintro ⟨hcl, hv⟩
    have hA : Above T y β K := (above_iff_total hGives hUniq h).mp hcl
    refine ⟨hA, ?_⟩
    show flowCouplings (T.stepParameters y) β K = P
    rw [← (total_flow_of_above_total hGives hUniq h hcl).2 K le_rfl]
    exact hv
  · rintro ⟨hA, hv⟩
    have hA' : Above T y β K := hA
    have hcl := (above_iff_total hGives hUniq h).mpr hA'
    refine ⟨hcl, ?_⟩
    rw [(total_flow_of_above_total hGives hUniq h hcl).2 K le_rfl]
    exact hv

end TuningAtEveryCutoff

theorem tuned_at_runFloor (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (hGives : TotalDensityFlow.ExpansionGivesFlow) (hUniq : TotalDensityFlow.FlowIsUnique)
    (h : RunTable T y Kr lam c₅) (K : ℕ) :
    (∀ β : ℝ, (y ≤ β ∧ ∀ j < K, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) →
      TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β K ∧
        ∀ j ≤ K, TotalDensityFlow.coupling (T.stepParameters y) β j =
          flowCouplings (T.stepParameters y) β j) ∧
    (IsOpen (runDomain T y K) ∧ IsUpperSet (runDomain T y K) ∧ (runDomain T y K).Nonempty ∧
      (∀ β ∈ runDomain T y K,
        y ≤ β ∧ ∀ j < K + 1, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) ∧
      ∀ β ∈ runDomain T y K, TotalDensityFlow.coupling (T.stepParameters y) β K =
        flowCouplings (T.stepParameters y) β K) ∧
    (ContDiffOn ℝ 1 (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) (runDomain T y K) ∧
      StrictMonoOn (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) (runDomain T y K) ∧
      ∀ β ∈ runDomain T y K,
        3 / 4 ≤ deriv (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) β ∧
          deriv (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) β ≤ 5 / 4) ∧
    (∀ P : ℝ, runFloor T y c₅ ≤ P →
      (∃! β, IsTunedAt T y P K β) ∧ ∀ β, IsTunedAt T y P K β → β ∈ runDomain T y K) ∧
    (∀ β ∈ runDomain T y K, HasDerivAt (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K)
      (runSlope T y Kr β K) β) ∧
    ContinuousOn (fun β => runSlope T y Kr β K) (runDomain T y K) := by
  obtain ⟨hopen, hup, hne, hder, hcont⟩ := run_has_slope hK hT hS hL hR hA h K
  have hagree : ∀ β ∈ runDomain T y K, TotalDensityFlow.coupling (T.stepParameters y) β K =
      flowCouplings (T.stepParameters y) β K := fun β hβ =>
    (total_flow_of_above hGives hUniq h (above_of_mem_domain h hβ)).2 K (Nat.le_succ K)
  have hcd : ∀ β ∈ runDomain T y K,
      HasDerivAt (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) (runSlope T y Kr β K) β :=
    fun β hβ => (hder β hβ).1.congr_of_eventuallyEq
      (eventuallyEq_of_mem (hopen.mem_nhds hβ) fun β' hβ' => hagree β' hβ')
  have hgood := TuningAtEveryCutoff.run_slope_near_one hK hT hS hL hR hA h
  refine ⟨fun β hβ => total_flow_of_above_total hGives hUniq h hβ,
    ⟨hopen, hup, hne, fun β hβ => (above_iff_total hGives hUniq h).mpr (above_of_mem_domain h hβ),
      hagree⟩, ⟨?_, ?_, fun β hβ => ?_⟩, fun P hP => ?_, hcd, hcont⟩
  · have hc : ContDiffOn ℝ (0 + 1) (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K)
        (runDomain T y K) := by
      refine (contDiffOn_succ_iff_deriv_of_isOpen hopen).mpr
        ⟨fun β hβ => (hcd β hβ).differentiableAt.differentiableWithinAt, fun h0 => ?_, ?_⟩
      · exact absurd h0 (by simp)
      · rw [contDiffOn_zero]
        exact hcont.congr fun β hβ => (hcd β hβ).deriv
    rwa [zero_add] at hc
  · have hmono := strictMonoOn_of_hasSlopeNearOneAboveFloor (F := y + 2 * T.B) (x := runFlow T y)
      (k := K) hup (hgood K)
    exact hmono.congr fun β hβ => (hagree β hβ).symm
  · rw [(hcd β hβ).deriv]
    exact (hder β hβ).2
  · have hex := exists_unique_of_increasing_family runFlow_zero (TuningAtEveryCutoff.floor_lt h) hgood
      (TuningAtEveryCutoff.run_descends h) K hP
    obtain ⟨β, hβ, hβu⟩ := hex.1
    refine ⟨⟨β, (TuningAtEveryCutoff.isTunedAt_iff hGives hUniq h).mpr hβ, fun β' hβ' =>
      hβu β' ((TuningAtEveryCutoff.isTunedAt_iff hGives hUniq h).mp hβ')⟩, fun β' hβ' => ?_⟩
    have h' := (TuningAtEveryCutoff.isTunedAt_iff hGives hUniq h).mp hβ'
    exact hex.2 β' h'.1 h'.2

theorem tuned_of_runTable (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (hGives : TotalDensityFlow.ExpansionGivesFlow) (hUniq : TotalDensityFlow.FlowIsUnique)
    (h : RunTable T y Kr lam c₅) : TunedAtEveryCutoff T y := by
  unfold TunedAtEveryCutoff
  refine ⟨runFloor T y c₅, TuningAtEveryCutoff.le_runFloor h, fun K => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := tuned_at_runFloor hK hT hS hL hR hA hGives hUniq h K
  exact ⟨h1, runDomain T y K, h2, h3, h4⟩

theorem same_bare_coupling (hK : KernelHasCouplingDerivative) (hT : BondScoreProperties)
    (hS : StepTransitionDensityBounds) (hL : ChainIsProbabilityLaw)
    (hR : ResponseConditionalMeanStatement) (hA : PlaneFields.LeastActionAtPlaneField)
    (hGives : TotalDensityFlow.ExpansionGivesFlow) (hUniq : TotalDensityFlow.FlowIsUnique)
    (h : RunTable T y Kr lam c₅) {P : ℝ} (hP : runFloor T y c₅ ≤ P) {β β' : ℕ → ℝ}
    (hβ : ∀ K, IsTunedAt T y P K (β K)) (hβ' : ∀ K, IsTunedAt T y P K (β' K)) : β = β' :=
  funext fun K =>
    ((tuned_at_runFloor hK hT hS hL hR hA hGives hUniq h K).2.2.2.1 P hP).1.unique (hβ K) (hβ' K)

end YangMills.ContinuumLimit

end
