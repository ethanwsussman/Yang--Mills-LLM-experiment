import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import YangMills.Construction.ClusterExpansionOfAStep.FlowWhereTheExpansionReturns
import YangMills.Construction.ResponseInTheExpansion.MarkedMeansAlongAMoveProof
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheFlowProof
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
section FlowAndChain
variable (ℓ : TorusLumps.StepParameters) (β : ℝ)
private theorem flowFunctional_succ (t : ℕ) :
    flowFunctional ℓ β (t + 1) =
      TorusLumps.kernelImage ℓ (flowCoupling ℓ β t) (flowFunctional ℓ β t) := rfl
private theorem chainFunctional_flowCoupling : ∀ s : ℕ,
    WeightedResponses.chainFunctional ℓ β (flowCoupling ℓ β) s = flowFunctional ℓ β s
  | 0 => rfl
  | s + 1 => by
    rw [flowFunctional_succ, ← chainFunctional_flowCoupling s]
    rfl
end FlowAndChain
private theorem expansion_step_of_returns {ℓ : TorusLumps.StepParameters}
    (hR : StepReturn.ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusLumps.TorusFunctional}
    (hx : ℓ.y₁ ≤ x) (hD : TorusLumps.HasExpansion ℓ t x D) :
    TorusLumps.HasExpansion ℓ (t + 1) (TorusLumps.expansionCoupling ℓ t x D)
        (TorusLumps.kernelImage ℓ x D) ∧
      |TorusLumps.expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B ∧
      ∀ (x'' : ℝ) (f'' : TorusLumps.LocalDensity),
        TorusLumps.ColdExpansion ℓ (t + 1) x'' (TorusLumps.kernelImage ℓ x D) f'' →
        x'' = TorusLumps.expansionCoupling ℓ t x D := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ResponseAlongFlow.expansion_step <;> assumption
private theorem hasExpansion_along_flow {ℓ : TorusLumps.StepParameters}
    (hR : StepReturn.ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) :
    ∀ t : ℕ, (∀ j < t, ℓ.y₁ ≤ flowCoupling ℓ β j) →
      TorusLumps.HasExpansion ℓ t (flowCoupling ℓ β t) (flowFunctional ℓ β t) := by apply _root_.YangMills.DeltaSharedProofs.p3925 <;> assumption
private theorem flowHasExpansionAt_of_returns {ℓ : TorusLumps.StepParameters}
    (hR : StepReturn.ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) :
    FlowHasExpansionAt ℓ β := fun t =>
  ⟨hasExpansion_along_flow hR h0 t, fun hj =>
    (expansion_step_of_returns hR (hj t le_rfl)
      (hasExpansion_along_flow hR h0 t fun j hjt => hj j hjt.le)).2.1⟩
private theorem flowReadOffAt_of_returns {ℓ : TorusLumps.StepParameters}
    (hR : StepReturn.ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) : FlowReadOffAt ℓ β := by
  intro t hj x
  have hrow := hasExpansion_along_flow hR h0 t fun j hjt => hj j hjt.le
  obtain ⟨h1, -, h3⟩ := expansion_step_of_returns hR (hj t le_rfl) hrow
  obtain ⟨-, f, hf, -⟩ := h1
  constructor
  · rintro ⟨f', hf'⟩
    exact h3 x f' hf'
  · rintro rfl
    exact ⟨f, hf⟩
private theorem flowUniqueAt_of_readOff {ℓ : TorusLumps.StepParameters} {β : ℝ}
    (hread : FlowReadOffAt ℓ β) : FlowUniqueAt ℓ β := by
  intro x t hx0 hfl hcold j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjt
    cases j with
    | zero => exact ⟨hx0, rfl⟩
    | succ j =>
      have hlow := ih j (Nat.lt_succ_self j) (by omega)
      have harr : WeightedResponses.chainFunctional ℓ β x (j + 1) = flowFunctional ℓ β (j + 1) := by
        rw [flowFunctional_succ, ← hlow.2, ← hlow.1]
        rfl
      refine ⟨?_, harr⟩
      have hc := hcold j (by omega)
      rw [harr] at hc
      refine (hread j (fun i hi => ?_) (x (j + 1))).mp hc
      have := (ih i (by omega) (by omega)).1
      rw [← this]
      exact hfl i (by omega)
private theorem integrable_of_integral_pos {X : Type} [MeasurableSpace X] {μ : Measure X}
    {D : X → ℝ} (hm : 0 < ∫ W, D W ∂μ) : Integrable D μ := by apply _root_.YangMills.Construction.ResponseInTheExpansion.PerturbedExpectation.integrable_of_integral_pos <;> assumption
private theorem measure_preimage_pos_of_density_pos {Y X : Type} [MeasurableSpace Y]
    [MeasurableSpace X] {ν : Measure Y} {μ : Measure X} {top : Y → X} {D : X → ℝ}
    (htop : ∀ F : X → ℝ, IsBoundedMeasurable F →
      ∫ u, F (top u) ∂ν = (∫ V, F V * D V ∂μ) / ∫ V, D V ∂μ)
    (hpos : ∀ V, 0 < D V) (hm : 0 < ∫ V, D V ∂μ) (A : Set X) (hA : MeasurableSet A)
    (hA0 : 0 < μ A) : 0 < ν (top ⁻¹' A) := by
  by_contra h
  have h0 : ν (top ⁻¹' A) = 0 := by simpa using h
  have hF : IsBoundedMeasurable (A.indicator (fun _ => (1 : ℝ))) := by
    refine ⟨measurable_const.indicator hA, 1, fun u => ?_⟩
    by_cases hu : u ∈ A <;> simp [hu]
  have e := htop _ hF
  have lhs : ∫ u, A.indicator (fun _ => (1 : ℝ)) (top u) ∂ν = 0 := by
    refine integral_eq_zero_of_ae (ae_iff.mpr (measure_mono_null (fun u hu => ?_) h0))
    have hne : A.indicator (fun _ => (1 : ℝ)) (top u) ≠ 0 := hu
    exact Set.mem_preimage.mpr (Set.mem_of_indicator_ne_zero hne)
  have hrw : (fun V => A.indicator (fun _ => (1 : ℝ)) V * D V) = A.indicator D := by
    funext V
    by_cases hV : V ∈ A <;> simp [hV]
  have hDi := integrable_of_integral_pos hm
  have rhs : 0 < ∫ V, A.indicator D V ∂μ := by
    rw [integral_indicator hA, setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun V => (hpos V).le) hDi.integrableOn]
    have hs : Function.support D = Set.univ := by
      ext V
      simp [Function.mem_support, (hpos V).ne']
    simpa [hs] using hA0
  rw [lhs, hrw] at e
  have := div_pos rhs hm
  linarith
private theorem flowIsChainLawAt_of_chainLaw (hC : WeightedResponses.ChainIsProbabilityLaw)
    {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) (β : ℝ) : FlowIsChainLawAt ℓ β := by
  intro t n _
  obtain ⟨hp, hZ, -, hpos, -, -, hmass, htop, hbot⟩ :=
    hC ℓ hfit hfit.depth_lt β (flowCoupling ℓ β) t n
  simp only [chainFunctional_flowCoupling] at hpos hmass htop
  have htop' : ∀ F : TorusFields.TorusField n → ℝ, IsBoundedMeasurable F →
      ∫ u, F (WeightedResponses.finalField ℓ t n u)
          ∂(WeightedResponses.chainJointLaw ℓ β (flowCoupling ℓ β) t n) =
        (∫ V, F V * flowFunctional ℓ β t n V ∂(TorusFields.fieldHaar n)) /
          ∫ V, flowFunctional ℓ β t n V ∂(TorusFields.fieldHaar n) := by
    intro F hF
    rw [htop F hF.1 hF.2, hmass]
  have hmass' : 0 < ∫ V, flowFunctional ℓ β t n V ∂(TorusFields.fieldHaar n) := hmass ▸ hZ
  exact ⟨⟨hp, fun G hG => hbot G hG.1 hG.2, hmass, hZ, htop'⟩, fun _ =>
    ⟨hpos, fun A hA hA0 => measure_preimage_pos_of_density_pos htop' hpos hmass' A hA hA0⟩⟩
theorem flowWhereExpansionReturns_holds (hW : TorusLumps.WilsonWeightHasExpansion)
    (hC : WeightedResponses.ChainIsProbabilityLaw) : FlowWhereExpansionReturns := by
  obtain ⟨C₀, hC₀⟩ := hW
  refine ⟨C₀, fun ℓ hfit hc hret =>
    ⟨fun β => flowIsChainLawAt_of_chainLaw hC hfit β, fun β hβ => ?_⟩⟩
  have h0 := hC₀ _ hfit hc β hβ
  have hread := flowReadOffAt_of_returns hret h0
  exact ⟨flowHasExpansionAt_of_returns hret h0, hread, flowUniqueAt_of_readOff hread⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
