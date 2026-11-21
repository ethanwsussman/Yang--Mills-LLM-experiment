import YangMills.Construction.CellOfTheFlow.FreeClassesGivenTheState
import YangMills.Construction.CellOfTheFlow.TheDrawsStandOnGrounds
import YangMills.Construction.CellOfTheFlow.TheGasHoldsItsSupportsRarely
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters StepReturn StepSettings StepGas WeightedResponses BlockAverages LumpContours
private theorem holdsAtAdmissibleParameters_of_three {P Q S U : ParameterAssignment → ℝ → Prop} (b : ParameterAssignment → ℝ)
    (hP : HoldsAtAdmissibleParameters P) (hQ : HoldsAtAdmissibleParameters Q) (hS : HoldsAtAdmissibleParameters S)
    (h : ∀ (Tb : ParameterAssignment) (y : ℝ), b Tb ≤ y → ExpansionReturnsAt (Tb.stepParameters y) →
      (∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) →
        P Tb y → Q Tb y → S Tb y → U Tb y) :
    HoldsAtAdmissibleParameters U := by
  intro a ha
  obtain ⟨L₁, r₁, p₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, p₂, h₂⟩ := hQ a ha
  obtain ⟨L₃, r₃, p₃, h₃⟩ := hS a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)), fun L hodd hL Tb hTa hTL hD hrt => ?_⟩
  obtain ⟨y₁, k₁⟩ := h₁ L hodd (le_trans (le_max_left _ _) hL) Tb hTa hTL hD
    (le_trans hrt (min_le_left _ _))
  obtain ⟨y₂, k₂⟩ := h₂ L hodd (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL) Tb hTa hTL hD
    (le_trans hrt (le_trans (min_le_right _ _) (min_le_left _ _)))
  obtain ⟨y₃, k₃⟩ := h₃ L hodd (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL) Tb hTa hTL hD
    (le_trans hrt (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨max (b Tb) (max y₁ (max y₂ y₃)), fun y hy hR hW => ?_⟩
  have e₀ : b Tb ≤ y := le_trans (le_max_left _ _) hy
  have e₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have e₂ : y₂ ≤ y :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have e₃ : y₃ ≤ y :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  exact h Tb y e₀ hR hW (k₁ y e₁ hR hW) (k₂ y e₂ hR hW) (k₃ y e₃ hR hW)
private theorem expansionCoupling_spec {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem hasExpansion_couplingFlow {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ) (ht : ∀ i < t, ℓ.y₁ ≤ (couplingFlow ℓ β i).1) :
    HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.SharedProofs.p3977 <;> assumption
private theorem nextCoupling_le_of_onParameters {Tb : ParameterAssignment} {y : ℝ} (hy : 200 * Tb.B ≤ y)
    (hR : ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    {T : StageTower (Tb.stepParameters y)} {β : ℝ} {j : ℕ} (hT : IsTowerAtParametersMeasurable Tb y T β (j + 1)) :
    (T.stage j).nextCoupling ≤ 1.01 * (T.stage j).coupling := by
  have hc := hT.onFamily.coupling_eq
  have hfloor : ∀ i ≤ j + 1, y ≤ (couplingFlow (Tb.stepParameters y) β i).1 := fun i hi => by
    rw [← hc i (by omega)]
    exact (hT.onFamily.onFamily i hi).le_coupling
  have hβ : y ≤ β := hfloor 0 (Nat.zero_le _)
  have hexp := hasExpansion_couplingFlow hR (hW β hβ) j fun i hi => hfloor i (by omega)
  have hmove := (expansionCoupling_spec hR (hfloor j (by omega)) hexp).2
  have e₀ : (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 := hc j (by omega)
  have e₁ : (T.stage j).nextCoupling = (couplingFlow (Tb.stepParameters y) β (j + 1)).1 := hc (j + 1) (by omega)
  have e₂ : (couplingFlow (Tb.stepParameters y) β (j + 1)).1 =
      expansionCoupling (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
        (couplingFlow (Tb.stepParameters y) β j).2 := rfl
  have hB : (Tb.stepParameters y).B = Tb.B := rfl
  rw [← e₂, ← e₀, ← e₁, hB] at hmove
  have hx : y ≤ (T.stage j).coupling := e₀ ▸ hfloor j (by omega)
  have := (abs_le.mp hmove).2
  linarith
theorem freeSupportsConditionalBound (hS : stepGivenStateIsGasStatement)
    (hG : supportsPresentRarelyStatement) (hD : drawsStandOnGroundsStatement) :
    freeSupportsConditionalBoundStatement := by
  refine holdsAtAdmissibleParameters_of_three (fun Tb => 200 * Tb.B) hS hG hD fun Tb y hy hR hW kS kG kD => ?_
  intro T β j hT m _ hm Θ A hA
  have hstep : (T.stage j).toStepSetup.OnParameters Tb y := hT.onFamily.onFamily j (Nat.le_succ j)
  have hnext : (T.stage j).toStepSetup.nextCoupling ≤ 1.01 * (T.stage j).toStepSetup.coupling :=
    nextCoupling_le_of_onParameters hy hR hW hT
  rw [kS T β j hT m hm Θ A hA]
  have hb : ∀ᵐ v ∂(markedSampleLaw T β (j + 1) m),
      (stageGround T j m v).gibbsLaw ∅ (supportsPresent (stageGround T j m v) Θ) ≤
        ENNReal.ofReal (∏ θ ∈ Θ, clusterWeight (Tb.stepParameters y).side Tb.gasRate (T.stage j).coupling
          (stageRange T j) θ) := by
    filter_upwards [kD T β j hT m hm] with v hv
    exact kG _ hstep hnext m _ Θ hv
  calc ∫⁻ v in A, (stageGround T j m v).gibbsLaw ∅ (supportsPresent (stageGround T j m v) Θ)
        ∂(markedSampleLaw T β (j + 1) m)
      ≤ ∫⁻ _ in A, ENNReal.ofReal
          (∏ θ ∈ Θ, clusterWeight (Tb.stepParameters y).side Tb.gasRate (T.stage j).coupling (stageRange T j) θ)
          ∂(markedSampleLaw T β (j + 1) m) := lintegral_mono_ae (ae_restrict_of_ae hb)
    _ = _ := setLIntegral_const _ _
end YangMills.Construction.CellWindows
end
