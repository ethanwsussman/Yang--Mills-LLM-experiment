import YangMills.Construction.LawInAState.TheLevelOfTheLaw
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import YangMills.Construction.SystemOfAdmissibleConstants.LevelOfADistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open TorusLumps StepReturn RenormalizationStepParameters TrajectoryData StateLaws AdmissibleConstants
private theorem expansionCoupling_spec {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {A : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hA : HasExpansion ℓ t x A) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x A) (kernelImage ℓ x A) ∧
      |expansionCoupling ℓ t x A - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem couplingFlow_hasExpansion {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ) :
    (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.SharedProofs.p3977 <;> assumption
private theorem isFlowDatum_of_window {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    (hR : ExpansionReturnsAt (T.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (T.stepParameters y) 0 β (wilsonWeight β)) {g d : ℝ} {K : ℕ} {β : ℝ}
    (hthr : y + 2 * T.B ≤ D.threshold g) (hB : 0 ≤ T.B) (hdat : IsDatumAtDistance D g d K β) :
    IsFlowDatum (T.stepParameters y) (D.threshold g) K β := by
  obtain ⟨⟨hβ, hK, hbelow⟩, hcut⟩ := hdat
  have hK2 : 2 ≤ K := (le_max_left _ _).trans hcut
  have hlow : ∀ j < K, y ≤ (couplingFlow (T.stepParameters y) β j).1 := fun j hj => by
    have h1 : D.threshold g < D.coupling β j := hbelow j hj
    have h2 : D.coupling β j = (couplingFlow (T.stepParameters y) β j).1 := rfl
    linarith
  have hβy : y ≤ β := by
    have h1 : D.threshold g ≤ β := hβ
    linarith
  refine ⟨hK2, ?_, hK⟩
  intro j hj
  rcases hj.lt_or_eq with hj | rfl
  · exact hlow j hj
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    have hexp := couplingFlow_hasExpansion hR (hW β hβy) t fun i hi => hlow i (by omega)
    have hstep := (expansionCoupling_spec hR (hlow t (by omega)) hexp).2
    have h1 : D.threshold g < D.coupling β t := hbelow t (by omega)
    have h2 : D.coupling β t = (couplingFlow (T.stepParameters y) β t).1 := rfl
    have h3 := (abs_le.mp hstep).1
    change y ≤ expansionCoupling (T.stepParameters y) t (couplingFlow (T.stepParameters y) β t).1
      (couplingFlow (T.stepParameters y) β t).2
    have h4 : (T.stepParameters y).B = T.B := rfl
    linarith
theorem separationLevelStatement_of_stateLaw (hL : StateLaws.separationLevelStatement) :
    SystemOfAdmissibleConstants.separationLevelStatement := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr₀, h⟩ := hL a ha
  refine ⟨L₀, r₀, C₀, hr₀, ?_⟩
  intro L hodd hL₀ T hTa hTL hadm hcold hon hr hC
  obtain ⟨y₀, hy₀⟩ := h L hodd hL₀ T hTa hTL hadm hcold hon hr hC
  refine ⟨y₀, ?_⟩
  intro y hy hret hwil D hD g _ hfloor d hd0 hd1 K β hdat
  have hdev : 0 ≤ oneLoopDeviation T := Real.iSup_nonneg fun _ => abs_nonneg _
  have hg : y + 2 * oneLoopDeviation T + 1 ≤ g ^ (-2 : ℤ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hfloor
  have hB : 0 ≤ T.B := zero_le_one.trans hadm.B_ge
  have hthr : y + 2 * T.B ≤ D.threshold g := by
    have h1 : D.threshold g = g ^ (-2 : ℤ) + D.shift := rfl
    have h2 := hD.shift_ge
    linarith
  have hdatum := isFlowDatum_of_window D hret hwil hthr hB hdat
  obtain ⟨h1, h2, h3⟩ := hy₀ y hy hret hwil (D.threshold g) hthr d hd0 hd1 K β hdatum hdat.2
  refine ⟨⟨⟨h2.le, h1⟩, ?_⟩, h2, h3⟩
  rintro k ⟨hk, hfar⟩
  classical
  unfold StateLaws.separationLevel
  exact Nat.le_findGreatest hk hfar
end YangMills.Construction.SystemOfAdmissibleConstants
end
