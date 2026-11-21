import YangMills.Construction.WindowOfTheParameters.DataOfTheTotalFlowAreThoseOfTheExpansion
import YangMills.Construction.WindowOfTheParameters.TheExpansionGivesTheTotalFlow
import YangMills.Construction.WindowOfTheParameters.TotalFlowIsOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensityFlow
open TorusLumps RenormalizationStepParameters WeightedResponses Conventions SequencePassage FloorBounds
private theorem chainFunctional_couplingFlow (P : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) :
    chainFunctional P β (fun k => (couplingFlow P β k).1) t = (couplingFlow P β t).2 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [chainFunctional, couplingFlow, ih]
private theorem coupling_eq_of_above_floor (hGives : ExpansionGivesFlow) (hUniq : FlowIsUnique)
    {T : ParameterAssignment} {y c X : ℝ} (hT : T.Admissible) (hF : FlowAboveFloor T y c X) {β : ℝ} (hβ : X ≤ β)
    {t : ℕ} (hlow : ∀ l < t, X ≤ (couplingFlow (T.stepParameters y) β l).1) :
    IsDefinedUpTo (T.stepParameters y) β t ∧
      ∀ j ≤ t, (couplingFlow (T.stepParameters y) β j).1 = coupling (T.stepParameters y) β j := by
  have hadm : IsAdmissibleBlockingFactor (T.stepParameters y).side :=
    ⟨hT.L_odd, le_trans (by norm_num) hT.L_ge⟩
  have hside : 2 ≤ (T.stepParameters y).side := le_trans (by norm_num) hT.L_ge
  have hflow : IsFlowUpTo (T.stepParameters y) β t (fun k => (couplingFlow (T.stepParameters y) β k).1) := by
    refine hGives T y hT hF.admissible hadm β t _ rfl (fun j hj => hF.le_floor.trans (hlow j hj)) ?_
    intro j hj
    rw [chainFunctional_couplingFlow]
    exact hF.hasExpansion β j hβ fun l hlj => hlow l (lt_of_lt_of_le hlj hj)
  exact hUniq (T.stepParameters y) β t _ hside hflow
theorem passageWindow_eq_expansionWindow (hGives : ExpansionGivesFlow)
    (hUniq : FlowIsUnique) : PassageWindowEqExpansionWindow := by
  intro T y c X hT hF B g hB _ hX K
  have hXP : X ≤ passageThreshold B g := by
    unfold passageThreshold
    linarith
  have hexp : ∀ β ∈ SequencePassage.passageWindow B g (fun β k => (couplingFlow (T.stepParameters y) β k).1) K,
      IsDefinedUpTo (T.stepParameters y) β K ∧
        ∀ j ≤ K, (couplingFlow (T.stepParameters y) β j).1 = coupling (T.stepParameters y) β j := by
    rintro β ⟨hβ, -, hk⟩
    exact coupling_eq_of_above_floor hGives hUniq hT hF (hXP.trans hβ) fun l hl => hXP.trans (hk l hl).le
  refine ⟨?_, fun β hβ k hk => ((hexp β hβ).2 k hk).symm⟩
  ext β
  constructor
  · rintro ⟨-, hβ, hKle, hk⟩
    have hβX : X ≤ β := hXP.trans hβ
    have hup : ∀ j ≤ K, ∀ l < j, X ≤ (couplingFlow (T.stepParameters y) β l).1 := by
      intro j
      induction j with
      | zero => intro _ l hl; exact absurd hl (Nat.not_lt_zero l)
      | succ j ih =>
        intro hj l hl
        have hjK : j ≤ K := by omega
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlj | rfl
        · exact ih hjK l hlj
        · have heq := (coupling_eq_of_above_floor hGives hUniq hT hF hβX (ih hjK)).2 l le_rfl
          rw [heq]
          exact hXP.trans (hk l (by omega)).le
    have hagree := (coupling_eq_of_above_floor hGives hUniq hT hF hβX (hup K le_rfl)).2
    refine ⟨hβ, ?_, fun k hk' => ?_⟩
    · show (couplingFlow (T.stepParameters y) β K).1 ≤ passageThreshold B g
      rw [hagree K le_rfl]
      exact hKle
    · show passageThreshold B g < (couplingFlow (T.stepParameters y) β k).1
      rw [hagree k hk'.le]
      exact hk k hk'
  · intro hβ
    obtain ⟨hD, hagree⟩ := hexp β hβ
    obtain ⟨hβP, hKle, hk⟩ := hβ
    refine ⟨hD, hβP, ?_, fun k hk' => ?_⟩
    · show coupling (T.stepParameters y) β K ≤ passageThreshold B g
      rw [← hagree K le_rfl]
      exact hKle
    · show passageThreshold B g < coupling (T.stepParameters y) β k
      rw [← hagree k hk'.le]
      exact hk k hk'
end YangMills.Construction.TotalDensityFlow
end
