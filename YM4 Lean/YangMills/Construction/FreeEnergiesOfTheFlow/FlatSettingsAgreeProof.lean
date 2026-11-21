import YangMills.Construction.ClusterExpansionOfAStep.GasesEqualInBoxes
import YangMills.Construction.FreeEnergiesOfTheFlow.FlatSettingsAgree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergiesOfTheFlow
open TorusFields TorusLumps StepSettings StepCosts BlockAverages ColdStepAtMirrorFrames
private theorem fineSite_mem_chartBonds_iff {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] (hL : Odd R.params.side)
    (hn : 2 ≤ n) (hn' : 2 ≤ n') (Y : TorusSite n) (Y' : TorusSite n') (h o : Fin 4 → ℤ) (ho : o ∈ centredCube R.params.side)
    (i : Fin 4) :
    ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ chartBonds R.params.side n ↔
      ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ chartBonds R.params.side n' := by apply _root_.YangMills.Construction.BoxAgreement.fineSite_mem_chartBonds_iff <;> assumption
private theorem toTorusSite_cellCentre {R : StepSetup} {n : ℕ} [NeZero n] (Y : TorusSite n) (h : Fin 4 → ℤ) :
    toTorusSite (n * R.params.side)
        (cellCentre (F := stepBlockFrame R.params.side n) 0
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
      fineSite R.params.side Y h 0 := by apply _root_.YangMills.Construction.BoxAgreement.toTorusSite_cellCentre <;> assumption
theorem trivialFieldSettingsAgree : FlatTops.TrivialFieldSettingsAgree := by
  intro R n n' _ _ m hL hn hn' hs hs'
  refine ⟨hs, hs', fun _ _ => rfl, ?_, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · rintro ⟨h, o, i⟩ ⟨_, ho⟩
    exact fineSite_mem_chartBonds_iff hL hn hn' 0 0 h o ho i
  · intro h o _ _
    simp [coldChartSetting]
  · intro h o hz
    exact absurd hz (by simp [coldChartSetting])
  · intro h _
    have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
      rw [BlockOffsets.mem_centredCube_iff]
      intro i
      have hpos : (1 : ℤ) ≤ R.params.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      have : 0 ≤ ((R.params.side : ℤ) - 1) / 2 := by omega
      simpa using this
    exact ⟨0, h0, toTorusSite_cellCentre 0 h, toTorusSite_cellCentre 0 h⟩
end YangMills.Construction.FreeEnergiesOfTheFlow
end
