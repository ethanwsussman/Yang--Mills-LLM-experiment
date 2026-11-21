import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.GapsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.HaarsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.TermsBetweenCompareOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages FamilyNorms
namespace ColdStepAtMirrorFrames
namespace InterpolatedTerms
open LocalCalculus
variable {F F' : BlockFrame}
theorem pairedPartsCompareSmoothly_sub {ι : Type} [Fintype ι] [DecidableEq ι] {ρ c₁ c₂ ε x κ : ℝ}
    (hρ : 0 < ρ)
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))} {z : F.Cell}
    {A B : StepVariable (finiteCells F) → ℝ} {A' B' : StepVariable (finiteCells F') → ℝ}
    (h₁ : PairedPartsCompareSmoothly ρ c₁ ε x κ j j' z A A')
    (h₂ : PairedPartsCompareSmoothly ρ c₂ ε x κ j j' z B B') :
    PairedPartsCompareSmoothly ρ (c₁ + c₂) ε x κ j j' z (fun η => A η - B η)
      (fun η => A' η - B' η) := by
  obtain ⟨s₁, b₁⟩ := h₁
  obtain ⟨s₂, b₂⟩ := h₂
  have e : (fun ζ => (A' (pushforwardField j' ζ) - B' (pushforwardField j' ζ)) -
      (A (pushforwardField j ζ) - B (pushforwardField j ζ))) =
      fun ζ => 1 * (A' (pushforwardField j' ζ) - A (pushforwardField j ζ)) +
        (-1) * (B' (pushforwardField j' ζ) - B (pushforwardField j ζ)) := by
    funext ζ
    ring
  refine ⟨?_, fun ξ hξ => ⟨?_, fun k => ?_⟩⟩
  · rw [e]
    exact (contDiffOn_const.mul s₁).add (contDiffOn_const.mul s₂)
  · have e1 := congrFun e ξ
    simp only at e1 ⊢
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_one, abs_neg, abs_one, one_mul, one_mul]
    have := (b₁ ξ hξ).1
    have := (b₂ ξ hξ).1
    linarith
  · simp only
    rw [e]
    have h := bondGradNorm_linear_combination_le hρ s₁ s₂ 1 (-1) hξ k
    rw [abs_neg, abs_one, one_mul, one_mul] at h
    have h1 := (b₁ ξ hξ).2 k
    have h2 := (b₂ ξ hξ).2 k
    refine h.trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    ring
end InterpolatedTerms
open InterpolatedTerms LocalCalculus in
theorem InterpolatedTerms.interpolatedTermsCloseOnTwoTori_holds
    (hs : interpolatedSlopesCompareStatement)
    (hg : GapPartsCompare) (hh : HaarDensitiesCompare)
    (hr : InterpolatedExpansionsCompare) (hj : EventuallyInParametersCombines) :
    InterpolatedTermsCloseOnTwoTori := by
  refine hj.2 _ _ ?_ (hj.1 _ _ (hj.1 _ _ (hj.1 _ _ hs hg) hh) hr)
  rintro T hT ⟨⟨⟨a, b⟩, c⟩, d⟩ t x s h F F' V V' Y Y' q ι _ _ j j' o hset
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have h1 := pairedPartsCompareSmoothly_sub hρ (a t x s h F F' V V' Y Y' q ι j j' o hset)
    (b t x s h F F' V V' Y Y' q ι j j' o hset)
  have h2 := (pairedPartsCompareSmoothly_sub hρ h1 (c t x s h F F' V V' Y Y' q ι j j' o hset)).2
  refine ⟨?_, (d t x s h F F' V V' Y Y' q ι j j' o hset).2⟩
  have e : T.Ct / 3 + T.Ct / 3 + T.Ct / 3 = T.Ct := by ring
  rw [e] at h2
  exact h2
end ColdStepAtMirrorFrames
end YangMills.Construction
end
