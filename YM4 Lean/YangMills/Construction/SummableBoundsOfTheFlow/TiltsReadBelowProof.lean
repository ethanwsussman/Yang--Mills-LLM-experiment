import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesReadBelow
import YangMills.Construction.SummableBoundsOfTheFlow.TiltsReadBelow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open TorusLumps TorusFields BlockAverages ColdStepAtMirrorFrames
private def expOfTotal (h : LocalDensity) : TorusFunctional := fun n W =>
  if hn : n = 0 then 1 else
    haveI : NeZero n := ⟨hn⟩
    Real.exp (∑ y, centered h n y W)
private theorem stepWeight_pos (p : StepParameters) (m : ℕ) : 0 < p.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem vanishingFormLocalFamilyStatement_holds (hb : localFamilyNormStatement)
    (hc : ColdExpansionRegular) : vanishingFormLocalFamilyStatement := by
  intro p t ε ε₃ h hp hn₁ H H0
  set C : ℝ := max 1 (max ε ε₃) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCε : ε ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCε₃ : ε₃ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  let p' : StepParameters := { p with E := C, E₃ := C }
  have hp' : p'.Admissible :=
    { a_ge := hp.a_ge, L_odd := hp.L_odd, L_ge := hp.L_ge, σ_pos := hp.σ_pos, κ_pos := hp.κ_pos,
      κ_le := hp.κ_le, κ₁_pos := hp.κ₁_pos, rt_pos := hp.rt_pos, n₁_pos := hp.n₁_pos,
      E_pos := by show 0 < C; linarith, E_ge := hC1, depth_lt := hp.depth_lt,
      E₃_pos := by show 0 < C; linarith, B_pos := hp.B_pos, Cder_ge := hp.Cder_ge,
      n₀_ge := hp.n₀_ge, y₁_ge := hp.y₁_ge, range_ge := hp.range_ge }
  have hR : ColdExpansion p' t 0 (expOfTotal h) h := by
    refine ⟨?_, H.admissible.smooth, H.admissible.gauge, H.admissible.translation, ?_, ?_, ?_, ?_⟩
    · intro n _ _ W _
      have hne : n ≠ 0 := NeZero.ne n
      simp only [expOfTotal, dif_neg hne]
      exact Real.exp_pos _
    · intro n _ _ W _
      have hne : n ≠ 0 := NeZero.ne n
      simp only [expOfTotal, dif_neg hne, Real.log_exp]
      have : ∑ y, centered h n y (trivialField n) = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        simp [centered]
      rw [this]
      simp
    · intro n _ hn y W hW k c X k1 k3 hX
      refine (H.decay n hn y W hW k c X k1 k3 hX).trans ?_
      show _ ≤ (if k = 3 then C else C) / p.weight (supportDiam y c)
      refine div_le_div_of_nonneg_right ?_ (stepWeight_pos p _).le
      split_ifs <;> assumption
    · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb' hX
      refine (H.comparison n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb' hX).trans ?_
      exact div_le_div_of_nonneg_right hCε (stepWeight_pos p _).le
    · intro A A' hA hA'
      have := H0.2 A A' hA hA'
      rw [zero_mul] at this
      exact this
  have hreg := hc p' t 0 (expOfTotal h) h hp' hn₁ hR
  have hfam := hb p t ε ε₃ h hp hn₁ H
  exact ⟨hfam.smooth, hfam.gauge_invariant, hfam.translation_invariant, hfam.decay, hfam.locality,
    hreg.flat_limit⟩
end YangMills.Construction.FamilyNorms
end
