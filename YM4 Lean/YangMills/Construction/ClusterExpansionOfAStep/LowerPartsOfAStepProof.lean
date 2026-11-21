import YangMills.Construction.ClusterExpansionOfAStep.LowerPartsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings TorusLumps TorusFields
theorem avoidingPart_nonneg_antitone : AvoidingParts.AvoidingPartNonnegAntitone := by
  classical
  intro R hR n _ hn W
  refine ⟨fun A => ENNReal.toReal_nonneg, fun A B hBA => ?_⟩
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hsum := hR.2.sum (n * R.params.side) hside W
  unfold StepSetup.avoidingPart
  have hsub : ∀ C : Finset (TorusSite n), Finset.univ.filter
      (fun Y : Finset (TorusSite (n * R.params.side)) =>
        IsHullState R.params R.range W Y ∧ Disjoint Y (sitesInBlocks R.params.side C)) ⊆
      Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W) := fun C Y hY => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
    exact hY.1
  have hfin : ∀ C : Finset (TorusSite n), (∑ Y ∈ Finset.univ.filter
      (fun Y : Finset (TorusSite (n * R.params.side)) =>
        IsHullState R.params R.range W Y ∧ Disjoint Y (sitesInBlocks R.params.side C)),
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
        ∂(Measure.pi fun _ : Y => R.labels.μ)) ≠ ⊤ := by
    intro C
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := R.functional (n * R.params.side) W)) ?_
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset (hsub C)
  refine ENNReal.toReal_mono (hfin B) (Finset.sum_le_sum_of_subset ?_)
  intro Y hY
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
  refine ⟨hY.1, hY.2.mono_right ?_⟩
  intro z hz
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact hBA hz
end YangMills.Construction.ClusterExpansionOfAStep
end
