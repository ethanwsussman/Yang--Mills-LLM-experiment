import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsProperty
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyForBondsOfAnyOrientation
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.InfiniteLattice.GibbsEquivalences
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.AnyOrientationGibbs
theorem equivalences_hold (hE : InfiniteLattice.GibbsEquivalences.GibbsEquivalenceStatement) :
    Equivalences := by
  intro a β ha hβ ν hν
  obtain ⟨agree, -, forms, -⟩ := hE a β ha hβ
  obtain ⟨tfae, gibbs⟩ := forms ν hν
  have h13 : IsGibbs β ν → PreservesBoundedMeasurable β ν := by
    intro hG Λ' h F hF
    obtain ⟨-, -, versions, -⟩ := gibbs.1 hG
    obtain ⟨Λ, hΛ, -, -, same⟩ := agree Λ' h
    rw [same F hF]
    have hv := (versions Λ hΛ F hF).2.2 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩ measurable_const
    simpa using hv
  have h32 : PreservesBoundedMeasurable β ν →
      PreservesContinuousLocal β ν :=
    fun hB Λ h F hF => hB Λ h F hF.2.1
  have h21 : PreservesContinuousLocal β ν → IsGibbs β ν := by
    intro hC
    have keep : KernelInvariant ha β ν := fun Λ hΛ F hF =>
      hC Λ (hasNoOppositePairs_of_subset_positiveLinks ha hΛ) F ⟨hF.2.2, hF.1, hF.2.1⟩
    exact gibbs.2 ⟨(tfae.out 3 0).1 keep, (tfae.out 3 1).1 keep, (tfae.out 3 2).1 keep, keep⟩
  tfae_have 1 → 3 := h13
  tfae_have 3 → 2 := h32
  tfae_have 2 → 1 := h21
  tfae_finish
end YangMills.Construction.GibbsAtFixedSpacing.AnyOrientationGibbs
