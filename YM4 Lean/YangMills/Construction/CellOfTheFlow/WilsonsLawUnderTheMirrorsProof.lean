import YangMills.Construction.CellOfTheFlow.MomentOfTheLowerMajorantProof
import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields FieldHaar WeightedResponses
namespace ReflectionInvariance
variable {m : ℕ}
private theorem measurable_pullbackBy (g : TorusIsometry) : Measurable (pullbackBy g : TorusField m → TorusField m) := by apply _root_.YangMills.SharedProofs.p130372 <;> assumption
private theorem pullbackBy_of_transports {g : TorusIsometry} {W W' : TorusField m} (h : g.Transports W W') :
    pullbackBy g W' = W := by
  funext x k
  have hk := h x k
  by_cases hs : g.axisSign (g.axisPerm.symm k) = 1
  · rw [if_pos hs] at hk
    simp only [pullbackBy, if_pos hs]
    exact hk
  · rw [if_neg hs] at hk
    simp only [pullbackBy, if_neg hs]
    exact hk
end ReflectionInvariance
theorem wilsonLaw_reflection_invariant (hH : HaarInvariantUnderSymmetries) :
    wilsonLawReflectionInvariantStatement := by
  intro β m _ G κ κ' F _ _ hF _
  obtain ⟨Ψ, hΨ, hc⟩ := (hH m).2 (G.reflectionTo κ κ')
  set g := G.reflectionTo κ κ' with hg
  set Z := ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar m) with hZ
  let ρ : TorusField m → NNReal := fun W => Real.toNNReal (Real.exp (-β * wilsonAction Finset.univ W) / Z)
  have hρc : Continuous ρ :=
    continuous_real_toNNReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))).div_const _)
  have hlaw : wilsonLaw β m = (fieldHaar m).withDensity fun W => (ρ W : ENNReal) := rfl
  have hρΨ : ∀ W, ρ (Ψ W) = ρ W := by
    intro W
    simp only [ρ, wilsonAction_of_transports (hc W)]
  have hh : Measurable fun W => ρ W • F (pullbackBy g W) :=
    hρc.measurable.smul (hF.comp (ReflectionInvariance.measurable_pullbackBy g))
  have hchange := integral_map (μ := fieldHaar m) hΨ.measurable.aemeasurable
    (f := fun W => ρ W • F (pullbackBy g W)) (by rw [hΨ.map_eq]; exact hh.aestronglyMeasurable)
  rw [hΨ.map_eq] at hchange
  rw [hlaw, integral_withDensity_eq_integral_smul hρc.measurable,
    integral_withDensity_eq_integral_smul hρc.measurable, hchange]
  refine integral_congr_ae (ae_of_all _ fun W => ?_)
  simp only [hρΨ, ReflectionInvariance.pullbackBy_of_transports (hc W)]
end YangMills.Construction.CellWindows
end
