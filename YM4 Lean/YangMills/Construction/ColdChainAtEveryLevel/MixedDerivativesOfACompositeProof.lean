import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfAComposite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.Analytic
theorem faaDiBrunoAnalyticProperty_holds : FaaDiBrunoAnalyticProperty := by
  intro k A B W _ _ _ _ _ _ _ _ _ G T x hT hG v
  have cT : ContDiffAt ℝ k T x := hT.contDiffAt.of_le (by exact_mod_cast le_top)
  have cG : ContDiffAt ℝ k G (T x) := hG.contDiffAt.of_le (by exact_mod_cast le_top)
  obtain ⟨t, ht, htx, hGt⟩ : ∃ t : Set B, IsOpen t ∧ T x ∈ t ∧ ContDiffOn ℝ k G t := by
    obtain ⟨u, hu, hc⟩ := cG.contDiffOn (m := k) le_rfl (by simp)
    obtain ⟨t, hts, ht, hx⟩ := mem_nhds_iff.1 hu
    exact ⟨t, ht, hx, (hc.mono (by simpa using hts))⟩
  obtain ⟨s, hs, hxs, hTs, hmap⟩ : ∃ s : Set A, IsOpen s ∧ x ∈ s ∧ ContDiffOn ℝ k T s ∧ Set.MapsTo T s t := by
    obtain ⟨u, hu, hc⟩ := cT.contDiffOn (m := k) le_rfl (by simp)
    have h2 : T ⁻¹' t ∈ 𝓝 x := cT.continuousAt.preimage_mem_nhds (ht.mem_nhds htx)
    obtain ⟨s, hss, hs, hx⟩ := mem_nhds_iff.1 (Filter.inter_mem hu h2)
    exact ⟨s, hs, hx, hc.mono (fun a ha => by simpa using (hss ha).1), fun a ha => (hss ha).2⟩
  have fG : HasFTaylorSeriesUpToOn k G (ftaylorSeriesWithin ℝ G t) t := hGt.ftaylorSeriesWithin ht.uniqueDiffOn
  have fT : HasFTaylorSeriesUpToOn k T (ftaylorSeriesWithin ℝ T s) s := hTs.ftaylorSeriesWithin hs.uniqueDiffOn
  have hcomp := fG.comp fT hmap
  have e1 := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs.uniqueDiffOn hxs
  rw [iteratedFDerivWithin_of_isOpen k hs hxs] at e1
  rw [← e1]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ftaylorSeriesWithin, iteratedFDerivWithin_of_isOpen _ ht htx, OrderedFinpartition.applyOrderedFinpartition_apply]
  congr 1
  funext m
  rw [iteratedFDerivWithin_of_isOpen _ hs hxs]
end YangMills.Construction.Analytic
end
