import YangMills.Construction.ColdStepAtMirrorFrames.FaaDiBrunoAtAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
theorem faaDiBrunoAt_holds : FaaDiBrunoAt := by
  intro E G H _ _ _ _ _ _ g f n x hg hf v
  obtain ⟨U, hU, hgU⟩ : ∃ U ∈ nhds (f x), ContDiffOn ℝ n g U := by
    obtain ⟨u, hu, h⟩ := hg.contDiffOn (m := n) le_rfl (by simp)
    exact ⟨u, by simpa using hu, by simpa using h⟩
  obtain ⟨U', hU'sub, hU'o, hfx⟩ := mem_nhds_iff.mp hU
  have hgU' : ContDiffOn ℝ n g U' := hgU.mono hU'sub
  obtain ⟨W, hW, hfW⟩ : ∃ W ∈ nhds x, ContDiffOn ℝ n f W := by
    obtain ⟨u, hu, h⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
    exact ⟨u, by simpa using hu, by simpa using h⟩
  have hpre : f ⁻¹' U' ∈ nhds x := hf.continuousAt.preimage_mem_nhds (hU'o.mem_nhds hfx)
  obtain ⟨W', hW'sub, hW'o, hxW⟩ := mem_nhds_iff.mp (Filter.inter_mem hW hpre)
  have hfW' : ContDiffOn ℝ n f W' := hfW.mono (fun y hy => (hW'sub hy).1)
  have hmaps : Set.MapsTo f W' U' := fun y hy => (hW'sub hy).2
  have hq := hgU'.ftaylorSeriesWithin hU'o.uniqueDiffOn
  have hp := hfW'.ftaylorSeriesWithin hW'o.uniqueDiffOn
  have hcomp := hq.comp hp hmaps
  have he := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) le_rfl hW'o.uniqueDiffOn hxW
  rw [iteratedFDerivWithin_of_isOpen n hW'o hxW] at he
  rw [← he]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : ftaylorSeriesWithin ℝ g U' (f x) c.length = iteratedFDeriv ℝ c.length g (f x) :=
    iteratedFDerivWithin_of_isOpen c.length hU'o hfx
  rw [e1]
  congr 1
  funext i
  simp only [OrderedFinpartition.applyOrderedFinpartition_apply]
  have e2 : ftaylorSeriesWithin ℝ f W' x (c.partSize i) = iteratedFDeriv ℝ (c.partSize i) f x :=
    iteratedFDerivWithin_of_isOpen (c.partSize i) hW'o hxW
  rw [e2]
end YangMills.Construction.Calculus
end
