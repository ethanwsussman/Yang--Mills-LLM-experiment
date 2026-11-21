import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanOfABondIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
theorem measurableContourMean (hK : BondKernelBorel) : MeasurableContourMeanStatement := by
  classical
  intro ℓ n _ b c f hf
  obtain ⟨-, -, hm, -, hc, -⟩ := hK ℓ 0 n
  set G : TorusField (n * ℓ.side) → ℝ :=
    fun U => f (contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n U)) b
      (fineLevelField ℓ n U) c) with hG
  intro s hs
  have hcover : G ⁻¹' s = ⋃ H, {U | fineHotLumps ℓ (fineLevelField ℓ n U) = H} ∩ G ⁻¹' s := by
    ext U
    simp
  rw [hcover]
  refine MeasurableSet.iUnion fun H => ?_
  have hpw : Measurable (({U : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n U) = H}).piecewise
      G fun _ => 0) :=
    ContinuousOn.measurable_piecewise (hf.comp_continuousOn (hc H b c)) continuousOn_const (hm H)
  have hset : {U : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n U) = H} ∩ G ⁻¹' s =
      {U : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n U) = H} ∩
        (({U : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n U) = H}).piecewise
          G fun _ => 0) ⁻¹' s := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    refine and_congr_right fun hU => ?_
    rw [Set.piecewise_eq_of_mem _ _ _ hU]
  rw [hset]
  exact (hm H).inter (hpw hs)
end YangMills.Construction.TorusLumps
end
