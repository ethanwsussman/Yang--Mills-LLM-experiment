import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.Continuum.LinearCombinationsAndTensorsLieInTheFlatSpaces
import YangMills.Construction.Continuum.TheThreeOpenSetsAndTheThreeSpaces
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConfigSpace
theorem flatSpaceClosure_of_openLoci_of_compactSupport
    (hloci : OpenLociAndFlatSubspaces)
    (hsupp : CompactSupportTensorFacts) :
    FlatSpaceClosure := by
  intro n hn
  refine ⟨fun c c' φ ψ => ?_, fun X hX => ?_⟩
  · obtain ⟨-, -, S, W, Wp, Wm, -, hW, -⟩ := hloci n hn
    have hφ : φ.1 ∈ W := by
      rw [← SetLike.mem_coe, hW]
      exact φ.2
    have hψ : ψ.1 ∈ W := by
      rw [← SetLike.mem_coe, hW]
      exact ψ.2
    have hcomb : c • φ.1 + c' • ψ.1 ∈ W := W.add_mem (W.smul_mem c hφ) (W.smul_mem c' hψ)
    refine ⟨⟨c • φ.1 + c' • ψ.1, ?_⟩, rfl⟩
    exact hW.subset hcomb
  · obtain ⟨-, hflat, -, -, hsmooth, -⟩ := hsupp n hn
    exact hflat (hsmooth X.1 X.2 hX).1
end YangMills.Construction.ConfigSpace
