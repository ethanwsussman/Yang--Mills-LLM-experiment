import YangMills.Construction.TorusOrFourSpace.MapsOfFourKindsOnTuplesTestFunctionsAndDistributions
import YangMills.Construction.TorusOrFourSpace.MembersOfABoundedFamilyAsDistributions
import YangMills.Construction.TorusOrFourSpace.MembersOfAHierarchyAsDistributions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.Kind
theorem HierarchyMembersAsDistributions.statement_holds
    (hBounded : BoundedHierarchyMembersAreDistributions)
    (hTupleMaps : ExtendedTupleMapFacts.MainProperties) :
    HierarchyMembersAsDistributions.Statement := by
  intro D E C Φ hΦ n hn
  obtain ⟨hFam, hIsOpen, -, hUniq, hPart⟩ := hBounded D E C Φ hΦ n hn
  refine ⟨fun R d G hG => hFam R d G hG.2, hUniq, fun T hT => ?_, fun ψ => ?_⟩
  · have hPartT := hPart T hT
    refine ⟨hPartT, fun x hx => ⟨_, subset_rfl, hIsOpen, hx, 5 * (n : ℕ) + 1, ?_⟩⟩
    exact hPartT.2.1
  · obtain ⟨-, hEvery⟩ := hTupleMaps D E n hn
    obtain ⟨hBijective, -, hRange, -, -, -, -, -, -, ⟨hTestFn, -⟩, -⟩ :=
      hEvery (ExtendedTupleMap.ofTupleMap ψ)
    refine ⟨⟨?_, hBijective.1.1.injOn, ?_⟩, fun F hF => hTestFn ⟨F, hF⟩⟩
    · intro x hx
      rw [← hRange]
      exact Set.mem_image_of_mem _ hx
    · rw [Set.SurjOn, hRange]
end YangMills.Construction.PeriodicSpace.Kind
