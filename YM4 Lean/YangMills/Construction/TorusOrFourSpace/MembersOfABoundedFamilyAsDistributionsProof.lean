import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamilies
import YangMills.Construction.TorusOrFourSpace.DistributionOfAMemberIsDeterminedAndInvariant
import YangMills.Construction.TorusOrFourSpace.GluingOfTheDistributionsOfAHierarchy
import YangMills.Construction.TorusOrFourSpace.MembersOfABoundedFamilyAsDistributions
import YangMills.Construction.TorusOrFourSpace.PartsAtAFamilyWithAnEmptyMember
import YangMills.Construction.TorusOrFourSpace.PartsAtAFamilyWithNoEmptyMember
import YangMills.Construction.TorusOrFourSpace.ValuesAtTensorsOfSeparatedSmoothTuples
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.Kind
theorem BoundedHierarchyMembersAreDistributions.holds
    (hEmpty : EmptyMemberBoxProperties.Statement)
    (hNonempty : NonemptyMembersBoxProperties.Statement)
    (hOpen : AdmissibleProductFacts)
    (hGlue : OffDiagDistribGluing)
    (hTensors : SepSmoothTensorValues)
    (hUnique : OffDiagDistribUniqueInvariant) :
    BoundedHierarchyMembersAreDistributions := by
  intro D E C S hS n hn
  obtain ⟨hDistinct, hProducts, -⟩ := hOpen D E n
  obtain ⟨hExists, hOrders⟩ := hGlue D E C S hS n hn
  refine ⟨?_, hDistinct, hProducts, hExists, ?_⟩
  · intro R d G hG
    by_cases hG0 : ∃ i, G i = ∅
    · exact hEmpty D E C S hS n hn R d G hG hG0
    · refine hNonempty D E C S hS n hn R d G hG fun i => ?_
      exact Set.nonempty_iff_ne_empty.mpr fun h => hG0 ⟨i, h⟩
  · intro T hT
    obtain ⟨hOrderOnProducts, hOrder⟩ := hOrders T hT
    obtain ⟨hOnly, hInvariant⟩ := hUnique D E C S hS n hn T hT
    exact ⟨hOrderOnProducts, hOrder, hTensors D E C S hS n hn T hT, hOnly, hInvariant⟩
end YangMills.Construction.PeriodicSpace.Kind
