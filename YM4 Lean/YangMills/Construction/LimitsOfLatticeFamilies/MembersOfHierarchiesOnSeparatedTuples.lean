import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def SepTupleMembers.Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace), ∀ P : HierarchySequence s Y, ∀ n, 2 ≤ n →
    (∀ j ∈ P.indices,
      ModelSpace.sepTuplesIn s Y n (P.rad j) ⊆ ModelSpace.lipSepTuplesIn s Y n (P.rad j) ∧
      (P.restrictSeq j n).IsSymm ∧
      ModelSpace.IsMultilinearSep (P.restrictSeq j n) ∧
      ∀ d R : ℝ, 0 < d → 0 < R → ∀ f ∈ ModelSpace.lipTuplesApart s Y n d R,
        (∀ i, ModelSpace.supportIn s Y (f i) ⊆ ModelSpace.ballAtBase s Y (P.rad j)) →
          f ∈ ModelSpace.lipSepTuplesIn s Y n (P.rad j)) ∧
    (∀ K : Set (Y.Carrier s), ModelSpace.IsCompactIn s Y K →
      EventuallyIn P.indices fun j => K ⊆ ModelSpace.ballAtBase s Y (P.rad j)) ∧
    ∀ f ∈ ModelSpace.sepTuples s Y n,
      EventuallyIn P.indices fun j =>
        f ∈ ModelSpace.sepTuplesIn s Y n (P.rad j) ∧ j ∈ P.definedAt f
end YangMills.Construction.LatticeLimits
end
