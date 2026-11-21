import YangMills.Construction.FamiliesOfLimits.FamiliesOfLimitsAlongGrowingTori
import YangMills.Construction.GrowingTori.BoundFunctionsHierarchiesAndCentredMomentsOfFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open AmbientPoints
open ToriLimits
namespace FamiliesOfLimits.LimitFamilyAsVolumeLimit
def HierarchyAgrees {Y : PeriodicSpace.Params} (Φ : EuclidHierarchy Y)
    {s : Conventions.StandingParameters} (S : SeparatedTupleFunctions s) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : separatedTuples s .euclidean n)
    (hX : X.1 ∈ PeriodicSpace.Kind.sepC1Tuples Y .euclidean n),
    S n hn X = ((Φ.func n hn ⟨X.1, hX⟩ : ℝ) : ℂ)
end FamiliesOfLimits.LimitFamilyAsVolumeLimit
end YangMills.Construction
end
