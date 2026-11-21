import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
def HalvesIntegralFactorization : Prop :=
  ∀ (Λ : PeriodSublattice 1) (v : AmbientSpace) (hv : v ∈ normalSet) (k : ℤ),
    Λ.SplitsAlongWithHalfPeriod v k → ∀ (c : ℝ) (hc : IsAllowedLevel 1 v c),
      let P : NormalLevelPair 1 := ⟨v, hv, c, hc⟩
      ∀ G ∈ Λ.plusAlgebra v k c, ∀ G' ∈ Λ.plusAlgebra v k c,
        ∀ g ∈ Λ.boundedAlgebra (Λ.sharedLinks v k c),
          ∫ U, g U * Λ.conjReflect P G' U * G U ∂Λ.quotientHaar =
            ∫ U, g U * conj (Λ.integrateOut (Λ.sharedLinks v k c)ᶜ G' U) *
              Λ.integrateOut (Λ.sharedLinks v k c)ᶜ G U ∂Λ.quotientHaar
end YangMills.Construction.InfiniteLattice
