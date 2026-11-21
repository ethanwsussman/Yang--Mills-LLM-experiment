import YangMills.Construction.InfiniteLattice.CubicTorusOfACutoffIsAPeriodicExtension
import YangMills.Construction.InfiniteLattice.DescentOfAnArrayToATorusIsDefined
import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusIsFaithful
import YangMills.Construction.InfiniteLattice.PerturbedSpecificationOfAnArrayIsDefined
import YangMills.Construction.InfiniteLattice.SubgroupsOfFiniteIndexContainCubicLattices
import YangMills.Construction.InfiniteLattice.SupportsOfAnArrayAreLocallyFinite
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithful
import YangMills.Construction.InfiniteLattice.WilsonMeasuresOfATorusAreProbabilities
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.InfiniteLattice
theorem toriArraysAndTiltedMeasuresFacts_holds
    (hfaithful : QuotientTorusFaithful.Statement)
    (hlift : PeriodicLiftIsFaithful)
    (hprob : QuotientGibbsMeasuresProbability.Statement)
    (hsupp : ArraySupportsLocallyFinite)
    (hkernel : TiltedKernelOfArrayIsWellDefined)
    (hdescent : PeriodicDescentDefined.Statement)
    (hcubic : FiniteIndexSubgroupsContainCubicSublattices)
    (hcutoff : CubicTorusAtCutoffLifts.Statement) :
    ToriArraysAndTiltedMeasuresFacts := fun β hβ =>
  ⟨fun a ha Γ => ⟨hfaithful a ha Γ, hlift a ha Γ, hprob β hβ a ha Γ⟩,
    fun 𝔸 t => ⟨hsupp 𝔸, hkernel β hβ 𝔸 t, fun Γ h => hdescent β hβ 𝔸 t Γ h⟩,
    hcubic, fun d => hcutoff β hβ d⟩
end YangMills.Construction.InfiniteLattice
