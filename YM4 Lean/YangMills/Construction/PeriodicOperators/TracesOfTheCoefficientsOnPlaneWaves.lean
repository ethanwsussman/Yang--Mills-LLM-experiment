import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import YangMills.Construction.PeriodicOperators.MatricesOfTheCoefficientsOnATorus
import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.PlaneWaveTraces
open JetDomains (IsLiftOf)
open RiemannSums (periodLattice classSum)
open JetQuad (logDensity)
def Claim : Prop :=
  ∀ F I : PeriodicData, IsPeriodic F → IsPeriodic I →
    ∀ (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (ρ R : ℝ), IsLocalWith F I I T ρ R →
    (∀ κ : InfiniteLattice.AmbientSpace,
      IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
        Module.End ℂ (I.UnitQuot → ℂ))) →
    ∀ s : ℕ, 0 < s → 4 * R < s →
      (∀ p ∈ dualLattice s, ∀ p' ∈ dualLattice s, p + p' ∉ periodLattice → ∀ a a' : F.UnitQuot → ℂ,
        ∀ ζ ζ' : F.QuotMod s → ℂ,
          IsLiftOf F s ζ (blochWave F (toComplexVec p) a) →
          IsLiftOf F s ζ' (blochWave F (toComplexVec p') a') →
          LinearMap.trace ℂ (I.QuotMod s → ℂ)
              (Ring.inverse (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
                  Module.End ℂ (I.QuotMod s → ℂ)) *
                periodicCoeffTwoMatrix F I T s ζ ζ') = 0 ∧
            LinearMap.trace ℂ (I.QuotMod s → ℂ)
              (Ring.inverse (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
                  Module.End ℂ (I.QuotMod s → ℂ)) *
                periodicCoeffOneMatrix F I T s ζ *
                Ring.inverse (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
                  Module.End ℂ (I.QuotMod s → ℂ)) *
                periodicCoeffOneMatrix F I T s ζ') = 0) ∧
      ∀ p ∈ dualLattice s, ∀ u v : F.UnitQuot → ℂ, ∀ ζu ζv : F.QuotMod s → ℂ,
        IsLiftOf F s ζu (blochWave F (toComplexVec p) u) →
        IsLiftOf F s ζv (blochWave F (-toComplexVec p) v) →
        LinearMap.trace ℂ (I.QuotMod s → ℂ)
            (Ring.inverse (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
                Module.End ℂ (I.QuotMod s → ℂ)) *
              periodicCoeffTwoMatrix F I T s ζu ζv) -
          LinearMap.trace ℂ (I.QuotMod s → ℂ)
            (Ring.inverse (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
                Module.End ℂ (I.QuotMod s → ℂ)) *
              periodicCoeffOneMatrix F I T s ζu *
              Ring.inverse (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
                Module.End ℂ (I.QuotMod s → ℂ)) *
              periodicCoeffOneMatrix F I T s ζv) =
          classSum s
            (logDensity (toComplexVec p)
              (jetAlong F I I T (toComplexVec p) u v))
end YangMills.Construction.PeriodicOperators.PlaneWaveTraces
end
