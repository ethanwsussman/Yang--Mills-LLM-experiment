import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import YangMills.Construction.PeriodicOperators.MatricesOfTheCoefficientsOnATorus
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
def Claim : Prop :=
  ∀ F I : PeriodicData, IsPeriodic F → IsPeriodic I →
    ∀ (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (ρ R : ℝ), IsLocalWith F I I T ρ R →
    ∀ s : ℕ, 0 < s → 4 * R < s →
      IsLinearMap ℂ (periodicCoeffOneMatrix F I T s) ∧
      (∀ ζ', IsLinearMap ℂ fun ζ => periodicCoeffTwoMatrix F I T s ζ ζ') ∧
      (∀ ζ, IsLinearMap ℂ (periodicCoeffTwoMatrix F I T s ζ)) ∧
      (∀ ζ ζ', periodicCoeffTwoMatrix F I T s ζ ζ' = periodicCoeffTwoMatrix F I T s ζ' ζ) ∧
      ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s),
        (∀ c' c, IsHolomorphicScalarIn (openPolydisk 0 ρ)
          fun z : Coordinates.ComplexCoordinates N =>
            linearMapEntry (linearMapOfEntries (descendMatrix I I s
              (periodicValue F I I T s fun d => z (e.symm d)))) c' c) ∧
        (∀ c' c, (fun z : Coordinates.ComplexCoordinates N =>
            linearMapEntry (linearMapOfEntries (descendMatrix I I s
              (periodicValue F I I T s fun d => z (e.symm d)))) c' c -
            (linearMapEntry (linearMapOfEntries (descendMatrix I I s
                (periodicValue F I I T s 0))) c' c +
              linearMapEntry (periodicCoeffOneMatrix F I T s fun d => z (e.symm d)) c' c +
              (1 / 2 : ℂ) * linearMapEntry (periodicCoeffTwoMatrix F I T s
                (fun d => z (e.symm d)) fun d => z (e.symm d)) c' c))
          =O[𝓝 0] fun z : Coordinates.ComplexCoordinates N => ‖z‖ ^ 3) ∧
        ((∀ ζ : F.Carrier → ℂ, (∀ κ, (ζ κ).im = 0) → InLocalDomain F I I T ζ →
            ∀ ι' ι, (T ζ ι' ι).im = 0) →
          ∀ v : Fin N → ℝ, (∀ j, |v j| < ρ) → ∀ c' c,
            (linearMapEntry (linearMapOfEntries (descendMatrix I I s
              (periodicValue F I I T s fun d => (v (e.symm d) : ℂ)))) c' c).im = 0)
end YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates
end
