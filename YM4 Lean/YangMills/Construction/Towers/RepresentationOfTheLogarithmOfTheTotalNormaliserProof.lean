import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPoint
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsGaugeInvariant
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsRealAnalyticNearOne
import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserIsTheFunctional
import YangMills.Construction.Towers.RepresentationOfTheLogarithmOfTheTotalNormaliser
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem logNormaliserRepresentation_holds
    (h₁ : BackgroundFunctionalWellDefinedAtTrivialField)
    (h₂ : BackgroundFunctionalAnalyticNearIdentityAtEverySide)
    (h₃ : BackgroundFunctionalIsGaugeInvariant)
    (h₄ : LogTotalNormaliserEqFunctional) :
    LogNormaliserRepresentationHolds :=
  fun L n k hL hn hk => ⟨h₁ L n k hL hn hk, h₂ L n k hL hn hk, h₃ L n k hL hn hk, h₄ L n k hL hn hk⟩
end YangMills.Construction.Tower
