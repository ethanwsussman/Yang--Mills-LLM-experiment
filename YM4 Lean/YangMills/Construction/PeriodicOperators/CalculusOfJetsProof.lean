import YangMills.Construction.PeriodicOperators.AdditivityAndIntegralOfTheLogarithmicNumber
import YangMills.Construction.PeriodicOperators.AssociativityAndNormOfProductsOfJets
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.CyclicityAndTransposeOfTheTraceNumber
import YangMills.Construction.PeriodicOperators.DerivativeOfTheLogarithmicNumberAlongAFamily
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJet
import YangMills.Construction.PeriodicOperators.JetsOfSumsProductsAndTransposesOfFunctions
import YangMills.Construction.PeriodicOperators.LogarithmicNumberOfBlockTriangularJets
import YangMills.Construction.PeriodicOperators.TransposesOfProductsOfJets
import YangMills.Construction.PeriodicOperators.VanishingProductsOfThreeJets
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicOperators
theorem JetCalculus.claim_holds
    (h₁ : JetProductsAssocAndNormLe)
    (h₂ : JetTranspose.Claim)
    (h₃ : JetAlgebra.Claim)
    (h₄ : TripleJets.VanishOnStrip)
    (h₅ : JetInverse.Claim)
    (h₆ : TraceNumberSymmetry.Claim)
    (h₇ : JetLogNumber.Claim)
    (h₈ : BlockTriangularLog.Claim)
    (h₉ : LogNumberDerivAlongFamily.Claim) :
    JetCalculus.Claim :=
  fun δ p hδ hp =>
    ⟨h₁ δ p hδ hp, h₂ δ p hδ hp, h₃ δ p hδ hp, h₄ δ p hδ hp, h₅ δ p hδ hp, h₆ δ p hδ hp,
      h₇ δ p hδ hp, h₈ δ p hδ hp, h₉ δ p hδ hp⟩
end YangMills.Construction.PeriodicOperators
