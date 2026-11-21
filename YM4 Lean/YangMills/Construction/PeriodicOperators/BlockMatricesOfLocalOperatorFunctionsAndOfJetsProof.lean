import YangMills.Construction.PeriodicOperators.BlockMatricesOfJetsAreJets
import YangMills.Construction.PeriodicOperators.BlockMatricesOfLocalOperatorFunctionsAndOfJets
import YangMills.Construction.PeriodicOperators.BlockMatricesOfLocalOperatorFunctionsAreLocal
import YangMills.Construction.PeriodicOperators.ClassesOfTheCopiesOfIndexSets
import YangMills.Construction.PeriodicOperators.CopiesAndUnionsOfPeriodicIndexSets
import YangMills.Construction.PeriodicOperators.JetsCarriedOverToCopies
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsCarriedOverToCopies
import YangMills.Construction.PeriodicOperators.MultiplesOfLocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.ProductsOfBlockMatricesOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockJets
theorem allConjuncts_holds
    (hCopies : CopiesUnions.Claim)
    (hMultiples : OpFunMultiples.Claim)
    (hJets : BlockJetsAreJets.Claim)
    (hProducts : BlockJetProducts.Claim)
    (hLocal : BlockLocality.Claim)
    (hQuot : CopyQuotients.Claim)
    (hCopyFun : CopyOpFuns.Claim)
    (hCopyJets : CopyJets.Claim) : AllConditions :=
  ⟨hCopies, fun F hF δ p hδ hp εPlus εMinus =>
    ⟨hMultiples F hF δ p hδ hp εPlus εMinus,
      fun J hJ => ⟨hJets δ p hδ hp J hJ, hProducts δ p hδ hp J hJ,
        hLocal F hF δ p hδ hp εPlus εMinus J hJ⟩,
      fun V hV => ⟨hQuot V hV, hCopyFun F hF δ p hδ hp εPlus εMinus V hV,
        hCopyJets δ p hδ hp V hV⟩⟩⟩
end YangMills.Construction.PeriodicOperators.BlockJets
end
