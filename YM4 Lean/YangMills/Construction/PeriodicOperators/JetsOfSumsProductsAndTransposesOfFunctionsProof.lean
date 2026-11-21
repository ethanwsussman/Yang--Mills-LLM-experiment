import YangMills.Construction.PeriodicOperators.JetOfAProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.JetOfASumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.JetOfATransposeOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.JetsOfSumsProductsAndTransposesOfFunctions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicOperators
theorem JetAlgebra.claim_of_add_comp_transpose
    (hAdd : JetAdd.Claim)
    (hComp : JetComp.Claim)
    (hTr : TransposeJet.Claim) :
    JetAlgebra.Claim := by
  intro r z hr hz F J₁ J₂ J₃ hF hJ₁ hJ₂ hJ₃ εp εm
  exact ⟨fun A B hA hB => hAdd r z hr hz F J₁ J₂ hF hJ₁ hJ₂ εp εm A B hA hB,
    fun A B hA hB => hComp r z hr hz F J₁ J₂ J₃ hF hJ₁ hJ₂ hJ₃ εp εm A B hA hB,
    fun A hA => hTr r z hr hz F J₁ J₂ hF hJ₁ hJ₂ εp εm A hA⟩
end YangMills.Construction.PeriodicOperators
