import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRule
import YangMills.Construction.Torus.ExponentialSumsOverSitesAndExpansionsProof
import YangMills.Construction.Torus.FloorOfTheInverseBounds
import YangMills.Construction.Torus.GeometryOfCubesAndCutSequences
import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
theorem ChangeSiteSum.shellSitesUnion_finite {D : ScaleData} (B : SeparatedChain D) :
    B.shellSitesUnion.Finite := by apply _root_.YangMills.Construction.GeneralTorus.ScaledDistExpSums.shellSitesUnion_finite <;> assumption
end YangMills.Construction.GeneralTorus
