import YangMills.Construction.Dirichlet.WalkExpansionTerms
import YangMills.Construction.Dirichlet.WeightedDistance
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.RegroupedFactors
variable {d L : ℕ} {S aMinus aPlus : ℝ}
def commutatorSource (B : BlockSetting d L aMinus aPlus S) (Q Q' : CentredCube d S)
    (ψ : LatticeSite d S B.ξ → ℝ) : LatticeSite d S B.ξ → ℝ :=
  pointwiseMul (B.latticeCutoff Q) (B.commutatorOp (B.latticeCutoff Q') ψ)
end YangMills.Construction.Dirichlet.RegroupedFactors
