import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet
namespace DirichletGreen
variable {d L : ℕ} {S lo hi : ℝ}
section Nonneg
variable {ξ : ℝ}
end Nonneg
theorem supNorm_zero_nonpos : Torus.supNorm (0 : Torus.PeriodicTorus d S) ≤ 0 := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_zero_le <;> assumption
variable (𝒮 : BlockSetting d L lo hi S)
namespace GreenConstants
variable {𝒮}
end GreenConstants
end DirichletGreen
namespace SeparatedClasses
open DirichletGreen
end SeparatedClasses
end YangMills.Construction
end
