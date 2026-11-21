import YangMills.Construction.DirichletOperator.BoundsOnTheOperatorsOfASeparatedSequenceProof
import YangMills.Construction.RegionSequence.GaugeLaplacianPositivityProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.TorusDataKernel
open YangMills.Construction.RegionSequence.TorusDataComparison
variable {𝒮 : NestedRegions} {M R₁ : ℕ} {h : 𝒮.IsTorusData M R₁}
variable {B : Weighted.SeparatedChain h.toTorusData}
theorem projSites_of_mem {f : 𝒮.FineSite → ℝ} (hf : f ∈ 𝒮.siteFns) :
    NestedRegions.projSites f = f := by apply _root_.YangMills.Construction.RegionSequence.GaugeLapPositivityProof.projSites_eq_self_of_mem <;> assumption
end YangMills.Construction.RegionSequence.TorusDataKernel
