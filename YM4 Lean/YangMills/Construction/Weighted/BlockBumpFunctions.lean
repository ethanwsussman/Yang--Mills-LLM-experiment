import YangMills.Construction.Weighted.FunctionSpaces
import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
namespace TorusData
variable {D : TorusData}
def bareLaplacian (f : D.BareSite → ℝ) (x : D.BareSite) : ℝ :=
  (D.scale 0)⁻¹ *
    (∑ᶠ b ∈ {b : D.Bond | b.target = x}, bondGrad f b -
      ∑ᶠ b ∈ {b : D.Bond | b.source = x}, bondGrad f b)
end TorusData
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
structure IsBlockBump (y : D.Space) (φ : D.BareSite → ℝ) : Prop where
  vanishes_of_not_mem : ∀ x, x ∉ B.block y → φ x = 0
  sum_eq : ∑ᶠ x ∈ B.block y, φ x = (D.L : ℝ) ^ (B.level y * 4)
  abs_laplacian_le : ∀ x, |TorusData.bareLaplacian φ x| ≤
    testLaplacianConst 4 * (B.siteScale y ^ 2)⁻¹
end SeparatedChain
def BlockBumpsExist : Prop :=
  ∀ G : GivenChain, ∀ y ∈ G.chain.allSites, ∃ φ : G.data.BareSite → ℝ,
    G.chain.IsBlockBump y φ
end YangMills.Construction.Weighted
end
