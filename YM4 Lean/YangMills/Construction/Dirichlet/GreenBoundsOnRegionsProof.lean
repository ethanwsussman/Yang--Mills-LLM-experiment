import YangMills.Construction.Dirichlet.LocalRegionGreenEstimates
import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.Dirichlet.RegionEnergy YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.RegionBounds
section Sums
variable {d : ℕ} {S ξ : ℝ}
theorem abs_le_supNormAll [Finite (LatticeSite d S ξ)] (f : LatticeSite d S ξ → ℝ)
    (x : LatticeSite d S ξ) : |f x| ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.abs_le_supNormAll <;> assumption
theorem supNormAll_nonneg (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem fieldSupNorm_nonneg (F : BondField d S ξ) : 0 ≤ fieldSupNorm F :=
  Real.iSup_nonneg fun _ => supNormAll_nonneg _
end Sums
section Setting
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
variable {𝒮}
theorem mem_shellSites_centreIndex {y : PeriodicTorus d S} (hy : y ∈ 𝒮.centres) :
    y ∈ shellSites L 𝒮.ξ 𝒮.Ω (𝒮.centreIndex y) := by
  obtain ⟨n, -, hn⟩ := hy
  exact Nat.sInf_mem (s := {n | y ∈ shellSites L 𝒮.ξ 𝒮.Ω n}) ⟨n, hn⟩
end Setting
end YangMills.Construction.Dirichlet.RegionBounds
