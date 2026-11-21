import YangMills.Construction.RegionSequence.GaugeLaplacianPositivityProof
import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.DirichletOperator.AveragedSquareInverseOnTheData
import YangMills.Construction.DirichletOperator.LongitudinalKernelOnTheData
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.RegionSequence.OperatorEstimates
import YangMills.Construction.Torus.AveragedSquareExpansion
import YangMills.Construction.Torus.GeometryOfCovers
import YangMills.Construction.Torus.ProjectionsOfTheSequence
import YangMills.Construction.Weighted.ChainSiteSums
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RegionSequence.OperatorEstimates
open Set
open YangMills.Construction.Torus
open YangMills.Construction.RegionSequence.CellStructure
theorem mul_mul_le_mul_mul {b b' u e e' : ℝ} (hb : b ≤ b') (hb' : 0 ≤ b') (hu : 0 ≤ u)
    (he : 0 ≤ e) (he' : e ≤ e') : b * u * e ≤ b' * u * e' :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hu) he).trans
    (mul_le_mul_of_nonneg_left he' (mul_nonneg hb' hu))
theorem mul_mul_mul_le_mul_mul_mul {b b' u e e' s : ℝ} (hb : b ≤ b') (hb' : 0 ≤ b') (hu : 0 ≤ u)
    (he : 0 ≤ e) (he' : e ≤ e') (hs : 0 ≤ s) : b * u * e * s ≤ b' * u * e' * s :=
  mul_le_mul_of_nonneg_right (mul_mul_le_mul_mul hb hb' hu he he') hs
theorem exp_neg_mul_le_of_le {r r' t : ℝ} (hr : r' ≤ r) (ht : 0 ≤ t) :
    Real.exp (-r * t) ≤ Real.exp (-r' * t) := by
  apply Real.exp_le_exp.2
  nlinarith
theorem levelScale_pos (𝒮 : NestedRegions) (y : 𝒮.Point) : 0 < 𝒮.levelScale y := by
  have hL : (0 : ℝ) < 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  exact mul_pos (zpow_pos hL _) 𝒮.ξ_pos
def toBlockSetting (𝒮 : NestedRegions) {M R₁ : ℕ}
    (hs : IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω)
    (hw : ∀ n, 1 - ((𝒮.L : ℝ) ^ 2)⁻¹ ≤ Dirichlet.blockWeights 𝒮.L n ∧
      Dirichlet.blockWeights 𝒮.L n ≤ 1) :
    Dirichlet.BlockSetting 4 𝒮.L (1 - ((𝒮.L : ℝ) ^ 2)⁻¹) 1 𝒮.side where
  ξ := 𝒮.ξ
  M := M
  R₁ := R₁
  t := 𝒮.s
  Ω := 𝒮.Ω
  a := Dirichlet.blockWeights 𝒮.L
  isSeparatedChain := hs
  weight_mem := fun n _ => hw n
section GreenOperator
variable (𝒮 : NestedRegions) {M R₁ : ℕ}
  (hs : IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω)
  (hw : ∀ n, 1 - ((𝒮.L : ℝ) ^ 2)⁻¹ ≤ Dirichlet.blockWeights 𝒮.L n ∧
    Dirichlet.blockWeights 𝒮.L n ≤ 1)
theorem restrictTo_of_mem {f : 𝒮.FineSite → ℝ} (hf : f ∈ 𝒮.siteFns) :
    Dirichlet.restrictTo (𝒮.Ω 0) f = f := by apply _root_.YangMills.Construction.RegionSequence.GaugeLapPositivityProof.projSites_eq_self_of_mem <;> assumption
def averagingOp (g : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  (toBlockSetting 𝒮 hs hw).averagingOp g
end GreenOperator
theorem supNormAll_nonneg {S ξ : ℝ} (f : Dirichlet.LatticeSite 4 S ξ → ℝ) :
    0 ≤ Dirichlet.supNormAll f :=
  Real.sSup_nonneg (by
    rintro _ ⟨x, -, rfl⟩
    exact abs_nonneg _)
theorem fieldSupNorm_nonneg {S ξ : ℝ} (F : Dirichlet.BondField 4 S ξ) :
    0 ≤ Dirichlet.fieldSupNorm F :=
  (supNormAll_nonneg (F 0)).trans (le_ciSup (f := fun μ => Dirichlet.supNormAll (F μ))
    (Set.finite_range _).bddAbove 0)
section DataBonds
variable {𝒮 : NestedRegions} {M R₁ : ℕ} (h : 𝒮.IsTorusData M R₁)
theorem scale_zero : h.toTorusData.scale 0 = 𝒮.ξ := by
  change (𝒮.L : ℝ) ^ 0 * 𝒮.ξ = 𝒮.ξ
  simp
variable {h} (B : Weighted.SeparatedChain h.toTorusData)
end DataBonds
section KernelEstimates
variable (hGreen : DirichletGreen.GreenBoundsClaim) (hForms : Dirichlet.Forms.FormsAndOperatorsHold)
  (hCells : CellStructureClaim) (hSettings : RegionSequence.SettingsCoherent)
  (hSums : Weighted.ChainSiteSumBounds)
  (hCover : Weighted.CoverGeometry)
  (hExpansion : Weighted.InverseExpansionTheorem)
  (hProjections : Weighted.ProjectionClaim)
  (hInverse : TorusDataComparison.AvgGreenSqInvAgreesClaim)
  (hLongitudinal : TorusDataKernel.LongKernelMatchesData)
end KernelEstimates
end YangMills.Construction.RegionSequence.OperatorEstimates
end
