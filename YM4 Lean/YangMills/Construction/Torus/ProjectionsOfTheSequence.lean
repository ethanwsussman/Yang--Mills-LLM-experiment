import YangMills.Construction.Torus.OneFormsOfTheSequence
import YangMills.Construction.Weighted.ProjectionConstants
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def IsOrthProjOnto (K : Module.End ℝ ↥B.bareSpace) (V : Submodule ℝ ↥B.bareSpace) : Prop :=
  (∀ f, K (K f) = K f) ∧
    (∀ f g : ↥B.bareSpace, B.bareInner (K f) g = B.bareInner f (K g)) ∧
      LinearMap.range K = V
def avgKernel : Submodule ℝ ↥B.bareSpace := LinearMap.ker B.avgOp
def greenAvgRange : Submodule ℝ ↥B.bareSpace :=
  LinearMap.range (B.greenOp ∘ₗ B.avgOpAdjoint)
def lapImageAvgKernel : Submodule ℝ ↥B.bareSpace :=
  B.avgKernel.map B.dirichletLap
def stageOneSitesNbhd : Set D.BareSite :=
  D.bareSites (B.stage 1) ∪
    {x' | ∃ x ∈ D.bareSites (B.stage 1), TorusData.Adjacent x x'}
structure ProjOrthogonality : Prop where
  averaged : B.IsOrthProjOnto B.avgProj B.greenAvgRange
  complementary : B.IsOrthProjOnto B.complProj B.lapImageAvgKernel
  avgKernel_vanishes : ∀ f ∈ B.avgKernel, ∀ x : D.BareSite,
    x ∉ D.bareSites (B.stage 1) → (f : D.BareSite → ℝ) x = 0
  lapImage_vanishes : ∀ f ∈ B.lapImageAvgKernel, ∀ x : D.BareSite,
    x ∉ B.stageOneSitesNbhd → (f : D.BareSite → ℝ) x = 0
  nbhd_subset_region : B.stageOneSitesNbhd ⊆ B.regionSites
  complKernel_indep : ∀ B' : SeparatedChain D, (B'.stage 0).Nonempty →
    (∀ n, 1 ≤ n → n ≤ D.top → B'.stage n = B.stage n) →
    ∀ x : D.BareSite, x ∈ B.regionSites → x ∈ B'.regionSites →
    ∀ (x' : D.BareSite) (h : x' ∈ B.regionSites) (h' : x' ∈ B'.regionSites),
      B'.siteKernel B'.complProj x ⟨x', h'⟩ = B.siteKernel B.complProj x ⟨x', h⟩
def projEnvelope (y y' : D.Space) (factor : ℝ) : ℝ :=
  projBoundConst 4 D.L * (D.scale 0 / B.siteScale y') ^ 4 * factor *
    Real.exp (-(projDecayRate 4 D.L * B.weightedDistance y y'))
open Classical in
structure ProjKernelBounds : Prop where
  site_site : ∀ y y' : ↥B.allSites, ∀ x : D.BareSite, x ∈ B.block y →
    ∀ x' : ↥B.regionSites, (x' : D.BareSite) ∈ B.block y' →
      |B.siteKernel B.avgProj x x'| ≤ B.projEnvelope y y' 1
  bond_site : ∀ y y' : ↥B.allSites, ∀ b : ↥B.starBonds, B.IsAttachedTo b y →
    ∀ x' : ↥B.regionSites, (x' : D.BareSite) ∈ B.block y' →
      |B.gradKernel B.avgProj b x'| ≤ B.projEnvelope y y' (B.siteScale y)⁻¹
  site_bond : ∀ y y' : ↥B.allSites, ∀ x : D.BareSite, x ∈ B.block y →
    ∀ b' : ↥B.starBonds, B.IsAttachedTo b' y' →
      |B.kernelGradAdjoint B.avgProj x b'| ≤ B.projEnvelope y y' (B.siteScale y)⁻¹
  bond_bond : ∀ y y' : ↥B.allSites, ∀ b : ↥B.starBonds, B.IsAttachedTo b y →
    ∀ b' : ↥B.starBonds, B.IsAttachedTo b' y' →
      |B.gradKernelGradAdjoint B.avgProj b b'| ≤
        B.projEnvelope y y' ((B.siteScale y ^ 2)⁻¹)
  compl_kernel_eq : ∀ y y' : ↥B.allSites, ∀ x : D.BareSite, x ∈ B.block y →
    ∀ x' : ↥B.regionSites, (x' : D.BareSite) ∈ B.block y' →
      B.siteKernel B.complProj x x' =
        (if x = (x' : D.BareSite) then 1 else 0) - B.siteKernel B.avgProj x x'
end SeparatedChain
def ProjectionClaim : Prop :=
  (∀ (D : TorusData) (B : SeparatedChain D), (B.stage 0).Nonempty → B.ProjOrthogonality) ∧
    (∀ L : ℕ, Blocking.FourDimOddFactor 4 L →
      0 < projDecayRate 4 L ∧ projDecayRate 4 L ≤ 1) ∧
    ∀ D : TorusData, projBlockFloor D.L ≤ (D.blockNumber : ℝ) →
      projSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ) →
      ∀ B : SeparatedChain D, (B.stage 0).Nonempty → B.ProjKernelBounds
end YangMills.Construction.Weighted
