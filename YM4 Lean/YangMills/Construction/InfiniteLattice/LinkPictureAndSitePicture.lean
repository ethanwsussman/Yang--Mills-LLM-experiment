import YangMills.Construction.HilbertSpaces.FunctionsOfAPositiveContractionAndItsSquareRoot
import YangMills.Construction.InfiniteLattice.SitePictures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert ContractionUnitary
namespace LatticeConventions.LinkSiteComparison
open InfiniteLattice (GaugeField)
section Objects
variable (a : Spacing) (μ : Direction) (ν : Measure (GaugeField (a : ℝ)))
  [IsProbabilityMeasure ν]
def MapsClassToSqrtTransfer
    (W : BddOpBetween (LinkFrame.LinkHilbertSpace a μ ν) (SiteFrame.SiteHilbertSpace a μ ν)) :
    Prop :=
  ∀ (F : LinkFrame.upperAlgebra a μ) (hF : F.1 ∈ SiteFrame.upperSpace a μ),
    W (LinkFrame.linkClass a μ ν F) =
      contractionSqrt (SiteFrame.transferOperator a μ ν)
        (SiteFrame.siteClass a μ ν ⟨F.1, hF⟩)
def linkToSite :
    BddOpBetween (LinkFrame.LinkHilbertSpace a μ ν) (SiteFrame.SiteHilbertSpace a μ ν) :=
  Classical.epsilon (MapsClassToSqrtTransfer a μ ν)
def siteKernelOrth : Submodule ℂ (SiteFrame.SiteHilbertSpace a μ ν) :=
  (LinearMap.ker (SiteFrame.transferOperator a μ ν :
    SiteFrame.SiteHilbertSpace a μ ν →ₗ[ℂ] SiteFrame.SiteHilbertSpace a μ ν))ᗮ
theorem coe_siteKernelOrth :
    (siteKernelOrth a μ ν : Set (SiteFrame.SiteHilbertSpace a μ ν)) =
      orthSet (linearKer (SiteFrame.transferOperator a μ ν :
        SiteFrame.SiteHilbertSpace a μ ν →ₗ[ℂ] SiteFrame.SiteHilbertSpace a μ ν)) := by
  ext χ
  change χ ∈ (LinearMap.ker _)ᗮ ↔ _
  rw [Submodule.mem_orthogonal']
  rfl
def LinkFormEqSiteFormTransfer : Prop :=
  ∀ (F G : LinkFrame.upperAlgebra a μ) (hF : F.1 ∈ SiteFrame.upperSpace a μ)
    (hG : G.1 ∈ SiteFrame.upperSpace a μ),
    LinkFrame.linkForm a μ ν F G =
      ⟪SiteFrame.siteClass a μ ν ⟨F.1, hF⟩,
        SiteFrame.transferOperator a μ ν (SiteFrame.siteClass a μ ν ⟨G.1, hG⟩)⟫_ℂ
def LinkToSiteUnitaryIntertwines : Prop :=
  MapsClassToSqrtTransfer a μ ν (linkToSite a μ ν) ∧
  (∀ W, MapsClassToSqrtTransfer a μ ν W → W = linkToSite a μ ν) ∧
  IsClosedSet (siteKernelOrth a μ ν : Set (SiteFrame.SiteHilbertSpace a μ ν)) ∧
  (∃ U : LinkFrame.LinkHilbertSpace a μ ν →ₗ[ℂ] siteKernelOrth a μ ν,
    (∀ ψ, (U ψ : SiteFrame.SiteHilbertSpace a μ ν) = linkToSite a μ ν ψ) ∧
      IsUnitaryMap U) ∧
  (linkToSite a μ ν).comp (LinkFrame.transferOperator a μ ν) =
    (SiteFrame.transferOperator a μ ν).comp (linkToSite a μ ν) ∧
  ∀ l : {d : Direction // d ≠ μ},
    (linkToSite a μ ν).comp (LinkFrame.transverseShift a μ ν l) =
      (SiteFrame.transverseShift a μ ν l).comp (linkToSite a μ ν)
def TransferInjective : Prop :=
  linearKer (LinkFrame.transferOperator a μ ν :
    LinkFrame.LinkHilbertSpace a μ ν →ₗ[ℂ] LinkFrame.LinkHilbertSpace a μ ν) = {0}
end Objects
def Statement : Prop :=
  ∀ (a : Spacing) (μ : Direction) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν],
    LinkFrame.IsAdmissibleState a μ ν →
    LinkFormEqSiteFormTransfer a μ ν ∧
      LinkToSiteUnitaryIntertwines a μ ν ∧
      TransferInjective a μ ν
end LatticeConventions.LinkSiteComparison
end YangMills.Construction
end
