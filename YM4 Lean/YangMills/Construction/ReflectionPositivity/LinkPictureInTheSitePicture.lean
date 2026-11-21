import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (IsBoundedObservable axisStep shift halfSpaceLocalObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect siteReflect linkReflectionForm)
open YangMills.Construction.FormHilbert
variable (ν : unitPositiveClass) (μ : Fin 4)
def transferSqrt : ReflectionPair.site.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ :=
  (ReflectionPair.site.jointPVM ν μ).spectralOp fun q => (((q.1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)
def transferKernelOrth : Submodule ℂ (ReflectionPair.site.Hilb ν μ) :=
  (LinearMap.ker (ReflectionPair.site.transferOp ν μ :
    ReflectionPair.site.Hilb ν μ →ₗ[ℂ] ReflectionPair.site.Hilb ν μ))ᗮ
theorem coe_transferKernelOrth :
    (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ)) =
      orthSet {ψ | ReflectionPair.site.transferOp ν μ ψ = 0} := by
  ext χ
  change χ ∈ (LinearMap.ker _)ᗮ ↔ _
  rw [Submodule.mem_orthogonal]
  rfl
def IsLinkSiteIntertwiner
    (W : ReflectionPair.link.Hilb ν μ →ₗ[ℂ] transferKernelOrth ν μ) : Prop :=
  IsUnitaryLinearMap W ∧ ∀ F ∈ halfSpaceLocalObservables μ,
    (W (ReflectionPair.link.obsClass ν μ F) : ReflectionPair.site.Hilb ν μ) =
      transferSqrt ν μ (ReflectionPair.site.obsClass ν μ F)
def linkSiteIntertwiner : ReflectionPair.link.Hilb ν μ →ₗ[ℂ] transferKernelOrth ν μ :=
  Classical.epsilon (IsLinkSiteIntertwiner ν μ)
def LinkPictureEmbedsInSitePicture : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4),
    ((linkReflect μ).toFun = (siteReflect μ).toFun ∘ (shift (axisStep 1 μ)).toFun ∧
      (siteReflect μ).toFun = (shift (axisStep 1 μ)).toFun ∘ (linkReflect μ).toFun ∧
      ∀ F, IsBoundedObservable F →
        (linkReflect μ).actOn F =
            (siteReflect μ).actOn ((shift (axisStep 1 μ)).actOn F) ∧
          (siteReflect μ).actOn F =
            (shift (axisStep 1 μ)).actOn ((linkReflect μ).actOn F)) ∧
    (∀ F H : halfSpaceLocalObservables μ,
      linkReflectionForm ν μ F H =
        inner ℂ (ReflectionPair.site.obsClass ν μ F)
          (ReflectionPair.site.transferOp ν μ (ReflectionPair.site.obsClass ν μ H))) ∧
    ((∃! W, IsLinkSiteIntertwiner ν μ W) ∧
      IsLinkSiteIntertwiner ν μ (linkSiteIntertwiner ν μ) ∧
      (∀ ψ, (linkSiteIntertwiner ν μ (ReflectionPair.link.transferOp ν μ ψ) :
          ReflectionPair.site.Hilb ν μ) =
        ReflectionPair.site.transferOp ν μ (linkSiteIntertwiner ν μ ψ)) ∧
      ∀ (t : TransverseAxis μ) ψ,
        (linkSiteIntertwiner ν μ (ReflectionPair.link.shiftOp ν μ t ψ) :
            ReflectionPair.site.Hilb ν μ) =
          ReflectionPair.site.shiftOp ν μ t (linkSiteIntertwiner ν μ ψ)) ∧
    Function.Injective (ReflectionPair.link.transferOp ν μ)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
