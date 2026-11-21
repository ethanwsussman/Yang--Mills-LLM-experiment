import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.SitePictures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert ContractionUnitary
namespace LatticeConventions
open InfiniteLattice (GaugeField IsBoundedObservable axisStep shift)
def LinkReflectionEqShiftedSite (a : Spacing) (μ : Direction) : Prop :=
  (∀ x : Point,
    (SiteFrame.siteReflection a μ).toFun (x + (a : ℝ) • basisVector μ) =
        x + (a : ℝ) • basisVector μ - (2 * (x μ + (a : ℝ))) • basisVector μ ∧
      x + (a : ℝ) • basisVector μ - (2 * (x μ + (a : ℝ))) • basisVector μ =
        x - (2 * x μ + (a : ℝ)) • basisVector μ) ∧
  LinkFrame.linkReflection a μ =
    (SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ)) ∧
  ∀ F : GaugeField (a : ℝ) → ℂ, IsBoundedObservable F →
    (LinkFrame.linkReflection a μ).actOn F =
      (SiteFrame.siteReflection a μ).actOn
        ((shift (axisStep (a : ℝ) μ)).actOn F)
def LinkFrame.TransferMatrixElements (a : Spacing) (μ : Direction)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν] : Prop :=
  IsSymmetricOp (transferOperator a μ ν) ∧
  OpGE (transferOperator a μ ν) 0 ∧
  OpLE (transferOperator a μ ν) (idOp (LinkHilbertSpace a μ ν)) ∧
  (∀ lam : {l : Direction // l ≠ μ},
    IsUnitaryMap (transverseShift a μ ν lam : LinkHilbertSpace a μ ν →ₗ[ℂ] LinkHilbertSpace a μ ν)) ∧
  (∀ lam : {l : Direction // l ≠ μ},
    Commute (transferOperator a μ ν) (transverseShift a μ ν lam)) ∧
  (∀ lam lam' : {l : Direction // l ≠ μ},
    Commute (transverseShift a μ ν lam) (transverseShift a μ ν lam')) ∧
  DenseRange (linkClass a μ ν) ∧
  ∀ (F F' : upperAlgebra a μ) (lam : {l : Direction // l ≠ μ}) (n : ℕ) (y : ℤ),
    ⟪linkClass a μ ν F,
        (transferOperator a μ ν ^ n * zpowOp (transverseShift a μ ν lam) y)
          (linkClass a μ ν F')⟫_ℂ =
      ∫ U, conjFun ((linkReflection a μ).actOn F.1) U *
        (shift (n • axisStep (a : ℝ) μ + y • axisStep (a : ℝ) lam.1)).actOn F'.1 U ∂ν
def SiteFrame.TransferMatrixElements (a : Spacing) (μ : Direction)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν] : Prop :=
  IsSymmetricOp (transferOperator a μ ν) ∧
  OpGE (transferOperator a μ ν) 0 ∧
  OpLE (transferOperator a μ ν) (idOp (SiteHilbertSpace a μ ν)) ∧
  (∀ lam : {l : Direction // l ≠ μ},
    IsUnitaryMap (transverseShift a μ ν lam : SiteHilbertSpace a μ ν →ₗ[ℂ] SiteHilbertSpace a μ ν)) ∧
  (∀ lam : {l : Direction // l ≠ μ},
    Commute (transferOperator a μ ν) (transverseShift a μ ν lam)) ∧
  (∀ lam lam' : {l : Direction // l ≠ μ},
    Commute (transverseShift a μ ν lam) (transverseShift a μ ν lam')) ∧
  DenseRange (siteClass a μ ν) ∧
  ∀ (F F' : upperSpace a μ) (lam : {l : Direction // l ≠ μ}) (n : ℕ) (y : ℤ),
    ⟪siteClass a μ ν F,
        (transferOperator a μ ν ^ n * zpowOp (transverseShift a μ ν lam) y)
          (siteClass a μ ν F')⟫_ℂ =
      ∫ U, conjFun ((siteReflection a μ).actOn F.1) U *
        (shift (n • axisStep (a : ℝ) μ + y • axisStep (a : ℝ) lam.1)).actOn F'.1 U ∂ν
def CoordinatePictureOperators : Prop :=
  ∀ (a : Spacing) (μ : Direction) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν],
    LinkFrame.IsAdmissibleState a μ ν →
      LinkReflectionEqShiftedSite a μ ∧
      LinkFrame.TransferMatrixElements a μ ν ∧
      SiteFrame.TransferMatrixElements a μ ν
end LatticeConventions
end YangMills.Construction
end
