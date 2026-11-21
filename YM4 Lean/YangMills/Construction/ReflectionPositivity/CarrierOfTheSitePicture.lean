import YangMills.Construction.ReflectionPositivity.SetOfTheSpectralVariablesThatCarriesTheSpectrum
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.FormHilbert (StrongTendsto)
def SiteCarrierFacts : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4),
  (∃ hC : IsClosed (imageInSpectrum μ (siteCone μ)),
    (ReflectionPair.site.jointPVM ν μ).IsSupportedOn ⟨_, hC.measurableSet⟩) ∧
  (∀ x ∈ siteCone μ,
    (x.1 = 0 → x.2 = 0) ∧
    (x.1 ≠ ⊤ → (∀ l, Real.cosh x.1.toReal + Real.cos (x.2 l) ≥ 2) ∧
      x.1.toReal ≥ slopeConstant * angleSupNorm μ x.2)) ∧
  (∀ l : TransverseAxis μ,
    ReflectionPair.site.shiftOp ν μ l * groundProjection μ ReflectionPair.site ν =
        groundProjection μ ReflectionPair.site ν ∧
      groundProjection μ ReflectionPair.site ν * ReflectionPair.site.shiftOp ν μ l =
        groundProjection μ ReflectionPair.site ν) ∧
  (∀ n : ℕ, ReflectionPair.site.transferOp ν μ ^ n * groundProjection μ ReflectionPair.site ν =
    groundProjection μ ReflectionPair.site ν) ∧
  StrongTendsto (fun n => ReflectionPair.site.transferOp ν μ ^ n)
    (groundProjection μ ReflectionPair.site ν)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
