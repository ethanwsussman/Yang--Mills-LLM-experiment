import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.MeasuresOfATorusOfAnyShapeWithAndWithoutAnArray
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
variable {a : ℝ}
def LinearMapPreservesPeriods (Γ : PeriodSublattice a) (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) :
    Prop :=
  w '' (Subtype.val '' (Γ.periods : Set (LatticePoint a))) =
    Subtype.val '' (Γ.periods : Set (LatticePoint a))
def TorusMeasureCovariance : Prop :=
  ∀ (a β : ℝ), 0 < a → 0 < β →
    ∀ (A : SingleGeneratorArray a) (t : ℝ) (Γ : PeriodSublattice a) (h : A.PeriodsWithin Γ),
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        ∫ U, F U ∂(A.liftedTiltMeasure h β t) =
          ∫ U, Γ.periodize F U ∂(A.tiltMeasure h β t)) ∧
      (∀ (r : LatticeSymmetry a) (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace),
        IsLinearPart a r.toFun w → LinearMapPreservesPeriods Γ w →
          (∃ ρ : Γ.QuotientField ≃ₜ Γ.QuotientField,
            MeasurePreserving ρ Γ.quotientHaar Γ.quotientHaar ∧
            ∀ U, Γ.lift (ρ U) = r.pullbackField (Γ.lift U)) ∧
          IsSymmetricUnder (Γ.liftedGibbsMeasure β) r) ∧
      ∀ v : LatticePoint a, v ∈ A.sublattice →
        IsSymmetricUnder (A.liftedTiltMeasure h β t) (shift v)
end YangMills.Construction.GibbsAtFixedSpacing
