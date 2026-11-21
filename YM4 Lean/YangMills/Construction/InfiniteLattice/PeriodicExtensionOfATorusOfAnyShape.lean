import YangMills.Construction.InfiniteLattice.OrientedBondsLiftsAndPreservedMeasuresOfATorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodSublattice
structure QuotientLiftFacts (Γ : PeriodSublattice 1) : Prop where
  periods_finiteIndex : Γ.periods.FiniteIndex
  finite_quotientTorus : Finite Γ.QuotientTorus
  finite_quotientLink : Finite Γ.QuotientLink
  finite_quotientPlaquette : Finite Γ.QuotientPlaquette
  lift_apply_link : ∀ (U : Γ.QuotientField) (l : Link 1),
    Γ.lift U l = Γ.orientedValue U (Γ.orientedClass l)
  lift_shift_invariant : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
    (shift γ).pullbackField (Γ.lift U) = Γ.lift U
  continuous_lift : Continuous Γ.lift
  injective_lift : Function.Injective Γ.lift
  faceEnergy_lifts_eq : ∀ (p : Γ.QuotientPlaquette) (U : Γ.QuotientField)
    (q q' : ElementaryPlaquette 1),
    Γ.IsLiftOfPlaquette q p → Γ.IsLiftOfPlaquette q' p →
      faceEnergy (Γ.lift U) q = faceEnergy (Γ.lift U) q'
  continuous_quotientFaceEnergy : ∀ p : Γ.QuotientPlaquette,
    Continuous fun U => Γ.quotientFaceEnergy U p
  quotientFaceEnergy_mem_Icc : ∀ (p : Γ.QuotientPlaquette) (U : Γ.QuotientField),
    0 ≤ Γ.quotientFaceEnergy U p ∧ Γ.quotientFaceEnergy U p ≤ 2
  quotientFaceEnergy_dependsOn : ∀ p : Γ.QuotientPlaquette,
    DependsOnlyOn (fun U => Γ.quotientFaceEnergy U p) (Γ.plaquetteLinks p)
  continuous_periodize : ∀ F ∈ continuousLocalFunctions 1, Continuous (Γ.periodize F)
  supNorm_periodize_le : ∀ F ∈ continuousLocalFunctions 1,
    supNorm (Γ.periodize F) ≤ observableSupNorm F
  periodize_dependsOn : ∀ F ∈ continuousLocalFunctions 1,
    DependsOnlyOn (Γ.periodize F) (Γ.linkClassImage (observableSupport F))
  measurable_bounded_comp_lift : ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
    Measurable (fun U => F (Γ.lift U)) ∧
      ∃ C : ℝ, ∀ U, ‖F (Γ.lift U)‖ ≤ C
  integral_map_lift : ∀ μ : Measure Γ.QuotientField, IsProbabilityMeasure μ →
    ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      ∫ U, F U ∂(μ.map Γ.lift) = ∫ U, F (Γ.lift U) ∂μ
  integral_map_lift_eq_periodize : ∀ μ : Measure Γ.QuotientField, IsProbabilityMeasure μ →
    ∀ F ∈ continuousLocalFunctions 1,
      ∫ U, F U ∂(μ.map Γ.lift) = integralOf μ (Γ.periodize F)
end PeriodSublattice
def PeriodicQuotient.FinitenessClaim : Prop :=
  (∀ Γ : PeriodSublattice 1, Γ.QuotientLiftFacts) ∧
    ∀ H : AddSubgroup (LatticePoint 1), HasFullRank (H.map (latticeSubgroup 1).subtype) → H.FiniteIndex
end YangMills.Construction.InfiniteLattice
