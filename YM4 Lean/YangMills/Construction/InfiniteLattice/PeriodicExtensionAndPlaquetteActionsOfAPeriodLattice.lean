import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PeriodicLiftAndQuotientEnergiesStatement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ Γ : PeriodSublattice a,
    ((∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
        (shift γ).pullbackField (Γ.lift U) = Γ.lift U) ∧
      Continuous Γ.lift ∧
      (∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette), ∀ q ∈ (p : Set (ElementaryPlaquette a)),
        ∀ q' ∈ (p : Set (ElementaryPlaquette a)),
          faceEnergy (Γ.lift U) q = faceEnergy (Γ.lift U) q') ∧
      ∀ p : Γ.QuotientPlaquette, Continuous (fun U => Γ.quotientFaceEnergy U p) ∧
        ∀ U, Γ.quotientFaceEnergy U p ∈ Icc (0 : ℝ) 2) ∧
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ v : LatticePoint a, ∀ γ ∈ Γ.periods,
      Γ.periodize ((shift (v + γ)).actOn F) =
        Γ.periodize ((shift v).actOn F)
end YangMills.Construction.InfiniteLattice
