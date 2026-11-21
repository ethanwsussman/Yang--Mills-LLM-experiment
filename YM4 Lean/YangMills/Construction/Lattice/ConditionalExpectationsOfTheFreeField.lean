import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.GaussianFreeCurvature
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
instance instFiniteSiteOfStanding (P : Conventions.StandingParameters) (j : ℤ) :
    Finite (Site P.L P.m j) :=
  SeparatedSequences.BaseParameters.site_finite
    (lt_of_lt_of_le (by norm_num) P.isAdmissible.2) P.m j
section SecondMoments
variable {L m : ℕ} {j : ℤ} [Finite (Plaquette L m j)]
def freeSecondMoment (X : ExactPlaquetteCochain L m j → ℝ) : ℝ≥0∞ :=
  freeLMean fun ω => ENNReal.ofReal (X ω ^ 2)
def HasSetIntegralsOf (G : MeasurableSpace (ExactPlaquetteCochain L m j))
    (X X' : ExactPlaquetteCochain L m j → ℝ) : Prop :=
  ∀ S, MeasurableSet[G] S →
    freeMean (fun ω => X' ω * S.indicator (fun _ => (1 : ℝ)) ω) =
      freeMean fun ω => X ω * S.indicator (fun _ => (1 : ℝ)) ω
def IsConditionalRepresentative (G : MeasurableSpace (ExactPlaquetteCochain L m j))
    (X X' : ExactPlaquetteCochain L m j → ℝ) : Prop :=
  IsBorelObservable X' ∧ Measurable[G] X' ∧ freeSecondMoment X' ≤ freeSecondMoment X ∧
    HasSetIntegralsOf G X X'
end SecondMoments
end YangMills.Construction.PeriodicLattice
