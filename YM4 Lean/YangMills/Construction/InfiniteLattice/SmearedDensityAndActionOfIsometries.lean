import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace SmearedEnergyAndSymmetryAction
def SmearedEnergyComplex (a : ℝ) : Prop :=
  ∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f →
    ∃ h : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite,
      (∀ U : GaugeField a,
        smearedEnergy f U = ∑ p ∈ h.toFinset, faceEnergy U p • f p.center) ∧
      IsBoundedObservable (smearedEnergy f : GaugeField a → ℂ) ∧
      IsLocalObservable (smearedEnergy f : GaugeField a → ℂ)
def SmearedEnergyReal (a : ℝ) : Prop :=
  ∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
    ∃ h : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite,
      (∀ U : GaugeField a,
        smearedEnergy f U = ∑ p ∈ h.toFinset, faceEnergy U p • f p.center) ∧
      IsBoundedObservable (fun U : GaugeField a => ((smearedEnergy f U : ℝ) : ℂ)) ∧
      IsLocalObservable (fun U : GaugeField a => ((smearedEnergy f U : ℝ) : ℂ))
def SymmetryActionProperties (a : ℝ) : Prop :=
  ∀ s : LatticeSymmetry a,
    (∀ U : GaugeField a, ∃ W : GaugeField a,
      (W : Link a → Matrices.ComplexMatrix2.specialUnitary) = U ∘ s.linkMap) ∧
    (∀ (U : GaugeField a) (l : Link a), s.pullbackField U l = U (s.linkMap l)) ∧
    Continuous s.pullbackField ∧
    ∀ (S : Set AmbientSpace) (A : GaugeField a → ℂ), IsBoundedObservable A → IsRegionMeasurable S A →
      IsBoundedObservable (s.actOn A) ∧ IsRegionMeasurable (s.setImage S) (s.actOn A) ∧
        (Continuous A → Continuous (s.actOn A))
def ActOn_comp (a : ℝ) : Prop :=
  ∀ (s t : LatticeSymmetry a) (A : GaugeField a → ℂ), IsBoundedObservable A →
    (s.comp t).actOn A = s.actOn (t.actOn A)
def ShiftInvariantSigmaCharacterization (a : ℝ) : Prop :=
  (∀ I : Set (GaugeField a), MeasurableSet I →
    (MeasurableSet[shiftInvariantSigma a] I ↔
      ∀ v : LatticePoint a, (shift v).pullbackField ⁻¹' I = I)) ∧
  MeasurableSet[shiftInvariantSigma a] (univ : Set (GaugeField a)) ∧
  (∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I →
    MeasurableSet[shiftInvariantSigma a] Iᶜ) ∧
  (∀ I : ℕ → Set (GaugeField a), (∀ n, MeasurableSet[shiftInvariantSigma a] (I n)) →
    MeasurableSet[shiftInvariantSigma a] (⋃ n, I n))
def Main : Prop :=
  ∀ a : ℝ, 0 < a →
    (SmearedEnergyComplex a ∧ SmearedEnergyReal a) ∧
      SymmetryActionProperties a ∧ ActOn_comp a ∧ ShiftInvariantSigmaCharacterization a
end SmearedEnergyAndSymmetryAction
end InfiniteLattice
end YangMills.Construction
