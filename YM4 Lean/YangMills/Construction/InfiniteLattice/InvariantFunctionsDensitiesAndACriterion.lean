import YangMills.Construction.InfiniteLattice.RationalPolynomialsInTheEntriesAndMeansOverBoxes
import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ShiftInvariance
variable {a : ℝ}
def IsCondExpRepresentative (μ : Measure (GaugeField a)) (F J : GaugeField a → ℂ) : Prop :=
  Measurable[shiftInvariantSigma a] J ∧ Integrable J μ ∧
    ∀ S : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] S →
      ∫ U, S.indicator (1 : GaugeField a → ℂ) U * J U ∂μ =
        ∫ U, S.indicator (1 : GaugeField a → ℂ) U * F U ∂μ
def ShiftsComposeOnFields (a : ℝ) : Prop :=
  (shift (0 : LatticePoint a)).pullbackField = id ∧
    ∀ v w : LatticePoint a, (shift v).pullbackField ∘ (shift w).pullbackField =
      (shift (v + w)).pullbackField
def InvariantSetsFormSigmaAlgebra (a : ℝ) : Prop :=
  IsShiftInvariantSet (univ : Set (GaugeField a)) ∧
    (∀ S : Set (GaugeField a), IsShiftInvariantSet S → IsShiftInvariantSet Sᶜ) ∧
    ∀ f : ℕ → Set (GaugeField a), (∀ i, IsShiftInvariantSet (f i)) →
      IsShiftInvariantSet (⋃ i, f i)
def InvariantMeasurableIffFixed (a : ℝ) : Prop :=
  ∀ J : GaugeField a → ℂ, Measurable J →
    (Measurable[shiftInvariantSigma a] J ↔
      ∀ v : LatticePoint a, J ∘ (shift v).pullbackField = J)
def AEInvariantAgreesOnInvariantSet (a : ℝ) : Prop :=
  ∀ μ : GaugeFieldProbability a, IsShiftInvariant μ.1 →
    ∀ φ : GaugeField a → ℂ, Measurable φ →
      (∀ v : LatticePoint a, φ ∘ (shift v).pullbackField =ᵐ[μ.1] φ) →
      ∃ V : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] V ∧ μ.1 V = 1 ∧
        Measurable[shiftInvariantSigma a]
          fun U => φ U * V.indicator (1 : GaugeField a → ℂ) U
def CondExpVersionsOfObservable (μ : GaugeFieldProbability a) (F : GaugeField a → ℂ) : Prop :=
  (∃ J, IsCondExpRepresentative μ.1 F J ∧ IsBoundedObservable J ∧
      observableSupNorm J ≤ observableSupNorm F) ∧
    ∀ J, IsCondExpRepresentative μ.1 F J →
      (∀ χ : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] χ → IsBoundedObservable χ →
        μ.expect (fun U => χ U * F U) = μ.expect (fun U => χ U * J U)) ∧
      IsCondExpRepresentative μ.1 (fun U => conj (F U)) (fun U => conj (J U)) ∧
      ∀ v : LatticePoint a, IsCondExpRepresentative μ.1 ((shift v).actOn F) J
def PlateauAsIntegralAndSquare (μ : GaugeFieldProbability a)
    (A B : GaugeField a → ℂ) : Prop :=
  (∀ Y, IsCondExpRepresentative μ.1 B Y →
    plateauForm μ.1 A B = μ.expect (fun U => conj (A U) * Y U)) ∧
    ∀ Y, IsCondExpRepresentative μ.1 A Y →
      plateauForm μ.1 A A - ((‖μ.expect A‖ ^ 2 : ℝ) : ℂ) =
        ((stateL2Norm μ (fun U => Y U - μ.expect A) ^ 2 : ℝ) : ℂ)
def CondExpAndPlateau (a : ℝ) : Prop :=
  ∀ μ : GaugeFieldProbability a, IsShiftInvariant μ.1 →
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F → CondExpVersionsOfObservable μ F) ∧
    ∀ A B : GaugeField a → ℂ, IsBoundedObservable A → IsBoundedObservable B →
      PlateauAsIntegralAndSquare μ A B
def InvariantDensitiesPreserveGibbs (L K : ℕ)
    (hmesh : 0 < PeriodicLattice.meshSize L (K : ℤ)) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ μ ∈ periodicGibbsStates L K β,
    ∀ h : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ,
      Measurable[shiftInvariantSigma _] h → IsBoundedObservable h →
      (∀ (Λ : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))))
        (hΛ : (Λ : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
          WilsonOperator.cutoffLinks L K)
        (F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ), IsBoundedObservable F →
        μ.expect (fun U => h U * WilsonOperator.kernelOperator hmesh β hΛ F U) =
          μ.expect (fun U => h U * F U)) ∧
      ((∀ U, 0 ≤ h U) → μ.expect h = 1 →
        ∃ μh : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)),
          (∀ E : Set (GaugeField (PeriodicLattice.meshSize L (K : ℤ))), MeasurableSet E →
            (((μh.1 E).toReal : ℝ) : ℂ) = μ.expect
              (fun U => h U * E.indicator (1 : GaugeField _ → ℂ) U)) ∧
          (∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, IsBoundedObservable F →
            μh.expect F = μ.expect (fun U => h U * F U)) ∧
          μh ∈ periodicGibbsStates L K β)
def ErgodicInvariantFunctionsConstant (a : ℝ) : Prop :=
  ∀ ρ : GaugeFieldProbability a, IsShiftInvariant ρ.1 →
    IsShiftErgodic ρ.1 →
    (∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J →
      ∃ c : ℂ, J =ᵐ[ρ.1] fun _ => c) ∧
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ J, IsCondExpRepresentative ρ.1 F J →
      J =ᵐ[ρ.1] fun _ => ρ.expect F
def FactorizationImpliesErgodic (L K : ℕ) : Prop :=
  ∀ ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)), IsShiftInvariant ρ.1 →
    (∀ S : Set (GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
      MeasurableSet[shiftInvariantSigma _] S → ∀ F ∈ ratPolyObservables _,
        ρ.expect (fun U => S.indicator (1 : GaugeField _ → ℂ) U * (F U : ℂ)) =
          (((ρ.1 S).toReal : ℝ) : ℂ) * ρ.expect (fun U => (F U : ℂ))) →
    IsShiftErgodic ρ.1
theorem meshSize_pos {L : ℕ} (hL : 0 < L) (K : ℕ) : 0 < PeriodicLattice.meshSize L (K : ℤ) := by apply _root_.YangMills.Construction.SourcesAndGluing.meshSize_pos <;> assumption
def ShiftInvarianceAndErgodicity : Prop :=
  ∀ (L K : ℕ) (hodd : Odd L) (hlarge : 13 ≤ L), 0 < K →
    ShiftsComposeOnFields (PeriodicLattice.meshSize L (K : ℤ)) ∧
    InvariantSetsFormSigmaAlgebra (PeriodicLattice.meshSize L (K : ℤ)) ∧
    InvariantMeasurableIffFixed (PeriodicLattice.meshSize L (K : ℤ)) ∧
    AEInvariantAgreesOnInvariantSet (PeriodicLattice.meshSize L (K : ℤ)) ∧
    CondExpAndPlateau (PeriodicLattice.meshSize L (K : ℤ)) ∧
    InvariantDensitiesPreserveGibbs L K (meshSize_pos (by omega) K) ∧
    ErgodicInvariantFunctionsConstant (PeriodicLattice.meshSize L (K : ℤ)) ∧
    FactorizationImpliesErgodic L K
end YangMills.Construction.InfiniteLattice.ShiftInvariance
end
