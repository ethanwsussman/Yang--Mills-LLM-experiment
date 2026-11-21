import YangMills.Construction.InfiniteLattice.MirrorsOfTheSixteenFamiliesAndTheClassOfReflectionPositiveStates
import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.LimitsAndErgodicity
open InfiniteLattice (GaugeField IsShiftErgodic IsSymmetricUnder
  IsShiftInvariant LatticeSymmetry LatticePoint shiftInvariantSigma observableSupNorm plateauVariance
  shift)
open LatticeConventions (NormalHyperplane)
open LatticeConventions.NormalHyperplane (reflectSymmetry)
def SymmetryClosedUnderWeakLimits (a : ℝ) : Prop :=
  ∀ (ν : ℕ → BorelProb a) (μ : BorelProb a) (s : LatticeSymmetry a), BorelProb.TendstoWeak ν μ →
    (∀ i, IsSymmetricUnder (ν i).1 s) → IsSymmetricUnder μ.1 s
def ReflectionPositivityFromContinuous (a : ℝ) : Prop :=
  ∀ (H : NormalHyperplane) (hH : H.IsLatticeMirror a) (ν : BorelProb a),
    IsSymmetricUnder ν.1 (reflectSymmetry hH) →
    (∀ F ∈ locallyMeasurableIn a H.upperHalfSpace, Continuous F → 0 ≤ reflectedPairing hH ν F) →
      IsLocallyReflectionPositive hH ν
def InvariantMeasurableIsPointwiseInvariant (a : ℝ) : Prop :=
  ∀ f : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] f →
    ∀ (v : LatticePoint a) (U : GaugeField a), (shift v).actOn f U = f U
def IsSupNormDense {a : ℝ} (D : Set (GaugeField a → ℂ)) : Prop :=
  ∀ F ∈ continuousFns a, ∀ r : ℝ, 0 < r → ∃ A ∈ D, observableSupNorm (F - A) < r
def ErgodicOfVanishingPlateauVariance (a : ℝ) : Prop :=
  ∀ (ρ : BorelProb a) (D : Set (GaugeField a → ℂ)), IsShiftInvariant ρ.1 →
    D ⊆ continuousFns a → IsSupNormDense D →
    (∀ A ∈ D, plateauVariance ρ.1 A = 0) → IsShiftErgodic ρ.1
def Statement : Prop :=
  ∀ a : ℝ, 0 < a →
    SymmetryClosedUnderWeakLimits a ∧ ReflectionPositivityFromContinuous a ∧
      InvariantMeasurableIsPointwiseInvariant a ∧ ErgodicOfVanishingPlateauVariance a
end YangMills.Construction.GibbsAtFixedSpacing.LimitsAndErgodicity
end
