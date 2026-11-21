import YangMills.Construction.ReflectionPositiveLimits.PeriodicGibbsStatesAndLatticeApproximations
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ExtremalIffErgodic
open InfiniteLattice (IsErgodicUnderShifts IsExtremalPeriodicGibbs ElementaryPlaquette
  shiftInvariantSigma periodicGibbsSet faceEnergy cutoffExtremalSet)
open GibbsAtFixedSpacing (BorelProb)
open PeriodicGibbs (plaquetteCentredStates)
def ExtremalImpliesZeroOne (L : ℕ) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), 0 < β → ∀ μ ∈ periodicGibbsSet L (K : ℕ) β,
    IsExtremalPeriodicGibbs β μ →
    ∀ I : Set (GaugeFieldsAtLevel L (K : ℕ)),
      MeasurableSet[shiftInvariantSigma (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))] I →
        μ I = 0 ∨ μ I = 1
def ZeroOneImpliesExtremal (L : ℕ) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), 0 < β → ∀ μ ∈ periodicGibbsSet L (K : ℕ) β,
    (∀ I : Set (GaugeFieldsAtLevel L (K : ℕ)),
      MeasurableSet[shiftInvariantSigma (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))] I →
        μ I = 0 ∨ μ I = 1) → IsExtremalPeriodicGibbs β μ
def ergodicSeq_iff_extremal (L : ℕ) : Prop :=
  ∀ (K : ℕ+ → ℕ+) (hK : StrictMono K) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j)
    (ρ μ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ))),
    (∀ j, (ρ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j)) →
    ∀ (hμ : ∀ j, (μ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j)) (m : ℕ+ → ℝ)
      (hm : ∀ j (p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ))),
        ∫ U, faceEnergy U p ∂(μ j).1 = m j),
      ((plaquetteCentredStates K hK β hβ μ hμ m hm).toSequence ρ).IsErgodicSeq ↔
        ∀ j, (ρ j).1 ∈ cutoffExtremalSet L (K j : ℕ) (β j)
def purePhaseLimit_iff_ergodicLimit (L : ℕ) : Prop :=
  ∀ (K : ℕ+ → ℕ+) (hK : StrictMono K) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j)
    (μ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ)))
    (hμ : ∀ j, (μ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j)) (m : ℕ+ → ℝ)
    (hm : ∀ j (p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ))),
      ∫ U, faceEnergy U p ∂(μ j).1 = m j) (σ : Tuple → ℝ),
    (plaquetteCentredStates K hK β hβ μ hμ m hm).IsPurePhaseLimit σ ↔
      ∃ ρ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ)),
        (∀ j, (ρ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j)) ∧
          (∀ j, IsErgodicUnderShifts (ρ j).1) ∧
            ((plaquetteCentredStates K hK β hβ μ hμ m hm).toSequence ρ).HasLimit σ
def ExtremalIffErgodicTheorem : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ExtremalImpliesZeroOne L ∧ ZeroOneImpliesExtremal L ∧
      ergodicSeq_iff_extremal L ∧ purePhaseLimit_iff_ergodicLimit L
end YangMills.Construction.ReflectionPositivity.ExtremalIffErgodic
