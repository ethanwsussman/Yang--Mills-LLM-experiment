import YangMills.Construction.ReflectionPositiveLimits.LatticeLimitsOfPurePhasesAndDecompositions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.PeriodicGibbs
open InfiniteLattice (LatticeSymmetry ElementaryPlaquette periodicGibbsSet faceEnergy smearedEnergy)
open GibbsAtFixedSpacing (BorelProb)
open ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
def PeriodicGibbsReflectionPositive (L : ℕ) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), 0 < β → ∀ μ : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
    μ.1 ∈ periodicGibbsSet L (K : ℕ) β →
      μ ∈ reflectionPositiveSet (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) ∧
        InfiniteLattice.IsShiftInvariant μ.1 ∧
          ∀ M : InfiniteLattice.LatticeMirror (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
            InfiniteLattice.IsReflectionPositiveAt μ.1 M
def PeriodicGibbsCentered (L : ℕ) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), 0 < β → ∀ μ : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
    μ.1 ∈ periodicGibbsSet L (K : ℕ) β →
      (∀ g : LatticeSymmetry (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
        InfiniteLattice.IsSymmetricUnder μ.1 g) ∧
        ∃ m : ℝ, (∀ p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
            ∫ U, faceEnergy U p ∂μ.1 = m) ∧
          ∀ f ∈ continuousCompact, ∀ U : GaugeFieldsAtLevel L (K : ℕ),
            smearedEnergy f U - ∫ V, smearedEnergy f V ∂μ.1 =
              ∑ᶠ p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
                f p.center * (faceEnergy U p - m)
def plaquetteCentredStates {L : ℕ} (K : ℕ+ → ℕ+) (hK : StrictMono K) (β : ℕ+ → ℝ)
    (hβ : ∀ j, 0 < β j)
    (μ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ)))
    (hμ : ∀ j, (μ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j)) (m : ℕ+ → ℝ)
    (hm : ∀ j (p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ))),
      ∫ U, faceEnergy U p ∂(μ j).1 = m j) : PlaquetteCentredStates L where
  level := K
  level_strictMono := hK
  beta := β
  beta_pos := hβ
  gibbs := μ
  gibbs_mem := hμ
  mean := m
  integral_faceEnergy := hm
def PeriodicGibbsLatticeSequences (L : ℕ) : Prop :=
  ∀ (K : ℕ+ → ℕ+) (hK : StrictMono K) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j)
    (ρ μ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ))),
    (∀ j, (ρ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j)) →
    ∀ hμ : ∀ j, (μ j).1 ∈ periodicGibbsSet L (K j : ℕ) (β j),
      ∃ (m : ℕ+ → ℝ) (hm : ∀ j (p : ElementaryPlaquette (PeriodicLattice.meshSize L ((K j : ℕ) : ℤ))),
          ∫ U, faceEnergy U p ∂(μ j).1 = m j),
        let S := (plaquetteCentredStates K hK β hβ μ hμ m hm).toSequence ρ
        S.IsRP ∧
          (∀ (j : ℕ+), ∀ f ∈ continuousCompact,
            ∀ U : GaugeFieldsAtLevel L (K j : ℕ),
              S.smeared j f U = smearedEnergy f U - ∫ V, smearedEnergy f V ∂(μ j).1) ∧
          (∀ (j : ℕ+) (X : Tuple), S.rep j X =
            centeredProduct L (K j : ℕ) (μ j) X) ∧
          ∀ σ : Tuple → ℝ, IsNormalizedFunctional σ → (S.HasLimit σ ↔ ∀ X : Tuple,
            Tendsto (fun j => ∫ U, centeredProduct L (K j : ℕ) (μ j) X U ∂(ρ j).1) atTop (𝓝 (σ X)))
def periodicGibbsTheorem : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    PeriodicGibbsReflectionPositive L ∧ PeriodicGibbsCentered L ∧
      PeriodicGibbsLatticeSequences L
end YangMills.Construction.ReflectionPositivity.PeriodicGibbs
