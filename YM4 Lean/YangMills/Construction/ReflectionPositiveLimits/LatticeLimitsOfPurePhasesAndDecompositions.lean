import YangMills.Construction.InfiniteLattice.CutoffGibbsSets
import YangMills.Construction.ReflectionPositiveLimits.LatticeApproximationsRepresentativesAndLimits
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open InfiniteLattice (ElementaryPlaquette periodicGibbsSet faceEnergy cutoffExtremalSet)
open GibbsAtFixedSpacing (BorelProb)
structure PlaquetteCentredStates (L : ℕ) where
  level : ℕ+ → ℕ+
  level_strictMono : StrictMono level
  beta : ℕ+ → ℝ
  beta_pos : ∀ j, 0 < beta j
  gibbs : ∀ j, BorelProb (PeriodicLattice.meshSize L ((level j : ℕ) : ℤ))
  gibbs_mem : ∀ j, (gibbs j).1 ∈ periodicGibbsSet L (level j : ℕ) (beta j)
  mean : ℕ+ → ℝ
  integral_faceEnergy : ∀ j (p : ElementaryPlaquette (PeriodicLattice.meshSize L ((level j : ℕ) : ℤ))),
    ∫ U, faceEnergy U p ∂(gibbs j).1 = mean j
namespace PlaquetteCentredStates
variable {L : ℕ} (S : PlaquetteCentredStates L)
def toSequence (ρ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((S.level j : ℕ) : ℤ))) :
    LatticeSequence L where
  level := S.level
  level_strictMono := S.level_strictMono
  measure := ρ
  shift := S.mean
def IsPurePhaseLimit (σ : Tuple → ℝ) : Prop :=
  ∃ ρ : ∀ j, BorelProb (PeriodicLattice.meshSize L ((S.level j : ℕ) : ℤ)),
    (∀ j, (ρ j).1 ∈ cutoffExtremalSet L (S.level j : ℕ) (S.beta j)) ∧
      (S.toSequence ρ).HasLimit σ
end PlaquetteCentredStates
end YangMills.Construction.ReflectionPositivity
