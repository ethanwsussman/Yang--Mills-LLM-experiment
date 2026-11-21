import YangMills.Construction.InfiniteLattice.RepresentativeOfATupleAndLimitsAlongStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction
open AmbientPoints
namespace StateLimits
open InfiniteLattice R4TupleForms
namespace SeparatedFunctionals
variable {s : Conventions.StandingParameters}
def IsSymmSepFunctional (σ : FinTuple s → ℝ) : Prop :=
  IsTupleFunctional σ ∧ IsSymmetricTupleFunctional σ
def HasConnectedParts (K : ℕ → ℕ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ)))) (j : ℕ) : Prop :=
  IsSymmSepFunctional (pairedValue K ρ ν j) ∧
    (∀ f : separatedTuples s .euclidean 1,
      connectedOf (pairedValue K ρ ν j) 1 f =
        (∫ U, smearedEnergy (f.1 0) U ∂ρ j) - ∫ U, smearedEnergy (f.1 0) U ∂ν j) ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ f : separatedTuples s .euclidean n,
      ((connectedOf (pairedValue K ρ ν j) n f : ℝ) : ℂ) = smearedEnergyCumulant (ρ j) f.1
def ConnectedTendsto (K : ℕ → ℕ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : FinTuple s → ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ f : separatedTuples s .euclidean n,
    Tendsto (fun j => connectedOf (pairedValue K ρ ν j) n f) atTop
      (𝓝 (connectedOf σ n f))
def FirstOrderTendsto (K : ℕ → ℕ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : FinTuple s → ℝ) : Prop :=
  ∀ f : separatedTuples s .euclidean 1,
    connectedOf σ 1 f = σ (toAllSeparated f) ∧
      Tendsto (fun j => (∫ U, smearedEnergy (f.1 0) U ∂ρ j) - ∫ U, smearedEnergy (f.1 0) U ∂ν j)
        atTop (𝓝 (σ (toAllSeparated f)))
def HigherOrderTendstoCumulant (K : ℕ → ℕ)
    (ρ : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : FinTuple s → ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ f : separatedTuples s .euclidean n,
    Tendsto (fun j => smearedEnergyCumulant (ρ j) f.1) atTop
      (𝓝 ((connectedOf σ n f : ℝ) : ℂ))
def IsPartitionExpansion (σ : FinTuple s → ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ f : separatedTuples s .euclidean n,
    σ (toAllSeparated f) =
      ∑ π : SetPartition.PartitionsFin n, ∏ J ∈ π.parts,
        connectedOf σ J.card (restrictSeparated f J)
end SeparatedFunctionals
end StateLimits
end YangMills.Construction
