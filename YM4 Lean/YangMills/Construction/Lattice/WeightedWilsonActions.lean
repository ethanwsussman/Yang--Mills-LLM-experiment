import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
def plaquetteEnergy (U : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (plaquetteHolonomy U p)
def plaquetteWeightedEnergy (c : Plaquette L m j → ℂ) (U : Bond L m j → ComplexMatrix2) : ℂ :=
  ∑ᶠ p : Plaquette L m j, c p * plaquetteEnergy U p
def barycenterWeightedEnergy (c : FourTorus L m → ℂ) (U : Bond L m j → ComplexMatrix2) : ℂ :=
  plaquetteWeightedEnergy (fun p => c p.barycenter) U
def totalEnergy (U : Bond L m j → ComplexMatrix2) : ℂ :=
  ∑ᶠ p : Plaquette L m j, plaquetteEnergy U p
def interiorEnergy (Ω₀ : Set (FourTorus L m)) (U : Bond L m j → ComplexMatrix2) : ℂ :=
  ∑ᶠ p ∈ (plaquettesInside Ω₀ : Set (Plaquette L m j)), plaquetteEnergy U p
def variableCouplingEnergy (x : FourTorus L m → ℝ) (U : Bond L m j → ComplexMatrix2) : ℂ :=
  barycenterWeightedEnergy (fun y => (x y : ℂ)) U
end YangMills.Construction.PeriodicLattice
