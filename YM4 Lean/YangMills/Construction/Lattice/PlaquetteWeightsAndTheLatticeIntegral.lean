import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def weightL1Norm (c : Plaquette L m j → ℂ) : ℝ := ∑ᶠ p : Plaquette L m j, ‖c p‖
def constantOneWeights : Plaquette L m j → ℂ := fun _ => 1
def weightsAtBarycenters (φ : FourTorus L m → ℂ) : Plaquette L m j → ℂ := fun p => φ p.barycenter
def latticeGaugeIntegral (c : Plaquette L m j → ℂ) : ℂ :=
  ∫ U : CompactGaugeField L m j, Complex.exp (-plaquetteWeightedEnergy c U.1)
    ∂gaugeFieldMeasure L m j
def partitionFunctionNonvanishing (L m : ℕ) (j : ℤ) : Set (Plaquette L m j → ℂ) :=
  {c | latticeGaugeIntegral c ≠ 0}
end PeriodicLattice
end YangMills.Construction
