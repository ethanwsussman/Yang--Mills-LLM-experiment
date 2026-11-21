import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def IsLipschitzSource (w : FourTorus L m → ℂ) : Prop := torusLipConst w ≠ ⊤
def sourcedPartitionFunction (L m J : ℕ) (β : ℂ) (w : FourTorus L m → ℂ) : ℂ :=
  ∫ U : CompactGaugeField L m (J : ℤ),
    Complex.exp (-barycenterWeightedEnergy (fun y => β - w y) U.1) ∂gaugeFieldMeasure L m (J : ℤ)
def nonvanishingCouplings (L m J : ℕ) : Set ℂ :=
  {β | sourcedPartitionFunction L m J β 0 ≠ 0}
end YangMills.Construction.PeriodicLattice
