import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ} {n : ℕ}
def complexSource (f : Fin n → FourTorus L m → ℝ) (z : Fin n → ℂ) : FourTorus L m → ℂ :=
  fun x => ∑ i, z i * (f i x : ℂ)
def sourceDisc (M ϱ : ℝ) (f : Fin n → FourTorus L m → ℝ) : Set (Fin n → ℂ) :=
  {z | ∑ i, ‖z i‖ * TestFunctions.sharpNormTorus M (f i) < ϱ}
def sourcedBoltzmannWeight (β : ℝ) (w : FourTorus L m → ℂ)
    (U : Bond L m j → Matrices.ComplexMatrix2) : ℂ :=
  Complex.exp (-barycenterWeightedEnergy (fun x => (β : ℂ) - w x) U)
def generatingFunction (L m K : ℕ) (β : ℝ) (f : Fin n → FourTorus L m → ℝ)
    (z : Fin n → ℂ) : ℂ :=
  ∫ U : Bond L m (K : ℤ) → Matrices.ComplexMatrix2, sourcedBoltzmannWeight β (complexSource f z) U
    ∂productHaarMeasure L m (K : ℤ)
end YangMills.Construction.PeriodicLattice
end
