import YangMills.Construction.Lattice.SourcesAndGeneratingFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m n : ℕ}
def IsRealLipschitzTuple (f : Fin n → FourTorus L m → ℝ) : Prop :=
  1 ≤ n ∧ ∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i)
def FlatNormLT (M ϱ : ℝ) (w : FourTorus L m → ℂ) : Prop :=
  ∃ (k : ℕ) (f : Fin k → FourTorus L m → ℝ) (z : Fin k → ℂ),
    IsRealLipschitzTuple f ∧ z ∈ sourceDisc M ϱ f ∧ w = complexSource f z
def generatingFunctionOfSource (L m K : ℕ) (β : ℝ) (w : FourTorus L m → ℂ) : ℂ :=
  ∫ U : Bond L m (K : ℤ) → Matrices.ComplexMatrix2, sourcedBoltzmannWeight β w U
    ∂productHaarMeasure L m (K : ℤ)
end PeriodicLattice
end YangMills.Construction
