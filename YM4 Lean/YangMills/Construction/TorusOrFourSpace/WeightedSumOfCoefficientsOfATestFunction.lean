import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.PeriodBoxCharactersAndCoefficients
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
def freqWeight {n : ℕ+} (ρ : ℝ) (k : IntCoords n) : ℝ :=
  ∏ i, (1 + intVecNorm (k.block i) / cutoffScale ρ)
def WeightedFourierSum : Prop :=
  ∀ (D : Params) (n : ℕ+) (ρ : ℝ), 0 < ρ → ∀ F ∈ cellTestFns D n (4 * ρ),
    Summable (fun k : IntCoords n => ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k) ∧
    ENNReal.ofReal (∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k) ≤
      ENNReal.ofReal (cutoffBound n ρ) *
        Kind.Tuple.cNorm D Kind.euclidean (5 * (n : ℕ) + 1) F
end YangMills.Construction.PeriodicSpace.PeriodCell
