import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace AdmissibleConstants
def CumulantBoundByCentredMoments : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (Z : Fin n → Ω → ℝ) (G : Fin n → ℝ), 2 ≤ n → (∀ i, Measurable (Z i)) →
    (∀ i, ∃ C : ℝ, ∀ᵐ ω ∂ν, |Z i ω| ≤ C) → (∀ i, 0 ≤ G i) →
    (∀ J : Finset (Fin n), J.Nonempty →
      |∫ ω, ∏ i ∈ J, (Z i ω - ∫ ω', Z i ω' ∂ν) ∂ν| ≤ ∏ i ∈ J, G i) →
    ‖YangMills.Construction.Cumulants.mixedCumulant ν Z‖ ≤ 2 ^ n * (n.factorial : ℝ) * ∏ i, G i
end AdmissibleConstants
end YangMills.Construction
end
