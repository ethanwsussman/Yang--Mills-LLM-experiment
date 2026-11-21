import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def pullbackFormBoundStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb z => ∀ (u n : ℕ) [NeZero n], (Tb.stepParameters z).n₀ ≤ n →
    ∀ (Y : TorusFields.TorusSite n) (sz : ℝ), 0 ≤ sz →
    ∀ qs : TorusFields.TorusSite (n * (Tb.stepParameters z).side) → BondBilinear (n * (Tb.stepParameters z).side),
    (∀ y ∈ TorusLumps.sitesInBlocks (Tb.stepParameters z).side {Y},
      AnnihilatesGradients (qs y) ∧ IsDecayingAbout (Tb.stepParameters z) sz y (qs y)) →
    ∀ c c' : TorusFields.TorusBond n,
      |∑ y ∈ TorusLumps.sitesInBlocks (Tb.stepParameters z).side {Y},
          pullbackForm Tb.coupling Tb.ρA (Tb.stepParameters z).side u (qs y) c c'| ≤
      ((Tb.stepParameters z).side : ℝ) ^ ((1 : ℝ) / 2) * sz / (Tb.stepParameters z).weight (tripleDiam Y c c')
end YangMills.Construction.MomentLaw
end
