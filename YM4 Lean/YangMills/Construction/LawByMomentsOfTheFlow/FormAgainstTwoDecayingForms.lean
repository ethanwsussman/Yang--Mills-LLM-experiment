import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TwoLevelMixtures
def twoDecayingFormsSumStatement : Prop :=
  ∀ ℓ : TorusLumps.StepParameters, 0 < ℓ.rt → 0 < ℓ.n₁ → Odd ℓ.side → 2 ^ 21 ≤ ℓ.side →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (Y : TorusSite n) (c c' : TorusBond n) (e a a' : ℝ)
    (q : TorusSite (n * ℓ.side) → BondBilinear (n * ℓ.side)) (R R' : TorusBond (n * ℓ.side) → ℝ), 0 ≤ e → 0 ≤ a → 0 ≤ a' →
    (∀ z ∈ sitesInBlocks ℓ.side {Y}, IsDecayingAbout ℓ e z (q z)) →
    (∀ b, |R b| ≤ a * Real.exp (-(2 * ℓ.weightRate * bondSiteDist ℓ.side b c.1))) →
    (∀ b, |R' b| ≤ a' * Real.exp (-(2 * ℓ.weightRate * bondSiteDist ℓ.side b c'.1))) →
    ∑ z ∈ sitesInBlocks ℓ.side {Y}, |bilinearEval (q z) R R'| ≤ C * e * a * a' / ℓ.weight (tripleDiam Y c c')
end YangMills.Construction.MomentLaw
end
