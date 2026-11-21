import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields WeightedResponses RenormalizationStepParameters
def IsMaxwellCovariance (a : ℝ) (L k : ℕ) {m : ℕ} [NeZero m]
    (cov : TorusPlaquette m → TorusPlaquette m → ℝ) : Prop :=
  (∀ p p', cov p p' = cov p' p) ∧ ∀ h : TorusPlaquette m → ℝ,
    IsLUB (Set.range (maxwellDefect a L k h))
      (∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ, h p * cov p p' * h p')
def StepCovariancesSumToMaxwellStatement : Prop :=
  HoldsOnParameterFamilies fun tbl y => ∃ C : ℝ, ∀ (k d n : ℕ) [NeZero n], tbl.n₀ ≤ n →
    ∃ cov : TorusPlaquette (fineSide (tbl.stepParameters y).side d n) →
        TorusPlaquette (fineSide (tbl.stepParameters y).side d n) → ℝ,
      IsMaxwellCovariance tbl.coupling (tbl.stepParameters y).side k cov ∧
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (tbl.stepParameters y).side d n))),
        ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (tbl.stepParameters y).side d n))),
          |accumulatedCovariance tbl.coupling tbl.ρA (tbl.stepParameters y).side k d n
              (curlFunctional p) (curlFunctional p') - cov p p'| ≤
            C * (4 : ℝ) ^ (-(d : ℤ))
end YangMills.Construction.ResponseInTheExpansion
end
