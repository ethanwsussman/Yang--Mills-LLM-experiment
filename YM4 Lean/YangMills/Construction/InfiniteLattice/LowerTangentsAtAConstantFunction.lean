import YangMills.Construction.InfiniteLattice.MeasuresOfTheInvariantClassAsLowerTangents
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.NormalFamilies
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ConstantTangents
def ConstantArrayFacts (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (Γ : PeriodSublattice 1)
    (A : LocalObservableArray) (c β t : ℝ) : Prop :=
  observableSupport (fun _ : GaugeField 1 => (c : ℂ)) = ∅ ∧
  (∀ W : LinkWindow 1, A.labelsTouching W = ∅) ∧
  A.tiltedPartition Γ β t =
    Real.exp (t * c * A.invIndex * ((F.fundamentalBox s).ncard : ℝ)) * A.untiltedTorusPartition Γ β ∧
  (∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
    A.logTiltRatioPerSite Γ F s β t =
      t * A.invIndex * (stateEval ν fun _ : GaugeField 1 => (c : ℂ)).re) ∧
  (∀ (ν : Measure (GaugeField 1)) (r : ℕ+), IsProbabilityMeasure ν →
    A.IsLowerTangent Γ F s r (fun _ => (c : ℂ)) ν β t) ∧
  ∀ r : ℕ+, 0 ≤ LocalObservableArray.shellDefect F s r (fun _ => (c : ℂ)) β t ∧
    0 ≤ LocalObservableArray.sideDefect s r (fun _ => (c : ℂ)) β t
def ConstantLowerTangentClaim : Prop :=
  ∀ (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (Γ : PeriodSublattice 1), Γ.IsBoxShaped F s →
    ∀ (A : LocalObservableArray), Γ.periods ≤ A.sublattice →
      ∀ c : ℝ, A.IsSingleGenerated (fun _ => (c : ℂ)) →
        ∀ β : ℝ, 0 < β → ∀ t : ℝ, ConstantArrayFacts F s Γ A c β t
end YangMills.Construction.InfiniteLattice.ConstantTangents
