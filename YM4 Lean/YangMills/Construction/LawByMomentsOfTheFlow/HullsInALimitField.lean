import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def limitHullBoundsStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ C : ℝ, 1 ≤ C ∧
    ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (z : Fin 4 → ℤ), u ≤ S.data.windowLevel →
    (∀ (D : ℝ) (j : F.Index), 0 ≤ D → F.observables j = largeHullIndicator u z D →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤
        Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u *
          (1 + D / (TorusLumps.clusterRange (S.coupling u) : ℝ))))) ∧
    ∀ (k : ℕ) (j : F.Index), 1 ≤ k → F.observables j = hullSizePower u z k →
      ∀ᵐ v ∂F.law, F.condMeanAt j v ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(HullTrees.hullDecayRate Λ.table * S.coupling u / 4))
end YangMills.Construction.MomentLaw
end
