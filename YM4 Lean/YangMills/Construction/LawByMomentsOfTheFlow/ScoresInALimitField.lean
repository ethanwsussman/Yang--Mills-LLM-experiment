import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def limitScoresMeanStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k))
    (j j' : F.Index), F.observables j = bottomProduct c B → F.observables j' = completedProduct c B →
      F.condMeanAt j =ᵐ[F.law] F.condMeanAt j'
end YangMills.Construction.MomentLaw
end
