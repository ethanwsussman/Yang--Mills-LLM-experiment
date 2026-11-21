import YangMills.Construction.EuclideanFunctionals.ClosedInsertionDomainAndInsertionFunctionOfATriple
import YangMills.Construction.EuclideanFunctionals.InsertionBoundAndPlateBound
import YangMills.Construction.EuclideanFunctionals.StandingDataOfTheStudyFromOneInsertionToPlates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
structure ExtendableTriple (c η : ℝ) (F : FreeSep) (k : R4 → ℝ) (A : FreeSep) : Prop where
  scale_pos : 0 < η
  scale_le_one : η ≤ 1
  probe_mem : k ∈ C1c ℝ
  probe_supp : supp k ⊆ {z | TorusMetric.euclidNormVec z ≤ 1 / 2 * c * η}
  left_mem : F ∈ finCombIn {y | η / 4 < y 3}
  right_mem : A ∈ finCombIn {y | η / 4 < y 3}
namespace TripleContinuation
def ExtensionExists : Prop :=
  ∀ {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S), σ.ConeCondition →
    ∀ p C c : ℝ, InsertionBoundHolds σ p C c →
    ∀ (η : ℝ) (F : FreeSep) (k : R4 → ℝ) (A : FreeSep), ExtendableTriple c η F k A →
      ∃ u : (Fin 4 → ℂ) → ℂ,
        closure (complexExtensionDomain η) = closedComplexExtensionDomain η ∧
        ContinuousOn u (closedComplexExtensionDomain η) ∧
        IsHolomorphicFn (complexExtensionDomain η) u ∧
        (∀ x : R4, |x 3| ≤ η / 8 →
          u (fun μ => (x μ : ℂ)) = tripleInsertionFn S F k A x) ∧
        ∀ z ∈ closedComplexExtensionDomain η,
          ‖u z‖ ≤ (2 : ℝ) ^ p * C * η ^ (-p) * m.sharpNorm k *
            heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
end TripleContinuation
end YangMills.Construction.EuclideanFunctionals
