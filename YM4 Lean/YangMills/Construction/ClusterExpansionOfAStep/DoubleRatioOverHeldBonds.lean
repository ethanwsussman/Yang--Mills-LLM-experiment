import YangMills.Construction.ClusterExpansionOfAStep.FourConvexPotentials
import YangMills.Construction.ClusterExpansionOfAStep.IntegralOverADisjointUnion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames DisjointUnionIntegrals ConvexPotentials
def assembledField {α : Type} [DecidableEq α] (C C' F : Finset α) (a : C → BondVector)
    (b : C' → BondVector) (ξ : F → BondVector) (x : α) : BondVector :=
  joinFields C (C' ∪ F) a (fun y => joinFields C' F b ξ y) x
def DoubleRatioPassesToFullIntegrals : Prop :=
  ∀ (α : Type) [DecidableEq α] (S : Fin 2 → Fin 2 → Finset α) (C C' : Fin 2 → Finset α) (F : Finset α)
    (Ψ : ∀ i j, BondField (S i j) → ℝ) (ρ c : ℝ) (p : ℝ → ℝ),
    0 < ρ → IsCutoff ρ p → (∀ i j, S i j = C i ∪ (C' j ∪ F)) → (∀ i j, Disjoint (C i) (C' j ∪ F)) →
    (∀ j, Disjoint (C' j) F) → (∀ i j, Continuous (Ψ i j)) →
    (∀ (a₁ : C 1 → BondVector) (a₀ : C 0 → BondVector) (b₁ : C' 1 → BondVector) (b₀ : C' 0 → BondVector),
      (∀ x, ‖a₁ x‖ < ρ) → (∀ x, ‖a₀ x‖ < ρ) → (∀ x, ‖b₁ x‖ < ρ) → (∀ x, ‖b₀ x‖ < ρ) →
      cutoffIntegral ρ p (fun ξ => Ψ 1 1 fun x => assembledField (C 1) (C' 1) F a₁ b₁ ξ x) *
          cutoffIntegral ρ p (fun ξ => Ψ 0 0 fun x => assembledField (C 0) (C' 0) F a₀ b₀ ξ x) ≤
        c * (cutoffIntegral ρ p (fun ξ => Ψ 1 0 fun x => assembledField (C 1) (C' 0) F a₁ b₀ ξ x) *
          cutoffIntegral ρ p (fun ξ => Ψ 0 1 fun x => assembledField (C 0) (C' 1) F a₀ b₁ ξ x))) →
    cutoffIntegral ρ p (Ψ 1 1) * cutoffIntegral ρ p (Ψ 0 0) ≤
      c * (cutoffIntegral ρ p (Ψ 1 0) * cutoffIntegral ρ p (Ψ 0 1))
end YangMills.Construction.ClusterExpansionOfAStep
end
