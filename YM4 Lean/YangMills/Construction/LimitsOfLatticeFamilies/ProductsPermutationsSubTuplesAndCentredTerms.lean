import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def TupleClassesClosed.Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace),
    (∀ n, 1 ≤ n → ∀ ρ : ℝ≥0∞, 0 < ρ →
      (∀ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y ρ) →
        (∀ l k, l ≠ k → Disjoint (A l) (A k)) →
          (∀ h : FunTuple s Y n, (∀ l, h l ∈ c1CompactSupp s Y (A l)) → h ∈ sepTuplesIn s Y n ρ) ∧
          ∀ h : FunTuple s Y n, (∀ l, h l ∈ lipCompactSupp s Y (A l)) →
            h ∈ lipSepTuplesIn s Y n ρ) ∧
      (∀ h ∈ sepTuplesIn s Y n ρ,
        (∀ p : Equiv.Perm (Fin n), (fun l => h (p l)) ∈ sepTuplesIn s Y n ρ) ∧
        ∀ B : Finset (Fin n), B.Nonempty → restrictTuple h B ∈ sepTuplesIn s Y B.card ρ) ∧
      ∀ h ∈ lipSepTuplesIn s Y n ρ,
        (∀ p : Equiv.Perm (Fin n), (fun l => h (p l)) ∈ lipSepTuplesIn s Y n ρ) ∧
        ∀ B : Finset (Fin n), B.Nonempty → restrictTuple h B ∈ lipSepTuplesIn s Y B.card ρ) ∧
    ∀ ρ : ℝ≥0∞, 0 < ρ →
      (∀ q, ∀ h ∈ sepTuplesIn s Y q ρ, ∀ P ∈ SetPartition.nonSingletonPartitions q,
        ∀ B ∈ P.parts, 2 ≤ B.card ∧ restrictTuple h B ∈ sepTuplesIn s Y B.card ρ) ∧
      ∀ Ψ : FunctionalSeq s Y ρ, IsMultilinearSeq Ψ →
        (∀ h : sepTuplesIn s Y 0 ρ, centredSum Ψ 0 h = 1) ∧
        ∀ h : sepTuplesIn s Y 1 ρ, centredSum Ψ 1 h = 0
end YangMills.Construction.LatticeLimits
end
