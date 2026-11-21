import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
structure IsPairing {ι : Type} [LinearOrder ι] (S : Finset ι) (P : Finset (Finset ι)) : Prop where
  card_two_subset : ∀ B ∈ P, B.card = 2 ∧ B ⊆ S
  disjoint : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B'
  covers : ∀ i ∈ S, ∃ B ∈ P, i ∈ B
open Classical in
def matchingSum {ι : Type} [LinearOrder ι] (S : Finset ι) (G : ι → ι → ℝ) : ℝ :=
  ∑ P ∈ S.powerset.powerset.filter (IsPairing S),
    ∏ B ∈ P, (if h : B.Nonempty then G (B.min' h) (B.max' h) else 1)
def matchingSumPropertiesStatement : Prop :=
  (∀ (q : ℕ) (G : Fin q → Fin q → ℝ), wickPairingSum G = matchingSum Finset.univ G) ∧
  (∀ (q : ℕ) (I : Finset (Fin q)) (G : Fin q → Fin q → ℝ),
    wickPairingSum (fun a b => G (I.orderEmbOfFin rfl a) (I.orderEmbOfFin rfl b)) = matchingSum I G) ∧
  ∀ (ι : Type) [LinearOrder ι], (∀ G : ι → ι → ℝ, matchingSum (∅ : Finset ι) G = 1) ∧
    (∀ (S : Finset ι) (A B : ι → ι → ℝ), matchingSum S (fun i j => A i j + B i j) =
      ∑ I ∈ S.powerset, matchingSum I A * matchingSum (S \ I) B) ∧
    (∀ (S : Finset ι) (G : ι → ι → ℝ) (b : ℝ), 0 ≤ b → (∀ i j, |G i j| ≤ b ^ 2) →
      |matchingSum S G| ≤ (S.card).factorial * b ^ S.card) ∧
    (∀ (S : Finset ι) (G : ι → ι → ℝ) (b δ : ℝ), 0 ≤ b → S.Nonempty → δ ≤ b ^ 2 → (∀ i j, |G i j| ≤ δ) →
      |matchingSum S G| ≤ (S.card).factorial * δ * b ^ (S.card - 2)) ∧
    ∀ (S : Finset ι) (G : ι → ι → ℝ) (c : ℝ),
      matchingSum S (fun i j => c ^ 2 * G i j) = c ^ S.card * matchingSum S G
end YangMills.Construction.ResponseInTheExpansion
end
