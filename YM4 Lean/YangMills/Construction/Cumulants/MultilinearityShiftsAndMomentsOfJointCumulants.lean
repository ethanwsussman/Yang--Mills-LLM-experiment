import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace Cumulants
open Probability (IsBoundedRealRV)
def MomentCumulantRelations.Holds : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
    (∀ (P : Type) [Fintype P] [Nonempty P] (Y : P → Ω → ℝ) (n : ℕ) (c : Fin n → P → ℝ),
      (∀ p, IsBoundedRealRV (Y p)) → 1 ≤ n →
      mixedCumulant ν (fun l ω => ∑ p, c l p * Y p ω) =
        ∑ r : Fin n → P, ((∏ l, c l (r l) : ℝ) : ℂ) * mixedCumulant ν fun l => Y (r l)) ∧
    (∀ X : Ω → ℝ, IsBoundedRealRV X →
      mixedCumulant ν (fun _ : Fin 1 => X) = ((∫ ω, X ω ∂ν : ℝ) : ℂ)) ∧
    (∀ (n : ℕ) (X : Fin n → Ω → ℝ) (b : Fin n → ℝ),
      2 ≤ n → (∀ l, IsBoundedRealRV (X l)) →
      mixedCumulant ν (fun l ω => X l ω + b l) = mixedCumulant ν X) ∧
    ∀ (q : ℕ) (X : Fin q → Ω → ℝ), 1 ≤ q → (∀ l, IsBoundedRealRV (X l)) →
      ((∫ ω, ∏ l, X l ω ∂ν : ℝ) : ℂ) =
        ∑ π : SourcesAndGluing.IndexPartition q, ∏ B ∈ π.parts,
          mixedCumulant ν (fun k : Fin B.card => X (B.orderEmbOfFin rfl k)) ∧
      ((∫ ω, ∏ l, (X l ω - ∫ ω', X l ω' ∂ν) ∂ν : ℝ) : ℂ) =
        ∑ π ∈ SourcesAndGluing.partitionsNoSingletons q, ∏ B ∈ π.parts,
          mixedCumulant ν (fun k : Fin B.card => X (B.orderEmbOfFin rfl k))
end Cumulants
end YangMills.Construction
