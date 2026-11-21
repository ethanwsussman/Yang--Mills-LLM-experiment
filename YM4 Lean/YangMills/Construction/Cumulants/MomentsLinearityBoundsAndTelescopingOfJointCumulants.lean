import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
open Probability (IsBoundedRealRV)
open SetPartition (PartitionsFin blockCount)
namespace MixedCumulantFacts
def cumulantBoundConst : ℕ → ℝ
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 26
  | _ => 0
def telescopeTuple {Ω : Type*} {k : ℕ} (X X' : Fin k → Ω → ℝ) (i : Fin k) :
    Fin k → Ω → ℝ :=
  fun j ω => if j < i then X j ω else if j = i then X' j ω else X j ω + X' j ω
def MixedCumulantProperties : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (k : ℕ)
    (X X' : Fin k → Ω → ℝ), 1 ≤ k → (∀ i, IsBoundedRealRV (X i)) →
    (∀ i, IsBoundedRealRV (X' i)) →
    (mixedCumulant ν X =
      ∑ π : PartitionsFin k, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) *
          ∏ B ∈ π.parts, ((∫ ω, ∏ i ∈ B, X i ω ∂ν : ℝ) : ℂ)) ∧
    (∀ (i : Fin k) (Y Y' : Ω → ℝ) (a a' : ℝ), IsBoundedRealRV Y →
      IsBoundedRealRV Y' →
      mixedCumulant ν (Function.update X i fun ω => a * Y ω + a' * Y' ω) =
        (a : ℂ) * mixedCumulant ν (Function.update X i Y) +
          (a' : ℂ) * mixedCumulant ν (Function.update X i Y')) ∧
    (∀ (i : Fin k) (Y : Ω → ℝ), IsBoundedRealRV Y → Y =ᵐ[ν] X i →
      mixedCumulant ν (Function.update X i Y) = mixedCumulant ν X) ∧
    (2 ≤ k → ∀ (i : Fin k) (c : ℝ),
      mixedCumulant ν (Function.update X i fun ω => X i ω + c) = mixedCumulant ν X) ∧
    (k ≤ 4 → ∀ I : Finset (Fin k),
      ‖mixedCumulant ν X‖ ≤ cumulantBoundConst k * (∏ i ∈ I, (eLpNorm (X i) ⊤ ν).toReal) *
        ∏ i ∈ Iᶜ, (eLpNorm (X i) 4 ν).toReal) ∧
    (mixedCumulant ν (fun i ω => X i ω + X' i ω) - mixedCumulant ν X =
      ∑ i, mixedCumulant ν (telescopeTuple X X' i))
end MixedCumulantFacts
end YangMills.Construction.Cumulants
