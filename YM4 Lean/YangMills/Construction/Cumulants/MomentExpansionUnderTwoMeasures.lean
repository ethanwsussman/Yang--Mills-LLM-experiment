import YangMills.Construction.ClusterExpansion.MultiplicitiesAndPrincipalLog
import YangMills.Construction.Cumulants.PartitionsAndPrincipalBranch
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.MomentComparison
variable {Ω : Type*} [MeasurableSpace Ω]
def shiftedFamily (n : ℕ) (f : ℕ → Ω → ℝ) : Fin n → Ω → ℝ := fun k => f (k + 1)
def blockMoment (ν : Measure Ω) (f : ℕ → Ω → ℝ) (B : Finset ℕ) : ℝ := ∫ ω, ∏ k ∈ B, f k ω ∂ν
def partitionMomentSum (ν : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∑ P ∈ partitionsIcc n, (-1 : ℝ) ^ (blockCount P - 1) *
    ((blockCount P - 1).factorial : ℝ) * ∏ B ∈ P, blockMoment ν f B
def partitionWeight (n : ℕ) : ℕ :=
  ∑ P ∈ partitionsIcc n, (blockCount P - 1).factorial * (2 ^ blockCount P - 1)
def momentExpansionAndStability : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (n : ℕ) (f : ℕ → Ω → ℝ), 1 ≤ n →
    (∀ k ∈ Finset.Icc 1 n, Probability.IsBoundedRealRV (f k)) →
    (∀ (ν : Measure Ω) [IsProbabilityMeasure ν],
      mixedCumulant ν (shiftedFamily n f) =
        iteratedFDeriv ℂ n
          (fun w : Fin n → ℂ => PrincipalLog.principalBranch
            (∫ ω, Complex.exp (∑ k, w k * (shiftedFamily n f k ω : ℂ)) ∂ν)) 0
          (fun k => Pi.single k 1) ∧
      mixedCumulant ν (shiftedFamily n f) = (partitionMomentSum ν f n : ℂ) ∧
      (mixedCumulant ν (shiftedFamily n f)).im = 0 ∧
      (∀ σ : Equiv.Perm (Fin n),
        mixedCumulant ν (fun k => shiftedFamily n f (σ k)) = mixedCumulant ν (shiftedFamily n f)) ∧
      ∀ (m : Fin n) (g g' : Ω → ℝ) (c c' : ℝ), Probability.IsBoundedRealRV g →
        Probability.IsBoundedRealRV g' →
        mixedCumulant ν (Function.update (shiftedFamily n f) m fun ω => c * g ω + c' * g' ω) =
          (c : ℂ) * mixedCumulant ν (Function.update (shiftedFamily n f) m g) +
            (c' : ℂ) * mixedCumulant ν (Function.update (shiftedFamily n f) m g')) ∧
    ∀ (ν ν' : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (M : ℕ → ℝ) (δ : ℝ),
      (∀ k ∈ Finset.Icc 1 n, 0 ≤ M k) → 0 ≤ δ → δ ≤ 1 →
      (∀ k ∈ Finset.Icc 1 n, ∀ ω, |f k ω| ≤ M k) →
      (∀ B : Finset ℕ, B.Nonempty → B ⊆ Finset.Icc 1 n →
        |blockMoment ν f B - blockMoment ν' f B| ≤ δ * ∏ k ∈ B, M k) →
      ‖mixedCumulant ν (shiftedFamily n f) - mixedCumulant ν' (shiftedFamily n f)‖ ≤
        (partitionWeight n : ℝ) * δ * ∏ k ∈ Finset.Icc 1 n, M k
end YangMills.Construction.Cumulants.MomentComparison
