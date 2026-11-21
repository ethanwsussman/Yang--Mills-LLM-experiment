import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesOfAConvexMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Cumulants
open BlockAverages ColdStepAtMirrorFrames
def cumulantFromMoments {ι : Type} [Fintype ι] (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) {M : ℕ}
    (H : Fin M → BondField ι → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin M)),
    (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
      ∏ J ∈ π.parts, ballExpectation r Ψ fun η => ∏ l ∈ J, H l η
def sizeConstantSum (Cq : ℕ → ℝ) (M : ℕ) : ℝ := 1 + ∑ q ∈ Finset.range (2 * M + 1), Cq q
def cumulantDecayBound : Prop :=
  ∀ (N : ℕ) (κ lam : ℝ), 0 < κ → 0 < lam →
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (R x : ℝ)
        (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ),
        0 < R → 0 < x → IsCutoff R p →
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        IsUniformlyConvexDecaying R (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K →
        (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        ∀ (M : ℕ) (H : Fin M → BondField ι → ℝ) (Z : Fin M → F.Cell) (h : Fin M → ℝ)
          (Cq : Fin M → ℕ → ℝ),
          2 ≤ M → M ≤ 9 → (∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < R}) → (∀ i, 0 ≤ h i) →
          (∀ i q, 0 ≤ Cq i q) →
          (∀ i, Interpolation.HasLocalSize R (cutoffFactor R p) Ψ (Cq i) x κ (h i)
            (fun b => (cellSupDist (y b) (Z i) : ℝ)) (H i)) →
          |cumulantFromMoments (cutoffFactor R p) Ψ H| ≤
              T * (∏ i, (sizeConstantSum (Cq i) M * h i)) *
                Real.exp (-(κ * ConvexObservables.cellsDiameter Z / ((M : ℝ) - 1))) ∧
            |cumulantFromMoments (cutoffFactor R p) Ψ H| ≤
              T * (∏ i, (sizeConstantSum (Cq i) M * h i)) *
                Real.exp (-(κ / 8 * ConvexObservables.cellsDiameter Z))
end Cumulants
end YangMills.Construction
end
