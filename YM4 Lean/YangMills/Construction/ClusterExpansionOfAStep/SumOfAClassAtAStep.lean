import YangMills.Construction.ClusterExpansionOfAStep.CountsOfAClassAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps
def classSumRate (ℓ : StepParameters) (cE : ℝ) : ℝ :=
  min cE (min (ℓ.κ * ℓ.threshold ^ 2) (ℓ.κ₁ * ℓ.threshold ^ 2)) / 2 ^ 8
structure ClassSumHypotheses (ℓ : StepParameters) (cE CE : ℝ) : Prop where
  cE_pos : 0 < cE
  CE_nonneg : 0 ≤ CE
  κ₁_le : ℓ.κ₁ ≤ ℓ.κ / 16
  κ₁_le_cE : ℓ.κ₁ * ℓ.threshold ^ 2 ≤ cE / 4
  side_ge : 80 ≤ ℓ.side
  range_ge : 2 ^ 16 + 1 ≤ clusterRange ℓ.y₁
  log_bound : ∀ x, ℓ.y₁ ≤ x → 2 ^ 18 * CE * (clusterRange x : ℝ) ^ 12 * Real.log x ≤ x ^ ((1 : ℝ) / 6)
  root_le_rate : ∀ x, ℓ.y₁ ≤ x → x ^ ((1 : ℝ) / 6) ≤ classSumRate ℓ cE * x
  coupling_shift : ∀ x x' : ℝ, ℓ.y₁ ≤ x → |x' - x| ≤ 2 * ℓ.B →
    x' ≤ 1.01 * x ∧ x ≤ 1.01 * x' ∧ clusterRange x ≤ clusterRange x' + 1 ∧ clusterRange x' ≤ clusterRange x + 1
def ClassExponentLePrice : Prop :=
  ∀ (ℓ : StepParameters) (cE CE : ℝ), ℓ.Admissible → ClassSumHypotheses ℓ cE CE → ∀ x x' : ℝ, ℓ.y₁ ≤ x →
    |x' - x| ≤ 2 * ℓ.B →
    ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n → ∀ (V : TorusField n) (W : TorusField (n * ℓ.side))
      (bad : Finset (TorusBond (n * ℓ.side)))
      (Yt : Finset (TorusSite (n * ℓ.side))) (P : Finset (Finset (TorusSite n))),
      P ⊆ chainComponents (clusterRange x') (coarseHull ℓ.side (clusterRange x) (clusterRange x') bad Yt
        (thickening (2 * clusterRange x') (torusHotSites ℓ V))) →
      -x * (6 * ℓ.κ * ℓ.threshold ^ 2 *
              ((open Classical in (torusHotLumps ℓ V).filter (· ⊆ P.biUnion id)).card : ℝ) +
            ℓ.κ / 4 * ℓ.threshold ^ 2 * (hotLumpsInAttached ℓ (clusterRange x) W bad Yt
              (thickening (2 * clusterRange x') (torusHotSites ℓ V)) (P.biUnion id) : ℝ) +
            cE * (badBlocksInAttached ℓ (clusterRange x) bad Yt
              (thickening (2 * clusterRange x') (torusHotSites ℓ V)) (P.biUnion id) : ℝ) +
            ℓ.κ₁ * ℓ.threshold ^ 2 * (lengthInAttached ℓ (clusterRange x) W bad Yt
              (thickening (2 * clusterRange x') (torusHotSites ℓ V)) (P.biUnion id) : ℝ)) +
          CE * (clusterRange x : ℝ) ^ 8 * Real.log x *
            ((nearSites (clusterRange x') (P.biUnion id)).card : ℝ) ≤
        -(x' * ℓ.κ * ℓ.threshold ^ 2 *
            ((open Classical in (torusHotLumps ℓ V).filter (· ⊆ P.biUnion id)).card : ℝ)) -
          ℓ.κ₁ * x' * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange x') (P.biUnion id) V : ℝ)
end YangMills.Construction.ClusterExpansionOfAStep
end
