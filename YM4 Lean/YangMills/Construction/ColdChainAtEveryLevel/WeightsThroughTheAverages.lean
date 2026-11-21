import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def chartWeightSq (ω : F.Site 0 → ℝ) (W : F.SiteWeights) (U : ChainChart F) : ChainChart F :=
  ⟨fun x i => (ω x ^ 2) • U.fine x i, fun j y i => (W (j + 1) y ^ 2) • U.coarse j y i⟩
def weightAverageCommutatorStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ θ₀ δ₀ : ℝ, 0 < θ₀ ∧ θ₀ ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧
    ∀ (F : BlockFrame) (S : Finset F.Cell) (R : F.FieldChain), Odd F.blockSide → 5 ≤ F.blockSide →
      ∀ (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (ω : F.Site 0 → ℝ), |θ| ≤ θ₀ →
        (∀ y y', |φ y - φ y'| ≤ δ₀ * cellSupDist y y') →
        (∀ x ∈ sitesOfCells S 0, Real.exp (-δ₀) * classWeight F φ θ p 0 x ≤ ω x ∧
          ω x ≤ Real.exp δ₀ * classWeight F φ θ p 0 x) →
        ∀ U : ChainChart F,
          ∑ c ∈ innerBonds S F.top, ((classWeight F φ θ p F.top c.1)⁻¹ *
              ‖linearPart R (chartWeightSq ω (classWeight F φ θ p) U) F.top c.1 c.2 -
                (classWeight F φ θ p F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2‖) ^ 2 ≤
            ε ^ 2 * (cellwiseL4Norm S (classWeight F φ θ p 0) (fun x i => U.fine x i) ^ 2 +
              ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
                (classWeight F φ θ p (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
end YangMills.Construction.BlockAverages
end
