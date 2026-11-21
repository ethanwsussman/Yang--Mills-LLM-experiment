import YangMills.Construction.Weighted.ChainSiteSums
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.WordExpansion
def alternatingWord {A ι : Type*} [Monoid A] (p : ι → A) (q : ι → ι → A) (n : ℕ)
    (ϖ : Fin (2 * n + 1) → ι) : A :=
  p (ϖ 0) *
    (List.ofFn fun k : Fin n => q (ϖ ⟨2 * k + 1, by omega⟩) (ϖ ⟨2 * k + 2, by omega⟩)).prod
end YangMills.Construction.WordExpansion

noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
structure NeumannSeriesBounds {ι : Type} (T : Module.End ℝ B.LayerFn)
    (p : ι → Module.End ℝ B.LayerFn) (q : ι → ι → Module.End ℝ B.LayerFn)
    (ρ a b : ℝ) : Prop where
  isUnit_one_sub_remainder : IsUnit (1 - ∑ᶠ i, ∑ᶠ i', q i i')
  inverse_eq_mul : Ring.inverse T = (∑ᶠ i, p i) * Ring.inverse (1 - ∑ᶠ i, ∑ᶠ i', q i i')
  hasSum_kernel_pow : ∀ y y' : ↥B.allSites,
    HasSum (fun n : ℕ => B.kernel ((∑ᶠ i, p i) * (∑ᶠ i, ∑ᶠ i', q i i') ^ n) y y')
      (B.kernel (Ring.inverse T) y y')
  hasSum_kernel_words : ∀ y y' : ↥B.allSites,
    HasSum (fun n : ℕ => B.kernel (∑ᶠ ϖ, WordExpansion.alternatingWord p q n ϖ) y y')
      (B.kernel (Ring.inverse T) y y')
  sum_abs_kernel_products_le : ∀ (n : ℕ) (y y' : ↥B.allSites),
    ∑ᶠ ϖ, |B.kernel (WordExpansion.alternatingWord p q n ϖ) y y'| ≤
      b * latticeSumConst 4 D.L (1 / 2 * ρ) * (2 : ℝ)⁻¹ ^ n * B.siteScale y ^ (-4 : ℤ) *
        Real.exp (-(1 / 2 * ρ) * B.weightedDistance y y')
  abs_kernel_inverse_le : ∀ y y' : ↥B.allSites,
    |B.kernel (Ring.inverse T) y y'| ≤
      2 * b * latticeSumConst 4 D.L (1 / 2 * ρ) * B.siteScale y ^ (-4 : ℤ) *
        Real.exp (-(1 / 2 * ρ) * B.weightedDistance y y')
end SeparatedChain
def NeumannParametrixExpansion : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D), (B.stage 0).Nonempty →
    ∀ ρ a b : ℝ, 0 < ρ → 0 ≤ a → 0 ≤ b →
      (∀ κ : ℝ, 1 / 2 * ρ ≤ κ →
        latticeSumRadius 4 D.L κ ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ)) →
      a * latticeSumConst 4 D.L (1 / 2 * ρ) ≤ 1 / 2 →
      ∀ (ι : Type), Finite ι →
        ∀ (T : Module.End ℝ B.LayerFn) (p : ι → Module.End ℝ B.LayerFn)
          (q : ι → ι → Module.End ℝ B.LayerFn),
          T * (∑ᶠ i, p i) = 1 - ∑ᶠ i, ∑ᶠ i', q i i' →
          (∀ y y' : ↥B.allSites, ∑ᶠ i, ∑ᶠ i', |B.kernel (q i i') y y'| ≤
            a * Real.exp (-ρ * B.weightedDistance y y')) →
          (∀ y y' : ↥B.allSites, ∑ᶠ i, |B.kernel (p i) y y'| ≤
            b * B.siteScale y ^ (-4 : ℤ) *
              Real.exp (-(2 * ρ) * B.weightedDistance y y')) →
          B.NeumannSeriesBounds T p q ρ a b
end YangMills.Construction.Weighted
