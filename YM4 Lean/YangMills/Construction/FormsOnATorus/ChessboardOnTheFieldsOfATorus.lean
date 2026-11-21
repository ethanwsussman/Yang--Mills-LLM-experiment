import YangMills.Construction.FormsOnATorus.MirrorsOfCells
import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages YangMills.Construction.WeightedResponses
def DependsOnlyOnBox {n : ℕ} (u : Fin 4 → ℤ) (m : ℕ) (G : TorusField n → ℝ) : Prop :=
  ∀ W W' : TorusField n, FieldsAgreeNear W W' (siteOfInt u) (siteOfInt u) m → G W = G W'
def IsCellCopy {n : ℕ} (c : ℕ) (u : Fin 4 → ℤ) {M : ℕ} (G : TorusField n → ℝ)
    (H : (Fin 4 → Fin M) → TorusField n → ℝ) : Prop :=
  ∀ (k : Fin 4 → Fin M) (W W' : TorusField n),
    (cellReflection c u fun i => ((k i : ℕ) : ℤ)).Transports W W' → H k W' = G W
def ChessboardEstimate : Prop :=
  ∀ (c M m : ℕ) [NeZero m], m = c * M → Odd c → Even M → 0 < M → 4 ≤ m → ∀ β : ℝ, 0 < β →
    ∀ (u : Fin 4 → ℤ) (G : TorusField m → ℝ) (H : (Fin 4 → Fin M) → TorusField m → ℝ),
      Measurable G → (∀ W, 0 ≤ G W) → (∀ W, G W ≤ 1) → DependsOnlyOnBox u ((c - 1) / 2) G →
      IsCellCopy c u G H →
      (∫ W, G W ∂(wilsonLaw β m)) ^ (M ^ 4) ≤ ∫ W, ∏ k, H k W ∂(wilsonLaw β m)
end YangMills.Construction.TorusFields
end
