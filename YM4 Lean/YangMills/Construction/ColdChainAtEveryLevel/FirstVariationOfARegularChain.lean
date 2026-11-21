import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def IsChartCurve (S : Finset F.Cell) (C : ℝ → ChainChart F) (U A : ChainChart F) : Prop :=
  ChartEqOnBonds S (C 0) U ∧
    (∀ b ∈ innerBonds S 0, HasDerivAt (fun τ => (C τ).fine b.1 b.2) (A.fine b.1 b.2) 0) ∧
    ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      HasDerivAt (fun τ => (C τ).coarse j b.1 b.2) (A.coarse j b.1 b.2) 0
def regularChainFirstVariationStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (W : F.GaugeField F.top),
    Odd F.blockSide → ChartIsRegular S R U →
    ∃ D : ChainChart F → ℝ,
      (∀ A A' : ChainChart F, D (chartSum A A') = D A + D A') ∧
      (∀ (t : ℝ) (A : ChainChart F), D (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ A t) = t * D A) ∧
      ∀ (C : ℝ → ChainChart F) (A : ChainChart F), IsChartCurve S C U A →
        HasDerivAt (fun τ => chartAction a S R (C τ) W) (D A) 0
end BlockAverages
end YangMills.Construction
end
