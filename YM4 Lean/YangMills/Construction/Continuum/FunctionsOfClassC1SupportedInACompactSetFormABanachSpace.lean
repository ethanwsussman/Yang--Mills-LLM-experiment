import YangMills.Construction.TestFunctions.C1Supported
import Mathlib
set_option autoImplicit false
open TopologicalSpace
noncomputable section
namespace YangMills.Construction.C1Banach
def NormFinite (W : Compacts (Fin 4 → ℝ)) : Prop :=
  ∀ h : TestFunctions.c1Supported W, TestFunctions.IsBoundedFun (h : (Fin 4 → ℝ) → ℝ) ∧
    ∀ k : Fin 4, TestFunctions.IsBoundedFun (TestFunctions.partialDerivR4 k (h : (Fin 4 → ℝ) → ℝ))
def CauchyConverges (W : Compacts (Fin 4 → ℝ)) : Prop :=
  ∀ u : ℕ → TestFunctions.c1Supported W,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ‖u a - u b‖ < ε) →
    ∃ h : TestFunctions.c1Supported W, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ a ≥ N, ‖u a - h‖ < ε
def IsRealBanach (W : Compacts (Fin 4 → ℝ)) : Prop :=
  NormFinite W ∧ NormedSpace.Core ℝ (TestFunctions.c1Supported W) ∧ CauchyConverges W
def NormsComparable (W : Compacts (Fin 4 → ℝ)) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∀ h : TestFunctions.c1Supported W,
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 (h : (Fin 4 → ℝ) → ℝ) ∧
    ‖h‖ ≤ TestFunctions.sharpNormR4 M (h : (Fin 4 → ℝ) → ℝ) ∧
    TestFunctions.sharpNormR4 M (h : (Fin 4 → ℝ) → ℝ) ≤ 80 * M * ‖h‖
def BanachAndComparable : Prop :=
  ∀ W : Compacts (Fin 4 → ℝ), IsRealBanach W ∧ NormsComparable W
end YangMills.Construction.C1Banach
