import YangMills.Construction.NormedSpaces.BanachSteinhausLinearAndMultilinear
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.NormedSpaces.MultilinearUniformBound
open YangMills.Construction.NormedSpaces.BanachSteinhaus
def IsUniformFormBound {ι : Type} {k : ℕ} {E : Fin k → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (T : ι → MultilinearMap ℝ E ℝ) (C : ℝ) : Prop :=
  ∀ (j : ι) (v : ∀ i, E i), |T j v| ≤ C * ∏ i, ‖v i‖
def uniformBoundednessPrinciple : Prop :=
  ∀ (ι : Type) (k : ℕ), 1 ≤ k →
    ∀ (E : Fin k → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
      [∀ i, CompleteSpace (E i)] (T : ι → MultilinearMap ℝ E ℝ),
      (∀ j, BddAbove (formValuesOnUnitPolyball (T j))) →
      (∀ v : ∀ i, E i, BddAbove (Set.range fun j => |T j v|)) →
      (∃ C : ℝ, IsUniformFormBound T C) ∧
        BddAbove (Set.range fun j => multilinearFormNorm (T j)) ∧
        IsUniformFormBound T (⨆ j, multilinearFormNorm (T j))
end YangMills.Construction.NormedSpaces.MultilinearUniformBound
