import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.NormedSpaces.BanachSteinhaus
def normsOnClosedUnitBall {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) : Set ℝ :=
  {r : ℝ | ∃ x : E, ‖x‖ ≤ 1 ∧ r = ‖T x‖}
noncomputable def linearOpNorm {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) : ℝ :=
  sSup (normsOnClosedUnitBall T)
def formValuesOnUnitPolyball {q : ℕ} {E : Fin q → Type} [∀ l, NormedAddCommGroup (E l)]
    [∀ l, NormedSpace ℝ (E l)] (Ψ : MultilinearMap ℝ E ℝ) : Set ℝ :=
  {r : ℝ | ∃ v : ∀ l, E l, (∀ l, ‖v l‖ ≤ 1) ∧ r = |Ψ v|}
noncomputable def multilinearFormNorm {q : ℕ} {E : Fin q → Type} [∀ l, NormedAddCommGroup (E l)]
    [∀ l, NormedSpace ℝ (E l)] (Ψ : MultilinearMap ℝ E ℝ) : ℝ :=
  sSup (formValuesOnUnitPolyball Ψ)
def linearMapsBounded : Prop :=
  ∀ (ι E F : Type) [Nonempty ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : ι → E →ₗ[ℝ] F),
    (∀ j, BddAbove (normsOnClosedUnitBall (T j))) →
    (∀ x, BddAbove (Set.range fun j => ‖T j x‖)) →
    BddAbove (Set.range fun j => linearOpNorm (T j))
def multilinearFormsBounded : Prop :=
  ∀ (ι : Type) [Nonempty ι] (q : ℕ), 1 ≤ q →
    ∀ (E : Fin q → Type) [∀ l, NormedAddCommGroup (E l)] [∀ l, NormedSpace ℝ (E l)]
      [∀ l, CompleteSpace (E l)] (Ψ : ι → MultilinearMap ℝ E ℝ),
      (∀ j, BddAbove (formValuesOnUnitPolyball (Ψ j))) →
      (∀ v : ∀ l, E l, BddAbove (Set.range fun j => |Ψ j v|)) →
      BddAbove (Set.range fun j => multilinearFormNorm (Ψ j)) ∧
        ∀ (j : ι) (v : ∀ l, E l), |Ψ j v| ≤ (⨆ i, multilinearFormNorm (Ψ i)) * ∏ l, ‖v l‖
def linearAndMultilinear : Prop :=
  linearMapsBounded ∧ multilinearFormsBounded
end YangMills.Construction.NormedSpaces.BanachSteinhaus
