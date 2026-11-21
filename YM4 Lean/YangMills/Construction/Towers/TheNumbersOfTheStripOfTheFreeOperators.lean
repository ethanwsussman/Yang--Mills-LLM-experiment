import YangMills.Construction.Towers.TheStripOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FreeStrip
def IsAdmissiblePair (δ C : ℝ) : Prop :=
  δ ∈ Ioc (0 : ℝ) (1 / 32) ∧ 1 ≤ C ∧
    ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
      StripBounds L k δ C
def admissibleRates : Set ℝ := {δ | ∃ C, IsAdmissiblePair δ C}
def admissibleConstants (δ : ℝ) : Set ℝ := {C | IsAdmissiblePair δ C}
def halfSupRate : Part ℝ := ⟨admissibleRates.Nonempty, fun _ => 1 / 2 * sSup admissibleRates⟩
def infConstantAtHalfRate : Part ℝ :=
  halfSupRate.bind fun δ => ⟨(admissibleConstants δ).Nonempty, fun _ => sInf (admissibleConstants δ)⟩
end YangMills.Construction.Tower.FreeStrip
end
