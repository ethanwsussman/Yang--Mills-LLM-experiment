import YangMills.Construction.HullsInEveryVolume.HullDefs
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def ForAllHullParameters (Q : MomentParameters → Prop) : Prop :=
  HullTrees.EventuallyInParameters fun Tb Kr y =>
    ∀ g : ℝ, 0 < g → y ≤ (g ^ 2)⁻¹ → ∀ (k : ℕ) [NeZero k], 2 ≤ k → k ≤ 8 → ∀ R d : ℝ, 0 < d →
      Q ⟨Tb, Kr, y, g, k, R, d⟩
def ForAllHullPoints (Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop) : Prop :=
  ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S
def meanScoreMomentBoundStatement : Prop :=
  ForAllHullPoints fun Λ C _ _ S => ∀ (p : ℕ), 1 ≤ p → ∀ J : List (Fin Λ.k), J.length = p →
    Integrable (fun w => (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod) (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
    ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
      ENNReal.ofReal (C 0 ^ p * (p.factorial : ℝ) ^ 6)
end YangMills.Construction.MomentLaw
end
