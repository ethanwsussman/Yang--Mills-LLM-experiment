import Mathlib
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Strips
variable {n : ℕ} [NeZero n]
def halfPiStrip : Set ℂ := {ζ | |ζ.im| < Real.pi / 2}
def IsStripExtensionAlong (g : (Fin n → ℝ) → ℂ) (j : Fin n) (x : Fin n → ℝ) (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F halfPiStrip ∧ ∀ t : ℝ, F (t : ℂ) = g (Function.update x j t)
def IsSepHolomorphicOnStrips (g : (Fin n → ℝ) → ℂ) : Prop :=
  Continuous g ∧ ∀ (j : Fin n) (x : Fin n → ℝ), ∃ F : ℂ → ℂ, IsStripExtensionAlong g j x F
def stripExtensionAlong (g : (Fin n → ℝ) → ℂ) (j : Fin n) (x : Fin n → ℝ) : ℂ → ℂ :=
  Classical.epsilon (IsStripExtensionAlong g j x)
def valueAlong (g : (Fin n → ℝ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  stripExtensionAlong g j (fun i => (z i).re) (z j)
def armOfCross (x : Fin n → ℝ) (T b : ℝ) (j : Fin n) : Set (Fin n → ℂ) :=
  {z | |(z j).re - x j| ≤ T ∧ |(z j).im| ≤ b ∧
    ∀ i, i ≠ j → (z i).im = 0 ∧ ‖z i - (x i : ℂ)‖ ≤ T}
def supOnCross (g : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) (T b : ℝ) : ℝ≥0∞ :=
  sSup {r | ∃ j : Fin n, ∃ z ∈ armOfCross x T b j, r = ‖valueAlong g j z‖ₑ}
def halfPiTube (n : ℕ) [NeZero n] : Set (Fin n → ℂ) := {z | ∑ j, |(z j).im| < Real.pi / 2}
end YangMills.Construction.Strips
