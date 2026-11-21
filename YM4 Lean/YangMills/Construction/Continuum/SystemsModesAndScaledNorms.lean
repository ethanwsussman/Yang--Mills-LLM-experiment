import YangMills.Construction.Continuum.PiecesOfTheShellsTheirCubesAndNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ConfigSpace
variable {n : ℕ}
structure PointSystem (n : ℕ) where
  base : Config n
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_half : scale ≤ 1 / 2
def configDot (ξ x : Config n) : ℝ := ∑ i, ξ i ⬝ᵥ x i
namespace PointSystem
variable (Q : PointSystem n)
def box (i : Fin n) : Set (Fin 4 → ℝ) := ShellPieces.closedBox (Q.base i) Q.scale
def midBox (i : Fin n) : Set (Fin 4 → ℝ) := ShellPieces.closedBox (Q.base i) (3 / 2 * Q.scale)
def outerBox (i : Fin n) : Set (Fin 4 → ℝ) := ShellPieces.closedBox (Q.base i) (2 * Q.scale)
def boxGap : ℝ≥0∞ :=
  ⨅ (i : Fin n) (i' : Fin n) (_ : i ≠ i'), TestFunctions.setDistR4 (Q.outerBox i) (Q.outerBox i')
def IsSeparated : Prop := 0 < Q.boxGap
def supportedClass : Set (Config n → ℂ) :=
  {Φ | ContDiff ℝ ∞ Φ ∧ tsupport Φ ⊆ cylinderSet Q.midBox}
def freqLattice : Set (Config n) :=
  {ξ | ∃ ζ : Fin n → Fin 4 → ℤ, ∀ i c, ξ i c = Real.pi / Q.scale * ζ i c}
def fourierCoeff (Φ : Config n → ℂ) (ξ : Config n) : ℂ :=
  (((2 * Q.scale) ^ (4 * n))⁻¹ : ℝ) *
    ∫ x in cylinderSet Q.outerBox,
      Φ x * Complex.exp (-(Complex.I * (configDot ξ (x - Q.base) : ℝ)))
def modeFun (i : Fin n) (ξ : Config n) : (Fin 4 → ℝ) → ℂ := fun y =>
  (Bumps.cubeBump (Q.scale⁻¹ • (y - Q.base i)) : ℝ) *
    Complex.exp (Complex.I * ((ξ i ⬝ᵥ (y - Q.base i) : ℝ)))
end PointSystem
def scaledSupNorm (ν : ℕ) (m : ℝ) (Ψ : Config n → ℂ) : ℝ :=
  ⨆ α : {α : MultiIndex n // α.order ≤ ν},
    m ^ α.1.order * TestFunctions.uniformNorm (iteratedPartial α.1 Ψ)
def modeConst : ℝ :=
  max (2 * TestFunctions.uniformNorm fun y => (Bumps.cubeBump y : ℂ))
    (gradSupNorm fun y => (Bumps.cubeBump y : ℂ))
end YangMills.Construction.ConfigSpace
