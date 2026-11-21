import YangMills.Construction.Lattice.ConstantsOfTheTorusBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound
def logFactor (d : ℝ) : ℝ := 1 + logPos (1 / d)
def ConstantParameters.SatisfiesUVBound (c : ConstantParameters) (d : ℝ) : Prop :=
  c.uvConstant d ≤ c.uvBound * ENNReal.ofReal (d ^ (-4 : ℤ) * logFactor d) ∧
    c.uvBound * ENNReal.ofReal (d ^ (-4 : ℤ) * logFactor d) ≤
      c.uvBound * ENNReal.ofReal ((1 + d ^ (-4 : ℤ)) * logFactor d)
def ScaleSumsHold (c : ConstantParameters) : Prop :=
  c.decaySup < ⊤ ∧
  (∀ d : ℝ, 0 < d → Summable (c.volumeTerm d)) ∧
  (∀ d R : ℝ, 0 < d → 0 < R → Summable (c.ballTerm d R)) ∧
  (∀ d : ℝ, 0 < d → 0 < c.uvConstant d) ∧
  AntitoneOn c.uvConstant (Set.Ioi 0) ∧
  (∀ R : ℝ, 0 < R → AntitoneOn (fun d => c.uvConstantInBall d R) (Set.Ioi 0)) ∧
  (∀ d : ℝ, 0 < d → c.SatisfiesUVBound d) ∧
  (∀ d R : ℝ, 0 < d → 0 < R →
    c.uvConstantInBall d R ≤
      c.uvBound * ENNReal.ofReal ((1 + (R + 1) / d) ^ 4 * logFactor d)) ∧
  c.uvBound < ⊤ ∧
  (∀ (n : ℕ) (R : ℝ), 2 ≤ n → 0 < R → 1 ≤ c.Q n R ∧ c.Q n R < ⊤)
def ScaleSumBounds : Prop :=
  (∀ c : ConstantParameters, ScaleSumsHold c) ∧
  (∀ c c' : ConstantParameters, c.cubeSide = c'.cubeSide → c.Ce = c'.Ce → c.κe = c'.κe →
    c.uvBound = c'.uvBound) ∧
  (∀ c c' : ConstantParameters, c.L = c'.L → c.cubeSide = c'.cubeSide → c.Ce = c'.Ce →
    c.κe = c'.κe → ∀ d : ℝ, 0 < d → c.uvConstant d = c'.uvConstant d) ∧
  (∀ c c' : ConstantParameters, c.L = c'.L → c.cubeSide = c'.cubeSide → c.Ce = c'.Ce →
    c.κe = c'.κe → ∀ d R : ℝ, 0 < d → 0 < R →
      c.uvConstantInBall d R = c'.uvConstantInBall d R)
end YangMills.Construction.TorusBound
end
