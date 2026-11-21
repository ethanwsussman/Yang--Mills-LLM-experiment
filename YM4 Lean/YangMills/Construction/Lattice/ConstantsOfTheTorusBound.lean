import YangMills.Construction.Lattice.CellSideLength
import YangMills.Construction.Lattice.SettingOfTheTorusBound
import YangMills.Construction.PolymerActivities.DomainCountingRate
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TorusBound
structure ConstantParameters where
  L : ℕ
  isAdmissible : Conventions.IsAdmissibleBlockingFactor L
  cubeExp : ℕ
  Ce : ℝ
  Ce_nonneg : 0 ≤ Ce
  κe : ℝ
  countingRate_lt_κe : PolymerActivities.DomainCounting.countingRate < κe
  Eplus : ℝ
  Clow : ℝ
def ConstantParameters.ofSetup (D : Setup) (Ce κe Eplus Clow : ℝ) (hCe : 0 ≤ Ce)
    (hκe : PolymerActivities.DomainCounting.countingRate < κe) : ConstantParameters where
  L := D.L
  isAdmissible := D.isAdmissible
  cubeExp := D.cubeExp
  Ce := Ce
  Ce_nonneg := hCe
  κe := κe
  countingRate_lt_κe := hκe
  Eplus := Eplus
  Clow := Clow
namespace ConstantParameters
variable (c : ConstantParameters)
abbrev cubeSide : ℕ := c.L ^ c.cubeExp
def rateGap : ℝ := c.κe - PolymerActivities.DomainCounting.countingRate
theorem rateGap_pos : 0 < c.rateGap := sub_pos.2 c.countingRate_lt_κe
def ballCubeCount (R : ℝ) (s : ℕ) : ℝ :=
  (2 * (R + 1) * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) + 4) ^ 4
def decayFactor (d : ℝ) (s : ℕ) : ℝ :=
  Real.exp (-c.rateGap *
    TorusBound.plusPart (d * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) - 10))
def volumeTerm (d : ℝ) (s : ℕ) : ℝ :=
  ((c.L : ℝ) ^ s / (c.cubeSide : ℝ)) ^ 4 * c.decayFactor d s
def ballTerm (d R : ℝ) (s : ℕ) : ℝ := c.ballCubeCount R s * c.decayFactor d s
def prefactor : ℝ := (c.Ce + 1) * PolymerActivities.DomainCounting.rateSum c.κe
def uvConstant (d : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal c.prefactor * ∑' s : ℕ, ENNReal.ofReal (c.volumeTerm d s)
def uvConstantInBall (d R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c.Ce * PolymerActivities.DomainCounting.rateSum c.κe) *
    ∑' s : ℕ, ENNReal.ofReal (c.ballTerm d R s)
def supTerm (t : ℝ) : ℝ := (2 * t + 4) ^ 4 * Real.exp (-c.rateGap * t / 4)
def decaySup : ℝ≥0∞ := ⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal (c.supTerm t)
def uvBound : ℝ≥0∞ :=
  ENNReal.ofReal c.prefactor *
    (ENNReal.ofReal (44 ^ 4 * (1 + Real.log (20 * (c.cubeSide : ℝ)))) +
      c.decaySup * ENNReal.ofReal (Real.exp (5 * c.rateGap) - 1)⁻¹)
def qExponent (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  2 * c.uvConstantInBall (2 * R + 4) R +
    ENNReal.ofReal (TorusBound.plusPart (c.Eplus + c.Clow) *
      Lattice.cellSideLength c.L n R ^ 4)
def Q (n : ℕ) (R : ℝ) : ℝ≥0∞ := EReal.exp (c.qExponent n R : EReal)
theorem Q_eq_ofReal_exp {n : ℕ} {R x : ℝ} (hx : 0 ≤ x)
    (h : c.qExponent n R = ENNReal.ofReal x) : c.Q n R = ENNReal.ofReal (Real.exp x) := by
  rw [Q, h, EReal.coe_ennreal_ofReal, max_eq_left hx, EReal.exp_coe]
theorem rateSum_pos : 0 < PolymerActivities.DomainCounting.rateSum c.κe := by
  have h : Real.exp (PolymerActivities.DomainCounting.countingRate - c.κe) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (sub_neg.2 c.countingRate_lt_κe)
  unfold PolymerActivities.DomainCounting.rateSum
  positivity
theorem prefactor_pos : 0 < c.prefactor := by
  have h₁ := c.Ce_nonneg
  have h₂ := c.rateSum_pos
  unfold prefactor
  positivity
theorem volumeTerm_nonneg (d : ℝ) (s : ℕ) : 0 ≤ c.volumeTerm d s :=
  mul_nonneg (Even.pow_nonneg (by decide) _) (Real.exp_pos _).le
theorem ballTerm_nonneg (d R : ℝ) (s : ℕ) : 0 ≤ c.ballTerm d R s :=
  mul_nonneg (Even.pow_nonneg (by decide) _) (Real.exp_pos _).le
theorem supTerm_nonneg (t : ℝ) : 0 ≤ c.supTerm t :=
  mul_nonneg (Even.pow_nonneg (by decide) _) (Real.exp_pos _).le
theorem one_le_cubeSide : (1 : ℝ) ≤ (c.cubeSide : ℝ) := by
  have hL : 0 < c.L := by
    have := c.isAdmissible.2
    omega
  exact_mod_cast Nat.one_le_pow _ _ hL
end ConstantParameters
end TorusBound
end YangMills.Construction
end
