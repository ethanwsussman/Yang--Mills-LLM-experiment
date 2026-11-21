import YangMills.Construction.EuclideanFunctionals.PlateVectorsAndFunctionsOnTheShiftedTubes
import YangMills.Construction.RotationInvariance.ApertureTimeGapsAndComplexAnalysisInThePlane
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane MeasureTheory
open scoped ContDiff
namespace RealPlane
def ofRealFun (δ : RealPlane → ℝ) : RealPlane → ℂ := fun y => (δ y : ℂ)
def convolve (b δ : RealPlane → ℂ) (y' : RealPlane) : ℂ :=
  ∫ y, b y * δ (y' - y)
end RealPlane
namespace EuclideanFunctionals.PlaneDataWithAperture
variable {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S)
structure IsRadialMollifier (η : ℝ) (δ : ℕ+ → RealPlane → ℝ) : Prop where
  contDiff : ∀ j, ContDiff ℝ ∞ (δ j)
  nonneg : ∀ j y, 0 ≤ δ j y
  hasCompactSupport : ∀ j, HasCompactSupport (δ j)
  tsupport_subset : ∀ j, tsupport (δ j) ⊆
    openDiscAt 0 (d.base.frac * η / ((j : ℕ) : ℝ))
  norm_eq : ∀ j y y', ‖y‖ = ‖y'‖ → δ j y = δ j y'
  integral_eq_one : ∀ j, ∫ y, δ j y = 1
variable {d}
theorem IsRadialMollifier.ofRealFun_mem {η : ℝ} {δ : ℕ+ → RealPlane → ℝ}
    (h : d.IsRadialMollifier η δ) (hη : 0 < η) (j : ℕ+) :
    ofRealFun (δ j) ∈ complexProfiles ∧
      tsupport (ofRealFun (δ j)) ⊆ openDiscAt 0 (d.base.frac * η) := by
  have hsupport : Function.support (ofRealFun (δ j)) = Function.support (δ j) := by
    ext y
    simp [ofRealFun]
  have htsupport : tsupport (ofRealFun (δ j)) = tsupport (δ j) := by
    simp only [tsupport, hsupport]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((h.contDiff j).of_le (by exact_mod_cast le_top))
  · rw [HasCompactSupport, htsupport]
    exact h.hasCompactSupport j
  · rw [htsupport]
    intro y hy
    have hc : 0 < d.base.frac := d.base.frac_mem.1
    have hj : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.one_le_cast.mpr j.pos
    have hy' : ‖y - 0‖ < d.base.frac * η / ((j : ℕ) : ℝ) := h.tsupport_subset j hy
    have hle : d.base.frac * η / ((j : ℕ) : ℝ) ≤ d.base.frac * η :=
      div_le_self (mul_pos hc hη).le hj
    exact lt_of_lt_of_le hy' hle
variable (d)
def mollifiedKernel {q : ℕ} (η : ℝ) (δ : ℕ+ → RealPlane → ℝ)
    (φ : Fin (q + 1) → RealPlane → ℝ) (j : ℕ+) (v : Fin q → ℂ × ℂ) : ℂ :=
  d.base.sigma.productKernel η (fun _ => ofRealFun (δ j)) φ v
end EuclideanFunctionals.PlaneDataWithAperture
end YangMills.Construction
end
