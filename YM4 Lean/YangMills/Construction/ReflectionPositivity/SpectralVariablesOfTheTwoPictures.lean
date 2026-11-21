import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.JointSpectrum (SpectralDomain)
def expNegEnergy (E : ℝ≥0∞) : unitInterval :=
  if E = ⊤ then 0 else
    ⟨Real.exp (-E.toReal), (Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)⟩
def energyOfUnit (t : unitInterval) : ℝ≥0∞ :=
  if (t : ℝ) = 0 then ⊤ else ENNReal.ofReal (-Real.log t)
theorem energyOfUnit_expNegEnergy (E : ℝ≥0∞) : energyOfUnit (expNegEnergy E) = E := by
  by_cases h : E = ⊤
  · subst h
    simp [energyOfUnit, expNegEnergy]
  · have hval : ((expNegEnergy E : unitInterval) : ℝ) = Real.exp (-E.toReal) := by
      simp [expNegEnergy, h]
    rw [energyOfUnit, hval, if_neg (Real.exp_pos _).ne', Real.log_exp, neg_neg,
      ENNReal.ofReal_toReal h]
theorem expNegEnergy_energyOfUnit (t : unitInterval) : expNegEnergy (energyOfUnit t) = t := by
  by_cases h : (t : ℝ) = 0
  · have ht : t = 0 := Subtype.ext h
    subst ht
    simp [energyOfUnit, expNegEnergy]
  · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h)
    have hlog : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos t.2.1 t.2.2)
    apply Subtype.ext
    simp only [energyOfUnit, if_neg h, expNegEnergy, ENNReal.ofReal_ne_top, if_false]
    rw [ENNReal.toReal_ofReal hlog, neg_neg, Real.exp_log hpos]
variable (μ : Fin 4)
def variableDomain : Set (ℝ≥0∞ × (TransverseAxis μ → ℝ)) :=
  {x | ∀ k, x.2 k ∈ Ioc (-π) π}
def toSpectrum (x : ℝ≥0∞ × (TransverseAxis μ → ℝ)) : SpectralDomain (TransverseAxis μ) :=
  (expNegEnergy x.1, fun k => Circle.exp (x.2 k))
def fromSpectrum (q : SpectralDomain (TransverseAxis μ)) :
    ℝ≥0∞ × (TransverseAxis μ → ℝ) :=
  (energyOfUnit q.1, fun k => Complex.arg (q.2 k))
def imageInSpectrum (D : Set (ℝ≥0∞ × (TransverseAxis μ → ℝ))) :
    Set (SpectralDomain (TransverseAxis μ)) :=
  toSpectrum μ '' (D ∩ variableDomain μ)
def pullToSpectrum (φ : ℝ≥0∞ × (TransverseAxis μ → ℝ) → ℂ) :
    SpectralDomain (TransverseAxis μ) → ℂ :=
  φ ∘ fromSpectrum μ
def angleDot (θ : TransverseAxis μ → ℝ) (w : Fin 4 → ℤ) : ℝ := ∑ k, θ k * (w k.1 : ℝ)
def angleSupNorm (θ : TransverseAxis μ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k => |θ k|
variable (p : ReflectionPair) (ν : unitPositiveClass)
def groundProjection : p.Hilb ν μ →L[ℂ] p.Hilb ν μ :=
  p.jointPVM ν μ (spectrumTop (TransverseAxis μ))
def spectralMeasureOf (ψ : p.Hilb ν μ) : Measure (SpectralDomain (TransverseAxis μ)) :=
  (p.jointPVM ν μ).quadMeasure ψ
def slopeConstant : ℝ := 2 / π * Real.log (1 + √2)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
