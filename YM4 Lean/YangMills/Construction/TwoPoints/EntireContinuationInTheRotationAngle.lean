import YangMills.Construction.TwoPoints.FunctionOfTheAngle
import YangMills.Construction.TwoPoints.ThirdPropertyAndFamiliesOfSpectralMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.SpectralCalculus (SpectralPlane)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
theorem diagNormalPlus_mem_planeReflectionNormals : diagNormalPlus ∈ planeReflectionNormals := by
  refine ⟨Or.inr ⟨0, 3, 1, 1, by decide, Or.inl rfl, Or.inl rfl, ?_⟩, ?_⟩
  · simp [diagNormalPlus, add_comm]
  · funext i
    fin_cases i <;> simp [transCoords, diagNormalPlus, coordVec]
def diagNormalMeasure (ρ : planeReflectionNormals → Measure SpectralPlane) : Measure SpectralPlane :=
  ρ ⟨diagNormalPlus, diagNormalPlus_mem_planeReflectionNormals⟩
def boostedExpWeight (r s : ℝ) (p : SpectralPlane) : ℝ :=
  Real.exp (-r * ((p.1 : ℝ) * Real.cosh s + p.2 * Real.sinh s))
structure IsBoostedLaplaceOnLine (F : ℂ → ℂ) (c r : ℝ) (μ : Measure SpectralPlane) : Prop where
  integrable : ∀ s : ℝ, Integrable (boostedExpWeight r s) μ
  eq_integral : ∀ s : ℝ,
    F ((c : ℂ) + Complex.I * (s : ℂ)) = ((∫ p, boostedExpWeight r s p ∂μ : ℝ) : ℂ)
  integral_nonneg : ∀ s : ℝ, 0 ≤ ∫ p, boostedExpWeight r s p ∂μ
structure IsAngleContinuation (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (r : ℝ) (F : ℂ → ℂ) : Prop where
  isAngleFunction : IsAngleFunction S φ r F
  even : ∀ z : ℂ, F (-z) = F z
  periodic : ∀ z : ℂ, F (z + (Real.pi : ℂ) / 2) = F z
  im_ofReal : ∀ t : ℝ, (F (t : ℂ)).im = 0
  norm_le : ∀ a b : ℝ, ‖F ((a : ℂ) + Complex.I * (b : ℂ))‖ ≤
    axisDecayTransform S φ ((2 : ℝ) ^ (-(1 / 2) : ℝ) * r * Real.exp (-|b|))
def EntireAngleContinuation.Statement : Prop :=
  ∀ (L : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ),
    IsDisjointForm S → IsAdmissibleForm L S →
    ∀ φ ∈ transProfiles, ∀ r : ℝ, 0 < r →
      IsAngleContinuation S φ r (angleFunction S φ r) ∧
      ∀ ρ : planeReflectionNormals → Measure SpectralPlane, IsSpectralFamily S φ ρ →
        IsBoostedLaplaceOnLine (angleFunction S φ r) 0 r (axialMeasure ρ) ∧
        IsBoostedLaplaceOnLine (angleFunction S φ r) (Real.pi / 4) r (diagNormalMeasure ρ)
end YangMills.Construction.TwoPoints
end
