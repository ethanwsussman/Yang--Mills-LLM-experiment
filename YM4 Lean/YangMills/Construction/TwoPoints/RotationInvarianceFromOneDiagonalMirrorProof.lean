import YangMills.Construction.Splines.CubicSplineBasicFacts
import YangMills.Construction.TwoPoints.GrowthOfTheAxisDecayFunctionAtTheOrigin
import YangMills.Construction.TwoPoints.RotationInvarianceFromOneDiagonalMirror
import YangMills.Construction.TwoPoints.TwoHarmonicsAndTwoSigns
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints.DiagonalReflectionRotationInvariance
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TwoPoints.Shapes
open YangMills.Construction.Splines (cubicSpline cubicSplineIntegral)
theorem shapeConst_mem_Ioc (hE : Shapes.ShapesExist.Statement)
    (hB : YangMills.Construction.Splines.CubicSplineBasicFacts) :
    shapeConst ∈ Ioc (0 : ℝ) 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hpos, -, h4⟩ := hE
  obtain ⟨-, -, ⟨-, -, hc⟩, -⟩ := hB
  have g₁ : 0 ≤ derivUniformNorm (Shapes.ofRealFun cubicSpline) := Real.iSup_nonneg fun _ => norm_nonneg _
  have g₂ : 0 ≤ gradPlaneSup (Shapes.ofRealFun planePlateau) := ENNReal.toReal_nonneg
  have g₃ : 0 ≤ gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity) := ENNReal.toReal_nonneg
  have hlow : 0 < lowerShapeBound := by
    unfold lowerShapeBound
    linarith
  have hupp : 0 < upperShapeBound := by
    unfold upperShapeBound
    linarith
  have k₁ : 0 < shapeCoeffOne * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ := by
    unfold shapeCoeffOne
    positivity
  have k₂ : 0 < shapeCoeffTwo / lowerShapeBound :=
    div_pos (by norm_num [shapeCoeffTwo]) hlow
  have k₃ : 0 < shapeCoeffThree / upperShapeBound :=
    div_pos (by norm_num [shapeCoeffThree]) hupp
  exact ⟨lt_min one_pos (lt_min k₁ (lt_min k₂ k₃)), min_le_left _ _⟩
theorem transverseAveragedKernel_zero (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (y : Fin 2 → ℝ) : transverseAveragedKernel S 0 y = 0 := by
  simp [transverseAveragedKernel, profileCorr, lebesgueIntegral, integralWrt]
theorem exists_radius_tsupport_subset {φ : (Fin 2 → ℝ) → ℂ} (hφ : φ ∈ transProfiles) :
    ∃ r : ℝ, 0 < r ∧ tsupport φ ⊆ {ζ | euclidNorm ζ ≤ r} := by
  have h : (ContDiff ℝ 1 φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ univ) ∧
      ∀ x, (φ x).im = 0 := hφ
  have hcont : Continuous (euclidNorm : (Fin 2 → ℝ) → ℝ) := by
    unfold euclidNorm
    fun_prop
  obtain ⟨b, hb⟩ := (h.1.2.1.image hcont).bddAbove
  exact ⟨max b 1, lt_max_of_lt_right one_pos, fun ζ hζ =>
    (hb (mem_image_of_mem _ hζ)).trans (le_max_left _ _)⟩
theorem statement_holds (hE : Shapes.ShapesExist.Statement)
    (hB : YangMills.Construction.Splines.CubicSplineBasicFacts)
    (hG : AxisDecayGrowthAtZero.Statement)
    (hT : TwoHarmonicsVanishing.Statement)
    (hR : PlaneKernelsToOrthogonalInvariance.Statement) :
    DiagonalReflectionRotationInvariance.Statement := by
  refine ⟨shapeConst_mem_Ioc hE hB, fun L S hS hadm hsmall => ?_⟩
  obtain ⟨d₀, u, hdu⟩ := hsmall
  have hinv : ∀ φ ∈ transProfiles, IsRotationInvariantAveragedKernel S φ := by
    intro φ hφ
    by_cases h0 : φ = 0
    · subst h0
      intro y _ t
      rw [transverseAveragedKernel_zero, transverseAveragedKernel_zero]
    · obtain ⟨r, hr, hsub⟩ := exists_radius_tsupport_subset hφ
      exact (hT L S φ hS hadm hφ (hG L S d₀ u φ r hS hadm hdu hφ h0 hr hsub).2.2).2
  obtain ⟨-, -, ⟨han, -⟩, hker, horth⟩ := hR L S hS hadm hinv
  exact ⟨horth, radialProfile S, han, hker⟩
end YangMills.Construction.TwoPoints.DiagonalReflectionRotationInvariance
end
