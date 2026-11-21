import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.EntireContinuationInTheRotationAngle
import YangMills.Construction.TwoPoints.GrowthBoundsTheNumberOfHarmonics
import YangMills.Construction.TwoPoints.TwoHarmonicsAndTwoSigns
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
namespace TwoHarmonicsVanishing
theorem cosh_coeff_eq_zero {a b : ℝ} (hAdd : ∀ x : ℝ, 0 ≤ a + b * Real.cosh (4 * x))
    (hSub : ∀ x : ℝ, 0 ≤ a - b * Real.cosh (4 * x)) : b = 0 := by
  by_contra hne
  have habs : 0 < |b| := abs_pos.mpr hne
  have hbound : ∀ x : ℝ, |b| * Real.cosh (4 * x) ≤ a := by
    intro x
    rcases abs_cases b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith [hAdd x, hSub x]
  set y : ℝ := 2 * (a / |b|) + 1 with hy
  have hcosh : (y + 1) / 2 ≤ Real.cosh y := by
    rw [Real.cosh_eq]
    linarith [Real.add_one_le_exp y, Real.exp_pos (-y)]
  have hx := hbound (y / 4)
  rw [show 4 * (y / 4) = y by ring] at hx
  have hlt : a / |b| < Real.cosh y := by
    have : (y + 1) / 2 = a / |b| + 1 := by rw [hy]; ring
    linarith
  rw [div_lt_iff₀ habs] at hlt
  linarith [mul_comm (Real.cosh y) |b|]
theorem exists_pos_smul_planeUnit (y : Fin 2 → ℝ) (hy : y ≠ 0) :
    ∃ (r : ℝ) (θ : ℝ), 0 < r ∧ embedPlane y = r • planeUnit θ := by
  set z : ℂ := ⟨y 0, y 1⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hy
    have h0 : y 0 = 0 := by simpa [hz] using congrArg Complex.re h
    have h1 : y 1 = 0 := by simpa [hz] using congrArg Complex.im h
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  refine ⟨‖z‖, Complex.arg z, norm_pos_iff.mpr hz0, ?_⟩
  have hre : ‖z‖ * Real.cos (Complex.arg z) = y 0 := Complex.norm_mul_cos_arg z
  have him : ‖z‖ * Real.sin (Complex.arg z) = y 1 := Complex.norm_mul_sin_arg z
  rw [embedPlane, planeUnit, smul_add, smul_smul, smul_smul, hre, him]
theorem planeCoords_embedPlane (y : Fin 2 → ℝ) : planeCoords (embedPlane y) = y := by
  funext i
  fin_cases i <;> simp [planeCoords, embedPlane, coordVec, PeriodicLattice.coordVec]
end TwoHarmonicsVanishing
open TwoHarmonicsVanishing in
theorem TwoHarmonicsVanishing.holds
    (hCount : HarmonicCountFromGrowth.Statement)
    (hEnt : EntireAngleContinuation.Statement)
    (hRefl : ReflectionsPlaneFacts.Statement)
    (hSpec : SpectralMeasuresAtAllNormals.Statement) :
    TwoHarmonicsVanishing.Statement := by
  intro St S φ hForm hProps hφ hGrowth
  have hFam : IsSpectralFamily S φ
      (fun n : planeReflectionNormals => averagedKernelSpectralMeasure S φ (n : AmbientSpace)) :=
    { decay := fun n => ((hSpec St S φ hForm hProps hφ).1 n n.2).represents
      plate_norm := fun n => ((hSpec St S φ hForm hProps hφ).1 n n.2).plateNorm }
  have key : ∀ r : ℝ, 0 < r → ∃ a b : ℝ,
      (∀ w : ℂ, angleFunction S φ r w = (a : ℂ) + (b : ℂ) * Complex.cos (4 * w)) ∧
      b = 0 ∧
      ∀ θ : ℝ, transverseAveragedKernel S φ (planeCoords (r • planeUnit θ)) = (a : ℂ) := by
    intro r hr
    obtain ⟨c, hc⟩ := hCount St S φ hForm hProps hφ 1
      (by simpa using hGrowth) r hr
    have hTwo : ∀ w : ℂ, angleFunction S φ r w =
        ((c 0 : ℝ) : ℂ) + ((c 1 : ℝ) : ℂ) * Complex.cos (4 * w) := by
      intro w
      rw [hc w, Fin.sum_univ_two]
      simp
    obtain ⟨hCont, hSigns⟩ := hEnt St S hForm hProps φ hφ r hr
    obtain ⟨hIm, hDiag⟩ := hSigns _ hFam
    have hFirst : ∀ x : ℝ, 0 ≤ c 0 + c 1 * Real.cosh (4 * x) := by
      intro x
      have h := hIm.eq_integral x
      rw [hTwo] at h
      have hcos : Complex.cos (4 * (((0 : ℝ) : ℂ) + Complex.I * (x : ℂ))) =
          ((Real.cosh (4 * x) : ℝ) : ℂ) := by
        rw [show (4 * (((0 : ℝ) : ℂ) + Complex.I * (x : ℂ))) = ((4 * x : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.cos_mul_I, Complex.ofReal_cosh]
      rw [hcos] at h
      have h' : c 0 + c 1 * Real.cosh (4 * x) =
          ∫ p, boostedExpWeight r x p ∂(axialMeasure
            (fun n : planeReflectionNormals => averagedKernelSpectralMeasure S φ (n : AmbientSpace))) := by
        exact_mod_cast h
      rw [h']
      exact hIm.integral_nonneg x
    have hSecond : ∀ x : ℝ, 0 ≤ c 0 - c 1 * Real.cosh (4 * x) := by
      intro x
      have h := hDiag.eq_integral x
      rw [hTwo] at h
      have hcos : Complex.cos (4 * (((Real.pi / 4 : ℝ) : ℂ) + Complex.I * (x : ℂ))) =
          -((Real.cosh (4 * x) : ℝ) : ℂ) := by
        rw [show (4 * (((Real.pi / 4 : ℝ) : ℂ) + Complex.I * (x : ℂ))) =
            ((4 * x : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) by push_cast; ring,
          Complex.cos_add_pi, Complex.cos_mul_I, Complex.ofReal_cosh]
      rw [hcos] at h
      have h' : c 0 - c 1 * Real.cosh (4 * x) =
          ∫ p, boostedExpWeight r x p ∂(diagNormalMeasure
            (fun n : planeReflectionNormals => averagedKernelSpectralMeasure S φ (n : AmbientSpace))) := by
        have h'' : ((c 0 - c 1 * Real.cosh (4 * x) : ℝ) : ℂ) =
            ((∫ p, boostedExpWeight r x p ∂(diagNormalMeasure
              (fun n : planeReflectionNormals => averagedKernelSpectralMeasure S φ (n : AmbientSpace))) : ℝ) : ℂ) := by
          rw [← h]
          push_cast
          ring
        exact_mod_cast h''
      rw [h']
      exact hDiag.integral_nonneg x
    have hZero : c 1 = 0 := cosh_coeff_eq_zero hFirst hSecond
    refine ⟨c 0, c 1, hTwo, hZero, fun θ => ?_⟩
    rw [← hCont.isAngleFunction.ofReal_eq θ, hTwo, hZero]
    simp
  refine ⟨key, ?_⟩
  intro y hy t
  obtain ⟨r, θ, hr, hyr⟩ := exists_pos_smul_planeUnit y hy
  obtain ⟨a, b, -, -, hConst⟩ := key r hr
  have hRot : rotateInPlane t (planeUnit θ) = planeUnit (θ + t) :=
    ((hRefl.2.2.2.2.1.1 θ t (planeUnit θ) rfl).2.2.2)
  have hy' : y = planeCoords (r • planeUnit θ) := by
    rw [← hyr, planeCoords_embedPlane]
  rw [hyr, map_smul, hRot, hConst (θ + t)]
  conv_rhs => rw [hy']
  rw [hConst θ]
end YangMills.Construction.TwoPoints
end
