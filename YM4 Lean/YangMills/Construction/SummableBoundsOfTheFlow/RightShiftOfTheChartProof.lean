import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftExists
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftMovesTheLogarithm
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftOfTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
namespace RightTranslationChart
instance instFiniteDimensionalImaginaryQuaternions : FiniteDimensional ℝ imaginaryQuaternions :=
  FiniteDimensional.finiteDimensional_submodule _
instance instCompleteSpaceImaginaryQuaternions : CompleteSpace imaginaryQuaternions :=
  FiniteDimensional.complete ℝ imaginaryQuaternions
def diagonalCLM : imaginaryQuaternions →L[ℝ]
    imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
  (ContinuousLinearMap.id ℝ imaginaryQuaternions).prod
    (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ imaginaryQuaternions))
def partialFirst
    (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (w : imaginaryQuaternions) : imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
  (fderiv ℝ Θ (diagonalTriple w)).comp
    (ContinuousLinearMap.inl ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions))
def partialSecond
    (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (w : imaginaryQuaternions) : imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
  (fderiv ℝ Θ (diagonalTriple w)).comp
    ((ContinuousLinearMap.inr ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)).comp
      (ContinuousLinearMap.inl ℝ imaginaryQuaternions imaginaryQuaternions))
theorem diagonalTriple_eq_diagonalCLM (w : imaginaryQuaternions) : diagonalTriple w = diagonalCLM w := by
  simp [diagonalTriple, diagonalCLM]
theorem partials_contDiffAt
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)} (hU : IsOpen U)
    (hdiag : ∀ r, diagonalTriple r ∈ U) (hsmooth : ContDiffOn ℝ 3 Θ U) (w : imaginaryQuaternions) :
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (partialFirst Θ) w ∧
      ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (partialSecond Θ) w := by
  have h1 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Θ (diagonalCLM w) := by
    rw [← diagonalTriple_eq_diagonalCLM]
    exact hsmooth.contDiffAt (hU.mem_nhds (hdiag w))
  have h2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fderiv ℝ Θ) (diagonalCLM w) :=
    h1.fderiv_right (by norm_num)
  have h3 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun w' => fderiv ℝ Θ (diagonalCLM w')) w :=
    ContDiffAt.comp w h2 diagonalCLM.contDiff.contDiffAt
  have e : ∀ w', fderiv ℝ Θ (diagonalTriple w') = fderiv ℝ Θ (diagonalCLM w') := fun w' => by
    rw [diagonalTriple_eq_diagonalCLM]
  refine ⟨?_, ?_⟩
  · have : partialFirst Θ = fun w' => (fderiv ℝ Θ (diagonalCLM w')).comp
        (ContinuousLinearMap.inl ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)) := by
      funext w'
      simp only [partialFirst, e]
    rw [this]
    exact h3.clm_comp contDiffAt_const
  · have : partialSecond Θ = fun w' => (fderiv ℝ Θ (diagonalCLM w')).comp
        ((ContinuousLinearMap.inr ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)).comp
          (ContinuousLinearMap.inl ℝ imaginaryQuaternions imaginaryQuaternions)) := by
      funext w'
      simp only [partialSecond, e]
    rw [this]
    exact h3.clm_comp contDiffAt_const
end RightTranslationChart
open RightTranslationChart in
theorem rightTranslationChart_holds (hE : rightTranslationDerivExistsStatement)
    (hM : logDerivAlongRightTranslationStatement) (hLog : ConjugatedExpLogSmooth) :
    rightTranslationChartStatement := by
  obtain ⟨T₀, hT₀⟩ := hE
  obtain ⟨Θ, U, C₀, hU, hC₀, hdiag, hsmooth, hexp, hzero, -, -, -⟩ := hLog
  have hm := hM Θ U hU hdiag hsmooth hexp hzero
  have hsecond : ∀ w X, ((partialSecond Θ w X : imaginaryQuaternions) : ℍ[ℝ]) =
      NormedSpace.exp (w : ℍ[ℝ]) * (X : ℍ[ℝ]) * (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) :=
    fun w X => (hm w X).1
  have hexp_ne : ∀ w : imaginaryQuaternions, NormedSpace.exp (w : ℍ[ℝ]) ≠ 0 := fun w h => by
    have h1 : (star ((expUnit w : UnitQuaternion) : ℍ[ℝ])) * ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = 1 :=
      Unitary.coe_star_mul_self _
    have h2 : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
    rw [h2, h] at h1
    simp at h1
  have hunit_ne : ∀ g : UnitQuaternion, (g : ℍ[ℝ]) ≠ 0 := fun g h => by
    have h1 : (star (g : ℍ[ℝ])) * (g : ℍ[ℝ]) = 1 := Unitary.coe_star_mul_self _
    rw [h] at h1
    simp at h1
  have hinj : ∀ w, Function.Injective
      (partialSecond Θ w : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions) := by
    intro w
    rw [injective_iff_map_eq_zero]
    intro X hX
    have h1 := hsecond w X
    have h2 : partialSecond Θ w X = 0 := hX
    rw [h2] at h1
    have h3 : (X : ℍ[ℝ]) = 0 := by
      have h4 : NormedSpace.exp (w : ℍ[ℝ]) * (X : ℍ[ℝ]) * (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 0 := by
        simpa using h1.symm
      rcases mul_eq_zero.1 h4 with h5 | h5
      · rcases mul_eq_zero.1 h5 with h6 | h6
        · exact absurd h6 (hexp_ne w)
        · exact h6
      · exact absurd h5 (hunit_ne _)
    exact Subtype.ext h3
  have hequiv : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi →
      ∃ e : imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions,
        (e : imaginaryQuaternions →L[ℝ] imaginaryQuaternions) = partialFirst Θ w ∧
        ∀ X, e.symm (partialSecond Θ w X) = T₀ w X := by
    intro w hw
    have key : ∀ X, partialFirst Θ w (T₀ w X) = partialSecond Θ w X := fun X =>
      Subtype.ext (((hm w X).2 _ (hT₀ w X hw)).trans (hsecond w X).symm)
    have hsurj2 := LinearMap.injective_iff_surjective.1 (hinj w)
    have hsurj : Function.Surjective
        (partialFirst Θ w : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions) := fun Y => by
      obtain ⟨X, hX⟩ := hsurj2 Y
      exact ⟨T₀ w X, (key X).trans hX⟩
    have hinj1 := LinearMap.injective_iff_surjective.2 hsurj
    let e := (LinearEquiv.ofBijective
      (partialFirst Θ w : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions) ⟨hinj1, hsurj⟩).toContinuousLinearEquiv
    have he : (e : imaginaryQuaternions →L[ℝ] imaginaryQuaternions) = partialFirst Θ w :=
      ContinuousLinearMap.ext fun X => rfl
    refine ⟨e, he, fun X => ?_⟩
    rw [← key X]
    have : partialFirst Θ w (T₀ w X) = e (T₀ w X) := by rw [← he]; rfl
    rw [this]
    simp
  set T : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions := fun w =>
    (ContinuousLinearMap.inverse (partialFirst Θ w)).comp (partialSecond Θ w) with hTdef
  have hsmoothT : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) T w := by
    intro w hw
    have hw' : ‖w‖ < Real.pi := lt_of_le_of_lt hw (by linarith [Real.pi_gt_three])
    obtain ⟨e, he, -⟩ := hequiv w hw'
    obtain ⟨h1, h2⟩ := partials_contDiffAt hU hdiag hsmooth w
    have h3 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
        (ContinuousLinearMap.inverse :
          (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
        (partialFirst Θ w) := by
      rw [← he]
      exact contDiffAt_map_inverse e
    have h4 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
        (fun w' => ContinuousLinearMap.inverse (partialFirst Θ w')) w :=
      ContDiffAt.comp w h3 h1
    exact h4.clm_comp h2
  have : ProperSpace imaginaryQuaternions := FiniteDimensional.proper_real imaginaryQuaternions
  have hcont : ∀ j : ℕ, j ≤ 2 → ∃ C : ℝ,
      ∀ w ∈ Metric.closedBall (0 : imaginaryQuaternions) 1, ‖iteratedFDeriv ℝ j T w‖ ≤ C := by
    intro j hj
    refine (isCompact_closedBall (0 : imaginaryQuaternions) 1).exists_bound_of_continuousOn fun w hw => ?_
    have hw1 : ‖w‖ ≤ 1 := by simpa using hw
    exact ((hsmoothT w hw1).continuousAt_iteratedFDeriv (by exact_mod_cast hj)).continuousWithinAt
  obtain ⟨C0, h0⟩ := hcont 0 (by omega)
  obtain ⟨C1, h1⟩ := hcont 1 (by omega)
  obtain ⟨C2, h2⟩ := hcont 2 le_rfl
  refine ⟨T, |C0| + |C1| + |C2|, by positivity, fun w X hw => ?_, hsmoothT, fun w j hw hj => ?_⟩
  · obtain ⟨e, he, hs⟩ := hequiv w hw
    have : T w X = T₀ w X := by
      simp only [hTdef]
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact hs X
    rw [this]
    exact hT₀ w X hw
  · have hmem : w ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 := by simpa using hw
    have a0 := abs_nonneg C0
    have a1 := abs_nonneg C1
    have a2 := abs_nonneg C2
    interval_cases j
    · exact (h0 w hmem).trans (by linarith [le_abs_self C0])
    · exact (h1 w hmem).trans (by linarith [le_abs_self C1])
    · exact (h2 w hmem).trans (by linarith [le_abs_self C2])
end YangMills.Construction.Interpolation
end
