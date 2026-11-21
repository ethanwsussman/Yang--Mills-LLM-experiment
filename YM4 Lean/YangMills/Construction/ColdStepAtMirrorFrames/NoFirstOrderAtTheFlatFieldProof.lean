import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalarProof
import YangMills.Construction.ColdStepAtMirrorFrames.NoFirstOrderAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
variable {F : BlockFrame}
theorem isSmallCurvature_leftTranslate_uniformField {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions) {s ε : ℝ}
    (hε : ∀ x i, ‖v x i‖ ≤ ε) (hs : 4 * ε < s) :
    IsSmallCurvature s (leftTranslate v (uniformField F j)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.isSmallCurvature_leftTranslate_uniform <;> assumption
theorem exists_conj_eq_neg (X : imaginaryQuaternions) :
    ∃ g : UnitQuaternion, (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - (X : ℍ[ℝ]) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.exists_conj_eq_neg <;> assumption
theorem conj_expUnit (g : UnitQuaternion) (w w' : imaginaryQuaternions)
    (h : (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (w' : ℍ[ℝ])) :
    g * expUnit w * g⁻¹ = expUnit w' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.mul_expUnit_mul_inv <;> assumption
theorem firstDerivVanishesAtUniform : FirstDerivVanishesAtUniform := by
  intro F j G s c X hs hinv hX
  obtain ⟨g, hg⟩ := exists_conj_eq_neg (X 0)
  set h : (Fin 1 → ℝ) → ℝ :=
    fun τ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) (uniformField F j)) with hh
  have hev : h =ᶠ[𝓝 0] fun τ => h (-τ) := by
    have hball : Metric.ball (0 : Fin 1 → ℝ) (s / 8) ∈ 𝓝 (0 : Fin 1 → ℝ) := Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with τ hτ
    have hτ0 : |τ 0| ≤ s / 8 := by
      have h1 : ‖τ‖ < s / 8 := by simpa using hτ
      have h2 : ‖τ 0‖ ≤ ‖τ‖ := norm_le_pi_norm τ 0
      rw [Real.norm_eq_abs] at h2
      linarith
    have hsp : ∀ (τ' : Fin 1 → ℝ) x i,
        ColdStepAtMirrorFrames.bondSpread c X τ' x i = if c 0 = (x, i) then τ' 0 • X 0 else 0 := by
      intro τ' x i
      simp [ColdStepAtMirrorFrames.bondSpread]
    have hsmall : IsSmallCurvature s
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) (uniformField F j)) := by
      refine isSmallCurvature_leftTranslate_uniformField _ (ε := s / 8) (fun x i => ?_) (by linarith)
      rw [hsp]
      split_ifs
      · rw [norm_smul, hX 0, mul_one, Real.norm_eq_abs]
        exact hτ0
      · simp
        positivity
    have key : gaugeTransform (fun _ => g)
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) (uniformField F j)) =
        leftTranslate (ColdStepAtMirrorFrames.bondSpread c X (-τ)) (uniformField F j) := by
      funext x i
      simp only [gaugeTransform, leftTranslate, uniformField, mul_one, hsp]
      split_ifs
      · apply conj_expUnit
        simp only [Submodule.coe_smul, Pi.neg_apply, mul_smul_comm, smul_mul_assoc, hg, neg_smul, smul_neg]
      · apply conj_expUnit
        simp
    show G _ = G _
    rw [← key, hinv _ _ hsmall]
  have e0 : ∀ v, fderiv ℝ h 0 v = 0 := by
    intro v
    by_cases hd : DifferentiableAt ℝ h 0
    · have hneg : HasFDerivAt (fun τ : Fin 1 → ℝ => -τ) (-ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) 0 :=
        (hasFDerivAt_id _).neg
      have hd' : HasFDerivAt h (fderiv ℝ h 0) (-(0 : Fin 1 → ℝ)) := by
        rw [neg_zero]
        exact hd.hasFDerivAt
      have hc : HasFDerivAt (fun τ => h (-τ))
          ((fderiv ℝ h 0).comp (-ContinuousLinearMap.id ℝ (Fin 1 → ℝ))) 0 :=
        hd'.comp 0 hneg
      have e1 := hev.fderiv_eq (𝕜 := ℝ)
      rw [hc.fderiv] at e1
      have e2 := congrArg (fun M : (Fin 1 → ℝ) →L[ℝ] ℝ => M v) e1
      simp at e2
      linarith
    · rw [fderiv_zero_of_not_differentiableAt hd]
      rfl
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply]
  exact e0 _
end ColdStepAtMirrorFrames
end YangMills.Construction
end
