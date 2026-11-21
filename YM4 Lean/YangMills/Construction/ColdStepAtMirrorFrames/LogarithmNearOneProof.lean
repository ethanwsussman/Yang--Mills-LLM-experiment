import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfANearElement
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def imPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q - (q.re : ℍ[ℝ]), by show (q - (q.re : ℍ[ℝ])).re = 0; simp⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp
  map_smul' c a := by apply Subtype.ext; ext <;> simp
def imPartCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imPartLinear
def AnalyticLogarithmNearOne : Prop :=
  ∃ (Ψ : imaginaryQuaternions → imaginaryQuaternions) (ε : ℝ), 0 < ε ∧ AnalyticAt ℝ Ψ 0 ∧ Ψ 0 = 0 ∧
    ∀ g : UnitQuaternion, ‖(g : ℍ[ℝ]) - 1‖ < ε → expUnit (Ψ (imPartCLM (g : ℍ[ℝ]))) = g
end YangMills.Construction.ColdStepAtMirrorFrames
end

noncomputable section
open scoped Quaternion ContDiff Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockAverages NormedSpace
namespace AnalyticLog
instance : FiniteDimensional ℝ imaginaryQuaternions := inferInstance
instance : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
def imExpMap (v : imaginaryQuaternions) : imaginaryQuaternions := imPartCLM (exp (v : ℍ[ℝ]))
theorem imPartCLM_coe (v : imaginaryQuaternions) : imPartCLM (v : ℍ[ℝ]) = v := by
  apply Subtype.ext
  have h : (v : ℍ[ℝ]).re = 0 := v.2
  show (v : ℍ[ℝ]) - ((v : ℍ[ℝ]).re : ℍ[ℝ]) = v
  simp [h]
theorem imPartCLM_one : imPartCLM (1 : ℍ[ℝ]) = 0 := by
  apply Subtype.ext
  show (1 : ℍ[ℝ]) - (((1 : ℍ[ℝ])).re : ℍ[ℝ]) = 0
  simp
theorem analyticAt_imExpMap (v : imaginaryQuaternions) : AnalyticAt ℝ imExpMap v := by
  have h1 : AnalyticAt ℝ (fun u : imaginaryQuaternions => (u : ℍ[ℝ])) v :=
    imaginaryQuaternions.subtypeL.analyticAt v
  have h2 : AnalyticAt ℝ (exp : ℍ[ℝ] → ℍ[ℝ]) (v : ℍ[ℝ]) := exp_analytic (𝕂 := ℝ) _
  exact (imPartCLM.analyticAt _).comp (h2.comp h1)
theorem hasFDerivAt_imExpMap_zero :
    HasFDerivAt imExpMap (ContinuousLinearMap.id ℝ imaginaryQuaternions) 0 := by
  have h0 : HasFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      (((0 : imaginaryQuaternions) : ℍ[ℝ])) :=
    hasFDerivAt_exp_zero (𝕂 := ℝ)
  have h1 := (imPartCLM.hasFDerivAt.comp _ h0).comp (0 : imaginaryQuaternions)
    imaginaryQuaternions.subtypeL.hasFDerivAt
  refine h1.congr_fderiv ?_
  ext1 v
  simp [imPartCLM_coe]
end AnalyticLog
open AnalyticLog BlockOffsets in
theorem analyticLogarithmNearOne_of_logNearOne (hlog : LogNearOne) :
    AnalyticLogarithmNearOne := by
  have hc : ContDiffAt ℝ ω imExpMap 0 := (analyticAt_imExpMap 0).contDiffAt
  have hd : HasFDerivAt imExpMap
      ((ContinuousLinearEquiv.refl ℝ imaginaryQuaternions :
        imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions) :
        imaginaryQuaternions →L[ℝ] imaginaryQuaternions) 0 := by
    simpa using hasFDerivAt_imExpMap_zero
  set e := hc.toOpenPartialHomeomorph imExpMap hd (by simp) with he
  have hs : (0 : imaginaryQuaternions) ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hcoe : (e : imaginaryQuaternions → imaginaryQuaternions) = imExpMap :=
    hc.toOpenPartialHomeomorph_coe hd (by simp)
  have h00 : imExpMap 0 = 0 := by
    unfold imExpMap
    simp [imPartCLM_one]
  have he0 : e 0 = 0 := by rw [hcoe]; exact h00
  have ht : (0 : imaginaryQuaternions) ∈ e.target := by
    have := e.map_source hs
    rwa [he0] at this
  have hsy : e.symm 0 = 0 := by
    have := e.left_inv hs
    rwa [he0] at this
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp e.open_source 0 hs
  refine ⟨e.symm, min 1 (δ / 4), by positivity, ?_, hsy, ?_⟩
  · refine e.analyticAt_symm (i := ContinuousLinearEquiv.refl ℝ imaginaryQuaternions) ht ?_ ?_
    · rw [hsy, hcoe]
      exact analyticAt_imExpMap 0
    · rw [hsy, hcoe, hasFDerivAt_imExpMap_zero.fderiv]
      rfl
  · intro g hg
    have hg1 : distFromOne g ≤ 1 := (le_of_lt hg).trans (min_le_left _ _)
    obtain ⟨A, hA, hA2⟩ := hlog g hg1
    have hg2 : distFromOne g < δ / 4 := lt_of_lt_of_le hg (min_le_right _ _)
    have hAs : A ∈ e.source := hball (by
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
    have e1 : imPartCLM (g : ℍ[ℝ]) = e A := by
      rw [hcoe]
      unfold imExpMap
      rw [← hA]
      rfl
    rw [e1, e.left_inv hAs, hA]
end YangMills.Construction.ColdStepAtMirrorFrames
end
