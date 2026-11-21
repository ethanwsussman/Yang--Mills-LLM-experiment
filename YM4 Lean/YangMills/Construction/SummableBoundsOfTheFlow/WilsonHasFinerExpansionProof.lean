import YangMills.Construction.QuaternionicWilsonModel.TheSeamsOfTheModelProof
import YangMills.Construction.SummableBoundsOfTheFlow.SumsOfFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.WilsonHasFinerExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open TorusLumps TorusFields BlockAverages
private theorem thirdOrderSize_nonneg {p : _root_.YangMills.Construction.TorusLumps.StepParameters} (h : p.Admissible) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ thirdOrderSize p ε := by
  unfold thirdOrderSize
  exact div_nonneg (mul_nonneg hε h.E₃_pos.le) h.E_pos.le
private theorem hasVanishingCurvatureForm_zero : HasVanishingCurvatureForm 0 := by
  have hd : ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions) (n : ℕ),
      mixedDeriv ((0 : LocalDensity) n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] = 0 := by
    intro c c' X X' n
    unfold mixedDeriv
    have : (fun σ : Fin 2 → ℝ =>
        (0 : LocalDensity) n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] σ (trivialField n))) =
        fun _ => 0 := rfl
    rw [this]
    have h0' : iteratedFDeriv ℝ 2 (fun _ : Fin 2 → ℝ => (0 : ℝ)) = 0 := by
      funext x
      exact congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := Fin 2 → ℝ) (F := ℝ) (n := 2)) x
    rw [h0']
    simp
  refine ⟨fun c c' X X' => ⟨0, ?_⟩, fun A A' _ _ => ?_⟩
  · simp only [hd]
    exact tendsto_const_nhds
  · have hz : limitFormTerm 0 A A' = fun _ => 0 := by
      funext cc
      unfold limitFormTerm secondDerivLimit
      simp only [hd]
      exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
    rw [hz, zero_mul]
    exact hasSum_zero
private theorem wilsonAction_trivialField (n : ℕ) [NeZero n] :
    TorusFields.wilsonAction (Finset.univ : Finset (TorusSite n)) (trivialField n) = 0 := by apply _root_.YangMills.Construction.ModelSeamsProof.wilsonAction_trivialField <;> assumption
theorem wilsonHasRefinedExpansion (hs : normBoundedFamilyClosureStatement)
    (hw : WilsonWeightHasExpansion) : wilsonHasRefinedExpansionStatement := by
  obtain ⟨C₀, hC⟩ := hw
  refine ⟨C₀, ?_⟩
  intro p f yp Bh hadm hCd hf0 hyl hyp hBh β hβ
  have hβ0 : 0 < β := hyp.trans_le hβ
  have hε : 0 ≤ Bh * β ^ (-(3 / 4 : ℝ)) := mul_nonneg hBh (Real.rpow_pos_of_pos hβ0 _).le
  refine ⟨hC p hadm hCd β (hyl.trans hβ), 0, ?_, hasVanishingCurvatureForm_zero, ?_⟩
  · exact (hs p).2.2.2 _ _ hε (thirdOrderSize_nonneg hadm hε)
  · intro n _ hn W hW
    have hne : n ≠ 0 := NeZero.ne n
    simp only [wilsonWeight, dif_neg hne, actionAtLevel]
    rw [Real.log_exp, Real.log_exp, wilsonAction_trivialField, hf0]
    simp [centered]
end YangMills.Construction.FamilyNorms
end
