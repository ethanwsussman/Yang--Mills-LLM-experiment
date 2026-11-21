import YangMills.Construction.SummableBoundsOfTheFlow.SumsOfFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.TheOneLoopNumberIsHad
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps FamilyNorms
namespace StepDensities
private theorem mixedDeriv_const_zero {n k : ℕ} (hk : 1 ≤ k) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField n => (0 : ℝ)) W c X = 0 := by
  unfold mixedDeriv
  rw [iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  rfl
private theorem referenceBounds_level_zero (T : ColdStepAtMirrorFrames.StepParameters)
    (ℓ : TorusLumps.StepParameters) (hS : normBoundedFamilyClosureStatement) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k) (hE : 0 ≤ T.E) (hE₃ : 0 ≤ T.energyRatio) (hw : ∀ m, 0 < ℓ.weight m) :
    ReferenceBoundsAtLevel T ℓ B 0 := by
  have h0 : T.referenceDensity 0 = 0 := rfl
  have hz : ∀ (n : ℕ) (y : TorusSite n), T.referenceDensity 0 n y = fun _ => (0 : ℝ) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]
    exact (hS ℓ).2.2.2 _ _ (by positivity) (by positivity)
  · refine ⟨fun c c' X X' => ⟨0, ?_⟩, fun A A' _ _ => ?_⟩
    · refine tendsto_const_nhds.congr fun n => ?_
      rw [hz, mixedDeriv_const_zero (by norm_num)]
    · have hterm : limitFormTerm (T.referenceDensity 0) A A' = fun _ => 0 := by
        funext cc
        unfold limitFormTerm secondDerivLimit
        have : (fun n : ℕ => mixedDeriv (T.referenceDensity 0 n 0) (trivialField n) ![bondFrom 0 cc.1, bondFrom 0 cc.2]
            ![linearPotential A cc.1, linearPotential A' cc.2]) = fun _ => 0 := by
          funext n
          rw [hz, mixedDeriv_const_zero (by norm_num)]
        rw [this]
        exact tendsto_const_nhds.limUnder_eq
      rw [hterm, zero_mul]
      exact hasSum_zero
  · intro n _ _ y W _ k c X
    rw [hz]
    exact analyticAt_const
  · intro n _ _ g W W' _ _ _
    simp [centered, hz]
  · intro n _ _ y W _ k c X h4 _ _
    rw [hz, mixedDeriv_const_zero (by omega), abs_zero]
    exact div_nonneg (hB k) (hw _).le
theorem referenceSmoothStatement_holds (hU : referenceNextLevelStatement)
    (hN : oneLoopCoeffBound) (hS : normBoundedFamilyClosureStatement) :
    referenceSmoothStatement := by
  refine EventuallyOrdered.mono (EventuallyOrdered.and hU hN) ?_
  rintro T hT hn ⟨cU, cN⟩ hroom
  obtain ⟨Ck, hCk, gU⟩ := cU hroom
  have hE₃ : 0 ≤ T.energyRatio := by
    have h1 : (1 : ℝ) ≤ T.E := hT.one_le_E
    have h2 := hT.η₃_pos
    unfold ColdStepAtMirrorFrames.StepParameters.energyRatio
    positivity
  set e₄ : ℝ := 4 / 3 * (Ck 4 * (1 + T.energyRatio)) with he₄
  set e₅ : ℝ := 4 / 3 * (Ck 5 * (1 + max T.energyRatio e₄)) with he₅
  set e₆ : ℝ := 4 / 3 * (Ck 6 * (1 + max (max T.energyRatio e₄) e₅)) with he₆
  have h₄ : 0 ≤ e₄ := mul_nonneg (by norm_num) (mul_nonneg (hCk 4) (by linarith))
  have h₅ : 0 ≤ e₅ := mul_nonneg (by norm_num)
    (mul_nonneg (hCk 5) (by linarith [le_max_left T.energyRatio e₄]))
  have h₆ : 0 ≤ e₆ := mul_nonneg (by norm_num)
    (mul_nonneg (hCk 6) (by linarith [le_max_left (max T.energyRatio e₄) e₅, le_max_left T.energyRatio e₄]))
  set B : ℕ → ℝ := fun k => if k = 4 then e₄ else if k = 5 then e₅ else if k = 6 then e₆ else 0 with hB
  have hB0 : ∀ k, 0 ≤ B k := by
    intro k
    simp only [hB]
    split_ifs <;> first | exact h₄ | exact h₅ | exact h₆ | exact le_rfl
  have hfix : ∀ k, 4 ≤ k → k ≤ 6 → B k / 4 + Ck k * (1 + maxLowerOrderBounds T.energyRatio B k) = B k := by
    intro k h4 h6
    have hk : k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk with rfl | rfl | rfl
    · simp only [hB, maxLowerOrderBounds]
      norm_num
      rw [he₄]
      ring
    · simp only [hB, maxLowerOrderBounds]
      norm_num
      rw [he₅]
      ring
    · simp only [hB, maxLowerOrderBounds]
      norm_num
      rw [he₆]
      ring
  refine ⟨B, fun ℓ hm hfits => ?_⟩
  have hw : ∀ m, 0 < ℓ.weight m := by
    intro m
    unfold TorusLumps.StepParameters.weight
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  have hE : 0 ≤ T.E := by
    have h1 : (1 : ℝ) ≤ T.E := hT.one_le_E
    linarith
  have hlevel : ∀ t, ReferenceBoundsAtLevel T ℓ B t := by
    intro t
    induction t with
    | zero => exact referenceBounds_level_zero T ℓ hS B hB0 hE hE₃ hw
    | succ t ih =>
      have h := (gU ℓ hm hfits t B hB0 ih).2
      refine ⟨h.family, h.vanishing_curvatureForm, h.analytic, h.isometries, ?_⟩
      intro n _ hn' y W hW k c X h4 h6 hX
      have := h.higherDeriv_le n hn' y W hW k c X h4 h6 hX
      simp only [hfix k h4 h6] at this
      exact this
  intro t
  obtain ⟨n₁, n₂⟩ := cN ℓ hm hfits t
  exact
    { hlevel t with
      curvatureForm_minimizer := (gU ℓ hm hfits t B hB0 (hlevel t)).1
      curvatureForm_step := n₁
      oneLoopCoeff_abs_le := n₂ }
end StepDensities
end YangMills.Construction
end
