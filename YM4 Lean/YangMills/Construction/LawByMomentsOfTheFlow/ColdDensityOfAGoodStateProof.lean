import YangMills.Construction.ResponseInTheExpansion.GasResponseReadsItsSiteProof
import YangMills.Construction.LawByMomentsOfTheFlow.ColdDensityOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun P => Q₁ P ∧ Q₂ P := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h : ∀ P, Q₁ P → Q₂ P) : ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem settings_forAllParameters (hMass : StepGas.SettingMassEqIntegral)
    (hConf : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) :
    ForAllParameters fun P => 0 < P.stepParams.threshold ∧ 1 ≤ P.stepParams.side ∧ 200 * P.table.B ≤ P.floor ∧
      0 ≤ P.floor ∧
      (∀ R : StepSettings.StepSetup, R.OnParameters P.table P.floor → ∀ (n : ℕ) [NeZero n], P.table.n₀ ≤ n →
        ∀ s : StepSettings.ChartSetting R n, s.IsAdmissible →
        Integrable (fun η => s.cutoffProduct η * Real.exp (-s.potential η)) ∧
          0 < ∫ η, s.cutoffProduct η * Real.exp (-s.potential η)) ∧
      (∀ R : StepSettings.StepSetup, R.OnParameters P.table P.floor → R.nextCoupling ≤ 1.01 * R.coupling →
        ∀ (n : ℕ) [NeZero n] (G : StepGas.GasGround R n), G.IsAdmissibleGround →
        ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible) := by
  obtain ⟨rt₀, hrt₀, HM⟩ := hMass
  intro a _
  refine ⟨1, rt₀, 0, hrt₀, ?_⟩
  intro L _ hL Tb _ hTL hD _ _ hrt _ _ _
  obtain ⟨y₁, Y₁⟩ := HM Tb hD hrt
  obtain ⟨y₂, Y₂⟩ := hConf Tb hD
  refine ⟨max (max y₁ y₂) (max (200 * Tb.B) 0), fun y hy _ _ g _ _ k _ _ _ R d _ => ?_⟩
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy₃ : 200 * Tb.B ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy₄ : 0 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  refine ⟨hD.σ_pos, ?_, hy₃, hy₄, ?_, ?_⟩
  · show 1 ≤ Tb.side
    rw [hTL]
    exact hL
  · intro R hR n _ hn s hs
    obtain ⟨h1, h2, -⟩ := Y₁ y hy₁ R hR n hn s hs
    exact ⟨h1, h2⟩
  · intro R hR hx n _ G hG σ hσ
    exact Y₂ y hy₂ R hR hx n G hG σ hσ
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem settingOf_allVacant (G : StepGas.GasGround R n) :
    G.settingOf (G.familyOf G.allVacant) = G.groundSetting := by apply _root_.YangMills.DeltaSharedProofs.p176 <;> assumption
abbrev _root_.YangMills.SharedProofs.p14309 := @settingOf_allVacant
private theorem mul_rpow_neg_quarter_lt (x σ : ℝ) (hσ : 0 < σ) (hx : (64 / σ + 1) ^ 4 ≤ x) :
    64 * x ^ (-(1 / 4) : ℝ) < 9 / 8 * σ := by
  have ha : 0 < 64 / σ + 1 := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : 64 / σ + 1 ≤ x ^ ((1 : ℝ) / 4) := by
    have h2 := Real.rpow_le_rpow (by positivity) hx (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have h3 : ((64 / σ + 1) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = 64 / σ + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      norm_num
    rwa [h3] at h2
  have h4 : 0 < x ^ ((1 : ℝ) / 4) := by positivity
  rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_lt_iff₀ h4]
  have h5 : 64 / σ * σ = 64 := by field_simp
  have h6 : (64 / σ + 1) * σ ≤ x ^ ((1 : ℝ) / 4) * σ := mul_le_mul_of_nonneg_right h1 hσ.le
  nlinarith
abbrev _root_.YangMills.SharedProofs.p21801 := @mul_rpow_neg_quarter_lt
theorem coldDensityIntegrable (hMass : StepGas.SettingMassEqIntegral)
    (hConf : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hCut : goodConfigCutoffStatement)
    (hWin : scaleWindowStatement) : coldDensityIntegrableStatement := by
  unfold goodConfigCutoffStatement ForAllPoints at hCut
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold coldDensityIntegrableStatement ForAllPoints
  refine forAllParameters_mono
    (forAllParameters_and (settings_forAllParameters hMass hConf) (forAllParameters_and hCut hWin)) ?_
  rintro P ⟨⟨hσ, hL1, hB, hy0, hM, hG⟩, ⟨_, _, X₁, _, hy₁, H₁⟩, ⟨_, _, X₂, _, _, H₂⟩⟩
  refine ⟨fun _ => 0, 1, max (max X₁ X₂) ((64 / P.stepParams.threshold + 1) ^ 4), one_pos,
    le_trans hy₁ (le_trans (le_max_left _ _) (le_max_left _ _)), fun S hx d n _ hd hn V Y hgood => ?_⟩
  have hx₁ : X₁ ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₃ : X₂ ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx₂ : (64 / P.stepParams.threshold + 1) ^ 4 ≤ S.scaleCoupling := le_trans (le_max_right _ _) hx
  have hK : S.lastSeparated + d ≤ S.data.windowLevel := by
    obtain ⟨-, -, -, -, -, h1, -⟩ := H₂ S hx₃
    omega
  have hstand : ResponseInTheExpansion.StageOnFlow P.table P.response P.floor S.β (S.lastSeparated + d)
      ⟨S.tower.stage (S.lastSeparated + d), S.resp (S.lastSeparated + d)⟩ := by
    have h := S.onFlow (S.lastSeparated + d) hK
    rwa [← S.stage_eq (S.lastSeparated + d) hK] at h
  have hon : (S.tower.stage (S.lastSeparated + d)).toStepSetup.OnParameters P.table P.floor :=
    hstand.onFamily.onFamily
  have hmv : |(S.tower.stage (S.lastSeparated + d)).toStepSetup.nextCoupling -
      (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling| ≤ 2 * P.table.B :=
    hstand.onFamily.abs_sub_le
  have hxx : (S.tower.stage (S.lastSeparated + d)).toStepSetup.nextCoupling ≤
      1.01 * (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by
    have h1 := (abs_le.mp hmv).2
    have h2 := hon.le_coupling
    linarith only [h1, h2, hB, hy0]
  have hcold : TorusFields.IsCold (9 / 8 * P.stepParams.threshold)
      (S.smoothedField (S.lastSeparated + d + 1) n V) := by
    intro z μ ν hμ
    obtain ⟨-, -, h3, -⟩ := H₁ S hx₁ (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hgood
    have h4 := h3 1 zero_le_one le_rfl z μ ν hμ
    have h5 := mul_rpow_neg_quarter_lt S.scaleCoupling P.stepParams.threshold hσ hx₂
    have h6 := hgood.curvature_le
    exact lt_of_le_of_lt (h4.trans (by linarith only [h6])) h5
  have hside : P.table.n₀ ≤ n := by
    have h1 : P.stepParams.side * P.stepParams.n₀ ≤ S.data.period P.stepParams.side := S.side_le
    have h2 : S.data.period P.stepParams.side ≤ n := by
      rw [hn]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have h3 : P.stepParams.n₀ ≤ P.stepParams.side * P.stepParams.n₀ := Nat.le_mul_of_pos_left _ (by omega)
    exact h3.trans (h1.trans h2)
  have hgr : (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)).IsAdmissibleGround :=
    Or.inl ⟨hside, hcold, rfl, rfl, rfl⟩
  have hset : (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)).IsAdmissible := by
    have h := hG _ hon hxx n _ hgr (StepGas.GasGround.allVacant _)
      (fun i j _ => StepGas.GasGround.pairConstraint _ |>.vacant_compatible i j _)
    rwa [settingOf_allVacant] at h
  exact hM _ hon n hside _ hset
end YangMills.Construction.MomentLaw
end
