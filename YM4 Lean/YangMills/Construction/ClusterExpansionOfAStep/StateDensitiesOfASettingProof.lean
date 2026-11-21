import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TwoActionsAlongMovesForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps TorusFields StepSettings BlockAverages ColdStepAtMirrorFrames
private theorem supDist_le_half_side {N : ℕ} [NeZero N] (x y : TorusSite N) : supDist x y ≤ N / 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card <;> assumption
private theorem coordNorm_zero : coordNorm 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
theorem blockDensitiesMeasurableBounded_holds (h3 : ExpansionBasicBounds) :
    BlockDensitiesMeasurableBounded := by
  intro R n _ s hfit hE hx hr hLr hrow hn hs
  classical
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  obtain ⟨_, facts2, _⟩ := h3 R.params R.depth R.coupling R.functional R.density R.labels
    R.labelWeight R.clusterFactor R.siteDensity hfit hE hx hr hrow.1 hrow.2
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have h0 : s.InBalls 0 := fun b => by
    show coordNorm 0 ≤ R.ballRadius
    rw [coordNorm_zero]
    exact hρ.le
  have hrt : 0 ≤ R.params.decayRate := by
    have := hfit.rt_pos
    unfold StepParameters.decayRate
    positivity
  have key : ∀ (y : TorusSite (n * R.params.side)) (η : FreeCoords s.free), s.InBalls η →
      |R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling| ≤
        2 * R.params.E + |R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling| + 1 := by
    intro y η hη
    have hEpos : 0 ≤ R.params.E := by linarith
    by_cases hfar : ∀ z ∈ s.support, (R.range : ℝ) / 4 ≤ supDist y z
    · have := facts2 (n * R.params.side) hbs (s.field η) s.support s.labelling y (hs.isHull η hη)
        (hs.factor_ne_zero η hη) hfar
      have h2 := abs_nonneg (R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling)
      linarith
    · push_neg at hfar
      obtain ⟨z, hz, hlt⟩ := hfar
      have hlt' : 4 * supDist y z < R.range := by
        have : (4 * (supDist y z : ℝ)) < R.range := by linarith
        exact_mod_cast this
      by_cases hfr : s.free.Nonempty
      · obtain ⟨b₀, hb₀⟩ := hfr
        have haway := hs.far_from_support b₀ hb₀ z (Finset.mem_union_left _ hz)
        have hhalf := supDist_le_half_side b₀.1 z
        have hside : 2 * R.range + 2 < n * R.params.side := by omega
        have hagree : StatesAgreeNear R.params (s.field η) (s.field 0) s.support s.support
            s.labelling s.labelling y y R.range := by
          refine ⟨hside, hside, ?_, fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
          intro b hb
          have hnf : (y + siteOfInt b.1, b.2) ∉ s.free := by
            intro hm
            have h1 := hs.far_from_support _ hm z (Finset.mem_union_left _ hz)
            have h2 : supDist (y + siteOfInt b.1) z ≤ supDist (y + siteOfInt b.1) y + supDist y z :=
              supDist_triangle _ _ _
            have h3 : supDist y (y + siteOfInt b.1) ≤ R.range :=
              supDist_add_siteOfInt_le y b.1 R.range fun i => by
                have := abs_le.mp (hb.1 i)
                omega
            rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h3
            have h4 : 4 * R.range ≤ supDist (y + siteOfInt b.1) z + R.params.side + 1 := h1
            omega
          have e1 : s.field η (y + siteOfInt b.1) b.2 = s.fine (y + siteOfInt b.1) b.2 := dif_neg hnf
          have e2 : s.field 0 (y + siteOfInt b.1) b.2 = s.fine (y + siteOfInt b.1) b.2 := dif_neg hnf
          show s.field η (y + siteOfInt b.1) b.2 = s.field 0 (y + siteOfInt b.1) b.2
          rw [e1, e2]
        have hf := hrow.2.forget (n * R.params.side) (n * R.params.side) hbs hbs _ _ _ _ _ _ y y
          R.range (hs.isHull η hη) (hs.isHull 0 h0)
          (hs.factor_ne_zero η hη) (hs.factor_ne_zero 0 h0)
          (by have : (0 : ℝ) ≤ R.range := Nat.cast_nonneg _
              show (R.range : ℝ) / 64 ≤ R.range
              linarith) hagree
        have hexp : Real.exp (-R.params.decayRate * R.range) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ R.params.decayRate * R.range := mul_nonneg hrt (Nat.cast_nonneg _)
          linarith
        have h5 := abs_sub_abs_le_abs_sub
          (R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling)
          (R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling)
        linarith
      · have hz0 : η = 0 := by
          funext b
          exact absurd ⟨b.1, b.2⟩ hfr
        rw [hz0]
        linarith
  refine ⟨fun Y => ?_, ?_⟩
  · have hG : ∀ y, ∃ G : FreeCoords s.free → ℝ, Measurable G ∧
        ∀ η, s.InBalls η → G η = R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling := by
      intro y
      refine ⟨_, ((hrow.2.borel (n * R.params.side) hbs s.support).2.2 y).comp
        ((ChartSetting.measurable_field s).prodMk (measurable_const (a := s.labelling))), fun η h => ?_⟩
      exact if_pos ⟨hs.isHull η h, hs.factor_ne_zero η h⟩
    choose G hGm hGe using hG
    refine ⟨fun η => ∑ y ∈ sitesInBlocks R.params.side {Y}, G y η,
      Finset.measurable_fun_sum _ fun y _ => hGm y, fun η h => ?_⟩
    exact Finset.sum_congr rfl fun y _ => hGe y η h
  · set MY : TorusSite n → ℝ := fun Y => ∑ y ∈ sitesInBlocks R.params.side {Y},
      (2 * R.params.E + |R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling| + 1)
      with hMY
    have hMYnn : ∀ Y, 0 ≤ MY Y := fun Y => Finset.sum_nonneg fun y _ => by
      have := abs_nonneg (R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling)
      linarith
    refine ⟨∑ Y, MY Y, fun η hη Y => ?_⟩
    calc |s.blockDensityAt Y η| ≤ ∑ y ∈ sitesInBlocks R.params.side {Y},
          |R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ MY Y := Finset.sum_le_sum fun y _ => key y η hη
      _ ≤ ∑ Y, MY Y := Finset.single_le_sum (fun Y _ => hMYnn Y) (Finset.mem_univ Y)
end YangMills.Construction.ClusterExpansionOfAStep
end
