import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.OscillationOfTheStateDensities
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TwoActionsAlongMovesForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepSettings BlockOffsets
private theorem supDist_le_half {N : ℕ} [NeZero N] (x y : TorusSite N) : supDist x y ≤ N / 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card <;> assumption
theorem blockDensityOscillationBound_of_expansionBasicBounds (h3 : ExpansionBasicBounds) :
    BlockDensityOscillationBound := by
  intro R n _ s hfit hE hx hr hLr hrow hn hs Y η₁ η₂ hη₁ hη₂
  classical
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  obtain ⟨_, facts2, _⟩ := h3 R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity hfit hE hx hr hrow.1 hrow.2
  have hrt : 0 ≤ R.params.decayRate := by
    have := hfit.rt_pos
    unfold TorusLumps.StepParameters.decayRate
    positivity
  have key : ∀ (y : TorusSite (n * R.params.side)) (η η' : FreeCoords s.free), s.InBalls η → s.InBalls η' →
      |R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling -
          R.siteDensity (n * R.params.side) y (s.field η') s.support s.labelling| ≤
        4 * R.params.E + 2 := by
    intro y η η' hη hη'
    have hEpos : 0 ≤ R.params.E := by linarith
    by_cases hfar : ∀ z ∈ s.support, (R.range : ℝ) / 4 ≤ supDist y z
    · have h1 := facts2 (n * R.params.side) hbs (s.field η) s.support s.labelling y (hs.isHull η hη)
        (hs.factor_ne_zero η hη) hfar
      have h2 := facts2 (n * R.params.side) hbs (s.field η') s.support s.labelling y (hs.isHull η' hη')
        (hs.factor_ne_zero η' hη') hfar
      have h3 := abs_sub (R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling)
        (R.siteDensity (n * R.params.side) y (s.field η') s.support s.labelling)
      linarith
    · push_neg at hfar
      obtain ⟨z, hz, hlt⟩ := hfar
      have hlt' : 4 * supDist y z < R.range := by
        have : (4 * (supDist y z : ℝ)) < R.range := by linarith
        exact_mod_cast this
      by_cases hfr : s.free.Nonempty
      · obtain ⟨b₀, hb₀⟩ := hfr
        have haway := hs.far_from_support b₀ hb₀ z (Finset.mem_union_left _ hz)
        have hhalf := supDist_le_half b₀.1 z
        have hside : 2 * R.range + 2 < n * R.params.side := by omega
        have hagree : StatesAgreeNear R.params (s.field η) (s.field η') s.support s.support s.labelling
            s.labelling y y R.range := by
          refine ⟨hside, hside, ?_, fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
          intro b hb
          have hnf : (y + siteOfInt b.1, b.2) ∉ s.free := by
            intro hm
            have h1 := hs.far_from_support _ hm z (Finset.mem_union_left _ hz)
            have h2 : supDist (y + siteOfInt b.1) z ≤ supDist (y + siteOfInt b.1) y + supDist y z :=
              supDist_triangle _ _ _
            have h3 : supDist y (y + siteOfInt b.1) ≤ R.range := supDist_add_siteOfInt_le y b.1 R.range fun i => by
              have := abs_le.mp (hb.1 i)
              omega
            rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h3
            have h4 : 4 * R.range ≤ supDist (y + siteOfInt b.1) z + R.params.side + 1 := h1
            omega
          have e1 : s.field η (y + siteOfInt b.1) b.2 = s.fine (y + siteOfInt b.1) b.2 := dif_neg hnf
          have e2 : s.field η' (y + siteOfInt b.1) b.2 = s.fine (y + siteOfInt b.1) b.2 := dif_neg hnf
          show s.field η (y + siteOfInt b.1) b.2 = s.field η' (y + siteOfInt b.1) b.2
          rw [e1, e2]
        have hf := hrow.2.forget (n * R.params.side) (n * R.params.side) hbs hbs _ _ _ _ _ _ y y R.range
          (hs.isHull η hη) (hs.isHull η' hη') (hs.factor_ne_zero η hη) (hs.factor_ne_zero η' hη')
          (by have : (0 : ℝ) ≤ R.range := Nat.cast_nonneg _
              show (R.range : ℝ) / 64 ≤ R.range
              linarith) hagree
        have hexp : Real.exp (-R.params.decayRate * R.range) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ R.params.decayRate * R.range := mul_nonneg hrt (Nat.cast_nonneg _)
          linarith
        linarith
      · have hz0 : η = η' := by
          funext b
          exact absurd ⟨b.1, b.2⟩ hfr
        rw [hz0, sub_self, abs_zero]
        linarith
  have hodd := hfit.L_odd
  have hs₁ : ∀ (ζ : FreeCoords s.free), s.blockDensityAt Y ζ =
      ∑ o ∈ centredCube R.params.side,
        R.siteDensity (n * R.params.side) (fineSite R.params.side Y 0 o) (s.field ζ) s.support s.labelling :=
    fun ζ => sum_sitesInBlocks hodd Y _
  rw [hs₁, hs₁, ← Finset.sum_sub_distrib]
  calc |∑ o ∈ centredCube R.params.side, _| ≤ ∑ o ∈ centredCube R.params.side, _ :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _o ∈ centredCube R.params.side, (4 * R.params.E + 2) :=
        Finset.sum_le_sum fun o _ => key _ η₁ η₂ hη₁ hη₂
    _ = (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) := by
      rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul]
      push_cast
      ring
end YangMills.Construction.ClusterExpansionOfAStep
end
