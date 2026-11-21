import YangMills.Construction.ColdStepAtMirrorFrames.BlocksHaveAGrid
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheFrameIsACurvatureFamily
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromASmallDifference
import YangMills.Construction.ColdStepAtMirrorFrames.TwoFramesAtTheFlatTop
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
private def flatLimitConstantFloor (K : ℝ → ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ :=
  flatLimitDifferenceConstant (T.decayRate / 6) * T.energyRatio ^ (1 / 3 : ℝ) *
    (K T.chainParams.δ₂ * (T.L : ℝ) ^ 12 * T.E * (T.Ct + 2) ^ 6 * T.Ct) ^ (2 / 3 : ℝ)
private theorem hasBoundedFlatLimitForm_mono {L t : ℕ} {g : TopLevelFamily} {e e' : ℝ} (h : e ≤ e')
    (hg : HasBoundedFlatLimitForm L t g e) : HasBoundedFlatLimitForm L t g e' := by
  obtain ⟨q, hq, hbound⟩ := hg
  refine ⟨q, hq, fun X μ ν B hX hμν hB => ?_⟩
  obtain ⟨v, hv, hve⟩ := hbound X μ ν B hX hμν hB
  exact ⟨v, hv, hve.trans h⟩
private theorem isSmallCurvature_uniformField {F : BlockFrame} {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
private theorem flatLimitAboveFrame_of_bounds (hgrid : LumpGridExists)
    (hstar : flatLimitAtMinimizerStatement) (hdens : expansionAtFrameIsLocalDensityStatement)
    (hfam : expansionAtFrameIsCurvatureFamily) (hdiff : flatLimitFromSmallDifference) {K : ℝ → ℝ}
    (hK0 : ∀ r, 0 ≤ K r)
    (hK : ∀ (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (Cf Cw : ℝ), T.IsOrdered → 64 ≤ T.n₀ → 0 < Cf → 0 ≤ Cw → Cw * T.σ ≤ 1 →
      ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x → 16 ≤ frameRadius x →
        IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
        (∀ n : ℕ, T.n₀ ≤ n → FramesAtUniformTop T Cf Cw (frameRadius x) t (cubicTorusFrame T.L t n)) →
        ∀ (b b' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
          ∀ᶠ n in Filter.atTop,
          |secondDerivAtUniform (expansionAtFrameFamily T false x f) T.L t n b b' X X' -
            secondDerivAtUniform (expansionAtFrameFamily T true x f) T.L t n b b' X X'| ≤
              twoFramesGapBound K T Cf Cw (frameRadius x))
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hd : T.IsOrdered) (hL : 2 ^ 16 ≤ T.L) (hn₀ : 4096 ≤ T.n₀)
    (hm : ∀ x, T.coupling ≤ x → 16 ≤ frameRadius x) (htr : expansionTransportAt T) (Cf C : ℝ) (hCf : 0 < Cf)
    (hC1 : 1 ≤ C) (hCle : Cf ≤ T.Ct) (hC2 : C ≤ T.Ct) (hCσ : C * T.σ ≤ 1)
    (hall : ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
        FrameBoundsAt T.a T.L T.chainParams Cf C T.σ T.κ x (frameRadius x) t T.n₀ F V)
    (hfloor : flatLimitConstantFloor K T ≤ T.CE) : FlatLimitAboveFrame T := by
  intro t x f hx hrow
  have hσ : 0 < T.σ := hd.σ_pos
  have hden : ExpansionAtFrameIsLocalDensityAt T := hdens T hd (by omega) htr
    (fun t x F V star hx hF hV => ⟨C, (hall t x F V hx hF hV).2.1 star⟩)
  have hs := hstar T hd hL hn₀ htr hden t x f hx hrow
  refine ⟨hs, ?_⟩
  obtain ⟨g⟩ := hgrid T.L hL
  have hLpos : 0 < T.L := by omega
  haveI : NeZero T.L := ⟨hLpos.ne'⟩
  obtain ⟨hfits, hfam'⟩ := hfam T g hd hL hn₀
  have hcf₁ := hfam' htr false t x f hx hrow (hden t x f false hx hrow)
  have hcf₀ := hfam' htr true t x f hx hrow (hden t x f true hx hrow)
  have hE : 0 < T.E := by linarith [hd.one_le_E]
  have hE₃ : 0 < T.energyRatio := by
    show 0 < T.E / T.η₃
    exact div_pos hE hd.η₃_pos
  have hC0 : 0 ≤ C := by linarith
  set m := frameRadius x with hmdef
  have hT : ∀ n : ℕ, T.n₀ ≤ n → IsCubicTopTorus T.L t T.n₀ (cubicTorusFrame T.L t n) :=
    fun n hn => ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  have hflatH : ∀ n : ℕ, T.n₀ ≤ n → FramesAtUniformTop T Cf C m t (cubicTorusFrame T.L t n) := by
    intro n hn
    have h := hall t x (cubicTorusFrame T.L t n) _ hx (hT n hn) (isSmallCurvature_uniformField (by positivity))
    exact ⟨h.1, h.2.1⟩
  have hgap := hK T Cf C hd (by omega) hCf hC0 hCσ t x f hx (hm x hx) hrow hflatH
  have hsm : ∀ (o : Bool) (n : ℕ), T.n₀ ≤ n →
      ContDiffThreeAlongBonds (expansionAtFrameFamily T o x f (TorusFields.torusFrame T.L t n) 0)
        (uniformField _ _) := by
    intro o n hn
    exact (hden t x f o hx hrow).smooth _ (hT n hn) 0 _ (isSmallCurvature_uniformField (by positivity))
  set w := twoFramesGapBound K T Cf C m with hw
  have hw0 : 0 ≤ w := by
    rw [hw]
    unfold twoFramesGapBound
    have := hK0 T.chainParams.δ₂
    positivity
  have hres := hdiff (torusStepParameters T g) t T.energyRatio w _ _ hfits hE₃.le hw0 hcf₁ hcf₀
    (hsm false) (hsm true) hs hgap
  refine hasBoundedFlatLimitForm_mono ?_ hres
  set A : ℝ := K T.chainParams.δ₂ * (T.L : ℝ) ^ 12 * T.E * (C + 2) ^ 6 * Cf with hA
  set AT : ℝ := K T.chainParams.δ₂ * (T.L : ℝ) ^ 12 * T.E * (T.Ct + 2) ^ 6 * T.Ct with hAT
  have hk := hK0 T.chainParams.δ₂
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  have hAA : A ≤ AT := by
    have h1 : (C + 2) ^ 6 ≤ (T.Ct + 2) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    have hb : 0 ≤ K T.chainParams.δ₂ * (T.L : ℝ) ^ 12 * T.E := by positivity
    rw [hA, hAT]
    have h2 := mul_le_mul h1 hCle hCf.le (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hb
    nlinarith
  have hwA : w = A * Real.exp (-(3 / 8 * T.chainParams.δ₂ * m)) := by
    rw [hw]
    rfl
  have hw23 : w ^ (2 / 3 : ℝ) = A ^ (2 / 3 : ℝ) * Real.exp (-(T.chainParams.δ₂ / 4 * m)) := by
    rw [hwA, Real.mul_rpow hA0 (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  have hdn : 0 ≤ flatLimitDifferenceConstant (T.decayRate / 6) := by
    unfold flatLimitDifferenceConstant
    positivity
  have hrate : (torusStepParameters T g).weightRate / 6 = T.decayRate / 6 := rfl
  rw [hrate, hw23]
  have hApow : A ^ (2 / 3 : ℝ) ≤ AT ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hA0 hAA (by norm_num)
  have hexp := Real.exp_pos (-(T.chainParams.δ₂ / 4 * m))
  have hfl : flatLimitDifferenceConstant (T.decayRate / 6) * T.energyRatio ^ (1 / 3 : ℝ) *
      A ^ (2 / 3 : ℝ) ≤ T.CE :=
    le_trans (mul_le_mul_of_nonneg_left hApow (by positivity)) hfloor
  calc flatLimitDifferenceConstant (T.decayRate / 6) * T.energyRatio ^ (1 / 3 : ℝ) *
        (A ^ (2 / 3 : ℝ) * Real.exp (-(T.chainParams.δ₂ / 4 * m)))
      = (flatLimitDifferenceConstant (T.decayRate / 6) * T.energyRatio ^ (1 / 3 : ℝ) * A ^ (2 / 3 : ℝ)) *
          Real.exp (-(T.chainParams.δ₂ / 4 * m)) := by ring
    _ ≤ T.CE * Real.exp (-(T.chainParams.δ₂ / 4 * m)) := mul_le_mul_of_nonneg_right hfl hexp.le
private theorem sixteen_le_frameRadius (x : ℝ) (hx : ((2 : ℝ) ^ 15) ^ 100 ≤ x) : 16 ≤ frameRadius x := by
  unfold frameRadius
  have h1 : (((2 : ℝ) ^ 15) ^ 100) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ 15 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h2 : (2 : ℝ) ^ 15 ≤ x ^ ((1 : ℝ) / 100) := by
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h3 : 2 ^ 15 ≤ ⌈x ^ ((1 : ℝ) / 100)⌉₊ := by
    have h4 := (h2.trans (Nat.le_ceil (x ^ ((1 : ℝ) / 100))))
    exact_mod_cast h4
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  norm_num at h3 ⊢
  exact h3
private theorem eventually_large_side_index_radius :
    EventuallyInParameters fun T => 2 ^ 16 ≤ T.L ∧ 4096 ≤ T.n₀ ∧
      ∀ x, T.coupling ≤ x → 16 ≤ frameRadius x := by
  intro a _
  refine ⟨2 ^ 16, fun L _ hL c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨4096, fun n₀ hn => ⟨0, fun CE _ =>
      ⟨((2 : ℝ) ^ 15) ^ 100, fun y₁ hy => ⟨hL, hn, fun x hx => sixteen_le_frameRadius x (hy.trans hx)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem flatLimitAboveFrameStatement_holds (hjoin : EventuallyInParametersCombines)
    (hraise : SummableBounds.joinAtLoweredConstantsStatement) (htr : expansionTransportStatement)
    (hfr : FrameBoundsEventually) (hgrid : LumpGridExists) (hstar : flatLimitAtMinimizerStatement)
    (hdens : expansionAtFrameIsLocalDensityStatement) (hfam : expansionAtFrameIsCurvatureFamily)
    (hdiff : flatLimitFromSmallDifference) (htwo : twoFramesAtUniformTopStatement) :
    flatLimitAboveFrameStatement := by
  obtain ⟨K, hK0, hK⟩ := htwo
  have hP : EventuallyInParameters fun T => T.IsOrdered ∧ expansionTransportAt T ∧ FrameBoundsForParameters T :=
    hjoin.2 (fun T => expansionTransportAt T ∧ FrameBoundsForParameters T) _ (fun T hd h => ⟨hd, h.1, h.2⟩)
      (hjoin.1 _ _ htr hfr)
  refine hraise _ _ FlatLimitAboveFrame (fun _ => 0) (flatLimitConstantFloor K) hP
    eventually_large_side_index_radius ?_
  intro T c c' _ _ _ _ _ _ _ _ hfloor hP' hR'
  obtain ⟨h1, h2, h3⟩ := hP'
  obtain ⟨r1, r2, r3⟩ := hR'
  have hd : T.IsOrdered := ⟨h1.one_le_a, h1.odd_L, h1.chain_admissible, h1.κ_pos, h1.η₃_pos, h1.η₃_le_one,
    h1.σ_pos, h1.cutoff, h1.one_le_E⟩
  obtain ⟨Cf, C, hCf, hC1, hle₁, hle₂, _, _, _, _, hb₁, _, _, _, _, hall⟩ := h3
  have hL1 : (1 : ℝ) ≤ (T.L : ℝ) := by exact_mod_cast hd.odd_L.pos
  have hσ : 0 < T.σ := hd.σ_pos
  have hCσ : C * T.σ ≤ 1 := by
    have h4 : 1 / (64 * (T.L : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h5 := hb₁.trans h4
    have h6 : 0 < T.σ / 64 := by positivity
    linarith
  exact flatLimitAboveFrame_of_bounds hgrid hstar hdens hfam hdiff hK0 hK T hd r1 r2 r3 h2 Cf C hCf hC1
    hle₁ hle₂ hCσ hall hfloor
end YangMills.Construction.ColdStepAtMirrorFrames
end
