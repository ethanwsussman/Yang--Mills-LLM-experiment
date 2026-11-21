import YangMills.Construction.LawByMomentsOfTheFlow.CarriedCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionAtTheWeightsOfThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps RenormalizationStepParameters
private theorem forAllParameters_and {P P' : MomentParameters → Prop} (h : ForAllParameters P)
    (h' : ForAllParameters P') : ForAllParameters fun Λ => P Λ ∧ P' Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {P P' : MomentParameters → Prop} (h : ForAllParameters P)
    (f : ∀ Λ, P Λ → P' Λ) : ForAllParameters P' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_contraction (h : responseContractionStatement) :
    ForAllParameters fun Λ => 4 ≤ Λ.stepParams.side ∧ 0 < Λ.stepParams.weightRate ∧ ∃ θ : ℝ, 0 ≤ θ ∧
    ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
      ∀ (ω : TorusPlaquette (n * Λ.stepParams.side) → ℝ) (ω' : TorusPlaquette n → ℝ), (∀ p, 0 < ω p) → (∀ p, 0 < ω' p) →
      IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8) ω ω' →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal), 1 ≤ q → Measurable X →
        weightedCurvatureNorm μ ω q (fun e => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u (X e)) ≤
          ENNReal.ofReal θ * weightedCurvatureNorm μ ω' q X := by
  intro a ha
  obtain ⟨Cw, hCw, L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨max L₀ 4, rt₀, C₀, hrt, ?_⟩
  intro L hL hLL Tb ha' hLT hD hCs hO hrtT hCd Kr hKr
  obtain ⟨-, y₀, Hy⟩ := H L hL (le_trans (le_max_left _ _) hLL) Tb ha' hLT hD hCs hO hrtT hCd
  refine ⟨y₀, fun y hy hret hwil g hg hgy k _ hk2 hk8 R d hd =>
    ⟨?_, ?_, Cw * (L : ℝ) ^ (-(1 / 2) : ℝ), by positivity, ?_⟩⟩
  · show 4 ≤ (Tb.stepParameters y).side
    have e : (Tb.stepParameters y).side = Tb.side := rfl
    rw [e, hLT]
    exact le_trans (le_max_right _ _) hLL
  · have := hD.rt_pos
    show 0 < (Tb.stepParameters y).rt / 2 ^ 10
    have e : (Tb.stepParameters y).rt = Tb.rt := rfl
    rw [e]
    positivity
  · intro u n _ hn ω ω' h1 h2 hs Ω _ μ X q hq hX
    exact Hy y hy hret hwil u n hn ω ω' h1 h2 hs Ω μ X q hq hX
private theorem eLpNorm_dirac_const (c : ℝ) :
    eLpNorm (fun _ : Unit => c) ⊤ (Measure.dirac ()) = ENNReal.ofReal |c| := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_const _ (by simp), Real.enorm_eq_ofReal_abs]
theorem carriedCutCurvature (hR : responseContractionStatement) (hA : weightContractionStatement)
    (hN : scaleWindowStatement) (hC : goodConfigCutoffStatement) : carriedCutCurvatureStatement := by
  unfold weightContractionStatement scaleWindowStatement goodConfigCutoffStatement ForAllPoints at *
  unfold carriedCutCurvatureStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and (forAllParameters_contraction hR)
    (forAllParameters_and hA (forAllParameters_and hN hC))) ?_
  rintro Λ ⟨⟨hL4, hrate, θ, hθ, hcon⟩, ⟨_, _, _, _, _, ha⟩, ⟨Cn, _, Xn, _, _, hn⟩, ⟨_, _, Xc, _, _, hc⟩⟩
  refine ⟨fun _ => θ * 60, 1, max Xn (max Xc Λ.floor), one_pos, le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro S hx d n _ hd hn' V Y hg pp
  have hxn : Xn ≤ S.scaleCoupling := le_trans (le_max_left _ _) hx
  have hxc : Xc ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, h3, -, -, hK, hwin⟩ := hn S hxn
  have h64 : 64 ≤ n := by
    have h1 := (hwin (S.lastSeparated + d + 1) (by omega) (by omega)).2
    rw [← hn'] at h1
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ Λ.stepParams.side ^ 3 := Nat.pow_le_pow_left hL4 3
      _ ≤ Λ.stepParams.side ^ S.logIndex := Nat.pow_le_pow_right (by omega) h3
      _ ≤ n := h1
  obtain ⟨-, h60, -, -⟩ := hc S hxc (S.lastSeparated + d + 1) (by omega) (by omega) n hn' V Y hg
  obtain ⟨-, -, hslow, -⟩ := ha S
  have hv0 : 0 ≤ S.localCurvature (S.lastSeparated + d + 1) n V := by
    unfold MomentPoint.localCurvature boxCurvature
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  have hω1 : ∀ p : TorusPlaquette n, S.distanceWeight (S.lastSeparated + d + 1) n p ≤ 1 := fun p => by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ Λ.stepParams.weightRate / 8 *
        max 0 ((TorusFields.supDist p.1 (S.originSite (S.lastSeparated + d + 1) n) : ℝ) - (S.radius : ℝ)) :=
      mul_nonneg (div_nonneg hrate.le (by norm_num)) (le_max_left _ _)
    linarith
  have hcs : ∀ {m : ℕ} (X : ColourForm m) (p : TorusPlaquette m), 0 ≤ curlNorm X p :=
    fun _ _ => Real.sqrt_nonneg _
  have hmain := hcon (S.lastSeparated + d) n h64 (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side))
    (S.distanceWeight (S.lastSeparated + d + 1) n) (fun p => Real.exp_pos _)
    (fun p => Real.exp_pos _) (hslow (S.lastSeparated + d) n) Unit (Measure.dirac ())
    (fun _ => S.cutoffColourForm (S.lastSeparated + d + 1) n V) ⊤ le_top measurable_const
  have h1 : ENNReal.ofReal (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) pp.1 *
      curlNorm (fun e b => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
      (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b) pp.1) ≤
        weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) ⊤
        (fun _ : Unit => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
          (S.cutoffColourForm (S.lastSeparated + d + 1) n V)) := by
    refine le_trans (le_of_eq ?_) (le_iSup _ pp)
    rw [eLpNorm_dirac_const, abs_of_nonneg (hcs _ _), ENNReal.ofReal_mul
      (show 0 ≤ S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) pp.1 from (Real.exp_pos _).le)]
  have h2 : weightedCurvatureNorm (Measure.dirac ()) (S.distanceWeight (S.lastSeparated + d + 1) n) ⊤
      (fun _ : Unit => S.cutoffColourForm (S.lastSeparated + d + 1) n V) ≤
      ENNReal.ofReal (60 * S.localCurvature (S.lastSeparated + d + 1) n V) := by
    refine iSup_le fun p => ?_
    rw [eLpNorm_dirac_const, abs_of_nonneg (hcs _ _), ← ENNReal.ofReal_mul
      (show 0 ≤ S.distanceWeight (S.lastSeparated + d + 1) n p.1 from (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact le_trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) (hω1 p.1)) (h60 p)
  have h3' := le_trans h1 (le_trans hmain (mul_le_mul' le_rfl h2))
  rw [← ENNReal.ofReal_mul hθ] at h3'
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3'
  show _ ≤ θ * 60 * _
  linarith
end YangMills.Construction.MomentLaw
end
