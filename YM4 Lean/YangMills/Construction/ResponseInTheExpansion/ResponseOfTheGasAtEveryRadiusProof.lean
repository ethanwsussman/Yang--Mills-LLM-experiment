import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.GasesEqualInBoxes
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGasAtEveryRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters BlockOffsets BlockAverages WeightedResponses StepFloors
private theorem siteOffset_fineSite {L n : ℕ} [NeZero L] [NeZero n] (Y : TorusSite n) (h o : Fin 4 → ℤ) :
    siteOffset (fineSite L Y h o : TorusSite (n * L)) =
      fun i => Fin.ofNat L (((o i + ((L : ℤ) - 1) / 2) % (L : ℤ)).toNat) := by apply _root_.YangMills.Construction.BoxAgreement.siteOffset_fineSite <;> assumption
private theorem recordedSiteScore_eq {R : StepSetup} {n : ℕ} [NeZero n] (A : ResponseSetup R) (G : GasGround R n)
    (y : TorusSite (n * R.params.side)) :
    recordedSiteScore A G y = Sum.elim (fun _ => 0) A.score (G.state.labelAt y) := by
  classical
  unfold recordedSiteScore siteScore
  rcases hl : G.state.labelAt y with u | w
  · have hy : y ∉ G.recordedSites := by
      simp [GasGround.recordedSites, hl]
    simp [hy]
  · have hy : y ∈ G.recordedSites := by
      simp [GasGround.recordedSites, hl]
    have key : ∀ (x : WithNone R.labels.Ω) (hx : x.isRight = true), x = Sum.inr w → x.getRight hx = w := by
      rintro _ _ rfl
      rfl
    simp only [hy, dif_pos, Sum.elim_inr]
    exact congrArg A.score (key _ _ hl)
private theorem recordedSiteScore_agree {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
    (hodd : Odd R.params.side) (A : ResponseSetup R) {G : GasGround R n} {G' : GasGround R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m : ℕ}
    (hag : GroundsAgreeNear G G' Y Y' m) {o : Fin 4 → ℤ} (ho : o ∈ centredCube R.params.side) :
    recordedSiteScore A G (fineSite R.params.side Y 0 o) =
      recordedSiteScore A G' (fineSite R.params.side Y' 0 o) := by
  have hlabel : G.state.labelAt (fineSite R.params.side Y 0 o) =
      G'.state.labelAt (fineSite R.params.side Y' 0 o) := by
    unfold CoarseState.labelAt
    rw [parentBlock_fineSite hodd Y 0 o ho, parentBlock_fineSite hodd Y' 0 o ho,
      hag.marking_eq 0 (fun i => by simp), siteOffset_fineSite, siteOffset_fineSite]
  rw [recordedSiteScore_eq, recordedSiteScore_eq, hlabel]
private theorem recordedSiteScore_nonneg {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R}
    (hA : A.IsAdmissible) (G : GasGround R n) (y : TorusSite (n * R.params.side)) :
    0 ≤ recordedSiteScore A G y := by
  rw [recordedSiteScore_eq]
  rcases G.state.labelAt y with u | w
  · simp
  · exact hA.price.nonneg w
private theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
private theorem abs_sub_le_of_abs_le_bounds {a b S e E u v : ℝ} (hS : 0 ≤ S) (he : 0 ≤ e) (heE : e ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : |a| ≤ S * e * u) (hb : |b| ≤ S * e * v) :
    |a - b| ≤ 2 * S * E * max u v := by
  have hE : 0 ≤ S * E := mul_nonneg hS (he.trans heE)
  have hse : S * e ≤ S * E := mul_le_mul_of_nonneg_left heE hS
  have h1 : S * e * u ≤ S * E * max u v := mul_le_mul hse (le_max_left _ _) hu hE
  have h2 : S * e * v ≤ S * E * max u v := mul_le_mul hse (le_max_right _ _) hv hE
  obtain ⟨a1, a2⟩ := abs_le.mp ha
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith
theorem gasResponseComparisonAllRadii_of_bounds (hGas : GasResponseBounds)
    (hFl : EventuallyFloorConditions) : GasResponseComparisonAllRadii := by
  obtain ⟨r₀, hr₀, h₀⟩ := hGas
  refine ⟨r₀, hr₀, fun T hT hle K => ?_⟩
  obtain ⟨y₁, hy₁⟩ := h₀ T hT hle K
  obtain ⟨y₄, hy₄⟩ := hFl T hT 1 1 one_pos one_pos
  refine ⟨max y₁ y₄, fun y hy R A hK hA n n' _ _ G G' Y Y' m hG hG' hag hm => ?_⟩
  obtain ⟨hP1, hP2⟩ := hy₁ y ((le_max_left _ _).trans hy) R A hK hA
  have hfl := (hy₄ R.coupling (((le_max_right _ _).trans hy).trans hA.onFamily.le_coupling)).gas_powers
  have hodd : Odd R.params.side := by
    have e : R.params.side = T.side := congrArg StepParameters.side hA.onFamily.params_eq
    exact e ▸ hT.L_odd
  have hrt : R.params.rt = T.rt := congrArg StepParameters.rt hA.onFamily.params_eq
  have hrt0 : 0 < T.rt := hT.rt_pos
  have hfr : 16 * T.rt * (R.frameReach : ℝ) + 16 * T.rt ≤ R.coupling ^ (1 / 90 : ℝ) := hfl.1
  have hxc : R.coupling ^ (1 / 90 : ℝ) ≤ T.gasRate * R.coupling := hfl.2.1
  have hm0 : (0 : ℝ) ≤ (R.frameReach : ℝ) := Nat.cast_nonneg _
  have hcx : 16 * T.rt * (R.frameReach : ℝ) ≤ T.gasRate * R.coupling := by nlinarith
  have hcx0 : 0 ≤ T.gasRate * R.coupling := le_trans (by positivity) hcx
  set E := Real.exp (-(T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8) with hE
  have hE0 : 0 < E := Real.exp_pos _
  by_cases hbig : 16 * R.frameReach ≤ m
  · obtain ⟨hresp, hscore⟩ := hP2 n n' G G' Y Y' m hG hG' hag hbig
    have hEE : Real.exp (-(2 * T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8) ≤ E :=
      Real.exp_le_exp.mpr (by nlinarith)
    refine ⟨fun o ho h h' hw => ?_, fun c hc => ?_⟩
    · have hb := hresp o ho h h' hw
      have hS : 0 ≤ 1 + recordedSiteScore A G (fineSite R.params.side Y 0 o) :=
        add_nonneg zero_le_one (recordedSiteScore_nonneg hA.admissible G _)
      have hu := weightNorm_nonneg R.params.side R.depth h
      have hM : weightNorm R.params.side R.depth h ≤
          max (weightNorm R.params.side R.depth h) (weightNorm R.params.side R.depth h') := le_max_left _ _
      have h1 : (1 + recordedSiteScore A G (fineSite R.params.side Y 0 o)) *
            Real.exp (-(2 * T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8) *
              weightNorm R.params.side R.depth h ≤
          (1 + recordedSiteScore A G (fineSite R.params.side Y 0 o)) * E *
            max (weightNorm R.params.side R.depth h) (weightNorm R.params.side R.depth h') :=
        mul_le_mul (mul_le_mul_of_nonneg_left hEE hS) hM hu (mul_nonneg hS hE0.le)
      have h2 : 0 ≤ (1 + recordedSiteScore A G (fineSite R.params.side Y 0 o)) * E *
          max (weightNorm R.params.side R.depth h) (weightNorm R.params.side R.depth h') :=
        mul_nonneg (mul_nonneg hS hE0.le) (hu.trans hM)
      linarith
    · have := hscore c hc
      linarith
  · have hmm : (m : ℝ) ≤ 16 * (R.frameReach : ℝ) := by exact_mod_cast (not_le.mp hbig).le
    have he : Real.exp (-(6 * T.gasRate * R.coupling)) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      rw [hrt]
      have h5 : T.rt * m ≤ 16 * T.rt * (R.frameReach : ℝ) := by nlinarith
      nlinarith
    have he0 : 0 ≤ Real.exp (-(6 * T.gasRate * R.coupling)) := (Real.exp_pos _).le
    refine ⟨fun o ho h h' _ => ?_, fun c _ => ?_⟩
    · have hs := recordedSiteScore_agree hodd A hag ho
      have hS : 0 ≤ 1 + recordedSiteScore A G (fineSite R.params.side Y 0 o) :=
        add_nonneg zero_le_one (recordedSiteScore_nonneg hA.admissible G _)
      have b₁ := ((hP1 n G hG).1 (fineSite R.params.side Y 0 o) h).1
      have b₂ := ((hP1 n' G' hG').1 (fineSite R.params.side Y' 0 o) h').1
      rw [← hs] at b₂
      exact abs_sub_le_of_abs_le_bounds hS he0 he (weightNorm_nonneg _ _ _) (weightNorm_nonneg _ _ _) b₁ b₂
    · have b₁ := ((hP1 n G hG).2 (bondFrom Y c)).1
      have b₂ := ((hP1 n' G' hG').2 (bondFrom Y' c)).1
      obtain ⟨a1, a2⟩ := abs_le.mp b₁
      obtain ⟨c1, c2⟩ := abs_le.mp b₂
      rw [abs_le]
      constructor <;> linarith
end YangMills.Construction.ResponseInTheExpansion
end
