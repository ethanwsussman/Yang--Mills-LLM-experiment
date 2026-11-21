import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAgreeingGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.GasBlocksForget
import YangMills.Construction.ResponseInTheExpansion.ResponseInTwoSettings
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGas
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoTori
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas RenormalizationStepParameters TorusFields TorusLumps BlockOffsets WeightedResponses
open BlockAverages hiding unitStep
section
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem gasFamily_sites_empty : (GasFamily.empty : GasFamily R n).sites = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.sites_empty <;> assumption
private theorem chartSiteScore_groundSetting (A : ResponseSetup R) (G : GasGround R n)
    (x : TorusSite (n * R.params.side)) :
    chartSiteScore A G.groundSetting x = recordedSiteScore A G x := by
  classical
  unfold chartSiteScore recordedSiteScore siteScore
  have hempty := gasFamily_sites_empty (R := R) (n := n)
  by_cases hx : x ∈ G.recordedSites
  · have hx' : x ∈ G.groundSetting.support := Finset.mem_union_left _ hx
    have hnot : x ∉ (GasFamily.empty : GasFamily R n).sites := by
      rw [hempty]
      simp
    rw [dif_pos hx', dif_pos hx]
    congr 1
    show (G.settingWithFamily GasFamily.empty).labelling ⟨x, hx'⟩ = _
    unfold GasGround.settingWithFamily
    simp only [dif_neg hnot]
  · have hx' : x ∉ G.groundSetting.support := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · exact hx hmem
      · rw [hempty] at hmem
        simp at hmem
    rw [dif_neg hx', dif_neg hx]
omit [NeZero n] in
private theorem torusBond_eq_bondFrom_zero (X : TorusSite n) (i : Fin 4) :
    ((X, i) : TorusBond n) = bondFrom X (0, i) := by
  have hzero : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
    funext l
    simp [siteOfInt]
  simp [bondFrom, hzero]
omit [NeZero n] in
private theorem torusBond_eq_bondFrom_neg_single (X : TorusSite n) (i : Fin 4) :
    ((X - unitStep n i, i) : TorusBond n) = bondFrom X (-Pi.single i 1, i) := by
  have hneg : (siteOfInt (-Pi.single i 1 : Fin 4 → ℤ) : TorusSite n) = - unitStep n i := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [siteOfInt, unitStep]
    · simp [siteOfInt, unitStep, hl]
  simp [bondFrom, hneg, sub_eq_add_neg]
end
theorem gasBlockMeanDecorrelation (hGas : GasResponseBounds) (hTwo : ChartResponseComparison)
    (hTori : WeightsCompatibleAcrossTori) (hNear : WeightsCloseToBlockMeans)
    (hAgree : SettingsAgreeOfGroundsAgree) (hCoarse : coarseStateGasStatement) :
    gasBlockMeanDecorrelationStatement := by
  obtain ⟨r₁, p₁, g₁⟩ := hGas
  obtain ⟨r₂, p₂, g₂⟩ := hTwo
  obtain ⟨r₃, p₃, g₃⟩ := hCoarse
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hD hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hD (hrt.trans (min_le_left _ _)) K
  obtain ⟨y₂, G₂⟩ := g₂ T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₃, G₃⟩ := g₃ T hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨max (max y₁ y₂) (max y₃ (max T.floorMin (200 * T.B))), fun y hy R A hK hAt => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hy3 : y₃ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy4 : T.floorMin ≤ y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hy5 : 200 * T.B ≤ y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hR := hAt.onFamily
  have hadm : R.params.Admissible := hR.params_eq ▸ hD.fits y hy4
  have hodd := hadm.L_odd
  have hnext : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    have h2 := hR.le_coupling
    linarith
  obtain ⟨c₀, d₀⟩ := G₁ y hy1 R A hK hAt
  obtain ⟨e₀, f₀⟩ := G₂ y hy2 R A hK hAt
  intro n n' _ _ G G' X X' m h h' hG hG' hag hm hw
  have hfn := hadm.n₀_ge
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have extentOf : ∀ (N : ℕ) [NeZero N] (H : GasGround R N), H.IsAdmissibleGround → R.params.n₀ ≤ N := by
    intro N _ H hH
    rcases hH with h₁ | h₁
    · exact h₁.n₀_le
    · have h2 := h₁.isBlockSide.2
      nlinarith
  have hn := extentOf n G hG
  have hn' := extentOf n' G' hG'
  have hs : G.groundSetting.IsAdmissible :=
    (G₃ y hy3 R hR hnext n G hG).1
  have hs' : G'.groundSetting.IsAdmissible :=
    (G₃ y hy3 R hR hnext n' G' hG').1
  have hoff := hAgree R n n' G G' X X' m hodd (by omega) (by omega) hag
  obtain ⟨c₁, c₂⟩ := d₀ n n' G G' X X' m hG hG' hag hm
  obtain ⟨-, d⟩ := f₀ n n' G.groundSetting G'.groundSetting X X' m hn hn' hs hs'
  obtain ⟨d₁, d₂⟩ := d hoff hm
  obtain ⟨w₁, w₂, w₃⟩ := hTori R.params.side hodd R.depth n n'
  obtain ⟨w₄, w₅, -⟩ := hTori R.params.side hodd (R.depth + 1) n n'
  have hmean : blockMean R.params.side (R.depth + 1) n X h = blockMean R.params.side (R.depth + 1) n' X' h' :=
    w₅ X X' h h' hw
  set S := weightNorm R.params.side R.depth h with hS
  have hS0 : 0 ≤ S := le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  set E₁ := Real.exp (-(15 / 16 * R.params.rt * m / 2 ^ 5)) with hE₁
  set E₂ := Real.exp (-(2 * T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8) with hE₂
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  have hE₂0 : 0 < E₂ := Real.exp_pos _
  have hrec0 : ∀ z, 0 ≤ recordedSiteScore A G z := by
    intro z
    classical
    unfold recordedSiteScore siteScore
    split_ifs
    · exact hAt.admissible.price.nonneg _
    · exact le_rfl
  have site : ∀ o ∈ centredCube R.params.side,
      |G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) (fineSite R.params.side X 0 o) h) -
          G'.expectation ∅ (fun σ => chartResponse A (configSetting G' σ) (fineSite R.params.side X' 0 o) h')| ≤
        (1 + recordedSiteScore A G (fineSite R.params.side X 0 o)) * (E₁ + E₂) * S := by
    intro o ho
    have hwo := w₁ X X' h h' hw o ho
    have a1 := c₁ o ho h h' hwo
    have a2 := d₁ o ho h h' hwo
    rw [chartSiteScore_groundSetting] at a2
    unfold gasResponseShift at a1
    have e : G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) (fineSite R.params.side X 0 o) h) -
        G'.expectation ∅ (fun σ => chartResponse A (configSetting G' σ) (fineSite R.params.side X' 0 o) h') =
        (G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) (fineSite R.params.side X 0 o) h) -
            chartResponse A G.groundSetting (fineSite R.params.side X 0 o) h -
          (G'.expectation ∅ (fun σ => chartResponse A (configSetting G' σ) (fineSite R.params.side X' 0 o) h') -
            chartResponse A G'.groundSetting (fineSite R.params.side X' 0 o) h')) +
        (chartResponse A G.groundSetting (fineSite R.params.side X 0 o) h -
          chartResponse A G'.groundSetting (fineSite R.params.side X' 0 o) h') := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have hre : (1 + recordedSiteScore A G (fineSite R.params.side X 0 o)) * (E₁ + E₂) * S =
        (1 + recordedSiteScore A G (fineSite R.params.side X 0 o)) * E₂ * S +
          (1 + recordedSiteScore A G (fineSite R.params.side X 0 o)) * E₁ * S := by ring
    rw [hre]
    exact add_le_add a1 a2
  have bond : ∀ c : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin c →
      |G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (bondFrom X c)) -
          G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (bondFrom X' c))| ≤ E₁ + E₂ := by
    intro c hc
    have a1 := c₂ c hc
    have a2 := d₂ c hc
    unfold gasBondScoreShift at a1
    have e : G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (bondFrom X c)) -
        G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (bondFrom X' c)) =
        (G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (bondFrom X c)) -
            chartBondScore G.groundSetting (bondFrom X c) -
          (G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (bondFrom X' c)) -
            chartBondScore G'.groundSetting (bondFrom X' c))) +
        (chartBondScore G.groundSetting (bondFrom X c) - chartBondScore G'.groundSetting (bondFrom X' c)) := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [add_comm E₁ E₂]
    exact add_le_add a1 a2
  have hcard : (∑ _o ∈ centredCube R.params.side, (1 : ℝ)) = (R.params.side : ℝ) ^ 4 := by
    rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul]
    push_cast
    ring
  have hsum : |∑ o ∈ centredCube R.params.side,
        (G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) (fineSite R.params.side X 0 o) h) -
          G'.expectation ∅ (fun σ => chartResponse A (configSetting G' σ) (fineSite R.params.side X' 0 o) h'))| ≤
      ((R.params.side : ℝ) ^ 4 + ∑ o ∈ centredCube R.params.side,
          recordedSiteScore A G (fineSite R.params.side X 0 o)) * (E₁ + E₂) * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum site).trans (le_of_eq ?_))
    rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib, hcard]
  have hbonds : |∑ i : Fin 4,
        ((G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (X, i)) +
            G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (X - unitStep n i, i))) -
          (G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (X', i)) +
            G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (X' - unitStep n' i, i))))| ≤
      8 * (E₁ + E₂) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        |(G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (X, i)) +
            G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (X - unitStep n i, i))) -
          (G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (X', i)) +
            G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (X' - unitStep n' i, i)))| ≤
          2 * (E₁ + E₂) := by
      intro i _
      have b1 := bond (0, i) (Or.inl rfl)
      have b2 := bond (-Pi.single i 1, i) (Or.inr rfl)
      rw [← torusBond_eq_bondFrom_zero, ← torusBond_eq_bondFrom_zero] at b1
      rw [← torusBond_eq_bondFrom_neg_single, ← torusBond_eq_bondFrom_neg_single] at b2
      have e : ∀ a b c d : ℝ, (a + b) - (c + d) = (a - c) + (b - d) := fun a b c d => by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      linarith
    refine (Finset.sum_le_sum each).trans (le_of_eq ?_)
    simp
    ring
  have hsup : |blockMean R.params.side (R.depth + 1) n X h| ≤ S :=
    ((hNear R.params.side hodd (R.depth + 1) n X).1 h).trans (le_max_left _ _)
  have hcoeff : |A.coeff| ≤ 2 := hAt.admissible.abs_coeff_le
  have ha1 := hadm.a_ge
  have hfactor : |R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n X h| ≤
      R.params.coupling * S := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < R.params.coupling)]
    have htwo : |(2 : ℝ)| = 2 := by norm_num
    rw [htwo]
    calc R.params.coupling / 2 * |A.coeff| * |blockMean R.params.side (R.depth + 1) n X h| ≤
          R.params.coupling / 2 * 2 * S := by
          have hhalf : 0 ≤ R.params.coupling / 2 := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hcoeff hhalf) hsup (abs_nonneg _) (by positivity)
      _ = R.params.coupling * S := by ring
  have hsplit : gasBlockMean A G X h - gasBlockMean A G' X' h' =
      ∑ o ∈ centredCube R.params.side,
        (G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) (fineSite R.params.side X 0 o) h) -
          G'.expectation ∅ (fun σ => chartResponse A (configSetting G' σ) (fineSite R.params.side X' 0 o) h')) +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n X h * ∑ i : Fin 4,
        ((G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (X, i)) +
            G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (X - unitStep n i, i))) -
          (G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (X', i)) +
            G'.expectation ∅ (fun σ => chartBondScore (configSetting G' σ) (X' - unitStep n' i, i)))) := by
    unfold gasBlockMean
    rw [sum_sitesInBlocks hodd X, sum_sitesInBlocks hodd X', ← hmean, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hE : 0 ≤ E₁ + E₂ := by positivity
  calc _ ≤ ((R.params.side : ℝ) ^ 4 + ∑ o ∈ centredCube R.params.side,
          recordedSiteScore A G (fineSite R.params.side X 0 o)) * (E₁ + E₂) * S +
        R.params.coupling * S * (8 * (E₁ + E₂)) :=
        add_le_add hsum (mul_le_mul hfactor hbonds (abs_nonneg _) (by positivity))
    _ = _ := by ring
end YangMills.Construction.ResponseInTheExpansion
end
