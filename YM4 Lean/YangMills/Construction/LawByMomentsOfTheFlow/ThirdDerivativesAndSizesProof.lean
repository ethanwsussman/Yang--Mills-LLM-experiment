import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageProof
import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsNearTheResponses
import YangMills.Construction.LawByMomentsOfTheFlow.ThirdDerivativesAndSizes
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion BlockAverages ShareFamilies StepCosts RenormalizationStepParameters
private theorem stepWeight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem weightLipschitz_nonneg' (L t : ℕ) {N : ℕ} (h : PlaquetteWeight N) : 0 ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.weightLipschitz_nonneg <;> assumption
private theorem perturb_zero' {n : ℕ} [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (W : TorusField n) : perturb c X 0 W = W := by
  funext x i
  have h0 : (∑ l, if c l = (x, i) then (0 : Fin k → ℝ) l • X l else 0) = (0 : imaginaryQuaternions) :=
    Finset.sum_eq_zero fun l _ => by simp
  simp only [perturb, h0]
  simp [expUnit_zero]
private theorem isCold_trivialField {n : ℕ} [NeZero n] {s : ℝ} (hs : 0 < s) : IsCold s (trivialField n) := by apply _root_.YangMills.Construction.ImageDensities.isCold_trivialField <;> assumption
private theorem contDiffThree_of_eq_decomp {n : ℕ} [NeZero n] (hC : ColdNearStatement)
    {G Rc Sh Ra : TorusField n → ℝ} {u al d s : ℝ} {W : TorusField n}
    (hW : IsCold s W) (hkey : ∀ V, IsCold s V → G V = Rc V + u • (al • Sh V + Ra V) + d)
    (hR : ContDiffThreeAt Rc W) (hS : ContDiffThreeAt Sh W) (hA : ContDiffThreeAt Ra W) :
    ContDiffThreeAt G W ∧ ∀ (c : Fin 3 → TorusBond n) (X : Fin 3 → imaginaryQuaternions),
      mixedDeriv G W c X = mixedDeriv Rc W c X + u * (al * mixedDeriv Sh W c X + mixedDeriv Ra W c X) := by
  have hev : ∀ {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) =ᶠ[𝓝 0]
      fun σ => Rc (perturb c X σ W) + u • (al • Sh (perturb c X σ W) + Ra (perturb c X σ W)) + d := fun c X =>
    (hC n W _ c X 0 s (by rw [perturb_zero']; exact hW)).mono fun σ h => hkey _ h
  refine ⟨fun k c X => ?_, fun c X => ?_⟩
  · exact (((hR k c X).add (((hS k c X).const_smul al).add (hA k c X) |>.const_smul u)).add
      contDiffAt_const).congr_of_eventuallyEq (hev c X)
  · unfold mixedDeriv
    rw [((hev c X).iteratedFDeriv ℝ 3).self_of_nhds]
    have a := hR 3 c X
    have b := hS 3 c X
    have e := hA 3 c X
    have e1 : (fun σ : Fin 3 → ℝ => Rc (perturb c X σ W) + u • (al • Sh (perturb c X σ W) + Ra (perturb c X σ W)) + d) =
        ((fun σ : Fin 3 → ℝ => Rc (perturb c X σ W)) +
          u • (al • (fun σ => Sh (perturb c X σ W)) + fun σ => Ra (perturb c X σ W))) + fun _ => d := rfl
    have b1 : ContDiffAt ℝ 3 (al • (fun σ : Fin 3 → ℝ => Sh (perturb c X σ W))) 0 := b.const_smul al
    have b2 : ContDiffAt ℝ 3 (al • (fun σ : Fin 3 → ℝ => Sh (perturb c X σ W)) + fun σ => Ra (perturb c X σ W)) 0 :=
      b1.add e
    have b3 : ContDiffAt ℝ 3 (u • (al • (fun σ : Fin 3 → ℝ => Sh (perturb c X σ W)) + fun σ => Ra (perturb c X σ W))) 0 :=
      b2.const_smul u
    have b4 : ContDiffAt ℝ 3 ((fun σ : Fin 3 → ℝ => Rc (perturb c X σ W)) +
        u • (al • (fun σ : Fin 3 → ℝ => Sh (perturb c X σ W)) + fun σ => Ra (perturb c X σ W))) 0 := a.add b3
    rw [e1, iteratedFDeriv_add_apply b4 contDiffAt_const, iteratedFDeriv_add_apply a b3,
      iteratedFDeriv_const_smul_apply b2, iteratedFDeriv_add_apply b1 e, iteratedFDeriv_const_smul_apply b,
      iteratedFDeriv_const_of_ne (by norm_num : (3 : ℕ) ≠ 0)]
    simp
    ring
private theorem abs_third_order_le {dR dS dA u al A B E sz lp w : ℝ} (hw : 0 < w) (hA : 0 ≤ A)
    (hu : |u| ≤ sz) (hal : |al| ≤ 2) (hlp : lp ≤ sz) (hR : |dR| ≤ A * lp / w) (hS : |dS| ≤ B / w)
    (hD : |dA| ≤ E / w) :
    |dR + u * (al * dS + dA)| ≤ (A + 2 * B + E) * sz / w := by
  have hsz : 0 ≤ sz := (abs_nonneg _).trans hu
  have h1 : |dR| ≤ A * sz / w := hR.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlp hA) hw.le)
  have h2 : |al * dS + dA| ≤ (2 * B + E) / w := by
    calc |al * dS + dA| ≤ |al| * |dS| + |dA| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 * (B / w) + E / w := by
          have := mul_le_mul hal hS (abs_nonneg _) (by norm_num)
          linarith
      _ = (2 * B + E) / w := by ring
  have h3 : |u * (al * dS + dA)| ≤ sz * ((2 * B + E) / w) := by
    rw [abs_mul]
    exact mul_le_mul hu h2 (abs_nonneg _) hsz
  calc |dR + u * (al * dS + dA)| ≤ |dR| + |u * (al * dS + dA)| := abs_add_le _ _
    _ ≤ A * sz / w + sz * ((2 * B + E) / w) := add_le_add h1 h3
    _ = (A + 2 * B + E) * sz / w := by ring
private theorem abs_quadratic_part_le {u f r B Kc sz lp w : ℝ} (hw : 0 < w) (hK : 0 ≤ Kc) (hu : |u| ≤ sz)
    (hlp : lp ≤ sz) (hf : |f| ≤ B / w) (hr : |r| ≤ Kc * lp / w) : |u * f + r| ≤ (B + Kc) * sz / w := by
  have hsz : 0 ≤ sz := (abs_nonneg _).trans hu
  have h1 : |u * f| ≤ sz * (B / w) := by
    rw [abs_mul]
    exact mul_le_mul hu hf (abs_nonneg _) hsz
  have h2 : |r| ≤ Kc * sz / w := hr.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlp hK) hw.le)
  calc |u * f + r| ≤ |u * f| + |r| := abs_add_le _ _
    _ ≤ sz * (B / w) + Kc * sz / w := add_le_add h1 h2
    _ = (B + Kc) * sz / w := by ring
private theorem unitGenerator_pair_areUnitVectors : AreUnitVectors ![unitGenerator, unitGenerator] := by
  intro l
  fin_cases l <;> exact SingleColourFields.norm_unitGenerator
private theorem pointwise_response_bounds (hC : ColdNearStatement) (hWt : WeightsCloseToBlockMeans)
    {Λ : MomentParameters} (S : MomentPoint Λ) (hodd : Odd Λ.stepParams.side)
    (hfit : Λ.response.Admissible Λ.stepParams) (hy : 1 ≤ Λ.floor) (hσ : 0 < Λ.stepParams.threshold)
    {Cs Kf : ℝ} (hKf : 0 ≤ Kf)
    (hfam : ∀ t, IsCurvatureFamily Λ.stepParams Cs
      (levelShareFamily Λ.stepParams.coupling Λ.stepParams.side t))
    (hcl : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) (b b' : TorusBond n),
      |classicalRemainder S.tower S.resp t n h y b b'| ≤
        Kf * weightLipschitz Λ.stepParams.side (S.tower.stage t).depth h / Λ.stepParams.weight (tripleDiam y b b')) :
    ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      (∀ W : TorusField n, IsCold Λ.stepParams.threshold W →
        ContDiffThreeAt (fun W' => (S.resp t).cold n y W' h) W ∧
        ∀ (c : Fin 3 → TorusBond n) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
          |mixedDeriv (fun W' => (S.resp t).cold n y W' h) W c X| ≤
            (Λ.response.Kc / Λ.response.η₃ + 2 * Cs + Λ.response.Ka / Λ.response.η₃) *
              weightNorm Λ.stepParams.side (S.tower.stage t).depth h / Λ.stepParams.weight (supportDiam y c)) ∧
      ∀ b b' : TorusBond n, |classicalQuadratic S.tower S.resp t n h y b b'| ≤
        (Cs + Kf) * weightNorm Λ.stepParams.side (S.tower.stage t).depth h /
          Λ.stepParams.weight (tripleDiam y b b') := by
  intro t ht n _ hn y h
  have hst := S.onFlow t ht
  rw [← S.stage_eq t ht] at hst
  have hT : OnStepParameters Λ.table Λ.floor (S.resp t) := hst.onFamily
  have hK : (S.resp t).responseParams = Λ.response := hst.params_eq
  have hI := hT.admissible
  have bnd := hI.bounds
  rw [hK] at bnd
  have hx : (1 : ℝ) ≤ (S.tower.stage t).coupling := hy.trans hT.onFamily.le_coupling
  have hsmall : (S.tower.stage t).coupling ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hη := hfit.η₃_pos
  have hKc : 0 ≤ Λ.response.Kc := zero_le_one.trans hfit.Kc_ge
  have hKa := hfit.Ka_nonneg
  have hu : |blockMean Λ.stepParams.side (S.tower.stage t).depth n y h| ≤
      weightNorm Λ.stepParams.side (S.tower.stage t).depth h :=
    ((hWt Λ.stepParams.side hodd (S.tower.stage t).depth n y).1 h).trans (le_max_left _ _)
  have hlp : weightLipschitz Λ.stepParams.side (S.tower.stage t).depth h ≤
      weightNorm Λ.stepParams.side (S.tower.stage t).depth h := le_max_right _ _
  have hsh : levelShareFamily Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth n y =
      levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y := funext fun V => by
    unfold levelShareFamily
    rw [dif_neg (NeZero.ne n)]
  refine ⟨fun W hW => ?_, fun b b' => ?_⟩
  · have hRc := bnd.remainder_smooth n hn y W hW h
    have hSh := (hfam (S.tower.stage t).depth).smooth n hn y W hW
    have hRa := bnd.site_family.smooth n hn y W hW
    have key : ∀ V, IsCold Λ.stepParams.threshold V → (S.resp t).cold n y V h =
        responseRemainder (S.resp t).cold n y h V + blockMean Λ.stepParams.side (S.tower.stage t).depth n y h •
          ((S.resp t).coeff • levelShareFamily Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth n y V +
          (S.resp t).siteRemainder n y V) + blockMean Λ.stepParams.side (S.tower.stage t).depth n y h *
          ((S.resp t).cold n y (trivialField n) (constOneWeight _) - (S.resp t).siteRemainder n y (trivialField n)) := by
      intro V hV
      have e := bnd.share_site n hn y V hV
      unfold centeredResponse centered at e
      rw [hsh]
      unfold responseRemainder
      simp only [smul_eq_mul]
      have e' : (S.resp t).cold n y V (constOneWeight _) =
          (S.resp t).coeff * levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y V +
          ((S.resp t).siteRemainder n y V - (S.resp t).siteRemainder n y (trivialField n)) +
          (S.resp t).cold n y (trivialField n) (constOneWeight _) := by linarith
      rw [e']
      ring
    obtain ⟨hc3, hd3⟩ := contDiffThree_of_eq_decomp hC hW key hRc hSh hRa
    refine ⟨hc3, fun c X hX => ?_⟩
    rw [hd3 c X]
    have hw := stepWeight_pos Λ.stepParams (supportDiam y c)
    have hR : |mixedDeriv (responseRemainder (S.resp t).cold n y h) W c X| ≤
        Λ.response.Kc / Λ.response.η₃ * weightLipschitz Λ.stepParams.side (S.tower.stage t).depth h /
          Λ.stepParams.weight (supportDiam y c) := by
      simpa using bnd.remainder_decay n hn y W hW h 3 c X (by norm_num) le_rfl hX
    have hS : |mixedDeriv (levelShareFamily Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth n y) W c X| ≤
        Cs / Λ.stepParams.weight (supportDiam y c) :=
      (hfam (S.tower.stage t).depth).decay n hn y W hW 3 c X (by norm_num) (by norm_num) hX
    have hA : |mixedDeriv ((S.resp t).siteRemainder n y) W c X| ≤
        Λ.response.Ka / Λ.response.η₃ / Λ.stepParams.weight (supportDiam y c) := by
      have h0 := bnd.site_family.decay n hn y W hW 3 c X (by norm_num) le_rfl hX
      rw [if_pos rfl] at h0
      refine h0.trans (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ?_ hη.le) hw.le)
      calc Λ.response.Ka * (S.tower.stage t).coupling ^ (-(1 / 2) : ℝ) ≤ Λ.response.Ka * 1 :=
            mul_le_mul_of_nonneg_left hsmall hKa
        _ = Λ.response.Ka := mul_one _
    exact abs_third_order_le hw (div_nonneg hKc hη.le) hu hI.abs_coeff_le hlp hR hS hA
  · have hw := stepWeight_pos Λ.stepParams (tripleDiam y b b')
    have hcold : IsCold Λ.stepParams.threshold (trivialField n) := isCold_trivialField hσ
    have hf : |shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b'| ≤
        Cs / Λ.stepParams.weight (tripleDiam y b b') := by
      have h0 := (hfam (S.tower.stage t).depth).decay n hn y (trivialField n) hcold 2 ![b, b']
        ![unitGenerator, unitGenerator] (by norm_num) (by norm_num) unitGenerator_pair_areUnitVectors
      rw [hsh] at h0
      exact h0
    exact abs_quadratic_part_le hw hKf hu hlp hf (hcl t ht n hn y h b b')
theorem thirdDerivativeBoundsStatement_holds (hF : classicalFormsApproxStatement)
    (hS : ResponseInTheExpansion.levelSharesUniformStatement) (hWt : WeightsCloseToBlockMeans)
    (hC : ColdNearStatement) : thirdDerivativeBoundsStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hF a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hS a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL Tb hTa hTL hD hCS hCH hrt hCd Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hL ((le_max_left _ _).trans hLL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd) Kr hKr
  obtain ⟨y₂, Y₂⟩ := H₂ L hL ((le_max_right _ _).trans hLL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd)
  refine ⟨max 1 (max y₁ y₂), ?_⟩
  intro y hy hRet hWil g hg hyg k _ hk2 hk8 R d hd
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hyy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  obtain ⟨C', c', X', _, _, Z⟩ := Y₁ y hyy₁ hRet hWil g hg hyg k hk2 hk8 R d hd
  obtain ⟨Cs, -, hfam⟩ := Y₂ y hyy₂ hRet hWil
  have hη := (hKr y).η₃_pos
  have hKc : 0 ≤ Kr.Kc := zero_le_one.trans (hKr y).Kc_ge
  have hKa := (hKr y).Ka_nonneg
  refine ⟨fun i => if i = 0 then Kr.Kc / Kr.η₃ + 2 * Cs + Kr.Ka / Kr.η₃ else Cs + |C' 2|, 1, y, one_pos, le_rfl, ?_⟩
  intro S
  have hodd : Odd (Tb.stepParameters y).side := by
    rw [show (Tb.stepParameters y).side = L from hTL]
    exact hL
  have hmain := pointwise_response_bounds hC hWt S hodd (hKr y) hy1 hD.σ_pos (abs_nonneg (C' 2)) (fun t => (hfam t).1)
    (fun t ht n _ hn z h b b' => (Z S t ht n hn z h b b').1.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (weightLipschitz_nonneg' _ _ h))
        (stepWeight_pos _ _).le))
  intro t ht n _ hn z h
  obtain ⟨h1, h2⟩ := hmain t ht n hn z h
  exact ⟨h1, h2⟩
end YangMills.Construction.MomentLaw
end
