import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.RegularityOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepFormAnExpansion
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamilyProof
import YangMills.Construction.ResponseInTheExpansion.ColdHalfOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.GasPartHasItsBoundsProof
import YangMills.Construction.ResponseInTheExpansion.HotHalfOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.TheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion.ResponseReturns
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses TopLevelSites StepCosts
section Size
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {n : ℕ} [NeZero n]
theorem mixedDeriv_fin_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → BlockAverages.imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p46649 <;> assumption
theorem fieldsAgreeNear_zero (W W' : TorusField n) (y : TorusSite n) : FieldsAgreeNear W W' y y 0 := by
  intro b hb
  exfalso
  have h1 := hb.1 b.2
  have h2 := hb.2 b.2
  simp only [Nat.cast_zero, abs_nonpos_iff] at h1
  simp [h1] at h2
theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
theorem stepWeight_zero (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) : ℓ.weight 0 = 1 := by apply _root_.YangMills.Construction.TorusLumps.StepParameters.weight_zero <;> assumption
end Size
theorem abs_centeredResponse_le_of_cold {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {K : ResponseParameters} {t : ℕ} {x al : ℝ}
    {P : ColdResponse ℓ.side (t + 1)} {Ra Rb : LocalDensity} (hW : WeightsCloseToBlockMeans) (hfit : ℓ.Admissible)
    (hK : K.Admissible ℓ) (hcl : ColdResponseBounds ℓ K (t + 1) x al P Ra Rb) (hal : |al| ≤ 3)
    (hσ1 : ℓ.threshold ≤ 1) (hsmall : K.Ka * x ^ (-(1 / 2) : ℝ) ≤ 1 / 4)
    (hshare : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n), IsCold ℓ.threshold V →
      |levelShare ℓ.coupling ℓ.side (t + 1) Finset.univ y V| ≤ K.N₀) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n)
    (Y : TorusSite n) (V : TorusField n) (hV : IsCold ℓ.threshold V) (h : PlaquetteWeight (fineSide ℓ.side (t + 1) n)) :
    |centeredResponse P n Y V h| ≤ (K.C₀ - 1) * weightNorm ℓ.side (t + 1) h := by
  have hn2 : 2 * 0 + 2 < n := by
    have := hfit.n₀_ge
    omega
  have hfl := trivialField_isCold hfit.σ_pos n
  have hag := fieldsAgreeNear_zero V (trivialField n) Y
  have e₀ : centeredResponse P n Y V h = centeredRemainder P n Y h V +
      blockMean ℓ.side (t + 1) n Y h * centeredResponse P n Y V (constOneWeight _) := by
    simp only [centeredResponse, centeredRemainder, responseRemainder]
    ring
  have hr := hcl.remainder.compare n hn Y V (trivialField n) 0 hn2 hV hfl hag h 0 (fun l => l.elim0)
    (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_fin_zero, mixedDeriv_fin_zero, stepWeight_zero, div_one] at hr
  have hr0 : centeredRemainder P n Y h (trivialField n) = 0 := by simp [centeredRemainder]
  rw [hr0, sub_zero] at hr
  have ha := hcl.site_family.local_density n n hn hn Y Y V (trivialField n) 0 hn2 hn2 hV hfl hag 0
    (fun l => l.elim0) (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_fin_zero, mixedDeriv_fin_zero, stepWeight_zero, div_one] at ha
  have ha0 : centered Ra n Y (trivialField n) = 0 := by simp [centered]
  rw [ha0, sub_zero] at ha
  have hone := hcl.share_site n hn Y V hV
  have hsz0 : 0 ≤ weightNorm ℓ.side (t + 1) h := by
    have p0 : OrientedPlaquette (fineSide ℓ.side (t + 1) n) := ⟨(0, 0, 1), by simp⟩
    have h1 : |h p0.1| ≤ weightSup h :=
      le_ciSup (f := fun p : OrientedPlaquette (fineSide ℓ.side (t + 1) n) => |h p.1|)
        (Set.finite_range _).bddAbove p0
    exact (abs_nonneg _).trans (h1.trans (le_max_left _ _))
  have hhat : |blockMean ℓ.side (t + 1) n Y h| ≤ weightNorm ℓ.side (t + 1) h :=
    (((hW ℓ.side hfit.L_odd (t + 1) n Y).1 h)).trans (le_max_left _ _)
  have hlip : weightLipschitz ℓ.side (t + 1) h ≤ weightNorm ℓ.side (t + 1) h := le_max_right _ _
  have hKc : 0 ≤ K.Kc := by linarith [hK.Kc_ge]
  have hN := hK.N₀_nonneg
  have hone' : |centeredResponse P n Y V (constOneWeight _)| ≤ 3 * K.N₀ + 1 / 4 := by
    rw [hone]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h₁ := hshare n hn Y V hV
    have h₂ : |al| * |levelShare ℓ.coupling ℓ.side (t + 1) Finset.univ Y V| ≤ 3 * K.N₀ :=
      mul_le_mul hal h₁ (abs_nonneg _) (by norm_num)
    linarith
  rw [e₀]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have h₃ : |blockMean ℓ.side (t + 1) n Y h| * |centeredResponse P n Y V (constOneWeight _)| ≤
      weightNorm ℓ.side (t + 1) h * (3 * K.N₀ + 1 / 4) :=
    mul_le_mul hhat hone' (abs_nonneg _) hsz0
  have h₄ : K.Kc * weightLipschitz ℓ.side (t + 1) h ≤ K.Kc * weightNorm ℓ.side (t + 1) h :=
    mul_le_mul_of_nonneg_left hlip hKc
  have hC : K.Kc + 3 * K.N₀ + 1 / 4 ≤ K.C₀ - 1 := by
    rw [hK.C₀_eq]
    have := hfit.a_ge
    linarith [hK.Kc_ge]
  nlinarith
theorem abs_levelShare_le {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy : T.floorMin ≤ y) (t n : ℕ)
    [NeZero n] (hn : T.n₀ ≤ n) (z : TorusSite n) (V : TorusField n) (hV : IsCold T.threshold V) :
    |levelShare T.coupling T.side (t + 1) Finset.univ z V| ≤ T.N 0 := by
  obtain ⟨-, -, -, -, -, -, -, hN, hchain⟩ := hT.chain
  have hside : ∀ i, (torusFrame T.side t n).extent i = n := fun _ => rfl
  have hamb : BlockAverages.IsAdmissibleAmbient (torusFrame T.side t n) :=
    TorusFrame.isAdmissibleAmbient_torusFrame (by
      have := hT.n₀_ge
      omega)
  have hσ₀ := hT.σ_pos
  have hle : T.threshold ≤ T.σA := by
    have := hT.σ_le
    linarith
  have hreg : BlockAverages.IsOrthantRegular
      (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n))) 2047 := by
    rw [cellsOfSites_univ hside]
    exact isOrthantRegular_finiteCells (fun i => by
      have := hT.n₀_ge
      show 0 < n
      omega) _
  have hcold : BlockAverages.IsCold (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n)))
      (torusFrame T.side t n).top T.threshold
      (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top V) := by
    rw [cellsOfSites_univ hside]
    exact isCold_readAtLevel hside hV
  have hall := hchain (torusFrame T.side t n) 2047 _ rfl hamb (by norm_num) hreg T.threshold _ hσ₀ hle hcold
  have hb := hall.2.2.1.2.2.2.2.2.2.2.1
  have hY := hb (torusSiteInFrame (torusFrame T.side t n) (torusFrame T.side t n).top z)
  have hN0 := hN 0
  have hsq : T.threshold ^ 2 ≤ 1 := by
    have := hT.σ_one
    nlinarith
  have h1 : levelShare T.coupling T.side (t + 1) Finset.univ z V =
      BlockAverages.minimalCellShare T.coupling
        (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n)))
        (torusSiteInFrame (torusFrame T.side t n) (torusFrame T.side t n).top z)
        (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top V) := rfl
  rw [h1, abs_of_nonneg hY.1]
  refine hY.2.trans ?_
  nlinarith
theorem isWellPosed_of_onParameters {T : ParameterAssignment} {y : ℝ} {R : StepSetup} (hT : T.Admissible)
    (hon : R.OnParameters T y) (hfit : R.params.Admissible) (hArr : R.IsSymmetricWeight)
    (hr₁ : R.nextRange ≤ R.range + 1) (hr₂ : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ R.range)
    (hx : 0 < R.coupling) : R.IsWellPosed := by apply _root_.YangMills.Construction.ResponseInTheExpansion.GasTermBounds.isWellPosed_of_onParameters <;> assumption
theorem mul_rpow_neg_three_halves_le_one {x Cs : ℝ} (hx : 1 ≤ x) (hC : Cs ≤ x) (hCs : 0 ≤ Cs) :
    Cs * x ^ (-(3 / 2) : ℝ) ≤ 1 := by
  have h0 : 0 < x := by linarith
  have h1 : x ^ (-(3 / 2) : ℝ) ≤ x⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  calc Cs * x ^ (-(3 / 2) : ℝ) ≤ x * x⁻¹ :=
        mul_le_mul hC h1 (Real.rpow_nonneg h0.le _) h0.le
    _ = 1 := mul_inv_cancel₀ h0.ne'
theorem mul_rpow_neg_half_le_quarter {x Ka : ℝ} (hKa : 0 ≤ Ka) (hx0 : 0 < x) (hx : (4 * Ka) ^ 2 ≤ x) :
    Ka * x ^ (-(1 / 2) : ℝ) ≤ 1 / 4 := by
  rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
  have h1 : 4 * Ka ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
  have h0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [← div_eq_mul_inv, div_le_iff₀ h0]
  linarith
set_option maxHeartbeats 2000000 in
theorem responseReturns (hCold : coldResponseUniqueCoefficient) (hHot : hotRegimeStepStatement)
    (hCar : StepResponseIsometryInvariant) (hW : WeightsCloseToBlockMeans)
    (hCI : ImageColdExpansion.ImageHasColdExpansion) (hSt : ClusterExpansionOfAStep.CoarseStatesFormHullExpansion)
    (hD : ImageDensities.ImageHasHullExpansion) (hReg : ClusterExpansionOfAStep.ImageHasHullExpansionRegularity)
    (hP : ClusterExpansionOfAStep.ImageHasHullExpansionPrice) (hFlr : StepFloors.EventuallyFloorConditions) :
    responseReturnsStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, g₁⟩ := hCold a ha
  obtain ⟨r₂, hr₂, g₂⟩ := hHot
  obtain ⟨r₃, hr₃, g₃⟩ := hCar
  obtain ⟨r₄, hr₄, g₄⟩ := hCI
  obtain ⟨r₅, hr₅, g₅⟩ := hD
  obtain ⟨r₆, hr₆, g₆⟩ := hP
  refine ⟨L₁, fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (r₆ c))))),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (lt_min (hr₄ c) (lt_min (hr₅ c) (hr₆ c))))),
    fun T hTa hLT hT hCS hOn hrt M => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have u₁ := hrt.trans (min_le_right _ _)
  have t₂ := u₁.trans (min_le_left _ _)
  have u₂ := u₁.trans (min_le_right _ _)
  have t₃ := u₂.trans (min_le_left _ _)
  have u₃ := u₂.trans (min_le_right _ _)
  have t₄ := u₃.trans (min_le_left _ _)
  have u₄ := u₃.trans (min_le_right _ _)
  have t₅ := u₄.trans (min_le_left _ _)
  have t₆ := u₄.trans (min_le_right _ _)
  obtain ⟨C₁, C₂, C₃, g₁⟩ := g₁ T hTa hLT hT hCS hOn t₁
  obtain ⟨-, -, -, -, -, -, -, hNpos, -⟩ := id hT.chain
  set Kc : ℝ := max (max M C₁) 1 with hKc
  let K₀ : ResponseParameters :=
    { η₃ := T.η₃, N₀ := T.N 0, nr := 0, Kc := Kc, C₀ := 12 + 40 * T.coupling + 8 * T.N 0 + 2 * Kc,
      s₁ := 2 * (T.side : ℝ) ^ 4 * (12 + 40 * T.coupling + 8 * T.N 0 + 2 * Kc + 2) + 40 * T.coupling,
      Ka := max C₂ 1, Kb := max C₃ 1, Cstar := 0 }
  have hFit : ∀ y : ℝ, K₀.Admissible (T.stepParameters y) := fun y =>
    ⟨hT.η₃_pos, hT.η₃_le, rfl, (hNpos 0).le, le_max_right _ _, rfl, rfl,
      le_trans zero_le_one (le_max_right _ _), le_trans zero_le_one (le_max_right _ _), le_rfl⟩
  refine ⟨K₀, (le_trans (le_max_left _ _) (le_max_left _ _)), rfl, rfl, hFit, ?_⟩
  obtain ⟨Cs, y₁, hCs, g₁⟩ :=
    g₁ K₀ (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _) (le_max_left _ _)
  obtain ⟨y₂, g₂⟩ := g₂ T hT t₂ K₀
  obtain ⟨y₃, g₃⟩ := g₃ T hT t₃ K₀
  obtain ⟨y₄, g₄⟩ := g₄ T hT hCS t₄
  obtain ⟨y₅, g₅⟩ := g₅ T hT hCS t₅
  obtain ⟨y₆, g₆⟩ := g₆ T hT t₆
  obtain ⟨y₇, g₇⟩ := hReg T hT
  have hCpos : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFlr T hT _ 1 hCpos one_pos
  refine ⟨Cs, max (max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆) (max y₇ yF)))
    (max T.floorMin (max (Cs + 1) ((4 * K₀.Ka) ^ 2 + 2 * T.B + 1))), hCs,
    fun y hy R A hL hK hA hArr hmv => ?_⟩
  have e₀ := (le_max_left _ _).trans hy
  have e₀' := (le_max_right _ _).trans hy
  have f₁ := (le_max_left _ _).trans e₀
  have f₂ := (le_max_right _ _).trans e₀
  have f₃ := (le_max_left _ _).trans f₁
  have f₄ := (le_max_right _ _).trans f₁
  have e₁ : y₁ ≤ y := (le_max_left _ _).trans f₃
  have e₂ : y₂ ≤ y := (le_max_right _ _).trans f₃
  have e₃ : y₃ ≤ y := (le_max_left _ _).trans f₄
  have e₄ : y₄ ≤ y := (le_max_right _ _).trans f₄
  have f₅ := (le_max_left _ _).trans f₂
  have f₆ := (le_max_right _ _).trans f₂
  have e₅ : y₅ ≤ y := (le_max_left _ _).trans f₅
  have e₆ : y₆ ≤ y := (le_max_right _ _).trans f₅
  have e₇ : y₇ ≤ y := (le_max_left _ _).trans f₆
  have e₈ : yF ≤ y := (le_max_right _ _).trans f₆
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans e₀'
  have f₇ := (le_max_right _ _).trans e₀'
  have hyC : Cs + 1 ≤ y := (le_max_left _ _).trans f₇
  have hyK : (4 * K₀.Ka) ^ 2 + 2 * T.B + 1 ≤ y := (le_max_right _ _).trans f₇
  have hon := hA.onFamily
  have hℓ : R.params = T.stepParameters y := hon.params_eq
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hresp := hA.admissible
  have hfit : R.params.Admissible := by
    rw [hℓ]
    exact hT.fits y hy0
  have hKf : A.responseParams.Admissible R.params := hresp.params_admissible
  have hmov := hA.abs_sub_le
  have hmovB : |R.nextCoupling - R.coupling| ≤ 2 * R.params.B := by
    rw [hℓ]
    exact hmov
  have hB1 : 1 ≤ T.B := hT.B_ge
  have hx1 : 1 ≤ R.coupling := by linarith
  have hx0 : 0 < R.coupling := by linarith
  have hF := hyF R.coupling (e₈.trans hxy)
  obtain ⟨-, -, -, hrr⟩ := hF.stable_nearby.2 R.nextCoupling hmov
  have hr' : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ R.range := by
    have h := hF.range_ge
    show 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange R.coupling
    exact_mod_cast h
  have hforms := isWellPosed_of_onParameters hT hon hfit hArr hrr hr' hx0
  have hframes : R.ColdChainFits :=
    ⟨T.δ₁, T.lam, T.σA, T.cg, T.N, by rw [hℓ, hon.anchorRadius_eq]; exact hT.chain, by rw [hℓ]; exact hT.σ_le,
      by rw [hℓ]; exact hT.σ_one⟩
  have hst := hSt R hforms hframes hL
  have hcold := (g₄ y e₄ R hon hArr).1
  have hdi := g₅ y e₅ R hon hforms hmv hmovB hL
  have hre := g₇ y e₇ R hℓ hon.anchorRadius_eq hon.barrierFn_eq hxy hon.isStep.1 hArr hmv hmovB hL
  have hpr := g₆ y e₆ R hon hforms hmv hmovB hL
  have hhull := hullExpansion_of_parts hst hdi hre hpr
  have hcoldX : ColdExpansion R.params (R.depth + 1) R.nextCoupling (kernelImage R.params R.coupling R.functional)
      (R.renormalizedDensity T.lam) := by
    rw [hmv]
    exact hcold
  obtain ⟨al', hal', ⟨Ra, Rb, hcl⟩, huniq⟩ := g₁ y e₁ R A hK hA hArr
  obtain ⟨hprice, hshape, hforget, hsizeI⟩ := g₂ y e₂ R A hK hA hforms hmv hL
  obtain ⟨c₁, c₂, c₃⟩ := g₃ y e₃ R A hK hA hL hArr
  have hal3 : |al'| ≤ 3 := by
    have h₁ := hal'.trans (mul_rpow_neg_three_halves_le_one hx1 (by linarith) hCs)
    have h₂ := hresp.abs_coeff_le
    have h₃ := abs_sub_abs_le_abs_sub al' A.coeff
    linarith
  have hmv2 := abs_le.mp hmov
  have hsq₀ := sq_nonneg (4 * K₀.Ka)
  have hx'0 : 0 < R.nextCoupling := by linarith [hmv2.1]
  have hsmall : A.responseParams.Ka * R.nextCoupling ^ (-(1 / 2) : ℝ) ≤ 1 / 4 := by
    rw [hK]
    refine mul_rpow_neg_half_le_quarter (le_trans zero_le_one (le_max_right _ _)) hx'0 ?_
    linarith [hmv2.1]
  have hcl' : ColdResponseBounds R.params A.responseParams (R.depth + 1) R.nextCoupling al' A.coldStep Ra Rb := by
    rw [hK]
    exact hcl
  have hσ1 : R.params.threshold ≤ 1 := by
    rw [hℓ]
    exact hT.σ_one
  have hshare : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (z : TorusSite n) (V : TorusField n),
      IsCold R.params.threshold V →
      |levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ z V| ≤ A.responseParams.N₀ := by
    intro n _ hn z V hV
    rw [hA.N₀_eq]
    rw [hℓ] at hn hV ⊢
    exact abs_levelShare_le hT hy0 R.depth n hn z V hV
  have hsize : StepSizeBounds A hL := hsizeI fun n _ hn Y V hV h =>
    abs_centeredResponse_le_of_cold hW hfit hKf hcl' hal3 hσ1 hsmall hshare hn Y V hV h
  have hrow : ResponseBounds R.params A.responseParams (R.depth + 1) R.nextCoupling al'
      (ClusterExpansionOfAStep.coarseLabelSpace R hL) (coarseWeightExpansion R)
      (coarseLabelScore A.responseParams.s₁ A.score) A.coldStep A.hullStep Ra Rb :=
    { cold_linear := hshape.cold_linear, hull_linear := hshape.hull_linear, cold_reads := hshape.cold_reads,
      hull_reads := hshape.hull_reads, cold_borel := hshape.cold_borel, hull_borel := hshape.hull_borel,
      cold_gauge := hshape.cold_gauge, hull_gauge := hshape.hull_gauge,
      cold_translation := hshape.cold_translation, hull_translation := hshape.hull_translation,
      empty := hshape.empty, mass_integrable := c₁, mass_carried := c₂, cold_carried := c₃,
      share_site := hcl'.share_site, share_total := hcl'.share_total, site_family := hcl'.site_family,
      total_family := hcl'.total_family, remainder_smooth := hcl'.remainder.smooth,
      remainder_decay := hcl'.remainder.decay, remainder_local := hcl'.remainder.compare,
      forget := hforget.forget, forget_cold := hforget.forget_cold,
      forget_both_cold := hforget.forget_both_cold, size_cold := hsize.size_cold, size_hull := hsize.size_hull }
  refine ⟨⟨hcoldX, hhull, hprice⟩, al', hal', ⟨Ra, Rb, hrow⟩, ?_⟩
  rintro al'' ⟨Ra'', Rb'', row⟩
  refine huniq al'' ⟨Ra'', Rb'', ?_⟩
  rw [← hK]
  exact ⟨row.share_site, row.share_total, row.site_family, row.total_family,
    ⟨row.remainder_smooth, row.remainder_decay, row.remainder_local⟩⟩
end YangMills.Construction.ResponseInTheExpansion.ResponseReturns
end
