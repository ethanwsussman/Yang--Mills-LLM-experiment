import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.GasPartHasItsBounds
import YangMills.Construction.ResponseInTheExpansion.ImageOfOneAtABlock
import YangMills.Construction.ResponseInTheExpansion.MeanOfAFamilyAtAStep
import YangMills.Construction.ResponseInTheExpansion.RemaindersOfAResponseAreCarried
import YangMills.Construction.ResponseInTheExpansion.ResponseIsCarried
import YangMills.Construction.ResponseInTheExpansion.ShapeOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.SmoothPartsHaveTheirBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames FamilyNorms Interpolation BlockMeans
namespace ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps TorusBlocks StepSettings RenormalizationStepParameters StepGas StepCosts ShareFamilies
  BlockAverages TermCalculus
namespace GasTermBounds
variable {R : StepSetup} {n : ℕ}
theorem weightNorm_constOneWeight_le_one (L t m : ℕ) : weightNorm L t (constOneWeight m) ≤ 1 := by
  unfold weightNorm weightSup weightLipschitz
  refine max_le (Real.iSup_le (fun p => by simp [constOneWeight]) zero_le_one) (Real.iSup_le (fun pp => ?_) zero_le_one)
  simp [constOneWeight]
theorem gasRate_pos {T : ParameterAssignment} (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
def translateBack [NeZero n] (u : TorusSite n) : TorusIsometry :=
  ⟨1, fun _ => 1, fun i => -((u i).cast : ℤ), fun _ => Or.inl rfl⟩
theorem translateBack_mapSite [NeZero n] (u x : TorusSite n) : (translateBack u).mapSite x = x - u := by
  funext i
  simp [TorusIsometry.mapSite, translateBack, sub_eq_add_neg]
theorem translateBack_transports [NeZero n] (u : TorusSite n) (W : TorusField n) :
    (translateBack u).Transports W (TorusFields.translate u W) := by
  intro x k
  have : (translateBack u).axisSign ((translateBack u).axisPerm.symm k) = 1 := rfl
  rw [if_pos this, translateBack_mapSite]
  simp only [TorusFields.translate, sub_add_cancel]
  rfl
theorem parentBlock_add_scaled {L : ℕ} [NeZero L] [NeZero n] (x : TorusSite (n * L)) (u : TorusSite n) :
    parentBlock L (x + siteOfInt fun i => (L : ℤ) * ((u i).cast : ℤ)) = parentBlock L x + u := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hx : (x + siteOfInt fun i => (L : ℤ) * ((u i).cast : ℤ)) =
      (siteOfInt fun i => ((x i).cast : ℤ) + (L : ℤ) * ((u i).cast : ℤ) : TorusSite (n * L)) := by
    funext i
    simp [siteOfInt]
  rw [hx]
  funext k
  rw [parentBlock_siteOfInt]
  have h2 : ((x k).cast : ℤ) + (L : ℤ) * ((u k).cast : ℤ) + ((L : ℤ) - 1) / 2 =
      (((x k).cast : ℤ) + ((L : ℤ) - 1) / 2) + (L : ℤ) * ((u k).cast : ℤ) := by ring
  rw [h2, Int.add_mul_ediv_left _ _ (ne_of_gt hLpos)]
  push_cast
  simp [parentBlock]
theorem blockConstantTerm_add {A : ResponseSetup R} (hA : A.IsAdmissible) (hσ : 0 < R.params.threshold) [NeZero n]
    (hn : R.params.n₀ ≤ n) (Y u : TorusSite n) :
    blockConstantTerm A n Y = blockConstantTerm A n (Y + u) := by
  classical
  unfold blockConstantTerm
  rw [dif_neg (NeZero.ne n), dif_neg (NeZero.ne n)]
  congr 1
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hnL : n ≤ n * R.params.side := Nat.le_mul_of_pos_right n hL0
  set s : TorusSite (n * R.params.side) := siteOfInt fun i => (R.params.side : ℤ) * ((u i).cast : ℤ) with hs
  have hg : ∀ x : TorusSite (n * R.params.side),
      A.cold (n * R.params.side) x (trivialField _) (constOneWeight _) =
      A.cold (n * R.params.side) (x + s) (trivialField _) (constOneWeight _) := fun x =>
    hA.bounds.cold_translation (n * R.params.side) (by omega) x (fun i => ((u i).cast : ℤ)) (trivialField _)
      (isCold_trivialField hσ _) (constOneWeight _)
  refine Finset.sum_bij' (fun x _ => x + s) (fun x _ => x - s) ?_ ?_ ?_ ?_ fun x _ => hg x
  · intro x hx
    have h1 : parentBlock R.params.side x = Y := by simpa [sitesInBlocks] using hx
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hs, parentBlock_add_scaled, h1]
  · intro x hx
    have h1 : parentBlock R.params.side x = Y + u := by simpa [sitesInBlocks] using hx
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    have h2 := parentBlock_add_scaled (L := R.params.side) (x - s) u
    rw [← hs, sub_add_cancel, h1] at h2
    exact (add_right_cancel h2).symm
  · intro x _
    simp
  · intro x _
    simp
theorem ColdDensityBounds.mono {ℓ : TorusLumps.StepParameters} {e e' η₃ : ℝ} {h : LocalDensity} (hη : 0 < η₃)
    (he : e ≤ e') (hf : ColdDensityBounds ℓ e (e / η₃) h) : ColdDensityBounds ℓ e' (e' / η₃) h := by
  have hw := weight_pos ℓ
  have h3 : e / η₃ ≤ e' / η₃ := div_le_div_of_nonneg_right he hη.le
  refine ⟨hf.smooth, hf.gauge, hf.translation, ?_, ?_, hf.no_curvature_term⟩
  · intro n _ hn y W hW k c X h1 h3' hX
    refine (hf.decay n hn y W hW k c X h1 h3' hX).trans (div_le_div_of_nonneg_right ?_ (hw _).le)
    split_ifs
    · exact h3
    · exact he
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    exact (hf.local_density n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu).trans
      (div_le_div_of_nonneg_right he (hw _).le)
theorem gasTerm_eq {A : ResponseSetup R} [NeZero n] (Y : TorusSite n) :
    gasTerm A n Y = fun V => gasTermAtBlock A (coldCaseGround R V) Y (constOneWeight _) := by
  funext V
  simp only [gasTerm, dif_neg (NeZero.ne n)]
theorem isWellPosed_of_onParameters {T : ParameterAssignment} {y : ℝ} {R : StepSetup} (hT : T.Admissible)
    (hon : R.OnParameters T y) (hadm : R.params.Admissible) (hsym : R.IsSymmetricWeight)
    (hr₁ : R.nextRange ≤ R.range + 1) (hr₂ : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ R.range)
    (hx : 0 < R.coupling) : R.IsWellPosed := by
  have hp := hon.params_eq
  have hLe : R.params.side = T.side := by rw [hp]; rfl
  have hn : R.params.n₀ = T.n₀ := by rw [hp]; rfl
  have hr₃ : R.range ≤ R.nextRange + 1 := hon.isStep.2.2
  refine ⟨hon.isStep.1, hadm, ?_, hr₃, hr₁, by omega, by rw [hLe]; omega, by rw [hn]; omega, hx, hsym⟩
  have e₁ : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius
    rw [hp]
    rfl
  rw [e₁, hon.barrierFn_eq]
  exact hT.cut
theorem gasTerm_isAdmissibleDensity {A : ResponseSetup R} {F : LocalDensity} {c : (m : ℕ) → TorusSite m → ℝ}
    (hFg : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ (Y : TorusSite m) (g : TorusSite m → UnitQuaternion)
      (W : TorusField m), IsCold R.params.threshold W → F m Y (_root_.YangMills.Construction.TorusFields.gaugeTransform g W) = F m Y W)
    (hFt : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ (Y u : TorusSite m) (W : TorusField m),
      IsCold R.params.threshold W → F m Y (TorusFields.translate u W) = F m (Y + u) W)
    (hsm : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ (Y : TorusSite m) (W : TorusField m),
      IsCold R.params.threshold W → ContDiffThreeAt (gasTerm A m Y) W)
    (hone : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ (Y : TorusSite m) (V : TorusField m),
      IsCold R.params.threshold V → A.coldStep m Y V (constOneWeight _) = F m Y V + gasTerm A m Y V + c m Y)
    (hc : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ Y u : TorusSite m, c m Y = c m (Y + u))
    (hg : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ (Y : TorusSite m) (g : TorusSite m → UnitQuaternion)
      (W : TorusField m), IsCold R.params.threshold W →
      A.coldStep m Y (_root_.YangMills.Construction.TorusFields.gaugeTransform g W) (constOneWeight _) = A.coldStep m Y W (constOneWeight _))
    (ht : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ (Y u : TorusSite m) (W : TorusField m),
      IsCold R.params.threshold W →
      A.coldStep m Y (TorusFields.translate u W) (constOneWeight _) = A.coldStep m (Y + u) W (constOneWeight _)) :
    IsAdmissibleDensity R.params (gasTerm A) := by
  refine ⟨hsm, fun m _ hm Y g W hW => ?_, fun m _ hm Y u W hW => ?_⟩
  · have hW' : IsCold R.params.threshold (_root_.YangMills.Construction.TorusFields.gaugeTransform g W) := fun x μ ν hμ => by
      rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
      exact hW x μ ν hμ
    have e₁ := hone m hm Y _ hW'
    have e₂ := hone m hm Y _ hW
    have e₃ := hg m hm Y g W hW
    have e₄ := hFg m hm Y g W hW
    linarith
  · have hW' : TorusFields.IsCold R.params.threshold (TorusFields.translate u W) := fun x μ ν hμ => by
      rw [curvature_translate]
      exact hW _ μ ν hμ
    have e₁ := hone m hm Y _ hW'
    have e₂ := hone m hm (Y + u) _ hW
    have e₃ := ht m hm Y u W hW
    have e₄ := hFt m hm Y u W hW
    have e₅ := hc m hm Y u
    linarith
end GasTermBounds
open GasTermBounds in
theorem gasTermBounds_holds (hGas : GasTermAtColdFields) (hOne : imageOfOneAtBlockStatement)
    (hSm : smoothTermsBoundsStatement) (hMn : meanOfFamilyAtStepStatement)
    (hCr : remaindersInvariantUnderIsometries) (hShape : ResponseShapeStatement)
    (hRC : StepResponseIsometryInvariant) (hSh : LevelSharesFormCurvatureFamily) (hLab : ClusterExpansionOfAStep.CoarseLabelsStandard)
    (hFl : StepFloors.EventuallyFloorConditions) : gasTermBoundsStatement := by
  obtain ⟨r₁, hr₁, g₁⟩ := hGas
  obtain ⟨r₂, hr₂, g₂⟩ := hOne
  obtain ⟨r₃, hr₃, g₃⟩ := hShape
  obtain ⟨r₄, hr₄, g₄⟩ := hRC
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c)), fun T hD hCS hOn hrt => ?_⟩
  have t₁ := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have t₂ := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have t₃ := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t₄ := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁, y₅, hC₁, g₅⟩ := hSm T hD hCS hOn
  obtain ⟨C₂, y₆, hC₂, g₆⟩ := hMn T hD hOn
  have hch := gasRate_pos hD
  obtain ⟨y₇, g₇⟩ := rpow_mul_exp_le_one (c := T.gasRate / 2) (by positivity) 1
  obtain ⟨y₈, g₈⟩ := hFl T hD (2 ^ 40 * (T.side : ℝ) + 4 * T.n₀ + 2 ^ 17) 1 (by positivity) one_pos
  refine ⟨2, by norm_num, fun K => ?_⟩
  obtain ⟨y₁, g₁⟩ := g₁ T hD t₁ K
  obtain ⟨y₂, g₂⟩ := g₂ T hD t₂ K
  obtain ⟨y₃, g₃⟩ := g₃ T hD t₃ K
  obtain ⟨y₄, g₄⟩ := g₄ T hD t₄ K
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆) (max (max y₇ y₈) (max T.floorMin T.yC))),
    fun y hy R A hK hA hSym => ?_⟩
  have f₁ := (le_max_left _ _).trans hy
  have f₂ := (le_max_right _ _).trans hy
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
  have f₇ := (le_max_left _ _).trans f₆
  have f₈ := (le_max_right _ _).trans f₆
  have e₇ : y₇ ≤ y := (le_max_left _ _).trans f₇
  have e₈ : y₈ ≤ y := (le_max_right _ _).trans f₇
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans f₈
  have hyC : T.yC ≤ y := (le_max_right _ _).trans f₈
  have hon := hA.onFamily
  have hp : R.params = T.stepParameters y := hon.params_eq
  have hresp := hA.admissible
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hadm : R.params.Admissible := by
    rw [hp]
    exact hD.fits y hy0
  have hσ : 0 < R.params.threshold := hadm.σ_pos
  have hx1 : 1 ≤ R.coupling := hD.yC_ge.trans (hyC.trans hxy)
  have hx0 : 0 < R.coupling := lt_of_lt_of_le one_pos hx1
  have hFl := g₈ R.coupling (e₈.trans hxy)
  obtain ⟨-, -, -, hrr⟩ := hFl.stable_nearby.2 R.nextCoupling hA.abs_sub_le
  have hr' : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ R.range := by
    have h := hFl.range_ge
    show 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange R.coupling
    exact_mod_cast h
  have hwp := isWellPosed_of_onParameters hD hon hadm hSym hrr hr' hx0
  have hL2 : 2 ≤ R.params.side := by
    have := hadm.L_ge
    omega
  have hL := hLab R hL2
  have shape := g₃ y e₃ R A hK hA hwp hL
  have car := (g₄ y e₄ R A hK hA hL hSym).2.2
  have one := g₂ y e₂ R A hK hA hCS
  have gas := g₁ y e₁ R A hK hA hSym
  obtain ⟨Pf, Ps, Pm, Pt⟩ := g₅ y e₅ R A hon hresp.abs_coeff_le
  have hKa : K.Admissible R.params := hK ▸ hresp.params_admissible
  have hE : 0 < R.params.E := hadm.E_pos
  have hη : K.η₃ = T.η₃ := by
    have h1 := hKa.E₃_eq
    have h2 : R.params.E₃ = R.params.E / T.η₃ := by
      rw [hp]
      rfl
    rw [h2] at h1
    have h3 := hKa.η₃_pos
    have h4 := hD.η₃_pos
    exact mul_left_cancel₀ hE.ne' ((div_eq_div_iff h4.ne' h3.ne').1 h1)
  have hxh : 0 < R.coupling ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hε : 0 < (K.Ka + 1) * R.coupling ^ (-(1 / 2) : ℝ) := mul_pos (by linarith [hKa.Ka_nonneg]) hxh
  have hfam : ColdDensityBounds R.params ((K.Ka + 1) * R.coupling ^ (-(1 / 2) : ℝ))
      ((K.Ka + 1) * R.coupling ^ (-(1 / 2) : ℝ) / T.η₃) A.siteRemainder := by
    have h0 := hresp.bounds.site_family
    rw [hK, hη] at h0
    exact ColdDensityBounds.mono hD.η₃_pos (mul_le_mul_of_nonneg_right (by linarith) hxh.le) h0
  have Pr := (g₆ y e₆ R hon _ A.siteRemainder hε hfam (hCr T hD y hy0 R A hon hresp).2).1
  obtain ⟨sh, -, -⟩ := hSh T hD y hy0 R.depth
  have ha : R.params.coupling = T.coupling := by rw [hp]; rfl
  have hLe : R.params.side = T.side := by rw [hp]; rfl
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hp]; rfl
  have hσe : R.params.threshold = T.threshold := by rw [hp]; rfl
  have hS : ∀ (m : ℕ) [NeZero m] (Y : TorusSite m) (V : TorusField m),
      levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V =
      levelShareFamily T.coupling T.side (R.depth + 1) m Y V := fun m _ Y V => by
    unfold levelShareFamily
    rw [dif_neg (NeZero.ne m), ha, hLe]
  have hexp : Real.exp (-(T.gasRate * R.coupling / 2)) ≤ R.coupling ^ (-(3 / 2) : ℝ) := by
    have h1 := g₇ R.coupling (e₇.trans hxy)
    have hq : 0 < R.coupling ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_neg hx0.le, inv_eq_one_div, le_div_iff₀ hq]
    have e : -(T.gasRate * R.coupling / 2) = -(T.gasRate / 2 * R.coupling) := by ring
    rw [e]
    linarith
  have hxt : 0 < R.coupling ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hsz : ∀ m : ℕ, Real.exp (-(T.gasRate * R.coupling / 2)) * weightNorm R.params.side R.depth (constOneWeight m) ≤
      R.coupling ^ (-(3 / 2) : ℝ) := fun m => by
    calc _ ≤ Real.exp (-(T.gasRate * R.coupling / 2)) * 1 :=
          mul_le_mul_of_nonneg_left (weightNorm_constOneWeight_le_one _ _ _) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact hexp
  have plain : IsAdmissibleDensity R.params (gasTerm A) := by
    refine gasTerm_isAdmissibleDensity (F := fun m Y V => A.coeff * levelShareFamily T.coupling T.side (R.depth + 1) m Y V +
      frameTerm A m Y V + incrementTerm A m Y V +
      densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.siteRemainder) m Y V + scoreTailTerm A m Y V)
      (c := blockConstantTerm A) ?_ ?_ ?_ ?_ (fun m _ hm Y u => blockConstantTerm_add hresp hσ hm Y u) ?_ ?_
    · intro m _ hm Y g W hW
      have h1 := sh.gauge m (hp ▸ hm) Y g W (hp ▸ hW)
      simp only [h1, Pf.admissible.gauge m hm Y g W hW, Pm.admissible.gauge m hm Y g W hW,
        Pr.admissible.gauge m hm Y g W hW, Pt.admissible.gauge m hm Y g W hW]
    · intro m _ hm Y u W hW
      have h1 := sh.translation m (hp ▸ hm) Y u W (hp ▸ hW)
      simp only [h1, Pf.admissible.translation m hm Y u W hW, Pm.admissible.translation m hm Y u W hW,
        Pr.admissible.translation m hm Y u W hW, Pt.admissible.translation m hm Y u W hW]
    · intro m _ hm Y W hW
      rw [gasTerm_eq]
      exact (gas.1 m hm Y W hW (constOneWeight _)).2.1
    · intro m _ hm Y V hV
      rw [one m hm Y V hV, hS]
    · intro m _ hm Y g W hW
      exact shape.cold_gauge m hm Y g W hW _
    · intro m _ hm Y u W hW
      have h1 := car m hm (translateBack u) (Y + u) W (TorusFields.translate u W) hW (translateBack_transports u W)
      rw [translateBack_mapSite, add_sub_cancel_right] at h1
      exact h1
  refine ⟨plain, ?_, ?_⟩
  · intro m _ hm Y W hW k c X h1 h3 hX
    rw [gasTerm_eq]
    refine ((gas.1 m hm Y W hW (constOneWeight _)).2.2 k c X h1 h3 hX).trans ?_
    have hw := weight_pos R.params (supportDiam Y c)
    refine div_le_div_of_nonneg_right ?_ hw.le
    have := hsz (fineSide R.params.side (R.depth + 1) m)
    split_ifs <;> linarith
  · have c₀ : LocalComparison R.params (gasTerm A) fun m => R.coupling ^ (-(3 / 2) : ℝ) / R.params.weight m := by
      intro m m' _ _ hm hm' Y Y' W W' r h2 h2' cW cW' ag k bb X hk hbox hu
      rw [gasTerm_eq, gasTerm_eq]
      refine (gas.2 m m' hm hm' Y Y' W W' r h2 h2' cW cW' ag (constOneWeight _) (constOneWeight _)
        (fun _ _ _ _ _ => rfl) k bb X hk hbox hu).trans
        (div_le_div_of_nonneg_right (hsz _) (weight_pos R.params r).le)
    have c₁ := localComparison_centeredFamily hσ plain c₀ fun m => div_nonneg hxt.le (weight_pos R.params m).le
    intro m m' _ _ hm hm' Y Y' W W' r h2 h2' cW cW' ag k bb X hk hbox hu
    refine (c₁ m m' hm hm' Y Y' W W' r h2 h2' cW cW' ag k bb X hk hbox hu).trans (le_of_eq ?_)
    ring
end ResponseInTheExpansion
end YangMills.Construction
end
