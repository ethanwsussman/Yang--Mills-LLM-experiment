import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheMovesAreCarried
import YangMills.Construction.ResponseInTheExpansion.SmoothPartsHaveTheirBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames BlockAverages TorusLumps RenormalizationStepParameters StepSettings WeightedResponses TermCalculus
namespace SmoothTermsBounds
variable {ℓ : TorusLumps.StepParameters} {T' : ColdStepAtMirrorFrames.StepParameters}
structure ParametersMatch (ℓ : TorusLumps.StepParameters) (T' : ColdStepAtMirrorFrames.StepParameters) : Prop where
  side : ℓ.side = T'.L
  n₀ : ℓ.n₀ = T'.n₀
  threshold : ℓ.threshold = T'.σ
  rate : ℓ.rt = T'.κ
theorem termBounds_of_topFamily (hA : TopFamilyOnTori) (hF : ℓ.Admissible) (hT : ParametersMatch ℓ T') {t : ℕ} {B : ℝ}
    {g : TopLevelFamily} (hB : 0 ≤ B) (hd : IsLocalDensity T'.L t T'.n₀ (5 / 4 * T'.σ) g)
    (hdec : DerivDecay T'.L t T'.n₀ (5 / 4 * T'.σ) g fun _ m => B * Real.exp (-(T'.κ / 2 ^ 5 * m)))
    (hloc : IsLocalOnTori T'.L t T'.n₀ (9 / 8 * T'.σ) g fun q => B * Real.exp (-(2 * T'.decayRate * q))) :
    TermBounds ℓ (weightGrowthSup ℓ.rt ℓ.n₁ * B) (weightGrowthSup ℓ.rt ℓ.n₁ * B) (2 * (weightGrowthSup ℓ.rt ℓ.n₁ * B))
      (densityOfTopFamily ℓ.side t g) := by
  have hσ := hF.σ_pos
  have hrt := hF.rt_pos
  rw [hT.rate] at hrt
  have hs : ℓ.threshold ≤ 5 / 4 * T'.σ := by rw [hT.threshold] at hσ ⊢; linarith
  have hs' : ℓ.threshold ≤ 9 / 8 * T'.σ := by rw [hT.threshold] at hσ ⊢; linarith
  refine termBounds_of_exp_bounds hA hF (s := 5 / 4 * T'.σ) (s' := 9 / 8 * T'.σ) hs hs' hB
    (by rw [hT.side, hT.n₀]; exact hd) ?_ ?_
  · rw [hT.side, hT.n₀, hT.rate]
    refine derivDecay_mono hdec fun k m _ _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : T'.κ / 2 ^ 9 * m ≤ T'.κ / 2 ^ 5 * m := mul_le_mul_of_nonneg_right (by linarith [hrt]) hm
    linarith
  · rw [hT.side, hT.n₀, hT.rate]
    refine isLocalOnTori_mono hloc fun m => le_of_eq ?_
    have : 2 * T'.decayRate = T'.κ / 2 ^ 9 := by
      unfold ColdStepAtMirrorFrames.StepParameters.decayRate
      ring
    rw [this]
theorem isSmallCurvature_mono {F : BlockFrame} {j : ℕ} {s s' : ℝ} (h : s ≤ s') {V : F.GaugeField j}
    (hV : IsSmallCurvature s V) : IsSmallCurvature s' V := fun q hq => lt_of_lt_of_le (hV q hq) h
theorem isLocalDensity_expectation {t : ℕ} {x h : ℝ} {f : LocalFamily} {K : FramedFamily}
    (hd : ExpectationDecays T' t x f h K)
    (hg : ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top) (γ : F.Cell → UnitQuaternion),
      IsCubicTopTorus T'.L t T'.n₀ F → IsSmallCurvature (5 / 4 * T'.σ) V →
      (coldHalfLawAt T' x f).expectationOf (K F Y) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = (coldHalfLawAt T' x f).expectationOf (K F Y) V)
    (hc : ∀ (F : BlockFrame) (Y h' : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T'.L t T'.n₀ F →
      IsSmallCurvature (5 / 4 * T'.σ) V →
      (coldHalfLawAt T' x f).expectationOf (K F (Y + h')) (translateField h' V) =
        (coldHalfLawAt T' x f).expectationOf (K F Y) V) :
    IsLocalDensity T'.L t T'.n₀ (5 / 4 * T'.σ) fun F Y V => (coldHalfLawAt T' x f).expectationOf (K F Y) V :=
  ⟨fun F hF Y V hV => (hd F Y V hF hV).1, fun F hF Y V γ hV => hg F Y V γ hF hV, fun F hF Y h' V hV => hc F Y h' V hF hV⟩
theorem derivDecay_expectation {t : ℕ} {x h : ℝ} {f : LocalFamily} {K : FramedFamily}
    (hd : ExpectationDecays T' t x f h K) :
    DerivDecay T'.L t T'.n₀ (5 / 4 * T'.σ) (fun F Y V => (coldHalfLawAt T' x f).expectationOf (K F Y) V)
      fun _ m => T'.CE * h * Real.exp (-(T'.κ / 2 ^ 5 * m)) :=
  fun F hF Y V k c X hV h1 h3 hX => (hd F Y V hF hV).2 k c X h1 h3 hX
theorem isLocalOnTori_expectation {t : ℕ} {x h : ℝ} {f : LocalFamily} {K : FramedFamily}
    (hc : ExpectationIsLocal T' t x f h K) :
    IsLocalOnTori T'.L t T'.n₀ (9 / 8 * T'.σ) (fun F Y V => (coldHalfLawAt T' x f).expectationOf (K F Y) V)
      fun q => T'.CE * h * Real.exp (-(2 * T'.decayRate * q)) :=
  fun F F' hF hF' Y Y' V V' r k b X hV hV' hA hk hb hX => hc F F' Y Y' V V' r k b X hF hF' hV hV' hA hk hb hX
theorem cellBond_add {F : BlockFrame} (Y h : F.Cell) (i : Fin 4) (back : Bool) :
    cellBond (Y + h) i back = ((cellBond Y i back).1 + h, (cellBond Y i back).2) := by
  cases back
  · rfl
  · simp only [cellBond, if_true]
    congr 1
    abel
theorem termBounds_of_lawFamily (hA : TopFamilyOnTori) (hF : ℓ.Admissible) (hT : ParametersMatch ℓ T') {t : ℕ}
    {x B : ℝ} {f : LocalFamily} {Q : ColdHalfLaw} (hQ : coldHalfLawAt T' x f = Q) (gf : ColdHalfLaw → TopLevelFamily)
    (hB : 0 ≤ B) (hd : IsLocalDensity T'.L t T'.n₀ (5 / 4 * T'.σ) (gf (coldHalfLawAt T' x f)))
    (hdec : DerivDecay T'.L t T'.n₀ (5 / 4 * T'.σ) (gf (coldHalfLawAt T' x f))
      fun _ m => B * Real.exp (-(T'.κ / 2 ^ 5 * m)))
    (hloc : IsLocalOnTori T'.L t T'.n₀ (9 / 8 * T'.σ) (gf (coldHalfLawAt T' x f))
      fun q => B * Real.exp (-(2 * T'.decayRate * q))) :
    TermBounds ℓ (weightGrowthSup ℓ.rt ℓ.n₁ * B) (weightGrowthSup ℓ.rt ℓ.n₁ * B) (2 * (weightGrowthSup ℓ.rt ℓ.n₁ * B))
      (densityOfTopFamily ℓ.side t (gf Q)) := by
  subst hQ
  exact termBounds_of_topFamily hA hF hT hB hd hdec hloc
theorem termBounds_of_frameFamily (hA : TopFamilyOnTori) (hF : ℓ.Admissible)
    (hn : ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ)) (hT : ParametersMatch ℓ T') {t : ℕ} {ε : ℝ} {g : TopLevelFamily}
    (hε : 0 ≤ ε) (hd : IsLocalDensity T'.L t T'.n₀ (9 / 8 * T'.σ) g)
    (hdec : DerivDecay T'.L t T'.n₀ (9 / 8 * T'.σ) g fun _ m => ε / torusDecayFactor T'.L T'.decayRate m)
    (hloc : IsLocalOnTori T'.L t T'.n₀ (9 / 8 * T'.σ) g fun r => ε / torusDecayFactor T'.L T'.decayRate r) :
    TermBounds ℓ ε ε (2 * ε) (densityOfTopFamily ℓ.side t g) := by
  have hσ := hF.σ_pos
  have hs : ℓ.threshold ≤ 9 / 8 * T'.σ := by rw [hT.threshold] at hσ ⊢; linarith
  obtain ⟨p, d, c, -, -⟩ := hA ℓ hF t (9 / 8 * T'.σ) g hs
  have hw : ∀ m : ℕ, torusDecayFactor T'.L T'.decayRate m = ℓ.weight m := fun m => by
    have := torusDecayFactor_eq_weight hn m
    rw [hT.side, hT.rate] at this
    exact this
  have hd' : IsLocalDensity ℓ.side t ℓ.n₀ (9 / 8 * T'.σ) g := by rw [hT.side, hT.n₀]; exact hd
  have P := p hd'
  refine ⟨P, ?_, ?_⟩
  · refine d _ ?_
    rw [hT.side, hT.n₀]
    refine derivDecay_mono hdec fun k m _ _ => le_of_eq ?_
    rw [hw]
    split_ifs <;> rfl
  · have c' : LocalComparison ℓ (densityOfTopFamily ℓ.side t g) fun m => ε / ℓ.weight m := by
      refine c _ ?_
      rw [hT.side, hT.n₀]
      exact isLocalOnTori_mono hloc fun m => le_of_eq (by rw [hw])
    have := localComparison_centeredFamily hσ P c' fun m => div_nonneg hε (weight_pos ℓ m).le
    intro n n' _ _ hn' hn'' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    refine (this n n' hn' hn'' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu).trans (le_of_eq ?_)
    ring
theorem termBounds_sum_eight {e d : ℝ} (P : Fin 4 → Bool → LocalDensity)
    (h : ∀ i b, TermBounds ℓ e e d (P i b)) :
    TermBounds ℓ (8 * e) (8 * e) (8 * d) (fun n y W => ∑ i, ∑ b, P i b n y W) := by
  have a : ∀ i, TermBounds ℓ (e + e) (e + e) (d + d) (fun n y W => P i true n y W + P i false n y W) :=
    fun i => termBounds_add (h i true) (h i false)
  have s := termBounds_add (termBounds_add (termBounds_add (a 0) (a 1)) (a 2)) (a 3)
  have e1 : (fun n y W => ∑ i, ∑ b, P i b n y W) = fun n y W =>
      P 0 true n y W + P 0 false n y W + (P 1 true n y W + P 1 false n y W) + (P 2 true n y W + P 2 false n y W) +
        (P 3 true n y W + P 3 false n y W) := by
    funext n y W
    simp only [Fin.sum_univ_four, Fintype.sum_bool]
  rw [e1]
  exact termBounds_mono (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring)) s
end SmoothTermsBounds
set_option maxHeartbeats 1600000 in
open SmoothTermsBounds in
theorem smoothTermsBoundsStatement_holds (hRB : ColdExpansionRegular) (hA : TopFamilyOnTori)
    (hMv : expectationsEquivariantStatement) : smoothTermsBoundsStatement := by
  intro T hD hCS hOn
  obtain ⟨c, nss, hTies, hAll⟩ := hOn
  obtain ⟨c', nss', hTies', hAll'⟩ := hCS
  obtain ⟨y₁, hy₁⟩ := rpow_mul_exp_frameRadius_le_one (c := T.δc / 8) (by have := hD.δc_pos; positivity) (4 * T.Ct)
  have hG0 : 0 ≤ weightGrowthSup T.rt T.n₁ := weightGrowthSup_nonneg _ _
  have hCE0 := hD.CE_pos
  have hCs0 := hD.Cs_pos
  have ha0 : 0 < T.coupling := lt_of_lt_of_le one_pos hD.a_ge
  refine ⟨1 + 4 * weightGrowthSup T.rt T.n₁ * T.CE + 32 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE),
    max (max T.floorMin T.yC) y₁, by positivity, fun y hy R A hR hal => ?_⟩
  set C : ℝ := 1 + 4 * weightGrowthSup T.rt T.n₁ * T.CE + 32 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) with hC
  have hy₀ : T.floorMin ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hy
  have hyC : T.yC ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hy
  have hyP : y₁ ≤ y := (le_max_right _ _).trans hy
  have hℓ := hR.params_eq
  have hF : R.params.Admissible := hℓ ▸ hD.fits y hy₀
  have hx : y ≤ R.coupling := hR.le_coupling
  have hx1 : 1 ≤ R.coupling := hD.yC_ge.trans (hyC.trans hx)
  have hx0 : 0 < R.coupling := lt_of_lt_of_le one_pos hx1
  have hn₁ : R.params.n₁ = (R.params.side : ℝ) ^ (1 / 640 : ℝ) := by rw [hℓ]; rfl
  have hGe : weightGrowthSup R.params.rt R.params.n₁ = weightGrowthSup T.rt T.n₁ := by rw [hℓ]; rfl
  have expansionF := hRB R.params R.depth R.coupling R.functional R.density hF hn₁ hR.isStep.1.1
  rw [hℓ] at expansionF
  have hTd : ParametersMatch R.params (T.stepParamsAt c nss y) :=
    ⟨by rw [hℓ]; rfl, by rw [hℓ]; rfl, by rw [hℓ]; rfl, by rw [hℓ]; rfl⟩
  have hρA : c.ρA = T.ρA := hTies.2.2.1
  have hρA' : c'.ρA = T.ρA := hTies'.2.2.1
  have hδ₂ : c'.δ₂ = T.δc := hTies'.2.2.2.2.2.2.1
  have hQ : coldHalfLawAt (T.stepParamsAt c nss y) R.coupling (localFamilyOfDensity R.density) = coldHalfLawOf R := by
    have h1 : R.params.coupling = T.coupling := by rw [hℓ]; rfl
    have h2 : R.ballRadius = T.threshold / 64 := by
      show R.params.threshold / 64 = _
      rw [hℓ]
      rfl
    have h3 : R.params.rt = T.rt := by rw [hℓ]; rfl
    unfold coldHalfLawOf
    rw [h1, h2, h3, hR.anchorRadius_eq, hR.barrierFn_eq, ← hρA]
    rfl
  set St := T.stepParamsAt c nss y with hSt
  have H := hAll y hyC
  have hDraw : St.IsOrdered := ⟨hD.a_ge, hD.L_odd, hTies.2.2.2.2.2.2.2, hD.rt_pos, hD.η₃_pos, hD.η₃_le, hD.σ_pos, hD.cut,
    (by have := (hD.fits y hy₀).E_pos; have hB := hD.B_ge; show (1 : ℝ) ≤ 4 * T.B; linarith)⟩
  have hL40 : 2 ^ 40 ≤ St.L := hD.L_ge
  have hn64 : 64 ≤ St.n₀ := le_trans (by norm_num) hD.n₀_ge
  have hcar := hMv St hDraw hL40 hn64 H.equivariance R.depth R.coupling (localFamilyOfDensity R.density) hx expansionF
  obtain ⟨m1, m2, m3, m4, m5, -⟩ := H.smoothIncrements R.depth R.coupling (localFamilyOfDensity R.density) hx expansionF
  have hκ : 0 < St.κ := hD.rt_pos
  have hσ : 0 < St.σ := hD.σ_pos
  have hxh : R.coupling ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hxh0 : 0 ≤ R.coupling ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  have hxt0 : 0 < R.coupling ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hal0 : |A.coeff| / R.coupling ≤ 2 / R.coupling := div_le_div_of_nonneg_right hal hx0.le
  have hbs : |A.coeff / R.coupling| = |A.coeff| / R.coupling := by rw [abs_div, abs_of_pos hx0]
  have hCge : 1 ≤ C := by
    have h1 : 0 ≤ 4 * weightGrowthSup T.rt T.n₁ * T.CE := by positivity
    have h2 : 0 ≤ 32 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) := by positivity
    rw [hC]
    linarith
  have hC1 : 4 * weightGrowthSup T.rt T.n₁ * T.CE ≤ C := by
    have h2 : 0 ≤ 32 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) := by positivity
    rw [hC]
    linarith
  have hC3 : 32 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) ≤ C := by
    have h2 : 0 ≤ 4 * weightGrowthSup T.rt T.n₁ * T.CE := by positivity
    rw [hC]
    linarith
  have Ps := termBounds_of_lawFamily hA hF hTd hQ (fun Q _ Y V => Q.expectationOf (Q.linearBlockPart Y) V)
    (B := St.CE * 1) (by positivity)
    (isLocalDensity_expectation m3 (fun F Y V γ hF hV => ((hcar F V hF hV).1 γ Y).1)
      (fun F Y h' V hF hV => ((hcar F V hF hV).2.2.1 h' Y).1))
    (derivDecay_expectation m3) (isLocalOnTori_expectation m4)
  have Pm := termBounds_of_lawFamily hA hF hTd hQ (fun Q _ Y V => Q.expectationOf (Q.blockIncrement Y) V)
    (B := St.CE * R.coupling ^ (-(1 / 2) : ℝ)) (mul_nonneg hCE0.le hxh0)
    (isLocalDensity_expectation m1 (fun F Y V γ hF hV => ((hcar F V hF hV).1 γ Y).2)
      (fun F Y h' V hF hV => ((hcar F V hF hV).2.2.1 h' Y).2))
    (derivDecay_expectation m1) (isLocalOnTori_expectation m2)
  rw [hGe] at Ps Pm
  have hexp : ∀ {u v : ℝ} (m : ℕ), u ≤ v → Real.exp (-(v * m)) ≤ Real.exp (-(u * m)) := fun m h => by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) m)
    linarith
  have hr1 : St.κ / 2 ^ 5 ≤ 2 ^ 8 * St.κ := by linarith
  have hr2 : 2 * St.decayRate ≤ 2 ^ 8 * St.κ := by
    unfold ColdStepAtMirrorFrames.StepParameters.decayRate
    linarith
  have Pt : ∀ (i : Fin 4) (back : Bool), TermBounds R.params (weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE))
      (weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE)) (2 * (weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE)))
      (densityOfTopFamily R.params.side R.depth fun _ Y V =>
        (coldHalfLawOf R).scoreRemainderAt (cellBond Y i back) 0 V +
          (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).scoreRemainderIncrement (cellBond Y i back)) V) := by
    intro i back
    have sc := H.scoreRemainder R.depth R.coupling (localFamilyOfDensity R.density) i back hx
    have dA : DerivDecay St.L R.depth St.n₀ (5 / 4 * St.σ)
        (fun F Y V => (coldHalfLawAt St R.coupling (localFamilyOfDensity R.density)).scoreRemainderAt
          (cellBond Y i back) 0 V) fun _ m => St.Cs * Real.exp (-(St.κ / 2 ^ 5 * m)) :=
      fun F hF' Y V k c X hV h1 h3 hX => (sc.1 F Y V k c X hF' hV h1 h3 hX).2.trans
        (mul_le_mul_of_nonneg_left (hexp _ hr1) hCs0.le)
    have cA : IsLocalOnTori St.L R.depth St.n₀ (9 / 8 * St.σ)
        (fun F Y V => (coldHalfLawAt St R.coupling (localFamilyOfDensity R.density)).scoreRemainderAt
          (cellBond Y i back) 0 V) fun q => St.Cs * Real.exp (-(2 * St.decayRate * q)) :=
      fun F F' hF' hF'' Y Y' V V' r k b X hV hV' hAg hk hb hX =>
        (sc.2 F F' Y Y' V V' r k b X hF' hF'' (isSmallCurvature_mono (by linarith) hV)
          (isSmallCurvature_mono (by linarith) hV') hAg hk hb hX).trans
          (mul_le_mul_of_nonneg_left (hexp _ hr2) hCs0.le)
    have dnA : IsLocalDensity St.L R.depth St.n₀ (5 / 4 * St.σ)
        (fun F Y V => (coldHalfLawAt St R.coupling (localFamilyOfDensity R.density)).scoreRemainderAt
          (cellBond Y i back) 0 V) :=
      ⟨fun F hF' Y V hV => (sc.1 F Y V 1 (fun _ => cellBond Y i back) (fun _ => quaternionI) hF' hV le_rfl
          (by norm_num) (fun _ => norm_quaternionI)).1,
        fun F hF' Y V γ hV => ((hcar F V hF' hV).2.1 γ _).1,
        fun F hF' Y h' V hV => by
          show (coldHalfLawAt St R.coupling (localFamilyOfDensity R.density)).scoreRemainderAt
            (cellBond (Y + h') i back) 0 (translateField h' V) = _
          rw [cellBond_add]
          exact ((hcar F V hF' hV).2.2.2 h' _).1⟩
    have PA := termBounds_of_lawFamily hA hF hTd hQ (fun Q _ Y V => Q.scoreRemainderAt (cellBond Y i back) 0 V)
      (B := St.Cs) hCs0.le dnA dA cA
    have mv := m5 i back
    have PB := termBounds_of_lawFamily hA hF hTd hQ
      (fun Q _ Y V => Q.expectationOf (Q.scoreRemainderIncrement (cellBond Y i back)) V)
      (B := St.CE * R.coupling ^ (-(1 / 2) : ℝ)) (mul_nonneg hCE0.le hxh0)
      (isLocalDensity_expectation mv.1 (fun F Y V γ hF' hV => ((hcar F V hF' hV).2.1 γ _).2)
        (fun F Y h' V hF' hV => by
          show (coldHalfLawAt St R.coupling (localFamilyOfDensity R.density)).expectationOf
            ((coldHalfLawAt St R.coupling (localFamilyOfDensity R.density)).scoreRemainderIncrement
              (cellBond (Y + h') i back)) (translateField h' V) = _
          rw [cellBond_add]
          exact ((hcar F V hF' hV).2.2.2 h' _).2))
      (derivDecay_expectation mv.1) (isLocalOnTori_expectation mv.2)
    rw [hGe] at PA PB
    have hs : weightGrowthSup T.rt T.n₁ * St.Cs + weightGrowthSup T.rt T.n₁ * (St.CE * R.coupling ^ (-(1 / 2) : ℝ)) ≤
        weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) := by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hG0
      have : St.CE * R.coupling ^ (-(1 / 2) : ℝ) ≤ St.CE * 1 := mul_le_mul_of_nonneg_left hxh hCE0.le
      show T.Cs + T.CE * R.coupling ^ (-(1 / 2) : ℝ) ≤ T.Cs + T.CE
      have h2 : T.CE * R.coupling ^ (-(1 / 2) : ℝ) ≤ T.CE * 1 := this
      linarith
    exact termBounds_mono hs hs (by linarith) (termBounds_add PA PB)
  have P8 := termBounds_sum_eight _ Pt
  have hx2 : (R.coupling ^ 2)⁻¹ ≤ R.coupling ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have haR : R.params.coupling = T.coupling := by rw [hℓ]; rfl
  have hbT : |-(R.params.coupling / 2 * A.coeff * (R.coupling ^ 2)⁻¹)| ≤ T.coupling * R.coupling ^ (-(3 / 2) : ℝ) := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by rw [haR]; positivity : 0 < R.params.coupling / 2),
      abs_of_pos (by positivity : 0 < (R.coupling ^ 2)⁻¹), haR]
    have h1 : T.coupling / 2 * |A.coeff| ≤ T.coupling := by nlinarith
    calc T.coupling / 2 * |A.coeff| * (R.coupling ^ 2)⁻¹ ≤ T.coupling * (R.coupling ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hx2 ha0.le
  have Ptails : TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
      (C * R.coupling ^ (-(3 / 2) : ℝ)) (scoreTailTerm A) := by
    have S := termBounds_scaled_abs (b := -(R.params.coupling / 2 * A.coeff * (R.coupling ^ 2)⁻¹)) P8
    have hE0 : 0 ≤ weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) := by positivity
    have hm : ∀ u : ℝ, 0 ≤ u → u ≤ 16 * (weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE)) →
        |-(R.params.coupling / 2 * A.coeff * (R.coupling ^ 2)⁻¹)| * u ≤ C * R.coupling ^ (-(3 / 2) : ℝ) :=
      fun u h0 h1 => by
      calc _ ≤ (T.coupling * R.coupling ^ (-(3 / 2) : ℝ)) * u := mul_le_mul_of_nonneg_right hbT h0
        _ ≤ (T.coupling * R.coupling ^ (-(3 / 2) : ℝ)) * (16 * (weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (16 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE)) * R.coupling ^ (-(3 / 2) : ℝ) := by ring
        _ ≤ C * R.coupling ^ (-(3 / 2) : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hxt0.le
          have : 16 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) ≤
              32 * T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) := by
            have h3 : 0 ≤ T.coupling * weightGrowthSup T.rt T.n₁ * (T.Cs + T.CE) := by positivity
            nlinarith
          linarith
    exact termBounds_mono (hm _ (by positivity) (by linarith)) (hm _ (by positivity) (by linarith))
      (hm _ (by positivity) (by linarith)) S
  have hTd' : ParametersMatch R.params (T.stepParamsAt c' nss' y) :=
    ⟨by rw [hℓ]; rfl, by rw [hℓ]; rfl, by rw [hℓ]; rfl, by rw [hℓ]; rfl⟩
  have Dn := hAll' y hyC R.depth R.coupling hx (localFamilyOfDensity R.density) expansionF
  have eτ : blockFrameExcess R = (T.stepParamsAt c' nss' y).frameFamily R.coupling := by
    funext F Y V
    show frameDensity false R.params.coupling R.anchorRadius R.coupling R.frameReach Y V =
      frameDensity false T.coupling c'.ρA R.coupling (frameRadius R.coupling) Y V
    rw [haR, hR.anchorRadius_eq, hρA']
    rfl
  have hCt := hD.Ct_pos
  set Eτ : ℝ := Real.exp (-(T.δc / 8 * frameRadius R.coupling)) with hEτ
  have hE0 : 0 < Eτ := Real.exp_pos _
  have Pf : TermBounds R.params (T.Ct * R.coupling * Eτ) (T.Ct * R.coupling * Eτ) (2 * (T.Ct * R.coupling * Eτ))
      (densityOfTopFamily R.params.side R.depth (blockFrameExcess R)) := by
    rw [eτ, hEτ, ← hδ₂]
    exact termBounds_of_frameFamily hA hF hn₁ hTd' (by positivity) Dn.localDensity_τ Dn.derivDecay_τ Dn.localOnTori_τ
  have Pframe : TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
      (C * R.coupling ^ (-(3 / 2) : ℝ)) (frameTerm A) := by
    have S := termBounds_scaled_abs (b := -(A.coeff / R.coupling)) Pf
    have hp : 0 < R.coupling ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hq : R.coupling ^ (-(3 / 2) : ℝ) = (R.coupling ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hx0.le _
    have hfl : 4 * T.Ct * Eτ ≤ R.coupling ^ (-(3 / 2) : ℝ) := by
      have h1 : 4 * T.Ct * R.coupling ^ (3 / 2 : ℝ) * Eτ ≤ 1 := hy₁ R.coupling (hyP.trans hx)
      have h2 : 4 * T.Ct * Eτ * R.coupling ^ (3 / 2 : ℝ) ≤ 1 := by
        calc 4 * T.Ct * Eτ * R.coupling ^ (3 / 2 : ℝ) = 4 * T.Ct * R.coupling ^ (3 / 2 : ℝ) * Eτ := by ring
          _ ≤ 1 := h1
      rw [hq, inv_eq_one_div]
      exact (le_div_iff₀ hp).mpr h2
    have hm : ∀ u : ℝ, 0 ≤ u → u ≤ 2 * (T.Ct * R.coupling * Eτ) →
        |-(A.coeff / R.coupling)| * u ≤ C * R.coupling ^ (-(3 / 2) : ℝ) := fun u h0 h1 => by
      rw [abs_neg, hbs]
      calc |A.coeff| / R.coupling * u ≤ 2 / R.coupling * u := mul_le_mul_of_nonneg_right hal0 h0
        _ ≤ 2 / R.coupling * (2 * (T.Ct * R.coupling * Eτ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * T.Ct * Eτ := by field_simp; ring
        _ ≤ R.coupling ^ (-(3 / 2) : ℝ) := hfl
        _ ≤ C * R.coupling ^ (-(3 / 2) : ℝ) := by nlinarith
    have hu : 0 ≤ T.Ct * R.coupling * Eτ := by positivity
    exact termBounds_mono (hm _ hu (by linarith)) (hm _ hu (by linarith)) (hm _ (by positivity) le_rfl) S
  have Pslope : TermBounds R.params (C / R.coupling) (C / R.coupling) (C / R.coupling) (linearTerm A) := by
    have S := termBounds_scaled_abs (b := A.coeff / R.coupling) Ps
    have hu : 0 ≤ weightGrowthSup T.rt T.n₁ * (St.CE * 1) := by positivity
    have hm : ∀ u : ℝ, 0 ≤ u → u ≤ 2 * (weightGrowthSup T.rt T.n₁ * (St.CE * 1)) →
        |A.coeff / R.coupling| * u ≤ C / R.coupling := fun u h0 h1 => by
      rw [hbs]
      calc |A.coeff| / R.coupling * u ≤ 2 / R.coupling * u := mul_le_mul_of_nonneg_right hal0 h0
        _ ≤ 2 / R.coupling * (2 * (weightGrowthSup T.rt T.n₁ * (St.CE * 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 * weightGrowthSup T.rt T.n₁ * T.CE) / R.coupling := by
          show 2 / R.coupling * (2 * (weightGrowthSup T.rt T.n₁ * (T.CE * 1))) = _
          ring
        _ ≤ C / R.coupling := div_le_div_of_nonneg_right hC1 hx0.le
    exact termBounds_mono (hm _ hu (by linarith)) (hm _ hu (by linarith)) (hm _ (by positivity) le_rfl) S
  have Pmove : TermBounds R.params (C * R.coupling ^ (-(1 / 2) : ℝ)) (C * R.coupling ^ (-(1 / 2) : ℝ))
      (C * R.coupling ^ (-(1 / 2) : ℝ)) (incrementTerm A) := by
    have S := termBounds_scaled_abs (b := A.coeff) Pm
    have hu : 0 ≤ weightGrowthSup T.rt T.n₁ * (St.CE * R.coupling ^ (-(1 / 2) : ℝ)) :=
      mul_nonneg hG0 (mul_nonneg hCE0.le hxh0)
    have hm : ∀ u : ℝ, 0 ≤ u → u ≤ 2 * (weightGrowthSup T.rt T.n₁ * (St.CE * R.coupling ^ (-(1 / 2) : ℝ))) →
        |A.coeff| * u ≤ C * R.coupling ^ (-(1 / 2) : ℝ) := fun u h0 h1 => by
      calc |A.coeff| * u ≤ 2 * u := mul_le_mul_of_nonneg_right hal h0
        _ ≤ 2 * (2 * (weightGrowthSup T.rt T.n₁ * (St.CE * R.coupling ^ (-(1 / 2) : ℝ)))) := by linarith
        _ = (4 * weightGrowthSup T.rt T.n₁ * T.CE) * R.coupling ^ (-(1 / 2) : ℝ) := by
          show 2 * (2 * (weightGrowthSup T.rt T.n₁ * (T.CE * R.coupling ^ (-(1 / 2) : ℝ)))) = _
          ring
        _ ≤ C * R.coupling ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_right hC1 hxh0
    exact termBounds_mono (hm _ hu (by linarith)) (hm _ hu (by linarith)) (hm _ (by linarith) le_rfl) S
  exact ⟨Pframe, Pslope, Pmove, Ptails⟩
end YangMills.Construction.ResponseInTheExpansion
end
