import YangMills.Construction.ClusterExpansionOfAStep.DensitiesInCoordinatesForm
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfTheDensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.RegionOffTheHotLumpsIsRegular
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepSettings
open BlockAverages TorusFields TorusLumps LevelAction RenormalizationStepParameters FieldMoves BondCoordinates ExponentialSums HotLumps
variable {S : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting S n}
theorem actionSmooth_of_levelBound (h : s.Hypotheses) {a : ℝ} {L : ℕ} {σA δ C : ℝ}
    (ha : S.params.coupling = a) (hL : S.params.side = L) (hδ : 0 < δ)
    (hC0 : 0 < C)
    (hact : ∀ (t m : ℕ) [NeZero m], 64 ≤ m → ∀ (X : Finset (TorusSite m)) (W : TorusField m),
      IsRegularRegion X 1024 → IsColdOn σA X W →
        ContDiffThreeAt (actionAtLevel a L t X) W ∧
        (∀ (k : ℕ) (c : Fin k → TorusBond m) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors Xs →
          |mixedDeriv (actionAtLevel a L t X) W c Xs| ≤ C * Real.exp (-δ * bondListSpread c)))
    (hreg : IsRegularRegion s.outsideHot 1024)
    (hcold : ∀ θ W, s.IsNear θ W → IsColdOn σA s.outsideHot W) :
    s.ActionSmooth C := by
  intro θ W hθ hnear k c X hc
  have hN : 64 ≤ n * S.params.side := by
    have h1 := h.n₀_le
    have h2 := h.admissible.n₀_ge
    have h3 := h.side_pos
    have : n ≤ n * S.params.side := Nat.le_mul_of_pos_right _ h3
    omega
  obtain ⟨h1, h2⟩ := hact S.depth (n * S.params.side) hN s.outsideHot W hreg (hcold θ W hnear)
  rw [← ha, ← hL] at h1 h2
  refine ⟨h1 k c X, fun hk1 hk3 hu => ?_⟩
  refine (h2 k c X (by omega) hk3 hu).trans ?_
  have : Real.exp (-δ * bondListSpread c) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : (0 : ℝ) ≤ bondListSpread c := by positivity
    nlinarith)
  nlinarith
theorem isColdOn_outsideHot (hadm : S.params.Admissible) {σA : ℝ} (hσ : S.params.threshold ≤ σA)
    {W : TorusField (n * S.params.side)}
    (hW : torusHotSites S.params W = torusHotSites S.params s.fine) : IsColdOn σA s.outsideHot W := by
  intro p hp
  obtain ⟨hlt, hc⟩ := mem_plaquettesIn.mp hp
  by_contra hcon
  have hge : S.params.threshold ≤ curvature W p.1 p.2.1 p.2.2 := hσ.trans (not_lt.mp hcon)
  have hz := mem_torusHotSites_of_mem_plaquetteVertices hadm (Dvd.intro_left n rfl) hlt hge
    (base_mem_plaquetteVertices p.1 p.2.1 p.2.2)
  rw [hW] at hz
  have h1 := hc p.1 (base_mem_plaquetteVertices p.1 p.2.1 p.2.2)
  exact (Finset.mem_sdiff.mp h1).2
    ((mem_thickening _ _ _).mpr ⟨_, hz, by rw [supDist_self]; exact Nat.zero_le _⟩)
theorem exp_neg_mul_div_eight_le {δ r : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r) :
    Real.exp (-δ * r / 8) ≤ Real.exp (-δ * r / 64) :=
  Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hδ.le hr])
theorem tail_poly_le {D τ M Q x3 : ℝ} (hD : 0 ≤ D) (hτ : 0 < τ) (hM : M ≤ Q * x3) (hx : 1 ≤ x3) :
    D / τ ^ 2 + 2 * M * τ ≤ (D / τ ^ 2 + 2 * Q * τ) * x3 := by
  have h1 : 0 ≤ D / τ ^ 2 := by positivity
  have h2 : D / τ ^ 2 ≤ D / τ ^ 2 * x3 := by nlinarith
  have h3 : 2 * M * τ ≤ 2 * (Q * x3) * τ := by nlinarith
  have e : (D / τ ^ 2 + 2 * Q * τ) * x3 = D / τ ^ 2 * x3 + 2 * (Q * x3) * τ := by ring
  rw [e]
  linarith
theorem first_poly_le {D τ M Q x3 : ℝ} (hD : 0 ≤ D) (hτ : 0 < τ) (hM : M ≤ Q * x3) (hx : 1 ≤ x3) :
    D / τ + M * τ ≤ (D / τ + Q * τ) * x3 := by
  have h1 : 0 ≤ D / τ := by positivity
  have h2 : D / τ ≤ D / τ * x3 := by nlinarith
  have h3 : M * τ ≤ (Q * x3) * τ := by nlinarith
  have e : (D / τ + Q * τ) * x3 = D / τ * x3 + (Q * x3) * τ := by ring
  rw [e]
  linarith
theorem totalDensityPieceBound_holds (hAct : ActionSmoothAlongMoves)
    (hreg : OffHotRegionIsRegular) :
    totalDensityPieceBound := by
  intro T hT
  have chain := hT.chain
  have hρ0 : 0 < T.ρA := chain.2.2.2.1
  have hρ1 : T.ρA ≤ 1 := chain.2.2.2.2.1
  have hσ := hT.σ_pos
  have hrt := hT.rt_pos
  obtain ⟨CA, hCA, hact⟩ := hAct T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N
    (by linarith [hT.a_ge]) hT.L_odd chain
  obtain ⟨Cξ, hCξ, hξ⟩ := exists_bound_deriv_bondLogMove
  obtain ⟨τ, hτ, hstep⟩ := exists_expUnit_near_one (ε := T.threshold / 64) (by positivity)
  set δ₂ : ℝ := T.rt / 2 ^ 12 with hδ₂
  set rate : ℝ := T.rt / 2 ^ 10 with hrate
  set D : ℝ := 4 * Real.exp (3 * δ₂) * expLatticeSum (δ₂ / 2) with hD
  set Z : ℝ := Real.exp (2 * T.rt) * (4 * expLatticeSum (δ₂ / 64)) with hZ
  set Q₃ : ℝ := T.derivBound ^ 3 + CA + T.E₃ * expLatticeSum rate with hQ₃
  set Q₂ : ℝ := T.derivBound ^ 2 + CA + T.E * expLatticeSum rate with hQ₂
  set P₁ : ℝ := D / τ ^ 2 + 2 * Q₃ * τ with hP₁
  set P₂ : ℝ := D / τ + Q₂ * τ with hP₂
  set C₀ : ℝ := 2 * (T.E * expLatticeSum (rate / 2)) * Cξ ^ 2 * Z + T.E * expLatticeSum rate * Cξ
    with hC₀
  set P : ℝ := 2 * P₁ * Cξ ^ 2 * Z + P₂ * Cξ with hP
  set B : ℕ := 2 ^ 20 * (T.side + T.n₀ + 1) with hB
  refine ⟨max C₀ 4, δ₂ / 64, max T.floorMin (max P (max 1 ((B : ℝ) ^ 100))), by positivity,
    by positivity, ?_⟩
  intro y hy S hS n _ hn s hs
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hxy : y ≤ S.coupling := hS.le_coupling
  have hxP : P ≤ S.coupling := ((le_max_left _ _).trans ((le_max_right _ _).trans hy)).trans hxy
  have hx1 : 1 ≤ S.coupling :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))).trans hxy
  have hxB : (B : ℝ) ^ 100 ≤ S.coupling :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))).trans hxy
  have hadm : S.params.Admissible := by
    rw [hS.params_eq]
    exact hT.fits y hy0
  have ea : S.params.coupling = T.coupling := by rw [hS.params_eq]; rfl
  have eL : S.params.side = T.side := by rw [hS.params_eq]; rfl
  have en : S.params.n₀ = T.n₀ := by rw [hS.params_eq]; rfl
  have eσ : S.params.threshold = T.threshold := by rw [hS.params_eq]; rfl
  have ert : S.params.rt = T.rt := by rw [hS.params_eq]; rfl
  have eE : S.params.E = T.E := by rw [hS.params_eq]; rfl
  have eE₃ : S.params.E₃ = T.E₃ := by rw [hS.params_eq]; rfl
  have eCd : S.params.derivBound = T.derivBound := by rw [hS.params_eq]; rfl
  have eF : S.params.decayRate = δ₂ := by
    unfold StepParameters.decayRate
    rw [ert]
  have eR : S.params.weightRate = rate := by
    unfold StepParameters.weightRate
    rw [ert]
  have hbig : 2 ^ 20 * (S.params.side + S.params.n₀ + 1) ≤ S.range := by
    rw [eL, en]
    exact le_clusterRange hxB
  have hrow := hS.isStep.1
  have h : s.Hypotheses := ⟨hadm, hrow.1, hrow.2, hs, hbig, by rw [en]; exact hn⟩
  have hσA : S.params.threshold ≤ T.σA := by
    rw [eσ]
    have := hT.σ_le
    linarith
  have hA : s.ActionSmooth CA := actionSmooth_of_levelBound h ea eL chain.1 hCA
    (fun t m _ h64 X W a b => by
      obtain ⟨c1, c2, -⟩ := hact t m h64 X W a b
      exact ⟨c1, c2⟩)
    (hreg S.params n s.fine hadm)
    (fun θ W hnear => isColdOn_outsideHot hadm hσA (by
      unfold torusHotSites
      rw [hnear.torusHotLumps_eq]))
  have hρS : S.anchorRadius = T.ρA := hS.anchorRadius_eq
  have hw : ∀ η, s.InBalls η → ∀ b, ‖s.pointAt η b‖ ≤ 3 := fun η hη b =>
    h.norm_pointAt_le (by rw [hρS]; exact hρ0.le) (by rw [hρS]; exact hρ1)
      (by rw [eσ]; exact hT.σ_one) hη b
  have hL19 : 2 ^ 19 ≤ S.params.side := by
    rw [eL]
    have := hT.L_ge
    omega
  have hx0 : 0 ≤ S.coupling := by linarith
  have hCd : 0 ≤ S.params.derivBound := by
    have := hadm.Cder_ge
    linarith
  have hstep' : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ →
      ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ S.params.threshold / 64 := by
    rw [eσ]
    exact hstep
  have piece := h.isPotentialPiece_totalDensity hA hCA.le hτ hstep' hx0 hCd hCξ hξ hw hL19
  refine piece.mono ?_
  have hδ := decayRate_pos h
  have hDS : S.differenceConstant = D := by
    unfold StepSetup.differenceConstant
    rw [eF]
  have hDnn : 0 ≤ D := by
    rw [← hDS]
    exact differenceConstant_nonneg h
  have hLr : 0 < expLatticeSum rate := by
    rw [← eR]
    exact expLatticeSum_pos (weightRate_pos h)
  have hE := hadm.E_pos
  have hE₃ := hadm.E₃_pos
  have x3 : 1 ≤ S.coupling ^ 3 := one_le_pow₀ hx1
  have hT₁ : S.tailConstant τ CA ≤ P₁ * S.coupling ^ 3 := by
    unfold StepSetup.tailConstant
    rw [hDS, eCd, eE₃, eR]
    refine tail_poly_le hDnn hτ ?_ x3
    have hb1 : 0 ≤ T.derivBound := by rwa [← eCd]
    exact cube_poly_le hb1 hCA.le (by rw [← eE₃]; positivity) hx1
  have hF₁ : S.firstTailConstant τ CA ≤ P₂ * S.coupling ^ 3 := by
    unfold StepSetup.firstTailConstant
    rw [hDS, eCd, eE, eR]
    refine first_poly_le hDnn hτ ?_ x3
    have hb1 : 0 ≤ T.derivBound := by rwa [← eCd]
    exact square_poly_le hb1 hCA.le (by rw [← eE]; positivity) hx1
  have hF0 : 0 ≤ S.firstTailConstant τ CA := by
    have hLr' : 0 < expLatticeSum S.params.weightRate := expLatticeSum_pos (weightRate_pos h)
    have hD' := differenceConstant_nonneg h
    unfold StepSetup.firstTailConstant
    positivity
  have hLc : 0 < expLatticeSum (S.params.decayRate / 64) := expLatticeSum_pos (by linarith)
  have hr0 : (0 : ℝ) ≤ (S.range : ℝ) := by positivity
  have hg : Real.exp (-S.params.decayRate * S.range / 8) ≤
      Real.exp (-S.params.decayRate * S.range / 64) := exp_neg_mul_div_eight_le hδ hr0
  have eg : Real.exp (-(δ₂ / 64) * (S.range : ℝ)) =
      Real.exp (-S.params.decayRate * S.range / 64) := by
    rw [eF]
    congr 1
    ring
  rw [eg]
  have hLe : 0 ≤ S.params.E * expLatticeSum S.params.weightRate := by
    have := expLatticeSum_pos (weightRate_pos h)
    positivity
  refine potential_size_arith (mainConstant_nonneg h) hLe hCξ (by positivity) hT₁ hF₁
    (Real.exp_pos _) (Real.exp_pos _) hg hF0
    (C₀ := C₀) (P := P) ?_ (by rw [ert, eF]) hxP hx1 (le_max_left _ _) (le_max_right _ _) ?_
  · rw [hC₀, hZ]
    unfold StepSetup.mainConstant
    rw [eE, eR, ert, eF]
  · rw [← eE₃]
    exact hE₃.le
end YangMills.Construction.StepSettings
end
