import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.ResponseInTheExpansion.MassOfALevel
import YangMills.Construction.ResponseInTheExpansion.MomentsAlongTheLevels
import YangMills.Construction.ResponseInTheExpansion.ResponsesAreLinear
import YangMills.Construction.SixteenPointsOnASmallTorus.CentringIsTheSumOfTheShifts
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAboutASite
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtTheLevelOfTheirRadius
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesHaveOneCentring
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesStandApart
import YangMills.Construction.SixteenPointsOnASmallTorus.ErrorOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfARadius
import YangMills.Construction.SixteenPointsOnASmallTorus.ResponseOfACopyIsBounded
import YangMills.Construction.SixteenPointsOnASmallTorus.SitesOfACopy
import YangMills.Construction.SixteenPointsOnASmallTorus.SizeOfACopy
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps RenormalizationStepParameters StepSettings ClusterExpansionOfAStep WeightedResponses ResponseInTheExpansion TestFunctions
section Scores
variable {n : ℕ} [NeZero n] {Ω : Type}
omit [NeZero n] in
private theorem siteScore_nonneg_aux {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (Y : Finset (TorusSite n)) (ω : Y → Ω)
    (y : TorusSite n) : 0 ≤ siteScore s Y ω y := by
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p42827 := @siteScore_nonneg_aux
private theorem one_le_meanSiteScore_aux {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (B Y : Finset (TorusSite n)) (ω : Y → Ω) :
    1 ≤ meanSiteScore s B Y ω := by apply _root_.YangMills.SharedProofs.p16546 <;> assumption
end Scores
section States
private theorem abs_stateIntegral_le_aux {R : StepSetup} {n : ℕ} [NeZero n] (H : StateFunction R n)
    (hD : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω),
      IsHullState R.params (clusterRange R.coupling) W Y → 0 ≤ R.labelWeight n W Y ω) :
    ENNReal.ofReal |stateIntegral R n H| ≤ stateLIntegral R n fun W Y ω => |H W Y ω| := by
  classical
  unfold stateIntegral stateLIntegral
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono fun W => ?_
  refine (enorm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun Y hY => ?_
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hD W Y ω (Finset.mem_filter.mp hY).2)]
private theorem stateLIntegral_le_mul_aux {R : StepSetup} {n : ℕ} [NeZero n] {H H' : StateFunction R n} {c : ℝ}
    (hc : 0 ≤ c) (hH : ∀ W Y ω, 0 ≤ H W Y ω)
    (h : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω),
      IsLiveState R.params R.coupling R.labelWeight W Y ω → H W Y ω ≤ c * H' W Y ω) :
    stateLIntegral R n H ≤ ENNReal.ofReal c * stateLIntegral R n H' := by
  classical
  unfold stateLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun W => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Y hY => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have hY' := (Finset.mem_filter.mp hY).2
  by_cases hq : 0 < R.labelWeight n W Y ω
  · rw [← ENNReal.ofReal_mul hc]
    apply ENNReal.ofReal_le_ofReal
    have := h W Y ω ⟨hY', hq⟩
    nlinarith
  · have h0 : R.labelWeight n W Y ω * H W Y ω ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) (hH W Y ω)
    rw [ENNReal.ofReal_of_nonpos h0]
    exact bot_le
private theorem labelWeight_nonneg_aux {R : StepSetup} (hrow : R.HasExpansions) (hfit : R.params.Admissible) {n : ℕ}
    [NeZero n] (hs : IsBlockTorusSide R.params n) (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω)
    (hY : IsHullState R.params (clusterRange R.coupling) W Y) : 0 ≤ R.labelWeight n W Y ω := by
  have hflat : IsCold R.params.threshold (trivialField n) := fun x μ ν _ => by
    simpa [curvature, holonomy, trivialField] using hfit.σ_pos
  have hn : R.params.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 * R.params.n₀ ≤ R.params.side * R.params.n₀ :=
      Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
    omega
  have hD1 : 0 < R.functional n (trivialField n) := hrow.1.positive n hn _ hflat
  rw [hrow.2.form n hs W Y ω hY]
  exact mul_nonneg (mul_nonneg hD1.le (Real.exp_pos _).le)
    (Finset.prod_nonneg fun X _ => hrow.2.factor_nonneg n hs W Y ω X)
private theorem abs_div_le_of_ofReal_aux {a Z V : ℝ} (hZ : 0 < Z) (hV : 0 ≤ V)
    (h : ENNReal.ofReal |a| ≤ ENNReal.ofReal V * ENNReal.ofReal Z) : |a / Z| ≤ V := by
  rw [← ENNReal.ofReal_mul hV, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  exact h
end States
section Weights
private theorem weightSupportSites_congr_depth {L : ℕ} [NeZero L] {t t' : ℕ} (e : t = t') (n : ℕ) [NeZero n]
    (w : (m : ℕ) → PlaquetteWeight m) :
    weightSupportSites L t n (w _) = weightSupportSites L t' n (w _) := by
  subst e
  rfl
private theorem weightNorm_congr_depth {L : ℕ} [NeZero L] {t t' : ℕ} (e : t = t') (n : ℕ) [NeZero n]
    (w : (m : ℕ) → PlaquetteWeight m) :
    weightNorm L t (m := fineSide L t n) (w _) = weightNorm L t' (m := fineSide L t' n) (w _) := by
  subst e
  rfl
private theorem productMean_congr_side {m m' : ℕ} [NeZero m] [NeZero m'] (e : m = m') (β a₀ : ℝ) (M : ℕ)
    (h : EuclideanFourSpace → ℝ) (c : ℝ) :
    ∫ W, ∏ k : Fin 4 → Fin 2, (curvatureObservable (reflectedWeight (m := m) a₀ M (fun μ => (k μ : ℕ)) h) W - c)
        ∂(wilsonLaw β m) =
      ∫ W, ∏ k : Fin 4 → Fin 2, (curvatureObservable (reflectedWeight (m := m') a₀ M (fun μ => (k μ : ℕ)) h) W - c)
        ∂(wilsonLaw β m') := by
  subst e
  rfl
private theorem reflectedProductMean_origin (β a₀ : ℝ) (M : ℕ) [NeZero M] (h : EuclideanFourSpace → ℝ) (c : ℝ) :
    reflectedProductMean β a₀ M 2 0 h c =
      ∫ W, ∏ k : Fin 4 → Fin 2,
        (curvatureObservable (reflectedWeight (m := 2 * M) a₀ M (fun μ => (k μ : ℕ)) h) W - c) ∂(wilsonLaw β (2 * M)) := by
  unfold reflectedProductMean
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  refine Finset.prod_congr rfl fun k _ => ?_
  have e : reflectedWeightAbout a₀ M (0 : TorusSite (2 * M)) (fun μ => (k μ : ℕ)) h =
      reflectedWeight a₀ M (fun μ => (k μ : ℕ)) h := by
    funext p
    simp [reflectedWeightAbout, translateWeight]
  rw [e]
private theorem curvatureObservable_smul {m : ℕ} [NeZero m] (c : ℝ) (w : PlaquetteWeight m) (W : TorusField m) :
    curvatureObservable (fun p => c * w p) W = c * curvatureObservable w W := by
  unfold curvatureObservable
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring
private theorem card_corners : (Finset.univ : Finset (Fin 4 → Fin 2)).card = 16 := by
  simp
private theorem reflectedProductMean_smul (β a₀ : ℝ) (M : ℕ) [NeZero M] (h : EuclideanFourSpace → ℝ) (c e : ℝ) :
    reflectedProductMean β a₀ M 2 0 (fun x => c * h x) (c * e) = c ^ 16 * reflectedProductMean β a₀ M 2 0 h e := by
  rw [reflectedProductMean_origin, reflectedProductMean_origin, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  have e₁ : ∀ k : Fin 4 → Fin 2,
      curvatureObservable (reflectedWeight (m := 2 * M) a₀ M (fun μ => (k μ : ℕ)) fun x => c * h x) W - c * e =
        c * (curvatureObservable (reflectedWeight (m := 2 * M) a₀ M (fun μ => (k μ : ℕ)) h) W - e) := fun k => by
    have := curvatureObservable_smul c (reflectedWeight (m := 2 * M) a₀ M (fun μ => (k μ : ℕ)) h) W
    have e₂ : (fun p => c * reflectedWeight (m := 2 * M) a₀ M (fun μ => (k μ : ℕ)) h p) =
        reflectedWeight (m := 2 * M) a₀ M (fun μ => (k μ : ℕ)) fun x => c * h x := rfl
    rw [e₂] at this
    rw [this]
    ring
  simp only [e₁]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_corners]
private theorem centring_smul_aux (hlin : ResponseLinearLocalStatement) {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (β : ℝ) (al : ℕ → ℝ) (K κ : ℕ) (ρ : ℝ) (h : EuclideanFourSpace → ℝ) (c : ℝ) :
    centring ℓ β al K κ ρ (fun x => c * h x) = c * centring ℓ β al K κ ρ h := by
  unfold centring reflectedCentring
  cases radiusLevel ℓ β K ρ with
  | none => simp
  | some s =>
    simp only
    unfold meanAtTrivial
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    have h1 := (hlin ℓ hfit β (flowCouplings ℓ β) al s (twoCellSide ℓ.side κ s) Y).1 c 0
      (reflectedWeight (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 0 h)
      (reflectedWeight (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 0 h) (trivialField _)
    have e : (fun p => c * reflectedWeight (m := fineSide ℓ.side s (twoCellSide ℓ.side κ s))
          (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 0 h p +
        0 * reflectedWeight (m := fineSide ℓ.side s (twoCellSide ℓ.side κ s))
          (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 0 h p) =
        reflectedWeight (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 0 fun x => c * h x := by
      funext p
      simp [reflectedWeight]
    rw [e] at h1
    rw [h1]
    ring
private theorem weightSupportSites_smul {L : ℕ} [NeZero L] (t n : ℕ) [NeZero n] {c : ℝ} (hc : c ≠ 0) (a₀ : ℝ) (M : ℕ)
    (k : Fin 4 → ℕ) (h : EuclideanFourSpace → ℝ) :
    weightSupportSites L t n (reflectedWeight a₀ M k fun x => c * h x) =
      weightSupportSites L t n (reflectedWeight a₀ M k h) := by
  have e : ∀ p : TorusPlaquette (fineSide L t n),
      (reflectedWeight (m := fineSide L t n) a₀ M k (fun x => c * h x) p ≠ 0) ↔
        (reflectedWeight (m := fineSide L t n) a₀ M k h p ≠ 0) := fun p => by
    simp [reflectedWeight, hc]
  unfold weightSupportSites
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
private theorem localizedSource_smul {l ρ H : ℝ} {Λ : NNReal} {h : EuclideanFourSpace → ℝ} {c : ℝ} (hc : 0 < c)
    (hs : IsLocalizedSource l ρ H Λ h) :
    IsLocalizedSource l ρ (c * H) (Real.toNNReal c * Λ) fun x => c * h x := by
  refine ⟨?_, fun x => ?_, ?_, fun x hx => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h1 := hs.lipschitz.dist_le_mul u v
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, ← Real.dist_eq]
    push_cast
    rw [Real.coe_toNNReal _ hc.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hc.le
  · rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hs.abs_le x) hc.le
  · obtain ⟨p, hp⟩ := hs.exists_ball
    exact ⟨p, fun x hx => hp x (right_ne_zero_of_mul hx)⟩
  · exact hs.away_from_faces x (right_ne_zero_of_mul hx)
private theorem sourceNorm_smul {ρ H : ℝ} {Λ : NNReal} {c : ℝ} (hc : 0 < c) :
    sourceNorm ρ (c * H) ((Real.toNNReal c * Λ : NNReal) : ℝ) = c * sourceNorm ρ H Λ := by
  unfold sourceNorm
  push_cast
  rw [Real.coe_toNNReal _ hc.le, mul_max_of_nonneg _ _ hc.le]
  congr 1
  ring
private theorem pow_sixteen_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 16 + b ≤ (a + b + 1) ^ 16 := by
  set u := a + b + 1 with hu
  have h1 : 1 ≤ u := by linarith
  have h2 : a ^ 15 ≤ u ^ 15 := pow_le_pow_left₀ ha (by linarith) 15
  have h3 : 1 ≤ u ^ 15 := one_le_pow₀ h1
  have e : u ^ 16 = u ^ 15 * a + u ^ 15 * (b + 1) := by
    rw [pow_succ u 15, ← mul_add]
    congr 1
    rw [hu]
    ring
  rw [e]
  have e₂ : a ^ 16 = a ^ 15 * a := pow_succ a 15
  rw [e₂]
  have h4 : a ^ 15 * a ≤ u ^ 15 * a := mul_le_mul_of_nonneg_right h2 ha
  have h5 : 1 * (b + 1) ≤ u ^ 15 * (b + 1) := mul_le_mul_of_nonneg_right h3 (by linarith)
  linarith
end Weights
section Separation
variable {ℓ : StepParameters} {hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup} {lam : ℝ} {x : ℕ → ℝ}
  {z₀ : StageWithResponse ℓ}
private theorem separatedAlong_of_gaps {ι : Type} (I : Finset ι) (D : ℕ → ℕ) (w : ι → (m : ℕ) → PlaquetteWeight m)
    (κ : ℕ) :
    ∀ (s n : ℕ) [NeZero n], s ≤ κ → n = twoCellSide ℓ.side κ s →
      (∀ t < s, (stageStep hL lam x z₀ t).depth = t ∧ 2 ^ 10 * (stageStep hL lam x z₀ t).range ≤ D t ∧ 8 < D t ∧
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ∀ Y ∈ thickening 2 (weightSupportSites ℓ.side (t + 1) (twoCellSide ℓ.side κ (t + 1)) (w i _)),
          ∀ Y' ∈ thickening 2 (weightSupportSites ℓ.side (t + 1) (twoCellSide ℓ.side κ (t + 1)) (w j _)),
            D t ≤ supDist Y Y') →
      SeparatedAlong hL lam x z₀ I D s n (fun i => w i _) := by
  intro s
  induction s with
  | zero => intro n _ _ _ _; trivial
  | succ s ih =>
    intro n _ hsκ hn hD
    obtain ⟨h₁, h₂, h₃, h₅⟩ := hD s (by omega)
    have hnL : n * ℓ.side = twoCellSide ℓ.side κ s := by
      rw [hn]
      unfold twoCellSide
      have e : κ - s = κ - (s + 1) + 1 := by omega
      rw [e, pow_succ]
      ring
    refine ⟨ih (n * ℓ.side) (by omega) hnL fun t ht => hD t (by omega), h₂, h₃, fun i hi j hj hij Y hY Y' hY' => ?_⟩
    subst hn
    have hY₁ : Y ∈ thickening 2 (weightSupportSites ℓ.side (s + 1) (twoCellSide ℓ.side κ (s + 1)) (w i _)) := by
      rw [← weightSupportSites_congr_depth (congrArg (· + 1) h₁) (twoCellSide ℓ.side κ (s + 1)) (w i)]
      exact hY
    have hY₂ : Y' ∈ thickening 2 (weightSupportSites ℓ.side (s + 1) (twoCellSide ℓ.side κ (s + 1)) (w j _)) := by
      rw [← weightSupportSites_congr_depth (congrArg (· + 1) h₁) (twoCellSide ℓ.side κ (s + 1)) (w j)]
      exact hY'
    exact h₅ i hi j hj hij Y hY₁ Y' hY₂
end Separation
section Spacing
private theorem levelSpacing_pos_aux {L : ℕ} (hL : 1 ≤ L) (K t : ℕ) : 0 < levelSpacing L K t := by
  unfold levelSpacing
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity
private theorem levelSpacing_le_one_aux {L : ℕ} (hL : 1 ≤ L) {K t : ℕ} (h : t ≤ K) : levelSpacing L K t ≤ 1 := by
  unfold levelSpacing
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (t : ℤ) - (K : ℤ) ≤ 0 := by omega
  calc (L : ℝ) ^ ((t : ℤ) - (K : ℤ)) ≤ (L : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ h1 h2
    _ = 1 := zpow_zero _
private theorem levelSpacing_succ_aux {L : ℕ} (hL : 1 ≤ L) (K t : ℕ) :
    levelSpacing L K (t + 1) = L * levelSpacing L K t := by
  unfold levelSpacing
  have h1 : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    exact this.ne'
  rw [show (((t + 1 : ℕ) : ℤ) - (K : ℤ)) = 1 + ((t : ℤ) - (K : ℤ)) by push_cast; ring, zpow_add₀ h1, zpow_one]
private theorem levelSpacing_self_aux {L : ℕ} (K : ℕ) : levelSpacing L K K = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
private theorem floor_gap_bounds {ρ a : ℝ} {r r' d : ℕ} (ha : 0 < a) (hfit : 2 ^ 11 * (r' : ℝ) * a ≤ ρ) (hr' : 1 ≤ r')
    (hrr : r ≤ r' + 1) :
    2 ^ 10 * r ≤ ⌊ρ / a⌋₊ ∧ 8 < ⌊ρ / a⌋₊ ∧ (2 * (ρ / a) - 6 ≤ d → ⌊ρ / a⌋₊ ≤ d) := by
  have h1 : 2 ^ 11 * (r' : ℝ) ≤ ρ / a := by
    rw [le_div_iff₀ ha]
    exact hfit
  have hr'1 : (1 : ℝ) ≤ r' := by exact_mod_cast hr'
  have hrr' : (r : ℝ) ≤ r' + 1 := by exact_mod_cast hrr
  have hX : (0 : ℝ) ≤ ρ / a := by nlinarith
  refine ⟨?_, ?_, fun hd => ?_⟩
  · apply Nat.le_floor
    push_cast
    nlinarith
  · have : 9 ≤ ⌊ρ / a⌋₊ := by
      apply Nat.le_floor
      push_cast
      nlinarith
    omega
  · have h2 : ((⌊ρ / a⌋₊ : ℕ) : ℝ) ≤ ρ / a := Nat.floor_le hX
    have h3 : ((⌊ρ / a⌋₊ : ℕ) : ℝ) ≤ d := by nlinarith
    exact_mod_cast h3
end Spacing
section Moment
variable {T : ParameterAssignment} {Kr : ResponseParameters} {y β : ℝ}
  {hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup} {z₀ : StageWithResponse (T.stepParameters y)}
open Classical in
private theorem abs_normalizedMoment_le {s n : ℕ} [NeZero n] {Ab Eb R : ℝ} {Cn : ℕ → ℝ} {D : ℕ → ℕ}
    (hfit : (T.stepParameters y).Admissible) (hs : StageOnFlow T Kr y β s (flowStages T y β hL z₀ s))
    (hbs : IsBlockTorusSide (T.stepParameters y) n) (hAb : 0 ≤ Ab) (hEb : 0 ≤ Eb) (hR : 0 ≤ R)
    (f : (Fin 4 → Fin 2) → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n)
    (hM3 : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (flowStages T y β hL z₀ s).1.labels.Ω),
      IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ s).1.coupling (flowStages T y β hL z₀ s).1.labelWeight
        W Y ω →
      |jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f W Y ω -
          ∏ i ∈ Finset.univ, supportResponseTotal (flowStages T y β hL z₀ s).2 (f i) W Y ω| ≤
        momentError hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ T.gasRate Cn D s n Finset.univ f *
          ∏ i ∈ Finset.univ, meanSiteScore (flowStages T y β hL z₀ s).2.score
            (weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)) Y ω)
    (hF : ∀ (i : Fin 4 → Fin 2) (W : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → (flowStages T y β hL z₀ s).1.labels.Ω),
      IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ s).1.coupling (flowStages T y β hL z₀ s).1.labelWeight
        W Y ω →
      |supportResponseTotal (flowStages T y β hL z₀ s).2 (f i) W Y ω| ≤
        Kr.C₀ * ((weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)).card : ℝ) *
          meanSiteScore (flowStages T y β hL z₀ s).2.score
            (weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)) Y ω)
    (hErr : momentError hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ T.gasRate Cn D s n Finset.univ f ≤ Eb)
    (hA : ∏ i : Fin 4 → Fin 2,
        (Kr.C₀ * ((weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)).card : ℝ)) ≤ Ab)
    (hMaj : stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup n (fun _ Y ω => ∏ i : Fin 4 → Fin 2,
        meanSiteScore (flowStages T y β hL z₀ s).2.score
          (weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)) Y ω) ≤
      ENNReal.ofReal R * stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1)
    (hPos : 0 < stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1)
    (hOf : ENNReal.ofReal (stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1) =
      stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1) :
    |stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n
        (jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f) /
      stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1| ≤ (Ab + Eb) * R := by
  set Rs := (flowStages T y β hL z₀ s).1.toStepSetup with hRs
  set As := (flowStages T y β hL z₀ s).2 with hAs
  have hresp : As.IsAdmissible := hs.onFamily.admissible
  have hrow : Rs.HasExpansions := hs.onFamily.onFamily.isStep.1
  have hsc := hresp.price.nonneg
  set sites : (Fin 4 → Fin 2) → Finset (TorusSite n) := fun i =>
    weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i) with hsites
  set N : StateFunction Rs n := fun _ Y ω => ∏ i : Fin 4 → Fin 2, meanSiteScore As.score (sites i) Y ω with hN
  have hN1 : ∀ W Y ω, 1 ≤ N W Y ω := fun W Y ω => by
    simp only [hN]
    calc (1 : ℝ) = ∏ _i : Fin 4 → Fin 2, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => one_le_meanSiteScore_aux hsc _ _ _
  have hN0 : ∀ W Y ω, 0 ≤ N W Y ω := fun W Y ω => by linarith [hN1 W Y ω]
  have hpoint : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Rs.labels.Ω),
      IsLiveState Rs.params Rs.coupling Rs.labelWeight W Y ω →
      |jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f W Y ω| ≤
        (Ab + Eb) * N W Y ω := by
    intro W Y ω hq
    have h₁ := hM3 W Y ω hq
    have h₂ : |∏ i : Fin 4 → Fin 2, supportResponseTotal As (f i) W Y ω| ≤ Ab * N W Y ω := by
      rw [Finset.abs_prod]
      have h₃ : ∏ i : Fin 4 → Fin 2, |supportResponseTotal As (f i) W Y ω| ≤
          ∏ i : Fin 4 → Fin 2, (Kr.C₀ * ((sites i).card : ℝ) * meanSiteScore As.score (sites i) Y ω) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hF i W Y ω hq
      refine h₃.trans ?_
      rw [Finset.prod_mul_distrib]
      exact mul_le_mul_of_nonneg_right hA (hN0 W Y ω)
    have h₄ : momentError hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ T.gasRate Cn D s n Finset.univ f *
        N W Y ω ≤ Eb * N W Y ω :=
      mul_le_mul_of_nonneg_right hErr (hN0 W Y ω)
    have h₅ := abs_sub_abs_le_abs_sub
      (jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f W Y ω)
      (∏ i : Fin 4 → Fin 2, supportResponseTotal As (f i) W Y ω)
    nlinarith
  have hDq : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Rs.labels.Ω),
      IsHullState Rs.params (clusterRange Rs.coupling) W Y → 0 ≤ Rs.labelWeight n W Y ω :=
    fun W Y ω hY => labelWeight_nonneg_aux hrow hfit hbs W Y ω hY
  have c₁ := abs_stateIntegral_le_aux
    (jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f) hDq
  have c₂ : stateLIntegral Rs n
      (fun W Y ω => |jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f W Y ω|) ≤
      ENNReal.ofReal (Ab + Eb) * stateLIntegral Rs n N :=
    stateLIntegral_le_mul_aux (by linarith) (fun W Y ω => abs_nonneg _) hpoint
  have hV : 0 ≤ (Ab + Eb) * R := by positivity
  refine abs_div_le_of_ofReal_aux hPos hV ?_
  rw [hOf, ENNReal.ofReal_mul (by linarith)]
  refine c₁.trans (c₂.trans ?_)
  rw [mul_assoc]
  exact mul_le_mul' le_rfl hMaj
end Moment
section Inputs
private structure RadiusLevelInputs (T : ParameterAssignment) (Kr : ResponseParameters) (y Ξ : ℝ) (Cn : ℕ → ℝ) (Ce : ℝ) :
    Prop where
  admissible : (T.stepParameters y).Admissible
  C₀_nonneg : 0 ≤ Kr.C₀
  one_le_range : ∀ x : ℝ, y ≤ x → 1 ≤ clusterRange x
  range_close : ∀ x x' : ℝ, y ≤ x → |x' - x| ≤ 2 * T.B →
    clusterRange x ≤ clusterRange x' + 1 ∧ clusterRange x' ≤ clusterRange x + 1
  stages : ∀ (β : ℝ) (K κ : ℕ) (ρ : ℝ), IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ →
    ρ ≤ cellLength T.side K κ / 4 → ∀ s : ℕ, radiusLevel (T.stepParameters y) β K ρ = some s →
      s ≤ K ∧ ∀ t ≤ s, FitsAtLevel (T.stepParameters y) β K ρ t ∧ t < κ ∧
        2 ^ 13 * rangeAtLevel (T.stepParameters y) β t ≤ (T.side : ℝ) ^ (κ - t) ∧
        IsBlockTorusSide (T.stepParameters y) (twoCellSide T.side κ t)
  centring_copy : ∀ (β : ℝ) (K κ : ℕ) (al : ℕ → ℝ) (ρ H : ℝ) (Λ : NNReal) (h : EuclideanFourSpace → ℝ),
    IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength T.side K κ / 4 →
    IsLocalizedSource (cellLength T.side K κ) ρ H Λ h →
    ∀ k : Fin 4 → Fin 2, reflectedCentring (T.stepParameters y) β al K κ ρ (fun μ => (k μ : ℕ)) h =
      centring (T.stepParameters y) β al K κ ρ h
  meanAtTrivial_eq : ∀ (β : ℝ) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)), IsInitialStage T y β z₀ →
    ∀ s : ℕ, StagesOnFlowUpTo T Kr y β hL z₀ s → ∀ (n : ℕ) [NeZero n] (w : (m : ℕ) → PlaquetteWeight m),
      IsBlockTorusSide (T.stepParameters y) n →
      meanAtTrivial (T.stepParameters y) β (fun j => (flowStages T y β hL z₀ j).2.coeff) s n (w _) =
        accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n (w _)
  response_le : ∀ (β : ℝ) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)), IsInitialStage T y β z₀ →
    ∀ s : ℕ, StagesOnFlowUpTo T Kr y β hL z₀ s → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (T.stepParameters y) n →
    ∀ f : StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n,
      weightNorm (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth f ≤ 1 →
      ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (flowStages T y β hL z₀ s).1.labels.Ω),
        IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ s).1.coupling
          (flowStages T y β hL z₀ s).1.labelWeight W Y ω →
        |supportResponseTotal (flowStages T y β hL z₀ s).2 f W Y ω| ≤
          Kr.C₀ * ((weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n f).card : ℝ) *
            meanSiteScore (flowStages T y β hL z₀ s).2.score
              (weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n f) Y ω
  error_le : ∀ (β : ℝ) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)), IsInitialStage T y β z₀ →
    ∀ (K κ s : ℕ) (ρ H : ℝ) (Λ : NNReal) (h : EuclideanFourSpace → ℝ),
      IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength T.side K κ / 4 →
      IsLocalizedSource (cellLength T.side K κ) ρ H Λ h → radiusLevel (T.stepParameters y) β K ρ = some s →
      StagesOnFlowUpTo T Kr y β hL z₀ s →
      momentError hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ T.gasRate Cn
        (radiusInStageUnits T.side K ρ) s (twoCellSide T.side κ s) Finset.univ
        (reflectedWeightsAtStage T y β hL z₀ K κ s (twoCellSide T.side κ s) h) ≤ Ce
  moment_eq : ∀ (β : ℝ) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)),
      IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T Kr y β hL z₀ s → ∀ (n : ℕ) [NeZero n],
      IsBlockTorusSide (T.stepParameters y) n → ∀ (D : ℕ → ℕ)
        (f : (Fin 4 → Fin 2) → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n),
        SeparatedAlong hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ Finset.univ D s n f →
        ∫ W, ∏ i ∈ Finset.univ, (curvatureObservable (f i) W -
            accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n (f i))
          ∂(wilsonLaw β (fineSide (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n)) =
        stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n
            (jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f) /
          stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1
  product_approx : ∀ (β : ℝ) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)),
      IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T Kr y β hL z₀ s →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (T.stepParameters y) n → ∀ (D : ℕ → ℕ)
        (f : (Fin 4 → Fin 2) → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n),
        (∀ i ∈ (Finset.univ : Finset (Fin 4 → Fin 2)),
          weightNorm (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth (f i) ≤ 1) →
        SeparatedAlong hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ Finset.univ D s n f →
        ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (flowStages T y β hL z₀ s).1.labels.Ω),
          IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ s).1.coupling
            (flowStages T y β hL z₀ s).1.labelWeight W Y ω →
          |jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n Finset.univ f W Y ω -
              ∏ i ∈ Finset.univ, supportResponseTotal (flowStages T y β hL z₀ s).2 (f i) W Y ω| ≤
            momentError hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ T.gasRate Cn D s n Finset.univ f *
              ∏ i ∈ Finset.univ, meanSiteScore (flowStages T y β hL z₀ s).2.score
                (weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)) Y ω
  mass_pos : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = Kr → OnStepParameters T y A →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      0 < stateIntegral R n (fun _ _ _ => 1) ∧
        ENNReal.ofReal (stateIntegral R n fun _ _ _ => 1) = stateLIntegral R n fun _ _ _ => 1
variable {T : ParameterAssignment} {Kr : ResponseParameters} {y Ξ β : ℝ} {Cn : ℕ → ℝ} {Ce : ℝ}
  {hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup} {z₀ : StageWithResponse (T.stepParameters y)}
private theorem reflectedProductMean_le_of_half (hSites : reflectedWeightSupportStatement)
    (hApart : reflectedSupportsSeparatedStatement) (hSize : reflectedWeightNormBoundStatement)
    (F : RadiusLevelInputs T Kr y Ξ Cn Ce) (hCe : 0 ≤ Ce) (hfirst : IsInitialStage T y β z₀) {K κ s : ℕ} {ρ H : ℝ}
    {Λ : NNReal} {h : EuclideanFourSpace → ℝ}
    (hd : IsAdmissibleFlow (T.stepParameters y) Ξ β K) (hκ : 2 ≤ κ) (hρ : 0 < ρ) (hρl : ρ ≤ cellLength T.side K κ / 4)
    (hsrc : IsLocalizedSource (cellLength T.side K κ) ρ H Λ h) (hlev : radiusLevel (T.stepParameters y) β K ρ = some s)
    (hst : StagesOnFlowUpTo T Kr y β hL z₀ K) (hN : sourceNorm ρ H Λ ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R)
    (hmaj : stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s)
        (prodMeanSiteScores T y β hL z₀ K κ s (twoCellSide T.side κ s) h) ≤
      ENNReal.ofReal R * stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s)
        (fun _ _ _ => 1)) :
    reflectedProductMean β (levelSpacing T.side K 0) (T.side ^ κ) 2 0 h
        (centring (T.stepParameters y) β (fun j => (flowStages T y β hL z₀ j).2.coeff) K κ ρ h) ≤
      ((Kr.C₀ * (81 * (ρ / levelSpacing T.side K s) ^ 4)) ^ 16 + Ce) * R := by
  have hfit := F.admissible
  have hL1 : 1 ≤ T.side := by
    have := hfit.L_ge
    have e : (T.stepParameters y).side = T.side := rfl
    omega
  have hodd : Odd T.side := hfit.L_odd
  obtain ⟨hsK, hlv⟩ := F.stages β K κ ρ hd hκ hρ hρl s hlev
  obtain ⟨hfs, hsκ, -, hbs⟩ := hlv s le_rfl
  have hstand : StagesOnFlowUpTo T Kr y β hL z₀ s := fun t ht => hst t (ht.trans hsK)
  have hs := hst s hsK
  have htK : ∀ t ≤ K, (flowStages T y β hL z₀ t).1.depth = t := fun t ht => (hst t ht).depth_eq
  have hr1 : ∀ t ≤ K, (1 : ℝ) ≤ rangeAtLevel (T.stepParameters y) β t := fun t ht => by
    have := F.one_le_range _ (hd.coupling_ge t ht)
    unfold rangeAtLevel
    exact_mod_cast this
  have has : 0 < levelSpacing T.side K s := levelSpacing_pos_aux hL1 K s
  have hfs' : 2 ^ 11 * rangeAtLevel (T.stepParameters y) β s * levelSpacing T.side K s ≤ ρ := hfs
  have ha_le : 3 * levelSpacing T.side K s ≤ ρ := by nlinarith [hr1 s hsK]
  have ha_min : levelSpacing T.side K s ≤ min 1 ρ := le_min (levelSpacing_le_one_aux hL1 hsK) (by linarith)
  set n := twoCellSide T.side κ s with hn
  let w : (Fin 4 → Fin 2) → (m : ℕ) → PlaquetteWeight m := fun k m =>
    reflectedWeight (levelSpacing T.side K 0) (T.side ^ κ) (fun μ => (k μ : ℕ)) h
  let f : (Fin 4 → Fin 2) → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n := fun k => w k _
  set D := radiusInStageUnits T.side K ρ with hD
  have hap : SeparatedAlong hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ Finset.univ D s n f := by
    refine separatedAlong_of_gaps (ℓ := T.stepParameters y) Finset.univ D w κ s n hsκ.le hn fun t ht => ?_
    have htK' : t + 1 ≤ K := by omega
    have hst₀ := hst t (by omega)
    have hfit₁ := (hlv (t + 1) (by omega)).1
    have hfit₁' : 2 ^ 11 * rangeAtLevel (T.stepParameters y) β (t + 1) * levelSpacing T.side K (t + 1) ≤ ρ := hfit₁
    have hx₀ : y ≤ (couplingFlow (T.stepParameters y) β t).1 := hd.coupling_ge t (by omega)
    have hx₁ : (flowStages T y β hL z₀ t).1.toStepSetup.nextCoupling =
        (couplingFlow (T.stepParameters y) β (t + 1)).1 := hst₀.nextCoupling_eq
    have hx₂ : (flowStages T y β hL z₀ t).1.toStepSetup.coupling = (couplingFlow (T.stepParameters y) β t).1 :=
      hst₀.coupling_eq
    have hmv : |(couplingFlow (T.stepParameters y) β (t + 1)).1 - (couplingFlow (T.stepParameters y) β t).1| ≤
        2 * T.B := by
      have := hst₀.onFamily.abs_sub_le
      rwa [hx₁, hx₂] at this
    have hrr := (F.range_close _ _ hx₀ hmv).1
    have hr' : 1 ≤ clusterRange (couplingFlow (T.stepParameters y) β (t + 1)).1 :=
      F.one_le_range _ (hd.coupling_ge (t + 1) htK')
    have hg := fun d => floor_gap_bounds (d := d) (levelSpacing_pos_aux hL1 K (t + 1)) hfit₁' hr' hrr
    have e₀ : (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t).range =
        clusterRange (couplingFlow (T.stepParameters y) β t).1 := by
      show clusterRange (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t).coupling = _
      rw [show (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t).coupling =
        (couplingFlow (T.stepParameters y) β t).1 from hx₂]
    refine ⟨htK t (by omega), ?_, (hg 0).2.1, fun i _ j _ hij Y hY Y' hY' => ?_⟩
    · rw [e₀]
      exact (hg 0).1
    · refine (hg (supDist Y Y')).2.2 ?_
      exact hApart T.side hodd K κ (t + 1) ρ H Λ h (by have := (hlv (t + 1) (by omega)).2.1; omega) hρ hρl hsrc
        i j hij Y hY Y' hY'
  have hsize : ∀ k, weightNorm (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth (f k) ≤ 1 := fun k => by
    have h₁ := hSize T.side hodd K κ s ρ H Λ h hsκ.le hρ hρl hsrc ha_min k
    have h₂ := weightNorm_congr_depth (L := T.side) (htK s hsK) n (w k)
    have h₃ : weightNorm (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth (f k) =
        weightNorm T.side s (m := fineSide T.side s n) (w k _) := h₂
    rw [h₃]
    linarith
  have hcard : ∀ k, ((weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f k)).card : ℝ) ≤
      81 * (ρ / levelSpacing T.side K s) ^ 4 := fun k => by
    have h₁ := hSites T.side hodd K κ s ρ H Λ h hsκ.le hρ hρl hsrc ha_le k
    have h₂ := weightSupportSites_congr_depth (L := T.side) (htK s hsK) n (w k)
    have h₃ : weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f k) =
        weightSupportSites T.side s n (w k _) := h₂
    rw [h₃]
    exact h₁
  have hC₀ := F.C₀_nonneg
  have hA : ∏ i : Fin 4 → Fin 2,
      (Kr.C₀ * ((weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)).card : ℝ)) ≤
      (Kr.C₀ * (81 * (ρ / levelSpacing T.side K s) ^ 4)) ^ 16 := by
    calc _ ≤ ∏ _i : Fin 4 → Fin 2, (Kr.C₀ * (81 * (ρ / levelSpacing T.side K s) ^ 4)) :=
          Finset.prod_le_prod (fun i _ => by positivity) fun i _ => mul_le_mul_of_nonneg_left (hcard i) hC₀
      _ = _ := by rw [Finset.prod_const, card_corners]
  have hmass := F.mass_pos (flowStages T y β hL z₀ s).1.toStepSetup (flowStages T y β hL z₀ s).2 hs.params_eq
    hs.onFamily n hbs
  have hmain := abs_normalizedMoment_le (Cn := Cn) (D := D) (R := R)
    (Ab := (Kr.C₀ * (81 * (ρ / levelSpacing T.side K s) ^ 4)) ^ 16) (Eb := Ce) hfit hs hbs
    (by positivity) hCe hR f
    (F.product_approx β hL z₀ hfirst s hstand n hbs D f (fun i _ => hsize i) hap)
    (fun i => F.response_le β hL z₀ hfirst s hstand n hbs (f i) (hsize i))
    (F.error_le β hL z₀ hfirst K κ s ρ H Λ h hd hκ hρ hρl hsrc hlev hstand) hA hmaj hmass.1 hmass.2
  have hmom := F.moment_eq β hL z₀ hfirst s hstand n hbs D f hap
  rw [← hmom] at hmain
  set kp := centring (T.stepParameters y) β (fun j => (flowStages T y β hL z₀ j).2.coeff) K κ ρ h with hkp
  have hsh : ∀ k, accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n (f k) = kp := fun k => by
    have h₁ := F.meanAtTrivial_eq β hL z₀ hfirst s hstand n (w k) hbs
    have h₂ := F.centring_copy β K κ (fun j => (flowStages T y β hL z₀ j).2.coeff) ρ H Λ h hd hκ hρ hρl hsrc k
    unfold reflectedCentring at h₂
    rw [hlev] at h₂
    exact h₁.symm.trans h₂
  have hnat : fineSide (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n = 2 * T.side ^ κ := by
    rw [fineSide_eq, htK s hsK, hn]
    show 2 * T.side ^ (κ - s) * T.side ^ s = 2 * T.side ^ κ
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hsκ.le]
  have hint : reflectedProductMean β (levelSpacing T.side K 0) (T.side ^ κ) 2 0 h kp =
      ∫ W, ∏ i ∈ Finset.univ, (curvatureObservable (f i) W -
            accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n (f i))
          ∂(wilsonLaw β (fineSide (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n)) := by
    simp only [hsh]
    rw [reflectedProductMean_origin]
    exact (productMean_congr_side hnat β (levelSpacing T.side K 0) (T.side ^ κ) h kp).symm
  rw [hint]
  exact (le_abs_self _).trans hmain
end Inputs
section Rescaling
variable {T : ParameterAssignment} {Kr : ResponseParameters} {y Ξ β : ℝ} {Cn : ℕ → ℝ} {Ce : ℝ}
  {hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup} {z₀ : StageWithResponse (T.stepParameters y)}
private theorem not_fitsAtLevel_of_gt {ℓ : StepParameters} {K s t : ℕ} {ρ : ℝ} (h : radiusLevel ℓ β K ρ = some s)
    (hst : s < t) (htK : t ≤ K) : ¬ FitsAtLevel ℓ β K ρ t := by
  classical
  unfold radiusLevel at h
  split_ifs at h with hex
  have e := Option.some.inj h
  subst e
  exact Nat.findGreatest_is_greatest hst htK
private theorem radius_div_spacing_pow_le (F : RadiusLevelInputs T Kr y Ξ Cn Ce) {K s : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : IsAdmissibleFlow (T.stepParameters y) Ξ β K) (hlev : radiusLevel (T.stepParameters y) β K ρ = some s)
    (hsK : s ≤ K) (hst : StagesOnFlowUpTo T Kr y β hL z₀ K) :
    (ρ / levelSpacing T.side K s) ^ 4 ≤
      (2 ^ 12 * (T.side : ℝ)) ^ 4 * (rangeAtLevel (T.stepParameters y) β s ^ 4 + ρ ^ 4) := by
  have hfit := F.admissible
  have hL1 : 1 ≤ T.side := by
    have := hfit.L_ge
    have e : (T.stepParameters y).side = T.side := rfl
    omega
  have hL1' : (1 : ℝ) ≤ T.side := by exact_mod_cast hL1
  have hc1 : (1 : ℝ) ≤ (2 ^ 12 * (T.side : ℝ)) ^ 4 := one_le_pow₀ (by nlinarith)
  rcases hsK.eq_or_lt with e | hlt
  · subst e
    rw [levelSpacing_self_aux, div_one]
    have h1 : 0 ≤ ρ ^ 4 := by positivity
    have h2 : 0 ≤ rangeAtLevel (T.stepParameters y) β s ^ 4 := by positivity
    nlinarith
  · have hnf := not_fitsAtLevel_of_gt hlev (Nat.lt_succ_self s) hlt
    have hnf' : ρ < 2 ^ 11 * rangeAtLevel (T.stepParameters y) β (s + 1) * levelSpacing T.side K (s + 1) :=
      not_le.mp hnf
    have ha : 0 < levelSpacing T.side K s := levelSpacing_pos_aux hL1 K s
    rw [levelSpacing_succ_aux hL1] at hnf'
    have hst₀ := hst s hsK
    have hx₀ : y ≤ (couplingFlow (T.stepParameters y) β s).1 := hd.coupling_ge s hsK
    have hx₁ : (flowStages T y β hL z₀ s).1.toStepSetup.nextCoupling =
        (couplingFlow (T.stepParameters y) β (s + 1)).1 := hst₀.nextCoupling_eq
    have hx₂ : (flowStages T y β hL z₀ s).1.toStepSetup.coupling = (couplingFlow (T.stepParameters y) β s).1 :=
      hst₀.coupling_eq
    have hmv : |(couplingFlow (T.stepParameters y) β (s + 1)).1 - (couplingFlow (T.stepParameters y) β s).1| ≤
        2 * T.B := by
      have := hst₀.onFamily.abs_sub_le
      rwa [hx₁, hx₂] at this
    have hrr : rangeAtLevel (T.stepParameters y) β (s + 1) ≤ rangeAtLevel (T.stepParameters y) β s + 1 := by
      have := (F.range_close _ _ hx₀ hmv).2
      unfold rangeAtLevel
      exact_mod_cast this
    have hr1 : (1 : ℝ) ≤ rangeAtLevel (T.stepParameters y) β s := by
      have := F.one_le_range _ hx₀
      unfold rangeAtLevel
      exact_mod_cast this
    have hX : ρ / levelSpacing T.side K s ≤ 2 ^ 12 * (T.side : ℝ) * rangeAtLevel (T.stepParameters y) β s := by
      rw [div_le_iff₀ ha]
      have h1 : 2 ^ 11 * rangeAtLevel (T.stepParameters y) β (s + 1) ≤
          2 ^ 12 * rangeAtLevel (T.stepParameters y) β s := by linarith
      have h2 : 0 ≤ (T.side : ℝ) * levelSpacing T.side K s := by positivity
      calc ρ ≤ 2 ^ 11 * rangeAtLevel (T.stepParameters y) β (s + 1) * ((T.side : ℝ) * levelSpacing T.side K s) :=
            hnf'.le
        _ ≤ 2 ^ 12 * rangeAtLevel (T.stepParameters y) β s * ((T.side : ℝ) * levelSpacing T.side K s) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = _ := by ring
    have hX0 : 0 ≤ ρ / levelSpacing T.side K s := by positivity
    calc (ρ / levelSpacing T.side K s) ^ 4
          ≤ (2 ^ 12 * (T.side : ℝ) * rangeAtLevel (T.stepParameters y) β s) ^ 4 := pow_le_pow_left₀ hX0 hX 4
      _ = (2 ^ 12 * (T.side : ℝ)) ^ 4 * rangeAtLevel (T.stepParameters y) β s ^ 4 := by ring
      _ ≤ _ := by
        have h1 : 0 ≤ ρ ^ 4 := by positivity
        nlinarith
private theorem prodMeanSiteScores_smul {K κ s : ℕ} (n : ℕ) [NeZero n] {c : ℝ} (hc : c ≠ 0)
    (h : EuclideanFourSpace → ℝ) :
    prodMeanSiteScores T y β hL z₀ K κ s n (fun x => c * h x) = prodMeanSiteScores T y β hL z₀ K κ s n h := by
  funext W Y ω
  unfold prodMeanSiteScores reflectedWeightsAtStage
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [weightSupportSites_smul _ _ hc]
private theorem reflectedProductMean_le_aux (hlin : ResponseLinearLocalStatement) (hSites : reflectedWeightSupportStatement)
    (hApart : reflectedSupportsSeparatedStatement) (hSize : reflectedWeightNormBoundStatement)
    (F : RadiusLevelInputs T Kr y Ξ Cn Ce) (hCe : 0 ≤ Ce) (hfirst : IsInitialStage T y β z₀) {K κ s : ℕ} {ρ H : ℝ}
    {Λ : NNReal} {h : EuclideanFourSpace → ℝ} (hd : IsAdmissibleFlow (T.stepParameters y) Ξ β K) (hκ : 2 ≤ κ)
    (hρ : 0 < ρ) (hρl : ρ ≤ cellLength T.side K κ / 4)
    (hsrc : IsLocalizedSource (cellLength T.side K κ) ρ H Λ h) (hlev : radiusLevel (T.stepParameters y) β K ρ = some s)
    (hst : StagesOnFlowUpTo T Kr y β hL z₀ K) {R : ℝ} (hR : 0 ≤ R)
    (hmaj : stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s)
        (prodMeanSiteScores T y β hL z₀ K κ s (twoCellSide T.side κ s) h) ≤
      ENNReal.ofReal R * stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s)
        (fun _ _ _ => 1)) :
    reflectedProductMean β (levelSpacing T.side K 0) (T.side ^ κ) 2 0 h
        (centring (T.stepParameters y) β (fun j => (flowStages T y β hL z₀ j).2.coeff) K κ ρ h) ≤
      (2 * (Kr.C₀ * 81 * (2 ^ 12 * (T.side : ℝ)) ^ 4 + Ce + 1) *
        (1 + rangeAtLevel (T.stepParameters y) β s ^ 4 + ρ ^ 4) * sourceNorm ρ H Λ) ^ 16 * R := by
  have hfit := F.admissible
  have hC₀ := F.C₀_nonneg
  set al : ℕ → ℝ := fun j => (flowStages T y β hL z₀ j).2.coeff with hal
  set v := 1 + rangeAtLevel (T.stepParameters y) β s ^ 4 + ρ ^ 4 with hv
  set N := sourceNorm ρ H Λ with hNdef
  have hH : 0 ≤ H := (abs_nonneg _).trans (hsrc.abs_le 0)
  have hHN : H ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := hH.trans hHN
  have hv1 : 1 ≤ v := by
    have h1 : 0 ≤ rangeAtLevel (T.stepParameters y) β s ^ 4 := by positivity
    have h2 : 0 ≤ ρ ^ 4 := by positivity
    rw [hv]
    linarith
  rcases hN0.eq_or_lt with hN | hNpos
  · have hH0 : H = 0 := le_antisymm (hHN.trans hN.symm.le) hH
    have hh : (fun x => (0 : ℝ) * h x) = h := by
      funext x
      have h1 := hsrc.abs_le x
      rw [hH0] at h1
      have h2 : h x = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
      rw [h2, mul_zero]
    have hkp : centring (T.stepParameters y) β al K κ ρ h = 0 * centring (T.stepParameters y) β al K κ ρ h := by
      have := centring_smul_aux hlin hfit β al K κ ρ h 0
      rw [hh] at this
      exact this
    have hm := reflectedProductMean_smul β (levelSpacing T.side K 0) (T.side ^ κ) h 0
      (centring (T.stepParameters y) β al K κ ρ h)
    rw [hh, ← hkp] at hm
    rw [hm, ← hN]
    simp
  · set c : ℝ := (2 * N)⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hcN : c * N = 1 / 2 := by
      rw [hc]
      field_simp
    have hsrc' := localizedSource_smul hc0 hsrc
    have hN' : sourceNorm ρ (c * H) ((Real.toNNReal c * Λ : NNReal) : ℝ) ≤ 1 / 2 := by
      rw [sourceNorm_smul hc0, ← hNdef, hcN]
    have hmaj' : stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s)
        (prodMeanSiteScores T y β hL z₀ K κ s (twoCellSide T.side κ s) fun x => c * h x) ≤
        ENNReal.ofReal R * stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s)
          (fun _ _ _ => 1) := by
      rw [prodMeanSiteScores_smul _ hc0.ne']
      exact hmaj
    have hhalf := reflectedProductMean_le_of_half hSites hApart hSize F hCe hfirst hd hκ hρ hρl hsrc' hlev hst hN' hR
      hmaj'
    rw [centring_smul_aux hlin hfit, reflectedProductMean_smul] at hhalf
    set A₁ : ℝ := Kr.C₀ * 81 * (2 ^ 12 * (T.side : ℝ)) ^ 4 with hA₁
    set a : ℝ := Kr.C₀ * (81 * (ρ / levelSpacing T.side K s) ^ 4) with ha
    have ha0 : 0 ≤ a := by
      have hsp : 0 < levelSpacing T.side K s :=
        levelSpacing_pos_aux (by have := hfit.L_ge; have e : (T.stepParameters y).side = T.side := rfl; omega) K s
      positivity
    have hrad := radius_div_spacing_pow_le (hL := hL) (z₀ := z₀) F hρ hd hlev
      (F.stages β K κ ρ hd hκ hρ hρl s hlev).1 hst
    have haA : a ≤ A₁ * v := by
      have h1 : 0 ≤ Kr.C₀ * 81 := by positivity
      have h2 : rangeAtLevel (T.stepParameters y) β s ^ 4 + ρ ^ 4 ≤ v := by rw [hv]; linarith
      have h3 : (2 ^ 12 * (T.side : ℝ)) ^ 4 * (rangeAtLevel (T.stepParameters y) β s ^ 4 + ρ ^ 4) ≤
          (2 ^ 12 * (T.side : ℝ)) ^ 4 * v :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      calc a = Kr.C₀ * 81 * (ρ / levelSpacing T.side K s) ^ 4 := by rw [ha]; ring
        _ ≤ Kr.C₀ * 81 * ((2 ^ 12 * (T.side : ℝ)) ^ 4 * v) := mul_le_mul_of_nonneg_left (hrad.trans h3) h1
        _ = A₁ * v := by rw [hA₁]; ring
    set u : ℝ := (A₁ + Ce + 1) * v with hu
    have hu1 : a + Ce + 1 ≤ u := by
      have h1 : Ce ≤ Ce * v := le_mul_of_one_le_right hCe hv1
      rw [hu]
      nlinarith
    have hsum : a ^ 16 + Ce ≤ u ^ 16 := (pow_sixteen_add_le ha0 hCe).trans (pow_le_pow_left₀ (by linarith) hu1 16)
    have hstep : c ^ 16 * reflectedProductMean β (levelSpacing T.side K 0) (T.side ^ κ) 2 0 h
        (centring (T.stepParameters y) β al K κ ρ h) ≤ u ^ 16 * R :=
      hhalf.trans (mul_le_mul_of_nonneg_right hsum hR)
    have e₁ : (2 * N) ^ 16 * c ^ 16 = 1 := by
      rw [← mul_pow, hc, mul_inv_cancel₀ (by positivity), one_pow]
    have hfin := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (2 * N) ^ 16 by positivity)
    rw [← mul_assoc, e₁, one_mul, ← mul_assoc, ← mul_pow] at hfin
    refine hfin.trans (le_of_eq ?_)
    congr 2
    rw [hu]
    ring
end Rescaling
theorem reflectedMeanAtRadiusLevel_holds (hLev : levelsBelowRadiusStatement) (hCen : reflectedCentringConstStatement)
    (hSh : centringEqSumShiftsStatement) (hBd : responseBoundedByScoreStatement) (hEr : reflectedMomentErrorStatement)
    (hMom : momentsAlongStagesStatement) (hMany : severalSupportsMomentStatement) (hPos : stageMassPositive)
    (hlin : ResponseLinearLocalStatement) (hSites : reflectedWeightSupportStatement)
    (hApart : reflectedSupportsSeparatedStatement) (hSize : reflectedWeightNormBoundStatement)
    (hAbout : reflectedMeanTranslationStatement) (hFlr : StepFloors.EventuallyFloorConditions) :
    reflectedMeanAtRadiusLevelStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, gLev⟩ := hLev a ha
  obtain ⟨L₂, r₂, C₂, hr₂, gCen⟩ := hCen a ha
  obtain ⟨r₃, hr₃, gSh⟩ := hSh
  obtain ⟨r₄, hr₄, gBd⟩ := hBd
  obtain ⟨r₅, hr₅, gEr⟩ := hEr
  obtain ⟨r₆, hr₆, gMo⟩ := hMom
  obtain ⟨r₇, hr₇, gMa⟩ := hMany
  obtain ⟨r₈, hr₈, gPo⟩ := hPos
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (min (r₆ c)
      (min (r₇ c) (r₈ c))))))),
    max C₁ C₂, fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (lt_min (hr₄ c) (lt_min (hr₅ c)
      (lt_min (hr₆ c) (lt_min (hr₇ c) (hr₈ c))))))), fun L hLo hLL T hTa hTL hT hCS hOn hrt hCd Kr hKr => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have u₁ := hrt.trans (min_le_right _ _)
  have t₂ := u₁.trans (min_le_left _ _)
  have u₂ := u₁.trans (min_le_right _ _)
  have t₃ := u₂.trans (min_le_left _ _)
  have u₃ := u₂.trans (min_le_right _ _)
  have t₄ := u₃.trans (min_le_left _ _)
  have u₄ := u₃.trans (min_le_right _ _)
  have t₅ := u₄.trans (min_le_left _ _)
  have u₅ := u₄.trans (min_le_right _ _)
  have t₆ := u₅.trans (min_le_left _ _)
  have u₆ := u₅.trans (min_le_right _ _)
  have t₇ := u₆.trans (min_le_left _ _)
  have t₈ := u₆.trans (min_le_right _ _)
  obtain ⟨y₁, gLev⟩ := gLev L hLo ((le_max_left _ _).trans hLL) T hTa hTL hT hCS hOn t₁ ((le_max_left _ _).trans hCd)
  obtain ⟨y₂, gCen⟩ := gCen L hLo ((le_max_right _ _).trans hLL) T hTa hTL hT hCS hOn t₂ ((le_max_right _ _).trans hCd)
  obtain ⟨y₃, gSh⟩ := gSh T hT t₃ Kr
  obtain ⟨y₄, gBd⟩ := gBd T hT t₄ Kr
  obtain ⟨y₅, gEr⟩ := gEr T hT t₅ Kr
  obtain ⟨y₆, gMo⟩ := gMo T hT t₆ Kr
  obtain ⟨y₇, Cn, hCn, gMa⟩ := gMa T hT t₇ Kr
  obtain ⟨y₈, gPo⟩ := gPo T hT t₈ Kr
  obtain ⟨yF, hyF⟩ := hFlr T hT 1 1 one_pos one_pos
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆) (max (max y₇ y₈) (max T.floorMin yF))),
    fun y hy hR hW Ξ hΞ => ?_⟩
  have e₀ : max (max y₁ y₂) (max y₃ y₄) ≤ y := (le_max_left _ _).trans hy
  have e₀' : max (max y₅ y₆) (max (max y₇ y₈) (max T.floorMin yF)) ≤ y := (le_max_right _ _).trans hy
  have e₁ : y₁ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans e₀
  have e₂ : y₂ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans e₀
  have e₃ : y₃ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans e₀
  have e₄ : y₄ ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans e₀
  have e₅ : y₅ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans e₀'
  have e₆ : y₆ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans e₀'
  have e₀'' : max (max y₇ y₈) (max T.floorMin yF) ≤ y := (le_max_right _ _).trans e₀'
  have e₇ : y₇ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans e₀''
  have e₈ : y₈ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans e₀''
  have hy0 : T.floorMin ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans e₀''
  have hyFy : yF ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans e₀''
  have hfitL := hT.fits y hy0
  have hfK := hKr y
  obtain ⟨Ce, hCe, gEr⟩ := gEr y e₅ Cn hCn
  have hC0 : 0 ≤ Kr.C₀ := by
    rw [hfK.C₀_eq]
    have h₁ := hfK.N₀_nonneg
    have h₂ := hfK.Kc_ge
    have h₃ := hfitL.a_ge
    nlinarith
  have F : RadiusLevelInputs T Kr y Ξ Cn Ce :=
    { admissible := hfitL
      C₀_nonneg := hC0
      one_le_range := fun x hx => by
        have h := (hyF x (hyFy.trans hx)).range_ge
        exact_mod_cast h
      range_close := fun x x' hx hm => by
        have h := (hyF x (hyFy.trans hx)).stable_nearby.2 x' hm
        exact ⟨h.2.2.1, h.2.2.2⟩
      stages := fun β K κ ρ hd hκ hρ hρl s hl => gLev y e₁ hR hW Ξ β K κ ρ hd hκ hρ hρl s hl
      centring_copy := fun β K κ al ρ H Λ h => gCen y e₂ hR hW Ξ β K κ al ρ H Λ h
      meanAtTrivial_eq := fun β hL z₀ hz s hs n _ w hb => (gSh y e₃ β hL z₀ hz s hs).2 n w hb
      response_le := fun β hL z₀ hz s hs n _ hb f hf W Y ω hq => gBd y e₄ β hL z₀ hz s hs n hb f hf W Y ω hq
      error_le := fun β hL z₀ hz => gEr Ξ hΞ β hL z₀ hz
      moment_eq := fun β hL z₀ hz s hs n _ hb D f hap => gMo y β hL z₀ e₆ hz s hs n hb Finset.univ D f hap
      product_approx := fun β hL z₀ hz s hs n _ hb D f hsz hap =>
        gMa y β hL z₀ e₇ hz s hs n hb Finset.univ D f hsz hap
      mass_pos := fun R A hK hAt n _ hb => gPo y e₈ R A hK hAt n hb }
  refine ⟨2 * (Kr.C₀ * 81 * (2 ^ 12 * (T.side : ℝ)) ^ 4 + Ce + 1), by positivity, ?_⟩
  intro β hL z₀ hz K κ s ρ H Λ h hd hκ hρ hρl hsrc hlev hst R hR₀ hmaj z
  rw [hAbout]
  exact reflectedProductMean_le_aux hlin hSites hApart hSize F hCe hz hd hκ hρ hρl hsrc hlev hst hR₀ hmaj
end YangMills.Construction.SmallTorusCopies
end
