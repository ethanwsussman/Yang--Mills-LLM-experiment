import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantAtBoundedCouplings
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheFarLevelOfTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsNearAProductAtTheFarLevel
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFarLevelAreBounded
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_forAllPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem forAllHullParameters_of_forAllHullPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllHullPoints Q) :
    ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem forAllHullParameters_of_imp {Q₁ Q₂ Q' : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllHullParameters Q₂)
    (hq : ∀ Λ : MomentParameters, Λ.table.Admissible → Λ.table.floorMin ≤ Λ.floor →
      (∀ y, Λ.response.Admissible (Λ.table.stepParameters y)) → 2 ≤ Λ.k → 0 < Λ.d →
      Q₁ Λ → Q₂ Λ → Q' Λ) : ForAllHullParameters Q' := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (rt₁ c) (rt₂ c), max C₁ C₂, fun c => lt_min (hrt₁ c) (hrt₂ c), ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd
  obtain ⟨M₂, Y₂⟩ := H₂ L hLodd ((le_max_right _ _).trans hLge) Tb hTa hTL hDr hCS hOn (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd)
  refine ⟨M₂, ?_⟩
  intro Kr hM hη hN hKr hRet
  obtain ⟨y₁, Z₁⟩ := H₁ L hLodd ((le_max_left _ _).trans hLge) Tb hTa hTL hDr hCS hOn (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd) Kr hKr
  obtain ⟨y₂, Z₂⟩ := Y₂ Kr hM hη hN hKr hRet
  refine ⟨max (max y₁ y₂) Tb.floorMin, ?_⟩
  intro y hy hR hH g hg hyg k _ hk2 hk8 R d hd
  have hy' := (le_max_left _ _).trans hy
  exact hq ⟨Tb, Kr, y, g, k, R, d⟩ hDr ((le_max_right _ _).trans hy) hKr hk2 hd
    (Z₁ y ((le_max_left _ _).trans hy') hR hH g hg hyg k hk2 hk8 R d hd)
    (Z₂ y ((le_max_right _ _).trans hy') hR hH g hg hyg k hk2 hk8 R d hd)
private theorem supDist_le_dist (x y : TestFunctions.EuclideanFourSpace) : supDist x y ≤ dist x y := by apply _root_.YangMills.SharedProofs.p2932 <;> assumption
private theorem admissible_of_supAdmissible {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} {R d : ℝ}
    (h : P.SupAdmissible L R d) : P.Admissible L (2 * R) d where
  isTestFamily :=
    { lipschitzWith_one := fun i => LipschitzWith.of_dist_le_mul fun x y => by
        rw [Real.dist_eq]
        simpa using (h.isSupTestFamily.lipschitz i x y).trans (supDist_le_dist x y)
      abs_le_one := h.isSupTestFamily.abs_le_one
      tsupport_subset_closedBall := fun i x hx => by
        have hb := h.isSupTestFamily.abs_coord_le i x hx
        have hR : 0 ≤ R := (abs_nonneg _).trans (hb 0)
        rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        have hsq : ∀ a, ‖x a‖ ^ 2 ≤ R ^ 2 := fun a => by
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hb a) 2
        rw [Fin.sum_univ_four]
        nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
      le_dist_of_ne := fun i j hij x hx y hy =>
        (h.isSupTestFamily.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y) }
  scaleLevel_le := h.scaleLevel_le
  support_small := h.support_small
  exists_ne_zero := h.exists_ne_zero
private theorem pow_mul_exp_neg_le (A a : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ X : ℝ, 1 ≤ X → A * X ^ n * Real.exp (-(a * X)) ≤ Q / X := by
  refine ⟨A * ((n + 1).factorial : ℝ) / a ^ (n + 1), by positivity, fun X hX => ?_⟩
  have hv : 0 < a * X := by positivity
  have h1 := Real.pow_div_factorial_le_exp (a * X) hv.le (n + 1)
  have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have h2 : Real.exp (-(a * X)) ≤ ((n + 1).factorial : ℝ) / (a * X) ^ (n + 1) := by
    rw [Real.exp_neg, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (Real.exp_pos _)]
    rwa [div_le_iff₀ hf] at h1
  calc A * X ^ n * Real.exp (-(a * X)) ≤ A * X ^ n * (((n + 1).factorial : ℝ) / (a * X) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = A * ((n + 1).factorial : ℝ) / a ^ (n + 1) / X := by
        rw [mul_pow, pow_succ X]
        field_simp
private theorem rpow_mul_exp_neg_le_geometric (e rt c : ℝ) (L : ℕ) (hrt : 0 < rt) (hc : 0 < c) (hL : 2 ≤ L) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (τ : ℕ) (D : ℝ), c * (L : ℝ) ^ τ - 12 ≤ D →
      (L : ℝ) ^ (e * (τ : ℝ)) * Real.exp (-(rt * D / 2 ^ 8)) ≤ Q / 2 ^ τ := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set A : ℕ := ⌈|e|⌉₊ with hA
  set E₀ : ℝ := Real.exp (12 * rt / 2 ^ 8) with hE₀
  obtain ⟨Q, hQ0, hQ⟩ := pow_mul_exp_neg_le E₀ (rt * c / 2 ^ 8) (Real.exp_pos _).le (by positivity) A
  refine ⟨Q, hQ0, fun τ D hD => ?_⟩
  set X : ℝ := (L : ℝ) ^ τ with hX
  have h2X : (2 : ℝ) ^ τ ≤ X := pow_le_pow_left₀ (by norm_num) hL2 τ
  have h2τ : (1 : ℝ) ≤ 2 ^ τ := one_le_pow₀ (by norm_num)
  have hX1 : 1 ≤ X := h2τ.trans h2X
  have hpow : (L : ℝ) ^ (e * (τ : ℝ)) ≤ X ^ A := by
    have h1 : e * (τ : ℝ) ≤ (τ : ℝ) * (A : ℝ) := by
      have h3 : e ≤ (A : ℝ) := (le_abs_self e).trans (Nat.le_ceil _)
      nlinarith [Nat.cast_nonneg (α := ℝ) τ]
    calc (L : ℝ) ^ (e * (τ : ℝ)) ≤ (L : ℝ) ^ ((τ : ℝ) * (A : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 h1
      _ = X ^ A := by
          rw [Real.rpow_mul (by linarith), Real.rpow_natCast, Real.rpow_natCast]
  have hexp : Real.exp (-(rt * D / 2 ^ 8)) ≤ E₀ * Real.exp (-(rt * c / 2 ^ 8 * X)) := by
    rw [hE₀, ← Real.exp_add, Real.exp_le_exp]
    have h4 : rt * (c * X - 12) ≤ rt * D := mul_le_mul_of_nonneg_left hD hrt.le
    linarith
  calc (L : ℝ) ^ (e * (τ : ℝ)) * Real.exp (-(rt * D / 2 ^ 8))
      ≤ X ^ A * (E₀ * Real.exp (-(rt * c / 2 ^ 8 * X))) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = E₀ * X ^ A * Real.exp (-(rt * c / 2 ^ 8 * X)) := by ring
    _ ≤ Q / X := hQ X hX1
    _ ≤ Q / 2 ^ τ := div_le_div_of_nonneg_left hQ0 (by positivity) h2X
private theorem sum_div_two_pow_le (Q : ℝ) (hQ : 0 ≤ Q) (s : ℕ) :
    ∀ t ≤ s, ∑ u ∈ Finset.range t, Q / 2 ^ (s - u) ≤ Q / 2 ^ (s - t) := by
  intro t
  induction t with
  | zero =>
    intro _
    simpa using (by positivity : 0 ≤ Q / 2 ^ s)
  | succ t ih =>
    intro ht
    rw [Finset.sum_range_succ]
    have h1 := ih (by omega)
    have e : s - t = (s - (t + 1)) + 1 := by omega
    have h2 : Q / 2 ^ (s - t) = Q / 2 ^ (s - (t + 1)) / 2 := by
      rw [e, pow_succ]
      field_simp
    rw [h2] at h1 ⊢
    linarith
private theorem curvatureObservable_isBounded {N : ℕ} [NeZero N] (h : WeightedResponses.PlaquetteWeight N) :
    Probability.IsBoundedRealRV (WeightedResponses.curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p42321 <;> assumption
private theorem norm_mixedCumulant_le (hC : Cumulants.MixedCumulantMomentExpansion)
    (hS : Cumulants.MomentCumulantRelations.Holds) {Ω' : Type} [MeasurableSpace Ω']
    (ν : Measure Ω') [IsProbabilityMeasure ν] {p : ℕ} (hp : 2 ≤ p) (X : Fin p → Ω' → ℝ)
    (hX : ∀ i, Probability.IsBoundedRealRV (X i)) (κ : Fin p → ℝ) (M : ℝ)
    (hm : ∀ I : Finset (Fin p), |∫ ω, ∏ i ∈ I, (X i ω - κ i) ∂ν| ≤ M) :
    ‖Cumulants.mixedCumulant ν X‖ ≤ ∑ π : SetPartition.PartitionsFin p,
      ((SetPartition.blockCount π - 1).factorial : ℝ) * M ^ SetPartition.blockCount π := by
  have hb : ∀ i, Probability.IsBoundedRealRV fun ω => X i ω + -κ i := fun i => by
    obtain ⟨C, hCb⟩ := (hX i).bounded
    exact ⟨(hX i).measurable.add_const _, C + |κ i|, fun ω =>
      (abs_add_le _ _).trans (by rw [abs_neg]; linarith [hCb ω])⟩
  have h1 := (hS Ω' ν).2.2.1 p X (fun i => -κ i) hp hX
  rw [← h1, hC Ω' ν p _ (by omega) hb]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∏ J ∈ π.parts, ‖((∫ ω, ∏ l ∈ J, (X l ω + -κ l) ∂ν : ℝ) : ℂ)‖ ≤ ∏ _J ∈ π.parts, M := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun J _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        simpa [sub_eq_add_neg] using hm J
    _ = M ^ SetPartition.blockCount π := by simp [SetPartition.blockCount]
private theorem measurable_bottomField {ℓ : TorusLumps.StepParameters} (s : ℕ) :
    ∀ n : ℕ, Measurable (WeightedResponses.bottomField ℓ s n) := by apply _root_.YangMills.SharedProofs.p4086 <;> assumption
theorem cumulantBoundedCoupling_of_components (hFar : productApproxAtLastSeparatedStatement)
    (hMom : separatedLevelMomentsStatement) (hSc : meanScoreMomentBoundStatement)
    (hSites : farLevelSupportSitesStatement) (hResp : farLevelResponseBoundStatement)
    (hGap : LevelTestFunctions.separationLowerBoundStatement)
    (hTP : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (hCum : Cumulants.MixedCumulantMomentExpansion)
    (hMul : Cumulants.MomentCumulantRelations.Holds) : cumulantBoundedCouplingStatement := by
  suffices h : ForAllHullParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧
      ∀ S : MomentPoint Λ, ∀ M : ℕ, S.scaleCoupling ≤ M → ‖S.torusCumulant‖ ≤ C M from h
  refine forAllHullParameters_of_imp (forAllParameters_and (forAllParameters_of_forAllPoints hFar)
    (forAllParameters_and (forAllParameters_of_forAllPoints hMom)
      (forAllParameters_and (forAllParameters_of_forAllPoints hSites) (forAllParameters_of_forAllPoints hResp))))
    (forAllHullParameters_of_forAllHullPoints hSc) ?_
  rintro Λ hDr hy hKr hk hd ⟨⟨Cf, _, _, _, _, HF⟩, ⟨_, _, _, _, _, HM⟩, ⟨Cd, _, _, _, _, HD⟩, ⟨_, _, _, _, _, HR⟩⟩
    ⟨Cg, _, _, _, _, HG⟩
  have hFit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hL2 : 2 ≤ Λ.stepParams.side := le_trans (by norm_num) hFit.L_ge
  have hC₀ : 0 ≤ Λ.response.C₀ := by
    have hk' := hKr Λ.floor
    have h1 : 1 ≤ (Λ.table.stepParameters Λ.floor).coupling := hFit.a_ge
    have h2 := hk'.N₀_nonneg
    have h3 := hk'.Kc_ge
    rw [hk'.C₀_eq]
    linarith
  obtain ⟨c₁, hc₁, Hg⟩ := hGap Λ.stepParams.side hFit.L_odd (by have := hFit.L_ge; omega) Λ.k hk (2 * Λ.R) Λ.d hd
  obtain ⟨Q, hQ0, hQ⟩ := rpow_mul_exp_neg_le_geometric (Cf 101) Λ.stepParams.rt c₁ Λ.stepParams.side
    hFit.rt_pos hc₁ hL2
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = |Cf 100| * Q := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℕ → ℝ, ∀ M, Kb M = 1 + Λ.response.C₀ *
      (|Cd 0| * (TorusLumps.clusterRange (M : ℝ) : ℝ) ^ 4) := ⟨_, fun _ => rfl⟩
  have hKb1 : ∀ M, 1 ≤ Kb M := fun M => by
    rw [hKb]
    have : 0 ≤ Λ.response.C₀ * (|Cd 0| * (TorusLumps.clusterRange (M : ℝ) : ℝ) ^ 4) := by positivity
    linarith
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℕ → ℝ, ∀ M, Mb M = 1 + (Kb M ^ Λ.k + E) *
      ((|Cg 0| + 1) ^ Λ.k * (Λ.k.factorial : ℝ) ^ 6) := ⟨_, fun _ => rfl⟩
  have hMb1 : ∀ M, 1 ≤ Mb M := fun M => by
    rw [hMb]
    have h1 : 0 ≤ Kb M := by linarith [hKb1 M]
    have : 0 ≤ (Kb M ^ Λ.k + E) * ((|Cg 0| + 1) ^ Λ.k * (Λ.k.factorial : ℝ) ^ 6) := by positivity
    linarith
  refine ⟨fun M => ∑ π : SetPartition.PartitionsFin Λ.k,
    ((SetPartition.blockCount π - 1).factorial : ℝ) * Mb M ^ SetPartition.blockCount π, 1, Λ.floor, one_pos, le_rfl, ?_⟩
  intro S M hM
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    unfold MomentPoint.lastSeparated
    classical exact Nat.findGreatest_le _
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have herr : ∀ B : Finset (Fin Λ.k), S.separationError (Cf B.card) S.lastSeparated B ≤ E := fun B => by
    have hterm : ∀ u ∈ Finset.range S.lastSeparated,
        (Λ.stepParams.side : ℝ) ^ (Cf 101 * ((S.data.scaleLevel : ℝ) - (u : ℝ))) *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) ≤
          Q / 2 ^ (S.data.scaleLevel - u) := fun u hu => by
      have hut : u < S.lastSeparated := Finset.mem_range.mp hu
      have e1 : (S.data.scaleLevel : ℝ) - (u : ℝ) = ((S.data.scaleLevel - u : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      have h1 := Hg S.data (admissible_of_supAdmissible S.supAdmissible) u (by omega)
      have e2 : (S.data.scaleLevel : ℤ) - (u : ℤ) = ((S.data.scaleLevel - u : ℕ) : ℤ) := by omega
      rw [e2, zpow_natCast] at h1
      rw [e1]
      exact hQ _ _ h1
    have hsum0 : 0 ≤ ∑ u ∈ Finset.range S.lastSeparated,
        (Λ.stepParams.side : ℝ) ^ (Cf 101 * ((S.data.scaleLevel : ℝ) - (u : ℝ))) *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) :=
      Finset.sum_nonneg fun u _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
    have hsum : ∑ u ∈ Finset.range S.lastSeparated,
        (Λ.stepParams.side : ℝ) ^ (Cf 101 * ((S.data.scaleLevel : ℝ) - (u : ℝ))) *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) ≤ Q :=
      calc _ ≤ ∑ u ∈ Finset.range S.lastSeparated, Q / 2 ^ (S.data.scaleLevel - u) := Finset.sum_le_sum hterm
        _ ≤ Q / 2 ^ (S.data.scaleLevel - S.lastSeparated) := sum_div_two_pow_le Q hQ0 _ _ hts
        _ ≤ Q := div_le_self hQ0 (one_le_pow₀ (by norm_num))
    calc S.separationError (Cf B.card) S.lastSeparated B ≤ _ := (HF S B).2.1
      _ ≤ |Cf 100| * _ := mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
      _ ≤ E := by rw [hE]; exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  have hxs : Λ.floor ≤ S.scaleCoupling := by
    have hst := S.onFlow S.data.scaleLevel hsK
    exact hst.onFamily.onFamily.le_coupling.trans (le_of_eq hst.coupling_eq)
  have hx0 : 0 ≤ S.scaleCoupling := by
    have h1 : 1 ≤ Λ.floor := hFit.y₁_ge
    linarith
  have hr : (S.range : ℝ) ≤ (TorusLumps.clusterRange (M : ℝ) : ℝ) := by
    have : S.range ≤ TorusLumps.clusterRange (M : ℝ) := Nat.ceil_mono (Real.rpow_le_rpow hx0 hM (by norm_num))
    exact_mod_cast this
  have hKi : ∀ i, Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) ≤ Kb M :=
    fun i => by
    have h1 := (HD S).1 i
    have h2 : Cd 0 * (S.range : ℝ) ^ 4 ≤ |Cd 0| * (TorusLumps.clusterRange (M : ℝ) : ℝ) ^ 4 :=
      mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (Nat.cast_nonneg _) hr 4) (by positivity) (abs_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hC₀
    rw [hKb]
    linarith
  have key : ∀ (m : ℕ) [NeZero m],
      m = WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated) →
      ‖WeightedResponses.connectedCurvature S.β m fun i => S.weight i m‖ ≤ ∑ π : SetPartition.PartitionsFin Λ.k,
        ((SetPartition.blockCount π - 1).factorial : ℝ) * Mb M ^ SetPartition.blockCount π := by
    intro m _ hm
    subst hm
    have hTP' := hTP Λ.stepParams hFit hFit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β S.coeff
    obtain ⟨hprob, -, hmap, -⟩ := hTP' S.lastSeparated (S.levelSide S.lastSeparated)
    have : IsProbabilityMeasure (WeightedResponses.wilsonLaw S.β
        (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) :=
      (hTP' 0 (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))).1
    have hmom : ∀ I : Finset (Fin Λ.k), |∫ W, ∏ i ∈ I, (WeightedResponses.curvatureObservable
        (S.weight i (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) W -
        S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i) ∂(WeightedResponses.wilsonLaw S.β
          (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))| ≤ Mb M := by
      intro I
      rcases I.eq_empty_or_nonempty with rfl | hI
      · simpa using hMb1 M
      have hf : Measurable fun W => ∏ i ∈ I, (WeightedResponses.curvatureObservable
          (S.weight i (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) W -
          S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i) :=
        Finset.measurable_prod _ fun i _ => (curvatureObservable_isBounded _).measurable.sub_const _
      have e1 : ∫ W, ∏ i ∈ I, (WeightedResponses.curvatureObservable
          (S.weight i (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) W -
          S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i) ∂(WeightedResponses.wilsonLaw S.β
            (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated))) =
          ∫ w, ∏ i ∈ I, (WeightedResponses.curvatureObservable
            (S.weight i (WeightedResponses.fineSide Λ.stepParams.side S.lastSeparated (S.levelSide S.lastSeparated)))
            (WeightedResponses.bottomField Λ.stepParams S.lastSeparated (S.levelSide S.lastSeparated) w) -
            S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i)
            ∂(WeightedResponses.markedSampleLaw S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated)) := by
        rw [← hmap]
        exact integral_map (measurable_bottomField _ _).aemeasurable hf.aestronglyMeasurable
      have e2 := HM S I fun i => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i
      rw [e1]
      refine (congrArg abs e2).le.trans ?_
      obtain ⟨G, hGdef⟩ : ∃ G, G = WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated
          (S.levelSide S.lastSeparated) (fun i => S.weight i _) I
          (fun i => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i) := ⟨_, rfl⟩
      rw [← hGdef]
      have hN := (HF S I).1
      rw [← hGdef] at hN
      have hcc : 0 ≤ Kb M ^ Λ.k + E := by
        have : 0 ≤ Kb M := by linarith [hKb1 M]
        positivity
      have hKprod : ∏ i ∈ I, (Λ.response.C₀ *
          ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ)) ≤ Kb M ^ Λ.k := by
        have hcard : I.card ≤ Λ.k := by simpa using Finset.card_le_univ I
        calc ∏ i ∈ I, (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ))
              ≤ ∏ _i ∈ I, Kb M :=
              Finset.prod_le_prod (fun i _ => by positivity) fun i _ => hKi i
          _ = Kb M ^ I.card := by simp
          _ ≤ Kb M ^ Λ.k := pow_le_pow_right₀ (hKb1 M) hcard
      have hae : ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)), ‖G w‖ ≤ (Kb M ^ Λ.k + E) *
          ∏ i ∈ I, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by
        filter_upwards [hN, ae_all_iff.2 (HR S)] with w h1 h2
        have hN0 : 0 ≤ ∏ i ∈ I, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) :=
          Finset.prod_nonneg fun i _ => by linarith [(h2 i).1]
        have hF : |∏ i ∈ I, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤ Kb M ^ Λ.k *
            ∏ i ∈ I, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by
          rw [Finset.abs_prod]
          calc ∏ i ∈ I, |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
                (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)|
              ≤ ∏ i ∈ I, (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) *
                  S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
                    (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) :=
                Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => (h2 i).2
            _ = (∏ i ∈ I, (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ))) *
                  ∏ i ∈ I, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
                    (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := Finset.prod_mul_distrib
            _ ≤ _ := mul_le_mul_of_nonneg_right hKprod hN0
        have h3 := mul_le_mul_of_nonneg_right (herr I) hN0
        have h4 : |G w| ≤ |G w - ∏ i ∈ I, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| +
            |∏ i ∈ I, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| := by
          simpa using abs_add_le (G w - ∏ i ∈ I, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
            (∏ i ∈ I, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
        rw [Real.norm_eq_abs, add_mul]
        linarith
      have hp : 1 ≤ I.card := hI.card_pos
      have hmoment := (HG S I.card hp I.toList (Finset.length_toList I)).2
      simp only [Finset.prod_map_toList] at hmoment
      have hl : ∫⁻ w, ENNReal.ofReal ‖G w‖ ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
          ENNReal.ofReal (Mb M) := by
        calc ∫⁻ w, ENNReal.ofReal ‖G w‖ ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated))
            ≤ ∫⁻ w, ENNReal.ofReal (Kb M ^ Λ.k + E) *
                ENNReal.ofReal (∏ i ∈ I, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
                  (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
                ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) :=
              lintegral_mono_ae (hae.mono fun w hw => by
                rw [← ENNReal.ofReal_mul hcc]
                exact ENNReal.ofReal_le_ofReal hw)
          _ = ENNReal.ofReal (Kb M ^ Λ.k + E) * ∫⁻ w,
                ENNReal.ofReal (∏ i ∈ I, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
                  (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
                ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal (Kb M ^ Λ.k + E) * ENNReal.ofReal (Cg 0 ^ I.card * (I.card.factorial : ℝ) ^ 6) := by
              gcongr
          _ = ENNReal.ofReal ((Kb M ^ Λ.k + E) * (Cg 0 ^ I.card * (I.card.factorial : ℝ) ^ 6)) :=
              (ENNReal.ofReal_mul hcc).symm
          _ ≤ ENNReal.ofReal (Mb M) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hcard : I.card ≤ Λ.k := by simpa using Finset.card_le_univ I
              have h1 : Cg 0 ^ I.card ≤ (|Cg 0| + 1) ^ Λ.k :=
                calc Cg 0 ^ I.card ≤ |Cg 0 ^ I.card| := le_abs_self _
                  _ = |Cg 0| ^ I.card := abs_pow _ _
                  _ ≤ (|Cg 0| + 1) ^ I.card := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
                  _ ≤ (|Cg 0| + 1) ^ Λ.k := pow_le_pow_right₀ (by linarith [abs_nonneg (Cg 0)]) hcard
              have h2 : (I.card.factorial : ℝ) ^ 6 ≤ (Λ.k.factorial : ℝ) ^ 6 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hcard) 6
              have h3 : Cg 0 ^ I.card * (I.card.factorial : ℝ) ^ 6 ≤
                  (|Cg 0| + 1) ^ Λ.k * (Λ.k.factorial : ℝ) ^ 6 :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
              have h4 := mul_le_mul_of_nonneg_left h3 hcc
              rw [hMb]
              linarith
      have h6 := norm_integral_le_lintegral_norm (μ := S.law S.lastSeparated (S.levelSide S.lastSeparated)) G
      rw [Real.norm_eq_abs] at h6
      exact h6.trans (ENNReal.toReal_le_of_le_ofReal (by linarith [hMb1 M]) hl)
    exact norm_mixedCumulant_le hCum hMul _ hk _ (fun i => curvatureObservable_isBounded _) _ (Mb M) hmom
  refine key _ ?_
  rw [WeightedResponses.fineSide_eq, WeightedResponses.fineSide_eq]
  have e : S.data.windowLevel = S.lastSeparated + (S.data.windowLevel - S.lastSeparated) := by omega
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ S.data.windowLevel =
    S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated) *
      Λ.stepParams.side ^ S.lastSeparated
  rw [mul_assoc, ← pow_add]
  congr 2
  omega
end YangMills.Construction.MomentLaw
end
