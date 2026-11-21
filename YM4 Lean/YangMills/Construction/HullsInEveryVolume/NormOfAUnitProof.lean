import YangMills.Construction.HullsInEveryVolume.CopiesByTranslationsOfTheChain
import YangMills.Construction.HullsInEveryVolume.NormOfAUnit
import YangMills.Construction.HullsInEveryVolume.PlacesFarApartAreRare
import YangMills.Construction.HullsInEveryVolume.ReachOfAUnit
import YangMills.Construction.HullsInEveryVolume.TranslationsMoveAUnit
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainMovesWithATranslationProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
namespace UnitNormBound
section Estimates
private theorem exists_threshold_affine_log_range_le (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      2 + D * Real.log x * (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ c * x / 2 := by
  set Q : ℝ := 2 * (2 + 1600 * D) / c with hQ
  refine ⟨max 1 (Q ^ 2), le_max_left _ _, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxQ : Q ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  set a : ℝ := x ^ ((1 : ℝ) / 100) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow hx1 (by norm_num)
  have hpow : a ^ 100 = x := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hr : (TorusLumps.clusterRange x : ℝ) ≤ 2 * a := by
    have := (Nat.ceil_lt_add_one (a := a) (by linarith)).le
    show ((⌈a⌉₊ : ℕ) : ℝ) ≤ _
    linarith
  have hr0 : (0 : ℝ) ≤ TorusLumps.clusterRange x := Nat.cast_nonneg _
  have hr4 : (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ 16 * a ^ 4 := by
    calc (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ (2 * a) ^ 4 := pow_le_pow_left₀ hr0 hr 4
      _ = 16 * a ^ 4 := by ring
  have hlog : Real.log x ≤ 100 * a := by
    have e : Real.log x = 100 * Real.log a := by
      rw [← hpow, Real.log_pow]
      norm_num
    have := Real.log_le_sub_one_of_pos (show 0 < a by linarith)
    rw [e]
    linarith
  set q : ℝ := a ^ 50 with hq
  have hq1 : 1 ≤ q := one_le_pow₀ ha1
  have hqx : q ^ 2 = x := by
    rw [hq, ← pow_mul]
    exact hpow
  have hqQ : Q ≤ q := by
    by_contra h
    push Not at h
    have : q ^ 2 < Q ^ 2 := pow_lt_pow_left₀ h (by linarith) (by norm_num)
    linarith
  have h5 : a ^ 5 ≤ q := pow_le_pow_right₀ ha1 (by norm_num)
  have hmain : D * Real.log x * (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ 1600 * D * q := by
    calc D * Real.log x * (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ D * (100 * a) * (16 * a ^ 4) := by gcongr
      _ = 1600 * D * a ^ 5 := by ring
      _ ≤ 1600 * D * q := by gcongr
  have hfin : (2 + 1600 * D) * q ≤ c * x / 2 := by
    have e1 : Q * c = 2 * (2 + 1600 * D) := by
      rw [hQ]
      field_simp
    rw [← hqx]
    nlinarith [mul_le_mul_of_nonneg_right hqQ (show 0 ≤ c * q by positivity)]
  nlinarith
private theorem two_mul_le_natAbs_valMinAbs {N l D : ℕ} [NeZero N] (hN : N = 2 * l * D) (hl : 0 < l)
    {d : ℤ} (hd0 : d ≠ 0) (hd : |d| < D) :
    2 * l ≤ (((2 * (l : ℤ) * d : ℤ) : ZMod N).valMinAbs).natAbs := by
  set t : ℤ := ((2 * (l : ℤ) * d : ℤ) : ZMod N).valMinAbs with ht
  have hcast : ((t : ℤ) : ZMod N) = ((2 * (l : ℤ) * d : ℤ) : ZMod N) := by
    rw [ht]
    exact ZMod.coe_valMinAbs _
  have hdvd : (N : ℤ) ∣ t - 2 * (l : ℤ) * d := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast.symm |> fun h => by
    simpa using h
  have h2l : (2 * (l : ℤ)) ∣ t := by
    have h1 : (2 * (l : ℤ)) ∣ (N : ℤ) := by
      rw [hN]
      push_cast
      exact Dvd.intro _ rfl
    have h2 := h1.trans hdvd
    have h3 : (2 * (l : ℤ)) ∣ 2 * (l : ℤ) * d := Dvd.intro _ rfl
    exact (dvd_sub_left h3).mp h2
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have e : d = -((D : ℤ) * k) := by
      have : 2 * (l : ℤ) * d = 2 * (l : ℤ) * (-((D : ℤ) * k)) := by
        rw [hN] at hk
        push_cast at hk
        linarith
      exact mul_left_cancel₀ (by positivity) this
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hd0 (by simpa using e)
    have : (D : ℤ) ≤ |d| := by
      rw [e, abs_neg, abs_mul, Nat.abs_cast]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hk0)
    linarith
  have h := Nat.le_of_dvd (Int.natAbs_pos.mpr ht0) (Int.natAbs_dvd_natAbs.mpr h2l)
  simpa [Int.natAbs_mul] using h
private theorem two_pow_mul_exp_le (c x Lg CEv E4 r4 l4 n4 : ℝ) (a : ℕ) (ha : 1 ≤ a) (hLg : 0 ≤ Lg)
    (hE4 : 0 ≤ E4) (hr4 : 0 ≤ r4) (hl4 : l4 ≤ E4 * r4) (hl0 : 0 ≤ l4) (hn4 : n4 = 16 * a * l4)
    (hfl : 2 + 16 * |CEv| * E4 * Lg * r4 ≤ c * x / 2) :
    (2 : ℝ) ^ (1 + a) * Real.exp (CEv * Lg * n4 - c * x * a) ≤ Real.exp (-(c * x / 32)) ^ (16 * a) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h2 : (2 : ℝ) ^ (1 + a) ≤ Real.exp ((1 + a : ℕ) : ℝ) := by
    have e : Real.exp ((1 + a : ℕ) : ℝ) = Real.exp 1 ^ (1 + a) := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have e2 : Real.exp (-(c * x / 32)) ^ (16 * a) = Real.exp (-(c * x * a / 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e2]
  have hce : CEv * Lg * n4 ≤ a * (16 * |CEv| * E4 * Lg * r4) := by
    have h1 : CEv * (Lg * n4) ≤ |CEv| * (Lg * n4) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by rw [hn4]; positivity)
    have h3 : |CEv| * (Lg * n4) ≤ |CEv| * (Lg * (16 * a * (E4 * r4))) := by
      rw [hn4]
      gcongr
    nlinarith
  have hsum : ((1 + a : ℕ) : ℝ) + (CEv * Lg * n4 - c * x * a) ≤ -(c * x * a / 2) := by
    push_cast
    have h4 : (a : ℝ) * (2 + 16 * |CEv| * E4 * Lg * r4) ≤ a * (c * x / 2) :=
      mul_le_mul_of_nonneg_left hfl (by linarith)
    nlinarith
  calc (2 : ℝ) ^ (1 + a) * Real.exp (CEv * Lg * n4 - c * x * a)
      ≤ Real.exp ((1 + a : ℕ) : ℝ) * Real.exp (CEv * Lg * n4 - c * x * a) := by gcongr
    _ = Real.exp (((1 + a : ℕ) : ℝ) + (CEv * Lg * n4 - c * x * a)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(c * x * a / 2)) := Real.exp_le_exp.mpr hsum
end Estimates
section Measures
private theorem integral_integral_le_measureReal_of_indicator {A B E : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace E] (μ : Measure A) (ν : Measure B) (κ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] (f : A × B → E)
    (hmap : (μ.prod ν).map f = κ) (S : Set E) (Ψ : A × B → ℝ) (hΨ : Measurable Ψ)
    (h1 : ∀ p, f p ∈ S → Ψ p = 1) (h0 : ∀ p, f p ∉ S → Ψ p = 0) :
    ∫ a, ∫ b, Ψ (a, b) ∂ν ∂μ ≤ κ.real S := by
  classical
  have hae : AEMeasurable f (μ.prod ν) := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hmap
    exact IsProbabilityMeasure.ne_zero κ hmap.symm
  have hset : f ⁻¹' S = Ψ ⁻¹' {1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact h1 p
    · intro h
      by_contra hp
      rw [h0 p hp] at h
      exact zero_ne_one h
  have hS : MeasurableSet (f ⁻¹' S) := by
    rw [hset]
    exact hΨ (measurableSet_singleton 1)
  have e : Ψ = (f ⁻¹' S).indicator 1 := by
    funext p
    by_cases hp : f p ∈ S
    · rw [h1 p hp]
      simp [Set.indicator, hp]
    · rw [h0 p hp]
      simp [Set.indicator, hp]
  have hint : Integrable Ψ (μ.prod ν) := by
    rw [e]
    exact (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_prod (fun p => Ψ p) hint]
  have e2 : ∫ p, Ψ p ∂(μ.prod ν) = (μ.prod ν).real (f ⁻¹' S) := by
    rw [e]
    exact integral_indicator_one hS
  rw [e2]
  have hle := Measure.le_map_apply hae S
  rw [hmap] at hle
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle
variable {ℓ : TorusLumps.StepParameters}
private theorem isProbabilityMeasure_chainNoiseLaw : ∀ (s n : ℕ) [NeZero n],
    IsProbabilityMeasure (ChainNoise.chainNoiseLaw ℓ s n) := by apply _root_.YangMills.SharedProofs.p2413 <;> assumption
private theorem evenTranslations_separated {n l D : ℕ} [NeZero n] (hnD : n = 2 * l * D) (hl : 0 < l)
    (G : ChessboardGrids.MirrorGrid) (hG : G.side = l) (site : (Fin 4 → ℕ) → TorusFields.TorusSite n)
    (hsite : ∀ e e' i, site e i - site e' i = ((2 * (l : ℤ) * ((e i : ℤ) - (e' i : ℤ)) : ℤ) : ZMod n))
    (e e' : Fin 4 → ℕ) (he : e ∈ G.evenTranslations n) (he' : e' ∈ G.evenTranslations n) (hne : e ≠ e') :
    2 * l ≤ TorusFields.supDist (site e) (site e') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hD : n / (2 * G.side) = D := by
    rw [hG, hnD]
    exact Nat.mul_div_cancel_left _ (by omega)
  have h1 : e i < D := by
    have := Fintype.mem_piFinset.mp he i
    rwa [Finset.mem_range, hD] at this
  have h2 : e' i < D := by
    have := Fintype.mem_piFinset.mp he' i
    rwa [Finset.mem_range, hD] at this
  have hd0 : (e i : ℤ) - (e' i : ℤ) ≠ 0 := by
    intro h
    apply hi
    omega
  have hd : |(e i : ℤ) - (e' i : ℤ)| < D := by
    rw [abs_lt]
    omega
  have hfar := two_mul_le_natAbs_valMinAbs hnD hl hd0 hd
  rw [← hsite] at hfar
  exact le_trans hfar (Finset.le_sup (f := fun i => ((site e i - site e' i).valMinAbs).natAbs) (Finset.mem_univ i))
open Classical in
private theorem chessboardNorm_pow_le_separated_units (hCop : ChainNoise.translatedCopiesBoundStatement)
    (T : WeightedResponses.StageTower ℓ) (rule : ChainNoise.NoiseRule ℓ) {β : ℝ} (hβ : 0 < β) {u n M : ℕ}
    [NeZero n] (hodd : Odd ℓ.side) (hL : 2 ^ 16 ≤ ℓ.side) (hnM : n = 2 * ℓ.side ^ M)
    (G : ChessboardGrids.MirrorGrid) {r : ℕ} (hr1 : 1 ≤ r)
    (hside : G.side = ChessboardGrids.leastPowerAbove ℓ.side (40 * r))
    (h2 : 2 * G.side ≤ n) (z : TorusFields.TorusSite n) (c : Fin 4 → ℕ) (hc : c ∈ G.cellIndices n)
    (hin : ChainNoise.IsCellObservable ℓ G u n c (ChainNoise.unitIndicator rule T u n z))
    (hborel : ∀ z' : TorusFields.TorusSite n, Measurable (ChainNoise.unitIndicator rule T u n z'))
    (hmove : ∀ (z' : TorusFields.TorusSite n) (w : Fin 4 → ℤ)
      (p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n),
      ChainNoise.unitIndicator rule T u n z' (ChainNoise.pairTranslate ℓ u n (fun i => (ℓ.side : ℤ) * w i) p) =
        ChainNoise.unitIndicator rule T u n (z' + TorusFields.siteOfInt fun i => (ℓ.side : ℤ) * w i) p)
    (hw : IsProbabilityMeasure (WeightedResponses.wilsonLaw β (WeightedResponses.fineSide ℓ.side u n)))
    (hk : IsProbabilityMeasure (WeightedResponses.markedSampleLaw T β u n))
    (hmap : ((WeightedResponses.wilsonLaw β (WeightedResponses.fineSide ℓ.side u n)).prod
      (ChainNoise.chainNoiseLaw ℓ u n)).map (fun p => rule.chain T u n p.1 p.2) =
      WeightedResponses.markedSampleLaw T β u n) :
    ∃ (A : Finset (TorusFields.TorusSite n)) (D : ℕ), 0 < D ∧ n = 2 * G.side * D ∧ A.Nonempty ∧
      A.card = D ^ 4 ∧ ChessboardGrids.numCells n G.side = 16 * D ^ 4 ∧
      HullTrees.Separated (2 * G.side) A ∧ G.side ≤ ℓ.side * (40 * r) ∧ 40 * r ≤ G.side ∧
      (G.atDepth ℓ.side u).chessboardNormAt β (WeightedResponses.fineSide ℓ.side u n) c
          (ChainNoise.noiseExpectation ℓ u n (ChainNoise.unitIndicator rule T u n z)) ^
          ChessboardGrids.numCells n G.side ≤
        (WeightedResponses.markedSampleLaw T β u n).real {w | ∀ z' ∈ A, HullTrees.IsUnit T u n w z'} := by
  have hL1 : 1 < ℓ.side := by omega
  have h40 : 1 < 40 * r := by omega
  have hp1 : 0 < Nat.clog ℓ.side (40 * r) := Nat.clog_pos hL1 h40
  obtain ⟨p, hp⟩ : ∃ p, Nat.clog ℓ.side (40 * r) = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp1).symm⟩
  have hl : G.side = ℓ.side ^ (p + 1) := by
    rw [hside, ChessboardGrids.leastPowerAbove, hp]
  have hlow : 40 * r ≤ G.side := by
    rw [hside]
    exact Nat.le_pow_clog hL1 _
  have hhigh : G.side ≤ ℓ.side * (40 * r) := by
    have h := Nat.pow_pred_clog_lt_self hL1 h40
    rw [hp] at h
    simp only [Nat.pred_succ] at h
    rw [hl, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ h.le
  have hlpos : 0 < G.side := by omega
  have hpM : p + 1 ≤ M := by
    have : ℓ.side ^ (p + 1) ≤ ℓ.side ^ M := by
      rw [← hl]
      omega
    exact (Nat.pow_le_pow_iff_right hL1).mp this
  have hgrid : ChessboardGrids.IsGridOfTorus G ℓ.side M := ⟨p + 1, by omega, hpM, hl⟩
  set D : ℕ := ℓ.side ^ (M - (p + 1)) with hDdef
  have hDpos : 0 < D := pow_pos (by omega) _
  have hnD : n = 2 * G.side * D := by
    rw [hnM, hl, hDdef, mul_assoc, ← pow_add, Nat.add_sub_cancel' hpM]
  let wv : (Fin 4 → ℕ) → Fin 4 → ℤ := fun e i => 2 * (ℓ.side : ℤ) ^ p * (e i : ℤ)
  let site : (Fin 4 → ℕ) → TorusFields.TorusSite n :=
    fun e => z + TorusFields.siteOfInt fun i => (ℓ.side : ℤ) * wv e i
  have hvec : ∀ (e : Fin 4 → ℕ) (i : Fin 4), 2 * (G.side : ℤ) * (e i : ℤ) = (ℓ.side : ℤ) * wv e i := by
    intro e i
    simp only [wv]
    rw [hl]
    push_cast
    ring
  have hsite : ∀ e e' i, site e i - site e' i =
      ((2 * (G.side : ℤ) * ((e i : ℤ) - (e' i : ℤ)) : ℤ) : ZMod n) := by
    intro e e' i
    have h1 := hvec e i
    have h2' := hvec e' i
    simp only [site, Pi.add_apply, TorusFields.siteOfInt]
    rw [← h1, ← h2']
    push_cast
    ring
  have happ : ∀ e ∈ G.evenTranslations n, ∀ e' ∈ G.evenTranslations n, e ≠ e' →
      2 * G.side ≤ TorusFields.supDist (site e) (site e') :=
    fun e he e' he' hne => evenTranslations_separated hnD hlpos G rfl site hsite e e' he he' hne
  have hinj : Set.InjOn site (G.evenTranslations n : Set (Fin 4 → ℕ)) := by
    intro e he e' he' h
    by_contra hne
    have h3 := happ e he e' he' hne
    rw [h] at h3
    have : TorusFields.supDist (site e') (site e') = 0 := by
      simp [TorusFields.supDist]
    omega
  have hD' : n / (2 * G.side) = D := by
    conv_lhs => rw [hnD]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hcardE : (G.evenTranslations n).card = D ^ 4 := by
    simp [ChessboardGrids.MirrorGrid.evenTranslations, Fintype.card_piFinset, hD']
  have hcount : ChessboardGrids.numCells n G.side = 16 * D ^ 4 := by
    have h2D : n = G.side * (2 * D) := by
      rw [hnD]
      ring
    have : n / G.side = 2 * D := by
      conv_lhs => rw [h2D]
      exact Nat.mul_div_cancel_left _ hlpos
    rw [ChessboardGrids.numCells, this]
    ring
  refine ⟨(G.evenTranslations n).image site, D, hDpos, hnD, ?_, ?_, hcount, ?_, hhigh, hlow, ?_⟩
  · refine Finset.Nonempty.image ⟨0, ?_⟩ _
    refine Fintype.mem_piFinset.mpr fun i => ?_
    rw [Finset.mem_range, hD']
    exact hDpos
  · rw [Finset.card_image_of_injOn hinj, hcardE]
  · intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hb
    exact happ e he e' he' fun h => hab (by rw [h])
  · have hcop := hCop ℓ β u n M G hodd hL hβ hnM hgrid h2 c (ChainNoise.unitIndicator rule T u n z) hc hin
    refine le_trans hcop ?_
    have hnoise := isProbabilityMeasure_chainNoiseLaw (ℓ := ℓ) u n
    let Ψ : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n → ℝ :=
      fun p => ∏ e ∈ G.evenTranslations n,
        ChainNoise.unitIndicator rule T u n z
          (ChainNoise.pairTranslate ℓ u n (fun i => 2 * (G.side : ℤ) * (e i : ℤ)) p) ^ 16
    have hΨ : ∀ p, Ψ p = ∏ e ∈ G.evenTranslations n, ChainNoise.unitIndicator rule T u n (site e) p ^ 16 := by
      intro p
      refine Finset.prod_congr rfl fun e _ => ?_
      have e1 : (fun i => 2 * (G.side : ℤ) * (e i : ℤ)) = fun i => (ℓ.side : ℤ) * wv e i := funext (hvec e)
      rw [e1, hmove]
    have hmeas : Measurable Ψ := by
      have : Ψ = fun p => ∏ e ∈ G.evenTranslations n, ChainNoise.unitIndicator rule T u n (site e) p ^ 16 :=
        funext hΨ
      rw [this]
      exact Finset.measurable_prod _ fun e _ => (hborel (site e)).pow_const 16
    have hone : ∀ (z' : TorusFields.TorusSite n)
        (p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n),
        HullTrees.IsUnit T u n (rule.chain T u n p.1 p.2) z' → ChainNoise.unitIndicator rule T u n z' p = 1 :=
      fun z' p h => by
        unfold ChainNoise.unitIndicator
        exact if_pos h
    have hzero : ∀ (z' : TorusFields.TorusSite n)
        (p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n),
        ¬ HullTrees.IsUnit T u n (rule.chain T u n p.1 p.2) z' → ChainNoise.unitIndicator rule T u n z' p = 0 :=
      fun z' p h => by
        unfold ChainNoise.unitIndicator
        exact if_neg h
    refine integral_integral_le_measureReal_of_indicator
      (WeightedResponses.wilsonLaw β (WeightedResponses.fineSide ℓ.side u n)) (ChainNoise.chainNoiseLaw ℓ u n)
      (WeightedResponses.markedSampleLaw T β u n) (fun p => rule.chain T u n p.1 p.2) hmap _ Ψ hmeas ?_ ?_
    · intro p hp
      rw [hΨ]
      refine Finset.prod_eq_one fun e he => ?_
      rw [hone _ _ (hp _ (Finset.mem_image_of_mem _ he))]
      norm_num
    · intro p hp
      simp only [Set.mem_ofPred_eq, not_forall] at hp
      obtain ⟨z', hz', hu⟩ := hp
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz'
      rw [hΨ]
      refine Finset.prod_eq_zero he ?_
      rw [hzero _ _ hu]
      norm_num
end Measures
section Flow
private theorem couplingFlow_expansion_until_crossing {Tb : RenormalizationStepParameters.ParameterAssignment} {y g β : ℝ} {K : ℕ}
    (hB : 0 ≤ Tb.B) (hret : StepReturn.ExpansionReturnsAt (Tb.stepParameters y))
    (h0 : ∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (Tb.stepParameters y) 0 β (TorusLumps.wilsonWeight β))
    (hp : HullTrees.FlowCrossing Tb y g β K) :
    ∀ j ≤ K, y ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1 ∧
      TorusLumps.HasExpansion (Tb.stepParameters y) j (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1
        (TorusLumps.couplingFlow (Tb.stepParameters y) β j).2 ∧
      (j < K → |(TorusLumps.couplingFlow (Tb.stepParameters y) β (j + 1)).1 -
        (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1| ≤ 2 * Tb.B) := by apply _root_.YangMills.SharedProofs.p36592 <;> assumption
private theorem clusterRange_mono {x x' : ℝ} (h0 : 0 ≤ x) (h : x ≤ x') :
    TorusLumps.clusterRange x ≤ TorusLumps.clusterRange x' := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
end Flow
end UnitNormBound
open UnitNormBound in
theorem unitProbabilityNormBound (hCop : ChainNoise.translatedCopiesBoundStatement)
    (hR : HullTrees.unitIndicatorLocal) (hP : HullTrees.separatedUnitsRareStatement)
    (hN : ChainNoise.noiseRepresentationStatement) (hT : unitTranslationStatement)
    (hLaw : WeightedResponses.forgetLastStepStatement) : unitProbabilityNormBoundStatement := by
  obtain ⟨CE, hP⟩ := hP
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, hR⟩ := hR a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, hP⟩ := hP a ha
  obtain ⟨L₃, rt₃, C₃, hrt₃, hN⟩ := hN a ha
  obtain ⟨L₄, rt₄, C₄, hrt₄, hT⟩ := hT a ha
  refine ⟨max L₁ (max L₂ (max L₃ L₄)), fun c => min (rt₁ c) (min (rt₂ c) (min (rt₃ c) (rt₄ c))),
    max C₁ (max C₂ (max C₃ C₄)), fun c => lt_min (hrt₁ c) (lt_min (hrt₂ c) (lt_min (hrt₃ c) (hrt₄ c))), ?_⟩
  intro L hodd hL₀ Tb hTa hTL hD hcold hhalf hrt hCd
  simp only [max_le_iff] at hL₀ hCd
  simp only [le_min_iff] at hrt
  obtain ⟨l₁, l₂, l₃, l₄⟩ := hL₀
  obtain ⟨c₁, c₂, c₃, c₄⟩ := hCd
  obtain ⟨r₁, r₂, r₃, r₄⟩ := hrt
  obtain ⟨M₁, hR⟩ := hR L hodd l₁ Tb hTa hTL hD hcold hhalf r₁ c₁
  obtain ⟨M₂, hP⟩ := hP L hodd l₂ Tb hTa hTL hD hcold hhalf r₂ c₂
  obtain ⟨M₃, hN⟩ := hN L hodd l₃ Tb hTa hTL hD hcold hhalf r₃ c₃
  obtain ⟨M₄, hT⟩ := hT L hodd l₄ Tb hTa hTL hD hcold hhalf r₄ c₄
  refine ⟨max M₁ (max M₂ (max M₃ M₄)), ?_⟩
  intro Kr hM hη hN₀ hfit hresp
  simp only [max_le_iff] at hM
  obtain ⟨m₁, m₂, m₃, m₄⟩ := hM
  obtain ⟨y₁, hR⟩ := hR Kr m₁ hη hN₀ hfit hresp
  obtain ⟨y₂, hP⟩ := hP Kr m₂ hη hN₀ hfit hresp
  obtain ⟨y₃, hN⟩ := hN Kr m₃ hη hN₀ hfit hresp
  obtain ⟨y₄, hT⟩ := hT Kr m₄ hη hN₀ hfit hresp
  have hcpos : 0 < HullTrees.unitDecayRate Tb := by
    unfold HullTrees.unitDecayRate
    have h1 : 0 < Tb.κ * Tb.threshold ^ 2 := mul_pos hD.κ_pos (pow_pos hD.σ_pos 2)
    have h2 := lt_min h1 hD.cE_pos
    positivity
  obtain ⟨y₅, hy₅, hfl⟩ := exists_threshold_affine_log_range_le (HullTrees.unitDecayRate Tb)
    (16 * |CE Tb| * (40 * (Tb.side : ℝ)) ^ 4) hcpos (by positivity)
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ Tb.floorMin)))), ?_⟩
  intro y hy hret h0 g β K m T u n _ hlev rule hr G hside h2 z c hc hbox
  simp only [max_le_iff] at hy
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := hy
  have hfits : (Tb.stepParameters y).Admissible := hD.fits y e₆
  have hB : 0 ≤ Tb.B := le_trans zero_le_one hD.B_ge
  have hone : (1 : ℝ) ≤ y := hfits.y₁_ge
  have hrun := couplingFlow_expansion_until_crossing hB hret h0 hlev.chain.toCrossingVolume.toFlowCrossing
  have hxy : y ≤ HullTrees.stageCoupling T u := by
    have h := (hrun u hlev.le).1
    have e : (T.stage u).coupling = (TorusLumps.couplingFlow (Tb.stepParameters y) β u).1 :=
      hlev.chain.follows u (by have := hlev.le; omega)
    show y ≤ (T.stage u).coupling
    rw [e]
    exact h
  have hβ : 0 < β := by
    have h1 := hlev.chain.upper_le
    have h2' := hlev.chain.le_inv_sq
    have h3 : HullTrees.windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
    linarith
  have hr16 : 2 ^ 16 ≤ HullTrees.stageRange T u := by
    have h := hfits.range_ge
    have e : (Tb.stepParameters y).y₁ = y := rfl
    rw [e] at h
    exact le_trans h (clusterRange_mono (by linarith) hxy)
  have hnM : n = 2 * (Tb.stepParameters y).side ^ (m + (K - u)) := by
    rw [hlev.side_eq]
    show WeightedResponses.fineSide Tb.side (K - u) (2 * Tb.side ^ m) = 2 * Tb.side ^ (m + (K - u))
    rw [WeightedResponses.fineSide_eq, pow_add]
    ring
  have hw : IsProbabilityMeasure
      (WeightedResponses.wilsonLaw β (WeightedResponses.fineSide (Tb.stepParameters y).side u n)) :=
    (hLaw (Tb.stepParameters y) hfits hfits.depth_lt T hlev.chain.cutoff_bottom hlev.chain.marks β 0
      (WeightedResponses.fineSide (Tb.stepParameters y).side u n)).1
  have hk : IsProbabilityMeasure (WeightedResponses.markedSampleLaw T β u n) :=
    (hLaw (Tb.stepParameters y) hfits hfits.depth_lt T hlev.chain.cutoff_bottom hlev.chain.marks β u n).1
  have hreach := hR y e₁ hret h0 g β K m T u n hlev rule hr
  have hsub : ∀ z' : TorusFields.TorusSite n, HullTrees.box z' (7 * HullTrees.stageRange T u) ⊆
      (⟨n + 1, 0⟩ : ChessboardGrids.MirrorGrid).cellSites n 0 := by
    intro z' x _
    classical
    simp only [ChessboardGrids.MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and]
    funext i
    exact Nat.div_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt _) (Nat.le_succ _))
  have hborel : ∀ z' : TorusFields.TorusSite n, Measurable (ChainNoise.unitIndicator rule T u n z') :=
    fun z' => ((hreach z').2 _ _ (hsub z')).measurable
  obtain ⟨A, D, hDpos, hnD, hne, hcard, hcount, happ, hhigh, hlow, hle⟩ :=
    chessboardNorm_pow_le_separated_units hCop T rule hβ hfits.L_odd hfits.L_ge hnM G
      (r := HullTrees.stageRange T u) (by omega) hside h2 z c hc
      ((hreach z).2 G c hbox) hborel (hT y e₄ hret h0 g β K m T u n hlev rule hr) hw hk
      ((hN y e₃ hret h0 g β K m T hlev.chain).2 rule hr u n hlev)
  have hb := hP y e₂ hret h0 g β K m T u n hlev A hne
    (fun a' ha' b' hb' hab => le_trans (by omega) (happ a' ha' b' hb' hab))
  have ha1 : 1 ≤ A.card := hne.card_pos
  have hx1 : (1 : ℝ) ≤ HullTrees.stageCoupling T u := by linarith
  have hl4 : (G.side : ℝ) ^ 4 ≤ (40 * (Tb.side : ℝ)) ^ 4 * (HullTrees.stageRange T u : ℝ) ^ 4 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 4
    have : (G.side : ℝ) ≤ (((Tb.stepParameters y).side * (40 * HullTrees.stageRange T u) : ℕ) : ℝ) := by
      exact_mod_cast hhigh
    have e : (((Tb.stepParameters y).side * (40 * HullTrees.stageRange T u) : ℕ) : ℝ) =
        40 * (Tb.side : ℝ) * (HullTrees.stageRange T u : ℝ) := by
      show ((Tb.side * (40 * HullTrees.stageRange T u) : ℕ) : ℝ) = _
      push_cast
      ring
    linarith
  have hn4 : (n : ℝ) ^ 4 = 16 * (A.card : ℝ) * (G.side : ℝ) ^ 4 := by
    have e1 : (n : ℝ) = 2 * (G.side : ℝ) * (D : ℝ) := by
      conv_lhs => rw [hnD]
      push_cast
      ring
    rw [hcard, e1]
    push_cast
    ring
  have hclasscost := two_pow_mul_exp_le (HullTrees.unitDecayRate Tb) (HullTrees.stageCoupling T u)
    (Real.log (HullTrees.stageCoupling T u)) (CE Tb) ((40 * (Tb.side : ℝ)) ^ 4)
    ((HullTrees.stageRange T u : ℝ) ^ 4) ((G.side : ℝ) ^ 4) ((n : ℝ) ^ 4) A.card ha1 (Real.log_nonneg hx1)
    (by positivity) (by positivity) hl4 (by positivity) hn4 (hfl (HullTrees.stageCoupling T u) (by linarith))
  by_contra hcon
  push Not at hcon
  have hN0 : ChessboardGrids.numCells n G.side ≠ 0 := by
    rw [hcount]
    have := pow_pos hDpos 4
    omega
  have hlt := pow_lt_pow_left₀ hcon (Real.exp_pos _).le hN0
  have e16 : ChessboardGrids.numCells n G.side = 16 * A.card := by rw [hcount, hcard]
  rw [e16] at hlt hle
  have := lt_of_lt_of_le hlt (le_trans hle (le_trans hb hclasscost))
  exact lt_irrefl _ this
end YangMills.Construction.HullsInEveryVolume
end
