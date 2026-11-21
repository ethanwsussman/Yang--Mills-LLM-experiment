import YangMills.Construction.CellOfTheFlow.TheChanceOfACellHasItsValueProof
import YangMills.Construction.FourPointCondition.EvaluationAtTheBareLevelProof
import YangMills.Construction.LawOnABoxOfTheFlow.AxialGaugeOfAColdFillingProof
import YangMills.Construction.LawOnABoxOfTheFlow.ColdEventsOfABoxAreLikely
import YangMills.Construction.LawOnABoxOfTheFlow.FitsAreRarelyLarge
import YangMills.Construction.LawOnABoxOfTheFlow.PlaquettesAreSmall
import YangMills.Construction.LawOnABoxOfTheFlow.SitesOfTheHullAreRare
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.BoxEvents
open YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses YangMills.Construction.BoxGaussian YangMills.Construction.TorusLumps YangMills.Construction.ResponseInTheExpansion YangMills.Construction.StepCosts YangMills.Construction.StepReturn
section Counting
variable {n : ℕ} [NeZero n]
private theorem card_supBall_le (o : TorusSite n) (t : ℝ) (r : ℕ) (h : t ≤ r) :
    (supBall o t).card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p104098 <;> assumption
private theorem card_plaquettesIn_le (S : Finset (TorusSite n)) : (plaquettesIn S).card ≤ 16 * S.card := by
  classical
  have hsub : plaquettesIn S ⊆ S ×ˢ ((Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin 4))) := by
    intro p hp
    have h1 := (Finset.mem_filter.1 hp).2.2 p.1 (by simp [plaquetteVertices])
    simp [h1]
  calc (plaquettesIn S).card ≤ _ := Finset.card_le_card hsub
    _ = 16 * S.card := by
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      ring
private theorem card_bondsWithin_le (S : Finset (TorusSite n)) : (bondsWithin S).card ≤ 4 * S.card := by apply _root_.YangMills.SharedProofs.p64206 <;> assumption
private theorem mem_plaquettesIn_univ {S : Finset (TorusSite n)} {p : TorusPlaquette n}
    (hp : p ∈ plaquettesIn S) : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
  classical
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2.1, fun _ _ => Finset.mem_univ _⟩
private theorem measureReal_biUnion_le_card_mul {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℝ}
    (hZ : 0 ≤ Z) (F : Finset ι) (A : ι → Set Ω) {c : ℕ} (hc : F.card ≤ c) (h : ∀ i ∈ F, μ.real (A i) ≤ Z) :
    μ.real (⋃ i ∈ F, A i) ≤ c * Z := by
  refine (measureReal_biUnion_finset_le F A).trans ((Finset.sum_le_sum h).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hZ
end Counting
section Probabilities
variable {ℓ : StepParameters}
private theorem stageState_fst_eq (T : StageTower ℓ) (k n : ℕ) [NeZero n] (u : MarkedSample ℓ k n) :
    (stageState T k n u).1 = topField ℓ k n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private theorem measurable_sample_fst (j m : ℕ) : Measurable fun u : MarkedSample ℓ (j + 1) m => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem not_cold_measureReal_le (T : StageTower ℓ) (β : ℝ) (k N : ℕ) [NeZero N] (o : TorusSite N)
    (R ρ : ℕ) (hρ : 3 * R ≤ ρ) (δ H Z : ℝ) (hH : 0 ≤ H) (hZ : 0 ≤ Z)
    [IsProbabilityMeasure (markedSampleLaw T β k N)]
    (hY : ∀ z : TorusSite N, (markedSampleLaw T β k N).real {u | z ∈ (stageState T k N u).2.1} ≤ H)
    (hP : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
      (markedSampleLaw T β k N).real {u | δ < curvature (topField ℓ k N u) p.1 p.2.1 p.2.2} ≤ Z) :
    (markedSampleLaw T β k N).real {u | ¬ IsColdOnBox o R δ (stageState T k N u).1 (stageState T k N u).2.1} ≤
      (2 * (ρ : ℝ) + 1) ^ 4 * (H + 16 * Z) := by
  classical
  set μ := markedSampleLaw T β k N
  have hb3 : (supBall o (3 * R)).card ≤ (2 * ρ + 1) ^ 4 :=
    card_supBall_le o _ ρ (by exact_mod_cast hρ)
  have hb2 : (supBall o (2 * R)).card ≤ (2 * ρ + 1) ^ 4 :=
    card_supBall_le o _ ρ (by
      have : (2 * R : ℝ) ≤ 3 * R := by nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
      exact this.trans (by exact_mod_cast hρ))
  have hp2 : (plaquettesIn (supBall o (2 * R))).card ≤ 16 * (2 * ρ + 1) ^ 4 :=
    (card_plaquettesIn_le _).trans (by omega)
  have hsub : {u | ¬ IsColdOnBox o R δ (stageState T k N u).1 (stageState T k N u).2.1} ⊆
      (⋃ z ∈ supBall o (3 * R), {u | z ∈ (stageState T k N u).2.1}) ∪
        ⋃ p ∈ plaquettesIn (supBall o (2 * R)), {u | δ < curvature (topField ℓ k N u) p.1 p.2.1 p.2.2} := by
    intro u hu
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    refine hu ⟨?_, fun p hp => ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hz3
      exact hc.1 (Set.mem_biUnion hz3 hz)
    · rw [stageState_fst_eq]
      by_contra h
      exact hc.2 (Set.mem_biUnion hp (not_le.1 h))
  have h1 := measureReal_biUnion_le_card_mul (μ := μ) hH (supBall o (3 * R))
    (fun z => {u | z ∈ (stageState T k N u).2.1}) hb3 fun z _ => hY z
  have h2 := measureReal_biUnion_le_card_mul (μ := μ) hZ (plaquettesIn (supBall o (2 * R)))
    (fun p => {u | δ < curvature (topField ℓ k N u) p.1 p.2.1 p.2.2}) hp2
    fun p hp => hP p (mem_plaquettesIn_univ hp)
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  push_cast
  ring
private theorem not_good_measureReal_le (T : StageTower ℓ) (β : ℝ) (k s top : ℕ) (δ f Zp Zf : ℝ) (ρ : ℕ)
    (hZp : 0 ≤ Zp) (hZf : 0 ≤ Zf) (hρ : ∀ i ≤ s, descendingRadius ℓ.side top i ≤ ρ)
    (hprob : ∀ (j m : ℕ) [NeZero m], j ≤ k + s → IsProbabilityMeasure (markedSampleLaw T β j m))
    (hmarg : ∀ (j m : ℕ) [NeZero m], j < k + s →
      (markedSampleLaw T β (j + 1) m).map (fun u => u.1) = markedSampleLaw T β j (m * ℓ.side))
    (hplaq : ∀ (j m : ℕ) [NeZero m], k ≤ j → j ≤ k + s → 2 * ℓ.side ∣ m → ℓ.side * ℓ.n₀ ≤ m →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
        (markedSampleLaw T β j m).real {u | δ < curvature (topField ℓ j m u) p.1 p.2.1 p.2.2} ≤ Zp)
    (hfit : ∀ (j m : ℕ) [NeZero m], k ≤ j → j < k + s → ∀ c : TorusBond m,
      (markedSampleLaw T β (j + 1) m).real
        {u | f < bondFit ℓ (topField ℓ j (m * ℓ.side) u.1) u.2.2.1 u.2.1 c} ≤ Zf) :
    ∀ d : ℕ, d ≤ s → ∀ (n : ℕ) [NeZero n] (o : TorusSite (fineSide ℓ.side d n)), 2 * ℓ.side ∣ n →
      ℓ.side * ℓ.n₀ ≤ n →
      (markedSampleLaw T β (k + d) n).real {u | ¬ IsGoodSample ℓ k s top δ f d n u o} ≤
        ((d : ℝ) + 1) * (16 * (2 * (ρ : ℝ) + 1) ^ 4 * (Zp + Zf)) := by
  classical
  intro d
  induction d with
  | zero =>
    intro _ n _ o h1 h2
    haveI := hprob k n (by omega)
    have hb : (supBall o (descendingRadius ℓ.side top s)).card ≤ (2 * ρ + 1) ^ 4 :=
      card_supBall_le o _ ρ (by exact_mod_cast hρ s le_rfl)
    have hp : (plaquettesIn (supBall o (descendingRadius ℓ.side top s))).card ≤ 16 * (2 * ρ + 1) ^ 4 :=
      (card_plaquettesIn_le _).trans (by omega)
    have hsub : {u | ¬ IsGoodSample ℓ k s top δ f 0 n u o} ⊆
        ⋃ p ∈ plaquettesIn (supBall o (descendingRadius ℓ.side top s)),
          {u | δ < curvature (topField ℓ k n u) p.1 p.2.1 p.2.2} := by
      intro u hu
      by_contra hc
      refine hu ?_
      show ∀ p ∈ plaquettesIn (supBall o (descendingRadius ℓ.side top s)),
        curvature (topField ℓ k n u) p.1 p.2.1 p.2.2 ≤ δ
      intro p hp'
      by_contra h
      exact hc (Set.mem_biUnion hp' (not_le.1 h))
    have h3 := measureReal_biUnion_le_card_mul (μ := markedSampleLaw T β k n) hZp
      (plaquettesIn (supBall o (descendingRadius ℓ.side top s)))
      (fun p => {u | δ < curvature (topField ℓ k n u) p.1 p.2.1 p.2.2}) hp
      fun p hp' => hplaq k n le_rfl (by omega) h1 h2 p (mem_plaquettesIn_univ hp')
    refine (measureReal_mono hsub (measure_ne_top (markedSampleLaw T β k n) _)).trans (h3.trans ?_)
    have hc0 : (0 : ℝ) ≤ 16 * (2 * (ρ : ℝ) + 1) ^ 4 := by positivity
    push_cast
    nlinarith [mul_nonneg hc0 hZf]
  | succ d ih =>
    intro hd n _ o h1 h2
    haveI := hprob (k + d + 1) n (by omega)
    haveI := hprob (k + d) (n * ℓ.side) (by omega)
    set r := descendingRadius ℓ.side top (s - (d + 1)) with hr
    set z := siteAbove ℓ.side (d + 1) n o with hz
    have hb : (supBall z r).card ≤ (2 * ρ + 1) ^ 4 := card_supBall_le z _ ρ (by exact_mod_cast hρ _ (by omega))
    have hp : (plaquettesIn (supBall z r)).card ≤ 16 * (2 * ρ + 1) ^ 4 :=
      (card_plaquettesIn_le _).trans (by omega)
    have hc : (bondsWithin (supBall z r)).card ≤ 4 * (2 * ρ + 1) ^ 4 :=
      (card_bondsWithin_le _).trans (by omega)
    set B : Set (MarkedSample ℓ (k + d) (n * ℓ.side)) :=
      {v | ¬ IsGoodSample ℓ k s top δ f d (n * ℓ.side) v o} with hB
    have hsub : {u : MarkedSample ℓ (k + d + 1) n | ¬ IsGoodSample ℓ k s top δ f (d + 1) n u o} ⊆
        ((⋃ p ∈ plaquettesIn (supBall z r), {u : MarkedSample ℓ (k + d + 1) n |
            δ < curvature (topField ℓ (k + d + 1) n u) p.1 p.2.1 p.2.2}) ∪
          ⋃ c ∈ bondsWithin (supBall z r), {u : MarkedSample ℓ (k + d + 1) n |
            f < bondFit ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) u.2.2.1 u.2.1 c}) ∪
        (fun u : MarkedSample ℓ (k + d + 1) n => u.1) ⁻¹' B := by
      intro u hu
      by_contra hcon
      rw [Set.mem_union, Set.mem_union, not_or, not_or] at hcon
      refine hu ⟨fun p hp' => ?_, fun c hc' => ?_, ?_⟩
      · by_contra h
        exact hcon.1.1 (Set.mem_biUnion hp' (not_le.1 h))
      · by_contra h
        exact hcon.1.2 (Set.mem_biUnion hc' (not_le.1 h))
      · by_contra h
        exact hcon.2 h
    have h3 := measureReal_biUnion_le_card_mul (μ := markedSampleLaw T β (k + d + 1) n) hZp
      (plaquettesIn (supBall z r))
      (fun p => {u | δ < curvature (topField ℓ (k + d + 1) n u) p.1 p.2.1 p.2.2}) hp
      fun p hp' => hplaq (k + d + 1) n (by omega) (by omega) h1 h2 p (mem_plaquettesIn_univ hp')
    have h4 := measureReal_biUnion_le_card_mul (μ := markedSampleLaw T β (k + d + 1) n) hZf
      (bondsWithin (supBall z r))
      (fun c => {u | f < bondFit ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) u.2.2.1 u.2.1 c}) hc
      fun c _ => hfit (k + d) n (by omega) (by omega) c
    have h5 : (markedSampleLaw T β (k + d + 1) n).real
        ((fun u : MarkedSample ℓ (k + d + 1) n => u.1) ⁻¹' B) ≤
        (markedSampleLaw T β (k + d) (n * ℓ.side)).real B := by
      refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
      rw [← hmarg (k + d) n (by omega)]
      exact Measure.le_map_apply (measurable_sample_fst (k + d) n).aemeasurable B
    have h6 := ih (by omega) (n * ℓ.side) o (Dvd.dvd.mul_right h1 _)
      (h2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne ℓ.side))))
    have hc0 : (0 : ℝ) ≤ (2 * (ρ : ℝ) + 1) ^ 4 := by positivity
    have hstep := (measureReal_mono (μ := markedSampleLaw T β (k + d + 1) n) hsub).trans
      ((measureReal_union_le _ _).trans (add_le_add ((measureReal_union_le _ _).trans (add_le_add h3 h4))
        (h5.trans h6)))
    refine hstep.trans ?_
    push_cast
    nlinarith [mul_nonneg hc0 hZf]
end Probabilities
section Estimates
private theorem boxRadius_bounds {κ₀ x : ℝ} (hx : 1 ≤ x) (h2 : κ₀ ≤ 1 / 21) :
    1 ≤ boxRadius κ₀ x ∧ (boxRadius κ₀ x : ℝ) ≤ 2 * x ^ (1 / 21 : ℝ) := by
  have hp : 0 < x ^ κ₀ := Real.rpow_pos_of_pos (by linarith) _
  have h1 : 1 ≤ x ^ (1 / 21 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have h3 : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h2
  refine ⟨Nat.ceil_pos.2 hp, ?_⟩
  have h4 := Nat.ceil_lt_add_one hp.le
  unfold boxRadius
  linarith
private theorem pow_coarseningSteps_le {L R : ℕ} (hL : 2 ≤ L) (hR : 1 ≤ R) :
    L ^ coarseningSteps L R ≤ L * R := by
  set S : Set ℕ := {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s} with hS
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  show L ^ sInf S ≤ L * R
  rcases Nat.eq_zero_or_pos (sInf S) with h0 | h0
  · rw [h0, pow_zero]
    exact Nat.mul_pos (by omega) hR
  · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero h0.ne'
    have hnot : t ∉ S := Nat.notMem_of_lt_sInf (by omega)
    have h1 : (L : ℝ) ^ t < (R : ℝ) ^ (2 / 3 : ℝ) := not_le.1 hnot
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have h2 : (R : ℝ) ^ (2 / 3 : ℝ) ≤ R := by
      have := Real.rpow_le_rpow_of_exponent_le hR1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
      simpa using this
    have h3 : L ^ t ≤ R := by
      have : (L : ℝ) ^ t ≤ R := (h1.trans_le h2).le
      exact_mod_cast this
    rw [ht, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ h3
private theorem descendingRadius_le {L : ℕ} (hL : 1 ≤ L) (top : ℕ) (i : ℕ) :
    descendingRadius L top i ≤ L ^ i * (top + 4 * i) := by
  induction i with
  | zero => simp [descendingRadius]
  | succ i ih =>
    show L * descendingRadius L top i + 4 * L ≤ L ^ (i + 1) * (top + 4 * (i + 1))
    have h1 : 1 ≤ L ^ i := Nat.one_le_pow _ _ hL
    have h2 : L * descendingRadius L top i ≤ L * (L ^ i * (top + 4 * i)) := Nat.mul_le_mul_left _ ih
    have h3 : 4 * L ≤ 4 * (L * L ^ i) := by nlinarith
    have h4 : L ^ (i + 1) * (top + 4 * (i + 1)) = L * (L ^ i * (top + 4 * i)) + 4 * (L * L ^ i) := by
      rw [pow_succ]
      ring
    omega
private theorem eventually_tail_le_rpow (M A C₁ D c : ℝ) (hD : 0 < D) (hc : 0 < c) (hC : 0 < C₁) (p : ℕ) :
    ∀ᶠ x : ℝ in atTop, M * x ^ 2 * (Real.exp (-(c * x)) +
      Real.exp (A * Real.log (C₁ * x) - D * Real.log x ^ 2)) ≤ x ^ (-(p : ℝ)) := by
  set q := p + 2 with hq
  set M₁ := |M| + 1 with hM₁
  have hM0 : 0 < M₁ := by positivity
  have t1 : Tendsto (fun x : ℝ => (c * x) ^ q * Real.exp (-(c * x))) atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero q).comp (tendsto_id.const_mul_atTop hc)
  have hcq : 0 < c ^ q := by positivity
  have e1 : ∀ᶠ x : ℝ in atTop, (c * x) ^ q * Real.exp (-(c * x)) < c ^ q / (2 * M₁) :=
    (tendsto_order.1 t1).2 _ (by positivity)
  set b : ℝ := (q : ℝ) + A with hb
  set c0 : ℝ := Real.log M₁ + A * Real.log C₁ + 1 with hc0
  set U : ℝ := (|b| + |c0| + 1) / D + 1 with hU
  have e2 : ∀ᶠ x : ℝ in atTop, U ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop U
  filter_upwards [e1, e2, eventually_gt_atTop 0] with x h1 h2 hx
  set u := Real.log x with hu
  have hU1 : 1 ≤ U := by
    have : 0 ≤ (|b| + |c0| + 1) / D := by positivity
    linarith
  have hu1 : 1 ≤ u := hU1.trans h2
  have hxe : Real.exp u = x := Real.exp_log hx
  have hDu : |b| + |c0| + 1 ≤ D * u := by
    have h3 : (|b| + |c0| + 1) / D ≤ u := by linarith
    rw [div_le_iff₀ hD] at h3
    linarith
  have hquad : b * u + c0 ≤ D * u ^ 2 := by
    have h4 : (|b| + |c0| + 1) * u ≤ D * u * u := mul_le_mul_of_nonneg_right hDu (by linarith)
    have h5 : b * u ≤ |b| * u := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
    have h6 : c0 ≤ |c0| * u := (le_abs_self c0).trans (le_mul_of_one_le_right (abs_nonneg _) hu1)
    nlinarith
  have hxq : x ^ q = Real.exp (q * u) := by rw [Real.exp_nat_mul, hxe]
  have hlog : Real.log (C₁ * x) = Real.log C₁ + u := Real.log_mul hC.ne' hx.ne'
  have hexp1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact inv_anti₀ (by norm_num) this
  have main2 : M₁ * x ^ q * Real.exp (A * Real.log (C₁ * x) - D * u ^ 2) ≤ 1 / 2 := by
    have e : M₁ * x ^ q * Real.exp (A * Real.log (C₁ * x) - D * u ^ 2) =
        Real.exp (Real.log M₁ + q * u + (A * (Real.log C₁ + u) - D * u ^ 2)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hM0, hxq, hlog]
    rw [e]
    refine le_trans (Real.exp_le_exp.2 ?_) hexp1
    simp only [hb, hc0] at hquad
    nlinarith
  have main1 : M₁ * x ^ q * Real.exp (-(c * x)) ≤ 1 / 2 := by
    rw [mul_pow, mul_assoc, lt_div_iff₀ (by positivity)] at h1
    have h7 : c ^ q * (x ^ q * Real.exp (-(c * x)) * (2 * M₁)) < c ^ q * 1 := by
      calc _ = c ^ q * (x ^ q * Real.exp (-(c * x))) * (2 * M₁) := by ring
        _ < c ^ q := h1
        _ = c ^ q * 1 := by ring
    have h8 := lt_of_mul_lt_mul_left h7 hcq.le
    nlinarith
  have hP : 0 < x ^ p := by positivity
  rw [Real.rpow_neg hx.le, Real.rpow_natCast, ← one_div, le_div_iff₀ hP]
  have hMM : M ≤ M₁ := by
    have := le_abs_self M
    linarith
  have hs : 0 ≤ x ^ 2 * (Real.exp (-(c * x)) + Real.exp (A * Real.log (C₁ * x) - D * u ^ 2)) * x ^ p := by
    positivity
  have e : M₁ * x ^ 2 * (Real.exp (-(c * x)) + Real.exp (A * Real.log (C₁ * x) - D * u ^ 2)) * x ^ p =
      M₁ * x ^ q * Real.exp (-(c * x)) + M₁ * x ^ q * Real.exp (A * Real.log (C₁ * x) - D * u ^ 2) := by
    rw [hq, pow_add]
    ring
  have h9 := mul_le_mul_of_nonneg_right hMM hs
  nlinarith
private theorem side_le_and_dvd {L n₀ s n e R : ℕ} {x v : ℝ} (hL : 2 ≤ L) (hn₀ : 2 ≤ n₀) (hv1 : 1 ≤ v)
    (hv : 2 * (L : ℝ) ^ 2 * n₀ ≤ v) (hLs : L ^ s ≤ L * R) (hRv : (R : ℝ) ≤ 2 * v) (hN : n * L ^ s = 2 * L ^ e)
    (hvx : v ^ 2 ≤ x) (hw : x ≤ ((n * L ^ s : ℕ) : ℝ)) : L * n₀ ≤ n ∧ 2 * L ∣ n := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLsr : ((L : ℝ) ^ s) ≤ L * (2 * v) := by
    have h1 : ((L ^ s : ℕ) : ℝ) ≤ ((L * R : ℕ) : ℝ) := by exact_mod_cast hLs
    push_cast at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hRv hLr.le)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : v * v ≤ (n * (L * 2)) * v := by
    have h2 : v ^ 2 ≤ (n : ℝ) * (L : ℝ) ^ s := by
      have := hvx.trans hw
      push_cast at this
      exact this
    have h3 := mul_le_mul_of_nonneg_left hLsr hn0
    nlinarith
  have h2 : v ≤ n * (L * 2) := le_of_mul_le_mul_right h1 (by linarith)
  have h3 : (L : ℝ) * n₀ ≤ n := by
    have h4 : (2 * L) * ((L : ℝ) * n₀) ≤ (2 * L) * n := by nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  have h4 : L * n₀ ≤ n := by exact_mod_cast h3
  refine ⟨h4, ?_⟩
  have h5 : 2 * L ≤ n := by nlinarith
  have hLpos : 0 < L ^ s := by positivity
  have h6 : L ^ (s + 1) ≤ L ^ e := by
    have : 2 * L ^ (s + 1) ≤ 2 * L ^ e := by
      rw [← hN, pow_succ]
      nlinarith
    omega
  have h7 : s + 1 ≤ e := (Nat.pow_le_pow_iff_right (by omega)).1 h6
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h7
  have h8 : n * L ^ s = (2 * L * L ^ m) * L ^ s := by
    rw [hN]
    ring
  exact ⟨L ^ m, Nat.eq_of_mul_eq_mul_right hLpos h8⟩
private theorem baseCellSide_le {L r : ℕ} (hL : 2 ≤ L) (hr : 1 ≤ r) :
    CellWindows.baseCellSide L r ≤ L * (2 ^ 7 * r) := by apply _root_.YangMills.SharedProofs.p1293 <;> assumption
private theorem couplingFlow_hasExpansion (ℓ : StepParameters) (hRet : ExpansionReturnsAt ℓ)
    (hW : ∀ β, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) (β : ℝ) :
    ∀ t, (∀ j ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 ∧
        |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p51822 <;> assumption
private theorem half_sq_lt_half_sq {δ u : ℝ} (h0 : 0 < δ) (h : δ < u) : δ ^ 2 / 2 < u ^ 2 / 2 := by
  nlinarith
private theorem plaquette_exponent_le {CP CF cK C₁ D x xj f : ℝ} (hCF : 0 < CF) (hx2 : 2 ≤ x) (hC : 2 ≤ C₁)
    (hD : D ≤ 2 * cK) (hcK : 0 < cK) (hj1 : x / 2 ≤ xj) (hj2 : xj ≤ 2 * x) (hf : f = Real.log x ^ 2 / x) :
    CP * Real.log xj - 2 * cK * xj * (2 * f) ≤ (|CP| + CF) * Real.log (C₁ * x) - D * Real.log x ^ 2 := by
  have hxj1 : 1 ≤ xj := by linarith
  have hlj0 : 0 ≤ Real.log xj := Real.log_nonneg hxj1
  have hCx : xj ≤ C₁ * x := by nlinarith
  have hlj : Real.log xj ≤ Real.log (C₁ * x) := Real.log_le_log (by linarith) hCx
  have hlogC : 0 ≤ Real.log (C₁ * x) := hlj0.trans hlj
  have h5 : CP * Real.log xj ≤ |CP| * Real.log xj := mul_le_mul_of_nonneg_right (le_abs_self _) hlj0
  have h6 : |CP| * Real.log xj ≤ |CP| * Real.log (C₁ * x) := mul_le_mul_of_nonneg_left hlj (abs_nonneg _)
  have h7 : 0 ≤ CF * Real.log (C₁ * x) := mul_nonneg hCF.le hlogC
  have hl2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hf0 : 0 ≤ f := by
    rw [hf]
    positivity
  have h8 : Real.log x ^ 2 ≤ xj * (2 * f) := by
    have h9 : (x / 2) * (2 * f) ≤ xj * (2 * f) := mul_le_mul_of_nonneg_right hj1 (by positivity)
    have h10 : (x / 2) * (2 * f) = Real.log x ^ 2 := by
      rw [hf]
      field_simp
    linarith
  have h11 : D * Real.log x ^ 2 ≤ 2 * cK * (xj * (2 * f)) :=
    (mul_le_mul_of_nonneg_right hD hl2).trans (mul_le_mul_of_nonneg_left h8 (by positivity))
  have e : 2 * cK * xj * (2 * f) = 2 * cK * (xj * (2 * f)) := by ring
  rw [e, add_mul]
  linarith
private theorem fit_exponent_le {CP CF a D x xj f : ℝ} (hCF : 0 < CF) (hx2 : 2 ≤ x) (ha : 1 ≤ a)
    (hD : D ≤ 1 / 2) (hj1 : x / 2 ≤ xj) (hj2 : xj ≤ 2 * x) (hf : f = Real.log x ^ 2 / x) :
    CF * Real.log (2 + a * xj) - a * xj * f ≤ (|CP| + CF) * Real.log (4 * a * x) - D * Real.log x ^ 2 := by
  have hax : 2 ≤ a * x := by nlinarith
  have haxj : a * xj ≤ a * (2 * x) := mul_le_mul_of_nonneg_left hj2 (by linarith)
  have haxj0 : 0 ≤ a * xj := by nlinarith
  have hlj : Real.log (2 + a * xj) ≤ Real.log (4 * a * x) := Real.log_le_log (by linarith) (by nlinarith)
  have hlogC : 0 ≤ Real.log (4 * a * x) := Real.log_nonneg (by nlinarith)
  have h5 := mul_le_mul_of_nonneg_left hlj hCF.le
  have h7 : 0 ≤ |CP| * Real.log (4 * a * x) := mul_nonneg (abs_nonneg _) hlogC
  have hl2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hf0 : 0 ≤ f := by
    rw [hf]
    positivity
  have h9 : (x / 2) * f ≤ xj * f := mul_le_mul_of_nonneg_right hj1 hf0
  have h10 : (x / 2) * f = Real.log x ^ 2 / 2 := by
    rw [hf]
    field_simp
  have h11 : xj * f ≤ a * xj * f := by
    have hxf : 0 ≤ xj * f := mul_nonneg (by linarith) hf0
    have : a * xj * f = a * (xj * f) := by ring
    rw [this]
    exact le_mul_of_one_le_left hxf ha
  have h12 : D * Real.log x ^ 2 ≤ 1 / 2 * Real.log x ^ 2 := mul_le_mul_of_nonneg_right hD hl2
  rw [add_mul]
  linarith
private theorem radius_product_le {Lr Rr v : ℝ} (hLr : 0 ≤ Lr) (hR0 : 0 ≤ Rr) (hRv : Rr ≤ 2 * v) (hv1 : 1 ≤ v) :
    (Lr * Rr) * (Rr + 8 + 4 * (Lr * Rr)) ≤ 2 * Lr * (10 + 8 * Lr) * v ^ 2 := by
  have h1 : Lr * Rr ≤ Lr * (2 * v) := mul_le_mul_of_nonneg_left hRv hLr
  have h2 : Rr + 8 + 4 * (Lr * Rr) ≤ (10 + 8 * Lr) * v := by nlinarith
  calc (Lr * Rr) * (Rr + 8 + 4 * (Lr * Rr)) ≤ (Lr * (2 * v)) * ((10 + 8 * Lr) * v) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 2 * Lr * (10 + 8 * Lr) * v ^ 2 := by ring
private theorem union_bounds_le {Lr K M H Z x v : ℝ} {ρ s : ℕ} (hK : K = 2 * Lr * (10 + 8 * Lr))
    (hM : M = 16 * 81 * K ^ 4 * (6 * Lr)) (hLr : 2 ≤ Lr) (hv1 : 1 ≤ v) (hv8 : v ^ 8 ≤ x) (hρ1 : 1 ≤ ρ)
    (hρ : (ρ : ℝ) ≤ K * v ^ 2) (hs : (s : ℝ) ≤ Lr * (2 * v)) (hH : 0 ≤ H) (hZ : 0 ≤ Z) :
    (2 * (ρ : ℝ) + 1) ^ 4 * (H + 16 * Z) ≤ M * x ^ 2 * (H + Z) ∧
      ((s : ℝ) + 1) * (16 * (2 * (ρ : ℝ) + 1) ^ 4 * (Z + Z)) ≤ M * x ^ 2 * (H + Z) := by
  have hρr : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ1
  have hvx : v ≤ x := by
    have : v ≤ v ^ 8 := le_self_pow₀ hv1 (by norm_num)
    linarith
  have hx1 : 1 ≤ x := hv1.trans hvx
  have h1 : 2 * (ρ : ℝ) + 1 ≤ 3 * (K * v ^ 2) := by linarith
  have hP : (2 * (ρ : ℝ) + 1) ^ 4 ≤ 81 * K ^ 4 * x := by
    calc (2 * (ρ : ℝ) + 1) ^ 4 ≤ (3 * (K * v ^ 2)) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
      _ = 81 * K ^ 4 * v ^ 8 := by ring
      _ ≤ 81 * K ^ 4 * x := mul_le_mul_of_nonneg_left hv8 (by positivity)
  have hHZ : 0 ≤ H + Z := by linarith
  have hxx : x ≤ 6 * Lr * x ^ 2 := by nlinarith
  have hMx : 16 * (81 * K ^ 4 * x) ≤ M * x ^ 2 := by
    rw [hM]
    have := mul_le_mul_of_nonneg_left hxx (show 0 ≤ 16 * 81 * K ^ 4 by positivity)
    nlinarith
  constructor
  · calc (2 * (ρ : ℝ) + 1) ^ 4 * (H + 16 * Z) ≤ (81 * K ^ 4 * x) * (16 * (H + Z)) :=
          mul_le_mul hP (by linarith) (by linarith) (by positivity)
      _ = 16 * (81 * K ^ 4 * x) * (H + Z) := by ring
      _ ≤ M * x ^ 2 * (H + Z) := mul_le_mul_of_nonneg_right hMx hHZ
  · have hs1 : (s : ℝ) + 1 ≤ 3 * Lr * x := by nlinarith
    calc ((s : ℝ) + 1) * (16 * (2 * (ρ : ℝ) + 1) ^ 4 * (Z + Z))
        ≤ (3 * Lr * x) * (16 * (81 * K ^ 4 * x) * (Z + Z)) := by
          refine mul_le_mul hs1 ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = M * x ^ 2 * Z := by
          rw [hM]
          ring
      _ ≤ M * x ^ 2 * (H + Z) := by
          refine mul_le_mul_of_nonneg_left (by linarith) ?_
          rw [hM]
          positivity
private theorem two_mul_cell_le {L r N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hr : (r : ℝ) ≤ 2 * v)
    (hv9 : 2 ^ 9 * (L : ℝ) ≤ v) (hw : v ^ 2 ≤ (N : ℝ)) : 2 * (L * (2 ^ 7 * r)) ≤ N := by
  have h1 : ((2 * (L * (2 ^ 7 * r)) : ℕ) : ℝ) ≤ N := by
    push_cast
    have h2 : (L : ℝ) * r ≤ L * (2 * v) := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
    have h3 : 2 ^ 9 * (L : ℝ) * v ≤ v * v := mul_le_mul_of_nonneg_right hv9 hv0
    nlinarith
  exact_mod_cast h1
private theorem drift_le_half {B Lr v x s : ℝ} (hB : 1 ≤ B) (hs : s ≤ Lr * (2 * v)) (hv : 8 * B * Lr ≤ v)
    (hv1 : 1 ≤ v) (hvx : v ^ 2 ≤ x) : 2 * B * s ≤ x / 2 := by
  have h1 : 2 * B * s ≤ 2 * B * (Lr * (2 * v)) := mul_le_mul_of_nonneg_left hs (by linarith)
  have h2 : 8 * B * Lr * v ≤ v * v := mul_le_mul_of_nonneg_right hv (by linarith)
  nlinarith
end Estimates
set_option maxHeartbeats 1000000 in
theorem coldEventsLikely_of_tails (hP : plaquetteEnergyTailStatement) (hD : sampleBelowLawStatement)
    (hH : hullSiteRareStatement) (hF : BoxLaws.BondFitTailBound) : coldEventsLikelyStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, hr₂, h₂⟩ := hD a ha
  obtain ⟨L₃, r₃, hr₃, h₃⟩ := hH a ha
  obtain ⟨CF, hCF, hFit⟩ := hF
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hL hLge Tb hTa hTL hDr hrt
  obtain ⟨y₁, g₁⟩ := h₁ L hL ((le_max_left _ _).trans hLge) Tb hTa hTL hDr (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, g₂⟩ := h₂ L hL (((le_max_left _ _).trans (le_max_right _ _)).trans hLge) Tb hTa hTL hDr
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, g₃⟩ := h₃ L hL (((le_max_right _ _).trans (le_max_right _ _)).trans hLge) Tb hTa hTL hDr
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨max y₁ (max y₂ y₃), fun y hy hRet hWil => ?_⟩
  obtain ⟨CP, t₀, yP, ht₀, hPl⟩ := g₁ y ((le_max_left _ _).trans hy) hRet hWil
  have hDraw := g₂ y (((le_max_left _ _).trans (le_max_right _ _)).trans hy) hRet hWil
  obtain ⟨yH, hHull⟩ := g₃ y (((le_max_right _ _).trans (le_max_right _ _)).trans hy) hRet hWil
  intro κ₀ hκ1 hκ2
  have hL40 : 2 ^ 40 ≤ Tb.side := hDr.L_ge
  have hL2 : 2 ≤ Tb.side := by omega
  have hLr : (2 : ℝ) ≤ (Tb.side : ℝ) := by exact_mod_cast hL2
  have ha1 : 1 ≤ Tb.coupling := hDr.a_ge
  have hB1 : 1 ≤ Tb.B := hDr.B_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hDr.n₀_ge
  have hcK : 0 < Tb.coercivity := hDr.cK_pos
  have hσ : 0 < Tb.threshold := hDr.σ_pos
  have hκ₁ : 0 < Tb.κ₁ := by
    have h1 : 0 < Tb.κ / 16 := by linarith [hDr.κ_pos]
    have h2 : 0 < Tb.cE / (4 * Tb.threshold ^ 2) := div_pos hDr.cE_pos (by positivity)
    exact lt_min h1 h2
  set c : ℝ := Tb.κ₁ * Tb.threshold ^ 2 / 2 ^ 5 with hc
  have hc0 : 0 < c := by positivity
  set Lr : ℝ := (Tb.side : ℝ) with hLrdef
  set K : ℝ := 2 * Lr * (10 + 8 * Lr) with hK
  set M : ℝ := 16 * 81 * K ^ 4 * (6 * Lr) with hM
  set A : ℝ := |CP| + CF with hA
  set D : ℝ := min (2 * Tb.coercivity) (1 / 2) with hDdef
  have hD0 : 0 < D := lt_min (by linarith) (by norm_num)
  set C₁ : ℝ := 4 * Tb.coupling with hC₁
  have hC₁0 : 0 < C₁ := by linarith
  set M₁ : ℝ := 8 * Tb.B * Lr + 2 * Lr ^ 2 * (Tb.n₀ : ℝ) + 2 ^ 9 * Lr + 1 with hM₁
  have hfl : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ 2 * yP ≤ x ∧ yH ≤ x ∧ Real.log x ^ 2 ≤ t₀ / 2 * x ∧
      M₁ ≤ x ^ (1 / 21 : ℝ) := by
    have e4 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ t₀ / 2 * x := by
      have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := t₀ / 2) (by positivity)
      filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
      have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      simpa [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_pos (show 0 < x by linarith)] using hx
    have e5 : ∀ᶠ x : ℝ in atTop, M₁ ≤ x ^ (1 / 21 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop M₁
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (2 * yP), eventually_ge_atTop yH, e4, e5]
      with x a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, a4, a5⟩
  obtain ⟨X, hX⟩ := eventually_atTop.1 hfl
  have hsm := fun p : ℕ => eventually_atTop.1 (eventually_tail_le_rpow M A C₁ D c hD0 hc0 hC₁0 p)
  choose xp hxp using hsm
  refine ⟨X, xp, ?_⟩
  intro T β k s n _ o x R hDat hx hR hs p hp
  obtain ⟨hx2, hxP, hxH, hlog, hvM⟩ := hX x (hx ▸ hDat.le_coupling)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set v : ℝ := x ^ (1 / 21 : ℝ) with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hx1 (by norm_num)
  have hLr0 : 0 < Lr := by linarith
  have hn₀r : (0 : ℝ) ≤ (Tb.n₀ : ℝ) := Nat.cast_nonneg _
  have hBL : 0 ≤ 8 * Tb.B * Lr := by positivity
  have hLn0 : 0 ≤ 2 * Lr ^ 2 * (Tb.n₀ : ℝ) := by positivity
  have hL90 : 0 ≤ 2 ^ 9 * Lr := by positivity
  have hv8BL : 8 * Tb.B * Lr ≤ v := by linarith
  have hvn : 2 * Lr ^ 2 * (Tb.n₀ : ℝ) ≤ v := by linarith
  have hv9 : 2 ^ 9 * Lr ≤ v := by linarith
  have hpow : ∀ m : ℕ, ∀ e : ℝ, (m : ℝ) / 21 ≤ e → v ^ m ≤ x ^ e := by
    intro m e he
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    linarith
  have hv2x : v ^ 2 ≤ x ^ (1 / 10 : ℝ) := hpow 2 _ (by norm_num)
  have hv8x : v ^ 8 ≤ x := by
    have := hpow 8 1 (by norm_num)
    simpa using this
  have hv2x' : v ^ 2 ≤ x := by
    have := hpow 2 1 (by norm_num)
    simpa using this
  obtain ⟨hR1', hRv'⟩ := boxRadius_bounds hx1 hκ2
  rw [← hR] at hR1' hRv'
  have hR1 : 1 ≤ R := hR1'
  have hRv : (R : ℝ) ≤ 2 * v := hRv'
  have hLs : Tb.side ^ s ≤ Tb.side * R := by
    have h := pow_coarseningSteps_le hL2 hR1
    rw [show coarseningSteps Tb.side R = s from hs.symm] at h
    exact h
  have hsL : s ≤ Tb.side * R := (Nat.lt_pow_self (by omega)).le.trans hLs
  have hsr : (s : ℝ) ≤ Lr * (2 * v) := by
    have h1 : (s : ℝ) ≤ ((Tb.side * R : ℕ) : ℝ) := by exact_mod_cast hsL
    push_cast at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hRv hLr0.le)
  have hSt : IsTowerAtParameters Tb y T β (k + s) := by
    have h := hDat.onFamily
    rw [← hx, ← hR, ← hs] at h
    exact h
  have hCoin : T.MarksMeasurable := hDat.measurable
  have hStj : ∀ j ≤ k + s, IsTowerAtParameters Tb y T β j := fun j hj =>
    ⟨hSt.startsAtWilson, fun i hi => hSt.coupling_eq i (by omega), fun i hi => hSt.onFamily i (by omega)⟩
  have hyj : ∀ j ≤ k + s, y ≤ flowCoupling (Tb.stepParameters y) β j := by
    intro j hj
    have h1 := (hSt.onFamily j hj).le_coupling
    have h2 : (T.stage j).coupling = flowCoupling (Tb.stepParameters y) β j := hSt.coupling_eq j (by omega)
    rw [← h2]
    exact h1
  have hrow := couplingFlow_hasExpansion (Tb.stepParameters y) hRet hWil β
  have hdrift : ∀ i, i ≤ s → |flowCoupling (Tb.stepParameters y) β (k + i) - x| ≤ 2 * Tb.B * i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [← hx]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 : |flowCoupling (Tb.stepParameters y) β (k + i + 1) - flowCoupling (Tb.stepParameters y) β (k + i)| ≤
          2 * Tb.B :=
        (hrow (k + i) fun j hj => hyj j (by omega)).2
      have h3 := abs_sub_le (flowCoupling (Tb.stepParameters y) β (k + i + 1))
        (flowCoupling (Tb.stepParameters y) β (k + i)) x
      have h4 : k + (i + 1) = k + i + 1 := rfl
      rw [h4]
      push_cast
      linarith
  have hBs : 2 * Tb.B * s ≤ x / 2 := drift_le_half hB1 hsr hv8BL hv1 hv2x'
  have hcoup : ∀ j, k ≤ j → j ≤ k + s →
      x / 2 ≤ flowCoupling (Tb.stepParameters y) β j ∧ flowCoupling (Tb.stepParameters y) β j ≤ 2 * x := by
    intro j hkj hjs
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have h1 := hdrift i (by omega)
    have h2 : 2 * Tb.B * i ≤ 2 * Tb.B * s :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : i ≤ s)) (by linarith)
    have h3 := abs_le.1 (h1.trans (h2.trans hBs))
    constructor <;> linarith [h3.1, h3.2]
  obtain ⟨e, he⟩ := hDat.side_eq
  have hN : n * Tb.side ^ s = 2 * Tb.side ^ e := by
    rw [← fineSide_eq]
    exact he
  have hwide : x ^ (1 / 10 : ℝ) ≤ ((n * Tb.side ^ s : ℕ) : ℝ) := by
    have h := hDat.coupling_rpow_le
    rw [← hx, fineSide_eq] at h
    exact h
  obtain ⟨hnL, hn2L⟩ := side_le_and_dvd hL2 (by omega : 2 ≤ Tb.n₀) hv1 hvn hLs hRv hN hv2x hwide
  have hnL' : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ n := hnL
  have hn2L' : 2 * (Tb.stepParameters y).side ∣ n := hn2L
  have hNeq : fineSide (Tb.stepParameters y).side s n = n * Tb.side ^ s := fineSide_eq _ _ _
  have hNL : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ fineSide (Tb.stepParameters y).side s n := by
    rw [hNeq]
    exact hnL'.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hN2L : 2 * (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side s n := by
    rw [hNeq]
    exact Dvd.dvd.mul_right hn2L _
  set δ : ℝ := boxScale x with hδ
  set f : ℝ := Real.log x ^ 2 / x with hf
  have hδ0 : 0 < δ := by
    have h1 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have h2 : 0 < Real.log x := Real.log_pos (by linarith)
    simp only [hδ, boxScale]
    positivity
  have hδsq : δ ^ 2 / 2 = 2 * f := by
    have h1 : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
      exact Real.rpow_neg_one x
    simp only [hδ, boxScale, hf]
    rw [mul_pow, mul_pow, h1]
    field_simp
  have hf0 : 0 ≤ f := by
    simp only [hf]
    positivity
  have hft : 2 * f ≤ t₀ := by
    simp only [hf]
    rw [← mul_div_assoc, div_le_iff₀ hx0]
    linarith
  have hf2 : 0 < 2 * f := by
    rw [← hδsq]
    positivity
  set Z : ℝ := Real.exp (A * Real.log (C₁ * x) - D * Real.log x ^ 2) with hZ
  set H : ℝ := Real.exp (-(c * x)) with hH'
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  have hH0 : 0 ≤ H := (Real.exp_pos _).le
  have hD2 : D ≤ 2 * Tb.coercivity := min_le_left _ _
  have hDh : D ≤ 1 / 2 := min_le_right _ _
  have hC2 : 2 ≤ C₁ := by linarith
  have hplaq : ∀ (j m : ℕ) [NeZero m], k ≤ j → j ≤ k + s → 2 * (Tb.stepParameters y).side ∣ m →
      (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ m →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
        (markedSampleLaw T β j m).real
          {u | δ < curvature (topField (Tb.stepParameters y) j m u) p.1 p.2.1 p.2.2} ≤ Z := by
    intro j m _ hkj hjs h2 h3 p hp
    obtain ⟨hj1, hj2⟩ := hcoup j hkj hjs
    haveI := (hDraw T β j 0 m (hStj j hjs) hCoin fun i hi => hyj i (by omega)).1
    have hsub : {u : MarkedSample (Tb.stepParameters y) j m |
          δ < curvature (topField (Tb.stepParameters y) j m u) p.1 p.2.1 p.2.2} ⊆
        {u | 2 * f < plaquetteEnergy (topField (Tb.stepParameters y) j m u) p.1 p.2.1 p.2.2} := by
      intro u hu
      show 2 * f < _
      rw [plaquetteEnergy_eq_curvature_sq, ← hδsq]
      exact half_sq_lt_half_sq hδ0 hu
    have hb := hPl T β j m (hStj j hjs) hCoin (by linarith) h2 h3 p hp (2 * f) hf2 hft
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hb.trans (Real.exp_le_exp.2
      (plaquette_exponent_le hCF hx2 hC2 hD2 hcK hj1 hj2 rfl)))
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h1 : T.base.barrierFn = Tb.cutoff := (hSt.onFamily 0 (by omega)).barrierFn_eq
    rw [h1]
    exact hDr.cut
  have hprob : ∀ (j m : ℕ) [NeZero m], j ≤ k + s → IsProbabilityMeasure (markedSampleLaw T β j m) :=
    fun j m _ hj => (hDraw T β j 0 m (hStj j hj) hCoin fun i hi => hyj i (by omega)).1
  have hmarg : ∀ (j m : ℕ) [NeZero m], j < k + s →
      (markedSampleLaw T β (j + 1) m).map (fun u => u.1) =
        markedSampleLaw T β j (m * (Tb.stepParameters y).side) :=
    fun j m _ hj => (hDraw T β j 1 m (hStj (j + 1) hj) hCoin fun i hi => hyj i (by omega)).2
  have hfit : ∀ (j m : ℕ) [NeZero m], k ≤ j → j < k + s → ∀ c' : TorusBond m,
      (markedSampleLaw T β (j + 1) m).real
        {u | f < bondFit (Tb.stepParameters y)
          (topField (Tb.stepParameters y) j (m * (Tb.stepParameters y).side) u.1) u.2.2.1 u.2.1 c'} ≤ Z := by
    intro j m _ hkj hjs c'
    obtain ⟨hj1, hj2⟩ := hcoup j hkj hjs.le
    have hxe : (T.stage j).coupling = flowCoupling (Tb.stepParameters y) β j := hSt.coupling_eq j (by omega)
    have hb := hFit (Tb.stepParameters y) ha1 T β hcut hCoin j m
      (hprob j (m * (Tb.stepParameters y).side) hjs.le) (by rw [hxe]; linarith) c' f
    rw [hxe] at hb
    exact hb.trans (Real.exp_le_exp.2 (fit_exponent_le hCF hx2 ha1 hDh hj1 hj2 rfl))
  set ρ : ℕ := (Tb.side * R) * (R + 8 + 4 * (Tb.side * R)) with hρ
  have hLR : 1 ≤ Tb.side * R := Nat.mul_pos (by omega) hR1
  have hRLR : R ≤ Tb.side * R := Nat.le_mul_of_pos_left _ (by omega)
  have h8R : (Tb.side * R) * 8 ≤ ρ := Nat.mul_le_mul_left _ (by omega)
  have h3R : 3 * R ≤ ρ := by omega
  have hρ1 : 1 ≤ ρ := by omega
  have hρK : (ρ : ℝ) ≤ K * v ^ 2 := by
    have h := radius_product_le hLr0.le (Nat.cast_nonneg R) hRv hv1
    simp only [hρ]
    push_cast
    exact h
  have hρi : ∀ i ≤ s,
      descendingRadius (Tb.stepParameters y).side (apexRadius (Tb.stepParameters y).side s R) i ≤ ρ := by
    intro i hi
    have h1 := descendingRadius_le (L := Tb.side) (by omega) (apexRadius Tb.side s R) i
    have h2 : Tb.side ^ i ≤ Tb.side * R := (Nat.pow_le_pow_right (by omega) hi).trans hLs
    have h3 : apexRadius Tb.side s R ≤ R + 8 := Nat.add_le_add_right (Nat.div_le_self _ _) 8
    have h4 : apexRadius Tb.side s R + 4 * i ≤ R + 8 + 4 * (Tb.side * R) := by omega
    exact h1.trans (Nat.mul_le_mul h2 h4)
  obtain ⟨hr1, hrv⟩ := boxRadius_bounds hx1 (show (1 / 100 : ℝ) ≤ 1 / 21 by norm_num)
  have hcell : 2 * CellWindows.baseCellSide (Tb.stepParameters y).side
      (clusterRange (flowCoupling (Tb.stepParameters y) β k)) ≤ fineSide (Tb.stepParameters y).side s n := by
    rw [← hx]
    have h1 := baseCellSide_le (L := Tb.side) (r := clusterRange x) hL2 hr1
    have h2 : v ^ 2 ≤ ((fineSide (Tb.stepParameters y).side s n : ℕ) : ℝ) := by
      rw [hNeq]
      exact hv2x.trans hwide
    have h3 := two_mul_cell_le (L := Tb.side) (r := clusterRange x) (by linarith) hrv hv9 h2
    exact (Nat.mul_le_mul_left 2 h1).trans h3
  have hgood := not_good_measureReal_le T β k s (apexRadius (Tb.stepParameters y).side s R) δ f Z Z ρ hZ0 hZ0
    hρi hprob hmarg hplaq hfit s le_rfl n o hn2L' hnL'
  haveI := hprob k (fineSide (Tb.stepParameters y).side s n) (by omega)
  have hY : ∀ z : TorusSite (fineSide (Tb.stepParameters y).side s n),
      (markedSampleLaw T β k (fineSide (Tb.stepParameters y).side s n)).real
        {u | z ∈ (stageState T k (fineSide (Tb.stepParameters y).side s n) u).2.1} ≤ H := by
    intro z
    have h := hHull T β k (fineSide (Tb.stepParameters y).side s n) (hStj k (by omega)) hCoin
      (by rw [← hx]; exact hxH) ⟨e, he⟩ hcell z
    rw [← hx] at h
    have e1 : x * Tb.κ₁ * Tb.threshold ^ 2 / 2 ^ 5 = c * x := by
      simp only [hc]
      ring
    rw [e1] at h
    exact h
  have hcold := not_cold_measureReal_le T β k (fineSide (Tb.stepParameters y).side s n) o R ρ h3R δ H Z hH0 hZ0 hY
    (hplaq k _ le_rfl (by omega) hN2L hNL)
  obtain ⟨hn1, hn2⟩ := union_bounds_le hK hM hLr hv1 hv8x hρ1 hρK hsr hH0 hZ0
  have hlast := hxp p x hp
  exact ⟨hcold.trans (hn1.trans hlast), hgood.trans (hn2.trans hlast)⟩
end YangMills.Construction.BoxEvents
end
