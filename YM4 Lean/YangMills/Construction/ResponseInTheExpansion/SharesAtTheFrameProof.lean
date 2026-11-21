import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivativesProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansionProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation Estimates DerivativeInterpolation CellCounting WeightedResponses
namespace ResponseInTheExpansion
private theorem pow_le_factorial_mul_exp (n : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    x ^ n ≤ (n.factorial : ℝ) * (1 / r) ^ n * Real.exp (r * x) := by
  have h1 := Real.pow_div_factorial_le_exp (r * x) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h1
  have h2 : x ^ n = (1 / r) ^ n * (r ^ n * x ^ n) := by
    have e : (1 / r) ^ n * r ^ n = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ hr.ne', one_pow]
    rw [← mul_assoc, e, one_mul]
  rw [h2]
  have h3 : (0 : ℝ) ≤ (1 / r) ^ n := by positivity
  calc (1 / r) ^ n * (r ^ n * x ^ n) ≤ (1 / r) ^ n * (Real.exp (r * x) * n.factorial) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = _ := by ring
private theorem max_one_pow_mul_exp_le (n : ℕ) {l δ r : ℝ} (hl : 1 ≤ l) (hr : 0 < r) (hδ : 2 * δ ≤ r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → max 1 ((x / l) ^ n) * Real.exp (δ * x) * Real.exp (-(r * x)) ≤ A := by
  refine ⟨max 1 ((n.factorial : ℝ) * (1 / (r / 2)) ^ n), le_max_left _ _, fun x hx => ?_⟩
  set A := max 1 ((n.factorial : ℝ) * (1 / (r / 2)) ^ n) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hr2 : 0 < r / 2 := by linarith
  have hE : 1 ≤ Real.exp (r / 2 * x) := Real.one_le_exp (by positivity)
  have h1 : max 1 ((x / l) ^ n) ≤ A * Real.exp (r / 2 * x) := by
    refine max_le ?_ ?_
    · nlinarith
    · have h2 : (x / l) ^ n ≤ x ^ n := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        exact div_le_self hx hl
      have h3 := pow_le_factorial_mul_exp n hr2 hx
      have h4 : (n.factorial : ℝ) * (1 / (r / 2)) ^ n ≤ A := le_max_right _ _
      calc (x / l) ^ n ≤ _ := h2.trans h3
        _ ≤ A * Real.exp (r / 2 * x) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
  have h5 : Real.exp (r / 2 * x) * Real.exp (δ * x) * Real.exp (-(r * x)) ≤ 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith
  have hA0 : 0 < A := by linarith
  calc max 1 ((x / l) ^ n) * Real.exp (δ * x) * Real.exp (-(r * x))
      ≤ (A * Real.exp (r / 2 * x)) * Real.exp (δ * x) * Real.exp (-(r * x)) := by
        gcongr
    _ = A * (Real.exp (r / 2 * x) * Real.exp (δ * x) * Real.exp (-(r * x))) := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left h5 hA0.le
    _ = A := mul_one _
private theorem one_le_rpow_root {L : ℕ} (hL : 1 ≤ L) : (1 : ℝ) ≤ (L : ℝ) ^ (1 / 640 : ℝ) :=
  Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
private theorem torusDecayFactor_mul_exp_le {L : ℕ} (hL : 1 ≤ L) {δ r : ℝ} (hr : 0 < r) (hδ : 2 * δ ≤ r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → torusDecayFactor L δ x * Real.exp (-(r * x)) ≤ A := by
  obtain ⟨A, hA, h⟩ := max_one_pow_mul_exp_le 16000 (one_le_rpow_root hL) hr hδ
  exact ⟨A, hA, fun x hx => h x hx⟩
private theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
private theorem torusDecayFactor_mono {L : ℕ} {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.torusDecayFactor_mono <;> assumption
private theorem abs_sub_le_sum_of_partial_deriv_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : (ι → EuclideanSpace ℝ (Fin 3)) → ℝ) (ρ : ℝ) (K : ι → ℝ)
    (h : ∀ η₀ : ι → EuclideanSpace ℝ (Fin 3), (∀ b, ‖η₀ b‖ ≤ ρ) → ∀ (b : ι) (u : EuclideanSpace ℝ (Fin 3)), ‖u‖ = 1 →
      ∃ d : ℝ, HasDerivAt (fun s : ℝ => Φ (η₀ + s • (Pi.single b u : ι → EuclideanSpace ℝ (Fin 3)))) d 0 ∧ |d| ≤ K b)
    (η : ι → EuclideanSpace ℝ (Fin 3)) (hη : ∀ b, ‖η b‖ ≤ ρ) (h0 : 0 ≤ ρ) :
    |Φ η - Φ 0| ≤ ∑ b, K b * ‖η b‖ := by
  classical
  set res : Finset ι → ι → EuclideanSpace ℝ (Fin 3) := fun A b => if b ∈ A then η b else 0 with hres
  have hball : ∀ A b, ‖res A b‖ ≤ ρ := by
    intro A b
    simp only [hres]
    split_ifs
    · exact hη b
    · simpa using h0
  have key : ∀ A : Finset ι, |Φ (res A) - Φ 0| ≤ ∑ b ∈ A, K b * ‖η b‖ := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      have : res ∅ = 0 := by
        funext b
        simp [hres]
      simp [this]
    | insert b A hb ih =>
      rw [Finset.sum_insert hb]
      by_cases hz : η b = 0
      · have e : res (insert b A) = res A := by
          funext b'
          simp only [hres, Finset.mem_insert]
          by_cases h1 : b' = b
          · subst h1
            simp [hb, hz]
          · simp [h1]
        rw [e, hz]
        simpa using ih
      set t := ‖η b‖ with ht
      have ht0 : 0 < t := norm_pos_iff.mpr hz
      set u : EuclideanSpace ℝ (Fin 3) := t⁻¹ • η b with hu
      have hu1 : ‖u‖ = 1 := by
        rw [hu, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0]
        exact inv_mul_cancel₀ ht0.ne'
      set γ : ℝ → ι → EuclideanSpace ℝ (Fin 3) := fun s => res A + s • (Pi.single b u : ι → EuclideanSpace ℝ (Fin 3)) with hγ
      have hγt : γ t = res (insert b A) := by
        funext b'
        simp only [hγ, hres, Pi.add_apply, Pi.smul_apply, Finset.mem_insert]
        by_cases h1 : b' = b
        · subst h1
          simp only [hb, if_false, Pi.single_eq_same, true_or, if_true, zero_add, hu, smul_smul]
          rw [mul_inv_cancel₀ ht0.ne', one_smul]
        · simp [h1]
      have hγ0 : γ 0 = res A := by simp [hγ]
      have hin : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ b', ‖γ s b'‖ ≤ ρ := by
        intro s hs b'
        simp only [hγ, Pi.add_apply, Pi.smul_apply]
        by_cases h1 : b' = b
        · subst h1
          have e : res A b' = 0 := by simp [hres, hb]
          rw [e, zero_add, Pi.single_eq_same, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_of_nonneg hs.1]
          exact hs.2.trans (hη _)
        · rw [Pi.single_eq_of_ne h1, smul_zero, add_zero]
          exact hball A b'
      have hder : ∀ s ∈ Set.Icc (0 : ℝ) t, ∃ d, HasDerivAt (fun v => Φ (γ v)) d s ∧ |d| ≤ K b := by
        intro s hs
        obtain ⟨d, h1, h2⟩ := h (γ s) (hin s hs) b u hu1
        refine ⟨d, ?_, h2⟩
        have h3 : HasDerivAt (fun s' : ℝ => Φ (γ s + s' • (Pi.single b u : ι → EuclideanSpace ℝ (Fin 3)))) d (s - s) := by simpa using h1
        have h4 := h3.comp_sub_const s s
        refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
        simp only [hγ]
        congr 1
        rw [add_assoc, ← add_smul]
        congr 2
        ring
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun v => Φ (γ v)) (C := K b)
        (s := Set.Icc (0 : ℝ) t) (x := 0) (y := t) (𝕜 := ℝ) (fun s hs => ?_) (fun s hs => ?_) (convex_Icc _ _)
        ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩
      · simp only [hγt, hγ0, Real.norm_eq_abs, sub_zero, abs_of_pos ht0] at hmv
        have h5 := abs_sub_le (Φ (res (insert b A))) (Φ (res A)) (Φ 0)
        linarith
      · obtain ⟨d, h1, -⟩ := hder s hs
        exact h1.differentiableAt
      · obtain ⟨d, h1, h2⟩ := hder s hs
        rw [h1.deriv]
        exact h2
  have e : res Finset.univ = η := by
    funext b
    simp [hres]
  have := key Finset.univ
  rwa [e] at this
variable {F : BlockFrame}
open Classical in
private def admissibleShares (a : ℝ) (L : ℕ) : LocalFamily :=
  fun F y W => if IsBlockTorus L F then minimalSiteShare a y W else 0
private theorem admissibleShares_of_admissible {a : ℝ} {L : ℕ} (hF : IsBlockTorus L F) (y : F.Site F.depth) :
    admissibleShares a L F y = minimalSiteShare a y := by
  funext W
  simp [admissibleShares, hF]
private theorem admissibleShares_of_not {a : ℝ} {L : ℕ} (hF : ¬ IsBlockTorus L F) (y : F.Site F.depth) :
    admissibleShares a L F y = fun _ => 0 := by
  funext W
  simp [admissibleShares, hF]
private theorem bondSpan_le_two_mul (hdist : SupDistCellComparison) {j k : ℕ} (y : F.Site j)
    (c : Fin k → F.Site j × Fin 4) : bondSpan y c ≤ 2 * bondListDist y c := by
  obtain ⟨h1, -, -⟩ := hdist
  have hd : ∀ l, siteSupDist y (c l).1 ≤ bondListDist y c := fun l =>
    Finset.le_sup (f := fun l : Fin k => siteSupDist y (c l).1) (Finset.mem_univ l)
  unfold bondSpan
  refine max_le ?_ ?_
  · refine Finset.sup_le fun l _ => ?_
    have := hd l
    omega
  · refine Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_
    have e := (h1 F j y (c l).1 y).2.1
    have h4 := (h1 F j (c l).1 y (c l').1).2.2
    have := hd l
    have := hd l'
    show siteSupDist (c l).1 (c l').1 ≤ _
    omega
private theorem admissibleShares_hasBoundedDerivatives {a : ℝ} {L t n₀ : ℕ} {c : ColdChainParameters} {N : ℕ → ℝ}
    (hN : ∀ k, 0 < N k)
    (hold : ∀ (F : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth), IsBlockTorus L F → 0 < s → s ≤ c.σA →
      IsSmallCurvature s W → ColdEstimatesBelow a c.δ₁ s N W)
    (hdist : SupDistCellComparison) {σ δ A : ℝ} (hσ : 0 < σ) (hσA : σ ≤ c.σA) (hδ₁ : 0 < c.δ₁)
    (hA1 : 1 ≤ A) (hA : ∀ x : ℝ, 0 ≤ x → torusDecayFactor L δ x * Real.exp (-(c.δ₁ / 2 * x)) ≤ A) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => N j * A) (admissibleShares a L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F _ y W hW j c' X
    by_cases hF : IsBlockTorus L F
    · rw [admissibleShares_of_admissible hF]
      exact ((hold F σ W hF hσ hσA hW).siteShare_analytic y j c' X).contDiffAt
    · rw [admissibleShares_of_not hF]
      exact contDiffAt_const
  · intro F _ y W γ hW
    by_cases hF : IsBlockTorus L F
    · rw [admissibleShares_of_admissible hF]
      exact (hold F σ W hF hσ hσA hW).siteShare_gauge_invariant y γ
    · rw [admissibleShares_of_not hF]
  · intro F _ y W j c' X hW hj1 _ hX
    have hw := torusDecayFactor_pos L δ (bondSpan y c' : ℝ)
    rw [le_div_iff₀ hw]
    by_cases hF : IsBlockTorus L F
    · rw [admissibleShares_of_admissible hF]
      have h1 := (hold F σ W hF hσ hσA hW).siteShare_deriv_decay y j c' X hj1 hX
      have h2 : Real.exp (-c.δ₁ * (bondListDist y c' : ℝ)) ≤ Real.exp (-(c.δ₁ / 2 * (bondSpan y c' : ℝ))) := by
        refine Real.exp_le_exp.mpr ?_
        have : (bondSpan y c' : ℝ) ≤ 2 * bondListDist y c' := by exact_mod_cast bondSpan_le_two_mul hdist y c'
        nlinarith
      have h3 := hA (bondSpan y c' : ℝ) (by positivity)
      have hNj := hN j
      calc |bondDeriv (minimalSiteShare a y) W c' X| * torusDecayFactor L δ (bondSpan y c' : ℝ)
          ≤ (N j * Real.exp (-(c.δ₁ / 2 * (bondSpan y c' : ℝ)))) * torusDecayFactor L δ (bondSpan y c' : ℝ) :=
            mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hNj.le)) hw.le
        _ = N j * (torusDecayFactor L δ (bondSpan y c' : ℝ) * Real.exp (-(c.δ₁ / 2 * (bondSpan y c' : ℝ)))) := by ring
        _ ≤ N j * A := mul_le_mul_of_nonneg_left h3 hNj.le
    · rw [admissibleShares_of_not hF]
      have e : bondDeriv (fun _ : F.GaugeField F.depth => (0 : ℝ)) W c' X = 0 := by
        unfold bondDeriv
        have : iteratedFDeriv ℝ j (fun _ : (Fin j → ℝ) => (0 : ℝ)) = 0 := iteratedFDeriv_fun_zero
        rw [this]
        rfl
      rw [e, abs_zero, zero_mul]
      have := hN j
      positivity
private theorem iteratedFDeriv_add_const_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ} (hp : p ≠ 0)
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ p g x) (c : ℝ) (v : Fin p → E) :
    iteratedFDeriv ℝ p (fun τ => g τ + c) x v = iteratedFDeriv ℝ p g x v := by
  have e : (fun τ => g τ + c) = g + fun _ => c := rfl
  have h := iteratedFDeriv_add_apply (i := p) hg (contDiffAt_const (c := c))
  rw [e, h, iteratedFDeriv_const_of_ne hp]
  simp
abbrev _root_.YangMills.SharedProofs.p68929 := @iteratedFDeriv_add_const_apply
private def SharePerturbationBounds (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (m : ℕ) (A₁ : ℝ) : Prop :=
  ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (p : ℕ) (w : Fin p → Perturbation F)
    (y : F.Site F.depth), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
    (∀ l, (w l).IsUnit) →
    ContDiffAt ℝ 3 (fun τ => minimalSiteShare T.a y (perturbedField 1 T.a T.chainParams.ρA m V η w τ)) 0 ∧
    (1 ≤ p → p ≤ 3 →
      |iteratedFDeriv ℝ p (fun τ => minimalSiteShare T.a y (perturbedField 1 T.a T.chainParams.ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
        A₁ * Real.exp (-(2 ^ 7 * T.κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w)))))
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem toImaginary_imaginaryCoords (X : imaginaryQuaternions) : toImaginary (_root_.YangMills.Construction.Interpolation.imaginaryCoords X) = X := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_imaginaryCoords <;> assumption
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs with h
  · apply Subtype.ext
    apply Quaternion.ext <;> rfl
  · rfl
private theorem mem_chordBonds (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {x : F.Site F.depth} {i : Fin 4} (ht : ¬ IsAxialTreeBond (x, i)) : (x, i) ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.SharedProofs.p40832 <;> assumption
private theorem sharePerturbationBounds_of (hcover : BlocksCoverLowerLevel) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ}
    {N K' : ℕ → ℝ} {D' : ℕ → ℕ → ℝ} {Cb A : ℝ}
    (hLo : Odd T.L) (h64 : 64 ≤ T.n₀) (hρ1 : T.chainParams.ρA ≤ 1) (hσ : 0 < T.σ) (hx : T.coupling ≤ x)
    (hnear : ∀ t : ℕ, InterpolatedFramesControlledAt T t x)
    (hker : interpolationKernelBoundsAt T K' D')
    (hB : ∀ (F : BlockFrame) (n₀ k p m : ℕ) (σ s a ρA : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
      (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F) (y : F.Site F.depth),
      F.blockSide = T.L → IsLargeCubicTorus F → IsCubicTorusAbove T.L F.depth n₀ F → k ≤ 6 → (∀ j, 0 ≤ e j) →
      HasBoundedDerivatives T.L F.depth n₀ σ (T.κ / 2 ^ 10) k e f →
      IsSmallCurvature σ (interpolatedField s a ρA m V η) →
      (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
        (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K' k' * Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ContDiffAt ℝ k (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0 ∧
      (1 ≤ p → p ≤ k →
        |iteratedFDeriv ℝ p (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
          Cb * runningMax e p *
            Real.exp (-(2 ^ 7 * T.κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w))))))
    (hN0 : ∀ k, 0 < N k) (hA0 : 0 ≤ A) (hCb : 0 ≤ Cb)
    (hfam : ∀ t : ℕ, HasBoundedDerivatives T.L t T.n₀ T.σ (T.κ / 2 ^ 10) 3 (fun j => N j * A) (admissibleShares T.a T.L)) :
    SharePerturbationBounds T (frameRadius x) (Cb * runningMax (fun j => N j * A) 3) := by
  intro t F V η p w y hF hV hη hw
  obtain ⟨hFL, ht, n, hside, hn⟩ := id hF
  subst ht
  have hchain : IsBlockTorus T.L F := ⟨hFL, n, by omega, hside⟩
  have hL1 : 1 ≤ T.L := hLo.pos
  have hlow : IsCubicTorusAbove T.L F.depth T.n₀ F := ⟨hFL, rfl, n, hside, by nlinarith⟩
  have hsm := ((hnear F.depth).single F V 1 hF hV zero_le_one le_rfl).2
  have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hz : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := fun b => by
    have : 0 ≤ T.ballRadius := by
      unfold StepParameters.ballRadius
      positivity
    simpa using this
  have hk := hker x F.depth F V 1 0 hx hF hV zero_le_one le_rfl hz
  have hcold : IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V η) := fun q hq =>
    (hsm.small_curvature_nearby η hη q hq).trans_le (by nlinarith)
  have hone : ∀ (x' : F.Site F.depth) (i : Fin 4), ¬ IsAxialTreeBond (x', i) →
      ‖interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η x' i‖ ≤ 1 := by
    intro x' i ht
    have hm := mem_chordBonds hcover hLF hs ht
    have e : stepCoordinates η x' i = toImaginary (η ⟨(x', i), hm⟩) := by
      unfold stepCoordinates
      rw [dif_pos hm]
    have h1 := hsm.norm_add_le (x', i) hm
    have h2 := hη ⟨(x', i), hm⟩
    have h3 : ‖interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η x' i‖ ≤
        ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (x', i) V‖ + ‖η ⟨(x', i), hm⟩‖ := by
      unfold interpolatedCoords
      rw [e, ← norm_toImaginary]
      exact norm_add_le _ _
    have h4 : T.ballRadius = T.σ / 64 := rfl
    linarith
  have he : ∀ j, 0 ≤ (fun j => N j * A) j := fun j => mul_nonneg (hN0 j).le hA0
  obtain ⟨b1, b2⟩ := hB F T.n₀ 3 p (frameRadius x) T.σ 1 T.a T.chainParams.ρA (fun j => N j * A)
    (admissibleShares T.a T.L) V η w y
    hFL ⟨n, by omega, hside⟩ hlow (by norm_num) he (hfam F.depth) hcold hone hk.analytic hk.frame_deriv hw
  set cst := admissibleShares T.a T.L F y (uniformField F F.depth) with hcst
  have e : (fun τ => minimalSiteShare T.a y (perturbedField 1 T.a T.chainParams.ρA (frameRadius x) V η w τ)) =
      fun τ => subtractTrivial (admissibleShares T.a T.L) F y
        (perturbedField 1 T.a T.chainParams.ρA (frameRadius x) V η w τ) + cst := by
    funext τ
    simp only [subtractTrivial, admissibleShares_of_admissible hchain y, hcst]
    ring
  rw [e]
  refine ⟨b1.add contDiffAt_const, fun h1 h3 => ?_⟩
  rw [iteratedFDeriv_add_const_apply (by omega) (b1.of_le (by exact_mod_cast h3))]
  refine (b2 h1 h3).trans ?_
  have hmono : runningMax (fun j => N j * A) p ≤ runningMax (fun j => N j * A) 3 := by
    interval_cases p <;> simp [runningMax]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hCb) (Real.exp_pos _).le
private theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem perturbedField_top {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (a ρA : ℝ) (m : ℕ) (τ : Fin k → ℝ) :
    perturbedField 1 a ρA m V η (fun l => Perturbation.top (c l) (X l)) τ =
      interpolatedField 1 a ρA m (leftTranslate (bondSpread c X τ) V) η := by
  unfold perturbedField perturbedTop perturbedVariable
  simp [Perturbation.variableDirection, Perturbation.topBond, Perturbation.topDirection]
private theorem bondSpan_le_diameter_top {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondSpan Y c ≤ cellSetDiameter (insert Y (perturbationCells fun l => Perturbation.top (c l) (X l))) := by apply _root_.YangMills.Construction.Interpolation.TransportBounds.bondSpan_le_cellSetDiameter <;> assumption
private theorem share_top_bounds {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {m : ℕ} {A₁ : ℝ} (hM : SharePerturbationBounds T m A₁) (hA : 0 ≤ A₁)
    (hκ : 0 ≤ T.κ) {t : ℕ} {V : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hρ : 0 ≤ T.ballRadius) (y : F.Site F.depth)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m (leftTranslate (bondSpread c X τ) V) 0)) 0 ∧
    (1 ≤ k → k ≤ 3 →
      |iteratedFDeriv ℝ k (fun τ : Fin k → ℝ =>
          minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m (leftTranslate (bondSpread c X τ) V) 0)) 0
          fun l => Pi.single l 1| ≤ A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan (enclosingCell y) c))) := by
  have h := hM t F V 0 k (fun l => Perturbation.top (c l) (X l)) y hF hV
    (fun b => by simpa using hρ) (fun l => hX l)
  simp only [perturbedField_top] at h
  refine ⟨h.1, fun h1 h3 => (h.2 h1 h3).trans (mul_le_mul_of_nonneg_left ?_ hA)⟩
  refine Real.exp_le_exp.mpr ?_
  have h4 : (bondSpan (enclosingCell y) c : ℝ) ≤
      cellSetDiameter (insert (enclosingCell y) (perturbationCells fun l => Perturbation.top (c l) (X l))) := by
    exact_mod_cast bondSpan_le_diameter_top (enclosingCell y) c X
  have h5 : (0 : ℝ) ≤ 2 ^ 7 * T.κ := by positivity
  nlinarith
private theorem exists_norm_eq_one : ∃ u : imaginaryQuaternions, ‖u‖ = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSecondDeriv.exists_norm_eq_one <;> assumption
private theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X U : Fin k → imaginaryQuaternions)
    (d : Fin k → ℝ) (h : ∀ l, X l = d l • U l) (τ : Fin k → ℝ) :
    bondSpread c X τ = bondSpread c U (fun l => d l * τ l) := by
  funext y i
  unfold bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [h l, smul_smul, mul_comm]
  · rfl
private theorem exists_unit_decomposition {k : ℕ} (X : Fin k → imaginaryQuaternions) :
    ∃ (U : Fin k → imaginaryQuaternions) (d : Fin k → ℝ), AreUnitVectors U ∧ ∀ l, X l = d l • U l := by
  obtain ⟨u, hu⟩ := exists_norm_eq_one
  classical
  refine ⟨fun l => if X l = 0 then u else ‖X l‖⁻¹ • X l, fun l => ‖X l‖, fun l => ?_, fun l => ?_⟩
  · by_cases h : X l = 0
    · simpa [h] using hu
    · have h0 : ‖X l‖ ≠ 0 := norm_ne_zero_iff.mpr h
      simp only [h, if_false]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  · by_cases h : X l = 0
    · simp [h]
    · have h0 : ‖X l‖ ≠ 0 := norm_ne_zero_iff.mpr h
      simp only [h, if_false]
      rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
private theorem blockSum_contDiffThree {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {m : ℕ} {A₁ : ℝ} (hM : SharePerturbationBounds T m A₁)
    (hA : 0 ≤ A₁) (hκ : 0 ≤ T.κ) {t : ℕ}
    {V : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hρ : 0 ≤ T.ballRadius) (Ys : Finset (F.Site F.depth)) (w : F.Site F.depth → ℝ) :
    ContDiffThreeAlongBonds (fun V' : F.GaugeField F.top => ∑ y ∈ Ys, w y *
      minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V' 0)) V := by
  intro k c X
  obtain ⟨U, d, hU, hd⟩ := exists_unit_decomposition X
  refine ContDiffAt.sum fun y _ => contDiffAt_const.mul ?_
  have h := (share_top_bounds hM hA hκ hF hV hρ y c U hU).1
  have e : (fun τ : Fin k → ℝ => minimalSiteShare T.a y
        (interpolatedField 1 T.a T.chainParams.ρA m (leftTranslate (bondSpread c X τ) V) 0)) =
      (fun τ : Fin k → ℝ => minimalSiteShare T.a y
        (interpolatedField 1 T.a T.chainParams.ρA m (leftTranslate (bondSpread c U τ) V) 0)) ∘
        fun τ l => d l * τ l := by
    funext τ
    simp only [Function.comp]
    rw [bondSpread_smul c X U d hd]
  rw [e]
  have h0 : (fun l => d l * (0 : Fin k → ℝ) l) = (0 : Fin k → ℝ) := by
    funext l
    simp
  have hc : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => fun l => d l * τ l) 0 :=
    contDiff_pi.mpr (fun l => contDiff_const.mul (contDiff_apply ℝ ℝ l)) |>.contDiffAt
  exact ContDiffAt.comp (0 : Fin k → ℝ) (by rw [h0]; exact h) hc
private theorem blockSum_deriv_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {m : ℕ} {A₁ B : ℝ} (hM : SharePerturbationBounds T m A₁)
    (hA : 0 ≤ A₁) (hκ : 0 ≤ T.κ) {t : ℕ}
    {V : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hρ : 0 ≤ T.ballRadius) (Ys : Finset (F.Site F.depth)) (w : F.Site F.depth → ℝ) (hw : ∀ y, |w y| ≤ B)
    {Y : F.Cell} (hY : ∀ y ∈ Ys, enclosingCell y = Y)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (h1 : 1 ≤ k) (h3 : k ≤ 3) :
    |bondDeriv (fun V' : F.GaugeField F.top => ∑ y ∈ Ys, w y *
        minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V' 0)) V c X| ≤
      Ys.card * (B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c)))) := by
  set h : F.Site F.depth → (Fin k → ℝ) → ℝ := fun y τ =>
    minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m (leftTranslate (bondSpread c X τ) V) 0) with hh
  have hc : ∀ y, ContDiffAt ℝ k (h y) 0 := fun y =>
    (share_top_bounds hM hA hκ hF hV hρ y c X hX).1.of_le (by exact_mod_cast h3)
  unfold bondDeriv
  rw [iteratedFDeriv_finsetSum_apply Ys k (fun y τ => w y * h y τ) 0 (fun y _ => contDiffAt_const.mul (hc y))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ y ∈ Ys, |iteratedFDeriv ℝ k (fun τ => w y * h y τ) 0 fun l => Pi.single l 1| ≤
      B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c))) := by
    intro y hy
    have e : (fun τ => w y * h y τ) = (w y) • h y := rfl
    rw [e, iteratedFDeriv_const_smul_apply (hc y)]
    simp only [smul_apply, smul_eq_mul]
    rw [abs_mul]
    have h2 := (share_top_bounds hM hA hκ hF hV hρ y c X hX).2 h1 h3
    rw [hY y hy] at h2
    exact mul_le_mul (hw y) h2 (abs_nonneg _) ((abs_nonneg _).trans (hw y))
  calc _ ≤ ∑ _y ∈ Ys, B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c))) := Finset.sum_le_sum hb
    _ = _ := by simp
private theorem share_hasDerivAt_bulk {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {m : ℕ} {A₁ : ℝ} (hM : SharePerturbationBounds T m A₁)
    (hA : 0 ≤ A₁) (hκ : 0 ≤ T.κ) {t : ℕ}
    {V : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (y : F.Site F.depth) (η₀ : StepVariable (finiteCells F)) (hη : ∀ b, ‖η₀ b‖ ≤ T.ballRadius)
    (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) :
    ∃ d : ℝ, HasDerivAt (fun s : ℝ => minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V
        (η₀ + s • (Perturbation.bulk b u).variableDirection))) d 0 ∧
      |d| ≤ A₁ * Real.exp (-(2 ^ 7 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y))) := by
  set w : Fin 1 → Perturbation F := fun _ => Perturbation.bulk b u with hw
  have hfield : ∀ τ : Fin 1 → ℝ, perturbedField 1 T.a T.chainParams.ρA m V η₀ w τ =
      interpolatedField 1 T.a T.chainParams.ρA m V (η₀ + τ 0 • (Perturbation.bulk b u).variableDirection) := by
    intro τ
    unfold perturbedField perturbedTop perturbedVariable
    have h1 : leftTranslate (bondSpread (fun l => (w l).topBond) (fun l => (w l).topDirection) τ) V = V := by
      funext y i
      simp [leftTranslate, bondSpread, hw, Perturbation.topDirection, expUnit_zero]
    rw [h1]
    simp [hw]
  obtain ⟨hc, hb⟩ := hM t F V η₀ 1 w y hF hV hη (fun _ => hu)
  simp only [hfield] at hc hb
  set g : (Fin 1 → ℝ) → ℝ := fun τ => minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V
    (η₀ + τ 0 • (Perturbation.bulk b u).variableDirection)) with hg
  have hd : HasFDerivAt g (fderiv ℝ g 0) 0 := (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => (fun _ => s : Fin 1 → ℝ)) (fun _ => 1) 0 :=
    hasDerivAt_pi.mpr fun _ => hasDerivAt_id 0
  refine ⟨fderiv ℝ g 0 (fun _ => 1), ?_, ?_⟩
  · exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (fun _ => s : Fin 1 → ℝ)) (0 : ℝ) hd hl
  · have h2 := hb le_rfl (by norm_num)
    rw [iteratedFDeriv_one_apply] at h2
    have e : (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) = fun _ => 1 := by
      funext l
      simp [Subsingleton.elim l 0]
    rw [e] at h2
    refine h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA)
    have hmem : enclosingCell b.1.1 ∈ insert (enclosingCell y) (perturbationCells w) :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    have h4 : (cellSupDist (enclosingCell b.1.1) (enclosingCell y) : ℝ) ≤
        cellSetDiameter (insert (enclosingCell y) (perturbationCells w)) := by
      exact_mod_cast cellSupDist_le_diameter hmem (Finset.mem_insert_self _ _)
    nlinarith
private theorem cellSupDist_comm (hdist : SupDistCellComparison) (u v : F.Cell) :
    cellSupDist u v = cellSupDist v u :=
  (hdist.1 F F.top u v u).2.1
private theorem norm_imaginaryCoords (X : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords X‖ = ‖X‖ := by apply _root_.YangMills.SharedProofs.p6124 <;> assumption
private theorem exists_fineBondAt (hsites : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) (x : F.Site F.depth) (i : Fin 4) :
    ∃ g : Fin 4 → ℤ, Y + siteOfCoords F.top g = enclosingCell x ∧
      (∀ l, |g l| ≤ (cellSupDist (enclosingCell x) Y : ℤ)) ∧
      fineBondAt Y g (cellOffset x) i = (x, i) ∧ cellOffset x ∈ centredCube F.blockSide := by
  obtain ⟨-, h2, -, -⟩ := hsites F hL hs
  have hg : Y + siteOfCoords F.top (fun l => ((enclosingCell x - Y) l).valMinAbs) = enclosingCell x := by
    funext l
    simp only [Pi.add_apply, siteOfCoords, ZMod.coe_valMinAbs]
    simp
  refine ⟨fun l => ((enclosingCell x - Y) l).valMinAbs, hg, fun l => ?_, ?_, (h2 x).2⟩
  · have h : ((enclosingCell x l - Y l).valMinAbs).natAbs ≤ cellSupDist (enclosingCell x) Y :=
      Finset.le_sup (f := fun l => ((enclosingCell x l - Y l).valMinAbs).natAbs) (Finset.mem_univ l)
    have e : |((enclosingCell x - Y) l).valMinAbs| = (((enclosingCell x l - Y l).valMinAbs).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      rfl
    rw [e]
    exact_mod_cast h
  · unfold fineBondAt
    rw [hg, (h2 x).1]
private theorem cellSupDist_enclosing_le (hdist : SupDistCellComparison) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (y : F.Site F.depth) (h : Fin 4 → ℤ) (r : ℕ) (hh : WithinRadius r h) :
    cellSupDist (enclosingCell y) (enclosingCell (y + siteOfCoords F.depth h : F.Site F.depth)) ≤ r + 1 := by
  have h1 := (hdist.2.2 F hL hs).1 (y + siteOfCoords F.depth h) y
  have h2 := hdist.2.1 F F.depth y h r (fun i => by
    have := hh i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this)
  have h3 := (hdist.1 F F.depth y (y + siteOfCoords F.depth h) y).2.1
  have e : siteSupDist (enclosingCell (y + siteOfCoords F.depth h : F.Site F.depth)) (enclosingCell y) =
      cellSupDist (enclosingCell (y + siteOfCoords F.depth h : F.Site F.depth)) (enclosingCell y) := rfl
  rw [e] at h1
  rw [cellSupDist_comm hdist]
  set D := cellSupDist (enclosingCell (y + siteOfCoords F.depth h : F.Site F.depth)) (enclosingCell y)
  by_contra hc
  have hD : (r : ℝ) + 2 ≤ D := by
    have : r + 2 ≤ D := by omega
    exact_mod_cast this
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL.pos
  have h4 : (siteSupDist (y + siteOfCoords F.depth h) y : ℝ) ≤ r := by
    rw [← h3]
    exact_mod_cast h2
  nlinarith
private theorem bondDeriv_zero_depth {G : F.GaugeField F.depth → ℝ} (W : F.GaugeField F.depth)
    (c : Fin 0 → F.Site F.depth × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.bondDeriv_zero_order <;> assumption
private theorem bondDeriv_zero_top {G : F.GaugeField F.top → ℝ} (W : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem share_sub_le_of_agree (hsites : SiteDecomposition) (hdist : SupDistCellComparison)
    (hcover : BlocksCoverLowerLevel) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {m : ℕ} {A₁ Ct Wt Cc : ℝ}
    (hM : SharePerturbationBounds T m A₁) (hA : 0 ≤ A₁)
    (hκ : 0 ≤ T.κ) (hLo : Odd T.L) (h2 : 2 ≤ T.n₀) {t : ℕ} {V V' : F.GaugeField F.top}
    (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) {Y : F.Cell} {q : ℕ}
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q) (hq : 6 ≤ q)
    (hloc : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y q h o i →
      ‖interpolatedFrame 1 T.a T.chainParams.ρA m (fineBondAt Y h o i) V -
          interpolatedFrame 1 T.a T.chainParams.ρA m (fineBondAt Y h o i) V'‖ ≤
        Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1)))))
    (hCt : 0 ≤ Ct * T.σ) (hδ₂ : 0 ≤ T.chainParams.δ₂)
    (hg : Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) ≤ T.ballRadius)
    (y : F.Site F.depth) (hy : enclosingCell y = Y)
    (hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA m V η))
    (hcold' : IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA m V' 0))
    (hcmp : ∀ (W W' : F.GaugeField F.depth) (r : ℕ), IsSmallCurvature T.σ W → IsSmallCurvature T.σ W' →
      AgreeOnBox W W' y y r →
      |minimalSiteShare T.a y W - minimalSiteShare T.a y W'| ≤ Cc * Real.exp (-T.chainParams.δ₁ * r))
    (hSum : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 7 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y))) ≤ Wt) :
    |minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V 0) -
        minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V' 0)| ≤
      Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) * (A₁ * Wt) +
        Cc * Real.exp (-T.chainParams.δ₁ * ((q / 3 : ℕ) : ℝ)) := by
  classical
  obtain ⟨hFL, ht, n, hside, hn⟩ := id hF
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
  set g₀ := Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) with hg₀
  have hg₀0 : 0 ≤ g₀ := mul_nonneg hCt (Real.exp_pos _).le
  set wf : F.GaugeField F.top → F.Site F.depth × Fin 4 → imaginaryQuaternions :=
    fun U b => interpolatedFrame 1 T.a T.chainParams.ρA m b U with hwf
  set η : StepVariable (finiteCells F) := fun b =>
    if 3 * cellSupDist Y (enclosingCell b.1.1) ≤ q + 3 then _root_.YangMills.Construction.Interpolation.imaginaryCoords (wf V' b.1 - wf V b.1) else 0 with hη
  have hsize : ∀ b, ‖η b‖ ≤ g₀ := by
    intro b
    by_cases hb : 3 * cellSupDist Y (enclosingCell b.1.1) ≤ q + 3
    · simp only [hη, hb, if_true]
      rw [norm_imaginaryCoords, norm_sub_rev]
      obtain ⟨g, hg1, hg2, hg3, hg4⟩ := exists_fineBondAt hsites hLF hs2 Y b.1.1 b.1.2
      have hcomm := cellSupDist_comm hdist (enclosingCell b.1.1) Y
      have hbox : IsFineBondWithinRadius Y q g (cellOffset b.1.1) b.1.2 := by
        have e1 : (fineBondAt Y g (cellOffset b.1.1) b.1.2).1 = b.1.1 := by rw [hg3]
        refine ⟨hg4, ?_, ?_, ?_, ?_⟩
        · rw [hg3]
          exact b.2
        · intro l
          have := hg2 l
          rw [hcomm] at this
          have h3 : (cellSupDist Y (enclosingCell b.1.1) : ℤ) ≤ q := by
            have : cellSupDist Y (enclosingCell b.1.1) ≤ q := by omega
            exact_mod_cast this
          linarith
        · rw [e1]
          omega
        · rw [e1]
          have hs4 := (hsites F hLF hs2).2.2.2 b.1.1 b.1.2
          rcases hs4 with h4 | h4
          · rw [h4]
            omega
          · rw [h4]
            have h5 := (hdist.1 F F.top Y (enclosingCell b.1.1) (enclosingCell b.1.1 + unitStep F.top b.1.2)).2.2
            have h6 := hdist.2.1 F F.top (enclosingCell b.1.1) (Pi.single b.1.2 1) 1 (fun i => by
              by_cases hi : i = b.1.2
              · subst hi
                simp
              · simp [Pi.single_eq_of_ne hi])
            have e2 : siteSupDist Y (enclosingCell b.1.1) = cellSupDist Y (enclosingCell b.1.1) := rfl
            have e3 : siteSupDist Y (enclosingCell b.1.1 + unitStep F.top b.1.2) =
                cellSupDist Y (enclosingCell b.1.1 + unitStep F.top b.1.2) := rfl
            have e4 : siteOfCoords F.top (Pi.single b.1.2 1) = (unitStep F.top b.1.2 : F.Cell) := rfl
            rw [e4] at h6
            rw [e2, e3] at h5
            omega
      have h1 := hloc g _ _ hbox
      rw [hg3] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCt)
      have h3 : (3 : ℝ) * cellSupDist Y (enclosingCell b.1.1) ≤ q + 3 := by exact_mod_cast hb
      simp only
      nlinarith
    · simp only [hη, hb, if_false]
      simpa using hg₀0
  have hball : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hsize b).trans hg
  have hρ0 : 0 ≤ T.ballRadius := hg₀0.trans hg
  set Φ : StepVariable (finiteCells F) → ℝ :=
    fun ζ => minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V ζ) with hΦ
  set K : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
    A₁ * Real.exp (-(2 ^ 7 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y))) with hKdef
  have hmove : |Φ η - Φ 0| ≤ ∑ b, K b * ‖η b‖ := by
    refine abs_sub_le_sum_of_partial_deriv_le Φ T.ballRadius K (fun η₀ hη₀ b u hu => ?_) η hball hρ0
    obtain ⟨d, h1, h2⟩ := share_hasDerivAt_bulk hM hA hκ hF hV y η₀ hη₀ b u hu
    refine ⟨d, ?_, h2⟩
    convert h1
    rfl
  have hsum : ∑ b, K b * ‖η b‖ ≤ g₀ * (A₁ * Wt) := by
    have hK0 : ∀ b, 0 ≤ K b := fun b => mul_nonneg hA (Real.exp_pos _).le
    calc ∑ b, K b * ‖η b‖ ≤ ∑ b, K b * g₀ :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hsize b) (hK0 b)
      _ = g₀ * (A₁ * ∑ b : ↥(chordBonds (finiteCells F)),
            Real.exp (-(2 ^ 7 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y)))) := by
          simp only [hKdef]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring
      _ ≤ g₀ * (A₁ * Wt) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSum hA) hg₀0
  have hper : ∀ i, 2 * (q / 3) + 2 < F.period F.depth i := by
    intro i
    rw [BlockOffsets.period_depth]
    have h1 : 2 * q + 2 < F.extent i := by
      rcases hag.1 i with h0 | h0
      · have := hs2 i
        omega
      · exact h0
    have h3 : 1 ≤ F.blockSide := hLF.pos
    have h4 : F.extent i ≤ F.extent i * F.blockSide := Nat.le_mul_of_pos_right _ h3
    omega
  have hagree : AgreeOnBox (interpolatedField 1 T.a T.chainParams.ρA m V η)
      (interpolatedField 1 T.a T.chainParams.ρA m V' 0) y y (q / 3) := by
    refine ⟨hper, hper, fun b hb => ?_⟩
    have hd := cellSupDist_enclosing_le hdist hLF hs0 y b.1 (q / 3) hb.1
    rw [hy] at hd
    set x : F.Site F.depth := y + siteOfCoords F.depth b.1 with hx
    obtain ⟨g, hg1, hg2, -, -⟩ := exists_fineBondAt hsites hLF hs2 Y x b.2
    have hnear : 3 * cellSupDist Y (enclosingCell x) ≤ q + 3 := by omega
    have hAeq : ¬ IsAxialTreeBond (x, b.2) → interpolatedCoords 1 T.a T.chainParams.ρA m V η x b.2 =
        interpolatedCoords 1 T.a T.chainParams.ρA m V' 0 x b.2 := by
      intro ht
      have hm := mem_chordBonds hcover hLF hs0 ht
      have e : stepCoordinates η x b.2 = wf V' (x, b.2) - wf V (x, b.2) := by
        unfold stepCoordinates
        rw [dif_pos hm]
        simp only [hη, hnear, if_true]
        exact toImaginary_imaginaryCoords _
      unfold interpolatedCoords
      rw [e, stepCoordinates_zero]
      simp [hwf]
    have hfield : ∀ (U : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)),
        interpolatedField 1 T.a T.chainParams.ρA m U ζ =
        chartedField (interpolatedCoords 1 T.a T.chainParams.ρA m U ζ) U := fun _ _ => rfl
    rw [hfield, hfield]
    unfold chartedField
    by_cases hc : IsCrossingBond (x, b.2)
    · have hcr : IsCrossingBond (x, b.2) := hc
      rw [if_pos hcr, if_pos hcr, hAeq (fun ht => ht.1 hcr)]
      have hcomm := cellSupDist_comm hdist (enclosingCell x) Y
      have hbox1 : WithinRadius q g := by
        intro l
        have := hg2 l
        rw [hcomm] at this
        have h3 : (cellSupDist Y (enclosingCell x) : ℤ) ≤ q := by
          have : cellSupDist Y (enclosingCell x) ≤ q := by omega
          exact_mod_cast this
        linarith
      have hbox2 : WithinRadius q (g + Pi.single b.2 1) := by
        intro l
        have h1 := hg2 l
        rw [hcomm] at h1
        have h3 : (cellSupDist Y (enclosingCell x) : ℤ) + 1 ≤ q := by
          have : cellSupDist Y (enclosingCell x) + 1 ≤ q := by omega
          exact_mod_cast this
        have h4 : |(Pi.single b.2 1 : Fin 4 → ℤ) l| ≤ 1 := by
          by_cases hl : l = b.2
          · subst hl
            simp
          · simp [Pi.single_eq_of_ne hl]
        calc |(g + (Pi.single b.2 1 : Fin 4 → ℤ)) l| ≤ |g l| + |(Pi.single b.2 1 : Fin 4 → ℤ) l| := abs_add_le _ _
          _ ≤ q := by linarith
      have hv := hag.2.2.2 (g, b.2) ⟨hbox1, hbox2⟩
      simp only [hg1] at hv
      rw [hv]
    · have hnc : ¬ IsCrossingBond (x, b.2) := hc
      rw [if_neg hnc, if_neg hnc]
      by_cases ht : IsAxialTreeBond (x, b.2)
      · rw [if_pos ht, if_pos ht]
      · rw [if_neg ht, if_neg ht, hAeq ht]
  have hc := hcmp _ _ (q / 3) (hcold η hball) hcold' hagree
  have h6 := abs_sub_le (Φ 0) (Φ η) (minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V' 0))
  rw [abs_sub_comm (Φ 0) (Φ η)] at h6
  have h7 := hmove.trans hsum
  calc _ ≤ |Φ η - Φ 0| + |Φ η - minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V' 0)| := h6
    _ ≤ _ := add_le_add h7 hc
private theorem rpow_mix_le {B U W R E α β : ℝ} (hB : 0 < B) (hU : 0 < U) (hW : 0 < W) (hUR : U ≤ R) (hWR : W ≤ R)
    (hE0 : 0 < E) (hE1 : E ≤ 1) (hα : 1 / 3 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    (B * (U * E ^ 3)) ^ α * (B * W) ^ β ≤ B * R * E := by
  have hR : 0 < R := lt_of_lt_of_le hU hUR
  have hα0 : 0 ≤ α := by linarith
  have hE3 : 0 ≤ E ^ 3 := by positivity
  rw [Real.mul_rpow hB.le (by positivity), Real.mul_rpow hU.le hE3, Real.mul_rpow hB.le hW.le]
  have h1 : (E ^ 3) ^ α ≤ E := by
    have e : (E ^ 3 : ℝ) = E ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e, ← Real.rpow_mul hE0.le]
    calc E ^ (3 * α) ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (by linarith)
      _ = E := Real.rpow_one E
  have h2 : U ^ α ≤ R ^ α := Real.rpow_le_rpow hU.le hUR hα0
  have h3 : W ^ β ≤ R ^ β := Real.rpow_le_rpow hW.le hWR hβ
  have h4 : B ^ α * B ^ β = B := by rw [← Real.rpow_add hB, hαβ, Real.rpow_one]
  have h5 : R ^ α * R ^ β = R := by rw [← Real.rpow_add hR, hαβ, Real.rpow_one]
  have p4 : 0 < W ^ β := Real.rpow_pos_of_pos hW _
  calc B ^ α * (U ^ α * (E ^ 3) ^ α) * (B ^ β * W ^ β)
      = (B ^ α * B ^ β) * (U ^ α * W ^ β) * (E ^ 3) ^ α := by ring
    _ ≤ (B ^ α * B ^ β) * (R ^ α * R ^ β) * E := by
        have : U ^ α * W ^ β ≤ R ^ α * R ^ β := mul_le_mul h2 h3 p4.le (Real.rpow_pos_of_pos hR _).le
        gcongr
    _ = B * R * E := by rw [h4, h5]
private theorem blockSum_deriv_sub_le {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {m : ℕ} {A₁ B C₂ M₀ Z : ℝ}
    (hM : SharePerturbationBounds T m A₁) (hA : 0 ≤ A₁) (hκ : 0 ≤ T.κ)
    (hlines : SmallCurvatureAlongLineAndAgreeOn)
    (htwo : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ) (V : F.GaugeField F.top)
      (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        C₂ * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    {t : ℕ} {V V' : F.GaugeField F.top} (hF : IsCubicTopTorus T.L t T.n₀ F) (hσ : 0 < T.σ)
    (hV : IsSmallCurvature (9 / 8 * T.σ) V) (hV' : IsSmallCurvature (9 / 8 * T.σ) V')
    {Y : F.Cell} {q : ℕ} (hag : AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q)
    (Ys : Finset (F.Site F.depth)) (w : F.Site F.depth → ℝ) (hw : ∀ y, |w y| ≤ B)
    (hY : ∀ y ∈ Ys, enclosingCell y = Y)
    (hZ : (Ys.card : ℝ) ≤ Z) (hB : 0 ≤ B) (hM₀ : 0 < M₀)
    (hclose : ∀ U U' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) U → IsSmallCurvature (5 / 4 * T.σ) U' →
      AgreeOnBall (finiteCells F) U (finiteCells F) U' Y Y q →
      |(∑ y ∈ Ys, w y * minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m U 0)) -
        ∑ y ∈ Ys, w y * minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m U' 0)| ≤ M₀)
    {k : ℕ} (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hb : ∀ l, BondWithinRadius q (b l)) (hX : AreUnitVectors X) :
    |bondDeriv (fun V₁ : F.GaugeField F.top => ∑ y ∈ Ys, w y *
          minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V₁ 0)) V (bondsAt Y b) X -
      bondDeriv (fun V₁ : F.GaugeField F.top => ∑ y ∈ Ys, w y *
          minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V₁ 0)) V' (bondsAt Y b) X| ≤
      C₂ * (M₀ / (T.σ / 64) ^ k + M₀ ^ (1 - (k : ℝ) / 3) * (B * (Z * A₁)) ^ ((k : ℝ) / 3)) := by
  set G : F.GaugeField F.top → ℝ := fun V₁ => ∑ y ∈ Ys, w y *
    minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA m V₁ 0) with hG
  have hρ : 0 ≤ T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hτ : 0 < T.σ / 64 := by positivity
  have hZ0 : 0 ≤ Z := (Nat.cast_nonneg _).trans hZ
  have hnorm : ∀ (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → AreUnitVectors fun l => ς l • X l := by
    intro ς hς l
    have h1 : ‖ς l‖ = 1 := by
      rcases hς l with h | h <;> simp [h]
    show ‖ς l • X l‖ = 1
    rw [norm_smul, h1, hX l, one_mul]
  have hcold : ∀ (U : F.GaugeField F.top) (ς : Fin k → ℝ), IsSmallCurvature (9 / 8 * T.σ) U →
      (∀ l, ς l = 1 ∨ ς l = -1) → ∀ s : ℝ, |s| ≤ T.σ / 64 →
      IsSmallCurvature (5 / 4 * T.σ) (alongLine (bondsAt Y b) (fun l => ς l • X l) s U) := by
    intro U ς hU hς s hs
    have h1 := hlines.1 F U k (bondsAt Y b) (fun l => ς l • X l) s (9 / 8 * T.σ) (fun l => (hnorm ς hς l).le) hU
    intro p hp
    refine (h1 p hp).trans_le ?_
    have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    nlinarith
  have hread : ∀ (U : F.GaugeField F.top) (ς : Fin k → ℝ), IsSmallCurvature (9 / 8 * T.σ) U →
      (∀ l, ς l = 1 ∨ ς l = -1) →
      IsControlledAlongLine G U (bondsAt Y b) (fun l => ς l • X l) (T.σ / 64) (B * (Z * A₁)) := by
    intro U ς hU hς
    refine ⟨fun s hs => blockSum_contDiffThree hM hA hκ hF (hcold U ς hU hς s hs) hρ Ys w, fun s hs e => ?_⟩
    have h1 := blockSum_deriv_le hM hA hκ hF (hcold U ς hU hς s hs) hρ Ys w hw hY (bondsAt Y b ∘ e)
      ((fun l => ς l • X l) ∘ e) (fun l => hnorm ς hς (e l)) (by norm_num) le_rfl
    refine h1.trans ?_
    have h2 : Real.exp (-(2 ^ 7 * T.κ * bondSpan Y (bondsAt Y b ∘ e))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ 2 ^ 7 * T.κ * bondSpan Y (bondsAt Y b ∘ e) := by positivity
        linarith)
    have h3 : A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y (bondsAt Y b ∘ e))) ≤ A₁ :=
      mul_le_of_le_one_right hA h2
    have h4 : B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y (bondsAt Y b ∘ e)))) ≤ B * A₁ :=
      mul_le_mul_of_nonneg_left h3 hB
    have h5 : 0 ≤ B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y (bondsAt Y b ∘ e)))) :=
      mul_nonneg hB (mul_nonneg hA (Real.exp_pos _).le)
    calc (Ys.card : ℝ) * (B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y (bondsAt Y b ∘ e)))))
        ≤ Z * (B * A₁) := mul_le_mul hZ h4 h5 hZ0
      _ = B * (Z * A₁) := by ring
  exact htwo F F G G V V' k (bondsAt Y b) (bondsAt Y b) X (T.σ / 64) M₀ (B * (Z * A₁)) hk1 hk2 hτ hM₀
    (mul_nonneg hB (mul_nonneg hZ0 hA)) (fun ς hς => ⟨hread V ς hV hς, hread V' ς hV' hς, fun s hs =>
      hclose _ _ (hcold V ς hV hς s hs) (hcold V' ς hV' hς s hs)
        (hlines.2 F F V V' Y Y q k b (fun l => ς l • X l) s hag hb)⟩)
private theorem deriv_bound_numbers {B Z A₁ A₂ E σ C₂ : ℝ} {k : ℕ} (hB : 0 < B) (hZ0 : 0 < Z) (hA₁ : 0 < A₁)
    (hA₂ : 0 < A₂) (hE0 : 0 < E) (hE1 : E ≤ 1) (hE3 : E ^ 3 ≤ E) (hσ : 0 < σ) (hC₂ : 0 ≤ C₂) (h0 : 0 < k)
    (hk : k ≤ 2) :
    C₂ * (B * (Z * A₂ * E ^ 3) / (σ / 64) ^ k +
        (B * (Z * A₂ * E ^ 3)) ^ (1 - (k : ℝ) / 3) * (B * (Z * A₁)) ^ ((k : ℝ) / 3)) ≤
      C₂ * (Z * A₂ * (1 + 64 / σ + (64 / σ) ^ 2) + (Z * A₂ + Z * A₁)) * B * E := by
  obtain ⟨P, hP⟩ : ∃ P, P = 1 + 64 / σ + (64 / σ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = Z * A₂ + Z * A₁ := ⟨_, rfl⟩
  rw [← hP, ← hR]
  have hZ1 := mul_pos hZ0 hA₁
  have hZ2 := mul_pos hZ0 hA₂
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h0
  have h6 := rpow_mix_le (B := B) (U := Z * A₂) (W := Z * A₁) (R := R) (E := E) (α := 1 - (k : ℝ) / 3)
    (β := (k : ℝ) / 3) hB hZ2 hZ1 (by linarith) (by linarith) hE0 hE1 (by linarith) (by positivity) (by ring)
  have hu : 0 < 64 / σ := by positivity
  have hM₀E : B * (Z * A₂ * E ^ 3) ≤ Z * A₂ * B * E := by
    have h5 : Z * A₂ * B * E ^ 3 ≤ Z * A₂ * B * E := mul_le_mul_of_nonneg_left hE3 (by positivity)
    calc B * (Z * A₂ * E ^ 3) = Z * A₂ * B * E ^ 3 := by ring
      _ ≤ _ := h5
  have h7 : B * (Z * A₂ * E ^ 3) / (σ / 64) ^ k ≤ Z * A₂ * B * E * P := by
    have e : 1 / (σ / 64) = 64 / σ := by field_simp
    have h8 : (64 / σ) ^ k ≤ P := by
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl
      · rw [hP, pow_one]
        nlinarith [sq_nonneg (64 / σ)]
      · rw [hP]
        nlinarith
    have e2 : B * (Z * A₂ * E ^ 3) / (σ / 64) ^ k = B * (Z * A₂ * E ^ 3) * (64 / σ) ^ k := by
      rw [← e, one_div, inv_pow, div_eq_mul_inv]
    rw [e2]
    exact mul_le_mul hM₀E h8 (by positivity) (by positivity)
  have h8 := add_le_add h7 h6
  calc _ ≤ C₂ * (Z * A₂ * B * E * P + B * R * E) := mul_le_mul_of_nonneg_left h8 hC₂
    _ = C₂ * (Z * A₂ * P + R) * B * E := by ring
private theorem weightedFrameShares_of_bounds {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {A₁ A₂ A₃ A₄ Sz Z C₂ : ℝ} {r₂ : ℕ}
    (hM : ∀ x : ℝ, T.coupling ≤ x → SharePerturbationBounds T (frameRadius x) A₁) (hA₁ : 0 < A₁) (hκ : 0 < T.κ)
    (hσ : 0 < T.σ) (hLo : Odd T.L) (h2 : 2 ≤ T.n₀) (hsites : SiteDecomposition)
    (hlines : SmallCurvatureAlongLineAndAgreeOn)
    (htwo : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ) (V : F.GaugeField F.top)
      (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        C₂ * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    (hclose : ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ) (y : F.Site F.depth),
      T.coupling ≤ x →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → r₂ ≤ q → enclosingCell y = Y →
      |minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V 0) -
        minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V' 0)| ≤
        A₂ * Real.exp (-(T.chainParams.δ₂ / 18 * q)) ^ 3)
    (hsz : ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top) (y : F.Site F.depth), T.coupling ≤ x →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      |minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V 0)| ≤ Sz)
    (hA₂ : 0 < A₂) (hSz : 0 ≤ Sz) (hZ : Z = ((centredCube T.L).card : ℝ) + 1) (hδ₂ : 0 < T.chainParams.δ₂)
    (hC₂ : 0 ≤ C₂)
    (h3 : ∀ x : ℝ, 0 ≤ x → torusDecayFactor T.L T.decayRate x * Real.exp (-(2 ^ 7 * T.κ * x)) ≤ A₃)
    (h4 : ∀ x : ℝ, 0 ≤ x → torusDecayFactor T.L T.decayRate x * Real.exp (-(T.chainParams.δ₂ / 18 * x)) ≤ A₄)
    (hC1 : Z * A₁ * A₃ ≤ T.Cs) (hC2 : Z * A₂ * A₄ ≤ T.Cs)
    (hC3 : C₂ * (Z * A₂ * (1 + 64 / T.σ + (64 / T.σ) ^ 2) + (Z * A₂ + Z * A₁)) * A₄ ≤ T.Cs)
    (hC4 : 2 * (Z * (A₁ + Sz)) * torusDecayFactor T.L T.decayRate r₂ ≤ T.Cs) :
    weightedFrameSharesStatementAt T := by
  intro t x B f F Y w hx hF hB0 hw
  have hM' := hM x hx
  have hκ0 := hκ.le
  have hρ : 0 ≤ T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hδ0 : 0 ≤ T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  obtain ⟨Ys, hYs, hG⟩ : ∃ Ys : Finset (F.Site F.depth), (∀ y ∈ Ys, enclosingCell y = Y) ∧
      (coldHalfLawAt T x f).weightedFrameShares w Y = fun V₁ => ∑ y ∈ Ys, w y *
        minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V₁ 0) :=
    ⟨_, fun y hy => (Finset.mem_filter.mp hy).2, rfl⟩
  obtain ⟨hFL, ht, n, hside, hn⟩ := id hF
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
  have hcard : (Ys.card : ℝ) ≤ Z := by
    obtain ⟨-, h5, -, -⟩ := hsites F hLF hs2
    have h6 : Ys.card ≤ (centredCube F.blockSide).card := by
      refine Finset.card_le_card_of_injOn cellOffset (fun y _ => (h5 y).2) ?_
      intro y hy y' hy' e1
      rw [← (h5 y).1, ← (h5 y').1, hYs y hy, hYs y' hy', e1]
    rw [hFL] at h6
    rw [hZ]
    have : (Ys.card : ℝ) ≤ ((centredCube T.L).card : ℝ) := by exact_mod_cast h6
    linarith
  have hZ0 : 0 < Z := by
    rw [hZ]
    positivity
  rw [hG]
  set G : F.GaugeField F.top → ℝ := fun V₁ => ∑ y ∈ Ys, w y *
    minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V₁ 0) with hGdef
  have hone : ∀ (U : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * T.σ) U → 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |bondDeriv G U c X| ≤ Z * (B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c)))) := by
    intro U k c X hU h1 h3' hX
    refine (blockSum_deriv_le hM' hA₁.le hκ0 hF hU hρ Ys w hw hYs c X hX h1 h3').trans ?_
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hB0 (mul_nonneg hA₁.le (Real.exp_pos _).le))
  refine ⟨fun V hV => ⟨blockSum_contDiffThree hM' hA₁.le hκ0 hF hV hρ Ys w, fun k c X h1 h3' hX => ?_⟩,
    fun V V' q k b X hV hV' hag hk hb hX => ?_⟩
  · have hw0 := torusDecayFactor_pos T.L T.decayRate (bondSpan Y c : ℝ)
    rw [le_div_iff₀ hw0]
    have h5 := h3 (bondSpan Y c : ℝ) (by positivity)
    have h6 := hone V k c X hV h1 h3' hX
    set e := Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c)) with he
    have h7 : 0 ≤ Z * B * A₁ := by positivity
    calc |bondDeriv G V c X| * torusDecayFactor T.L T.decayRate (bondSpan Y c : ℝ)
        ≤ (Z * (B * (A₁ * e))) * torusDecayFactor T.L T.decayRate (bondSpan Y c : ℝ) :=
          mul_le_mul_of_nonneg_right h6 hw0.le
      _ = Z * B * A₁ * (torusDecayFactor T.L T.decayRate (bondSpan Y c : ℝ) * e) := by ring
      _ ≤ Z * B * A₁ * A₃ := mul_le_mul_of_nonneg_left h5 h7
      _ = (Z * A₁ * A₃) * B := by ring
      _ ≤ T.Cs * B := mul_le_mul_of_nonneg_right hC1 hB0
  have hmono : ∀ U : F.GaugeField F.top, IsSmallCurvature (9 / 8 * T.σ) U → IsSmallCurvature (5 / 4 * T.σ) U :=
    fun U hU p hp => (hU p hp).trans_le (by nlinarith)
  have hV5 := hmono V hV
  have hV5' := hmono V' hV'
  have hdq := torusDecayFactor_pos T.L T.decayRate (q : ℝ)
  rw [le_div_iff₀ hdq]
  set c := bondsAt Y b with hc
  have hsize : ∀ U : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) U →
      |bondDeriv G U c X| ≤ Z * (A₁ + Sz) * B := by
    intro U hU
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [bondDeriv_zero_top]
      have h5 : |G U| ≤ Ys.card * (B * Sz) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ y ∈ Ys, |w y * minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) U 0)|
            ≤ ∑ _y ∈ Ys, B * Sz := Finset.sum_le_sum fun y _ => by
              rw [abs_mul]
              exact mul_le_mul (hw y) (hsz t x F U y hx hF hU) (abs_nonneg _) hB0
          _ = _ := by simp
      have h6 : (Ys.card : ℝ) * (B * Sz) ≤ Z * (B * Sz) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hB0 hSz)
      have h7 : 0 ≤ Z * A₁ * B := by positivity
      nlinarith
    · have h5 := hone U k c X hU h0 (by omega) hX
      have h6 : Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ 2 ^ 7 * T.κ * bondSpan Y c := by positivity
        linarith)
      refine h5.trans ?_
      have h7 : B * (A₁ * Real.exp (-(2 ^ 7 * T.κ * bondSpan Y c))) ≤ B * A₁ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA₁.le h6) hB0
      have h8 : 0 ≤ Z * Sz * B := by positivity
      nlinarith
  by_cases hbig : 0 < B ∧ r₂ ≤ q
  · obtain ⟨hB, hq⟩ := hbig
    set E := Real.exp (-(T.chainParams.δ₂ / 18 * q)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ T.chainParams.δ₂ / 18 * q := by positivity
      linarith)
    have hE3 : E ^ 3 ≤ E := by
      have h5 : E ^ 2 ≤ 1 := pow_le_one₀ hE0.le hE1
      nlinarith
    have hEd : torusDecayFactor T.L T.decayRate (q : ℝ) * E ≤ A₄ := h4 q (by positivity)
    set M₀ := B * (Z * A₂ * E ^ 3) with hM₀
    have hM₀0 : 0 < M₀ := by positivity
    have hclose' : ∀ U U' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) U → IsSmallCurvature (5 / 4 * T.σ) U' →
        AgreeOnBall (finiteCells F) U (finiteCells F) U' Y Y q → |G U - G U'| ≤ M₀ := by
      intro U U' hU hU' hagU
      have e : G U - G U' = ∑ y ∈ Ys, w y *
          (minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) U 0) -
          minimalSiteShare T.a y (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) U' 0)) := by
        simp only [hGdef]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [e]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _y ∈ Ys, B * (A₂ * E ^ 3) := Finset.sum_le_sum fun y hy => by
            rw [abs_mul]
            exact mul_le_mul (hw y) (hclose t x F U U' Y q y hx hF hU hU' hagU hq (hYs y hy)) (abs_nonneg _) hB0
        _ = Ys.card * (B * (A₂ * E ^ 3)) := by simp
        _ ≤ Z * (B * (A₂ * E ^ 3)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = M₀ := by rw [hM₀]; ring
    have hfin : ∀ v Q : ℝ, v ≤ Q * B * E → 0 ≤ Q → Q * A₄ ≤ T.Cs →
        v * torusDecayFactor T.L T.decayRate (q : ℝ) ≤ T.Cs * B := by
      intro v Q h5 h6 h7
      calc v * torusDecayFactor T.L T.decayRate (q : ℝ) ≤ (Q * B * E) * torusDecayFactor T.L T.decayRate (q : ℝ) :=
            mul_le_mul_of_nonneg_right h5 hdq.le
        _ = Q * B * (torusDecayFactor T.L T.decayRate (q : ℝ) * E) := by ring
        _ ≤ Q * B * A₄ := mul_le_mul_of_nonneg_left hEd (by positivity)
        _ = (Q * A₄) * B := by ring
        _ ≤ T.Cs * B := mul_le_mul_of_nonneg_right h7 hB0
    have hM₀E : M₀ ≤ Z * A₂ * B * E := by
      have h5 : Z * A₂ * B * E ^ 3 ≤ Z * A₂ * B * E := mul_le_mul_of_nonneg_left hE3 (by positivity)
      calc M₀ = Z * A₂ * B * E ^ 3 := by rw [hM₀]; ring
        _ ≤ _ := h5
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [bondDeriv_zero_top, bondDeriv_zero_top]
      exact hfin _ (Z * A₂) ((hclose' V V' hV5 hV5' hag).trans hM₀E) (by positivity) hC2
    · have h5 := blockSum_deriv_sub_le hM' hA₁.le hκ0 hlines htwo hF hσ hV hV' hag Ys w hw hYs hcard hB0 hM₀0 hclose'
        b X h0 hk hb hX
      have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h0
      refine hfin _ (C₂ * (Z * A₂ * (1 + 64 / T.σ + (64 / T.σ) ^ 2) + (Z * A₂ + Z * A₁))) (h5.trans ?_)
        (by positivity) hC3
      exact deriv_bound_numbers hB hZ0 hA₁ hA₂ hE0 hE1 hE3 hσ hC₂ h0 hk
  · have h5 : |bondDeriv G V c X - bondDeriv G V' c X| ≤ 2 * (Z * (A₁ + Sz)) * B := by
      have h6 := abs_sub (bondDeriv G V c X) (bondDeriv G V' c X)
      have h7 := hsize V hV5
      have h8 := hsize V' hV5'
      linarith
    rcases eq_or_lt_of_le hB0 with h0 | h0
    · rw [← h0] at h5 ⊢
      have h6 : |bondDeriv G V c X - bondDeriv G V' c X| = 0 := by
        have := abs_nonneg (bondDeriv G V c X - bondDeriv G V' c X)
        linarith
      rw [h6]
      simp
    · have hq : q < r₂ := by
        by_contra hc
        exact hbig ⟨h0, by omega⟩
      have h6 : torusDecayFactor T.L T.decayRate (q : ℝ) ≤ torusDecayFactor T.L T.decayRate (r₂ : ℝ) :=
        torusDecayFactor_mono hδ0 (by positivity) (by exact_mod_cast hq.le)
      have h7 : 0 ≤ 2 * (Z * (A₁ + Sz)) * B := by positivity
      calc |bondDeriv G V c X - bondDeriv G V' c X| * torusDecayFactor T.L T.decayRate (q : ℝ)
          ≤ (2 * (Z * (A₁ + Sz)) * B) * torusDecayFactor T.L T.decayRate (r₂ : ℝ) := mul_le_mul h5 h6 hdq.le h7
        _ = (2 * (Z * (A₁ + Sz)) * torusDecayFactor T.L T.decayRate r₂) * B := by ring
        _ ≤ T.Cs * B := mul_le_mul_of_nonneg_right hC4 hB0
private theorem exp_pow_three (δ : ℝ) (q : ℕ) : Real.exp (-(δ / 18 * q)) ^ 3 = Real.exp (-(δ / 6 * q)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring
private theorem close_bound_numbers {S δ₁ δ₂ AW Cc : ℝ} {q : ℕ} (hCc : 0 ≤ Cc) (hδ₂ : 0 ≤ δ₂)
    (hδ₁ : 64 * δ₂ ≤ δ₁) :
    S * Real.exp (-(δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) * AW + Cc * Real.exp (-δ₁ * ((q / 3 : ℕ) : ℝ)) ≤
      (S * Real.exp (δ₂ / 4) * AW + Cc * Real.exp δ₁) * Real.exp (-(δ₂ / 18 * q)) ^ 3 := by
  rw [exp_pow_three]
  have e1 : Real.exp (-(δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) = Real.exp (δ₂ / 4) * Real.exp (-(δ₂ / 6 * q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-δ₁ * ((q / 3 : ℕ) : ℝ)) ≤ Real.exp δ₁ * Real.exp (-(δ₂ / 6 * q)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (q : ℝ) ≤ 3 * ((q / 3 : ℕ) : ℝ) + 2 := by
      have : q ≤ 3 * (q / 3) + 2 := by omega
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ ((q / 3 : ℕ) : ℝ) := by positivity
    have h3 : δ₂ / 6 * q ≤ δ₂ / 6 * (3 * ((q / 3 : ℕ) : ℝ) + 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : δ₂ * ((q / 3 : ℕ) : ℝ) ≤ δ₁ * ((q / 3 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right (by linarith) h2
    have h5 : 0 ≤ δ₂ * ((q / 3 : ℕ) : ℝ) := by positivity
    nlinarith
  rw [e1, add_mul]
  have h6 := mul_le_mul_of_nonneg_left e2 hCc
  have e3 : S * (Real.exp (δ₂ / 4) * Real.exp (-(δ₂ / 6 * q))) * AW =
      S * Real.exp (δ₂ / 4) * AW * Real.exp (-(δ₂ / 6 * q)) := by ring
  rw [e3]
  linarith
private theorem exists_radius_le_one (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, 6 ≤ r ∧ ∀ q : ℕ, r ≤ q → M * Real.exp (-(δ / 18 * q)) ^ 3 ≤ 1 := by
  refine ⟨max 6 ⌈6 * |M| / δ⌉₊, le_max_left _ _, fun q hq => ?_⟩
  rw [exp_pow_three]
  have h1 : 6 * |M| / δ ≤ q := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hq)
  have h2 : |M| ≤ δ / 6 * q := by
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  have h3 : δ / 6 * q + 1 ≤ Real.exp (δ / 6 * q) := Real.add_one_le_exp _
  have h4 : |M| ≤ Real.exp (δ / 6 * q) := by linarith
  have h5 : Real.exp (δ / 6 * q) * Real.exp (-(δ / 6 * q)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h6 : 0 < Real.exp (-(δ / 6 * q)) := Real.exp_pos _
  calc M * Real.exp (-(δ / 6 * q)) ≤ |M| * Real.exp (-(δ / 6 * q)) :=
        mul_le_mul_of_nonneg_right (le_abs_self M) h6.le
    _ ≤ Real.exp (δ / 6 * q) * Real.exp (-(δ / 6 * q)) := mul_le_mul_of_nonneg_right h4 h6.le
    _ = 1 := h5
private theorem weightedFrameSharesAt_of (hsites : SiteDecomposition) (hdist : SupDistCellComparison)
    (hcover : BlocksCoverLowerLevel) (hlines : SmallCurvatureAlongLineAndAgreeOn)
    (hbonds : cellBondsCardStatement)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {N K' : ℕ → ℝ} {D' : ℕ → ℕ → ℝ} {Cb A A₃ A₄ Wt C₂ : ℝ} {r₂ : ℕ} (hN0 : ∀ k, 0 < N k)
    (hold : ∀ (F : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth), IsBlockTorus T.L F → 0 < s →
      s ≤ T.chainParams.σA →
      IsSmallCurvature s W → ColdEstimatesBelow T.a T.chainParams.δ₁ s N W)
    (hcomp : ∀ (F F' : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth)
      (y : F.Site F.depth) (y' : F'.Site F'.depth)
      (r : ℕ), IsBlockTorus T.L F → IsBlockTorus T.L F' → F'.depth = F.depth → 0 < s →
      s ≤ T.chainParams.σA →
      IsSmallCurvature s W → IsSmallCurvature s W' → AgreeOnBox W W' y y' r →
      ColdComparisonBelow T.a T.chainParams.δ₁ T.chainParams.δ₂ s T.chainParams.s₀ N W W' y y' r)
    (hB : ∀ (F : BlockFrame) (n₀ k p m : ℕ) (σ s a ρA : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
      (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F) (y : F.Site F.depth),
      F.blockSide = T.L → IsLargeCubicTorus F → IsCubicTorusAbove T.L F.depth n₀ F → k ≤ 6 → (∀ j, 0 ≤ e j) →
      HasBoundedDerivatives T.L F.depth n₀ σ (T.κ / 2 ^ 10) k e f →
      IsSmallCurvature σ (interpolatedField s a ρA m V η) →
      (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
        (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K' k' * Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ContDiffAt ℝ k (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0 ∧
      (1 ≤ p → p ≤ k →
        |iteratedFDeriv ℝ p (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
          Cb * runningMax e p *
            Real.exp (-(2 ^ 7 * T.κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w))))))
    (hCb : 0 < Cb) (hA1 : 1 ≤ A)
    (hA : ∀ x : ℝ, 0 ≤ x → torusDecayFactor T.L (T.κ / 2 ^ 10) x * Real.exp (-(T.chainParams.δ₁ / 2 * x)) ≤ A)
    (hLo : Odd T.L) (h64 : 64 ≤ T.n₀) (hκ : 0 < T.κ) (hσ : 0 < T.σ) (hσA : T.σ ≤ T.chainParams.σA) (hCt : 1 ≤ T.Ct)
    (hρ1 : T.chainParams.ρA ≤ 1) (hδ₁ : 0 < T.chainParams.δ₁) (hδ₂ : 0 < T.chainParams.δ₂)
    (hδ : 64 * T.chainParams.δ₂ ≤ T.chainParams.δ₁)
    (hnear : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x)
    (hker : interpolationKernelBoundsAt T K' D')
    (htwo : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ) (V : F.GaugeField F.top)
      (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        C₂ * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    (hC₂ : 0 ≤ C₂) (hWt0 : 0 ≤ Wt)
    (hWt : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * T.L ^ 4) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(2 ^ 7 * T.κ * (cellSupDist (y b) z : ℝ))) ≤ Wt)
    (hr₆ : 6 ≤ r₂)
    (hr₂ : ∀ q : ℕ, r₂ ≤ q →
      64 * T.Ct * Real.exp (T.chainParams.δ₂ / 4) * Real.exp (-(T.chainParams.δ₂ / 18 * q)) ^ 3 ≤ 1)
    (h3 : ∀ x : ℝ, 0 ≤ x → torusDecayFactor T.L T.decayRate x * Real.exp (-(2 ^ 7 * T.κ * x)) ≤ A₃)
    (h4 : ∀ x : ℝ, 0 ≤ x → torusDecayFactor T.L T.decayRate x * Real.exp (-(T.chainParams.δ₂ / 18 * x)) ≤ A₄)
    (hC : ∀ (A₁ A₂ Z Sz : ℝ), A₁ = Cb * runningMax (fun j => N j * A) 3 →
      A₂ = T.Ct * T.σ * Real.exp (T.chainParams.δ₂ / 4) * (A₁ * Wt) + T.σ ^ 2 * N 0 * Real.exp T.chainParams.δ₁ →
      Z = ((centredCube T.L).card : ℝ) + 1 → Sz = N 0 * T.σ ^ 2 →
      Z * A₁ * A₃ ≤ T.Cs ∧ Z * A₂ * A₄ ≤ T.Cs ∧
      C₂ * (Z * A₂ * (1 + 64 / T.σ + (64 / T.σ) ^ 2) + (Z * A₂ + Z * A₁)) * A₄ ≤ T.Cs ∧
      2 * (Z * (A₁ + Sz)) * torusDecayFactor T.L T.decayRate r₂ ≤ T.Cs) :
    weightedFrameSharesStatementAt T := by
  obtain ⟨A₁, hA₁d⟩ : ∃ A₁, A₁ = Cb * runningMax (fun j => N j * A) 3 := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂d⟩ : ∃ A₂, A₂ = T.Ct * T.σ * Real.exp (T.chainParams.δ₂ / 4) * (A₁ * Wt) +
      T.σ ^ 2 * N 0 * Real.exp T.chainParams.δ₁ :=
    ⟨_, rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = ((centredCube T.L).card : ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨Sz, hSzd⟩ : ∃ Sz, Sz = N 0 * T.σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨hC1, hC2, hC3, hC4⟩ := hC A₁ A₂ Z Sz hA₁d hA₂d hZd hSzd
  have hA0 : 0 < A := by linarith
  have hκ0 := hκ.le
  have hfam : ∀ t : ℕ, HasBoundedDerivatives T.L t T.n₀ T.σ (T.κ / 2 ^ 10) 3 (fun j => N j * A)
      (admissibleShares T.a T.L) :=
    fun t => admissibleShares_hasBoundedDerivatives hN0 hold hdist hσ hσA hδ₁ hA1 hA
  have hlarge : 0 < runningMax (fun j => N j * A) 3 := by
    have h1 : (fun j => N j * A) 3 ≤ runningMax (fun j => N j * A) 3 := by
      simp [runningMax]
    exact lt_of_lt_of_le (mul_pos (hN0 3) hA0) h1
  have hA₁ : 0 < A₁ := by
    rw [hA₁d]
    exact mul_pos hCb hlarge
  have hM : ∀ x : ℝ, T.coupling ≤ x → SharePerturbationBounds T (frameRadius x) A₁ := fun x hx => by
    rw [hA₁d]
    exact sharePerturbationBounds_of hcover hLo h64 hρ1 hσ hx (fun t => hnear t x hx) hker hB hN0 hA0.le hCb.le hfam
  have hCtσ : 0 < T.Ct * T.σ := by positivity
  have hA₂ : 0 < A₂ := by
    rw [hA₂d]
    have := hN0 0
    have h1 : 0 ≤ T.Ct * T.σ * Real.exp (T.chainParams.δ₂ / 4) * (A₁ * Wt) := by positivity
    have h2 : 0 < T.σ ^ 2 * N 0 * Real.exp T.chainParams.δ₁ := by positivity
    linarith
  refine weightedFrameShares_of_bounds hM hA₁ hκ hσ hLo (by omega) hsites hlines htwo ?_ ?_ hA₂ ?_ hZd hδ₂ hC₂ h3 h4
    hC1 hC2 hC3 hC4
  · intro t x F V V' Y q y hx hF hV hV' hag hq hy
    obtain ⟨hFL, ht, n, hside, hn⟩ := id hF
    have hchain : IsBlockTorus T.L F := ⟨hFL, n, by omega, hside⟩
    have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
    have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
    have hsm := ((hnear t x hx).single F V 1 hF hV zero_le_one le_rfl).2
    have hsm' := ((hnear t x hx).single F V' 1 hF hV' zero_le_one le_rfl).2
    have hloc := ((hnear t x hx).pair F F V V' Y Y q 1 hF hF hV hV' hag zero_le_one le_rfl).norm_sub_le
    have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
        IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V η) := fun η hη p hp =>
      (hsm.small_curvature_nearby η hη p hp).trans_le (by nlinarith)
    have hcold' : IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V' 0) := fun p hp =>
      (hsm'.small_curvature p hp).trans_le (by nlinarith)
    have hcmp : ∀ (W W' : F.GaugeField F.depth) (r : ℕ), IsSmallCurvature T.σ W → IsSmallCurvature T.σ W' →
        AgreeOnBox W W' y y r →
        |minimalSiteShare T.a y W - minimalSiteShare T.a y W'| ≤ T.σ ^ 2 * N 0 * Real.exp (-T.chainParams.δ₁ * r) := by
      intro W W' r hW hW' hAg
      have h1 := (hcomp F F T.σ W W' y y r hchain hchain rfl hσ hσA hW hW' hAg).siteShare_deriv_close 0 Fin.elim0
        Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
      rw [bondDeriv_zero_depth, bondDeriv_zero_depth] at h1
      simpa [derivativeScale] using h1
    have hsum : ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 7 * T.κ * cellSupDist (enclosingCell b.1.1) (enclosingCell y))) ≤ Wt := by
      refine hWt F _ (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) (fun z => ?_) (enclosingCell y)
      have h1 := hbonds F hLF hs2 z
      rw [hFL] at h1
      convert h1
    have hq6 : 6 ≤ q := hr₆.trans hq
    have hg : T.Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) ≤ T.ballRadius := by
      have h1 := hr₂ q hq
      rw [exp_pow_three] at h1
      have e : Real.exp (-(T.chainParams.δ₂ / 4 * (2 * (q : ℝ) / 3 - 1))) =
          Real.exp (T.chainParams.δ₂ / 4) * Real.exp (-(T.chainParams.δ₂ / 6 * q)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      have h2 : T.ballRadius = T.σ / 64 := rfl
      rw [h2]
      have h3' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ T.σ / 64)
      calc _ = T.σ / 64 * (64 * T.Ct * Real.exp (T.chainParams.δ₂ / 4) * Real.exp (-(T.chainParams.δ₂ / 6 * q))) := by
            ring
        _ ≤ T.σ / 64 * 1 := h3'
        _ = T.σ / 64 := mul_one _
    have h1 := share_sub_le_of_agree hsites hdist hcover (hM x hx) hA₁.le hκ0 hLo (by omega) hF hV hag hq6 hloc
      hCtσ.le hδ₂.le hg y hy hcold hcold' hcmp hsum
    refine h1.trans ?_
    rw [hA₂d]
    exact close_bound_numbers (by have := hN0 0; positivity) hδ₂.le hδ
  · intro t x F V y hx hF hV
    obtain ⟨hFL, ht, n, hside, hn⟩ := id hF
    have hchain : IsBlockTorus T.L F := ⟨hFL, n, by omega, hside⟩
    have hsm := ((hnear t x hx).single F V 1 hF hV zero_le_one le_rfl).2
    have hcold : IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V 0) := fun p hp =>
      (hsm.small_curvature p hp).trans_le (by nlinarith)
    have h1 := (hold F T.σ _ hchain hσ hσA hcold).siteShare_bounds y
    rw [abs_of_nonneg h1.1, hSzd]
    exact h1.2
  · rw [hSzd]
    have := hN0 0
    positivity
theorem weightedFrameSharesStatement_holds (hker : interpolationKernelBoundsStatement)
    (hnear : interpolatedFramesControlled)
    (hbound : boundAlongPerturbationsStatement) (hch : ColdEstimatesAtEveryDepth)
    (htwo : DerivDiffLeOfCloseAlongLines) (hlines : SmallCurvatureAlongLineAndAgreeOn)
    (hweights : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) (hbonds : cellBondsCardStatement)
    (hsites : SiteDecomposition) (hdist : SupDistCellComparison)
    (hcover : BlocksCoverLowerLevel) (hJ : EventuallyInParametersCombines) : weightedFrameSharesStatement := by
  obtain ⟨K, D, hK0, hD0, hKt⟩ := hker
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ =>
    ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h =>
      ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hP := hJ.1 _ _ hKt (hJ.1 _ _ hnear h64)
  obtain ⟨C₂, hC₂, htw⟩ := htwo
  intro a ha
  obtain ⟨L₀, h1⟩ := hP a ha
  refine ⟨max L₀ (2 ^ 40), fun L hLo hL c hc => ?_⟩
  have hL40 : 2 ^ 40 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨Ct₀, h2⟩ := h1 L hLo ((le_max_left _ _).trans hL) c hc
  obtain ⟨N, hN0, hNc⟩ := hch a L c ha hLo hL40 hc
  obtain ⟨⟨hρ, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, -⟩ := hc.classical
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have hδ : 2 ^ 6 * c.δ₂ ≤ c.δ₁ := hc.inequalities.2.1
  have hδ' : 64 * c.δ₂ ≤ c.δ₁ := by linarith
  refine ⟨max Ct₀ 1, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h3⟩ := h2 Ct ((le_max_left _ _).trans hCt)
  have hCt1 : 1 ≤ Ct := (le_max_right _ _).trans hCt
  refine ⟨min κ₀ (c.δ₂ / 8), lt_min hκ₀ (by positivity), fun κ hκ hκc => ?_⟩
  have hκδ : κ ≤ c.δ₂ / 8 := hκc.trans (min_le_right _ _)
  obtain ⟨η₀, hη₀, h4⟩ := h3 κ hκ (hκc.trans (min_le_left _ _))
  refine ⟨η₀, hη₀, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₀, h5⟩ := h4 η₃ a1 a2 a3
  refine ⟨N₀, fun nss hn => ?_⟩
  obtain ⟨σ₀, hσ₀, h6⟩ := h5 nss hn
  refine ⟨min σ₀ c.σA, lt_min hσ₀ hc.positivity.2.2.2.1, fun σ hσ hσc p hp => ?_⟩
  obtain ⟨C₀, h7⟩ := h6 σ hσ (hσc.trans (min_le_left _ _)) p hp
  have hL1 : 1 ≤ L := hLo.pos
  have hκ10 : 0 ≤ κ / 2 ^ 10 := by positivity
  obtain ⟨A, hA1, hA⟩ := torusDecayFactor_mul_exp_le (δ := κ / 2 ^ 10) (r := c.δ₁ / 2) hL1 (by positivity) (by
    have : κ ≤ c.δ₁ := by nlinarith
    nlinarith)
  obtain ⟨A₃, hA₃1, hA₃⟩ := torusDecayFactor_mul_exp_le (δ := κ / 2 ^ 10) (r := 2 ^ 7 * κ) hL1 (by positivity)
    (by nlinarith)
  obtain ⟨A₄, hA₄1, hA₄⟩ := torusDecayFactor_mul_exp_le (δ := κ / 2 ^ 10) (r := c.δ₂ / 18) hL1 (by positivity)
    (by nlinarith)
  set T₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters := ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ with hT₀
  obtain ⟨Cb, hCb, hB⟩ := hbound (K T₀) c.κ₂ κ L (fun k => (hK0 T₀ k).le) hκ (by nlinarith) hLo hL40
  obtain ⟨Wt, hWt0, hWt⟩ := hweights (4 * L ^ 4) (2 ^ 7 * κ) (by positivity)
  obtain ⟨r₂, hr₆, hr₂⟩ := exists_radius_le_one (64 * Ct * Real.exp (c.δ₂ / 4)) hδ₂
  obtain ⟨A₁, hA₁d⟩ : ∃ A₁, A₁ = Cb * runningMax (fun j => N j * A) 3 := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂d⟩ : ∃ A₂, A₂ = Ct * σ * Real.exp (c.δ₂ / 4) * (A₁ * Wt) + σ ^ 2 * N 0 * Real.exp c.δ₁ :=
    ⟨_, rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = ((centredCube L).card : ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨Sz, hSzd⟩ : ∃ Sz, Sz = N 0 * σ ^ 2 := ⟨_, rfl⟩
  refine ⟨max (max C₀ (Z * A₁ * A₃)) (max (Z * A₂ * A₄) (max
    (C₂ * (Z * A₂ * (1 + 64 / σ + (64 / σ) ^ 2) + (Z * A₂ + Z * A₁)) * A₄)
    (2 * (Z * (A₁ + Sz)) * torusDecayFactor L (κ / 2 ^ 10) r₂))), fun Cs hCs E hE => ?_⟩
  have c0 : C₀ ≤ Cs := (le_max_left _ _).trans ((le_max_left _ _).trans hCs)
  have c1 : Z * A₁ * A₃ ≤ Cs := (le_max_right _ _).trans ((le_max_left _ _).trans hCs)
  have c2 : Z * A₂ * A₄ ≤ Cs := (le_max_left _ _).trans ((le_max_right _ _).trans hCs)
  have c3 : C₂ * (Z * A₂ * (1 + 64 / σ + (64 / σ) ^ 2) + (Z * A₂ + Z * A₁)) * A₄ ≤ Cs :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hCs))
  have c4 : 2 * (Z * (A₁ + Sz)) * torusDecayFactor L (κ / 2 ^ 10) r₂ ≤ Cs :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hCs))
  obtain ⟨m₀, h8⟩ := h7 Cs c0 E hE
  refine ⟨m₀, fun n₀ hn0 => ?_⟩
  obtain ⟨C₃, h9⟩ := h8 n₀ hn0
  refine ⟨C₃, fun CE hCE => ?_⟩
  obtain ⟨y₀, h10⟩ := h9 CE hCE
  refine ⟨y₀, fun y₁ hy => ?_⟩
  obtain ⟨hk, hnr, h64'⟩ := h10 y₁ hy
  refine weightedFrameSharesAt_of (T := ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, n₀, CE, y₁⟩) (N := N) (Cb := Cb)
    (A := A) (A₃ := A₃) (A₄ := A₄) (Wt := Wt) (C₂ := C₂) (r₂ := r₂)
    hsites hdist hcover hlines hbonds hN0 hNc.1 hNc.2 hB hCb hA1 hA hLo h64' hκ hσ (hσc.trans (min_le_right _ _))
    hCt1 hρ1 hδ₁ hδ₂ hδ' hnr hk htw hC₂.le hWt0 (fun F ι _ y hy' z => hWt F ι y hy' z) hr₆ hr₂ hA₃ hA₄ ?_
  intro B₁ B₂ Z' Sz' e1 e2 e3 e4
  simp only at e1 e2 e3 e4
  subst e1
  subst e2
  subst e3
  subst e4
  rw [← hA₁d, ← hA₂d, ← hZd, ← hSzd] at *
  exact ⟨c1, c2, c3, c4⟩
end ResponseInTheExpansion
end YangMills.Construction
end
