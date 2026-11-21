import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecay
import YangMills.Construction.Continuum.FunctionOfASystemSumsItsSeries
import YangMills.Construction.Continuum.SumOverTheFrequenciesOfASystem
import YangMills.Construction.FourierSeries.SeriesOfASmoothPeriodicFunctionWithSummableCoefficients
import YangMills.Construction.RealFunctions.GevreyBumpBounds
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff Matrix
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace SeriesExpansion
section Periodize
variable {D : ℕ} {m : ℝ} {a : Fin D → ℝ} {Ψ : (Fin D → ℝ) → ℂ}
def latticeShift (m : ℝ) (κ : Fin D → ℤ) : Fin D → ℝ := fun ι => 2 * m * κ ι
def periodize (m : ℝ) (Ψ : (Fin D → ℝ) → ℂ) : (Fin D → ℝ) → ℂ :=
  fun u => ∑ᶠ κ : Fin D → ℤ, Ψ (u + latticeShift m κ)
theorem latticeShift_eq_of_ne_zero (hm : 0 < m)
    (hΨ : ∀ u, Ψ u ≠ 0 → ∀ ι, |u ι - a ι| ≤ 3 / 4 * m)
    {u v : Fin D → ℝ} {κ κ' : Fin D → ℤ} (huv : ∀ ι, |u ι - v ι| < m / 4)
    (h1 : Ψ (u + latticeShift m κ) ≠ 0) (h2 : Ψ (v + latticeShift m κ') ≠ 0) : κ = κ' := by
  funext ι
  have a1 := abs_le.1 (hΨ _ h1 ι)
  have a2 := abs_le.1 (hΨ _ h2 ι)
  have a3 := abs_lt.1 (huv ι)
  simp only [Pi.add_apply, latticeShift] at a1 a2
  have c1 : (κ ι : ℝ) - κ' ι < 1 := by
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) (by positivity : 0 ≤ 2 * m)
    nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have c2 : -1 < (κ ι : ℝ) - κ' ι := by
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) (by positivity : 0 ≤ 2 * m)
    nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have d1 : κ ι - κ' ι < 1 := by exact_mod_cast c1
  have d2 : -1 < κ ι - κ' ι := by exact_mod_cast c2
  omega
theorem locallyFinite_support_translates (hm : 0 < m)
    (hΨ : ∀ u, Ψ u ≠ 0 → ∀ ι, |u ι - a ι| ≤ 3 / 4 * m) :
    LocallyFinite fun κ : Fin D → ℤ => Function.support fun u => Ψ (u + latticeShift m κ) := by
  intro x
  refine ⟨Metric.ball x (m / 8), Metric.ball_mem_nhds x (by positivity),
    Set.Subsingleton.finite ?_⟩
  rintro κ ⟨u, hu, hux⟩ κ' ⟨v, hv, hvx⟩
  refine latticeShift_eq_of_ne_zero hm hΨ (u := u) (v := v) (fun ι => ?_) hu hv
  have e1 : |u ι - x ι| < m / 8 := by
    have := (dist_le_pi_dist u x ι).trans_lt (Metric.mem_ball.1 hux)
    rwa [Real.dist_eq] at this
  have e2 : |v ι - x ι| < m / 8 := by
    have := (dist_le_pi_dist v x ι).trans_lt (Metric.mem_ball.1 hvx)
    rwa [Real.dist_eq] at this
  have := abs_lt.1 e1
  have := abs_lt.1 e2
  rw [abs_lt]
  constructor <;> linarith
theorem contDiff_periodize (hm : 0 < m) (hΨ : ∀ u, Ψ u ≠ 0 → ∀ ι, |u ι - a ι| ≤ 3 / 4 * m)
    (hs : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (periodize m Ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hsx⟩ := finsum_eventually_eq_sum (locallyFinite_support_translates hm hΨ) x
  have hsum : ContDiffAt ℝ ∞ (fun u => ∑ κ ∈ s, Ψ (u + latticeShift m κ)) x :=
    (ContDiff.sum fun κ _ => hs.comp (contDiff_id.add contDiff_const)).contDiffAt
  exact hsum.congr_of_eventuallyEq hsx
theorem periodize_periodic : FourierSeries.IsPeriodicInEachCoord (2 * m) (periodize m Ψ) := by
  intro ι x
  have hx : Function.update x ι (x ι + 2 * m) = x + latticeShift m (Pi.single ι 1) := by
    funext k
    by_cases h : k = ι
    · subst h
      simp [latticeShift]
    · simp [latticeShift, h]
  unfold periodize
  rw [hx, ← finsum_comp_equiv (Equiv.addLeft (Pi.single ι 1 : Fin D → ℤ))
    (f := fun κ => Ψ (x + latticeShift m κ))]
  refine finsum_congr fun κ => ?_
  congr 1
  funext k
  simp only [Pi.add_apply, latticeShift, Equiv.coe_addLeft, Int.cast_add]
  ring
theorem periodize_eq_self (hm : 0 < m) (hΨ : ∀ u, Ψ u ≠ 0 → ∀ ι, |u ι - a ι| ≤ 3 / 4 * m)
    {u : Fin D → ℝ} (hu : ∀ ι, |u ι - a ι| ≤ m) : periodize m Ψ u = Ψ u := by
  unfold periodize
  rw [finsum_eq_single _ (0 : Fin D → ℤ)]
  · have : u + latticeShift m (0 : Fin D → ℤ) = u := by
      funext k
      simp [latticeShift]
    rw [this]
  · intro κ hκ
    by_contra hne
    obtain ⟨ι, hι⟩ := Function.ne_iff.1 hκ
    have a1 := abs_le.1 (hΨ _ hne ι)
    have a2 := abs_le.1 (hu ι)
    simp only [Pi.add_apply, latticeShift] at a1
    have hι' : κ ι ≠ 0 := hι
    rcases lt_or_gt_of_ne hι' with h | h
    · have h1 : (κ ι : ℝ) ≤ -1 := by exact_mod_cast (by omega : κ ι ≤ -1)
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * m)
      nlinarith [a1.1, a1.2, a2.1, a2.2]
    · have h1 : (1 : ℝ) ≤ κ ι := by exact_mod_cast (by omega : 1 ≤ κ ι)
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * m)
      nlinarith [a1.1, a1.2, a2.1, a2.2]
theorem supCoord_le_iff {x : Fin D → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    EuclideanCoords.supCoord x ≤ r ↔ ∀ ι, |x ι| ≤ r := by
  constructor
  · intro h ι
    exact (le_ciSup (f := fun ι => |x ι|) (Set.finite_range _).bddAbove ι).trans h
  · exact fun h => Real.iSup_le h hr
theorem measurableSet_supCoord_ball (hm : 0 < m) :
    MeasurableSet {x : Fin D → ℝ | EuclideanCoords.supCoord (x - a) ≤ m} := by
  have : {x : Fin D → ℝ | EuclideanCoords.supCoord (x - a) ≤ m} =
      ⋂ ι, {x : Fin D → ℝ | |x ι - a ι| ≤ m} := by
    ext x
    simp [supCoord_le_iff hm.le]
  rw [this]
  exact MeasurableSet.iInter fun ι =>
    (isClosed_le (by fun_prop) continuous_const).measurableSet
theorem cubeCoeff_periodize (hm : 0 < m)
    (hΨ : ∀ u, Ψ u ≠ 0 → ∀ ι, |u ι - a ι| ≤ 3 / 4 * m) (ξ : Fin D → ℝ) :
    FourierSeries.cubeCoeff m a (periodize m Ψ) ξ = FourierSeries.cubeCoeff m a Ψ ξ := by
  unfold FourierSeries.cubeCoeff
  congr 1
  refine setIntegral_congr_fun (measurableSet_supCoord_ball hm) fun x hx => ?_
  have hx' : ∀ ι, |(x - a) ι| ≤ m := (supCoord_le_iff hm.le).1 hx
  simp only [periodize_eq_self hm hΨ (u := x) hx']
theorem hasExpansion_on_box
    (hS : FourierSeries.fourierSeries_eq_of_smooth_periodic_summable)
    (hD : 1 ≤ D) (hm : 0 < m) (hs : ContDiff ℝ ∞ Ψ)
    (hΨ : ∀ u, Ψ u ≠ 0 → ∀ ι, |u ι - a ι| ≤ 3 / 4 * m)
    (hsum : Summable fun ξ : FourierSeries.dualLattice D m => ‖FourierSeries.cubeCoeff m a Ψ ξ‖)
    {u : Fin D → ℝ} (hu : ∀ ι, |u ι - a ι| ≤ m) :
    Ψ u = ∑' ξ : FourierSeries.dualLattice D m, FourierSeries.cubeCoeff m a Ψ ξ *
      Complex.exp (Complex.I * (((ξ : Fin D → ℝ) ⬝ᵥ (u - a) : ℝ) : ℂ)) := by
  have key := hS D hD m hm a (periodize m Ψ) (contDiff_periodize hm hΨ hs)
    periodize_periodic
    (by simpa only [cubeCoeff_periodize hm hΨ] using hsum) u
  simpa only [cubeCoeff_periodize hm hΨ, periodize_eq_self hm hΨ hu] using key
end Periodize
section Unflatten
variable {n : ℕ}
def unflatten (n : ℕ) : (Fin (n * 4) → ℝ) ≃ₗ[ℝ] Config n where
  toFun u := fun i c => u (finProdFinEquiv (i, c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := fun ι => x (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2
  left_inv u := by
    funext ι
    show u (finProdFinEquiv ((finProdFinEquiv.symm ι).1, (finProdFinEquiv.symm ι).2)) = u ι
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv x := by
    funext i c
    simp
theorem unflatten_apply (u : Fin (n * 4) → ℝ) (i : Fin n) (c : Fin 4) :
    unflatten n u i c = u (finProdFinEquiv (i, c)) := rfl
theorem unflatten_symm_apply (x : Config n) (ι : Fin (n * 4)) :
    (unflatten n).symm x ι = x (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2 := rfl
theorem measurableEmbedding_unflatten : MeasurableEmbedding (unflatten n) :=
  (unflatten n).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
theorem measurePreserving_unflatten : MeasurePreserving (unflatten n) volume volume := by
  have hc : Continuous (unflatten n) := (unflatten n).toContinuousLinearEquiv.continuous
  refine ⟨hc.measurable, ?_⟩
  let L := (unflatten n).toContinuousLinearEquiv
  have : (Measure.map L (volume : Measure (Fin (n * 4) → ℝ))).IsAddHaarMeasure :=
    L.isAddHaarMeasure_map volume
  have hvol : (volume : Measure (Config n)).IsAddHaarMeasure := by
    have h4 : (volume : Measure (Fin 4 → ℝ)).IsAddHaarMeasure := inferInstance
    exact Measure.pi.isAddHaarMeasure (fun _ : Fin n => (volume : Measure (Fin 4 → ℝ)))
  have hsm := Measure.isAddLeftInvariant_eq_smul
    (Measure.map L (volume : Measure (Fin (n * 4) → ℝ))) (volume : Measure (Config n))
  set K : Set (Config n) := Set.pi univ fun _ => Set.pi univ fun _ => Icc (0 : ℝ) 1 with hK
  have hKm : MeasurableSet K :=
    MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvK : volume K = 1 := by
    rw [hK, volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    simp
  have hpre : L ⁻¹' K = Set.pi univ fun _ => Icc (0 : ℝ) 1 := by
    ext u
    simp only [hK, mem_preimage, mem_pi, mem_univ, forall_const]
    constructor
    · intro h ι
      have h1 := h (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2
      have h2 : L u (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2 = u ι := by
        show u (finProdFinEquiv ((finProdFinEquiv.symm ι).1, (finProdFinEquiv.symm ι).2)) = u ι
        rw [Prod.mk.eta, Equiv.apply_symm_apply]
      rwa [h2] at h1
    · intro h i c
      exact h _
  have hvL : Measure.map L (volume : Measure (Fin (n * 4) → ℝ)) K = 1 := by
    rw [Measure.map_apply L.continuous.measurable hKm, hpre, volume_pi_pi]
    simp
  have hone := congrArg (fun μ : Measure (Config n) => μ K) hsm
  simp only [hvL, Measure.smul_apply, hvK] at hone
  have hcst : Measure.addHaarScalarFactor
      (Measure.map L (volume : Measure (Fin (n * 4) → ℝ))) (volume : Measure (Config n)) = 1 := by
    have h2 : (1 : ENNReal) = (Measure.addHaarScalarFactor
      (Measure.map L (volume : Measure (Fin (n * 4) → ℝ))) (volume : Measure (Config n)) : ENNReal) := by
      simpa [ENNReal.smul_def] using hone
    exact_mod_cast h2.symm
  rw [hcst, one_smul] at hsm
  exact hsm
theorem configDot_unflatten (ξ u : Fin (n * 4) → ℝ) :
    configDot (unflatten n ξ) (unflatten n u) = ξ ⬝ᵥ u := by
  simp only [configDot, dotProduct, unflatten_apply]
  rw [← Fintype.sum_prod_type' (fun i c => ξ (finProdFinEquiv (i, c)) * u (finProdFinEquiv (i, c)))]
  exact Equiv.sum_comp finProdFinEquiv fun ι => ξ ι * u ι
theorem cubeCoeff_comp_unflatten (Q : PointSystem n) (Φ : Config n → ℂ) (ξ : Fin (n * 4) → ℝ) :
    FourierSeries.cubeCoeff Q.scale ((unflatten n).symm Q.base) (Φ ∘ unflatten n) ξ =
      Q.fourierCoeff Φ (unflatten n ξ) := by
  have hm : 0 < Q.scale := Q.scale_pos
  unfold FourierSeries.cubeCoeff PointSystem.fourierCoeff
  have hpow : (2 * Q.scale) ^ (n * 4) = (2 * Q.scale) ^ (4 * n) := by rw [mul_comm n 4]
  rw [hpow]
  congr 1
  have hset : {x : Fin (n * 4) → ℝ |
      EuclideanCoords.supCoord (x - (unflatten n).symm Q.base) ≤ Q.scale} =
      unflatten n ⁻¹' cylinderSet Q.outerBox := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, supCoord_le_iff hm.le]
    constructor
    · intro h i
      show EuclideanCoords.supCoord (unflatten n x i - Q.base i) ≤ 2 * Q.scale / 2
      rw [supCoord_le_iff (by positivity)]
      intro c
      have := h (finProdFinEquiv (i, c))
      simp only [Pi.sub_apply, unflatten_symm_apply, Equiv.symm_apply_apply] at this
      simpa [unflatten_apply] using (this.trans_eq (by ring) : _ ≤ 2 * Q.scale / 2)
    · intro h ι
      have h1 : EuclideanCoords.supCoord
          (unflatten n x (finProdFinEquiv.symm ι).1 - Q.base (finProdFinEquiv.symm ι).1) ≤
          2 * Q.scale / 2 := h (finProdFinEquiv.symm ι).1
      have h2 := (supCoord_le_iff (by positivity)).1 h1 (finProdFinEquiv.symm ι).2
      simp only [Pi.sub_apply, unflatten_symm_apply]
      simp only [Pi.sub_apply, unflatten_apply, Prod.mk.eta, Equiv.apply_symm_apply] at h2
      exact h2.trans_eq (by ring)
  rw [hset, ← measurePreserving_unflatten.setIntegral_preimage_emb measurableEmbedding_unflatten
    (fun x => Φ x * Complex.exp (-(Complex.I * ((configDot (unflatten n ξ) (x - Q.base) : ℝ) : ℂ))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hy : unflatten n u - Q.base = unflatten n (u - (unflatten n).symm Q.base) := by
    rw [map_sub, LinearEquiv.apply_symm_apply]
  simp only [Function.comp_apply, hy, configDot_unflatten]
def dualLatticeEquiv (Q : PointSystem n) :
    FourierSeries.dualLattice (n * 4) Q.scale ≃ Q.freqLattice :=
  (unflatten n).toEquiv.subtypeEquiv fun ξ => by
    constructor
    · rintro ⟨ζ, h⟩
      exact ⟨fun i c => ζ (finProdFinEquiv (i, c)), fun i c => h _⟩
    · rintro ⟨ζ, h⟩
      refine ⟨fun ι => ζ (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2, fun ι => ?_⟩
      have := h (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2
      have h2 : (unflatten n).toEquiv ξ (finProdFinEquiv.symm ι).1 (finProdFinEquiv.symm ι).2 =
          ξ ι := by
        show ξ (finProdFinEquiv ((finProdFinEquiv.symm ι).1, (finProdFinEquiv.symm ι).2)) = ξ ι
        rw [Prod.mk.eta, Equiv.apply_symm_apply]
      rw [h2] at this
      exact this
theorem dualLatticeEquiv_coe (Q : PointSystem n) (ξ : FourierSeries.dualLattice (n * 4) Q.scale) :
    ((dualLatticeEquiv Q ξ : Q.freqLattice) : Config n) = unflatten n ξ := rfl
end Unflatten
end SeriesExpansion
open SeriesExpansion in
theorem systemFunctionHasExpansion_holds
    (hb : Bumps.GevreyBumpBounds)
    (hDecay : SystemCoeffsDecay)
    (hFreq : FrequencySum.FrequencySumBound)
    (hSeries : FourierSeries.fourierSeries_eq_of_smooth_periodic_summable) :
    SystemFunctionHasExpansion := by
  obtain ⟨-, -, -, -, ⟨-, -, hrange, hone, hsupp, -⟩, -⟩ := hb
  intro n hn Q Φ hΦ x
  have hm : 0 < Q.scale := Q.scale_pos
  have hD : 1 ≤ n * 4 := by omega
  have hsm : ContDiff ℝ ∞ (Φ ∘ unflatten n) :=
    hΦ.1.comp (unflatten n).toContinuousLinearEquiv.contDiff
  have h0 : ∀ u, (Φ ∘ unflatten n) u ≠ 0 → ∀ ι,
      |u ι - (unflatten n).symm Q.base ι| ≤ 3 / 4 * Q.scale := by
    intro u hu ι
    have hmem : unflatten n u ∈ cylinderSet Q.midBox := hΦ.2 (subset_tsupport _ hu)
    have h1 : EuclideanCoords.supCoord
        (unflatten n u (finProdFinEquiv.symm ι).1 - Q.base (finProdFinEquiv.symm ι).1) ≤
        3 / 2 * Q.scale / 2 := hmem (finProdFinEquiv.symm ι).1
    have h2 := (supCoord_le_iff (by positivity)).1 h1 (finProdFinEquiv.symm ι).2
    simp only [Pi.sub_apply, unflatten_apply, Prod.mk.eta, Equiv.apply_symm_apply] at h2
    rw [unflatten_symm_apply]
    exact h2.trans_eq (by ring)
  have hsumQ : Summable fun ξ : Q.freqLattice => ‖Q.fourierCoeff Φ ξ‖ := by
    have hbound : ∀ ξ : Q.freqLattice, ‖‖Q.fourierCoeff Φ ξ‖‖ ≤
        (2 ^ (4 * n + 1) * scaledSupNorm (4 * n + 1) Q.scale Φ) *
          (1 + Q.scale * coordSupNorm (ξ : Config n)) ^ (-(4 * (n : ℤ)) - 1) := by
      intro ξ
      have hdec := hDecay n hn Q Φ hΦ (4 * n + 1) ξ ξ.2
      have hM : 0 ≤ coordSupNorm (ξ : Config n) :=
        Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
      have hw : 0 < 1 + Q.scale * coordSupNorm (ξ : Config n) := by positivity
      have hz : (1 + Q.scale * coordSupNorm (ξ : Config n)) ^ (-(4 * (n : ℤ)) - 1) =
          ((1 + Q.scale * coordSupNorm (ξ : Config n)) ^ (4 * n + 1))⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg]
        congr 1
        push_cast
        ring
      rw [norm_norm, hz, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hw _), mul_comm]
      exact hdec
    simpa only [norm_norm] using (hFreq n hn Q _ (fun ξ => ‖Q.fourierCoeff Φ ξ‖) hbound).1
  have hsumL : Summable fun ξ : FourierSeries.dualLattice (n * 4) Q.scale =>
      ‖FourierSeries.cubeCoeff Q.scale ((unflatten n).symm Q.base)
        (Φ ∘ unflatten n) ξ‖ := by
    refine ((dualLatticeEquiv Q).summable_iff.2 hsumQ).congr fun ξ => ?_
    rw [cubeCoeff_comp_unflatten]
    rfl
  set P : ℂ := ∏ i, ((Bumps.cubeBump (Q.scale⁻¹ • (x i - Q.base i)) : ℝ) : ℂ) with hP
  have hnormP : ‖P‖ ≤ 1 := by
    rw [hP, norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hrange _).1]
    exact (hrange _).2
  have hfactor : ∀ ξ : Config n, ∏ i, Q.modeFun i ξ (x i) =
      P * Complex.exp (Complex.I * ((configDot ξ (x - Q.base) : ℝ) : ℂ)) := by
    intro ξ
    simp only [PointSystem.modeFun, configDot]
    rw [Finset.prod_mul_distrib, hP]
    congr 1
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    rfl
  have hterm : ∀ ξ : Q.freqLattice, ‖Q.fourierCoeff Φ ξ * ∏ i, Q.modeFun i ξ (x i)‖ ≤
      ‖Q.fourierCoeff Φ ξ‖ := by
    intro ξ
    rw [hfactor, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) hnormP
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumQ, ?_⟩
  simp only [hfactor]
  by_cases hx : x ∈ cylinderSet Q.outerBox
  · have hu : ∀ ι, |(unflatten n).symm x ι - (unflatten n).symm Q.base ι| ≤ Q.scale := by
      intro ι
      have h1 : EuclideanCoords.supCoord
          (x (finProdFinEquiv.symm ι).1 - Q.base (finProdFinEquiv.symm ι).1) ≤
          2 * Q.scale / 2 := hx (finProdFinEquiv.symm ι).1
      have h2 := (supCoord_le_iff (by positivity)).1 h1 (finProdFinEquiv.symm ι).2
      rw [Pi.sub_apply] at h2
      rw [unflatten_symm_apply, unflatten_symm_apply]
      exact h2.trans_eq (by ring)
    have hseries := hasExpansion_on_box hSeries hD hm hsm h0 hsumL hu
    have hval : Φ x = ∑' ξ : Q.freqLattice, Q.fourierCoeff Φ ξ *
        Complex.exp (Complex.I * ((configDot (ξ : Config n) (x - Q.base) : ℝ) : ℂ)) := by
      rw [← (dualLatticeEquiv Q).tsum_eq]
      have hΦx : (Φ ∘ unflatten n) ((unflatten n).symm x) = Φ x := by
        simp
      rw [← hΦx, hseries]
      refine tsum_congr fun ξ => ?_
      rw [cubeCoeff_comp_unflatten, dualLatticeEquiv_coe]
      have hy : x - Q.base =
          unflatten n ((unflatten n).symm x - (unflatten n).symm Q.base) := by
        simp
      rw [hy, configDot_unflatten]
    have hsplit : ∀ ξ : Q.freqLattice, Q.fourierCoeff Φ ξ *
        (P * Complex.exp (Complex.I * ((configDot (ξ : Config n) (x - Q.base) : ℝ) : ℂ))) =
        P * (Q.fourierCoeff Φ ξ *
          Complex.exp (Complex.I * ((configDot (ξ : Config n) (x - Q.base) : ℝ) : ℂ))) :=
      fun ξ => by ring
    simp only [hsplit]
    rw [tsum_mul_left, ← hval]
    by_cases hz : Φ x = 0
    · simp [hz]
    · have hmid : x ∈ cylinderSet Q.midBox := hΦ.2 (subset_tsupport _ hz)
      have hP1 : P = 1 := by
        rw [hP]
        refine Finset.prod_eq_one fun i _ => ?_
        have hi : EuclideanCoords.supCoord (x i - Q.base i) ≤ 3 / 2 * Q.scale / 2 := hmid i
        have hin : ∀ c, (Q.scale⁻¹ • (x i - Q.base i)) c ∈ Icc (-(3 / 4) : ℝ) (3 / 4) := by
          intro c
          have hc := abs_le.1 ((supCoord_le_iff (by positivity)).1 hi c)
          have h1 : x i c - Q.base i c ≤ 3 / 2 * Q.scale / 2 := hc.2
          have h2 : -(3 / 2 * Q.scale / 2) ≤ x i c - Q.base i c := hc.1
          show Q.scale⁻¹ * (x i c - Q.base i c) ∈ Icc (-(3 / 4) : ℝ) (3 / 4)
          constructor
          · rw [le_inv_mul_iff₀ hm]
            linarith
          · rw [inv_mul_le_iff₀ hm]
            linarith
        rw [hone _ hin]
        simp
      rw [hP1, one_mul]
  · have hΦ0 : Φ x = 0 := by
      by_contra hz
      have hmid : x ∈ cylinderSet Q.midBox := hΦ.2 (subset_tsupport _ hz)
      refine hx fun i => ?_
      have hi : EuclideanCoords.supCoord (x i - Q.base i) ≤ 3 / 2 * Q.scale / 2 := hmid i
      show EuclideanCoords.supCoord (x i - Q.base i) ≤ 2 * Q.scale / 2
      linarith
    have hP0 : P = 0 := by
      have hnot : ¬ ∀ i, EuclideanCoords.supCoord (x i - Q.base i) ≤ 2 * Q.scale / 2 := hx
      simp only [not_forall, not_le] at hnot
      obtain ⟨i, hi⟩ := hnot
      rw [hP]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      have hout : Q.scale⁻¹ • (x i - Q.base i) ∉ tsupport Bumps.cubeBump := by
        intro h
        apply not_le.2 hi
        rw [supCoord_le_iff (by positivity)]
        intro c
        have hk := hsupp h c (mem_univ c)
        have h1 : -1 ≤ Q.scale⁻¹ * (x i c - Q.base i c) := hk.1
        have h2 : Q.scale⁻¹ * (x i c - Q.base i c) ≤ 1 := hk.2
        have h3 := (le_inv_mul_iff₀ hm).1 h1
        have h4 := (inv_mul_le_iff₀ hm).1 h2
        rw [Pi.sub_apply, abs_le]
        constructor <;> linarith
      rw [image_eq_zero_of_notMem_tsupport hout]
      simp
    simp [hΦ0, hP0]
end YangMills.Construction.ConfigSpace
