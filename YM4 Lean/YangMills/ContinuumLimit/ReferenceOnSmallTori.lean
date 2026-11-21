import Formulation.ReferenceCoupling
import YangMills.Construction.TheStatementsProvedTogether.FromSimilarityCarriesTheInfiniteLatticeProof
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCoveringProof
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace YangMills.ReferenceCalibration
open Construction Construction.PeriodicLattice Construction.Matrices TorusBound.ObservableCumulants

private theorem gibbs_moment_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (a f : X → ℝ) (ha : Continuous a) (hf : Continuous f) (hna : ∀ x, 0 ≤ a x)
    (q : ℕ) (hq : 0 < q) {B β T : ℝ} (hβ : 0 < β) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hdom : ∀ x, |f x| ≤ B * a x ^ q)
    (hZ : Real.exp (-T / 2) ≤ ∫ x, Real.exp (-β * a x) ∂μ) :
    |(∫ x, f x * Real.exp (-β * a x) ∂μ) / (∫ x, Real.exp (-β * a x) ∂μ)| ≤
      B * ((T / β) ^ q + ((2 * q : ℝ) / β) ^ q) := by
  let w (x : X) := Real.exp (-β * a x)
  let Z := ∫ x, w x ∂μ
  have hw : Continuous w := (continuous_const.mul ha).rexp
  have integ {F : X → ℝ} (h : Continuous F) : Integrable F μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpos : 0 < Z := (Real.exp_pos _).trans_le hZ
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  let c := (2 * q : ℝ) / β
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound (x : X) : |f x * w x| ≤
      (B * (T/β)^q) * w x + (B * c ^ q) * Real.exp (-T/2) := by
    have hwx : 0 < w x := Real.exp_pos _
    rw [abs_mul, abs_of_pos hwx]
    by_cases small : β * a x ≤ T
    · have hs : a x ≤ T/β := (le_div_iff₀ hβ).2 (by linarith)
      exact (mul_le_mul_of_nonneg_right ((hdom x).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hna x) hs q) hB)) hwx.le).trans
        (le_add_of_nonneg_right (by positivity))
    · have hsingle : a x ≤ c * Real.exp (a x / c) := by
        rw [mul_comm]
        exact (div_le_iff₀ hc).1 ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
      have hp := pow_le_pow_left₀ (hna x) hsingle q
      rw [mul_pow, ← Real.exp_nat_mul] at hp
      have hexp : (q : ℝ) * (a x / c) = β * a x / 2 := by
        dsimp [c]; field_simp
      rw [hexp] at hp
      calc |f x| * w x ≤ (B * (c^q * Real.exp (β * a x / 2))) * w x :=
              mul_le_mul_of_nonneg_right ((hdom x).trans (mul_le_mul_of_nonneg_left hp hB)) hwx.le
           _ = (B * c^q) * Real.exp (-(β*a x) / 2) := by
              dsimp [w]; rw [mul_assoc B, mul_assoc (c^q), ← Real.exp_add, ← mul_assoc]; congr 2; ring
           _ ≤ (B * c ^ q) * Real.exp (-T/2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp.2; linarith
           _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have habs : |∫ x, f x * w x ∂μ| ≤ B * (T/β)^q * Z + B * c^q * Real.exp (-T/2) := calc
    _ ≤ ∫ x, |f x * w x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (B * (T/β)^q) * w x + (B * c ^ q) * Real.exp (-T/2) ∂μ :=
      integral_mono (integ (hf.mul hw).abs) (integ ((continuous_const.mul hw).add continuous_const)) hbound
    _ = _ := by rw [integral_add ((integ hw).const_mul _) (integrable_const _), integral_const_mul]; simp [Z]
  rw [abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  change _ ≤ B * ((T/β)^q+c^q) * Z
  calc _ ≤ _ := habs
       _ ≤ B * (T/β)^q * Z + B * c^q * Z :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hZ (mul_nonneg hB (pow_nonneg hc.le q)))
       _ = _ := by ring

end YangMills.ReferenceCalibration
namespace YangMills.ReferenceCalibration.SmallBox
open Construction Construction.PeriodicLattice Construction.Matrices TorusBound.ObservableCumulants
variable (s : Conventions.StandingParameters) (K : ℕ+)
private abbrev Fields := Bond s.L s.m ((K : ℕ) : ℤ) → ComplexMatrix2
private abbrev Links := PositivelyOrientedBond s.L s.m ((K : ℕ) : ℤ)
private abbrev Configs := Links s K → ComplexMatrix2.specialUnitary
private abbrev Faces := Plaquette s.L s.m ((K : ℕ) : ℤ)
private local instance : Fintype (Faces s K) := by
  classical
  exact @Fintype.ofFinite _ (WilsonPlaquetteSum.finite_plaquette (by have := s.isAdmissible.2; omega) K)
private local instance : Finite (Links s K) := by
  have := Counting.bond_finite (L := s.L) (m := (s.m : ℕ)) (j := ((K : ℕ) : ℤ))
    (by have := s.isAdmissible.2; omega) (by have := s.m.pos; omega)
  exact Subtype.finite
private local instance : IsProbabilityMeasure (ComplexMatrix2.haarPi (Links s K)) := by
  unfold ComplexMatrix2.haarPi
  infer_instance
private abbrev action (v : Configs s K) := wilsonAction (gaugeFieldOfPositive v)
private abbrev energy (f : FourTorus s.L s.m → ℝ) (U : Fields s K) := smearedObservable f U

private theorem cost_nonneg (v : Configs s K) (p : Faces s K) :
    0 ≤ plaquetteCost (gaugeFieldOfPositive v) p := by
  apply (WilsonWeightGaugeInvariance.plaquetteEnergy_mem_Icc _ p).1
  apply WilsonWeightGaugeInvariance.gaugeFieldOfPositive_mem _ v
  exact fun _ => Counting.not_isPositivelyOriented_opposite
    (by have := s.isAdmissible.2; omega) (by have := K.pos; have := s.m.pos; omega)

private theorem z_formula (β : ℝ) : partitionFunction s.L s.m K β =
      ∫ v : Configs s K, Real.exp (-β * action s K v) ∂ComplexMatrix2.haarPi (Links s K) := by
  unfold partitionFunction productHaarMeasure
  rw [HaarWilsonInvarianceProof.measurableEmbedding_gaugeFieldOfPositive.integral_map]
  rfl
private theorem expectation_formula (β : ℝ) (F : Fields s K → ℝ) :
    (∫ U, F U ∂wilsonGibbsMeasure s.L s.m K β) =
    (∫ v : Configs s K, F (gaugeFieldOfPositive v) * Real.exp (-β * action s K v)
      ∂ComplexMatrix2.haarPi (Links s K)) /
    (∫ v : Configs s K, Real.exp (-β * action s K v) ∂ComplexMatrix2.haarPi (Links s K)) := by
  have hz : 0 ≤ partitionFunction s.L s.m K β := by
    rw [z_formula]
    exact integral_nonneg fun _ => (Real.exp_pos _).le
  rw [HaarWilsonInvarianceProof.integral_wilsonGibbsMeasure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hz, z_formula, smul_eq_mul, div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  simp only [boltzmannWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, action]
  ring

private theorem energy_dom (f : FourTorus s.L s.m → ℝ) {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (v : Configs s K) : |energy s K f (gaugeFieldOfPositive v)| ≤ B * action s K v := by
  rw [energy, smearedObservable_eq_sum, action, wilsonAction_eq_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [smul_eq_mul, abs_mul, abs_of_nonneg (cost_nonneg s K v p), mul_comm B]
  exact mul_le_mul_of_nonneg_left (hf _) (cost_nonneg s K v p)

private theorem moment_le (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T)
    (hz : Real.exp (-T/2) ≤ partitionFunction s.L s.m K β)
    (q : ℕ) (hq : 0 < q) (F : Fields s K → ℝ) (hF : Continuous F)
    {B : ℝ} (hB : 0 ≤ B) (hdom : ∀ v : Configs s K, |F (gaugeFieldOfPositive v)| ≤ B * action s K v ^ q) :
    |∫ U, F U ∂wilsonGibbsMeasure s.L s.m K β| ≤ B * ((T/β)^q+((2*q:ℝ)/β)^q) := by
  rw [expectation_formula]
  apply gibbs_moment_bound (ComplexMatrix2.haarPi (Links s K)) (action s K)
    _ (continuous_wilsonAction.comp HaarWilsonInvarianceProof.continuous_gaugeFieldOfPositive)
    (hF.comp HaarWilsonInvarianceProof.continuous_gaugeFieldOfPositive) _ q hq hβ hB hT hdom
  · exact (z_formula s K β) ▸ hz
  · intro v
    rw [action, wilsonAction_eq_sum]
    exact Finset.sum_nonneg fun p _ => cost_nonneg s K v p

private theorem covariance_le (f : Fin 2 → FourTorus s.L s.m → ℝ)
    {B β T : ℝ} (hB : 0 ≤ B) (hf : ∀ i x, |f i x| ≤ B)
    (hβ : 0 < β) (hT : 0 ≤ T) (hz : Real.exp (-T/2) ≤ partitionFunction s.L s.m K β) :
    |energyCovariance s K f β| ≤
      B^2 * ((T/β)^2 + (4/β)^2) + (B * (T/β + 2/β))^2 := by
  let E (i : Fin 2) := energy s K (f i)
  let μ := wilsonGibbsMeasure s.L s.m K β
  have hE (i) : |∫ U, E i U ∂μ| ≤ B * (T/β + 2/β) := by
    simpa [E, μ] using moment_le s K β T hβ hT hz 1 (by decide) (E i)
      (continuous_smearedObservable _) hB (by simpa [E] using energy_dom s K (f i) (hf i))
  have hEE : |∫ U, E 0 U * E 1 U ∂μ| ≤ B^2 * ((T/β)^2 + (4/β)^2) := by
    apply (moment_le s K β T hβ hT hz 2 (by decide) (fun U => E 0 U * E 1 U)
      ((continuous_smearedObservable _).mul (continuous_smearedObservable _)) (sq_nonneg B) ?_).trans
    · norm_num
    · intro v
      rw [abs_mul]
      have h0 := energy_dom s K (f 0) (hf 0) v
      have h1 := energy_dom s K (f 1) (hf 1) v
      calc
        _ ≤ (B*action s K v)*(B*action s K v) := mul_le_mul h0 h1 (abs_nonneg _) ((abs_nonneg _).trans h0)
        _ = _ := by ring
  refine (abs_sub _ _).trans (add_le_add hEE ?_)
  rw [abs_mul, sq]
  exact mul_le_mul (hE 0) (hE 1) (abs_nonneg _) ((abs_nonneg _).trans (hE 0))

private def sites (s : Conventions.StandingParameters) (K : ℕ+) := 2 * s.L ^ (s.m + K : ℕ)

private theorem partition_lower : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (s : Conventions.StandingParameters) (K : ℕ+) (β : ℝ), 1 ≤ β →
    Real.exp (-(((C + 6 * Real.log β) * (sites s K : ℝ)^4))) ≤ partitionFunction s.L s.m K β := by
  obtain ⟨C, hC⟩ := TheStatementsProvedTogether.wilsonPartition_bounds
  refine ⟨|C|, abs_nonneg _, ?_⟩
  intro s K β hβ
  have hL := s.isAdmissible.2
  have hpow : s.L ≤ s.L ^ (s.m + K : ℕ) := Nat.le_self_pow (by have := K.pos; omega) _
  have hn : 2 < sites s K := by dsimp [sites]; omega
  let : NeZero (sites s K) := ⟨by omega⟩
  have hs := TheStatementsProvedTogether.wilson_measure_torus s.L s.m K (sites s K) rfl hn
  rw [hs.partitionFunction_eq]
  change _ ≤ ClusterExpansionOfAStep.wilsonPartition β (sites s K)
  obtain ⟨hp, _, hl⟩ := hC β hβ (sites s K)
  apply (Real.le_log_iff_exp_le hp).1
  apply le_trans _ hl
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_right (add_le_add (le_abs_self C) le_rfl) (by positivity)

end YangMills.ReferenceCalibration.SmallBox
namespace YangMills.ReferenceCalibration.SmallBox
open Construction Construction.PeriodicLattice Construction.TopAux.NonemptyTestClasses

private theorem reference_tests_bounded (s : Conventions.StandingParameters) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, |fixedReferenceTests s.L s.m i x| ≤ B := by
  have hL : 0 < s.L := by have := s.isAdmissible.2; omega
  have hs : 0 < torusSide s.L s.m := by dsimp [torusSide]; positivity
  have hbp (c : Fin 4 → ℝ) := PeriodizationIdentities.periodize_norm_bounded hs
    (f := scaledBump (6/5) c)
    (⟨1, fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (scaledBump_nonneg ..)]; exact scaledBump_le_one ..⟩)
    (scaledBump_hasCompactSupport (by norm_num : (0:ℝ)<6/5) c)
  let d : Fin 4 → ℝ := Pi.single 0 3
  obtain ⟨u,hu⟩ := hbp 0
  obtain ⟨v,hv⟩ := hbp d
  have hid : (fun x => fixedReferenceBump (x - d)) = scaledBump (6/5) d := by
    funext x; simp [fixedReferenceBump, scaledBump]
  refine ⟨max |u| |v|, (abs_nonneg _).trans (le_max_left _ _), ?_⟩
  intro i x
  fin_cases i
  · exact (hu x).trans ((le_abs_self _).trans (le_max_left _ _))
  · change |TestFunctions.periodize _ (fun x => fixedReferenceBump (x-d)) x| ≤ _
    rw [hid]
    exact (hv x).trans ((le_abs_self _).trans (le_max_right _ _))

/-- On a fixed physical torus, the unweighted reference covariance vanishes whenever
the number of lattice sites times the Wilson free-energy bound is sublinear in β. -/
theorem referenceResponse_cold_of_sites {ι : Type*} {l : Filter ι}
    (s : Conventions.StandingParameters) (K : ι → ℕ+) (β : ι → ℝ)
    (hβ : Tendsto β l atTop)
    (hn : Tendsto (fun j => (2 * (s.L:ℝ)^(s.m + K j : ℕ))^4 * (1+Real.log (β j)) / β j) l (𝓝 0)) :
    Tendsto (fun j => referenceResponse s.L s.m (K j) (β j)) l (𝓝 0) := by
  obtain ⟨C,hC,hZ⟩ := partition_lower
  obtain ⟨B,hB,hf⟩ := reference_tests_bounded s
  let n (j : ι) := (sites s (K j) : ℝ)
  let T (j : ι) := 2 * ((C+6*Real.log (β j)) * (n j)^4)
  have hn' : Tendsto (fun j => (n j)^4 * (1+Real.log (β j)) / β j) l (𝓝 0) := by
    simpa [n, sites] using hn
  have he := hβ.eventually_ge_atTop 1
  have hT : Tendsto (fun j => T j / β j) l (𝓝 0) := by
    apply squeeze_zero' _ _ (show Tendsto (fun j => (2*(C+6)) * (n j ^ 4 * (1+Real.log (β j)) / β j)) l (𝓝 0)
      by simpa using hn'.const_mul (2*(C+6)))
    · filter_upwards [he] with j hj
      dsimp [T]; have := Real.log_nonneg hj; positivity
    · filter_upwards [he] with j hj
      have hb : 0 < β j := zero_lt_one.trans_le hj
      have hlog := Real.log_nonneg hj
      have hc : C+6*Real.log (β j) ≤ (C+6)*(1+Real.log (β j)) := by nlinarith [mul_nonneg hC hlog]
      calc T j / β j ≤ 2 * (((C+6)*(1+Real.log (β j))) * (n j)^4) / β j :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity)) (by norm_num)) hb.le
           _ = _ := by ring
  have hinv (c : ℝ) : Tendsto (fun j => c / β j) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hβ).const_mul c
  have htop := ((hT.pow 2).add ((hinv 4).pow 2)).const_mul (B^2) |>.add (((hT.add (hinv 2)).const_mul B).pow 2)
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using htop)
  filter_upwards [he] with j hj
  have hb := zero_lt_one.trans_le hj
  have ht : 0 ≤ T j := by dsimp [T]; have := Real.log_nonneg hj; positivity
  have hz := hZ s (K j) _ hj
  have hz' : Real.exp (-(T j)/2) ≤ partitionFunction s.L s.m (K j) (β j) := by
    convert hz using 2
    dsimp [T,n]; ring
  rw [Real.norm_eq_abs, referenceResponse, reference_covariance_eq s (K j) _ hb]
  exact covariance_le s (K j) _ hB hf hb ht hz'

private theorem counting_cold {ι : Type*} {l : Filter ι} (n β : ι → ℝ)
    (hn : ∀ j, 0 ≤ n j) (hβ : Tendsto β l atTop) {A : ℝ}
    (hA : ∀ᶠ j in l, n j ≤ A * β j ^ (1/92:ℝ)) :
    Tendsto (fun j => (n j)^4 * (1+Real.log (β j)) / β j) l (𝓝 0) := by
  have hi : Tendsto (fun j => β j ^ (-(22/23):ℝ)) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<22/23)).comp hβ
  have hlog : Tendsto (fun j => Real.log (β j) / (β j ^ (22/23:ℝ))) l (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<22/23)).tendsto_div_nhds_zero.comp hβ
  have hlim := (hi.add hlog).const_mul (A^4)
  apply squeeze_zero' _ _ (by simpa using hlim)
  · filter_upwards [hβ.eventually_ge_atTop 1] with j hj
    have := Real.log_nonneg hj
    positivity
  · filter_upwards [hβ.eventually_ge_atTop 1,hA] with j hj hsize
    have hb : 0 < β j := zero_lt_one.trans_le hj
    have hold : (β j ^ (1/92:ℝ))^4 = β j ^ (1 / 23:ℝ) := by
      rw [← Real.rpow_mul_natCast hb.le]
      norm_num
    have hpow : β j ^ (1/23:ℝ) / β j = β j ^ (-(22/23):ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one (β j)]
      rw [← Real.rpow_sub hb]
      norm_num
    have hhi := pow_le_pow_left₀ (hn j) hsize 4
    rw [mul_pow,hold] at hhi
    have hpos : 0 ≤ 1+Real.log (β j) := by have := Real.log_nonneg hj; linarith
    calc _ ≤ (A^4 * (β j ^ (1/23:ℝ))) * (1+Real.log (β j)) / β j :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hhi hpos) hb.le
         _ = A^4 * (1+Real.log (β j)) * (β j ^ (1/23:ℝ) / β j) := by ring
         _ = _ := by rw [hpow, Real.rpow_neg hb.le]; ring

theorem referenceResponse_cold_of_small_side {ι : Type*} {l : Filter ι}
    (s : Conventions.StandingParameters) (K : ι → ℕ+) (β : ι → ℝ)
    (hβ : Tendsto β l atTop) {A : ℝ}
    (hs : ∀ᶠ j in l, 2 * (s.L:ℝ)^(s.m + K j : ℕ) ≤ A * β j ^ (1/92:ℝ)) :
    Tendsto (fun j => referenceResponse s.L s.m (K j) (β j)) l (𝓝 0) :=
  referenceResponse_cold_of_sites s K β hβ (counting_cold _ β (fun _ => by positivity) hβ hs)

/-- A positive fixed reference covariance excludes every small-side subsequence. -/
theorem small_side_excluded_at_reference_level {ι : Type*} {l : Filter ι}
    (s : Conventions.StandingParameters) (K : ι → ℕ+) (β : ι → ℝ)
    (hβ : Tendsto β l atTop) {r : ℝ} (hr : 0 < r)
    (hlevel : ∀ᶠ j in l, r ≤ referenceResponse s.L s.m (K j) (β j)) (A : ℝ) :
    ∀ᶠ j in l, A * β j ^ (1/92:ℝ) < 2 * (s.L:ℝ)^(s.m + K j : ℕ) := by
  by_contra h
  let E := {j | 2 * (s.L:ℝ)^(s.m + K j : ℕ) ≤ A * β j ^ (1/92:ℝ)}
  have hf : ∃ᶠ j in l, j ∈ E := by
    intro hc
    apply h
    filter_upwards [hc] with j hj
    exact lt_of_not_ge hj
  let l' := l ⊓ 𝓟 E
  have : l'.NeBot := frequently_iff_neBot.1 hf
  have hs : ∀ᶠ j in l', j ∈ E := mem_inf_of_right (mem_principal_self E)
  have hz := referenceResponse_cold_of_small_side s K β (hβ.mono_left (show l' ≤ l from inf_le_left)) hs
  have hh := (hz.eventually_lt_const hr).and (hlevel.filter_mono (show l' ≤ l from inf_le_left))
  obtain ⟨j,hj,hj'⟩ := hh.exists
  exact (not_lt_of_ge hj') hj

end YangMills.ReferenceCalibration.SmallBox
