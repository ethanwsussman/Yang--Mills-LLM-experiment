import YangMills.Construction.Lattice.LatticeIntegralIsEntireAndPositive
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequalityProof
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PartitionFunctionAnalyticity
open PeriodicLattice SeveralComplexVariables TorusMetric GaugeFieldProduct Matrices
section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
theorem norm_cexp_neg_le_exp {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) : ‖Complex.exp (-z)‖ ≤ Real.exp B := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre := Complex.abs_re_le_norm z
  have hneg := neg_le_abs z.re
  simp only [Complex.neg_re]
  linarith
theorem differentiable_integral_cexp_affine {s t : Ω → ℂ} (hs : Continuous s) (ht : Continuous t)
    {B : ℝ} (hB : 0 ≤ B) (hsB : ∀ U, ‖s U‖ ≤ B) (htB : ∀ U, ‖t U‖ ≤ B) :
    Differentiable ℂ fun ζ : ℂ => ∫ U, Complex.exp (-(s U + ζ * t U)) ∂μ := by
  intro ζ₀
  have hF : ∀ ζ : ℂ, Continuous fun U => Complex.exp (-(s U + ζ * t U)) := fun ζ =>
    Complex.continuous_exp.comp ((hs.add (continuous_const.mul ht)).neg)
  have hbd : ∀ (ζ : ℂ) (U : Ω), ‖ζ‖ ≤ ‖ζ₀‖ + 1 →
      ‖s U + ζ * t U‖ ≤ B + (‖ζ₀‖ + 1) * B := by
    intro ζ U hζ
    calc ‖s U + ζ * t U‖ ≤ ‖s U‖ + ‖ζ‖ * ‖t U‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ B + (‖ζ₀‖ + 1) * B := by
          gcongr
          · exact hsB U
          · exact htB U
  have hint : Integrable (fun U => Complex.exp (-(s U + ζ₀ * t U))) μ :=
    Integrable.of_bound (hF ζ₀).aestronglyMeasurable (Real.exp (B + (‖ζ₀‖ + 1) * B))
      (Eventually.of_forall fun U => norm_cexp_neg_le_exp (hbd ζ₀ U (by linarith)))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ)
    (F := fun ζ U => Complex.exp (-(s U + ζ * t U)))
    (F' := fun ζ U => Complex.exp (-(s U + ζ * t U)) * (-(t U)))
    (x₀ := ζ₀) (s := Metric.ball ζ₀ 1) (bound := fun _ => Real.exp (B + (‖ζ₀‖ + 1) * B) * B)
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun ζ => (hF ζ).aestronglyMeasurable) hint
    ((hF ζ₀).mul ht.neg).aestronglyMeasurable
    (Eventually.of_forall fun U ζ hζ => by
      have hζ' : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
        have hdist : ‖ζ - ζ₀‖ < 1 := by simpa [dist_eq_norm] using hζ
        have htri := norm_le_norm_add_norm_sub' ζ ζ₀
        linarith
      rw [norm_mul, norm_neg]
      exact mul_le_mul (norm_cexp_neg_le_exp (hbd ζ U hζ')) (htB U) (norm_nonneg _)
        (Real.exp_pos _).le)
    (integrable_const _)
    (Eventually.of_forall fun U ζ _ => by
      have hd := ((((hasDerivAt_id ζ).mul_const (t U)).const_add (s U)).neg).cexp
      simpa using hd)
  exact hderiv.2.differentiableAt
variable {P : Type*} [Fintype P]
theorem norm_sum_mul_le_two_mul {a : P → Ω → ℂ} (ha : ∀ p U, ‖a p U‖ ≤ 2) (c : P → ℂ) (U : Ω) :
    ‖∑ p, c p * a p U‖ ≤ 2 * ∑ p, ‖c p‖ := by
  calc ‖∑ p, c p * a p U‖ ≤ ∑ p, ‖c p * a p U‖ := norm_sum_le _ _
    _ ≤ ∑ p, ‖c p‖ * 2 := Finset.sum_le_sum fun p _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ha p U) (norm_nonneg _)
    _ = 2 * ∑ p, ‖c p‖ := by rw [← Finset.sum_mul]; ring
theorem continuous_sum_const_mul {a : P → Ω → ℂ} (hc : ∀ p, Continuous (a p)) (c : P → ℂ) :
    Continuous fun U => ∑ p, c p * a p U :=
  continuous_finsetSum _ fun p _ => continuous_const.mul (hc p)
theorem differentiable_integral_cexp_sum_line {a : P → Ω → ℂ} (hc : ∀ p, Continuous (a p))
    (ha : ∀ p U, ‖a p U‖ ≤ 2) (c d : P → ℂ) :
    Differentiable ℂ fun ζ : ℂ => ∫ U, Complex.exp (-∑ p, (c + ζ • d) p * a p U) ∂μ := by
  have hN : ∀ e : P → ℂ, 0 ≤ 2 * ∑ p, ‖e p‖ := fun e =>
    mul_nonneg zero_le_two (Finset.sum_nonneg fun p _ => norm_nonneg _)
  have hline := differentiable_integral_cexp_affine μ (s := fun U => ∑ p, c p * a p U)
    (t := fun U => ∑ p, d p * a p U) (continuous_sum_const_mul hc c)
    (continuous_sum_const_mul hc d) (B := 2 * ∑ p, ‖c p‖ + 2 * ∑ p, ‖d p‖)
    (add_nonneg (hN c) (hN d))
    (fun U => (norm_sum_mul_le_two_mul ha c U).trans (le_add_of_nonneg_right (hN d)))
    (fun U => (norm_sum_mul_le_two_mul ha d U).trans (le_add_of_nonneg_left (hN c)))
  have hsplit : ∀ (ζ : ℂ) (U : Ω), ∑ p, (c + ζ • d) p * a p U =
      ∑ p, c p * a p U + ζ * ∑ p, d p * a p U := by
    intro ζ U
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [hsplit] using hline
theorem continuous_integral_cexp_sum {a : P → Ω → ℂ} (hc : ∀ p, Continuous (a p))
    (ha : ∀ p U, ‖a p U‖ ≤ 2) :
    Continuous fun c : P → ℂ => ∫ U, Complex.exp (-∑ p, c p * a p U) ∂μ := by
  rw [continuous_iff_continuousAt]
  intro c₀
  have hN : Continuous fun c : P → ℂ => ∑ p, ‖c p‖ :=
    continuous_finsetSum _ fun p _ => (continuous_apply p).norm
  have hnear : ∀ᶠ c in 𝓝 c₀, ∑ p, ‖c p‖ < ∑ p, ‖c₀ p‖ + 1 :=
    hN.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  refine continuousAt_of_dominated
    (bound := fun _ => Real.exp (2 * (∑ p, ‖c₀ p‖ + 1))) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun c =>
      (Complex.continuous_exp.comp (continuous_sum_const_mul hc c).neg).aestronglyMeasurable
  · filter_upwards [hnear] with c hc'
    refine Eventually.of_forall fun U => norm_cexp_neg_le_exp ?_
    have := norm_sum_mul_le_two_mul ha c U
    linarith
  · refine Eventually.of_forall fun U => Continuous.continuousAt ?_
    exact Complex.continuous_exp.comp
      ((continuous_finsetSum _ fun p _ => (continuous_apply p).mul continuous_const).neg)
end
section
variable {L m : ℕ} {j : ℤ} [Fintype (Plaquette L m j)]
theorem plaquetteWeightedEnergy_eq_sum (c : Plaquette L m j → ℂ) (U : Bond L m j → ComplexMatrix2) :
    plaquetteWeightedEnergy c U = ∑ p, c p * plaquetteEnergy U p :=
  finsum_eq_sum_of_fintype _
theorem weightL1Norm_eq_sum (c : Plaquette L m j → ℂ) :
    weightL1Norm c = ∑ p, ‖c p‖ :=
  finsum_eq_sum_of_fintype _
theorem partitionFunction_eq_integral (c : Plaquette L m j → ℂ) :
    latticeGaugeIntegral c = ∫ U : CompactGaugeField L m j,
      Complex.exp (-∑ p, c p * plaquetteEnergy U.1 p)
        ∂gaugeFieldMeasure L m j := by
  unfold latticeGaugeIntegral
  simp only [plaquetteWeightedEnergy_eq_sum]
theorem norm_plaquetteEnergy_le_two (hc : PlaquetteEnergyContinuousBounded L m j)
    (p : Plaquette L m j) (U : CompactGaugeField L m j) :
    ‖plaquetteEnergy U.1 p‖ ≤ 2 := by
  obtain ⟨t, ⟨h0, h2⟩, ht⟩ := (hc p).2 U
  rw [← ht, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h2
variable [IsProbabilityMeasure (gaugeFieldMeasure L m j)]
theorem continuous_partitionFunction (hc : PlaquetteEnergyContinuousBounded L m j) :
    Continuous (latticeGaugeIntegral : (Plaquette L m j → ℂ) → ℂ) := by
  have hcont := continuous_integral_cexp_sum (gaugeFieldMeasure L m j)
    (a := fun p U => plaquetteEnergy U.1 p) (fun p => (hc p).1)
    (norm_plaquetteEnergy_le_two hc)
  have heq : (latticeGaugeIntegral : (Plaquette L m j → ℂ) → ℂ) = fun c =>
      ∫ U : CompactGaugeField L m j, Complex.exp (-∑ p, c p * plaquetteEnergy U.1 p)
        ∂gaugeFieldMeasure L m j := funext partitionFunction_eq_integral
  rw [heq]
  exact hcont
theorem differentiable_partitionFunction_line (hc : PlaquetteEnergyContinuousBounded L m j)
    (c d : Plaquette L m j → ℂ) :
    Differentiable ℂ fun ζ : ℂ => latticeGaugeIntegral (c + ζ • d) := by
  have hdiff := differentiable_integral_cexp_sum_line (gaugeFieldMeasure L m j)
    (a := fun p U => plaquetteEnergy U.1 p) (fun p => (hc p).1)
    (norm_plaquetteEnergy_le_two hc) c d
  have heq : (fun ζ : ℂ => latticeGaugeIntegral (c + ζ • d)) = fun ζ : ℂ =>
      ∫ U : CompactGaugeField L m j,
        Complex.exp (-∑ p, (c + ζ • d) p * plaquetteEnergy U.1 p)
        ∂gaugeFieldMeasure L m j := funext fun ζ => partitionFunction_eq_integral _
  rw [heq]
  exact hdiff
theorem isEntire_partitionFunction_comp {I : Type*} (hc : PlaquetteEnergyContinuousBounded L m j)
    (Ψ : (I → ℂ) → Plaquette L m j → ℂ) (hΨ : Continuous Ψ)
    (hlin : ∀ (x y : I → ℂ) (ζ : ℂ), Ψ (x + ζ • y) = Ψ x + ζ • Ψ y) :
    IsEntire fun x => latticeGaugeIntegral (Ψ x) :=
  ⟨isOpen_univ, ((continuous_partitionFunction hc).comp hΨ).continuousOn, fun c _ q =>
    Eventually.of_forall fun ζ => by
      simpa only [hlin] using differentiable_partitionFunction_line hc (Ψ c) (Ψ (basisVector q)) ζ⟩
theorem partitionFunction_real_ge (hc : PlaquetteEnergyContinuousBounded L m j)
    (c : Plaquette L m j → ℂ) (hr : IsRealVector c) :
    ∃ t : ℝ, latticeGaugeIntegral c = t ∧ Real.exp (-2 * weightL1Norm c) ≤ t := by
  set μ := gaugeFieldMeasure L m j
  set ar : Plaquette L m j → CompactGaugeField L m j → ℝ :=
    fun p U => (plaquetteEnergy U.1 p).re with har
  have hareal : ∀ p U, plaquetteEnergy U.1 p = (ar p U : ℂ) := by
    intro p U
    obtain ⟨t, -, ht⟩ := (hc p).2 U
    simp only [har, ← ht, Complex.ofReal_re]
  have habs : ∀ p U, |ar p U| ≤ 2 := by
    intro p U
    refine (Complex.abs_re_le_norm _).trans (norm_plaquetteEnergy_le_two hc p U)
  have hcr : ∀ p, c p = ((c p).re : ℂ) := fun p =>
    Complex.ext (by simp) (by simp [hr p])
  set r : CompactGaugeField L m j → ℝ := fun U => ∑ p, (c p).re * ar p U with hrdef
  have hrc : Continuous r := continuous_finsetSum _ fun p _ =>
    continuous_const.mul (Complex.continuous_re.comp (hc p).1)
  have hrb : ∀ U, |r U| ≤ 2 * ∑ p, ‖c p‖ := by
    intro U
    calc |r U| ≤ ∑ p, |(c p).re * ar p U| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p, ‖c p‖ * 2 := Finset.sum_le_sum fun p _ => by
          rw [abs_mul]
          exact mul_le_mul (Complex.abs_re_le_norm _) (habs p U) (abs_nonneg _) (norm_nonneg _)
      _ = 2 * ∑ p, ‖c p‖ := by rw [← Finset.sum_mul]; ring
  have hint : ∀ U, Complex.exp (-∑ p, c p * plaquetteEnergy U.1 p) =
      ((Real.exp (-r U) : ℝ) : ℂ) := by
    intro U
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
    congr 2
    simp only [hrdef, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hareal p U, ← hcr p]
  have hcont : Continuous fun U => Real.exp (-r U) := Real.continuous_exp.comp hrc.neg
  have hI : Integrable (fun U => Real.exp (-r U)) μ :=
    Integrable.of_bound hcont.aestronglyMeasurable (Real.exp (2 * ∑ p, ‖c p‖))
      (Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((neg_le_abs _).trans (hrb U)))
  refine ⟨∫ U, Real.exp (-r U) ∂μ, ?_, ?_⟩
  · rw [partitionFunction_eq_integral]
    simp only [hint]
    exact integral_complex_ofReal
  · rw [weightL1Norm_eq_sum]
    calc Real.exp (-2 * ∑ p, ‖c p‖) = ∫ _U : CompactGaugeField L m j,
          Real.exp (-2 * ∑ p, ‖c p‖) ∂μ := by simp
      _ ≤ ∫ U, Real.exp (-r U) ∂μ := integral_mono (integrable_const _) hI fun U => by
          have hle := (le_abs_self (r U)).trans (hrb U)
          exact Real.exp_le_exp.mpr (by linarith)
theorem partitionFunction_real_pos (hc : PlaquetteEnergyContinuousBounded L m j)
    (c : Plaquette L m j → ℂ) (hr : IsRealVector c) :
    ∃ t : ℝ, 0 < t ∧ latticeGaugeIntegral c = t := by
  obtain ⟨t, ht, hle⟩ := partitionFunction_real_ge hc c hr
  exact ⟨t, (Real.exp_pos _).trans_le hle, ht⟩
theorem partitionFunction_real_ne_zero (hc : PlaquetteEnergyContinuousBounded L m j)
    (c : Plaquette L m j → ℂ) (hr : IsRealVector c) : latticeGaugeIntegral c ≠ 0 := by
  obtain ⟨t, ht, heq⟩ := partitionFunction_real_pos hc c hr
  rw [heq]
  exact_mod_cast ht.ne'
end
section
variable {L m J : ℕ} [Fintype (Plaquette L m (J : ℤ))]
  [IsProbabilityMeasure (gaugeFieldMeasure L m (J : ℤ))]
theorem sourcedPartitionFunction_eq (β : ℂ) (w : FourTorus L m → ℂ) :
    sourcedPartitionFunction L m J β w =
      latticeGaugeIntegral (fun p : Plaquette L m (J : ℤ) => β - w p.barycenter) :=
  rfl
theorem entireAndBoundedBelow (hc : PlaquetteEnergyContinuousBounded L m (J : ℤ)) :
    PartitionFunctionEntireAndBoundedBelow L m J := by
  refine ⟨isEntire_partitionFunction_comp hc id continuous_id fun _ _ _ => rfl, fun c hr => ?_, ?_, ?_⟩
  · obtain ⟨t, ht, hle⟩ := partitionFunction_real_ge hc c hr
    exact ⟨t, ht, hle, Real.exp_pos _⟩
  · exact isOpen_ne_fun (continuous_partitionFunction hc) continuous_const
  · exact fun c hr => partitionFunction_real_ne_zero hc c hr
theorem barycenterWeightsRepresent : BarycenterWeightsRepresent L m J := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun φ hφ p => hφ _, rfl, fun _ _ => rfl, ?_⟩
  intro β w _
  rw [sourcedPartitionFunction_eq]
  congr 1
  funext p
  simp [constantOneWeights, weightsAtBarycenters]
def sourceCouplings {n : ℕ} (f : Fin n → FourTorus L m → ℝ) (x : Fin 2 ⊕ Fin n → ℂ) :
    Plaquette L m (J : ℤ) → ℂ :=
  fun p => x (.inl 0) - x (.inl 1) - ∑ i, x (.inr i) * (f i p.barycenter : ℂ)
theorem continuous_sourceCouplings {n : ℕ} (f : Fin n → FourTorus L m → ℝ) :
    Continuous (sourceCouplings f : (Fin 2 ⊕ Fin n → ℂ) → Plaquette L m (J : ℤ) → ℂ) := by
  refine continuous_pi fun p => ?_
  unfold sourceCouplings
  fun_prop
theorem sourceCouplings_add_smul {n : ℕ} (f : Fin n → FourTorus L m → ℝ) (x y : Fin 2 ⊕ Fin n → ℂ)
    (ζ : ℂ) :
    (sourceCouplings f (x + ζ • y) : Plaquette L m (J : ℤ) → ℂ) =
      sourceCouplings f x + ζ • sourceCouplings f y := by
  funext p
  have hs : ∑ i, (x (.inr i) + ζ * y (.inr i)) * (f i p.barycenter : ℂ) =
      ∑ i, x (.inr i) * (f i p.barycenter : ℂ) +
        ζ * ∑ i, y (.inr i) * (f i p.barycenter : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [sourceCouplings, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
  ring
theorem sourcedPartitionFunctionInArgs_eq {n : ℕ} (f : Fin n → FourTorus L m → ℝ)
    (x : Fin 2 ⊕ Fin n → ℂ) :
    sourcedPartitionFunctionInArgs L m J f x =
      latticeGaugeIntegral (sourceCouplings f x : Plaquette L m (J : ℤ) → ℂ) := by
  unfold sourcedPartitionFunctionInArgs
  rw [sourcedPartitionFunction_eq]
  congr 1
  funext p
  simp only [sourceCouplings, complexSource]
  ring
theorem sourcedEntireAndPositive (hc : PlaquetteEnergyContinuousBounded L m (J : ℤ)) :
    SourcedEntireAndPositive L m J := by
  intro n _ f _
  constructor
  · have heq : sourcedPartitionFunctionInArgs L m J f = fun x =>
        latticeGaugeIntegral (sourceCouplings f x : Plaquette L m (J : ℤ) → ℂ) :=
      funext (sourcedPartitionFunctionInArgs_eq f)
    rw [heq]
    exact isEntire_partitionFunction_comp hc _ (continuous_sourceCouplings f)
      (sourceCouplings_add_smul f)
  · intro x hx
    have hr : IsRealVector (sourceCouplings f x : Plaquette L m (J : ℤ) → ℂ) := by
      intro p
      simp [sourceCouplings, Complex.sub_im, Complex.im_sum, hx _]
    rw [sourcedPartitionFunctionInArgs_eq]
    exact partitionFunction_real_pos hc _ hr
theorem constantSourceShiftsCoupling : ConstantSourceShiftsCoupling L m J := by
  intro β c w _
  rw [sourcedPartitionFunction_eq, sourcedPartitionFunction_eq]
  congr 1
  funext p
  ring
theorem nonvanishingSetOpenContainsReals (hc : PlaquetteEnergyContinuousBounded L m (J : ℤ)) :
    NonvanishingSetOpenContainsReals L m J := by
  have hZ : ∀ β : ℂ, sourcedPartitionFunction L m J β 0 =
      latticeGaugeIntegral (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) := by
    intro β
    rw [sourcedPartitionFunction_eq]
    congr 1
    funext p
    simp [constantOneWeights]
  have hset : nonvanishingCouplings L m J =
      {β : ℂ | latticeGaugeIntegral (β • constantOneWeights : Plaquette L m (J : ℤ) → ℂ) ≠ 0} := by
    ext β
    simp only [nonvanishingCouplings, Set.mem_ofPred_eq, hZ]
  refine ⟨hset, ?_, fun t => ?_⟩
  · rw [hset]
    exact isOpen_ne_fun ((continuous_partitionFunction hc).comp
      (continuous_id.smul continuous_const)) continuous_const
  · rw [hset]
    refine partitionFunction_real_ne_zero hc _ fun p => ?_
    simp [constantOneWeights]
end
section
theorem torusEuclidNorm_le {S : ℝ} (hS : 0 < S) (y : Torus4 S) :
    torusEuclidNorm y ≤ S := by apply _root_.YangMills.SharedProofs.p53575 <;> assumption
theorem norm_apply_le_torusEuclidNorm {S : ℝ} (y : Torus4 S) (μ : Fin 4) :
    ‖y μ‖ ≤ torusEuclidNorm y := by apply _root_.YangMills.SharedProofs.p28925 <;> assumption
theorem torusEuclidNorm_pos {S : ℝ} {y : Torus4 S} (hy : y ≠ 0) :
    0 < torusEuclidNorm y := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hy
  refine lt_of_lt_of_le ?_ (norm_apply_le_torusEuclidNorm y μ)
  obtain ⟨v, hv, hv'⟩ := exists_coe_eq_abs_eq_norm (y μ)
  refine lt_of_le_of_ne (norm_nonneg _) fun h0 => hμ ?_
  have hv0 : v = 0 := abs_eq_zero.mp (hv'.trans h0.symm)
  rw [← hv, hv0]
  simp
variable {L m : ℕ} {E : Type*} [NormedAddCommGroup E]
theorem div_le_torusLipConst {f : FourTorus L m → E} (hf : torusLipConst f ≠ ⊤) {y y' : FourTorus L m}
    (h : y ≠ y') : ‖f y - f y'‖ / torusEuclidNorm (y - y') ≤ (torusLipConst f).toReal := by
  have hsup : ENNReal.ofReal (‖f y - f y'‖ / torusEuclidNorm (y - y')) ≤ torusLipConst f :=
    le_iSup_of_le y (le_iSup_of_le y' (le_iSup_of_le h le_rfl))
  exact (ENNReal.ofReal_le_iff_le_toReal hf).mp hsup
theorem torusLipConst_ne_top_of_le {f : FourTorus L m → E} (K : ℝ)
    (h : ∀ y y' : FourTorus L m, y ≠ y' → ‖f y - f y'‖ / torusEuclidNorm (y - y') ≤ K) :
    torusLipConst f ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun y => iSup_le fun y' => iSup_le fun hy => ENNReal.ofReal_le_ofReal (h y y' hy))
theorem torusSupNorm_ne_top (hS : 0 < torusSide L m) {f : FourTorus L m → E}
    (hf : torusLipConst f ≠ ⊤) : torusSupNorm f ≠ ⊤ := by
  have hK : 0 ≤ (torusLipConst f).toReal := ENNReal.toReal_nonneg
  have hb : ∀ y, ‖f y‖ ≤ ‖f 0‖ + (torusLipConst f).toReal * torusSide L m := by
    intro y
    by_cases hy : y = 0
    · subst hy
      exact le_add_of_nonneg_right (mul_nonneg hK hS.le)
    · have hpos : 0 < torusEuclidNorm (y - 0) := torusEuclidNorm_pos (by simpa using hy)
      have hlip := div_le_torusLipConst hf hy
      rw [div_le_iff₀ hpos] at hlip
      have hside : torusEuclidNorm (y - 0) ≤ torusSide L m := torusEuclidNorm_le hS _
      have htri := norm_le_norm_add_norm_sub' (f y) (f 0)
      have hmul := mul_le_mul_of_nonneg_left hside hK
      linarith
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (hb y))
theorem complexSource_torusLipConst_ne_top {n : ℕ} {f : Fin n → FourTorus L m → ℝ}
    (hf : ∀ i, torusLipConst (f i) ≠ ⊤) (z : Fin n → ℂ) :
    torusLipConst (complexSource f z) ≠ ⊤ := by
  refine torusLipConst_ne_top_of_le (∑ i, ‖z i‖ * (torusLipConst (f i)).toReal) fun y y' hne => ?_
  have hnn : 0 ≤ torusEuclidNorm (y - y') := (torusEuclidNorm_pos (sub_ne_zero.mpr hne)).le
  have hdiff : complexSource f z y - complexSource f z y' =
      ∑ i, z i * ((f i y - f i y' : ℝ) : ℂ) := by
    simp [complexSource, mul_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  calc ‖∑ i, z i * ((f i y - f i y' : ℝ) : ℂ)‖ / torusEuclidNorm (y - y')
      ≤ (∑ i, ‖z i‖ * ‖f i y - f i y'‖) / torusEuclidNorm (y - y') := by
        refine div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (le_of_eq ?_)) hnn
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_real]
    _ = ∑ i, ‖z i‖ * (‖f i y - f i y'‖ / torusEuclidNorm (y - y')) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => mul_div_assoc _ _ _
    _ ≤ ∑ i, ‖z i‖ * (torusLipConst (f i)).toReal := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (div_le_torusLipConst (hf i) hne) (norm_nonneg _)
theorem torusLipConst_comp_ne_top {g : ℂ → ℝ} (hg : ∀ a b, ‖g a - g b‖ ≤ ‖a - b‖)
    {w : FourTorus L m → ℂ} (hw : torusLipConst w ≠ ⊤) :
    torusLipConst (fun y => g (w y)) ≠ ⊤ :=
  torusLipConst_ne_top_of_le (torusLipConst w).toReal fun _ _ h =>
    (div_le_div_of_nonneg_right (hg _ _) (torusEuclidNorm_pos (sub_ne_zero.mpr h)).le).trans
      (div_le_torusLipConst hw h)
theorem sourcesBoundedAndComplexCombinations (hS : 0 < torusSide L m) :
    SourcesBoundedAndComplexCombinations L m := by
  refine ⟨fun f hf => torusSupNorm_ne_top hS hf, fun f hf => torusSupNorm_ne_top hS hf,
    fun w hw => torusSupNorm_ne_top hS hw, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have hre : torusLipConst (fun y => (w y).re) ≠ ⊤ :=
      torusLipConst_comp_ne_top (g := Complex.re) (fun a b => by
        rw [← Complex.sub_re, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _) hw
    have him : torusLipConst (fun y => (w y).im) ≠ ⊤ :=
      torusLipConst_comp_ne_top (g := Complex.im) (fun a b => by
        rw [← Complex.sub_im, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _) hw
    refine ⟨2, by norm_num, ![fun y => (w y).re, fun y => (w y).im], ?_, ![1, Complex.I], ?_⟩
    · intro i
      fin_cases i
      · exact hre
      · exact him
    · funext y
      simp only [complexSource, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_mul]
      rw [mul_comm Complex.I, Complex.re_add_im]
  · rintro ⟨n, -, f, hf, z, rfl⟩
    exact complexSource_torusLipConst_ne_top hf z
end
open PeriodicLattice SeveralComplexVariables TorusMetric GaugeFieldProduct Matrices
theorem statement_proof (h : GaugeFieldProduct.Statement) : PartitionFunctionAnalyticity.Statement := by
  intro L m J hL hm
  obtain ⟨-, hfin, hconf, hc⟩ := h.1 L m (J : ℤ) hL hm (Int.natCast_nonneg J)
  have : Finite (Plaquette L m (J : ℤ)) := hfin.2.2.1
  let _ : Fintype (Plaquette L m (J : ℤ)) := Fintype.ofFinite _
  have : IsProbabilityMeasure (gaugeFieldMeasure L m (J : ℤ)) := hconf.2.2.2.2.2.2
  have hS : 0 < torusSide L m := by
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    unfold torusSide
    positivity
  exact ⟨entireAndBoundedBelow hc, barycenterWeightsRepresent, sourcedEntireAndPositive hc,
    constantSourceShiftsCoupling, nonvanishingSetOpenContainsReals hc,
    sourcesBoundedAndComplexCombinations hS⟩
end YangMills.Construction.PartitionFunctionAnalyticity
