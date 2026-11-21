import YangMills.Construction.LawByMomentsOfTheFlow.ColdLawOfAGoodStateProof
import YangMills.Construction.ColdChainAtEveryLevel.SumsOverTheEvaluations
import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsKillClosedFormsProof
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOfTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.MeanOverTheFluctuationOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.TreeGaugeOfAChain
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepCosts WeightedResponses RenormalizationStepParameters TopLevelSites ColdStepAtMirrorFrames
  ResponseInTheExpansion
open BlockAverages hiding unitStep
namespace FormMeans
section Closed
variable {n : ℕ} [NeZero n]
private theorem closed_form (A : TorusBond n → ℝ) (hA : ∀ p : TorusPlaquette n, curl A p = 0) :
    ∃ (φ : TorusSite n → ℝ) (v : Fin 4 → ℝ), ∀ b, A b = latticeGradient φ b + constantOneForm v b := by apply _root_.YangMills.SharedProofs.p19533 <;> assumption
private theorem bilinearEval_add_left (q : BondBilinear n) (A A' B : TorusBond n → ℝ) :
    bilinearEval q (fun b => A b + A' b) B = bilinearEval q A B + bilinearEval q A' B := by
  simp only [bilinearEval, add_mul, Finset.sum_add_distrib]
private theorem bilinearEval_add_right (q : BondBilinear n) (A B B' : TorusBond n → ℝ) :
    bilinearEval q A (fun b => B b + B' b) = bilinearEval q A B + bilinearEval q A B' := by
  simp only [bilinearEval, mul_add, Finset.sum_add_distrib]
private theorem bilinearEval_of_curl {q : BondBilinear n} (hq : AnnihilatesClosedForms q) {A A' : TorusBond n → ℝ}
    (h : ∀ p, curl A p = curl A' p) : bilinearEval q A A = bilinearEval q A' A' := by
  obtain ⟨φ, v, hφ⟩ := closed_form (fun b => A b - A' b) (fun p => by
    have := h p
    simp only [curl] at this ⊢
    linarith)
  obtain ⟨g, hg⟩ : ∃ g : TorusBond n → ℝ, g = fun b => latticeGradient φ b + constantOneForm v b := ⟨_, rfl⟩
  have hA : A = fun b => A' b + g b := by
    funext b
    have := hφ b
    rw [hg]
    linarith
  have kl : ∀ B, bilinearEval q g B = 0 := fun B => by
    rw [hg, bilinearEval_add_left, (hq.1 φ B).1, (hq.2 v B).1, add_zero]
  have kr : ∀ B, bilinearEval q B g = 0 := fun B => by
    rw [hg, bilinearEval_add_right, (hq.1 φ B).2, (hq.2 v B).2, add_zero]
  rw [hA, bilinearEval_add_left q A' g, bilinearEval_add_right q A' A' g, kl, kr]
  ring
end Closed
section Growth
variable {E : Type*} [SeminormedAddCommGroup E]
private def PolyGrowth (f : E → ℝ) : Prop := ∃ (K : ℝ) (k : ℕ), 0 ≤ K ∧ ∀ x, |f x| ≤ K * (1 + ‖x‖) ^ k
private theorem one_le_base (x : E) : (1 : ℝ) ≤ 1 + ‖x‖ := by
  have := norm_nonneg x
  linarith
private theorem PolyGrowth.const (c : ℝ) : PolyGrowth (fun _ : E => c) :=
  ⟨|c|, 0, abs_nonneg _, fun x => by simp⟩
private theorem PolyGrowth.add {f g : E → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x + g x) := by
  obtain ⟨K, k, hK, h⟩ := hf
  obtain ⟨K', k', hK', h'⟩ := hg
  refine ⟨K + K', max k k', add_nonneg hK hK', fun x => ?_⟩
  have e1 : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ max k k' := pow_le_pow_right₀ (one_le_base x) (le_max_left _ _)
  have e2 : (1 + ‖x‖) ^ k' ≤ (1 + ‖x‖) ^ max k k' := pow_le_pow_right₀ (one_le_base x) (le_max_right _ _)
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ K * (1 + ‖x‖) ^ k + K' * (1 + ‖x‖) ^ k' := add_le_add (h x) (h' x)
    _ ≤ K * (1 + ‖x‖) ^ max k k' + K' * (1 + ‖x‖) ^ max k k' :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hK) (mul_le_mul_of_nonneg_left e2 hK')
    _ = _ := by ring
private theorem PolyGrowth.mul {f g : E → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x * g x) := by
  obtain ⟨K, k, hK, h⟩ := hf
  obtain ⟨K', k', hK', h'⟩ := hg
  refine ⟨K * K', k + k', mul_nonneg hK hK', fun x => ?_⟩
  rw [abs_mul, pow_add]
  calc |f x| * |g x| ≤ (K * (1 + ‖x‖) ^ k) * (K' * (1 + ‖x‖) ^ k') :=
        mul_le_mul (h x) (h' x) (abs_nonneg _) (mul_nonneg hK (pow_nonneg (by linarith [one_le_base x]) _))
    _ = _ := by ring
private theorem PolyGrowth.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, PolyGrowth (f i)) :
    PolyGrowth (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowth.const (E := E) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
private theorem PolyGrowth.prod {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, PolyGrowth (f i)) :
    PolyGrowth (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowth.const (E := E) 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Growth
section Forms
variable {n : ℕ} [NeZero n]
private theorem coord_growth (e : Fin 3) (b : TorusBond n) : PolyGrowth (fun Z : ColourForm n => Z e b) := by
  refine ⟨1, 1, zero_le_one, fun Z => ?_⟩
  have h1 : ‖Z e b‖ ≤ ‖Z e‖ := norm_le_pi_norm (Z e) b
  have h2 : ‖Z e‖ ≤ ‖Z‖ := norm_le_pi_norm Z e
  have : |Z e b| = ‖Z e b‖ := rfl
  rw [this, pow_one, one_mul]
  linarith
private theorem colourEval_growth (q : BondBilinear n) : PolyGrowth (fun Z : ColourForm n => colourEval q Z Z) := by
  unfold colourEval bilinearEval
  refine PolyGrowth.sum _ fun e _ => PolyGrowth.sum _ fun b _ => PolyGrowth.sum _ fun b' _ => ?_
  exact ((coord_growth e b).mul (PolyGrowth.const _)).mul (coord_growth e b')
end Forms
section Steps
variable (a ρA : ℝ) (L : ℕ) [NeZero L]
private def pushLin (u : ℕ) (n : ℕ) [NeZero n] : ColourForm n →ₗ[ℝ] ColourForm (n * L) where
  toFun := pushColours a ρA L u
  map_add' X Y := by
    funext e b
    simp [pushColours, responseMap, mul_add, Finset.sum_add_distrib]
  map_smul' r X := by
    funext e b
    simp only [pushColours, responseMap, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
variable {L}
private def extendLin (u : ℕ) (n : ℕ) [NeZero n] : StepFluctuation L u n →ₗ[ℝ] ColourForm (n * L) where
  toFun := extendFluctuation
  map_add' X Y := by
    funext e b
    simp only [extendFluctuation, extendChart, Pi.add_apply, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
  map_smul' r X := by
    funext e b
    simp only [extendFluctuation, extendChart, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
variable (L)
private theorem exists_bound_lin {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ₗ[ℝ] F) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖f x‖ ≤ K * ‖x‖ :=
  ⟨‖f.toContinuousLinearMap‖, norm_nonneg _, fun x => f.toContinuousLinearMap.le_opNorm x⟩
variable (t : ℕ)
private def sampleNorm : (d n : ℕ) → FluctuationSample L t d n → ℝ
  | 0, _, _ => 0
  | d + 1, n, w => ‖w.1‖ + sampleNorm d (n * L) w.2
private theorem sampleNorm_nonneg : ∀ (d n : ℕ) (w : FluctuationSample L t d n), 0 ≤ sampleNorm L t d n w
  | 0, _, _ => le_rfl
  | d + 1, n, w => add_nonneg (norm_nonneg _) (sampleNorm_nonneg d (n * L) w.2)
private theorem measurable_sampleNorm : ∀ (d n : ℕ), Measurable (sampleNorm L t d n)
  | 0, _ => measurable_const
  | d + 1, n => by
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    exact (measurable_fst.norm).add ((measurable_sampleNorm d (n * L)).comp measurable_snd)
private instance fluctuationGaussian_prob (x : ℝ) (u n : ℕ) : IsProbabilityMeasure (fluctuationGaussian a L x u n) := by
  unfold fluctuationGaussian
  infer_instance
private instance fluctuationSampleLaw_prob : ∀ (d n : ℕ), IsProbabilityMeasure (fluctuationSampleLaw a L t d n)
  | 0, _ => Measure.dirac.isProbabilityMeasure
  | d + 1, n => by
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    haveI := fluctuationSampleLaw_prob d (n * L)
    exact Measure.prod.instIsProbabilityMeasure _ _
private theorem integrable_gauss_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (Sg : Matrix ι ι ℝ) (k : ℕ) :
    Integrable (fun η : EuclideanSpace ℝ ι => (1 + ‖η‖) ^ k) (multivariateGaussian 0 Sg) := by
  by_cases hk : k = 0
  · subst hk
    simp
  have h0 : MemLp (fun η : EuclideanSpace ℝ ι => η) (k : ℕ) (multivariateGaussian 0 Sg) :=
    IsGaussian.memLp_id _ _ (by simp)
  have h3 : MemLp (fun η : EuclideanSpace ℝ ι => ‖η‖) (k : ℕ) (multivariateGaussian 0 Sg) := h0.norm
  have h4 : MemLp (fun η : EuclideanSpace ℝ ι => (1 : ℝ)) (k : ℕ) (multivariateGaussian 0 Sg) := memLp_const 1
  have h1 := h4.add h3
  refine (h1.integrable_norm_pow hk).congr (Filter.Eventually.of_forall fun η => ?_)
  show ‖(1 : ℝ) + ‖η‖‖ ^ k = (1 + ‖η‖) ^ k
  exact (by
    have : (0 : ℝ) ≤ 1 + ‖η‖ := by positivity
    rw [Real.norm_of_nonneg this])
private theorem integrable_fluct_pow (x : ℝ) (u n k : ℕ) :
    Integrable (fun η : StepFluctuation L u n => (1 + ‖η‖) ^ k) (fluctuationGaussian a L x u n) := by
  unfold fluctuationGaussian
  exact integrable_gauss_pow _ k
private theorem integrable_sample_pow (k : ℕ) : ∀ (d n : ℕ),
    Integrable (fun w => (1 + sampleNorm L t d n w) ^ k) (fluctuationSampleLaw a L t d n)
  | 0, _ => by
    simp only [sampleNorm, add_zero, one_pow]
    exact integrable_const _
  | d + 1, n => by
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    haveI := fluctuationSampleLaw_prob a L t d (n * L)
    have h1 := integrable_fluct_pow a L 1 (t + d) n k
    have h2 := integrable_sample_pow k d (n * L)
    have h3 := h1.mul_prod h2
    refine h3.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (((measurable_const.add (measurable_sampleNorm L t (d + 1) n)).pow_const k)).aestronglyMeasurable
    · have e0 := sampleNorm_nonneg L t d (n * L) w.2
      have e1 := norm_nonneg w.1
      have e2 : (0 : ℝ) ≤ 1 + sampleNorm L t (d + 1) n w := by
        have := sampleNorm_nonneg L t (d + 1) n w
        linarith
      rw [Real.norm_of_nonneg (pow_nonneg e2 _), ← mul_pow]
      refine pow_le_pow_left₀ e2 ?_ k
      simp only [sampleNorm]
      nlinarith [mul_nonneg e1 e0]
variable {L}
private abbrev FormFamily : Type := ∀ (m : ℕ) [NeZero m], ColourForm m → ℝ
private theorem descendWithNoise_bound (c : ℝ) : ∀ (d n : ℕ) [NeZero n], ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ColourForm n) (w : FluctuationSample L t d n),
    ‖descendWithNoise a ρA t c d n A w‖ ≤ K * (‖A‖ + sampleNorm L t d n w)
  | 0, n, _ => ⟨1, zero_le_one, fun A w => by
      simp only [descendWithNoise, sampleNorm, add_zero, one_mul]
      exact le_rfl⟩
  | d + 1, n, _ => by
    obtain ⟨K, hK, h⟩ := descendWithNoise_bound c d (n * L)
    obtain ⟨Km, hKm, hm⟩ := exists_bound_lin (pushLin a ρA L (t + d) n)
    obtain ⟨Kn, hKn, hn⟩ := exists_bound_lin (extendLin (L := L) (t + d) n)
    refine ⟨K * (Km + |c| * Kn + 1), by positivity, fun A w => ?_⟩
    have e := h (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b) w.2
    have e1 : ‖(fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b : ColourForm (n * L))‖ ≤
        Km * ‖A‖ + |c| * (Kn * ‖w.1‖) := by
      have : (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b : ColourForm (n * L)) =
          pushLin a ρA L (t + d) n A + c • extendLin (L := L) (t + d) n w.1 := rfl
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add (hm A) ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hn _) (abs_nonneg _)
    have e2 := sampleNorm_nonneg L t d (n * L) w.2
    have e3 := norm_nonneg w.1
    have e4 := norm_nonneg A
    simp only [descendWithNoise, sampleNorm]
    refine e.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK
    have e5 : |c| * (Kn * ‖w.1‖) = (|c| * Kn) * ‖w.1‖ := by ring
    have e6 : 0 ≤ |c| * Kn := by positivity
    nlinarith [mul_nonneg hKm e3, mul_nonneg e6 e4, mul_nonneg hKm e2, mul_nonneg e6 e2, mul_nonneg hKm e4, mul_nonneg e6 e3]
private theorem measurable_descendWithNoise (c : ℝ) : ∀ (d n : ℕ) [NeZero n],
    Measurable (fun p : ColourForm n × FluctuationSample L t d n => descendWithNoise a ρA t c d n p.1 p.2)
  | 0, n, _ => measurable_fst
  | d + 1, n, _ => by
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    have hM : Measurable (pushLin a ρA L (t + d) n) :=
      (pushLin a ρA L (t + d) n).continuous_of_finiteDimensional.measurable
    have hN : Measurable (extendLin (L := L) (t + d) n) :=
      (extendLin (L := L) (t + d) n).continuous_of_finiteDimensional.measurable
    have h1 : Measurable (fun p : ColourForm n × (StepFluctuation L (t + d) n × FluctuationSample L t d (n * L)) =>
        ((pushLin a ρA L (t + d) n p.1 + c • extendLin (L := L) (t + d) n p.2.1 : ColourForm (n * L)), p.2.2)) :=
      ((hM.comp measurable_fst).add ((hN.comp (measurable_fst.comp measurable_snd)).const_smul c)).prodMk
        (measurable_snd.comp measurable_snd)
    exact (measurable_descendWithNoise c d (n * L)).comp h1
private def meanOf (L : ℕ) [NeZero L] (c : ℝ) (G : FormFamily) (d n : ℕ) [NeZero n] (A : ColourForm n) : ℝ :=
  ∫ w, G (fineSide L d n) (descendWithNoise a ρA t c d n A w) ∂(fluctuationSampleLaw a L t d n)
variable {a ρA t}
section Family
variable (c : ℝ) (G : FormFamily) (hGm : ∀ (m : ℕ) [NeZero m], Measurable (G m))
  (hGg : ∀ (m : ℕ) [NeZero m], PolyGrowth (G m))
include hGg in
private theorem bound_along (d n : ℕ) [NeZero n] : ∃ (K : ℝ) (k : ℕ), 0 ≤ K ∧ ∀ (A : ColourForm n) (w : FluctuationSample L t d n),
    |G (fineSide L d n) (descendWithNoise a ρA t c d n A w)| ≤ K * ((1 + ‖A‖) ^ k * (1 + sampleNorm L t d n w) ^ k) := by
  obtain ⟨Kf, hKf, hf⟩ := descendWithNoise_bound (L := L) a ρA t c d n
  obtain ⟨K, k, hK, hg⟩ := hGg (fineSide L d n)
  refine ⟨K * (1 + Kf) ^ k, k, by positivity, fun A w => ?_⟩
  have e0 := sampleNorm_nonneg L t d n w
  have e1 := norm_nonneg A
  have e2 := hf A w
  refine (hg _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  rw [← mul_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  nlinarith [mul_nonneg e1 e0, mul_nonneg hKf (mul_nonneg e1 e0), mul_nonneg hKf e1, mul_nonneg hKf e0]
include hGm hGg in
private theorem integrable_along (d n : ℕ) [NeZero n] (A : ColourForm n) :
    Integrable (fun w => G (fineSide L d n) (descendWithNoise a ρA t c d n A w)) (fluctuationSampleLaw a L t d n) := by
  obtain ⟨K, k, hK, h⟩ := bound_along (L := L) (t := t) (a := a) (ρA := ρA) c G hGg d n
  have hm : Measurable (fun w => G (fineSide L d n) (descendWithNoise a ρA t c d n A w)) :=
    (hGm _).comp ((measurable_descendWithNoise (L := L) a ρA t c d n).comp measurable_prodMk_left)
  refine Integrable.mono' (((integrable_sample_pow a L t k d n).const_mul ((1 + ‖A‖) ^ k)).const_mul K)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => h A w)
include hGm hGg in
private theorem meanOf_succ (d n : ℕ) [NeZero n] (A : ColourForm n) :
    meanOf a ρA t L c G (d + 1) n A = ∫ η, meanOf a ρA t L c G d (n * L)
      (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation η e b)
      ∂(fluctuationGaussian a L 1 (t + d) n) := by
  letI := instMeasurableSpaceFluctuationSample L t d (n * L)
  haveI := fluctuationSampleLaw_prob a L t d (n * L)
  have hint := integrable_along (L := L) (a := a) (ρA := ρA) (t := t) c G hGm hGg (d + 1) n A
  exact integral_prod (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) => G (fineSide L (d + 1) n) (descendWithNoise a ρA t c (d + 1) n A w)) hint
end Family
end Steps
section Rotations
open scoped RealInnerProductSpace
variable {κ : Type} [Fintype κ]
private def pair (Bm : κ → κ → ℝ) (u v : κ → ℝ) : ℝ := ∑ b, ∑ b', u b * Bm b b' * v b'
private theorem pair_sum_left (Bm : κ → κ → ℝ) (r : Fin 3 → ℝ) (x : Fin 3 → κ → ℝ) (v : κ → ℝ) :
    pair Bm (fun b => ∑ i, r i * x i b) v = ∑ i, r i * pair Bm (x i) v := by
  simp only [pair, Fin.sum_univ_three, add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
private theorem pair_sum_right (Bm : κ → κ → ℝ) (r : Fin 3 → ℝ) (x : Fin 3 → κ → ℝ) (u : κ → ℝ) :
    pair Bm u (fun b => ∑ i, r i * x i b) = ∑ i, r i * pair Bm u (x i) := by
  simp only [pair, Fin.sum_univ_three, add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1 <;> exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  · exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
private theorem pair_rot (Bm : κ → κ → ℝ) {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin 3 → κ → ℝ) :
    ∑ e, pair Bm (fun b => ∑ i, R e i * x i b) (fun b => ∑ i, R e i * x i b) = ∑ e, pair Bm (x e) (x e) := by
  have hRR : R.transpose * R = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hR
    simpa [Matrix.star_eq_conjTranspose] using this
  have hent : ∀ i j, ∑ e, R e i * R e j = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun hRR i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have h1 : ∀ e, pair Bm (fun b => ∑ i, R e i * x i b) (fun b => ∑ i, R e i * x i b) =
      ∑ i, ∑ j, R e i * (R e j * pair Bm (x i) (x j)) := fun e => by
    rw [pair_sum_left Bm (R e) x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair_sum_right Bm (R e) x, Finset.mul_sum]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j, ∑ e, R e i * (R e j * pair Bm (x i) (x j)) = (if i = j then 1 else 0) * pair Bm (x i) (x j) := fun j => by
    rw [← hent i j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp only [this]
  simp
variable [DecidableEq (Fin 3 × κ)]
private def rotE (R : Matrix (Fin 3) (Fin 3) ℝ) : EuclideanSpace ℝ (Fin 3 × κ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 × κ) where
  toFun v := WithLp.toLp 2 fun i => ∑ e', R i.1 e' * v (e', i.2)
  map_add' x y := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
@[simp] private theorem rotE_apply (R : Matrix (Fin 3) (Fin 3) ℝ) (v : EuclideanSpace ℝ (Fin 3 × κ)) (e : Fin 3) (b : κ) :
    rotE R v (e, b) = ∑ e', R e e' * v (e', b) := rfl
private theorem inner_rotE (R : Matrix (Fin 3) (Fin 3) ℝ) (v x : EuclideanSpace ℝ (Fin 3 × κ)) :
    ⟪rotE R v, x⟫ = ⟪v, rotE R.transpose x⟫ := by
  have key : ∀ u w : EuclideanSpace ℝ (Fin 3 × κ), ⟪u, w⟫ = ∑ b, ∑ e, u (e, b) * w (e, b) := fun u w => by
    rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
    simp [mul_comm]
  rw [key, key]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [rotE_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring
private theorem gauss_rot (Sg : Matrix (Fin 3 × κ) (Fin 3 × κ) ℝ) (σ : κ → κ → ℝ)
    (hS : ∀ e e' b b', Sg (e, b) (e', b') = if e = e' then σ b b' else 0)
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R.transpose ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    (multivariateGaussian 0 Sg).map (rotE R) = multivariateGaussian 0 Sg := by
  have hc : Continuous (rotE (κ := κ) R) := (rotE R).continuous_of_finiteDimensional
  by_cases hp : Sg.PosSemidef
  · refine Measure.ext_of_charFun ?_
    funext x
    have hq : ∀ y : EuclideanSpace ℝ (Fin 3 × κ), y ⬝ᵥ Sg.mulVec y =
        ∑ e, pair σ (fun b => y (e, b)) (fun b => y (e, b)) := fun y => by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, hS, pair, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have h2 : ∀ z, (∑ w, if e = z then y (e, b) * (σ b w * y (z, w)) else 0) =
          if e = z then ∑ w, y (e, b) * (σ b w * y (z, w)) else 0 := fun z => by
        split_ifs <;> simp
      simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [charFun_apply, integral_map hc.measurable.aemeasurable (by fun_prop)]
    simp only [inner_rotE]
    rw [← charFun_apply, charFun_multivariateGaussian hp, charFun_multivariateGaussian hp, hq, hq]
    have h3 := pair_rot σ hR (fun i b => x (i, b))
    have h4 : (∑ e, pair σ (fun b => (rotE R.transpose x) (e, b)) fun b => (rotE R.transpose x) (e, b)) =
        ∑ e, pair σ (fun b => x (e, b)) fun b => x (e, b) := h3
    rw [h4]
    simp
  · rw [multivariateGaussian_of_not_posSemidef _ hp, Measure.map_dirac' hc.measurable]
    simp
end Rotations
section Means
variable {a ρA : ℝ} {L : ℕ} [NeZero L] {t : ℕ}
private def rotF {m : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ) (A : ColourForm m) : ColourForm m := fun e b => ∑ e', R e e' * A e' b
private theorem meanOf_zero (c : ℝ) (G : FormFamily) (n : ℕ) [NeZero n] (A : ColourForm n) :
    meanOf a ρA t L c G 0 n A = G n A :=
  integral_dirac (α := Unit) (fun w => G n A) ()
private theorem push_rot (R : Matrix (Fin 3) (Fin 3) ℝ) (u : ℕ) {n : ℕ} [NeZero n] (A : ColourForm n) :
    pushColours a ρA L u (rotF R A) = rotF R (pushColours a ρA L u A) := by
  funext e b
  simp only [pushColours, rotF, responseMap, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring
private theorem extend_rot (R : Matrix (Fin 3) (Fin 3) ℝ) {u n : ℕ} [NeZero n] (η : StepFluctuation L u n) (e : Fin 3) (b : TorusBond (n * L)) :
    extendFluctuation (rotE R η) e b = ∑ e', R e e' * extendFluctuation η e' b := by
  simp only [extendFluctuation, extendChart, rotE_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
section Family
variable (c : ℝ) (G : FormFamily) (hGm : ∀ (m : ℕ) [NeZero m], Measurable (G m))
  (hGg : ∀ (m : ℕ) [NeZero m], PolyGrowth (G m))
include hGm in
private theorem measurable_meanOf (d n : ℕ) [NeZero n] : Measurable (meanOf a ρA t L c G d n) := by
  have h : Measurable (fun p : ColourForm n × FluctuationSample L t d n => G (fineSide L d n) (descendWithNoise a ρA t c d n p.1 p.2)) :=
    (hGm _).comp (measurable_descendWithNoise (L := L) a ρA t c d n)
  haveI := fluctuationSampleLaw_prob a L t d n
  exact (h.stronglyMeasurable.integral_prod_right' (ν := fluctuationSampleLaw a L t d n)).measurable
include hGm hGg in
private theorem growth_meanOf (d n : ℕ) [NeZero n] : PolyGrowth (meanOf a ρA t L c G d n) := by
  obtain ⟨K, k, hK, h⟩ := bound_along (L := L) (t := t) (a := a) (ρA := ρA) c G hGg d n
  haveI := fluctuationSampleLaw_prob a L t d n
  have hI := integrable_sample_pow a L t k d n
  refine ⟨K * ∫ w, (1 + sampleNorm L t d n w) ^ k ∂(fluctuationSampleLaw a L t d n), k, ?_, fun A => ?_⟩
  · refine mul_nonneg hK (integral_nonneg fun w => ?_)
    have := sampleNorm_nonneg L t d n w
    positivity
  · have e : |meanOf a ρA t L c G d n A| ≤ ∫ w, K * ((1 + ‖A‖) ^ k * (1 + sampleNorm L t d n w) ^ k) ∂(fluctuationSampleLaw a L t d n) := by
      have := norm_integral_le_of_norm_le (μ := fluctuationSampleLaw a L t d n)
        (f := fun w => G (fineSide L d n) (descendWithNoise a ρA t c d n A w)) ((hI.const_mul ((1 + ‖A‖) ^ k)).const_mul K)
        (Filter.Eventually.of_forall fun w => h A w)
      exact this
    rw [integral_const_mul, integral_const_mul] at e
    calc _ ≤ _ := e
      _ = _ := by ring
include hGm hGg in
private theorem meanOf_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hG : ∀ (m : ℕ) [NeZero m] (Z : ColourForm m), G m (rotF R Z) = G m Z) :
    ∀ (d n : ℕ) [NeZero n] (A : ColourForm n), meanOf a ρA t L c G d n (rotF R A) = meanOf a ρA t L c G d n A
  | 0, n, _, A => by rw [meanOf_zero, meanOf_zero, hG]
  | d + 1, n, _, A => by
    have ih := meanOf_rot hR hG d (n * L)
    rw [meanOf_succ c G hGm hGg, meanOf_succ c G hGm hGg]
    have hRt : R.transpose ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      have := Unitary.star_mem hR
      simpa [Matrix.star_eq_conjTranspose] using this
    have hlaw : (fluctuationGaussian a L 1 (t + d) n).map (rotE R) = fluctuationGaussian a L 1 (t + d) n := by
      unfold fluctuationGaussian
      refine gauss_rot _ (fun b b' => (1 : ℝ)⁻¹ * (trivialHessian a L (t + d) n)⁻¹ b b') (fun e e' b b' => ?_) hRt
      simp [fluctuationCov]
    have hc : Measurable (rotE (κ := ChartBondIndex L (t + d) n) R) := (rotE R).continuous_of_finiteDimensional.measurable
    have hf : Measurable (fun η : StepFluctuation L (t + d) n => meanOf a ρA t L c G d (n * L)
        (fun e b => pushColours a ρA L (t + d) (rotF R A) e b + c * extendFluctuation η e b)) := by
      refine (measurable_meanOf c G hGm d (n * L)).comp ?_
      have hN : Measurable (extendLin (L := L) (t + d) n) :=
        (extendLin (L := L) (t + d) n).continuous_of_finiteDimensional.measurable
      exact (measurable_const.add (hN.const_smul c))
    conv_lhs => rw [← hlaw]
    rw [integral_map hc.aemeasurable hf.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show meanOf a ρA t L c G d (n * L) _ = meanOf a ρA t L c G d (n * L) _
    rw [← ih (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation η e b)]
    congr 1
    funext e b
    rw [push_rot, extend_rot]
    simp only [rotF, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
include hGm hGg in
private theorem meanOf_curl {n₀ : ℕ} (hL : 1 ≤ L)
    (hM : ∀ (u m : ℕ) [NeZero m], n₀ ≤ m → ∀ A A' : TorusBond m → ℝ, (∀ p, curl A p = curl A' p) → ∀ p,
      curl (responseMap a ρA L u A) p = curl (responseMap a ρA L u A') p)
    (hG : ∀ (m : ℕ) [NeZero m], n₀ ≤ m → ∀ A A' : ColourForm m, (∀ e p, curl (A e) p = curl (A' e) p) → G m A = G m A') :
    ∀ (d n : ℕ) [NeZero n], n₀ ≤ n → ∀ A A' : ColourForm n, (∀ e p, curl (A e) p = curl (A' e) p) →
      meanOf a ρA t L c G d n A = meanOf a ρA t L c G d n A'
  | 0, n, _, hn, A, A', h => by rw [meanOf_zero, meanOf_zero, hG n hn A A' h]
  | d + 1, n, _, hn, A, A', h => by
    rw [meanOf_succ c G hGm hGg, meanOf_succ c G hGm hGg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    refine meanOf_curl hL hM hG d (n * L) (hn.trans (Nat.le_mul_of_pos_right n hL)) _ _ fun e p => ?_
    have := hM (t + d) n hn (A e) (A' e) (h e) p
    simp only [curl, pushColours] at this ⊢
    linarith
end Family
end Means
section Curl
variable {n : ℕ} [NeZero n]
private theorem curlNorm_eq (X : ColourForm n) (p : TorusPlaquette n) :
    curlNorm X p = ‖(WithLp.toLp 2 fun e => curl (X e) p : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [curlNorm]
private theorem curlNorm_add_le (X Y : ColourForm n) (p : TorusPlaquette n) : curlNorm (X + Y) p ≤ curlNorm X p + curlNorm Y p := by apply _root_.YangMills.SharedProofs.p71255 <;> assumption
private theorem continuous_curl (p : TorusPlaquette n) : Continuous (fun A : TorusBond n → ℝ => curl A p) := by
  unfold curl
  fun_prop
private theorem continuous_curlNorm (p : TorusPlaquette n) : Continuous (fun X : ColourForm n => curlNorm X p) := by apply _root_.YangMills.SharedProofs.p29578 <;> assumption
private theorem curlNorm_le (X : ColourForm n) (p : TorusPlaquette n) : curlNorm X p ≤ ∑ e, |curl (X e) p| := by apply _root_.YangMills.SharedProofs.p49135 <;> assumption
variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
private theorem weightedCurvatureNorm_le_of {μ : Measure Ω} {q : ENNReal} {X : Ω → ColourForm n} {v : ENNReal}
    (h : ∀ p : OrientedPlaquette n, eLpNorm (fun e => curlNorm (X e) p.1) q μ ≤ v) :
    weightedCurvatureNorm μ (fun _ => 1) q X ≤ v := by
  refine iSup_le fun p => ?_
  simpa using h p
private theorem eLp_le_weightedCurvatureNorm (μ : Measure Ω) (q : ENNReal) (X : Ω → ColourForm n) (p : OrientedPlaquette n) :
    eLpNorm (fun e => curlNorm (X e) p.1) q μ ≤ weightedCurvatureNorm μ (fun _ => 1) q X := by
  have := le_iSup (fun p : OrientedPlaquette n => ENNReal.ofReal (((fun _ => 1) : TorusPlaquette n → ℝ) p.1) *
    eLpNorm (fun e => curlNorm (X e) p.1) q μ) p
  simpa [weightedCurvatureNorm] using this
private theorem weightedCurvatureNorm_add {μ : Measure Ω} {q : ENNReal} (hq : 1 ≤ q) {X Y : Ω → ColourForm n}
    (hX : Measurable X) (hY : Measurable Y) :
    weightedCurvatureNorm μ (fun _ => 1) q (fun w => X w + Y w) ≤
      weightedCurvatureNorm μ (fun _ => 1) q X + weightedCurvatureNorm μ (fun _ => 1) q Y := by
  refine weightedCurvatureNorm_le_of fun p => ?_
  have hx : Measurable (fun w => curlNorm (X w) p.1) := (continuous_curlNorm p.1).measurable.comp hX
  have hy : Measurable (fun w => curlNorm (Y w) p.1) := (continuous_curlNorm p.1).measurable.comp hY
  calc eLpNorm (fun w => curlNorm (X w + Y w) p.1) q μ
      ≤ eLpNorm (fun w => curlNorm (X w) p.1 + curlNorm (Y w) p.1) q μ := by
        refine eLpNorm_mono_real fun w => ?_
        have e0 : 0 ≤ curlNorm (X w + Y w) p.1 := Real.sqrt_nonneg _
        rw [Real.norm_of_nonneg e0]
        exact curlNorm_add_le _ _ _
    _ ≤ eLpNorm (fun w => curlNorm (X w) p.1) q μ + eLpNorm (fun w => curlNorm (Y w) p.1) q μ :=
        eLpNorm_add_le hx.aestronglyMeasurable hy.aestronglyMeasurable hq
    _ ≤ _ := add_le_add (eLp_le_weightedCurvatureNorm μ q X p) (eLp_le_weightedCurvatureNorm μ q Y p)
private theorem weightedCurvatureNorm_comp {μ : Measure Ω} {ν : Measure Ω'} {T : Ω' → Ω} (hT : MeasurePreserving T ν μ)
    (q : ENNReal) {X : Ω → ColourForm n} (hX : Measurable X) :
    weightedCurvatureNorm ν (fun _ => 1) q (fun w => X (T w)) = weightedCurvatureNorm μ (fun _ => 1) q X := by
  unfold weightedCurvatureNorm
  refine iSup_congr fun p => ?_
  have hx : Measurable (fun w => curlNorm (X w) p.1) := (continuous_curlNorm p.1).measurable.comp hX
  congr 1
  exact eLpNorm_comp_measurePreserving hx.aestronglyMeasurable hT
end Curl
section Gauss
private theorem gauss_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {Sg : Matrix ι ι ℝ} (hp : Sg.PosSemidef) (i : ι) (q : ENNReal) :
    eLpNorm (fun η : EuclideanSpace ℝ ι => η i) q (multivariateGaussian 0 Sg) =
      ENNReal.ofReal (Real.sqrt (Sg i i)) * eLpNorm id q (gaussianReal 0 1) := by apply _root_.YangMills.SharedProofs.p91446 <;> assumption
private theorem quad_block {κ : Type} [Fintype κ] [DecidableEq (Fin 3 × κ)] (Sg : Matrix (Fin 3 × κ) (Fin 3 × κ) ℝ) (σ : κ → κ → ℝ)
    (hS : ∀ e e' b b', Sg (e, b) (e', b') = if e = e' then σ b b' else 0) (y : Fin 3 × κ → ℝ) :
    y ⬝ᵥ Sg.mulVec y = ∑ e, pair σ (fun b => y (e, b)) (fun b => y (e, b)) := by apply _root_.YangMills.DeltaSharedProofs.p502266 <;> assumption
variable {a : ℝ} {L : ℕ} [NeZero L]
open Classical in
private theorem covariance_psd {u n : ℕ} (hH : (trivialHessian a L u n).PosDef) :
    (fluctuationCov a L 1 u n).PosSemidef := by apply _root_.YangMills.SharedProofs.p20571 <;> assumption
end Gauss
section Noise
private theorem curlNorm_zero {m : ℕ} [NeZero m] (p : TorusPlaquette m) : curlNorm (0 : ColourForm m) p = 0 := by
  simp [curlNorm, curl]
variable {a ρA : ℝ} {L : ℕ} [NeZero L] {t : ℕ}
private theorem descend_add : ∀ (d n : ℕ) [NeZero n] (X Y : ColourForm n),
    descend (L := L) a ρA t d n (X + Y) = descend a ρA t d n X + descend a ρA t d n Y
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, X, Y => by
    have h : pushColours a ρA L (t + d) (X + Y) = pushColours a ρA L (t + d) X + pushColours a ρA L (t + d) Y :=
      map_add (pushLin a ρA L (t + d) n) X Y
    simp only [descend]
    rw [h, descend_add]
    rfl
private theorem pushColours_zero (u : ℕ) {n : ℕ} [NeZero n] : pushColours a ρA L u (0 : ColourForm n) = 0 :=
  map_zero (pushLin a ρA L u n)
private theorem measurable_descend : ∀ (d n : ℕ) [NeZero n], Measurable (descend (L := L) a ρA t d n)
  | 0, _, _ => measurable_id
  | d + 1, n, _ => (measurable_descend d (n * L)).comp
      (pushLin a ρA L (t + d) n).continuous_of_finiteDimensional.measurable
private theorem descendWithNoise_split (c : ℝ) : ∀ (d n : ℕ) [NeZero n] (A : ColourForm n) (w : FluctuationSample L t d n),
    descendWithNoise a ρA t c d n A w = descend a ρA t d n A + descendWithNoise a ρA t c d n 0 w
  | 0, _, _, A, w => (add_zero A).symm
  | d + 1, n, _, A, w => by
    simp only [descendWithNoise, descend]
    have h1 : (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b : ColourForm (n * L)) =
        pushColours a ρA L (t + d) A + c • extendFluctuation w.1 := rfl
    have h2 : (fun e b => pushColours a ρA L (t + d) 0 e b + c * extendFluctuation w.1 e b : ColourForm (n * L)) =
        c • extendFluctuation w.1 := by
      rw [pushColours_zero]
      funext e b
      simp
    rw [h1, h2, descendWithNoise_split c d (n * L) _ w.2, descendWithNoise_split c d (n * L) (c • extendFluctuation w.1) w.2,
      descend_add]
    abel
variable {q : ENNReal} {θ : ℝ}
private theorem curvature_descend (hθ : 0 ≤ θ)
    (hC : ∀ (u m : ℕ) [NeZero m], 64 ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm m), Measurable X →
      weightedCurvatureNorm μ (fun _ => 1) q (fun w => pushColours a ρA L u (X w)) ≤
        ENNReal.ofReal θ * weightedCurvatureNorm μ (fun _ => 1) q X) (hL : 1 ≤ L) :
    ∀ (d n : ℕ) [NeZero n], 64 ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n), Measurable X →
      weightedCurvatureNorm μ (fun _ => 1) q (fun w => descend (L := L) a ρA t d n (X w)) ≤
        ENNReal.ofReal θ ^ d * weightedCurvatureNorm μ (fun _ => 1) q X
  | 0, n, _, hn, Ω, _, μ, X, hX => by
    simp only [pow_zero, one_mul]
    exact le_rfl
  | d + 1, n, _, hn, Ω, _, μ, X, hX => by
    have h1 : weightedCurvatureNorm μ (fun _ => 1) q (fun w => descend a ρA t d (n * L) (pushColours a ρA L (t + d) (X w))) ≤
        ENNReal.ofReal θ ^ d * weightedCurvatureNorm μ (fun _ => 1) q (fun w => pushColours a ρA L (t + d) (X w)) :=
      curvature_descend hθ hC hL d (n * L) (hn.trans (Nat.le_mul_of_pos_right n hL)) Ω μ _
        ((pushLin a ρA L (t + d) n).continuous_of_finiteDimensional.measurable.comp hX)
    refine h1.trans ?_
    rw [pow_succ, mul_assoc]
    exact mul_le_mul_right (hC (t + d) n hn Ω μ X hX) _
private theorem noise_bound (hq : 1 ≤ q) {Nq : ℝ} {n₀ : ℕ} (hθ : 0 ≤ θ) (hNq : 0 ≤ Nq) (hn₀ : 64 ≤ n₀) (hL : 1 ≤ L)
    (hC : ∀ (u m : ℕ) [NeZero m], 64 ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm m), Measurable X →
      weightedCurvatureNorm μ (fun _ => 1) q (fun w => pushColours a ρA L u (X w)) ≤
        ENNReal.ofReal θ * weightedCurvatureNorm μ (fun _ => 1) q X)
    (hN : ∀ (u m : ℕ) [NeZero m], n₀ ≤ m →
      weightedCurvatureNorm (fluctuationGaussian a L 1 u m) (fun _ => 1) q extendFluctuation ≤ ENNReal.ofReal Nq) :
    ∀ (d n : ℕ) [NeZero n], n₀ ≤ n →
      weightedCurvatureNorm (fluctuationSampleLaw a L t d n) (fun _ => 1) q (descendWithNoise a ρA t 1 d n 0) ≤
        ENNReal.ofReal (Nq * ∑ j ∈ Finset.range d, θ ^ j)
  | 0, n, _, hn => by
    refine weightedCurvatureNorm_le_of fun p => ?_
    have : (fun e => curlNorm (descendWithNoise a ρA t 1 0 n (0 : ColourForm n) e) p.1) = 0 := by
      funext e
      exact curlNorm_zero _
    rw [this]
    simp
  | d + 1, n, _, hn => by
    letI := instMeasurableSpaceFluctuationSample L t d (n * L)
    haveI := fluctuationSampleLaw_prob a L t d (n * L)
    have hn' : n₀ ≤ n * L := hn.trans (Nat.le_mul_of_pos_right n hL)
    have ih := noise_bound hq hθ hNq hn₀ hL hC hN d (n * L) hn'
    have hsplit : (descendWithNoise a ρA t 1 (d + 1) n 0 : FluctuationSample L t (d + 1) n → _) =
        fun w => descend a ρA t d (n * L) (extendFluctuation w.1) + descendWithNoise a ρA t 1 d (n * L) 0 w.2 := by
      funext w
      simp only [descendWithNoise]
      rw [pushColours_zero, descendWithNoise_split 1 d (n * L) _ w.2]
      congr 2
      funext e b
      simp
    have hm1 : Measurable (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) =>
        descend (L := L) a ρA t d (n * L) (extendFluctuation w.1)) :=
      (measurable_descend (L := L) (t := t) (a := a) (ρA := ρA) d (n * L)).comp
        ((extendLin (L := L) (t + d) n).continuous_of_finiteDimensional.measurable.comp measurable_fst)
    have hm0 : Measurable (descendWithNoise (L := L) a ρA t 1 d (n * L) (0 : ColourForm (n * L))) :=
      (measurable_descendWithNoise (L := L) a ρA t 1 d (n * L)).comp measurable_prodMk_left
    have hm2 : Measurable (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) =>
        descendWithNoise a ρA t 1 d (n * L) (0 : ColourForm (n * L)) w.2) := hm0.comp measurable_snd
    have hpf : MeasurePreserving (Prod.fst : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) → _)
        ((fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L))) (fluctuationGaussian a L 1 (t + d) n) :=
      measurePreserving_fst
    have hps : MeasurePreserving (Prod.snd : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) → _)
        ((fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L))) (fluctuationSampleLaw a L t d (n * L)) :=
      measurePreserving_snd
    have hml : Measurable (fun η : StepFluctuation L (t + d) n => descend (L := L) a ρA t d (n * L) (extendFluctuation η)) :=
      (measurable_descend (L := L) (t := t) (a := a) (ρA := ρA) d (n * L)).comp
        ((extendLin (L := L) (t + d) n).continuous_of_finiteDimensional.measurable)
    have h1 := weightedCurvatureNorm_add (μ := (fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L))) hq hm1 hm2
    have h2 := weightedCurvatureNorm_comp hpf q hml
    have h3 := weightedCurvatureNorm_comp hps q hm0
    have h4 : weightedCurvatureNorm (fluctuationGaussian a L 1 (t + d) n) (fun _ => 1) q
        (fun η => descend (L := L) a ρA t d (n * L) (extendFluctuation η)) ≤
        ENNReal.ofReal θ ^ d * weightedCurvatureNorm (fluctuationGaussian a L 1 (t + d) n) (fun _ => 1) q extendFluctuation :=
      curvature_descend hθ hC hL d (n * L) (hn₀.trans hn') _ _ _
        ((extendLin (L := L) (t + d) n).continuous_of_finiteDimensional.measurable)
    have h5 := hN (t + d) n hn
    rw [hsplit]
    refine h1.trans ?_
    rw [h2, h3]
    refine (add_le_add (h4.trans (mul_le_mul_right h5 _)) ih).trans ?_
    have hsum : 0 ≤ ∑ j ∈ Finset.range d, θ ^ j := Finset.sum_nonneg fun j _ => pow_nonneg hθ j
    rw [Finset.sum_range_succ, ← ENNReal.ofReal_pow hθ, ← ENNReal.ofReal_mul (pow_nonneg hθ d),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
end Noise
section Extend
variable {a : ℝ} {L : ℕ} [NeZero L] {u m : ℕ} [NeZero m]
private theorem extend_read (e : Fin 3) (c : TorusBond (m * L)) :
    (∀ η : StepFluctuation L u m, extendFluctuation η e c = 0) ∨
      ∃ b : ChartBondIndex L u m, ∀ η : StepFluctuation L u m, extendFluctuation η e c = η (e, b) := by apply _root_.YangMills.SharedProofs.p34049 <;> assumption
private theorem extend_bound {q : ENNReal} (hq : 1 ≤ q) {V : ℝ} (hV : 0 ≤ V)
    (h : ∀ i, eLpNorm (fun η : StepFluctuation L u m => η i) q (fluctuationGaussian a L 1 u m) ≤ ENNReal.ofReal V) :
    weightedCurvatureNorm (fluctuationGaussian a L 1 u m) (fun _ => 1) q extendFluctuation ≤ ENNReal.ofReal (12 * V) := by
  refine weightedCurvatureNorm_le_of fun p => ?_
  have hb : ∀ e c, eLpNorm (fun η : StepFluctuation L u m => extendFluctuation η e c) q (fluctuationGaussian a L 1 u m) ≤
      ENNReal.ofReal V := fun e c => by
    rcases extend_read (u := u) e c with h0 | ⟨b, h1⟩
    · have : (fun η : StepFluctuation L u m => extendFluctuation η e c) = 0 := funext h0
      rw [this]
      simp
    · have : (fun η : StepFluctuation L u m => extendFluctuation η e c) = fun η => η (e, b) := funext h1
      rw [this]
      exact h _
  have hm : ∀ e c, AEStronglyMeasurable (fun η : StepFluctuation L u m => extendFluctuation η e c) (fluctuationGaussian a L 1 u m) :=
    fun e c => by
      have h1 : Measurable (extendLin (L := L) u m) := (extendLin (L := L) u m).continuous_of_finiteDimensional.measurable
      have h2 : Measurable (fun Z : ColourForm (m * L) => Z e c) := (measurable_pi_apply c).comp (measurable_pi_apply e)
      exact (h2.comp h1).aestronglyMeasurable
  have hE : ∀ e, eLpNorm (fun η : StepFluctuation L u m => curl (extendFluctuation η e) p.1) q (fluctuationGaussian a L 1 u m) ≤
      4 * ENNReal.ofReal V := fun e => by
    obtain ⟨x, i, j⟩ := p.1
    have e0 : (fun η : StepFluctuation L u m => curl (extendFluctuation η e) (x, i, j)) =
        (((fun η : StepFluctuation L u m => extendFluctuation η e (x, i)) + (fun η => extendFluctuation η e (x + unitStep (m * L) i, j))) -
          (fun η => extendFluctuation η e (x + unitStep (m * L) j, i))) - (fun η => extendFluctuation η e (x, j)) := rfl
    rw [e0]
    have s1 := eLpNorm_sub_le (((hm e (x, i)).add (hm e (x + unitStep (m * L) i, j))).sub (hm e (x + unitStep (m * L) j, i))) (hm e (x, j)) hq
    have s2 := eLpNorm_sub_le ((hm e (x, i)).add (hm e (x + unitStep (m * L) i, j))) (hm e (x + unitStep (m * L) j, i)) hq
    have s3 := eLpNorm_add_le (hm e (x, i)) (hm e (x + unitStep (m * L) i, j)) hq
    refine s1.trans ((add_le_add (s2.trans (add_le_add s3 (hb _ _))) (hb _ _)).trans ?_)
    refine (add_le_add (add_le_add (add_le_add (hb _ _) (hb _ _)) le_rfl) le_rfl).trans ?_
    exact le_of_eq (by ring)
  have hmc : ∀ e, AEStronglyMeasurable (fun η : StepFluctuation L u m => curl (extendFluctuation η e) p.1) (fluctuationGaussian a L 1 u m) :=
    fun e => by
      have h1 : Measurable (extendLin (L := L) u m) := (extendLin (L := L) u m).continuous_of_finiteDimensional.measurable
      have h2 : Measurable (fun Z : ColourForm (m * L) => curl (Z e) p.1) :=
        (continuous_curl p.1).measurable.comp (measurable_pi_apply e)
      exact (h2.comp h1).aestronglyMeasurable
  calc eLpNorm (fun η : StepFluctuation L u m => curlNorm (extendFluctuation η) p.1) q (fluctuationGaussian a L 1 u m)
      ≤ eLpNorm ((((fun η : StepFluctuation L u m => |curl (extendFluctuation η 0) p.1|) +
          fun η => |curl (extendFluctuation η 1) p.1|) + fun η => |curl (extendFluctuation η 2) p.1|)) q (fluctuationGaussian a L 1 u m) := by
        refine eLpNorm_mono_real fun η => ?_
        have e0 : 0 ≤ curlNorm (extendFluctuation η) p.1 := Real.sqrt_nonneg _
        rw [Real.norm_of_nonneg e0]
        have := curlNorm_le (extendFluctuation η) p.1
        rw [Fin.sum_univ_three] at this
        exact this
    _ ≤ _ := by
        have ha : ∀ e, eLpNorm (fun η : StepFluctuation L u m => |curl (extendFluctuation η e) p.1|) q (fluctuationGaussian a L 1 u m) ≤
            4 * ENNReal.ofReal V := fun e => by
          have := eLpNorm_norm (p := q) (μ := fluctuationGaussian a L 1 u m)
            (fun η : StepFluctuation L u m => curl (extendFluctuation η e) p.1)
          exact (le_of_eq this).trans (hE e)
        have hma : ∀ e, AEStronglyMeasurable (fun η : StepFluctuation L u m => |curl (extendFluctuation η e) p.1|) (fluctuationGaussian a L 1 u m) :=
          fun e => (hmc e).norm
        have s1 := eLpNorm_add_le ((hma 0).add (hma 1)) (hma 2) hq
        have s2 := eLpNorm_add_le (hma 0) (hma 1) hq
        refine s1.trans ((add_le_add (s2.trans (add_le_add (ha 0) (ha 1))) (ha 2)).trans ?_)
        rw [ENNReal.ofReal_mul (by norm_num)]
        have : ENNReal.ofReal 12 = 12 := by norm_num
        rw [this]
        exact le_of_eq (by ring)
end Extend
section Chart
open scoped RealInnerProductSpace
variable {a : ℝ} {L : ℕ} [NeZero L] {u m : ℕ} [NeZero m]
private abbrev frameBond (L u m : ℕ) (c : TorusBond (m * L)) : (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4 :=
  (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2)
private theorem frameBond_inj (c c' : TorusBond (m * L)) (h : frameBond L u m c = frameBond L u m c') : c = c' := by
  have hp : ∀ i, (torusFrame L u m).period (torusFrame L u m).depth i = m * L := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have e := congrArg (toTorusSite (m * L)) h1
  simp only [frameBond] at e
  rw [toTorusSite_torusSiteInFrame hp, toTorusSite_torusSiteInFrame hp] at e
  exact Prod.ext e h2
private theorem mem_chord_of (hodd : Odd L) (h2 : 2 ≤ m) {c : TorusBond (m * L)} (hc : c ∈ chartBonds L m) :
    frameBond L u m c ∈ chordBonds (finiteCells (torusFrame L u m)) := by
  classical
  have hs : ¬ IsAxialTreeBond (F := stepBlockFrame L m) (torusSiteInFrame (stepBlockFrame L m) 0 c.1, c.2) := by
    simpa [chartBonds] using hc
  haveI : NeZero (m * (stepBlockFrame L m).blockSide) := inferInstanceAs (NeZero (m * L))
  haveI : NeZero (m * (torusFrame L u m).blockSide) := inferInstanceAs (NeZero (m * L))
  have t1 := isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L m) (fun _ => rfl) hodd h2 c.1 c.2
  have t2 := isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u m) (fun _ => rfl) hodd h2 c.1 c.2
  have hnt : ¬ IsAxialTreeBond (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2) := fun h =>
    hs (t1.2 (t2.1 h))
  have := mem_chordBonds_of_parentBlock (F := torusFrame L u m) (S := Finset.univ) (fun _ => rfl) hodd h2 c.1 c.2 hnt
    (Finset.mem_univ _) (Finset.mem_univ _)
  rwa [cellsOfSites_univ (fun _ => rfl)] at this
private theorem extend_coords (hodd : Odd L) (h2 : 2 ≤ m) (X : ColourForm (m * L)) (hX : ∀ e, ∀ b ∉ chartBonds L m, X e b = 0) :
    extendFluctuation (WithLp.toLp 2 fun i => chartValues (u := u) X i.1 i.2 : StepFluctuation L u m) = X := by
  classical
  funext e c
  have hread : ∀ b : ChartBondIndex L u m, frameBond L u m c = b.1 → chartValues (u := u) X e b = X e c := fun b hb => by
    simp only [chartValues]
    rw [Finset.sum_eq_single c]
    · rw [if_pos hb]
    · intro c' _ hne
      rw [if_neg]
      intro h'
      exact hne (frameBond_inj c' c (h'.trans hb.symm))
    · simp
  simp only [extendFluctuation, extendChart]
  by_cases hc : c ∈ chartBonds L m
  · have hmem := mem_chord_of (u := u) hodd h2 hc
    rw [Finset.sum_eq_single (⟨frameBond L u m c, hmem⟩ : ChartBondIndex L u m)]
    · rw [if_pos rfl]
      exact hread _ rfl
    · intro b _ hne
      rw [if_neg]
      intro h'
      exact hne (Subtype.ext h'.symm)
    · simp
  · rw [hX e c hc]
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · rw [← hX e c hc]
      exact hread b hb
    · rfl
open Classical in
private theorem law_of_coords {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hH : (trivialHessian a L u m).PosDef) (W : Ω → Fin 3 → ChartBondIndex L u m → ℝ) (hW : Measurable W)
    (hlaw : ∀ co : Fin 3 → ChartBondIndex L u m → ℝ, μ.map (fun x => ∑ e : Fin 3, ∑ b, co e b * W x e b) =
      gaussianReal 0 (∑ e : Fin 3, co e ⬝ᵥ ((trivialHessian a L u m)⁻¹.mulVec (co e))).toNNReal) :
    μ.map (fun x => (WithLp.toLp 2 fun i => W x i.1 i.2 : StepFluctuation L u m)) = fluctuationGaussian a L 1 u m := by
  have hT : Measurable (fun x => (WithLp.toLp 2 fun i => W x i.1 i.2 : StepFluctuation L u m)) := by
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun i => ?_)
    exact (measurable_pi_apply i.2).comp ((measurable_pi_apply i.1).comp hW)
  refine Measure.ext_of_charFun ?_
  funext y
  have hf : Measurable (fun x => ∑ e : Fin 3, ∑ b, y (e, b) * W x e b) :=
    Finset.measurable_sum _ fun e _ => Finset.measurable_sum _ fun b _ =>
      ((measurable_pi_apply b).comp ((measurable_pi_apply e).comp hW)).const_mul _
  have hin : ∀ x, ⟪(WithLp.toLp 2 fun i => W x i.1 i.2 : StepFluctuation L u m), y⟫ = ∑ e : Fin 3, ∑ b, y (e, b) * W x e b := fun x => by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => ?_
    simp
  have hv := hlaw (fun e b => y (e, b))
  rw [charFun_apply, integral_map hT.aemeasurable (by fun_prop)]
  simp only [hin]
  have e1 : ∫ x, Complex.exp (((∑ e : Fin 3, ∑ b, y (e, b) * W x e b : ℝ) : ℂ) * Complex.I) ∂μ =
      ∫ r : ℝ, Complex.exp ((r : ℂ) * Complex.I) ∂(μ.map fun x => ∑ e : Fin 3, ∑ b, y (e, b) * W x e b) :=
    (integral_map (f := fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I)) hf.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))).symm
  rw [e1, hv]
  have hq : ∑ e : Fin 3, (fun b => y (e, b)) ⬝ᵥ ((trivialHessian a L u m)⁻¹.mulVec (fun b => y (e, b))) =
      y ⬝ᵥ (fluctuationCov a L 1 u m).mulVec y := by
    rw [quad_block (κ := ChartBondIndex L u m) (fluctuationCov a L 1 u m)
      (fun b b' => (1 : ℝ)⁻¹ * (trivialHessian a L u m)⁻¹ b b') (fun e e' b b' => by simp [fluctuationCov]) y]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [pair, dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  have hp := covariance_psd (a := a) (L := L) (u := u) (n := m) hH
  have hn : 0 ≤ y ⬝ᵥ (fluctuationCov a L 1 u m).mulVec y := by
    have := hp.dotProduct_mulVec_nonneg y
    rwa [star_trivial] at this
  have e2 := charFun_gaussianReal (μ := 0) (v := (y ⬝ᵥ (fluctuationCov a L 1 u m).mulVec y).toNNReal) 1
  rw [charFun_apply_real] at e2
  simp only [Complex.ofReal_one, one_mul] at e2
  rw [hq, e2]
  unfold fluctuationGaussian
  rw [charFun_multivariateGaussian hp]
  simp [Real.coe_toNNReal _ hn]
end Chart
section Freeze
variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
private theorem freeze {B W : Type} [MeasurableSpace B] [MeasurableSpace W] {ψ : Ω → B} (hψ : Measurable ψ)
    {D : Ω → W} (hD : Measurable D) (hI : IndepFun ψ D μ) {f : B × W → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => f (ψ x, D x)) μ) {T : Set B} (hT : MeasurableSet T) :
    ∫ x in ψ ⁻¹' T, f (ψ x, D x) ∂μ = ∫ x in ψ ⁻¹' T, ∫ z, f (ψ x, z) ∂(μ.map D) ∂μ := by
  classical
  have hmap : μ.map (fun x => (ψ x, D x)) = (μ.map ψ).prod (μ.map D) :=
    (indepFun_iff_map_prod_eq_prod_map_map hψ.aemeasurable hD.aemeasurable).1 hI
  haveI : IsProbabilityMeasure (μ.map ψ) := Measure.isProbabilityMeasure_map hψ.aemeasurable
  haveI : IsProbabilityMeasure (μ.map D) := Measure.isProbabilityMeasure_map hD.aemeasurable
  have hpair : Measurable (fun x => (ψ x, D x)) := hψ.prodMk hD
  let g : B × W → ℝ := fun p => T.indicator (fun _ => (1 : ℝ)) p.1 * f p
  have hg : Measurable g := ((measurable_const.indicator hT).comp measurable_fst).mul hf
  have hS : MeasurableSet (ψ ⁻¹' T) := hψ hT
  have hgx : ∀ x, g (ψ x, D x) = (ψ ⁻¹' T).indicator (fun x => f (ψ x, D x)) x := fun x => by
    by_cases h : ψ x ∈ T
    · simp [g, h]
    · simp [g, h]
  have hgi : Integrable (fun x => g (ψ x, D x)) μ := by
    simp only [hgx]
    exact hint.indicator hS
  have hgp : Integrable g ((μ.map ψ).prod (μ.map D)) := by
    rw [← hmap]
    exact (integrable_map_measure hg.aestronglyMeasurable hpair.aemeasurable).2 hgi
  have hin : Measurable (fun b => ∫ z, g (b, z) ∂(μ.map D)) :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := μ.map D)).measurable
  calc ∫ x in ψ ⁻¹' T, f (ψ x, D x) ∂μ = ∫ x, g (ψ x, D x) ∂μ := by
        simp only [hgx]
        exact (integral_indicator hS).symm
    _ = ∫ p, g p ∂(μ.map fun x => (ψ x, D x)) := (integral_map hpair.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ b, ∫ z, g (b, z) ∂(μ.map D) ∂(μ.map ψ) := by
        rw [hmap]
        exact integral_prod g hgp
    _ = ∫ x, ∫ z, g (ψ x, z) ∂(μ.map D) ∂μ := integral_map hψ.aemeasurable hin.aestronglyMeasurable
    _ = ∫ x in ψ ⁻¹' T, ∫ z, f (ψ x, z) ∂(μ.map D) ∂μ := by
        rw [← integral_indicator hS]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases h : ψ x ∈ T
        · simp [g, h]
        · simp [g, h]
end Freeze
section Inverse
private theorem exists_rangeInverse {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] (f : E →ₗ[ℝ] F) :
    ∃ g : F →ₗ[ℝ] E, ∀ x, f (g (f x)) = f x := by
  obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := LinearMap.exists_extend r
  refine ⟨g, fun x => ?_⟩
  have h1 : g (f x) = r (f.rangeRestrict x) := by
    have := LinearMap.congr_fun hg (f.rangeRestrict x)
    simpa using this
  rw [h1]
  have h2 := LinearMap.congr_fun hr (f.rangeRestrict x)
  have h3 := congrArg Subtype.val h2
  simpa using h3
end Inverse
section Down
variable {L : ℕ} [NeZero L]
private theorem lower_heq {s s' n : ℕ} (h : s = s') {X : LevelChain L (s + 1) n} {X' : LevelChain L (s' + 1) n}
    (hX : HEq X X') : HEq (chainLower X) (chainLower X') := by
  subst h
  cases hX
  rfl
private theorem lower_descend_heq (s : ℕ) : ∀ (D n : ℕ) (X : LevelChain L (s + 1 + D) n) (X' : LevelChain L (s + (D + 1)) n),
    HEq X X' → HEq (chainLower (chainDescend (s + 1) D n X)) (chainDescend s (D + 1) n X')
  | 0, n, X, X', h => by
    have e : X = X' := eq_of_heq h
    subst e
    exact HEq.rfl
  | D + 1, n, X, X', h =>
    lower_descend_heq s D (n * L) (chainLower X) (chainLower X') (lower_heq (by omega) h)
private def IsDown {K top : ℕ} (D : ℕ) {s m : ℕ} (X : LevelChain L K top) (Z : LevelChain L s m) : Prop :=
  ∃ (h : s + D = K) (_ : fineSide L D top = m), HEq Z (chainDescend s D top (h.symm ▸ X : LevelChain L (s + D) top))
variable {K top : ℕ} {X : LevelChain L K top}
private theorem IsDown.zero (X : LevelChain L K top) : IsDown 0 X X := ⟨rfl, rfl, HEq.rfl⟩
private theorem fineSide_succ' (D n : ℕ) : fineSide L (D + 1) n = fineSide L D n * L := by
  rw [fineSide_eq, fineSide_eq, pow_succ, mul_assoc]
private theorem heq_tr {a b top : ℕ} (h : b = a) (X : LevelChain L b top) : HEq X (h ▸ X : LevelChain L a top) := by
  subst h
  rfl
private theorem IsDown.below {D s m : ℕ} {Z : LevelChain L (s + 1) m} (h : IsDown D X Z) : IsDown (D + 1) X (chainLower Z) := by
  obtain ⟨h1, h2, h3⟩ := h
  subst h1
  subst h2
  have e : Z = chainDescend (s + 1) D top X := eq_of_heq h3
  subst e
  have h' : s + (D + 1) = s + 1 + D := by omega
  exact ⟨h', fineSide_succ' D top, lower_descend_heq s D top X _ (heq_tr _ X)⟩
private theorem IsDown.down {s : ℕ} : ∀ (j D m : ℕ) {Z : LevelChain L (s + j) m}, IsDown D X Z →
    IsDown (D + j) X (chainDescend s j m Z)
  | 0, D, m, Z, h => h
  | j + 1, D, m, Z, h => by
    have h1 := IsDown.down j (D + 1) (m * L) (IsDown.below h)
    have e : D + 1 + j = D + (j + 1) := by omega
    exact e ▸ h1
private theorem IsDown.unique {D s m m' : ℕ} {Z : LevelChain L s m} {Z' : LevelChain L s m'} (h : IsDown D X Z)
    (h' : IsDown D X Z') : m = m' ∧ HEq Z Z' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  exact ⟨h2.symm.trans h2', h3.trans h3'.symm⟩
end Down
section Lin
variable (L : ℕ) [NeZero L]
private def topLin : (s m : ℕ) → LevelChain L s m →ₗ[ℝ] ColourForm m
  | 0, _ => LinearMap.id
  | _ + 1, _ => { toFun := chainTop _ _, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
@[simp] private theorem topLin_apply (s m : ℕ) (X : LevelChain L s m) : topLin L s m X = chainTop s m X := by
  cases s <;> rfl
private def lowerLin (s m : ℕ) : LevelChain L (s + 1) m →ₗ[ℝ] LevelChain L s (m * L) where
  toFun := chainLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def descendLin (s : ℕ) : (d n : ℕ) → LevelChain L (s + d) n →ₗ[ℝ] LevelChain L s (fineSide L d n)
  | 0, _ => LinearMap.id
  | d + 1, n => (descendLin s d (n * L)).comp (lowerLin L (s + d) n)
private theorem descendLin_apply (s : ℕ) : ∀ (d n : ℕ) (X : LevelChain L (s + d) n), descendLin L s d n X = chainDescend s d n X
  | 0, _, _ => rfl
  | d + 1, n, X => descendLin_apply s d (n * L) (chainLower X)
variable {L}
private def curlV (m : ℕ) : ColourForm m →ₗ[ℝ] (Fin 3 → TorusPlaquette m → ℝ) where
  toFun A := fun e p => curl (A e) p
  map_add' A B := by
    funext e p
    simp only [curl, Pi.add_apply]
    ring
  map_smul' r A := by
    funext e p
    simp only [curl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
@[simp] private theorem curlV_apply (m : ℕ) (A : ColourForm m) (e : Fin 3) (p : TorusPlaquette m) : curlV m A e p = curl (A e) p := rfl
variable (L)
private theorem finite_levelBond : ∀ (s n : ℕ) [NeZero n], Finite (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Finite (TorusBond n))
  | s + 1, n, _ => by
    haveI := finite_levelBond s (n * L)
    exact inferInstanceAs (Finite (LevelBond L s (n * L) ⊕ TorusBond n))
end Lin
section Canonical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {En : V → ℝ} {μ : Measure V}
private theorem integrable_isGaussian_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [IsGaussian ν] (k : ℕ) :
    Integrable (fun η : E => (1 + ‖η‖) ^ k) ν := by
  by_cases hk : k = 0
  · subst hk
    simp
  have h0 : MemLp (fun η : E => η) (k : ℕ) ν := IsGaussian.memLp_id _ _ (by simp)
  have h3 : MemLp (fun η : E => ‖η‖) (k : ℕ) ν := h0.norm
  have h4 : MemLp (fun η : E => (1 : ℝ)) (k : ℕ) ν := memLp_const 1
  have h1 := h4.add h3
  refine (h1.integrable_norm_pow hk).congr (Filter.Eventually.of_forall fun η => ?_)
  show ‖(1 : ℝ) + ‖η‖‖ ^ k = (1 + ‖η‖) ^ k
  have : (0 : ℝ) ≤ 1 + ‖η‖ := by positivity
  rw [Real.norm_of_nonneg this]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem gauss_of_lin (hc : IsCanonicalGaussian En μ) (W : V →ₗ[ℝ] E) (hW : ∀ x, En x = 0 → W x = 0) :
    HasGaussianLaw W μ := by
  haveI := hc.isProbabilityMeasure
  have hWm : Measurable W := W.continuous_of_finiteDimensional.measurable
  refine ⟨isGaussian_of_map_eq_gaussianReal fun Lf => ?_⟩
  let f : V →ₗ[ℝ] ℝ := Lf.toLinearMap.comp W
  refine ⟨0, (gaussianVariance En f).toNNReal, ?_⟩
  rw [Measure.map_map Lf.continuous.measurable hWm]
  exact hc.map_eq f fun x hx => by simp [f, hW x hx]
private theorem moments_of_lin (hc : IsCanonicalGaussian En μ) (W : V →ₗ[ℝ] E) (hW : ∀ x, En x = 0 → W x = 0) (k : ℕ) :
    Integrable (fun x => (1 + ‖W x‖) ^ k) μ := by
  haveI := (gauss_of_lin hc W hW).isGaussian_map
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hWm : Measurable W := W.continuous_of_finiteDimensional.measurable
  have h := integrable_isGaussian_pow (μ.map W) k
  exact (integrable_map_measure (by fun_prop) hWm.aemeasurable).1 h
private theorem indep_of_cov {ι κ : Type} [Fintype ι] [Fintype κ] (hc : IsCanonicalGaussian En μ)
    (X : ι → V →ₗ[ℝ] ℝ) (Y : κ → V →ₗ[ℝ] ℝ) (hX : ∀ i x, En x = 0 → X i x = 0) (hY : ∀ j x, En x = 0 → Y j x = 0)
    (h : ∀ i j, cov[X i, Y j; μ] = 0) :
    IndepFun (fun x i => X i x) (fun x j => Y j x) μ := by
  let W : V →ₗ[ℝ] (ι → ℝ) × (κ → ℝ) := (LinearMap.pi X).prod (LinearMap.pi Y)
  have hW : ∀ x, En x = 0 → W x = 0 := fun x hx => by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · exact hX i x hx
    · exact hY j x hx
  exact HasGaussianLaw.indepFun_of_covariance_eval (gauss_of_lin hc W hW) h
end Canonical
section Tower
private theorem PolyGrowth.comp_lin {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : PolyGrowth f) (T : E →ₗ[ℝ] F) : PolyGrowth (fun x => f (T x)) := by
  obtain ⟨K, k, hK, h⟩ := hf
  obtain ⟨Kt, hKt, ht⟩ := exists_bound_lin T
  refine ⟨K * (1 + Kt) ^ k, k, by positivity, fun x => (h _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) hK
  nlinarith [ht x, norm_nonneg x, mul_nonneg hKt (norm_nonneg x)]
variable {a ρA : ℝ} {L : ℕ} [NeZero L] {top K : ℕ}
private def Down (D : ℕ) {s m : ℕ} (Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m) : Prop := ∀ x, IsDown D x (Z x)
private def topCurl {s m : ℕ} (Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m) :
    LevelChain L K top →ₗ[ℝ] (Fin 3 → TorusPlaquette m → ℝ) := (curlV m).comp ((topLin L s m).comp Z)
private def coordOf {m : ℕ} (W : LevelChain L K top →ₗ[ℝ] (Fin 3 → TorusPlaquette m → ℝ)) (c : Fin 3) (p : TorusPlaquette m) :
    LevelChain L K top →ₗ[ℝ] ℝ := (LinearMap.proj p).comp ((LinearMap.proj c).comp W)
@[simp] private theorem coordOf_apply {m : ℕ} (W : LevelChain L K top →ₗ[ℝ] (Fin 3 → TorusPlaquette m → ℝ)) (c : Fin 3) (p : TorusPlaquette m) (x) :
    coordOf W c p x = W x c p := rfl
private def stepLin (a ρA : ℝ) (u m : ℕ) [NeZero m] : LevelChain L (u + 1) m →ₗ[ℝ] ColourForm (m * L) :=
  ((topLin L u (m * L)).comp (lowerLin L u m)) - (pushLin a ρA L u m).comp (topLin L (u + 1) m)
private theorem stepLin_apply (u m : ℕ) [NeZero m] (X : LevelChain L (u + 1) m) : stepLin a ρA u m X = stepDefect a ρA u m X := by
  funext e b
  simp [stepLin, stepDefect, pushLin, lowerLin, topLin_apply]
  rfl
private structure Facts (a ρA : ℝ) (L top K : ℕ) [NeZero L] [NeZero top] [Fintype (LevelBond L K top)] (μ : Measure (LevelChain L K top)) (n₀ : ℕ) : Prop where
  canon : IsCanonicalGaussian (levelEnergy a K top) μ
  side : ∀ {D s m : ℕ} {Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m}, Down D Z → n₀ ≤ m
  ker : ∀ {D s m : ℕ} {Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m}, Down D Z → ∀ x, levelEnergy a K top x = 0 → topCurl Z x = 0
  resp : ∀ (u m : ℕ) [NeZero m], n₀ ≤ m → ∀ A A' : TorusBond m → ℝ, (∀ p, curl A p = curl A' p) → ∀ p,
    curl (responseMap a ρA L u A) p = curl (responseMap a ρA L u A') p
  law : ∀ {D u m : ℕ} [NeZero m] {Z : LevelChain L K top →ₗ[ℝ] LevelChain L (u + 1) m}, Down D Z →
    μ.map (fun x => curlV (m * L) (stepDefect a ρA u m (Z x))) =
      (fluctuationGaussian a L 1 u m).map (fun η => curlV (m * L) (extendFluctuation η))
  indep : ∀ {D D' u m s m' : ℕ} [NeZero m] {Z : LevelChain L K top →ₗ[ℝ] LevelChain L (u + 1) m}
    {Z' : LevelChain L K top →ₗ[ℝ] LevelChain L s m'}, Down D Z → Down D' Z' → D' ≤ D →
    IndepFun (fun x => curlV (m * L) (stepDefect a ρA u m (Z x))) (fun x => topCurl Z' x) μ
private def CurvAt (D : ℕ) (f : LevelChain L K top →ₗ[ℝ] ℝ) : Prop :=
  ∃ (D' s m : ℕ) (Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m), D' ≤ D ∧ Down D' Z ∧
    ∃ (c : Fin 3) (p : TorusPlaquette m), f = coordOf (topCurl Z) c p
variable [NeZero top] [Fintype (LevelBond L K top)] {μ : Measure (LevelChain L K top)} {n₀ : ℕ} (hF : Facts a ρA L top K μ n₀)
  (t : ℕ) (c : ℝ) (G : FormFamily) (hGm : ∀ (m : ℕ) [NeZero m], Measurable (G m))
  (hGg : ∀ (m : ℕ) [NeZero m], PolyGrowth (G m))
  (hGc : ∀ (m : ℕ) [NeZero m], n₀ ≤ m → ∀ A A' : ColourForm m, (∀ e p, curl (A e) p = curl (A' e) p) → G m A = G m A')
include hF hGm hGg hGc in
private theorem tower (hL : 1 ≤ L) : ∀ (e D n : ℕ) [NeZero n] (Z : LevelChain L K top →ₗ[ℝ] LevelChain L (t + e) n), Down D Z →
    ∀ (ι : Type) [Fintype ι] (H : ι → LevelChain L K top →ₗ[ℝ] ℝ), (∀ i, CurvAt D (H i)) →
    (∀ c' p, ∃ i, H i = coordOf (topCurl Z) c' p) → ∀ T : Set (ι → ℝ), MeasurableSet T →
    ∫ x in (fun x i => H i x) ⁻¹' T, G (fineSide L e n) (c • chainTop t _ (chainDescend t e n (Z x))) ∂μ =
      ∫ x in (fun x i => H i x) ⁻¹' T, meanOf a ρA t L c G e n (c • chainTop (t + e) n (Z x)) ∂μ
  | 0, D, n, _, Z, hZ, ι, _, H, hH, htop, T, hT => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (meanOf_zero c G n _).symm
  | e + 1, D, n, _, Z, hZ, ι, _, H, hH, htop, T, hT => by
    classical
    haveI := hF.canon.isProbabilityMeasure
    have hn : n₀ ≤ n := hF.side hZ
    have hnL : n₀ ≤ n * L := hn.trans (Nat.le_mul_of_pos_right n hL)
    let Z' : LevelChain L K top →ₗ[ℝ] LevelChain L (t + e) (n * L) := (lowerLin L (t + e) n).comp Z
    have hZ' : Down (D + 1) Z' := fun x => (hZ x).below
    let H' : ι ⊕ (Fin 3 × TorusPlaquette (n * L)) → LevelChain L K top →ₗ[ℝ] ℝ :=
      Sum.elim H (fun q => coordOf (topCurl Z') q.1 q.2)
    have hH' : ∀ i, CurvAt (D + 1) (H' i) := by
      rintro (i | q)
      · obtain ⟨D', s, m, Z₂, hle, hd, hc⟩ := hH i
        exact ⟨D', s, m, Z₂, by omega, hd, hc⟩
      · exact ⟨D + 1, _, _, Z', le_rfl, hZ', q.1, q.2, rfl⟩
    have htop' : ∀ c' p, ∃ i, H' i = coordOf (topCurl Z') c' p := fun c' p => ⟨Sum.inr (c', p), rfl⟩
    have hT' : MeasurableSet ((fun (b : ι ⊕ (Fin 3 × TorusPlaquette (n * L)) → ℝ) i => b (Sum.inl i)) ⁻¹' T) :=
      (measurable_pi_lambda _ fun i => measurable_pi_apply _) hT
    have ih := tower hL e (D + 1) (n * L) Z' hZ' _ H' hH' htop' _ hT'
    have hset : (fun x (i : ι ⊕ (Fin 3 × TorusPlaquette (n * L))) => H' i x) ⁻¹'
        ((fun (b : ι ⊕ (Fin 3 × TorusPlaquette (n * L)) → ℝ) i => b (Sum.inl i)) ⁻¹' T) = (fun x i => H i x) ⁻¹' T := rfl
    rw [hset] at ih
    refine ih.trans ?_
    obtain ⟨R, hR⟩ := exists_rangeInverse (curlV (n * L))
    obtain ⟨R₂, hR₂⟩ := exists_rangeInverse (curlV n)
    let M := pushLin a ρA L (t + e) n
    let Φ : (Fin 3 → TorusPlaquette n → ℝ) →ₗ[ℝ] (Fin 3 → TorusPlaquette (n * L) → ℝ) := (curlV (n * L)).comp (M.comp R₂)
    have hΦ : ∀ A : ColourForm n, Φ (curlV n A) = curlV (n * L) (M A) := fun A => by
      funext e' p
      exact hF.resp (t + e) n hn (R₂ (curlV n A) e') (A e') (fun p' => congrFun (congrFun (hR₂ A) e') p') p
    let gr : (Fin 3 → TorusPlaquette (n * L) → ℝ) → ℝ := fun w => meanOf a ρA t L c G e (n * L) (c • R w)
    have hK1 : ∀ A : ColourForm (n * L), meanOf a ρA t L c G e (n * L) (c • A) = gr (curlV (n * L) A) := fun A =>
      meanOf_curl c G hGm hGg hL hF.resp hGc e (n * L) hnL _ _ fun e' p => by
        have h0 := congrFun (congrFun (hR A) e') p
        simp only [curlV_apply] at h0
        have e1 : ∀ B : ColourForm (n * L), curl ((c • B) e') p = c * curl (B e') p := fun B => by
          simp only [curl, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e1, e1, h0]
    choose idx hidx using htop
    let ψ : LevelChain L K top → ι → ℝ := fun x i => H i x
    have hψm : Measurable ψ := measurable_pi_lambda _ fun i => (H i).continuous_of_finiteDimensional.measurable
    let yb : (ι → ℝ) → (Fin 3 → TorusPlaquette (n * L) → ℝ) := fun b => Φ (fun c' p => b (idx c' p))
    have hyb : Measurable yb := Φ.continuous_of_finiteDimensional.measurable.comp
      (measurable_pi_lambda _ fun c' => measurable_pi_lambda _ fun p => measurable_pi_apply _)
    have hy : ∀ x, yb (ψ x) = curlV (n * L) (M (chainTop (t + (e + 1)) n (Z x))) := fun x => by
      have h0 : (fun c' p => ψ x (idx c' p)) = curlV n (chainTop (t + (e + 1)) n (Z x)) := by
        funext c' p
        show H (idx c' p) x = _
        rw [hidx]
        simp [topCurl, coordOf]
      simp only [yb]
      rw [h0, hΦ]
    have hgrm : Measurable gr := (measurable_meanOf c G hGm e (n * L)).comp
      ((c • R).continuous_of_finiteDimensional.measurable)
    let f : (ι → ℝ) × (Fin 3 → TorusPlaquette (n * L) → ℝ) → ℝ := fun q => gr (yb q.1 + q.2)
    have hf : Measurable f := hgrm.comp ((hyb.comp measurable_fst).add measurable_snd)
    let St : LevelChain L K top →ₗ[ℝ] (Fin 3 → TorusPlaquette (n * L) → ℝ) :=
      (curlV (n * L)).comp ((stepLin a ρA (t + e) n).comp Z)
    have hSt : ∀ x, St x = curlV (n * L) (stepDefect a ρA (t + e) n (Z x)) := fun x => by
      simp only [St, LinearMap.comp_apply, stepLin_apply]
    have hDm : Measurable (fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) := by
      have : (fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) = St := by
        funext x
        exact (hSt x).symm
      rw [this]
      exact St.continuous_of_finiteDimensional.measurable
    have hsplit : ∀ x, chainTop (t + e) (n * L) (Z' x) = M (chainTop (t + (e + 1)) n (Z x)) + stepDefect a ρA (t + e) n (Z x) := fun x => by
      funext e' b
      exact (add_sub_cancel (pushColours a ρA L (t + e) (chainTop (t + e + 1) n (Z x)) e' b)
        (chainTop (t + e) (n * L) (chainLower (Z x)) e' b)).symm
    have hval : ∀ x, f (ψ x, curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) =
        meanOf a ρA t L c G e (n * L) (c • chainTop (t + e) (n * L) (Z' x)) := fun x => by
      rw [hK1, hsplit, map_add]
      simp only [f, hy]
    have hpsi : ∀ x, yb (ψ x) + curlV (n * L) (stepDefect a ρA (t + e) n (Z x)) = topCurl Z' x := fun x => by
      rw [hy, ← map_add, ← hsplit]
      simp [topCurl]
    have hgr : PolyGrowth gr := (growth_meanOf (a := a) (ρA := ρA) (t := t) (L := L) c G hGm hGg e (n * L)).comp_lin
      (E := Fin 3 → TorusPlaquette (n * L) → ℝ) (c • R)
    have hint : Integrable (fun x => f (ψ x, curlV (n * L) (stepDefect a ρA (t + e) n (Z x)))) μ := by
      obtain ⟨Kg, k, hKg, hg⟩ := hgr
      have hmom := moments_of_lin hF.canon (topCurl Z') (hF.ker hZ') k
      refine Integrable.mono' (hmom.const_mul Kg) (hf.comp (hψm.prodMk hDm)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [f, hpsi]
      exact hg _
    have hYk : ∀ x, levelEnergy a K top x = 0 → St x = 0 := fun x hx => by
      have h1 := hF.ker hZ' x hx
      have h2 := hF.ker hZ x hx
      have h3 := hpsi x
      rw [← hSt] at h3
      rw [h1] at h3
      have h4 : yb (ψ x) = 0 := by
        rw [hy, ← hΦ]
        have : curlV n (chainTop (t + (e + 1)) n (Z x)) = topCurl Z x := by simp [topCurl]
        rw [this, h2, map_zero]
      rw [h4, zero_add] at h3
      exact h3
    have hHk : ∀ i x, levelEnergy a K top x = 0 → H i x = 0 := fun i x hx => by
      obtain ⟨D', s, m, Z₂, _, hd, c', p, hf'⟩ := hH i
      rw [hf', coordOf_apply, hF.ker hd x hx]
      rfl
    let Y : Fin 3 × TorusPlaquette (n * L) → LevelChain L K top →ₗ[ℝ] ℝ := fun j => coordOf St j.1 j.2
    have hYk' : ∀ j x, levelEnergy a K top x = 0 → Y j x = 0 := fun j x hx => by
      simp only [Y, coordOf_apply, hYk x hx]
      rfl
    have hcov : ∀ i j, cov[H i, Y j; μ] = 0 := fun i j => by
      obtain ⟨D', s, m, Z₂, hle, hd, c', p, hf'⟩ := hH i
      have h1 := hF.indep (u := t + e) hZ hd hle
      have h2 := h1.comp (φ := fun w : Fin 3 → TorusPlaquette (n * L) → ℝ => w j.1 j.2) (ψ := fun w : Fin 3 → TorusPlaquette m → ℝ => w c' p)
        (by fun_prop) (by fun_prop)
      have h3 : IndepFun (Y j) (H i) μ := by
        have e1 : (⇑(Y j)) = (fun w : Fin 3 → TorusPlaquette (n * L) → ℝ => w j.1 j.2) ∘ fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x)) := by
          funext x
          simp only [Y, coordOf_apply, hSt, Function.comp]
        have e2 : (⇑(H i)) = (fun w : Fin 3 → TorusPlaquette m → ℝ => w c' p) ∘ fun x => topCurl Z₂ x := by
          funext x
          rw [hf']
          rfl
        rw [e1, e2]
        exact h2
      have m1 : MemLp (H i) 2 μ := (gauss_of_lin hF.canon (H i) (hHk i)).memLp_two
      have m2 : MemLp (Y j) 2 μ := (gauss_of_lin hF.canon (Y j) (hYk' j)).memLp_two
      exact h3.symm.covariance_eq_zero m1 m2
    have hI : IndepFun ψ (fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) μ := by
      have h3 := indep_of_cov hF.canon H Y hHk hYk' hcov
      have hc : Measurable (fun (v : Fin 3 × TorusPlaquette (n * L) → ℝ) (c' : Fin 3) (p : TorusPlaquette (n * L)) => v (c', p)) :=
        measurable_pi_lambda _ fun c' => measurable_pi_lambda _ fun p => measurable_pi_apply _
      have h4 := h3.comp measurable_id hc
      have e1 : (fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) =
          (fun (v : Fin 3 × TorusPlaquette (n * L) → ℝ) (c' : Fin 3) (p : TorusPlaquette (n * L)) => v (c', p)) ∘ fun x j => Y j x := by
        funext x c' p
        simp only [Y, coordOf_apply, hSt, Function.comp]
      rw [e1]
      exact h4
    have hfr := freeze hψm hDm hI hf hint hT
    have hcN : Measurable (fun η : StepFluctuation L (t + e) n => curlV (n * L) (extendFluctuation η)) :=
      ((curlV (n * L)).comp (extendLin (L := L) (t + e) n)).continuous_of_finiteDimensional.measurable
    calc ∫ x in (fun x i => H i x) ⁻¹' T, meanOf a ρA t L c G e (n * L) (c • chainTop (t + e) (n * L) (Z' x)) ∂μ
        = ∫ x in ψ ⁻¹' T, f (ψ x, curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) ∂μ := by
          simp only [hval, ψ]
      _ = ∫ x in ψ ⁻¹' T, ∫ z, f (ψ x, z) ∂(μ.map fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) ∂μ := hfr
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have hfx : Measurable (fun z => f (ψ x, z)) := hf.comp measurable_prodMk_left
          show ∫ z, f (ψ x, z) ∂(μ.map fun x => curlV (n * L) (stepDefect a ρA (t + e) n (Z x))) =
            meanOf a ρA t L c G (e + 1) n (c • chainTop (t + (e + 1)) n (Z x))
          rw [hF.law (u := t + e) hZ, integral_map hcN.aemeasurable hfx.aestronglyMeasurable,
            meanOf_succ c G hGm hGg e n]
          refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
          show f (ψ x, curlV (n * L) (extendFluctuation η)) = _
          simp only [f, hy]
          rw [← map_add, ← hK1]
          congr 1
          funext e' b
          have hM : pushColours a ρA L (t + e) (c • chainTop (t + (e + 1)) n (Z x)) = c • M (chainTop (t + (e + 1)) n (Z x)) :=
            map_smul (pushLin a ρA L (t + e) n) c _
          rw [hM]
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]
end Tower
section Kernel
variable {L : ℕ} [NeZero L]
private theorem curlNorm_smul {m : ℕ} [NeZero m] (r : ℝ) (X : ColourForm m) (p : TorusPlaquette m) : curlNorm (r • X) p = |r| * curlNorm X p := by apply _root_.YangMills.SharedProofs.p47915 <;> assumption
private theorem curl_of_norm {m : ℕ} [NeZero m] {X : ColourForm m} (h : ∀ p : OrientedPlaquette m, curlNorm X p.1 = 0) (e : Fin 3) (p : TorusPlaquette m) :
    curl (X e) p = 0 := by
  obtain ⟨x, i, j⟩ := p
  have hz : ∀ (q : TorusPlaquette m), q.2.1 < q.2.2 → curl (X e) q = 0 := fun q hq => by
    have h0 := h ⟨q, hq⟩
    rw [curlNorm_eq, norm_eq_zero] at h0
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v e) h0
    simpa using this
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hz _ hij
  · subst hij
    simp [curl]
  · have := hz (x, j, i) hij
    simp only [curl] at this ⊢
    linarith
variable {a : ℝ} {top K Kt : ℕ} [NeZero top] {C0 : ℝ}
private def LevelBound (a : ℝ) (L top Kt : ℕ) [NeZero L] [NeZero top] (C0 : ℝ) : Prop :=
  ∀ u d : ℕ, u + d = Kt → ∀ μ : Measure (LevelChain L (u + d) top), IsCanonicalGaussian (levelEnergy a (u + d) top) μ →
    ∀ p : OrientedPlaquette (fineSide L d top),
      ∫⁻ X, ENNReal.ofReal (curlNorm (chainTop u (fineSide L d top) (chainDescend u d top X)) p.1 ^ 2) ∂μ ≤ ENNReal.ofReal C0
private theorem Down.eq {s D : ℕ} {Z : LevelChain L (s + D) top →ₗ[ℝ] LevelChain L s (fineSide L D top)} (hZ : Down D Z)
    (x : LevelChain L (s + D) top) : Z x = chainDescend s D top x := by
  obtain ⟨h, _, h3⟩ := hZ x
  exact eq_of_heq h3
variable [Fintype (LevelBond L K top)]
private theorem shifted_canon {μ : Measure (LevelChain L K top)} (hc : IsCanonicalGaussian (levelEnergy a K top) μ)
    {x₀ : LevelChain L K top} (h0 : levelEnergy a K top x₀ = 0) (r : ℝ) :
    IsCanonicalGaussian (levelEnergy a K top) (μ.map fun x => x + r • x₀) := by
  have hm : Measurable (fun x : LevelChain L K top => x + r • x₀) := measurable_id.add_const _
  haveI := hc.isProbabilityMeasure
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, fun f hf => ?_⟩
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  rw [Measure.map_map hfm hm]
  have : f ∘ (fun x => x + r • x₀) = f := by
    funext x
    simp [hf x₀ h0]
  rw [this]
  exact hc.map_eq f hf
private theorem curl_on_kernel (hB : LevelBound a L top Kt C0) (hK : K = Kt) {μ : Measure (LevelChain L K top)}
    (hc : IsCanonicalGaussian (levelEnergy a K top) μ) {D s m : ℕ} [NeZero m]
    {Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m} (hZ : Down D Z) {x₀ : LevelChain L K top}
    (h0 : levelEnergy a K top x₀ = 0) : topCurl Z x₀ = 0 := by
  obtain ⟨h, hm, -⟩ := hZ 0
  subst h
  subst hm
  haveI := hc.isProbabilityMeasure
  have hbound : ∀ (r : ℝ) (p : OrientedPlaquette (fineSide L D top)),
      ∫⁻ x, ENNReal.ofReal (curlNorm (chainTop s _ (Z (x + r • x₀))) p.1 ^ 2) ∂μ ≤ ENNReal.ofReal C0 := fun r p => by
    have h1 := hB s D hK _ (shifted_canon hc h0 r) p
    have hm : Measurable (fun x : LevelChain L (s + D) top => x + r • x₀) := measurable_id.add_const _
    have hg : Measurable (fun X : LevelChain L (s + D) top =>
        ENNReal.ofReal (curlNorm (chainTop s (fineSide L D top) (chainDescend s D top X)) p.1 ^ 2)) := by
      have e : (fun X : LevelChain L (s + D) top => chainTop s (fineSide L D top) (chainDescend s D top X)) =
          (topLin L s _).comp Z := by
        funext X
        simp [hZ.eq]
      have h2 : Measurable (fun X : LevelChain L (s + D) top => chainTop s (fineSide L D top) (chainDescend s D top X)) := by
        rw [e]
        exact ((topLin L s _).comp Z).continuous_of_finiteDimensional.measurable
      exact ((continuous_curlNorm p.1).measurable.comp h2).pow_const 2 |>.ennreal_ofReal
    rw [lintegral_map hg hm] at h1
    simpa only [hZ.eq] using h1
  let T : LevelChain L (s + D) top →ₗ[ℝ] ColourForm (fineSide L D top) := (topLin L s _).comp Z
  have hT : ∀ x, T x = chainTop s _ (Z x) := fun x => by simp [T]
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have hzero : ∀ p : OrientedPlaquette (fineSide L D top), curlNorm (T x₀) p.1 = 0 := fun p => by
    by_contra hne
    have hδ : 0 < curlNorm (T x₀) p.1 := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)
    obtain ⟨δ, hδd⟩ : ∃ δ, δ = curlNorm (T x₀) p.1 := ⟨_, rfl⟩
    rw [← hδd] at hδ
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = max C0 0 + 1 := ⟨_, rfl⟩
    have hY1 : 1 ≤ Y := by
      rw [hY]
      linarith [le_max_right C0 0]
    have hYC : C0 < Y := by
      rw [hY]
      linarith [le_max_left C0 0]
    let r : ℝ := 2 * Y / δ
    have hr : r * δ = 2 * Y := by
      simp only [r]
      field_simp
    let G1 : LevelChain L (s + D) top → ENNReal := fun x => ENNReal.ofReal (curlNorm (T (x + r • x₀)) p.1 ^ 2)
    let G2 : LevelChain L (s + D) top → ENNReal := fun x => ENNReal.ofReal (curlNorm (T x) p.1 ^ 2)
    have hG2m : Measurable G2 := (((continuous_curlNorm p.1).measurable.comp hTm).pow_const 2).ennreal_ofReal
    have hG1m : Measurable G1 := hG2m.comp (measurable_id.add_const _)
    have hb1 : ∫⁻ x, G1 x ∂μ ≤ ENNReal.ofReal C0 := by
      have := hbound r p
      simpa only [G1, hT] using this
    have hb2 : ∫⁻ x, G2 x ∂μ ≤ ENNReal.ofReal C0 := by
      have := hbound 0 p
      simpa only [G2, hT, zero_smul, add_zero] using this
    have hpt : ∀ x, ENNReal.ofReal ((2 * Y) ^ 2) ≤ 2 * G1 x + 2 * G2 x := fun x => by
      have e1 : T (x + r • x₀) + (-1 : ℝ) • T x = r • T x₀ := by
        rw [map_add, map_smul]
        simp only [neg_smul, one_smul]
        abel
      have e2 := curlNorm_add_le (T (x + r • x₀)) ((-1 : ℝ) • T x) p.1
      rw [e1, curlNorm_smul, curlNorm_smul] at e2
      have e3 : |r| * curlNorm (T x₀) p.1 = 2 * Y := by
        rw [← hδd, abs_of_nonneg (by positivity), hr]
      rw [e3] at e2
      simp only [abs_neg, abs_one, one_mul] at e2
      have u0 : 0 ≤ curlNorm (T (x + r • x₀)) p.1 := Real.sqrt_nonneg _
      have v0 : 0 ≤ curlNorm (T x) p.1 := Real.sqrt_nonneg _
      have e4 : (2 * Y) ^ 2 ≤ 2 * curlNorm (T (x + r • x₀)) p.1 ^ 2 + 2 * curlNorm (T x) p.1 ^ 2 := by
        have : 0 ≤ 2 * Y := by positivity
        nlinarith [sq_nonneg (curlNorm (T (x + r • x₀)) p.1 - curlNorm (T x) p.1)]
      refine (ENNReal.ofReal_le_ofReal e4).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp [G1, G2]
    have key : ENNReal.ofReal ((2 * Y) ^ 2) ≤ 2 * ENNReal.ofReal C0 + 2 * ENNReal.ofReal C0 := by
      calc ENNReal.ofReal ((2 * Y) ^ 2) = ∫⁻ x, ENNReal.ofReal ((2 * Y) ^ 2) ∂μ := by simp
        _ ≤ ∫⁻ x, (2 * G1 x + 2 * G2 x) ∂μ := lintegral_mono hpt
        _ = 2 * ∫⁻ x, G1 x ∂μ + 2 * ∫⁻ x, G2 x ∂μ := by
            rw [lintegral_add_left (hG1m.const_mul _), lintegral_const_mul _ hG1m, lintegral_const_mul _ hG2m]
        _ ≤ _ := add_le_add (mul_le_mul_right hb1 _) (mul_le_mul_right hb2 _)
    have hC : ENNReal.ofReal ((2 * Y) ^ 2) ≤ ENNReal.ofReal (4 * max C0 0) := by
      refine key.trans ?_
      have e0 : ENNReal.ofReal C0 ≤ ENNReal.ofReal (max C0 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
      have e1 : (0 : ℝ) ≤ max C0 0 := le_max_right _ _
      have e2 : ENNReal.ofReal (4 * max C0 0) = 2 * ENNReal.ofReal (max C0 0) + 2 * ENNReal.ofReal (max C0 0) := by
        have : 4 * max C0 0 = 2 * max C0 0 + 2 * max C0 0 := by ring
        rw [this, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp
      rw [e2]
      exact add_le_add (mul_le_mul_right e0 _) (mul_le_mul_right e0 _)
    have hC' : (2 * Y) ^ 2 ≤ 4 * max C0 0 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hC
    have hY2 : max C0 0 + 1 = Y := hY.symm
    nlinarith [le_max_right C0 0]
  funext e p
  have h1 := curl_of_norm hzero e p
  simpa [topCurl, hT] using h1
end Kernel
section Build
variable {a ρA : ℝ} {L : ℕ} [NeZero L] {top K Kt : ℕ} [NeZero top] {C0 : ℝ}
private def StepsOfTheChain (a ρA : ℝ) (L top Kt : ℕ) [NeZero L] [NeZero top] : Prop :=
  ∀ u j d : ℕ, u + 1 + j + d = Kt → ∀ μ : Measure (LevelChain L (u + 1 + j + d) top),
    IsCanonicalGaussian (levelEnergy a (u + 1 + j + d) top) μ →
    (∀ᵐ X ∂μ, IsTreeGauge (u + 1 + j + d) top X) →
    (∀ᵐ X ∂μ, ∀ (e : Fin 3), ∀ b ∉ chartBonds L (fineSide L j (fineSide L d top)),
      stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d top X)) e b = 0) ∧
    (∀ co : Fin 3 → ChartBondIndex L u (fineSide L j (fineSide L d top)) → ℝ,
      μ.map (fun X => ∑ e : Fin 3, ∑ b, co e b * chartValues (u := u)
          (stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d top X))) e b) =
        gaussianReal 0 (∑ e : Fin 3, co e ⬝ᵥ
          ((trivialHessian a L u (fineSide L j (fineSide L d top)))⁻¹.mulVec (co e))).toNNReal) ∧
    IndepFun (fun X => stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) d top X)))
      (fun X (e : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
        curl (chainTop (u + 1 + j) _ (chainDescend (u + 1 + j) d top X) e) p) μ
private theorem measurable_chartValues {u m : ℕ} [NeZero m] (e : Fin 3) (b : ChartBondIndex L u m) :
    Measurable (fun X : ColourForm (m * L) => chartValues (u := u) X e b) := by
  classical
  unfold chartValues
  refine Finset.measurable_sum _ fun c _ => ?_
  by_cases h : (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2) = b.1
  · simp only [h, if_true]
    exact (measurable_pi_apply c).comp (measurable_pi_apply e)
  · simp only [h, if_false]
    exact measurable_const
variable [Fintype (LevelBond L K top)] {μ : Measure (LevelChain L K top)} {n₀ : ℕ}
private theorem side_of_down {D s m : ℕ} (hL : 1 ≤ L) (htop : n₀ ≤ top) {Z : LevelChain L K top →ₗ[ℝ] LevelChain L s m}
    (hZ : Down D Z) : n₀ ≤ m := by
  obtain ⟨_, hm, _⟩ := hZ 0
  rw [← hm, fineSide_eq]
  exact htop.trans (Nat.le_mul_of_pos_right _ (pow_pos hL _))
private theorem facts_law (hS : StepsOfTheChain a ρA L top Kt) (hK : K = Kt) (hodd : Odd L) (hL : 1 ≤ L) (htop : n₀ ≤ top) (h2 : 2 ≤ n₀)
    (hH : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → (trivialHessian a L u n).PosDef)
    (hc : IsCanonicalGaussian (levelEnergy a K top) μ) (htree : ∀ᵐ X ∂μ, IsTreeGauge K top X)
    {D u m : ℕ} [NeZero m] {Z : LevelChain L K top →ₗ[ℝ] LevelChain L (u + 1) m} (hZ : Down D Z) :
    μ.map (fun x => curlV (m * L) (stepDefect a ρA u m (Z x))) =
      (fluctuationGaussian a L 1 u m).map (fun η => curlV (m * L) (extendFluctuation η)) := by
  have hside := side_of_down hL htop hZ
  obtain ⟨h, hm, -⟩ := hZ 0
  subst h
  subst hm
  haveI := hc.isProbabilityMeasure
  have hs := hS u 0 D hK μ hc htree
  have hZe := Down.eq hZ
  have hSf : Measurable (fun x => stepDefect a ρA u (fineSide L D top) (Z x)) := by
    have : (fun x => stepDefect a ρA u (fineSide L D top) (Z x)) = (stepLin a ρA u (fineSide L D top)).comp Z := by
      funext x
      simp [stepLin_apply]
    rw [this]
    exact ((stepLin a ρA u (fineSide L D top)).comp Z).continuous_of_finiteDimensional.measurable
  let W : LevelChain L (u + 1 + D) top → Fin 3 → ChartBondIndex L u (fineSide L D top) → ℝ :=
    fun x e b => chartValues (u := u) (stepDefect a ρA u (fineSide L D top) (Z x)) e b
  have hWm : Measurable W := measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun b =>
    (measurable_chartValues e b).comp hSf
  have hlawW := law_of_coords (a := a) (μ := μ) (hH u _ hside) W hWm (fun co => by
    have := hs.2.1 co
    simp only [W, hZe]
    exact this)
  have hTm : Measurable (fun x => (WithLp.toLp 2 fun i => W x i.1 i.2 : StepFluctuation L u (fineSide L D top))) := by
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun i => ?_)
    exact (measurable_pi_apply i.2).comp ((measurable_pi_apply i.1).comp hWm)
  have hcN : Measurable (fun η : StepFluctuation L u (fineSide L D top) => curlV (fineSide L D top * L) (extendFluctuation η)) :=
    ((curlV (fineSide L D top * L)).comp (extendLin (L := L) u _)).continuous_of_finiteDimensional.measurable
  have e1 : (fun x => curlV (fineSide L D top * L) (stepDefect a ρA u (fineSide L D top) (Z x))) =ᵐ[μ]
      (fun η : StepFluctuation L u (fineSide L D top) => curlV (fineSide L D top * L) (extendFluctuation η)) ∘
        fun x => (WithLp.toLp 2 fun i => W x i.1 i.2 : StepFluctuation L u (fineSide L D top)) := by
    filter_upwards [hs.1] with x hx
    show _ = curlV (fineSide L D top * L) (extendFluctuation _)
    rw [extend_coords hodd (h2.trans hside) _ (fun e b hb => by
      rw [hZe x]
      exact hx e b hb)]
  rw [Measure.map_congr e1, ← hlawW, Measure.map_map hcN hTm]
private theorem facts_indep (hS : StepsOfTheChain a ρA L top Kt) (hK : K = Kt)
    (hc : IsCanonicalGaussian (levelEnergy a K top) μ) (htree : ∀ᵐ X ∂μ, IsTreeGauge K top X)
    {D D' u m s m' : ℕ} [NeZero m] {Z : LevelChain L K top →ₗ[ℝ] LevelChain L (u + 1) m}
    {Z' : LevelChain L K top →ₗ[ℝ] LevelChain L s m'} (hZ : Down D Z) (hZ' : Down D' Z') (hle : D' ≤ D) :
    IndepFun (fun x => curlV (m * L) (stepDefect a ρA u m (Z x))) (fun x => topCurl Z' x) μ := by
  obtain ⟨j, rfl⟩ : ∃ j, D = D' + j := ⟨D - D', by omega⟩
  obtain ⟨h1, -, -⟩ := hZ 0
  obtain ⟨h2, hm2, -⟩ := hZ' 0
  have hs : s = u + 1 + j := by omega
  subst hs
  subst h2
  subst hm2
  have hZe' := Down.eq hZ'
  have hdown : ∀ x : LevelChain L (u + 1 + j + D') top,
      IsDown (D' + j) x (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) D' top x)) := fun x => by
    have ha : IsDown D' x (chainDescend (u + 1 + j) D' top x) := by
      have := IsDown.down (s := u + 1 + j) D' 0 top (Z := x) (IsDown.zero x)
      rwa [Nat.zero_add] at this
    exact IsDown.down (s := u + 1) j D' _ ha
  have hmm : m = fineSide L j (fineSide L D' top) := (IsDown.unique (hZ 0) (hdown 0)).1
  subst hmm
  have hZc : ∀ x, Z x = chainDescend (u + 1) j _ (chainDescend (u + 1 + j) D' top x) :=
    fun x => eq_of_heq (IsDown.unique (hZ x) (hdown x)).2
  have hs3 := (hS u j D' hK μ hc htree).2.2
  have hm : Measurable (curlV (fineSide L j (fineSide L D' top) * L)) :=
    (curlV (fineSide L j (fineSide L D' top) * L)).continuous_of_finiteDimensional.measurable
  have h4 := hs3.comp hm measurable_id
  have e1 : (fun x => curlV _ (stepDefect a ρA u (fineSide L j (fineSide L D' top)) (Z x))) =
      (curlV _) ∘ (fun X => stepDefect a ρA u _ (chainDescend (u + 1) j _ (chainDescend (u + 1 + j) D' top X))) := by
    funext x
    simp only [Function.comp, hZc]
  have e2 : (fun x => topCurl Z' x) = id ∘ (fun X (e : Fin 3) (p : TorusPlaquette (fineSide L D' top)) =>
      curl (chainTop (u + 1 + j) _ (chainDescend (u + 1 + j) D' top X) e) p) := by
    funext x e p
    simp [topCurl, hZe']
  rw [e1, e2]
  exact h4
private theorem curl_factor {m : ℕ} [NeZero m] {Gf : ColourForm m → ℝ} (hm : Measurable Gf) (hg : PolyGrowth Gf)
    (hr : ∀ A A' : ColourForm m, (∀ e p, curl (A e) p = curl (A' e) p) → Gf A = Gf A') :
    ∃ gr : (Fin 3 → TorusPlaquette m → ℝ) → ℝ, Measurable gr ∧ PolyGrowth gr ∧ ∀ A, Gf A = gr (curlV m A) := by
  obtain ⟨R, hR⟩ := exists_rangeInverse (curlV m)
  refine ⟨fun w => Gf (R w), hm.comp R.continuous_of_finiteDimensional.measurable, hg.comp_lin R, fun A => ?_⟩
  refine hr _ _ fun e p => ?_
  exact (congrFun (congrFun (hR A) e) p).symm
private theorem integrable_observable (hc : IsCanonicalGaussian (levelEnergy a K top) μ) {s m : ℕ} [NeZero m]
    {Zs : LevelChain L K top →ₗ[ℝ] LevelChain L s m} (hk : ∀ x, levelEnergy a K top x = 0 → topCurl Zs x = 0)
    {gr : (Fin 3 → TorusPlaquette m → ℝ) → ℝ} (hm : Measurable gr) (hg : PolyGrowth gr) :
    Integrable (fun x => gr (topCurl Zs x)) μ := by
  obtain ⟨Kg, k, hKg, h⟩ := hg
  have hmom := moments_of_lin hc (topCurl Zs) hk k
  refine Integrable.mono' (hmom.const_mul Kg)
    (hm.comp (topCurl Zs).continuous_of_finiteDimensional.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => h _)
end Build
section Mean
variable {a ρA : ℝ} {L : ℕ} [NeZero L] {top Kt : ℕ} [NeZero top] {C0 : ℝ} {n₀ : ℕ}
private theorem smul_curl {m : ℕ} (c : ℝ) {A A' : ColourForm m} (h : ∀ e p, curl (A e) p = curl (A' e) p) (e : Fin 3) (p : TorusPlaquette m) :
    curl ((c • A) e) p = curl ((c • A') e) p := by
  have e1 : ∀ B : ColourForm m, curl ((c • B) e) p = c * curl (B e) p := fun B => by
    simp only [curl, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, e1, h]
private theorem chain_condMean (hB : LevelBound a L top Kt C0) (hS : StepsOfTheChain a ρA L top Kt)
    (hTree : treeGaugeFixingStatement) (hodd : Odd L) (hL : 1 ≤ L) (htop : n₀ ≤ top) (h64 : 64 ≤ n₀)
    (hH : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → (trivialHessian a L u n).PosDef)
    (hresp : ∀ (u m : ℕ) [NeZero m], n₀ ≤ m → ∀ A A' : TorusBond m → ℝ, (∀ p, curl A p = curl A' p) → ∀ p,
      curl (responseMap a ρA L u A) p = curl (responseMap a ρA L u A') p)
    (c : ℝ) (G : FormFamily) (hGm : ∀ (m : ℕ) [NeZero m], Measurable (G m))
    (hGg : ∀ (m : ℕ) [NeZero m], PolyGrowth (G m))
    (hGc : ∀ (m : ℕ) [NeZero m], n₀ ≤ m → ∀ A A' : ColourForm m, (∀ e p, curl (A e) p = curl (A' e) p) → G m A = G m A')
    (t e d : ℕ) (hK : t + e + d = Kt) (μ : Measure (LevelChain L (t + e + d) top))
    (hc : IsCanonicalGaussian (levelEnergy a (t + e + d) top) μ) :
    (fun X => meanOf a ρA t L c G e (fineSide L d top) (c • chainTop (t + e) _ (chainDescend (t + e) d top X))) =ᵐ[μ]
      μ[fun X => G (fineSide L e (fineSide L d top)) (c • chainTop t _ (chainDescend t e _ (chainDescend (t + e) d top X))) |
        MeasurableSpace.comap (fun X (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
          curl (chainTop (t + e) _ (chainDescend (t + e) d top X) cc) p) inferInstance] := by
  classical
  haveI := finite_levelBond L (t + e + d) top
  letI : Fintype (LevelBond L (t + e + d) top) := Fintype.ofFinite _
  haveI := hc.isProbabilityMeasure
  obtain ⟨Gm, hGmap⟩ := hTree L hodd (t + e + d) top (h64.trans htop)
  have hGmm : Measurable Gm := Gm.continuous_of_finiteDimensional.measurable
  have hker : ∀ x, levelEnergy a (t + e + d) top (Gm x - x) = 0 := fun x => (hGmap x).2 a
  have hc' : IsCanonicalGaussian (levelEnergy a (t + e + d) top) (μ.map Gm) := by
    refine ⟨Measure.isProbabilityMeasure_map hGmm.aemeasurable, fun f hf => ?_⟩
    rw [Measure.map_map f.continuous_of_finiteDimensional.measurable hGmm]
    have : f ∘ Gm = f := by
      funext x
      have := hf _ (hker x)
      simp only [map_sub] at this
      simpa using sub_eq_zero.1 this
    rw [this]
    exact hc.map_eq f hf
  have htree : ∀ᵐ X ∂(μ.map Gm), IsTreeGauge (t + e + d) top X := by
    have hcl : MeasurableSet ((LinearMap.range Gm : Submodule ℝ (LevelChain L (t + e + d) top)) : Set (LevelChain L (t + e + d) top)) :=
      (Submodule.closed_of_finiteDimensional _).measurableSet
    have h0 : (μ.map Gm) ((LinearMap.range Gm : Submodule ℝ (LevelChain L (t + e + d) top)) : Set (LevelChain L (t + e + d) top))ᶜ = 0 := by
      rw [Measure.map_apply hGmm hcl.compl]
      have : Gm ⁻¹' ((LinearMap.range Gm : Submodule ℝ (LevelChain L (t + e + d) top)) : Set (LevelChain L (t + e + d) top))ᶜ = ∅ := by
        ext x
        simp
      rw [this]
      simp
    refine measure_mono_null (fun X hX => ?_) h0
    intro hr
    obtain ⟨y, rfl⟩ := hr
    exact hX (hGmap y).1
  have hF : Facts a ρA L top (t + e + d) (μ.map Gm) n₀ :=
    { canon := hc'
      side := fun hZ => side_of_down hL htop hZ
      ker := fun {D s m Z} hZ x hx => by
        obtain ⟨_, hm, _⟩ := hZ 0
        subst hm
        exact curl_on_kernel hB hK hc' hZ hx
      resp := hresp
      law := fun hZ => facts_law hS hK hodd hL htop (by omega) hH hc' htree hZ
      indep := fun hZ hZ' hle => facts_indep hS hK hc' htree hZ hZ' hle }
  obtain ⟨m, hmdef⟩ : ∃ m, m = fineSide L d top := ⟨_, rfl⟩
  let Z0 : LevelChain L (t + e + d) top →ₗ[ℝ] LevelChain L (t + e) (fineSide L d top) := descendLin L (t + e) d top
  have hZ0x : ∀ x, Z0 x = chainDescend (t + e) d top x := fun x => descendLin_apply L (t + e) d top x
  have hZ0 : Down d Z0 := fun x => by
    rw [hZ0x]
    have := IsDown.down (s := t + e) d 0 top (Z := x) (IsDown.zero x)
    rwa [Nat.zero_add] at this
  let Zt : LevelChain L (t + e + d) top →ₗ[ℝ] LevelChain L t (fineSide L e (fineSide L d top)) :=
    (descendLin L t e (fineSide L d top)).comp Z0
  have hZtx : ∀ x, Zt x = chainDescend t e _ (chainDescend (t + e) d top x) := fun x => by
    simp only [Zt, LinearMap.comp_apply, descendLin_apply, hZ0x]
  have hZt : Down (d + e) Zt := fun x => by
    rw [hZtx, ← hZ0x]
    exact IsDown.down (s := t) e d _ (hZ0 x)
  have k0 : ∀ x, levelEnergy a (t + e + d) top x = 0 → topCurl Z0 x = 0 := fun x hx => curl_on_kernel hB hK hc hZ0 hx
  have kt : ∀ x, levelEnergy a (t + e + d) top x = 0 → topCurl Zt x = 0 := fun x hx => curl_on_kernel hB hK hc hZt hx
  have hm0 : n₀ ≤ fineSide L d top := side_of_down hL htop hZ0
  have hmt : n₀ ≤ fineSide L e (fineSide L d top) := side_of_down hL htop hZt
  obtain ⟨g1, hg1m, hg1g, hg1⟩ := curl_factor (Gf := fun A : ColourForm (fineSide L e (fineSide L d top)) => G _ (c • A))
    ((hGm _).comp (measurable_const_smul c)) (PolyGrowth.comp_lin (f := G (fineSide L e (fineSide L d top))) (hGg _) (c • LinearMap.id))
    (fun A A' h => hGc _ hmt _ _ (smul_curl c h))
  obtain ⟨g0, hg0m, hg0g, hg0⟩ := curl_factor (Gf := fun A : ColourForm (fineSide L d top) => meanOf a ρA t L c G e (fineSide L d top) (c • A))
    ((measurable_meanOf c G hGm e _).comp (measurable_const_smul c))
    (PolyGrowth.comp_lin (f := meanOf a ρA t L c G e (fineSide L d top)) (growth_meanOf c G hGm hGg e _) (c • LinearMap.id))
    (fun A A' h => meanOf_curl c G hGm hGg hL hresp hGc e _ hm0 _ _ (smul_curl c h))
  have hcur0 : ∀ x, topCurl Z0 x = curlV _ (chainTop (t + e) _ (Z0 x)) := fun x => by simp [topCurl]
  have hcurt : ∀ x, topCurl Zt x = curlV _ (chainTop t _ (Zt x)) := fun x => by simp [topCurl]
  let H : Fin 3 × TorusPlaquette (fineSide L d top) → LevelChain L (t + e + d) top →ₗ[ℝ] ℝ := fun q => coordOf (topCurl Z0) q.1 q.2
  have ht := tower hF t c G hGm hGg hGc hL e d (fineSide L d top) Z0 hZ0 _ H
    (fun q => ⟨d, _, _, Z0, le_rfl, hZ0, q.1, q.2, rfl⟩) (fun c' p => ⟨(c', p), rfl⟩)
  have hinv0 : ∀ x, topCurl Z0 (Gm x) = topCurl Z0 x := fun x => by
    have := k0 _ (hker x)
    rw [map_sub] at this
    exact sub_eq_zero.1 this
  have hinvt : ∀ x, topCurl Zt (Gm x) = topCurl Zt x := fun x => by
    have := kt _ (hker x)
    rw [map_sub] at this
    exact sub_eq_zero.1 this
  have hmC0 : Measurable (fun x => g0 (topCurl Z0 x)) :=
    hg0m.comp (topCurl Z0).continuous_of_finiteDimensional.measurable
  have hmCt : Measurable (fun x => g1 (topCurl Zt x)) :=
    hg1m.comp (topCurl Zt).continuous_of_finiteDimensional.measurable
  have hψm : Measurable (fun x (q : Fin 3 × TorusPlaquette (fineSide L d top)) => H q x) :=
    measurable_pi_lambda _ fun q => (H q).continuous_of_finiteDimensional.measurable
  have hpull : ∀ T : Set (Fin 3 × TorusPlaquette (fineSide L d top) → ℝ), MeasurableSet T →
      ∫ x in (fun x q => H q x) ⁻¹' T, g1 (topCurl Zt x) ∂μ = ∫ x in (fun x q => H q x) ⁻¹' T, g0 (topCurl Z0 x) ∂μ := fun T hT => by
    have h1 := ht T hT
    have e1 : ∀ x, G (fineSide L e (fineSide L d top)) (c • chainTop t _ (chainDescend t e _ (Z0 x))) = g1 (topCurl Zt x) := fun x => by
      rw [hcurt, ← hg1, hZtx, hZ0x]
    have e2 : ∀ x, meanOf a ρA t L c G e (fineSide L d top) (c • chainTop (t + e) _ (Z0 x)) = g0 (topCurl Z0 x) := fun x => by
      rw [hcur0, ← hg0]
    simp only [e1, e2] at h1
    have hs : MeasurableSet ((fun x q => H q x) ⁻¹' T) := hψm hT
    have hpre : Gm ⁻¹' ((fun x q => H q x) ⁻¹' T) = (fun x q => H q x) ⁻¹' T := by
      ext x
      have : (fun q => H q (Gm x)) = fun q => H q x := by
        funext q
        simp only [H, coordOf_apply, hinv0]
      simp only [Set.mem_preimage, this]
    rw [setIntegral_map hs hmCt.aestronglyMeasurable hGmm.aemeasurable,
      setIntegral_map hs hmC0.aestronglyMeasurable hGmm.aemeasurable, hpre] at h1
    simpa only [Function.comp, hinv0, hinvt] using h1
  have e0 : (fun X => meanOf a ρA t L c G e (fineSide L d top) (c • chainTop (t + e) _ (chainDescend (t + e) d top X))) =
      fun x => g0 (topCurl Z0 x) := by
    funext x
    rw [hcur0, ← hg0, hZ0x]
  have e1 : (fun X => G (fineSide L e (fineSide L d top)) (c • chainTop t _ (chainDescend t e _ (chainDescend (t + e) d top X)))) =
      fun x => g1 (topCurl Zt x) := by
    funext x
    rw [hcurt, ← hg1, hZtx]
  rw [e0, e1]
  have hcv : Measurable (fun X (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
      curl (chainTop (t + e) _ (chainDescend (t + e) d top X) cc) p) := by
    have : (fun X (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
        curl (chainTop (t + e) _ (chainDescend (t + e) d top X) cc) p) = topCurl Z0 := by
      funext X cc p
      simp [topCurl, hZ0x]
    rw [this]
    exact (topCurl Z0).continuous_of_finiteDimensional.measurable
  have hcv0 : ∀ x, topCurl Z0 x = (fun (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
      curl (chainTop (t + e) _ (chainDescend (t + e) d top x) cc) p) := fun x => by
    funext cc p
    simp [topCurl, hZ0x]
  have hI0 := integrable_observable hc k0 hg0m hg0g
  have hIt := integrable_observable hc kt hg1m hg1g
  refine ae_eq_condExp_of_forall_setIntegral_eq hcv.comap_le hIt (fun s _ _ => hI0.integrableOn) (fun s hs _ => ?_) ?_
  · obtain ⟨T', hT', rfl⟩ := hs
    have hT : MeasurableSet ((fun (v : Fin 3 × TorusPlaquette (fineSide L d top) → ℝ) (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) => v (cc, p)) ⁻¹' T') :=
      (measurable_pi_lambda _ fun cc => measurable_pi_lambda _ fun p => measurable_pi_apply _) hT'
    have := hpull _ hT
    have hset : (fun x q => H q x) ⁻¹' ((fun (v : Fin 3 × TorusPlaquette (fineSide L d top) → ℝ) (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) => v (cc, p)) ⁻¹' T') =
        (fun X (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
          curl (chainTop (t + e) _ (chainDescend (t + e) d top X) cc) p) ⁻¹' T' := by
      ext x
      simp only [Set.mem_preimage, H, coordOf_apply, hcv0]
    rw [hset] at this
    exact this.symm
  · have : Measurable[MeasurableSpace.comap (fun X (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
        curl (chainTop (t + e) _ (chainDescend (t + e) d top X) cc) p) inferInstance] (fun x => g0 (topCurl Z0 x)) := by
      have e3 : (fun x => g0 (topCurl Z0 x)) = g0 ∘ (fun X (cc : Fin 3) (p : TorusPlaquette (fineSide L d top)) =>
          curl (chainTop (t + e) _ (chainDescend (t + e) d top X) cc) p) := by
        funext x
        simp only [Function.comp, hcv0]
      rw [e3]
      exact hg0m.comp (comap_measurable _)
    exact this.stronglyMeasurable.aestronglyMeasurable
end Mean
section Params
private theorem params_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (f : ∀ Λ, Q Λ → Q' Λ) : ForAllParameters Q' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem params_and {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (h' : ForAllParameters Q') :
    ForAllParameters fun Λ => Q Λ ∧ Q' Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem params_families {P : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies P) :
    ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem params_admissible : ForAllParameters fun Λ => Λ.table.Admissible := by apply _root_.YangMills.SharedProofs.p23915 <;> assumption
private def ContractionAt (Λ : MomentParameters) : Prop :=
  ∃ Cw : ℝ, 0 < Cw ∧ Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2⁻¹ ^ 10 * (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ∧
    ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
      ∀ (ω : TorusPlaquette (n * Λ.stepParams.side) → ℝ) (ω' : TorusPlaquette n → ℝ), (∀ p, 0 < ω p) → (∀ p, 0 < ω' p) →
      IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8) ω ω' →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal), 1 ≤ q → Measurable X →
        weightedCurvatureNorm μ ω q (fun e => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u (X e)) ≤
          ENNReal.ofReal (Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ)) * weightedCurvatureNorm μ ω' q X
private theorem params_contraction (h : responseContractionStatement) : ForAllParameters ContractionAt := by
  intro a ha
  obtain ⟨Cw, hCw, L₀, rt₀, C₀, hpos, h1⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hpos, fun L hodd hL Tb hTa hTL hD hCS hCH hrt hC Kr hKr => ?_⟩
  obtain ⟨hi, y₀, h2⟩ := h1 L hodd hL Tb hTa hTL hD hCS hCH hrt hC
  subst hTL
  subst hTa
  exact ⟨y₀, fun y hy hR hW g hg hgy k _ hk hk' R d hd => ⟨Cw, hCw, hi, h2 y hy hR hW⟩⟩
end Params
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem annihilates_sum {n : ℕ} [NeZero n] {ι : Type*} (s : Finset ι) (q : ι → BondBilinear n)
    (h : ∀ y ∈ s, AnnihilatesClosedForms (q y)) :
    AnnihilatesClosedForms (fun b b' => ∑ y ∈ s, q y b b') := by
  classical
  have hs : ∀ A B : TorusBond n → ℝ, bilinearEval (fun b b' => ∑ y ∈ s, q y b b') A B = ∑ y ∈ s, bilinearEval (q y) A B := fun A B => by
    induction s using Finset.induction_on with
    | empty => simp [bilinearEval]
    | insert y s hy ih =>
      simp only [Finset.sum_insert hy]
      rw [← ih fun z hz => h z (Finset.mem_insert_of_mem hz)]
      simp only [bilinearEval, mul_add, add_mul, Finset.sum_add_distrib]
  constructor
  · intro φ A
    rw [hs, hs]
    exact ⟨Finset.sum_eq_zero fun y hy => ((h y hy).1 φ A).1, Finset.sum_eq_zero fun y hy => ((h y hy).1 φ A).2⟩
  · intro v A
    rw [hs, hs]
    exact ⟨Finset.sum_eq_zero fun y hy => ((h y hy).2 v A).1, Finset.sum_eq_zero fun y hy => ((h y hy).2 v A).2⟩
private theorem product_measurable (t m : ℕ) [NeZero m] (B : Finset (Fin Λ.k)) : Measurable (S.formProduct t m B) := by apply _root_.YangMills.SharedProofs.p97087 <;> assumption
private theorem product_growth (t m : ℕ) [NeZero m] (B : Finset (Fin Λ.k)) : PolyGrowth (S.formProduct t m B) := by
  unfold MomentPoint.formProduct
  exact PolyGrowth.prod _ fun i _ => (PolyGrowth.const _).mul (colourEval_growth _)
private theorem colourEval_rot {m : ℕ} [NeZero m] (q : BondBilinear m) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (Z : ColourForm m) : colourEval q (rotF R Z) (rotF R Z) = colourEval q Z Z :=
  pair_rot q hR Z
end Point
section Final
private theorem geom_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) (d : ℕ) : ∑ j ∈ Finset.range d, θ ^ j ≤ 2 := by apply _root_.YangMills.Construction.EvaluationSums.geom_sum_le_two <;> assumption
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem coord_bound {a lam : ℝ} {L u m : ℕ} [NeZero L] [NeZero m] {q : ENNReal} (hq : q ≠ ⊤) (hH : (trivialHessian a L u m).PosDef)
    (hb : ∀ b, (trivialHessian a L u m)⁻¹ b b ≤ 2 / lam) (i : Fin 3 × ChartBondIndex L u m) :
    eLpNorm (fun η : StepFluctuation L u m => η i) q (fluctuationGaussian a L 1 u m) ≤
      ENNReal.ofReal (Real.sqrt (2 / lam) * (eLpNorm id q (gaussianReal 0 1)).toReal) := by
  classical
  have hp := covariance_psd (a := a) (L := L) (u := u) (n := m) hH
  have hfin : eLpNorm id q (gaussianReal 0 1) ≠ ⊤ := (memLp_id_gaussianReal' q hq).2.ne
  unfold fluctuationGaussian
  rw [gauss_coord hp, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hfin]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)) _
  obtain ⟨e, b⟩ := i
  simpa [fluctuationCov] using hb b
private theorem product_reads (ht : S.lastSeparated ≤ S.data.windowLevel)
    (hK : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      AnnihilatesClosedForms (classicalRemainder S.tower S.resp t n h y) ∧ AnnihilatesClosedForms (classicalQuadratic S.tower S.resp t n h y) ∧
      (∀ h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n),
        (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = h' p) →
        classicalRemainder S.tower S.resp t n h y = classicalRemainder S.tower S.resp t n h' y ∧
          classicalQuadratic S.tower S.resp t n h y = classicalQuadratic S.tower S.resp t n h' y) ∧
      ((∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
        classicalRemainder S.tower S.resp t n h y = 0 ∧ classicalQuadratic S.tower S.resp t n h y = 0))
    (B : Finset (Fin Λ.k)) (m : ℕ) [NeZero m] (hm : Λ.stepParams.n₀ ≤ m) (A A' : ColourForm m)
    (h : ∀ e p, curl (A e) p = curl (A' e) p) : S.formProduct S.lastSeparated m B A = S.formProduct S.lastSeparated m B A' := by
  unfold MomentPoint.formProduct
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have hk : AnnihilatesClosedForms (S.supportForm S.lastSeparated m i) :=
    annihilates_sum _ _ fun y _ => (hK S.lastSeparated ht m hm y _).2.1
  unfold colourEval
  exact Finset.sum_congr rfl fun e _ => bilinearEval_of_curl hk (h e)
end Final
theorem formMeansStatement_holds (hCont : responseContractionStatement) (hCoord : gaussianChainCoordinatesStatement)
    (hFl : gaussianChainFluctuationsStatement) (hRC : responseMapClosedFormsStatement)
    (hCl : classicalFormsAnnihilateClosedStatement) (hHess : stepHessianPosDefStatement)
    (hTree : treeGaugeFixingStatement) : formMeansStatement := by
  unfold gaussianChainCoordinatesStatement ForAllPoints at hCoord
  unfold gaussianChainFluctuationsStatement ForAllPoints at hFl
  unfold classicalFormsAnnihilateClosedStatement ForAllPoints at hCl
  unfold formMeansStatement ForAllPoints
  have hall := params_and (params_contraction hCont) (params_and params_admissible (params_and (params_families hRC)
    (params_and (params_families hHess) (params_and hCoord (params_and hFl hCl)))))
  refine params_mono hall fun Λ h => ?_
  obtain ⟨⟨Cw, hCw, hθ, hCon⟩, hD, hR, hH, ⟨C1, c1, X1, hc1, hX1, hCoS⟩, ⟨C2, c2, X2, hc2, hX2, hFS⟩, ⟨C3, c3, X3, hc3, hX3, hKS⟩⟩ := h
  have hLodd : Odd Λ.stepParams.side := hD.L_odd
  have hLge : 2 ^ 40 ≤ Λ.stepParams.side := hD.L_ge
  have hL1 : 1 ≤ Λ.stepParams.side := le_trans (by norm_num) hLge
  have hn0 : 4096 ≤ Λ.stepParams.n₀ := hD.n₀_ge
  have hresp : ∀ (u m : ℕ) [NeZero m], Λ.stepParams.n₀ ≤ m → ∀ A A' : TorusBond m → ℝ, (∀ p, curl A p = curl A' p) → ∀ p,
      curl (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u A) p =
        curl (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u A') p :=
    fun u m _ hm A A' h p => (hR u m (by omega)).2.2 A A' h p
  have hHd : ∀ (u n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → (trivialHessian Λ.stepParams.coupling Λ.stepParams.side u n).PosDef :=
    fun u n _ hn => hH u n hn
  refine ⟨fun q => 2 * (12 * (Real.sqrt (2 / Λ.table.lam) * (eLpNorm id (q : ENNReal) (gaussianReal 0 1)).toReal)), 1, Λ.floor,
    one_pos, le_rfl, fun S => ?_⟩
  have htop : Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := le_trans (Nat.le_mul_of_pos_left _ hL1) S.side_le
  have ht : S.lastSeparated ≤ S.data.windowLevel := by
    classical
    unfold MomentPoint.lastSeparated
    exact (Nat.findGreatest_le (P := S.data.SeparatedBelow Λ.stepParams S.β) S.data.scaleLevel).trans S.supAdmissible.scaleLevel_le
  have hGm : ∀ B : Finset (Fin Λ.k), ∀ (m : ℕ) [NeZero m], Measurable (S.formProduct S.lastSeparated m B) := fun B m _ =>
    product_measurable S _ m B
  have hGg : ∀ B : Finset (Fin Λ.k), ∀ (m : ℕ) [NeZero m], PolyGrowth (S.formProduct S.lastSeparated m B) := fun B m _ =>
    product_growth S _ m B
  have hGc : ∀ B : Finset (Fin Λ.k), ∀ (m : ℕ) [NeZero m], Λ.stepParams.n₀ ≤ m → ∀ A A' : ColourForm m,
      (∀ e p, curl (A e) p = curl (A' e) p) → S.formProduct S.lastSeparated m B A = S.formProduct S.lastSeparated m B A' :=
    fun B m _ hm A A' h => product_reads S ht (hKS S) B m hm A A' h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d n _ hd hn q hq
    have hq1 : (1 : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
    have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
    obtain ⟨θ, hθd⟩ : ∃ θ, θ = Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
    have hL0 : (0 : ℝ) < Λ.stepParams.side := by exact_mod_cast hL1
    have hθ0 : 0 ≤ θ := by
      rw [hθd]
      positivity
    have hθ1 : θ ≤ 1 / 2 := by
      rw [hθd]
      refine hθ.trans ?_
      have h1 : (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL1) (by norm_num)
      nlinarith
    have hslow : ∀ (m : ℕ) [NeZero m], IsSlowlyVaryingPair (n := m) Λ.stepParams.side (Λ.stepParams.weightRate / 8) (fun _ => 1) (fun _ => 1) :=
      fun m _ p p' => by
      have hr : 0 ≤ Λ.stepParams.weightRate := by
        have := hD.rt_pos
        show 0 ≤ Λ.table.rt / 2 ^ 10
        positivity
      have hd' : (0 : ℝ) ≤ 1 + (TorusFields.supDist (parentBlock Λ.stepParams.side p.1) p'.1 : ℝ) := by positivity
      simpa using Real.one_le_exp (by positivity)
    have hCq : ∀ (u m : ℕ) [NeZero m], 64 ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm m), Measurable X →
        weightedCurvatureNorm μ (fun _ => 1) (q : ENNReal) (fun w => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u (X w)) ≤
          ENNReal.ofReal θ * weightedCurvatureNorm μ (fun _ => 1) (q : ENNReal) X := fun u m _ hm Ω _ μ X hX => by
      rw [hθd]
      exact hCon u m hm (fun _ => 1) (fun _ => 1) (fun _ => one_pos) (fun _ => one_pos) (hslow m) Ω μ X _ hq1 hX
    have hV : 0 ≤ Real.sqrt (2 / Λ.table.lam) * (eLpNorm id (q : ENNReal) (gaussianReal 0 1)).toReal := by positivity
    have hN : ∀ (u m : ℕ) [NeZero m], Λ.stepParams.n₀ ≤ m →
        weightedCurvatureNorm (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 u m) (fun _ => 1) (q : ENNReal) extendFluctuation ≤
        ENNReal.ofReal (12 * (Real.sqrt (2 / Λ.table.lam) * (eLpNorm id (q : ENNReal) (gaussianReal 0 1)).toReal)) := fun u m _ hm => by
      refine extend_bound hq1 hV fun i => coord_bound hqt (hHd u m hm) (fun b => ?_) i
      have h1 := (hFS S).2 u m (by omega) b b
      have h2 := le_abs_self ((trivialHessian Λ.stepParams.coupling Λ.stepParams.side u m)⁻¹ b b)
      refine h2.trans (h1.trans (le_of_eq ?_))
      simp [supDist_self]
    have hsd : Λ.stepParams.n₀ ≤ n := by
      rw [hn]
      exact htop.trans (Nat.le_mul_of_pos_right _ (pow_pos hL1 _))
    have hx := noise_bound (t := S.lastSeparated) (a := Λ.stepParams.coupling) (ρA := Λ.table.ρA) (L := Λ.stepParams.side)
      (q := (q : ENNReal)) hq1 hθ0 (by positivity) (n₀ := Λ.stepParams.n₀) (by omega) hL1 hCq hN d n hsd
    refine hx.trans (ENNReal.ofReal_le_ofReal ?_)
    have hg := geom_le hθ0 hθ1 d
    nlinarith [mul_nonneg hV (by norm_num : (0:ℝ) ≤ 12)]
  · intro d n _ hn B A A' h
    exact meanOf_curl _ (fun m _ => S.formProduct S.lastSeparated m B) (hGm B) (hGg B) hL1 hresp (hGc B) d n hn A A' h
  · intro d n _ B A Rt hRt
    refine meanOf_rot (L := Λ.stepParams.side) _ (fun m _ => S.formProduct S.lastSeparated m B) (hGm B) (hGg B) hRt (fun m _ Z => ?_) d n A
    unfold MomentPoint.formProduct
    exact Finset.prod_congr rfl fun i _ => by rw [colourEval_rot _ hRt]
  · intro n _ B A
    exact meanOf_zero _ (fun m _ => S.formProduct S.lastSeparated m B) n A
  · intro d n _ B A
    exact meanOf_succ _ (fun m _ => S.formProduct S.lastSeparated m B) (hGm B) (hGg B) d n A
  · intro e d hK μ hc B
    exact chain_condMean (hB := fun u d' h μ' hc' => (((hCoS S) u d' h).2 μ' hc').2.2) (hS := (hFS S).1) hTree hLodd hL1 htop
      (by omega) hHd hresp _ (fun m _ => S.formProduct S.lastSeparated m B) (hGm B) (hGg B) (hGc B) S.lastSeparated e d hK μ hc
end FormMeans
end YangMills.Construction.MomentLaw
end
