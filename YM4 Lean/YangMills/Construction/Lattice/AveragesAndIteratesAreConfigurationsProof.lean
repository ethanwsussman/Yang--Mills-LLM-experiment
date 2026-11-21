import YangMills.Construction.Matrices.LogConjugateInverseIdentity
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Lattice.AveragesAndIteratesAreConfigurations
import YangMills.Construction.Lattice.AveragingMapIsABorelMap
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.BondwiseAveragesUnderReversal
import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Matrices.LogSeriesTracelessOnUnitDetProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Conventions Averaging
namespace PeriodicLattice
namespace GaugeFieldMembership
theorem norm_le_operatorNorm_of_charpoly_root (D : ComplexMatrix2) (ν : ℂ)
    (hroot : ν ^ 2 - ComplexMatrix2.fullTrace D * ν + D.det = 0) :
    ‖ν‖ ≤ ComplexMatrix2.operatorNorm D := by
  have hdet : (algebraMap ℂ ComplexMatrix2 ν - D).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.det_fin_two] at hroot
    simp [Matrix.algebraMap_matrix_apply]
    linear_combination hroot
  have hspec : ν ∈ spectrum ℂ D := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, hdet]
    exact not_isUnit_zero
  exact spectrum.norm_le_norm_of_mem hspec
theorem fullTrace_pow_eq_of_roots (D : ComplexMatrix2) (a b : ℂ)
    (htr : ComplexMatrix2.fullTrace D = a + b) (hdt : D.det = a * b) (n : ℕ) :
    ComplexMatrix2.fullTrace (D ^ n) = a ^ n + b ^ n ∧
      ComplexMatrix2.fullTrace (D ^ (n + 1)) = a ^ (n + 1) + b ^ (n + 1) := by
  have hcayley : D * D = (a + b) • D - (a * b) • (1 : ComplexMatrix2) := by
    rw [← htr, ← hdt]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
  induction n with
  | zero =>
    refine ⟨?_, by simpa using htr⟩
    simp [ComplexMatrix2.fullTrace, Matrix.trace_one]
    norm_num
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hpow : D ^ (n + 1 + 1) = (a + b) • D ^ (n + 1) - (a * b) • D ^ n := by
      calc D ^ (n + 1 + 1) = D ^ n * (D * D) := by rw [pow_succ, pow_succ, mul_assoc]
        _ = _ := by rw [hcayley, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, pow_succ]
    rw [hpow]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at ih ⊢
    rw [ih.1, ih.2]
    ring
theorem hasSum_inv_mul_pow_neg_log (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((n + 1 : ℂ)⁻¹) * z ^ (n + 1)) (-Complex.log (1 - z)) := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.TracelessLogSeries.hasSum_neg_log_one_sub <;> assumption
theorem summable_logSeries_terms (D : ComplexMatrix2) (hD : ‖D‖ < 1) :
    Summable fun n : ℕ => ((n + 1 : ℂ)⁻¹) • D ^ (n + 1) := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.LogConjInv.summable_logTerm <;> assumption
theorem fullTrace_logSeries_one_sub (D : ComplexMatrix2) (hdet : (1 - D).det = 1) (hD : ‖D‖ < 1) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.logSeries (1 - D)) = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (ComplexMatrix2.fullTrace D ^ 2 - 4 * D.det) (n := 2) (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = (ComplexMatrix2.fullTrace D + s) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = (ComplexMatrix2.fullTrace D - s) / 2 := ⟨_, rfl⟩
  have htr : ComplexMatrix2.fullTrace D = a + b := by rw [ha, hb]; ring
  have hdt : D.det = a * b := by rw [ha, hb]; linear_combination (1 / 4 : ℂ) * hs
  have hna : ‖a‖ < 1 :=
    lt_of_le_of_lt (norm_le_operatorNorm_of_charpoly_root D a (by rw [htr, hdt]; ring)) hD
  have hnb : ‖b‖ < 1 :=
    lt_of_le_of_lt (norm_le_operatorNorm_of_charpoly_root D b (by rw [htr, hdt]; ring)) hD
  have hprod : (1 - a) * (1 - b) = 1 := by
    have hexp : (1 - D).det = 1 - ComplexMatrix2.fullTrace D + D.det := by
      simp [Matrix.det_fin_two, Matrix.trace_fin_two, ComplexMatrix2.fullTrace]
      ring
    rw [htr, hdt] at hexp
    rw [hdet] at hexp
    linear_combination -hexp
  have htraced : HasSum (fun n : ℕ => Matrix.trace (((n + 1 : ℂ)⁻¹) • D ^ (n + 1)))
      (Matrix.trace (∑' n : ℕ, ((n + 1 : ℂ)⁻¹) • D ^ (n + 1))) :=
    (summable_logSeries_terms D hD).hasSum.map (Matrix.traceAddMonoidHom (Fin 2) ℂ)
      (continuous_id.matrix_trace)
  have hroots : HasSum (fun n : ℕ => Matrix.trace (((n + 1 : ℂ)⁻¹) • D ^ (n + 1)))
      (-Complex.log (1 - a) + -Complex.log (1 - b)) := by
    refine ((hasSum_inv_mul_pow_neg_log a hna).add
      (hasSum_inv_mul_pow_neg_log b hnb)).congr_fun ?_
    intro n
    rw [Matrix.trace_smul, smul_eq_mul]
    have hpow := (fullTrace_pow_eq_of_roots D a b htr hdt n).2
    simp only [ComplexMatrix2.fullTrace] at hpow
    rw [hpow]
    ring
  have hsum := htraced.unique hroots
  have hre : 0 < (1 - a).re := by
    have hle := Complex.re_le_norm a
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have harg : (1 - a).arg ≠ Real.pi := by
    intro hpi
    have hneg := (Complex.arg_eq_pi_iff.mp hpi).1
    linarith
  have hinv : 1 - b = (1 - a)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hlog : ComplexMatrix2.logSeries (1 - D) = -∑' n : ℕ, ((n + 1 : ℂ)⁻¹) • D ^ (n + 1) := by
    simp only [ComplexMatrix2.logSeries, sub_sub_cancel]
  rw [hlog]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_neg]
  rw [hsum, hinv, Complex.log_inv _ harg]
  ring
theorem fullTrace_logSeries_eq_zero (X : ComplexMatrix2) (hdet : X.det = 1)
    (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.logSeries X) = 0 := by
  have hzero := fullTrace_logSeries_one_sub (1 - X) (by simpa using hdet)
    (by rw [norm_sub_rev]; exact hX)
  simpa using hzero
theorem one_mem_complexGaugeGroup : (1 : ComplexMatrix2) ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.one_mem_gaugeGroup <;> assumption
theorem mul_mem_complexGaugeGroup {A B : ComplexMatrix2} (hA : A ∈ complexGaugeGroup)
    (hB : B ∈ complexGaugeGroup) : A * B ∈ complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p592 <;> assumption
theorem inv_mem_complexGaugeGroup {A : ComplexMatrix2} (hA : A ∈ complexGaugeGroup) :
    A⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem pathHolonomy_mem_complexGaugeGroup {L m : ℕ} {j : ℤ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, U b ∈ complexGaugeGroup) (γ : List (Bond L m j)) :
    pathHolonomy U γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.pathHolonomy_mem_complexGaugeGroup <;> assumption
theorem complexLogMean_mem (hMean : ComplexLogMeanOfSmallFamilies) {ι : Type*} [Fintype ι]
    [Nonempty ι] (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hdiam : ComplexMatrix2.familyDiameter V < centreOfMassDiameter) :
    complexLogMean V ∈ complexGaugeGroup := by
  obtain ⟨-, -, -, hfam, -⟩ := hMean
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hsmall : V ∘ e ∈ smallComplexFamilies (Fintype.card ι) := by
    refine ⟨fun i => hV _, ?_⟩
    have hsame : ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by
      unfold ComplexMatrix2.familyDiameter
      exact (Equiv.prodCongr e e).surjective.iSup_comp
        (fun p : ι × ι => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
    rwa [hsame]
  obtain ⟨W, ⟨⟨hWG, hWn, hWs⟩, i, hi⟩, -⟩ := (hfam _ hcard).existsUnique _ hsmall
  have hex : ∃ W, ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
      ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance := by
    refine ⟨W, ⟨hWG, fun k => ?_, ?_⟩, e i, hi⟩
    · simpa using hWn (e.symm k)
    · rw [← hWs]
      exact (Equiv.sum_comp e (fun k => ComplexMatrix2.logSeries (V k * W⁻¹))).symm
  exact (Classical.epsilon_spec hex).1.1
instance axisOrdering_nonempty {L m : ℕ} {j j' : ℤ} (y : Site L m j) (x : Site L m j') :
    Nonempty (AxisOrdering y x) :=
  ⟨(Finset.equivFin _).symm⟩
theorem complexMeanContourHolonomy_mem (hMean : ComplexLogMeanOfSmallFamilies) {L m : ℕ}
    {j j' : ℤ} {U : Bond L m j' → ComplexMatrix2} (hU : ∀ b, U b ∈ complexGaugeGroup)
    (y : Site L m j) (x : Site L m j')
    (hdiam : ComplexMatrix2.familyDiameter (contourHolonomies U y x) < centreOfMassDiameter) :
    complexMeanContourHolonomy U y x ∈ complexGaugeGroup :=
  complexLogMean_mem hMean _ (fun _ => pathHolonomy_mem_complexGaugeGroup hU _) hdiam
theorem complexBlockAverageOnPositive_mem (hDouble : DoubleBlockStructure.Statement)
    (hMean : ComplexLogMeanOfSmallFamilies) (hExp : ComplexMatrix2.ExpLogEstimates)
    {L m K n : ℕ} (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (c : BondAtLevel L m K (n + 1)) {U : BondAtLevel L m K n → ComplexMatrix2}
    (hU : ∀ b, U b ∈ complexGaugeGroup) (hdom : U ∈ complexAveragingDomainNearOne c) :
    complexBlockAverageOnPositive U c ∈ complexGaugeGroup := by
  obtain ⟨-, -, -, -, -, hdetExp, -⟩ := hExp
  obtain ⟨⟨-, hSource, hTarget⟩, hNear⟩ := hdom
  have hCross := (hDouble L m K n hL hm hn c).2.2.1.1
  have hDefect : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      complexCrossingDefect U c x ∈ complexGaugeGroup := by
    intro x hx
    have hfirst := complexMeanContourHolonomy_mem hMean hU c.source x (hSource x hx)
    have hsecond := complexMeanContourHolonomy_mem hMean hU c.target (shiftAcross c x)
      (hTarget _ (hCross x hx).1)
    exact mul_mem_complexGaugeGroup (mul_mem_complexGaugeGroup (mul_mem_complexGaugeGroup hfirst
      (pathHolonomy_mem_complexGaugeGroup hU _)) (inv_mem_complexGaugeGroup hsecond))
      (inv_mem_complexGaugeGroup (pathHolonomy_mem_complexGaugeGroup hU _))
  have hSum : ComplexMatrix2.fullTrace (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
      ComplexMatrix2.logSeries (complexCrossingDefect U c x)) = 0 :=
    finsum_mem_induction (fun M : ComplexMatrix2 => ComplexMatrix2.fullTrace M = 0)
      (by simp [ComplexMatrix2.fullTrace])
      (fun A B hA hB => by
        simp only [ComplexMatrix2.fullTrace] at hA hB ⊢
        rw [Matrix.trace_add, hA, hB, add_zero])
      (fun x hx => fullTrace_logSeries_eq_zero _ (hDefect x hx) (hNear x hx))
  change (complexBlockAverageOnPositive U c).det = 1
  unfold complexBlockAverageOnPositive
  have hTransport : (parallelTransport U c).det = 1 := pathHolonomy_mem_complexGaugeGroup hU _
  rw [Matrix.det_mul, hTransport, mul_one, hdetExp]
  simp only [ComplexMatrix2.fullTrace] at hSum ⊢
  rw [Matrix.trace_smul, hSum]
  simp
theorem extendByOne_mem_gaugeFieldsAtLevel (hDouble : DoubleBlockStructure.Statement)
    {L m K j : ℕ} (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < K)
    {S : Set (BondAtLevel L m K j)} {U : BondAtLevel L m K j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup S U) (c : BondAtLevel L m K (j + 1))
    (hc : (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) ⊆ S) :
    onSetElseOne (bondsInDoubleBlock c) U ∈ gaugeFieldsAtLevel L m K j := by
  have hclosed : IsReversalClosed (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) :=
    (hDouble L m K j hL hm hj c).1.2.2.1
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K j))
    · simp only [onSetElseOne, if_pos hb]
      exact hU.1 b (hc hb)
    · simp only [onSetElseOne, if_neg hb]
      exact Submonoid.one_mem _
  · by_cases hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K j))
    · simp only [onSetElseOne, if_pos hb, if_pos (hclosed b hb)]
      exact hU.2 b (hc hb)
    · have hback : b.opposite.opposite = b := Bond.ext rfl rfl
      have hb' : b.opposite ∉ (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) := by
        intro hmem
        have hmem' := hclosed _ hmem
        rw [hback] at hmem'
        exact hb hmem'
      simp [onSetElseOne, hb, hb']
theorem eq_inv_of_mul_eq_one_matrix {A B : ComplexMatrix2} (h : A * B = 1) : B = A⁻¹ :=
  (Matrix.inv_eq_right_inv h).symm
theorem partialBlockAverage_isValued (hDouble : DoubleBlockStructure.Statement)
    (hRev : PartialBlockAverageReversalInverse) (hBorel : BlockAverageIsBorelMap)
    {L m K j : ℕ} (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < K)
    {S : Set (BondAtLevel L m K j)} (hS : IsReversalClosed S)
    {U : BondAtLevel L m K j → ComplexMatrix2} (hU : IsGaugeField compactGaugeGroup S U) :
    (realPartialBlockAverage (smoothingRadius L)
      (⟨S, U⟩ : PartialGaugeField L m (levelDepth K j)) :
      PartialGaugeField L m (levelDepth K (j + 1))).IsValuedOnSymmetricSupport
        compactGaugeGroup := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hj
  obtain ⟨hcl, hinv⟩ := (hRev L m K hL hm hK j hj S hS).1 U hU
  refine ⟨hcl, fun c hc => ?_, fun c hc => eq_inv_of_mul_eq_one_matrix (hinv c hc)⟩
  obtain ⟨hmaps, -⟩ := hBorel ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ j hj
  have hext := extendByOne_mem_gaugeFieldsAtLevel hDouble hL hm hj hU c hc
  exact (hmaps hext).1 c (mem_univ c)
theorem complexPartialBlockAverage_isValued (hDouble : DoubleBlockStructure.Statement)
    (hRev : PartialBlockAverageReversalInverse) (hMean : ComplexLogMeanOfSmallFamilies)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    {L m K j : ℕ} (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < K)
    {S : Set (BondAtLevel L m K j)} (hS : IsReversalClosed S)
    {U : BondAtLevel L m K j → ComplexMatrix2} (hU : IsGaugeField complexGaugeGroup S U) :
    (complexPartialBlockAverage (⟨S, U⟩ : PartialGaugeField L m (levelDepth K j)) :
      PartialGaugeField L m (levelDepth K (j + 1))).IsValuedOnSymmetricSupport
        complexGaugeGroup := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hj
  obtain ⟨hcl, hinv⟩ := (hRev L m K hL hm hK j hj S hS).2 U hU
  refine ⟨hcl, fun c hc => ?_, fun c hc => eq_inv_of_mul_eq_one_matrix (hinv c hc)⟩
  obtain ⟨hsub, hdom⟩ := hc
  have hext : ∀ b, onSetElseOne (bondsInDoubleBlock c) U b ∈ complexGaugeGroup := by
    intro b
    by_cases hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K j))
    · simp only [onSetElseOne, if_pos hb]
      exact hU.1 b (hsub hb)
    · simp only [onSetElseOne, if_neg hb]
      exact one_mem_complexGaugeGroup
  change complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) U) c ∈ complexGaugeGroup
  by_cases hpos : c.IsPositivelyOriented
  · have hcp : c.positivelyOriented = c := by simp [Bond.positivelyOriented, hpos]
    rw [hcp] at hdom
    simp only [complexBlockAverage, if_pos hpos]
    exact complexBlockAverageOnPositive_mem hDouble hMean hExp hL hm hj c hext hdom
  · have hcp : c.positivelyOriented = c.opposite := by simp [Bond.positivelyOriented, hpos]
    rw [hcp] at hdom
    simp only [complexBlockAverage, if_neg hpos]
    exact inv_mem_complexGaugeGroup
      (complexBlockAverageOnPositive_mem hDouble hMean hExp hL hm hj c.opposite hext hdom)
end GaugeFieldMembership
open GaugeFieldMembership in
theorem averagesAndIteratesAreGaugeFields
    (hDouble : DoubleBlockStructure.Statement)
    (hRev : PartialBlockAverageReversalInverse)
    (hBorel : BlockAverageIsBorelMap)
    (hMean : ComplexLogMeanOfSmallFamilies)
    (hExp : ComplexMatrix2.ExpLogEstimates) :
    AveragesAndIteratesAreGaugeFields := by
  intro L m K j hL hm hj S hS
  refine ⟨fun U c hU hc => ⟨extendByOne_mem_gaugeFieldsAtLevel hDouble hL hm hj hU c hc,
    fun b hb => ?_⟩,
    fun U hU => partialBlockAverage_isValued hDouble hRev hBorel hL hm hj hS hU,
    fun U hU => complexPartialBlockAverage_isValued hDouble hRev hMean hExp hL hm hj hS hU,
    fun i hi => ⟨?_, ?_⟩⟩
  · simp only [onSetElseOne, if_pos hb]
  · intro U hU
    induction i with
    | zero => exact ⟨hS, hU⟩
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact partialBlockAverage_isValued hDouble hRev hBorel hL hm (by omega) h1 h2
  · intro U hU
    induction i with
    | zero => exact ⟨hS, hU⟩
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact complexPartialBlockAverage_isValued hDouble hRev hMean hExp hL hm (by omega) h1 h2
end PeriodicLattice
end YangMills.Construction
