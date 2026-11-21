import YangMills.Construction.Towers.TheMassiveFunctionalIsGaugeInvariantProof
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.PeriodicOperators.TheFibresAtTheTopOfATowerProof
import YangMills.Construction.Towers.AbelianOperatorsAreLocalAndSelfAdjointProof
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Towers.NormOfTheColourCoefficientsProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction
open PeriodicOperators
namespace Tower
namespace UnitLatticeL2.L2Steps
theorem pauliFamily_combination_injective {c d : Fin 3 → ℂ}
    (h : ∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a =
      ∑ a, d a • Matrices.ComplexMatrix2.pauliFamily a) : c = d := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.pauliFamily_sum_injective <;> assumption
theorem exists_pauliFamily_combination {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∃ c : Fin 3 → ℂ, X = ∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a := by
  have ht : Matrix.trace X = 0 := hX
  rw [Matrix.trace_fin_two] at ht
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  refine ⟨![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0], ?_⟩
  rw [Matrices.ComplexMatrix2.sum_smul_pauliFamily]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    field_simp
    ring
  · simp
    field_simp
    ring
  · simp
    linear_combination ht
theorem eq_sum_pauliCoeffs_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeffs X a • Matrices.ComplexMatrix2.pauliFamily a :=
  Classical.epsilon_spec (exists_pauliFamily_combination hX)
theorem pauliCoeffs_combination (c : Fin 3 → ℂ) :
    pauliCoeffs (∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a) = c := by
  have h : (∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a) =
      ∑ a, pauliCoeffs (∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a) a •
        Matrices.ComplexMatrix2.pauliFamily a :=
    Classical.epsilon_spec (p := fun d : Fin 3 → ℂ =>
      (∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a) =
        ∑ a, d a • Matrices.ComplexMatrix2.pauliFamily a) ⟨c, rfl⟩
  exact (pauliFamily_combination_injective h).symm
theorem combination_mem_traceless (c : Fin 3 → ℂ) :
    ∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem halfTraceProduct_combinations (x y : Fin 3 → ℂ) :
    halfTraceProduct (∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a)
      (∑ a, y a • Matrices.ComplexMatrix2.pauliFamily a) = ∑ a, conj (x a) * y a := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.halfTrace_conjTranspose_sum_mul_sum <;> assumption
theorem adjointMatrix_combination (c : Fin 3 → ℂ) :
    Matrices.ComplexMatrix2.adjointMatrix (∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a) =
      ∑ a, conj (c a) • Matrices.ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.adjointMatrix_sum_smul <;> assumption
theorem halfTraceProduct_eq_sum {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless) :
    halfTraceProduct X Y = ∑ a, conj (pauliCoeffs X a) * pauliCoeffs Y a := by
  have h := halfTraceProduct_combinations (pauliCoeffs X) (pauliCoeffs Y)
  rwa [← eq_sum_pauliCoeffs_smul hX, ← eq_sum_pauliCoeffs_smul hY] at h
theorem conj_mul_self_eq_normSq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']
  push_cast
  rfl
theorem halfTraceProduct_self_re {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    (halfTraceProduct X X).re = ∑ a, ‖pauliCoeffs X a‖ ^ 2 := by
  rw [halfTraceProduct_eq_sum hX hX, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conj_mul_self_eq_normSq, Complex.ofReal_re]
theorem pauliCoeffs_adjointMatrix {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    pauliCoeffs (Matrices.ComplexMatrix2.adjointMatrix X) = fun a => conj (pauliCoeffs X a) := by
  have h := adjointMatrix_combination (pauliCoeffs X)
  rw [← eq_sum_pauliCoeffs_smul hX] at h
  rw [h, pauliCoeffs_combination]
theorem adjointMatrix_mem_traceless {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.adjointMatrix X ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance.conjTranspose_mem_traceless <;> assumption
theorem halfTraceProduct_smul_smul (c c' : ℂ) (X : Matrices.ComplexMatrix2) :
    halfTraceProduct (c • X) (c' • X) =
      (conj c * c') * Matrices.ComplexMatrix2.halfTrace (Matrices.ComplexMatrix2.adjointMatrix X * X) := by
  simp only [halfTraceProduct, Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.adjointMatrix,
    Matrices.ComplexMatrix2.fullTrace, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.star_def]
  ring
theorem summable_sq_norm_lp {J : Type} (v : lp (fun _ : J => ℂ) 2) : Summable fun i => ‖v i‖ ^ 2 := by
  have h := (lp.memℓp v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using h
theorem memℓp_two_of_summable_sq {J : Type} {u : J → ℂ} (h : Summable fun i => ‖u i‖ ^ 2) :
    Memℓp u 2 :=
  memℓp_gen (by simpa using h)
theorem finset_sum_sq_le_norm_sq {J : Type} (f : lp (fun _ : J => ℂ) 2) (s : Finset J) :
    ∑ i ∈ s, ‖f i‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f s
  simpa using h
theorem summable_prod_fin_three_iff {σ : Type} {g : Fin 3 × σ → ℝ} (hg : ∀ ι, 0 ≤ g ι) :
    Summable g ↔ Summable fun s => ∑ a, g (a, s) := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.summable_fin_three_prod_iff <;> assumption
theorem tsum_prod_fin_three {σ : Type} {g : Fin 3 × σ → ℂ} (hg : Summable g) :
    ∑' ι, g ι = ∑' s, ∑ a, g (a, s) := by
  have hs : Summable fun c : σ × Fin 3 => g (Equiv.prodComm σ (Fin 3) c) :=
    (Equiv.prodComm σ (Fin 3)).summable_iff.2 hg
  rw [← (Equiv.prodComm σ (Fin 3)).tsum_eq g, hs.tsum_prod]
  simp only [Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk, tsum_fintype]
theorem summable_norm_conj_mul {J : Type} {u w : J → ℂ} (hu : Summable fun i => ‖u i‖ ^ 2)
    (hw : Summable fun i => ‖w i‖ ^ 2) : Summable fun i => ‖conj (u i) * w i‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (hu.add hw)
  simp only [norm_mul, RCLike.norm_conj]
  nlinarith [sq_nonneg (‖u i‖ - ‖w i‖), sq_nonneg (‖u i‖), sq_nonneg (‖w i‖)]
section Fields
variable {σ : Type}
theorem isL2Traceless_iff {f : σ → Matrices.ComplexMatrix2}
    (hf : ∀ s, f s ∈ Matrices.ComplexMatrix2.traceless) :
    IsL2Traceless f ↔ Summable fun ι => ‖coordAt f ι‖ ^ 2 := by
  rw [summable_prod_fin_three_iff (fun _ => by positivity)]
  have h : (fun i => (halfTraceProduct (f i) (f i)).re) =
      fun s => ∑ a, ‖pauliCoeffs (f s) a‖ ^ 2 :=
    funext fun s => halfTraceProduct_self_re (hf s)
  unfold IsL2Traceless
  rw [h]
  exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
theorem hermitianInner_eq_tsum {f f' : σ → Matrices.ComplexMatrix2} (hf : IsL2Traceless f)
    (hf' : IsL2Traceless f') :
    hermitianInner f f' = ∑' ι, conj (coordAt f ι) * coordAt f' ι := by
  have hs : Summable fun ι => conj (coordAt f ι) * coordAt f' ι :=
    (summable_norm_conj_mul ((isL2Traceless_iff hf.1).1 hf)
      ((isL2Traceless_iff hf'.1).1 hf')).of_norm
  rw [tsum_prod_fin_three hs]
  exact tsum_congr fun s => halfTraceProduct_eq_sum (hf.1 s) (hf'.1 s)
theorem coordAt_ofCoords (v : Fin 3 × σ → ℂ) (ι : Fin 3 × σ) :
    coordAt (ofCoords v) ι = v ι :=
  congrFun (pauliCoeffs_combination fun a => v (a, ι.2)) ι.1
theorem isL2Traceless_ofCoords (v : L2Field σ) : IsL2Traceless (ofCoords v) := by
  have hmem : ∀ s, ofCoords v s ∈ Matrices.ComplexMatrix2.traceless := fun s =>
    combination_mem_traceless _
  refine (isL2Traceless_iff hmem).2 ?_
  simp only [coordAt_ofCoords]
  exact summable_sq_norm_lp v
theorem coordsIsometry : CoordsIsometry σ := by
  refine ⟨fun f hf => isL2Traceless_iff hf, fun f f' hf hf' => ⟨?_, hermitianInner_eq_tsum hf hf'⟩,
    fun v => ⟨isL2Traceless_ofCoords v, coordAt_ofCoords v⟩, fun f hf => ?_,
    fun c v v' => ⟨?_, ?_⟩, fun v v' => ?_⟩
  · exact summable_norm_conj_mul ((isL2Traceless_iff hf.1).1 hf) ((isL2Traceless_iff hf'.1).1 hf')
  · refine ⟨⟨coordAt f, memℓp_two_of_summable_sq ((isL2Traceless_iff hf.1).1 hf)⟩, ?_⟩
    funext s
    exact (eq_sum_pauliCoeffs_smul (hf.1 s)).symm
  · funext s
    simp [ofCoords, add_smul, Finset.sum_add_distrib]
  · funext s
    simp [ofCoords, Finset.smul_sum, mul_smul]
  · rw [hermitianInner_eq_tsum (isL2Traceless_ofCoords v) (isL2Traceless_ofCoords v'),
      lp.inner_eq_tsum]
    refine tsum_congr fun ι => ?_
    rw [coordAt_ofCoords, coordAt_ofCoords]
    simp [RCLike.inner_apply, mul_comm]
theorem starProperties : StarProperties σ := by
  intro f hf
  have hmem : ∀ s, Matrices.ComplexMatrix2.adjointMatrix (f s) ∈ Matrices.ComplexMatrix2.traceless :=
    fun s => adjointMatrix_mem_traceless (hf.1 s)
  have hval : ∀ ι, coordAt (fieldStar f) ι = conj (coordAt f ι) := fun ι =>
    congrFun (pauliCoeffs_adjointMatrix (hf.1 ι.2)) ι.1
  refine ⟨hmem, hval, ?_, ?_⟩
  · have hmem' : ∀ s, fieldStar f s ∈ Matrices.ComplexMatrix2.traceless := hmem
    refine (isL2Traceless_iff hmem').2 ?_
    simp only [hval, RCLike.norm_conj]
    exact (isL2Traceless_iff hf.1).1 hf
  · unfold fieldNorm hermitianInner
    have h : ∀ s, halfTraceProduct (fieldStar f s) (fieldStar f s) =
        halfTraceProduct (f s) (f s) := by
      intro s
      change halfTraceProduct (Matrices.ComplexMatrix2.adjointMatrix (f s))
        (Matrices.ComplexMatrix2.adjointMatrix (f s)) = _
      rw [halfTraceProduct_eq_sum (hmem s) (hmem s), halfTraceProduct_eq_sum (hf.1 s) (hf.1 s),
        pauliCoeffs_adjointMatrix (hf.1 s)]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [mul_comm]
    simp only [h]
theorem scalarMultipleInner : ScalarMultipleInner σ := by
  intro X hX s s' hs hs'
  have hsq : ∀ t : σ → ℂ, Summable (fun i => ‖t i‖ ^ 2) → IsL2Traceless fun i => t i • X := by
    intro t ht
    refine ⟨fun i => Matrices.ComplexMatrix2.traceless.smul_mem _ hX, ?_⟩
    have h : ∀ i, (halfTraceProduct (t i • X) (t i • X)).re =
        ‖t i‖ ^ 2 *
          (Matrices.ComplexMatrix2.halfTrace (Matrices.ComplexMatrix2.adjointMatrix X * X)).re := by
      intro i
      rw [halfTraceProduct_smul_smul, conj_mul_self_eq_normSq, Complex.re_ofReal_mul]
    simp only [h]
    exact ht.mul_right _
  refine ⟨hsq s hs, hsq s' hs', ?_⟩
  unfold hermitianInner
  simp only [halfTraceProduct_smul_smul]
  rw [tsum_mul_right, mul_comm]
end Fields
section Kernels
variable {J : Type}
theorem inner_basisVec (ι : J) (g : lp (fun _ : J => ℂ) 2) : inner ℂ (basisVec ι) g = g ι := by
  classical
  unfold basisVec
  rw [lp.inner_single_left]
  simp [RCLike.inner_apply]
theorem norm_basisVec (ι : J) : ‖basisVec ι‖ = 1 := by
  classical
  unfold basisVec
  rw [lp.norm_single (by norm_num)]
  simp
theorem matrixEntryProperties : MatrixEntryProperties J := by
  intro S
  have hentry : ∀ ι' ι, matrixEntry S ι' ι = inner ℂ (basisVec ι') (S (basisVec ι)) :=
    fun _ _ => (inner_basisVec _ _).symm
  refine ⟨fun ι' ι => ⟨hentry _ _, ?_⟩, fun f ι' => ?_⟩
  · calc ‖matrixEntry S ι' ι‖ ≤ ‖S (basisVec ι)‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖S‖ * ‖basisVec ι‖ := S.le_opNorm _
      _ = ‖S‖ := by rw [norm_basisVec, mul_one]
  · have hw : ∀ ι, conj ((ContinuousLinearMap.adjoint S (basisVec ι')) ι) = matrixEntry S ι' ι := by
      intro ι
      rw [hentry, ← inner_basisVec ι (ContinuousLinearMap.adjoint S (basisVec ι')),
        ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
    have hs := lp.hasSum_inner (𝕜 := ℂ) (ContinuousLinearMap.adjoint S (basisVec ι')) f
    have hterm : ∀ ι, inner ℂ ((ContinuousLinearMap.adjoint S (basisVec ι')) ι) (f ι) =
        matrixEntry S ι' ι * f ι := by
      intro ι
      rw [← hw]
      simp [RCLike.inner_apply, mul_comm]
    have hval : inner ℂ (ContinuousLinearMap.adjoint S (basisVec ι')) f = S f ι' := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact inner_basisVec _ _
    simp only [hterm, hval] at hs
    exact ⟨summable_norm_iff.2 hs.summable, hs.tsum_eq.symm⟩
theorem euclidNormVec_sub_comm (x y : InfiniteLattice.AmbientSpace) :
    TorusMetric.euclidNormVec (x - y) = TorusMetric.euclidNormVec (y - x) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem boundedKernelOperator [Nonempty J] (place : J → InfiniteLattice.AmbientSpace)
    (hcount : ∀ ι', {ι | TorusMetric.euclidNormVec (place ι - place ι') ≤ 2}.Finite ∧
      {ι | TorusMetric.euclidNormVec (place ι - place ι') ≤ 2}.ncard ≤ 12 * 5 ^ 4) :
    BoundedKernelOperator place := by
  classical
  intro C M hC hM
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (Classical.arbitrary J) (Classical.arbitrary J))
  let A : J → Finset J := fun ι' => (hcount ι').1.toFinset
  have hAcard : ∀ ι', (A ι').card ≤ 12 * 5 ^ 4 := fun ι' => by
    have h := (hcount ι').2
    rwa [Set.ncard_eq_toFinset_card _ (hcount ι').1] at h
  have hAcardR : ∀ ι', ((A ι').card : ℝ) ≤ 12 * 5 ^ 4 := fun ι' => by exact_mod_cast hAcard ι'
  have hAmem : ∀ ι' ι, ι ∈ A ι' ↔
      TorusMetric.euclidNormVec (place ι - place ι') ≤ 2 := fun ι' ι => by simp [A]
  have hsymm : ∀ ι' ι, ι ∈ A ι' ↔ ι' ∈ A ι := fun ι' ι => by
    rw [hAmem, hAmem, euclidNormVec_sub_comm]
  have hzero : ∀ ι' ι, ι ∉ A ι' → M ι' ι = 0 := fun ι' ι h =>
    hM ι' ι fun hd => h ((hsymm ι' ι).2 ((hAmem ι ι').2 hd))
  let val : lp (fun _ : J => ℂ) 2 → J → ℂ := fun f ι' => ∑ ι ∈ A ι', M ι' ι * f ι
  have hrow : ∀ (f : lp (fun _ : J => ℂ) 2) ι',
      ‖val f ι'‖ ^ 2 ≤ 12 * 5 ^ 4 * C ^ 2 * ∑ ι ∈ A ι', ‖f ι‖ ^ 2 := by
    intro f ι'
    have h1 : ‖val f ι'‖ ≤ C * ∑ ι ∈ A ι', ‖f ι‖ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _ _) (norm_nonneg _)
    have h2 : (∑ ι ∈ A ι', ‖f ι‖) ^ 2 ≤ 12 * 5 ^ 4 * ∑ ι ∈ A ι', ‖f ι‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right (hAcardR ι')
        (Finset.sum_nonneg fun _ _ => by positivity))
    calc ‖val f ι'‖ ^ 2 ≤ (C * ∑ ι ∈ A ι', ‖f ι‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C ^ 2 * (∑ ι ∈ A ι', ‖f ι‖) ^ 2 := by ring
      _ ≤ C ^ 2 * (12 * 5 ^ 4 * ∑ ι ∈ A ι', ‖f ι‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 12 * 5 ^ 4 * C ^ 2 * ∑ ι ∈ A ι', ‖f ι‖ ^ 2 := by ring
  have hfin : ∀ (f : lp (fun _ : J => ℂ) 2) (F : Finset J),
      ∑ ι' ∈ F, ‖val f ι'‖ ^ 2 ≤ (12 * 5 ^ 4 * C) ^ 2 * ‖f‖ ^ 2 := by
    intro f F
    let G : Finset J := F.biUnion A
    have hswap : ∑ ι' ∈ F, ∑ ι ∈ A ι', ‖f ι‖ ^ 2 =
        ∑ ι ∈ G, ∑ ι' ∈ F, if ι ∈ A ι' then ‖f ι‖ ^ 2 else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ι' hι' => ?_
      rw [Finset.sum_ite_mem]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      rw [Finset.inter_eq_right.2]
      exact Finset.subset_biUnion_of_mem A hι'
    have hcol : ∀ ι, ∑ ι' ∈ F, (if ι ∈ A ι' then ‖f ι‖ ^ 2 else 0) ≤ 12 * 5 ^ 4 * ‖f ι‖ ^ 2 := by
      intro ι
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hsub : F.filter (fun ι' => ι ∈ A ι') ⊆ A ι := fun ι' h =>
        (hsymm ι' ι).1 (Finset.mem_filter.1 h).2
      exact (by exact_mod_cast Finset.card_le_card hsub : (((F.filter fun ι' => ι ∈ A ι').card : ℕ) : ℝ) ≤ (A ι).card).trans (hAcardR ι)
    have hsum : ∑ ι' ∈ F, ∑ ι ∈ A ι', ‖f ι‖ ^ 2 ≤ 12 * 5 ^ 4 * ‖f‖ ^ 2 := by
      rw [hswap]
      refine (Finset.sum_le_sum fun ι _ => hcol ι).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (finset_sum_sq_le_norm_sq f G) (by positivity)
    calc ∑ ι' ∈ F, ‖val f ι'‖ ^ 2
        ≤ ∑ ι' ∈ F, 12 * 5 ^ 4 * C ^ 2 * ∑ ι ∈ A ι', ‖f ι‖ ^ 2 :=
          Finset.sum_le_sum fun ι' _ => hrow f ι'
      _ = 12 * 5 ^ 4 * C ^ 2 * ∑ ι' ∈ F, ∑ ι ∈ A ι', ‖f ι‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 12 * 5 ^ 4 * C ^ 2 * (12 * 5 ^ 4 * ‖f‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (12 * 5 ^ 4 * C) ^ 2 * ‖f‖ ^ 2 := by ring
  have hmem : ∀ f : lp (fun _ : J => ℂ) 2, Memℓp (val f) 2 := fun f =>
    memℓp_gen' (C := (12 * 5 ^ 4 * C) ^ 2 * ‖f‖ ^ 2) (fun F => by simpa using hfin f F)
  let T₀ : lp (fun _ : J => ℂ) 2 →ₗ[ℂ] lp (fun _ : J => ℂ) 2 :=
    { toFun := fun f => ⟨val f, hmem f⟩
      map_add' := fun f g => by
        refine lp.ext (funext fun ι' => ?_)
        change val (f + g) ι' = val f ι' + val g ι'
        simp [val, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        refine lp.ext (funext fun ι' => ?_)
        change val (c • f) ι' = c * val f ι'
        simp only [val, Finset.mul_sum, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hbound : ∀ f, ‖T₀ f‖ ≤ 12 * 5 ^ 4 * C * ‖f‖ := by
    intro f
    refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun F => ?_
    have h := hfin f F
    have h' : ∑ ι' ∈ F, ‖(T₀ f) ι'‖ ^ 2 ≤ (12 * 5 ^ 4 * C * ‖f‖) ^ 2 := by
      refine le_of_le_of_eq h ?_
      ring
    simpa using h'
  let T := T₀.mkContinuous (12 * 5 ^ 4 * C) hbound
  have hT : ∀ (f : lp (fun _ : J => ℂ) 2) ι', T f ι' = ∑' ι, M ι' ι * f ι := by
    intro f ι'
    refine Eq.symm (tsum_eq_sum fun ι h => ?_)
    rw [hzero _ _ h, zero_mul]
  refine ⟨T, fun f ι' => ?_, LinearMap.mkContinuous_norm_le _ (by positivity) hbound, ?_⟩
  · have hsub : {ι | M ι' ι * f ι ≠ 0} ⊆ (A ι' : Set J) := fun ι h => by
      by_contra hn
      exact h (by rw [hzero _ _ hn, zero_mul])
    refine ⟨(A ι').finite_toSet.subset hsub, ?_, hT f ι'⟩
    refine (Set.ncard_le_ncard hsub (A ι').finite_toSet).trans ?_
    rw [Set.ncard_coe_finset]
    exact hAcard ι'
  · intro hconj
    have hE := matrixEntryProperties (J := J)
    have hTentry : ∀ ι' ι, matrixEntry T ι' ι = M ι' ι := by
      intro ι' ι
      unfold matrixEntry
      rw [hT, tsum_eq_single ι]
      · simp [basisVec]
      · intro κ hκ
        simp [basisVec, lp.single_apply, hκ]
    have h1 : ∀ ι' ι, matrixEntry (opAdjoint T) ι' ι = matrixEntry T ι' ι := by
      intro ι' ι
      rw [((hE (opAdjoint T)).1 ι' ι).1, hTentry, hconj ι ι']
      change inner ℂ (basisVec ι') (ContinuousLinearMap.adjoint T (basisVec ι)) = _
      rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, ← hTentry,
        ((hE T).1 ι ι').1]
    refine ContinuousLinearMap.ext fun f => lp.ext (funext fun ι' => ?_)
    rw [((hE (opAdjoint T)).2 f ι').2, ((hE T).2 f ι').2]
    exact tsum_congr fun ι => by rw [h1]
end Kernels
theorem ncard_near_le {a : ℝ} (ha : a = 1) {J K : Type} [Fintype K] (hK : Fintype.card K ≤ 12)
    (place : J → InfiniteLattice.LatticePoint a) (colour : J → K)
    (hinj : ∀ ι ι', place ι = place ι' → colour ι = colour ι' → ι = ι')
    (y : InfiniteLattice.LatticePoint a) :
    {ι | TorusMetric.euclidNormVec ((place ι : InfiniteLattice.AmbientSpace) - y) ≤ 2}.Finite ∧
      {ι | TorusMetric.euclidNormVec ((place ι : InfiniteLattice.AmbientSpace) - y) ≤ 2}.ncard ≤
        12 * 5 ^ 4 := by
  classical
  subst ha
  obtain ⟨m, hm⟩ := y.2
  choose n hn using fun ι => (place ι).2
  let target : Finset (K × (Fin 4 → ℤ)) :=
    Finset.univ ×ˢ Fintype.piFinset fun _ => Finset.Icc (-2 : ℤ) 2
  let φ : J → K × (Fin 4 → ℤ) := fun ι => (colour ι, fun μ => n ι μ - m μ)
  have hmaps : ∀ ι ∈ {ι | TorusMetric.euclidNormVec ((place ι : InfiniteLattice.AmbientSpace) - y) ≤ 2},
      φ ι ∈ target := by
    intro ι hι
    have hsq : ∑ μ, (((place ι : InfiniteLattice.AmbientSpace) - y) μ) ^ 2 ≤ 2 ^ 2 :=
      (Real.sqrt_le_iff.1 hι).2
    simp only [target, φ, Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_Icc]
    intro μ
    have h1 : (((place ι : InfiniteLattice.AmbientSpace) - y) μ) ^ 2 ≤
        ∑ μ, (((place ι : InfiniteLattice.AmbientSpace) - y) μ) ^ 2 :=
      Finset.single_le_sum (f := fun μ => (((place ι : InfiniteLattice.AmbientSpace) - y) μ) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
    have h2 : ((place ι : InfiniteLattice.AmbientSpace) - y) μ = ((n ι μ - m μ : ℤ) : ℝ) := by
      simp [hn, hm]
    rw [h2] at h1
    have h3 : |((n ι μ - m μ : ℤ) : ℝ)| ≤ 2 := abs_le_of_sq_le_sq (by linarith) (by norm_num)
    have h4 := abs_le.1 h3
    constructor
    · have := h4.1
      exact_mod_cast this
    · have := h4.2
      exact_mod_cast this
  have hinjOn : Set.InjOn φ
      {ι | TorusMetric.euclidNormVec ((place ι : InfiniteLattice.AmbientSpace) - y) ≤ 2} := by
    intro ι _ ι' _ h
    have hc : colour ι = colour ι' := congrArg Prod.fst h
    have hd : (fun μ => n ι μ - m μ) = fun μ => n ι' μ - m μ := congrArg Prod.snd h
    refine hinj ι ι' (Subtype.ext (funext fun μ => ?_)) hc
    have : n ι μ = n ι' μ := by simpa using congrFun hd μ
    rw [hn, hn, this]
  refine ⟨Set.Finite.of_injOn hmaps hinjOn target.finite_toSet, ?_⟩
  refine (Set.ncard_le_ncard_of_injOn φ hmaps hinjOn target.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
  simp only [target, Finset.card_product, Finset.card_univ, Fintype.card_piFinset, Int.card_Icc]
  simpa using Nat.mul_le_mul_right _ hK
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by simp [meshAt]
theorem axisStep_injective {a : ℝ} (ha : a = 1) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.PeriodicOperators.TopFibreDimension.axisStep_injective <;> assumption
theorem vertexIndexCount (L : ℕ) : VertexIndexCount L := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun y => ?_⟩
  · ext ⟨a, s⟩
    constructor
    · intro h
      have hs : s = x := Subtype.ext h
      exact ⟨a, by rw [hs]⟩
    · rintro ⟨b, hb⟩
      have hs : x = s := congrArg Prod.snd hb
      subst hs
      rfl
  · have hinj : Function.Injective fun a : Fin 3 => ((a, x) : VertexIndex L) := fun a b h =>
      congrArg Prod.fst h
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp [Nat.card_eq_fintype_card]
  · exact ncard_near_le (meshAt_zero_zero L) (K := Fin 3) (by simp) (fun ι : VertexIndex L => ι.2)
      (fun ι => ι.1) (fun ι ι' h h' => Prod.ext h' h) y
theorem edgeIndexCount (L : ℕ) : EdgeIndexCount L := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun y => ?_⟩
  · ext ⟨c, b⟩
    constructor
    · intro h
      have hs : b.1.initial = x := Subtype.ext h
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨(c, μ), Prod.ext rfl (Subtype.ext (InfiniteLattice.Link.ext hs.symm ?_))⟩
      change x + InfiniteLattice.axisStep _ μ = b.1.terminal
      rw [← hμ, hs]
      abel
    · rintro ⟨⟨c', μ⟩, hb⟩
      have hs : FullSpace.forwardEdge x μ = b := congrArg Prod.snd hb
      subst hs
      rfl
  · have hinj : Function.Injective fun c : Fin 3 × Fin 4 =>
        ((c.1, FullSpace.forwardEdge x c.2) : EdgeIndex L) := by
      rintro ⟨c, μ⟩ ⟨c', ν⟩ h
      have h1 : c = c' := congrArg Prod.fst h
      have h2 : FullSpace.forwardEdge x μ = FullSpace.forwardEdge x ν := congrArg Prod.snd h
      have h3 : x + InfiniteLattice.axisStep _ μ = x + InfiniteLattice.axisStep _ ν :=
        congrArg (fun b : FullSpace.PositiveEdge _ => b.1.terminal) h2
      rw [h1, axisStep_injective (meshAt_zero_zero L) (add_left_cancel h3)]
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp [Nat.card_eq_fintype_card]
  · refine ncard_near_le (meshAt_zero_zero L) (K := Fin 3 × Fin 4) (by simp)
      (fun ι : EdgeIndex L => ι.2.1.initial) (fun ι => (ι.1, Classical.choose ι.2.2)) ?_ y
    rintro ⟨c, b⟩ ⟨c', b'⟩ h h'
    have h1 : c = c' := congrArg Prod.fst h'
    have h2 : Classical.choose b.2 = Classical.choose b'.2 := congrArg Prod.snd h'
    have h3 := Classical.choose_spec b.2
    have h4 := Classical.choose_spec b'.2
    rw [h2, ← h4] at h3
    have h5 : b.1.initial = b'.1.initial := h
    rw [h5] at h3
    exact Prod.ext h1 (Subtype.ext (InfiniteLattice.Link.ext h5 (sub_left_injective h3)))
theorem euclideanFunctions_l2 {J : Type} (N' : ℕ) :
    (∀ v : J → EuclideanSpace ℂ (Fin N'), Memℓp v 2 ↔ Summable fun x => ∑ i, ‖v x i‖ ^ 2) ∧
    ∀ v v' : lp (fun _ : J => EuclideanSpace ℂ (Fin N')) 2,
      Summable (fun x => ‖∑ i, conj (v x i) * v' x i‖) ∧
        inner ℂ v v' = ∑' x, ∑ i, conj (v x i) * v' x i := by
  refine ⟨fun v => ?_, fun v v' => ?_⟩
  · rw [memℓp_gen_iff (by norm_num)]
    have h : (fun x => ‖v x‖ ^ (2 : ℝ≥0∞).toReal) = fun x => ∑ i, ‖v x i‖ ^ 2 := by
      funext x
      rw [← EuclideanSpace.norm_sq_eq]
      simp
    rw [h]
  · have hterm : ∀ x, inner ℂ (v x) (v' x) = ∑ i, conj (v x i) * v' x i := by
      intro x
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have hs := lp.hasSum_inner (𝕜 := ℂ) v v'
    simp only [hterm] at hs
    exact ⟨summable_norm_iff.2 hs.summable, hs.tsum_eq.symm⟩
end UnitLatticeL2.L2Steps
open UnitLatticeL2 UnitLatticeL2.L2Steps in
theorem unitLatticeL2Statement_holds : UnitLatticeL2Statement := by
  refine ⟨?_, fun L => ⟨fun N' _ => euclideanFunctions_l2 N', ⟨coordsIsometry, starProperties,
    scalarMultipleInner, vertexIndexCount L, matrixEntryProperties, ?_⟩,
    ⟨coordsIsometry, starProperties, scalarMultipleInner, edgeIndexCount L,
      matrixEntryProperties, ?_⟩⟩⟩
  · intro H H' _ _ _ _ _ _ Z
    exact ⟨fun ψ χ => ContinuousLinearMap.adjoint_inner_left Z χ ψ,
      fun A hA => (ContinuousLinearMap.eq_adjoint_iff A Z).2 hA⟩
  · have : Nonempty (VertexIndex L) := ⟨(0, 0)⟩
    exact boundedKernelOperator _ fun ι' => (vertexIndexCount L).2 ι'.2
  · have : Nonempty (EdgeIndex L) := ⟨(0, Classical.arbitrary _)⟩
    exact boundedKernelOperator _ fun ι' => (edgeIndexCount L).2 ι'.2.1.initial
end Tower
end YangMills.Construction
end
