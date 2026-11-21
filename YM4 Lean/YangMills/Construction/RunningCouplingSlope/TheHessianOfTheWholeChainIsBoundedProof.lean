import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.RunningCouplingSlope.AFormIsAGradientNearEachCell
import YangMills.Construction.RunningCouplingSlope.BoundedInversesOfLocalMatricesAreLocal
import YangMills.Construction.RunningCouplingSlope.FunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.GaugeDirectionsOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheSoftActionReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheWholeChainIsBounded
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheHessianOfTheWholeChainDecays
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.HessianBound
open Tower Matrices
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem mixedDeriv_eq_secondFDeriv (g : E → ℝ) (hg : ContDiffAt ℝ 2 g 0) (x y : E) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => g (s • x + u • y)) 0) 0 =
      fderiv ℝ (fderiv ℝ g) 0 x y := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
end Calculus
section Schur
variable {Y : Type} [Fintype Y]
private theorem sq_weighted_sum_le (w : Y → ℝ) (hw : ∀ y, 0 ≤ w y) {S : ℝ} (hS : ∑ y, w y ≤ S)
    (B : Y → ℝ) : (∑ y, w y * B y) ^ 2 ≤ S * ∑ y, w y * B y ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => Real.sqrt (w y))
    (fun y => Real.sqrt (w y) * B y)
  have e1 : ∀ y, Real.sqrt (w y) * (Real.sqrt (w y) * B y) = w y * B y := fun y => by
    rw [← mul_assoc, Real.mul_self_sqrt (hw y)]
  have e2 : ∀ y, Real.sqrt (w y) ^ 2 = w y := fun y => Real.sq_sqrt (hw y)
  have e3 : ∀ y, (Real.sqrt (w y) * B y) ^ 2 = w y * B y ^ 2 := fun y => by
    rw [mul_pow, Real.sq_sqrt (hw y)]
  simp only [e1, e2, e3] at h
  refine h.trans (mul_le_mul_of_nonneg_right hS ?_)
  exact Finset.sum_nonneg fun y _ => mul_nonneg (hw y) (sq_nonneg _)
private theorem sum_mul_kernel_rows_le (w : Y → Y → ℝ) (hw : ∀ y y', 0 ≤ w y y') {S : ℝ}
    (hS : ∀ y, ∑ y', w y y' ≤ S) (a : Y → ℝ) (B : Y → Y → ℝ) :
    ∑ y, a y * ∑ y', w y y' * B y y' ≤
      Real.sqrt (∑ y, a y ^ 2) * Real.sqrt (S * ∑ y, ∑ y', w y y' * B y y' ^ 2) := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun y _ => sq_weighted_sum_le (w y) (hw y) (hS y) (B y)
private theorem schur_test (w : Y → Y → ℝ) (hw : ∀ y y', 0 ≤ w y y')
    (hsym : ∀ y y', w y y' = w y' y)
    {S : ℝ} (hS0 : 0 ≤ S) (hS : ∀ y, ∑ y', w y y' ≤ S) (a b : Y → ℝ) :
    ∑ y, a y * ∑ y', w y y' * b y' ≤
      S * (Real.sqrt (∑ y, a y ^ 2) * Real.sqrt (∑ y, b y ^ 2)) := by
  refine (sum_mul_kernel_rows_le w hw hS a fun _ y' => b y').trans ?_
  have h1 : ∑ y, ∑ y', w y y' * b y' ^ 2 ≤ S * ∑ y, b y ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun y' _ => ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc ∑ y, w y y' = ∑ y, w y' y := Finset.sum_congr rfl fun y _ => hsym y y'
      _ ≤ S := hS y'
  have h2 : Real.sqrt (S * ∑ y, ∑ y', w y y' * b y' ^ 2) ≤ S * Real.sqrt (∑ y, b y ^ 2) := by
    calc _ ≤ Real.sqrt (S * (S * ∑ y, b y ^ 2)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 hS0)
      _ = S * Real.sqrt (∑ y, b y ^ 2) := by
          rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hS0 hS0), Real.sqrt_mul_self hS0]
  calc _ ≤ Real.sqrt (∑ y, a y ^ 2) * (S * Real.sqrt (∑ y, b y ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := by ring
end Schur
section SeriesExpansions
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
private def euclidNorm (x : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖
private theorem euclidNorm_sq (x : ι → ℂ) : euclidNorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold euclidNorm
  rw [EuclideanSpace.norm_sq_eq]
private theorem euclidNorm_nonneg (x : ι → ℂ) : 0 ≤ euclidNorm x := norm_nonneg _
private theorem opNorm_le_of_euclidNorm [DecidableEq ι] (A : Matrix ι' ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x, euclidNorm (A.mulVec x) ≤ K * euclidNorm x) : ‖A‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  exact h x.ofLp
private theorem euclidNorm_mulVec_le [DecidableEq ι] (A : Matrix ι' ι ℂ) (x : ι → ℂ) :
    euclidNorm (A.mulVec x) ≤ ‖A‖ * euclidNorm x :=
  Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
end SeriesExpansions
section Cells
variable {L n k : ℕ}
private theorem exists_cellDecay_row_bound (hb : LocalMatricesBoundedAndInverseLocal) {θ : ℝ}
    (hθ : 0 < θ) : ∃ S : ℝ, 0 ≤ S ∧ ∀ (L n k : ℕ), Conventions.IsAdmissibleBlockingFactor L →
      0 < n → ∀ [Fintype (Vertex L n k k)] (y : Vertex L n k k),
        ∑ y', Real.exp (-(θ * cellDist y y')) ≤ S := by
  classical
  obtain ⟨S₀, hS₀, h⟩ := hb.1 (θ / 2) (by positivity)
  refine ⟨S₀ ^ 2, by positivity, fun L n k hL hn _ y => ?_⟩
  set t : Vertex L n k k → ℝ := fun y' => Real.exp (-(θ / 2 * cellDist y y')) with ht
  set T : Matrix Unit (Vertex L n k k) ℂ := fun _ y' => (t y' : ℂ) with hT
  have hloc : IsLocalOnCells (fun y' : Vertex L n k k => y') (fun _ : Unit => y) T 1 (θ / 2)
      (fun _ => 1) := by
    intro a b
    change ‖_‖ ≤ 1 * Real.exp (-(θ / 2 * cellDist a b)) * 1
    refine opNorm_le_of_euclidNorm _ (by positivity) fun x => ?_
    have hb2 : ‖x b‖ ≤ euclidNorm x := by
      have h1 := euclidNorm_sq x
      have h2 : ‖x b‖ ^ 2 ≤ euclidNorm x ^ 2 := by
        rw [h1]
        exact Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
          (Finset.mem_univ b)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (euclidNorm_nonneg _) (by norm_num)).1 h2
    have hv : ∀ u : Unit,
        (blockBetween (fun y' : Vertex L n k k => y') (fun _ : Unit => y) T a b).mulVec
          x u = if y = a then (t b : ℂ) * x b else 0 := by
      intro u
      simp only [Matrix.mulVec, dotProduct, blockBetween, hT]
      by_cases hya : y = a
      · simp [hya]
      · simp [hya]
    have hn2 : euclidNorm ((blockBetween (fun y' : Vertex L n k k => y') (fun _ : Unit => y)
        T a b).mulVec x) ≤ Real.exp (-(θ / 2 * cellDist a b)) * ‖x b‖ := by
      refine (pow_le_pow_iff_left₀ (euclidNorm_nonneg _) (by positivity)
        (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
      rw [euclidNorm_sq]
      simp only [Finset.univ_unique, Finset.sum_singleton, hv]
      by_cases hya : y = a
      · subst hya
        simp only [if_true, norm_mul, Complex.norm_real, Real.norm_eq_abs, ht]
        rw [abs_of_pos (Real.exp_pos _)]
      · simp only [hya, if_false, norm_zero]
        rw [zero_pow (by norm_num)]
        positivity
    calc _ ≤ _ := hn2
      _ ≤ Real.exp (-(θ / 2 * cellDist a b)) * euclidNorm x :=
          mul_le_mul_of_nonneg_left hb2 (Real.exp_pos _).le
      _ = _ := by ring
  have hn1 : ‖T‖ ≤ S₀ * 1 := h L n k (Vertex L n k k) Unit _ _ T 1 hL hn (by norm_num) hloc
  set x : Vertex L n k k → ℂ := fun y' => (t y' : ℂ) with hx
  have hTx : euclidNorm (T.mulVec x) = ∑ y', t y' ^ 2 := by
    have h0 : 0 ≤ ∑ y', t y' ^ 2 := Finset.sum_nonneg fun y' _ => by positivity
    refine (pow_left_inj₀ (euclidNorm_nonneg _) h0 (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
    rw [euclidNorm_sq]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    have e : T.mulVec x default = ((∑ y', t y' ^ 2 : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, hT, hx]
      push_cast
      exact Finset.sum_congr rfl fun y' _ => by ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  have hxl : euclidNorm x ^ 2 = ∑ y', t y' ^ 2 := by
    rw [euclidNorm_sq]
    refine Finset.sum_congr rfl fun y' _ => ?_
    simp only [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hmain := euclidNorm_mulVec_le T x
  rw [hTx] at hmain
  have hS : ∑ y', t y' ^ 2 ≤ S₀ ^ 2 := by
    have h3 : euclidNorm x ^ 2 ≤ S₀ * euclidNorm x := by
      rw [hxl]
      refine hmain.trans ?_
      have := mul_le_mul_of_nonneg_right hn1 (euclidNorm_nonneg x)
      linarith
    have h4 : euclidNorm x ≤ S₀ := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [euclidNorm_nonneg x]
    rw [← hxl]
    exact pow_le_pow_left₀ (euclidNorm_nonneg x) h4 2
  refine le_trans (le_of_eq ?_) hS
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp only [ht]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring
end Cells
section Parts
variable {L n k j : ℕ}
private def halfTraceSq (X : ComplexMatrix2) : ℝ := (ComplexMatrix2.halfTrace (X * X)).re
private theorem halfTraceSq_nonneg {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ halfTraceSq X := by apply _root_.YangMills.DeltaSharedProofs.p2944 <;> assumption
private theorem traceFinsumPairing_re_self {ι : Type*} [Fintype ι] (f : ι → ComplexMatrix2) :
    (traceFinsumPairing f f).re = ∑ i, halfTraceSq (f i) := by
  simp only [traceFinsumPairing, halfTraceSq, finsum_eq_sum_of_fintype, Complex.re_sum]
private def restrictValues (y : Vertex L n k k) (B : Edge L n k j → ComplexMatrix2) :
    Edge L n k j → ComplexMatrix2 :=
  open Classical in extendOddly fun b => if levelVertexCell b.source = y then B b else 0
private theorem restrictValues_pos (y : Vertex L n k k) (B : Edge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    open Classical in
    restrictValues y B b = if levelVertexCell b.source = y then B b else 0 := by
  simp only [restrictValues, extendOddly]
  rw [if_pos hb]
private theorem restrictValues_mem
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (y : Vertex L n k k) (B : edgeFormSpace L n k j) :
    restrictValues y (B : Edge L n k j → ComplexMatrix2) ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [restrictValues_pos y _ hb]
    split_ifs
    · exact B.2.1 b hb
    · exact ComplexMatrix2.hermitianTraceless.zero_mem
  · simp only [restrictValues, extendOddly]
    rcases hX b with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · rw [if_neg hn, if_pos hp, show b.opposite.opposite = b from rfl]
    · rw [if_pos hp, if_neg hn, neg_neg]
private def restrictForm (y : Vertex L n k k) (B : edgeFormSpace L n k j) : edgeFormSpace L n k j :=
  open Classical in
  if h : restrictValues y (B : Edge L n k j → ComplexMatrix2) ∈ edgeFormSpace L n k j then ⟨_, h⟩
  else 0
private theorem coe_restrictForm
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (y : Vertex L n k k) (B : edgeFormSpace L n k j) :
    (restrictForm y B : Edge L n k j → ComplexMatrix2) =
      restrictValues y (B : Edge L n k j → ComplexMatrix2) := by
  simp only [restrictForm, dif_pos (restrictValues_mem hX y B)]
private theorem restrictForm_supported
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (y : Vertex L n k k) (B : edgeFormSpace L n k j) :
    FormSupportedInCell y (restrictForm y B : Edge L n k j → ComplexMatrix2) := by
  intro b hb
  rw [coe_restrictForm hX, restrictValues_pos y _ b.2, if_neg hb]
private theorem sum_restrictForm [Fintype (Vertex L n k k)]
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k j) : ∑ y, restrictForm y B = B := by
  classical
  apply Subtype.ext
  funext b
  have hpos : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      ((∑ y, restrictForm y B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) c =
        (B : Edge L n k j → ComplexMatrix2) c := by
    intro c hc
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [coe_restrictForm hX, restrictValues_pos _ _ hc]
    simp
  rcases hX b with ⟨hp, -⟩ | ⟨hp, -⟩
  · exact hpos b hp
  · have h1 := ((∑ y, restrictForm y B : edgeFormSpace L n k j)).2.2 b
    have h2 := B.2.2 b
    have h3 := hpos _ hp
    rw [h1, h2] at h3
    exact neg_injective h3
private theorem sum_normSq_restrictForm [Fintype (Vertex L n k k)] [Finite (PositiveEdge L n k j)]
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k j) :
    ∑ y, (edgeFormPairing (restrictForm y B : Edge L n k j → ComplexMatrix2)
        (restrictForm y B : Edge L n k j → ComplexMatrix2)).re =
      (edgeFormPairing (B : Edge L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)).re := by
  classical
  letI : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
  simp only [edgeFormPairing, traceFinsumPairing_re_self, restrictToPositiveEdges,
    coe_restrictForm hX]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [restrictValues_pos _ _ b.2]
  have e : ∀ y : Vertex L n k k, halfTraceSq (if levelVertexCell b.1.source = y then
      (B : Edge L n k j → ComplexMatrix2) b.1 else 0) =
      if levelVertexCell b.1.source = y then halfTraceSq ((B : Edge L n k j → ComplexMatrix2) b.1)
      else 0 := by
    intro y
    split_ifs
    · rfl
    · simp [halfTraceSq, ComplexMatrix2.halfTrace]
  simp only [e]
  simp
private theorem edgeFormPairing_re_self_nonneg [Finite (PositiveEdge L n k j)]
    (B : edgeFormSpace L n k j) :
    0 ≤ (edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B : Edge L n k j → ComplexMatrix2)).re := by
  letI : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
  simp only [edgeFormPairing, traceFinsumPairing_re_self, restrictToPositiveEdges]
  exact Finset.sum_nonneg fun b _ => halfTraceSq_nonneg (B.2.1 _ b.2)
end Parts
section Triples
variable {L n k : ℕ}
private def restrictLevelForms (y : Vertex L n k k) (ξ : LevelForms L n k) : LevelForms L n k :=
  (restrictForm y ξ.1, fun i => restrictForm y (ξ.2 i))
private def restrictTriple (y : Vertex L n k k) (τ : LevelTriple L n k) : LevelTriple L n k :=
  (restrictLevelForms y τ.1, restrictLevelForms y τ.2.1, restrictForm y τ.2.2)
private structure LevelsRegular (L n k : ℕ) : Prop where
  xor_opposite : ∀ j ≤ k, ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  finite_pos : ∀ j ≤ k, Finite (PositiveEdge L n k j)
private theorem sum_restrictLevelForms [Fintype (Vertex L n k k)] (h : LevelsRegular L n k)
    (ξ : LevelForms L n k) : ∑ y, restrictLevelForms y ξ = ξ := by
  apply Prod.ext
  · rw [Prod.fst_sum]
    exact sum_restrictForm (h.xor_opposite 0 (Nat.zero_le _)) ξ.1
  · funext i
    rw [Prod.snd_sum, Finset.sum_apply]
    exact sum_restrictForm (h.xor_opposite _ i.2) (ξ.2 i)
private theorem sum_restrictTriple [Fintype (Vertex L n k k)] (h : LevelsRegular L n k)
    (τ : LevelTriple L n k) : ∑ y, restrictTriple y τ = τ := by
  apply Prod.ext
  · rw [Prod.fst_sum]
    exact sum_restrictLevelForms h τ.1
  · apply Prod.ext
    · rw [Prod.snd_sum, Prod.fst_sum]
      exact sum_restrictLevelForms h τ.2.1
    · rw [Prod.snd_sum, Prod.snd_sum]
      exact sum_restrictForm (h.xor_opposite k le_rfl) τ.2.2
private theorem levelFormsNormSq_eq (ξ : LevelForms L n k) :
    levelFormsNormSq ξ = (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2)
        (ξ.1 : Edge L n k 0 → ComplexMatrix2)).re +
      ∑ i : Fin k, (edgeFormPairing (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)
        (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)).re := rfl
private theorem sum_normSq_restrictLevelForms [Fintype (Vertex L n k k)] (h : LevelsRegular L n k)
    (ξ : LevelForms L n k) :
    ∑ y, levelFormsNormSq (restrictLevelForms y ξ) = levelFormsNormSq ξ := by
  haveI := h.finite_pos 0 (Nat.zero_le _)
  simp only [levelFormsNormSq_eq, restrictLevelForms]
  rw [Finset.sum_add_distrib, sum_normSq_restrictForm (h.xor_opposite 0 (Nat.zero_le _)),
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := h.finite_pos _ i.2
  exact sum_normSq_restrictForm (h.xor_opposite _ i.2) (ξ.2 i)
private theorem sum_normSq_restrictTriple [Fintype (Vertex L n k k)] (h : LevelsRegular L n k)
    (τ : LevelTriple L n k) : ∑ y, tripleNormSq (restrictTriple y τ) = tripleNormSq τ := by
  haveI := h.finite_pos k le_rfl
  simp only [tripleNormSq, restrictTriple, Finset.sum_add_distrib, sum_normSq_restrictLevelForms h]
  congr 1
  exact sum_normSq_restrictForm (h.xor_opposite k le_rfl) τ.2.2
private theorem levelFormsNormSq_nonneg (h : LevelsRegular L n k) (ξ : LevelForms L n k) :
    0 ≤ levelFormsNormSq ξ := by
  haveI := h.finite_pos 0 (Nat.zero_le _)
  rw [levelFormsNormSq_eq]
  refine add_nonneg (edgeFormPairing_re_self_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
  haveI := h.finite_pos _ i.2
  exact edgeFormPairing_re_self_nonneg _
private theorem tripleNormSq_nonneg (h : LevelsRegular L n k) (τ : LevelTriple L n k) :
    0 ≤ tripleNormSq τ := by
  haveI := h.finite_pos k le_rfl
  exact add_nonneg (add_nonneg (levelFormsNormSq_nonneg h _) (levelFormsNormSq_nonneg h _))
    (edgeFormPairing_re_self_nonneg _)
private theorem restrictLevelForms_supported (h : LevelsRegular L n k) (y : Vertex L n k k)
    (ξ : LevelForms L n k) : LevelFormsSupportedInCell y (restrictLevelForms y ξ) :=
  ⟨restrictForm_supported (h.xor_opposite 0 (Nat.zero_le _)) y ξ.1,
    fun i => restrictForm_supported (h.xor_opposite _ i.2) y (ξ.2 i)⟩
private theorem restrictTriple_supported (h : LevelsRegular L n k) (y : Vertex L n k k)
    (τ : LevelTriple L n k) : TripleSupportedInCell y (restrictTriple y τ) :=
  ⟨restrictLevelForms_supported h y τ.1, restrictLevelForms_supported h y τ.2.1,
    restrictForm_supported (h.xor_opposite k le_rfl) y τ.2.2⟩
private theorem edgeFormPairing_zero {j : ℕ} :
    edgeFormPairing (0 : Edge L n k j → ComplexMatrix2) (0 : Edge L n k j → ComplexMatrix2) = 0 := by
  simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace]
private theorem tripleNormSq_backgroundOnly (A : edgeFormSpace L n k 0) :
    tripleNormSq (backgroundOnlyTriple A) =
      (edgeFormPairing (A : Edge L n k 0 → ComplexMatrix2) (A : Edge L n k 0 → ComplexMatrix2)).re := by
  have e0 : levelFormsNormSq (0 : LevelForms L n k) = 0 := by
    rw [levelFormsNormSq_eq]
    simp [edgeFormPairing_zero]
  have e1 : levelFormsNormSq ((A, 0) : LevelForms L n k) =
      (edgeFormPairing (A : Edge L n k 0 → ComplexMatrix2) (A : Edge L n k 0 → ComplexMatrix2)).re := by
    rw [levelFormsNormSq_eq]
    simp [edgeFormPairing_zero]
  simp only [tripleNormSq, backgroundOnlyTriple, e0, e1, topFormNormSq]
  simp [edgeFormPairing_zero]
abbrev _root_.YangMills.SharedProofs.p87848 := @tripleNormSq_backgroundOnly
private theorem zero_supported {j : ℕ} (y : Vertex L n k k) :
    FormSupportedInCell y ((0 : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) :=
  fun _ _ => rfl
private theorem backgroundOnly_supported {y : Vertex L n k k} {A : edgeFormSpace L n k 0}
    (h : FormSupportedInCell y (A : Edge L n k 0 → ComplexMatrix2)) :
    TripleSupportedInCell y (backgroundOnlyTriple A) :=
  ⟨⟨h, fun _ => zero_supported y⟩, ⟨zero_supported y, fun _ => zero_supported y⟩, zero_supported y⟩
private theorem backgroundOnly_add (A B : edgeFormSpace L n k 0) :
    backgroundOnlyTriple (A + B) = backgroundOnlyTriple A + backgroundOnlyTriple B := by
  simp [backgroundOnlyTriple]
private theorem backgroundOnly_sum {Y : Type} (s : Finset Y) (f : Y → edgeFormSpace L n k 0) :
    backgroundOnlyTriple (∑ y ∈ s, f y) = ∑ y ∈ s, backgroundOnlyTriple (f y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [backgroundOnlyTriple]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, backgroundOnly_add, ih]
private theorem levelVertexCell_eq_fine (x : Vertex L n k 0) :
    levelVertexCell x = fineVertexCell x := by apply _root_.YangMills.SharedProofs.p6946 <;> assumption
private theorem weighted_sum_restrictForm [Fintype (Vertex L n k k)]
    [Fintype (PositiveEdge L n k 0)]
    (hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : Vertex L n k k → ℝ) (B : edgeFormSpace L n k 0) :
    ∑ y, w y * (edgeFormPairing (restrictForm y B : Edge L n k 0 → ComplexMatrix2)
        (restrictForm y B : Edge L n k 0 → ComplexMatrix2)).re =
      ∑ b : PositiveEdge L n k 0, w (fineVertexCell b.1.source) *
        halfTraceSq ((B : Edge L n k 0 → ComplexMatrix2) b.1) := by
  classical
  simp only [edgeFormPairing, traceFinsumPairing_re_self, restrictToPositiveEdges,
    coe_restrictForm hX, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [restrictValues_pos _ _ b.2, levelVertexCell_eq_fine]
  have e : ∀ y : Vertex L n k k, w y * halfTraceSq (if fineVertexCell b.1.source = y then
      (B : Edge L n k 0 → ComplexMatrix2) b.1 else 0) =
      if fineVertexCell b.1.source = y then
        w y * halfTraceSq ((B : Edge L n k 0 → ComplexMatrix2) b.1) else 0 := by
    intro y
    split_ifs
    · rfl
    · simp [halfTraceSq, ComplexMatrix2.halfTrace]
  simp only [e]
  simp
end Triples
private theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by apply _root_.YangMills.Construction.CoordinateSeminorms.sqrt_add_le_add_sqrt <;> assumption
private theorem levelsRegular_of (hf : Tower.BondSetFields.ProductStructureHolds) {L n k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : LevelsRegular L n k := by
  refine ⟨fun j hj b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite
    (by have := hL.2; omega) ?_ b, fun j hj => ?_⟩
  · simp only [PeriodicLattice.levelDepth]
    omega
  · have hb : Finite (Edge L n k j) := Set.finite_univ_iff.1 ((hf L hL k j hj).1 n hn).2.1
    exact Subtype.finite
private structure CellKernelBound {L n k : ℕ} [Fintype (Vertex L n k k)]
    (H : LevelTriple L n k → LevelTriple L n k → ℝ) (C θ S : ℝ) : Prop where
  map_sum_left : ∀ {Y : Type} (s : Finset Y) (f : Y → LevelTriple L n k) (t : LevelTriple L n k),
    H (∑ y ∈ s, f y) t = ∑ y ∈ s, H (f y) t
  map_sum_right : ∀ {Y : Type} (s : Finset Y) (f : Y → LevelTriple L n k) (t : LevelTriple L n k),
    H t (∑ y ∈ s, f y) = ∑ y ∈ s, H t (f y)
  map_add_left : ∀ x x' t : LevelTriple L n k, H (x + x') t = H x t + H x' t
  decay : ∀ (y y' : Vertex L n k k) (τ τ' : LevelTriple L n k),
    TripleSupportedInCell y τ → TripleSupportedInCell y' τ' →
    |H τ τ'| ≤ C * Real.exp (-(θ * cellDist y y')) *
      Real.sqrt (tripleNormSq τ) * Real.sqrt (tripleNormSq τ')
  dist_comm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
  row_le : ∀ y : Vertex L n k k, ∑ y', Real.exp (-(θ * cellDist y y')) ≤ S
section Requirements
variable {L n k : ℕ} [Fintype (Vertex L n k k)]
private theorem sum_sqrt_tripleNormSq_sq (hlev : LevelsRegular L n k) (τ : LevelTriple L n k) :
    ∑ y, Real.sqrt (tripleNormSq (restrictTriple y τ)) ^ 2 = tripleNormSq τ := by
  rw [← sum_normSq_restrictTriple hlev τ]
  exact Finset.sum_congr rfl fun y _ => Real.sq_sqrt (tripleNormSq_nonneg hlev _)
private theorem abs_le_of_normSq {H : LevelTriple L n k → LevelTriple L n k → ℝ} {C θ S : ℝ}
    (P : CellKernelBound H C θ S) (hlev : LevelsRegular L n k) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (τ τ' : LevelTriple L n k) :
    |H τ τ'| ≤ C * (S * (Real.sqrt (tripleNormSq τ) * Real.sqrt (tripleNormSq τ'))) := by
  set w : Vertex L n k k → Vertex L n k k → ℝ := fun y y' => Real.exp (-(θ * cellDist y y'))
    with hw
  set α : Vertex L n k k → ℝ := fun y => Real.sqrt (tripleNormSq (restrictTriple y τ)) with hα
  set β : Vertex L n k k → ℝ := fun y => Real.sqrt (tripleNormSq (restrictTriple y τ')) with hβ
  have e1 : H τ τ' = ∑ y, ∑ y', H (restrictTriple y τ) (restrictTriple y' τ') := by
    conv_lhs => rw [← sum_restrictTriple hlev τ, ← sum_restrictTriple hlev τ']
    rw [P.map_sum_left]
    exact Finset.sum_congr rfl fun y _ => P.map_sum_right _ _ _
  have e2 : |H τ τ'| ≤ C * ∑ y, α y * ∑ y', w y y' * β y' := by
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y' _ => ?_
    refine (P.decay y y' _ _ (restrictTriple_supported hlev y τ)
      (restrictTriple_supported hlev y' τ')).trans (le_of_eq ?_)
    simp only [hw, hα, hβ]
    ring
  have e3 := schur_test w (fun y y' => (Real.exp_pos _).le)
    (fun y y' => by simp only [hw, P.dist_comm y y']) hS0 P.row_le α β
  simp only [hα, hβ, sum_sqrt_tripleNormSq_sq hlev] at e3
  exact e2.trans (mul_le_mul_of_nonneg_left e3 hC)
private theorem abs_backgroundOnly_le {H : LevelTriple L n k → LevelTriple L n k → ℝ} {C θ S : ℝ}
    (P : CellKernelBound H C θ S) (hlev : LevelsRegular L n k) (hC : 0 ≤ C)
    [Fintype (PositiveEdge L n k 0)] (A : edgeFormSpace L n k 0)
    (gr : Vertex L n k k → edgeFormSpace L n k 0)
    (hzero : ∀ y t, H (backgroundOnlyTriple (gr y)) t = 0) (τ' : LevelTriple L n k) :
    |H (backgroundOnlyTriple A) τ'| ≤ C * (Real.sqrt (tripleNormSq τ') * Real.sqrt (S *
      ∑ y, ∑ b : PositiveEdge L n k 0,
        Real.exp (-(θ * cellDist (fineVertexCell b.1.source) y)) *
          halfTraceSq (((A - gr y : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) b.1))) := by
  set w : Vertex L n k k → Vertex L n k k → ℝ := fun y y' => Real.exp (-(θ * cellDist y y'))
    with hw
  have hX0 := hlev.xor_opposite 0 (Nat.zero_le _)
  haveI := hlev.finite_pos 0 (Nat.zero_le _)
  set A' : Vertex L n k k → edgeFormSpace L n k 0 := fun y => A - gr y with hA'
  have hstep : ∀ y t, H (backgroundOnlyTriple A) t =
      ∑ y'', H (backgroundOnlyTriple (restrictForm y'' (A' y))) t := by
    intro y t
    have e1 : backgroundOnlyTriple A =
        backgroundOnlyTriple (A' y) + backgroundOnlyTriple (gr y) := by
      rw [← backgroundOnly_add]
      simp [hA']
    rw [e1, P.map_add_left, hzero, add_zero]
    conv_lhs => rw [← sum_restrictForm hX0 (A' y), backgroundOnly_sum]
    rw [P.map_sum_left]
  set β : Vertex L n k k → ℝ := fun y => Real.sqrt (tripleNormSq (restrictTriple y τ')) with hβ
  set α : Vertex L n k k → Vertex L n k k → ℝ := fun y y'' =>
    Real.sqrt ((edgeFormPairing (restrictForm y'' (A' y) : Edge L n k 0 → ComplexMatrix2)
      (restrictForm y'' (A' y) : Edge L n k 0 → ComplexMatrix2)).re) with hα
  have e2 : |H (backgroundOnlyTriple A) τ'| ≤ C * ∑ y, β y * ∑ y'', w y y'' * α y y'' := by
    conv_lhs => rw [← sum_restrictTriple hlev τ', P.map_sum_right]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [hstep y]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y'' _ => ?_
    refine (P.decay y'' y _ _
      (backgroundOnly_supported (restrictForm_supported hX0 y'' (A' y)))
      (restrictTriple_supported hlev y τ')).trans (le_of_eq ?_)
    rw [tripleNormSq_backgroundOnly]
    simp only [hw, hα, hβ, P.dist_comm y'' y]
    ring
  have e3 := sum_mul_kernel_rows_le w (fun y y' => (Real.exp_pos _).le) P.row_le β α
  simp only [hβ, sum_sqrt_tripleNormSq_sq hlev] at e3
  have hαsq : ∀ y, ∑ y'', w y y'' * α y y'' ^ 2 =
      ∑ b : PositiveEdge L n k 0, Real.exp (-(θ * cellDist (fineVertexCell b.1.source) y)) *
        halfTraceSq (((A - gr y : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) b.1) := by
    intro y
    have e4 : ∀ y'', w y y'' * α y y'' ^ 2 = w y y'' *
        (edgeFormPairing (restrictForm y'' (A' y) : Edge L n k 0 → ComplexMatrix2)
          (restrictForm y'' (A' y) : Edge L n k 0 → ComplexMatrix2)).re := fun y'' => by
      simp only [hα]
      rw [Real.sq_sqrt (edgeFormPairing_re_self_nonneg _)]
    simp only [e4]
    rw [weighted_sum_restrictForm hX0 (w y) (A' y)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hw, P.dist_comm y]
    rfl
  simp only [hαsq] at e3
  exact e2.trans (mul_le_mul_of_nonneg_left e3 hC)
end Requirements
private theorem first_slot_arith {C S CG c' Q cv sq T u : ℝ} (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hCG : 0 ≤ CG) (hcv : 0 ≤ cv) (hsq : 0 ≤ sq) (hT : 0 ≤ T)
    (hQ : Q ≤ CG * (cv + Real.exp (-(2 * c')) * sq))
    (hu : |u| ≤ C * (T * Real.sqrt (S * Q))) :
    |u| ≤ (C * S + C * Real.sqrt (S * CG)) *
      (Real.sqrt cv + Real.exp (-c') * Real.sqrt sq) * T := by
  have he : Real.sqrt (Real.exp (-(2 * c'))) = Real.exp (-c') := by
    rw [← Real.exp_half]
    congr 1
    ring
  have h1 : Real.sqrt (S * Q) ≤ Real.sqrt (S * CG) *
      (Real.sqrt cv + Real.exp (-c') * Real.sqrt sq) := by
    have h2 : S * Q ≤ S * CG * (cv + Real.exp (-(2 * c')) * sq) := by
      have := mul_le_mul_of_nonneg_left hQ hS0
      linarith
    refine (Real.sqrt_le_sqrt h2).trans ?_
    rw [Real.sqrt_mul (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine (sqrt_add_le_add_sqrt hcv (by positivity)).trans ?_
    rw [Real.sqrt_mul (Real.exp_pos _).le, he]
  have h3 : C * (T * Real.sqrt (S * Q)) ≤ C * Real.sqrt (S * CG) *
      (Real.sqrt cv + Real.exp (-c') * Real.sqrt sq) * T := by
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hT)
    calc _ = C * T * Real.sqrt (S * Q) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have h4 : 0 ≤ C * S * (Real.sqrt cv + Real.exp (-c') * Real.sqrt sq) * T := by positivity
  calc |u| ≤ _ := hu
    _ ≤ _ := h3
    _ ≤ _ := by nlinarith
private theorem hessian_bilinear (hF : ChainFreeEnergyAnalytic.Claim) {a : ℝ} (ha : 0 < a)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hbond : ∀ j ≤ k, Finite (Edge L n k j)) :
    (∀ {Y : Type} (s : Finset Y) (f : Y → LevelTriple L n k) (t : LevelTriple L n k),
      hessianOfFreeEnergy a (∑ y ∈ s, f y) t = ∑ y ∈ s, hessianOfFreeEnergy a (f y) t) ∧
    (∀ {Y : Type} (s : Finset Y) (f : Y → LevelTriple L n k) (t : LevelTriple L n k),
      hessianOfFreeEnergy a t (∑ y ∈ s, f y) = ∑ y ∈ s, hessianOfFreeEnergy a t (f y)) ∧
    ∀ x x' t : LevelTriple L n k,
      hessianOfFreeEnergy a (x + x') t = hessianOfFreeEnergy a x t + hessianOfFreeEnergy a x' t := by
  have hfd : ∀ j ≤ k, FiniteDimensional ℝ (edgeFormSpace L n k j) := fun j hj => by
    haveI := hbond j hj
    infer_instance
  haveI := hfd 0 (Nat.zero_le _)
  haveI := hfd k le_rfl
  haveI : ∀ i : Fin k, FiniteDimensional ℝ (edgeFormSpace L n k (i + 1)) := fun i => hfd _ i.2
  haveI : FiniteDimensional ℝ (LevelForms L n k) := inferInstance
  haveI : FiniteDimensional ℝ (LevelTriple L n k) := inferInstance
  set e : (Fin (Module.finrank ℝ (LevelTriple L n k)) → ℝ) ≃ₗ[ℝ] LevelTriple L n k :=
    (Module.finBasis ℝ (LevelTriple L n k)).equivFun.symm with he
  have hg : ContDiffAt ℝ 2 (fun w => tripleFreeEnergy a (e w)) 0 :=
    ((hF a ha L hL k n hk hn).1 _ e).1.contDiffAt
  set D := fderiv ℝ (fderiv ℝ fun w => tripleFreeEnergy a (e w)) 0 with hD
  have hH : ∀ τ τ' : LevelTriple L n k,
      hessianOfFreeEnergy a τ τ' = D (e.symm τ) (e.symm τ') := by
    intro τ τ'
    rw [hD, ← mixedDeriv_eq_secondFDeriv _ hg]
    unfold hessianOfFreeEnergy
    simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
  refine ⟨fun s f t => ?_, fun s f t => ?_, fun x x' t => ?_⟩
  · simp only [hH, map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  · simp only [hH, map_sum]
  · simp only [hH, map_add, ContinuousLinearMap.coe_add', Pi.add_apply]
private theorem backgroundCurvatureNormSq_nonneg {L n k : ℕ} [Finite (Face L n k 0)]
    (A : edgeFormSpace L n k 0) : 0 ≤ backgroundCurvatureNormSq A := by
  letI : Fintype (Face L n k 0) := Fintype.ofFinite _
  simp only [backgroundCurvatureNormSq]
  rw [traceFinsumPairing_re_self]
  exact Finset.sum_nonneg fun p _ =>
    halfTraceSq_nonneg (Submodule.mem_pi.1
      (CriticalBranchResponse.formCoboundary L n k A).2 p (Set.mem_univ _))
private theorem vertexCoboundary_mem {L n k : ℕ} (l : vertexFunctionSpace L n k 0) :
    vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2) ∈ edgeFormSpace L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · have h1 := Submodule.mem_pi.1 l.2
    exact ComplexMatrix2.hermitianTraceless.sub_mem (h1 _ (Set.mem_univ _)) (h1 _ (Set.mem_univ _))
  · simp [vertexCoboundary, PeriodicLattice.Bond.opposite]
theorem hessianOfFreeEnergyBounded_of_kernelDecay (hK : HessianKernelDecays)
    (hG : FormIsLocallyAGradient)
    (hGauge : GaugeDirectionsAreFlat)
    (hF : ChainFreeEnergyAnalytic.Claim)
    (hB : LocalMatricesBoundedAndInverseLocal)
    (hCell : NeighbouringFineVertexCells)
    (hConf : Tower.BondSetFields.ProductStructureHolds) :
    HessianOfFreeEnergyBounded := by
  intro a ha L hL k hk
  obtain ⟨C, θ, hC, hθ, hKn⟩ := hK a ha L hL k hk
  obtain ⟨CG, c, hCG, hc, hGn⟩ := hG L hL k hk θ hθ
  obtain ⟨S, hS0, hS⟩ := exists_cellDecay_row_bound hB hθ
  refine ⟨C * S + C * Real.sqrt (S * CG), c / 2, by positivity, by positivity, ?_⟩
  filter_upwards [hKn, eventually_gt_atTop 0] with n hKn hn
  have hlev : LevelsRegular L n k := levelsRegular_of hConf hL hn
  have hbond : ∀ j ≤ k, Finite (Edge L n k j) := fun j hj =>
    Set.finite_univ_iff.1 ((hConf L hL k j hj).1 n hn).2.1
  have hy : Finite (Vertex L n k k) := by
    haveI := hbond k le_rfl
    exact Finite.of_injective (fun y : Vertex L n k k => PeriodicLattice.Bond.forwardFrom y 0)
      fun y y' e => congrArg PeriodicLattice.Bond.source e
  letI : Fintype (Vertex L n k k) := Fintype.ofFinite _
  obtain ⟨b1, b2, b3⟩ := hessian_bilinear hF ha hL hk hn hbond
  have P : CellKernelBound (hessianOfFreeEnergy a) C θ S :=
    ⟨b1, b2, b3, hKn, (hCell L hL n k).1, hS L n k hL hn⟩
  refine ⟨fun τ τ' => ?_, fun A τ' => ?_⟩
  · refine (abs_le_of_normSq P hlev hC hS0 τ τ').trans ?_
    have h5 : 0 ≤ Real.sqrt (tripleNormSq τ) * Real.sqrt (tripleNormSq τ') := by positivity
    have h6 : 0 ≤ C * Real.sqrt (S * CG) := by positivity
    nlinarith [mul_nonneg h6 h5]
  · obtain ⟨l, hl⟩ := hGn n hn A
    haveI := hlev.finite_pos 0 (Nat.zero_le _)
    letI : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
    set gr : Vertex L n k k → edgeFormSpace L n k 0 := fun y => ⟨_, vertexCoboundary_mem (l y)⟩
      with hgrd
    have hzero : ∀ y t, hessianOfFreeEnergy a (backgroundOnlyTriple (gr y)) t = 0 := fun y t =>
      (hGauge a ha L hL k n hk hn).2 (l y) (gr y) rfl t
    have hmain := abs_backgroundOnly_le P hlev hC A gr hzero τ'
    simp only [finsum_eq_sum_of_fintype] at hl
    have hsq0 : 0 ≤ (edgeFormPairing (A : Edge L n k 0 → ComplexMatrix2)
        (A : Edge L n k 0 → ComplexMatrix2)).re :=
      edgeFormPairing_re_self_nonneg A
    have hs0 : Finite (Vertex L n k 0) := by
      haveI := hbond 0 (Nat.zero_le _)
      exact Finite.of_injective (fun y : Vertex L n k 0 => PeriodicLattice.Bond.forwardFrom y 0)
        fun y y' e => congrArg PeriodicLattice.Bond.source e
    have hp0 : Finite (Face L n k 0) :=
      Finite.of_injective (fun p : Face L n k 0 => (p.origin, p.firstAxis, p.secondAxis))
        fun p p' e => by
          simp only [Prod.mk.injEq] at e
          exact PeriodicLattice.Plaquette.ext e.1 e.2.1 e.2.2
    have hcv : 0 ≤ backgroundCurvatureNormSq A := backgroundCurvatureNormSq_nonneg A
    rw [tripleNormSq_backgroundOnly]
    refine first_slot_arith (c' := c / 2 * (2 * (L : ℝ) ^ n)) hC hS0 hCG hcv hsq0
      (Real.sqrt_nonneg _) ?_ hmain
    have e2 : -(2 * (c / 2 * (2 * (L : ℝ) ^ n))) = -(c * (2 * (L : ℝ) ^ n)) := by ring
    rw [e2]
    exact hl
end YangMills.Construction.RunningCouplingSlope.HessianBound
end
