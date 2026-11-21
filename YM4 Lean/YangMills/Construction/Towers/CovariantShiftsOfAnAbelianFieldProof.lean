import YangMills.Construction.Towers.AbelianOperatorsAreLocalAndSelfAdjointProof
import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianField
import YangMills.Construction.Towers.TheDilationOfAWaveOfTheThirdColourProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianShiftsProof
open Tower.AbelianFieldFacts Tower.UnitLatticeL2 Matrices
open UnitaryCombinations (ScalarL2)
open InfiniteLattice (axisStep)
variable {L : ℕ}
theorem meshAt_zero_zero : meshAt L 0 0 = 1 := by
  simp [meshAt]
section PhaseTwisted
variable (c : FullSpace.Vertex L 0 0 → ℂ) (σ : FullSpace.Vertex L 0 0 ≃ FullSpace.Vertex L 0 0)
def phaseTwistedFn (w : ScalarL2 L) :
    FullSpace.Vertex L 0 0 → EuclideanSpace ℂ (Fin 1) :=
  fun x => c x • (w (σ x) : EuclideanSpace ℂ (Fin 1))
variable {c}
theorem norm_phaseTwistedFn (hc : ∀ x, ‖c x‖ = 1) (w : ScalarL2 L)
    (x : FullSpace.Vertex L 0 0) : ‖phaseTwistedFn c σ w x‖ = ‖w (σ x)‖ := by
  simp [phaseTwistedFn, norm_smul, hc]
theorem memℓp_phaseTwistedFn (hc : ∀ x, ‖c x‖ = 1) (w : ScalarL2 L) :
    Memℓp (phaseTwistedFn c σ w) 2 := by
  have h := lp.memℓp w
  rw [memℓp_gen_iff (by norm_num)] at h ⊢
  refine (σ.summable_iff.2 h).congr fun x => ?_
  simp [norm_phaseTwistedFn σ hc]
def phaseTwistedIsometry (hc : ∀ x, ‖c x‖ = 1) : ScalarL2 L →ₗᵢ[ℂ] ScalarL2 L where
  toFun w := ⟨phaseTwistedFn c σ w, memℓp_phaseTwistedFn σ hc w⟩
  map_add' w w' := by
    apply lp.ext
    funext x
    show phaseTwistedFn c σ (w + w') x = phaseTwistedFn c σ w x + phaseTwistedFn c σ w' x
    simp [phaseTwistedFn, smul_add]
  map_smul' z w := by
    apply lp.ext
    funext x
    simp [phaseTwistedFn, smul_comm (c x) z]
  norm_map' w := by
    show ‖(⟨phaseTwistedFn c σ w, memℓp_phaseTwistedFn σ hc w⟩ : ScalarL2 L)‖ = ‖w‖
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    rw [← σ.tsum_eq (fun x => ‖w x‖ ^ (2 : ENNReal).toReal)]
    exact tsum_congr fun x => by
      show ‖phaseTwistedFn c σ w x‖ ^ _ = _
      rw [norm_phaseTwistedFn σ hc]
theorem phaseTwistedIsometry_apply (hc : ∀ x, ‖c x‖ = 1) (w : ScalarL2 L)
    (x : FullSpace.Vertex L 0 0) :
    phaseTwistedIsometry σ hc w x 0 = c x * w (σ x) 0 := by
  show (c x • (w (σ x) : EuclideanSpace ℂ (Fin 1))) 0 = _
  simp
end PhaseTwisted
section ShiftMaps
variable (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (μ : Fin 4)
def shiftPhase (x : FullSpace.Vertex L 0 0) : ℂ :=
  Complex.exp (2 * Complex.I * (θ (FullSpace.forwardEdge x μ) : ℂ))
def shiftBackPhase (x : FullSpace.Vertex L 0 0) : ℂ :=
  Complex.exp (-(2 * Complex.I * (θ (FullSpace.forwardEdge (x - axisStep _ μ) μ) : ℂ)))
theorem norm_exp_two_I_mul_ofReal (t : ℝ) : ‖Complex.exp (2 * Complex.I * (t : ℂ))‖ = 1 := by
  have e : 2 * Complex.I * (t : ℂ) = ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]
theorem norm_shiftPhase (x : FullSpace.Vertex L 0 0) : ‖shiftPhase θ μ x‖ = 1 :=
  norm_exp_two_I_mul_ofReal _
theorem norm_shiftBackPhase (x : FullSpace.Vertex L 0 0) : ‖shiftBackPhase θ μ x‖ = 1 := by
  have e : -(2 * Complex.I * ((θ (FullSpace.forwardEdge (x - axisStep _ μ) μ) : ℝ) : ℂ)) =
      2 * Complex.I * ((-θ (FullSpace.forwardEdge (x - axisStep _ μ) μ) : ℝ) : ℂ) := by
    push_cast
    ring
  unfold shiftBackPhase
  rw [e]
  exact norm_exp_two_I_mul_ofReal _
def shiftIsometry : ScalarL2 L →ₗᵢ[ℂ] ScalarL2 L :=
  phaseTwistedIsometry (Equiv.addRight (axisStep _ μ)) (norm_shiftPhase θ μ)
def shiftBackIsometry : ScalarL2 L →ₗᵢ[ℂ] ScalarL2 L :=
  phaseTwistedIsometry (Equiv.subRight (axisStep _ μ)) (norm_shiftBackPhase θ μ)
theorem shiftIsometry_apply (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    shiftIsometry θ μ w x 0 = shiftPhase θ μ x * w (x + axisStep _ μ) 0 :=
  phaseTwistedIsometry_apply _ _ w x
theorem shiftBackIsometry_apply (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    shiftBackIsometry θ μ w x 0 = shiftBackPhase θ μ x * w (x - axisStep _ μ) 0 :=
  phaseTwistedIsometry_apply _ _ w x
theorem scalarL2_ext {w w' : ScalarL2 L} (h : ∀ x, w x 0 = w' x 0) : w = w' := by
  apply lp.ext
  funext x
  ext i
  rw [Subsingleton.elim i 0]
  exact h x
theorem shiftIsometry_shiftBackIsometry (w : ScalarL2 L) :
    shiftIsometry θ μ (shiftBackIsometry θ μ w) = w := by
  refine scalarL2_ext fun x => ?_
  rw [shiftIsometry_apply, shiftBackIsometry_apply]
  unfold shiftPhase shiftBackPhase
  rw [add_sub_cancel_right, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    one_mul]
theorem shiftBackIsometry_shiftIsometry (w : ScalarL2 L) :
    shiftBackIsometry θ μ (shiftIsometry θ μ w) = w := by
  refine scalarL2_ext fun x => ?_
  rw [shiftBackIsometry_apply, shiftIsometry_apply]
  unfold shiftPhase shiftBackPhase
  rw [sub_add_cancel, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
def shiftUnitary : ScalarL2 L ≃ₗᵢ[ℂ] ScalarL2 L where
  toLinearEquiv := LinearEquiv.ofLinearMap (shiftIsometry θ μ).toLinearMap
    (shiftBackIsometry θ μ).toLinearMap (LinearMap.ext (shiftIsometry_shiftBackIsometry θ μ))
    (LinearMap.ext (shiftBackIsometry_shiftIsometry θ μ))
  norm_map' := (shiftIsometry θ μ).norm_map
theorem shiftUnitary_apply (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    shiftUnitary θ μ w x 0 = FullSpace.chargedShift θ μ (fun y => w y 0) x :=
  shiftIsometry_apply θ μ w x
theorem shiftUnitary_symm_apply (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    (shiftUnitary θ μ).symm w x 0 = shiftBackPhase θ μ x * w (x - axisStep _ μ) 0 :=
  shiftBackIsometry_apply θ μ w x
theorem covShift_eval (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    covShift θ μ w x 0 = FullSpace.chargedShift θ μ (fun y => w y 0) x :=
  Classical.epsilon_spec
    (p := fun T : ScalarL2 L →L[ℂ] ScalarL2 L =>
      ∀ (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0),
        T w x 0 = FullSpace.chargedShift θ μ (fun y => w y 0) x)
    ⟨(shiftUnitary θ μ : ScalarL2 L →L[ℂ] ScalarL2 L), shiftUnitary_apply θ μ⟩ w x
theorem covShift_eq_shiftUnitary :
    covShift θ μ = (shiftUnitary θ μ : ScalarL2 L →L[ℂ] ScalarL2 L) := by
  ext1 w
  refine scalarL2_ext fun x => ?_
  rw [covShift_eval]
  exact (shiftUnitary_apply θ μ w x).symm
theorem opAdjoint_covShift_eval (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    opAdjoint (covShift θ μ) w x 0 = shiftBackPhase θ μ x * w (x - axisStep _ μ) 0 := by
  rw [covShift_eq_shiftUnitary]
  unfold opAdjoint
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact shiftUnitary_symm_apply θ μ w x
theorem covShift_isUnitaryOp : UnitaryCombinations.IsUnitaryOp
    (covShift θ μ : ScalarL2 L →ₗ[ℂ] ScalarL2 L) := by
  rw [covShift_eq_shiftUnitary]
  exact ⟨(shiftUnitary θ μ).bijective, (shiftUnitary θ μ).norm_map⟩
end ShiftMaps
section PauliMatrices
theorem raisingPauli_eq_matrix : raisingPauli = !![0, 1; 0, 0] := by
  obtain ⟨h0, h1, -⟩ := ComplexMatrix2.pauliFamily_apply
  unfold raisingPauli
  rw [h0, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf
theorem loweringPauli_eq_matrix : loweringPauli = !![0, 0; 1, 0] := by
  obtain ⟨h0, h1, -⟩ := ComplexMatrix2.pauliFamily_apply
  unfold loweringPauli
  rw [h0, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf
theorem raisingPauli_mem_traceless : raisingPauli ∈ ComplexMatrix2.traceless := by
  show Matrix.trace raisingPauli = 0
  rw [raisingPauli_eq_matrix]
  simp [Matrix.trace_fin_two]
theorem loweringPauli_mem_traceless : loweringPauli ∈ ComplexMatrix2.traceless := by
  show Matrix.trace loweringPauli = 0
  rw [loweringPauli_eq_matrix]
  simp [Matrix.trace_fin_two]
theorem pauliFamily_two_mem_traceless :
    ComplexMatrix2.pauliFamily 2 ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling.pauliFamily_two_mem_traceless <;> assumption
theorem cartanPhase_eq_diagonal (t : ℝ) : cartanPhase t =
    Matrix.diagonal ![Complex.exp (Complex.I * t), Complex.exp (-(Complex.I * t))] := by
  have h : Complex.I • ((t : ℂ) • ComplexMatrix2.pauliFamily 2) =
      Matrix.diagonal ![Complex.I * t, -(Complex.I * t)] := by
    rw [ComplexMatrix2.pauliFamily_apply.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [cartanPhase, h, ComplexMatrix2.matExp, Matrix.exp_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [Complex.exp_eq_exp_ℂ]
theorem cartanPhase_inv_eq_diagonal (t : ℝ) : (cartanPhase t)⁻¹ =
    Matrix.diagonal ![Complex.exp (-(Complex.I * t)), Complex.exp (Complex.I * t)] := by
  rw [cartanPhase_eq_diagonal]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [← Complex.exp_add]
theorem det_cartanPhase (t : ℝ) : (cartanPhase t).det = 1 := by
  rw [cartanPhase_eq_diagonal, Matrix.det_diagonal, Fin.prod_univ_two]
  simp [← Complex.exp_add]
theorem det_cartanPhase_inv (t : ℝ) : ((cartanPhase t)⁻¹).det = 1 := by
  rw [cartanPhase_inv_eq_diagonal, Matrix.det_diagonal, Fin.prod_univ_two]
  simp [← Complex.exp_add]
theorem conjugateBy_cartanPhase (t : ℝ) (M : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (cartanPhase t) M =
    !![M 0 0, Complex.exp (2 * Complex.I * t) * M 0 1;
      Complex.exp (-(2 * Complex.I * t)) * M 1 0, M 1 1] := by
  have h1 : Complex.exp (Complex.I * t) * Complex.exp (-(Complex.I * t)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (2 * Complex.I * t) =
      Complex.exp (Complex.I * t) * Complex.exp (Complex.I * t) := by
    rw [← Complex.exp_add]
    ring_nf
  have h3 : Complex.exp (-(2 * Complex.I * t)) =
      Complex.exp (-(Complex.I * t)) * Complex.exp (-(Complex.I * t)) := by
    rw [← Complex.exp_add]
    ring_nf
  unfold ComplexMatrix2.conjugateBy
  rw [cartanPhase_inv_eq_diagonal, cartanPhase_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h2, h3]
  · linear_combination (M 0 0) * h1
  · ring
  · ring
  · linear_combination (M 1 1) * h1
theorem halfTrace_smul_raisingPauli_mul (c : ℂ) (A : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((c • raisingPauli) * A) = 1 / 2 * (c * A 1 0) := by
  rw [raisingPauli_eq_matrix]
  show (1 / 2 : ℂ) * Matrix.trace _ = _
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp
theorem halfTraceProduct_smul_raisingPauli_re (c : ℂ) :
    (halfTraceProduct (c • raisingPauli) (c • raisingPauli)).re = ‖c‖ ^ 2 / 2 := by
  have e : halfTraceProduct (c • raisingPauli) (c • raisingPauli) = ((‖c‖ ^ 2 / 2 : ℝ) : ℂ) := by
    unfold halfTraceProduct
    rw [raisingPauli_eq_matrix]
    simp [ComplexMatrix2.adjointMatrix, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.conj_mul']
    ring
  rw [e, Complex.ofReal_re]
end PauliMatrices
section PositiveEdges
theorem axisStep_injective : Function.Injective (axisStep (meshAt L 0 0)) := by
  intro μ ν h
  by_contra hne
  have h' := congrArg (fun s : InfiniteLattice.LatticePoint (meshAt L 0 0) =>
    (s : InfiniteLattice.AmbientSpace) μ) h
  simp [axisStep, hne, meshAt_zero_zero] at h'
theorem forwardEdge_bijective : Function.Bijective
    (fun c : Fin 4 × FullSpace.Vertex L 0 0 => FullSpace.forwardEdge c.2 c.1) := by
  constructor
  · rintro ⟨μ, x⟩ ⟨ν, y⟩ h
    have h' := congrArg Subtype.val h
    have ht : x = y := congrArg InfiniteLattice.Link.initial h'
    subst ht
    have hh : x + axisStep _ μ = x + axisStep _ ν := congrArg InfiniteLattice.Link.terminal h'
    have hμ := axisStep_injective (add_left_cancel hh)
    subst hμ
    rfl
  · rintro ⟨b, μ, hμ⟩
    refine ⟨(μ, b.initial), Subtype.ext (InfiniteLattice.Link.ext rfl ?_)⟩
    show b.initial + axisStep _ μ = b.terminal
    rw [← hμ]
    abel
def positiveEdgeEquiv (L : ℕ) :
    Fin 4 × FullSpace.Vertex L 0 0 ≃ FullSpace.PositiveEdge (meshAt L 0 0) :=
  Equiv.ofBijective _ forwardEdge_bijective
theorem existsUnique_forwardEdge_eq (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    ∃! c : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge c.1 c.2 = b := by
  obtain ⟨⟨μ, x⟩, h⟩ := (forwardEdge_bijective (L := L)).2 b
  refine ⟨(x, μ), h, ?_⟩
  rintro ⟨y, ν⟩ h'
  have e := (forwardEdge_bijective (L := L)).1 (a₁ := (ν, y)) (a₂ := (μ, x)) (h'.trans h.symm)
  simp only [Prod.mk.injEq] at e
  exact Prod.ext e.2 e.1
theorem forwardFrom_isPositivelyOriented (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  (FullSpace.forwardEdge x μ).2
theorem not_opposite_isPositivelyOriented {b : FullSpace.Edge L 0 0}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.not_opposite_positive <;> assumption
theorem isPositivelyOriented_or_opposite (b : FullSpace.Edge L 0 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  simpa only [InfiniteLattice.mem_positiveLinks_iff] using
    InfiniteLattice.mem_positiveLinks_or_opposite_mem b
theorem extendOddly_of_positive (f : FullSpace.Edge L 0 0 → ComplexMatrix2)
    {b : FullSpace.Edge L 0 0} (h : b.IsPositivelyOriented) : FullSpace.extendOddly f b = f b :=
  if_pos h
theorem extendOddly_opposite (f : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (b : FullSpace.Edge L 0 0) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by
  unfold FullSpace.extendOddly
  by_cases h : b.IsPositivelyOriented
  · rw [if_neg (not_opposite_isPositivelyOriented h), if_pos h]
    rfl
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left h
    rw [if_pos hr, if_neg h, neg_neg]
end PositiveEdges
section RaisingFunctions
theorem summable_norm_sq_eval (w : ScalarL2 L) : Summable fun x => ‖w x 0‖ ^ 2 := by
  have h := lp.memℓp w
  rw [memℓp_gen_iff (by norm_num)] at h
  refine h.congr fun x => ?_
  have e : ‖(w x : EuclideanSpace ℂ (Fin 1))‖ ^ 2 = ‖w x 0‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [← e]
  simp
theorem raisingVertexFn_isL2Traceless (w : ScalarL2 L) : IsL2Traceless (raisingVertexFn w) := by
  refine ⟨fun x => ComplexMatrix2.traceless.smul_mem _ raisingPauli_mem_traceless, ?_⟩
  refine ((summable_norm_sq_eval w).div_const 2).congr fun x => ?_
  exact (halfTraceProduct_smul_raisingPauli_re _).symm
def raisingEdgeValue (W : Fin 4 → ScalarL2 L) (b : FullSpace.Edge L 0 0) : ComplexMatrix2 :=
  open Classical in
  if h : b.IsPositivelyOriented then W h.choose b.initial 0 • raisingPauli else 0
theorem raisingEdgeValue_forwardFrom (W : Fin 4 → ScalarL2 L) (x : FullSpace.Vertex L 0 0)
    (μ : Fin 4) :
    raisingEdgeValue W (InfiniteLattice.Link.forwardFrom x μ) = W μ x 0 • raisingPauli := by
  have h := forwardFrom_isPositivelyOriented x μ
  unfold raisingEdgeValue
  rw [dif_pos h]
  have hc := h.choose_spec
  have e : h.choose = μ :=
    axisStep_injective (hc.symm.trans (by simp [InfiniteLattice.Link.forwardFrom]))
  rw [e]
  rfl
theorem exists_isRaisingFormOf (W : Fin 4 → ScalarL2 L) : ∃ B, IsRaisingFormOf W B := by
  refine ⟨FullSpace.extendOddly (raisingEdgeValue W), ?_, fun x μ => ?_⟩
  · refine ⟨fun b hb => ?_, extendOddly_opposite _⟩
    rw [extendOddly_of_positive _ hb]
    unfold raisingEdgeValue
    rw [dif_pos hb]
    exact ComplexMatrix2.traceless.smul_mem _ raisingPauli_mem_traceless
  · rw [extendOddly_of_positive _ (forwardFrom_isPositivelyOriented x μ),
      raisingEdgeValue_forwardFrom]
theorem mem_l2Forms_of_isRaisingFormOf (W : Fin 4 → ScalarL2 L)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) (h : IsRaisingFormOf W B) :
    B ∈ FullSpace.l2Forms (meshAt L 0 0) := by
  refine ⟨h.1, fun b => h.1.1 b.1 b.2, ?_⟩
  rw [← (positiveEdgeEquiv L).summable_iff]
  have hs : Summable fun c : Fin 4 × FullSpace.Vertex L 0 0 => ‖W c.1 c.2 0‖ ^ 2 / 2 :=
    (summable_prod_of_nonneg fun c => by positivity).2
      ⟨fun μ => (summable_norm_sq_eval (W μ)).div_const 2, (hasSum_fintype _).summable⟩
  refine hs.congr fun c => ?_
  show _ = (halfTraceProduct (B (InfiniteLattice.Link.forwardFrom c.2 c.1))
    (B (InfiniteLattice.Link.forwardFrom c.2 c.1))).re
  rw [h.2, halfTraceProduct_smul_raisingPauli_re]
end RaisingFunctions
section AdjointOnRaising
variable (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
theorem abelianLinkField_positive (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.abelianLinkField θ b.1 = cartanPhase (θ b) :=
  dif_pos b.2
theorem abelianLinkField_forwardFrom (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.abelianLinkField θ (InfiniteLattice.Link.forwardFrom x μ) =
      cartanPhase (θ (FullSpace.forwardEdge x μ)) :=
  abelianLinkField_positive θ (FullSpace.forwardEdge x μ)
theorem abelianLinkField_negative {b : FullSpace.Edge L 0 0} (h : ¬ b.IsPositivelyOriented)
    (h' : b.opposite.IsPositivelyOriented) :
    FullSpace.abelianLinkField θ b = (cartanPhase (θ ⟨b.opposite, h'⟩))⁻¹ := by
  unfold FullSpace.abelianLinkField
  rw [dif_neg h, dif_pos h']
  rfl
theorem abelianLinkField_mem_fieldsValuedIn :
    FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · exact (abelianLinkField_positive θ ⟨b, h⟩).symm ▸ det_cartanPhase _
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left h
      exact (abelianLinkField_negative θ h hr).symm ▸ det_cartanPhase_inv _
  · by_cases h : b.IsPositivelyOriented
    · rw [abelianLinkField_negative θ (not_opposite_isPositivelyOriented h) h,
        abelianLinkField_positive θ ⟨b, h⟩]
      rfl
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left h
      rw [abelianLinkField_positive θ ⟨b.opposite, hr⟩, abelianLinkField_negative θ h hr,
        Matrix.nonsing_inv_nonsing_inv]
      rw [det_cartanPhase]
      exact isUnit_one
theorem scalarL2_sub_eval (w w' : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    (w - w') x 0 = w x 0 - w' x 0 := by
  simp
theorem covShiftSubOne_eval (μ : Fin 4) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    covShiftSubOne θ μ w x 0 = shiftPhase θ μ x * w (x + axisStep _ μ) 0 - w x 0 := by
  show (covShift θ μ w - w) x 0 = _
  rw [scalarL2_sub_eval, covShift_eval]
  rfl
theorem covShiftAdjSubOne_eval (μ : Fin 4) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    covShiftAdjSubOne θ μ w x 0 = shiftBackPhase θ μ x * w (x - axisStep _ μ) 0 - w x 0 := by
  show (opAdjoint (covShift θ μ) w - w) x 0 = _
  rw [scalarL2_sub_eval, opAdjoint_covShift_eval]
theorem covDiff_raisingVertexFn_forwardFrom (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0)
    (μ : Fin 4) :
    FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w)
        (InfiniteLattice.Link.forwardFrom x μ) = covShiftSubOne θ μ w x 0 • raisingPauli := by
  unfold FullSpace.covDiff
  rw [extendOddly_of_positive _ (forwardFrom_isPositivelyOriented x μ),
    abelianLinkField_forwardFrom, conjugateBy_cartanPhase, covShiftSubOne_eval]
  unfold raisingVertexFn shiftPhase
  show _ - _ • raisingPauli = _
  simp only [InfiniteLattice.Link.forwardFrom]
  rw [raisingPauli_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem covDiff_forwardFrom_apply_one_zero (l : FullSpace.Vertex L 0 0 → ComplexMatrix2)
    (y : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.covDiff (FullSpace.abelianLinkField θ) l (InfiniteLattice.Link.forwardFrom y μ)
        1 0 =
      Complex.exp (-(2 * Complex.I * (θ (FullSpace.forwardEdge y μ) : ℂ))) *
          l (y + axisStep _ μ) 1 0 - l y 1 0 := by
  unfold FullSpace.covDiff
  rw [extendOddly_of_positive _ (forwardFrom_isPositivelyOriented y μ),
    abelianLinkField_forwardFrom, conjugateBy_cartanPhase]
  simp [InfiniteLattice.Link.forwardFrom]
theorem finsum_incidence_at_vertex (x : FullSpace.Vertex L 0 0)
    (p q : Fin 4 → FullSpace.Vertex L 0 0 → ℂ) (ζ : ℂ) :
    open Classical in
    ∑ᶠ c : Fin 4 × FullSpace.Vertex L 0 0,
        (p c.1 c.2 * (if c.2 + axisStep _ c.1 = x then ζ else 0) -
          q c.1 c.2 * (if c.2 = x then ζ else 0)) =
      ζ * ∑ μ, (p μ (x - axisStep _ μ) - q μ x) := by
  classical
  have hs : (Function.support fun c : Fin 4 × FullSpace.Vertex L 0 0 =>
      (p c.1 c.2 * (if c.2 + axisStep _ c.1 = x then ζ else 0) -
        q c.1 c.2 * (if c.2 = x then ζ else 0))).Finite := by
    refine ((Set.finite_range fun μ : Fin 4 => (μ, x)).union
      (Set.finite_range fun μ : Fin 4 => (μ, x - axisStep _ μ))).subset ?_
    rintro ⟨μ, y⟩ hc
    by_cases h₁ : y = x
    · exact Or.inl ⟨μ, by rw [h₁]⟩
    · by_cases h₂ : y + axisStep _ μ = x
      · refine Or.inr ⟨μ, ?_⟩
        show (μ, x - axisStep _ μ) = (μ, y)
        rw [← h₂, add_sub_cancel_right]
      · exact absurd (by simp [h₁, h₂]) hc
  rw [finsum_curry _ hs, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h₁ : (Function.support fun y : FullSpace.Vertex L 0 0 =>
      p μ y * (if y + axisStep _ μ = x then ζ else 0)).Finite := by
    refine (Set.finite_singleton (x - axisStep _ μ)).subset fun y hy => ?_
    by_contra hn
    have hne : y + axisStep _ μ ≠ x := fun e => hn (by rw [← e, add_sub_cancel_right]; rfl)
    exact hy (by simp [hne])
  have h₂ : (Function.support fun y : FullSpace.Vertex L 0 0 =>
      q μ y * (if y = x then ζ else 0)).Finite := by
    refine (Set.finite_singleton x).subset fun y hy => ?_
    by_contra hn
    have hne : y ≠ x := hn
    exact hy (by simp [hne])
  show ∑ᶠ y : FullSpace.Vertex L 0 0, (p μ y * (if y + axisStep _ μ = x then ζ else 0) -
    q μ y * (if y = x then ζ else 0)) = _
  rw [finsum_sub_distrib h₁ h₂, finsum_eq_single _ (x - axisStep _ μ),
    finsum_eq_single _ x]
  · simp
    ring
  · intro y hy
    simp [hy]
  · intro y hy
    have hne : y + axisStep _ μ ≠ x := fun e => hy (by rw [← e, add_sub_cancel_right])
    simp [hne]
open UnitGaugeDirections in
theorem halfTrace_covDiffAdjoint_mul
    (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    (W : Fin 4 → ScalarL2 L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (h : IsRaisingFormOf W B) (x : FullSpace.Vertex L 0 0) (X : ComplexMatrix2)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x * X) =
      1 / 2 * (X 1 0 * ∑ μ, covShiftAdjSubOne θ μ (W μ) x 0) := by
  classical
  obtain ⟨-, hM, -, hT, hV⟩ := hD
  let l : FullSpace.Vertex L 0 0 → ComplexMatrix2 := fun y => if y = x then X else 0
  have hl : l ∈ (unitVertexSpace L).complexSubmodule := by
    intro y _
    by_cases hy : y = x
    · simpa [l, hy] using hX
    · simp [l, hy]
  have hfin : (unitVertexSpace L).IsFinitelySupported l := by
    refine (Set.finite_singleton x).subset fun y hy => ?_
    by_contra hn
    have hne : y ≠ x := hn
    exact hy (by simp [l, hne])
  have hp := hT ⟨B, h.1⟩ ⟨l, hl⟩ hfin
  have e : traceFinsumPairing (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B) l =
      FullSpace.finiteEdgePairing B (FullSpace.covDiff (FullSpace.abelianLinkField θ) l) := by
    have e₁ := hV ⟨B, h.1⟩
    have e₂ := hM ⟨l, hl⟩
    simp only at e₁ e₂
    rw [e₁, ← e₂]
    exact hp
  have eL : traceFinsumPairing (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B) l =
      ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x * X) := by
    unfold traceFinsumPairing
    rw [finsum_eq_single _ x]
    · simp [l]
    · intro y hy
      simp [l, hy]
  have hv : ∀ y, l y 1 0 = if y = x then X 1 0 else 0 := by
    intro y
    by_cases hy : y = x
    · simp [l, hy]
    · simp [l, hy]
  rw [← eL, e]
  unfold FullSpace.finiteEdgePairing traceFinsumPairing
  rw [← finsum_comp_equiv (positiveEdgeEquiv L)]
  have hterm : ∀ c : Fin 4 × FullSpace.Vertex L 0 0,
      ComplexMatrix2.halfTrace (FullSpace.restrictToPositiveEdges B (positiveEdgeEquiv L c) *
          FullSpace.restrictToPositiveEdges
            (FullSpace.covDiff (FullSpace.abelianLinkField θ) l) (positiveEdgeEquiv L c)) =
        (1 / 2 * (W c.1 c.2 0 *
            Complex.exp (-(2 * Complex.I * (θ (FullSpace.forwardEdge c.2 c.1) : ℂ))))) *
            (if c.2 + axisStep _ c.1 = x then X 1 0 else 0) -
          (1 / 2 * W c.1 c.2 0) * (if c.2 = x then X 1 0 else 0) := by
    intro c
    show ComplexMatrix2.halfTrace (B (InfiniteLattice.Link.forwardFrom c.2 c.1) *
      FullSpace.covDiff (FullSpace.abelianLinkField θ) l
        (InfiniteLattice.Link.forwardFrom c.2 c.1)) = _
    rw [h.2, halfTrace_smul_raisingPauli_mul, covDiff_forwardFrom_apply_one_zero, hv, hv]
    ring
  simp only [hterm]
  rw [finsum_incidence_at_vertex x (fun μ y => 1 / 2 * (W μ y 0 *
      Complex.exp (-(2 * Complex.I * (θ (FullSpace.forwardEdge y μ) : ℂ)))))
    (fun μ y => 1 / 2 * W μ y 0) (X 1 0)]
  simp only [covShiftAdjSubOne_eval]
  rw [mul_left_comm (1 / 2 : ℂ)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold shiftBackPhase
  ring
theorem eq_smul_raisingPauli_of_halfTraces (Y : ComplexMatrix2) (φ : ℂ)
    (hY : Y ∈ ComplexMatrix2.traceless)
    (h₁ : ComplexMatrix2.halfTrace (Y * raisingPauli) = 1 / 2 * (raisingPauli 1 0 * φ))
    (h₂ : ComplexMatrix2.halfTrace (Y * loweringPauli) = 1 / 2 * (loweringPauli 1 0 * φ))
    (h₃ : ComplexMatrix2.halfTrace (Y * ComplexMatrix2.pauliFamily 2) =
      1 / 2 * (ComplexMatrix2.pauliFamily 2 1 0 * φ)) :
    Y = φ • raisingPauli := by
  have hT : ∀ a b c d : ℂ, ComplexMatrix2.halfTrace (Y * !![a, b; c, d]) =
      1 / 2 * (Y 0 0 * a + Y 0 1 * c + Y 1 0 * b + Y 1 1 * d) := by
    intro a b c d
    show (1 / 2 : ℂ) * Matrix.trace _ = _
    rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
    ring
  have htr : Y 0 0 + Y 1 1 = 0 := by
    have h : Matrix.trace Y = 0 := hY
    rwa [Matrix.trace_fin_two] at h
  rw [raisingPauli_eq_matrix, hT] at h₁
  rw [loweringPauli_eq_matrix, hT] at h₂
  rw [ComplexMatrix2.pauliFamily_apply.2.2, hT] at h₃
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h₁ h₂ h₃
  rw [raisingPauli_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (1 / 2) * htr + h₃
  · linear_combination 2 * h₂
  · linear_combination 2 * h₁
  · linear_combination (1 / 2) * htr - h₃
open UnitGaugeDirections in
theorem covDiffAdjoint_eq_smul_raisingPauli
    (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    (W : Fin 4 → ScalarL2 L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (h : IsRaisingFormOf W B) (x : FullSpace.Vertex L 0 0) :
    FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x =
      (∑ μ, covShiftAdjSubOne θ μ (W μ) x 0) • raisingPauli := by
  refine eq_smul_raisingPauli_of_halfTraces _ _ ?_
    (halfTrace_covDiffAdjoint_mul θ hD W B h x _ raisingPauli_mem_traceless)
    (halfTrace_covDiffAdjoint_mul θ hD W B h x _ loweringPauli_mem_traceless)
    (halfTrace_covDiffAdjoint_mul θ hD W B h x _ pauliFamily_two_mem_traceless)
  have e := hD.2.2.2.2 ⟨B, h.1⟩
  simp only at e
  rw [e]
  exact ((PairedFunctionSpace.transposeMap (_root_.YangMills.Construction.Tower.UnitGaugeDirections.covDiffLinear (FullSpace.abelianLinkField θ)))
    ⟨B, h.1⟩).2 x (Set.mem_univ x)
end AdjointOnRaising
theorem covariantShiftsUnitary_of_unitGaugeDirections (hGauge : UnitGaugeDirections.Claim) :
    CovariantShiftsUnitary := by
  intro L hL θ
  have hD := ((hGauge L hL).2 _ (abelianLinkField_mem_fieldsValuedIn θ)).1
  exact
    { covShift_apply := covShift_eval θ
      covShift_unitary := covShift_isUnitaryOp θ
      existsUnique_forwardEdge := existsUnique_forwardEdge_eq
      raisingVertexFn_l2 := raisingVertexFn_isL2Traceless
      exists_raisingForm := exists_isRaisingFormOf
      raisingForm_l2 := mem_l2Forms_of_isRaisingFormOf
      covDiff_raising := fun w x μ => covDiff_raisingVertexFn_forwardFrom θ w x μ
      covDiffAdjoint_raising := fun W B h x => covDiffAdjoint_eq_smul_raisingPauli θ hD W B h x }
end YangMills.Construction.Tower.AbelianShiftsProof
end
