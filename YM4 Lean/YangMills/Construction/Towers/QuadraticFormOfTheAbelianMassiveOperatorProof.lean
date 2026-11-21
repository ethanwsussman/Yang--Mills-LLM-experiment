import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianFieldProof
import YangMills.Construction.Towers.QuadraticFormOfTheAbelianMassiveOperator
import YangMills.Construction.Towers.TheAlgebraOfTheCharges
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
open Function (support)
noncomputable section
namespace YangMills.Construction.Tower.MassiveFormExpansion
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.AbelianFieldFacts
section PauliMatrices
theorem pauliFamily_two_eq : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] :=
  ComplexMatrix2.pauliFamily_apply.2.2
theorem raisingPauli_eq : raisingPauli = !![0, 1; 0, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_eq_matrix <;> assumption
theorem loweringPauli_eq : loweringPauli = !![0, 0; 1, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_eq_matrix <;> assumption
theorem cartanCombination_eq (c s r : ℂ) :
    c • ComplexMatrix2.pauliFamily 2 + s • raisingPauli + r • loweringPauli = !![c, s; r, -c] := by
  rw [pauliFamily_two_eq, raisingPauli_eq, loweringPauli_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem halfTrace_mul_pauliFamily_two (A : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * ComplexMatrix2.pauliFamily 2) = (1 / 2) * (A 0 0 - A 1 1) := by
  rw [pauliFamily_two_eq]
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring
theorem halfTrace_mul_loweringPauli (A : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * loweringPauli) = (1 / 2) * A 0 1 := by
  rw [loweringPauli_eq]
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
theorem halfTrace_mul_raisingPauli (A : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * raisingPauli) = (1 / 2) * A 1 0 := by
  rw [raisingPauli_eq]
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
theorem halfTrace_self_mul_of_traceless (A : ComplexMatrix2) (hA : ComplexMatrix2.fullTrace A = 0) :
    ComplexMatrix2.halfTrace (A * A) =
      ComplexMatrix2.halfTrace (A * ComplexMatrix2.pauliFamily 2) ^ 2 +
      4 * ComplexMatrix2.halfTrace (A * loweringPauli) * ComplexMatrix2.halfTrace (A * raisingPauli) := by
  have hdiag : A 1 1 = -A 0 0 := by
    have hsum : A 0 0 + A 1 1 = 0 := by
      simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using hA
    linear_combination hsum
  rw [halfTrace_mul_pauliFamily_two, halfTrace_mul_loweringPauli, halfTrace_mul_raisingPauli]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, hdiag]
  ring
theorem halfTrace_cartanCombination_sq (c s r : ℂ) :
    ComplexMatrix2.halfTrace
      ((c • ComplexMatrix2.pauliFamily 2 + s • raisingPauli + r • loweringPauli) *
        (c • ComplexMatrix2.pauliFamily 2 + s • raisingPauli + r • loweringPauli)) =
      c ^ 2 + s * r := by
  rw [cartanCombination_eq]
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring
theorem sum_Ioi_fin_four {M : Type} [AddCommMonoid M] (g : Fin 4 → Fin 4 → M) :
    ∑ i : Fin 4, ∑ m ∈ Finset.Ioi i, g i m =
      g 0 1 + g 0 2 + g 0 3 + g 1 2 + g 1 3 + g 2 3 := by
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp [add_assoc]
theorem sum_filter_lt_fin_four {M : Type} [AddCommMonoid M] (g : Fin 4 × Fin 4 → M) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin 4 × Fin 4 => c.1 < c.2), g c =
      g (0, 1) + g (0, 2) + g (0, 3) + g (1, 2) + g (1, 3) + g (2, 3) := by
  have hpairs : Finset.univ.filter (fun c : Fin 4 × Fin 4 => c.1 < c.2) =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  rw [hpairs]
  simp [add_assoc]
end PauliMatrices
section OneFace
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
theorem sum_transportedForm (h : FaceVariables θ) {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0)) (p : FullSpace.Face L 0 0) :
    ∑ i, FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p i =
      ((FullSpace.edgeDifference (FullSpace.diagonalComponent B) p : ℝ) : ℂ) •
          ComplexMatrix2.pauliFamily 2 +
        (∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i) • raisingPauli +
        conj (∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i) •
          loweringPauli := by
  have hc : ∑ i, transportSign i *
      ((FullSpace.diagonalComponent B (facePositiveEdge p i) : ℝ) : ℂ) =
      ((FullSpace.edgeDifference (FullSpace.diagonalComponent B) p : ℝ) : ℂ) := by
    simp [Fin.sum_univ_four, transportSign, facePositiveEdge, FullSpace.edgeDifference]
    ring
  simp only [h.transportedForm_eq B hB p, Finset.sum_add_distrib, ← Finset.sum_smul, map_sum, hc]
theorem secondDerivExpr_eq_faceTerm (h : FaceVariables θ)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0)) (p : FullSpace.Face L 0 0) :
    FaceTermDerivatives.secondDerivExpr
        (FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p)
        (FullSpace.faceVariable (FullSpace.abelianLinkField θ) p) =
      ((_root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm θ B p : ℝ) : ℂ) := by
  have hcomm : ∀ i j : Fin 4, (Complex.I / 2) *
      ComplexMatrix2.fullTrace ((FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p i *
          FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p j -
        FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p j *
          FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p i) *
            ComplexMatrix2.pauliFamily 2) =
      ((-2 * (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i *
        conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p j)).im : ℝ) : ℂ) := by
    intro i j
    have hij := h.lie_trace B hB p i j
    rwa [Ring.lie_def] at hij
  have h01 := hcomm 0 1
  have h02 := hcomm 0 2
  have h03 := hcomm 0 3
  have h12 := hcomm 1 2
  have h13 := hcomm 1 3
  have h23 := hcomm 2 3
  have hnorm : (∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i) *
      conj (∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i) =
      ((‖∑ i, FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold FaceTermDerivatives.secondDerivExpr FaceTermDerivatives.commutatorSum
  rw [sum_transportedForm h hB, halfTrace_cartanCombination_sq, h.half_fullTrace p,
    h.faceVariable_sub_inv p, sum_Ioi_fin_four]
  simp only [_root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm]
  rw [sum_filter_lt_fin_four (fun c : Fin 4 × Fin 4 =>
    (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p c.1 *
      conj (FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p c.2)).im)]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, smul_eq_mul,
    ComplexMatrix2.fullTrace] at h01 h02 h03 h12 h13 h23 ⊢
  rw [hnorm]
  push_cast at h01 h02 h03 h12 h13 h23 ⊢
  linear_combination
    Complex.sin ((FullSpace.faceAngle θ p : ℝ) : ℂ) * (h01 + h02 + h03 + h12 + h13 + h23)
theorem faceTerm_eq_zero (h : FaceVariables θ) {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0)) (p : FullSpace.Face L 0 0)
    (hz : ∀ i, B (FullSpace.faceEdge p i) = 0) : _root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm θ B p = 0 := by
  have hY : FullSpace.transportedForm (FullSpace.abelianLinkField θ) B p = 0 := by
    funext i
    simp [FullSpace.transportedForm, hz, ComplexMatrix2.conjugateBy]
  have hexpr := secondDerivExpr_eq_faceTerm h hB p
  rw [hY] at hexpr
  simp [FaceTermDerivatives.secondDerivExpr,
    FaceTermDerivatives.commutatorSum, ComplexMatrix2.halfTrace] at hexpr
  first | exact hexpr | exact hexpr.symm | exact_mod_cast hexpr.symm
theorem finite_support_faceTerm (h : FaceVariables θ)
    (hFin : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L 0 0)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0))
    (hfin : FullSpace.HasFiniteEdgeSupport B) : (support (_root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm θ B)).Finite := by
  refine ((hFin.2.1 (FullSpace.edgeSupport B) hfin fun b hb => hb.1).1).subset fun p hp => ?_
  by_contra hn
  refine (Function.mem_support.1 hp) (faceTerm_eq_zero h hB p fun i => ?_)
  by_contra hi
  have hmem : FullSpace.faceEdge p i ∈ FullSpace.faceEdges p := List.getElem_mem _
  exact hn ⟨_, ⟨hFin.1.2 p _ hmem, hi⟩, hmem⟩
end OneFace
section OneVertex
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
open YangMills.Construction.Tower.UnitGaugeDirections
theorem conjugateBy_smul (V A : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • A) = c • ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem halfTrace_cartanCombination_mul_pauli (c s r : ℂ) : ComplexMatrix2.halfTrace
    ((c • ComplexMatrix2.pauliFamily 2 + s • raisingPauli + r • loweringPauli) *
      ComplexMatrix2.pauliFamily 2) = c := by
  rw [cartanCombination_eq, halfTrace_mul_pauliFamily_two]
  simp
  ring
theorem halfTrace_cartanCombination_mul_lowering (c s r : ℂ) : ComplexMatrix2.halfTrace
    ((c • ComplexMatrix2.pauliFamily 2 + s • raisingPauli + r • loweringPauli) * loweringPauli) =
      (1 / 2) * s := by
  rw [cartanCombination_eq, halfTrace_mul_loweringPauli]
  simp
theorem halfTrace_cartanCombination_mul_raising (c s r : ℂ) : ComplexMatrix2.halfTrace
    ((c • ComplexMatrix2.pauliFamily 2 + s • raisingPauli + r • loweringPauli) * raisingPauli) =
      (1 / 2) * r := by
  rw [cartanCombination_eq, halfTrace_mul_raisingPauli]
  simp
theorem pauliFamily_two_mem_traceless : ComplexMatrix2.pauliFamily 2 ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling.pauliFamily_two_mem_traceless <;> assumption
theorem raisingPauli_mem_traceless : raisingPauli ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_mem_traceless <;> assumption
theorem loweringPauli_mem_traceless : loweringPauli ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_mem_traceless <;> assumption
def vertexIndicator (R : Type) [Zero R] [One R] (x : FullSpace.Vertex L 0 0) :
    FullSpace.Vertex L 0 0 → R :=
  open Classical in fun y => if y = x then 1 else 0
theorem ofReal_vertexIndicator (x y : FullSpace.Vertex L 0 0) :
    ((vertexIndicator ℝ x y : ℝ) : ℂ) = vertexIndicator ℂ x y := by
  by_cases h : y = x <;> simp [vertexIndicator, h]
theorem conj_vertexIndicator (x y : FullSpace.Vertex L 0 0) :
    conj (vertexIndicator ℂ x y) = vertexIndicator ℂ x y := by
  by_cases h : y = x <;> simp [vertexIndicator, h]
theorem finite_support_vertexIndicator (R : Type) [Zero R] [One R] (x : FullSpace.Vertex L 0 0) :
    (support (vertexIndicator R x)).Finite := by
  refine (Set.finite_singleton x).subset fun y hy => ?_
  by_contra h
  exact (Function.mem_support.1 hy) (by simp [vertexIndicator, show y ≠ x from h])
theorem abelianLinkField_positive (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.abelianLinkField θ b.1 = cartanPhase (θ b) :=
  dif_pos b.2
theorem covDiff_smul_eigen {X : ComplexMatrix2} (χ : ℝ → ℂ)
    (hX : ∀ b, ComplexMatrix2.conjugateBy (cartanPhase (θ b)) X = χ (θ b) • X)
    (v : FullSpace.Vertex L 0 0 → ℂ) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.covDiff (FullSpace.abelianLinkField θ) (fun y => v y • X) b.1 =
      (χ (θ b) * v b.1.terminal - v b.1.initial) • X := by
  have hb : FullSpace.covDiff (FullSpace.abelianLinkField θ) (fun y => v y • X) b.1 =
      ComplexMatrix2.conjugateBy (FullSpace.abelianLinkField θ b.1) (v b.1.terminal • X) -
        v b.1.initial • X :=
    if_pos b.2
  rw [hb, abelianLinkField_positive, conjugateBy_smul, hX, smul_smul, sub_smul, mul_comm]
theorem covDiffAdjoint_pairing {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hD : CovDiffAndAdjoint U)
    {g : FullSpace.Edge L 0 0 → ComplexMatrix2} (hg : g ∈ (unitEdgeSpace L).complexSubmodule)
    {f : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hf : f ∈ (unitVertexSpace L).complexSubmodule)
    (hfin : HasFiniteSupp f) :
    traceFinsumPairing (FullSpace.covDiffAdjoint U g) f =
      FullSpace.finiteEdgePairing g (FullSpace.covDiff U f) := by
  obtain ⟨-, h2, -, h4, h5⟩ := hD
  have hpair := h4 ⟨g, hg⟩ ⟨f, hf⟩ hfin
  rw [h5 ⟨g, hg⟩, ← h2 ⟨f, hf⟩]
  exact hpair
theorem traceFinsumPairing_vertexIndicator (f : FullSpace.Vertex L 0 0 → ComplexMatrix2)
    (x : FullSpace.Vertex L 0 0) (X : ComplexMatrix2) :
    traceFinsumPairing f (fun y => vertexIndicator ℂ x y • X) =
      ComplexMatrix2.halfTrace (f x * X) := by
  unfold traceFinsumPairing
  rw [finsum_eq_single _ x fun y hy => by simp [vertexIndicator, hy]]
  simp [vertexIndicator]
def edgeWeight (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (χ : ℝ → ℂ)
    (x : FullSpace.Vertex L 0 0) (b : FullSpace.PositiveEdge (meshAt L 0 0)) : ℂ :=
  χ (θ b) * vertexIndicator ℂ x b.1.terminal - vertexIndicator ℂ x b.1.initial
theorem halfTrace_covDiffAdjoint_mul_eigen
    (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    {g : FullSpace.Edge L 0 0 → ComplexMatrix2} (hg : g ∈ (unitEdgeSpace L).complexSubmodule)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (χ : ℝ → ℂ)
    (hχ : ∀ b, ComplexMatrix2.conjugateBy (cartanPhase (θ b)) X = χ (θ b) • X)
    (x : FullSpace.Vertex L 0 0) :
    ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) g x * X) =
      ∑ᶠ b, edgeWeight θ χ x b * ComplexMatrix2.halfTrace (g b.1 * X) := by
  have hl : (fun y => vertexIndicator ℂ x y • X) ∈ (unitVertexSpace L).complexSubmodule :=
    fun y _ => ComplexMatrix2.traceless.smul_mem _ hX
  have hf : HasFiniteSupp fun y => vertexIndicator ℂ x y • X := by
    refine (finite_support_vertexIndicator ℂ x).subset fun y hy => ?_
    by_contra h
    exact (Function.mem_support.1 hy) (by simp [Function.notMem_support.1 h])
  have hpair := covDiffAdjoint_pairing hD hg hl hf
  rw [traceFinsumPairing_vertexIndicator] at hpair
  rw [hpair]
  refine finsum_congr fun b => ?_
  show ComplexMatrix2.halfTrace (g b.1 * FullSpace.covDiff _ _ b.1) = _
  rw [covDiff_smul_eigen χ hχ, edgeWeight]
  simp only [Matrix.mul_smul, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_smul, smul_eq_mul]
  ring
end OneVertex
section TheForm
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
open YangMills.Construction.Tower.UnitGaugeDirections
theorem mem_complexEdgeForms_of_mem {a : ℝ} {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace a) : B ∈ FullSpace.complexEdgeForms a :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem finite_support_of_forall_eq_zero {E : Type} [Zero E]
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hfin : FullSpace.HasFiniteEdgeSupport B) {f : FullSpace.PositiveEdge (meshAt L 0 0) → E}
    (hf : ∀ b, B b.1 = 0 → f b = 0) : (support f).Finite := by
  refine (hfin.preimage Subtype.val_injective.injOn).subset fun b hb => ?_
  exact ⟨b.2, fun h => (Function.mem_support.1 hb) (hf b h)⟩
theorem traceFinsumPairing_add_right {ι : Type*} {f : ι → ComplexMatrix2} (g h : ι → ComplexMatrix2)
    (hf : (support f).Finite) :
    traceFinsumPairing f (g + h) = traceFinsumPairing f g + traceFinsumPairing f h := by
  unfold traceFinsumPairing
  rw [← finsum_add_distrib]
  · refine finsum_congr fun i => ?_
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.mul_add, Matrix.trace_add,
      mul_add]
  · refine hf.subset fun i hi => ?_
    by_contra hn
    exact (Function.mem_support.1 hi)
      (by simp [Function.notMem_support.1 hn, ComplexMatrix2.halfTrace])
  · refine hf.subset fun i hi => ?_
    by_contra hn
    exact (Function.mem_support.1 hi)
      (by simp [Function.notMem_support.1 hn, ComplexMatrix2.halfTrace])
theorem finite_support_edgeComponent {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hfin : FullSpace.HasFiniteEdgeSupport B) (μ : Fin 4) :
    (support (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ)).Finite := by
  refine (hfin.image InfiniteLattice.Link.initial).subset fun y hy => ?_
  refine ⟨(FullSpace.forwardEdge y μ).1, ⟨(FullSpace.forwardEdge y μ).2, fun h => ?_⟩, rfl⟩
  refine (Function.mem_support.1 hy) ?_
  show 2 * ComplexMatrix2.halfTrace (B (FullSpace.forwardEdge y μ).1 * loweringPauli) = 0
  rw [h]
  simp [ComplexMatrix2.halfTrace]
theorem toScalarL2_apply (v : FullSpace.Vertex L 0 0 → ℂ) (hv : (support v).Finite)
    (x : FullSpace.Vertex L 0 0) : toScalarL2 v x 0 = v x := by
  have hmem : Memℓp (fun y : FullSpace.Vertex L 0 0 =>
      (EuclideanSpace.single (0 : Fin 1) (v y) : EuclideanSpace ℂ (Fin 1))) 2 := by
    refine memℓp_gen (summable_of_finite_support (hv.subset fun y hy => ?_))
    by_contra hn
    exact (Function.mem_support.1 hy) (by simp [Function.notMem_support.1 hn])
  have hex : ∃ w : UnitaryCombinations.ScalarL2 L, ∀ x, w x 0 = v x :=
    ⟨⟨_, hmem⟩, fun y => by simp⟩
  exact Classical.epsilon_spec hex x
theorem halfTrace_smul_raising_mul_lowering (s : ℂ) :
    ComplexMatrix2.halfTrace ((s • raisingPauli) * loweringPauli) = (1 / 2) * s := by
  rw [halfTrace_mul_loweringPauli, raisingPauli_eq]
  simp
def expTwoI (ϑ : ℝ) : ℂ := Complex.exp (2 * Complex.I * (ϑ : ℂ))
def expNegTwoI (ϑ : ℝ) : ℂ := Complex.exp (-(2 * Complex.I * (ϑ : ℂ)))
theorem conj_expNegTwoI (ϑ : ℝ) : conj (expNegTwoI ϑ) = expTwoI ϑ := by
  simp [expNegTwoI, expTwoI, ← Complex.exp_conj, map_ofNat]
theorem conjugateBy_pauli_of_eigen (hBr : ⁅raisingPauli, loweringPauli⁆ = ComplexMatrix2.pauliFamily 2)
    (V : ComplexMatrix2) (hV : IsUnit V.det) (e e' : ℂ)
    (h₁ : ComplexMatrix2.conjugateBy V raisingPauli = e • raisingPauli)
    (h₂ : ComplexMatrix2.conjugateBy V loweringPauli = e' • loweringPauli) (hee : e * e' = 1) :
    ComplexMatrix2.conjugateBy V (ComplexMatrix2.pauliFamily 2) =
      (1 : ℂ) • ComplexMatrix2.pauliFamily 2 := by
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hV
  have hmul : ∀ X Y : ComplexMatrix2, ComplexMatrix2.conjugateBy V (X * Y) =
      ComplexMatrix2.conjugateBy V X * ComplexMatrix2.conjugateBy V Y := by
    intro X Y
    have hassoc : V * X * V⁻¹ * (V * Y * V⁻¹) = V * X * (V⁻¹ * V) * Y * V⁻¹ := by
      simp only [mul_assoc]
    simp only [ComplexMatrix2.conjugateBy]
    rw [hassoc, hinv]
    simp only [mul_one, mul_assoc]
  have hsub : ∀ X Y : ComplexMatrix2, ComplexMatrix2.conjugateBy V (X - Y) =
      ComplexMatrix2.conjugateBy V X - ComplexMatrix2.conjugateBy V Y := by
    intro X Y
    simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
  rw [← hBr, Ring.lie_def, hsub, hmul, hmul, h₁, h₂, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm e' e, hee, one_smul, one_smul, one_smul]
theorem isUnit_det_cartanPhase (hP : FaceVariables θ) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    IsUnit (cartanPhase (θ b)).det := by
  have h := hP.abelianLinkField_mem.1 b.1
  rw [abelianLinkField_positive] at h
  have h1 := (Matrix.mem_specialUnitaryGroup_iff.1 h).2
  rw [h1]
  exact isUnit_one
theorem conjugateBy_cartanPhase_pauli (hAlg : ChargeAlgebra) (hP : FaceVariables θ)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    ComplexMatrix2.conjugateBy (cartanPhase (θ b)) (ComplexMatrix2.pauliFamily 2) =
      (1 : ℂ) • ComplexMatrix2.pauliFamily 2 := by
  refine conjugateBy_pauli_of_eigen hAlg.2.1 _ (isUnit_det_cartanPhase hP b) (expTwoI (θ b))
    (expNegTwoI (θ b)) (hAlg.1 (θ b)).1 (hAlg.1 (θ b)).2 ?_
  rw [expTwoI, expNegTwoI, ← Complex.exp_add]
  simp
theorem diagonal_coordinate (hAlg : ChargeAlgebra)
    (hForms : FormsChargeDecomposition (meshAt L 0 0)) (hP : FaceVariables θ)
    (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    (hT : FullSpace.IsVertexAdjoint (FullSpace.vertexAdjoint (a := meshAt L 0 0) (R := ℝ)))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0))
    (hfin : FullSpace.HasFiniteEdgeSupport B) (x : FullSpace.Vertex L 0 0) :
    ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x *
          ComplexMatrix2.pauliFamily 2) =
      ((FullSpace.vertexAdjoint (FullSpace.diagonalComponent B) x : ℝ) : ℂ) := by
  rw [halfTrace_covDiffAdjoint_mul_eigen hD (mem_complexEdgeForms_of_mem hB)
    pauliFamily_two_mem_traceless (fun _ => 1) (conjugateBy_cartanPhase_pauli hAlg hP) x]
  have hN : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
      ComplexMatrix2.halfTrace (B b.1 * ComplexMatrix2.pauliFamily 2) =
        ((FullSpace.diagonalComponent B b : ℝ) : ℂ) := by
    intro b
    rw [(hForms B hB b).1, halfTrace_cartanCombination_mul_pauli]
  have hr := hT (FullSpace.diagonalComponent B) (vertexIndicator ℝ x)
    (finite_support_vertexIndicator ℝ x)
  rw [finsum_eq_single _ x fun y hy => by simp [vertexIndicator, hy]] at hr
  have hx : FullSpace.vertexAdjoint (FullSpace.diagonalComponent B) x =
      ∑ᶠ b, FullSpace.diagonalComponent B b *
        FullSpace.vertexDifference (vertexIndicator ℝ x) b := by
    simpa [vertexIndicator] using hr
  have hf : (support fun b => FullSpace.diagonalComponent B b *
      FullSpace.vertexDifference (vertexIndicator ℝ x) b).Finite :=
    finite_support_of_forall_eq_zero hfin fun b hb => by
      simp [FullSpace.diagonalComponent, hb, ComplexMatrix2.halfTrace]
  have hc : ((∑ᶠ b, FullSpace.diagonalComponent B b *
      FullSpace.vertexDifference (vertexIndicator ℝ x) b : ℝ) : ℂ) =
      ∑ᶠ b, ((FullSpace.diagonalComponent B b *
        FullSpace.vertexDifference (vertexIndicator ℝ x) b : ℝ) : ℂ) :=
    Complex.ofRealHom.toAddMonoidHom.map_finsum hf
  rw [hx, hc]
  refine finsum_congr fun b => ?_
  rw [hN, edgeWeight]
  simp only [FullSpace.vertexDifference]
  push_cast
  rw [ofReal_vertexIndicator, ofReal_vertexIndicator]
  ring
theorem lowering_coordinate (hAlg : ChargeAlgebra) (hS : CovariantShifts θ)
    (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0))
    (hfin : FullSpace.HasFiniteEdgeSupport B) (x : FullSpace.Vertex L 0 0) :
    ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x * loweringPauli) =
      (1 / 2) * ∑ μ, covShiftAdjSubOne θ μ
        (toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ)) x 0 := by
  obtain ⟨Bp, hBp⟩ := hS.exists_raisingForm
    fun μ => toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ)
  have hχ : ∀ b, ComplexMatrix2.conjugateBy (cartanPhase (θ b)) loweringPauli =
      expNegTwoI (θ b) • loweringPauli :=
    fun b => (hAlg.1 (θ b)).2
  have h2 := halfTrace_covDiffAdjoint_mul_eigen hD hBp.1 loweringPauli_mem_traceless expNegTwoI hχ x
  rw [hS.covDiffAdjoint_raising _ Bp hBp x] at h2
  have hv : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
      ComplexMatrix2.halfTrace (B b.1 * loweringPauli) =
        ComplexMatrix2.halfTrace (Bp b.1 * loweringPauli) := by
    intro b
    obtain ⟨⟨y, μ⟩, hc, -⟩ := hS.existsUnique_forwardEdge b
    subst hc
    have h3 : Bp (FullSpace.forwardEdge y μ).1 = _ := hBp.2 y μ
    rw [h3, toScalarL2_apply _ (finite_support_edgeComponent hfin μ),
      halfTrace_smul_raising_mul_lowering]
    show _ = (1 / 2) *
      (2 * ComplexMatrix2.halfTrace (B (FullSpace.forwardEdge y μ).1 * loweringPauli))
    ring
  rw [halfTrace_covDiffAdjoint_mul_eigen hD (mem_complexEdgeForms_of_mem hB)
    loweringPauli_mem_traceless expNegTwoI hχ x]
  simp only [hv]
  rw [← h2, halfTrace_smul_raising_mul_lowering]
theorem raising_coordinate (hAlg : ChargeAlgebra)
    (hForms : FormsChargeDecomposition (meshAt L 0 0))
    (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0))
    (hfin : FullSpace.HasFiniteEdgeSupport B) (x : FullSpace.Vertex L 0 0) :
    ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x * raisingPauli) =
      conj (ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x * loweringPauli)) := by
  rw [halfTrace_covDiffAdjoint_mul_eigen hD (mem_complexEdgeForms_of_mem hB)
      raisingPauli_mem_traceless expTwoI (fun b => (hAlg.1 (θ b)).1) x,
    halfTrace_covDiffAdjoint_mul_eigen hD (mem_complexEdgeForms_of_mem hB)
      loweringPauli_mem_traceless expNegTwoI (fun b => (hAlg.1 (θ b)).2) x]
  have hf : (support fun b => edgeWeight θ expNegTwoI x b *
      ComplexMatrix2.halfTrace (B b.1 * loweringPauli)).Finite :=
    finite_support_of_forall_eq_zero hfin fun b hb => by simp [hb, ComplexMatrix2.halfTrace]
  have hc : conj (∑ᶠ b, edgeWeight θ expNegTwoI x b *
      ComplexMatrix2.halfTrace (B b.1 * loweringPauli)) =
      ∑ᶠ b, conj (edgeWeight θ expNegTwoI x b *
        ComplexMatrix2.halfTrace (B b.1 * loweringPauli)) :=
    (starRingEnd ℂ).toAddMonoidHom.map_finsum hf
  rw [hc]
  refine finsum_congr fun b => ?_
  rw [map_mul]
  congr 1
  · simp only [edgeWeight, map_sub, map_mul, conj_vertexIndicator, conj_expNegTwoI]
  · rw [(hForms B hB b).1, halfTrace_cartanCombination_mul_raising,
      halfTrace_cartanCombination_mul_lowering]
    simp [map_ofNat]
theorem halfTrace_covDiffAdjoint_sq (hAlg : ChargeAlgebra)
    (hForms : FormsChargeDecomposition (meshAt L 0 0)) (hP : FaceVariables θ)
    (hS : CovariantShifts θ) (hD : CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    (hF : CompositesDefined (FullSpace.abelianLinkField θ))
    (hT : FullSpace.IsVertexAdjoint (FullSpace.vertexAdjoint (a := meshAt L 0 0) (R := ℝ)))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0))
    (hfin : FullSpace.HasFiniteEdgeSupport B) (x : FullSpace.Vertex L 0 0) :
    ComplexMatrix2.halfTrace
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x *
          FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x) =
      ((vertexTerm θ B x : ℝ) : ℂ) := by
  have htr : ComplexMatrix2.fullTrace
      (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B x) = 0 :=
    (hF.2 B (mem_complexEdgeForms_of_mem hB)).1 x (Set.mem_univ _)
  rw [halfTrace_self_mul_of_traceless _ htr, diagonal_coordinate hAlg hForms hP hD hT hB hfin,
    raising_coordinate hAlg hForms hD hB hfin, lowering_coordinate hAlg hS hD hB hfin]
  simp only [vertexTerm]
  generalize (∑ μ, covShiftAdjSubOne θ μ
    (toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ)) x 0) = W
  have hnorm : W * conj W = ((‖W‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [map_mul, map_div₀, map_one, map_ofNat]
  push_cast at hnorm ⊢
  linear_combination hnorm
theorem finite_support_covDiffAdjoint {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (h8 : EightIncidentEdges L) (hD : CovDiffAndAdjoint U) (hR : AdjointIsLocal U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule)
    (hfin : FullSpace.HasFiniteEdgeSupport B) :
    (support (FullSpace.covDiffAdjoint U B)).Finite := by
  have hzero : FullSpace.covDiffAdjoint U 0 = 0 := by
    have h := hD.2.2.2.2 0
    rw [map_zero] at h
    exact h
  refine ((hfin.image InfiniteLattice.Link.terminal).union
    (hfin.image InfiniteLattice.Link.initial)).subset fun x hx => ?_
  by_contra hn
  refine (Function.mem_support.1 hx) ?_
  have h0 : FullSpace.covDiffAdjoint U B x = FullSpace.covDiffAdjoint U 0 x := by
    refine hR B hB 0 (Submodule.zero_mem _) x fun b hb => ?_
    by_contra hb0
    have hmem : b ∈ positiveIncidentEdges x := by
      rw [(h8 x).1]
      exact hb
    rcases hmem.2 with h | h
    · exact hn (Or.inl ⟨b, ⟨hmem.1, hb0⟩, h⟩)
    · exact hn (Or.inr ⟨b, ⟨hmem.1, hb0⟩, h⟩)
  rw [h0, hzero]
  rfl
end TheForm
theorem massiveHessian_quadraticForm
    (hCharges : ChargeAlgebraAndForms)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hShifts : CovariantShiftsUnitary)
    (hDerivatives : FaceTermDerivatives.Statement)
    (hKernel : HessianKernel.KernelProperties)
    (hDirections : UnitGaugeDirections.Claim)
    (hReal : ScalarDifferenceAdjoints)
    (hFinite : FaceEdgeFinsets.FacesAndEdgesFinite) :
    MassiveOperatorQuadraticForm := by
  intro L hL θ B hB hfin
  have hP := hPlaquettes L hL θ
  have hS := hShifts L hL θ
  have hAlg := hCharges.1
  have hForms := hCharges.2 L hL
  have hT : FullSpace.IsVertexAdjoint (FullSpace.vertexAdjoint (a := meshAt L 0 0) (R := ℝ)) :=
    (hReal L hL).2.2.2.2.2.2.1.2.2.1
  have hU : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.1 (hP.abelianLinkField_mem.1 b)).2,
      hP.abelianLinkField_mem.2⟩
  obtain ⟨h8, hdirs⟩ := hDirections L hL
  obtain ⟨hD, hR, hF, -⟩ := hdirs _ hU
  have hBc := mem_complexEdgeForms_of_mem hB
  have hFin := (hFinite L hL 0 0 le_rfl).2
  have hl := finite_support_covDiffAdjoint h8 hD hR hBc hfin
  have hterm := halfTrace_covDiffAdjoint_sq hAlg hForms hP hS hD hF hT hB hfin
  have hsite : (support (vertexTerm θ B)).Finite := by
    refine hl.subset fun x hx => ?_
    by_contra hn
    refine (Function.mem_support.1 hx) ?_
    have h := hterm x
    rw [Function.notMem_support.1 hn] at h
    have h0 : ((vertexTerm θ B x : ℝ) : ℂ) = 0 := by
      rw [← h]
      simp [ComplexMatrix2.halfTrace]
    exact_mod_cast h0
  have hplaq := finite_support_faceTerm hP hFin hB hfin
  refine ⟨fun μ x => toScalarL2_apply _ (finite_support_edgeComponent hfin μ) x, hplaq,
    hsite, ?_⟩
  have hfs : B ∈ HessianKernel.finiteSupportComplexForms L 0 0 := ⟨hBc, hfin⟩
  have hA := ((hKernel L hL 0 0 le_rfl).2 _ hU).2.2.2.2.1 B hfs B hfs
  have hsecond := ((((hDerivatives L hL 0 0 le_rfl).2 B hBc).2 hfin).1 _ hU).1
  have hpair := covDiffAdjoint_pairing hD hBc (hF.2 B hBc).1 hl
  have hsplit : FullSpace.finiteEdgePairing B (FullSpace.abelianMassiveHessian θ B) =
      FullSpace.finiteEdgePairing B
          (FullSpace.complexHessianOperator (FullSpace.abelianLinkField θ) B) +
        FullSpace.finiteEdgePairing B (FullSpace.covDiff (FullSpace.abelianLinkField θ)
          (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B)) :=
    traceFinsumPairing_add_right _ _ (finite_support_of_forall_eq_zero hfin fun b hb => hb)
  have hc₁ : ((∑ᶠ p, _root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm θ B p : ℝ) : ℂ) = ∑ᶠ p, ((_root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm θ B p : ℝ) : ℂ) :=
    Complex.ofRealHom.toAddMonoidHom.map_finsum hplaq
  have hc₂ : ((∑ᶠ x, vertexTerm θ B x : ℝ) : ℂ) = ∑ᶠ x, ((vertexTerm θ B x : ℝ) : ℂ) :=
    Complex.ofRealHom.toAddMonoidHom.map_finsum hsite
  rw [hsplit, hA, ← hsecond, ← hpair, Complex.ofReal_add, hc₁, hc₂]
  congr 1
  · exact finsum_congr fun p => secondDerivExpr_eq_faceTerm hP hB p
  · exact finsum_congr hterm
end YangMills.Construction.Tower.MassiveFormExpansion
end
