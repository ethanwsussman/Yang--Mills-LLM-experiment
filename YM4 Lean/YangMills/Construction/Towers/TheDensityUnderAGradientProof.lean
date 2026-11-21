import YangMills.Construction.Towers.SymmetriesOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.TheDensityIsEvenInTheFieldProof
import YangMills.Construction.Towers.TheDensityUnderAGradient
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.GaugeInvariance
open YangMills.Construction.Matrices
open AbelianFieldFacts UnitLatticeL2 SectorDecomposition
open UnitGaugeDirections (unitVertexSpace unitEdgeSpace CovDiffAndAdjoint CompositesDefined)
section Matrices
theorem cartanPhase_eq_diag (t : ℝ) :
    cartanPhase t = !![Complex.exp (Complex.I * t), 0; 0, Complex.exp (-(Complex.I * t))] := by apply _root_.YangMills.Construction.Tower.AbelianActionGradient.cartanPhase_eq_diagonal <;> assumption
theorem cartanPhase_mul (s t : ℝ) : cartanPhase s * cartanPhase t = cartanPhase (s + t) := by
  rw [cartanPhase_eq_diag, cartanPhase_eq_diag, cartanPhase_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.exp_add, mul_add, add_comm]
theorem cartanPhase_zero : cartanPhase 0 = 1 := by apply _root_.YangMills.Construction.Tower.AbelianFieldPlaquettes.cartanPhase_at_zero <;> assumption
theorem cartanPhase_inv (t : ℝ) : (cartanPhase t)⁻¹ = cartanPhase (-t) := by apply _root_.YangMills.Construction.Tower.AbelianFieldPlaquettes.cartanPhase_inverse <;> assumption
theorem conjugateBy_cartanPhase_neg (t : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (cartanPhase t) (ComplexMatrix2.conjugateBy (cartanPhase (-t)) X) = X := by
  unfold ComplexMatrix2.conjugateBy
  rw [cartanPhase_inv, cartanPhase_inv, neg_neg]
  calc cartanPhase t * (cartanPhase (-t) * X * cartanPhase t) * cartanPhase (-t)
      = (cartanPhase t * cartanPhase (-t)) * X * (cartanPhase t * cartanPhase (-t)) := by
        simp only [mul_assoc]
    _ = X := by rw [cartanPhase_mul, add_neg_cancel, cartanPhase_zero]; simp
theorem halfTrace_conjugateBy_mul (t : ℝ) (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (ComplexMatrix2.conjugateBy (cartanPhase t) X *
        ComplexMatrix2.conjugateBy (cartanPhase t) Y) =
      ComplexMatrix2.halfTrace (X * Y) := by
  unfold ComplexMatrix2.conjugateBy
  rw [cartanPhase_inv]
  have hre : cartanPhase t * X * cartanPhase (-t) * (cartanPhase t * Y * cartanPhase (-t)) =
      cartanPhase t * (X * (cartanPhase (-t) * cartanPhase t) * Y * cartanPhase (-t)) := by
    simp only [mul_assoc]
  rw [hre, cartanPhase_mul, neg_add_cancel, cartanPhase_zero, mul_one]
  show (1 / 2 : ℂ) * Matrix.trace (cartanPhase t * (X * Y * cartanPhase (-t))) =
    (1 / 2 : ℂ) * Matrix.trace (X * Y)
  rw [Matrix.trace_mul_comm, mul_assoc (X * Y), cartanPhase_mul, neg_add_cancel, cartanPhase_zero,
    mul_one]
theorem mem_traceless_iff {X : ComplexMatrix2} :
    X ∈ ComplexMatrix2.traceless ↔ Matrix.trace X = 0 := Iff.rfl
theorem conjugateBy_mem_traceless (t : ℝ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy (cartanPhase t) X ∈ ComplexMatrix2.traceless := by
  rw [mem_traceless_iff] at hX ⊢
  unfold ComplexMatrix2.conjugateBy
  rw [cartanPhase_inv, Matrix.trace_mul_comm, ← mul_assoc, cartanPhase_mul, neg_add_cancel,
    cartanPhase_zero, one_mul]
  exact hX
theorem conjugateBy_add (t : ℝ) (X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (cartanPhase t) (X + Y) =
      ComplexMatrix2.conjugateBy (cartanPhase t) X + ComplexMatrix2.conjugateBy (cartanPhase t) Y := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_zero (t : ℝ) : ComplexMatrix2.conjugateBy (cartanPhase t) 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
theorem traceless_ext {Z W : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.traceless)
    (hW : W ∈ ComplexMatrix2.traceless)
    (h : ∀ a, ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * Z) =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * W)) : Z = W := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.traceless_ext_of_halfTrace <;> assumption
end Matrices
section Links
variable {a : ℝ}
theorem positive_opposite_of_not (b : InfiniteLattice.Link a) (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem extendOddly_mem (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (hf : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    FullSpace.extendOddly f ∈ FullSpace.complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
theorem odd_ext {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : ∀ b : InfiniteLattice.Link a, B b.opposite = -B b)
    (hB' : ∀ b : InfiniteLattice.Link a, B' b.opposite = -B' b)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b = B' b) : B = B' := by apply _root_.YangMills.Construction.Tower.FullSpace.Surjectivity.eq_of_eq_on_positive <;> assumption
end Links
section Pairings
variable {ι : Type}
theorem traceless_funext [DecidableEq ι] {Z W : ι → ComplexMatrix2}
    (hZ : ∀ x, Z x ∈ ComplexMatrix2.traceless) (hW : ∀ x, W x ∈ ComplexMatrix2.traceless)
    (h : ∀ x, ∀ Y ∈ ComplexMatrix2.traceless,
      traceFinsumPairing Z (Pi.single x Y) = traceFinsumPairing W (Pi.single x Y)) : Z = W := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.traceless_funext <;> assumption
theorem hasFiniteSupp_single [DecidableEq ι] (x : ι) (Y : ComplexMatrix2) :
    HasFiniteSupp (Pi.single x Y : ι → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.hasFiniteSupp_single <;> assumption
end Pairings
section Gauge
variable {L : ℕ}
def phaseField (t : FullSpace.Vertex L 0 0 → ℝ) : FullSpace.Vertex L 0 0 → ComplexMatrix2 :=
  fun x => cartanPhase (t x)
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.meshAt_zero_pos <;> assumption
theorem adjointForm_of_positive (t : FullSpace.Vertex L 0 0 → ℝ)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented) :
    FullSpace.adjointForm (phaseField t) B b =
      ComplexMatrix2.conjugateBy (cartanPhase (t b.initial)) (B b) :=
  extendOddly_of_positive _ hb
theorem adjointForm_mem (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.adjointForm (phaseField t) B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
  extendOddly_mem (meshAt_pos hL) _ fun b hb => conjugateBy_mem_traceless _ (hB.1 b hb)
theorem adjointForm_neg_cancel (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    {E : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hE : ∀ b : FullSpace.Edge L 0 0, E b.opposite = -E b) :
    FullSpace.adjointForm (phaseField t) (FullSpace.adjointForm (phaseField (-t)) E) = E :=
  odd_ext (extendOddly_opposite (meshAt_pos hL) _) hE fun b hb => by
    rw [adjointForm_of_positive _ _ hb, adjointForm_of_positive _ _ hb]
    exact conjugateBy_cartanPhase_neg _ _
theorem adjointForm_finite (t : FullSpace.Vertex L 0 0 → ℝ)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (h : FullSpace.HasFiniteEdgeSupport B) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.adjointForm (phaseField t) B) :=
  Set.Finite.subset h fun b hb => ⟨hb.1, fun hz => hb.2 (by
    show FullSpace.adjointForm (phaseField t) B b = 0
    rw [adjointForm_of_positive _ _ hb.1, hz, conjugateBy_zero])⟩
theorem edgeFormPairing_adjointForm (t : FullSpace.Vertex L 0 0 → ℝ)
    (B C : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.finiteEdgePairing (FullSpace.adjointForm (phaseField t) B)
        (FullSpace.adjointForm (phaseField t) C) =
      FullSpace.finiteEdgePairing B C := by
  unfold FullSpace.finiteEdgePairing traceFinsumPairing
  refine finsum_congr fun c => ?_
  show ComplexMatrix2.halfTrace (FullSpace.adjointForm (phaseField t) B c.1 *
    FullSpace.adjointForm (phaseField t) C c.1) = ComplexMatrix2.halfTrace (B c.1 * C c.1)
  rw [adjointForm_of_positive _ _ c.2, adjointForm_of_positive _ _ c.2, halfTrace_conjugateBy_mul]
theorem vertexPairing_adjoint (t : FullSpace.Vertex L 0 0 → ℝ)
    (f h : FullSpace.Vertex L 0 0 → ComplexMatrix2) :
    traceFinsumPairing (FullSpace.adjointVertexFn (phaseField t) f)
        (FullSpace.adjointVertexFn (phaseField t) h) =
      traceFinsumPairing f h := by
  unfold traceFinsumPairing
  exact finsum_congr fun x => halfTrace_conjugateBy_mul _ _ _
theorem adjointVertexFn_mem (t : FullSpace.Vertex L 0 0 → ℝ)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hl : l ∈ (unitVertexSpace L).complexSubmodule) :
    FullSpace.adjointVertexFn (phaseField t) l ∈ (unitVertexSpace L).complexSubmodule :=
  fun x _ => conjugateBy_mem_traceless _ (hl x (Set.mem_univ x))
variable {U U' : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem covDiffAdjoint_pairing (hD : CovDiffAndAdjoint U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hl : l ∈ (unitVertexSpace L).complexSubmodule)
    (hf : HasFiniteSupp l) :
    traceFinsumPairing (FullSpace.covDiffAdjoint U B) l =
      FullSpace.finiteEdgePairing B (FullSpace.covDiff U l) := by apply _root_.YangMills.Construction.Tower.MassiveFormExpansion.covDiffAdjoint_pairing <;> assumption
theorem covDiffAdjoint_gauge (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    (hcov : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
      FullSpace.covDiff U' (FullSpace.adjointVertexFn (phaseField t) l) =
        FullSpace.adjointForm (phaseField t) (FullSpace.covDiff U l))
    (hD : CovDiffAndAdjoint U) (hD' : CovDiffAndAdjoint U')
    (hF : CompositesDefined U) (hF' : CompositesDefined U')
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule) :
    FullSpace.covDiffAdjoint U' (FullSpace.adjointForm (phaseField t) B) =
      FullSpace.adjointVertexFn (phaseField t) (FullSpace.covDiffAdjoint U B) := by
  classical
  have hB' : FullSpace.adjointForm (phaseField t) B ∈ (unitEdgeSpace L).complexSubmodule :=
    adjointForm_mem hL t hB
  have hT := (hF.2 B hB).1
  have hT' := (hF'.2 _ hB').1
  refine traceless_funext (fun x => hT' x (Set.mem_univ x))
    (fun x => conjugateBy_mem_traceless _ (hT x (Set.mem_univ x))) fun x Y hY => ?_
  obtain ⟨l, hl₀⟩ : ∃ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      l = Pi.single x (ComplexMatrix2.conjugateBy (cartanPhase (-t x)) Y) := ⟨_, rfl⟩
  have hf : l ∈ (unitVertexSpace L).complexSubmodule := by
    intro i _
    rw [hl₀]
    by_cases hi : i = x
    · subst hi
      simpa using conjugateBy_mem_traceless (-t i) hY
    · rw [Pi.single_eq_of_ne hi]
      exact ComplexMatrix2.traceless.zero_mem
  have hs : FullSpace.adjointVertexFn (phaseField t) l = Pi.single x Y := by
    funext i
    rw [hl₀]
    by_cases hi : i = x
    · subst hi
      simpa [FullSpace.adjointVertexFn, phaseField] using conjugateBy_cartanPhase_neg (t i) Y
    · show ComplexMatrix2.conjugateBy (cartanPhase (t i)) _ = _
      rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, conjugateBy_zero]
  have hfin : HasFiniteSupp l := by
    rw [hl₀]
    exact hasFiniteSupp_single x _
  have r₀ := covDiffAdjoint_pairing hD hB hf hfin
  have r₁ := covDiffAdjoint_pairing hD' hB' (adjointVertexFn_mem t hf)
    (by rw [hs]; exact hasFiniteSupp_single x _)
  rw [← hs, r₁, hcov l fun y => hf y (Set.mem_univ y), edgeFormPairing_adjointForm, ← r₀,
    vertexPairing_adjoint]
theorem gaugeLaplacian_gauge (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    (hcov : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
      FullSpace.covDiff U' (FullSpace.adjointVertexFn (phaseField t) l) =
        FullSpace.adjointForm (phaseField t) (FullSpace.covDiff U l))
    (hD : CovDiffAndAdjoint U) (hD' : CovDiffAndAdjoint U')
    (hF : CompositesDefined U) (hF' : CompositesDefined U')
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hl : l ∈ (unitVertexSpace L).complexSubmodule) :
    FullSpace.gaugeLaplacian U' (FullSpace.adjointVertexFn (phaseField t) l) =
      FullSpace.adjointVertexFn (phaseField t) (FullSpace.gaugeLaplacian U l) := by
  unfold FullSpace.gaugeLaplacian
  rw [hcov l fun y => hl y (Set.mem_univ y),
    covDiffAdjoint_gauge hL t hcov hD hD' hF hF' (hF.1 l hl).1]
end Gauge
section Operator
open PeriodicOperators (applyKernel)
open HessianKernel (finiteSupportComplexForms)
variable {L : ℕ} {U U' : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem complexHessianOperator_mem (hL : 0 < L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.complexHessianOperator U B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.complexHessianOperator_mem <;> assumption
theorem basisForm_mem (hL : 0 < L) (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm a b ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.basisForm_mem_complexEdgeForms <;> assumption
theorem basisForm_finite (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm a b) := by apply _root_.YangMills.SharedProofs.p37344 <;> assumption
theorem edgeFormPairing_basisForm (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    (X : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.finiteEdgePairing (FullSpace.basisForm a b) X =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * X b.1) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.edgeFormPairing_basisForm <;> assumption
theorem complexHessianOperator_gauge_of_finite (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hph : ∀ x, phaseField t x ∈ PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (hP' : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B
          (FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U) B') =
        FullSpace.complexActionHessian (FullSpace.gaugeAct (phaseField t) U) B B')
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    (hf : FullSpace.HasFiniteEdgeSupport B) {b : FullSpace.Edge L 0 0}
    (hb : b.IsPositivelyOriented) :
    FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U)
        (FullSpace.adjointForm (phaseField t) B) b =
      ComplexMatrix2.conjugateBy (cartanPhase (t b.initial))
        (FullSpace.complexHessianOperator U B b) := by
  refine traceless_ext ((complexHessianOperator_mem hL _).1 b hb)
    (conjugateBy_mem_traceless _ ((complexHessianOperator_mem hL _).1 b hb)) fun a => ?_
  have hEc := basisForm_mem hL a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
  have hEf := basisForm_finite (L := L) a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
  obtain ⟨E, hE⟩ : ∃ E, E = FullSpace.basisForm a
    (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0)) := ⟨_, rfl⟩
  rw [← hE] at hEc hEf
  have hE₀c := adjointForm_mem hL (-t) hEc
  have hE₀f := adjointForm_finite (-t) hEf
  have hEE := adjointForm_neg_cancel hL t hEc.2
  have l₁ := hP' E ⟨hEc, hEf⟩ _ ⟨adjointForm_mem hL t hB, adjointForm_finite t hf⟩
  have g := (hG U (phaseField t) 0 _ B hUc hph (fun _ => ComplexMatrix2.traceless.zero_mem)
    (by simp [HasFiniteSupp]) hE₀c hB hE₀f hf).2.1
  rw [hEE] at g
  have l₂ := hP _ ⟨hE₀c, hE₀f⟩ B ⟨hB, hf⟩
  have l₃ : FullSpace.finiteEdgePairing E
        (FullSpace.adjointForm (phaseField t) (FullSpace.complexHessianOperator U B)) =
      FullSpace.finiteEdgePairing (FullSpace.adjointForm (phaseField (-t)) E)
        (FullSpace.complexHessianOperator U B) := by
    conv_lhs => rw [← hEE]
    exact edgeFormPairing_adjointForm _ _ _
  have t₁ := edgeFormPairing_basisForm a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
    (FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U)
      (FullSpace.adjointForm (phaseField t) B))
  have t₂ := edgeFormPairing_basisForm a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
    (FullSpace.adjointForm (phaseField t) (FullSpace.complexHessianOperator U B))
  rw [← hE] at t₁ t₂
  rw [show (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0)).1 = b from rfl,
    adjointForm_of_positive _ _ hb] at t₂
  exact t₁.symm.trans (l₁.trans (g.trans (l₂.symm.trans (l₃.symm.trans t₂))))
def restrictForm (F : Set (FullSpace.PositiveEdge (meshAt L 0 0)))
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) : FullSpace.Edge L 0 0 → ComplexMatrix2 :=
  open Classical in FullSpace.extendOddly fun c => if c ∈ Subtype.val '' F then B c else 0
theorem restrictForm_apply {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) {c : FullSpace.PositiveEdge (meshAt L 0 0)}
    (hc : c ∈ F) : restrictForm F B c.1 = B c.1 := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.restrictToEdges_of_mem <;> assumption
theorem restrictForm_mem (hL : 0 < L) (F : Set (FullSpace.PositiveEdge (meshAt L 0 0)))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    restrictForm F B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.restrictToEdges_mem <;> assumption
theorem restrictForm_finite {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))} (hF : F.Finite)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.HasFiniteEdgeSupport (restrictForm F B) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.restrictToEdges_hasFiniteEdgeSupport <;> assumption
theorem complexHessianOperator_congr {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented)
    (hrow : ∀ (a : Fin 3) κ, FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F)
    {B B' : FullSpace.Edge L 0 0 → ComplexMatrix2} (h : ∀ c ∈ F, B c.1 = B' c.1) :
    FullSpace.complexHessianOperator U B b = FullSpace.complexHessianOperator U B' b := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.complexHessianOperator_congr_of_row <;> assumption
theorem complexHessianOperator_gauge (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hph : ∀ x, phaseField t x ∈ PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (hP' : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B
          (FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U) B') =
        FullSpace.complexActionHessian (FullSpace.gaugeAct (phaseField t) U) B B')
    (hR : HessianKernel.RowFinite (FullSpace.complexHessianKernel U))
    (hR' : HessianKernel.RowFinite
      (FullSpace.complexHessianKernel (FullSpace.gaugeAct (phaseField t) U)))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented) :
    FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U)
        (FullSpace.adjointForm (phaseField t) B) b =
      ComplexMatrix2.conjugateBy (cartanPhase (t b.initial))
        (FullSpace.complexHessianOperator U B b) := by
  obtain ⟨F, hF⟩ : ∃ F : Set (FullSpace.PositiveEdge (meshAt L 0 0)), F =
      (⋃ a : Fin 3, Prod.snd '' {κ | FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0}) ∪
      ⋃ a : Fin 3, Prod.snd '' {κ | FullSpace.complexHessianKernel
        (FullSpace.gaugeAct (phaseField t) U) (a, ⟨b, hb⟩) κ ≠ 0} := ⟨_, rfl⟩
  have hFfin : F.Finite := by
    rw [hF]
    exact (Set.finite_iUnion fun a => (hR _).image _).union
      (Set.finite_iUnion fun a => (hR' _).image _)
  have hrow : ∀ (a : Fin 3) κ,
      FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F := by
    intro a κ hk
    rw [hF]
    exact Or.inl (Set.mem_iUnion.mpr ⟨a, κ, hk, rfl⟩)
  have hrow' : ∀ (a : Fin 3) κ,
      FullSpace.complexHessianKernel (FullSpace.gaugeAct (phaseField t) U)
        (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F := by
    intro a κ hk
    rw [hF]
    exact Or.inr (Set.mem_iUnion.mpr ⟨a, κ, hk, rfl⟩)
  have e₁ : FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U)
        (FullSpace.adjointForm (phaseField t) B) b =
      FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U)
        (FullSpace.adjointForm (phaseField t) (restrictForm F B)) b :=
    complexHessianOperator_congr hb hrow' fun c hc => by
      rw [adjointForm_of_positive _ _ c.2, adjointForm_of_positive _ _ c.2,
        restrictForm_apply B hc]
  have e₂ : FullSpace.complexHessianOperator U B b =
      FullSpace.complexHessianOperator U (restrictForm F B) b :=
    complexHessianOperator_congr hb hrow fun c hc => (restrictForm_apply B hc).symm
  rw [e₁, e₂]
  exact complexHessianOperator_gauge_of_finite hL t hUc hph hG hP hP' (restrictForm_mem hL F hB)
    (restrictForm_finite hFfin B) hb
theorem massiveHessian_gauge (hL : 0 < L) (t : FullSpace.Vertex L 0 0 → ℝ)
    (hU' : U' = FullSpace.gaugeAct (phaseField t) U)
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hph : ∀ x, phaseField t x ∈ PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (hP' : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B
          (FullSpace.complexHessianOperator (FullSpace.gaugeAct (phaseField t) U) B') =
        FullSpace.complexActionHessian (FullSpace.gaugeAct (phaseField t) U) B B')
    (hR : HessianKernel.RowFinite (FullSpace.complexHessianKernel U))
    (hR' : HessianKernel.RowFinite
      (FullSpace.complexHessianKernel (FullSpace.gaugeAct (phaseField t) U)))
    (hcov : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
      FullSpace.covDiff U' (FullSpace.adjointVertexFn (phaseField t) l) =
        FullSpace.adjointForm (phaseField t) (FullSpace.covDiff U l))
    (hD : CovDiffAndAdjoint U) (hD' : CovDiffAndAdjoint U')
    (hF : CompositesDefined U) (hF' : CompositesDefined U')
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented) :
    FullSpace.massiveHessian U' (FullSpace.adjointForm (phaseField t) B) b =
      ComplexMatrix2.conjugateBy (cartanPhase (t b.initial)) (FullSpace.massiveHessian U B b) := by
  have hT := covDiffAdjoint_gauge hL t hcov hD hD' hF hF' hB
  have hC := hcov _ fun x => (hF.2 B hB).1 x (Set.mem_univ x)
  subst hU'
  unfold FullSpace.massiveHessian
  rw [hT, hC, Pi.add_apply, Pi.add_apply,
    complexHessianOperator_gauge hL t hUc hph hG hP hP' hR hR' hB hb,
    adjointForm_of_positive _ _ hb, conjugateBy_add]
end Operator
section Field
variable {L : ℕ}
theorem abelianLinkField_of_positive (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    {b : FullSpace.Edge L 0 0} (h : b.IsPositivelyOriented) :
    FullSpace.abelianLinkField θ b = cartanPhase (θ ⟨b, h⟩) := dif_pos h
theorem abelianLinkField_of_opposite (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    {b : FullSpace.Edge L 0 0} (h : ¬ b.IsPositivelyOriented)
    (h' : b.opposite.IsPositivelyOriented) :
    FullSpace.abelianLinkField θ b = cartanPhase (-θ ⟨b.opposite, h'⟩) := by
  rw [← cartanPhase_inv]
  unfold FullSpace.abelianLinkField
  rw [dif_neg h, dif_pos h']
  rfl
theorem abelianLinkField_add_gradient (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (lam : FullSpace.Vertex L 0 0 → ℝ) :
    FullSpace.abelianLinkField (fun b => θ b + FullSpace.vertexDifference lam b) =
      FullSpace.gaugeAct (phaseField (-lam)) (FullSpace.abelianLinkField θ) := by
  funext b
  show _ = cartanPhase (-lam b.initial) * FullSpace.abelianLinkField θ b *
    (cartanPhase (-lam b.terminal))⁻¹
  rw [cartanPhase_inv]
  by_cases h : b.IsPositivelyOriented
  · rw [abelianLinkField_of_positive _ h, abelianLinkField_of_positive _ h, cartanPhase_mul,
      cartanPhase_mul]
    congr 1
    show θ ⟨b, h⟩ + (lam b.terminal - lam b.initial) = _
    ring
  · have h' := positive_opposite_of_not b h
    rw [abelianLinkField_of_opposite _ h h', abelianLinkField_of_opposite _ h h', cartanPhase_mul,
      cartanPhase_mul]
    congr 1
    show -(θ ⟨b.opposite, h'⟩ + (lam b.initial - lam b.terminal)) = _
    ring
theorem ofCoords_injective {σ : Type} (hco : CoordsIsometry σ)
    {v w : L2Field σ} (h : ofCoords v = ofCoords w) : v = w := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.ofCoords_injective <;> assumption
theorem formOfPositiveValues_apply (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (b : PeriodicOperators.PosEdge L 0 0) : formOfPositiveValues g b.1 = g b := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.formOfPositiveValues_apply <;> assumption
theorem formOfPositiveValues_opposite (hL : 0 < L)
    (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2) (b : FullSpace.Edge L 0 0) :
    formOfPositiveValues g b.opposite = -formOfPositiveValues g b :=
  extendOddly_opposite (meshAt_pos hL) _ b
theorem vertexAdd_zero (x : FullSpace.Vertex L 0 0) : vertexAdd 0 x = x := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.EvenInFieldProof.vertexAdd_zero <;> assumption
end Field
theorem densityGaugeInvariant_holds
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hDirections : UnitGaugeDirections.Claim)
    (hAlgebra : LeftChartAlgebra.AllConditionsHold)
    (hKernel : HessianKernel.KernelProperties)
    (hSquare : UnitLatticeL2Statement)
    (hOperators : AbelianOperatorsLocalSelfAdjoint)
    (hSymmetries : AbelianOperatorSymmetries)
    (hLogarithms : LogSectorsAndDensity) :
    DensityGaugeInvariant := by
  intro z hz L hL lam θ hformed
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨θ', hθ'⟩ : ∃ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      θ' = fun b => θ b + FullSpace.vertexDifference lam b := ⟨_, rfl⟩
  rw [← hθ']
  obtain ⟨t, ht⟩ : ∃ t : FullSpace.Vertex L 0 0 → ℝ, t = -lam := ⟨_, rfl⟩
  have hconf : FullSpace.abelianLinkField θ' =
      FullSpace.gaugeAct (phaseField t) (FullSpace.abelianLinkField θ) := by
    rw [hθ', ht]
    exact abelianLinkField_add_gradient θ lam
  have hUr : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup :=
    (hPlaquettes L hL θ).abelianLinkField_mem
  have hUr' : FullSpace.abelianLinkField θ' ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup :=
    (hPlaquettes L hL θ').abelianLinkField_mem
  have hUc : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hUr.1 b)).2, hUr.2⟩
  have hUc' : FullSpace.abelianLinkField θ' ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hUr'.1 b)).2, hUr'.2⟩
  have hu : phaseField t ∈ FullSpace.gaugeGroupAt L 0 0 :=
    fun x => (hSymmetries L hL θ).cartanPhase_mem _
  have hph : ∀ x, phaseField t x ∈ PeriodicLattice.complexGaugeGroup :=
    fun x => (Matrix.mem_specialUnitaryGroup_iff.mp (hu x)).2
  obtain ⟨hD, -, hF, -⟩ := (hDirections L hL).2 _ hUc
  obtain ⟨hD', -, hF', -⟩ := (hDirections L hL).2 _ hUc'
  obtain ⟨-, -, hrows, -, hpair, -⟩ := (hKernel L hL 0 0 le_rfl).2 _ hUc
  obtain ⟨-, -, hrows', -, hpair', -⟩ := (hKernel L hL 0 0 le_rfl).2 _ hUc'
  obtain ⟨hgauge, hunitary, -, hder, -⟩ := (hAlgebra.2.2 L 0 0 hL le_rfl).2
  have hcov : ∀ l : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
      FullSpace.covDiff (FullSpace.abelianLinkField θ')
          (FullSpace.adjointVertexFn (phaseField t) l) =
        FullSpace.adjointForm (phaseField t)
          (FullSpace.covDiff (FullSpace.abelianLinkField θ) l) := by
    intro l hl
    rw [hconf]
    exact (hgauge _ _ hUc hph).1 l hl
  have hco := (hSquare.2 L).2.1.1
  have hcb := (hSquare.2 L).2.2.1
  obtain ⟨-, -, hub, hus⟩ := hunitary.2.2 (phaseField t) hu
  have hsite : ∀ f : L2Field (FullSpace.Vertex L 0 0),
      ofCoords (gaugeVertexFn (phaseField t) f) =
        FullSpace.adjointVertexFn (phaseField t) (ofCoords f) := by
    intro f
    have h₁ : FullSpace.adjointVertexFn (phaseField t) (ofCoords f) ∈
        {l : FullSpace.Vertex L 0 0 → ComplexMatrix2 | IsL2Traceless l} :=
      hus.bijOn.mapsTo (hco.2.2.1 f).1
    obtain ⟨v, hv⟩ := hco.2.2.2.1 _ h₁
    exact Classical.epsilon_spec
      (p := fun g : L2Field (FullSpace.Vertex L 0 0) => ofCoords g =
        FullSpace.adjointVertexFn (phaseField t) (ofCoords f)) ⟨v, hv⟩
  have hform : ∀ f : L2Field (PeriodicOperators.PosEdge L 0 0),
      formOfPositiveValues (ofCoords f) ∈ FullSpace.l2Forms (meshAt L 0 0) := by
    intro f
    have e : FullSpace.restrictToPositiveEdges (formOfPositiveValues (ofCoords f)) =
        ofCoords f := funext fun b => formOfPositiveValues_apply _ b
    refine ⟨⟨fun b hb => ?_, formOfPositiveValues_opposite hL0 _⟩, ?_⟩
    · rw [show formOfPositiveValues (ofCoords f) b = _ from formOfPositiveValues_apply _ ⟨b, hb⟩]
      exact (hcb.2.2.1 f).1.1 ⟨b, hb⟩
    · rw [e]
      exact (hcb.2.2.1 f).1
  have hbond : ∀ (f : L2Field (PeriodicOperators.PosEdge L 0 0))
      (b : PeriodicOperators.PosEdge L 0 0),
      ofCoords (gaugeEdgeFn (phaseField t) f) b =
        FullSpace.adjointForm (phaseField t) (formOfPositiveValues (ofCoords f)) b.1 := by
    intro f
    have h₁ := hub.bijOn.mapsTo (hform f)
    obtain ⟨v, hv⟩ := hcb.2.2.2.1 _ h₁.2
    exact Classical.epsilon_spec
      (p := fun g : L2Field (PeriodicOperators.PosEdge L 0 0) =>
        ∀ b : PeriodicOperators.PosEdge L 0 0, ofCoords g b =
          FullSpace.adjointForm (phaseField t) (formOfPositiveValues (ofCoords f)) b.1)
      ⟨v, fun b => congrFun hv b⟩
  have hops := hOperators L hL θ
  have hops' := hOperators L hL θ'
  have hlap : ∀ f, gaugeVertexFn (phaseField t) (laplacianOp θ f) =
      laplacianOp θ' (gaugeVertexFn (phaseField t) f) := by
    intro f
    refine ofCoords_injective hco ?_
    rw [hsite, hops.laplacian_apply, hops'.laplacian_apply, hsite]
    exact (gaugeLaplacian_gauge hL0 t hcov hD hD' hF hF' fun x _ => (hco.2.2.1 f).1.1 x).symm
  have hmas : ∀ f, gaugeEdgeFn (phaseField t) (AbelianFieldDensity.massiveOp θ f) =
      AbelianFieldDensity.massiveOp θ' (gaugeEdgeFn (phaseField t) f) := by
    intro f
    refine ofCoords_injective hcb (funext fun b => ?_)
    have e : formOfPositiveValues (ofCoords (gaugeEdgeFn (phaseField t) f)) =
        FullSpace.adjointForm (phaseField t) (formOfPositiveValues (ofCoords f)) :=
      odd_ext (formOfPositiveValues_opposite hL0 _) (extendOddly_opposite (meshAt_pos hL0) _)
        fun c hc => (formOfPositiveValues_apply _ ⟨c, hc⟩).trans (hbond f ⟨c, hc⟩)
    have l₃ := congrFun (hops.hessian_apply f) b
    have l₂ := congrFun (hops'.hessian_apply (gaugeEdgeFn (phaseField t) f)) b
    rw [hbond, l₂]
    show _ = FullSpace.abelianMassiveHessian θ'
      (formOfPositiveValues (ofCoords (gaugeEdgeFn (phaseField t) f))) b.1
    rw [e, adjointForm_of_positive _ _ b.2, formOfPositiveValues_apply, l₃]
    exact (massiveHessian_gauge hL0 t hconf hUc hph hder hpair (by rw [← hconf]; exact hpair')
      hrows (by rw [← hconf]; exact hrows') hcov hD hD' hF hF' (hform f).1 b.2).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsymmetry, -⟩ := hLogarithms.2 L hL z hz
  obtain ⟨hformed', hx⟩ := (hsymmetry (phaseField t) hu).2.2 θ θ' hformed hlap hmas
  refine ⟨hformed', fun x => ?_⟩
  have e := hx x
  rwa [vertexAdd_zero] at e
end YangMills.Construction.Tower.AbelianFieldDensity.GaugeInvariance
end
