import YangMills.Construction.Towers.LogarithmsSectorsAndTheDensity
import YangMills.Construction.Towers.QuadraticFormOfTheAbelianMassiveOperatorProof
import YangMills.Construction.Towers.SymmetriesOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.TheDensityIsEvenInTheField
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.EvenInFieldProof
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.AbelianFieldFacts YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
section Matrices
def iPauliX : ComplexMatrix2 := !![0, Complex.I; Complex.I, 0]
theorem iPauliX_inv : iPauliX⁻¹ = !![0, -Complex.I; -Complex.I, 0] := by
  apply Matrix.inv_eq_right_inv
  unfold iPauliX
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem iPauliX_mem_compact : iPauliX ∈ PeriodicLattice.compactGaugeGroup := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    unfold iPauliX
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · unfold iPauliX
    rw [Matrix.det_fin_two_of]
    simp
theorem conjugateBy_iPauliX (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy iPauliX X = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  unfold ComplexMatrix2.conjugateBy
  rw [iPauliX_inv]
  unfold iPauliX
  conv_lhs => rw [Matrix.eta_fin_two X]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-X 1 1) * hI
  · linear_combination (-X 1 0) * hI
  · linear_combination (-X 0 1) * hI
  · linear_combination (-X 0 0) * hI
def swapConj : ComplexMatrix2 →+ ComplexMatrix2 where
  toFun := ComplexMatrix2.conjugateBy iPauliX
  map_zero' := by simp [ComplexMatrix2.conjugateBy]
  map_add' := fun X Y => by simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem swapConj_apply (X : ComplexMatrix2) :
    swapConj X = !![X 1 1, X 1 0; X 0 1, X 0 0] := conjugateBy_iPauliX X
theorem swapConj_swapConj (X : ComplexMatrix2) : swapConj (swapConj X) = X := by
  rw [swapConj_apply, swapConj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem mem_traceless_iff {X : ComplexMatrix2} :
    X ∈ ComplexMatrix2.traceless ↔ X 0 0 + X 1 1 = 0 := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.mem_traceless_iff <;> assumption
theorem swapConj_mem_traceless {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    swapConj X ∈ ComplexMatrix2.traceless := by
  rw [mem_traceless_iff] at hX ⊢
  rw [swapConj_apply]
  simpa [add_comm] using hX
theorem halfTrace_swapConj_mul (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (swapConj X * swapConj Y) = ComplexMatrix2.halfTrace (X * Y) := by
  rw [swapConj_apply, swapConj_apply]
  show (1 / 2 : ℂ) * Matrix.trace _ = (1 / 2 : ℂ) * Matrix.trace _
  congr 1
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring
theorem cartanPhase_eq (ϑ : ℝ) :
    cartanPhase ϑ = !![Complex.exp (Complex.I * ϑ), 0; 0, Complex.exp (-(Complex.I * ϑ))] := by apply _root_.YangMills.Construction.Tower.AbelianActionGradient.cartanPhase_eq_diagonal <;> assumption
theorem cartanPhase_inv (ϑ : ℝ) : (cartanPhase ϑ)⁻¹ = cartanPhase (-ϑ) := by apply _root_.YangMills.Construction.Tower.AbelianFieldPlaquettes.cartanPhase_inverse <;> assumption
theorem iPauliX_conj_cartanPhase (t : ℝ) :
    iPauliX * cartanPhase t * iPauliX⁻¹ = cartanPhase (-t) := by
  have e := conjugateBy_iPauliX (cartanPhase t)
  unfold ComplexMatrix2.conjugateBy at e
  rw [e, cartanPhase_eq, cartanPhase_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
end Matrices
section Bonds
open YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem extendOddly_mem (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (hf : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    FullSpace.extendOddly f ∈ FullSpace.complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
theorem oddFn_ext {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : ∀ b : InfiniteLattice.Link a, B b.opposite = -B b)
    (hB' : ∀ b : InfiniteLattice.Link a, B' b.opposite = -B' b)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b = B' b) : B = B' := by apply _root_.YangMills.Construction.Tower.FullSpace.Surjectivity.eq_of_eq_on_positive <;> assumption
theorem swapConj_mem_forms {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms a) :
    (fun b => swapConj (B b)) ∈ FullSpace.complexEdgeForms a :=
  ⟨fun b hb => swapConj_mem_traceless (hB.1 b hb), fun b => by
    show swapConj (B b.opposite) = -swapConj (B b)
    rw [hB.2 b, map_neg]⟩
theorem adjointForm_iPauliX (ha : 0 < a) {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms a) :
    FullSpace.adjointForm (fun _ => iPauliX) B = fun b => swapConj (B b) := by
  refine oddFn_ext (extendOddly_opposite ha _) (fun b => ?_) fun b hb => ?_
  · show swapConj _ = -swapConj _
    rw [hB.2 b, map_neg]
  · exact extendOddly_of_positive _ hb
end Bonds
section Pairings
variable {ι : Type}
theorem traceFinsumPairing_swapConj (f h : ι → ComplexMatrix2) :
    traceFinsumPairing (fun i => swapConj (f i)) (fun i => swapConj (h i)) =
      traceFinsumPairing f h := by
  unfold traceFinsumPairing
  exact finsum_congr fun i => halfTrace_swapConj_mul _ _
end Pairings
section Configuration
variable {a : ℝ}
theorem gaugeAct_iPauliX_abelian (θ : FullSpace.PositiveEdge a → ℝ) :
    FullSpace.gaugeAct (fun _ => iPauliX) (FullSpace.abelianLinkField θ) =
      FullSpace.abelianLinkField fun b => -θ b := by
  funext b
  show iPauliX * FullSpace.abelianLinkField θ b * iPauliX⁻¹ = _
  unfold FullSpace.abelianLinkField
  split_ifs with h h'
  · exact iPauliX_conj_cartanPhase _
  · show iPauliX * (cartanPhase (θ ⟨b.opposite, h'⟩))⁻¹ * iPauliX⁻¹ =
      (cartanPhase (-θ ⟨b.opposite, h'⟩))⁻¹
    rw [cartanPhase_inv, iPauliX_conj_cartanPhase, cartanPhase_inv]
  · rw [mul_one, Matrix.mul_nonsing_inv]
    have := (Matrix.mem_specialUnitaryGroup_iff.mp iPauliX_mem_compact).2
    rw [this]
    exact isUnit_one
end Configuration
section Difference
open YangMills.Construction.Tower.UnitGaugeDirections
variable {L : ℕ} {U U' : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem swapConj_mem_vertex {l : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hl : l ∈ (unitVertexSpace L).complexSubmodule) :
    (fun x => swapConj (l x)) ∈ (unitVertexSpace L).complexSubmodule :=
  fun x _ => swapConj_mem_traceless (hl x (Set.mem_univ x))
theorem traceless_ext {Z W : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.traceless)
    (hW : W ∈ ComplexMatrix2.traceless)
    (h : ∀ a : Fin 3, ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * Z) =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * W)) : Z = W := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.traceless_ext_of_halfTrace <;> assumption
theorem tracelessFn_ext {ι : Type} [DecidableEq ι] {Z W : ι → ComplexMatrix2}
    (hZ : ∀ x, Z x ∈ ComplexMatrix2.traceless) (hW : ∀ x, W x ∈ ComplexMatrix2.traceless)
    (h : ∀ x, ∀ Y ∈ ComplexMatrix2.traceless,
      traceFinsumPairing Z (Pi.single x Y) = traceFinsumPairing W (Pi.single x Y)) :
    Z = W := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.traceless_funext <;> assumption
theorem hasFiniteSupp_single {ι : Type} [DecidableEq ι] (x : ι) (Y : ComplexMatrix2) :
    HasFiniteSupp (Pi.single x Y : ι → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.hasFiniteSupp_single <;> assumption
theorem covDiffAdjoint_pairing (hD : CovDiffAndAdjoint U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hl : l ∈ (unitVertexSpace L).complexSubmodule)
    (hf : HasFiniteSupp l) :
    traceFinsumPairing (FullSpace.covDiffAdjoint U B) l =
        FullSpace.finiteEdgePairing B (FullSpace.covDiff U l) := by apply _root_.YangMills.Construction.Tower.MassiveFormExpansion.covDiffAdjoint_pairing <;> assumption
theorem covDiffAdjoint_swapConj (hD : CovDiffAndAdjoint U) (hD' : CovDiffAndAdjoint U')
    (hF : CompositesDefined U) (hF' : CompositesDefined U')
    (hd : ∀ l ∈ (unitVertexSpace L).complexSubmodule,
      FullSpace.covDiff U' (fun x => swapConj (l x)) =
        fun b => swapConj (FullSpace.covDiff U l b))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule) :
    FullSpace.covDiffAdjoint U' (fun b => swapConj (B b)) =
      fun x => swapConj (FullSpace.covDiffAdjoint U B x) := by
  classical
  have hB' : (fun b => swapConj (B b)) ∈ (unitEdgeSpace L).complexSubmodule :=
    swapConj_mem_forms hB
  have hT := (hF.2 B hB).1
  have hT' := (hF'.2 _ hB').1
  refine tracelessFn_ext (fun x => hT' x (Set.mem_univ x))
    (fun x => swapConj_mem_traceless (hT x (Set.mem_univ x))) fun x Y hY => ?_
  have hf : (Pi.single x (swapConj Y) : FullSpace.Vertex L 0 0 → ComplexMatrix2) ∈
      (unitVertexSpace L).complexSubmodule := by
    intro i _
    by_cases hi : i = x
    · subst hi
      simpa using swapConj_mem_traceless hY
    · rw [Pi.single_eq_of_ne hi]
      exact ComplexMatrix2.traceless.zero_mem
  have hs : (fun i => swapConj
      ((Pi.single x (swapConj Y) : FullSpace.Vertex L 0 0 → ComplexMatrix2) i)) =
      Pi.single x Y := by
    funext i
    by_cases hi : i = x
    · subst hi
      simpa using swapConj_swapConj Y
    · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, map_zero]
  have hfin : HasFiniteSupp (Pi.single x (swapConj Y) : FullSpace.Vertex L 0 0 → ComplexMatrix2) :=
    hasFiniteSupp_single x _
  have r₀ := covDiffAdjoint_pairing hD hB hf hfin
  have r₁ := covDiffAdjoint_pairing hD' hB' (swapConj_mem_vertex hf)
    (by rw [hs]; exact hasFiniteSupp_single x _)
  rw [← hs, r₁, hd _ hf, traceFinsumPairing_swapConj]
  show traceFinsumPairing (fun b => swapConj (FullSpace.restrictToPositiveEdges B b))
    (fun b => swapConj (FullSpace.restrictToPositiveEdges (FullSpace.covDiff U _) b)) = _
  rw [traceFinsumPairing_swapConj]
  exact r₀.symm
end Difference
section Operator
open YangMills.Construction.PeriodicOperators (applyKernel)
open YangMills.Construction.Tower.HessianKernel (finiteSupportComplexForms)
variable {L : ℕ} {U U' : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem meshAt_pos (L : ℕ) (hL : 0 < L) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.meshAt_zero_pos <;> assumption
theorem complexHessianOperator_opposite (hL : 0 < L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (b : FullSpace.Edge L 0 0) :
    FullSpace.complexHessianOperator U B b.opposite = -FullSpace.complexHessianOperator U B b :=
  extendOddly_opposite (meshAt_pos L hL) _ b
theorem complexHessianOperator_mem (hL : 0 < L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.complexHessianOperator U B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.complexHessianOperator_mem <;> assumption
theorem swapConj_hasFiniteEdgeSupport {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (h : FullSpace.HasFiniteEdgeSupport B) :
    FullSpace.HasFiniteEdgeSupport fun b => swapConj (B b) :=
  Set.Finite.subset h fun b hb => ⟨hb.1, fun hz => hb.2 (by
    show swapConj (B b) = 0
    rw [hz, map_zero])⟩
theorem basisForm_mem (hL : 0 < L) (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm a b ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.basisForm_mem_complexEdgeForms <;> assumption
theorem basisForm_hasFiniteEdgeSupport (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm a b) := by apply _root_.YangMills.SharedProofs.p37344 <;> assumption
theorem edgeFormPairing_basisForm (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    (X : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.finiteEdgePairing (FullSpace.basisForm a b) X =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * X b.1) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.edgeFormPairing_basisForm <;> assumption
theorem complexHessianOperator_swapConj_of_finite (hL : 0 < L)
    (hUU : FullSpace.gaugeAct (fun _ => iPauliX) U = U')
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (hP' : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U' B') =
        FullSpace.complexActionHessian U' B B')
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) (hf : FullSpace.HasFiniteEdgeSupport B) :
    FullSpace.complexHessianOperator U' (fun b => swapConj (B b)) =
      fun b => swapConj (FullSpace.complexHessianOperator U B b) := by
  have hpos := meshAt_pos L hL
  refine oddFn_ext (complexHessianOperator_opposite hL _) (fun b => ?_) fun b hb => ?_
  · show swapConj _ = -swapConj _
    rw [complexHessianOperator_opposite hL, map_neg]
  refine traceless_ext ((complexHessianOperator_mem hL _).1 b hb)
    (swapConj_mem_traceless ((complexHessianOperator_mem hL _).1 b hb)) fun a => ?_
  have hEc := basisForm_mem hL a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
  have hEf := basisForm_hasFiniteEdgeSupport (L := L) a
    (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
  obtain ⟨E, hE⟩ : ∃ E, E = FullSpace.basisForm a
    (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0)) := ⟨_, rfl⟩
  rw [← hE] at hEc hEf
  have hE₀c : (fun c => swapConj (E c)) ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
    swapConj_mem_forms hEc
  have hE₀f : FullSpace.HasFiniteEdgeSupport fun c => swapConj (E c) :=
    swapConj_hasFiniteEdgeSupport hEf
  have hEE : (fun c => swapConj (swapConj (E c))) = E := funext fun c => swapConj_swapConj _
  have l₁ := hP' E ⟨hEc, hEf⟩ (fun b => swapConj (B b))
    ⟨swapConj_mem_forms hB, swapConj_hasFiniteEdgeSupport hf⟩
  have g := (hG U (fun _ => iPauliX) 0 (fun c => swapConj (E c)) B hUc
    (fun _ => (Matrix.mem_specialUnitaryGroup_iff.mp iPauliX_mem_compact).2)
    (fun _ => ComplexMatrix2.traceless.zero_mem) (by simp [HasFiniteSupp]) hE₀c hB hE₀f hf).2.1
  rw [hUU, adjointForm_iPauliX hpos hE₀c, adjointForm_iPauliX hpos hB, hEE] at g
  have l₂ := hP _ ⟨hE₀c, hE₀f⟩ B ⟨hB, hf⟩
  have l₃ : FullSpace.finiteEdgePairing E
        (fun c => swapConj (FullSpace.complexHessianOperator U B c)) =
      FullSpace.finiteEdgePairing (fun c => swapConj (E c))
        (FullSpace.complexHessianOperator U B) := by
    conv_lhs => rw [← hEE]
    exact traceFinsumPairing_swapConj _ _
  have t₁ := edgeFormPairing_basisForm a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
    (FullSpace.complexHessianOperator U' fun b => swapConj (B b))
  have t₂ := edgeFormPairing_basisForm a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
    (fun c => swapConj (FullSpace.complexHessianOperator U B c))
  rw [← hE] at t₁ t₂
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
theorem restrictForm_hasFiniteEdgeSupport {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    (hF : F.Finite) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.HasFiniteEdgeSupport (restrictForm F B) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.restrictToEdges_hasFiniteEdgeSupport <;> assumption
theorem restrictForm_swapConj (F : Set (FullSpace.PositiveEdge (meshAt L 0 0)))
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    restrictForm F (fun b => swapConj (B b)) = fun b => swapConj (restrictForm F B b) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · unfold restrictForm
    rw [extendOddly_of_positive _ hb, extendOddly_of_positive _ hb]
    split_ifs
    · rfl
    · rw [map_zero]
  · unfold restrictForm
    have e : ∀ f : FullSpace.Edge L 0 0 → ComplexMatrix2,
        FullSpace.extendOddly f b = -f b.opposite :=
      fun f => if_neg hb
    rw [e, e, map_neg]
    split_ifs
    · rfl
    · rw [map_zero]
theorem complexHessianOperator_congr {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented)
    (hrow : ∀ (a : Fin 3) κ, FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F)
    {B B' : FullSpace.Edge L 0 0 → ComplexMatrix2} (h : ∀ c ∈ F, B c.1 = B' c.1) :
    FullSpace.complexHessianOperator U B b = FullSpace.complexHessianOperator U B' b := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.complexHessianOperator_congr_of_row <;> assumption
theorem complexHessianOperator_swapConj (hL : 0 < L)
    (hUU : FullSpace.gaugeAct (fun _ => iPauliX) U = U')
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (hP' : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U' B') =
        FullSpace.complexActionHessian U' B B')
    (hR : HessianKernel.RowFinite (FullSpace.complexHessianKernel U))
    (hR' : HessianKernel.RowFinite (FullSpace.complexHessianKernel U'))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.complexHessianOperator U' (fun b => swapConj (B b)) =
      fun b => swapConj (FullSpace.complexHessianOperator U B b) := by
  refine oddFn_ext (complexHessianOperator_opposite hL _) (fun b => ?_) fun b hb => ?_
  · show swapConj _ = -swapConj _
    rw [complexHessianOperator_opposite hL, map_neg]
  obtain ⟨F, hF⟩ : ∃ F : Set (FullSpace.PositiveEdge (meshAt L 0 0)), F =
      (⋃ a : Fin 3, Prod.snd '' {κ | FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0}) ∪
      ⋃ a : Fin 3, Prod.snd '' {κ | FullSpace.complexHessianKernel U' (a, ⟨b, hb⟩) κ ≠ 0} :=
    ⟨_, rfl⟩
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
      FullSpace.complexHessianKernel U' (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F := by
    intro a κ hk
    rw [hF]
    exact Or.inr (Set.mem_iUnion.mpr ⟨a, κ, hk, rfl⟩)
  have e₁ : FullSpace.complexHessianOperator U' (fun b => swapConj (B b)) b =
      FullSpace.complexHessianOperator U' (restrictForm F fun b => swapConj (B b)) b :=
    complexHessianOperator_congr hb hrow' fun c hc =>
      (restrictForm_apply (fun b => swapConj (B b)) hc).symm
  have e₂ : FullSpace.complexHessianOperator U B b =
      FullSpace.complexHessianOperator U (restrictForm F B) b :=
    complexHessianOperator_congr hb hrow fun c hc => (restrictForm_apply B hc).symm
  show _ = swapConj _
  rw [e₁, e₂, restrictForm_swapConj,
    complexHessianOperator_swapConj_of_finite hL hUU hUc hG hP hP' (restrictForm_mem hL F hB)
      (restrictForm_hasFiniteEdgeSupport hFfin B)]
end Operator
section Maps
open YangMills.Construction.Tower.UnitGaugeDirections
variable {L : ℕ}
theorem abelianOperators_swapConj (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hDirections : UnitGaugeDirections.Claim)
    (hAlgebra : LeftChartAlgebra.AllConditionsHold)
    (hKernel : HessianKernel.KernelProperties)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    (∀ l ∈ (unitVertexSpace L).complexSubmodule,
      FullSpace.abelianGaugeLaplacian (fun b => -θ b) (fun x => swapConj (l x)) =
        fun x => swapConj (FullSpace.abelianGaugeLaplacian θ l x)) ∧
    ∀ B ∈ (unitEdgeSpace L).complexSubmodule,
      FullSpace.abelianMassiveHessian (fun b => -θ b) (fun b => swapConj (B b)) =
        fun b => swapConj (FullSpace.abelianMassiveHessian θ B b) := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hpos := meshAt_pos L hL0
  have hcomplex : ∀ ϑ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.abelianLinkField ϑ ∈
        FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
    intro ϑ
    have hUr : FullSpace.abelianLinkField ϑ ∈
        FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup :=
      (hPlaquettes L hL ϑ).abelianLinkField_mem
    exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hUr.1 b)).2, hUr.2⟩
  have hUc := hcomplex θ
  have hUc' := hcomplex fun b => -θ b
  obtain ⟨hD, -, hF, -⟩ := (hDirections L hL).2 _ hUc
  obtain ⟨hD', -, hF', -⟩ := (hDirections L hL).2 _ hUc'
  obtain ⟨-, -, hrows, -, hpair, -⟩ := (hKernel L hL 0 0 le_rfl).2 _ hUc
  obtain ⟨-, -, hrows', -, hpair', -⟩ := (hKernel L hL 0 0 le_rfl).2 _ hUc'
  have hder := (hAlgebra.2.2 L 0 0 hL le_rfl).2.2.2.2.1
  have hUU := gaugeAct_iPauliX_abelian θ
  have hd : ∀ l ∈ (unitVertexSpace L).complexSubmodule,
      FullSpace.covDiff (FullSpace.abelianLinkField fun b => -θ b)
          (fun x => swapConj (l x)) =
        fun b => swapConj (FullSpace.covDiff (FullSpace.abelianLinkField θ) l b) := by
    intro l hl
    have e := ((hAlgebra.2.2 L 0 0 hL le_rfl).2.1 _ (fun _ => iPauliX) hUc
      (fun _ => (Matrix.mem_specialUnitaryGroup_iff.mp iPauliX_mem_compact).2)).1 l
      (fun x => hl x (Set.mem_univ x))
    rw [hUU, adjointForm_iPauliX hpos (hF.1 l hl).1] at e
    exact e
  refine ⟨fun l hl => ?_, fun B hB => ?_⟩
  · show FullSpace.gaugeLaplacian _ _ = fun x => swapConj (FullSpace.gaugeLaplacian _ _ x)
    unfold FullSpace.gaugeLaplacian
    rw [hd l hl, covDiffAdjoint_swapConj hD hD' hF hF' hd (hF.1 l hl).1]
  · show FullSpace.massiveHessian _ _ = fun b => swapConj (FullSpace.massiveHessian _ _ b)
    unfold FullSpace.massiveHessian
    rw [complexHessianOperator_swapConj hL0 hUU hUc hder hpair hpair' hrows hrows' hB,
      covDiffAdjoint_swapConj hD hD' hF hF' hd hB, hd _ (hF.2 B hB).1]
    funext b
    simp
end Maps
section Operators
variable {L : ℕ}
theorem ofCoords_injective {σ : Type} (hC : CoordsIsometry σ) {v v' : L2Field σ}
    (h : ofCoords v = ofCoords v') : v = v' := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.ofCoords_injective <;> assumption
theorem ofCoords_gaugeVertexFn {u : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hC : CoordsIsometry (FullSpace.Vertex L 0 0))
    (hU : IsUnitaryOnSet {l : FullSpace.Vertex L 0 0 → ComplexMatrix2 | IsL2Traceless l} id
      (FullSpace.adjointVertexFn u))
    (f : L2Field (FullSpace.Vertex L 0 0)) :
    ofCoords (gaugeVertexFn u f) = FullSpace.adjointVertexFn u (ofCoords f) := by
  obtain ⟨g, hg⟩ := hC.2.2.2.1 _ (hU.bijOn.mapsTo (hC.2.2.1 f).1)
  exact Classical.epsilon_spec (p := fun g : L2Field (FullSpace.Vertex L 0 0) =>
    ofCoords g = FullSpace.adjointVertexFn u (ofCoords f)) ⟨g, hg⟩
theorem formOfPositiveValues_apply (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (b : PeriodicOperators.PosEdge L 0 0) : formOfPositiveValues g b.1 = g b := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.formOfPositiveValues_apply <;> assumption
theorem formOfPositiveValues_mem (hL : 0 < L)
    {g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2} (hg : IsL2Traceless g) :
    formOfPositiveValues g ∈ FullSpace.l2Forms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.formOfPositiveValues_mem <;> assumption
theorem formOfPositiveValues_restrict (hL : 0 < L) {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    formOfPositiveValues (fun b : PeriodicOperators.PosEdge L 0 0 => B b.1) = B := by
  refine oddFn_ext (extendOddly_opposite (meshAt_pos L hL) _) hB.2 fun b hb => ?_
  exact formOfPositiveValues_apply _ ⟨b, hb⟩
theorem ofCoords_gaugeEdgeFn (hL : 0 < L) {u : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hC : CoordsIsometry (PeriodicOperators.PosEdge L 0 0))
    (hU : IsUnitaryOnSet (FullSpace.l2Forms (meshAt L 0 0)) FullSpace.restrictToPositiveEdges
      (FullSpace.adjointForm u))
    (f : L2Field (PeriodicOperators.PosEdge L 0 0))
    (b : PeriodicOperators.PosEdge L 0 0) :
    ofCoords (gaugeEdgeFn u f) b =
      FullSpace.adjointForm u (formOfPositiveValues (ofCoords f)) b.1 := by
  have hB := formOfPositiveValues_mem hL (hC.2.2.1 f).1
  obtain ⟨g, hg⟩ := hC.2.2.2.1 _ (hU.bijOn.mapsTo hB).2
  exact Classical.epsilon_spec (p := fun g : L2Field (PeriodicOperators.PosEdge L 0 0) =>
    ∀ b : PeriodicOperators.PosEdge L 0 0, ofCoords g b =
      FullSpace.adjointForm u (formOfPositiveValues (ofCoords f)) b.1)
    ⟨g, fun b => congrFun hg b⟩ b
theorem vertexAdd_zero (x : FullSpace.Vertex L 0 0) : vertexAdd (L := L) 0 x = x := by
  have hv : PeriodicOperators.castVec 0 = 0 := by
    funext μ
    simp [PeriodicOperators.castVec]
  have e := Classical.epsilon_spec
    (p := fun x' : FullSpace.Vertex L 0 0 =>
      (x' : InfiniteLattice.AmbientSpace) = PeriodicOperators.intShift 0 x)
    ⟨x, by simp [PeriodicOperators.intShift, hv]⟩
  exact Subtype.ext (e.trans (by simp [PeriodicOperators.intShift, hv]))
end Operators
theorem densityEvenInField_holds
    (hSectors : LogSectorsAndDensity)
    (hOperators : AbelianOperatorsLocalSelfAdjoint)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hDirections : UnitGaugeDirections.Claim)
    (hAlgebra : LeftChartAlgebra.AllConditionsHold)
    (hKernel : HessianKernel.KernelProperties)
    (hSquare : UnitLatticeL2Statement) :
    DensityEvenInField := by
  intro L hL z hz θ hform
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hpos := meshAt_pos L hL0
  have hCs := (hSquare.2 L).2.1.1
  have hCb := (hSquare.2 L).2.2.1
  obtain ⟨-, -, hUb, hUs⟩ := ((hAlgebra.2.2 L 0 0 hL le_rfl).2.2.1).2.2 (fun _ => iPauliX)
    fun _ => iPauliX_mem_compact
  obtain ⟨hmL, hmK⟩ := abelianOperators_swapConj hL hPlaquettes hDirections hAlgebra hKernel θ
  have hg : DensityInvariance z (gaugeVertexFn (L := L) fun _ => iPauliX)
      (gaugeEdgeFn (L := L) fun _ => iPauliX) 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := (hSectors.2 L hL z hz)
    exact h _ fun _ => iPauliX_mem_compact
  have hO := hOperators L hL θ
  have hO' := hOperators L hL fun b => -θ b
  have hVs : ∀ f, gaugeVertexFn (L := L) (fun _ => iPauliX) (laplacianOp θ f) =
      laplacianOp (fun b => -θ b) (gaugeVertexFn (L := L) (fun _ => iPauliX) f) := by
    intro f
    refine ofCoords_injective hCs ?_
    have hf : ofCoords f ∈ (UnitGaugeDirections.unitVertexSpace L).complexSubmodule :=
      fun x _ => (hCs.2.2.1 f).1.1 x
    rw [ofCoords_gaugeVertexFn hCs hUs, hO.laplacian_apply, hO'.laplacian_apply,
      ofCoords_gaugeVertexFn hCs hUs]
    exact (hmL _ hf).symm
  have hVb : ∀ f, gaugeEdgeFn (L := L) (fun _ => iPauliX) (massiveOp θ f) =
      massiveOp (fun b => -θ b) (gaugeEdgeFn (L := L) (fun _ => iPauliX) f) := by
    intro f
    refine ofCoords_injective hCb ?_
    obtain ⟨B, hBdef⟩ : ∃ B, B = formOfPositiveValues (ofCoords f) := ⟨_, rfl⟩
    have hB : B ∈ FullSpace.l2Forms (meshAt L 0 0) := by
      rw [hBdef]
      exact formOfPositiveValues_mem hL0 (hCb.2.2.1 f).1
    have hK : FullSpace.abelianMassiveHessian θ B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
      obtain ⟨-, -, hF, -⟩ := (hDirections L hL).2 _ (by
        have hUr : FullSpace.abelianLinkField θ ∈
            FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup :=
          (hPlaquettes L hL θ).abelianLinkField_mem
        exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hUr.1 b)).2, hUr.2⟩)
      exact (hF.2 B hB.1).2.2.2
    have e₁ : formOfPositiveValues (ofCoords (massiveOp θ f)) =
        FullSpace.abelianMassiveHessian θ B := by
      rw [hO.hessian_apply, ← hBdef]
      exact formOfPositiveValues_restrict hL0 hK
    have e₂ : formOfPositiveValues
        (ofCoords (gaugeEdgeFn (L := L) (fun _ => iPauliX) f)) =
        fun b => swapConj (B b) := by
      have e : ofCoords (gaugeEdgeFn (L := L) (fun _ => iPauliX) f) =
          fun b : PeriodicOperators.PosEdge L 0 0 => swapConj (B b.1) := by
        funext b
        rw [ofCoords_gaugeEdgeFn hL0 hCb hUb, ← hBdef, adjointForm_iPauliX hpos hB.1]
      rw [e]
      exact formOfPositiveValues_restrict hL0 (swapConj_mem_forms hB.1)
    funext b
    rw [ofCoords_gaugeEdgeFn hL0 hCb hUb, hO'.hessian_apply, e₁, e₂,
      adjointForm_iPauliX hpos hK, hmK B hB.1]
  obtain ⟨h₁, h₂⟩ := hg.2.2 θ (fun b => -θ b) hform hVs hVb
  refine ⟨h₁, fun x => ?_⟩
  have e := h₂ x
  rwa [vertexAdd_zero] at e
end YangMills.Construction.Tower.AbelianFieldDensity.EvenInFieldProof
end
