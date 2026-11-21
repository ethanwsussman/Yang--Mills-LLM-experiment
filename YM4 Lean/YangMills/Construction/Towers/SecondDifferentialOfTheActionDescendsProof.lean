import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonActionProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Torus.ProjectionsOfTheSequenceProof
import YangMills.Construction.Towers.DerivativesOfAPlaquetteTerm
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import YangMills.Construction.Towers.PeriodicExtensionOfAConfigurationIsAConfiguration
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernelProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionDescends
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.HessianAtLifts
open Periodisation Tower Matrices
open PeriodicOperators (KernelMatrix applyKernel HasFiniteSupport)
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem sum_smul_pauli_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
private theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
section Generic
variable {β : Type} {pos : β → Prop} (rev : β → β)
def oddExtension (c : Fin 3 × {b // pos b} → ℂ) : β → ComplexMatrix2 :=
  open Classical in fun b =>
    if h : pos b then ofPauliCoeffs c ⟨b, h⟩
    else if h' : pos (rev b) then -ofPauliCoeffs c ⟨rev b, h'⟩ else 0
variable {rev}
theorem oddExtension_of_pos (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    oddExtension rev c b = ofPauliCoeffs c ⟨b, h⟩ := dif_pos h
theorem oddExtension_mem_traceless (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    oddExtension rev c b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_mem <;> assumption
theorem toPauliCoeffs_oddExtension (c : Fin 3 × {b // pos b} → ℂ) :
    toPauliCoeffs (fun b : {b // pos b} => oddExtension rev c b.1) = c := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.toPauliCoeffs_antisymmExtend <;> assumption
theorem oddExtension_rev (hrr : ∀ b, rev (rev b) = b) (hx : ∀ b, Xor (pos b) (pos (rev b)))
    (c : Fin 3 × {b // pos b} → ℂ) (b : β) :
    oddExtension rev c (rev b) = -oddExtension rev c b := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_rev <;> assumption
theorem oddExtension_toPauliCoeffs (hrr : ∀ b, rev (rev b) = b)
    (hx : ∀ b, Xor (pos b) (pos (rev b))) {B : β → ComplexMatrix2}
    (hm : ∀ b, pos b → B b ∈ ComplexMatrix2.traceless) (hr : ∀ b, B (rev b) = -B b) :
    oddExtension rev (toPauliCoeffs fun b : {b // pos b} => B b.1) = B := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_toPauliCoeffs <;> assumption
theorem oddExtension_add (c c' : Fin 3 × {b // pos b} → ℂ) :
    oddExtension rev (c + c') = oddExtension rev c + oddExtension rev c' := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_add <;> assumption
theorem oddExtension_smul (z : ℂ) (c : Fin 3 × {b // pos b} → ℂ) :
    oddExtension rev (z • c) = z • oddExtension rev c := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_smul <;> assumption
end Generic
theorem toPauliCoeffs_add {σ : Type} {X Y : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless)
    (p : Fin 3 × σ) : toPauliCoeffs (X + Y) p = toPauliCoeffs X p + toPauliCoeffs Y p :=
  pauliCoeff_add p.1 (hX p.2) (hY p.2)
theorem toPauliCoeffs_smul {σ : Type} (z : ℂ) {X : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (p : Fin 3 × σ) :
    toPauliCoeffs (z • X) p = z * toPauliCoeffs X p :=
  pauliCoeff_smul p.1 z (hX p.2)
section Sides
variable {L n k j : ℕ}
def fullIdxEquiv (L k j : ℕ) (h : j ≤ k) :
    Idx L (CellClass.edgeClass k j h).colourPairs ≃ Fin 3 × PeriodicOperators.PosEdge L k j where
  toFun ι := ι.2
  invFun p := ⟨(), p⟩
  left_inv ι := by rcases ι with ⟨⟨⟩, p⟩; rfl
  right_inv _ := rfl
abbrev EdgeProjSurjective (L n k j : ℕ) : Prop :=
  Function.Surjective (Cell.proj n : Cell L k j .edge → QuotientCell L n k j .edge)
theorem mem_colourPairs_image (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (p : Fin 3 × Tower.PositiveEdge L n k j) :
    p ∈ (CellClass.edgeClass k j h).colourComponent.image L n := by
  obtain ⟨b, hb⟩ := hs p.2
  exact ⟨(p.1, b), Prod.ext rfl hb⟩
def quotIdxEquiv (h : j ≤ k) (hs : EdgeProjSurjective L n k j) :
    (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n ≃
      Fin 3 × Tower.PositiveEdge L n k j where
  toFun κ := κ.2.1
  invFun p := ⟨(), ⟨p, mem_colourPairs_image h hs p⟩⟩
  left_inv κ := by rcases κ with ⟨⟨⟩, p, hp⟩; rfl
  right_inv _ := rfl
def fullForm (h : j ≤ k) (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    FullSpace.Edge L k j → ComplexMatrix2 :=
  oddExtension (pos := fun b => b.IsPositivelyOriented) InfiniteLattice.Link.opposite
    fun p => f ((fullIdxEquiv L k j h).symm p)
def quotForm (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    Edge L n k j → ComplexMatrix2 :=
  oddExtension (pos := fun b => b.IsPositivelyOriented) PeriodicLattice.Bond.opposite
    fun p => f ((quotIdxEquiv h hs).symm p)
theorem link_opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem link_xor_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem fullForm_coeffsOn (ha : 0 < meshAt L k j) (h : j ≤ k)
    {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    fullForm h (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) = B :=
  oddExtension_toPauliCoeffs link_opposite_opposite (link_xor_opposite ha) hB.1 hB.2
theorem quotForm_quotCoeffsOn
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : EdgeProjSurjective L n k j) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    quotForm h hs (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B) = B :=
  oddExtension_toPauliCoeffs PeriodicLattice.Bond.opposite_opposite hx hB.1 hB.2
theorem quotCoeffsOn_quotForm (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) (quotForm h hs f) = f := by
  funext κ
  have e := congrFun (toPauliCoeffs_oddExtension
    (pos := fun b : Edge L n k j => b.IsPositivelyOriented)
    (rev := PeriodicLattice.Bond.opposite) fun p => f ((quotIdxEquiv h hs).symm p))
    (quotIdxEquiv h hs κ)
  rw [Equiv.symm_apply_apply] at e
  exact e
theorem fullForm_add (h : j ≤ k) (f g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullForm h (f + g) = fullForm h f + fullForm h g :=
  oddExtension_add (fun p => f ((fullIdxEquiv L k j h).symm p))
    (fun p => g ((fullIdxEquiv L k j h).symm p))
theorem fullForm_smul (h : j ≤ k) (z : ℂ)
    (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullForm h (z • f) = z • fullForm h f :=
  oddExtension_smul z fun p => f ((fullIdxEquiv L k j h).symm p)
theorem quotForm_add (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (f g : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotForm h hs (f + g) = quotForm h hs f + quotForm h hs g :=
  oddExtension_add (fun p => f ((quotIdxEquiv h hs).symm p))
    (fun p => g ((quotIdxEquiv h hs).symm p))
theorem quotForm_smul (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (z : ℂ)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotForm h hs (z • f) = z • quotForm h hs f :=
  oddExtension_smul z fun p => f ((quotIdxEquiv h hs).symm p)
theorem coeffsOn_hasFiniteSupport (h : j ≤ k) {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : HasFiniteSupp (FullSpace.restrictToPositiveEdges B)) :
    HasFiniteSupport (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) := by
  have hfin := ((finite_univ (α := Fin 3)).prod hB).image (fullIdxEquiv L k j h).symm
  refine hfin.subset fun ι hι => ?_
  refine ⟨fullIdxEquiv L k j h ι, ⟨mem_univ _, fun h0 => hι ?_⟩,
    (fullIdxEquiv L k j h).symm_apply_apply ι⟩
  show pauliCoeff _ (FullSpace.restrictToPositiveEdges B (fullIdxEquiv L k j h ι).2) = 0
  rw [h0, pauliCoeff_zero]
private theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem fullForm_lift (ha : 0 < meshAt L k j)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (hB : ProjEdgesCompatible L n k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    fullForm h ((CellClass.edgeClass k j h).colourPairs.lift L n f) =
      liftGaugeField L n k j (quotForm h hs f) := by
  have hrev : ∀ b : FullSpace.Edge L k j,
      FullSpace.projEdge L n k j b.opposite = (FullSpace.projEdge L n k j b).opposite := fun b =>
    PeriodicLattice.Bond.ext ((hB.1 b.opposite).1.trans (hB.1 b).2.symm)
      ((hB.1 b.opposite).2.trans (hB.1 b).1.symm)
  have hform : liftGaugeField L n k j (quotForm h hs f) ∈
      FullSpace.complexEdgeForms (meshAt L k j) := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · show quotForm h hs f (FullSpace.projEdge L n k j b) ∈ ComplexMatrix2.traceless
      rw [← hB.2.1 ⟨b, hb⟩]
      exact oddExtension_mem_traceless _ (projPositiveEdge L n k j ⟨b, hb⟩).2
    · show quotForm h hs f (FullSpace.projEdge L n k j b.opposite) =
        -quotForm h hs f (FullSpace.projEdge L n k j b)
      rw [hrev]
      exact oddExtension_rev PeriodicLattice.Bond.opposite_opposite hx _ _
  have hread : CellClass.coeffsOn L (CellClass.edgeClass k j h)
      (liftGaugeField L n k j (quotForm h hs f)) =
      (CellClass.edgeClass k j h).colourPairs.lift L n f := by
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (quotForm h hs f (FullSpace.projEdge L n k j c.1)) =
      f ((CellClass.edgeClass k j h).colourPairs.proj L n ⟨(), (a, c)⟩)
    rw [← hB.2.1 c]
    exact congrFun (quotCoeffsOn_quotForm h hs f)
      ((CellClass.edgeClass k j h).colourPairs.proj L n ⟨(), (a, c)⟩)
  rw [← hread]
  exact fullForm_coeffsOn ha h hform
theorem fullForm_congr (h : j ≤ k) {f g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (b : PeriodicOperators.PosEdge L k j)
    (e : ∀ a, f ((fullIdxEquiv L k j h).symm (a, b)) = g ((fullIdxEquiv L k j h).symm (a, b))) :
    fullForm h f b.1 = fullForm h g b.1 := by
  unfold fullForm
  rw [oddExtension_of_pos _ b.2, oddExtension_of_pos _ b.2]
  exact Finset.sum_congr rfl fun a _ => congrArg (· • ComplexMatrix2.pauliFamily a) (e a)
end Sides
section Polar
open FaceTermDerivatives (secondDerivExpr)
def bracketSum (Y Y' : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  ∑ i : Fin 4, ∑ m ∈ Finset.Ioi i, (Y i * Y' m - Y' m * Y i)
def mixedSecondExpr (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) : ℂ :=
  (1 / 2) * ComplexMatrix2.fullTrace W * ComplexMatrix2.halfTrace ((∑ i, Y i) * ∑ i, Y' i) +
    (1 / 4) * ComplexMatrix2.fullTrace (bracketSum Y Y' * (W - W⁻¹))
theorem secondDerivExpr_eq_mixed (Y : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    secondDerivExpr Y W = mixedSecondExpr Y Y W := rfl
theorem bracketSum_add_left (Y₁ Y₂ Y' : Fin 4 → ComplexMatrix2) :
    bracketSum (Y₁ + Y₂) Y' = bracketSum Y₁ Y' + bracketSum Y₂ Y' := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_add_left <;> assumption
theorem bracketSum_add_right (Y Y₁ Y₂ : Fin 4 → ComplexMatrix2) :
    bracketSum Y (Y₁ + Y₂) = bracketSum Y Y₁ + bracketSum Y Y₂ := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_add_right <;> assumption
theorem bracketSum_smul_left (z : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) :
    bracketSum (z • Y) Y' = z • bracketSum Y Y' := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_smul_left <;> assumption
theorem bracketSum_smul_right (z : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) :
    bracketSum Y (z • Y') = z • bracketSum Y Y' := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.bracketSumOrdered_smul_right <;> assumption
theorem fullTrace_add (X Y : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (X + Y) = ComplexMatrix2.fullTrace X + ComplexMatrix2.fullTrace Y :=
  Matrix.trace_add X Y
theorem fullTrace_smul (z : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (z • X) = z * ComplexMatrix2.fullTrace X := by
  simp [ComplexMatrix2.fullTrace, Matrix.trace_smul]
theorem halfTrace_add (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (X + Y) = ComplexMatrix2.halfTrace X + ComplexMatrix2.halfTrace Y := by
  simp only [ComplexMatrix2.halfTrace, fullTrace_add]
  ring
theorem halfTrace_smul (z : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (z • X) = z * ComplexMatrix2.halfTrace X := by
  simp only [ComplexMatrix2.halfTrace, fullTrace_smul]
  ring
theorem mixedSecondExpr_add_left (Y₁ Y₂ Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    mixedSecondExpr (Y₁ + Y₂) Y' W = mixedSecondExpr Y₁ Y' W + mixedSecondExpr Y₂ Y' W := by
  have h : ∑ i, (Y₁ + Y₂) i = ∑ i, Y₁ i + ∑ i, Y₂ i := Finset.sum_add_distrib
  simp only [mixedSecondExpr, h, bracketSum_add_left, add_mul, halfTrace_add, fullTrace_add]
  ring
theorem mixedSecondExpr_add_right (Y Y₁ Y₂ : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    mixedSecondExpr Y (Y₁ + Y₂) W = mixedSecondExpr Y Y₁ W + mixedSecondExpr Y Y₂ W := by
  have h : ∑ i, (Y₁ + Y₂) i = ∑ i, Y₁ i + ∑ i, Y₂ i := Finset.sum_add_distrib
  simp only [mixedSecondExpr, h, bracketSum_add_right, add_mul, mul_add, halfTrace_add,
    fullTrace_add]
  ring
theorem mixedSecondExpr_smul_left (z : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    mixedSecondExpr (z • Y) Y' W = z * mixedSecondExpr Y Y' W := by
  have h : ∑ i, (z • Y) i = z • ∑ i, Y i := by simp only [Pi.smul_apply, Finset.smul_sum]
  simp only [mixedSecondExpr, h, bracketSum_smul_left, smul_mul_assoc, halfTrace_smul,
    fullTrace_smul]
  ring
theorem mixedSecondExpr_smul_right (z : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    mixedSecondExpr Y (z • Y') W = z * mixedSecondExpr Y Y' W := by
  have h : ∑ i, (z • Y') i = z • ∑ i, Y' i := by simp only [Pi.smul_apply, Finset.smul_sum]
  simp only [mixedSecondExpr, h, bracketSum_smul_right, smul_mul_assoc, mul_smul_comm,
    halfTrace_smul, fullTrace_smul]
  ring
def polarSecondExpr (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) : ℂ :=
  (1 / 2) * (mixedSecondExpr Y Y' W + mixedSecondExpr Y' Y W)
theorem polarSecondExpr_add_left (Y₁ Y₂ Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    polarSecondExpr (Y₁ + Y₂) Y' W = polarSecondExpr Y₁ Y' W + polarSecondExpr Y₂ Y' W := by
  simp only [polarSecondExpr, mixedSecondExpr_add_left, mixedSecondExpr_add_right]
  ring
theorem polarSecondExpr_add_right (Y Y₁ Y₂ : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    polarSecondExpr Y (Y₁ + Y₂) W = polarSecondExpr Y Y₁ W + polarSecondExpr Y Y₂ W := by
  simp only [polarSecondExpr, mixedSecondExpr_add_left, mixedSecondExpr_add_right]
  ring
theorem polarSecondExpr_smul_left (z : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    polarSecondExpr (z • Y) Y' W = z * polarSecondExpr Y Y' W := by
  simp only [polarSecondExpr, mixedSecondExpr_smul_left, mixedSecondExpr_smul_right]
  ring
theorem polarSecondExpr_smul_right (z : ℂ) (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    polarSecondExpr Y (z • Y') W = z * polarSecondExpr Y Y' W := by
  simp only [polarSecondExpr, mixedSecondExpr_smul_left, mixedSecondExpr_smul_right]
  ring
theorem secondDerivExpr_add (Y Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    secondDerivExpr (Y + Y') W =
      secondDerivExpr Y W + secondDerivExpr Y' W + 2 * polarSecondExpr Y Y' W := by
  simp only [secondDerivExpr_eq_mixed, polarSecondExpr, mixedSecondExpr_add_left,
    mixedSecondExpr_add_right]
  ring
theorem mixedSecondExpr_zero_left (Y' : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    mixedSecondExpr 0 Y' W = 0 := by
  simpa using mixedSecondExpr_smul_left 0 0 Y' W
theorem mixedSecondExpr_zero_right (Y : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    mixedSecondExpr Y 0 W = 0 := by
  simpa using mixedSecondExpr_smul_right 0 Y 0 W
theorem polarSecondExpr_zero_right (Y : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) :
    polarSecondExpr Y 0 W = 0 := by
  simp [polarSecondExpr, mixedSecondExpr_zero_left, mixedSecondExpr_zero_right]
theorem secondDerivExpr_zero (W : ComplexMatrix2) : secondDerivExpr 0 W = 0 := by
  rw [secondDerivExpr_eq_mixed, mixedSecondExpr_zero_left]
theorem symmBilinear_add_add {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : HessianKernel.IsSymmBilinearOn 𝒮 Q) {X Y : α → ComplexMatrix2}
    (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hXY : X + Y ∈ 𝒮) :
    Q (X + Y) (X + Y) = Q X X + Q Y Y + 2 * Q X Y := by
  have h₁ := (hQ 1 X hX Y hY _ hXY).1
  have h₂ := (hQ 1 X hX Y hY X hX).2.1
  have h₃ := (hQ 1 X hX Y hY Y hY).2.1
  have h₄ := (hQ 1 X hX Y hY Y hY).2.2
  simp only [one_smul, one_mul] at h₁ h₂ h₃
  rw [h₁, h₂, h₃, ← h₄]
  ring
theorem finsum_polarization {P : Type} (q₁ q₂ q₃ t : P → ℂ) {Ω : Set P} (hΩ : Ω.Finite)
    (h₁ : ∀ p ∉ Ω, q₁ p = 0) (h₂ : ∀ p ∉ Ω, q₂ p = 0) (ht : ∀ p ∉ Ω, t p = 0)
    (h : ∀ p, q₃ p = q₁ p + q₂ p + 2 * t p) :
    ∑ᶠ p, q₃ p = ∑ᶠ p, q₁ p + ∑ᶠ p, q₂ p + 2 * ∑ᶠ p, t p := by
  have e : ∀ f : P → ℂ, (∀ p ∉ Ω, f p = 0) → ∑ᶠ p, f p = ∑ p ∈ hΩ.toFinset, f p := fun f hf =>
    finsum_eq_sum_of_support_subset _ fun p hp => by
      by_contra hn
      exact hp (hf p (by simpa using hn))
  rw [e q₃ fun p hp => by rw [h, h₁ p hp, h₂ p hp, ht p hp]; simp, e q₁ h₁, e q₂ h₂, e t ht,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => h p
end Polar
section Terms
open FaceTermDerivatives (secondDerivExpr)
theorem quot_transportedForm_add {L n k j : ℕ} (U B B' : Edge L n k j → ComplexMatrix2)
    (p : Face L n k j) :
    transportedForm U (B + B') p = transportedForm U B p + transportedForm U B' p := by
  funext i
  simp [transportedForm, ComplexMatrix2.conjugateBy, mul_add, add_mul, smul_add]
theorem quot_transportedForm_smul {L n k j : ℕ} (z : ℂ) (U B : Edge L n k j → ComplexMatrix2)
    (p : Face L n k j) :
    transportedForm U (z • B) p = z • transportedForm U B p := by
  funext i
  simp only [transportedForm, ComplexMatrix2.conjugateBy, Pi.smul_apply, mul_smul_comm,
    smul_mul_assoc]
  exact smul_comm _ _ _
theorem full_transportedForm_add {a : ℝ} (U B B' : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.transportedForm U (B + B') p =
      FullSpace.transportedForm U B p + FullSpace.transportedForm U B' p := by
  funext i
  simp [FullSpace.transportedForm, ComplexMatrix2.conjugateBy, mul_add, add_mul, smul_add]
theorem full_transportedForm_smul {a : ℝ} (z : ℂ) (U B : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.transportedForm U (z • B) p = z • FullSpace.transportedForm U B p := by
  funext i
  simp only [FullSpace.transportedForm, ComplexMatrix2.conjugateBy, Pi.smul_apply, mul_smul_comm,
    smul_mul_assoc]
  exact smul_comm _ _ _
theorem full_transportedForm_eq_zero {a : ℝ} {U B : InfiniteLattice.Link a → ComplexMatrix2}
    {p : InfiniteLattice.ElementaryPlaquette a} (h : ∀ i, B (FullSpace.faceEdge p i) = 0) :
    FullSpace.transportedForm U B p = 0 := by
  funext i
  simp [FullSpace.transportedForm, ComplexMatrix2.conjugateBy, h i]
def quotFaceTerm {L n k j : ℕ} (U X Y : Edge L n k j → ComplexMatrix2) (p : Face L n k j) : ℂ :=
  polarSecondExpr (transportedForm U X p) (transportedForm U Y p)
    (PeriodicLattice.plaquetteHolonomy U p)
def fullFaceTerm {a : ℝ} (U X Y : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) : ℂ :=
  polarSecondExpr (FullSpace.transportedForm U X p) (FullSpace.transportedForm U Y p)
    (FullSpace.faceVariable U p)
theorem forwardFrom_isPositivelyOriented {a : ℝ} (x : InfiniteLattice.LatticePoint a)
    (μ : Fin 4) : (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem full_faceEdge_isPositivelyOriented {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a)
    (i : Fin 4) : (FullSpace.faceEdge p i).IsPositivelyOriented := by
  fin_cases i <;> exact forwardFrom_isPositivelyOriented _ _
theorem full_faceEdge_mem {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    FullSpace.faceEdge p i ∈ FullSpace.faceEdges p :=
  List.getElem_mem _
theorem supNormVec_single_le {a : ℝ} (ha : 0 ≤ a) (μ : Fin 4) :
    TorusMetric.supNormVec (Pi.single μ a) ≤ a := by apply _root_.YangMills.Construction.Weighted.ProjectionProof.supNormVec_single_le <;> assumption
theorem full_faceEdge_near {a : ℝ} (ha : 0 ≤ a) (p : InfiniteLattice.ElementaryPlaquette a)
    (i : Fin 4) :
    TorusMetric.supNormVec ((FullSpace.faceEdge p i).initial.1 - p.corner.1) ≤ a := by
  have h0 : TorusMetric.supNormVec ((p.corner.1 : InfiniteLattice.AmbientSpace) - p.corner.1)
      ≤ a := by
    rw [sub_self]
    refine Finset.sup'_le _ _ fun ν _ => ?_
    simpa using ha
  have h1 : ∀ μ, TorusMetric.supNormVec (((p.corner + InfiniteLattice.axisStep a μ).1 :
      InfiniteLattice.AmbientSpace) - p.corner.1) ≤ a := fun μ => by
    have e : (((p.corner + InfiniteLattice.axisStep a μ).1 : InfiniteLattice.AmbientSpace) -
        p.corner.1) = Pi.single μ a := by
      show (p.corner.1 + Pi.single μ a) - p.corner.1 = _
      abel
    rw [e]
    exact supNormVec_single_le ha μ
  fin_cases i
  · exact h0
  · exact h1 _
  · exact h1 _
  · exact h0
theorem full_faces_finite_of_forms {L k j : ℕ} (hS : FacesContainingEdge.OnFullSpace L k j)
    {X Y : FullSpace.Edge L k j → ComplexMatrix2} (hX : FullSpace.HasFiniteEdgeSupport X)
    (hY : FullSpace.HasFiniteEdgeSupport Y) :
    ∃ Ω : Set (FullSpace.Face L k j), Ω.Finite ∧ ∀ p ∉ Ω, ∀ i,
      X (FullSpace.faceEdge p i) = 0 ∧ Y (FullSpace.faceEdge p i) = 0 := by
  have h₁ : (Subtype.val ⁻¹' FullSpace.edgeSupport X :
      Set (FullSpace.PositiveEdge (meshAt L k j))).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hX
  have h₂ : (Subtype.val ⁻¹' FullSpace.edgeSupport Y :
      Set (FullSpace.PositiveEdge (meshAt L k j))).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hY
  refine ⟨_, hS.2.2 _ (h₁.union h₂), fun p hp i => ?_⟩
  by_contra hne
  refine hp ⟨⟨_, full_faceEdge_isPositivelyOriented p i⟩, ?_, full_faceEdge_mem p i⟩
  by_contra h
  simp only [Set.mem_union, Set.mem_preimage, not_or] at h
  refine hne ⟨?_, ?_⟩
  · by_contra h0
    exact h.1 ⟨full_faceEdge_isPositivelyOriented p i, h0⟩
  · by_contra h0
    exact h.2 ⟨full_faceEdge_isPositivelyOriented p i, h0⟩
theorem fullFaceTerm_eq_zero {a : ℝ} {U X Y : InfiniteLattice.Link a → ComplexMatrix2}
    {p : InfiniteLattice.ElementaryPlaquette a} (h : ∀ i, Y (FullSpace.faceEdge p i) = 0) :
    fullFaceTerm U X Y p = 0 := by
  rw [fullFaceTerm, full_transportedForm_eq_zero h, polarSecondExpr_zero_right]
theorem full_hessian_eq_finsum {L k j : ℕ} (hD : FaceTermDerivatives.HoldsOnFullSpaceLevel L k j)
    (hK : HessianKernel.HoldsOnFullSpace L k j)
    (hS : FacesContainingEdge.OnFullSpace L k j) {U X Y : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hX : X ∈ HessianKernel.finiteSupportComplexForms L k j)
    (hY : Y ∈ HessianKernel.finiteSupportComplexForms L k j) :
    FullSpace.complexActionHessian U X Y = ∑ᶠ p, fullFaceTerm U X Y p := by
  have hXY : X + Y ∈ HessianKernel.finiteSupportComplexForms L k j := by
    refine ⟨(FullSpace.complexEdgeForms _).add_mem hX.1 hY.1,
      (Set.Finite.union hX.2 hY.2).subset ?_⟩
    rintro b ⟨hb, hne⟩
    by_contra h
    simp only [Set.mem_union, not_or] at h
    have h1 : X b = 0 := by
      by_contra h1
      exact h.1 ⟨hb, h1⟩
    have h2 : Y b = 0 := by
      by_contra h2
      exact h.2 ⟨hb, h2⟩
    exact hne (by simp [h1, h2])
  have hQ := symmBilinear_add_add (hK U hU).1 hX hY hXY
  have d₃ := (((hD _ hXY.1).2 hXY.2).1 U hU).1
  have d₁ := (((hD _ hX.1).2 hX.2).1 U hU).1
  have d₂ := (((hD _ hY.1).2 hY.2).1 U hU).1
  obtain ⟨Ω, hΩ, hout⟩ := full_faces_finite_of_forms hS hX.2 hY.2
  have hp := finsum_polarization
    (fun p => secondDerivExpr (FullSpace.transportedForm U X p) (FullSpace.faceVariable U p))
    (fun p => secondDerivExpr (FullSpace.transportedForm U Y p) (FullSpace.faceVariable U p))
    (fun p => secondDerivExpr (FullSpace.transportedForm U (X + Y) p)
      (FullSpace.faceVariable U p))
    (fun p => fullFaceTerm U X Y p) hΩ
    (fun p hp => by
      show secondDerivExpr _ _ = 0
      rw [full_transportedForm_eq_zero fun i => (hout p hp i).1, secondDerivExpr_zero])
    (fun p hp => by
      show secondDerivExpr _ _ = 0
      rw [full_transportedForm_eq_zero fun i => (hout p hp i).2, secondDerivExpr_zero])
    (fun p hp => fullFaceTerm_eq_zero fun i => (hout p hp i).2)
    (fun p => by
      show secondDerivExpr _ _ = _
      rw [full_transportedForm_add]
      exact secondDerivExpr_add _ _ _)
  rw [d₃, d₁, d₂, hQ] at hp
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ h2 (add_left_cancel hp)
theorem quot_hessian_eq_finsum {L n k j : ℕ} [Finite (Face L n k j)]
    (hD : FaceTermDerivatives.HoldsOnPeriodicLevel L n k j)
    (hK : HessianKernel.HoldsOnTorus L n k j) {U X Y : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hX : X ∈ complexEdgeForms L n k j) (hY : Y ∈ complexEdgeForms L n k j) :
    complexActionHessian U X Y = ∑ᶠ p, quotFaceTerm U X Y p := by
  have hXY : X + Y ∈ complexEdgeForms L n k j := (complexEdgeForms L n k j).add_mem hX hY
  have hQ := symmBilinear_add_add
    (𝒮 := (complexEdgeForms L n k j : Set (Edge L n k j → ComplexMatrix2))) (hK U hU).1 hX hY hXY
  have d₃ := ((hD _ hXY).1 U hU).2.1
  have d₁ := ((hD _ hX).1 U hU).2.1
  have d₂ := ((hD _ hY).1 U hU).2.1
  have hp := finsum_polarization (Ω := univ)
    (fun p => secondDerivExpr (transportedForm U X p) (PeriodicLattice.plaquetteHolonomy U p))
    (fun p => secondDerivExpr (transportedForm U Y p) (PeriodicLattice.plaquetteHolonomy U p))
    (fun p => secondDerivExpr (transportedForm U (X + Y) p)
      (PeriodicLattice.plaquetteHolonomy U p))
    (fun p => quotFaceTerm U X Y p) (Set.toFinite _)
    (fun p hp => absurd (mem_univ p) hp) (fun p hp => absurd (mem_univ p) hp)
    (fun p hp => absurd (mem_univ p) hp)
    (fun p => by
      show secondDerivExpr _ _ = _
      rw [quot_transportedForm_add]
      exact secondDerivExpr_add _ _ _)
  rw [d₃, d₁, d₂, hQ] at hp
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ h2 (add_left_cancel hp)
end Terms
section Extension
variable {L n k j : ℕ}
theorem edge_pos_or_opposite_pos (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem edge_not_both_pos (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem projEdge_opposite (hB : ProjEdgesCompatible L n k j) (b : FullSpace.Edge L k j) :
    FullSpace.projEdge L n k j b.opposite = (FullSpace.projEdge L n k j b).opposite :=
  PeriodicLattice.Bond.ext ((hB.1 b.opposite).1.trans (hB.1 b).2.symm)
    ((hB.1 b.opposite).2.trans (hB.1 b).1.symm)
theorem projEdge_faceEdge (hB : ProjEdgesCompatible L n k j) (p : FullSpace.Face L k j)
    (i : Fin 4) :
    FullSpace.projEdge L n k j (FullSpace.faceEdge p i) =
      faceEdge (FullSpace.projFace L n k j p) i := by
  have e := hB.2.2 p
  simp only [faceEdges, FullSpace.faceEdges, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  fin_cases i
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm
theorem faceVariable_lift (hB : ProjEdgesCompatible L n k j) (V : Edge L n k j → ComplexMatrix2)
    (p : FullSpace.Face L k j) :
    FullSpace.faceVariable (liftGaugeField L n k j V) p =
      PeriodicLattice.plaquetteHolonomy V (FullSpace.projFace L n k j p) := by
  have e := hB.2.2 p
  simp only [faceEdges, FullSpace.faceEdges, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary,
    PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, liftGaugeField, projEdge_opposite hB]
  rw [← e0, ← e1, ← e2, ← e3]
theorem faceTransports_lift (hB : ProjEdgesCompatible L n k j) (V : Edge L n k j → ComplexMatrix2)
    (p : FullSpace.Face L k j) :
    FullSpace.faceTransports (liftGaugeField L n k j V) p =
      faceTransports V (FullSpace.projFace L n k j p) := by
  have b0 := projEdge_faceEdge hB p 0
  have b1 := projEdge_faceEdge hB p 1
  have b2 := projEdge_faceEdge hB p 2
  simp only [FullSpace.faceTransports, faceTransports, faceVariable_lift hB, liftGaugeField, b0,
    b1, b2]
theorem fullFaceTerm_lift (hB : ProjEdgesCompatible L n k j) (V X Y : Edge L n k j → ComplexMatrix2)
    (p : FullSpace.Face L k j) :
    fullFaceTerm (liftGaugeField L n k j V) (liftGaugeField L n k j X)
        (liftGaugeField L n k j Y) p =
      quotFaceTerm V X Y (FullSpace.projFace L n k j p) := by
  have ht : ∀ B : Edge L n k j → ComplexMatrix2,
      FullSpace.transportedForm (liftGaugeField L n k j V) (liftGaugeField L n k j B) p =
        transportedForm V B (FullSpace.projFace L n k j p) := fun B => by
    funext i
    show transportSign i • ComplexMatrix2.conjugateBy
        (FullSpace.faceTransports (liftGaugeField L n k j V) p i)
        (B (FullSpace.projEdge L n k j (FullSpace.faceEdge p i))) =
      transportSign i • ComplexMatrix2.conjugateBy
        (faceTransports V (FullSpace.projFace L n k j p) i)
        (B (faceEdge (FullSpace.projFace L n k j p) i))
    rw [faceTransports_lift hB, projEdge_faceEdge hB]
  rw [fullFaceTerm, quotFaceTerm, ht, ht, faceVariable_lift hB]
end Extension
section Maps
variable {L n k j : ℕ}
theorem quotFaceTerm_add_left (V X₁ X₂ Y : Edge L n k j → ComplexMatrix2) (p : Face L n k j) :
    quotFaceTerm V (X₁ + X₂) Y p = quotFaceTerm V X₁ Y p + quotFaceTerm V X₂ Y p := by
  simp only [quotFaceTerm, quot_transportedForm_add, polarSecondExpr_add_left]
theorem quotFaceTerm_add_right (V X Y₁ Y₂ : Edge L n k j → ComplexMatrix2) (p : Face L n k j) :
    quotFaceTerm V X (Y₁ + Y₂) p = quotFaceTerm V X Y₁ p + quotFaceTerm V X Y₂ p := by
  simp only [quotFaceTerm, quot_transportedForm_add, polarSecondExpr_add_right]
theorem quotFaceTerm_smul_left (z : ℂ) (V X Y : Edge L n k j → ComplexMatrix2)
    (p : Face L n k j) : quotFaceTerm V (z • X) Y p = z * quotFaceTerm V X Y p := by
  simp only [quotFaceTerm, quot_transportedForm_smul, polarSecondExpr_smul_left]
theorem quotFaceTerm_smul_right (z : ℂ) (V X Y : Edge L n k j → ComplexMatrix2)
    (p : Face L n k j) : quotFaceTerm V X (z • Y) p = z * quotFaceTerm V X Y p := by
  simp only [quotFaceTerm, quot_transportedForm_smul, polarSecondExpr_smul_right]
theorem fullFaceTerm_add_left {a : ℝ} (V X₁ X₂ Y : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    fullFaceTerm V (X₁ + X₂) Y p = fullFaceTerm V X₁ Y p + fullFaceTerm V X₂ Y p := by
  simp only [fullFaceTerm, full_transportedForm_add, polarSecondExpr_add_left]
theorem fullFaceTerm_add_right {a : ℝ} (V X Y₁ Y₂ : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    fullFaceTerm V X (Y₁ + Y₂) p = fullFaceTerm V X Y₁ p + fullFaceTerm V X Y₂ p := by
  simp only [fullFaceTerm, full_transportedForm_add, polarSecondExpr_add_right]
theorem fullFaceTerm_smul_left {a : ℝ} (z : ℂ) (V X Y : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    fullFaceTerm V (z • X) Y p = z * fullFaceTerm V X Y p := by
  simp only [fullFaceTerm, full_transportedForm_smul, polarSecondExpr_smul_left]
theorem fullFaceTerm_smul_right {a : ℝ} (z : ℂ) (V X Y : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    fullFaceTerm V X (z • Y) p = z * fullFaceTerm V X Y p := by
  simp only [fullFaceTerm, full_transportedForm_smul, polarSecondExpr_smul_right]
def faceComponent (k j : ℕ) (h : j ≤ k) : Component k := ⟨j, h, .face, false, 1, one_pos⟩
def faceIndexSet (k j : ℕ) (h : j ≤ k) : WeightedIndexSet k :=
  WeightedIndexSet.ofComponent (faceComponent k j h)
def fullFaceEquiv (L k j : ℕ) (h : j ≤ k) : Idx L (faceIndexSet k j h) ≃ FullSpace.Face L k j where
  toFun ι := ι.2
  invFun p := ⟨(), p⟩
  left_inv ι := by rcases ι with ⟨⟨⟩, p⟩; rfl
  right_inv _ := rfl
abbrev FaceProjSurjective (L n k j : ℕ) : Prop :=
  Function.Surjective (Cell.proj n : Cell L k j .face → QuotientCell L n k j .face)
def quotFaceEquiv (h : j ≤ k) (hp : FaceProjSurjective L n k j) :
    (faceIndexSet k j h).ImageCarrier L n ≃ Face L n k j where
  toFun κ := κ.2.1
  invFun p := ⟨(), ⟨p, hp p⟩⟩
  left_inv κ := by rcases κ with ⟨⟨⟩, p, hq⟩; rfl
  right_inv _ := rfl
def fullFaceMap (h : j ≤ k) (U : FullSpace.Edge L k j → ComplexMatrix2)
    (f f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    Idx L (faceIndexSet k j h) → ℂ :=
  fun ι => fullFaceTerm U (fullForm h f) (fullForm h f') ι.2
def quotFaceValue (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (V : Edge L n k j → ComplexMatrix2)
    (f f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    (faceIndexSet k j h).ImageCarrier L n → ℂ :=
  fun κ => quotFaceTerm V (quotForm h hs f) (quotForm h hs f') κ.2.1
def quotFaceMap (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (V : Edge L n k j → ComplexMatrix2) :
    ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) →ₗ[ℂ]
      ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) →ₗ[ℂ]
        ((faceIndexSet k j h).ImageCarrier L n → ℂ) :=
  LinearMap.mk₂ ℂ (quotFaceValue h hs V)
    (fun f g f' => by
      funext κ
      show quotFaceTerm V (quotForm h hs (f + g)) _ _ =
        quotFaceTerm V _ _ _ + quotFaceTerm V _ _ _
      rw [quotForm_add]
      exact quotFaceTerm_add_left _ _ _ _ _)
    (fun z f f' => by
      funext κ
      show quotFaceTerm V (quotForm h hs (z • f)) _ _ = z * quotFaceTerm V _ _ _
      rw [quotForm_smul]
      exact quotFaceTerm_smul_left _ _ _ _ _)
    (fun f f' g' => by
      funext κ
      show quotFaceTerm V _ (quotForm h hs (f' + g')) _ =
        quotFaceTerm V _ _ _ + quotFaceTerm V _ _ _
      rw [quotForm_add]
      exact quotFaceTerm_add_right _ _ _ _ _)
    (fun z f f' => by
      funext κ
      show quotFaceTerm V _ (quotForm h hs (z • f')) _ = z * quotFaceTerm V _ _ _
      rw [quotForm_smul]
      exact quotFaceTerm_smul_right _ _ _ _ _)
theorem fullFaceTerm_congr {a : ℝ} {U X X' Y Y' : InfiniteLattice.Link a → ComplexMatrix2}
    {p : InfiniteLattice.ElementaryPlaquette a}
    (hX : ∀ i, X (FullSpace.faceEdge p i) = X' (FullSpace.faceEdge p i))
    (hY : ∀ i, Y (FullSpace.faceEdge p i) = Y' (FullSpace.faceEdge p i)) :
    fullFaceTerm U X Y p = fullFaceTerm U X' Y' p := by
  have e : ∀ {B B' : InfiniteLattice.Link a → ComplexMatrix2},
      (∀ i, B (FullSpace.faceEdge p i) = B' (FullSpace.faceEdge p i)) →
      FullSpace.transportedForm U B p = FullSpace.transportedForm U B' p := fun hB => by
    funext i
    simp only [FullSpace.transportedForm, hB i]
  rw [fullFaceTerm, fullFaceTerm, e hX, e hY]
theorem fullFaceMap_isLocalBilinear (h : j ≤ k) (ha : 0 ≤ meshAt L k j) (ha1 : meshAt L k j ≤ 1)
    (U : FullSpace.Edge L k j → ComplexMatrix2) :
    IsLocalBilinear ((CellClass.edgeClass k j h).colourPairs.toPeriodicData L)
      ((CellClass.edgeClass k j h).colourPairs.toPeriodicData L)
      ((faceIndexSet k j h).toPeriodicData L) 1 (fullFaceMap h U) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f g f' _ _ _
    funext ι
    show fullFaceTerm U (fullForm h (f + g)) _ _ = fullFaceTerm U _ _ _ + fullFaceTerm U _ _ _
    rw [fullForm_add]
    exact fullFaceTerm_add_left _ _ _ _ _
  · intro z f f' _ _
    funext ι
    show fullFaceTerm U (fullForm h (z • f)) _ _ = z * fullFaceTerm U _ _ _
    rw [fullForm_smul]
    exact fullFaceTerm_smul_left _ _ _ _ _
  · intro f f' g' _ _ _
    funext ι
    show fullFaceTerm U _ (fullForm h (f' + g')) _ = fullFaceTerm U _ _ _ + fullFaceTerm U _ _ _
    rw [fullForm_add]
    exact fullFaceTerm_add_right _ _ _ _ _
  · intro z f f' _ _
    funext ι
    show fullFaceTerm U _ (fullForm h (z • f')) _ = z * fullFaceTerm U _ _ _
    rw [fullForm_smul]
    exact fullFaceTerm_smul_right _ _ _ _ _
  · intro f g f' g' _ _ _ _ ι h₁ h₂
    let p : FullSpace.Face L k j := ι.2
    have hd : ∀ i,
        TorusMetric.supNormVec ((FullSpace.faceEdge p i).initial.1 - p.corner.1) ≤ 1 :=
      fun i => (full_faceEdge_near ha p i).trans ha1
    exact fullFaceTerm_congr (p := p)
      (fun i => fullForm_congr h ⟨_, full_faceEdge_isPositivelyOriented p i⟩ fun a =>
        h₁ ⟨(), (a, ⟨_, full_faceEdge_isPositivelyOriented p i⟩)⟩ (hd i))
      (fun i => fullForm_congr h ⟨_, full_faceEdge_isPositivelyOriented p i⟩ fun a =>
        h₂ ⟨(), (a, ⟨_, full_faceEdge_isPositivelyOriented p i⟩)⟩ (hd i))
theorem fullFaceMap_lift (ha : 0 < meshAt L k j)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (hB : ProjEdgesCompatible L n k j)
    (V : Edge L n k j → ComplexMatrix2)
    (f f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    fullFaceMap h (liftGaugeField L n k j V)
        ((CellClass.edgeClass k j h).colourPairs.lift L n f)
        ((CellClass.edgeClass k j h).colourPairs.lift L n f') =
      (faceIndexSet k j h).lift L n (quotFaceMap h hs V f f') := by
  funext ι
  show fullFaceTerm (liftGaugeField L n k j V)
      (fullForm h ((CellClass.edgeClass k j h).colourPairs.lift L n f))
      (fullForm h ((CellClass.edgeClass k j h).colourPairs.lift L n f')) ι.2 =
    quotFaceTerm V (quotForm h hs f) (quotForm h hs f') (FullSpace.projFace L n k j ι.2)
  rw [fullForm_lift ha hx h hs hB f, fullForm_lift ha hx h hs hB f']
  exact fullFaceTerm_lift hB V _ _ _
end Maps
section Entries
variable {L n k j : ℕ}
open Classical in
theorem wPairing_indicator {J : Type} (w : J → ℝ) (hw : ∀ i, w i = 1) (ι : J) {d : J → ℂ}
    (hd : ∀ i, d i = if i = ι then 1 else 0) (g : J → ℂ) :
    PeriodicOperators.wPairing w d g = g ι := by
  classical
  unfold PeriodicOperators.wPairing
  rw [tsum_eq_single ι fun i hi => by simp [hd i, hi]]
  simp [hw, hd]
open Classical in
theorem applyKernel_indicator {J J' : Type} (T : J' → J → ℂ) (ι : J) {d : J → ℂ}
    (hd : ∀ i, d i = if i = ι then 1 else 0) (i' : J') : applyKernel T d i' = T i' ι := by
  classical
  unfold applyKernel
  rw [tsum_eq_single ι fun i hi => by simp [hd i, hi]]
  simp [hd]
theorem pauliCoeff_pauliFamily (a a' : Fin 3) :
    pauliCoeff a' (ComplexMatrix2.pauliFamily a) = if a' = a then 1 else 0 := by
  have e := pauliCoeff_sum_smul (fun b => if b = a then (1 : ℂ) else 0) a'
  simpa [ite_smul] using e
open Classical in
theorem toPauliCoeffs_indicator {σ : Type} {X : σ → ComplexMatrix2} {a : Fin 3} {c : σ}
    (hc : X c = ComplexMatrix2.pauliFamily a) (ho : ∀ b, b ≠ c → X b = 0) (p : Fin 3 × σ) :
    toPauliCoeffs X p = if p = (a, c) then 1 else 0 := by
  classical
  rcases p with ⟨a', b⟩
  show pauliCoeff a' (X b) = _
  by_cases hb : b = c
  · subst hb
    rw [hc, pauliCoeff_pauliFamily]
    simp
  · rw [ho b hb, pauliCoeff_zero]
    simp [hb]
theorem link_opposite_pos_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
theorem full_extendOddly_pos (f : FullSpace.Edge L k j → ComplexMatrix2)
    (b : FullSpace.Edge L k j) (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem full_extendOddly_opposite
    (hiff : ∀ b : FullSpace.Edge L k j,
      b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (f : FullSpace.Edge L k j → ComplexMatrix2) (b : FullSpace.Edge L k j) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.HessianKernel.full_extendOddly_opposite <;> assumption
theorem quot_extendOddly_pos (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos hb
theorem quot_extendOddly_opposite
    (hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have h' : ¬ b.opposite.IsPositivelyOriented := fun h => (hiff b).1 h hb
    have e1 : extendOddly f b.opposite = -f b := if_neg h'
    have e2 : extendOddly f b = f b := if_pos hb
    rw [e1, e2]
  · have h' : b.opposite.IsPositivelyOriented := (hiff b).2 hb
    have e1 : extendOddly f b.opposite = f b.opposite := if_pos h'
    have e2 : extendOddly f b = -f b.opposite := if_neg hb
    rw [e1, e2, neg_neg]
theorem full_basisForm_mem
    (hiff : ∀ b : FullSpace.Edge L k j,
      b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k j)) :
    FullSpace.basisForm (L := L) (k := k) (j := j) a b ∈
      HessianKernel.finiteSupportComplexForms L k j := by apply _root_.YangMills.Construction.Tower.HessianKernel.full_basisForm_mem <;> assumption
theorem quot_basisForm_mem
    (hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (a : Fin 3) (b : Tower.PositiveEdge L n k j) :
    basisForm a b ∈ complexEdgeForms L n k j := by
  classical
  refine ⟨fun b' hb' => ?_, fun b' => quot_extendOddly_opposite hiff _ b'⟩
  have e : basisForm a b b' = if b' = b.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos hb'
  rw [e]
  split_ifs
  · exact pauliFamily_mem_traceless a
  · exact ComplexMatrix2.traceless.zero_mem
def fullKernel (h : j ≤ k) (U : FullSpace.Edge L k j → ComplexMatrix2) :
    KernelMatrix (Idx L (CellClass.edgeClass k j h).colourPairs)
      (Idx L (CellClass.edgeClass k j h).colourPairs) :=
  fun ι' ι => FullSpace.complexHessianKernel U (fullIdxEquiv L k j h ι') (fullIdxEquiv L k j h ι)
def quotKernel (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (V : Edge L n k j → ComplexMatrix2) :
    KernelMatrix ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)
      ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n) :=
  fun κ' κ => complexHessianKernel V (quotIdxEquiv h hs κ') (quotIdxEquiv h hs κ)
open Classical in
theorem coeffsOn_basisForm (h : j ≤ k) (ι ι' : Idx L (CellClass.edgeClass k j h).colourPairs) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h)
        (FullSpace.basisForm (fullIdxEquiv L k j h ι).1 (fullIdxEquiv L k j h ι).2) ι' =
      if ι' = ι then 1 else 0 := by
  classical
  have e := toPauliCoeffs_indicator (X := FullSpace.restrictToPositiveEdges
      (FullSpace.basisForm (L := L) (k := k) (j := j) (fullIdxEquiv L k j h ι).1
        (fullIdxEquiv L k j h ι).2)) (a := (fullIdxEquiv L k j h ι).1)
    (c := (fullIdxEquiv L k j h ι).2) ?_ ?_ (fullIdxEquiv L k j h ι')
  · refine e.trans ?_
    simp only [Prod.mk.eta, EmbeddingLike.apply_eq_iff_eq]
  · exact (if_pos (fullIdxEquiv L k j h ι).2.2).trans (if_pos rfl)
  · intro b hb
    refine (if_pos b.2).trans (if_neg fun h' => hb (Subtype.ext h'))
open Classical in
theorem quotCoeffsOn_basisForm (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (κ κ' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n) :
    CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h)
        (basisForm (quotIdxEquiv h hs κ).1 (quotIdxEquiv h hs κ).2) κ' =
      if κ' = κ then 1 else 0 := by
  classical
  have e := toPauliCoeffs_indicator (X := restrictToPositiveEdges (basisForm
      (quotIdxEquiv h hs κ).1 (quotIdxEquiv h hs κ).2)) (a := (quotIdxEquiv h hs κ).1)
    (c := (quotIdxEquiv h hs κ).2) ?_ ?_ (quotIdxEquiv h hs κ')
  · refine e.trans ?_
    simp only [Prod.mk.eta, EmbeddingLike.apply_eq_iff_eq]
  · exact (if_pos (quotIdxEquiv h hs κ).2.2).trans (if_pos rfl)
  · intro b hb
    refine (if_pos b.2).trans (if_neg fun h' => hb (Subtype.ext h'))
theorem fullKernel_unique (hD : FaceTermDerivatives.HoldsOnFullSpaceLevel L k j)
    (hK : HessianKernel.HoldsOnFullSpace L k j)
    (hS : FacesContainingEdge.OnFullSpace L k j) (ha : 0 < meshAt L k j) (h : j ≤ k)
    {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {T : KernelMatrix (Idx L (CellClass.edgeClass k j h).colourPairs)
      (Idx L (CellClass.edgeClass k j h).colourPairs)}
    (hT : IsBilinearKernel L n (CellClass.edgeClass k j h).colourPairs
      (CellClass.edgeClass k j h).colourPairs (faceIndexSet k j h) (fullFaceMap h U)
      (fun _ => 1) T) :
    T = fullKernel h U := by
  have hiff := link_opposite_pos_iff (a := meshAt L k j) ha
  funext ι ι'
  set E := FullSpace.basisForm (L := L) (k := k) (j := j) (fullIdxEquiv L k j h ι).1
    (fullIdxEquiv L k j h ι).2 with hE
  set E' := FullSpace.basisForm (L := L) (k := k) (j := j) (fullIdxEquiv L k j h ι').1
    (fullIdxEquiv L k j h ι').2 with hE'
  have mE : E ∈ HessianKernel.finiteSupportComplexForms L k j := full_basisForm_mem hiff _ _
  have mE' : E' ∈ HessianKernel.finiteSupportComplexForms L k j := full_basisForm_mem hiff _ _
  have fin : ∀ {B : FullSpace.Edge L k j → ComplexMatrix2}, FullSpace.HasFiniteEdgeSupport B →
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B) := fun hB =>
    (Set.Finite.preimage Subtype.val_injective.injOn hB).subset fun b hb => ⟨b.2, hb⟩
  have key := hT _ _ (coeffsOn_hasFiniteSupport h (fin mE.2))
    (coeffsOn_hasFiniteSupport h (fin mE'.2))
  have l : weightedBracket L (CellClass.edgeClass k j h).colourPairs
      (CellClass.coeffsOn L (CellClass.edgeClass k j h) E)
      (applyKernel T (CellClass.coeffsOn L (CellClass.edgeClass k j h) E')) = T ι ι' := by
    refine (wPairing_indicator _ (fun _ => rfl) ι (coeffsOn_basisForm h ι) _).trans ?_
    exact applyKernel_indicator T ι' (coeffsOn_basisForm h ι') ι
  obtain ⟨Ω, hΩ, hout⟩ := full_faces_finite_of_forms hS mE.2 mE'.2
  have hsup : (Function.support fun p => fullFaceTerm U E E' p).Finite :=
    hΩ.subset fun p hp => by
      by_contra hn
      exact hp (fullFaceTerm_eq_zero fun i => (hout p hn i).2)
  have r : weightedBracket L (faceIndexSet k j h) ((faceIndexSet k j h).lift L n fun _ => 1)
      (fullFaceMap h U (CellClass.coeffsOn L (CellClass.edgeClass k j h) E)
        (CellClass.coeffsOn L (CellClass.edgeClass k j h) E')) =
      ∑ᶠ p, fullFaceTerm U E E' p := by
    have e₁ : (fun i : Idx L (faceIndexSet k j h) =>
        ((((faceIndexSet k j h).toPeriodicData L).weightOf i : ℝ) : ℂ) *
          ((faceIndexSet k j h).lift L n (fun _ => (1 : ℂ)) i *
            fullFaceMap h U (CellClass.coeffsOn L (CellClass.edgeClass k j h) E)
              (CellClass.coeffsOn L (CellClass.edgeClass k j h) E') i)) =
        fun i => fullFaceTerm U E E' (fullFaceEquiv L k j h i) := by
      funext i
      show (((1 : ℝ) : ℂ)) * ((1 : ℂ) * fullFaceTerm U
        (fullForm h (CellClass.coeffsOn L (CellClass.edgeClass k j h) E))
        (fullForm h (CellClass.coeffsOn L (CellClass.edgeClass k j h) E')) i.2) = _
      rw [fullForm_coeffsOn ha h mE.1, fullForm_coeffsOn ha h mE'.1]
      rw [Complex.ofReal_one, one_mul, one_mul]
      rfl
    refine (congrArg tsum e₁).trans ?_
    rw [(fullFaceEquiv L k j h).tsum_eq fun p => fullFaceTerm U E E' p]
    exact tsum_eq_finsum hsup
  rw [← l, key, r, ← full_hessian_eq_finsum hD hK hS hU mE mE']
  rfl
theorem quotKernel_unique [Finite (Face L n k j)]
    (hD : FaceTermDerivatives.HoldsOnPeriodicLevel L n k j)
    (hK : HessianKernel.HoldsOnTorus L n k j)
    (hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (hp : FaceProjSurjective L n k j)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    {M : KernelMatrix ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)
      ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)}
    (hM : IsBilinearMatrix L n (CellClass.edgeClass k j h).colourPairs
      (CellClass.edgeClass k j h).colourPairs (faceIndexSet k j h) (quotFaceMap h hs V)
      (fun _ => 1) M) :
    M = quotKernel h hs V := by
  funext κ κ'
  set E := basisForm (quotIdxEquiv h hs κ).1 (quotIdxEquiv h hs κ).2 with hE
  set E' := basisForm (quotIdxEquiv h hs κ').1 (quotIdxEquiv h hs κ').2 with hE'
  have mE : E ∈ complexEdgeForms L n k j := quot_basisForm_mem hiff _ _
  have mE' : E' ∈ complexEdgeForms L n k j := quot_basisForm_mem hiff _ _
  have key := hM (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E)
    (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E')
  have l : quotBracket L n (CellClass.edgeClass k j h).colourPairs
      (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E)
      (applyKernel M (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E')) = M κ κ' := by
    refine (wPairing_indicator _ (fun _ => rfl) κ (quotCoeffsOn_basisForm h hs κ) _).trans ?_
    exact applyKernel_indicator M κ' (quotCoeffsOn_basisForm h hs κ') κ
  have r : quotBracket L n (faceIndexSet k j h) (fun _ => 1)
      (quotFaceMap h hs V (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E)
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E')) =
      ∑ᶠ p, quotFaceTerm V E E' p := by
    have e₁ : (fun i : (faceIndexSet k j h).ImageCarrier L n =>
        (((faceIndexSet k j h).imageWeight L n i : ℝ) : ℂ) * ((1 : ℂ) *
          quotFaceMap h hs V (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E)
            (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E') i)) =
        fun i => quotFaceTerm V E E' (quotFaceEquiv h hp i) := by
      funext i
      show (((1 : ℝ) : ℂ)) * ((1 : ℂ) * quotFaceTerm V
        (quotForm h hs (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E))
        (quotForm h hs (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) E')) i.2.1) = _
      rw [quotForm_quotCoeffsOn hx h hs mE, quotForm_quotCoeffsOn hx h hs mE']
      rw [Complex.ofReal_one, one_mul, one_mul]
      rfl
    refine (congrArg tsum e₁).trans ?_
    rw [(quotFaceEquiv h hp).tsum_eq fun p => quotFaceTerm V E E' p]
    exact tsum_eq_finsum (Set.toFinite _)
  rw [← l, key, r, ← quot_hessian_eq_finsum hD hK hV mE mE']
  rfl
end Entries
section Operators
variable {L n k j : ℕ}
theorem applyKernel_reindex {J J' : Type} (e : J ≃ J') (K : J' → J' → ℂ) (g : J' → ℂ) (ι : J) :
    applyKernel (fun ι' ι => K (e ι') (e ι)) (fun i => g (e i)) ι = applyKernel K g (e ι) :=
  e.tsum_eq fun c => K (e ι) c * g c
theorem applyKernel_add {J J' : Type} {T : J' → J → ℂ} (hrow : ∀ i', {i | T i' i ≠ 0}.Finite)
    (u v : J → ℂ) : applyKernel T (u + v) = applyKernel T u + applyKernel T v := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_add <;> assumption
theorem applyKernel_smul {J J' : Type} (T : J' → J → ℂ) (z : ℂ) (u : J → ℂ) :
    applyKernel T (z • u) = z • applyKernel T u := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_smul <;> assumption
theorem full_restrict_hessianOperator (U B : FullSpace.Edge L k j → ComplexMatrix2) :
    FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U B) =
      ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U)
        (toPauliCoeffs (FullSpace.restrictToPositiveEdges B))) := by
  funext b
  change FullSpace.complexHessianOperator U B b.1 = _
  rw [FullSpace.complexHessianOperator, full_extendOddly_pos _ _ b.2]
  exact dif_pos b.2
theorem quot_restrict_hessianOperator (U B : Edge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (complexHessianOperator U B) =
      ofPauliCoeffs (applyKernel (complexHessianKernel U)
        (toPauliCoeffs (restrictToPositiveEdges B))) := by
  funext b
  change complexHessianOperator U B b.1 = _
  rw [complexHessianOperator, quot_extendOddly_pos _ _ b.2]
  exact dif_pos b.2
theorem full_hessianOperator_mem
    (hiff : ∀ b : FullSpace.Edge L k j,
      b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (U B : FullSpace.Edge L k j → ComplexMatrix2) :
    FullSpace.complexHessianOperator U B ∈ FullSpace.complexEdgeForms (meshAt L k j) := by
  refine ⟨fun b hb => ?_, fun b => full_extendOddly_opposite hiff _ b⟩
  have e := congrFun (full_restrict_hessianOperator U B) ⟨b, hb⟩
  change FullSpace.complexHessianOperator U B b = _ at e
  rw [e]
  exact sum_smul_pauli_mem_traceless _
theorem quot_hessianOperator_mem
    (hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (U B : Edge L n k j → ComplexMatrix2) :
    complexHessianOperator U B ∈ complexEdgeForms L n k j := by
  refine ⟨fun b hb => ?_, fun b => quot_extendOddly_opposite hiff _ b⟩
  have e := congrFun (quot_restrict_hessianOperator U B) ⟨b, hb⟩
  change complexHessianOperator U B b = _ at e
  rw [e]
  exact sum_smul_pauli_mem_traceless _
theorem coeffsOn_hessianOperator (h : j ≤ k) (U B : FullSpace.Edge L k j → ComplexMatrix2) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h) (FullSpace.complexHessianOperator U B) =
      applyKernel (fullKernel h U) (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) := by
  funext ι
  show toPauliCoeffs (FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U B))
      (fullIdxEquiv L k j h ι) = _
  rw [full_restrict_hessianOperator, toPauliCoeffs_ofPauliCoeffs]
  exact (applyKernel_reindex (fullIdxEquiv L k j h) _ _ ι).symm
theorem quotCoeffsOn_hessianOperator (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (U B : Edge L n k j → ComplexMatrix2) :
    CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) (complexHessianOperator U B) =
      applyKernel (quotKernel h hs U)
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B) := by
  funext κ
  show toPauliCoeffs (restrictToPositiveEdges (complexHessianOperator U B))
      (quotIdxEquiv h hs κ) = _
  rw [quot_restrict_hessianOperator, toPauliCoeffs_ofPauliCoeffs]
  exact (applyKernel_reindex (quotIdxEquiv h hs) _ _ κ).symm
theorem coeffsOn_add (h : j ≤ k) {B B' : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h) (B + B') =
      CellClass.coeffsOn L (CellClass.edgeClass k j h) B +
        CellClass.coeffsOn L (CellClass.edgeClass k j h) B' := by
  funext ι
  exact toPauliCoeffs_add (X := FullSpace.restrictToPositiveEdges B)
    (Y := FullSpace.restrictToPositiveEdges B')
    (fun b => hB.1 _ b.2) (fun b => hB'.1 _ b.2) (fullIdxEquiv L k j h ι)
theorem coeffsOn_smul (h : j ≤ k) (z : ℂ) {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h) (z • B) =
      z • CellClass.coeffsOn L (CellClass.edgeClass k j h) B := by
  funext ι
  exact toPauliCoeffs_smul (X := FullSpace.restrictToPositiveEdges B) z (fun b => hB.1 _ b.2)
    (fullIdxEquiv L k j h ι)
theorem quotCoeffsOn_add (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) :
    CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) (B + B') =
      CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B +
        CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B' := by
  funext κ
  exact toPauliCoeffs_add (X := restrictToPositiveEdges B) (Y := restrictToPositiveEdges B')
    (fun b => hB.1 _ b.2) (fun b => hB'.1 _ b.2) (quotIdxEquiv h hs κ)
theorem quotCoeffsOn_smul (h : j ≤ k) (hs : EdgeProjSurjective L n k j) (z : ℂ)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) (z • B) =
      z • CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B := by
  funext κ
  exact toPauliCoeffs_smul (X := restrictToPositiveEdges B) z (fun b => hB.1 _ b.2)
    (quotIdxEquiv h hs κ)
theorem fullKernel_rowFinite (h : j ≤ k) {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hr : HessianKernel.RowFinite (FullSpace.complexHessianKernel U))
    (ι : Idx L (CellClass.edgeClass k j h).colourPairs) :
    {ι' | fullKernel h U ι ι' ≠ 0}.Finite :=
  Set.Finite.preimage (fullIdxEquiv L k j h).injective.injOn (hr (fullIdxEquiv L k j h ι))
theorem quotKernel_rowFinite (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    {U : Edge L n k j → ComplexMatrix2}
    (hr : HessianKernel.RowFinite (complexHessianKernel U))
    (κ : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n) :
    {κ' | quotKernel h hs U κ κ' ≠ 0}.Finite :=
  Set.Finite.preimage (quotIdxEquiv h hs).injective.injOn (hr (quotIdxEquiv h hs κ))
theorem full_hessianOperator_add (ha : 0 < meshAt L k j) (h : j ≤ k)
    (hiff : ∀ b : FullSpace.Edge L k j,
      b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hr : HessianKernel.RowFinite (FullSpace.complexHessianKernel U))
    {f g : FullSpace.Edge L k j → ComplexMatrix2}
    (hf : f ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hg : g ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    FullSpace.complexHessianOperator U (f + g) =
      FullSpace.complexHessianOperator U f + FullSpace.complexHessianOperator U g := by
  have m₁ := full_hessianOperator_mem hiff U f
  have m₂ := full_hessianOperator_mem hiff U g
  rw [← fullForm_coeffsOn ha h (full_hessianOperator_mem hiff U (f + g)),
    ← fullForm_coeffsOn ha h ((FullSpace.complexEdgeForms _).add_mem m₁ m₂)]
  congr 1
  rw [coeffsOn_add h m₁ m₂, coeffsOn_hessianOperator, coeffsOn_hessianOperator,
    coeffsOn_hessianOperator, coeffsOn_add h hf hg, applyKernel_add (fullKernel_rowFinite h hr)]
theorem full_hessianOperator_smul (ha : 0 < meshAt L k j) (h : j ≤ k)
    (hiff : ∀ b : FullSpace.Edge L k j,
      b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (U : FullSpace.Edge L k j → ComplexMatrix2) (z : ℂ) {f : FullSpace.Edge L k j → ComplexMatrix2}
    (hf : f ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    FullSpace.complexHessianOperator U (z • f) = z • FullSpace.complexHessianOperator U f := by
  have m₁ := full_hessianOperator_mem hiff U f
  rw [← fullForm_coeffsOn ha h (full_hessianOperator_mem hiff U (z • f)),
    ← fullForm_coeffsOn ha h ((FullSpace.complexEdgeForms _).smul_mem z m₁)]
  congr 1
  rw [coeffsOn_smul h z m₁, coeffsOn_hessianOperator, coeffsOn_hessianOperator,
    coeffsOn_smul h z hf, applyKernel_smul]
theorem quot_hessianOperator_add
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    {U : Edge L n k j → ComplexMatrix2}
    (hr : HessianKernel.RowFinite (complexHessianKernel U))
    {f g : Edge L n k j → ComplexMatrix2} (hf : f ∈ complexEdgeForms L n k j)
    (hg : g ∈ complexEdgeForms L n k j) :
    complexHessianOperator U (f + g) = complexHessianOperator U f + complexHessianOperator U g := by
  have m₁ := quot_hessianOperator_mem hiff U f
  have m₂ := quot_hessianOperator_mem hiff U g
  rw [← quotForm_quotCoeffsOn hx h hs (quot_hessianOperator_mem hiff U (f + g)),
    ← quotForm_quotCoeffsOn hx h hs ((complexEdgeForms L n k j).add_mem m₁ m₂)]
  congr 1
  rw [quotCoeffsOn_add h hs m₁ m₂, quotCoeffsOn_hessianOperator h hs,
    quotCoeffsOn_hessianOperator h hs, quotCoeffsOn_hessianOperator h hs,
    quotCoeffsOn_add h hs hf hg, applyKernel_add (quotKernel_rowFinite h hs hr)]
theorem quot_hessianOperator_smul
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (U : Edge L n k j → ComplexMatrix2) (z : ℂ) {f : Edge L n k j → ComplexMatrix2}
    (hf : f ∈ complexEdgeForms L n k j) :
    complexHessianOperator U (z • f) = z • complexHessianOperator U f := by
  have m₁ := quot_hessianOperator_mem hiff U f
  rw [← quotForm_quotCoeffsOn hx h hs (quot_hessianOperator_mem hiff U (z • f)),
    ← quotForm_quotCoeffsOn hx h hs ((complexEdgeForms L n k j).smul_mem z m₁)]
  congr 1
  rw [quotCoeffsOn_smul h hs z m₁, quotCoeffsOn_hessianOperator h hs,
    quotCoeffsOn_hessianOperator h hs, quotCoeffsOn_smul h hs z hf, applyKernel_smul]
theorem full_hessianOperator_local (h : j ≤ k) {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hloc : IsRLocal L (CellClass.edgeClass k j h).colourPairs
      (CellClass.edgeClass k j h).colourPairs 2 (fullKernel h U))
    {f g : FullSpace.Edge L k j → ComplexMatrix2} (c' : PeriodicOperators.PosEdge L k j)
    (hc : ∀ c : PeriodicOperators.PosEdge L k j,
      TorusMetric.supNormVec (c.1.initial.1 - c'.1.initial.1) ≤ 2 →
        FullSpace.restrictToPositiveEdges f c = FullSpace.restrictToPositiveEdges g c) :
    FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U f) c' =
      FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U g) c' := by
  rw [full_restrict_hessianOperator, full_restrict_hessianOperator]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine tsum_congr fun ι => ?_
  by_cases hd : TorusMetric.supNormVec (ι.2.1.initial.1 - c'.1.initial.1) ≤ 2
  · show _ * pauliCoeff ι.1 (FullSpace.restrictToPositiveEdges f ι.2) =
      _ * pauliCoeff ι.1 (FullSpace.restrictToPositiveEdges g ι.2)
    rw [hc ι.2 hd]
  · have h0 : FullSpace.complexHessianKernel U (a, c') ι = 0 :=
      hloc ⟨(), (a, c')⟩ ⟨(), ι⟩ hd
    rw [h0, zero_mul, zero_mul]
theorem full_hessianOperator_lift (h : j ≤ k) (hs : EdgeProjSurjective L n k j)
    (hB : ProjEdgesCompatible L n k j)
    {U : FullSpace.Edge L k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hdesc : KernelDescends L n (CellClass.edgeClass k j h).colourPairs
      (CellClass.edgeClass k j h).colourPairs (fullKernel h U) (quotKernel h hs V))
    (f : Edge L n k j → ComplexMatrix2) (c' : PeriodicOperators.PosEdge L k j) :
    FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U
        (liftGaugeField L n k j f)) c' =
      restrictToPositiveEdges (complexHessianOperator V f) (projPositiveEdge L n k j c') := by
  rw [full_restrict_hessianOperator, quot_restrict_hessianOperator]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hread : CellClass.coeffsOn L (CellClass.edgeClass k j h) (liftGaugeField L n k j f) =
      (CellClass.edgeClass k j h).colourPairs.lift L n
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) f) := by
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (f (FullSpace.projEdge L n k j c.1)) =
      pauliCoeff a (f (projPositiveEdge L n k j c).1)
    rw [hB.2.1 c]
  have d := congrFun (hdesc.2 (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) f))
    ⟨(), (a, c')⟩
  rw [← hread] at d
  have l := applyKernel_reindex (fullIdxEquiv L k j h) (FullSpace.complexHessianKernel U)
    (toPauliCoeffs (FullSpace.restrictToPositiveEdges (liftGaugeField L n k j f)))
    ⟨(), (a, c')⟩
  have r := applyKernel_reindex (quotIdxEquiv h hs) (complexHessianKernel V)
    (toPauliCoeffs (restrictToPositiveEdges f))
    ((CellClass.edgeClass k j h).colourPairs.proj L n ⟨(), (a, c')⟩)
  exact l.symm.trans (d.trans r)
end Operators
theorem hessianDescendsAtLifts_holds (hBil : LocalBilinearKernels.Claim)
    (hLin : LocalLinearMapsPeriodize)
    (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hK : HessianKernel.KernelProperties)
    (hD : FaceTermDerivatives.Statement)
    (hS : FacesContainingEdge.Holds)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hE : LiftIsGaugeField) : HessianDescendsAtLifts := by
  intro L hL k n hn j h V hV
  have hCl := hCells L hL k n hn
  have hc := hCl.1 j h
  have hs : EdgeProjSurjective L n k j := (hc.1 .edge).1
  have hp : FaceProjSurjective L n k j := (hc.1 .face).1
  have : Finite (Face L n k j) := by
    have := (hCl.2 (faceIndexSet k j h)).1
    exact Finite.of_equiv _ (quotFaceEquiv h hp)
  have hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented :=
    fun b => ⟨fun h' h'' => edge_not_both_pos hA hL hn h b h'' h',
      fun h' => (edge_pos_or_opposite_pos b).resolve_left h'⟩
  have hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => by
      by_cases hb : b.IsPositivelyOriented
      · exact Or.inl ⟨hb, fun h' => (hiff b).1 h' hb⟩
      · exact Or.inr ⟨(hiff b).2 hb, hb⟩
  have hL0 : (1 : ℝ) ≤ (L : ℝ) := by
    have : 1 ≤ L := by
      have := hL.2
      omega
    exact_mod_cast this
  have ha : 0 < meshAt L k j := zpow_pos (by linarith) _
  have ha1 : meshAt L k j ≤ 1 := zpow_le_one_of_nonpos₀ hL0 (by omega)
  have hwiff := link_opposite_pos_iff (a := meshAt L k j) ha
  have hside : 4 < periodSide L n := by
    have h₁ : L ≤ L ^ n := Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hn) L
    have := hL.2
    unfold periodSide
    omega
  have hside' : (4 : ℝ) < (periodSide L n : ℝ) := by exact_mod_cast hside
  obtain ⟨hKs, hKw⟩ := hK L hL k j h
  obtain ⟨hDs, hDw⟩ := hD L hL k j h
  obtain ⟨-, hSw⟩ := hS L hL k j h
  have hW : liftGaugeField L n k j V ∈
      FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    (hE L n k j hL hn h V).2 hV
  obtain ⟨-, ⟨T, hT, -⟩, ⟨M, hM, -⟩, hall⟩ := hBil L hL k n hn
    (CellClass.edgeClass k j h).colourPairs (CellClass.edgeClass k j h).colourPairs
    (faceIndexSet k j h) 1 zero_le_one (by linarith) _ (quotFaceMap h hs V) (fun _ => 1)
    (fullFaceMap_isLocalBilinear h ha.le ha1 _) (fullFaceMap_lift ha hx h hs hc.2 V)
  obtain ⟨hT2, hdesc, -⟩ := hall T M hT hM
  have eT := fullKernel_unique hDw hKw hSw ha h hW hT
  have eM := quotKernel_unique (hDs n hn) (hKs n hn) hiff hx h hs hp hV hM
  rw [mul_one] at hT2
  subst eT
  subst eM
  have hrw := (hKw _ hW).2.2.1
  have hrt := ((hKs n hn) V hV).2.2.1
  refine hLin L hL k n hn (CellClass.edgeClass k j h) (CellClass.edgeClass k j h) nofun nofun 2
    (by norm_num) (by linarith) _ _ ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun f _ => full_hessianOperator_mem hwiff _ f
  · exact fun f hf g hg => full_hessianOperator_add ha h hwiff hrw hf hg
  · exact fun z f hf => full_hessianOperator_smul ha h hwiff _ z hf
  · exact fun f _ g _ c' hc' => full_hessianOperator_local h hT2 c' hc'
  · exact fun f _ => quot_hessianOperator_mem hiff _ f
  · exact fun f hf g hg => quot_hessianOperator_add hx h hs hiff hrt hf hg
  · exact fun z f hf => quot_hessianOperator_smul hx h hs hiff _ z hf
  · exact fun f _ c' => full_hessianOperator_lift h hs hc.2 hdesc f c'
end YangMills.Construction.LocalKernels.HessianAtLifts
end
