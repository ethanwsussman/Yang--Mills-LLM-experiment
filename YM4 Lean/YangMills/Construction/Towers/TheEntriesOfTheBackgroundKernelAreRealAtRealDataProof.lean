import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLatticeProof
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminants
import YangMills.Construction.Towers.TheEntriesOfTheBackgroundKernelAreRealAtRealData
import YangMills.Construction.Towers.TheIteratedMapsKeepRealFunctions
import YangMills.Construction.Towers.TheSecondOrderTermIsRealAtRealConfigurations
import YangMills.Construction.Towers.TheThreeKernelsAreRealAtRealConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RealBackgroundKernel
open FieldValueFunctions (hessianBilinear sourceBilinear rawHessianKernel)
theorem halfTrace_mul_im {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (hY : Y ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (Matrices.ComplexMatrix2.halfTrace (X * Y)).im = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.halfTrace_mul_im <;> assumption
theorem smul_I_half_lie_mem {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (hY : Y ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (Complex.I / 2) • ⁅X, Y⁆ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.halfI_smul_bracket_mem <;> assumption
theorem pauliFamily_mem (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem traceFinsumPairing_im {ι : Type*} {f f' : ι → Matrices.ComplexMatrix2}
    (h : ∀ i, f i ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (h' : ∀ i, f' i ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (traceFinsumPairing f f').im = 0 := by
  unfold traceFinsumPairing
  exact finsum_induction (fun z : ℂ => z.im = 0) (by simp)
    (fun x y hx hy => by simp [hx, hy]) fun i => halfTrace_mul_im (h i) (h' i)
theorem edgeFormPairing_im {a : ℝ} {B B' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a) (hB' : B' ∈ edgeFormSpace a) :
    (finiteEdgePairing B B').im = 0 :=
  traceFinsumPairing_im (fun e => hB.1 e.1 e.2) fun e => hB'.1 e.1 e.2
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem opposite_isPositivelyOriented_of_not {a : ℝ} {e : InfiniteLattice.Link a}
    (he : ¬ e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem opposite_opposite {a : ℝ} (e : InfiniteLattice.Link a) : e.opposite.opposite = e := rfl
theorem extendOddly_mem {a : ℝ} (ha : 0 < a)
    {f : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hf : ∀ e : InfiniteLattice.Link a, e.IsPositivelyOriented →
      f e ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace a := by
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · simpa [extendOddly, he] using hf e he
  · by_cases he : e.IsPositivelyOriented
    · have hr := InfiniteLattice.Link.opposite_not_isPositivelyOriented ha he
      simp [extendOddly, he, hr, opposite_opposite]
    · have hr := opposite_isPositivelyOriented_of_not he
      simp [extendOddly, he, hr]
theorem covDiff_mem {a : ℝ} (ha : 0 < a) {V : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hV : IsFieldIn PeriodicLattice.compactGaugeGroup V)
    {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace a) : covDiff V l ∈ edgeFormSpace a :=
  extendOddly_mem ha fun e _ =>
    Matrices.ComplexMatrix2.hermitianTraceless.sub_mem
      (Matrices.ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hV.1 e) _
        (hl _ (mem_univ _))) (hl _ (mem_univ _))
theorem levelBracketTerm_mem {a : ℝ} (ha : 0 < a)
    {V : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hV : IsFieldIn PeriodicLattice.compactGaugeGroup V)
    {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace a) {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a) :
    levelBracketTerm V l B ∈ edgeFormSpace a :=
  extendOddly_mem ha fun e he => smul_I_half_lie_mem
    (Matrices.ComplexMatrix2.hermitianTraceless.add_mem (hl _ (mem_univ _))
      (Matrices.ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hV.1 e) _
        (hl _ (mem_univ _))))
    (hB.1 e he)
theorem basisForm_mem {L k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (a : Fin 3)
    (e : PositiveEdge (meshAt L k j)) :
    basisForm a e ∈ edgeFormSpace (meshAt L k j) := by
  unfold basisForm
  refine extendOddly_mem (meshAt_pos hL k j) fun e' _ => ?_
  split_ifs
  · exact pauliFamily_mem a
  · exact Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
theorem basisForm_hasFiniteEdgeSupport {L k j : ℕ} (a : Fin 3)
    (e : PositiveEdge (meshAt L k j)) :
    HasFiniteEdgeSupport (basisForm a e) := by apply _root_.YangMills.Construction.Tower.IdentityOperators.basisForm_hasFiniteEdgeSupport <;> assumption
theorem rawHessianKernelReal_holds (hIter : IteratesPreserveRealFields.Holds)
    (hKer : KernelsRealAtGroupFields)
    (hSec : QuadraticTermHermitianAtRealFields)
    (hAct : HessianDeterminants.HessianSymmAndDetsPositive) : RawHessianKernelReal := by
  intro L hL k hk U hU hUr J hJ μ hμ ι' ι
  have hs := meshAt_pos hL k 0
  have hV : IsFieldIn PeriodicLattice.compactGaugeGroup U := hUr
  obtain ⟨-, hI⟩ := hIter L hL k hk
  obtain ⟨-, -, hAvg, hBack⟩ := hI U hU hUr
  obtain ⟨-, -, -, hT1, hT2⟩ := hKer L hL k hk U hU hUr
  have hreal := ((hAct L hL).1 k 0 (Nat.zero_le k)).2.2
  have hG : ∀ B ∈ edgeFormSpace (meshAt L k 0),
      gaugeFixingTerm L k U B ∈ vertexFunctionSpace (meshAt L k 0) := fun B hB =>
    Submodule.sub_mem _ (hT1 B hB) (Submodule.smul_mem _ _
      (hT2 _ (hAvg k le_rfl _ (hT1 B hB))))
  set B := basisForm ι'.1 ι'.2 with hBdef
  set B' := basisForm ι.1 ι.2 with hB'def
  have hB : B ∈ edgeFormSpace (meshAt L k 0) := basisForm_mem hL _ _
  have hB' : B' ∈ edgeFormSpace (meshAt L k 0) := basisForm_mem hL _ _
  have hσ := (hBack B hB).1
  have hσ' := (hBack B' hB').1
  have hτ := (hBack B hB).2
  have hτ' := (hBack B' hB').2
  have e1 : (complexActionHessian U B B').im = 0 :=
    hreal U hUr B hB (basisForm_hasFiniteEdgeSupport _ _) B' hB'
      (basisForm_hasFiniteEdgeSupport _ _)
  have e2 : (traceFinsumPairing (gaugeFixingTerm L k U B) (gaugeFixingTerm L k U B')).im = 0 :=
    traceFinsumPairing_im (fun x => hG B hB x (mem_univ _)) fun x => hG B' hB' x (mem_univ _)
  have e3 : (finiteEdgePairing J (levelBracketTerm U (gaugeParam U B) B')).im = 0 :=
    edgeFormPairing_im hJ (levelBracketTerm_mem hs hV hσ hB')
  have e4 : (finiteEdgePairing J (levelBracketTerm U (gaugeParam U B)
      (covDiff U (gaugeParam U B')))).im = 0 :=
    edgeFormPairing_im hJ (levelBracketTerm_mem hs hV hσ (covDiff_mem hs hV hσ'))
  have e5 : (traceFinsumPairing (restrictToPositiveEdges μ)
      (AsDifferentials.complexQuadraticTerm L k U (shiftedForm U B) (shiftedForm U B'))).im = 0 :=
    traceFinsumPairing_im (fun c => hμ.1 c.1 c.2) fun c => hSec L hL k hk U hU hUr _ hτ _ hτ' c
  change (hessianBilinear U J μ B B').im = 0
  simp only [hessianBilinear, sourceBilinear, backgroundForm,
    Complex.add_im, Complex.sub_im, Complex.mul_im, e1, e2, e3, e4, e5]
  simp
end YangMills.Construction.Tower.FullSpace.RealBackgroundKernel
end
