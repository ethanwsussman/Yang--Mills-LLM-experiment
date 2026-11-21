import YangMills.Construction.OneLoop.PauliMatrixComputations
import YangMills.Construction.Towers.BracketsAndTransposesOnThePairsProof
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.DifferentialOfTheCompositeOfTheCriticalBranchProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernels
import YangMills.Construction.Towers.TheDifferencesOfFormsReadAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FormCoboundariesAtInfinity
open Matrices
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators (KernelMatrix RowFinite applyKernel compKernel colourEdges
  colourVertices colourFaces)
section Generic
variable {L n k : ℕ}
abbrev FullPair (L : ℕ) {k : ℕ} (A : CellClass k) : Type :=
  Fin 3 × Cell L k A.level A.cellType
abbrev QuotPair (L n : ℕ) {k : ℕ} (A : CellClass k) : Type :=
  Fin 3 × QuotientCell L n k A.level A.cellType
def projPair (n : ℕ) {k : ℕ} (A : CellClass k) (x : FullPair L A) : QuotPair L n A :=
  (x.1, Cell.proj n x.2)
def colourPairEquiv (L : ℕ) {k : ℕ} (A : CellClass k) : Idx L A.colourPairs ≃ FullPair L A where
  toFun ι := ι.2
  invFun x := ⟨(), x⟩
  left_inv _ := rfl
  right_inv _ := rfl
def liftKernel (A A' : CellClass k) (W : KernelMatrix (FullPair L A) (FullPair L A')) :
    KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs) :=
  fun ι' ι => W (colourPairEquiv L A' ι') (colourPairEquiv L A ι)
theorem applyKernel_liftKernel (A A' : CellClass k)
    (W : KernelMatrix (FullPair L A) (FullPair L A'))
    (g : FullPair L A → ℂ) (ι' : Idx L A'.colourPairs) :
    applyKernel (liftKernel A A' W) (g ∘ colourPairEquiv L A) ι' =
      applyKernel W g (colourPairEquiv L A' ι') :=
  (colourPairEquiv L A).tsum_eq fun x => W (colourPairEquiv L A' ι') x * g x
def imageCarrierEquiv (A : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)) :
    A.colourPairs.ImageCarrier L n ≃ QuotPair L n A where
  toFun c := c.2.1
  invFun x := ⟨(), ⟨x, by
    obtain ⟨b, hb⟩ := hs x.2
    exact ⟨(x.1, b), Prod.ext rfl hb⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem imageCarrierEquiv_proj (A : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (ι : Idx L A.colourPairs) :
    imageCarrierEquiv A hs (A.colourPairs.proj L n ι) = projPair n A (colourPairEquiv L A ι) :=
  rfl
theorem transpose_applyKernel_comp_projPair (hS : DescendsAlgebra (k := k) L n)
    (A A' : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (hs' : Function.Surjective
      (Cell.proj n : Cell L k A'.level A'.cellType → QuotientCell L n k A'.level A'.cellType))
    (R : ℝ) (hR : 0 ≤ R) (h2R : 2 * R < (periodSide L n : ℝ))
    (W : KernelMatrix (FullPair L A) (FullPair L A'))
    (K : KernelMatrix (QuotPair L n A) (QuotPair L n A'))
    (hloc : IsRLocal L A.colourPairs A'.colourPairs R (liftKernel A A' W))
    (hd : ∀ f : QuotPair L n A → ℂ,
      applyKernel W (f ∘ projPair n A) = applyKernel K f ∘ projPair n A')
    (h : QuotPair L n A' → ℂ) :
    applyKernel (fun x y => W y x) (h ∘ projPair n A') =
      applyKernel (fun x y => K y x) h ∘ projPair n A := by
  classical
  let e := imageCarrierEquiv (L := L) (n := n) A hs
  let e' := imageCarrierEquiv (L := L) (n := n) A' hs'
  let M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n) :=
    fun c' c => K (e' c') (e c)
  have hdesc : KernelDescends L n A.colourPairs A'.colourPairs (liftKernel A A' W) M := by
    refine ⟨⟨R, hR, hloc⟩, fun f => ?_⟩
    funext ι'
    have hf : A.colourPairs.lift L n f =
        ((f ∘ e.symm) ∘ projPair n A) ∘ colourPairEquiv L A := by
      funext ι
      show f (A.colourPairs.proj L n ι) = f (e.symm (projPair n A (colourPairEquiv L A ι)))
      rw [← imageCarrierEquiv_proj A hs ι, Equiv.symm_apply_apply]
    rw [hf, applyKernel_liftKernel, hd]
    show applyKernel K (f ∘ e.symm) (projPair n A' (colourPairEquiv L A' ι')) =
      applyKernel M f (A'.colourPairs.proj L n ι')
    have := e.tsum_eq fun x => K (projPair n A' (colourPairEquiv L A' ι')) x * (f ∘ e.symm) x
    simp only [applyKernel]
    rw [← this]
    refine tsum_congr fun c => ?_
    show _ * f (e.symm (e c)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hz : IsRLocal L A.colourPairs A.colourPairs R
      (0 : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs)) :=
    fun _ _ _ => rfl
  have hz' : KernelDescends L n A.colourPairs A.colourPairs
      (0 : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs)) 0 := by
    refine ⟨⟨R, hR, hz⟩, fun f => ?_⟩
    funext ι
    simp [applyKernel, WeightedIndexSet.lift]
  have hT := ((hS A.colourPairs A'.colourPairs A.colourPairs R hR _ _ _ M M 0 hloc hloc hz hdesc
    hdesc hz').2.2.2.2.2 h2R).2.2.2 (h ∘ e')
  funext x
  have hx := congrFun hT ((colourPairEquiv L A).symm x)
  have hp : A'.colourPairs.lift L n (h ∘ e') = (h ∘ projPair n A') ∘ colourPairEquiv L A' := by
    funext ι
    rfl
  have ht : kernelT L A.colourPairs A'.colourPairs (liftKernel A A' W) =
      liftKernel A' A (fun x y => W y x) := by
    funext ι ι'
    show (((1 : ℝ) / 1 : ℝ) : ℂ) * _ = _
    simp [liftKernel]
  rw [hp, ht, applyKernel_liftKernel] at hx
  simp only [Equiv.apply_symm_apply] at hx
  rw [hx]
  show applyKernel (quotMatrixT L n A.colourPairs A'.colourPairs M) (h ∘ e')
      (A.colourPairs.proj L n ((colourPairEquiv L A).symm x)) = _
  have := e'.tsum_eq fun y => K y (projPair n A x) * h y
  simp only [applyKernel, Function.comp]
  rw [← this]
  refine tsum_congr fun c => ?_
  show (((1 : ℝ) / 1 : ℝ) : ℂ) * _ * _ = _
  simp only [div_one, Complex.ofReal_one, one_mul]
  rfl
end Generic
section SeriesExpansions
variable {L k : ℕ}
theorem kernelT_liftKernel (A A' : CellClass k)
    (W : KernelMatrix (FullPair L A) (FullPair L A')) :
    kernelT L A.colourPairs A'.colourPairs (liftKernel A A' W) =
      liftKernel A' A (fun x y => W y x) := by
  funext ι ι'
  show (((1 : ℝ) / 1 : ℝ) : ℂ) * _ = _
  simp [liftKernel]
theorem rowFinite_of_isRLocal (hE : LocalKernelFacts (k := k) L) (A A' : CellClass k) (R : ℝ)
    (hR : 0 ≤ R) (W : KernelMatrix (FullPair L A) (FullPair L A'))
    (hloc : IsRLocal L A.colourPairs A'.colourPairs R (liftKernel A A' W)) : RowFinite W := by
  intro x'
  have h := (hE A.colourPairs A'.colourPairs R hR _ hloc).1 (fun _ => 1)
    ((colourPairEquiv L A').symm x')
  refine (h.image (colourPairEquiv L A)).subset fun x hx => ?_
  refine ⟨(colourPairEquiv L A).symm x, ?_, Equiv.apply_symm_apply _ _⟩
  simpa [liftKernel] using hx
theorem rowFinite_swap_of_isRLocal (hE : LocalKernelFacts (k := k) L) (A A' : CellClass k)
    (R : ℝ) (hR : 0 ≤ R) (W : KernelMatrix (FullPair L A) (FullPair L A'))
    (hloc : IsRLocal L A.colourPairs A'.colourPairs R (liftKernel A A' W)) :
    RowFinite (fun x y => W y x : KernelMatrix (FullPair L A') (FullPair L A)) := by
  have h := (hE A.colourPairs A'.colourPairs R hR _ hloc).2.2.1
  rw [kernelT_liftKernel] at h
  exact rowFinite_of_isRLocal hE A' A R hR _ h
theorem supNormVec_le_euclidNormVec_neg (v : Fin 4 → ℝ) :
    TorusMetric.supNormVec v ≤ TorusMetric.euclidNormVec (-v) := by
  refine Finset.sup'_le _ _ fun μ _ => ?_
  unfold TorusMetric.euclidNormVec
  rw [show |v μ| = Real.sqrt (v μ ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
  refine Real.sqrt_le_sqrt ?_
  have : (-v) μ ^ 2 ≤ ∑ ν, (-v) ν ^ 2 :=
    Finset.single_le_sum (f := fun ν => (-v) ν ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  simpa using this
theorem isRLocal_of_vanishes (A A' : CellClass k) (R : ℝ)
    (W : KernelMatrix (FullPair L A) (FullPair L A'))
    (h : ∀ x' x, ¬ TorusMetric.euclidNormVec (Cell.anchor x'.2 - Cell.anchor x.2) ≤ R →
      W x' x = 0) : IsRLocal L A.colourPairs A'.colourPairs R (liftKernel A A' W) := by
  intro ι' ι hfar
  refine h _ _ fun hn => hfar ((supNormVec_le_euclidNormVec_neg _).trans ?_)
  have e : -(((A.colourPairs.toPeriodicData L).pos ι) - ((A'.colourPairs.toPeriodicData L).pos ι')) =
      Cell.anchor (colourPairEquiv L A' ι').2 - Cell.anchor (colourPairEquiv L A ι).2 := by
    rw [neg_sub]
    rfl
  rw [e]
  exact hn
end SeriesExpansions
section Coefficients
open OneLoop (pauliCoordinateEquiv)
theorem pauliCoeff_coe (X : ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X : ComplexMatrix2) = pauliCoordinateEquiv X a := by apply _root_.YangMills.Construction.LocalKernels.PairBrackets.pauliCoeff_coe <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (c • X) = c * pauliCoeff a X := by
  have h := pauliCoeff_coe (c • (⟨X, hX⟩ : ComplexMatrix2.traceless)) a
  rw [map_smul, Pi.smul_apply, ← pauliCoeff_coe, smul_eq_mul] at h
  exact h
theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, pauliCoeff a X * pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p22145 <;> assumption
theorem traceFinsumPairing_eq_tsum (hP : OneLoop.PauliMatrixRelations) {σ : Type} [Finite σ]
    {f g : σ → ComplexMatrix2} (hf : ∀ i, f i ∈ ComplexMatrix2.traceless)
    (hg : ∀ i, g i ∈ ComplexMatrix2.traceless) :
    traceFinsumPairing f g = ∑' ι, toPauliCoeffs f ι * toPauliCoeffs g ι := by
  have := Fintype.ofFinite σ
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, tsum_fintype, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun i _ => halfTrace_mul_eq_sum hP (hf i) (hg i)
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := hX.2
end Coefficients
section EvaluationMaps
variable {L n k j : ℕ}
open CovDiffTransposes (matrixKernel)
def edgeFormOf (c : Fin 3 × PositiveEdge L n k j → ℂ) : Edge L n k j → ComplexMatrix2 :=
  (edgePauliCoordinates L n k j).ofCoeffs c
open Classical in
theorem edgeFormOf_eq (c : Fin 3 × PositiveEdge L n k j → ℂ) :
    edgeFormOf c = extendOddly fun b =>
      if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0 :=
  rfl
theorem edgeFormOf_pos (c : Fin 3 × PositiveEdge L n k j → ℂ) (b : PositiveEdge L n k j) :
    edgeFormOf c b.1 = ofPauliCoeffs c b := by
  rw [edgeFormOf_eq]
  unfold extendOddly
  rw [if_pos b.2]
  exact dif_pos b.2
theorem edgeFormOf_opposite
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℂ) (b : Edge L n k j) :
    edgeFormOf c b.opposite = -edgeFormOf c b := by
  have e : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  rw [edgeFormOf_eq]
  unfold extendOddly
  rcases hX b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [if_neg h₂, if_pos h₁, e]
  · rw [if_pos h₁, if_neg h₂, neg_neg]
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem edgeFormOf_mem_complexEdgeForms
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℂ) :
    edgeFormOf c ∈ complexEdgeForms L n k j := by
  refine ⟨fun b hb => ?_, edgeFormOf_opposite hX c⟩
  rw [edgeFormOf_pos c ⟨b, hb⟩]
  exact ofPauliCoeffs_mem_traceless c _
theorem toPauliCoeffs_restrict_edgeFormOf (c : Fin 3 × PositiveEdge L n k j → ℂ) :
    toPauliCoeffs (restrictToPositiveEdges (edgeFormOf c)) = c := by
  funext ι
  show pauliCoeff ι.1 (edgeFormOf c ι.2.1) = _
  rw [edgeFormOf_pos]
  exact pauliCoeff_sum_smul (fun a => c (a, ι.2)) ι.1
def indicatorAt {P : Type} (κ : P) : P → ℂ :=
  fun κ' => @ite ℂ (κ' = κ) (Classical.propDecidable _) 1 0
theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem edgeFormOf_indicatorAt_mem
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (κ : Fin 3 × PositiveEdge L n k j) :
    edgeFormOf (indicatorAt κ) ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, edgeFormOf_opposite hX _⟩
  rw [edgeFormOf_pos _ ⟨b, hb⟩]
  refine Submodule.sum_mem _ fun a _ => ?_
  unfold indicatorAt
  split_ifs with h
  · rw [one_smul]
    exact pauliFamily_mem_hermitianTraceless a
  · rw [zero_smul]
    exact ComplexMatrix2.hermitianTraceless.zero_mem
end EvaluationMaps
section Descent
variable {L n k j : ℕ}
open CovDiffTransposes (HasTransposeKernel matrixKernel)
open FreeOperators (IsRangeThreeKernelOf)
def faceClass (k j : ℕ) (h : j ≤ k) : CellClass k := ⟨j, h, .face⟩
def fullEdgeFormOf (c : Fin 3 × PeriodicOperators.PosEdge L k j → ℂ) :
    FullSpace.Edge L k j → ComplexMatrix2 :=
  (FullSpace.edgePauliCoordinates L k j).ofCoeffs c
open Classical in
theorem fullEdgeFormOf_eq (c : Fin 3 × PeriodicOperators.PosEdge L k j → ℂ) :
    fullEdgeFormOf c = FullSpace.extendOddly fun b =>
      if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0 :=
  rfl
theorem fullEdgeFormOf_pos (c : Fin 3 × PeriodicOperators.PosEdge L k j → ℂ)
    (b : PeriodicOperators.PosEdge L k j) : fullEdgeFormOf c b.1 = ofPauliCoeffs c b := by
  rw [fullEdgeFormOf_eq]
  unfold FullSpace.extendOddly
  rw [if_pos b.2]
  exact dif_pos b.2
theorem fullEdgeFormOf_lift_eq (hB : ProjEdgesCompatible L n k j)
    (f : Fin 3 × Tower.PositiveEdge L n k j → ℂ)
    (b : FullSpace.Edge L k j) (hb : b.IsPositivelyOriented) :
    fullEdgeFormOf (fun x => f (x.1, projPositiveEdge L n k j x.2)) b =
      edgeFormOf f (FullSpace.projEdge L n k j b) := by
  rw [fullEdgeFormOf_pos _ ⟨b, hb⟩, ← hB.2.1 ⟨b, hb⟩, edgeFormOf_pos]
  rfl
theorem fullForwardFrom_isPositivelyOriented {a : ℝ} (x : InfiniteLattice.LatticePoint a)
    (μ : Fin 4) : (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem forwardFrom_isPositivelyOriented (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
theorem edgeCoboundary_fullEdgeFormOf_lift (hB : ProjEdgesCompatible L n k j)
    (f : Fin 3 × Tower.PositiveEdge L n k j → ℂ) (p : FullSpace.Face L k j) :
    FullSpace.edgeCoboundary (fullEdgeFormOf fun x => f (x.1, projPositiveEdge L n k j x.2)) p =
      edgeCoboundary (edgeFormOf f) (FullSpace.projFace L n k j p) := by
  have e := hB.2.2 p
  simp only [faceEdges, FullSpace.faceEdges, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at e
  obtain ⟨e₁, e₂, e₃, e₄⟩ := e
  unfold edgeCoboundary FullSpace.edgeCoboundary
  rw [e₁, e₂, e₃, e₄, fullEdgeFormOf_lift_eq hB f _ (fullForwardFrom_isPositivelyOriented _ _),
    fullEdgeFormOf_lift_eq hB f _ (fullForwardFrom_isPositivelyOriented _ _),
    fullEdgeFormOf_lift_eq hB f _ (fullForwardFrom_isPositivelyOriented _ _),
    fullEdgeFormOf_lift_eq hB f _ (fullForwardFrom_isPositivelyOriented _ _)]
theorem vertexCoboundary_lift (hB : ProjEdgesCompatible L n k j) (f : Fin 3 × Vertex L n k j → ℂ)
    (b : PeriodicOperators.PosEdge L k j) :
    FullSpace.vertexCoboundary
        (ofPauliCoeffs fun x => f (x.1, FullSpace.projVertex L n k j x.2)) b.1 =
      vertexCoboundary (ofPauliCoeffs f) (projPositiveEdge L n k j b).1 := by
  rw [hB.2.1 b]
  unfold vertexCoboundary FullSpace.vertexCoboundary
  rw [(hB.1 b.1).1, (hB.1 b.1).2]
  rfl
theorem edgeCoboundary_mem_traceless {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (p : Face L n k j) :
    edgeCoboundary B p ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.sub_mem (ComplexMatrix2.traceless.sub_mem
    (ComplexMatrix2.traceless.add_mem (hB.1 _ (forwardFrom_isPositivelyOriented _ _))
      (hB.1 _ (forwardFrom_isPositivelyOriented _ _)))
      (hB.1 _ (forwardFrom_isPositivelyOriented _ _)))
    (hB.1 _ (forwardFrom_isPositivelyOriented _ _))
theorem mul_pauliCoeff_inv_smul {l : ℝ} (hl : l ≠ 0) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    (l : ℂ) * pauliCoeff a (l⁻¹ • Y) = pauliCoeff a Y := by
  have e : (l⁻¹ • Y : ComplexMatrix2) = ((l : ℂ)⁻¹) • Y := by
    ext i i'
    simp [Complex.real_smul]
  rw [e, pauliCoeff_smul _ hY, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hl), one_mul]
theorem applyKernel_const_mul {J J' : Type} (c : ℂ) (T : KernelMatrix J J') (g : J → ℂ)
    (x : J') : applyKernel (fun x' y => c * T x' y) g x = c * applyKernel T g x := by
  simp only [applyKernel, mul_assoc]
  exact tsum_mul_left
theorem applyKernel_smul {J J' : Type} (c : ℂ) (T : KernelMatrix J J') (g : J → ℂ) (x : J') :
    applyKernel T (c • g) x = c * applyKernel T g x := by
  simp only [applyKernel, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact tsum_mul_left
theorem edgeCoboundary_kernel_descends (hj : j ≤ k) (hB : ProjEdgesCompatible L n k j)
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hl : meshAt L k j ≠ 0)
    (hw : IsRangeThreeKernelOf (colourEdges L k j) (colourFaces L k j)
      (FullSpace.scaledEdgeCoboundaryKernel L k j)
      ((FullSpace.edgePauliCoordinates L k j).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k j))
        FullSpace.scaledEdgeCoboundary))
    (hK : HasTransposeKernel (edgePauliCoordinates L n k j) (vertexCoordinate (Face L n k j))
      edgeCoboundary)
    (f : QuotPair L n (CellClass.edgeClass k j hj) → ℂ) :
    applyKernel (fun x' x => (meshAt L k j : ℂ) *
        FullSpace.scaledEdgeCoboundaryKernel L k j x' x :
          KernelMatrix (FullPair L (CellClass.edgeClass k j hj))
            (FullPair L (faceClass k j hj)))
        (f ∘ projPair n (CellClass.edgeClass k j hj)) =
      applyKernel (matrixKernel (edgePauliCoordinates L n k j) (vertexCoordinate (Face L n k j))
        edgeCoboundary) f ∘ projPair n (faceClass k j hj) := by
  funext x
  obtain ⟨c, p⟩ := x
  refine (applyKernel_const_mul (meshAt L k j : ℂ) (FullSpace.scaledEdgeCoboundaryKernel L k j)
    _ _).trans ?_
  have hi := congrFun (hw.applyKernel_eq (f ∘ projPair n (CellClass.edgeClass k j hj))) (c, p)
  have hg := (hK.represents (edgeFormOf f) (edgeFormOf_mem_complexEdgeForms hX f)
    (c, FullSpace.projFace L n k j p)).2
  have hg' : pauliCoeff c
      (edgeCoboundary (edgeFormOf f) (FullSpace.projFace L n k j p)) =
      applyKernel (matrixKernel (edgePauliCoordinates L n k j) (vertexCoordinate (Face L n k j))
        edgeCoboundary) f (c, FullSpace.projFace L n k j p) :=
    hg.trans (congrArg (fun g => applyKernel (matrixKernel (edgePauliCoordinates L n k j)
      (vertexCoordinate (Face L n k j)) edgeCoboundary) g
        (c, FullSpace.projFace L n k j p)) (toPauliCoeffs_restrict_edgeFormOf f))
  refine (congrArg (fun z => (meshAt L k j : ℂ) * z) hi).trans ?_
  refine Eq.trans ?_ hg'
  have hE := edgeCoboundary_fullEdgeFormOf_lift hB f p
  have hY := edgeCoboundary_mem_traceless (edgeFormOf_mem_complexEdgeForms hX f)
    (FullSpace.projFace L n k j p)
  rw [← hE] at hY
  exact (mul_pauliCoeff_inv_smul hl hY c).trans (congrArg (pauliCoeff c) hE)
theorem vertexCoboundary_kernel_descends (hj : j ≤ k) (hB : ProjEdgesCompatible L n k j)
    (hl : meshAt L k j ≠ 0)
    (hw : IsRangeThreeKernelOf (colourVertices L k j) (colourEdges L k j)
      (FullSpace.scaledVertexCoboundaryKernel L k j)
      ((vertexCoordinate (FullSpace.Vertex L k j)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k j)
        FullSpace.scaledVertexCoboundary))
    (hK : HasTransposeKernel (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j)
      vertexCoboundary)
    (f : QuotPair L n (CellClass.vertexClass k j hj) → ℂ) :
    applyKernel (fun x' x => (meshAt L k j : ℂ) *
        FullSpace.scaledVertexCoboundaryKernel L k j x' x :
          KernelMatrix (FullPair L (CellClass.vertexClass k j hj))
            (FullPair L (CellClass.edgeClass k j hj)))
        (f ∘ projPair n (CellClass.vertexClass k j hj)) =
      applyKernel (matrixKernel (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j)
        vertexCoboundary) f ∘ projPair n (CellClass.edgeClass k j hj) := by
  funext x
  obtain ⟨c, b⟩ := x
  refine (applyKernel_const_mul (meshAt L k j : ℂ) (FullSpace.scaledVertexCoboundaryKernel L k j)
    _ _).trans ?_
  have hi := congrFun (hw.applyKernel_eq (f ∘ projPair n (CellClass.vertexClass k j hj))) (c, b)
  have hmem : ofPauliCoeffs f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k j) :=
    fun i _ => ofPauliCoeffs_mem_traceless f i
  have hcol : toPauliCoeffs (ofPauliCoeffs f) = f := by
    funext ι
    exact pauliCoeff_sum_smul (fun a => f (a, ι.2)) ι.1
  have hg := (hK.represents (ofPauliCoeffs f) hmem (c, projPositiveEdge L n k j b)).2
  have hg' : pauliCoeff c
      (vertexCoboundary (ofPauliCoeffs f) (projPositiveEdge L n k j b).1) =
      applyKernel (matrixKernel (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j)
        vertexCoboundary) f (c, projPositiveEdge L n k j b) :=
    hg.trans (congrArg (fun g => applyKernel (matrixKernel (vertexCoordinate (Vertex L n k j))
      (edgePauliCoordinates L n k j) vertexCoboundary) g (c, projPositiveEdge L n k j b)) hcol)
  refine (congrArg (fun z => (meshAt L k j : ℂ) * z) hi).trans ?_
  refine Eq.trans ?_ hg'
  have hE := vertexCoboundary_lift hB f b
  have hY : vertexCoboundary (ofPauliCoeffs f) (projPositiveEdge L n k j b).1 ∈
      ComplexMatrix2.traceless :=
    ComplexMatrix2.traceless.sub_mem (ofPauliCoeffs_mem_traceless f _)
      (ofPauliCoeffs_mem_traceless f _)
  exact (mul_pauliCoeff_inv_smul hl
    (Eq.mpr (congrArg (fun X => X ∈ ComplexMatrix2.traceless) hE) hY) c).trans
    (congrArg (pauliCoeff c) hE)
end Descent
section Torus
variable {L n k : ℕ}
open CovDiffTransposes (HasTransposeKernel matrixKernel)
open PeriodicForm (coeffsOnEdges)
open CriticalBranchResponse
theorem formCoboundary_apply (A : edgeFormSpace L n k 0) :
    (formCoboundary L n k A : Face L n k 0 → ComplexMatrix2) = edgeCoboundary A := by apply _root_.YangMills.Construction.Tower.ProlongDifferential.formCoboundary_apply <;> assumption
theorem matrixKernel_eq (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2)
    (ι' : r'.Index) (ι : r.Index) :
    matrixKernel r r' m ι' ι = r'.coeffs (m (r.ofCoeffs (indicatorAt ι))) ι' := by
  unfold matrixKernel indicatorAt
  congr!
theorem pauliCoeff_formCoboundaryTranspose (hP : OneLoop.PauliMatrixRelations)
    (hPt : RealTransposeFaceFunctionPairing)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Finite (Tower.PositiveEdge L n k 0)] [Finite (Face L n k 0)]
    (G : faceFunctionSpace L n k 0) (κ : Fin 3 × Tower.PositiveEdge L n k 0) :
    toPauliCoeffs (restrictToPositiveEdges
        (formCoboundaryTranspose L n k G : Edge L n k 0 → ComplexMatrix2)) κ =
      applyKernel (fun x y => matrixKernel (edgePauliCoordinates L n k 0)
        (vertexCoordinate (Face L n k 0)) edgeCoboundary y x)
        (toPauliCoeffs (G : Face L n k 0 → ComplexMatrix2)) κ := by
  classical
  let Q : edgeFormSpace L n k 0 := ⟨edgeFormOf (indicatorAt κ), edgeFormOf_indicatorAt_mem hX κ⟩
  have hp := hPt L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k) (formCoboundary L n k) G Q
  have hXr := (formCoboundaryTranspose L n k G).2
  have h₁ : edgeFormPairing (formCoboundaryTranspose L n k G : Edge L n k 0 → ComplexMatrix2)
      (Q : Edge L n k 0 → ComplexMatrix2) =
      toPauliCoeffs (restrictToPositiveEdges
        (formCoboundaryTranspose L n k G : Edge L n k 0 → ComplexMatrix2)) κ := by
    unfold edgeFormPairing
    rw [traceFinsumPairing_eq_tsum hP
      (f := restrictToPositiveEdges
        (formCoboundaryTranspose L n k G : Edge L n k 0 → ComplexMatrix2))
      (g := restrictToPositiveEdges (Q : Edge L n k 0 → ComplexMatrix2))
      (fun b => mem_traceless_of_mem_hermitianTraceless (hXr.1 _ b.2))
      (fun b => (edgeFormOf_mem_complexEdgeForms hX _).1 _ b.2)]
    have hc : toPauliCoeffs (restrictToPositiveEdges (Q : Edge L n k 0 → ComplexMatrix2)) =
        indicatorAt κ :=
      toPauliCoeffs_restrict_edgeFormOf _
    rw [hc, tsum_eq_single κ]
    · simp [indicatorAt]
    · intro ι hι
      simp [indicatorAt, hι]
  have h₂ : traceFinsumPairing (G : Face L n k 0 → ComplexMatrix2)
      (formCoboundary L n k Q : Face L n k 0 → ComplexMatrix2) =
      applyKernel (fun x y => matrixKernel (edgePauliCoordinates L n k 0)
        (vertexCoordinate (Face L n k 0)) edgeCoboundary y x)
        (toPauliCoeffs (G : Face L n k 0 → ComplexMatrix2)) κ := by
    rw [formCoboundary_apply, traceFinsumPairing_eq_tsum hP
      (fun p => mem_traceless_of_mem_hermitianTraceless (G.2 p (mem_univ p)))
      (edgeCoboundary_mem_traceless (edgeFormOf_mem_complexEdgeForms hX _))]
    simp only [applyKernel]
    refine tsum_congr fun ι => ?_
    rw [mul_comm]
    exact congrArg (· * toPauliCoeffs (G : Face L n k 0 → ComplexMatrix2) ι)
      (matrixKernel_eq (edgePauliCoordinates L n k 0) (vertexCoordinate (Face L n k 0)) edgeCoboundary
        ι κ).symm
  rw [← h₁, ← h₂]
  exact hp
end Torus
section Side
variable {L n k : ℕ}
open CriticalBranchResponse
open CovDiffTransposes (HasTransposeKernel matrixKernel LatticeTransposeData)
open PeriodicForm (coeffsOnEdges)
open PlaneWaveCalculus (edgeCoboundaryT vertexCoboundaryT)
open ResponseProperties (coboundaryLaplacian)
theorem meshAt_ne_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    meshAt L k j ≠ 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.meshAt_ne_zero <;> assumption
theorem edgeCoboundaryT_eq {j : ℕ} (hl : meshAt L k j ≠ 0) :
    edgeCoboundaryT L k j =
      fun x y => FullSpace.scaledEdgeCoboundaryKernel L k j y x := by
  funext x y
  show (((meshAt L k j ^ 4 / meshAt L k j ^ 4 : ℝ)) : ℂ) * _ = _
  rw [div_self (pow_ne_zero 4 hl)]
  simp
theorem vertexCoboundaryT_eq {j : ℕ} (hl : meshAt L k j ≠ 0) :
    vertexCoboundaryT L k j =
      fun x y => FullSpace.scaledVertexCoboundaryKernel L k j y x := by
  funext x y
  show (((meshAt L k j ^ 4 / meshAt L k j ^ 4 : ℝ)) : ℂ) * _ = _
  rw [div_self (pow_ne_zero 4 hl)]
  simp
theorem six_lt_periodSide (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    2 * (3 : ℝ) < (periodSide L n : ℝ) := by
  have h13 := hL.2
  have hPow : L ≤ L ^ n := Nat.le_self_pow (by omega) L
  have h : 6 < periodSide L n := by
    unfold periodSide
    omega
  have : (6 : ℝ) < (periodSide L n : ℝ) := by exact_mod_cast h
  linarith
theorem trivialField_mem (j : ℕ) :
    trivialField L n k j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.RescaledTrivialStepsProof.trivialField_mem_fieldsIn <;> assumption
theorem finite_quotientCell (A : CellClass k) (hI : QuotientClassesPeriodic L n A.colourPairs)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)) :
    Finite (QuotientCell L n k A.level A.cellType) := by
  have := hI.1
  have : Finite (QuotPair L n A) := Finite.of_equiv _ (imageCarrierEquiv A hs)
  exact Finite.of_surjective (Prod.snd : QuotPair L n A → _) fun c => ⟨(0, c), rfl⟩
end Side
section Main
variable {L n k : ℕ}
open CovDiffTransposes (HasTransposeKernel matrixKernel)
open PeriodicForm (coeffsOnEdges)
open PlaneWaveCalculus (edgeCoboundaryT vertexCoboundaryT)
open ResponseProperties (coboundaryLaplacian)
open FreeOperators (IsRangeThreeKernelOf)
open CriticalBranchResponse
theorem mem_complexEdgeForms {j : ℕ} (A : edgeFormSpace L n k j) :
    (A : Edge L n k j → ComplexMatrix2) ∈ complexEdgeForms L n k j :=
  ⟨fun b hb => mem_traceless_of_mem_hermitianTraceless (A.2.1 b hb), A.2.2⟩
theorem coeffsOnEdges_transpose_coboundary (hP : OneLoop.PauliMatrixRelations)
    (hPt : RealTransposeFaceFunctionPairing)
    (hA : PeriodicOperators.RowFiniteKernels.ApplyComp)
    (hS : DescendsAlgebra (k := k) L n)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hB : ProjEdgesCompatible L n k 0)
    (hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hs : Function.Surjective (Cell.proj n :
      Cell L k (CellClass.edgeClass k 0 (Nat.zero_le k)).level
        (CellClass.edgeClass k 0 (Nat.zero_le k)).cellType → QuotientCell L n k 0 .edge))
    (hs' : Function.Surjective (Cell.proj n :
      Cell L k (faceClass k 0 (Nat.zero_le k)).level
        (faceClass k 0 (Nat.zero_le k)).cellType → QuotientCell L n k 0 .face))
    [Finite (Tower.PositiveEdge L n k 0)] [Finite (Face L n k 0)]
    (hw : IsRangeThreeKernelOf (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0)
      ((FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary))
    (hK : HasTransposeKernel (edgePauliCoordinates L n k 0) (vertexCoordinate (Face L n k 0))
      edgeCoboundary)
    (hrow : RowFinite (FullSpace.scaledEdgeCoboundaryKernel L k 0))
    (hrow' : RowFinite
      (fun x y => FullSpace.scaledEdgeCoboundaryKernel L k 0 y x :
        KernelMatrix (Fin 3 × FullSpace.Face L k 0)
          (Fin 3 × PeriodicOperators.PosEdge L k 0)))
    (A : edgeFormSpace L n k 0) :
    coeffsOnEdges L n k 0 (formCoboundaryTranspose L n k (formCoboundary L n k A)) =
      ((finestMesh L k : ℂ) ^ 2) • applyKernel (coboundaryLaplacian L k)
        (coeffsOnEdges L n k 0 A) := by
  have hl := meshAt_ne_zero hL k 0
  let T := FullSpace.scaledEdgeCoboundaryKernel L k 0
  let K := matrixKernel (edgePauliCoordinates L n k 0) (vertexCoordinate (Face L n k 0)) edgeCoboundary
  let B₀ := CellClass.edgeClass k 0 (Nat.zero_le k)
  let P₀ := faceClass k 0 (Nat.zero_le k)
  let W : KernelMatrix (FullPair L B₀) (FullPair L P₀) :=
    fun x' x => (meshAt L k 0 : ℂ) * T x' x
  let f : QuotPair L n B₀ → ℂ :=
    toPauliCoeffs (restrictToPositiveEdges (A : Edge L n k 0 → ComplexMatrix2))
  let h : QuotPair L n P₀ → ℂ := toPauliCoeffs (edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2))
  have hloc : IsRLocal L B₀.colourPairs P₀.colourPairs 3 (liftKernel B₀ P₀ W) := by
    refine isRLocal_of_vanishes B₀ P₀ 3 W fun x' x hfar => ?_
    show (meshAt L k 0 : ℂ) * T x' x = 0
    rw [show T x' x = 0 from hw.vanishes_outside x' x hfar, mul_zero]
  have hcar := edgeCoboundary_kernel_descends (Nat.zero_le k) hB hX hl hw hK
  have e₂ : applyKernel K f = h := by
    funext κ
    exact ((hK.represents (A : Edge L n k 0 → ComplexMatrix2) (mem_complexEdgeForms A) κ).2).symm
  have e₁ : applyKernel W (f ∘ projPair n B₀) = h ∘ projPair n P₀ := by
    rw [← e₂]
    exact hcar f
  have e₃ := transpose_applyKernel_comp_projPair hS B₀ P₀ hs hs' 3 (by norm_num)
    (six_lt_periodSide hL hn) W K hloc hcar h
  have e₄ : ∀ ι, toPauliCoeffs (restrictToPositiveEdges
      (formCoboundaryTranspose L n k (formCoboundary L n k A) : Edge L n k 0 → ComplexMatrix2))
        (projPair n B₀ ι) =
      applyKernel (fun x y => K y x) h (projPair n B₀ ι) := by
    intro ι
    have e := pauliCoeff_formCoboundaryTranspose hP hPt hL hn hX (formCoboundary L n k A)
      (projPair n B₀ ι)
    rw [formCoboundary_apply] at e
    exact e
  have hprod := ((hA _ _ T hrow).2 _ _ hrow').2.2 (coeffsOnEdges L n k 0 A)
  have hcurl : coboundaryLaplacian L k = compKernel (fun x y => T y x) T := by
    unfold coboundaryLaplacian
    rw [edgeCoboundaryT_eq hl]
    rfl
  have hcp : applyKernel (coboundaryLaplacian L k) (coeffsOnEdges L n k 0 A) =
      applyKernel (fun x y => T y x) (applyKernel T (coeffsOnEdges L n k 0 A)) := by
    rw [hcurl]
    exact hprod.2.2
  have hg : (f ∘ projPair n B₀ : FullPair L B₀ → ℂ) = coeffsOnEdges L n k 0 A := rfl
  have hW : applyKernel W (coeffsOnEdges L n k 0 A) =
      (meshAt L k 0 : ℂ) • applyKernel T (coeffsOnEdges L n k 0 A) := by
    funext x
    exact applyKernel_const_mul _ T _ x
  funext ι
  have hη : (finestMesh L k : ℂ) = (meshAt L k 0 : ℂ) := rfl
  calc coeffsOnEdges L n k 0 (formCoboundaryTranspose L n k (formCoboundary L n k A)) ι
      = applyKernel (fun x y => K y x) h (projPair n B₀ ι) := e₄ ι
    _ = applyKernel (fun x y => W y x) (h ∘ projPair n P₀) ι := (congrFun e₃ ι).symm
    _ = applyKernel (fun x y => W y x) (applyKernel W (coeffsOnEdges L n k 0 A)) ι := by
        rw [← e₁, hg]
    _ = (meshAt L k 0 : ℂ) * applyKernel (fun x y => T y x)
          (applyKernel W (coeffsOnEdges L n k 0 A)) ι :=
        applyKernel_const_mul _ (fun x y => T y x) _ ι
    _ = (meshAt L k 0 : ℂ) * ((meshAt L k 0 : ℂ) * applyKernel (fun x y => T y x)
          (applyKernel T (coeffsOnEdges L n k 0 A)) ι) := by
        exact congrArg (fun z => (meshAt L k 0 : ℂ) * z)
          ((congrArg (fun g => applyKernel (fun x y => T y x) g ι) hW).trans
            (applyKernel_smul _ _ _ ι))
    _ = (((finestMesh L k : ℂ) ^ 2) • applyKernel (coboundaryLaplacian L k)
          (coeffsOnEdges L n k 0 A)) ι := by
        show _ = ((finestMesh L k : ℂ) ^ 2) * applyKernel (coboundaryLaplacian L k)
          (coeffsOnEdges L n k 0 A) ι
        rw [hcp, hη]
        ring
end Main
section Divergence
variable {L n k : ℕ}
open CovDiffTransposes (HasTransposeKernel matrixKernel)
open PeriodicForm (coeffsOnEdges)
open CriticalBranchResponse
open PlaneWaveCalculus (vertexCoboundaryT)
open PairedFunctionSpace (linearOfValues transposeOfValues)
open FreeOperators (IsRangeThreeKernelOf)
theorem edgeFormPairing_vertexCoboundary_eq_zero (hS : DescendsAlgebra (k := k) L n)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hB : ProjEdgesCompatible L n k k)
    (hs : Function.Surjective (Cell.proj n :
      Cell L k (CellClass.vertexClass k k le_rfl).level
        (CellClass.vertexClass k k le_rfl).cellType → QuotientCell L n k k .vertex))
    (hs' : Function.Surjective (Cell.proj n :
      Cell L k (CellClass.edgeClass k k le_rfl).level
        (CellClass.edgeClass k k le_rfl).cellType → QuotientCell L n k k .edge))
    [Finite (Vertex L n k k)]
    (hw : IsRangeThreeKernelOf (colourVertices L k k) (colourEdges L k k)
      (FullSpace.scaledVertexCoboundaryKernel L k k)
      ((vertexCoordinate (FullSpace.Vertex L k k)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k k)
        FullSpace.scaledVertexCoboundary))
    (hK : HasTransposeKernel (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k)
      vertexCoboundary)
    (μ : edgeFormSpace L n k k)
    (hz : applyKernel (vertexCoboundaryT L k k) (coeffsOnEdges L n k k μ) = 0)
    (l : Vertex L n k k → ComplexMatrix2) (hl : l ∈ vertexFunctionSpace L n k k) :
    edgeFormPairing (μ : Edge L n k k → ComplexMatrix2) (vertexCoboundary l) = 0 := by
  have hsp := meshAt_ne_zero hL k k
  let T := FullSpace.scaledVertexCoboundaryKernel L k k
  let K := matrixKernel (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) vertexCoboundary
  let S₀ := CellClass.vertexClass k k le_rfl
  let B₀ := CellClass.edgeClass k k le_rfl
  let W : KernelMatrix (FullPair L S₀) (FullPair L B₀) :=
    fun x' x => (meshAt L k k : ℂ) * T x' x
  let h : QuotPair L n B₀ → ℂ :=
    toPauliCoeffs (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2))
  have hloc : IsRLocal L S₀.colourPairs B₀.colourPairs 3 (liftKernel S₀ B₀ W) := by
    refine isRLocal_of_vanishes S₀ B₀ 3 W fun x' x hfar => ?_
    show (meshAt L k k : ℂ) * T x' x = 0
    rw [show T x' x = 0 from hw.vanishes_outside x' x hfar, mul_zero]
  have e₃ := transpose_applyKernel_comp_projPair hS S₀ B₀ hs hs' 3 (by norm_num)
    (six_lt_periodSide hL hn) W K hloc (vertexCoboundary_kernel_descends le_rfl hB hsp hw hK) h
  have hzero : ∀ x, applyKernel (fun x y => K y x) h (projPair n S₀ x) = 0 := by
    intro x
    have e := congrFun e₃ x
    have e' : applyKernel (fun x y => W y x) (h ∘ projPair n B₀) x =
        (meshAt L k k : ℂ) * applyKernel (fun x y => T y x) (coeffsOnEdges L n k k μ) x :=
      applyKernel_const_mul _ (fun x y => T y x) _ x
    have e'' : applyKernel (fun x y => T y x) (coeffsOnEdges L n k k μ) x = 0 := by
      have := congrFun hz x
      rw [vertexCoboundaryT_eq hsp] at this
      exact this
    rw [e'', mul_zero] at e'
    exact e.symm.trans e'
  have hzero' : ∀ κ, applyKernel (fun x y => K y x) h κ = 0 := by
    rintro ⟨a, c⟩
    obtain ⟨x, hx⟩ := hs c
    have := hzero (a, x)
    have e : projPair n S₀ (a, x) = (a, c) := Prod.ext rfl hx
    rw [e] at this
    exact this
  have hμ := mem_complexEdgeForms μ
  have hl' : l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k k) :=
    fun i hi => mem_traceless_of_mem_hermitianTraceless (hl i hi)
  let C := linearOfValues (vertexCoordinate (Vertex L n k k)).space
    (edgePauliCoordinates L n k k).space vertexCoboundary
  let t := PairedFunctionSpace.transposeMap C ⟨(μ : Edge L n k k → ComplexMatrix2), hμ⟩
  have ht : (t.1 : Vertex L n k k → ComplexMatrix2) = 0 := by
    funext x
    have hmem : (t.1 : Vertex L n k k → ComplexMatrix2) x ∈ ComplexMatrix2.traceless :=
      t.2 x (mem_univ x)
    rw [Pi.zero_apply, ← sum_pauliCoeff_smul hmem]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hg := (hK.transpose_represents (μ : Edge L n k k → ComplexMatrix2) hμ (a, x)).2
    have hv : transposeOfValues (vertexCoordinate (Vertex L n k k)).space
        (edgePauliCoordinates L n k k).space vertexCoboundary (μ : Edge L n k k → ComplexMatrix2) =
          t.1 := dif_pos hμ
    rw [hv] at hg
    have e : pauliCoeff a ((t.1 : Vertex L n k k → ComplexMatrix2) x) = 0 :=
      hg.trans (hzero' (a, x))
    rw [e, zero_smul]
  have hf := hK.isTranspose ⟨(μ : Edge L n k k → ComplexMatrix2), hμ⟩ ⟨l, hl'⟩ (Set.toFinite _)
  have hlin := hK.coe_linear ⟨l, hl'⟩
  have e : edgeFormPairing (μ : Edge L n k k → ComplexMatrix2) (vertexCoboundary l) =
      traceFinsumPairing (t.1 : Vertex L n k k → ComplexMatrix2) l := by
    rw [← hlin]
    exact hf.symm
  rw [e, ht]
  simp [traceFinsumPairing, ComplexMatrix2.halfTrace]
end Divergence
theorem claim (hKernels : PeriodicOperators.RowFiniteKernels.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hSums : DescendingKernelAlgebra)
    (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hLocal : KernelsAndLinearMapMatrices)
    (hTrans : CovDiffTransposes.Claim)
    (hPt : RealTransposeFaceFunctionPairing)
    (hXor : PeriodicLattice.LevelBondOrientationDichotomy)
    (hP : OneLoop.PauliMatrixRelations) : FormCoboundariesAtInfinity.Claim := by
  intro L hL k hk n hn
  have hz : 0 ≤ k := Nat.zero_le k
  have hC := hCells L hL k n hn
  obtain ⟨hC₀, hB₀⟩ := hC.1 0 hz
  obtain ⟨hCk, hBk⟩ := hC.1 k le_rfl
  have hE := (hLocal L hL k n hn).1
  have hS := hSums L hL k n hn
  obtain ⟨hmaps, -⟩ := hFree.2 L hL k hk
  have hw₀ := (hmaps.edgeCoboundary 0 hz)
  have hwk := (hmaps.vertexCoboundary k le_rfl)
  have hX : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => hXor L n k hL hn (by omega) 0 hz b
  have hK₀ := ((hTrans L hL k 0 hz).1 n hn _ (trivialField_mem 0)).edgeCoboundary
  have hKk := ((hTrans L hL k k le_rfl).1 n hn _ (trivialField_mem k)).vertexCoboundary
  have hs₀ := (hC₀ .edge).1
  have hp₀ := (hC₀ .face).1
  have hsk := (hCk .vertex).1
  have hbk := (hCk .edge).1
  have hfb : Finite (Tower.PositiveEdge L n k 0) :=
    finite_quotientCell (CellClass.edgeClass k 0 hz) (hC.2 _) hs₀
  have hfp : Finite (Face L n k 0) := finite_quotientCell (faceClass k 0 hz) (hC.2 _) hp₀
  have hfs : Finite (Vertex L n k k) :=
    finite_quotientCell (CellClass.vertexClass k k le_rfl) (hC.2 _) hsk
  have hloc₀ : IsRLocal L (CellClass.edgeClass k 0 hz).colourPairs (faceClass k 0 hz).colourPairs 3
      (liftKernel _ _ (FullSpace.scaledEdgeCoboundaryKernel L k 0)) :=
    isRLocal_of_vanishes _ _ 3 _ hw₀.vanishes_outside
  have hlock : IsRLocal L (CellClass.vertexClass k k le_rfl).colourPairs
      (CellClass.edgeClass k k le_rfl).colourPairs 3
      (liftKernel _ _ (FullSpace.scaledVertexCoboundaryKernel L k k)) :=
    isRLocal_of_vanishes _ _ 3 _ hwk.vanishes_outside
  have hr₀ := rowFinite_of_isRLocal hE _ _ 3 (by norm_num) _ hloc₀
  have hr₀' := rowFinite_swap_of_isRLocal hE _ _ 3 (by norm_num) _ hloc₀
  have hrk' := rowFinite_swap_of_isRLocal hE _ _ 3 (by norm_num) _ hlock
  refine ⟨?_, ?_, fun A => ?_, fun μ hμ l hl => ?_⟩
  · unfold ResponseProperties.coboundaryLaplacian
    rw [edgeCoboundaryT_eq (meshAt_ne_zero hL k 0)]
    exact ((hKernels.1 _ _ _ hr₀).2 _ _ hr₀').2.1
  · rw [vertexCoboundaryT_eq (meshAt_ne_zero hL k k)]
    exact hrk'
  · exact coeffsOnEdges_transpose_coboundary hP hPt hKernels.1 hS hL hn hB₀ hX hs₀ hp₀ hw₀ hK₀
      hr₀ hr₀' A
  · exact edgeFormPairing_vertexCoboundary_eq_zero hS hL hn hBk hsk hbk hwk hKk μ hμ l hl
end YangMills.Construction.Tower.FormCoboundariesAtInfinity
end
