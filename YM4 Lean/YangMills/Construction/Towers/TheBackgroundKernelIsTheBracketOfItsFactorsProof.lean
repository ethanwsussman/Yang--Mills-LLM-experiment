import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescendProof
import YangMills.Construction.Towers.BracketOfTheFactorsDescendsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AssembledHessian
open YangMills.Construction.Matrices
open YangMills.Construction.LocalKernels YangMills.Construction.LocalKernels.Periodisation
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel compKernel swapKernel unitKernel
  RowFinite HasFiniteSupport BackgroundKernelFactors)
open YangMills.Construction.PeriodicOperators.RowFiniteKernels
section RowAndColumnFiniteness
variable {N N' N'' : Type}
def RowColFinite (T : KernelMatrix N N') : Prop :=
  RowFinite T ∧ RowFinite (swapKernel T)
theorem summable_mul_of_rowFinite {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) (ι' : N') :
    Summable fun ι => T ι' ι * f ι := by
  refine summable_of_hasFiniteSupport ((hT ι').subset ?_)
  intro ι hι h0
  apply hι
  have h0' : T ι' ι = 0 := by simpa using h0
  simp [h0']
theorem swapKernel_compKernel (T : KernelMatrix N' N'') (S : KernelMatrix N N') :
    swapKernel (compKernel T S) = compKernel (swapKernel S) (swapKernel T) := by
  funext a b
  exact tsum_congr fun _ => mul_comm _ _
theorem RowColFinite.swap {T : KernelMatrix N N'} (h : RowColFinite T) :
    RowColFinite (swapKernel T) := ⟨h.2, h.1⟩
theorem RowColFinite.comp (hA : ApplyComp) {T : KernelMatrix N' N''}
    {S : KernelMatrix N N'} (hT : RowColFinite T) (hS : RowColFinite S) :
    RowColFinite (compKernel T S) := by
  refine ⟨((hA N' N S hS.1).2 N'' T hT.1).2.1, ?_⟩
  rw [swapKernel_compKernel]
  exact ((hA N' N'' (swapKernel T) hT.2).2 N (swapKernel S) hS.2).2.1
theorem rowFinite_add {T T' : KernelMatrix N N'} (hT : RowFinite T) (hT' : RowFinite T') :
    RowFinite (T + T') := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.rowFinite_add <;> assumption
theorem rowFinite_smul {T : KernelMatrix N N'} (z : ℂ) (hT : RowFinite T) :
    RowFinite (z • T) := fun ι' =>
  (hT ι').subset fun ι h h0 => h (by
    have h0' : T ι' ι = 0 := by simpa using h0
    simp [h0'])
theorem RowColFinite.add {T T' : KernelMatrix N N'} (hT : RowColFinite T) (hT' : RowColFinite T') :
    RowColFinite (T + T') :=
  ⟨rowFinite_add hT.1 hT'.1, rowFinite_add hT.2 hT'.2⟩
theorem RowColFinite.smul {T : KernelMatrix N N'} (z : ℂ) (hT : RowColFinite T) :
    RowColFinite (z • T) :=
  ⟨rowFinite_smul z hT.1, rowFinite_smul z hT.2⟩
theorem RowColFinite.sub {T T' : KernelMatrix N N'} (hT : RowColFinite T) (hT' : RowColFinite T') :
    RowColFinite (T - T') := by
  have e : T - T' = T + (-1 : ℂ) • T' := by
    funext a b
    simp [sub_eq_add_neg]
  rw [e]
  exact hT.add (hT'.smul _)
theorem swapKernel_unitKernel : swapKernel (unitKernel N) = unitKernel N := by apply _root_.YangMills.Construction.LocalKernels.BracketDescent.swapKernel_unitKernel <;> assumption
theorem swapKernel_unit_sub_smul (z : ℂ) (A : KernelMatrix N N') :
    swapKernel (unitKernel N - z • compKernel (swapKernel A) A) =
      unitKernel N - z • compKernel (swapKernel A) A := by
  have e₁ : swapKernel (compKernel (swapKernel A) A) = compKernel (swapKernel A) A := by
    rw [swapKernel_compKernel]
    rfl
  funext a b
  have h₁ : unitKernel N b a = unitKernel N a b := congrFun (congrFun swapKernel_unitKernel a) b
  have h₂ : compKernel (swapKernel A) A b a = compKernel (swapKernel A) A a b :=
    congrFun (congrFun e₁ a) b
  show unitKernel N b a - z * compKernel (swapKernel A) A b a =
    unitKernel N a b - z * compKernel (swapKernel A) A a b
  rw [h₁, h₂]
theorem rowColFinite_unitKernel (hU : UnitLaws) : RowColFinite (unitKernel N) :=
  ⟨(hU N).1, by rw [swapKernel_unitKernel]; exact (hU N).1⟩
theorem applyKernel_indicator (T : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel T (fun j => unitKernel N j ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem applyKernel_unitKernel (f : N → ℂ) : applyKernel (unitKernel N) f = f := by apply _root_.YangMills.Construction.Tower.IterRelationsOnTorus.applyKernel_unit <;> assumption
theorem applyKernel_add {T T' : KernelMatrix N N'} (hT : RowFinite T)
    (hT' : RowFinite T') (f : N → ℂ) :
    applyKernel (T + T') f = applyKernel T f + applyKernel T' f := by
  funext ι'
  simp only [applyKernel, Pi.add_apply, add_mul]
  exact (summable_mul_of_rowFinite hT f ι').tsum_add (summable_mul_of_rowFinite hT' f ι')
theorem applyKernel_sub {T T' : KernelMatrix N N'} (hT : RowFinite T)
    (hT' : RowFinite T') (f : N → ℂ) :
    applyKernel (T - T') f = applyKernel T f - applyKernel T' f := by
  funext ι'
  simp only [applyKernel, Pi.sub_apply, sub_mul]
  exact (summable_mul_of_rowFinite hT f ι').tsum_sub (summable_mul_of_rowFinite hT' f ι')
theorem applyKernel_smul (z : ℂ) (T : KernelMatrix N N') (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.OperatorBlocksDescend.applyKernel_smul <;> assumption
theorem hasFiniteSupport_applyKernel {T : KernelMatrix N N'} (hT : RowColFinite T) {f : N → ℂ}
    (hf : HasFiniteSupport f) : HasFiniteSupport (applyKernel T f) := by
  refine (Set.Finite.biUnion hf fun i _ => hT.2 i).subset ?_
  intro ι' h
  by_contra hn
  apply h
  show ∑' ι, T ι' ι * f ι = 0
  refine (tsum_congr fun i => ?_).trans tsum_zero
  by_cases hi : f i = 0
  · simp [hi]
  · have : T ι' i = 0 := by
      by_contra h0
      exact hn (Set.mem_biUnion (show i ∈ Function.support f from hi) (show swapKernel T i ι' ≠ 0 from h0))
    simp [this]
end RowAndColumnFiniteness
section PauliCoefficients
theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
variable {σ : Type}
theorem ofPauliCoeffs_mem (c : Fin 3 × σ → ℂ) (i : σ) : ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs (c : Fin 3 × σ → ℂ) : toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem ofPauliCoeffs_toPauliCoeffs {X : σ → ComplexMatrix2} (hX : ∀ i, X i ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs X) = X := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
theorem hasFiniteSupp_ofPauliCoeffs_iff (c : Fin 3 × σ → ℂ) :
    HasFiniteSupp (ofPauliCoeffs c) ↔ (Function.support c).Finite := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.hasFiniteSupp_ofPauliCoeffs_iff <;> assumption
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hs : (Function.support fun ι => a ι * b ι).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ ι, a ι * b ι := by apply _root_.YangMills.Construction.Tower.FullSpace.IterRelations.traceFinsumPairing_ofPauliCoeffs <;> assumption
end PauliCoefficients
section CoefficientExtraction
variable {k : ℕ} (L : ℕ)
def colourPairEquiv (A : CellClass k) :
    Idx L A.colourPairs ≃ Fin 3 × Cell L k A.level A.cellType where
  toFun ι := ι.2
  invFun p := ⟨(), p⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem weightOf_colourPairs (A : CellClass k) (ι : Idx L A.colourPairs) :
    (A.colourPairs.toPeriodicData L).weightOf ι = 1 := rfl
theorem kernelT_colourPairs (A A' : CellClass k)
    (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)) :
    kernelT L A.colourPairs A'.colourPairs T = swapKernel T := by
  funext a b
  simp [kernelT, PeriodicOperators.wTranspose, weightOf_colourPairs, swapKernel]
theorem traceFinsumPairing_ofCoeffs (hP : OneLoop.PauliMatrixRelations) (A : CellClass k)
    {X : Cell L k A.level A.cellType → ComplexMatrix2} (hX : ∀ c, X c ∈ ComplexMatrix2.traceless)
    (hf : HasFiniteSupp X) (g : Idx L A.colourPairs → ℂ) :
    traceFinsumPairing X (CellClass.ofCoeffs L A g) =
      ∑' ι : Idx L A.colourPairs, toPauliCoeffs X ι.2 * g ι := by
  have hc : (Function.support (toPauliCoeffs X)).Finite := by
    rw [← hasFiniteSupp_ofPauliCoeffs_iff, ofPauliCoeffs_toPauliCoeffs hX]
    exact hf
  have hs : (Function.support fun p : Fin 3 × Cell L k A.level A.cellType =>
      toPauliCoeffs X p * g ⟨(), p⟩).Finite :=
    hc.subset fun p h h0 => h (by simp [show toPauliCoeffs X p = 0 from h0])
  have e : ∑' ι : Idx L A.colourPairs, toPauliCoeffs X ι.2 * g ι =
      ∑' p : Fin 3 × Cell L k A.level A.cellType, toPauliCoeffs X p * g ⟨(), p⟩ :=
    ((colourPairEquiv L A).symm.tsum_eq fun ι : Idx L A.colourPairs => toPauliCoeffs X ι.2 * g ι).symm
  rw [e, tsum_eq_finsum hs]
  conv_lhs => rw [← ofPauliCoeffs_toPauliCoeffs hX]
  exact traceFinsumPairing_ofPauliCoeffs hP _ _ hs
structure CoeffExtraction (A : CellClass k) : Prop where
  exists_coeffsOn_eq : ∀ g : Idx L A.colourPairs → ℂ,
    ∃ f ∈ (CellClass.fullSpace L A).complexSubmodule, CellClass.coeffsOn L A f = g
  coeffsOn_inj : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
    ∀ f' ∈ (CellClass.fullSpace L A).complexSubmodule,
    CellClass.coeffsOn L A f = CellClass.coeffsOn L A f' → f = f'
  cellFn_mem : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule, ∀ c,
    CellClass.cellFn L A f c ∈ ComplexMatrix2.traceless
  cellFn_add : ∀ f f' : (CellClass.fullSpace L A).index → ComplexMatrix2,
    CellClass.cellFn L A (f + f') = CellClass.cellFn L A f + CellClass.cellFn L A f'
  cellFn_smul : ∀ (z : ℂ) (f : (CellClass.fullSpace L A).index → ComplexMatrix2),
    CellClass.cellFn L A (z • f) = z • CellClass.cellFn L A f
variable {L}
namespace CoeffExtraction
variable {A : CellClass k}
theorem coeffsOn_add (r : CoeffExtraction L A) {f f' : (CellClass.fullSpace L A).index → ComplexMatrix2}
    (hf : f ∈ (CellClass.fullSpace L A).complexSubmodule)
    (hf' : f' ∈ (CellClass.fullSpace L A).complexSubmodule) :
    CellClass.coeffsOn L A (f + f') = CellClass.coeffsOn L A f + CellClass.coeffsOn L A f' := by
  funext ι
  show pauliCoeff ι.2.1 (CellClass.cellFn L A (f + f') ι.2.2) =
    pauliCoeff ι.2.1 (CellClass.cellFn L A f ι.2.2) + pauliCoeff ι.2.1 (CellClass.cellFn L A f' ι.2.2)
  rw [r.cellFn_add]
  exact pauliCoeff_add _ (r.cellFn_mem f hf _) (r.cellFn_mem f' hf' _)
theorem coeffsOn_smul (r : CoeffExtraction L A) (z : ℂ)
    {f : (CellClass.fullSpace L A).index → ComplexMatrix2}
    (hf : f ∈ (CellClass.fullSpace L A).complexSubmodule) :
    CellClass.coeffsOn L A (z • f) = z • CellClass.coeffsOn L A f := by
  funext ι
  show pauliCoeff ι.2.1 (CellClass.cellFn L A (z • f) ι.2.2) =
    z * pauliCoeff ι.2.1 (CellClass.cellFn L A f ι.2.2)
  rw [r.cellFn_smul]
  exact pauliCoeff_smul _ z (r.cellFn_mem f hf _)
theorem hasFiniteSupp_iff (r : CoeffExtraction L A) {f : (CellClass.fullSpace L A).index → ComplexMatrix2}
    (hf : f ∈ (CellClass.fullSpace L A).complexSubmodule) :
    HasFiniteSupp (CellClass.cellFn L A f) ↔ HasFiniteSupport (CellClass.coeffsOn L A f) := by
  have e := hasFiniteSupp_ofPauliCoeffs_iff (toPauliCoeffs (CellClass.cellFn L A f))
  rw [ofPauliCoeffs_toPauliCoeffs (r.cellFn_mem f hf)] at e
  rw [e]
  have e₂ : Function.support (CellClass.coeffsOn L A f) =
      (colourPairEquiv L A) ⁻¹' Function.support (toPauliCoeffs (CellClass.cellFn L A f)) := rfl
  unfold PeriodicOperators.HasFiniteSupport
  rw [e₂]
  constructor
  · intro h
    exact h.preimage (colourPairEquiv L A).injective.injOn
  · intro h
    have h' := h.image (colourPairEquiv L A)
    rwa [Set.image_preimage_eq _ (colourPairEquiv L A).surjective] at h'
end CoeffExtraction
end CoefficientExtraction
section VerticesAndEdges
variable {L k j : ℕ}
theorem coeffRepresentation_vertexClass (h : j ≤ k) : CoeffExtraction L (CellClass.vertexClass k j h) where
  exists_coeffsOn_eq g := ⟨CellClass.ofCoeffs L (CellClass.vertexClass k j h) g,
    fun i _ => ofPauliCoeffs_mem _ i, by
      funext ι
      exact congrFun (toPauliCoeffs_ofPauliCoeffs fun p => g ⟨(), p⟩) ι.2⟩
  coeffsOn_inj f hf f' hf' e := by
    have e' : toPauliCoeffs f = toPauliCoeffs f' := funext fun p => congrFun e ⟨(), p⟩
    have h₁ : ofPauliCoeffs (toPauliCoeffs f) = f :=
      ofPauliCoeffs_toPauliCoeffs fun i => hf i (mem_univ _)
    have h₂ : ofPauliCoeffs (toPauliCoeffs f') = f' :=
      ofPauliCoeffs_toPauliCoeffs fun i => hf' i (mem_univ _)
    rw [← h₁, ← h₂, e']
  cellFn_mem f hf c := hf c (mem_univ _)
  cellFn_add _ _ := rfl
  cellFn_smul _ _ := rfl
def formOfPauliCoeffs (c : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ) :
    FullSpace.Edge L k j → ComplexMatrix2 :=
  open Classical in
  FullSpace.extendOddly fun b =>
    if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
theorem restrict_formOfPauliCoeffs (c : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ) :
    FullSpace.restrictToPositiveEdges (formOfPauliCoeffs c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.FullSpace.IterRelations.restrict_edgeEval_ofCoeffs <;> assumption
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem formOfPauliCoeffs_mem (ha : 0 < meshAt L k j)
    (c : Fin 3 × FullSpace.PositiveEdge (meshAt L k j) → ℂ) :
    formOfPauliCoeffs c ∈ FullSpace.complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterRelations.edgePauliCoordinates_ofCoeffs_mem <;> assumption
theorem coeffRepresentation_edgeClass (ha : 0 < meshAt L k j) (h : j ≤ k) :
    CoeffExtraction L (CellClass.edgeClass k j h) where
  exists_coeffsOn_eq g := ⟨formOfPauliCoeffs fun p => g ⟨(), p⟩, formOfPauliCoeffs_mem ha _, by
    funext ι
    have e := restrict_formOfPauliCoeffs (L := L) (k := k) (j := j) fun p => g ⟨(), p⟩
    show toPauliCoeffs (FullSpace.restrictToPositiveEdges (formOfPauliCoeffs fun p => g ⟨(), p⟩)) ι.2 = g ι
    exact (congrFun (congrArg toPauliCoeffs e) ι.2).trans
      (congrFun (toPauliCoeffs_ofPauliCoeffs fun p => g ⟨(), p⟩) ι.2)⟩
  coeffsOn_inj f hf f' hf' e := by
    have e' : toPauliCoeffs (FullSpace.restrictToPositiveEdges f) =
        toPauliCoeffs (FullSpace.restrictToPositiveEdges f') :=
      funext fun p => congrFun e ⟨(), p⟩
    have h₁ : ofPauliCoeffs (toPauliCoeffs (FullSpace.restrictToPositiveEdges f)) =
        FullSpace.restrictToPositiveEdges f :=
      ofPauliCoeffs_toPauliCoeffs fun b => hf.1 b.1 b.2
    have h₂ : ofPauliCoeffs (toPauliCoeffs (FullSpace.restrictToPositiveEdges f')) =
        FullSpace.restrictToPositiveEdges f' :=
      ofPauliCoeffs_toPauliCoeffs fun b => hf'.1 b.1 b.2
    have e₃ : FullSpace.restrictToPositiveEdges f = FullSpace.restrictToPositiveEdges f' := by
      rw [← h₁, ← h₂, e']
    have e₄ : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented → f b = f' b := fun b hb =>
      congrFun e₃ ⟨b, hb⟩
    funext b
    rcases xor_isPositivelyOriented_opposite ha b with ⟨h₁, _⟩ | ⟨h₁, _⟩
    · exact e₄ b h₁
    · have a₁ := hf.2 b
      have a₂ := hf'.2 b
      have a₃ := e₄ _ h₁
      rw [a₁, a₂] at a₃
      exact neg_injective a₃
  cellFn_mem f hf c := hf.1 c.1 c.2
  cellFn_add _ _ := rfl
  cellFn_smul _ _ := rfl
theorem basisForm_eq (q : Fin 3 × FullSpace.PositiveEdge (meshAt L k j)) :
    FullSpace.basisForm (L := L) (k := k) (j := j) q.1 q.2 =
      formOfPauliCoeffs fun p => unitKernel _ p q := by
  classical
  unfold FullSpace.basisForm formOfPauliCoeffs
  refine congrArg (@FullSpace.extendOddly (meshAt L k j)) (funext fun b => ?_)
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    by_cases e : b = q.2.1
    · have e' : (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L k j)) = q.2 := Subtype.ext e
      rw [if_pos e, e']
      unfold ofPauliCoeffs
      rw [Finset.sum_eq_single q.1]
      · simp [unitKernel]
      · intro a _ ha
        have : unitKernel _ (a, q.2) q = 0 := if_neg fun h => ha (Prod.ext_iff.1 h).1
        beta_reduce
        rw [this, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg e]
      unfold ofPauliCoeffs
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      have : unitKernel _ (a, (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L k j))) q = 0 :=
        if_neg fun h => e (congrArg Subtype.val (Prod.ext_iff.1 h).2)
      beta_reduce
      rw [this, zero_smul]
  · rw [dif_neg hb, if_neg]
    intro e
    exact hb (e ▸ q.2.2)
theorem toPauliCoeffs_basisForm (q : Fin 3 × FullSpace.PositiveEdge (meshAt L k j)) :
    toPauliCoeffs (FullSpace.restrictToPositiveEdges
        (FullSpace.basisForm (L := L) (k := k) (j := j) q.1 q.2)) =
      fun p => unitKernel _ p q := by
  rw [basisForm_eq, restrict_formOfPauliCoeffs, toPauliCoeffs_ofPauliCoeffs]
theorem basisForm_mem (ha : 0 < meshAt L k j) (q : Fin 3 × FullSpace.PositiveEdge (meshAt L k j)) :
    FullSpace.basisForm (L := L) (k := k) (j := j) q.1 q.2 ∈
      FullSpace.complexEdgeForms (meshAt L k j) := by
  rw [basisForm_eq q]
  exact formOfPauliCoeffs_mem ha _
variable (L)
theorem coeffsOn_basisForm (h : j ≤ k) (ι : Idx L (CellClass.edgeClass k j h).colourPairs) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h) (FullSpace.basisForm ι.2.1 ι.2.2) =
      fun i => unitKernel _ i ι := by
  classical
  funext i
  have e := toPauliCoeffs_basisForm (L := L) (k := k) (j := j) ι.2
  refine (congrFun e i.2).trans ?_
  by_cases hi : i = ι
  · subst hi
    have a : unitKernel (Idx L (CellClass.edgeClass k j h).colourPairs) i i = 1 := if_pos rfl
    exact (if_pos rfl).trans a.symm
  · have hi' : ¬ (colourPairEquiv L _ i = colourPairEquiv L _ ι) := fun e =>
      hi ((colourPairEquiv L _).injective e)
    have e₁ : unitKernel (Idx L (CellClass.edgeClass k j h).colourPairs) i ι = 0 := if_neg hi
    exact (if_neg hi').trans e₁.symm
end VerticesAndEdges
section KernelActions
variable {k : ℕ} (L : ℕ)
structure ActsByKernel (A A' : CellClass k)
    (m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2)
    (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)) : Prop where
  maps_mem : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
    m f ∈ (CellClass.fullSpace L A').complexSubmodule
  coeffsOn_apply : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
    CellClass.coeffsOn L A' (m f) = applyKernel T (CellClass.coeffsOn L A f)
  rowColFinite : RowColFinite T
variable {L} {A A' A'' : CellClass k}
namespace ActsByKernel
variable {m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
    (CellClass.fullSpace L A').index → ComplexMatrix2}
  {T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
theorem comp {m' : ((CellClass.fullSpace L A').index → ComplexMatrix2) →
      (CellClass.fullSpace L A'').index → ComplexMatrix2}
    {T' : KernelMatrix (Idx L A'.colourPairs) (Idx L A''.colourPairs)}
    (hA : ApplyComp) (h : ActsByKernel L A A' m T) (h' : ActsByKernel L A' A'' m' T') :
    ActsByKernel L A A'' (fun f => m' (m f)) (compKernel T' T) where
  maps_mem f hf := h'.maps_mem _ (h.maps_mem f hf)
  coeffsOn_apply f hf := by
    rw [h'.coeffsOn_apply _ (h.maps_mem f hf), h.coeffsOn_apply f hf]
    exact ((((hA _ _ T h.rowColFinite.1).2 _ T' h'.rowColFinite.1).2.2 _).2.2).symm
  rowColFinite := h'.rowColFinite.comp hA h.rowColFinite
theorem hasFiniteSupp (r : CoeffExtraction L A) (r' : CoeffExtraction L A') (h : ActsByKernel L A A' m T)
    {f : (CellClass.fullSpace L A).index → ComplexMatrix2}
    (hf : f ∈ (CellClass.fullSpace L A).complexSubmodule)
    (hs : HasFiniteSupp (CellClass.cellFn L A f)) :
    HasFiniteSupp (CellClass.cellFn L A' (m f)) := by
  rw [r'.hasFiniteSupp_iff (h.maps_mem f hf), h.coeffsOn_apply f hf]
  exact hasFiniteSupport_applyKernel h.rowColFinite ((r.hasFiniteSupp_iff hf).1 hs)
theorem kernel_eq_coeffsOn (h : ActsByKernel L A A' m T)
    {e : (CellClass.fullSpace L A).index → ComplexMatrix2}
    (he : e ∈ (CellClass.fullSpace L A).complexSubmodule) {ι : Idx L A.colourPairs}
    (hr : CellClass.coeffsOn L A e = fun i => unitKernel _ i ι) (s : Idx L A'.colourPairs) :
    T s ι = CellClass.coeffsOn L A' (m e) s := by
  rw [h.coeffsOn_apply e he, hr, applyKernel_indicator]
end ActsByKernel
theorem kernel_unique_of_represented (r : CoeffExtraction L A)
    {m : (CellClass.fullSpace L A).complexSubmodule → (CellClass.fullSpace L A').index → ComplexMatrix2}
    {T T' : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    (h : IsRepresentedOnPairs L A A' m T) (h' : IsRepresentedOnPairs L A A' m T') : T = T' := by
  funext ι' ι
  obtain ⟨f, hf, hr⟩ := r.exists_coeffsOn_eq fun i => unitKernel _ i ι
  have c : applyKernel T (CellClass.coeffsOn L A f) ι' = applyKernel T' (CellClass.coeffsOn L A f) ι' :=
    congrFun ((h ⟨f, hf⟩).2.symm.trans (h' ⟨f, hf⟩).2) ι'
  rwa [hr, applyKernel_indicator, applyKernel_indicator] at c
theorem rowColFinite_of_isRLocal (hE : LocalKernelFacts (k := k) L) {R : ℝ} (hR : 0 ≤ R)
    {T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    (hT : IsRLocal L A.colourPairs A'.colourPairs R T) : RowColFinite T := by
  have h₁ := hE A.colourPairs A'.colourPairs R hR T hT
  have h₂ := hE A'.colourPairs A.colourPairs R hR _ h₁.2.2.1
  rw [kernelT_colourPairs] at h₂
  refine ⟨fun ι' => ?_, fun ι => ?_⟩
  · exact (h₁.1 1 ι').subset fun ι h => by simpa using h
  · exact (h₂.1 1 ι).subset fun ι' h => by simpa using h
theorem actsByKernel_of_periodizes {n : ℕ} (hE : LocalKernelFacts (k := k) L) (r : CoeffExtraction L A)
    {R : ℝ} (hR : 0 ≤ R)
    {mW : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n A).index → ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → ComplexMatrix2}
    (h : Periodizes L n A A' R mW mT) :
    IsRLocal L A.colourPairs A'.colourPairs R (pairKernelOfMap L A A' mW) ∧
      ActsByKernel L A A' mW (pairKernelOfMap L A A' mW) := by
  obtain ⟨T, m, hl, hg, -⟩ := h
  have hε : IsRepresentedOnPairs L A A' (fun f => mW f) (pairKernelOfMap L A A' mW) :=
    Classical.epsilon_spec (p := fun T => IsRepresentedOnPairs L A A' (fun f => mW f) T) ⟨T, hg⟩
  have e : pairKernelOfMap L A A' mW = T := kernel_unique_of_represented r hε hg
  rw [e]
  exact ⟨hl, fun f hf => (hg ⟨f, hf⟩).1, fun f hf => (hg ⟨f, hf⟩).2, rowColFinite_of_isRLocal hE hR hl⟩
theorem ActsByKernel.transposeOfValues (hB : PairBracketTranspose (k := k) L)
    (hA : A.cellType ≠ .face) (hA' : A'.cellType ≠ .face) (r' : CoeffExtraction L A') {R : ℝ}
    (hR : 0 ≤ R)
    {m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    {T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    (hT : IsRLocal L A.colourPairs A'.colourPairs R T) (h : ActsByKernel L A A' m T) :
    ActsByKernel L A' A (PairedFunctionSpace.transposeOfValues (CellClass.fullSpace L A)
      (CellClass.fullSpace L A') m) (swapKernel T) := by
  obtain ⟨mL, m', g₁, g₂, -, -, e⟩ := (hB A A' hA hA').2 R hR T hT
  have hval : ∀ f : (CellClass.fullSpace L A).complexSubmodule,
      ((mL f : (CellClass.fullSpace L A').complexSubmodule) :
        (CellClass.fullSpace L A').index → ComplexMatrix2) = m f := fun f =>
    r'.coeffsOn_inj _ (mL f).2 _ (h.maps_mem f.1 f.2) ((g₁ f).2.trans (h.coeffsOn_apply f.1 f.2).symm)
  have hc : PairedFunctionSpace.linearOfValues (CellClass.fullSpace L A)
      (CellClass.fullSpace L A') m = mL := by
    have hs := Classical.epsilon_spec
      (p := fun T : (CellClass.fullSpace L A).complexSubmodule →ₗ[ℂ]
        (CellClass.fullSpace L A').complexSubmodule =>
          ∀ f : (CellClass.fullSpace L A).complexSubmodule,
            (T f : (CellClass.fullSpace L A').index → ComplexMatrix2) = m f) ⟨mL, hval⟩
    exact LinearMap.ext fun f => Subtype.ext ((hs f).trans (hval f).symm)
  have ev : ∀ (g : (CellClass.fullSpace L A').index → ComplexMatrix2)
      (hg : g ∈ (CellClass.fullSpace L A').complexSubmodule),
      PairedFunctionSpace.transposeOfValues (CellClass.fullSpace L A)
        (CellClass.fullSpace L A') m g = (m' ⟨g, hg⟩).1 := by
    intro g hg
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos hg, hc, e]
  refine ⟨fun g hg => ?_, fun g hg => ?_, h.rowColFinite.swap⟩
  · rw [ev g hg]
    exact (m' _).2
  · rw [ev g hg, ← kernelT_colourPairs]
    exact (g₂ ⟨g, hg⟩).2
theorem ActsByKernel.id_add (hU : UnitLaws) (r : CoeffExtraction L A)
    {m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A).index → ComplexMatrix2}
    {T : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs)} (h : ActsByKernel L A A m T) :
    ActsByKernel L A A (fun f => f + m f) (unitKernel _ + T) where
  maps_mem f hf := Submodule.add_mem _ hf (h.maps_mem f hf)
  coeffsOn_apply f hf := by
    rw [r.coeffsOn_add hf (h.maps_mem f hf),
      applyKernel_add (rowColFinite_unitKernel hU).1 h.rowColFinite.1,
      applyKernel_unitKernel, h.coeffsOn_apply f hf]
  rowColFinite := (rowColFinite_unitKernel hU).add h.rowColFinite
theorem real_smul_eq_complex_smul {ι : Type} (c : ℝ) (f : ι → ComplexMatrix2) :
    c • f = (c : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
theorem ActsByKernel.id_sub_smul (hU : UnitLaws) (r : CoeffExtraction L A)
    {m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A).index → ComplexMatrix2}
    {T : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs)} (h : ActsByKernel L A A m T)
    (c : ℝ) (z : ℂ) (hz : z = (c : ℂ)) :
    ActsByKernel L A A (fun f => f - c • m f) (unitKernel _ - z • T) := by
  have e : ∀ f : (CellClass.fullSpace L A).index → ComplexMatrix2,
      f - c • m f = f + (-z) • m f := fun f => by
    rw [real_smul_eq_complex_smul, hz, neg_smul, sub_eq_add_neg]
  have hm : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
      (-z) • m f ∈ (CellClass.fullSpace L A).complexSubmodule := fun f hf =>
    Submodule.smul_mem _ _ (h.maps_mem f hf)
  refine ⟨fun f hf => ?_, fun f hf => ?_,
    (rowColFinite_unitKernel hU).sub (h.rowColFinite.smul z)⟩
  · rw [e]
    exact Submodule.add_mem _ hf (hm f hf)
  · rw [e, r.coeffsOn_add hf (hm f hf), r.coeffsOn_smul _ (h.maps_mem f hf), h.coeffsOn_apply f hf,
      applyKernel_sub (rowColFinite_unitKernel hU).1 (h.rowColFinite.smul z).1, applyKernel_unitKernel,
      applyKernel_smul, neg_smul, sub_eq_add_neg]
end KernelActions
section KernelEntries
variable {L k : ℕ}
theorem kernel_eq_complexHessianKernel (ha : 0 < meshAt L k 0) {V : FullSpace.Edge L k 0 → ComplexMatrix2}
    {T : KernelMatrix (Idx L (edgesAtZero k).colourPairs) (Idx L (edgesAtZero k).colourPairs)}
    (h : ActsByKernel L (edgesAtZero k) (edgesAtZero k) (FullSpace.complexHessianOperator V) T)
    (ι' ι : Idx L (edgesAtZero k).colourPairs) :
    T ι' ι = FullSpace.complexHessianKernel V ι'.2 ι.2 := by
  have he : FullSpace.basisForm (L := L) (k := k) (j := 0) ι.2.1 ι.2.2 ∈
      FullSpace.complexEdgeForms (meshAt L k 0) := basisForm_mem ha ι.2
  refine (h.kernel_eq_coeffsOn he (coeffsOn_basisForm L (Nat.zero_le k) ι) ι').trans ?_
  have e : FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator V
      (FullSpace.basisForm (L := L) (k := k) (j := 0) ι.2.1 ι.2.2)) =
      ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel V)
        (toPauliCoeffs (FullSpace.restrictToPositiveEdges
          (FullSpace.basisForm (L := L) (k := k) (j := 0) ι.2.1 ι.2.2)))) :=
    restrict_formOfPauliCoeffs _
  refine (congrFun (congrArg toPauliCoeffs e) ι'.2).trans ?_
  rw [toPauliCoeffs_ofPauliCoeffs]
  exact (congrFun (congrArg (applyKernel (FullSpace.complexHessianKernel V))
    (toPauliCoeffs_basisForm (L := L) (k := k) (j := 0) ι.2)) ι'.2).trans
    (applyKernel_indicator _ _ _)
theorem rawHessianKernel_eq_assembled (hP : OneLoop.PauliMatrixRelations)
    (hPr : PeriodicOperators.RowFiniteKernels.Claim)
    (ha : 0 < meshAt L k 0)
    (V J : FullSpace.Edge L k 0 → ComplexMatrix2) (μ : FullSpace.Edge L k k → ComplexMatrix2)
    (F : BackgroundKernelFactors (Idx L (verticesAtZero k).colourPairs)
      (Idx L (edgesAtZero k).colourPairs) (Idx L (CellClass.vertexClass k k le_rfl).colourPairs))
    (hσ : ActsByKernel L (edgesAtZero k) (verticesAtZero k) (FullSpace.gaugeParam V) F.sigma)
    (hD : ActsByKernel L (verticesAtZero k) (edgesAtZero k) (FullSpace.covDiff V) F.diff)
    (hDt : ActsByKernel L (edgesAtZero k) (verticesAtZero k) (FullSpace.covDiffTranspose L k V)
      (swapKernel F.diff))
    (hav : ActsByKernel L (verticesAtZero k) (CellClass.vertexClass k k le_rfl)
      (FullSpace.iterAdjointCubeAverage L k V k) F.avg)
    (hat : ActsByKernel L (CellClass.vertexClass k k le_rfl) (verticesAtZero k)
      (FullSpace.iterAverageTranspose L k V) (swapKernel F.avg))
    (hfV : RowColFinite F.brk) (hfQ : RowColFinite F.quad)
    (hact : ∀ ι' ι, F.hess ι' ι = FullSpace.complexHessianKernel V
      (show Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) from ι'.2)
      (show Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) from ι.2))
    (hsc : F.scale = (((L : ℝ) ^ (4 * k) : ℝ) : ℂ))
    (hV : ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k 0), HasFiniteSupp l →
      ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k 0), HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
        traceFinsumPairing l (CellClass.ofCoeffs L (verticesAtZero k)
            (applyKernel F.brk (CellClass.coeffsOn L (edgesAtZero k) B))) =
          FullSpace.finiteEdgePairing J (FullSpace.levelBracketTerm V l B))
    (hQ : ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k 0),
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
      ∀ B' ∈ FullSpace.complexEdgeForms (meshAt L k 0),
        HasFiniteSupp (FullSpace.restrictToPositiveEdges B') →
        traceFinsumPairing (FullSpace.restrictToPositiveEdges B) (CellClass.ofCoeffs L (edgesAtZero k)
            (applyKernel F.quad (CellClass.coeffsOn L (edgesAtZero k) B'))) =
          traceFinsumPairing (FullSpace.restrictToPositiveEdges μ)
            (FullSpace.AsDifferentials.complexQuadraticTerm L k V B B'))
    (ι' ι : Idx L (edgesAtZero k).colourPairs) :
    FullSpace.FieldValueFunctions.rawHessianKernel V J μ ι'.2 ι.2 = F.assembled ι' ι := by
  have hA := hPr.1
  have hAs := hPr.2.1
  have hU := hPr.2.2.1
  have r₀ : CoeffExtraction L (verticesAtZero k) := coeffRepresentation_vertexClass _
  have rb : CoeffExtraction L (edgesAtZero k) := coeffRepresentation_edgeClass ha _
  have hG : ActsByKernel L (verticesAtZero k) (verticesAtZero k)
      (fun l : FullSpace.Vertex L k 0 → ComplexMatrix2 => l - ((L : ℝ) ^ (4 * k)) •
        FullSpace.iterAverageTranspose L k V
        (FullSpace.iterAdjointCubeAverage L k V k l)) F.complementKernel :=
    (hav.comp hA hat).id_sub_smul hU r₀ ((L : ℝ) ^ (4 * k)) F.scale hsc
  have hg : ActsByKernel L (edgesAtZero k) (verticesAtZero k) (FullSpace.gaugeFixingTerm L k V)
      (compKernel F.complementKernel (swapKernel F.diff)) := hDt.comp hA hG
  have hDσ := hσ.comp hA hD
  have hτ : ActsByKernel L (edgesAtZero k) (edgesAtZero k) (FullSpace.shiftedForm V) F.tauKernel :=
    hDσ.id_add hU rb
  let E : Idx L (edgesAtZero k).colourPairs → FullSpace.Edge L k 0 → ComplexMatrix2 := fun i =>
    FullSpace.basisForm (L := L) (k := k) (j := 0) i.2.1 i.2.2
  have he : ∀ i, E i ∈ FullSpace.complexEdgeForms (meshAt L k 0) := fun i =>
    basisForm_mem ha i.2
  have hr : ∀ i, CellClass.coeffsOn L (edgesAtZero k) (E i) = fun j => unitKernel _ j i :=
    fun i => coeffsOn_basisForm L (Nat.zero_le k) i
  have hfin : ∀ i, HasFiniteSupp (FullSpace.restrictToPositiveEdges (E i)) := fun i => by
    refine (rb.hasFiniteSupp_iff (he i)).2 ?_
    rw [hr i]
    refine (Set.finite_singleton i).subset fun j hj => ?_
    by_contra hn
    exact hj (if_neg hn)
  have hb : ∀ B B', B ∈ FullSpace.complexEdgeForms (meshAt L k 0) →
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B) →
      B' ∈ FullSpace.complexEdgeForms (meshAt L k 0) →
      HasFiniteSupp (FullSpace.restrictToPositiveEdges B') →
      ∑' s, CellClass.coeffsOn L (verticesAtZero k) (FullSpace.gaugeParam V B) s *
        applyKernel F.brk (CellClass.coeffsOn L (edgesAtZero k) B') s =
      FullSpace.finiteEdgePairing J (FullSpace.levelBracketTerm V (FullSpace.gaugeParam V B) B') := by
    intro B B' hB hBf hB' hB'f
    rw [← hV _ (hσ.maps_mem B hB) (hσ.hasFiniteSupp rb r₀ hB hBf) B' hB' hB'f]
    exact (traceFinsumPairing_ofCoeffs L hP (verticesAtZero k) (r₀.cellFn_mem _ (hσ.maps_mem B hB))
      (hσ.hasFiniteSupp rb r₀ hB hBf) _).symm
  have t₂ : compKernel (swapKernel F.sigma) F.brk ι' ι =
      FullSpace.finiteEdgePairing J (FullSpace.levelBracketTerm V (FullSpace.gaugeParam V (E ι'))
        (E ι)) := by
    rw [← hb _ _ (he ι') (hfin ι') (he ι) (hfin ι), hr ι]
    refine tsum_congr fun s => ?_
    rw [applyKernel_indicator]
    exact congrArg (· * F.brk s ι) (hσ.kernel_eq_coeffsOn (he ι') (hr ι') s)
  have t₃ : compKernel (compKernel (swapKernel F.sigma) F.brk) (compKernel F.diff F.sigma) ι' ι =
      FullSpace.finiteEdgePairing J (FullSpace.levelBracketTerm V (FullSpace.gaugeParam V (E ι'))
        (FullSpace.covDiff V (FullSpace.gaugeParam V (E ι)))) := by
    have e₃ := (hAs _ _ _ _ (swapKernel F.sigma) F.brk
      (compKernel F.diff F.sigma) hσ.rowColFinite.2 hfV.1).2.2.2
    rw [e₃, ← hb _ _ (he ι') (hfin ι') (hDσ.maps_mem _ (he ι))
      (hDσ.hasFiniteSupp rb rb (he ι) (hfin ι))]
    refine tsum_congr fun s => ?_
    have c₁ := hσ.kernel_eq_coeffsOn (he ι') (hr ι') s
    have c₂ : (fun b => compKernel F.diff F.sigma b ι) =
        CellClass.coeffsOn L (edgesAtZero k) (FullSpace.covDiff V (FullSpace.gaugeParam V (E ι))) :=
      funext (hDσ.kernel_eq_coeffsOn (he ι) (hr ι))
    rw [← c₂]
    exact congrArg (· * compKernel F.brk (compKernel F.diff F.sigma) s ι) c₁
  have t₄ : compKernel (compKernel (swapKernel F.tauKernel) F.quad) F.tauKernel ι' ι =
      traceFinsumPairing (FullSpace.restrictToPositiveEdges μ)
        (FullSpace.AsDifferentials.complexQuadraticTerm L k V
          (FullSpace.shiftedForm V (E ι')) (FullSpace.shiftedForm V (E ι))) := by
    have e₄ := (hAs _ _ _ _ (swapKernel F.tauKernel) F.quad F.tauKernel
      hτ.rowColFinite.2 hfQ.1).2.2.2
    rw [e₄, ← hQ _ (hτ.maps_mem _ (he ι')) (hτ.hasFiniteSupp rb rb (he ι') (hfin ι')) _
      (hτ.maps_mem _ (he ι)) (hτ.hasFiniteSupp rb rb (he ι) (hfin ι))]
    refine Eq.trans ?_ (traceFinsumPairing_ofCoeffs L hP (edgesAtZero k)
      (rb.cellFn_mem _ (hτ.maps_mem _ (he ι'))) (hτ.hasFiniteSupp rb rb (he ι') (hfin ι')) _).symm
    refine tsum_congr fun s => ?_
    have c₁ := hτ.kernel_eq_coeffsOn (he ι') (hr ι') s
    have c₂ : (fun b => F.tauKernel b ι) =
        CellClass.coeffsOn L (edgesAtZero k) (FullSpace.shiftedForm V (E ι)) :=
      funext (hτ.kernel_eq_coeffsOn (he ι) (hr ι))
    rw [← c₂]
    exact congrArg (· * compKernel F.quad F.tauKernel s ι) c₁
  have hsym : swapKernel F.complementKernel = F.complementKernel :=
    swapKernel_unit_sub_smul F.scale F.avg
  have t₅ : compKernel (compKernel F.diff F.complementKernel)
      (compKernel F.complementKernel (swapKernel F.diff)) ι' ι =
      traceFinsumPairing (FullSpace.gaugeFixingTerm L k V (E ι'))
        (FullSpace.gaugeFixingTerm L k V (E ι)) := by
    have e₁ : compKernel F.diff F.complementKernel =
        swapKernel (compKernel F.complementKernel (swapKernel F.diff)) := by
      rw [swapKernel_compKernel, hsym]
      rfl
    have m₁ := hg.maps_mem _ (he ι')
    have m₂ := hg.maps_mem _ (he ι)
    have e₂ : CellClass.ofCoeffs L (verticesAtZero k)
        (CellClass.coeffsOn L (verticesAtZero k) (FullSpace.gaugeFixingTerm L k V (E ι))) =
        FullSpace.gaugeFixingTerm L k V (E ι) :=
      ofPauliCoeffs_toPauliCoeffs (r₀.cellFn_mem _ m₂)
    have e₃ := traceFinsumPairing_ofCoeffs L hP (verticesAtZero k) (r₀.cellFn_mem _ m₁)
      (hg.hasFiniteSupp rb r₀ (he ι') (hfin ι'))
      (CellClass.coeffsOn L (verticesAtZero k) (FullSpace.gaugeFixingTerm L k V (E ι)))
    rw [e₂] at e₃
    refine Eq.trans ?_ e₃.symm
    rw [e₁]
    refine tsum_congr fun s => ?_
    have c₁ := hg.kernel_eq_coeffsOn (he ι') (hr ι') s
    have c₂ := hg.kernel_eq_coeffsOn (he ι) (hr ι) s
    show compKernel F.complementKernel (swapKernel F.diff) s ι' *
      compKernel F.complementKernel (swapKernel F.diff) s ι = _
    rw [c₁, c₂]
    rfl
  show FullSpace.FieldValueFunctions.hessianBilinear V J μ (E ι') (E ι) = _
  have h₁ := hact ι' ι
  have h₀ : FullSpace.complexHessianKernel V
      (show Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) from ι'.2)
      (show Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) from ι.2) =
      FullSpace.complexActionHessian V (E ι') (E ι) := rfl
  simp only [BackgroundKernelFactors.assembled, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h₁, h₀, t₂, t₃, t₄, t₅]
  simp only [FullSpace.FieldValueFunctions.hessianBilinear,
    FullSpace.FieldValueFunctions.sourceBilinear, FullSpace.backgroundForm]
  ring
end KernelEntries
theorem hessianKernelIsAssembledFactors (hP : OneLoop.PauliMatrixRelations)
    (hPr : PeriodicOperators.RowFiniteKernels.Claim)
    (hS : LocalKernels.Periodisation.PeriodisationHolds) : HessianKernelIsAssembledFactors := by
  intro L hL k hk n hn U hU J hJ μ hμ
  obtain ⟨-, -, -, hE, -, hB, -, hAct, hAvg⟩ := hS L hL k n hn
  obtain ⟨-, hDd, hAd, hCd⟩ := hAct 0 (Nat.zero_le k) U hU.1 J hJ
  obtain ⟨-, -, hIt, hEx, hSec⟩ := (hAvg hk U hU.1).2 hU μ hμ
  obtain ⟨-, -, hAv, hDr⟩ := hIt k le_rfl hk
  have hpos : ∀ j, 0 < meshAt L k j := fun j => by
    have h0 : 0 < L := by
      have := hL.2
      omega
    exact zpow_pos (by exact_mod_cast h0) _
  have hA := hPr.1
  have r₀ : CoeffExtraction L (verticesAtZero k) := coeffRepresentation_vertexClass _
  have rb : CoeffExtraction L (edgesAtZero k) := coeffRepresentation_edgeClass (hpos 0) _
  have rk : CoeffExtraction L (CellClass.vertexClass k k le_rfl) := coeffRepresentation_vertexClass _
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  obtain ⟨lD, cD⟩ := actsByKernel_of_periodizes hE r₀ h2 hDd
  obtain ⟨-, cA⟩ := actsByKernel_of_periodizes hE rb h2 hAd
  obtain ⟨lAv, cAv⟩ := actsByKernel_of_periodizes hE r₀ h6 hAv
  obtain ⟨-, cDr⟩ := actsByKernel_of_periodizes hE rb h6 hDr
  obtain ⟨-, cEx⟩ := actsByKernel_of_periodizes hE rk h6 hEx
  obtain ⟨⟨T₁, hT₁, -⟩, ⟨M₁, hM₁, -⟩, hC⟩ := hCd
  have hε₁ : IsBracketKernel L n k 0 (Nat.zero_le k) U J
      (Classical.epsilon (IsBracketKernel L n k 0 (Nat.zero_le k) U J)) :=
    Classical.epsilon_spec ⟨T₁, hT₁⟩
  obtain ⟨⟨T₂, hT₂, -⟩, ⟨M₂, hM₂, -⟩, hQ⟩ := hSec
  have hε₂ : IsQuadraticKernel L n k U μ (Classical.epsilon (IsQuadraticKernel L n k U μ)) :=
    Classical.epsilon_spec ⟨T₂, hT₂⟩
  funext ι' ι
  exact rawHessianKernel_eq_assembled hP hPr (hpos 0) _ _ _ (fullFactors L n k U J μ)
    (cDr.comp hA cEx) cD
    (cD.transposeOfValues hB (by simp [verticesAtZero, CellClass.vertexClass])
      (by simp [edgesAtZero, CellClass.edgeClass]) rb h2 lD)
    cAv
    (cAv.transposeOfValues hB (by simp [verticesAtZero, CellClass.vertexClass])
      (by simp [CellClass.vertexClass]) rk h6 lAv)
    (rowColFinite_of_isRLocal hE h2 (hC _ M₁ hε₁ hM₁).1)
    (rowColFinite_of_isRLocal hE h6 (hQ _ M₂ hε₂ hM₂).1)
    (fun a b => kernel_eq_complexHessianKernel (hpos 0) cA a b) rfl hε₁ hε₂ ι' ι
end YangMills.Construction.Tower.AssembledHessian
end
