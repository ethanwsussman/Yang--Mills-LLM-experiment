import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminantsProof
import YangMills.Construction.Towers.TheTwoOperatorsAtOneOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.IdentityOperatorsTorus
open Set
open Matrices
open PairedFunctionSpace (linearOfValues transposeOfValues)
section Matrices
theorem traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := hX.2
theorem halfTrace_mul_im_eq_zero {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    (ComplexMatrix2.halfTrace (X * Y)).im = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.halfTrace_mul_im <;> assumption
def hermitianPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def skewPart (X : ComplexMatrix2) : ComplexMatrix2 := (-Complex.I / 2) • (X - X.conjTranspose)
theorem hermitianPart_add_I_smul_skewPart (X : ComplexMatrix2) :
    hermitianPart X + Complex.I • skewPart X = X := by
  simp only [hermitianPart, skewPart, smul_smul]
  have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  rw [this, ← smul_add]
  have hTwo : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [hTwo, smul_smul]
  norm_num
theorem fullTrace_conjTranspose_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.RescaledTrivialStepsProof.fullTrace_conjTranspose_of_traceless <;> assumption
theorem hermitianPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    hermitianPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : ComplexMatrix2.fullTrace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [hermitianPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm X.conjTranspose X]
    simp
  · simp only [hermitianPart, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add]
    have t' := fullTrace_conjTranspose_eq_zero hX
    simp only [ComplexMatrix2.fullTrace] at t t'
    rw [t, t']
    simp
theorem skewPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    skewPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have t : ComplexMatrix2.fullTrace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp only [skewPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]
      ring
    rw [this, neg_smul, ← smul_neg, neg_sub]
  · simp only [skewPart, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub]
    have t' := fullTrace_conjTranspose_eq_zero hX
    simp only [ComplexMatrix2.fullTrace] at t t'
    rw [t, t']
    simp
end Matrices
section Pairing
variable {ι : Type}
theorem pairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_comm <;> assumption
theorem pairing_eq_sum [Fintype ι] (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = ∑ i, ComplexMatrix2.halfTrace (f i * g i) :=
  finsum_eq_sum_of_fintype _
variable [Finite ι]
theorem pairing_im_eq_zero {f g : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) : (traceFinsumPairing f g).im = 0 := by
  have := Fintype.ofFinite ι
  rw [pairing_eq_sum, Complex.im_sum]
  exact Finset.sum_eq_zero fun i _ => halfTrace_mul_im_eq_zero (hf i) (hg i)
theorem pairing_add (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + h) = traceFinsumPairing f g + traceFinsumPairing f h := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_add_right <;> assumption
theorem pairing_smul (c : ℂ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (c • g) = c * traceFinsumPairing f g := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_smul_right <;> assumption
theorem pairing_self_re_nonneg {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_self_re_nonneg <;> assumption
theorem eq_zero_of_pairing_self_re {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (h : (traceFinsumPairing f f).re = 0) : f = 0 := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.eq_zero_of_traceFinsumPairing_self <;> assumption
theorem mem_hermitianTraceless_of_pairing_skewPart_im {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.traceless)
    (h : (traceFinsumPairing (fun i => skewPart (f i)) f).im = 0) :
    ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless := by
  set r : ι → ComplexMatrix2 := fun i => hermitianPart (f i) with hr
  set s : ι → ComplexMatrix2 := fun i => skewPart (f i) with hs
  have hrMem : ∀ i, r i ∈ ComplexMatrix2.hermitianTraceless := fun i => hermitianPart_mem (hf i)
  have hsMem : ∀ i, s i ∈ ComplexMatrix2.hermitianTraceless := fun i => skewPart_mem (hf i)
  have hSplit : f = r + Complex.I • s := by
    funext i
    exact (hermitianPart_add_I_smul_skewPart (f i)).symm
  have hExpand : traceFinsumPairing s f =
      traceFinsumPairing s r + Complex.I * traceFinsumPairing s s := by
    conv_lhs => rw [hSplit]
    rw [pairing_add, pairing_smul]
  rw [hExpand] at h
  have imCross := pairing_im_eq_zero hsMem hrMem
  have imSelf := pairing_im_eq_zero hsMem hsMem
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, imCross, imSelf] at h
  have hZero : s = 0 := eq_zero_of_pairing_self_re hsMem (by linarith)
  intro i
  have hParts := hermitianPart_add_I_smul_skewPart (f i)
  have hSkew : skewPart (f i) = 0 := congrFun hZero i
  rw [hSkew, smul_zero, add_zero] at hParts
  rw [← hParts]
  exact hermitianPart_mem (hf i)
end Pairing
section Difference
open TwoOperators
open CovDiffTransposes
variable {L n : ℕ}
theorem trivialField_mem_compact :
    trivialField L n 0 0 ∈ fieldsIn L n 0 0 PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.identityField_mem <;> assumption
theorem trivialField_mem_complex :
    trivialField L n 0 0 ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.DeltaSharedProofs.p33329 <;> assumption
theorem edgeForm_apply_mem {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n 0 0)
    (b : Edge L n 0 0) : B b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.DeltaSharedProofs.p500934 <;> assumption
theorem mem_complexEdgeForms {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : B ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.DeltaSharedProofs.p8199 <;> assumption
theorem vertexFunction_apply_mem {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.hermitianTracelessFunctions σ) (x : σ) :
    l x ∈ ComplexMatrix2.hermitianTraceless :=
  (Submodule.mem_pi.mp hl) x (mem_univ x)
theorem mem_tracelessFunctions {σ : Type} {l : σ → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.hermitianTracelessFunctions σ) :
    l ∈ GroupLieProduct.tracelessFunctions σ := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.mem_tracelessFunctions_of_mem <;> assumption
def covDiffTranspose (L n : ℕ) : (Edge L n 0 0 → ComplexMatrix2) → Vertex L n 0 0 → ComplexMatrix2 :=
  transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
    (covDiff (trivialField L n 0 0))
theorem gaugeLaplacian_eq (l : Vertex L n 0 0 → ComplexMatrix2) :
    gaugeLaplacian (trivialField L n 0 0) l =
      covDiffTranspose L n (covDiff (trivialField L n 0 0) l) := rfl
theorem massiveHessian_eq (B : Edge L n 0 0 → ComplexMatrix2) :
    massiveHessian (trivialField L n 0 0) B =
      complexHessianOperator (trivialField L n 0 0) B +
        covDiff (trivialField L n 0 0) (covDiffTranspose L n B) := rfl
structure CovDiffAdjunction (L n : ℕ) : Prop where
  covDiff_mem : ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0),
    covDiff (trivialField L n 0 0) l ∈ complexEdgeForms L n 0 0
  transpose_mem : ∀ B ∈ complexEdgeForms L n 0 0,
    covDiffTranspose L n B ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0)
  pairing_eq : ∀ B ∈ complexEdgeForms L n 0 0,
    ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0), HasFiniteSupp l →
      traceFinsumPairing (covDiffTranspose L n B) l =
        edgeFormPairing B (covDiff (trivialField L n 0 0) l)
theorem covDiffAdjunction_of_onTorus (hX : OnTorus L n 0 0) : CovDiffAdjunction L n := by
  have hD := (hX _ trivialField_mem_complex).covDiff
  have hLin := hD.coe_linear
  have hTr := hD.isTranspose
  have hVal : ∀ (g : Edge L n 0 0 → ComplexMatrix2) (hg : g ∈ complexEdgeForms L n 0 0),
      covDiffTranspose L n g =
      (PairedFunctionSpace.transposeMap (linearOfValues (pairedFunctions (Vertex L n 0 0))
        (edgePairedSpace L n 0 0) (covDiff (trivialField L n 0 0))) ⟨g, hg⟩ :
          (pairedFunctions (Vertex L n 0 0)).complexSubmodule).1 :=
    fun g hg => dif_pos hg
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    rw [show covDiff (trivialField L n 0 0) l = _ from (hLin ⟨l, hl⟩).symm]
    exact Subtype.property _
  · intro B hB
    rw [hVal B hB]
    exact Subtype.property _
  · intro B hB l hl hs
    rw [hVal B hB, ← hLin ⟨l, hl⟩]
    exact hTr ⟨B, hB⟩ ⟨l, hl⟩ hs
theorem covDiff_mem_edgeFormSpace (hF : CovDiffAdjunction L n) {l : Vertex L n 0 0 → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n 0 0) :
    covDiff (trivialField L n 0 0) l ∈ edgeFormSpace L n 0 0 := by
  have hc := hF.covDiff_mem l (mem_tracelessFunctions hl)
  refine ⟨fun b hb => ?_, hc.2⟩
  have hEval : covDiff (trivialField L n 0 0) l b =
      ComplexMatrix2.conjugateBy (trivialField L n 0 0 b) (l b.target) - l b.source := by
    simp [covDiff, extendOddly, if_pos hb]
  rw [hEval]
  exact ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (Submonoid.one_mem _) _
      (vertexFunction_apply_mem hl _))
    (vertexFunction_apply_mem hl _)
theorem hasFiniteSupp_of_finite [Finite (Vertex L n 0 0)] (l : Vertex L n 0 0 → ComplexMatrix2) :
    HasFiniteSupp l :=
  Set.toFinite _
theorem covDiffTranspose_apply_mem [Finite (Vertex L n 0 0)] [Finite (PositiveEdge L n 0 0)]
    (hF : CovDiffAdjunction L n) {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) (x : Vertex L n 0 0) :
    covDiffTranspose L n B x ∈ ComplexMatrix2.hermitianTraceless := by
  have hc : covDiffTranspose L n B ∈ GroupLieProduct.tracelessFunctions (Vertex L n 0 0) :=
    hF.transpose_mem B (mem_complexEdgeForms hB)
  have hv : ∀ y, covDiffTranspose L n B y ∈ ComplexMatrix2.traceless :=
    fun y => (Submodule.mem_pi.mp hc) y (mem_univ y)
  refine mem_hermitianTraceless_of_pairing_skewPart_im hv ?_ x
  have hs : (fun y => skewPart (covDiffTranspose L n B y)) ∈ vertexFunctionSpace L n 0 0 :=
    Submodule.mem_pi.mpr fun y _ => skewPart_mem (hv y)
  rw [pairing_comm, hF.pairing_eq B (mem_complexEdgeForms hB) _ (mem_tracelessFunctions hs)
    (hasFiniteSupp_of_finite _)]
  have hd := covDiff_mem_edgeFormSpace hF hs
  exact pairing_im_eq_zero (fun b => edgeForm_apply_mem hB b.1)
    (fun b => edgeForm_apply_mem hd b.1)
end Difference
theorem twoOperatorsAtIdentityTorusClaim_holds
    (hD : HessianDeterminants.HessianSymmAndDetsPositive)
    (hX : CovDiffTransposes.Claim)
    (hA : HessianKernel.KernelProperties)
    (hP : FaceTermDerivatives.Statement)
    (hE : FaceSums.FacesAndPairings) : TwoOperatorsAtIdentityTorusClaim := by
  intro L hL n hn
  have hfin := (hE L hL 0 0 le_rfl).1 n hn
  have fs : Finite (Vertex L n 0 0) := Set.finite_univ_iff.mp (hfin.2.1 univ).2.1
  have fb : Finite (PositiveEdge L n 0 0) := Set.finite_univ_iff.mp (hfin.2.2.1 univ).2.1
  have fp : Finite (Face L n 0 0) := Set.finite_univ_iff.mp (hfin.2.2.2 univ).2.1
  have hF : CovDiffAdjunction L n :=
    covDiffAdjunction_of_onTorus ((hX L hL 0 0 le_rfl).1 n hn)
  obtain ⟨⟨⟨T, hT⟩, _⟩, ⟨⟨T', hT'⟩, _⟩, _⟩ :=
    ((hD L hL).2 1 one_pos n hn).1 _ (trivialField_mem_compact (L := L) (n := n))
  refine ⟨fun l hl => ?_, fun B hB => ?_, fun l hl => ?_, fun B hB => ?_⟩
  · have := (T ⟨l, hl⟩).2
    rwa [hT ⟨l, hl⟩] at this
  · have := (T' ⟨B, hB⟩).2
    rwa [hT' ⟨B, hB⟩] at this
  · have hd := covDiff_mem_edgeFormSpace hF hl
    have hEq : traceFinsumPairing l (gaugeLaplacian (trivialField L n 0 0) l) =
        edgeFormPairing (covDiff (trivialField L n 0 0) l)
          (covDiff (trivialField L n 0 0) l) := by
      rw [pairing_comm, gaugeLaplacian_eq]
      exact hF.pairing_eq _ (mem_complexEdgeForms hd) l (mem_tracelessFunctions hl)
        (hasFiniteSupp_of_finite _)
    have hv : ∀ b : PositiveEdge L n 0 0, restrictToPositiveEdges
        (covDiff (trivialField L n 0 0) l) b ∈ ComplexMatrix2.hermitianTraceless :=
      fun b => edgeForm_apply_mem hd b.1
    rw [hEq]
    exact ⟨pairing_im_eq_zero hv hv, pairing_self_re_nonneg hv⟩
  · have hc := mem_complexEdgeForms hB
    have ht := covDiffTranspose_apply_mem hF hB
    have hvB : ∀ p : Face L n 0 0, edgeCoboundary B p ∈ ComplexMatrix2.hermitianTraceless :=
      fun p => by
        simp only [edgeCoboundary]
        have h := edgeForm_apply_mem hB
        exact ComplexMatrix2.hermitianTraceless.sub_mem
          (ComplexMatrix2.hermitianTraceless.sub_mem
            (ComplexMatrix2.hermitianTraceless.add_mem (h _) (h _)) (h _)) (h _)
    have htc := hF.transpose_mem B hc
    have hEq : edgeFormPairing B (massiveHessian (trivialField L n 0 0) B) =
        traceFinsumPairing (edgeCoboundary B) (edgeCoboundary B) +
          traceFinsumPairing (covDiffTranspose L n B) (covDiffTranspose L n B) := by
      have eHess : edgeFormPairing B (complexHessianOperator (trivialField L n 0 0) B) =
          complexActionHessian (trivialField L n 0 0) B B :=
        ((hA L hL 0 0 le_rfl).1 n hn _
          (trivialField_mem_complex (L := L) (n := n))).2.2.2.2.1 B hc B hc
      have eFace : complexActionHessian (trivialField L n 0 0) B B =
          traceFinsumPairing (edgeCoboundary B) (edgeCoboundary B) :=
        ((hP L hL 0 0 le_rfl).1 n hn B hc).2
      have eAdj := hF.pairing_eq B hc _ htc (hasFiniteSupp_of_finite _)
      have eSplit : edgeFormPairing B (complexHessianOperator (trivialField L n 0 0) B +
          covDiff (trivialField L n 0 0) (covDiffTranspose L n B)) =
          edgeFormPairing B (complexHessianOperator (trivialField L n 0 0) B) +
            edgeFormPairing B (covDiff (trivialField L n 0 0) (covDiffTranspose L n B)) :=
        pairing_add _ _ _
      rw [massiveHessian_eq, eSplit, eHess, eFace, eAdj]
    rw [hEq]
    refine ⟨?_, ?_⟩
    · rw [Complex.add_im, pairing_im_eq_zero hvB hvB, pairing_im_eq_zero ht ht, add_zero]
    · rw [Complex.add_re]
      exact add_nonneg (pairing_self_re_nonneg hvB) (pairing_self_re_nonneg ht)
end YangMills.Construction.Tower.IdentityOperatorsTorus
end
