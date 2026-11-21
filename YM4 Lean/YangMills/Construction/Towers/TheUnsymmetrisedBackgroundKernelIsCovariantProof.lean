import YangMills.Construction.PeriodicOperators.OperatorFunctionsThatAgreeOnSmallFieldsProof
import YangMills.Construction.Towers.IsometriesKeepThePairingsAndTheSecondDerivativeAtTheSideInfinity
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLattice
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormedProof
import YangMills.Construction.Towers.TheUnsymmetrisedBackgroundKernelIsCovariant
import YangMills.Construction.Towers.TranslationRelationsOfTheTwoOperatorFunctions
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RawHessianCovariance
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
open YangMills.Construction.Tower.FullSpace.ShiftCovariance
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
open YangMills.Construction.Tower.FullSpace.UnsymmetrisedKernelTerms (CoeffsHolomorphicOn)
open YangMills.Construction.LocalKernels (FieldIdx FieldComponent)
section OneLattice
variable {a : ℝ} (hv : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup a)
def latticeVector (m : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a := ⟨castVec m, hv m⟩
theorem latticeVector_neg (m : Fin 4 → ℤ) : latticeVector hv (-m) = -latticeVector hv m :=
  Subtype.ext (funext fun μ => by simp [latticeVector, castVec])
theorem vertexImage_latticeShift (m : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    vertexImage (latticeShift m) x = x + latticeVector hv m :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a =>
      (x' : InfiniteLattice.AmbientSpace) = latticeShift m x)
    ⟨x + latticeVector hv m, rfl⟩ |>.trans rfl)
theorem vertexPreimage_latticeShift (m : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    vertexPreimage (latticeShift m) x = x - latticeVector hv m := by
  have spec : latticeShift m (vertexPreimage (latticeShift m) x :
      InfiniteLattice.LatticePoint a) = x :=
    Classical.epsilon_spec
      (p := fun x' : InfiniteLattice.LatticePoint a => latticeShift m x' = x)
      ⟨x - latticeVector hv m, by
        show ((x : InfiniteLattice.AmbientSpace) - castVec m) + castVec m = x
        rw [sub_add_cancel]⟩
  refine Subtype.ext ?_
  show (vertexPreimage (latticeShift m) x : InfiniteLattice.AmbientSpace) = x - castVec m
  exact eq_sub_of_add_eq spec
theorem edgeImage_endpoints (m : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    (edgeImage (latticeShift m) b).initial = b.initial + latticeVector hv m ∧
      (edgeImage (latticeShift m) b).terminal = b.terminal + latticeVector hv m := by
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexImage (latticeShift m) b.initial ∧
        b'.terminal = vertexImage (latticeShift m) b.terminal)
    ⟨⟨vertexImage (latticeShift m) b.initial, vertexImage (latticeShift m) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_latticeShift hv, vertexImage_latticeShift hv, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (edgeImage (latticeShift m) b).initial = vertexImage (latticeShift m) b.initial ∧
      (edgeImage (latticeShift m) b).terminal = vertexImage (latticeShift m) b.terminal := spec
  rw [vertexImage_latticeShift hv, vertexImage_latticeShift hv] at spec'
  exact spec'
theorem edgePreimage_endpoints (m : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    (edgePreimage (latticeShift m) b).initial = b.initial - latticeVector hv m ∧
      (edgePreimage (latticeShift m) b).terminal = b.terminal - latticeVector hv m := by
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexPreimage (latticeShift m) b.initial ∧
        b'.terminal = vertexPreimage (latticeShift m) b.terminal)
    ⟨⟨vertexPreimage (latticeShift m) b.initial, vertexPreimage (latticeShift m) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexPreimage_latticeShift hv, vertexPreimage_latticeShift hv, sub_sub_sub_cancel_right]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (edgePreimage (latticeShift m) b).initial =
      vertexPreimage (latticeShift m) b.initial ∧
      (edgePreimage (latticeShift m) b).terminal =
        vertexPreimage (latticeShift m) b.terminal := spec
  rw [vertexPreimage_latticeShift hv, vertexPreimage_latticeShift hv] at spec'
  exact spec'
def shiftBack (m : Fin 4 → ℤ) (c : PositiveEdge a) : PositiveEdge a :=
  ⟨edgePreimage (latticeShift m) c.1, by
    obtain ⟨μ, hμ⟩ := c.2
    refine ⟨μ, ?_⟩
    rw [(edgePreimage_endpoints hv m c.1).1, (edgePreimage_endpoints hv m c.1).2,
      sub_sub_sub_cancel_right]
    exact hμ⟩
theorem positiveEdge_ext {c c' : PositiveEdge a} (ht : c.1.initial = c'.1.initial)
    (hh : c.1.terminal = c'.1.terminal) : c = c' :=
  Subtype.ext (InfiniteLattice.Link.ext ht hh)
def shiftBackEquiv (m : Fin 4 → ℤ) : PositiveEdge a ≃ PositiveEdge a where
  toFun := shiftBack hv m
  invFun := shiftBack hv (-m)
  left_inv := fun c => positiveEdge_ext
    (by
      show (edgePreimage _ (edgePreimage _ c.1)).initial = _
      rw [(edgePreimage_endpoints hv (-m) _).1, (edgePreimage_endpoints hv m _).1,
        latticeVector_neg, sub_neg_eq_add, sub_add_cancel])
    (by
      show (edgePreimage _ (edgePreimage _ c.1)).terminal = _
      rw [(edgePreimage_endpoints hv (-m) _).2, (edgePreimage_endpoints hv m _).2,
        latticeVector_neg, sub_neg_eq_add, sub_add_cancel])
  right_inv := fun c => positiveEdge_ext
    (by
      show (edgePreimage _ (edgePreimage _ c.1)).initial = _
      rw [(edgePreimage_endpoints hv m _).1, (edgePreimage_endpoints hv (-m) _).1,
        latticeVector_neg, sub_neg_eq_add, add_sub_cancel_right])
    (by
      show (edgePreimage _ (edgePreimage _ c.1)).terminal = _
      rw [(edgePreimage_endpoints hv m _).2, (edgePreimage_endpoints hv (-m) _).2,
        latticeVector_neg, sub_neg_eq_add, add_sub_cancel_right])
theorem edgeImage_shiftBack (m : Fin 4 → ℤ) (c : PositiveEdge a) :
    c.1 = edgeImage (latticeShift m) (shiftBack hv m c).1 :=
  InfiniteLattice.Link.ext
    (by
      rw [(edgeImage_endpoints hv m _).1]
      show _ = (edgePreimage _ c.1).initial + _
      rw [(edgePreimage_endpoints hv m _).1, sub_add_cancel])
    (by
      rw [(edgeImage_endpoints hv m _).2]
      show _ = (edgePreimage _ c.1).terminal + _
      rw [(edgePreimage_endpoints hv m _).2, sub_add_cancel])
include hv in
theorem traceFinsumPairing_pushSiteFunction (m : Fin 4 → ℤ)
    (g g' : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    Tower.traceFinsumPairing (pushSiteFunction (latticeShift m) g)
        (pushSiteFunction (latticeShift m) g') = Tower.traceFinsumPairing g g' := by
  let e : InfiniteLattice.LatticePoint a ≃ InfiniteLattice.LatticePoint a :=
    { toFun := fun x => x - latticeVector hv m
      invFun := fun x => x + latticeVector hv m
      left_inv := fun x => sub_add_cancel x _
      right_inv := fun x => add_sub_cancel_right x _ }
  unfold Tower.traceFinsumPairing pushSiteFunction
  simp only [vertexPreimage_latticeShift hv]
  exact finsum_comp_equiv e (f := fun x => ComplexMatrix2.halfTrace (g x * g' x))
theorem traceFinsumPairing_shiftBack (m : Fin 4 → ℤ) {p p' q q' : PositiveEdge a → ComplexMatrix2}
    (h : ∀ c, p' c = p (shiftBack hv m c)) (h' : ∀ c, q' c = q (shiftBack hv m c)) :
    Tower.traceFinsumPairing p' q' = Tower.traceFinsumPairing p q := by
  unfold Tower.traceFinsumPairing
  simp only [h, h']
  exact finsum_comp_equiv (shiftBackEquiv hv m) (f := fun c => ComplexMatrix2.halfTrace (p c * q c))
theorem opposite_isPositivelyOriented {b : InfiniteLattice.Link a}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_congr {g g' : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → g c = g' c) :
    extendOddly g = extendOddly g' := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_congr <;> assumption
include hv in
theorem isometryOnTangent_latticeShift (m : Fin 4 → ℤ) (U B : InfiniteLattice.Link a → ComplexMatrix2) :
    isometryOnTangent (latticeShift m) U B =
      extendOddly fun b => B (edgePreimage (latticeShift m) b) := by
  refine extendOddly_congr fun c hc => ?_
  exact if_pos (shiftBack hv m ⟨c, hc⟩).2
theorem isometryOnTangent_positive (m : Fin 4 → ℤ) (U B : InfiniteLattice.Link a → ComplexMatrix2)
    (c : PositiveEdge a) :
    isometryOnTangent (latticeShift m) U B c.1 = B (shiftBack hv m c).1 := by
  rw [isometryOnTangent_latticeShift hv]
  exact if_pos c.2
include hv in
theorem isometryOnTangent_add (m : Fin 4 → ℤ) (U B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    isometryOnTangent (latticeShift m) U (B + B') =
      isometryOnTangent (latticeShift m) U B + isometryOnTangent (latticeShift m) U B' := by
  classical
  rw [isometryOnTangent_latticeShift hv, isometryOnTangent_latticeShift hv,
    isometryOnTangent_latticeShift hv]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [extendOddly, if_pos hb]
  · simp [extendOddly, if_neg hb]
    abel
end OneLattice
section Forms
variable {L k : ℕ}
theorem meshAt_pos (hL : 0 < L) (j : ℕ) : 0 < meshAt L k j :=
  zpow_pos (Nat.cast_pos.2 hL) _
theorem basisForm_mem (ha : 0 < meshAt L k 0) (a : Fin 3)
    (b : PositiveEdge (meshAt L k 0)) :
    basisForm a b ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.basisForm_mem <;> assumption
theorem basisForm_hasFiniteEdgeSupport (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    HasFiniteEdgeSupport (basisForm (L := L) (k := k) (j := 0) a b) := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.basisForm_finiteSupport <;> assumption
theorem mem_boundedSubmodule_of_finite {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0))
    (hf : (Function.support (restrictToPositiveEdges B)).Finite) :
    B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) := by
  have hp : ∀ p : PositiveEdge (meshAt L k 0),
      ‖B p.1‖ ≤ ∑ q ∈ hf.toFinset, ‖B q.1‖ := by
    intro p
    by_cases hs : p ∈ Function.support (restrictToPositiveEdges B)
    · exact Finset.single_le_sum (f := fun q : PositiveEdge (meshAt L k 0) => ‖B q.1‖)
        (fun _ _ => norm_nonneg _) (hf.mem_toFinset.2 hs)
    · have h0 : B p.1 = 0 := by simpa [restrictToPositiveEdges] using hs
      rw [h0, norm_zero]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨hB, ∑ q ∈ hf.toFinset, ‖B q.1‖, fun b => ?_⟩
  by_cases hb : b.IsPositivelyOriented
  · exact hp ⟨b, hb⟩
  · have hr : IsEdgeFormIn PeriodicLattice.complexLieAlgebra B := hB
    have e : ‖B b‖ = ‖B b.opposite‖ := by rw [hr.2 b, norm_neg]
    change ‖B b‖ ≤ _
    rw [e]
    exact hp ⟨b.opposite, opposite_isPositivelyOriented hb⟩
section Translated
variable {j : ℕ} (hv : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k j))
theorem shiftEdge_endpoints (n : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge n b).1.initial = b.1.initial + latticeVector hv n ∧
      (shiftEdge n b).1.terminal = b.1.terminal + latticeVector hv n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : PosEdge L k j => b'.1 = edgeImage (intShift n) b.1)
    ⟨⟨edgeImage (intShift n) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      have e := edgeImage_endpoints hv n b.1
      show (edgeImage (latticeShift n) b.1).terminal -
        (edgeImage (latticeShift n) b.1).initial = _
      rw [e.1, e.2, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have spec' : (shiftEdge n b).1 = edgeImage (latticeShift n) b.1 := spec
  rw [spec']
  exact edgeImage_endpoints hv n b.1
theorem shiftEdge_neg (n : Fin 4 → ℤ) (c : PosEdge L k j) :
    shiftEdge (-n) c = shiftBack hv n c := by
  have e := shiftEdge_endpoints hv (-n) c
  refine positiveEdge_ext ?_ ?_
  · rw [e.1, latticeVector_neg, ← sub_eq_add_neg]
    exact ((edgePreimage_endpoints hv n c.1).1).symm
  · rw [e.2, latticeVector_neg, ← sub_eq_add_neg]
    exact ((edgePreimage_endpoints hv n c.1).2).symm
end Translated
theorem basisForm_shiftEdge
    (hv : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k 0))
    (n : Fin 4 → ℤ) (U : Edge L k 0 → ComplexMatrix2) (a : Fin 3)
    (b : PosEdge L k 0) :
    basisForm a (shiftEdge n b) =
      isometryOnTangent (latticeShift n) U (basisForm a b) := by
  classical
  rw [isometryOnTangent_latticeShift hv]
  refine extendOddly_congr fun c hc => ?_
  have ht := shiftEdge_endpoints hv n b
  have hi := edgePreimage_endpoints hv n c
  have e : basisForm a b (edgePreimage (latticeShift n) c) =
      if edgePreimage (latticeShift n) c = b.1 then ComplexMatrix2.pauliFamily a else 0 :=
    if_pos (shiftBack hv n ⟨c, hc⟩).2
  rw [e]
  by_cases h : c = (shiftEdge n b).1
  · have h' : edgePreimage (latticeShift n) c = b.1 :=
      InfiniteLattice.Link.ext (by rw [hi.1, h, ht.1, add_sub_cancel_right])
        (by rw [hi.2, h, ht.2, add_sub_cancel_right])
    rw [if_pos h, if_pos h']
  · have h' : ¬ edgePreimage (latticeShift n) c = b.1 := fun e' => h
      (InfiniteLattice.Link.ext (by rw [ht.1, ← e', hi.1, sub_add_cancel])
        (by rw [ht.2, ← e', hi.2, sub_add_cancel]))
    rw [if_neg h, if_neg h']
theorem sourceOfCoeffs_apply (hL : 0 < L) (f : FieldIdx L k hL → ℂ) {c : Edge L k 0}
    (hc : c.IsPositivelyOriented) :
    sourceOfCoeffs hL f c = ∑ a, f ⟨.source, (a, ⟨c, hc⟩)⟩ • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.sourceOfCoeffs_apply <;> assumption
theorem coarseOfCoeffs_apply (hL : 0 < L) (f : FieldIdx L k hL → ℂ) {c : Edge L k k}
    (hc : c.IsPositivelyOriented) :
    coarseOfCoeffs hL f c = ∑ a, f ⟨.coarse, (a, ⟨c, hc⟩)⟩ • ComplexMatrix2.pauliFamily a := by
  classical
  have e : coarseOfCoeffs hL f c =
      if h : c.IsPositivelyOriented then ofPauliCoeffs (fun ι => f ⟨.coarse, ι⟩) ⟨c, h⟩
      else 0 := if_pos hc
  rw [e, dif_pos hc]
  rfl
theorem sourceOfCoeffs_shiftField
    (hv : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k 0))
    (hL : 0 < L) (f : (fieldPeriodicData L k hL).Carrier → ℂ) (n : Fin 4 → ℤ)
    (c : PositiveEdge (meshAt L k 0)) :
    restrictToPositiveEdges (sourceOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f)) c =
      restrictToPositiveEdges (sourceOfCoeffs hL f) (shiftBack hv n c) := by
  show sourceOfCoeffs hL _ c.1 = sourceOfCoeffs hL f (shiftBack hv n c).1
  rw [sourceOfCoeffs_apply hL _ c.2, sourceOfCoeffs_apply hL f (shiftBack hv n c).2]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : shiftField (fieldPeriodicData L k hL) n f ⟨.source, (a, ⟨c.1, c.2⟩)⟩ =
      f ⟨.source, (a, shiftEdge (-n) c)⟩ := rfl
  rw [e]
  exact congrArg (fun c' : PosEdge L k 0 =>
    f ⟨.source, (a, c')⟩ • ComplexMatrix2.pauliFamily a) (shiftEdge_neg hv n c)
theorem coarseOfCoeffs_shiftField
    (hv : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k k))
    (hL : 0 < L) (f : (fieldPeriodicData L k hL).Carrier → ℂ) (n : Fin 4 → ℤ)
    (c : PositiveEdge (meshAt L k k)) :
    restrictToPositiveEdges (coarseOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f)) c =
      restrictToPositiveEdges (coarseOfCoeffs hL f) (shiftBack hv n c) := by
  show coarseOfCoeffs hL _ c.1 = coarseOfCoeffs hL f (shiftBack hv n c).1
  rw [coarseOfCoeffs_apply hL _ c.2, coarseOfCoeffs_apply hL f (shiftBack hv n c).2]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : shiftField (fieldPeriodicData L k hL) n f ⟨.coarse, (a, ⟨c.1, c.2⟩)⟩ =
      f ⟨.coarse, (a, shiftEdge (-n) c)⟩ := rfl
  rw [e]
  exact congrArg (fun c' : PosEdge L k k =>
    f ⟨.coarse, (a, c')⟩ • ComplexMatrix2.pauliFamily a) (shiftEdge_neg hv n c)
end Forms
section Terms
variable {L k : ℕ}
structure IsTameForm (L k : ℕ) (U B : Edge L k 0 → ComplexMatrix2) : Prop where
  mem : B ∈ complexEdgeForms (meshAt L k 0)
  finite : HasFiniteEdgeSupport B
  drift_mem : ∀ y, iterContourLogDrift L k U k B y ∈ ComplexMatrix2.traceless
  param_mem : ∀ x, gaugeParam U B x ∈ ComplexMatrix2.traceless
  shifted_mem : shiftedForm U B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0))
structure ShiftRelations (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) (n : Fin 4 → ℤ) : Prop where
  commutes : ShiftCommutesAt L k U n
  covDiff_push : ∀ l : Vertex L k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
    covDiff (pushField (latticeShift n) U) (pushSiteFunction (latticeShift n) l) =
      isometryOnTangent (latticeShift n) U (covDiff U l)
  average_push : ∀ l : Vertex L k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
    iterAdjointCubeAverage L k (pushField (latticeShift n) U) k
        (pushSiteFunction (latticeShift n) l) =
      pushSiteFunction (latticeShift n) (iterAdjointCubeAverage L k U k l)
  average_mem : ∀ l : Vertex L k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
    ∀ y, iterAdjointCubeAverage L k U k l y ∈ ComplexMatrix2.traceless
  drift_push : ∀ B ∈ complexEdgeForms (meshAt L k 0),
    iterContourLogDrift L k (pushField (latticeShift n) U) k
        (isometryOnTangent (latticeShift n) U B) =
      pushSiteFunction (latticeShift n) (iterContourLogDrift L k U k B)
variable {U B B' : Edge L k 0 → ComplexMatrix2} {n : Fin 4 → ℤ}
theorem gaugeParam_shift (R : ShiftRelations L k U n) (G : IsTameForm L k U B) :
    gaugeParam (pushField (latticeShift n) U) (isometryOnTangent (latticeShift n) U B) =
      pushSiteFunction (latticeShift n) (gaugeParam U B) := by
  unfold gaugeParam
  rw [R.drift_push B G.mem, R.commutes.zeroExtend_shift _ G.drift_mem]
theorem shiftedForm_shift
    (hv : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k 0))
    (R : ShiftRelations L k U n) (G : IsTameForm L k U B) :
    shiftedForm (pushField (latticeShift n) U) (isometryOnTangent (latticeShift n) U B) =
      isometryOnTangent (latticeShift n) U (shiftedForm U B) := by
  unfold shiftedForm
  rw [gaugeParam_shift R G, R.covDiff_push _ G.param_mem, isometryOnTangent_add hv]
theorem transposeOfValues_mem_complex (S S' : Tower.PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    Tower.PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by apply _root_.YangMills.Construction.Tower.CovDiffTransposes.transposeOfValues_mem <;> assumption
theorem covDiffTranspose_mem (G : IsTameForm L k U B) (x : Vertex L k 0) :
    covDiffTranspose L k U B x ∈ ComplexMatrix2.traceless :=
  transposeOfValues_mem_complex (Tower.pairedFunctions (Vertex L k 0))
    (edgePairedSpace (meshAt L k 0)) (covDiff U) (g := B) G.mem x (Set.mem_univ x)
theorem gaugeFixingTerm_shift (R : ShiftRelations L k U n) (G : IsTameForm L k U B) :
    gaugeFixingTerm L k (pushField (latticeShift n) U) (isometryOnTangent (latticeShift n) U B) =
      pushSiteFunction (latticeShift n) (gaugeFixingTerm L k U B) := by
  unfold gaugeFixingTerm
  rw [R.commutes.covDiffTranspose_shift B G.mem, R.average_push _ (covDiffTranspose_mem G),
    R.commutes.averageTranspose_shift _ (R.average_mem _ (covDiffTranspose_mem G))]
  rfl
theorem covDiff_gaugeParam_mem (G : IsTameForm L k U B) :
    covDiff U (gaugeParam U B) ∈ complexEdgeForms (meshAt L k 0) := by
  have e : covDiff U (gaugeParam U B) = shiftedForm U B - B := by
    simp [shiftedForm]
  rw [e]
  exact Submodule.sub_mem _ G.shifted_mem.1 G.mem
theorem hessianBilinear_shift
    (hv₀ : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k 0))
    (hvk : ∀ m : Fin 4 → ℤ, castVec m ∈ InfiniteLattice.latticeSubgroup (meshAt L k k))
    (R : ShiftRelations L k U n) (G : IsTameForm L k U B) (G' : IsTameForm L k U B')
    {J J' : Edge L k 0 → ComplexMatrix2} {μ μ' : Edge L k k → ComplexMatrix2}
    (hJ : ∀ c, restrictToPositiveEdges J' c = restrictToPositiveEdges J (shiftBack hv₀ n c))
    (hμ : ∀ c, restrictToPositiveEdges μ' c = restrictToPositiveEdges μ (shiftBack hvk n c))
    (hA : complexActionHessian (pushField (latticeShift n) U)
        (isometryOnTangent (latticeShift n) U B) (isometryOnTangent (latticeShift n) U B') =
      complexActionHessian U B B') :
    hessianBilinear (pushField (latticeShift n) U) J' μ'
        (isometryOnTangent (latticeShift n) U B) (isometryOnTangent (latticeShift n) U B') =
      hessianBilinear U J μ B B' := by
  have hP : ∀ X : Edge L k 0 → ComplexMatrix2,
      finiteEdgePairing J' (isometryOnTangent (latticeShift n) U X) = finiteEdgePairing J X :=
    fun X => traceFinsumPairing_shiftBack hv₀ n hJ fun c => isometryOnTangent_positive hv₀ n U X c
  have hQ : Tower.traceFinsumPairing (restrictToPositiveEdges μ')
      (complexQuadraticTerm L k (pushField (latticeShift n) U)
        (isometryOnTangent (latticeShift n) U (shiftedForm U B))
        (isometryOnTangent (latticeShift n) U (shiftedForm U B'))) =
      Tower.traceFinsumPairing (restrictToPositiveEdges μ)
        (complexQuadraticTerm L k U (shiftedForm U B) (shiftedForm U B')) :=
    traceFinsumPairing_shiftBack hvk n hμ fun c =>
      R.commutes.quadraticTerm_shift _ G.shifted_mem _ G'.shifted_mem (shiftBack hvk n c) c
        (edgeImage_shiftBack hvk n c)
  unfold hessianBilinear backgroundForm sourceBilinear
  rw [hA, gaugeFixingTerm_shift R G, gaugeFixingTerm_shift R G',
    traceFinsumPairing_pushSiteFunction hv₀, gaugeParam_shift R G, gaugeParam_shift R G',
    R.covDiff_push _ G'.param_mem, R.commutes.bracketTerm_shift _ G.param_mem _ G'.mem,
    R.commutes.bracketTerm_shift _ G.param_mem _ (covDiff_gaugeParam_mem G'),
    hP, hP, shiftedForm_shift hv₀ R G, shiftedForm_shift hv₀ R G', hQ]
end Terms
section Assembly
variable {L k : ℕ}
theorem isSupBelow_mono {F : PeriodicData} {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ}
    (h : IsSupBelow F ζ ρ) (hle : ρ ≤ ρ') : IsSupBelow F ζ ρ' := by apply _root_.YangMills.Construction.PeriodicOperators.LocalAgreement.isSupBelow_mono <;> assumption
theorem iterAverage_mem (hN : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {l : Vertex L k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (j : ℕ) (hj : j ≤ k) :
    ∀ y, iterAdjointCubeAverage L k U j l y ∈ ComplexMatrix2.traceless := by
  induction j with
  | zero => exact hl
  | succ j ih =>
    have h : j < k := hj
    exact ((hN L hL k j h _ (hU.2 j h)).2.2.1 _ (ih h.le)).2
theorem iterDrift_mem (hC : ComplexIterChain)
    (hN : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (j : ℕ) (hj : j ≤ k) :
    ∀ y, iterContourLogDrift L k U j B y ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.HessianLaplacian.iterContourLogDrift_mem <;> assumption
end Assembly
theorem covarianceClaim_holds
    (hTR : ShiftCovariance.Claim)
    (hIso : CovariantSmoothingIsometryEquivariance)
    (hTrans : Tower.Translations.TranslationProperties)
    (hPair : LeftChartAlgebra.SymmetriesPreservePairingsAndHessian)
    (hC : ComplexIterChain)
    (hN : CovariantStepComplexLinear)
    (hSite : BasisFormLocality.ElementaryFormLocality) : CovarianceClaim := by
  intro L hL hLs k hk
  obtain ⟨ρ₁, hρ₁, hR⟩ := hTR L hL hLs k hk
  obtain ⟨ρ₂, hρ₂, hS⟩ := hSite L hL hLs k hk
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun f hf n ι' ι => ?_⟩
  have hf₁ : IsSupBelow (fieldPeriodicData L k hL) f ρ₁ := isSupBelow_mono hf (min_le_left _ _)
  have hf₂ : IsSupBelow (fieldPeriodicData L k hL) f ρ₂ := isSupBelow_mono hf (min_le_right _ _)
  obtain ⟨hU, -, -, hconf, hmaps, -⟩ := hR f hf₁ n
  have h0 := hTrans L hLs k 0 (Nat.zero_le k)
  have hkk := hTrans L hLs k k le_rfl
  have hv₀ := h0.2.2.2.2.1.2.1
  have hvk := hkk.2.2.2.2.1.2.1
  have hcar := hkk.2.2.2.1 n
  have hI := hIso L hLs k k le_rfl (latticeShift n) hcar.1 (hcar.2.1 k le_rfl) _ hU
  have R : ShiftRelations L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f) n :=
    ⟨hmaps, fun l hl => (hI.1 l hl).1, fun l hl => (hI.1 l hl).2,
      fun l hl => iterAverage_mem hN hLs hU hl k le_rfl, fun B hB => (hI.2 B hB).2.2⟩
  have ha := meshAt_pos (k := k) hL 0
  have G : ∀ ι : Fin 3 × PositiveEdge (meshAt L k 0),
      IsTameForm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm ι.1 ι.2) := by
    intro ι
    obtain ⟨hσ, hτ, hmem⟩ := hS ι.1 ι.2
    have hB := basisForm_mem ha ι.1 ι.2
    refine ⟨hB, basisForm_hasFiniteEdgeSupport ι.1 ι.2, iterDrift_mem hC hN hLs hU hB k le_rfl,
      hσ.mem_traceless f hf₂,
      mem_boundedSubmodule_of_finite (hmem f hf₂) (hτ.finite.subset fun c hc => ?_)⟩
    by_contra hn
    exact hc (hτ.eq_zero_of_not_mem f hf₂ c hn)
  have hA := (hPair L k 0 hLs (Nat.zero_le k) (latticeShift n) _ hcar.1
    (hcar.2.1 0 (Nat.zero_le k)) hU.1 _ (G ι').mem _ (G ι).mem).2 (G ι').finite (G ι).finite
  show hessianBilinear
      (FieldValueFunctions.gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f))
      (sourceOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f))
      (coarseOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f))
      (basisForm ι'.1 (shiftEdge n ι'.2)) (basisForm ι.1 (shiftEdge n ι.2)) =
    hessianBilinear (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
      (sourceOfCoeffs hL f) (coarseOfCoeffs hL f)
      (basisForm ι'.1 ι'.2) (basisForm ι.1 ι.2)
  rw [hconf, basisForm_shiftEdge hv₀ n (FieldValueFunctions.gaugeFieldOfCoeffs hL f),
    basisForm_shiftEdge hv₀ n (FieldValueFunctions.gaugeFieldOfCoeffs hL f)]
  exact hessianBilinear_shift hv₀ hvk R (G ι') (G ι) (sourceOfCoeffs_shiftField hv₀ hL f n)
    (coarseOfCoeffs_shiftField hvk hL f n) hA
end YangMills.Construction.Tower.FullSpace.RawHessianCovariance
end
