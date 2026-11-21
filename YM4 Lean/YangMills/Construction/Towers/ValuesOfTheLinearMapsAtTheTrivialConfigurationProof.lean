import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import YangMills.Construction.Towers.ValuesOfTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace LinearMapValues
open Matrices.GroupLieProduct
theorem ofReal_smul_mem_hermitianTraceless {A : Matrices.ComplexMatrix2} (r : ℝ)
    (hA : A ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • A ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.ofReal_smul_mem_hermitianTraceless <;> assumption
theorem inverseFourthPowerWeight_smul_mem (L : ℕ) {A : Matrices.ComplexMatrix2}
    (hA : A ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    PeriodicLattice.inverseFourthPowerWeight L • A ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.inverseFourthPowerWeight_smul_mem <;> assumption
theorem mem_hermitianTracelessFunctions {σ : Type} {f : σ → Matrices.ComplexMatrix2}
    (hf : ∀ s, f s ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    f ∈ hermitianTracelessFunctions σ :=
  Submodule.mem_pi.2 fun s _ => hf s
theorem apply_mem_of_mem_hermitianTracelessFunctions {σ : Type} {f : σ → Matrices.ComplexMatrix2}
    (hf : f ∈ hermitianTracelessFunctions σ) (s : σ) :
    f s ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  Submodule.mem_pi.1 hf s (mem_univ s)
theorem innerProductCore_of_finite {ι : Type} [Finite ι] (h : FaceSums.PairingIsInner ι) :
    ∃ c : InnerProductSpace.Core ℝ (hermitianTracelessFunctions ι),
      ∀ f g : hermitianTracelessFunctions ι, ((c.inner f g : ℝ) : ℂ) =
        traceFinsumPairing (f : ι → Matrices.ComplexMatrix2) (g : ι → Matrices.ComplexMatrix2) := by
  obtain ⟨-, c, hc⟩ := h
  let e : hermitianTracelessFunctions ι → FaceSums.finSuppLieFields ι := fun f =>
    ⟨f, fun s => apply_mem_of_mem_hermitianTracelessFunctions f.2 s, Set.toFinite _⟩
  have hadd : ∀ f g, e (f + g) = e f + e g := fun _ _ => rfl
  have hsmul : ∀ (r : ℝ) f, e (r • f) = r • e f := fun _ _ => rfl
  refine ⟨{ inner := fun f g => c.inner (e f) (e g)
            conj_inner_symm := fun f g => c.conj_inner_symm (e f) (e g)
            re_inner_nonneg := fun f => c.re_inner_nonneg (e f)
            add_left := fun f g u => ?_
            smul_left := fun f g r => ?_
            definite := fun f hf => ?_ }, fun f g => hc (e f) (e g)⟩
  · change c.inner (e (f + g)) (e u) = _
    rw [hadd]
    exact c.add_left _ _ _
  · change c.inner (e (r • f)) (e g) = _
    rw [hsmul]
    exact c.smul_left _ _ _
  · have h0 : e f = 0 := c.definite (e f) hf
    exact Subtype.ext
      (congrArg (fun g : FaceSums.finSuppLieFields ι => (g : ι → Matrices.ComplexMatrix2)) h0)
section PeriodicSide
variable {L n k j : ℕ}
theorem bondFormSumAlong_mem {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong B γ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.bondFormSumAlong_mem <;> assumption
theorem contourFormAverage_mem {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) {i : ℤ} (y : PeriodicLattice.Site L n i)
    (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) :
    PeriodicLattice.contourFormAverage B y x ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem_hermitianTraceless _ (sum_mem fun _ _ => bondFormSumAlong_mem hB _)
theorem crossingSmoothing_opposite (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j + 1 ≤ k)
    {B : Edge L n k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (c : Edge L n k (j + 1)) :
    crossingSmoothing L n k j B c.opposite = -crossingSmoothing L n k j B c := by
  have hside := (hF L hL k).1 n hn
  have h := (hside.2 j hj c B ((hside.1 j (by omega)).1 B hB)).1
  unfold crossingSmoothing
  rw [h, smul_neg]
theorem crossingSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j + 1 ≤ k)
    {B : Edge L n k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    crossingSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) := by
  refine ⟨fun c _ => ?_, fun c => crossingSmoothing_opposite hF hL hn hj hB c⟩
  refine inverseFourthPowerWeight_smul_mem L ?_
  exact finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ h h' => Matrices.ComplexMatrix2.hermitianTraceless.add_mem h h')
    fun x _ => bondFormSumAlong_mem hB _
theorem linearSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j + 1 ≤ k)
    {B : Edge L n k j → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) := by
  have hside := (hF L hL k).1 n hn
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · refine ofReal_smul_mem_hermitianTraceless _ ?_
    refine finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
      Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
      (fun _ _ h h' => Matrices.ComplexMatrix2.hermitianTraceless.add_mem h h') fun x _ => ?_
    exact Matrices.ComplexMatrix2.hermitianTraceless.sub_mem
      (Matrices.ComplexMatrix2.hermitianTraceless.add_mem (contourFormAverage_mem hB _ _)
        (bondFormSumAlong_mem hB _))
      (contourFormAverage_mem hB _ _)
  · exact (hside.2 j hj c B ((hside.1 j (by omega)).1 B hB)).2
theorem crossingSmoothingIter_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {B : Edge L n k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) (i : ℕ)
    (hi : i ≤ k) : crossingSmoothingIter L n k i B ∈ edgeFormSpace L n k i := by
  induction i with
  | zero => exact hB
  | succ i ih => exact crossingSmoothing_mem_edgeFormSpace hF hL hn hi (ih (by omega))
theorem cubeContourAverage_mem {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (y : Vertex L n k (j + 1)) :
    cubeContourAverage L n k j B y ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  refine inverseFourthPowerWeight_smul_mem L ?_
  exact finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ h h' => Matrices.ComplexMatrix2.hermitianTraceless.add_mem h h')
    fun x _ => contourFormAverage_mem hB _ _
theorem cubeContourAverageIter_mem_vertexFunctionSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m ≤ k)
    {B : Edge L n k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    cubeContourAverageIter L n k m B ∈ vertexFunctionSpace L n k m := by
  refine sum_mem fun i hi => mem_hermitianTracelessFunctions fun x => ?_
  have hi' : i < m := Finset.mem_range.1 hi
  exact cubeContourAverage_mem (crossingSmoothingIter_mem_edgeFormSpace hF hL hn hB i (by omega)) _
end PeriodicSide
section FullSpaceSide
variable {a a' : ℝ}
theorem fullSpace_sumAlong_mem {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace a) (γ : List (InfiniteLattice.Link a)) :
    FullSpace.sumAlong B γ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.FullSpace.CovariantIteratesAtIdentityProof.sumAlong_mem <;> assumption
theorem fullSpace_contourAverage_mem (L : ℕ) {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace a') (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    FullSpace.contourAverage L B y x ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem_hermitianTraceless _ (sum_mem fun _ _ => fullSpace_sumAlong_mem hB _)
variable {L k j : ℕ}
theorem fullSpace_crossingSmoothing_opposite (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j + 1 ≤ k)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.crossingSmoothing L B c.opposite = -FullSpace.crossingSmoothing L B c := by
  have hside := (hF L hL k).2
  have h := (hside.2 j hj c B ((hside.1 j (by omega)).1 B hB)).1
  unfold FullSpace.crossingSmoothing
  rw [h, smul_neg]
theorem fullSpace_crossingSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j + 1 ≤ k)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) :
    FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L B ∈
      FullSpace.edgeFormSpace (meshAt L k (j + 1)) := by
  refine ⟨fun c _ => ?_, fun c => fullSpace_crossingSmoothing_opposite hF hL hj hB c⟩
  refine inverseFourthPowerWeight_smul_mem L ?_
  exact finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ h h' => Matrices.ComplexMatrix2.hermitianTraceless.add_mem h h')
    fun x _ => fullSpace_sumAlong_mem hB _
theorem fullSpace_linearSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j + 1 ≤ k)
    {B : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) :
    FullSpace.linearSmoothing (a := meshAt L k (j + 1)) L B ∈
      FullSpace.edgeFormSpace (meshAt L k (j + 1)) := by
  have hside := (hF L hL k).2
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · refine inverseFourthPowerWeight_smul_mem L ?_
    refine finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
      Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
      (fun _ _ h h' => Matrices.ComplexMatrix2.hermitianTraceless.add_mem h h') fun x _ => ?_
    exact Matrices.ComplexMatrix2.hermitianTraceless.sub_mem
      (Matrices.ComplexMatrix2.hermitianTraceless.add_mem (fullSpace_contourAverage_mem L hB _ _)
        (fullSpace_sumAlong_mem hB _))
      (fullSpace_contourAverage_mem L hB _ _)
  · exact (hside.2 j hj c B ((hside.1 j (by omega)).1 B hB)).2
theorem fullSpace_crossingSmoothingIter_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {B : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k 0)) (i : ℕ) (hi : i ≤ k) :
    FullSpace.crossingSmoothingIter L k i B ∈ FullSpace.edgeFormSpace (meshAt L k i) := by
  induction i with
  | zero => exact hB
  | succ i ih => exact fullSpace_crossingSmoothing_mem_edgeFormSpace hF hL hi (ih (by omega))
theorem fullSpace_cubeContourAverage_mem {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace a') (y : InfiniteLattice.LatticePoint a) :
    FullSpace.cubeContourAverage L B y ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  refine inverseFourthPowerWeight_smul_mem L ?_
  exact finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ h h' => Matrices.ComplexMatrix2.hermitianTraceless.add_mem h h')
    fun x _ => fullSpace_contourAverage_mem L hB _ _
theorem fullSpace_cubeContourAverageIter_mem_vertexFunctionSpace
    (hF : AxisPathReversal.MainStatement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {m : ℕ} (hm : m ≤ k) {B : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k 0)) :
    FullSpace.cubeContourAverageIter L k m B ∈ FullSpace.vertexFunctionSpace (meshAt L k m) := by
  refine sum_mem fun i hi => mem_hermitianTracelessFunctions fun x => ?_
  have hi' : i < m := Finset.mem_range.1 hi
  exact fullSpace_cubeContourAverage_mem
    (fullSpace_crossingSmoothingIter_mem_edgeFormSpace hF hL hB i (by omega)) _
end FullSpaceSide
end LinearMapValues
theorem LinearMapValues.statement_of_axisPathReversal (hF : AxisPathReversal.MainStatement)
    (hP : FaceSums.FacesAndPairings) : LinearMapValues.Statement := by
  intro L hL k
  refine ⟨fun n hn => ⟨fun j hj => ⟨fun B hB => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, fun m hm B hB => ?_⟩,
    fun j hj B hB => ⟨?_, ?_, ?_, ?_⟩, fun m hm B hB => ?_⟩
  · exact LinearMapValues.crossingSmoothing_opposite hF hL hn hj hB
  · exact LinearMapValues.crossingSmoothing_mem_edgeFormSpace hF hL hn hj hB
  · exact LinearMapValues.linearSmoothing_mem_edgeFormSpace hF hL hn hj hB
  · exact LinearMapValues.mem_hermitianTracelessFunctions fun x =>
      LinearMapValues.contourFormAverage_mem hB _ _
  · exact (((hP L hL k j (by omega)).1 n hn).2.1
      {x | (x : PeriodicLattice.FourTorus L n) ∉
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (j + 1))}).2.1.to_subtype
  · have hS := (((hP L hL k j (by omega)).1 n hn).2.1
      {x | (x : PeriodicLattice.FourTorus L n) ∉
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (j + 1))})
    have : Finite (FineOnlyVertex L n k j) := hS.2.1.to_subtype
    exact LinearMapValues.innerProductCore_of_finite hS.1
  · exact LinearMapValues.cubeContourAverageIter_mem_vertexFunctionSpace hF hL hn hm hB
  · exact LinearMapValues.fullSpace_crossingSmoothing_opposite hF hL hj hB
  · exact LinearMapValues.fullSpace_crossingSmoothing_mem_edgeFormSpace hF hL hj hB
  · exact LinearMapValues.fullSpace_linearSmoothing_mem_edgeFormSpace hF hL hj hB
  · exact LinearMapValues.mem_hermitianTracelessFunctions fun x =>
      LinearMapValues.fullSpace_contourAverage_mem L hB _ _
  · exact LinearMapValues.fullSpace_cubeContourAverageIter_mem_vertexFunctionSpace hF hL hm hB
end YangMills.Construction.Tower
end
