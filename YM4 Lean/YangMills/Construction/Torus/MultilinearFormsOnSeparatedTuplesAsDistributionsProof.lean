import YangMills.Construction.ReflectionPositivity.ReflectionOfAMirrorOfOneTorusProof
import YangMills.Construction.Torus.ChartsAndTransportOfTestFunctionsProof
import YangMills.Construction.Torus.FiniteSmoothPartitionsOfUnity
import YangMills.Construction.Torus.GluingOfDistributionsOnOpenSetsOfTuples
import YangMills.Construction.Torus.MultilinearFormsOnSeparatedTuplesAsDistributions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.MultilinearAsDistrib
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem singletonTupleSet_eq_boxSet (A : Set (Pt s E)) :
    singletonTupleSet A = boxSet fun _ : Fin 1 => A := by apply _root_.YangMills.Construction.AmbientPoints.ChartTransportProof.singletonTupleSet_eq_boxSet <;> assumption
theorem const_apply_zero_eq (v : Tuple s E 1) : (fun _ => v 0) = v := by apply _root_.YangMills.Construction.AmbientPoints.ChartTransportProof.const_apply_zero_eq <;> assumption
theorem tsupport_eq_image_closedSupport (f : Pt s E → ℝ) :
    tsupport f = (fun y : Tuple s E 1 => y 0) '' closedSupport (asFunctionOnOnePoint f) := by
  rw [closedSupport_asFunctionOnOnePoint, Set.image_preimage_eq]
  exact fun x => ⟨fun _ => x, rfl⟩
theorem c1CompactSupportIn_of_isRealTestFn {A : Set (Pt s E)} {φ : Pt s E → ℝ}
    (h : IsRealTestFn A φ) : φ ∈ c1CompactSupportIn A := by
  refine ⟨⟨h.1.1, fun m _ => h.1.2 m le_top⟩, ?_, ?_⟩
  · rw [tsupport_eq_image_closedSupport]
    exact h.2.1.image (continuous_apply 0)
  · intro x hx
    have hmem : (fun _ => x : Tuple s E 1) ∈ closedSupport (asFunctionOnOnePoint φ) := by
      rw [closedSupport_asFunctionOnOnePoint]
      exact hx
    exact h.2.2 hmem 0 (mem_univ 0)
theorem isRealTestFn_of_tsupport {A : Set (Pt s E)} {φ : Pt s E → ℝ}
    (h : IsSmoothFn (asFunctionOnOnePoint φ)) (hc : IsCompact (tsupport φ)) (hA : tsupport φ ⊆ A) :
    IsRealTestFn A φ := by
  refine ⟨h, ?_, ?_⟩
  · rw [closedSupport_asFunctionOnOnePoint]
    exact (Homeomorph.funUnique (Fin 1) (Pt s E)).isCompact_preimage.2 hc
  · rw [closedSupport_asFunctionOnOnePoint]
    intro y hy j _
    rw [Subsingleton.elim j 0]
    exact hA hy
theorem realTensor_mem_testFns (hC : TestFnOperations)
    (hn : 1 ≤ n) {V : Fin n → Set (Pt s E)} (hV : ∀ i, IsOpen (V i))
    {φ : Fin n → Pt s E → ℝ} (hφ : ∀ i, IsRealTestFn (V i) (φ i)) :
    realTensor φ ∈ testFns (boxSet V) :=
  ((hC s E n hn).2.2.2 V (fun i x => (φ i x : ℂ)) hV fun i => by
    rw [singletonTupleSet_eq_boxSet]
    exact hφ i).1
theorem continuousPartialsUpTo_zero {D : ℕ} (U : Set (Fin D → ℝ)) (ν : ℕ) :
    ContinuousPartialsUpTo U ν (0 : (Fin D → ℝ) → ℂ) := by
  induction ν with
  | zero => exact continuousOn_const
  | succ ν ih =>
    refine ⟨continuousOn_const, fun j => ⟨fun x _ => ?_, ?_⟩⟩
    · show DifferentiableAt ℝ (fun _ : ℝ => (0 : ℂ)) 0
      exact differentiableAt_const _
    · have h0 : partialDeriv j (0 : (Fin D → ℝ) → ℂ) = 0 := by
        funext x
        show deriv (fun _ : ℝ => (0 : ℂ)) 0 = 0
        simp
      rw [h0]
      exact ih
theorem isSmoothFn_zero {p : ℕ} : IsSmoothFn (0 : Tuple s E p → ℂ) :=
  ⟨isOpen_univ, fun m _ => continuousPartialsUpTo_zero univ m⟩
theorem closedSupport_zero {p : ℕ} : closedSupport (0 : Tuple s E p → ℂ) = ∅ := by
  simp [closedSupport]
theorem zero_mem_testFns {p : ℕ} (Ω : Set (Tuple s E p)) :
    (0 : Tuple s E p → ℂ) ∈ testFns Ω := by apply _root_.YangMills.Construction.AmbientPoints.ChartTransportProof.zero_mem_testFns <;> assumption
theorem cnNorm_zero (hTop : TupleTopology.Holds) {p : ℕ} (hp : 1 ≤ p) (ν : ℕ) :
    cnNorm ν (0 : Tuple s E p → ℂ) = 0 := by
  refine le_antisymm (iSup_le fun α => iSup_le fun _ => iSup_le fun y => ?_) bot_le
  have hsup := (((hTop s E).1 p hp).2.2.2.2 ⊤ 0 isSmoothFn_zero).1 α le_top
  have hy : multiDeriv α (0 : Tuple s E p → ℂ) y = 0 := by
    by_contra hne
    have : y ∈ closedSupport (multiDeriv α (0 : Tuple s E p → ℂ)) := subset_closure hne
    have := hsup.2.2.1 this
    rw [closedSupport_zero] at this
    exact this
  rw [hy]
  simp
theorem eq_zero_of_mem_testFns_empty {p : ℕ} {Ω : Set (Tuple s E p)} (hΩ : Ω = ∅)
    {F : Tuple s E p → ℂ} (hF : F ∈ testFns Ω) : F = 0 := by
  funext y
  by_contra hne
  have : y ∈ closedSupport F := subset_closure hne
  have := hF.2.2 this
  rw [hΩ] at this
  exact this
theorem linearForm_apply_eq_zero {p : ℕ} {Ω : Set (Tuple s E p)} {T : testFns Ω → ℂ}
    (hT : IsComplexLinearForm T) (F : testFns Ω) (h : F.1 = 0) : T F = 0 := by
  have := hT.2 0 F F (by rw [h]; simp)
  simpa using this
theorem setDiam_mono {A B : Set (Pt s E)} (h : A ⊆ B) : setDiam s E A ≤ setDiam s E B :=
  iSup₂_le fun a ha => iSup₂_le fun b hb =>
    le_iSup₂_of_le a (h ha) (le_iSup₂_of_le b (h hb) le_rfl)
theorem setDist_anti {A A' B B' : Set (Pt s E)} (h : A ⊆ A') (h' : B ⊆ B') :
    setDist s E A' B' ≤ setDist s E A B :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb =>
    iInf₂_le_of_le a (h ha) (iInf₂_le_of_le b (h' hb) le_rfl)
theorem pairwiseDisjointFamily_of_separated {R d : ℝ} {V : Fin n → Set (Pt s E)}
    (hV : IsSeparatedOpenFamily R d V) : PairwiseDisjointFamily V := by
  intro i i' hne
  refine Set.disjoint_left.mpr fun a ha ha' => ?_
  have hle : setDist s E (V i) (V i') ≤ 0 := by
    refine iInf₂_le_of_le a ha (iInf₂_le_of_le a ha' ?_)
    simp [pointDist_self]
  have hpos : 0 < ENNReal.ofReal d := ENNReal.ofReal_pos.mpr hV.gap_pos
  exact absurd ((hV.separated i i' hne).trans hle) (not_le.mpr hpos)
theorem mem_sepTuples_of_family (hP : SeparationAndProductFacts.statement) (hn : 1 ≤ n) {R d : ℝ}
    {V : Fin n → Set (Pt s E)} (hV : IsSeparatedOpenFamily R d V)
    {f : Fin n → Pt s E → ℝ} (hf : ∀ i, f i ∈ c1CompactSupportIn (V i)) :
    f ∈ sepTuples s E n :=
  ((hP s n hn).1 E).c1ProductOver_subset V (pairwiseDisjointFamily_of_separated hV) fun i _ => hf i
theorem IsSeparatedOpenFamily.ofSubsets {R d : ℝ} {V W : Fin n → Set (Pt s E)}
    (hV : IsSeparatedOpenFamily R d V) (hW : ∀ i, IsOpen (W i)) (h : ∀ i, W i ⊆ V i) :
    IsSeparatedOpenFamily R d W where
  radius_pos := hV.radius_pos
  gap_pos := hV.gap_pos
  isOpen := hW
  setDiam_le i := (setDiam_mono (h i)).trans (hV.setDiam_le i)
  setDiam_lt_of_torus hE i := (setDiam_mono (h i)).trans_lt (hV.setDiam_lt_of_torus hE i)
  separated i i' hne := (hV.separated i i' hne).trans (setDist_anti (h i) (h i'))
theorem isOpen_boxSet {V : Fin n → Set (Pt s E)} (hV : ∀ i, IsOpen (V i)) :
    IsOpen (boxSet V) :=
  isOpen_set_pi finite_univ fun i _ => hV i
theorem mem_of_isLinearBijOnWithInv {𝕜 X Y : Type*} [Semiring 𝕜] [AddCommMonoid X]
    [AddCommMonoid Y] [Module 𝕜 X] [Module 𝕜 Y] {f : X → Y} {g : Y → X} {A : Set X} {B : Set Y}
    (h : IsLinearBijOnWithInv 𝕜 f g A B) {y : Y} (hy : y ∈ B) : g y ∈ A := by
  obtain ⟨x, hx, rfl⟩ := h.1.surjOn hy
  rw [h.2.1.1 hx]
  exact hx
section Coordinates
variable {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
theorem singlePullback_ofReal (i : Fin n) (φ : Pt s E → ℝ) :
    singlePullback V z i (fun y => (φ y : ℂ)) = fun u => ((singlePullback V z i φ u : ℝ) : ℂ) := by
  funext u
  by_cases hu : u ∈ localChartDomain (V i) (z i)
  · rw [singlePullback_of_mem _ hu, singlePullback_of_mem _ hu]
  · rw [singlePullback_of_notMem _ hu, singlePullback_of_notMem _ hu, Complex.ofReal_zero]
theorem singlePushforward_ofReal (i : Fin n) (g : Pt s .euclidean → ℝ) :
    singlePushforward V z i (fun u => (g u : ℂ)) =
      fun y => ((singlePushforward V z i g y : ℝ) : ℂ) := by
  funext y
  exact congrFun (chartPushforward_ofReal (fun _ : Fin 1 => V i) (fun _ => z i)
    (fun v => g (v 0))) (fun _ => y)
theorem asFunctionOnOnePoint_singlePullback (i : Fin n) (φ : Pt s E → ℝ) :
    asFunctionOnOnePoint (singlePullback V z i φ) = coordPullback V z i (asFunctionOnOnePoint φ) := by
  funext v
  have h := congrFun (chartPullback_ofReal (fun _ : Fin 1 => V i) (fun _ => z i)
    (fun y : Tuple s E 1 => φ (y 0))) v
  refine Eq.trans ?_ h.symm
  show ((chartPullback (fun _ : Fin 1 => V i) (fun _ => z i) (fun y : Tuple s E 1 => φ (y 0))
    (fun _ => v 0) : ℝ) : ℂ) = _
  rw [const_apply_zero_eq]
theorem asFunctionOnOnePoint_singlePushforward (i : Fin n) (g : Pt s .euclidean → ℝ) :
    asFunctionOnOnePoint (singlePushforward V z i g) =
      coordPushforward V z i (asFunctionOnOnePoint g) := by
  funext v
  have h := congrFun (chartPushforward_ofReal (fun _ : Fin 1 => V i) (fun _ => z i)
    (fun y : Tuple s .euclidean 1 => g (y 0))) v
  refine Eq.trans ?_ h.symm
  show ((chartPushforward (fun _ : Fin 1 => V i) (fun _ => z i)
    (fun y : Tuple s .euclidean 1 => g (y 0)) (fun _ => v 0) : ℝ) : ℂ) = _
  rw [const_apply_zero_eq]
theorem singlePullback_mem_testFns {i : Fin n} (h : TransportCoord V z i) {φ : Pt s E → ℝ}
    (hφ : IsRealTestFn (V i) φ) :
    asFunctionOnOnePoint (singlePullback V z i φ) ∈
      testFns (singletonTuples (localChartDomain (V i) (z i))) := by
  rw [asFunctionOnOnePoint_singlePullback]
  have hm : coordPullback V z i (asFunctionOnOnePoint φ) ∈ coordTestFns V z i :=
    h.1.1.mapsTo hφ
  have he : singletonTuples (localChartDomain (V i) (z i)) =
      boxSet fun _ : Fin 1 => localChartDomain (V i) (z i) :=
    singletonTupleSet_eq_boxSet _
  rw [he]
  exact hm
theorem isRealTestFn_singlePushforward {i : Fin n} (h : TransportCoord V z i)
    {g : Pt s .euclidean → ℝ}
    (hg : asFunctionOnOnePoint g ∈ testFns (singletonTuples (localChartDomain (V i) (z i)))) :
    IsRealTestFn (V i) (singlePushforward V z i g) := by
  have he : singletonTuples (localChartDomain (V i) (z i)) =
      boxSet fun _ : Fin 1 => localChartDomain (V i) (z i) :=
    singletonTupleSet_eq_boxSet _
  rw [he] at hg
  have hm := mem_of_isLinearBijOnWithInv h.1 (y := asFunctionOnOnePoint g) hg
  unfold IsRealTestFn
  rw [asFunctionOnOnePoint_singlePushforward]
  exact hm
theorem singlePushforward_mem {i : Fin n} (h : TransportCoord V z i) {g : Pt s .euclidean → ℝ}
    (hg : g ∈ c1CompactSupportIn (localChartDomain (V i) (z i))) :
    singlePushforward V z i g ∈ c1CompactSupportIn (V i) :=
  h.2.2.2.1.1.mapsTo hg
theorem singlePullback_mem {i : Fin n} (h : TransportCoord V z i) {φ : Pt s E → ℝ}
    (hφ : φ ∈ c1CompactSupportIn (V i)) :
    singlePullback V z i φ ∈ c1CompactSupportIn (localChartDomain (V i) (z i)) :=
  mem_of_isLinearBijOnWithInv h.2.2.2.1 hφ
theorem singlePushforward_singlePullback {i : Fin n} (h : TransportCoord V z i)
    {φ : Pt s E → ℝ} (hφ : φ ∈ c1CompactSupportIn (V i)) :
    singlePushforward V z i (singlePullback V z i φ) = φ :=
  h.2.2.2.1.2.1.2 hφ
end Coordinates
def extendByZero (Φ : TupleForm (sepTuples s E n)) (f : Fin n → Pt s E → ℝ) : ℂ :=
  open Classical in if h : f ∈ sepTuples s E n then Φ ⟨f, h⟩ else 0
theorem extendByZero_of_mem (Φ : TupleForm (sepTuples s E n)) {f : Fin n → Pt s E → ℝ}
    (h : f ∈ sepTuples s E n) : extendByZero Φ f = Φ ⟨f, h⟩ :=
  dif_pos h
def pulledForm (Φ : TupleForm (sepTuples s E n)) (V : Fin n → Set (Pt s E))
    (z : Fin n → Fin 4 → ℝ) : EntryTuple (fun i => localChartDomain (V i) (z i)) → ℝ :=
  fun g => (extendByZero Φ fun i => singlePushforward V z i (g i).1).re
theorem pulledForm_isMultilinearOnComponents (hP : SeparationAndProductFacts.statement) (hn : 1 ≤ n)
    {Φ : TupleForm (sepTuples s E n)} (hΦ : TupleForm.IsMultilinear Φ) {R d : ℝ}
    {V : Fin n → Set (Pt s E)} (hV : IsSeparatedOpenFamily R d V) {z : Fin n → Fin 4 → ℝ}
    (hone : ∀ i, TransportCoord V z i) : IsMultilinearOnComponents (pulledForm Φ V z) := by
  intro g i u v w a b hw
  set f : Fin n → Pt s E → ℝ :=
    fun j => singlePushforward V z j (Function.update g i u j).1 with hf
  set f' : Fin n → Pt s E → ℝ :=
    fun j => singlePushforward V z j (Function.update g i v j).1 with hf'
  have hfm : f ∈ sepTuples s E n :=
    mem_sepTuples_of_family hP hn hV fun j =>
      singlePushforward_mem (hone j) (Function.update g i u j).2
  have hfm' : f' ∈ sepTuples s E n :=
    mem_sepTuples_of_family hP hn hV fun j =>
      singlePushforward_mem (hone j) (Function.update g i v j).2
  have hagree : ∀ j, j ≠ i → f j = f' j := by
    intro j hj
    simp only [hf, hf', Function.update_of_ne hj]
  have hsp := ((hP s n hn).1 .euclidean).c1_isSpace (localChartDomain (V i) (z i))
  have hD := (hone i).2.2.2.1
  have hau : a • u.1 ∈ c1CompactSupportIn (localChartDomain (V i) (z i)) := by
    simpa using (hsp.2 u.1 u.2 u.1 u.2 a 0).1
  have hbv : b • v.1 ∈ c1CompactSupportIn (localChartDomain (V i) (z i)) := by
    simpa using (hsp.2 v.1 v.2 v.1 v.2 b 0).1
  have hkey : singlePushforward V z i w.1 = a • f i + b • f' i := by
    rw [hw, hD.2.2.1 _ hau _ hbv, hD.2.2.2 a _ u.2, hD.2.2.2 b _ v.2]
    simp [hf, hf']
  have heq : (fun j => singlePushforward V z j (Function.update g i w j).1) =
      Function.update f i (a • f i + b • f' i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact hkey
    · simp only [Function.update_of_ne hj, hf]
  have hmem : Function.update f i (a • f i + b • f' i) ∈ sepTuples s E n := by
    rw [← heq]
    exact mem_sepTuples_of_family hP hn hV fun j =>
      singlePushforward_mem (hone j) (Function.update g i w j).2
  have hlin : Φ ⟨_, hmem⟩ = (a : ℂ) * Φ ⟨f, hfm⟩ + (b : ℂ) * Φ ⟨f', hfm'⟩ :=
    hΦ i a b ⟨f, hfm⟩ ⟨f', hfm'⟩ hagree hmem
  show (extendByZero Φ fun j => singlePushforward V z j (Function.update g i w j).1).re =
    a * (extendByZero Φ f).re + b * (extendByZero Φ f').re
  rw [heq, extendByZero_of_mem Φ hmem, extendByZero_of_mem Φ hfm, extendByZero_of_mem Φ hfm', hlin]
  simp
theorem ambientSharpNorm_nonneg (M : Set.Ici (1 : ℝ)) (f : Pt s E → ℝ) :
    0 ≤ ambientSharpNorm s M E f := by
  have hM : 0 ≤ (M : ℝ) := le_trans zero_le_one M.2
  cases E <;>
    exact le_max_of_le_right
      (mul_nonneg (mul_nonneg (by norm_num) hM) (Real.sInf_nonneg fun C hC => hC.1))
theorem pulledForm_isGradNormBounded (hP : SeparationAndProductFacts.statement)
    (hS : GradientC1Bounds.Statement) (hn : 1 ≤ n)
    {M : Set.Ici (1 : ℝ)} {Φ : TupleForm (sepTuples s E n)} {R d r C : ℝ}
    {V : Fin n → Set (Pt s E)} (hV : IsSeparatedOpenFamily R d V) {z : Fin n → Fin 4 → ℝ}
    (hone : ∀ i, TransportCoord V z i)
    (hball : ∀ i, V i ⊆ closedBall s E (proj s E (z i)) r)
    (hb : BoundedAt M Φ C d r) (hC0 : 0 ≤ C) :
    IsGradNormBounded ((40 * (M : ℝ)) ^ n * C) (pulledForm Φ V z) := by
  intro g
  set f : Fin n → Pt s E → ℝ := fun i => singlePushforward V z i (g i).1 with hf
  have hmem : ∀ i, f i ∈ c1CompactSupportIn (V i) :=
    fun i => singlePushforward_mem (hone i) (g i).2
  have hfm : f ∈ sepTuples s E n := mem_sepTuples_of_family hP hn hV hmem
  have hsupp : SupportsInBalls r f := fun i => ⟨_, (hmem i).2.2.trans (hball i)⟩
  have hsepd : ENNReal.ofReal d ≤ supportGap f :=
    le_iInf fun i => le_iInf fun i' => le_iInf fun hne =>
      (hV.separated i i' hne).trans (setDist_anti (hmem i).2.2 (hmem i').2.2)
  have h1 := hb ⟨f, hfm⟩ hsupp hsepd
  have hM : 0 ≤ 40 * (M : ℝ) := mul_nonneg (by norm_num) (le_trans zero_le_one M.2)
  have h2 : ∀ i, ENNReal.ofReal (ambientSharpNorm s M E (f i)) ≤
      ENNReal.ofReal (40 * (M : ℝ)) * c1GradNorm (fun u => ((g i).1 u : ℂ)) := by
    intro i
    have hcl : IsCnAtPoint 1 (fun x => (f i x : ℂ)) := (hmem i).1
    have hco : IsCompact (closedSupport (ofSinglePoint fun x => (f i x : ℂ))) := by
      show IsCompact (closedSupport (asFunctionOnOnePoint (f i)))
      rw [closedSupport_asFunctionOnOnePoint]
      exact (Homeomorph.funUnique (Fin 1) (Pt s E)).isCompact_preimage.2 (hmem i).2.1
    have h3 := ((hS s E).2 M (f i) hcl hco).2.2.2
    have h4 : c1GradNorm (fun y => ((f i y : ℝ) : ℂ)) =
        c1GradNorm (fun u => ((g i).1 u : ℂ)) := (hone i).2.2.2.2 (g i).1 (g i).2
    rwa [h4] at h3
  have hre : pulledForm Φ V z g = (Φ ⟨f, hfm⟩).re := by
    show (extendByZero Φ f).re = _
    rw [extendByZero_of_mem Φ hfm]
  calc ENNReal.ofReal |pulledForm Φ V z g| ≤ ENNReal.ofReal ‖Φ ⟨f, hfm⟩‖ := by
        rw [hre]
        exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
    _ ≤ ENNReal.ofReal (C * ∏ i, ambientSharpNorm s M E (f i)) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal C * ∏ i, ENNReal.ofReal (ambientSharpNorm s M E (f i)) := by
        rw [ENNReal.ofReal_mul hC0,
          ENNReal.ofReal_prod_of_nonneg fun i _ => ambientSharpNorm_nonneg _ _]
    _ ≤ ENNReal.ofReal C * ∏ i, (ENNReal.ofReal (40 * (M : ℝ)) *
          c1GradNorm (fun u => ((g i).1 u : ℂ))) := by
        gcongr with i
        exact h2 i
    _ = ENNReal.ofReal ((40 * (M : ℝ)) ^ n * C) *
          ∏ i, c1GradNorm (fun u => ((g i).1 u : ℂ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_mul (pow_nonneg hM n), ENNReal.ofReal_pow hM]
        ring
theorem distribPullback_of_mem {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
    (T : testFns (boxChartDomain V z) → ℂ) (F : testFns (boxSet V))
    (h : chartPullback V z F.1 ∈ testFns (boxChartDomain V z)) :
    distribPullback V z T F = T ⟨_, h⟩ :=
  dif_pos h
theorem distribPushforward_of_mem {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
    (T : testFns (boxSet V) → ℂ) (H : testFns (boxChartDomain V z))
    (h : chartPushforward V z H.1 ∈ testFns (boxSet V)) :
    distribPushforward V z T H = T ⟨_, h⟩ :=
  dif_pos h
theorem isRealTestFn_of_mem_singletonTuples {A : Set (Pt s .euclidean)}
    {g : Pt s .euclidean → ℝ} (h : asFunctionOnOnePoint g ∈ testFns (singletonTuples A)) :
    IsRealTestFn A g := by
  have he : singletonTuples A = boxSet fun _ : Fin 1 => A := singletonTupleSet_eq_boxSet _
  rw [he] at h
  exact h
theorem ofReal_re_of_isReal {Φ : TupleForm (sepTuples s E n)} (hΦ : TupleForm.IsReal Φ)
    (f : sepTuples s E n) : (((Φ f).re : ℝ) : ℂ) = Φ f :=
  Complex.ext (by simp) (by simp [hΦ f])
theorem isSmallOpenTuple_of_nonempty (hn : 1 ≤ n) {R d : ℝ} {V : Fin n → Set (Pt s E)}
    (hV : IsSeparatedOpenFamily R d V) (hne : ∀ i, (V i).Nonempty) : IsSmallOpenTuple V := by
  refine ⟨hn, fun i => ⟨hV.isOpen i, hne i, ?_⟩⟩
  cases E with
  | torus => exact hV.setDiam_lt_of_torus rfl i
  | euclidean => exact (hV.setDiam_le i).trans_lt ENNReal.ofReal_lt_top
theorem of_nonempty_members (hT : ChartTransport.statement)
    (hK : BoundedMultilinearFormIsDistribution)
    (hP : SeparationAndProductFacts.statement) (hC : TestFnOperations)
    (hS : GradientC1Bounds.Statement) (hn : 1 ≤ n)
    {M : Set.Ici (1 : ℝ)} {Φ : TupleForm (sepTuples s E n)} (hΦr : TupleForm.IsReal Φ)
    (hΦm : TupleForm.IsMultilinear Φ) {c : ℝ → ℝ → ℝ}
    (hc : ∀ d : ℝ, 0 < d → ∀ R : ℝ, 0 < R → ENNReal.ofReal R < injRadius s E →
      0 ≤ c d R ∧ BoundedAt M Φ (c d R) d R)
    {R d : ℝ} {V : Fin n → Set (Pt s E)} (hV : IsSeparatedOpenFamily R d V)
    (hne : ∀ i, (V i).Nonempty) :
    (∃! T, IsBoxDistrib Φ V T) ∧
      DenseInTestFns (boxSet V) (tensorSums V) ∧
      (0 < maxDiam V ∧ maxDiam V < injRadius s E) ∧
      BoxBound M c R d V (boxDistrib Φ V) ∧
      HasOrderLE (5 * n + 1) (boxDistrib Φ V) := by
  obtain ⟨⟨z, hz⟩, hall⟩ := hT s E n V (isSmallOpenTuple_of_nonempty hn hV hne)
  obtain ⟨⟨hr0, hrq⟩, hent, htup, -, -, htr, hone, htens, hdense⟩ := hall z hz
  have hle : maxDiam V ≤ ENNReal.ofReal (2 * R) := iSup_le hV.setDiam_le
  have hRpos := hV.radius_pos
  have hrtop : maxDiam V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hrpos : 0 < (maxDiam V).toReal := ENNReal.toReal_pos hr0.ne' hrtop
  have hr2R : (maxDiam V).toReal ≤ 2 * R :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  have hrq' : ENNReal.ofReal (maxDiam V).toReal < injRadius s E := by
    rw [ENNReal.ofReal_toReal hrtop]
    exact hrq
  obtain ⟨hc0, hcb⟩ := hc d hV.gap_pos _ hrpos hrq'
  have hM : 0 ≤ 40 * (M : ℝ) := mul_nonneg (by norm_num) (le_trans zero_le_one M.2)
  have hcc : 0 ≤ (40 * (M : ℝ)) ^ n * c d (maxDiam V).toReal :=
    mul_nonneg (pow_nonneg hM n) hc0
  have hOball : IsOpenTupleInBall (2 * R) (fun i => localChartDomain (V i) (z i)) :=
    ⟨hn, by positivity, fun i => ⟨(hent i).1, fun u hu =>
      le_trans ((hent i).2.2.2.2.1 hu) hr2R⟩⟩
  have hlin := pulledForm_isMultilinearOnComponents hP hn hΦm hV hone
  have hbd := pulledForm_isGradNormBounded hP hS hn hV hone (fun i => (hent i).2.2.2.2.2) hcb hc0
  obtain ⟨hcut, ⟨T0, hT0, hT0u⟩, hprop⟩ := hK s n (2 * R) _ _ hOball hcc _ hlin hbd
  have hTVd := htr.2.2.2.1 T0 hT0.1
  have hagree : MatchesOnTensors Φ V (distribPullback V z T0) := by
    intro φ hφ
    have hmem : ∀ i, φ i ∈ c1CompactSupportIn (V i) :=
      fun i => c1CompactSupportIn_of_isRealTestFn (hφ i)
    have hsep := mem_sepTuples_of_family hP hn hV hmem
    have hF := realTensor_mem_testFns hC hn hV.isOpen hφ
    refine ⟨hsep, hF, ?_⟩
    have hpm : chartPullback V z (realTensor φ) ∈ testFns (boxChartDomain V z) :=
      htr.1.1.mapsTo hF
    obtain ⟨hgE, hF', hval⟩ := hT0.2 (fun i => singlePullback V z i (φ i))
      (fun i => singlePullback_mem_testFns (hone i) (hφ i))
    have e1 : chartPullback V z (realTensor φ) =
        tensorProd (fun i y => ((singlePullback V z i (φ i) y : ℝ) : ℂ)) := by
      refine (htens.1 (fun i x => (φ i x : ℂ)) hφ).trans ?_
      congr 1
      funext i
      exact singlePullback_ofReal i (φ i)
    have e2 : (fun i => singlePushforward V z i (singlePullback V z i (φ i))) = φ :=
      funext fun i => singlePushforward_singlePullback (hone i) (hmem i)
    have e3 : pulledForm Φ V z (fun i => ⟨singlePullback V z i (φ i), hgE i⟩) =
        (Φ ⟨φ, hsep⟩).re := by
      show (extendByZero Φ fun i =>
        singlePushforward V z i (singlePullback V z i (φ i))).re = _
      rw [e2, extendByZero_of_mem Φ hsep]
    rw [distribPullback_of_mem T0 ⟨_, hF⟩ hpm]
    calc T0 ⟨_, hpm⟩ = T0 ⟨_, hF'⟩ := congrArg T0 (Subtype.ext e1)
      _ = ((pulledForm Φ V z fun i => ⟨singlePullback V z i (φ i), hgE i⟩ : ℝ) : ℂ) := hval
      _ = Φ ⟨φ, hsep⟩ := by rw [e3]; exact ofReal_re_of_isReal hΦr _
  have huniq : ∀ T', IsBoxDistrib Φ V T' → T' = distribPullback V z T0 := by
    rintro T' ⟨hT'd, hT'a⟩
    have hform : IsDistribExtending (pulledForm Φ V z) (distribPushforward V z T') := by
      refine ⟨htr.2.2.2.2 T' hT'd, fun g hg => ?_⟩
      have hgt : ∀ i, IsRealTestFn (localChartDomain (V i) (z i)) (g i) :=
        fun i => isRealTestFn_of_mem_singletonTuples (hg i)
      have hgE : ∀ i, g i ∈ entrySpace (fun i => localChartDomain (V i) (z i)) i :=
        fun i => c1CompactSupportIn_of_isRealTestFn (hgt i)
      have hFg : tensorProd (fun i y => ((g i y : ℝ) : ℂ)) ∈
          testFns (boxSet fun i => localChartDomain (V i) (z i)) :=
        realTensor_mem_testFns hC hn (fun i => (hent i).1) hgt
      refine ⟨hgE, hFg, ?_⟩
      have hf := fun i => isRealTestFn_singlePushforward (hone i) (hg i)
      obtain ⟨hsep, hF, hval⟩ := hT'a (fun i => singlePushforward V z i (g i)) hf
      have hpm : chartPushforward V z (tensorProd fun i y => ((g i y : ℝ) : ℂ)) ∈
          testFns (boxSet V) := mem_of_isLinearBijOnWithInv htr.1 hFg
      have e1 : chartPushforward V z (tensorProd fun i y => ((g i y : ℝ) : ℂ)) =
          realTensor (fun i => singlePushforward V z i (g i)) := by
        refine (htens.2 (fun i y => ((g i y : ℝ) : ℂ)) (fun i => hgt i)).trans ?_
        show tensorProd _ = tensorProd _
        congr 1
        funext i
        exact singlePushforward_ofReal i (g i)
      have e3 : pulledForm Φ V z (fun i => ⟨g i, hgE i⟩) = (Φ ⟨_, hsep⟩).re := by
        show (extendByZero Φ fun i => singlePushforward V z i (g i)).re = _
        rw [extendByZero_of_mem Φ hsep]
      refine (distribPushforward_of_mem T' ⟨_, hFg⟩ hpm).trans ?_
      calc T' ⟨_, hpm⟩ = T' ⟨_, hF⟩ := congrArg T' (Subtype.ext e1)
        _ = Φ ⟨_, hsep⟩ := hval
        _ = _ := by rw [e3]; exact (ofReal_re_of_isReal hΦr _).symm
    have hT0eq := hT0u _ hform
    funext F
    have hpm : chartPullback V z F.1 ∈ testFns (boxChartDomain V z) := htr.1.1.mapsTo F.2
    have hback : chartPushforward V z (chartPullback V z F.1) = F.1 := htr.1.2.1.1 F.2
    have hpb : chartPushforward V z (chartPullback V z F.1) ∈ testFns (boxSet V) := by
      rw [hback]
      exact F.2
    rw [distribPullback_of_mem T0 F hpm]
    have h1 := congrFun hT0eq ⟨_, hpm⟩
    rw [distribPushforward_of_mem T' ⟨_, hpm⟩ hpb] at h1
    refine Eq.trans ?_ h1
    exact congrArg T' (Subtype.ext hback.symm)
  have hspec : IsBoxDistrib Φ V (distribPullback V z T0) := ⟨hTVd.1, hagree⟩
  have hdist : boxDistrib Φ V = distribPullback V z T0 :=
    huniq _ (isBoxDistrib_boxDistrib ⟨_, hspec⟩)
  refine ⟨⟨_, hspec, huniq⟩, hdense, ⟨hr0, hrq⟩, ?_, ?_⟩
  · rw [hdist]
    intro F χ hχ hχ1
    have hpm : chartPullback V z F.1 ∈ testFns (boxChartDomain V z) := htr.1.1.mapsTo F.2
    have hcutoff : IsCutoff (fun i => localChartDomain (V i) (z i))
        (fun i => singlePullback V z i (χ i)) :=
      fun i => singlePullback_mem_testFns (hone i) (hχ i)
    have hones : CutOffIsOneOnProjections (chartPullback V z F.1)
        (fun i => singlePullback V z i (χ i)) := by
      rintro i _ ⟨u, hu, rfl⟩
      rw [(htr.2.1 F.1 F.2).2] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      have hwV := F.2.2.2 hw
      have huO : boxChartInv V z w ∈ boxChartDomain V z := by
        obtain ⟨x, hx, rfl⟩ := htup.2.2.1.surjOn hwV
        rw [htup.2.2.2.1.1 hx]
        exact hx
      have hchart : boxChart s E z (boxChartInv V z w) = w := htup.2.2.2.1.2 hwV
      have hi : boxChartInv V z w i ∈ localChartDomain (V i) (z i) := huO i (mem_univ i)
      show singlePullback V z i (χ i) (boxChartInv V z w i) = 1
      rw [singlePullback_of_mem _ hi]
      have hcw : localChart s E (z i) (boxChartInv V z w i) = w i := congrFun hchart i
      rw [hcw]
      obtain ⟨N, ⟨O', -, hsub, hON⟩, h1⟩ := hχ1 i
      exact h1 _ (hON (hsub ⟨w, hw, rfl⟩))
    have hcf := (hcut ⟨_, hpm⟩).1 _ hcutoff hones
    have hb := (hprop T0 hT0).1 ⟨_, hpm⟩ _ hcf
    have hnorm := (htr.2.1 F.1 F.2).1 (5 * n + 1)
    have hgrad : ∀ i, c1GradNorm (fun x => ((singlePullback V z i (χ i) x : ℝ) : ℂ)) =
        c1GradNorm (fun y => ((χ i y : ℝ) : ℂ)) := by
      intro i
      have hm := c1CompactSupportIn_of_isRealTestFn (hχ i)
      have h4 := (hone i).2.2.2.2 _ (singlePullback_mem (hone i) hm)
      rw [singlePushforward_singlePullback (hone i) hm] at h4
      exact h4.symm
    rw [distribPullback_of_mem T0 F hpm]
    have hfac : boxBoundConst n M R (c d (maxDiam V).toReal) =
        2 ^ n * ((40 * (M : ℝ)) ^ n * c d (maxDiam V).toReal) *
          bumpNumber n (2 * R) := by
      simp only [boxBoundConst]
      ring
    rw [hfac, ← hnorm]
    simp only [hgrad] at hb
    exact hb
  · rw [hdist]
    exact hTVd.2 _ (hprop T0 hT0).2
theorem of_empty_member (hP : SeparationAndProductFacts.statement) (hC : TestFnOperations)
    (hTop : TupleTopology.Holds) (hn : 1 ≤ n) {Φ : TupleForm (sepTuples s E n)}
    (hΦm : TupleForm.IsMultilinear Φ) {R d : ℝ} {V : Fin n → Set (Pt s E)}
    (hV : IsSeparatedOpenFamily R d V) {i₀ : Fin n} (hi : V i₀ = ∅) :
    (∃! T, IsBoxDistrib Φ V T) ∧
      DenseInTestFns (boxSet V) (tensorSums V) ∧
      HasOrderLE (5 * n + 1) (boxDistrib Φ V) := by
  have hE : boxSet V = ∅ := by
    ext y
    simp only [mem_empty_iff_false, iff_false]
    intro hy
    have h0 := hy i₀ (mem_univ _)
    rw [hi] at h0
    exact h0
  have hzeroT : ∀ T : testFns (boxSet V) → ℂ, IsComplexLinearForm T → ∀ F, T F = 0 :=
    fun T h F => linearForm_apply_eq_zero h F (eq_zero_of_mem_testFns_empty hE F.2)
  have hlin0 : IsDistrib (fun _ : testFns (boxSet V) => (0 : ℂ)) :=
    ⟨⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩, fun K _ _ => ⟨0, 0, fun F _ => by simp⟩⟩
  have hagree : MatchesOnTensors Φ V (fun _ => 0) := by
    intro φ hφ
    have hmem : ∀ i, φ i ∈ c1CompactSupportIn (V i) :=
      fun i => c1CompactSupportIn_of_isRealTestFn (hφ i)
    have hsep := mem_sepTuples_of_family hP hn hV hmem
    refine ⟨hsep, realTensor_mem_testFns hC hn hV.isOpen hφ, ?_⟩
    have hz : ∀ y, φ i₀ y = 0 := fun y => image_eq_zero_of_notMem_tsupport fun hy => by
      have h0 := (hmem i₀).2.2 hy
      rw [hi] at h0
      exact h0
    exact (((hP s n hn).1 E).eq_zero_of_entry_eq_zero Φ hΦm ⟨φ, hsep⟩ i₀ hz).symm
  have hspec : IsBoxDistrib Φ V (fun _ => 0) := ⟨hlin0, hagree⟩
  refine ⟨⟨_, hspec, fun T hT => funext fun F => hzeroT T hT.1.1 F⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro F ⟨m, φ, hφ, rfl⟩
    have hz : ∀ k, tensorProd (φ k) = 0 := by
      intro k
      have hE1 : boxSet (fun _ : Fin 1 => V i₀) = ∅ := by
        ext y
        simp only [mem_empty_iff_false, iff_false]
        intro hy
        have h0 := hy 0 (mem_univ _)
        rw [hi] at h0
        exact h0
      have h0 : ofSinglePoint (φ k i₀) = 0 := eq_zero_of_mem_testFns_empty hE1 (hφ k i₀)
      funext x
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (congrFun h0 fun _ => x i₀)
    simp only [hz, Finset.sum_const_zero]
    exact zero_mem_testFns _
  · intro F hF
    rw [eq_zero_of_mem_testFns_empty hE hF]
    refine ⟨fun _ => 0, fun _ => ⟨0, fun k => k.elim0, fun k => k.elim0, by simp⟩,
      fun _ => zero_mem_testFns _, zero_mem_testFns _,
      ⟨∅, isCompact_empty, empty_subset _, by rw [closedSupport_zero],
        fun _ => by rw [closedSupport_zero]⟩,
      fun ν => ?_⟩
    show Filter.Tendsto (fun _ => cnNorm ν ((0 : Tuple s E n → ℂ) - 0)) _ _
    rw [sub_zero, cnNorm_zero hTop hn]
    exact tendsto_const_nhds
  · have hd := isBoxDistrib_boxDistrib ⟨_, hspec⟩
    exact ⟨hd.1, fun K _ _ => ⟨0, fun F _ => by rw [hzeroT _ hd.1.1 F]; simp⟩⟩
theorem boxDistribs_and_order (hT : ChartTransport.statement)
    (hK : BoundedMultilinearFormIsDistribution)
    (hP : SeparationAndProductFacts.statement) (hC : TestFnOperations)
    (hS : GradientC1Bounds.Statement)
    (hTop : TupleTopology.Holds) (hn : 1 ≤ n)
    {M : Set.Ici (1 : ℝ)} {Φ : TupleForm (sepTuples s E n)} (hΦr : TupleForm.IsReal Φ)
    (hΦm : TupleForm.IsMultilinear Φ) {c : ℝ → ℝ → ℝ}
    (hc : ∀ d : ℝ, 0 < d → ∀ R : ℝ, 0 < R → ENNReal.ofReal R < injRadius s E →
      0 ≤ c d R ∧ BoundedAt M Φ (c d R) d R) :
    HasBoxDistribs M c Φ ∧
      ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
        HasOrderLE (5 * n + 1) (boxDistrib Φ V) := by
  refine ⟨fun R d V hV => ?_, fun R d V hV => ?_⟩
  · by_cases hne : ∀ i, (V i).Nonempty
    · obtain ⟨h1, h2, h3, h4, -⟩ := of_nonempty_members hT hK hP hC hS hn hΦr hΦm hc hV hne
      exact ⟨h1, h2, fun _ => ⟨h3.1, h3.2, h4⟩⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hne
      obtain ⟨h1, h2, -⟩ :=
        of_empty_member hP hC hTop hn hΦm hV (Set.not_nonempty_iff_eq_empty.mp hi)
      exact ⟨h1, h2, fun hall => absurd (hall i) hi⟩
  · by_cases hne : ∀ i, (V i).Nonempty
    · exact (of_nonempty_members hT hK hP hC hS hn hΦr hΦm hc hV hne).2.2.2.2
    · obtain ⟨i, hi⟩ := not_forall.mp hne
      exact (of_empty_member hP hC hTop hn hΦm hV (Set.not_nonempty_iff_eq_empty.mp hi)).2.2
theorem standingSide_pos (s : Conventions.StandingParameters) : 0 < s.side := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusMirrors.AxisReflection.side_pos <;> assumption
theorem pointDist_nonneg (a b : Pt s E) : 0 ≤ pointDist s E a b :=
  (dist_nonneg : 0 ≤ dist a b)
theorem exists_small_radius (s : Conventions.StandingParameters) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ / 3 ∧ η ≤ s.side / 16 :=
  ⟨min (δ / 3) (s.side / 16), lt_min (by positivity) (by have := standingSide_pos s; positivity),
    min_le_left _ _, min_le_right _ _⟩
theorem isSeparatedOpenFamily_balls (hL : DistanceFacts.MetricFactsClaim) {δ η : ℝ} (hη : 0 < η)
    (hη3 : η ≤ δ / 3) (hηs : η ≤ s.side / 16) {y : Fin n → Pt s E}
    (hy : ∀ i i', i ≠ i' → δ ≤ pointDist s E (y i) (y i')) :
    IsSeparatedOpenFamily η (δ / 3) (fun i => openBall s E (y i) η) where
  radius_pos := hη
  gap_pos := by linarith
  isOpen _ := (hL s E).isOpen_openBall _ _ hη
  setDiam_le _ := (hL s E).setDiam_openBall_le _ _ hη
  setDiam_lt_of_torus _ _ := ((hL s E).setDiam_openBall_le _ _ hη).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by have := standingSide_pos s; linarith)).2
      (by have := standingSide_pos s; linarith))
  separated i i' hne := le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (by
    have h1 := hy i i' hne
    have ha' : pointDist s E a (y i) < η := ha
    have hb' : pointDist s E b (y i') < η := hb
    have h2 := pointDist_triangle E (y i) a (y i')
    have h3 := pointDist_triangle E a b (y i')
    have h4 := pointDist_comm E (y i) a
    linarith)
abbrev SeparatedFamily (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ) : Type :=
  {V : Fin n → Set (Pt s E) // ∃ R d : ℝ, IsSeparatedOpenFamily R d V}
theorem iUnion_boxSet_eq (hL : DistanceFacts.MetricFactsClaim) (hn : 1 ≤ n) :
    ⋃ γ : SeparatedFamily s E n, boxSet γ.1 = pairwiseDistinctTuples s E n := by
  apply Subset.antisymm
  · refine iUnion_subset fun γ => ?_
    obtain ⟨V, R, d, hV⟩ := γ
    exact hV.boxSet_subset
  · intro x hx
    have hinj : Function.Injective x := hx
    have hnon : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    let f : Fin n × Fin n → ℝ := fun p => if p.1 = p.2 then 1 else pointDist s E (x p.1) (x p.2)
    obtain ⟨p0, hp0⟩ := Finite.exists_min f
    have hfpos : ∀ p, 0 < f p := by
      intro p
      by_cases h : p.1 = p.2
      · have e : f p = 1 := if_pos h
        rw [e]
        exact one_pos
      · have e : f p = pointDist s E (x p.1) (x p.2) := if_neg h
        rw [e]
        exact lt_of_le_of_ne (pointDist_nonneg _ _)
          fun h0 => h (hinj (eq_of_pointDist_eq_zero E h0.symm))
    have hy : ∀ i i', i ≠ i' → f p0 ≤ pointDist s E (x i) (x i') := by
      intro i i' hne
      have h := hp0 (i, i')
      have e : f (i, i') = pointDist s E (x i) (x i') := if_neg hne
      rwa [e] at h
    obtain ⟨η, h1, h2, h3⟩ := exists_small_radius s (hfpos p0)
    have hfam := isSeparatedOpenFamily_balls hL h1 h2 h3 hy
    refine mem_iUnion.mpr ⟨⟨_, _, _, hfam⟩, fun i _ => ?_⟩
    show pointDist s E (x i) (x i) < η
    rw [pointDist_self]
    exact h1
theorem restrictDistrib_boxDistrib (hC : TestFnOperations)
    (hn : 1 ≤ n) {Φ : TupleForm (sepTuples s E n)}
    (hA : ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
      ∃! T, IsBoxDistrib Φ V T)
    {R d R' d' : ℝ} {V W : Fin n → Set (Pt s E)} (hV : IsSeparatedOpenFamily R d V)
    (hW : IsSeparatedOpenFamily R' d' W) (hWV : ∀ i, W i ⊆ V i)
    (hsub : boxSet W ⊆ boxSet V) :
    restrictDistrib hsub (boxDistrib Φ V) = boxDistrib Φ W := by
  have hspecV := isBoxDistrib_boxDistrib (hA R d V hV).exists
  have hspecW := isBoxDistrib_boxDistrib (hA R' d' W hW).exists
  refine (hA R' d' W hW).unique ⟨?_, ?_⟩ hspecW
  · exact (((hC s E n hn).1 _ _ hsub (isOpen_boxSet hW.isOpen)
      (isOpen_boxSet hV.isOpen)).2.2 _ hspecV.1).1
  · intro φ hφ
    have hφV : ∀ i, IsRealTestFn (V i) (φ i) :=
      fun i => testFns_mono (show boxSet (fun _ : Fin 1 => W i) ⊆
        boxSet fun _ : Fin 1 => V i from fun y hy j hj => hWV i (hy j hj)) (hφ i)
    obtain ⟨hsep, hF, hval⟩ := hspecV.2 φ hφV
    exact ⟨hsep, realTensor_mem_testFns hC hn hW.isOpen hφ, hval⟩
theorem glued_exists_unique (hG : DistributionsGlueUniquely) (hL : DistanceFacts.MetricFactsClaim)
    (hC : TestFnOperations) (hn : 1 ≤ n) {Φ : TupleForm (sepTuples s E n)}
    (hA : ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
      ∃! T, IsBoxDistrib Φ V T)
    (hord : ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
      HasOrderLE (5 * n + 1) (boxDistrib Φ V)) :
    (∃! Ψ, IsGluedDistrib Φ Ψ) ∧ HasOrderLE (5 * n + 1) (formDistrib Φ) := by
  have hopen : ∀ γ : SeparatedFamily s E n, IsOpen (boxSet γ.1) := by
    rintro ⟨V, R, d, hV⟩
    exact isOpen_boxSet hV.isOpen
  have hdist : ∀ γ : SeparatedFamily s E n, IsDistrib (boxDistrib Φ γ.1) := by
    rintro ⟨V, R, d, hV⟩
    exact (isBoxDistrib_boxDistrib (hA R d V hV).exists).1
  have hoverlap : ∀ (γ γ' : SeparatedFamily s E n)
      (F : testFns (boxSet γ.1 ∩ boxSet γ'.1)),
      restrictDistrib inter_subset_left (boxDistrib Φ γ.1) F =
        restrictDistrib inter_subset_right (boxDistrib Φ γ'.1) F := by
    rintro ⟨V, R, d, hV⟩ ⟨V', R', d', hV'⟩ F
    have hWo : ∀ i, IsOpen (V i ∩ V' i) := fun i => (hV.isOpen i).inter (hV'.isOpen i)
    have hW := IsSeparatedOpenFamily.ofSubsets hV hWo fun i => inter_subset_left
    have hset : boxSet (fun i => V i ∩ V' i) = boxSet V ∩ boxSet V' := by
      ext y
      simp [boxSet, Set.mem_pi, forall_and]
    have hF : F.1 ∈ testFns (boxSet fun i => V i ∩ V' i) := by
      rw [hset]
      exact F.2
    have h1 := restrictDistrib_boxDistrib hC hn hA hV hW (fun i => inter_subset_left)
      (fun y hy i hi => (hy i hi).1)
    have h2 := restrictDistrib_boxDistrib hC hn hA hV' hW (fun i => inter_subset_right)
      (fun y hy i hi => (hy i hi).2)
    exact (congrFun h1 ⟨F.1, hF⟩).trans (congrFun h2 ⟨F.1, hF⟩).symm
  obtain ⟨⟨S, ⟨hSd, hSr⟩, hSu⟩, hSord⟩ := hG s E n hn (pairwiseDistinctTuples s E n)
    isOpen_pairwiseDistinctTuples (SeparatedFamily s E n) (fun γ => boxSet γ.1) hopen
    (iUnion_boxSet_eq hL hn) (fun γ => boxDistrib Φ γ.1) hdist hoverlap
  have hIS : IsGluedDistrib Φ S := ⟨hSd, fun R d V hV => hSr ⟨V, R, d, hV⟩⟩
  have huq : ∀ Ψ, IsGluedDistrib Φ Ψ → Ψ = S := fun Ψ hΨ => hSu Ψ ⟨hΨ.1, by
    rintro ⟨V, R, d, hV⟩
    exact hΨ.2 R d V hV⟩
  have hdf := isGluedDistrib_formDistrib ⟨S, hIS⟩
  refine ⟨⟨S, hIS, huq⟩, hSord (5 * n + 1) ?_ _ hdf.1 ?_⟩
  · rintro ⟨V, R, d, hV⟩
    exact hord R d V hV
  · rintro ⟨V, R, d, hV⟩
    exact hdf.2 R d V hV
def IsSmoothInside (A : Fin n → Set (Pt s E)) (g : Fin n → Pt s E → ℝ) : Prop :=
  ∀ l, asFunctionOnOnePoint (g l) ∈ testFns (singletonTupleSet (univ : Set (Pt s E))) ∧
    tsupport (g l) ⊆ A l
def ExtendsAt (Φ : TupleForm (sepTuples s E n)) (Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ)
    (g : Fin n → Pt s E → ℝ) : Prop :=
  ∃ (hg : g ∈ sepTuples s E n)
    (hF : realTensor g ∈ testFns (pairwiseDistinctTuples s E n)), Ψ ⟨_, hF⟩ = Φ ⟨g, hg⟩
theorem isOpen_singletonTupleSet_univ : IsOpen (singletonTupleSet (univ : Set (Pt s E))) := by
  have h : singletonTupleSet (univ : Set (Pt s E)) = univ := by
    ext y
    simp [singletonTupleSet]
  rw [h]
  exact isOpen_univ
theorem mem_c1ProductOver_of_smoothInside {A : Fin n → Set (Pt s E)} (hAc : ∀ l, IsCompact (A l))
    {g : Fin n → Pt s E → ℝ} (hg : IsSmoothInside A g) : g ∈ c1ProductOver A :=
  fun l _ => ⟨⟨(hg l).1.1.1, fun m _ => (hg l).1.1.2 m le_top⟩,
    (hAc l).of_isClosed_subset (isClosed_tsupport _) (hg l).2, (hg l).2⟩
theorem tsupport_ofReal_comp (f : Pt s E → ℝ) : tsupport (fun x => (f x : ℂ)) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support]
theorem realTensor_mem_pairwiseDistinct (hC : TestFnOperations)
    (hn : 1 ≤ n) {A : Fin n → Set (Pt s E)} (hAd : PairwiseDisjointFamily A)
    {g : Fin n → Pt s E → ℝ} (hg : IsSmoothInside A g) :
    realTensor g ∈ testFns (pairwiseDistinctTuples s E n) := by
  have h := (hC s E n hn).2.2.2 (fun _ => univ) (fun i x => (g i x : ℂ))
    (fun _ => isOpen_univ) (fun i => (hg i).1)
  refine ⟨h.1.1, h.1.2.1, fun y hy => ?_⟩
  have hy' := h.2 hy
  show Function.Injective y
  intro i i' hyy
  by_contra hne
  have h1 : y i ∈ A i := (hg i).2 (by
    have h0 : y i ∈ tsupport (fun x => (g i x : ℂ)) := hy' i (mem_univ i)
    rwa [tsupport_ofReal_comp] at h0)
  have h2 : y i' ∈ A i' := (hg i').2 (by
    have h0 : y i' ∈ tsupport (fun x => (g i' x : ℂ)) := hy' i' (mem_univ i')
    rwa [tsupport_ofReal_comp] at h0)
  rw [← hyy] at h2
  exact Set.disjoint_left.mp (hAd i i' hne) h1 h2
theorem realTensor_update (g : Fin n → Pt s E → ℝ) (l : Fin n) (w : Pt s E → ℝ)
    (x : Tuple s E n) :
    realTensor (Function.update g l w) x =
      (w (x l) : ℂ) * ∏ i ∈ Finset.univ.erase l, (g i (x i) : ℂ) := by
  show ∏ i, ((Function.update g l w i (x i) : ℝ) : ℂ) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
theorem smoothInside_update {A : Fin n → Set (Pt s E)} {g : Fin n → Pt s E → ℝ} {l : Fin n}
    {u w : Pt s E → ℝ} (hu : IsSmoothInside A (Function.update g l u))
    (h1 : asFunctionOnOnePoint w ∈ testFns (singletonTupleSet (univ : Set (Pt s E))))
    (h2 : tsupport w ⊆ A l) : IsSmoothInside A (Function.update g l w) := by
  intro j
  by_cases hj : j = l
  · subst hj
    rw [Function.update_self]
    exact ⟨h1, h2⟩
  · have h := hu j
    rw [Function.update_of_ne hj] at h ⊢
    exact h
theorem smoothInside_update_add (hC : TestFnOperations)
    {A : Fin n → Set (Pt s E)} {g : Fin n → Pt s E → ℝ} {l : Fin n}
    {u v : Pt s E → ℝ} (hu : IsSmoothInside A (Function.update g l u))
    (hv : IsSmoothInside A (Function.update g l v)) :
    IsSmoothInside A (Function.update g l (u + v)) := by
  have hu' := hu l
  have hv' := hv l
  rw [Function.update_self] at hu' hv'
  refine smoothInside_update hu ?_ ?_
  · have hcomb := (((hC s E 1 le_rfl).2.1 _ isOpen_singletonTupleSet_univ).2.1
      (asFunctionOnOnePoint u) hu'.1 (asFunctionOnOnePoint v) hv'.1 1 1).1
    have e : asFunctionOnOnePoint (u + v) =
        (1 : ℂ) • asFunctionOnOnePoint u + (1 : ℂ) • asFunctionOnOnePoint v := by
      funext y
      simp [asFunctionOnOnePoint]
    rw [e]
    exact hcomb
  · exact (closure_mono (Function.support_add u v)).trans
      (closure_union.subset.trans (union_subset hu'.2 hv'.2))
theorem smoothInside_update_zero {A : Fin n → Set (Pt s E)} {g : Fin n → Pt s E → ℝ}
    (hg : IsSmoothInside A g) (l : Fin n) : IsSmoothInside A (Function.update g l 0) := by
  have hg' : IsSmoothInside A (Function.update g l (g l)) := by
    rw [Function.update_eq_self]
    exact hg
  refine smoothInside_update hg' ?_ ?_
  · have e : asFunctionOnOnePoint (0 : Pt s E → ℝ) = 0 := by
      funext y
      simp [asFunctionOnOnePoint]
    rw [e]
    exact zero_mem_testFns _
  · rw [tsupport, Function.support_zero, closure_empty]
    exact empty_subset _
theorem extendsAt_update_add (hP : SeparationAndProductFacts.statement)
    (hC : TestFnOperations) (hn : 1 ≤ n)
    {Φ : TupleForm (sepTuples s E n)} (hΦm : TupleForm.IsMultilinear Φ)
    {Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ} (hΨ : IsDistrib Ψ)
    {A : Fin n → Set (Pt s E)} (hAc : ∀ l, IsCompact (A l)) (hAd : PairwiseDisjointFamily A)
    {g : Fin n → Pt s E → ℝ} {l : Fin n} {u v : Pt s E → ℝ}
    (hu : IsSmoothInside A (Function.update g l u)) (hv : IsSmoothInside A (Function.update g l v))
    (h1 : ExtendsAt Φ Ψ (Function.update g l u)) (h2 : ExtendsAt Φ Ψ (Function.update g l v)) :
    ExtendsAt Φ Ψ (Function.update g l (u + v)) := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  have huv := smoothInside_update_add hC hu hv
  have hm := (hP s n hn).1 E
  have hr := (hm.restrict_isEntrywiseLinear A hAd Φ hΦm).1 l g u v
    (mem_c1ProductOver_of_smoothInside hAc hu) (mem_c1ProductOver_of_smoothInside hAc hv)
    (mem_c1ProductOver_of_smoothInside hAc huv)
  have hsep := hm.c1ProductOver_subset A hAd (mem_c1ProductOver_of_smoothInside hAc huv)
  have hF := realTensor_mem_pairwiseDistinct hC hn hAd huv
  refine ⟨hsep, hF, ?_⟩
  have hadd := hΨ.1.1 ⟨_, b1⟩ ⟨_, b2⟩ ⟨_, hF⟩ (by
    funext x
    simp only [Pi.add_apply, realTensor_update]
    push_cast
    ring)
  rw [hadd, c1, c2]
  exact hr.symm
theorem extendsAt_of_component_zero (hP : SeparationAndProductFacts.statement)
    (hC : TestFnOperations) (hn : 1 ≤ n)
    {Φ : TupleForm (sepTuples s E n)} (hΦm : TupleForm.IsMultilinear Φ)
    {Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ} (hΨ : IsDistrib Ψ)
    {A : Fin n → Set (Pt s E)} (hAc : ∀ l, IsCompact (A l)) (hAd : PairwiseDisjointFamily A)
    {g : Fin n → Pt s E → ℝ} {l : Fin n} (hg : IsSmoothInside A g) (h0 : g l = 0) :
    ExtendsAt Φ Ψ g := by
  have hm := (hP s n hn).1 E
  have hsep := hm.c1ProductOver_subset A hAd (mem_c1ProductOver_of_smoothInside hAc hg)
  have hF := realTensor_mem_pairwiseDistinct hC hn hAd hg
  refine ⟨hsep, hF, ?_⟩
  have hz : realTensor g = 0 := by
    funext x
    show ∏ i, ((g i (x i) : ℝ) : ℂ) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [h0])
  rw [linearForm_apply_eq_zero hΨ.1 ⟨_, hF⟩ hz]
  exact (hm.eq_zero_of_entry_eq_zero Φ hΦm ⟨g, hsep⟩ l fun y => by simp [h0]).symm
theorem extendsAt_update_sum (hP : SeparationAndProductFacts.statement)
    (hC : TestFnOperations) (hn : 1 ≤ n)
    {Φ : TupleForm (sepTuples s E n)} (hΦm : TupleForm.IsMultilinear Φ)
    {Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ} (hΨ : IsDistrib Ψ)
    {A : Fin n → Set (Pt s E)} (hAc : ∀ l, IsCompact (A l)) (hAd : PairwiseDisjointFamily A)
    {g : Fin n → Pt s E → ℝ} {l : Fin n} (hg : IsSmoothInside A g) {ι : Type} (S : Finset ι)
    (w : ι → Pt s E → ℝ) (hw : ∀ a ∈ S, IsSmoothInside A (Function.update g l (w a)))
    (hh : ∀ a ∈ S, ExtendsAt Φ Ψ (Function.update g l (w a))) :
    IsSmoothInside A (Function.update g l (∑ a ∈ S, w a)) ∧
      ExtendsAt Φ Ψ (Function.update g l (∑ a ∈ S, w a)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := smoothInside_update_zero hg l
    exact ⟨h0, extendsAt_of_component_zero hP hC hn hΦm hΨ hAc hAd h0 (Function.update_self _ _ _)⟩
  | insert a S ha ih =>
    have ih' := ih (fun b hb => hw b (Finset.mem_insert_of_mem hb))
      (fun b hb => hh b (Finset.mem_insert_of_mem hb))
    rw [Finset.sum_insert ha]
    exact ⟨smoothInside_update_add hC (hw a (Finset.mem_insert_self a S)) ih'.1,
      extendsAt_update_add hP hC hn hΦm hΨ hAc hAd (hw a (Finset.mem_insert_self a S)) ih'.1
        (hh a (Finset.mem_insert_self a S)) ih'.2⟩
theorem exists_partition_on_balls (hU : SmoothPartitionOfUnityStatement)
    {K : Set (Pt s E)} (hK : IsCompact K) (hne : K.Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ (r : ℕ) (ψ : Fin r → Pt s E → ℝ) (y : Fin r → Pt s E), (∀ a, y a ∈ K) ∧
      (∀ a, asFunctionOnOnePoint (ψ a) ∈ testFns (singletonTupleSet (univ : Set (Pt s E)))) ∧
      (∀ a, tsupport (ψ a) ⊆ openBall s E (y a) η) ∧ ∀ x ∈ K, ∑ a, ψ a x = 1 := by
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls hη
  obtain ⟨r, y, -, hy⟩ := htf.fin_param
  have hr : 1 ≤ r := by
    by_contra h0
    have h00 : r = 0 := by omega
    subst h00
    have ht : t = ∅ := by
      rw [← hy]
      exact range_eq_empty _
    obtain ⟨x, hx⟩ := hne
    have hxc := hcov hx
    simp [ht] at hxc
  have hpre : Continuous (fun v : Tuple s E 1 => v 0) := continuous_apply 0
  obtain ⟨φ, hφ, hval, N, ⟨U, -, hKU, hUN⟩, hsum⟩ := (hU s E 1 le_rfl).1 r hr
    ((fun v : Tuple s E 1 => v 0) ⁻¹' K)
    (fun a => (fun v : Tuple s E 1 => v 0) ⁻¹' Metric.ball (y a) η)
    ((Homeomorph.funUnique (Fin 1) (Pt s E)).isCompact_preimage.2 hK)
    (fun a => Metric.isOpen_ball.preimage hpre) (by
      intro v hv
      have hvc := hcov hv
      simp only [mem_iUnion, exists_prop] at hvc ⊢
      obtain ⟨x, hxt, hx⟩ := hvc
      rw [← hy] at hxt
      obtain ⟨a, rfl⟩ := hxt
      exact ⟨a, hx⟩)
  have hre : ∀ a, asFunctionOnOnePoint (fun x => (φ a (fun _ => x)).re) = φ a := by
    intro a
    funext v
    obtain ⟨t', -, ht⟩ := hval a v
    show (((φ a (fun _ => v 0)).re : ℝ) : ℂ) = φ a v
    rw [const_apply_zero_eq, ht, Complex.ofReal_re]
  refine ⟨r, fun a x => (φ a (fun _ => x)).re, y,
    fun a => htK (hy ▸ mem_range_self a), fun a => ?_, fun a => ?_, fun x hx => ?_⟩
  · rw [hre]
    exact testFns_mono (show _ ⊆ singletonTupleSet (univ : Set (Pt s E)) from
      fun v _ => mem_univ (v 0)) (hφ a)
  · intro x hx
    have hm : (fun _ => x : Tuple s E 1) ∈
        closedSupport (asFunctionOnOnePoint fun x => (φ a fun _ => x).re) := by
      rw [closedSupport_asFunctionOnOnePoint]
      exact hx
    rw [hre] at hm
    exact (hφ a).2.2 hm
  · have h1 := hsum (fun _ => x) (hUN (hKU hx))
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2
theorem smoothInside_update_mul (hC : TestFnOperations)
    {A : Fin n → Set (Pt s E)} {g : Fin n → Pt s E → ℝ} (hg : IsSmoothInside A g) (l : Fin n)
    {ψ : Pt s E → ℝ}
    (hψ : asFunctionOnOnePoint ψ ∈ testFns (singletonTupleSet (univ : Set (Pt s E)))) :
    IsSmoothInside A (Function.update g l fun x => ψ x * g l x) := by
  have hg' : IsSmoothInside A (Function.update g l (g l)) := by
    rw [Function.update_eq_self]
    exact hg
  refine smoothInside_update hg' ?_ ?_
  · have e : asFunctionOnOnePoint (fun x => ψ x * g l x) =
        asFunctionOnOnePoint ψ * asFunctionOnOnePoint (g l) := by
      funext y
      simp [asFunctionOnOnePoint]
    rw [e]
    exact (((hC s E 1 le_rfl).2.1 _ isOpen_singletonTupleSet_univ).2.2.2 _ _ hψ.1
      (hg l).1.1).2.2.1 (Or.inl hψ)
  · exact (tsupport_mul_subset_right).trans (hg l).2
theorem extendsAt_of_smoothInside (hP : SeparationAndProductFacts.statement)
    (hC : TestFnOperations) (hL : DistanceFacts.MetricFactsClaim)
    (hU : SmoothPartitionOfUnityStatement)
    (hn : 1 ≤ n) {Φ : TupleForm (sepTuples s E n)} (hΦm : TupleForm.IsMultilinear Φ)
    (hA : ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
      ∃! T, IsBoxDistrib Φ V T)
    {Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ} (hΨ : IsGluedDistrib Φ Ψ)
    {A : Fin n → Set (Pt s E)} (hAc : ∀ l, IsCompact (A l)) (hAd : PairwiseDisjointFamily A)
    {δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ i i', i ≠ i' → ∀ a ∈ A i, ∀ b ∈ A i', δ ≤ pointDist s E a b)
    (g : Fin n → Pt s E → ℝ) (hg : IsSmoothInside A g) : ExtendsAt Φ Ψ g := by
  obtain ⟨η, h1, h2, h3⟩ := exists_small_radius s hδ
  have hbase : ∀ g, IsSmoothInside A g →
      (∀ l, ∃ y ∈ A l, tsupport (g l) ⊆ openBall s E y η) → ExtendsAt Φ Ψ g := by
    intro g hg hsmall
    choose y hyA hys using hsmall
    have hfam := isSeparatedOpenFamily_balls hL h1 h2 h3 (y := y)
      (fun i i' hne => hdist i i' hne _ (hyA i) _ (hyA i'))
    have hφ : ∀ i, IsRealTestFn (openBall s E (y i) η) (g i) := fun i =>
      isRealTestFn_of_tsupport (hg i).1.1
        ((hAc i).of_isClosed_subset (isClosed_tsupport _) (hg i).2) (hys i)
    have hspec := isBoxDistrib_boxDistrib (hA _ _ _ hfam).exists
    obtain ⟨hsep, hF, hval⟩ := hspec.2 g hφ
    refine ⟨hsep, realTensor_mem_pairwiseDistinct hC hn hAd hg, ?_⟩
    rw [← hval]
    exact congrFun (hΨ.2 _ _ _ hfam) ⟨_, hF⟩
  have hind : ∀ I : Finset (Fin n), ∀ g, IsSmoothInside A g →
      (∀ l, l ∉ I → ∃ y ∈ A l, tsupport (g l) ⊆ openBall s E y η) → ExtendsAt Φ Ψ g := by
    intro I
    induction I using Finset.induction_on with
    | empty => exact fun g hg h => hbase g hg fun l => h l (Finset.notMem_empty l)
    | insert l I hl ih =>
      intro g hg hsm
      by_cases hne : (A l).Nonempty
      · obtain ⟨r, ψ, y, hyA, hψ, hψs, hsum⟩ := exists_partition_on_balls hU (hAc l) hne h1
        have hwg : ∀ a, IsSmoothInside A (Function.update g l fun x => ψ a x * g l x) :=
          fun a => smoothInside_update_mul hC hg l (hψ a)
        have hws : ∀ a, ExtendsAt Φ Ψ (Function.update g l fun x => ψ a x * g l x) := by
          intro a
          refine ih _ (hwg a) fun l' hl' => ?_
          by_cases hll : l' = l
          · subst hll
            rw [Function.update_self]
            exact ⟨y a, hyA a, (tsupport_mul_subset_left).trans (hψs a)⟩
          · rw [Function.update_of_ne hll]
            exact hsm l' (by simp [Finset.mem_insert, hll, hl'])
        have hsumw : ∑ a, (fun x => ψ a x * g l x) = g l := by
          funext x
          rw [Finset.sum_apply]
          by_cases hx : x ∈ A l
          · rw [← Finset.sum_mul, hsum x hx, one_mul]
          · have hz : g l x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ((hg l).2 h)
            simp [hz]
        have hfin := (extendsAt_update_sum hP hC hn hΦm hΨ.1 hAc hAd hg Finset.univ
          (fun a x => ψ a x * g l x) (fun a _ => hwg a) (fun a _ => hws a)).2
        rwa [hsumw, Function.update_eq_self] at hfin
      · have h0 : g l = 0 := funext fun x =>
          image_eq_zero_of_notMem_tsupport fun hx => hne ⟨x, (hg l).2 hx⟩
        exact extendsAt_of_component_zero hP hC hn hΦm hΨ.1 hAc hAd hg h0
  exact hind Finset.univ g hg fun l hl => absurd (Finset.mem_univ l) hl
theorem extendsAt_of_smooth_components (hP : SeparationAndProductFacts.statement)
    (hC : TestFnOperations) (hL : DistanceFacts.MetricFactsClaim)
    (hU : SmoothPartitionOfUnityStatement)
    (hn2 : 2 ≤ n) {Φ : TupleForm (sepTuples s E n)} (hΦm : TupleForm.IsMultilinear Φ)
    (hA : ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
      ∃! T, IsBoxDistrib Φ V T)
    {Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ} (hΨ : IsGluedDistrib Φ Ψ)
    (f : sepTuples s E n) (hsm : ∀ i, IsSmoothFn (asFunctionOnOnePoint (f.1 i))) :
    ExtendsAt Φ Ψ f.1 := by
  have hn : 1 ≤ n := by omega
  have hm := (hP s n hn).1 E
  have hsepos : 0 < supportGap f.1 := hm.gap_pos hn2 f.1 (Or.inl f.2)
  have htop : min (supportGap f.1) 1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hδ : 0 < (min (supportGap f.1) 1).toReal :=
    ENNReal.toReal_pos (lt_min hsepos one_pos).ne' htop
  refine extendsAt_of_smoothInside hP hC hL hU hn hΦm hA hΨ (A := fun l => tsupport (f.1 l))
    f.2.2.1 f.2.2.2 hδ ?_ f.1 fun l => ⟨?_, subset_rfl⟩
  · intro i i' hne a ha b hb
    have h1 : ENNReal.ofReal (min (supportGap f.1) 1).toReal ≤ supportGap f.1 := by
      rw [ENNReal.ofReal_toReal htop]
      exact min_le_left _ _
    have h2 : supportGap f.1 ≤ ENNReal.ofReal (pointDist s E a b) :=
      iInf_le_of_le i (iInf_le_of_le i' (iInf_le_of_le hne
        (iInf₂_le_of_le a ha (iInf₂_le_of_le b hb le_rfl))))
    exact (ENNReal.ofReal_le_ofReal_iff (pointDist_nonneg a b)).1 (h1.trans h2)
  · rw [singletonTupleSet_eq_boxSet]
    exact isRealTestFn_of_tsupport (hsm l) (f.2.2.1 l) (subset_univ _)
theorem holds (hT : ChartTransport.statement) (hK : BoundedMultilinearFormIsDistribution)
    (hG : DistributionsGlueUniquely) (hP : SeparationAndProductFacts.statement)
    (hC : TestFnOperations) (hS : GradientC1Bounds.Statement)
    (hL : DistanceFacts.MetricFactsClaim) (hU : SmoothPartitionOfUnityStatement)
    (hTop : TupleTopology.Holds) : Statement := by
  intro s E n hn M Φ hΦr hΦm c hc
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ha, hord⟩ := boxDistribs_and_order hT hK hP hC hS hTop hn1 hΦr hΦm hc
  have hA : ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
      ∃! T, IsBoxDistrib Φ V T := fun R d V hV => (ha R d V hV).1
  obtain ⟨hg, hgo⟩ := glued_exists_unique hG hL hC hn1 hA hord
  have hdf := isGluedDistrib_formDistrib hg.exists
  refine ⟨ha, hord, hg, hgo, ?_, ?_⟩
  · intro f hsm
    obtain ⟨_, hF, hv⟩ := extendsAt_of_smooth_components hP hC hL hU hn hΦm hA hdf f hsm
    exact ⟨hF, hv⟩
  · intro Ψ hΨ hag
    have hglued : IsGluedDistrib Φ Ψ := by
      refine ⟨hΨ, fun R d V hV => ?_⟩
      have hspec := isBoxDistrib_boxDistrib (hA R d V hV).exists
      refine (hA R d V hV).unique ⟨?_, fun φ hφ => ?_⟩ hspec
      · exact (((hC s E n hn1).1 _ _ hV.boxSet_subset (isOpen_boxSet hV.isOpen)
          isOpen_pairwiseDistinctTuples).2.2 Ψ hΨ).1
      · have hsep := mem_sepTuples_of_family hP hn1 hV fun i =>
          c1CompactSupportIn_of_isRealTestFn (hφ i)
        obtain ⟨hF, hv⟩ := hag ⟨φ, hsep⟩ fun i => (hφ i).1
        exact ⟨hsep, realTensor_mem_testFns hC hn1 hV.isOpen hφ, hv⟩
    exact hg.unique hglued hdf
end YangMills.Construction.AmbientPoints.MultilinearAsDistrib
