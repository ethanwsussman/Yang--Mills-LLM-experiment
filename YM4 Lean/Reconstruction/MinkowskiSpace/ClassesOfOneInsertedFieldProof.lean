import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.ClassesOfOneInsertedField
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpaceProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldClasses
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.ReflectionPositivity.FormProperties YangMills.Construction.FieldFormConditions YangMills.Construction.ProjectionMeasures YangMills.Construction.HilbertToolkit YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.MinkowskiSpace YangMills.Construction.FieldForms YangMills.Construction.InsertedFieldForm
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.WightmanReconstruction (complexTuple linearExtension)
open YangMills.Construction.TupleLists (ofList)
def tupleOfLength (X : SepTuple) {n : ℕ} (h : X.1.length = n) : TestSpaces.SepTupleOfCard n :=
  ⟨fun k => X.1.get (Fin.cast h.symm k), by
    subst h
    exact TupleLists.get_mem_disjointSupportTuples X⟩
theorem ofList_eq_mk (X : SepTuple) {n : ℕ} (h : X.1.length = n) :
    ofList X = ⟨n, tupleOfLength X h⟩ :=
  TestSpaces.sepTuple_ext _ _ h fun k => by simp [tupleOfLength]
theorem getElem_append_cons_of_ne (A B : List RealValued) (f f' : RealValued) (j : ℕ)
    (h : j < (A ++ f :: B).length) (h' : j < (A ++ f' :: B).length) (hj : j ≠ A.length) :
    (A ++ f :: B)[j] = (A ++ f' :: B)[j] := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
  · obtain ⟨m, rfl⟩ : ∃ m, j = A.length + (m + 1) := ⟨j - A.length - 1, by omega⟩
    have e : ∀ g : RealValued, ∀ hg : A.length + (m + 1) < (A ++ g :: B).length,
        (A ++ g :: B)[A.length + (m + 1)] = B[m]'(by simp at hg; omega) := by
      intro g hg
      rw [List.getElem_append_right (by omega)]
      simp
    rw [e f h, e f' h']
theorem apply_ofList_linearCombination {σ : TestSpaces.SepTuple → ℝ}
    (hσ : TestSpaces.IsSepFunctional σ) (A B : List RealValued)
    (f f' : RealValued) (α α' : ℝ) (X X' Z : SepTuple) (hX : X.1 = A ++ f :: B)
    (hX' : X'.1 = A ++ f' :: B) (hZ : Z.1 = A ++ (α • f + α' • f') :: B) :
    σ (ofList Z) = α * σ (ofList X) + α' * σ (ofList X') := by
  obtain ⟨L, hL⟩ := X
  obtain ⟨L', hL'⟩ := X'
  obtain ⟨M, hM⟩ := Z
  simp only at hX hX' hZ
  subst hX hX' hZ
  have hn : ∀ g : RealValued, (A ++ g :: B).length = A.length + B.length + 1 := fun g => by
    simp
    omega
  rw [ofList_eq_mk ⟨_, hL⟩ (hn f), ofList_eq_mk ⟨_, hL'⟩ (hn f'), ofList_eq_mk ⟨_, hM⟩ (hn _)]
  refine hσ.2 _ (by omega) ⟨A.length, by omega⟩ α α' _ _ _ ?_ ?_ ?_
  · intro j hj
    exact getElem_append_cons_of_ne A B f f' j _ _ (fun e => hj (Fin.ext e))
  · simp [tupleOfLength]
  · intro j hj
    exact getElem_append_cons_of_ne A B _ f j _ _ (fun e => hj (Fin.ext e))
def singletonTuple (g : RealValued) (hg : IsC1c g) : SepTuple :=
  ⟨[g], ⟨by simpa using hg, by simp⟩⟩
theorem linearExtension_basisVec_eq (σ : TestSpaces.SepTuple → ℝ) (X : SepTuple) :
    linearExtension σ (basisVec X) = (σ (ofList X) : ℂ) :=
  linearExtend_basisVec _ X
structure IsFlanking (S : Set AmbientSpace) (W Y : SepTuple) : Prop where
  left : ∀ h ∈ W.1, Disjoint (tsupport h) S
  right : ∀ h ∈ Y.1, Disjoint S (tsupport h)
  composable : SepTuple.Composable W Y
theorem IsFlanking.juxt_val {S : Set AmbientSpace} {W Y : SepTuple} (hWY : IsFlanking S W Y)
    {g : RealValued} (hg : IsC1c g) (hS : tsupport g ⊆ S) :
    (SepTuple.juxt W (SepTuple.juxt (singletonTuple g hg) Y)).1 = W.1 ++ g :: Y.1 := by
  have h₁ : SepTuple.Composable (singletonTuple g hg) Y := by
    intro f hf h hh
    rw [show f = g by simpa [singletonTuple] using hf]
    exact (hWY.right h hh).mono_left hS
  have h₂ : SepTuple.Composable W (SepTuple.juxt (singletonTuple g hg) Y) := by
    intro f hf h hh
    rw [SepTuple.juxt_val h₁] at hh
    rcases List.mem_append.1 hh with hh | hh
    · rw [show h = g by simpa [singletonTuple] using hh]
      exact (hWY.left f hf).mono_right hS
    · exact hWY.composable f hf h hh
  rw [SepTuple.juxt_val h₂, SepTuple.juxt_val h₁]
  rfl
section Middle
variable (σ : TestSpaces.SepTuple → ℝ)
def sandwichValue (W Y : SepTuple) (g : RealValued) (hg : IsC1c g) : ℝ :=
  σ (ofList (SepTuple.juxt W (SepTuple.juxt (singletonTuple g hg) Y)))
variable {σ}
theorem sandwichValue_congr {W Y : SepTuple} {g g' : RealValued} (e : g = g')
    (hg : IsC1c g) (hg' : IsC1c g') :
    sandwichValue σ W Y g hg = sandwichValue σ W Y g' hg' := by
  subst e
  rfl
theorem sandwichValue_linearCombination (hσ : TestSpaces.IsSepFunctional σ)
    {S : Set AmbientSpace} {W Y : SepTuple} (hWY : IsFlanking S W Y) {g g' : RealValued}
    (hg : IsC1c g) (hg' : IsC1c g')
    (hS : tsupport g ⊆ S) (hS' : tsupport g' ⊆ S) (α α' : ℝ)
    (hc : IsC1c (α • g + α' • g')) (hcS : tsupport (α • g + α' • g') ⊆ S) :
    sandwichValue σ W Y (α • g + α' • g') hc =
      α * sandwichValue σ W Y g hg + α' * sandwichValue σ W Y g' hg' :=
  apply_ofList_linearCombination hσ W.1 Y.1 g g' α α' _ _ _ (hWY.juxt_val hg hS)
    (hWY.juxt_val hg' hS') (hWY.juxt_val hc hcS)
theorem isC1c_zero : IsC1c (0 : RealValued) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩
theorem sandwichValue_zero (hσ : TestSpaces.IsSepFunctional σ) {S : Set AmbientSpace}
    {W Y : SepTuple} (hWY : IsFlanking S W Y) (h0 : IsC1c (0 : RealValued)) :
    sandwichValue σ W Y 0 h0 = 0 := by
  have hs : tsupport (0 : RealValued) ⊆ S := by simp
  have hc : IsC1c ((0 : ℝ) • (0 : RealValued) + (0 : ℝ) • (0 : RealValued)) := by
    simpa using h0
  have := sandwichValue_linearCombination hσ hWY h0 h0 hs hs 0 0 hc (by simp)
  rw [sandwichValue_congr (by simp) hc h0] at this
  simpa using this
variable (σ) in
def sandwichFunctional (W Y : SepTuple) : FormalSpan →ₗ[ℂ] ℂ :=
  linearExtension σ ∘ₗ formalMul (basisVec W) ∘ₗ formalMul.flip (basisVec Y)
theorem sandwichFunctional_singleton (W Y : SepTuple) {g : RealValued} (hg : IsC1c g) :
    sandwichFunctional σ W Y (basisVec (singletonTuple g hg)) = (sandwichValue σ W Y g hg : ℂ) := by
  show linearExtension σ (formalMul (basisVec W)
    (formalMul (basisVec (singletonTuple g hg)) (basisVec Y))) = _
  rw [formalMul_basisVec, formalMul_basisVec]
  exact linearExtension_basisVec_eq _ _
end Middle
abbrev ComplexC1c : Set (AmbientSpace → ℂ) := TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))
abbrev reFun (f : AmbientSpace → ℂ) : RealValued := fun x => (f x).re
abbrev imFun (f : AmbientSpace → ℂ) : RealValued := fun x => (f x).im
theorem isC1c_reFun {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) : IsC1c (reFun f) :=
  ⟨Complex.reCLM.contDiff.comp hf.1, hf.2.1.comp_left (g := Complex.re) Complex.zero_re⟩
theorem isC1c_imFun {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) : IsC1c (imFun f) :=
  ⟨Complex.imCLM.contDiff.comp hf.1, hf.2.1.comp_left (g := Complex.im) Complex.zero_im⟩
theorem tsupport_reFun_subset (f : AmbientSpace → ℂ) : tsupport (reFun f) ⊆ tsupport f :=
  tsupport_comp_subset (g := Complex.re) Complex.zero_re f
theorem tsupport_imFun_subset (f : AmbientSpace → ℂ) : tsupport (imFun f) ⊆ tsupport f :=
  tsupport_comp_subset (g := Complex.im) Complex.zero_im f
theorem singleton_mem_sepAll {g : RealValued} (hg : IsC1c g) :
    [g] ∈ EuclideanFunctionals.sepAll := by
  refine Set.mem_iUnion.2 ⟨1, rfl, fun f hf => ?_, List.pairwise_singleton _ _⟩
  rw [List.mem_singleton.1 hf, ← FourSpace.C1c_eq_compactC1]
  exact ⟨hg.1, hg.2⟩
theorem complexTuple_eq_of_real {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c)
    (hr : ∀ x, (f x).im = 0) :
    complexTuple f = basisVec (singletonTuple (reFun f) (isC1c_reFun hf)) := by
  have e : f = fun x => ((reFun f x : ℝ) : ℂ) :=
    funext fun x => Complex.ext rfl (by simp [hr])
  have h := WightmanReconstruction.complexTuple_ofReal (reFun f)
    (singleton_mem_sepAll (isC1c_reFun hf))
  rw [← e] at h
  exact h
theorem complexTuple_eq_of_not_real {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c)
    (hr : ¬∀ x, (f x).im = 0) :
    complexTuple f = basisVec (singletonTuple (reFun f) (isC1c_reFun hf)) +
      Complex.I • basisVec (singletonTuple (imFun f) (isC1c_imFun hf)) :=
  WightmanReconstruction.complexTuple_of_not_real f hr
    (singleton_mem_sepAll (isC1c_reFun hf)) (singleton_mem_sepAll (isC1c_imFun hf))
theorem complexTuple_mem_spanIn {S : Set AmbientSpace} {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c)
    (hS : tsupport f ⊆ S) : complexTuple f ∈ spanIn S := by
  have hre : singletonTuple (reFun f) (isC1c_reFun hf) ∈ supportedIn S := by
    intro g hg
    rw [show g = reFun f by simpa [singletonTuple] using hg]
    exact (tsupport_reFun_subset f).trans hS
  have him : singletonTuple (imFun f) (isC1c_imFun hf) ∈ supportedIn S := by
    intro g hg
    rw [show g = imFun f by simpa [singletonTuple] using hg]
    exact (tsupport_imFun_subset f).trans hS
  by_cases hr : ∀ x, (f x).im = 0
  · rw [complexTuple_eq_of_real hf hr]
    exact Submodule.subset_span ⟨⟨_, hre⟩, rfl⟩
  · rw [complexTuple_eq_of_not_real hf hr]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨⟨_, hre⟩, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, him⟩, rfl⟩))
section Pairing
variable {σ : TestSpaces.SepTuple → ℝ}
theorem sandwichFunctional_complexTuple (hσ : TestSpaces.IsSepFunctional σ) {S : Set AmbientSpace}
    {W Y : SepTuple} (hWY : IsFlanking S W Y) {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) :
    sandwichFunctional σ W Y (complexTuple f) =
      (sandwichValue σ W Y (reFun f) (isC1c_reFun hf) : ℂ) +
        Complex.I * (sandwichValue σ W Y (imFun f) (isC1c_imFun hf) : ℂ) := by
  by_cases hr : ∀ x, (f x).im = 0
  · have e : imFun f = 0 := funext hr
    rw [complexTuple_eq_of_real hf hr, sandwichFunctional_singleton,
      sandwichValue_congr e (isC1c_imFun hf) isC1c_zero,
      sandwichValue_zero hσ hWY]
    simp
  · rw [complexTuple_eq_of_not_real hf hr, map_add, map_smul, sandwichFunctional_singleton,
      sandwichFunctional_singleton, smul_eq_mul]
theorem add_mem_complexC1c {f g : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) (hg : g ∈ ComplexC1c) :
    f + g ∈ ComplexC1c :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, Set.subset_univ _⟩
theorem smul_mem_complexC1c (c : ℂ) {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) :
    c • f ∈ ComplexC1c :=
  ⟨hf.1.const_smul c, hf.2.1.mono (Function.support_const_smul_subset c _), Set.subset_univ _⟩
theorem tsupport_add_subset_of {S : Set AmbientSpace} {f g : AmbientSpace → ℂ}
    (hf : tsupport f ⊆ S) (hg : tsupport g ⊆ S) : tsupport (f + g) ⊆ S := by
  refine (closure_mono (Function.support_add f g)).trans ?_
  rw [closure_union]
  exact Set.union_subset hf hg
theorem tsupport_const_smul_subset_of {S : Set AmbientSpace} (c : ℂ) {f : AmbientSpace → ℂ}
    (hf : tsupport f ⊆ S) : tsupport (c • f) ⊆ S :=
  (closure_mono (Function.support_const_smul_subset c f)).trans hf
theorem isC1c_linearCombination {g g' : RealValued} (hg : IsC1c g)
    (hg' : IsC1c g') (α α' : ℝ) : IsC1c (α • g + α' • g') := by apply _root_.YangMills.Construction.SeparatedTuples.BasicFacts.isC1c_smul_add_smul <;> assumption
theorem tsupport_linearCombination_subset {S : Set AmbientSpace} {g g' : RealValued}
    (hg : tsupport g ⊆ S) (hg' : tsupport g' ⊆ S) (α α' : ℝ) : tsupport (α • g + α' • g') ⊆ S := by
  refine (closure_mono (Function.support_add _ _)).trans ?_
  rw [closure_union]
  exact Set.union_subset ((closure_mono (Function.support_const_smul_subset α g)).trans hg)
    ((closure_mono (Function.support_const_smul_subset α' g')).trans hg')
theorem sandwichFunctional_complexTuple_add (hσ : TestSpaces.IsSepFunctional σ)
    {S : Set AmbientSpace} {W Y : SepTuple} (hWY : IsFlanking S W Y) {f g : AmbientSpace → ℂ}
    (hf : f ∈ ComplexC1c) (hg : g ∈ ComplexC1c) (hfS : tsupport f ⊆ S) (hgS : tsupport g ⊆ S) :
    sandwichFunctional σ W Y (complexTuple (f + g)) =
      sandwichFunctional σ W Y (complexTuple f) +
        sandwichFunctional σ W Y (complexTuple g) := by
  have hfg := add_mem_complexC1c hf hg
  have hr := (tsupport_reFun_subset f).trans hfS
  have hr' := (tsupport_reFun_subset g).trans hgS
  have hi := (tsupport_imFun_subset f).trans hfS
  have hi' := (tsupport_imFun_subset g).trans hgS
  have e₁ : reFun (f + g) = (1 : ℝ) • reFun f + (1 : ℝ) • reFun g := by
    funext x
    show (f x + g x).re = 1 * (f x).re + 1 * (g x).re
    simp
  have e₂ : imFun (f + g) = (1 : ℝ) • imFun f + (1 : ℝ) • imFun g := by
    funext x
    show (f x + g x).im = 1 * (f x).im + 1 * (g x).im
    simp
  have c₁ := isC1c_linearCombination (isC1c_reFun hf) (isC1c_reFun hg) 1 1
  have c₂ := isC1c_linearCombination (isC1c_imFun hf) (isC1c_imFun hg) 1 1
  rw [sandwichFunctional_complexTuple hσ hWY hfg, sandwichFunctional_complexTuple hσ hWY hf,
    sandwichFunctional_complexTuple hσ hWY hg,
    sandwichValue_congr e₁ (isC1c_reFun hfg) c₁, sandwichValue_congr e₂ (isC1c_imFun hfg) c₂,
    sandwichValue_linearCombination hσ hWY (isC1c_reFun hf) (isC1c_reFun hg) hr hr' 1 1 c₁
      (tsupport_linearCombination_subset hr hr' 1 1),
    sandwichValue_linearCombination hσ hWY (isC1c_imFun hf) (isC1c_imFun hg) hi hi' 1 1 c₂
      (tsupport_linearCombination_subset hi hi' 1 1)]
  push_cast
  ring
theorem sandwichFunctional_complexTuple_smul (hσ : TestSpaces.IsSepFunctional σ)
    {S : Set AmbientSpace} {W Y : SepTuple} (hWY : IsFlanking S W Y) (c : ℂ)
    {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) (hfS : tsupport f ⊆ S) :
    sandwichFunctional σ W Y (complexTuple (c • f)) =
      c * sandwichFunctional σ W Y (complexTuple f) := by
  have hcf := smul_mem_complexC1c c hf
  have hr := (tsupport_reFun_subset f).trans hfS
  have hi := (tsupport_imFun_subset f).trans hfS
  have e₁ : reFun (c • f) = c.re • reFun f + (-c.im) • imFun f := by
    funext x
    show (c * f x).re = c.re * (f x).re + (-c.im) * (f x).im
    simp [Complex.mul_re]
    ring
  have e₂ : imFun (c • f) = c.im • reFun f + c.re • imFun f := by
    funext x
    show (c * f x).im = c.im * (f x).re + c.re * (f x).im
    simp [Complex.mul_im]
    ring
  have c₁ := isC1c_linearCombination (isC1c_reFun hf) (isC1c_imFun hf) c.re (-c.im)
  have c₂ := isC1c_linearCombination (isC1c_reFun hf) (isC1c_imFun hf) c.im c.re
  rw [sandwichFunctional_complexTuple hσ hWY hcf, sandwichFunctional_complexTuple hσ hWY hf,
    sandwichValue_congr e₁ (isC1c_reFun hcf) c₁, sandwichValue_congr e₂ (isC1c_imFun hcf) c₂,
    sandwichValue_linearCombination hσ hWY (isC1c_reFun hf) (isC1c_imFun hf) hr hi c.re (-c.im) c₁
      (tsupport_linearCombination_subset hr hi _ _),
    sandwichValue_linearCombination hσ hWY (isC1c_reFun hf) (isC1c_imFun hf) hr hi c.im c.re c₂
      (tsupport_linearCombination_subset hr hi _ _)]
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  push_cast
  conv_rhs => rw [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring
variable (σ) in
def insertionPairing (f : AmbientSpace → ℂ) : FormalSpan →ₗ[ℂ] FormalSpan →ₗ[ℂ] ℂ :=
  (formalMul.compl₂ (formalMul (complexTuple f))).compr₂ (linearExtension σ)
theorem insertionPairing_basisVec (f : AmbientSpace → ℂ) (W Y : SepTuple) :
    insertionPairing σ f (basisVec W) (basisVec Y) =
      sandwichFunctional σ W Y (complexTuple f) := rfl
theorem bilinear_eqOn_spanIn {N O : Set AmbientSpace}
    (Ψ Ψ' : FormalSpan →ₗ[ℂ] FormalSpan →ₗ[ℂ] ℂ)
    (h : ∀ W ∈ supportedIn N, ∀ Y ∈ supportedIn O,
      Ψ (basisVec W) (basisVec Y) = Ψ' (basisVec W) (basisVec Y))
    {A C : FormalSpan} (hA : A ∈ spanIn N) (hC : C ∈ spanIn O) :
    Ψ A C = Ψ' A C := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨W, rfl⟩ := hx
    induction hC using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Y, rfl⟩ := hy
      exact h W.1 W.2 Y.1 Y.2
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb]
    | smul z a _ ha => simp only [map_smul, ha]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul z a _ ha => simp only [map_smul, LinearMap.smul_apply, ha]
theorem isFlanking_of_mem {N S O : Set AmbientSpace} (hNS : Disjoint N S) (hSO : Disjoint S O)
    (hNO : Disjoint N O) {W Y : SepTuple} (hW : W ∈ supportedIn N) (hY : Y ∈ supportedIn O) :
    IsFlanking S W Y :=
  ⟨fun h hh => hNS.mono_left (hW h hh), fun h hh => hSO.mono_right (hY h hh),
    composable_of_mem_supportedIn hNO hW hY⟩
theorem insertionPairing_add (hσ : TestSpaces.IsSepFunctional σ) {N S O : Set AmbientSpace}
    (hNS : Disjoint N S) (hSO : Disjoint S O) (hNO : Disjoint N O) {f g : AmbientSpace → ℂ}
    (hf : f ∈ ComplexC1c) (hg : g ∈ ComplexC1c) (hfS : tsupport f ⊆ S) (hgS : tsupport g ⊆ S)
    {A C : FormalSpan} (hA : A ∈ spanIn N) (hC : C ∈ spanIn O) :
    insertionPairing σ (f + g) A C = insertionPairing σ f A C + insertionPairing σ g A C := by
  have h := bilinear_eqOn_spanIn (insertionPairing σ (f + g))
    (insertionPairing σ f + insertionPairing σ g) (fun W hW Y hY => by
    rw [LinearMap.add_apply, LinearMap.add_apply, insertionPairing_basisVec,
      insertionPairing_basisVec, insertionPairing_basisVec]
    exact sandwichFunctional_complexTuple_add hσ (isFlanking_of_mem hNS hSO hNO hW hY)
      hf hg hfS hgS) hA hC
  rwa [LinearMap.add_apply, LinearMap.add_apply] at h
theorem insertionPairing_smul (hσ : TestSpaces.IsSepFunctional σ) {N S O : Set AmbientSpace}
    (hNS : Disjoint N S) (hSO : Disjoint S O) (hNO : Disjoint N O) (c : ℂ) {f : AmbientSpace → ℂ}
    (hf : f ∈ ComplexC1c) (hfS : tsupport f ⊆ S)
    {A C : FormalSpan} (hA : A ∈ spanIn N) (hC : C ∈ spanIn O) :
    insertionPairing σ (c • f) A C = c * insertionPairing σ f A C := by
  have h := bilinear_eqOn_spanIn (insertionPairing σ (c • f)) (c • insertionPairing σ f)
    (fun W hW Y hY => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, insertionPairing_basisVec,
      insertionPairing_basisVec, smul_eq_mul]
    exact sandwichFunctional_complexTuple_smul hσ (isFlanking_of_mem hNS hSO hNO hW hY) c hf hfS)
    hA hC
  rwa [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
end Pairing
def slabBelow (v : AmbientSpace) : Set AmbientSpace :=
  {x | 0 < x TimeAxis.timeIdx ∧ x TimeAxis.timeIdx ≤ v TimeAxis.timeIdx}
def regionAbove (v : AmbientSpace) : Set AmbientSpace :=
  {x | 0 < x TimeAxis.timeIdx ∧ v TimeAxis.timeIdx < x TimeAxis.timeIdx}
def lowerHalfSpace : Set AmbientSpace := TimeAxis.timeReflection '' TimeAxis.upperHalfSpace
theorem upperHalfSpace_isOpen : IsOpen TimeAxis.upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply TimeAxis.timeIdx)
theorem isEuclidIsometry_timeReflection : IsEuclidIsometry TimeAxis.timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.isEuclidIsometry_timeReflection <;> assumption
theorem timeIdx_neg_of_mem_lowerHalfSpace {x : AmbientSpace} (hx : x ∈ lowerHalfSpace) :
    x TimeAxis.timeIdx < 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h : 0 < y 3 := hy
  simpa [TimeAxis.timeReflection, TimeAxis.timeIdx] using h
theorem disjoint_slabBelow_regionAbove (v : AmbientSpace) : Disjoint (slabBelow v) (regionAbove v) :=
  Set.disjoint_left.2 fun _ h h' => absurd h.2 (not_le.2 h'.2)
theorem disjoint_lowerHalfSpace_slabBelow (v : AmbientSpace) : Disjoint lowerHalfSpace (slabBelow v) :=
  Set.disjoint_left.2 fun _ h h' => lt_asymm (timeIdx_neg_of_mem_lowerHalfSpace h) h'.1
theorem disjoint_lowerHalfSpace_regionAbove (v : AmbientSpace) :
    Disjoint lowerHalfSpace (regionAbove v) :=
  Set.disjoint_left.2 fun _ h h' => lt_asymm (timeIdx_neg_of_mem_lowerHalfSpace h) h'.1
theorem spanIn_mono {O O' : Set AmbientSpace} (h : O ⊆ O') {G : FormalSpan}
    (hG : G ∈ spanIn O) : G ∈ spanIn O' :=
  Submodule.span_mono (by
    rintro _ ⟨X, rfl⟩
    exact ⟨⟨X.1, fun f hf => (X.2 f hf).trans h⟩, rfl⟩) hG
theorem conjugation_mem_spanIn {O : Set AmbientSpace} {G : FormalSpan} (hG : G ∈ spanIn O) :
    conjugation G ∈ spanIn O := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.conjugation_mem_spanIn <;> assumption
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
section Translations
variable (hAct : BasicFacts.PushSpanProperties)
include hAct
theorem reflectConj_mem (F : PositiveSpan) : reflectConj F ∈ spanIn lowerHalfSpace := by
  have hθ := isEuclidIsometry_timeReflection
  have hmap := ((hAct _ _ hθ hθ 0 0 0).2.2.2.2.1 TimeAxis.upperHalfSpace upperHalfSpace_isOpen).2
  have hc : conjugation F.1 ∈ spanIn TimeAxis.upperHalfSpace := conjugation_mem_spanIn F.2
  exact hmap ▸ Submodule.mem_map_of_mem hc
theorem pushSpan_translate_mem {a : AmbientSpace} (ha : 0 ≤ a TimeAxis.timeIdx) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate a) G ∈ spanIn (regionAbove a) := by
  have hτ := isEuclidIsometry_translate a
  have hmap := ((hAct _ _ hτ hτ 0 0 G).2.2.2.2.1 TimeAxis.upperHalfSpace upperHalfSpace_isOpen).2
  have hm : pushSpan (translate a) G ∈ spanIn (translate a '' TimeAxis.upperHalfSpace) :=
    hmap ▸ Submodule.mem_map_of_mem hG
  refine spanIn_mono ?_ hm
  rintro _ ⟨y, hy, rfl⟩
  have hy' : 0 < y TimeAxis.timeIdx := hy
  show 0 < (y + a) TimeAxis.timeIdx ∧ a TimeAxis.timeIdx < (y + a) TimeAxis.timeIdx
  simp only [Pi.add_apply]
  constructor <;> linarith
theorem shiftedSpan_val {a : AmbientSpace} (ha : 0 ≤ a TimeAxis.timeIdx) (F : PositiveSpan) :
    (shiftedSpan a F).1 = pushSpan (translate a) F.1 := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.coe_shiftedSpan <;> assumption
theorem shiftedSpan_mem_regionAbove (v : AmbientSpace) (F : PositiveSpan) :
    (shiftedSpan v F).1 ∈ spanIn (regionAbove v) := by
  by_cases hv : 0 ≤ v TimeAxis.timeIdx
  · rw [shiftedSpan_val hAct hv]
    exact pushSpan_translate_mem hAct hv F.2
  · refine spanIn_mono ?_ (shiftedSpan v F).2
    intro x hx
    have hx' : 0 < x TimeAxis.timeIdx := hx
    exact ⟨hx', by linarith [not_le.1 hv]⟩
theorem shiftedSpan_shiftedSpan {a b : AmbientSpace} (ha : 0 ≤ a TimeAxis.timeIdx)
    (hb : 0 ≤ b TimeAxis.timeIdx) (F : PositiveSpan) :
    shiftedSpan a (shiftedSpan b F) = shiftedSpan (a + b) F := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.shiftedSpan_shiftedSpan <;> assumption
theorem pushSpan_translate_formalMul (a : AmbientSpace) {A C : FormalSpan}
    (h : R4TupleForms.FormalMulDefined A C) :
    pushSpan (translate a) (formalMul A C) =
      formalMul (pushSpan (translate a) A) (pushSpan (translate a) C) := by
  obtain ⟨O, O', hO, hO', hd, hA, hC⟩ :=
    R4TupleForms.exists_isOpen_of_formalMulDefined h
  have hτ := isEuclidIsometry_translate a
  exact ((hAct _ _ hτ hτ 0 0 0).2.2.2.2.2 O O' hO hO' hd A hA C hC).symm
end Translations
theorem supportedBelow_tsupport_subset {v : AmbientSpace} {f : AmbientSpace → ℂ}
    (hf : SupportedBelow v f) : tsupport f ⊆ slabBelow v :=
  fun x hx => hf.2 x hx
theorem supportedBelow_of_tsupport_subset {v : AmbientSpace} {f : AmbientSpace → ℂ}
    (hf : f ∈ ComplexC1c) (hs : tsupport f ⊆ slabBelow v) : SupportedBelow v f :=
  ⟨hf, fun _ hx => hs hx⟩
theorem supportedBelow_add {v : AmbientSpace} {f g : AmbientSpace → ℂ} (hf : SupportedBelow v f)
    (hg : SupportedBelow v g) : SupportedBelow v (f + g) :=
  supportedBelow_of_tsupport_subset (add_mem_complexC1c hf.1 hg.1)
    (tsupport_add_subset_of (supportedBelow_tsupport_subset hf) (supportedBelow_tsupport_subset hg))
theorem supportedBelow_smul {v : AmbientSpace} (c : ℂ) {f : AmbientSpace → ℂ}
    (hf : SupportedBelow v f) : SupportedBelow v (c • f) :=
  supportedBelow_of_tsupport_subset (smul_mem_complexC1c c hf.1)
    (tsupport_const_smul_subset_of c (supportedBelow_tsupport_subset hf))
theorem supportedBelow_zero (v : AmbientSpace) : SupportedBelow v 0 :=
  ⟨⟨contDiff_const, HasCompactSupport.zero, Set.subset_univ _⟩, fun _ hx => by simp at hx⟩
theorem eq_zero_of_supportedBelow {v : AmbientSpace} {f : AmbientSpace → ℂ}
    (hv : ¬0 ≤ v TimeAxis.timeIdx) (hf : SupportedBelow v f) : f = 0 := by
  refine tsupport_eq_empty_iff.1 (Set.eq_empty_of_forall_notMem fun x hx => ?_)
  have h := hf.2 x hx
  exact hv (h.1.le.trans h.2)
theorem supportedBelow_sum {ι : Type} {v : AmbientSpace} (s : Finset ι) (c : ι → ℂ)
    (f : ι → AmbientSpace → ℂ) (hf : ∀ i ∈ s, SupportedBelow v (f i)) :
    SupportedBelow v (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supportedBelow_zero v
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact supportedBelow_add (supportedBelow_smul _ (hf i (Finset.mem_insert_self i s)))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
section Classes
variable {σ : TestSpaces.SepTuple → ℝ}
theorem exists_linear_stateOf (hC : HilbertWellDefined.WellDefinedStatement)
    (hpos : PairingPosSemidef σ) :
    ∃ cl : PositiveSpan →ₗ[ℂ] StateSpace σ, (∀ F, cl F = stateOf σ F) ∧
      ∀ F F', ⟪cl F, cl F'⟫_ℂ = FieldFormConditions.pairing σ F F' := by
  obtain ⟨-, cl, hcl, hp⟩ := hC.1 PositiveSpan (FieldFormConditions.pairing σ) hpos
  exact ⟨cl, hcl, hp.inner_eq⟩
theorem stateOf_eq_of_pairing (hC : HilbertWellDefined.WellDefinedStatement)
    (hpos : PairingPosSemidef σ) {P Q : PositiveSpan}
    (h : ∀ F', FieldFormConditions.pairing σ F' P = FieldFormConditions.pairing σ F' Q) :
    stateOf σ P = stateOf σ Q := by
  obtain ⟨cl, hcl, hin⟩ := exists_linear_stateOf hC hpos
  have hp : SesquilinearForms.IsPosSemidefForm (FieldFormConditions.pairing σ) := hpos
  have e := (congrArg (FieldFormConditions.pairing σ (P - Q)) (sub_add_cancel P Q).symm).trans
    (hp.add_right (P - Q) (P - Q) Q)
  rw [h (P - Q)] at e
  have e₀ : FieldFormConditions.pairing σ (P - Q) (P - Q) = 0 := by
    linear_combination -e
  have hz : cl (P - Q) = 0 := inner_self_eq_zero (𝕜 := ℂ).1 ((hin _ _).trans e₀)
  rw [← hcl, ← hcl]
  exact sub_eq_zero.1 (by rw [← map_sub]; exact hz)
theorem pairing_eq_insertionPairing (f : AmbientSpace → ℂ) (G : FormalSpan)
    (h : formalMul (complexTuple f) G ∈ spanIn TimeAxis.upperHalfSpace) (F' : PositiveSpan) :
    FieldFormConditions.pairing σ F' ⟨_, h⟩ = insertionPairing σ f (reflectConj F') G := rfl
variable (hAct : BasicFacts.PushSpanProperties)
include hAct
theorem insertion_mem_spanIn {v : AmbientSpace} {f : AmbientSpace → ℂ} (hf : SupportedBelow v f)
    (F : PositiveSpan) :
    formalMul (complexTuple f) (shiftedSpan v F).1 ∈ spanIn TimeAxis.upperHalfSpace :=
  spanIn_mono (Set.union_subset (fun _ hx => hx.1) (fun _ hx => hx.1))
    (R4TupleForms.formalMul_mem (disjoint_slabBelow_regionAbove v)
      (complexTuple_mem_spanIn hf.1 (supportedBelow_tsupport_subset hf))
      (shiftedSpan_mem_regionAbove hAct v F))
theorem insertedState_eq {v : AmbientSpace} {f : AmbientSpace → ℂ} (hf : SupportedBelow v f)
    (F : PositiveSpan) :
    insertedState σ f v F = stateOf σ ⟨_, insertion_mem_spanIn hAct hf F⟩ :=
  dif_pos _
theorem insertedState_add (hC : HilbertWellDefined.WellDefinedStatement)
    (hσ : TestSpaces.IsSepFunctional σ) (hpos : PairingPosSemidef σ) {v : AmbientSpace}
    {f g : AmbientSpace → ℂ} (hf : SupportedBelow v f) (hg : SupportedBelow v g) (F : PositiveSpan) :
    insertedState σ (f + g) v F = insertedState σ f v F + insertedState σ g v F := by
  obtain ⟨cl, hcl, -⟩ := exists_linear_stateOf hC hpos
  have hp : SesquilinearForms.IsPosSemidefForm (FieldFormConditions.pairing σ) := hpos
  rw [insertedState_eq hAct (supportedBelow_add hf hg), insertedState_eq hAct hf,
    insertedState_eq hAct hg, ← hcl, ← hcl, ← hcl, ← map_add, hcl, hcl]
  refine stateOf_eq_of_pairing hC hpos fun F' => ?_
  rw [hp.add_right, pairing_eq_insertionPairing, pairing_eq_insertionPairing,
    pairing_eq_insertionPairing]
  exact insertionPairing_add hσ (disjoint_lowerHalfSpace_slabBelow v)
    (disjoint_slabBelow_regionAbove v) (disjoint_lowerHalfSpace_regionAbove v)
    hf.1 hg.1 (supportedBelow_tsupport_subset hf) (supportedBelow_tsupport_subset hg)
    (reflectConj_mem hAct F') (shiftedSpan_mem_regionAbove hAct v F)
theorem insertedState_smul (hC : HilbertWellDefined.WellDefinedStatement)
    (hσ : TestSpaces.IsSepFunctional σ) (hpos : PairingPosSemidef σ) {v : AmbientSpace}
    (c : ℂ) {f : AmbientSpace → ℂ} (hf : SupportedBelow v f) (F : PositiveSpan) :
    insertedState σ (c • f) v F = c • insertedState σ f v F := by
  obtain ⟨cl, hcl, -⟩ := exists_linear_stateOf hC hpos
  have hp : SesquilinearForms.IsPosSemidefForm (FieldFormConditions.pairing σ) := hpos
  rw [insertedState_eq hAct (supportedBelow_smul c hf), insertedState_eq hAct hf, ← hcl, ← hcl,
    ← map_smul, hcl, hcl]
  refine stateOf_eq_of_pairing hC hpos fun F' => ?_
  rw [hp.smul_right, pairing_eq_insertionPairing, pairing_eq_insertionPairing]
  exact insertionPairing_smul hσ (disjoint_lowerHalfSpace_slabBelow v)
    (disjoint_slabBelow_regionAbove v) (disjoint_lowerHalfSpace_regionAbove v) c hf.1
    (supportedBelow_tsupport_subset hf) (reflectConj_mem hAct F')
    (shiftedSpan_mem_regionAbove hAct v F)
theorem insertedState_zero (hC : HilbertWellDefined.WellDefinedStatement)
    (hσ : TestSpaces.IsSepFunctional σ) (hpos : PairingPosSemidef σ) (v : AmbientSpace)
    (F : PositiveSpan) : insertedState σ 0 v F = 0 := by
  simpa using insertedState_smul hAct hC hσ hpos 0 (supportedBelow_zero v) F
theorem insertedState_sum (hC : HilbertWellDefined.WellDefinedStatement)
    (hσ : TestSpaces.IsSepFunctional σ) (hpos : PairingPosSemidef σ) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → AmbientSpace → ℂ) (v : AmbientSpace) (F : PositiveSpan)
    (hf : ∀ i ∈ s, SupportedBelow v (f i)) :
    insertedState σ (∑ i ∈ s, c i • f i) v F = ∑ i ∈ s, c i • insertedState σ (f i) v F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using insertedState_zero hAct hC hσ hpos v F
  | insert i s hi ih =>
    have h₁ := hf i (Finset.mem_insert_self i s)
    have h₂ : ∀ j ∈ s, SupportedBelow v (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      insertedState_add hAct hC hσ hpos (supportedBelow_smul _ h₁) (supportedBelow_sum s c f h₂),
      insertedState_smul hAct hC hσ hpos _ h₁, ih h₂]
end Classes
theorem translateFun_mem_complexC1c (a : AmbientSpace) {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) :
    translateFun a f ∈ ComplexC1c :=
  ⟨hf.1.comp (contDiff_id.sub contDiff_const), hf.2.1.comp_homeomorph (Homeomorph.subRight a),
    Set.subset_univ _⟩
theorem supportedBelow_translateFun {a v : AmbientSpace} (ha : 0 ≤ a TimeAxis.timeIdx)
    {f : AmbientSpace → ℂ} (hf : SupportedBelow v f) : SupportedBelow (a + v) (translateFun a f) := by
  refine ⟨translateFun_mem_complexC1c a hf.1, fun x hx => ?_⟩
  have e : tsupport (translateFun a f) = Homeomorph.subRight a ⁻¹' tsupport f :=
    tsupport_comp_eq_preimage f (Homeomorph.subRight a)
  rw [e] at hx
  have h := hf.2 _ hx
  have e' : (Homeomorph.subRight a x) TimeAxis.timeIdx =
      x TimeAxis.timeIdx - a TimeAxis.timeIdx := rfl
  rw [e'] at h
  show 0 < x TimeAxis.timeIdx ∧
    x TimeAxis.timeIdx ≤ a TimeAxis.timeIdx + v TimeAxis.timeIdx
  constructor <;> linarith [h.1, h.2]
theorem push_translate_singletonTuple (hIso : BasicFacts.IsometryActionOnTuples) (a : AmbientSpace)
    {g : RealValued} (hg : IsC1c g) (hg' : IsC1c fun x => g (x - a)) :
    push (translate a) (singletonTuple g hg) = singletonTuple (fun x => g (x - a)) hg' := by
  have hsep := (hIso _ (isEuclidIsometry_translate a) (singletonTuple g hg)
    (singletonTuple g hg)).1
  refine Subtype.ext ?_
  unfold push
  rw [dif_pos hsep]
  show pushList (translate a) [g] = [fun x => g (x - a)]
  rw [pushList_translate]
  rfl
theorem pushSpan_translate_complexTuple (hIso : BasicFacts.IsometryActionOnTuples) (a : AmbientSpace)
    {f : AmbientSpace → ℂ} (hf : f ∈ ComplexC1c) :
    pushSpan (translate a) (complexTuple f) = complexTuple (translateFun a f) := by
  have hs := translateFun_mem_complexC1c a hf
  by_cases hr : ∀ x, (f x).im = 0
  · have hr' : ∀ x, (translateFun a f x).im = 0 := fun x => hr _
    rw [complexTuple_eq_of_real hf hr, complexTuple_eq_of_real hs hr', pushSpan_basisVec,
      push_translate_singletonTuple hIso a _ (isC1c_reFun hs)]
    rfl
  · have hr' : ¬∀ x, (translateFun a f x).im = 0 := fun h => hr fun x => by
      simpa [translateFun] using h (x + a)
    rw [complexTuple_eq_of_not_real hf hr, complexTuple_eq_of_not_real hs hr', map_add, map_smul,
      pushSpan_basisVec, pushSpan_basisVec, push_translate_singletonTuple hIso a _ (isC1c_reFun hs),
      push_translate_singletonTuple hIso a _ (isC1c_imFun hs)]
    rfl
section Moves
variable {σ : TestSpaces.SepTuple → ℝ}
theorem spectralTranslation_insertedState (hAct : BasicFacts.PushSpanProperties)
    (hIso : BasicFacts.IsometryActionOnTuples)
    (hC : HilbertWellDefined.WellDefinedStatement)
    (hσ : TestSpaces.IsSepFunctional σ) (hpos : PairingPosSemidef σ)
    {E : FourBorelSet → BddOp (StateSpace σ)} (hE : IsTranslationMeasure σ E)
    {a v : AmbientSpace} {f : AmbientSpace → ℂ} (F : PositiveSpan) (ha : 0 ≤ a TimeAxis.timeIdx)
    (hf : SupportedBelow v f) :
    spectralTranslation E (realWickPoint a) (insertedState σ f v F) =
      insertedState σ (translateFun a f) (a + v) F := by
  by_cases hv : 0 ≤ v TimeAxis.timeIdx
  · have hf' := supportedBelow_translateFun ha hf
    have hdef : R4TupleForms.FormalMulDefined (complexTuple f) (shiftedSpan v F).1 :=
      R4TupleForms.formalMulDefined_of_mem (disjoint_slabBelow_regionAbove v)
        (complexTuple_mem_spanIn hf.1 (supportedBelow_tsupport_subset hf))
        (shiftedSpan_mem_regionAbove hAct v F)
    rw [insertedState_eq hAct hf, insertedState_eq hAct hf']
    refine (hE.translate_stateOf _ a ha).trans (congrArg _ (Subtype.ext ?_))
    rw [shiftedSpan_val hAct ha]
    show pushSpan (translate a) (formalMul (complexTuple f) (shiftedSpan v F).1) =
      formalMul (complexTuple (translateFun a f)) (shiftedSpan (a + v) F).1
    rw [pushSpan_translate_formalMul hAct a hdef, pushSpan_translate_complexTuple hIso a hf.1,
      ← shiftedSpan_val hAct ha (shiftedSpan v F), shiftedSpan_shiftedSpan hAct ha hv]
  · have e := eq_zero_of_supportedBelow hv hf
    subst e
    have e' : translateFun a (0 : AmbientSpace → ℂ) = 0 := rfl
    rw [e', insertedState_zero hAct hC hσ hpos, insertedState_zero hAct hC hσ hpos, map_zero]
theorem insertedState_shiftedSpan (hAct : BasicFacts.PushSpanProperties)
    (hC : HilbertWellDefined.WellDefinedStatement)
    (hσ : TestSpaces.IsSepFunctional σ) (hpos : PairingPosSemidef σ)
    {v w : AmbientSpace} {f : AmbientSpace → ℂ} (F : PositiveSpan) (hw : 0 ≤ w TimeAxis.timeIdx)
    (hf : SupportedBelow v f) :
    insertedState σ f (v + w) F = insertedState σ f v (shiftedSpan w F) := by
  by_cases hv : 0 ≤ v TimeAxis.timeIdx
  · rw [insertedState, insertedState, shiftedSpan_shiftedSpan hAct hv hw]
  · have e := eq_zero_of_supportedBelow hv hf
    subst e
    rw [insertedState_zero hAct hC hσ hpos, insertedState_zero hAct hC hσ hpos]
end Moves
theorem insertedStateProperties_holds (hFacts : BasicFacts.MainFacts)
    (hC : HilbertWellDefined.WellDefinedStatement) : InsertedStateProperties := by
  intro σ E p C h
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  have hIso : BasicFacts.IsometryActionOnTuples := hFacts.1
  refine ⟨fun v f F hf => insertion_mem_spanIn hAct hf F, fun s c f v F hf => ?_,
    fun a v f F ha hf => ?_, fun v w f F hw hf => ?_⟩
  · exact insertedState_sum hAct hC h.isSepFunctional h.posSemidef s c f v F hf
  · exact spectralTranslation_insertedState hAct hIso hC h.isSepFunctional h.posSemidef
      h.translationMeasure F ha hf
  · exact insertedState_shiftedSpan hAct hC h.isSepFunctional h.posSemidef F hw hf
end YangMills.Construction.InsertedFieldClasses
end
