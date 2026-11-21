import YangMills.Construction.ReflectionPositivity.SequencesOfLatticeDataAndTheirLimits
import YangMills.Construction.PassageToTheLimit.NestedPositions
import YangMills.Construction.ReflectionPositivity.CentredFunctionalsAlongAConvergentSequenceProof
import YangMills.Construction.ReflectionPositivity.InequalityOnTuplesAtALinkMirror
import YangMills.Construction.ReflectionPositivity.InequalityPassesToTheLimitAtFixedTuples
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ComplexConjugate ComplexOrder ENNReal Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity
variable {D : MirrorData}
theorem eventually_mem_halfShifted (hn : LimitSpaces.RefinedCutoffs.Claim)
    {E : Ambient} (S : LatticeDataSeq D E) {c : ℝ}
    (hc : c ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters) :
    ∀ᶠ j in atTop,
      c ∈ LimitSpaces.halfShiftedMultiplesOf (PeriodicLattice.meshSize D.L (S.K j : ℕ)) := by
  obtain ⟨n, hn'⟩ := mem_iUnion.1 hc
  let p : Conventions.StandingParameters := ⟨D.L, D.isAdmissible, n, D.m⟩
  filter_upwards [S.K_tendsto.eventually_ge_atTop (n : ℕ)] with j hj
  exact (hn p (S.K j) hj).2.2.2.1 hn'
def toCutoffData (d : MirrorData) (μ : Fin 4) : CutoffMirrors.MirrorData :=
  ⟨d.toStandingParameters, d.β, d.β_pos, μ⟩
theorem reflect_eq_cutoffReflect (d : MirrorData) (μ : Fin 4) (c : ℝ) :
    CoordMirror.reflect d ⟨μ, c⟩ .torus = (toCutoffData d μ).reflect c := by
  refine ((toCutoffData d μ).existsUnique_induces c).unique ?_
    ((toCutoffData d μ).induces_reflect c)
  rw [Sides.reflect_torus]
  funext y
  have h₁ :=
    congrFun (LimitSpaces.Ambient.periodic.reflect_comp_proj d.toStandingParameters μ c) y
  have h₂ : (toCutoffData d μ).reflectVec c y = LimitSpaces.reflectR4 μ c y :=
    ((toCutoffData d μ).reflectVec_eq_sub c y).trans
      (congrFun (Sides.euclidReflect_eq_reflectR4 μ c) y)
  simp only [Function.comp_apply] at h₁ ⊢
  rw [h₂]
  exact h₁
theorem upperSide_eq_openSlab (d : MirrorData) (μ : Fin 4) (c : ℝ) :
    (CoordMirror.mk μ c).upperSide d .torus =
      (toCutoffData d μ).openSlab c CutoffMirrors.SlabSide.pos := by
  simp only [CoordMirror.upperSide, CutoffMirrors.MirrorData.openSlab,
    CutoffMirrors.SlabSide.toReal, one_mul]
  rfl
theorem list_pairwise_get_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x)
    {L : List α} (h : L.Pairwise R) : Pairwise fun i j : Fin L.length => R (L.get i) (L.get j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_get.1 h _ _ hlt
  · exact hR _ _ (List.pairwise_iff_get.1 h _ _ hlt)
theorem positivity_at_cutoff (hin : CutoffMirrors.TupleInequality.Statement)
    (d : MirrorData) (μ : Fin 4) {c : ℝ}
    (hc : c ∈ LimitSpaces.halfShiftedMultiplesOf (PeriodicLattice.meshSize d.L (d.K : ℕ)))
    {r : ℕ} (hr : 1 ≤ r) (X : Fin r → FnList d torus) (w : Fin r → ℂ)
    (hlip : ∀ i, ∀ f ∈ X i, TestFunctions.IsLipschitzFor (toCutoffData d μ).torusDist f)
    (hdis : ∀ i, (X i).Pairwise fun f g => Disjoint (closedSupport d torus f) (closedSupport d torus g))
    (hsupp : ∀ i, ∀ f ∈ X i, closedSupport d torus f ⊆ (CoordMirror.mk μ c).upperSide d torus) :
    (∑ i, ∑ k, conj (w i) * w k * (((toCutoffData d μ).gibbsFunctionalList
        ((CoordMirror.mk μ c).reflectAppend d torus (X i) (X k)) : ℝ) : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ k, conj (w i) * w k * (((toCutoffData d μ).gibbsFunctionalList
        ((CoordMirror.mk μ c).reflectAppend d torus (X i) (X k)) : ℝ) : ℂ)).re := by
  let C : CutoffMirrors.LinkLevel (toCutoffData d μ) :=
    ⟨c, by obtain ⟨n, hn⟩ := hc; exact ⟨n, hn⟩⟩
  have hargs : ∀ i, CutoffMirrors.TupleInequality.IsPosSideArgs C (X i).get := fun i => by
    refine ⟨⟨fun l => hlip i _ (List.get_mem _ _), fun l l' hll => ?_⟩, fun l => ?_⟩
    · exact Set.disjoint_iff_inter_eq_empty.1
        (list_pairwise_get_of_symm (fun _ _ h => h.symm) (hdis i) hll)
    · have h := hsupp i _ (List.get_mem (X i) l)
      rw [upperSide_eq_openSlab] at h
      exact h
  obtain ⟨-, -, ⟨e, hn⟩, -⟩ := (hin (toCutoffData d μ) C).1 r hr X w hargs
  let Xd : Fin r → (toCutoffData d μ).FunTuple ℝ := X
  have eT : ∀ i k, (CoordMirror.mk μ c).reflectAppend d torus (X i) (X k) =
      C.reflectTuple (Xd i) ++ Xd k := fun i k => by
    have hθ : (CoordMirror.mk μ c).pullback d torus (α := ℝ) = C.reflectFn := by
      funext f
      show f ∘ CoordMirror.reflect d ⟨μ, c⟩ .torus = f ∘ (toCutoffData d μ).reflect c
      rw [reflect_eq_cutoffReflect]
      rfl
    exact congrArg (fun g : (Point d torus → ℝ) → (Point d torus → ℝ) => List.map g (X i) ++ X k) hθ
  have eS : (∑ i, ∑ k, conj (w i) * w k * (((toCutoffData d μ).gibbsFunctionalList
      ((CoordMirror.mk μ c).reflectAppend d torus (X i) (X k)) : ℝ) : ℂ)) =
      CutoffMirrors.TupleInequality.pairSum C X w
        (fun Y => (((toCutoffData d μ).gibbsFunctionalList Y : ℝ) : ℂ)) := by
    simp only [CutoffMirrors.TupleInequality.pairSum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [eT]
  rw [eS, e]
  exact ⟨(Complex.le_def.1 hn).2.symm, (Complex.le_def.1 hn).1⟩
def pairSumAt {E : Ambient} (S : LatticeDataSeq D E) (μ : Fin 4) (c : ℝ) {r : ℕ}
    (X : Fin r → FnList D E) (w : Fin r → ℂ) (j : ℕ+) : ℂ :=
  ∑ i, ∑ k, conj (w i) * w k *
    ((S.centredAt j ((CoordMirror.mk μ c).reflectAppend D E (X i) (X k)) : ℝ) : ℂ)
theorem positivity_torus (hin : CutoffMirrors.TupleInequality.Statement)
    (S : LatticeDataSeq D torus) {μ : Fin 4} {c : ℝ} {j : ℕ+}
    (hlink : c ∈ LimitSpaces.halfShiftedMultiplesOf (PeriodicLattice.meshSize D.L (S.K j : ℕ)))
    {r : ℕ} (hr : 1 ≤ r) (X : Fin r → FnList D torus) (w : Fin r → ℂ)
    (hlip : ∀ i, ∀ f ∈ X i, LimitSpaces.Ambient.periodic.IsLip D.toStandingParameters f)
    (hdis : ∀ i, (X i).Pairwise fun f g => Disjoint (closedSupport D torus f) (closedSupport D torus g))
    (hsupp : ∀ i, ∀ f ∈ X i, closedSupport D torus f ⊆ (CoordMirror.mk μ c).upperSide D torus) :
    (pairSumAt S μ c X w j).im = 0 ∧ 0 ≤ (pairSumAt S μ c X w j).re := by
  let d : MirrorData := ⟨S.standingAtExp j D.m, S.β j, S.β_pos j⟩
  have h := positivity_at_cutoff hin d μ hlink hr
    (fun i => (X i : FnList d torus)) w hlip hdis hsupp
  have e : pairSumAt S μ c X w j =
      ∑ i, ∑ k, conj (w i) * w k *
        (((toCutoffData d μ).gibbsFunctionalList ((CoordMirror.mk μ c).reflectAppend d torus
          (X i : FnList d torus) (X k : FnList d torus)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [S.centredAt_torus]
    rfl
  rw [e]
  exact h
theorem isSepLipList_of_mem_separatedAll (hs : Sides.HyperplaneSidesClaim) (E : Ambient)
    {X : FnList D E} (hX : X ∈ separatedAll D E) : IsSepLipList D E X := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.CenteredConvergence.isSepLipList_of_mem <;> assumption
def mirrorDataAt {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) : MirrorData :=
  ⟨S.standingAt j, S.β j, S.β_pos j⟩
theorem positivity_euclidean (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties)
    (S : LatticeDataSeq D euclidean) {μ : Fin 4} {c : ℝ} {j : ℕ+}
    (hlink : c ∈ LimitSpaces.halfShiftedMultiplesOf (PeriodicLattice.meshSize D.L (S.K j : ℕ)))
    (I : (CoordMirror.mk μ c).PositivityInstance D euclidean)
    (hfit : ∀ i k, LimitSpaces.FitsInTorus (S.standingAt j)
      ((CoordMirror.mk μ c).reflectAppend D euclidean (I.tuples i).1 (I.tuples k).1))
    (hslab : ∀ i, ∀ f ∈ (I.tuples i).1, closedSupport D euclidean f ⊆
      coordSet μ fun t => c < t ∧ t < c + (mirrorDataAt S j).side / 2) :
    (pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j).im = 0 ∧
      0 ≤ (pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j).re := by
  let d : MirrorData := mirrorDataAt S j
  let p : Conventions.StandingParameters := S.standingAt j
  have hcompact : ∀ i, ∀ f ∈ (I.tuples i).1,
      LimitSpaces.Ambient.euclidean.IsCompactSubset d.toStandingParameters
        (LimitSpaces.Ambient.euclidean.closedSupport d.toStandingParameters f) := fun i f hf =>
    ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf).2
  have hcat := fun i k => (htr d).2.2 (I.tuples i).1 (I.tuples k).1 (hcompact i) (hcompact k) μ c
    (hfit i k)
  have hfits : ∀ i, LimitSpaces.FitsInTorus p (I.tuples i).1 := fun i => (hcat i i).1
  let Xl : Fin I.size → List ((Fin 4 → ℝ) → ℝ) := fun i => (I.tuples i).1
  have hsepT := fun i => (htr d).2.1 _ (Xl i).get
  have hlists : ∀ i, LimitSpaces.periodizeList p (Xl i) =
      List.ofFn fun l => LimitSpaces.periodizeFun p ((Xl i).get l) := fun i => by
    have e := LimitSpaces.periodizeList_ofFn p (Xl i).get
    rwa [List.ofFn_get] at e
  have hr : ∀ i, LimitSpaces.Ambient.periodic.IsSepLipTuple p univ
      (fun l => LimitSpaces.periodizeFun p ((Xl i).get l)) := fun i =>
    (hsepT i (isSepLipList_of_mem_separatedAll hs euclidean (I.tuples i).2.1)
      (by rw [List.ofFn_get]; exact hfits i)).1
  let Y : Fin I.size → FnList d torus :=
    fun i => LimitSpaces.periodizeList p (I.tuples i).1
  have hsupp : ∀ i, ∀ g ∈ Y i, closedSupport d torus g ⊆ (CoordMirror.mk μ c).upperSide d torus := by
    intro i g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have hsup : LimitSpaces.Ambient.euclidean.SupportedWithin d.toStandingParameters
        (LimitSpaces.Ambient.euclidean.listSupport d.toStandingParameters (I.tuples i).1) f :=
      ⟨hcompact i f hf, fun x hx => mem_iUnion₂.2 ⟨f, hf, hx⟩⟩
    exact ((htr d).1 _ f f (hfits i).2 hsup hsup).2.2.2.2.2.2 μ c (hslab i f hf) |>.2
  have hlip : ∀ i, ∀ f ∈ Y i, TestFunctions.IsLipschitzFor (toCutoffData d μ).torusDist f := by
    intro i f hf
    have hf' : f ∈ List.ofFn fun l => LimitSpaces.periodizeFun p ((Xl i).get l) :=
      (hlists i) ▸ hf
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hf'
    exact ((hr i).1 l).1
  have hdis : ∀ i, (Y i).Pairwise fun f g => Disjoint (closedSupport d torus f) (closedSupport d torus g) := by
    intro i
    have hp : (List.ofFn fun l => LimitSpaces.periodizeFun p ((Xl i).get l)).Pairwise
        fun f g => Disjoint (closedSupport d torus f) (closedSupport d torus g) :=
      List.pairwise_ofFn.2 fun x y hxy => (hr i).2 hxy.ne
    exact Eq.mpr (congrArg (List.Pairwise _) (hlists i)) hp
  have h := positivity_at_cutoff hin d μ hlink I.one_le_size Y I.coeffs hlip hdis hsupp
  have e : pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j =
      ∑ i, ∑ k, conj (I.coeffs i) * I.coeffs k *
        (((toCutoffData d μ).gibbsFunctionalList
          ((CoordMirror.mk μ c).reflectAppend d torus (Y i) (Y k)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have e₁ : S.centredAt j ((CoordMirror.mk μ c).reflectAppend D euclidean
        (I.tuples i).1 (I.tuples k).1) = (toCutoffData d μ).gibbsFunctionalList
          ((CoordMirror.mk μ c).reflectAppend d torus (Y i) (Y k)) :=
      congrArg (toCutoffData d μ).gibbsFunctionalList (hcat i k).2.2
    exact congrArg (fun z : ℝ => conj (I.coeffs i) * I.coeffs k * (z : ℂ)) e₁
  rw [e]
  exact h
theorem coord_le_euclidNormVec (y : Fin 4 → ℝ) (μ : Fin 4) :
    y μ ≤ TorusMetric.euclidNormVec y := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun ν => y ν ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
theorem side_mirrorDataAt {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) :
    (mirrorDataAt S j).side = S.ℓ j := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.side_standingAt <;> assumption
theorem eventually_support_subset_slab (S : LatticeDataSeq D euclidean) {μ : Fin 4} {c : ℝ}
    {f : Point D euclidean → ℝ} (hf : f ∈ compactC1 D ℝ euclidean)
    (hsub : closedSupport D euclidean f ⊆ (CoordMirror.mk μ c).upperSide D euclidean) :
    ∀ᶠ j in atTop, closedSupport D euclidean f ⊆
      coordSet μ fun t => c < t ∧ t < c + (mirrorDataAt S j).side / 2 := by
  obtain ⟨R, hR⟩ := exists_bound_of_isCompactWrt hf.2
  have hℓ : Tendsto S.ℓ atTop atTop := S.isSideSequence
  filter_upwards [hℓ.eventually_ge_atTop (2 * (R + |c| + 2))] with j h₃ y hy
  refine ⟨hsub hy, ?_⟩
  have h₄ : y μ ≤ R := (coord_le_euclidNormVec y μ).trans (hR y hy)
  have h₆ := neg_abs_le c
  rw [side_mirrorDataAt]
  linarith
theorem eventually_forall_mem_of_list {α β : Type*} {l : Filter β} {P : α → β → Prop} (L : List α)
    (h : ∀ f ∈ L, ∀ᶠ j in l, P f j) : ∀ᶠ j in l, ∀ f ∈ L, P f j := by
  induction L with
  | nil => simp
  | cons f L ih =>
    filter_upwards [h f (by simp), ih fun g hg => h g (by simp [hg])] with j h₁ h₂ g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h₁
    · exact h₂ g hg
theorem limit_pairSum_mem {E : Ambient} (S : LatticeDataSeq D E) {μ : Fin 4} {c : ℝ} {r : ℕ}
    (X : Fin r → FnList D E) (w : Fin r → ℂ) (v : Fin r → Fin r → ℝ)
    (hv : ∀ i k, Tendsto (fun j => S.centredAt j
      ((CoordMirror.mk μ c).reflectAppend D E (X i) (X k))) atTop (𝓝 (v i k)))
    (hev : ∀ᶠ j in atTop, (pairSumAt S μ c X w j).im = 0 ∧ 0 ≤ (pairSumAt S μ c X w j).re) :
    (∑ i, ∑ k, conj (w i) * w k * (v i k : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ k, conj (w i) * w k * (v i k : ℂ)).re := by
  have hclosed : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hlim : Tendsto (pairSumAt S μ c X w) atTop
      (𝓝 (∑ i, ∑ k, conj (w i) * w k * (v i k : ℂ))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ =>
      ((Complex.continuous_ofReal.tendsto _).comp (hv i k)).const_mul _
  exact hclosed.mem_of_tendsto hlim hev
theorem tendsto_centredAt
    (hsig : CenteredFunctionalsConverge) {E : Ambient}
    (S : LatticeDataSeq D E) (T : FunctionalFamily D E) (hST : S.TendsToFamily T)
    {Z : FnList D E} (hZ : Z ∈ separatedAll D E) :
    Tendsto (fun j => S.centredAt j Z) atTop
      (𝓝 (evalOrZero (FunctionalFamily.centeredFunctional T) Z)) := by
  have e : evalOrZero (FunctionalFamily.centeredFunctional T) Z =
      FunctionalFamily.centeredFunctional T ⟨Z, hZ⟩ := by
    simp [evalOrZero, hZ]
  rw [e]
  exact (hsig.1 D E S T hST).1.1 ⟨Z, hZ⟩
theorem eventually_positivity (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties)
    (hn : LimitSpaces.RefinedCutoffs.Claim) {E : Ambient}
    (S : LatticeDataSeq D E) {μ : Fin 4} {c : ℝ}
    (hc : c ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters)
    (I : (CoordMirror.mk μ c).PositivityInstance D E) :
    ∀ᶠ j in atTop, (pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j).im = 0 ∧
      0 ≤ (pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j).re := by
  have hlink := eventually_mem_halfShifted hn S hc
  cases E with
  | torus =>
    filter_upwards [hlink] with j hj
    obtain ⟨-, -, -, -, -, -, -, h₈⟩ := ((hs D 0 0).1 .periodic).1
    exact positivity_torus hin S hj I.one_le_size _ _
      (fun i f hf => (h₈ f ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf)).2.2)
      (fun i => (isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).2)
      (fun i f hf => (I.tuples i).2.2 f hf)
  | euclidean =>
    have hfit : ∀ᶠ j in atTop, ∀ i k, LimitSpaces.FitsInTorus (S.standingAt j)
        ((CoordMirror.mk μ c).reflectAppend D euclidean (I.tuples i).1 (I.tuples k).1) :=
      eventually_all.2 fun i => eventually_all.2 fun k =>
        S.eventually_fitsInTorus ((hs D μ c).2.2.2.2 euclidean _ _ (I.tuples i).2 (I.tuples k).2)
    have hslab : ∀ᶠ j in atTop, ∀ i, ∀ f ∈ (I.tuples i).1, closedSupport D euclidean f ⊆
        coordSet μ fun t => c < t ∧ t < c + (mirrorDataAt S j).side / 2 :=
      eventually_all.2 fun i => eventually_forall_mem_of_list _ fun f hf =>
        eventually_support_subset_slab S
          ((isSeparatedList_of_mem_separatedAll (I.tuples i).2.1).1 f hf)
          ((I.tuples i).2.2 f hf)
    filter_upwards [hlink, hfit, hslab] with j h₁ h₂ h₃
    exact positivity_euclidean hs hin htr S h₁ I h₂ h₃
theorem holds_instances (hs : Sides.HyperplaneSidesClaim)
    (hin : CutoffMirrors.TupleInequality.Statement)
    (htr : LimitSpaces.Periodization.Properties)
    (hn : LimitSpaces.RefinedCutoffs.Claim)
    (hsig : CenteredFunctionalsConverge) {E : Ambient}
    (S : LatticeDataSeq D E) (T : FunctionalFamily D E) (hST : S.TendsToFamily T)
    {μ : Fin 4} {c : ℝ} (hc : c ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters)
    (I : (CoordMirror.mk μ c).PositivityInstance D E) :
    I.HoldsReal (FunctionalFamily.centeredFunctional T) := by
  have h := limit_pairSum_mem S (fun i => (I.tuples i).1) I.coeffs
    (fun i k => evalOrZero (FunctionalFamily.centeredFunctional T)
      ((CoordMirror.mk μ c).reflectAppend D E (I.tuples i).1 (I.tuples k).1))
    (fun i k => tendsto_centredAt hsig S T hST
      ((hs D μ c).2.2.2.2 E _ _ (I.tuples i).2 (I.tuples k).2))
    (eventually_positivity hs hin htr hn S hc I)
  have e : I.lhs (fun X => (FunctionalFamily.centeredFunctional T X : ℂ)) =
      ∑ i, ∑ k, conj (I.coeffs i) * I.coeffs k *
        ((evalOrZero (FunctionalFamily.centeredFunctional T)
          ((CoordMirror.mk μ c).reflectAppend D E (I.tuples i).1 (I.tuples k).1) : ℝ) : ℂ) := by
    simp only [CoordMirror.PositivityInstance.lhs, CoordMirror.positivitySum, evalOrZeroC_ofReal]
  show (I.lhs _).im = 0 ∧ 0 ≤ (I.lhs _).re
  rw [e]
  exact h
theorem reflectAppend_torus (d : MirrorData) (μ : Fin 4) (c : ℝ)
    (X Y : List (LimitSpaces.Ambient.periodic.Carrier d.toStandingParameters → ℝ)) :
    ((CoordMirror.mk μ c).reflectAppend d torus X Y : FnList d torus) =
      (X.map (LimitSpaces.Ambient.periodic.reflectFun d.toStandingParameters μ c) ++ Y :
        List (LimitSpaces.Ambient.periodic.Carrier d.toStandingParameters → ℝ)) := by
  have h : (CoordMirror.mk μ c).pullback d torus (α := ℝ) =
      LimitSpaces.Ambient.periodic.reflectFun d.toStandingParameters μ c := by
    funext f
    show f ∘ CoordMirror.reflect d ⟨μ, c⟩ .torus = _
    rw [Sides.reflect_torus]
    rfl
  exact congrArg (fun g : (LimitSpaces.Ambient.periodic.Carrier d.toStandingParameters → ℝ) →
    (LimitSpaces.Ambient.periodic.Carrier d.toStandingParameters → ℝ) => List.map g X ++ Y) h
theorem reflectAppend_mem_sepLipTuples (hs : Sides.HyperplaneSidesClaim) {μ : Fin 4} {c : ℝ}
    {X Y : FnList D torus}
    (hX : X ∈ sepLipTuplesSuppIn D ((CoordMirror.mk μ c).upperSide D torus))
    (hY : Y ∈ sepLipTuplesSuppIn D ((CoordMirror.mk μ c).upperSide D torus)) :
    (CoordMirror.mk μ c).reflectAppend D torus X Y ∈ sepLipTuples D := by
  have h := ((hs D μ c).1 .periodic).2.2.2.2.2.1 X Y hX.1 hY.1 hX.2 hY.2
  exact Eq.mpr (congrArg (fun Z : FnList D torus => Z ∈ sepLipTuples D)
    (reflectAppend_torus D μ c X Y)) h
theorem holds_lipInstances (hin : CutoffMirrors.TupleInequality.Statement)
    (hs : Sides.HyperplaneSidesClaim) (hn : LimitSpaces.RefinedCutoffs.Claim)
    (hsig : CenteredFunctionalsConverge)
    (S : LatticeDataSeq D torus) (T : FunctionalFamily D torus) (hST : S.TendsToFamily T)
    {μ : Fin 4} {c : ℝ} (hc : c ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters)
    (hex : S.LipLimitsExist) (I : (CoordMirror.mk μ c).LipPositivityInstance D) :
    I.HoldsReal S.lipLimitCenteredFunctional := by
  have hconv : ∀ i k, Tendsto (fun j => S.centredAt j
      ((CoordMirror.mk μ c).reflectAppend D torus (I.tuples i).1 (I.tuples k).1)) atTop
      (𝓝 (evalOrZero S.lipLimitCenteredFunctional
        ((CoordMirror.mk μ c).reflectAppend D torus (I.tuples i).1 (I.tuples k).1))) := by
    intro i k
    have hZ := reflectAppend_mem_sepLipTuples hs (I.tuples i).2 (I.tuples k).2
    have e : evalOrZero S.lipLimitCenteredFunctional
        ((CoordMirror.mk μ c).reflectAppend D torus (I.tuples i).1 (I.tuples k).1) =
        S.lipLimitCenteredFunctional ⟨_, hZ⟩ := by
      simp [evalOrZero, hZ]
    rw [e]
    exact (hsig.2 D S T hST hex) _ hZ
  have hev : ∀ᶠ j in atTop,
      (pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j).im = 0 ∧
      0 ≤ (pairSumAt S μ c (fun i => (I.tuples i).1) I.coeffs j).re := by
    filter_upwards [eventually_mem_halfShifted hn S hc] with j hj
    refine positivity_torus hin S hj I.one_le_size _ _ (fun i f hf => ?_) (fun i => ?_)
      (fun i f hf => ((I.tuples i).2.2 f hf).2)
    · obtain ⟨l, rfl⟩ := List.get_of_mem hf
      exact ((I.tuples i).2.1.1 l).1
    · refine List.pairwise_iff_get.2 fun x y hxy => ?_
      exact (I.tuples i).2.1.2 hxy.ne
  have h := limit_pairSum_mem S (fun i => (I.tuples i).1) I.coeffs _ hconv hev
  have e : I.lhs (fun X => (S.lipLimitCenteredFunctional X : ℂ)) =
      ∑ i, ∑ k, conj (I.coeffs i) * I.coeffs k *
        ((evalOrZero S.lipLimitCenteredFunctional
          ((CoordMirror.mk μ c).reflectAppend D torus (I.tuples i).1 (I.tuples k).1) : ℝ) : ℂ) := by
    simp only [CoordMirror.LipPositivityInstance.lhs, CoordMirror.positivitySum,
      evalOrZeroC_ofReal]
  show (I.lhs _).im = 0 ∧ 0 ≤ (I.lhs _).re
  rw [e]
  exact h
theorem positivityPassesToLimit_holds (hin : CutoffMirrors.TupleInequality.Statement)
    (hn : LimitSpaces.RefinedCutoffs.Claim) (hs : Sides.HyperplaneSidesClaim)
    (hsig : CenteredFunctionalsConverge)
    (htr : LimitSpaces.Periodization.Properties) : PositivityPassesToLimit :=
  ⟨fun _ _ S T hST _ _ hc I => holds_instances hs hin htr hn hsig S T hST hc I,
    fun _ S T hST _ _ hc hex I => holds_lipInstances hin hs hn hsig S T hST hc hex I⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.LatticeDataSeq.LimitPositivity
end
