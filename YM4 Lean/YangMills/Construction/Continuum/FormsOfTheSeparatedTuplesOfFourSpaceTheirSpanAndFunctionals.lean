import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.R4TupleForms
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
variable (s : Conventions.StandingParameters)
abbrev FinTuple : Type := allSeparatedTuples s .euclidean
variable {s}
theorem closure_pt_euclidean (Z : Set (Fin 4 → ℝ)) :
    @closure (Pt s .euclidean) _ Z = closure Z :=
  (closure_eq_closureWrt (X := Pt s .euclidean) Z).trans
    (SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) Z)
theorem tsupport_pt_euclidean (f : SeparatedTuples.RealValued) :
    (@tsupport (Pt s .euclidean) ℝ _ _ f : Set (Fin 4 → ℝ)) = tsupport f :=
  closure_pt_euclidean _
theorem isCompact_pt_euclidean_iff (Z : Set (Fin 4 → ℝ)) :
    @IsCompact (Pt s .euclidean) _ Z ↔ IsCompact Z :=
  (isCompact_iff_isCompactWrt (X := Pt s .euclidean) Z).trans
    (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) Z)
theorem isCompact_tsupport_pt_iff_hasCompactSupport (f : SeparatedTuples.RealValued) :
    @IsCompact (Pt s .euclidean) _ (@tsupport (Pt s .euclidean) ℝ _ _ f) ↔
      HasCompactSupport f :=
  (isCompact_pt_euclidean_iff _).trans
    (congrArg (@IsCompact (Fin 4 → ℝ) _) (tsupport_pt_euclidean f)).to_iff
theorem mem_c1CompactlySupportedIn_univ_iff (f : SeparatedTuples.RealValued) :
    f ∈ c1CompactlySupportedIn (Set.univ : Set (Pt s .euclidean)) ↔
      SeparatedTuples.IsC1c f :=
  ⟨fun h => ⟨h.1, (isCompact_tsupport_pt_iff_hasCompactSupport f).1 h.2.1⟩,
    fun h => ⟨h.1, (isCompact_tsupport_pt_iff_hasCompactSupport f).2 h.2, Set.subset_univ _⟩⟩
theorem mem_separatedTuples_iff_ofFn {n : ℕ} (f : Fin n → SeparatedTuples.RealValued) :
    f ∈ separatedTuples s .euclidean n ↔
      SeparatedTuples.IsDisjointlySupported (List.ofFn f) := by
  constructor
  · rintro ⟨hreg, hdisj⟩
    refine ⟨fun g hg => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact ⟨(hreg i).1, (isCompact_tsupport_pt_iff_hasCompactSupport (f i)).1 (hreg i).2⟩
    · exact Disjoint.mono (tsupport_pt_euclidean (s := s) (f i)).ge
        (tsupport_pt_euclidean (s := s) (f j)).ge (hdisj hij.ne)
  · rintro ⟨hreg, hpw⟩
    have hp := List.pairwise_ofFn.1 hpw
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have h := hreg (f i) ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
      exact ⟨h.1, (isCompact_tsupport_pt_iff_hasCompactSupport (f i)).2 h.2⟩
    · have hd : Disjoint (tsupport (f i)) (tsupport (f j)) := by
        rcases lt_or_gt_of_ne hij with h | h
        · exact hp h
        · exact (hp h).symm
      exact Disjoint.mono (tsupport_pt_euclidean (s := s) (f i)).le
        (tsupport_pt_euclidean (s := s) (f j)).le hd
def listOf (X : FinTuple s) : SeparatedTuples.SepTuple :=
  ⟨List.ofFn X.1.2, (mem_separatedTuples_iff_ofFn X.1.2).1 X.2⟩
def ofListTuple (X : SeparatedTuples.SepTuple) : FinTuple s :=
  ⟨⟨X.1.length, X.1.get⟩, (mem_separatedTuples_iff_ofFn (s := s) X.1.get).2 (by
    rw [show List.ofFn X.1.get = X.1 from List.ofFn_get X.1]
    exact X.2)⟩
variable (s) in
def finTupleEquiv : FinTuple s ≃ SeparatedTuples.SepTuple where
  toFun := listOf
  invFun := ofListTuple
  left_inv := by
    rintro ⟨⟨n, f⟩, hf⟩
    refine Subtype.ext (Sigma.ext (List.length_ofFn) ?_)
    refine (Fin.heq_fun_iff List.length_ofFn).2 fun i => ?_
    exact List.get_ofFn f i
  right_inv := fun X => Subtype.ext (List.ofFn_get X.1)
theorem listOf_nilTuple :
    listOf (⟨nilTuple s .euclidean, nilTuple_mem_allSeparatedTuples⟩ : FinTuple s) =
      SeparatedTuples.SepTuple.nil :=
  Subtype.ext rfl
theorem isDisjointlySupported_iff_mem_separatedAll
    (D : ReflectionPositivity.AxisMirror.MirrorData)
    (X : List SeparatedTuples.RealValued) :
    SeparatedTuples.IsDisjointlySupported X ↔ X ∈ Ambient.separatedAll D .euclidean := by apply _root_.YangMills.Construction.SeparatedTuplesR4.isDisjointTuple_iff_mem_separatedAll <;> assumption
theorem closedSupport_euclidean_eq (D : ReflectionPositivity.AxisMirror.MirrorData)
    (f : SeparatedTuples.RealValued) :
    (Ambient.closedSupport D .euclidean f : Set (Fin 4 → ℝ)) = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_supportedIn_iff_mem_separatedWithin
    (D : ReflectionPositivity.AxisMirror.MirrorData) (O : Set (Fin 4 → ℝ))
    (X : SeparatedTuples.SepTuple) :
    X ∈ SeparatedTuples.supportedIn O ↔ X.1 ∈ Ambient.separatedWithin D .euclidean O := by
  constructor
  · intro h
    refine ⟨(isDisjointlySupported_iff_mem_separatedAll D X.1).1 X.2, fun f hf x hx => ?_⟩
    exact h f hf ((Set.ext_iff.1 (closedSupport_euclidean_eq D f) x).1 hx)
  · rintro ⟨-, h⟩ f hf x hx
    exact h f hf ((Set.ext_iff.1 (closedSupport_euclidean_eq D f) x).2 hx)
theorem juxt_val_eq_append (D : ReflectionPositivity.AxisMirror.MirrorData)
    {X Y : SeparatedTuples.SepTuple} (h : SeparatedTuples.SepTuple.Composable X Y) :
    (SeparatedTuples.SepTuple.juxt X Y).1 =
      Ambient.append (D := D) (E := .euclidean) X.1 Y.1 :=
  SeparatedTuples.SepTuple.juxt_val h
def singleTuple (f : SeparatedTuples.RealValued) (hf : SeparatedTuples.IsC1c f) :
    SeparatedTuples.SepTuple :=
  ⟨[f], by simpa [SeparatedTuples.IsDisjointlySupported] using hf⟩
theorem isDistIsometry_iff (r : Pt s .euclidean ≃ Pt s .euclidean) :
    IsDistIsometry r ↔ SeparatedTuples.IsEuclidIsometry r :=
  Iff.rfl
theorem invMap_eq_symm (r : Pt s .euclidean ≃ Pt s .euclidean) :
    SeparatedTuples.invMap r = r.symm := by
  have hne : Nonempty (Pt s .euclidean) := ⟨(0 : Fin 4 → ℝ)⟩
  funext x
  exact (congrArg (Function.invFun r) (r.apply_symm_apply x)).symm.trans
    (Function.leftInverse_invFun r.injective (r.symm x))
theorem ofFn_transportTuple {n : ℕ} (r : Pt s .euclidean ≃ Pt s .euclidean)
    (f : Fin n → Pt s .euclidean → ℝ) :
    List.ofFn (transportTuple r f) = SeparatedTuples.pushList r (List.ofFn f) := by
  simp only [SeparatedTuples.pushList, invMap_eq_symm]
  exact List.map_ofFn.symm
theorem listOf_transportTuple {n : ℕ} (r : Pt s .euclidean ≃ Pt s .euclidean)
    {f : Fin n → Pt s .euclidean → ℝ} (hf : f ∈ separatedTuples s .euclidean n)
    (hr : transportTuple r f ∈ separatedTuples s .euclidean n) :
    (listOf ⟨⟨n, transportTuple r f⟩, hr⟩ : SeparatedTuples.SepTuple) =
      SeparatedTuples.push r (listOf ⟨⟨n, f⟩, hf⟩) := by
  have hsep : SeparatedTuples.IsDisjointlySupported
      (SeparatedTuples.pushList r (listOf (⟨⟨n, f⟩, hf⟩ : FinTuple s)).1) :=
    Eq.mp (congrArg SeparatedTuples.IsDisjointlySupported (ofFn_transportTuple r f))
      ((mem_separatedTuples_iff_ofFn _).1 hr)
  unfold SeparatedTuples.push
  rw [dif_pos hsep]
  exact Subtype.ext (ofFn_transportTuple r f)
variable (s) in
def shiftEquiv (v : Fin 4 → ℝ) : Pt s .euclidean ≃ Pt s .euclidean :=
  (Equiv.addRight v : (Fin 4 → ℝ) ≃ (Fin 4 → ℝ))
theorem isDistIsometry_shiftEquiv (v : Fin 4 → ℝ) : IsDistIsometry (shiftEquiv s v) :=
  (isDistIsometry_iff _).2 (SeparatedTuples.isEuclidIsometry_translate v)
theorem mem_spanIn_iff (O : Set (Fin 4 → ℝ)) (F : SeparatedTuples.FormalSpan) :
    F ∈ SeparatedTuples.spanIn O ↔
      ∀ X ∈ F.support, X ∈ SeparatedTuples.supportedIn O := by
  have h : SeparatedTuples.spanIn O =
      Finsupp.supported ℂ ℂ (SeparatedTuples.supportedIn O) := by
    rw [Finsupp.supported_eq_span_single, SeparatedTuples.spanIn]
    congr 1
    ext G
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨X.1, X.2, rfl⟩
    · rintro ⟨X, hX, rfl⟩
      exact ⟨⟨X, hX⟩, rfl⟩
  rw [h, Finsupp.mem_supported]
  exact Iff.rfl
def FormalMulDefined (F F' : SeparatedTuples.FormalSpan) : Prop :=
  ∀ X ∈ F.support, ∀ Y ∈ F'.support, SeparatedTuples.SepTuple.Composable X Y
theorem formalMulDefined_of_mem {O O' : Set (Fin 4 → ℝ)} (hO : Disjoint O O')
    {F F' : SeparatedTuples.FormalSpan} (hF : F ∈ SeparatedTuples.spanIn O)
    (hF' : F' ∈ SeparatedTuples.spanIn O') : FormalMulDefined F F' :=
  fun X hX Y hY => SeparatedTuples.composable_of_mem_supportedIn hO
    ((mem_spanIn_iff O F).1 hF X hX) ((mem_spanIn_iff O' F').1 hF' Y hY)
theorem exists_isOpen_of_formalMulDefined {F F' : SeparatedTuples.FormalSpan}
    (h : FormalMulDefined F F') :
    ∃ O O' : Set (Fin 4 → ℝ), IsOpen O ∧ IsOpen O' ∧ Disjoint O O' ∧
      F ∈ SeparatedTuples.spanIn O ∧ F' ∈ SeparatedTuples.spanIn O' := by
  have hcompact : ∀ G : SeparatedTuples.FormalSpan,
      IsCompact (⋃ X ∈ G.support, ⋃ f ∈ X.1, tsupport f) := fun G =>
    G.support.isCompact_biUnion fun X _ =>
      (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
  have hdisj : Disjoint (⋃ X ∈ F.support, ⋃ f ∈ X.1, tsupport f)
      (⋃ Y ∈ F'.support, ⋃ g ∈ Y.1, tsupport g) := by
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [Set.mem_iUnion] at hx hx'
    obtain ⟨X, hX, f, hf, hxf⟩ := hx
    obtain ⟨Y, hY, g, hg, hxg⟩ := hx'
    exact Set.disjoint_left.1 (h X hX Y hY f hf g hg) hxf hxg
  obtain ⟨O, O', hO, hO', hsub, hsub', hOO'⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hcompact F) (hcompact F') hdisj
  refine ⟨O, O', hO, hO', hOO', (mem_spanIn_iff O F).2 fun X hX f hf => ?_,
    (mem_spanIn_iff O' F').2 fun X hX f hf => ?_⟩
  · exact (Set.subset_biUnion_of_mem (u := fun X : SeparatedTuples.SepTuple => ⋃ f ∈ X.1, tsupport f)
      (Finset.mem_coe.2 hX)).trans' (Set.subset_biUnion_of_mem
        (u := fun f : SeparatedTuples.RealValued => tsupport f) hf) |>.trans hsub
  · exact (Set.subset_biUnion_of_mem (u := fun X : SeparatedTuples.SepTuple => ⋃ f ∈ X.1, tsupport f)
      (Finset.mem_coe.2 hX)).trans' (Set.subset_biUnion_of_mem
        (u := fun f : SeparatedTuples.RealValued => tsupport f) hf) |>.trans hsub'
theorem formalMul_mem {O O' : Set (Fin 4 → ℝ)} (hO : Disjoint O O')
    {F F' : SeparatedTuples.FormalSpan} (hF : F ∈ SeparatedTuples.spanIn O)
    (hF' : F' ∈ SeparatedTuples.spanIn O') :
    SeparatedTuples.formalMul F F' ∈ SeparatedTuples.spanIn (O ∪ O') := by
  have hbasis : ∀ (X : SeparatedTuples.supportedIn O) (Y : SeparatedTuples.supportedIn O'),
      SeparatedTuples.formalMul (SeparatedTuples.basisVec X.1)
        (SeparatedTuples.basisVec Y.1) ∈ SeparatedTuples.spanIn (O ∪ O') := by
    intro X Y
    have hdef := SeparatedTuples.composable_of_mem_supportedIn hO X.2 Y.2
    have hmem : SeparatedTuples.SepTuple.juxt X.1 Y.1 ∈ SeparatedTuples.supportedIn (O ∪ O') := by
      intro f hf
      rw [SeparatedTuples.SepTuple.juxt_val hdef] at hf
      rcases List.mem_append.1 hf with hf | hf
      · exact (X.2 f hf).trans Set.subset_union_left
      · exact (Y.2 f hf).trans Set.subset_union_right
    rw [SeparatedTuples.formalMul_basisVec]
    exact Submodule.subset_span ⟨⟨_, hmem⟩, rfl⟩
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, rfl⟩ := hG
    induction hF' using Submodule.span_induction with
    | mem G' hG' =>
      obtain ⟨Y, rfl⟩ := hG'
      exact hbasis X Y
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ c ha
section Extension
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
def spanLift (Ψ : FinTuple s → V) : SeparatedTuples.FormalSpan →ₗ[ℂ] V :=
  SeparatedTuples.linearExtend fun X => Ψ ((finTupleEquiv s).symm X)
end Extension
def realSpanLift (Ψ : FinTuple s → ℝ) : SeparatedTuples.FormalSpan →ₗ[ℂ] ℂ :=
  spanLift fun X => (Ψ X : ℂ)
def toTupleFunctional (σ : FinTuple s → ℝ) (hσ : IsTupleFunctional σ) :
    SeparatedTuples.TupleFunctional where
  toFun X := σ ((finTupleEquiv s).symm X)
  map_nil := by
    have h : (finTupleEquiv s).symm SeparatedTuples.SepTuple.nil =
        (⟨nilTuple s .euclidean, nilTuple_mem_allSeparatedTuples⟩ : FinTuple s) :=
      (Equiv.symm_apply_eq _).2 listOf_nilTuple.symm
    rw [h]
    exact hσ.1
theorem spanExtension_toTupleFunctional (σ : FinTuple s → ℝ)
    (hσ : IsTupleFunctional σ) :
    (toTupleFunctional σ hσ).spanExtension = realSpanLift σ :=
  rfl
end YangMills.Construction.R4TupleForms
