import YangMills.Construction.LimitsOfTwoKinds.WhatTheSettingNamesIsFormed
import YangMills.Construction.ToriAtArbitraryCouplings.BoundedFormsAlongABoundedSequenceProof
import YangMills.Construction.ToriAtArbitraryCouplings.ExtractionOfLimitsFromABoundedSequence
import YangMills.Construction.Torus.MultilinearFormsOnSeparatedTuplesAsDistributions
import YangMills.Construction.Torus.MultilinearOnSeparatedTuplesSaidByProducts
import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TotalDensitiesGiveASystem.ListOfALimitOnATorus
import YangMills.Construction.TotalDensitiesGiveASystem.SymmetriesOfALimitOfABoundedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set AmbientPoints AmbientPoints.AmbientMirror ToriAtArbitraryCouplings
open scoped Topology ENNReal ContDiff
open ReflectionPositivity.AxisMirror (Ambient CoordMirror)
namespace TotalDensities
namespace TorusLimit
variable {s : Conventions.StandingParameters}
abbrev torusSideOf (s : Conventions.StandingParameters) : TorusSide := TorusSide.ofStandingParameters s
abbrev unitCutoff (s : Conventions.StandingParameters) : Conventions.StandingParameters :=
  (torusSideOf s).asMirrorData.toStandingParameters
def tupleToList {n : ℕ} (f : Fin n → Pt s .torus → ℝ) : (torusSideOf s).FnTuple .torus :=
  List.ofFn (f : Fin n → (torusSideOf s).Point .torus → ℝ)
theorem closedSupport_eq_tsupport (g : Pt s .torus → ℝ) :
    (torusSideOf s).closedSupport .torus (g : (torusSideOf s).Point .torus → ℝ) = tsupport g :=
  (closure_eq_closureWrt (Function.support g)).symm
theorem mem_separatedTuples_iff_list (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts) {n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → Pt s .torus → ℝ) :
    f ∈ separatedTuples s .torus n ↔ tupleToList f ∈ (torusSideOf s).sepOfLength .torus n := by
  have h := (hT (unitCutoff s)).2.2.2.2.2.2.1 n hn
  have hB := h.2.1
  have hC := h.2.2 1 one_pos
  constructor
  · intro hf
    have h1 : TorusLipschitzTuples.componentList (unitCutoff s) f ∈
        ReflectionPositivity.TorusTuples.disjointC1Tuples (unitCutoff s) n := by
      rw [hB]
      exact ⟨f, hf, rfl⟩
    rw [hC] at h1
    exact h1
  · intro hf
    have h1 : TorusLipschitzTuples.componentList (unitCutoff s) f ∈
        ReflectionPositivity.TorusTuples.disjointC1Tuples (unitCutoff s) n := by
      rw [hC]
      exact hf
    rw [hB] at h1
    obtain ⟨g, hg, e⟩ := h1
    have e' : g = f := List.ofFn_injective e
    exact e' ▸ hg
theorem sepTuples_eq_separatedTuples (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts) {n : ℕ} (hn : 1 ≤ n) :
    sepTuples s .torus n = separatedTuples s .torus n := by
  have h := (hT (unitCutoff s)).2.2.2.2.2.2.1 n hn
  exact Set.image_injective.2 (fun a b e => List.ofFn_injective e) (h.1.symm.trans h.2.1)
theorem exists_eq_ofFn {α : Type*} (Y : List α) {n : ℕ} (h : Y.length = n) :
    ∃ f : Fin n → α, Y = List.ofFn f := by
  subst h
  exact ⟨Y.get, (List.ofFn_get Y).symm⟩
theorem supportGap_tupleToList {n : ℕ} (f : Fin n → Pt s .torus → ℝ) :
    (torusSideOf s).gapAllLengths .torus (tupleToList f) = supportGap f := by
  refine ((torusSideOf s).gapAllLengths_eq_supportGap .torus _).trans
    (((torusSideOf s).supportGap_ofFn .torus f).trans ?_)
  refine iInf_congr fun i => iInf_congr fun k => iInf_congr fun _ => ?_
  exact congrArg₂ (fun A B => (torusSideOf s).setDist .torus A B) (closedSupport_eq_tsupport (f i))
    (closedSupport_eq_tsupport (f k))
theorem sharpNormProduct_ofFn (t : TorusSide) (m' : ℕ) {n : ℕ} (f : Fin n → t.Point .torus → ℝ) :
    t.sharpNormProduct m' .torus (List.ofFn f) = ∏ i, t.sharpNormAt m' .torus (f i) := by
  unfold TorusSide.sharpNormProduct
  rw [List.map_ofFn, List.prod_ofFn]
  rfl
theorem sharpNormProduct_tupleToList (m' : ℕ) {n : ℕ} (f : Fin n → Pt s .torus → ℝ) :
    (torusSideOf s).sharpNormProduct m' .torus (tupleToList f) =
      ∏ i, (torusSideOf s).sharpNormAt m' .torus (f i : (torusSideOf s).Point .torus → ℝ) :=
  sharpNormProduct_ofFn (torusSideOf s) m' f
theorem sharpNorm_nonneg (t : TorusSide) (m' : ℕ) (f : t.Point .torus → ℝ) :
    0 ≤ t.sharpNormAt m' .torus f := by
  rw [t.sharpNormAt_eq]
  exact le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem connectedFunction_ofFn_get (L m c : ℕ) (b : ℂ) {n : ℕ} (f : Fin n → PeriodicLattice.FourTorus L m → ℝ) :
    PeriodicLattice.connectedFunction L m c b (List.ofFn f).get =
      PeriodicLattice.connectedFunction L m c b f := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.BoundedMultilinearForms.connectedFunction_get_ofFn <;> assumption
theorem isBoundedOnTorus_of_abs_le {L m : ℕ} {f : PeriodicLattice.FourTorus L m → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : ConnectedFunctionExpansion.IsBoundedOnTorus f :=
  ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C))
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (hC y))
theorem connectedFunctionAt_tupleToList
    (hCent : OneCutoffCumulants.Statement)
    (hL : 8 * 105 ^ 4 ≤ s.L) {n : ℕ} (hn : 1 ≤ n) (K : ℕ+) {β : ℝ} (hβ : 0 < β)
    (f : Fin n → Pt s .torus → ℝ)
    (hb : ∀ i, ConnectedFunctionExpansion.IsBoundedOnTorus
      (f i : PeriodicLattice.FourTorus s.L s.m → ℝ)) :
    (torusSideOf s).cumulantAt K β (tupleToList f) =
      SchwingerFunctions.connectedSchwinger s.L s.m K β f := by
  have h := (hCent ⟨⟨s.L, s.isAdmissible, K, s.m⟩, β, hβ⟩ hL).1.1 n hn f hb
  exact (connectedFunction_ofFn_get _ _ _ _ f).trans h
theorem instTopology_eq_metric (s : Conventions.StandingParameters) :
    (inferInstance : TopologicalSpace (Pt s .torus)) =
      (inferInstance : TopologicalSpace
        (TorusMetric.Torus4 (PeriodicLattice.torusSide s.L s.m))) := by
  rw [← TorusAnalysis.euclidTopology_eq_instTopology]
  refine TopologicalSpace.ext (funext fun (U : Set
    (TorusMetric.Torus4 (PeriodicLattice.torusSide s.L s.m))) => propext ?_)
  change @IsOpen (Pt s .torus) _ U ↔
    (∀ y ∈ U, ∃ r > 0, ∀ y', TorusMetric.torusEuclidNorm (y' - y) < r → y' ∈ U)
  exact @Metric.isOpen_iff (Pt s .torus) _ U
theorem tsupport_metric_eq (f : Pt s .torus → ℝ) :
    @tsupport _ _ _ (inferInstance : TopologicalSpace
      (TorusMetric.Torus4 (PeriodicLattice.torusSide s.L s.m))) f = tsupport f :=
  (congrArg (fun τ => @tsupport _ _ _ τ f) (instTopology_eq_metric s)).symm
theorem mem_sepLipTuples_of_list {n : ℕ} {f : Fin n → Pt s .torus → ℝ}
    (h : tupleToList f ∈ (torusSideOf s).lipDisjointOfLength .torus n) :
    f ∈ sepLipTuples s .torus n := by
  obtain ⟨hl, hc, hd⟩ := ((torusSideOf s).ofFn_mem_lipDisjointOfLength_iff .torus f).1 h
  refine ⟨hl, fun i => ?_, fun i k hik => ?_⟩
  · have h1 := hc i
    rw [closedSupport_eq_tsupport] at h1
    exact (isCompact_iff_isCompactWrt _).2 h1
  · have h1 := hd i k hik
    rw [closedSupport_eq_tsupport, closedSupport_eq_tsupport] at h1
    exact h1
theorem isBoundedOnTorus_of_mem_sepLipTuples (hForm : LimitsOfTwoKinds.SettingWellDefined.Statement) {n : ℕ}
    {f : Fin n → Pt s .torus → ℝ} (hf : f ∈ sepLipTuples s .torus n) (i : Fin n) :
    ConnectedFunctionExpansion.IsBoundedOnTorus
      (f i : PeriodicLattice.FourTorus s.L s.m → ℝ) := by
  obtain ⟨C, hC⟩ := (hForm.2 s .torus).1.bounded_of_lipschitz_torus (f i) (hf.1 i)
  exact isBoundedOnTorus_of_abs_le hC
def mapFamilyOf (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    (F : Ambient.ConnectedFamily (torusSideOf s).asMirrorData .torus) : TupleMapFamily s .torus :=
  fun n hn Y => F.fn n hn ⟨tupleToList Y.1, (mem_separatedTuples_iff_list hT (by omega) Y.1).1 Y.2⟩
theorem mem_compactC1SuppIn (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    {A : Set (Pt s .torus)} {g : Pt s .torus → ℝ} (hg : g ∈ c1CompactlySupportedIn A) :
    (g : (torusSideOf s).Point .torus → ℝ) ∈
      Ambient.compactC1SuppIn (torusSideOf s).asMirrorData .torus A := by
  have h1 : (fun _ : Fin 1 => g) ∈ separatedTuples s .torus 1 :=
    ⟨fun _ => ⟨hg.1, hg.2.1⟩, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  have h2 := (mem_separatedTuples_iff_list hT le_rfl _).1 h1
  refine ⟨h2.2.1 g ((List.mem_ofFn' _ _).2 ⟨0, rfl⟩), ?_⟩
  exact (closedSupport_eq_tsupport g).trans_subset hg.2.2
theorem update_update_same {n : ℕ} {α : Type} (G : Fin n → α) (i : Fin n) (a b : α) :
    Function.update (Function.update G i a) i b = Function.update G i b :=
  Function.update_idem _ _ _
theorem update_apply_same {n : ℕ} {α : Type} (G : Fin n → α) (i : Fin n) (a : α) :
    Function.update G i a i = a :=
  Function.update_self _ _ _
def entryFns {n : ℕ} {A : Fin n → Set (Pt s .torus)}
    (m : (i : Fin n) → c1Submodule (A i)) : Fin n → (torusSideOf s).Point .torus → ℝ :=
  fun k => (m k).1
theorem isTupleMultilinear_of_list (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts) {n : ℕ} (hn : 1 ≤ n)
    (Ψ : (torusSideOf s).sepOfLength .torus n → ℝ)
    (hΨ : Ambient.IsSeparatedMultilinear (torusSideOf s).asMirrorData .torus Ψ) :
    IsTupleMultilinear (fun Y : separatedTuples s .torus n =>
      Ψ ⟨tupleToList Y.1, (mem_separatedTuples_iff_list hT hn Y.1).1 Y.2⟩) := by
  intro A hA
  have hA' : Pairwise fun i j =>
      0 < Ambient.setDist (torusSideOf s).asMirrorData .torus (A i) (A j) := fun i j hij =>
    pos_iff_ne_zero.2 (hA hij)
  let toFun : ((i : Fin n) → c1Submodule (A i)) → ℝ := fun g =>
    Ψ ⟨tupleToList fun i => (g i).1, (mem_separatedTuples_iff_list hT hn _).1
      (mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2)⟩
  have hval : ∀ (g : (i : Fin n) → c1Submodule (A i))
      (h : Fin n → (torusSideOf s).Point .torus → ℝ), (fun i => (g i).1) = h →
      toFun g = Ambient.evalOrZero Ψ (List.ofFn h) := by
    intro g h e
    subst e
    have hm : List.ofFn (fun i => (g i).1) ∈ (torusSideOf s).sepOfLength .torus n :=
      (mem_separatedTuples_iff_list hT hn _).1
        (mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2)
    have e : Ambient.evalOrZero Ψ (List.ofFn fun i => (g i).1) = Ψ ⟨_, hm⟩ := dif_pos hm
    exact e.symm
  have hsup : ∀ (g : (i : Fin n) → c1Submodule (A i)) (i : Fin n),
      (g i).1 ∈ Ambient.compactC1SuppIn (torusSideOf s).asMirrorData .torus (A i) :=
    fun g i => mem_compactC1SuppIn hT (g i).2
  have hu : ∀ (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (z : c1Submodule (A i)),
      (fun k => (Function.update m i z k).1) =
        Function.update (entryFns m) i z.1 := by
    intro m i z
    funext k
    by_cases hk : k = i
    · subst hk
      exact (congrArg Subtype.val (Function.update_self k z m)).trans
        (Function.update_self k z.1 (entryFns m)).symm
    · exact (congrArg Subtype.val (Function.update_of_ne hk z m)).trans
        (Function.update_of_ne hk z.1 (entryFns m)).symm
  have hs : ∀ (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (z : c1Submodule (A i)) (k : Fin n),
      Function.update (entryFns m) i z.1 k ∈
        Ambient.compactC1SuppIn (torusSideOf s).asMirrorData .torus (A k) :=
    fun m i z k => congrFun (hu m i z) k ▸ hsup (Function.update m i z) k
  refine ⟨{ toFun := toFun, map_update_add' := ?_, map_update_smul' := ?_ }, fun g => rfl⟩
  · intro inst m i x y
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    have h := hΨ A hA' _ (hs m i x) i y.1 (mem_compactC1SuppIn hT y.2) 1 1
    have e2 := update_update_same (entryFns m) i x.1 y.1
    rw [hval _ _ (hu m i (x + y)), hval _ _ (hu m i x), hval _ _ (hu m i y)]
    refine (congrArg (fun Z : Fin n → (torusSideOf s).Point .torus → ℝ =>
        Ambient.evalOrZero Ψ (List.ofFn Z))
      ((update_update_same (entryFns m) i x.1 _).trans (congrArg (Function.update (entryFns m) i)
        (funext fun p => ?_)))).symm.trans (h.trans ?_)
    · have hx := congrFun (update_apply_same (entryFns m) i x.1) p
      exact (congrArg₂ (fun u v : ℝ => (1 : ℝ) * u + (1 : ℝ) * v) hx rfl).trans
        (by show (1 : ℝ) * x.1 p + (1 : ℝ) * y.1 p = x.1 p + y.1 p; ring)
    · rw [one_mul, one_mul]
      exact congrArg₂ (· + ·) rfl
        (congrArg (fun Z : Fin n → (torusSideOf s).Point .torus → ℝ =>
          Ambient.evalOrZero Ψ (List.ofFn Z)) e2)
  · intro inst m i c x
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    have h := hΨ A hA' _ (hs m i x) i x.1 (mem_compactC1SuppIn hT x.2) c 0
    rw [hval _ _ (hu m i (c • x)), hval _ _ (hu m i x)]
    refine (congrArg (fun Z : Fin n → (torusSideOf s).Point .torus → ℝ =>
        Ambient.evalOrZero Ψ (List.ofFn Z))
      ((update_update_same (entryFns m) i x.1 _).trans (congrArg (Function.update (entryFns m) i)
        (funext fun p => ?_)))).symm.trans (h.trans ?_)
    · have hx := congrFun (update_apply_same (entryFns m) i x.1) p
      exact (congrArg₂ (fun u v : ℝ => c * u + (0 : ℝ) * v) hx rfl).trans
        (by show c * x.1 p + (0 : ℝ) * x.1 p = c * x.1 p; ring)
    · rw [zero_mul, add_zero]
      rfl
section FamilyOfAConnectedFamily
variable (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts)
  (F : Ambient.ConnectedFamily (torusSideOf s).asMirrorData .torus)
include hT in
theorem isTupleMultilinear_mapFamilyOf (n : ℕ) (hn : 2 ≤ n) : IsTupleMultilinear (mapFamilyOf hT F n hn) :=
  isTupleMultilinear_of_list hT (by omega) (F.fn n hn) (F.fn_multilinear n hn)
theorem isTupleSymmetric_mapFamilyOf (hsym : (torusSideOf s).IsPermInvariantFamily .torus F) (n : ℕ)
    (hn : 2 ≤ n) : IsTupleSymmetric (mapFamilyOf hT F n hn) := by
  intro Y ς
  exact hsym n hn Y.1 ς ((mem_separatedTuples_iff_list hT (by omega) Y.1).1 Y.2) _
theorem isInvariantOnLength_mapFamilyOf (r : Pt s .torus ≃ Pt s .torus)
    (hr : (torusSideOf s).CumulantsInvariantUnder F r) (n : ℕ) (hn : 2 ≤ n) :
    TorusSymmetries.IsInvariantOnLength r (mapFamilyOf hT F n hn) := by
  intro Y
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h, e⟩ := hr n hn ⟨tupleToList Y.1, (mem_separatedTuples_iff_list hT hn1 Y.1).1 Y.2⟩
  have hl : ReflectionPositivity.TorusTuples.transportTuple
      (s := unitCutoff s) r (tupleToList Y.1) =
      tupleToList (transportTuple r Y.1) := by
    unfold ReflectionPositivity.TorusTuples.transportTuple tupleToList
    exact List.map_ofFn
  have h' : transportTuple r Y.1 ∈ separatedTuples s .torus n :=
    (mem_separatedTuples_iff_list hT hn1 _).2 (hl ▸ h)
  refine ⟨h', ?_⟩
  refine Eq.trans ?_ e
  exact congrArg (F.fn n hn) (Subtype.ext hl.symm)
end FamilyOfAConnectedFamily
theorem tupleToList_mem_separatedAll (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts) {n : ℕ}
    {f : Fin n → Pt s .torus → ℝ} (hf : f ∈ separatedTuples s .torus n) :
    tupleToList f ∈ Ambient.separatedAll (torusSideOf s).asMirrorData .torus := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · refine Ambient.separatedN_subset_separatedAll _ _ 0 ?_
    rw [Ambient.separatedN_zero]
    rfl
  · exact Ambient.separatedN_subset_separatedAll _ _ n ((mem_separatedTuples_iff_list hT h f).1 hf)
def listToTuple (Y : (torusSideOf s).FnTuple .torus) : FunctionTuple s .torus :=
  ⟨Y.length, (Y.get : Fin Y.length → Pt s .torus → ℝ)⟩
theorem heq_ofFn_get {α : Type*} {n : ℕ} (f : Fin n → α) : HEq f (List.ofFn f).get :=
  (Fin.heq_fun_iff (List.length_ofFn).symm).2 fun i => by simp
theorem eq_listToTuple {n : ℕ} (f : Fin n → Pt s .torus → ℝ) :
    (⟨n, f⟩ : FunctionTuple s .torus) = listToTuple (tupleToList f) :=
  Sigma.ext (List.length_ofFn).symm (heq_ofFn_get f)
theorem evalOrZero_of_mem {D : ReflectionPositivity.AxisMirror.MirrorData} {E : Ambient}
    {A : Set (Ambient.FnList D E)} (φ : A → ℝ) {X : Ambient.FnList D E} (h : X ∈ A) :
    Ambient.evalOrZero φ X = φ ⟨X, h⟩ :=
  dif_pos h
theorem ofFn_append_eq_map_append {α : Type*} {m n : ℕ} (a : Fin m → α) (g : α → α) (a' : Fin m → α)
    (b : Fin n → α) (h : a' = g ∘ a) :
    List.ofFn (Fin.append a' b) = (List.ofFn a).map g ++ List.ofFn b := by
  subst h
  rw [List.ofFn_fin_append, List.map_ofFn]
theorem tupleToList_reflectAppend (M : AmbientMirror .torus)
    (A B : AmbientMirror.separatedIn (s := s) (AmbientMirror.positiveSide s .torus M)) :
    tupleToList (AmbientMirror.reflectAppend s .torus M A B).1.2 =
      CoordMirror.reflectAppend (torusSideOf s).asMirrorData M .torus
        (tupleToList A.1.2) (tupleToList B.1.2) := by
  refine ofFn_append_eq_map_append (α := (torusSideOf s).Point .torus → ℝ) A.1.2
    (CoordMirror.pullback (torusSideOf s).asMirrorData M .torus) _ B.1.2 (funext fun i => ?_)
  refine (AmbientMirror.transportTuple_reflect s .torus M A.1.2 i).trans ?_
  exact congrArg ((A.1.2 i) ∘ ·) (AmbientMirror.reflect_torus (torusSideOf s).asMirrorData M)
section CentredFunctionalOfAConnectedFamily
variable (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts)
  (F : Ambient.ConnectedFamily (torusSideOf s).asMirrorData .torus)
theorem centredOfMaps_listToTuple (Y : (torusSideOf s).FnTuple .torus)
    (hY : Y ∈ Ambient.separatedAll (torusSideOf s).asMirrorData .torus)
    (hg : listToTuple Y ∈ allSeparatedTuples s .torus) :
    centredOfMaps (mapFamilyOf hT F) ⟨listToTuple Y, hg⟩ = F.centeredFunctional ⟨Y, hY⟩ := by
  show ∑ π ∈ SetPartition.singletonFree Y.length, ∏ J ∈ π.parts,
      mapFamilyBlockFactor (mapFamilyOf hT F) ⟨(listToTuple Y).2, hg⟩ J =
    ∑ π ∈ SetPartition.nonSingletonPartitions Y.length, ∏ J ∈ π.parts,
      F.evalAt J.card (Ambient.subList Y J)
  rw [← SetPartition.atLeastTwoPartitions_univ,
    ← SetPartition.nonSingletonPartitions_eq_atLeastTwoPartitions]
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  by_cases h : 2 ≤ J.card
  · have hm : Ambient.subList Y J ∈ (torusSideOf s).sepOfLength .torus J.card :=
      (mem_separatedTuples_iff_list hT (by omega) _).1 (restrictTuple_mem hg J)
    exact (dif_pos h).trans (F.evalAt_of_mem h hm).symm
  · have e : F.evalAt J.card (Ambient.subList Y J) = 0 := by
      unfold Ambient.ConnectedFamily.evalAt
      exact dif_neg h
    exact (dif_neg h).trans e.symm
theorem centredOfMaps_mapFamilyOf (Z : allSeparatedTuples s .torus) :
    centredOfMaps (mapFamilyOf hT F) Z =
      F.centeredFunctional ⟨tupleToList Z.1.2, tupleToList_mem_separatedAll hT Z.2⟩ := by
  obtain ⟨⟨n, f⟩, hf⟩ := Z
  have key : ∀ (T : FunctionTuple s .torus) (hT' : T ∈ allSeparatedTuples s .torus),
      T = listToTuple (tupleToList f) →
      centredOfMaps (mapFamilyOf hT F) ⟨T, hT'⟩ =
        F.centeredFunctional ⟨tupleToList f, tupleToList_mem_separatedAll hT hf⟩ := by
    rintro _ hT' rfl
    exact centredOfMaps_listToTuple hT F _ _ hT'
  exact key _ hf (eq_listToTuple f)
theorem isReflectionPositive_mapFamilyOf (M : AmbientMirror .torus)
    (h : CoordMirror.IsReflectionPositiveFor (torusSideOf s).asMirrorData M .torus F.centeredFunctional) :
    AmbientMirror.IsReflectionPositive s .torus M (centredOfMaps (mapFamilyOf hT F)) := by
  intro r Xs c
  have hL : ∀ i, tupleToList (Xs i).1.2 ∈ Ambient.separatedWithin (torusSideOf s).asMirrorData .torus
      (CoordMirror.upperSide (torusSideOf s).asMirrorData M .torus) := by
    intro i
    refine ⟨tupleToList_mem_separatedAll hT (Xs i).2.1, fun f hf => ?_⟩
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    have h1 := (Xs i).2.2 k
    have e := AmbientMirror.positiveSide_torus (torusSideOf s).asMirrorData M
    exact (closedSupport_eq_tsupport _).trans_subset (h1.trans e.subset)
  have key : ∀ i j, centredOfMaps (mapFamilyOf hT F)
      (AmbientMirror.reflectAppend s .torus M (Xs i) (Xs j)) =
      Ambient.evalOrZero F.centeredFunctional
        (CoordMirror.reflectAppend (torusSideOf s).asMirrorData M .torus
          (tupleToList (Xs i).1.2) (tupleToList (Xs j).1.2)) := by
    intro i j
    rw [centredOfMaps_mapFamilyOf hT F, ← tupleToList_reflectAppend M (Xs i) (Xs j)]
    exact (evalOrZero_of_mem _ _).symm
  have e : AmbientMirror.gramSum s .torus M (centredOfMaps (mapFamilyOf hT F)) Xs c =
      CoordMirror.reflectedGramSum (torusSideOf s).asMirrorData M .torus F.centeredFunctional
        (fun i => tupleToList (Xs i).1.2) c := by
    unfold AmbientMirror.gramSum CoordMirror.reflectedGramSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [key]
  rw [e]
  exact h r _ hL c
end CentredFunctionalOfAConnectedFamily
theorem continuousPartialsUpTo_univ_iff (p : ℕ+) (ν : ℕ) (G : (Fin (4 * (p : ℕ)) → ℝ) → ℂ) :
    ContinuousPartialsUpTo univ ν G ↔
      PeriodicSpace.Coords.ContPartialsUpTo (p := p) ν G := by
  induction ν generalizing G with
  | zero => exact continuousOn_univ
  | succ ν ih =>
    refine and_congr continuousOn_univ (forall_congr' fun j => and_congr ?_ (ih _))
    simp
abbrev liftToCoords (f : Pt s .torus → ℝ) : (Fin (4 * 1) → ℝ) → ℂ :=
  asFunctionOnOnePoint f ∘ tupleProj s .torus 1
section SmoothFunctionsOfOnePoint
variable (hCD : PeriodicSpace.ContPartialsIffContDiff)
include hCD in
theorem isSmoothFn_of_isSmoothReal {f : Pt s .torus → ℝ} (h : IsSmoothReal f) :
    IsSmoothFn (asFunctionOnOnePoint f) := by
  have hL : ContDiff ℝ ∞ (fun x : Fin (4 * 1) → ℝ => (flattenCoords 1).symm x 0) :=
    contDiff_pi.2 fun μ => contDiff_apply ℝ ℝ _
  have hH : ContDiff ℝ ∞ (liftToCoords f) := Complex.ofRealCLM.contDiff.comp (h.comp hL)
  refine ⟨isOpen_univ, fun n _ => ?_⟩
  exact (continuousPartialsUpTo_univ_iff 1 n _).2 ((hCD 1 n _).2 (hH.of_le (by exact_mod_cast le_top)))
include hCD in
theorem isSmoothReal_of_isSmoothFn {f : Pt s .torus → ℝ} (h : IsSmoothFn (asFunctionOnOnePoint f)) :
    IsSmoothReal f := by
  have hH : ContDiff ℝ ∞ (liftToCoords f) :=
    contDiff_infty.2 fun n => (hCD 1 n _).1 ((continuousPartialsUpTo_univ_iff 1 n _).1 (h.2 n le_top))
  have hι : ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => flattenCoords 1 fun _ => x) :=
    contDiff_pi.2 fun j => contDiff_apply ℝ ℝ _
  have e : f ∘ proj s .torus = fun x => (liftToCoords f (flattenCoords 1 fun _ => x)).re := by
    funext x
    simp only [liftToCoords, Function.comp_apply, asFunctionOnOnePoint]
    rw [tupleProj_flattenCoords]
    simp
  show ContDiff ℝ ∞ (f ∘ proj s .torus)
  rw [e]
  exact Complex.reCLM.contDiff.comp (hH.comp hι)
end SmoothFunctionsOfOnePoint
theorem hasOrderLEOn_of_subset {n ν : ℕ} {W W' : Set (Tuple s .torus n)} (h : W' ⊆ W)
    {u : testFns W → ℂ} (hu : HasOrderLE ν u) : HasOrderLEOn ν h u := by
  have hserve : ∀ K, IsCompact K → K ⊆ W' → OrderBoundsOn (restrictDistrib h u) K ν := by
    intro K hK hs
    obtain ⟨C, hC⟩ := hu.2 K hK (hs.trans h)
    exact ⟨C, fun F hF => hC ⟨F.1, testFns_mono h F.2⟩ hF⟩
  exact ⟨⟨⟨fun F G H e => hu.1.1.1 ⟨F.1, testFns_mono h F.2⟩ ⟨G.1, testFns_mono h G.2⟩
      ⟨H.1, testFns_mono h H.2⟩ e,
    fun c F H e => hu.1.1.2 c ⟨F.1, testFns_mono h F.2⟩ ⟨H.1, testFns_mono h H.2⟩ e⟩,
    fun K hK hs => ⟨ν, hserve K hK hs⟩⟩, hserve⟩
theorem hasUniqueDistribOfOrder_of_bound (hCD : PeriodicSpace.ContPartialsIffContDiff)
    (hDist : MultilinearAsDistrib.Statement)
    (hProd : MultilinearOnSeparatedIffProducts)
    (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts) {n : ℕ} (hn : 2 ≤ n)
    (φ : separatedTuples s .torus n → ℝ) (hφ : IsTupleMultilinear φ) (M : Set.Ici (1 : ℝ))
    (c : ℝ → ℝ) (hc : ∀ d : ℝ, 0 < d → 0 ≤ c d)
    (hb : ∀ d : ℝ, 0 < d → ∀ Y : separatedTuples s .torus n, ENNReal.ofReal d ≤ supportGap Y.1 →
      |φ Y| ≤ c d * ∏ i, ambientSharpNorm s M .torus (Y.1 i))
    (P : Set (Pt s .torus) → Prop) :
    FamiliesOfLimits.HasUniqueDistribOfOrder P φ := by
  have hset : sepTuples s .torus n = separatedTuples s .torus n :=
    sepTuples_eq_separatedTuples hT (by omega)
  have hsub : ∀ f, f ∈ sepTuples s .torus n → f ∈ separatedTuples s .torus n :=
    fun f hf => hset ▸ hf
  have hsup : ∀ f, f ∈ separatedTuples s .torus n → f ∈ sepTuples s .torus n :=
    fun f hf => hset ▸ hf
  let Φ : TupleForm (sepTuples s .torus n) := fun f => ((φ ⟨f.1, hsub _ f.2⟩ : ℝ) : ℂ)
  have hreal : TupleForm.IsReal Φ := fun f => Complex.ofReal_im _
  have hm : AmbientPoints.IsMultilinearOnSeparated φ := (hProd s .torus n (by omega) φ).2 hφ
  have hml : TupleForm.IsMultilinear Φ := by
    intro l b b' f f' hag h
    exact hm l b b' ⟨f.1, hsub _ f.2⟩ ⟨f'.1, hsub _ f'.2⟩ hag (hsub _ h)
  obtain ⟨-, -, -, hord, hagree, huniq⟩ := hDist s .torus n hn M Φ hreal hml (fun d _ => c d)
    (fun d hd R _ _ => ⟨hc d hd, fun f _ hsep => by
      have h := hb d hd ⟨f.1, hsub _ f.2⟩ hsep
      exact (Complex.norm_real _).trans_le h⟩)
  refine ⟨formDistrib Φ, hord.1, ?_, ?_, ?_⟩
  · intro f hf hsm
    obtain ⟨hF, e⟩ := hagree ⟨f, hsup _ hf⟩ fun i => isSmoothFn_of_isSmoothReal hCD (hsm i)
    exact ⟨hF, e⟩
  · intro v hv hag
    refine huniq v hv fun f hsm => ?_
    obtain ⟨hF, e⟩ := hag f.1 (hsub _ f.2) fun i => isSmoothReal_of_isSmoothFn hCD (hsm i)
    exact ⟨hF, e⟩
  · intro O _ _ _ h
    exact hasOrderLEOn_of_subset h hord
theorem mem_sepLipTuples_of_mem (hForm : LimitsOfTwoKinds.SettingWellDefined.Statement) {n : ℕ}
    {f : Fin n → Pt s .torus → ℝ} (hf : f ∈ separatedTuples s .torus n) :
    f ∈ sepLipTuples s .torus n :=
  ⟨fun i => ((hForm.2 s .torus).1.tuple_components n f hf i).2, fun i => (hf.1 i).2,
    fun _ _ hik => hf.2 hik⟩
abbrev sharpNormOne (f : Pt s .torus → ℝ) : ℝ :=
  TestFunctions.sharpNormTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (1 : ℝ) f
theorem sharpNormAt_zero_eq (f : Pt s .torus → ℝ) :
    (torusSideOf s).sharpNormAt 0 .torus (f : (torusSideOf s).Point .torus → ℝ) = sharpNormOne f := by
  refine ((torusSideOf s).sharpNormAt_eq 0 .torus (f : (torusSideOf s).Point .torus → ℝ)).trans ?_
  have hM : ((cubeEdge (torusSideOf s).L 0 : ℕ) : ℝ) = 1 := by simp [cubeEdge]
  rw [hM]
  rfl
theorem sharpNormOne_nonneg (f : Pt s .torus → ℝ) : 0 ≤ sharpNormOne f :=
  (sharpNorm_nonneg (torusSideOf s) 0 f).trans_eq (sharpNormAt_zero_eq f)
structure IsUniformBound (s : Conventions.StandingParameters) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (n : ℕ) (d C : ℝ) :
    Prop where
  nonneg : 0 ≤ C
  bounds : ∀ (j : ℕ+), ∀ f ∈ sepLipTuples s .torus n, ENNReal.ofReal d ≤ supportGap f →
    ‖SchwingerFunctions.connectedSchwinger s.L s.m (K j) (β j) f‖ ≤
      C * ∏ i, sharpNormOne (f i)
variable {K : ℕ+ → ℕ+} {β : ℕ+ → ℝ}
theorem isUniformBound_mono {n : ℕ} {d d' C : ℝ} (h : d ≤ d') (hC : IsUniformBound s K β n d C) :
    IsUniformBound s K β n d' C :=
  ⟨hC.nonneg, fun j f hf hsep => hC.bounds j f hf ((ENNReal.ofReal_le_ofReal h).trans hsep)⟩
variable (s K β) in
def optimalBound (n : ℕ) (d : ℝ) : ℝ := sInf {C | IsUniformBound s K β n d C}
theorem bddBelow_isUniformBound (n : ℕ) (d : ℝ) : BddBelow {C | IsUniformBound s K β n d C} :=
  ⟨0, fun _ hC => hC.nonneg⟩
theorem isUniformBound_optimalBound {n : ℕ} {d : ℝ} (h : ∃ C, IsUniformBound s K β n d C) :
    IsUniformBound s K β n d (optimalBound s K β n d) := by
  obtain ⟨C₀, hC₀⟩ := h
  refine ⟨le_csInf ⟨C₀, hC₀⟩ fun _ hC => hC.nonneg, fun j f hf hsep => ?_⟩
  have hP : 0 ≤ ∏ i, sharpNormOne (f i) := Finset.prod_nonneg fun i _ => sharpNormOne_nonneg (f i)
  rcases hP.eq_or_lt with h0 | h0
  · have := hC₀.bounds j f hf hsep
    rw [← h0] at this ⊢
    simpa using this
  · rw [← div_le_iff₀ h0]
    exact le_csInf ⟨C₀, hC₀⟩ fun C hC => (div_le_iff₀ h0).2 (hC.bounds j f hf hsep)
theorem isClusterConstant_optimalBound
    (hadm : ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d → ∃ C : ℝ, IsUniformBound s K β n d C) :
    TorusSide.IsClusterConstant (optimalBound s K β) where
  nonneg n hn d hd := (isUniformBound_optimalBound (hadm n hn d hd)).nonneg
  antitoneOn n hn d hd d' hd' hdd := by
    obtain ⟨C, hC⟩ := hadm n hn d hd
    exact csInf_le_csInf (bddBelow_isUniformBound n d') ⟨C, hC⟩ fun C' hC' => isUniformBound_mono hdd hC'
theorem isBoundedSequence_optimalBound
    (hCent : OneCutoffCumulants.Statement)
    (hForm : LimitsOfTwoKinds.SettingWellDefined.Statement) (hL : 8 * 105 ^ 4 ≤ s.L)
    (hK : Tendsto K atTop atTop) (hβ : ∀ j, 0 < β j)
    (hadm : ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d → ∃ C : ℝ, IsUniformBound s K β n d C) :
    (torusSideOf s).IsUniformlyBoundedSeq 0 K β (optimalBound s K β) := by
  refine ⟨hK, hβ, isClusterConstant_optimalBound hadm, ?_⟩
  intro j n hn d hd Y hY hsep
  obtain ⟨f, rfl⟩ := exists_eq_ofFn Y hY.1
  have hf : f ∈ sepLipTuples s .torus n := mem_sepLipTuples_of_list hY
  have h := (isUniformBound_optimalBound (hadm n hn d hd)).bounds j f hf
    (hsep.trans_eq (supportGap_tupleToList f))
  have e1 := connectedFunctionAt_tupleToList hCent hL (by omega) (K j) (hβ j) f
    (isBoundedOnTorus_of_mem_sepLipTuples hForm hf)
  have e2 : (torusSideOf s).sharpNormProduct 0 .torus (tupleToList f) = ∏ i, sharpNormOne (f i) :=
    (sharpNormProduct_tupleToList _ f).trans (Finset.prod_congr rfl fun i _ => sharpNormAt_zero_eq (f i))
  show ‖(torusSideOf s).cumulantAt (K j) (β j) (tupleToList f)‖ ≤ optimalBound s K β n d *
    (torusSideOf s).sharpNormProduct 0 .torus (tupleToList f)
  rw [e1, e2]
  exact h
theorem limit_properties (hGen : LimitExtraction.Combined)
    (hSym : BoundedSequenceLimit.Claim)
    (hCent : OneCutoffCumulants.Statement)
    (hForm : LimitsOfTwoKinds.SettingWellDefined.Statement)
    (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    (hDist : MultilinearAsDistrib.Statement)
    (hProd : MultilinearOnSeparatedIffProducts)
    (hCD : PeriodicSpace.ContPartialsIffContDiff)
    (hL : 8 * 105 ^ 4 ≤ s.L) (hK : Tendsto K atTop atTop) (hβ : ∀ j, 0 < β j)
    (hadm : ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d → ∃ C : ℝ, IsUniformBound s K β n d C)
    (S : TupleMapFamily s .torus)
    (hlim : ∀ (n : ℕ) (hn : 2 ≤ n) (X : separatedTuples s .torus n),
      Tendsto (fun j => SchwingerFunctions.connectedSchwinger s.L s.m (K j) (β j) X.1)
        atTop (𝓝 ((S n hn X : ℝ) : ℂ))) :
    (∀ (n : ℕ) (hn : 2 ≤ n), IsTupleMultilinear (S n hn)) ∧
      (∀ (n : ℕ) (hn : 2 ≤ n), IsTupleSymmetric (S n hn)) ∧
      FamiliesOfLimits.IsTranslationHypercubicInvariant S ∧
      FamiliesOfLimits.TorusReflectionPositive S ∧
      ∀ (n : ℕ) (hn : 2 ≤ n), ∃! u : testFns (pairwiseDistinctTuples s .torus n) → ℂ,
        IsDistrib u ∧ FamiliesOfLimits.AgreesOnTensorProducts u (S n hn) := by
  have hseq := isBoundedSequence_optimalBound hCent hForm hL hK hβ hadm
  obtain ⟨hExt, -, hAll⟩ := hGen.1 (torusSideOf s) hL 0 K β (optimalBound s K β) hseq
  obtain ⟨J, -, hJ, ⟨S', hS'⟩, -⟩ := hExt univ infinite_univ Empty inferInstance
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
  obtain ⟨F, rfl, hsym, hbound, hequi, -, -⟩ := hAll J hJ S' hS'
  obtain ⟨hinv, hrp⟩ := hSym (torusSideOf s) hL 0 K β (optimalBound s K β) hseq J hJ F hS' hequi
  have hne : (atTop ⊓ 𝓟 J : Filter ℕ+).NeBot := by
    rw [← Filter.frequently_mem_iff_neBot, Filter.frequently_atTop]
    intro a
    obtain ⟨b, hb, hab⟩ := hJ.exists_gt a
    exact ⟨b, hab.le, hb⟩
  have hSF : S = mapFamilyOf hT F := by
    funext n hn Y
    have h1 := hS' n hn ⟨tupleToList Y.1, (mem_separatedTuples_iff_list hT (by omega) Y.1).1 Y.2⟩
    have h2 := (hlim n hn Y).mono_left (inf_le_left : atTop ⊓ 𝓟 J ≤ atTop)
    have e : ∀ j, (torusSideOf s).cumulantFnsAt (K j) (β j) n hn
        ⟨tupleToList Y.1, (mem_separatedTuples_iff_list hT (by omega) Y.1).1 Y.2⟩ =
        SchwingerFunctions.connectedSchwinger s.L s.m (K j) (β j) Y.1 := fun j =>
      connectedFunctionAt_tupleToList hCent hL (by omega) (K j) (hβ j) Y.1
        (isBoundedOnTorus_of_mem_sepLipTuples hForm (mem_sepLipTuples_of_mem hForm Y.2))
    exact Complex.ofReal_injective (tendsto_nhds_unique h2 (h1.congr e))
  subst hSF
  have hsharp : ∀ {n : ℕ} (f : Fin n → Pt s .torus → ℝ),
      (torusSideOf s).sharpNormProduct 0 .torus (tupleToList f) = ∏ i, sharpNormOne (f i) := fun f =>
    (sharpNormProduct_tupleToList _ f).trans (Finset.prod_congr rfl fun i _ => sharpNormAt_zero_eq (f i))
  have hbd : ∀ (n : ℕ) (hn : 2 ≤ n) (d : ℝ), 0 < d → ∀ Y : separatedTuples s .torus n,
      ENNReal.ofReal d ≤ supportGap Y.1 →
      |mapFamilyOf hT F n hn Y| ≤ optimalBound s K β n d * ∏ i, sharpNormOne (Y.1 i) := by
    intro n hn d hd Y hsep
    have h := hbound n hn d hd ⟨tupleToList Y.1, (mem_separatedTuples_iff_list hT (by omega) Y.1).1 Y.2⟩
      (hsep.trans_eq (supportGap_tupleToList Y.1).symm)
    rw [hsharp] at h
    exact (Complex.norm_real _).symm.trans_le h
  refine ⟨isTupleMultilinear_mapFamilyOf hT F, isTupleSymmetric_mapFamilyOf hT F hsym, ?_,
    fun M => isReflectionPositive_mapFamilyOf hT F M (hrp M).positive, ?_⟩
  · intro n hn
    refine ⟨fun v => isInvariantOnLength_mapFamilyOf hT F _ (hinv.translate v) n hn, fun r hr => ?_⟩
    obtain ⟨w, rfl⟩ := (TorusSymmetries.mem_groupOn_iff s .torus r).1 hr
    exact isInvariantOnLength_mapFamilyOf hT F _
      (hinv.signedPerm _ (TorusSymmetries.toMatrix_mem w)) n hn
  · intro n hn
    obtain ⟨u, hu, hag, huniq, -⟩ := hasUniqueDistribOfOrder_of_bound hCD hDist hProd hT hn
      (mapFamilyOf hT F n hn) (isTupleMultilinear_mapFamilyOf hT F n hn) ⟨1, Set.mem_Ici.2 le_rfl⟩
      (optimalBound s K β n) (fun d hd => (isClusterConstant_optimalBound hadm).nonneg n hn d hd)
      (fun d hd Y hsep => hbd n hn d hd Y hsep) (fun _ => True)
    exact ⟨u, ⟨hu, hag⟩, fun v hv => huniq v hv.1 hv.2⟩
theorem hasSeparatedSupportsTorus_of_le {n : ℕ} {f : Fin n → Pt s .torus → ℝ} {d : ℝ} (hd : 0 < d)
    (hsep : ENNReal.ofReal d ≤ supportGap f) :
    TestFunctions.HasSeparatedSupportsTorus
      (f : Fin n → PeriodicLattice.FourTorus s.L s.m → ℝ) d := by
  refine ⟨hd, fun i k hik => ?_⟩
  have h1 : ENNReal.ofReal d ≤ setDist s .torus (tsupport (f i)) (tsupport (f k)) :=
    hsep.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
  rw [← tsupport_metric_eq, ← tsupport_metric_eq] at h1
  exact h1
end TorusLimit
open TorusLimit
private def trivialDemands : AssignmentConstraints where
  property _ := True
  sideFloor _ := 0
  derivBoundFloor _ := 0
  rateCeiling _ := 1
  thresholdCeiling _ _ := 1
  n₀Floor _ _ _ := 0
  CsFloor _ _ _ := 0
  NFloor _ := 0
private theorem trivialDemands_satisfiable : trivialDemands.Satisfiable where
  property_eventually := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ =>
    ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ _ _ => ⟨0, fun _ _ _ _ =>
      ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  rateCeiling_pos _ := one_pos
  thresholdCeiling_pos _ _ := one_pos
theorem torusLimitsHaveProperties (hGen : LimitExtraction.Combined)
    (hSym : BoundedSequenceLimit.Claim)
    (hCent : OneCutoffCumulants.Statement)
    (hForm : LimitsOfTwoKinds.SettingWellDefined.Statement)
    (hT : TorusLipschitzTuples.TorusLipschitzTupleFacts)
    (hDist : MultilinearAsDistrib.Statement)
    (hProd : MultilinearOnSeparatedIffProducts)
    (hCD : PeriodicSpace.ContPartialsIffContDiff) :
    TorusLimitsHaveProperties := by
  refine ⟨trivialDemands, trivialDemands_satisfiable, fun T hA _ => ⟨0, fun y _ => ?_⟩⟩
  refine ⟨|2 * T.B| + 1, fun g _ hy cV Cn C _ hTB hPB s S hsL hlim => ?_⟩
  obtain ⟨K, β, hpair, hK, hconv⟩ := hlim
  have hβ : ∀ j, 0 < β j := fun j => by
    obtain ⟨-, hthr, -⟩ := hpair j
    have h2 : -(2 * T.B) ≤ |2 * T.B| := neg_le_abs _
    unfold SequencePassage.passageThreshold at hthr
    linarith
  have hL : 8 * 105 ^ 4 ≤ s.L := by
    rw [hsL]
    exact le_trans (by norm_num) hA.L_ge
  obtain ⟨L, hLs, K₀, m⟩ := s
  obtain rfl : L = (T.stepParameters y).side := hsL
  have hexp : ∀ (n : ℕ) (d : ℝ),
      0 ≤ max 0 (Cn n d) * Real.exp (n * cV * PeriodicLattice.torusSide (T.stepParameters y).side m ^ 4) :=
    fun n d => mul_nonneg (le_max_left _ _) (Real.exp_pos _).le
  have hadm : ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d → ∃ c : ℝ,
      IsUniformBound ⟨(T.stepParameters y).side, hLs, K₀, m⟩ K β n d c := by
    intro n hn d hd
    refine ⟨_, hexp n d, fun j f hf hsep => ?_⟩
    have h := hTB (K j) (β j) (hpair j) m n hn d hd f hf.1 (hasSeparatedSupportsTorus_of_le hd hsep)
    refine h.trans (mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun i _ => sharpNormOne_nonneg (f i)))
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    limit_properties hGen hSym hCent hForm hT hDist hProd hCD hL hK hβ hadm S hconv
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro n hn d hd X hsep
    have ht := (hconv n hn X).norm
    rw [Complex.norm_real, Real.norm_eq_abs] at ht
    refine le_of_tendsto' ht fun j => ?_
    exact hTB (K j) (β j) (hpair j) m n hn d hd X.1 (mem_sepLipTuples_of_mem hForm X.2).1
      (hasSeparatedSupportsTorus_of_le hd hsep)
  · intro n hn R d hR hd X hball hsep
    have ht := (hconv n hn X).norm
    rw [Complex.norm_real, Real.norm_eq_abs] at ht
    have hball' : ∀ i, ∃ x, @tsupport _ _ _ (inferInstance : TopologicalSpace
        (TorusMetric.Torus4 (PeriodicLattice.torusSide (T.stepParameters y).side m))) (X.1 i) ⊆
          TestFunctions.closedBallTorus x R := by
      intro i
      obtain ⟨x, hx⟩ := hball i
      exact ⟨x, (tsupport_metric_eq (X.1 i)).trans_subset hx⟩
    have hb := fun j => hPB.onTori (K j) (β j) (hpair j) m n hn R d hR hd X.1
      (mem_sepLipTuples_of_mem hForm X.2).1 hball' (hasSeparatedSupportsTorus_of_le hd hsep)
    exact ⟨le_of_tendsto' ht fun j => (hb j).1, le_of_tendsto' ht fun j => (hb j).2⟩
end TotalDensities
end YangMills.Construction
end
