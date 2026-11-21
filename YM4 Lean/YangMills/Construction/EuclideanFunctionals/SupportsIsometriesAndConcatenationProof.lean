import YangMills.Construction.Continuum.TraceOfARingOfPropagatorsProof
import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValueProof
import YangMills.Construction.EuclideanFunctionals.RulesForTheTensorComponentsProof
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntriesProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.TorusMetric YangMills.Construction.MetricNotions
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MotionProofs
theorem norm_le_euclidNormVec (v : R4) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : R4) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.euclidNormVec_le_two_mul_norm <;> assumption
abbrev r4Dist : R4 → R4 → ℝ := Ambient.metric defaultMirrorData Ambient.euclidean
theorem closureWrt_r4Dist_eq (Z : Set R4) : closureWrt r4Dist Z = closure Z := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.closureWrt_r4Metric_eq <;> assumption
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  closureWrt_r4Dist_eq _
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem disjointCompactPosDist : MotionRules.DisjointCompactPosDist := by apply _root_.YangMills.Construction.PropagatorRings.setDistR4_pos_of_disjoint <;> assumption
theorem continuous_motion (r : EuclidMotion) : Continuous fun x => r x :=
  (LinearMap.continuous_of_finiteDimensional r.lin).add continuous_const
theorem contDiff_motion (r : EuclidMotion) : ContDiff ℝ 1 fun x => r x :=
  (LinearMap.toContinuousLinearMap r.lin).contDiff.add contDiff_const
theorem supp_actFn {𝕜 : Type*} [RCLike 𝕜] (r : EuclidMotion) (f : R4 → 𝕜) :
    supp (r.actFn f) = r '' supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.supp_actFn <;> assumption
theorem actFn_mem_C1c {𝕜 : Type*} [RCLike 𝕜] (r : EuclidMotion) {f : R4 → 𝕜}
    (hf : f ∈ C1c 𝕜) : r.actFn f ∈ C1c 𝕜 := by
  rw [mem_C1c_iff] at hf ⊢
  refine ⟨hf.1.comp (contDiff_motion r⁻¹), ?_⟩
  have hs := supp_actFn r f
  rw [supp_eq_tsupport, supp_eq_tsupport] at hs
  unfold HasCompactSupport
  rw [hs]
  exact IsCompact.image hf.2 (continuous_motion r)
theorem actFn_mul {α : Type*} (r r' : EuclidMotion) (f : R4 → α) :
    (r * r').actFn f = r.actFn (r'.actFn f) := by
  funext x
  simp only [EuclidMotion.actFn, mul_inv_rev, EuclidMotion.mul_apply]
theorem actFn_one {α : Type*} (f : R4 → α) : (1 : EuclidMotion).actFn f = f := by
  funext x
  simp only [EuclidMotion.actFn, inv_one, EuclidMotion.one_apply]
theorem actList_mem_sepAll (r : EuclidMotion) {X : FnList} (hX : X ∈ sepAll) :
    r.actList X ∈ sepAll := by
  have s := isSeparatedList_of_mem_sepAll hX
  refine Set.mem_iUnion.2 ⟨_, rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact actFn_mem_C1c r (s.1 g hg)
  · have key : ∀ f g : R4 → ℝ, Disjoint (supp f) (supp g) →
        Disjoint (supp (r.actFn f)) (supp (r.actFn g)) := fun f g hfg => by
      rw [supp_actFn, supp_actFn]
      exact (Set.disjoint_image_iff r.toPerm.injective).2 hfg
    exact List.pairwise_map.2 (s.2.imp (key _ _))
theorem actList_mem_sepIn (r : EuclidMotion) {O : Set R4} {X : FnList}
    (hX : X ∈ sepIn O) : r.actList X ∈ sepIn (r '' O) := by
  refine ⟨actList_mem_sepAll r hX.1, ?_⟩
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  show supp (r.actFn g) ⊆ _
  rw [supp_actFn]
  exact Set.image_mono (hX.2 g hg)
theorem actList_mul (r r' : EuclidMotion) (X : FnList) :
    (r * r').actList X = r.actList (r'.actList X) := by
  simp only [EuclidMotion.actList, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  exact actFn_mul r r' f
theorem actList_one (X : FnList) : (1 : EuclidMotion).actList X = X := by
  have e : EuclidMotion.actFn (α := ℝ) 1 = id := funext actFn_one
  rw [EuclidMotion.actList, e, List.map_id]
theorem image_inv_image_image (r : EuclidMotion) (O : Set R4) :
    (fun x => r⁻¹ x) '' ((fun x => r x) '' O) = O := by
  rw [Set.image_image]
  simp only [EuclidMotion.inv_apply_apply, Set.image_id']
theorem actFree_toFree (r : EuclidMotion) {X : FnList} (hX : X ∈ sepAll) :
    r.actFree (toFree X) = toFree (r.actList X) :=
  liftLin_toFree _ ⟨X, hX⟩
theorem linearMap_ext_sep {V : Type*} [AddCommMonoid V] [Module ℂ V] {f g : FreeSep →ₗ[ℂ] V}
    (hfg : ∀ X : sepAll, f (toFree X.1) = g (toFree X.1)) : f = g :=
  freeBasis.ext fun X => by
    rw [freeBasis_apply]
    exact hfg X
theorem actFree_mul (r r' : EuclidMotion) (F : FreeSep) :
    (r * r').actFree F = r.actFree (r'.actFree F) := by
  have hc : (r * r').actFree = r.actFree ∘ₗ r'.actFree := linearMap_ext_sep fun X => by
    rw [LinearMap.comp_apply, actFree_toFree _ X.2, actFree_toFree _ X.2,
      actFree_toFree _ (actList_mem_sepAll r' X.2), actList_mul]
  rw [hc, LinearMap.comp_apply]
theorem actFree_one (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.one_actFree <;> assumption
theorem toFree_mem_freeSpanIn {O : Set R4} {X : FnList} (hX : X ∈ sepIn O) :
    toFree X ∈ freeSpanIn O :=
  Submodule.subset_span ⟨X, hX, rfl⟩
theorem freeSpanIn_induction {O : Set R4} {p : FreeSep → Prop}
    (mem : ∀ X ∈ sepIn O, p (toFree X)) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (smul : ∀ (a : ℂ) x, p x → p (a • x))
    {F : FreeSep} (hF : F ∈ freeSpanIn O) : p F := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeSpanIn_induction_on <;> assumption
theorem freeSep_induction {p : FreeSep → Prop}
    (mem : ∀ X : sepAll, p (toFree X.1)) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (smul : ∀ (a : ℂ) x, p x → p (a • x))
    (F : FreeSep) : p F := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeSep_induction_on <;> assumption
theorem actFree_mem_freeSpanIn (r : EuclidMotion) {O : Set R4} {F : FreeSep}
    (hF : F ∈ freeSpanIn O) : r.actFree F ∈ freeSpanIn (r '' O) := by
  refine freeSpanIn_induction (p := fun F => r.actFree F ∈ freeSpanIn (r '' O)) (fun X hX => ?_) ?_
    (fun x y hx hy => ?_) (fun a x hx => ?_) hF
  · rw [actFree_toFree r hX.1]
    exact toFree_mem_freeSpanIn (actList_mem_sepIn r hX)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · rw [map_add]
    exact add_mem hx hy
  · rw [map_smul]
    exact Submodule.smul_mem _ a hx
theorem freeConj_add (F G : FreeSep) : freeConj (F + G) = freeConj F + freeConj G := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.freeConj_add <;> assumption
theorem freeConj_smul (a : ℂ) (F : FreeSep) : freeConj (a • F) = conj a • freeConj F := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.freeConj_smul <;> assumption
theorem freeConj_zero : freeConj 0 = 0 := Finsupp.mapRange_zero
theorem freeConj_toFree (X : FnList) : freeConj (toFree X) = toFree X := by
  by_cases hX : X ∈ sepAll
  · rw [toFree_of_mem hX]
    simp [freeConj]
  · simp [toFree, hX, freeConj]
theorem freeConj_actFree (r : EuclidMotion) (F : FreeSep) :
    freeConj (r.actFree F) = r.actFree (freeConj F) := by
  refine freeSep_induction (p := fun F => freeConj (r.actFree F) = r.actFree (freeConj F))
    (fun X => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) F
  · rw [actFree_toFree r X.2, freeConj_toFree, freeConj_toFree, actFree_toFree r X.2]
  · rw [map_zero, freeConj_zero, map_zero]
  · rw [map_add, freeConj_add, freeConj_add, map_add, hx, hy]
  · rw [map_smul, freeConj_smul, freeConj_smul, map_smul, hx]
theorem freeMul_toFree {X Y : FnList} (hX : X ∈ sepAll) (hY : Y ∈ sepAll) :
    freeMul (toFree X) (toFree Y) = toFree (listAppend X Y) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeMul_toFree <;> assumption
theorem freeMul_mem_freeSpanIn {O O' : Set R4} (hd : Disjoint O O') {F F' : FreeSep}
    (hF : F ∈ freeSpanIn O) (hF' : F' ∈ freeSpanIn O') : freeMul F F' ∈ freeSpanIn (O ∪ O') := by
  refine freeSpanIn_induction (p := fun F => freeMul F F' ∈ freeSpanIn (O ∪ O')) (fun X hX => ?_) ?_
    (fun x y hx hy => ?_) (fun a x hx => ?_) hF
  · refine freeSpanIn_induction (p := fun F' => freeMul (toFree X) F' ∈ freeSpanIn (O ∪ O'))
      (fun Y hY => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) hF'
    · rw [freeMul_toFree hX.1 hY.1]
      exact toFree_mem_freeSpanIn (listAppend_mem_sepIn hd hX hY)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · rw [map_add]
      exact add_mem hx hy
    · rw [map_smul]
      exact Submodule.smul_mem _ a hx
  · rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · rw [map_add, LinearMap.add_apply]
    exact add_mem hx hy
  · rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ a hx
theorem actFree_freeMul (r : EuclidMotion) {O O' : Set R4} (hd : Disjoint O O') {F F' : FreeSep}
    (hF : F ∈ freeSpanIn O) (hF' : F' ∈ freeSpanIn O') :
    r.actFree (freeMul F F') = freeMul (r.actFree F) (r.actFree F') := by
  refine freeSpanIn_induction
    (p := fun F => r.actFree (freeMul F F') = freeMul (r.actFree F) (r.actFree F'))
    (fun X hX => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) hF
  · refine freeSpanIn_induction
      (p := fun F' => r.actFree (freeMul (toFree X) F') = freeMul (r.actFree (toFree X)) (r.actFree F'))
      (fun Y hY => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) hF'
    · rw [freeMul_toFree hX.1 hY.1, actFree_toFree r (listAppend_mem_sepIn hd hX hY).1,
        actFree_toFree r hX.1, actFree_toFree r hY.1,
        freeMul_toFree (actList_mem_sepAll r hX.1) (actList_mem_sepAll r hY.1)]
      exact congrArg toFree (List.map_append ..)
    · simp only [map_zero]
    · simp only [map_add, hx, hy]
    · simp only [map_smul, hx]
  · simp only [map_zero, LinearMap.zero_apply]
  · simp only [map_add, LinearMap.add_apply, hx, hy]
  · simp only [map_smul, LinearMap.smul_apply, hx]
theorem freeConj_freeMul (F F' : FreeSep) :
    freeConj (freeMul F F') = freeMul (freeConj F) (freeConj F') := by
  refine freeSep_induction (p := fun F => freeConj (freeMul F F') = freeMul (freeConj F) (freeConj F'))
    (fun X => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) F
  · refine freeSep_induction
      (p := fun F' => freeConj (freeMul (toFree X.1) F') =
        freeMul (freeConj (toFree X.1)) (freeConj F'))
      (fun Y => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) F'
    · rw [freeMul_toFree X.2 Y.2, freeConj_toFree, freeConj_toFree, freeConj_toFree,
        freeMul_toFree X.2 Y.2]
    · rw [map_zero, freeConj_zero, map_zero]
    · rw [map_add, freeConj_add, freeConj_add, map_add, hx, hy]
    · rw [map_smul, freeConj_smul, freeConj_smul, map_smul, hx]
  · rw [map_zero, LinearMap.zero_apply, freeConj_zero, map_zero, LinearMap.zero_apply]
  · rw [map_add, LinearMap.add_apply, freeConj_add, freeConj_add, map_add, LinearMap.add_apply,
      hx, hy]
  · rw [map_smul, LinearMap.smul_apply, freeConj_smul, freeConj_smul, map_smul,
      LinearMap.smul_apply, hx]
theorem freeMul_assoc {O O' O'' : Set R4} (hd : Disjoint O O') (hd' : Disjoint O' O'')
    {F F' F'' : FreeSep} (hF : F ∈ freeSpanIn O) (hF' : F' ∈ freeSpanIn O')
    (hF'' : F'' ∈ freeSpanIn O'') :
    freeMul (freeMul F F') F'' = freeMul F (freeMul F' F'') := by
  refine freeSpanIn_induction (p := fun F => freeMul (freeMul F F') F'' = freeMul F (freeMul F' F''))
    (fun X hX => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) hF
  · refine freeSpanIn_induction
      (p := fun F' => freeMul (freeMul (toFree X) F') F'' = freeMul (toFree X) (freeMul F' F''))
      (fun Y hY => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) hF'
    · refine freeSpanIn_induction
        (p := fun F'' => freeMul (freeMul (toFree X) (toFree Y)) F'' =
          freeMul (toFree X) (freeMul (toFree Y) F''))
        (fun Z hZ => ?_) ?_ (fun x y hx hy => ?_) (fun a x hx => ?_) hF''
      · rw [freeMul_toFree hX.1 hY.1, freeMul_toFree hY.1 hZ.1,
          freeMul_toFree (listAppend_mem_sepIn hd hX hY).1 hZ.1,
          freeMul_toFree hX.1 (listAppend_mem_sepIn hd' hY hZ).1]
        exact congrArg toFree (List.append_assoc ..)
      · simp only [map_zero]
      · simp only [map_add, hx, hy]
      · simp only [map_smul, hx]
    · simp only [map_zero, LinearMap.zero_apply]
    · simp only [map_add, LinearMap.add_apply, hx, hy]
    · simp only [map_smul, LinearMap.smul_apply, hx]
  · simp only [map_zero, LinearMap.zero_apply]
  · simp only [map_add, LinearMap.add_apply, hx, hy]
  · simp only [map_smul, LinearMap.smul_apply, hx]
theorem re_mem_C1c {f : R4 → ℂ} (hf : f ∈ C1c ℂ) :
    (fun x => (f x).re) ∈ C1c ℝ := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.re_mem_C1c <;> assumption
theorem im_mem_C1c {f : R4 → ℂ} (hf : f ∈ C1c ℂ) :
    (fun x => (f x).im) ∈ C1c ℝ := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.im_mem_C1c <;> assumption
theorem supp_re_subset (f : R4 → ℂ) : supp (fun x => (f x).re) ⊆ supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.supp_re_subset <;> assumption
theorem supp_im_subset (f : R4 → ℂ) : supp (fun x => (f x).im) ⊆ supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.supp_im_subset <;> assumption
section ComplexComponents
variable {n : ℕ} (h : Fin n → R4 → ℂ)
theorem realPartComponent_eq_re_or_im (ε : nonrealIdx h → Fin 2) (k : Fin n) :
    realPartComponent h ε k = (fun x => (h k x).re) ∨ realPartComponent h ε k = (fun x => (h k x).im) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.realPartComponent_re_or_im <;> assumption
variable {h}
theorem ofFn_realPartComponent_mem_sepIn {O : Set R4} (hh : ∀ k, h k ∈ C1c ℂ)
    (hd : Pairwise fun k l => Disjoint (supp (h k)) (supp (h l)))
    (hO : ∀ k, supp (h k) ⊆ O) (ε : nonrealIdx h → Fin 2) :
    List.ofFn (realPartComponent h ε) ∈ sepIn O := by
  have hsup : ∀ k, supp (realPartComponent h ε k) ⊆ supp (h k) := fun k => by
    rcases realPartComponent_eq_re_or_im h ε k with e | e <;> rw [e]
    · exact supp_re_subset _
    · exact supp_im_subset _
  have hmem : ∀ k, realPartComponent h ε k ∈ C1c ℝ := fun k => by
    rcases realPartComponent_eq_re_or_im h ε k with e | e <;> rw [e]
    · exact re_mem_C1c (hh k)
    · exact im_mem_C1c (hh k)
  refine ⟨Set.mem_iUnion.2 ⟨_, rfl, ?_, ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact hmem k
  · exact List.pairwise_ofFn.2 fun i j hij => (hd hij.ne).mono (hsup i) (hsup j)
  · intro f hf
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact (hsup k).trans (hO k)
theorem complexList_mem_freeSpanIn {O : Set R4} (hh : ∀ k, h k ∈ C1c ℂ)
    (hd : Pairwise fun k l => Disjoint (supp (h k)) (supp (h l)))
    (hO : ∀ k, supp (h k) ⊆ O) : complexList h ∈ freeSpanIn O :=
  Submodule.sum_mem _ fun ε _ =>
    Submodule.smul_mem _ _ (toFree_mem_freeSpanIn (ofFn_realPartComponent_mem_sepIn hh hd hO ε))
variable (h)
theorem nonrealIdx_actFn (r : EuclidMotion) :
    nonrealIdx (fun k => r.actFn (h k)) = nonrealIdx h := by
  ext k
  simp only [nonrealIdx, Finset.mem_filter, Finset.mem_univ, true_and, not_iff_not]
  constructor
  · intro hk x
    have hx := hk (r x)
    simpa only [EuclidMotion.actFn, EuclidMotion.inv_apply_apply] using hx
  · intro hk x
    exact hk _
theorem sum_signs_congr {V : Type*} [AddCommMonoid V] {S S' : Finset (Fin n)} (e : S = S')
    (A : (S → Fin 2) → V) (B : (S' → Fin 2) → V)
    (hAB : ∀ ε ε', (∀ k (hk : k ∈ S) (hk' : k ∈ S'), ε ⟨k, hk⟩ = ε' ⟨k, hk'⟩) → A ε = B ε') :
    ∑ ε, A ε = ∑ ε, B ε := by
  subst e
  exact Finset.sum_congr rfl fun ε _ => hAB ε ε fun k hk hk' => rfl
theorem sum_signs_val_congr {S S' : Finset (Fin n)} (e : S = S') (ε : S → Fin 2) (ε' : S' → Fin 2)
    (hag : ∀ k (hk : k ∈ S) (hk' : k ∈ S'), ε ⟨k, hk⟩ = ε' ⟨k, hk'⟩) :
    ∑ k, (ε k : ℕ) = ∑ k, (ε' k : ℕ) := by
  subst e
  have hε : ε = ε' := funext fun k => hag k.1 k.2 k.2
  rw [hε]
theorem actFn_realPartEntry (r : EuclidMotion) (ε : nonrealIdx h → Fin 2)
    (ε' : nonrealIdx (fun k => r.actFn (h k)) → Fin 2)
    (hag : ∀ k (hk : k ∈ nonrealIdx h) (hk' : k ∈ nonrealIdx fun k => r.actFn (h k)),
      ε ⟨k, hk⟩ = ε' ⟨k, hk'⟩) (k : Fin n) :
    r.actFn (realPartComponent h ε k) = realPartComponent (fun k => r.actFn (h k)) ε' k := by
  have e := nonrealIdx_actFn h r
  by_cases hk : k ∈ nonrealIdx h
  · have hk' : k ∈ nonrealIdx fun k => r.actFn (h k) := e ▸ hk
    simp only [realPartComponent, dif_pos hk, dif_pos hk', hag k hk hk']
    split_ifs <;> rfl
  · have hk' : k ∉ nonrealIdx fun k => r.actFn (h k) := e ▸ hk
    simp only [realPartComponent, dif_neg hk, dif_neg hk']
    rfl
theorem actFree_complexList (r : EuclidMotion) {O : Set R4}
    (hh : ∀ k, h k ∈ C1c ℂ)
    (hd : Pairwise fun k l => Disjoint (supp (h k)) (supp (h l)))
    (hO : ∀ k, supp (h k) ⊆ O) :
    r.actFree (complexList h) = complexList fun k => r.actFn (h k) := by
  unfold complexList
  rw [map_sum]
  refine sum_signs_congr (nonrealIdx_actFn h r).symm _ _ fun ε ε' hag => ?_
  rw [map_smul, actFree_toFree r (ofFn_realPartComponent_mem_sepIn hh hd hO ε).1]
  have hs : imagCount h ε = imagCount (fun k => r.actFn (h k)) ε' :=
    sum_signs_val_congr (nonrealIdx_actFn h r).symm ε ε' hag
  rw [hs, EuclidMotion.actList, List.map_ofFn]
  congr 2
  congr 1
  funext k
  exact actFn_realPartEntry h r ε ε' hag k
end ComplexComponents
theorem timeVec_three : timeVec 3 = 1 := by
  simp [timeVec, PeriodicLattice.coordVec]
theorem dotProduct_timeVec (x : R4) : x ⬝ᵥ timeVec = x 3 := by
  simp [timeVec, PeriodicLattice.coordVec]
theorem timeFlip_apply_three (x : R4) : timeFlip x 3 = -x 3 := by
  rw [timeFlip_apply, Pi.sub_apply, Pi.smul_apply, timeVec_three, smul_eq_mul]
  ring
theorem timeFlip_mul_self : timeFlip * timeFlip = 1 :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.one_apply, timeFlip_apply (timeFlip x),
      timeFlip_apply_three, timeFlip_apply x]
    funext μ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
theorem timeFlip_inv : timeFlip⁻¹ = timeFlip := inv_eq_of_mul_eq_one_left timeFlip_mul_self
theorem apply_sub_smul_of_offset_eq_zero (w : EuclidMotion) (hs : w.offset = 0) (a b : R4)
    (c : ℝ) : w (a - c • b) = w a - c • w b := by
  rw [hs]
  simp only [add_zero, map_sub, map_smul]
theorem offset_eq_zero_of_mem {w : EuclidMotion} (hw : w ∈ hyperoctahedral) : w.offset = 0 := by
  obtain ⟨f, rfl⟩ := hw
  rfl
theorem dotProduct_apply_of_mem {w : EuclidMotion} (hw : w ∈ hyperoctahedral) (x y : R4) :
    w x ⬝ᵥ w y = x ⬝ᵥ y := by
  obtain ⟨f, rfl⟩ := hw
  rw [ofSignedFrame_apply, ofSignedFrame_apply]
  simp only [dotProduct, PeriodicLattice.SignedFrame.actOnVector]
  have hf : ∀ μ, ((f.2 μ : ℤ) : ℝ) * x (f.1 μ) * (((f.2 μ : ℤ) : ℝ) * y (f.1 μ)) =
      x (f.1 μ) * y (f.1 μ) := fun μ => by
    have hs := intUnit_mul_self (f.2 μ)
    calc ((f.2 μ : ℤ) : ℝ) * x (f.1 μ) * (((f.2 μ : ℤ) : ℝ) * y (f.1 μ))
        = (((f.2 μ : ℤ) : ℝ) * ((f.2 μ : ℤ) : ℝ)) * (x (f.1 μ) * y (f.1 μ)) := by ring
      _ = x (f.1 μ) * y (f.1 μ) := by rw [hs, one_mul]
  simp only [hf]
  exact Equiv.sum_comp f.1 fun μ => x μ * y μ
theorem dotProduct_apply_timeVec {w : EuclidMotion} (hw : w ∈ hyperoctahedral) (x : R4) :
    x ⬝ᵥ w timeVec = (w⁻¹ x) 3 := by
  rw [← dotProduct_timeVec (w⁻¹ x), ← dotProduct_apply_of_mem hw (w⁻¹ x) timeVec,
    w.apply_inv_apply]
theorem image_setOf_coord_three {w : EuclidMotion} (hw : w ∈ hyperoctahedral) (P : ℝ → Prop) :
    w '' {x | P (x 3)} = {x | P (x ⬝ᵥ w timeVec)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show P (_ ⬝ᵥ _)
    rw [dotProduct_apply_timeVec hw, w.inv_apply_apply]
    exact hx
  · intro hy
    refine ⟨w⁻¹ y, ?_, w.apply_inv_apply y⟩
    show P ((w⁻¹ y) 3)
    rw [← dotProduct_apply_timeVec hw]
    exact hy
theorem apply_three_of_mem_timeStabilizer {w : EuclidMotion} (hw : w ∈ timeStabilizer) (x : R4) :
    w x 3 = x 3 := by
  obtain ⟨hw, he⟩ := hw
  rw [← dotProduct_timeVec (w x), ← dotProduct_timeVec x, ← dotProduct_apply_of_mem hw x timeVec,
    he]
theorem image_setOf_of_mem_timeStabilizer {w : EuclidMotion} (hw : w ∈ timeStabilizer)
    (P : ℝ → Prop) : w '' {x | P (x 3)} = {x | P (x 3)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show P (w x 3)
    rw [apply_three_of_mem_timeStabilizer hw]
    exact hx
  · intro hy
    refine ⟨w⁻¹ y, ?_, w.apply_inv_apply y⟩
    show P ((w⁻¹ y) 3)
    rw [apply_three_of_mem_timeStabilizer (timeStabilizer.inv_mem hw)]
    exact hy
theorem timeStabilizerRules : MotionRules.TimeStabilizerRules := by
  intro w hw
  refine ⟨apply_three_of_mem_timeStabilizer hw,
    fun c => image_setOf_of_mem_timeStabilizer hw fun t => c < t,
    image_setOf_of_mem_timeStabilizer hw fun t => t = 0, EuclidMotion.ext_of_apply fun x => ?_⟩
  rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, timeFlip_apply, timeFlip_apply,
    apply_sub_smul_of_offset_eq_zero w (offset_eq_zero_of_mem hw.1), hw.2,
    apply_three_of_mem_timeStabilizer hw]
theorem conjugateFlip : MotionRules.ConjugateFlip := by
  intro w hw
  refine ⟨image_setOf_coord_three hw fun t => 0 < t, image_setOf_coord_three hw fun t => t = 0,
    fun x => ?_⟩
  rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, timeFlip_apply,
    apply_sub_smul_of_offset_eq_zero w (offset_eq_zero_of_mem hw), w.apply_inv_apply,
    dotProduct_apply_timeVec hw]
theorem halfSpaceImages : MotionRules.HalfSpaceImages := by
  intro c t
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show timeFlip x 3 < -c
      rw [timeFlip_apply_three]
      exact neg_lt_neg hx
    · intro hy
      have hy' : y 3 < -c := hy
      refine ⟨timeFlip y, ?_, ?_⟩
      · show c < timeFlip y 3
        rw [timeFlip_apply_three]
        linarith
      · rw [← EuclidMotion.mul_apply, timeFlip_mul_self, EuclidMotion.one_apply]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : c < x 3 := hx
      show c + t < (x + t • timeVec) 3
      simp only [Pi.add_apply, Pi.smul_apply, timeVec_three, smul_eq_mul, mul_one]
      linarith
    · intro hy
      have hy' : c + t < y 3 := hy
      refine ⟨y - t • timeVec, ?_, ?_⟩
      · show c < (y - t • timeVec) 3
        simp only [Pi.sub_apply, Pi.smul_apply, timeVec_three, smul_eq_mul, mul_one]
        linarith
      · rw [EuclidMotion.transl_apply, sub_add_cancel]
  · have hv' : v 3 = 0 := hv
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : c < x 3 := hx
      show c < (x + v) 3
      simp only [Pi.add_apply, hv', add_zero]
      exact hx'
    · intro hy
      have hy' : c < y 3 := hy
      refine ⟨y - v, ?_, ?_⟩
      · show c < (y - v) 3
        simp only [Pi.sub_apply, hv', sub_zero]
        exact hy'
      · rw [EuclidMotion.transl_apply, sub_add_cancel]
theorem translationRules : MotionRules.TranslationRules := by
  intro r v v'
  have h₁ : ∀ x, (EuclidMotion.transl v * EuclidMotion.transl v') x =
      EuclidMotion.transl (v + v') x := fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply, add_assoc, add_comm v' v]
  have h₂ : ∀ x, (r * EuclidMotion.transl v) x =
      (EuclidMotion.transl (r.lin v) * r) x := fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply]
    show r.lin (x + v) + r.offset = r.lin x + r.offset + r.lin v
    rw [map_add]
    abel
  refine ⟨h₁, h₂, fun F => ?_, fun F => ?_⟩
  · rw [← actFree_mul, EuclidMotion.ext_of_apply h₁]
  · rw [← actFree_mul, ← actFree_mul, EuclidMotion.ext_of_apply h₂]
theorem motionOnLists : MotionRules.MotionOnLists := by
  intro O hO r r'
  refine ⟨?_, ⟨fun X hX => actList_mem_sepIn r hX, ?_, ?_⟩, fun X _ => List.length_map _,
    ⟨fun F hF => actFree_mem_freeSpanIn r hF, ?_, ?_⟩, actFree_mul r r', freeConj_actFree r,
    fun n _ h hh hd hs => ⟨complexList_mem_freeSpanIn hh hd hs, actFree_complexList h r hh hd hs⟩⟩
  · have e : (fun x => r x) '' O = (fun x => r⁻¹ x) ⁻¹' O := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        show r⁻¹ (r x) ∈ O
        rwa [r.inv_apply_apply]
      · intro hy
        exact ⟨r⁻¹ y, hy, r.apply_inv_apply y⟩
    rw [e]
    exact hO.preimage (continuous_motion r⁻¹)
  · intro X _ Y _ hXY
    have hc := congrArg (r⁻¹).actList hXY
    rwa [← actList_mul, ← actList_mul, inv_mul_cancel, actList_one, actList_one] at hc
  · intro Y hY
    refine ⟨(r⁻¹).actList Y, ?_, ?_⟩
    · have hm := actList_mem_sepIn r⁻¹ hY
      rwa [image_inv_image_image] at hm
    · rw [← actList_mul, mul_inv_cancel, actList_one]
  · intro F _ G _ hFG
    have hc := congrArg (r⁻¹).actFree hFG
    rwa [← actFree_mul, ← actFree_mul, inv_mul_cancel, actFree_one, actFree_one] at hc
  · intro G hG
    refine ⟨(r⁻¹).actFree G, ?_, ?_⟩
    · have hm := actFree_mem_freeSpanIn r⁻¹ hG
      rwa [image_inv_image_image] at hm
    · rw [← actFree_mul, mul_inv_cancel, actFree_one]
theorem allRules : MotionRules.AllRules := by
  refine ⟨disjointCompactPosDist, ?_, motionOnLists, ?_, ?_, translationRules, ?_,
    halfSpaceImages, timeStabilizerRules, conjugateFlip⟩
  · intro r r' f hf
    exact ⟨actFn_mem_C1c r hf, supp_actFn r f, rfl, rfl, rfl, actFn_mul r r' f⟩
  · intro O O' _ _ hd r
    refine ⟨fun F hF F' hF' => freeMul_mem_freeSpanIn hd hF hF', fun a b F₁ _ F₂ _ F' _ => ?_,
      fun a b F₁ _ F₂ _ F' _ => ?_, fun F hF F' hF' => actFree_freeMul r hd hF hF',
      fun F _ F' _ => freeConj_freeMul F F'⟩
    · simp only [map_add, map_smul]
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · intro O O' O'' _ _ _ h₁ _ h₃ F hF F' hF' F'' hF''
    exact freeMul_assoc h₁ h₃ hF hF' hF''
  · refine ⟨rfl, fun w hw => offset_eq_zero_of_mem hw, timeFlip_inv⟩
end YangMills.Construction.EuclideanFunctionals.MotionProofs
