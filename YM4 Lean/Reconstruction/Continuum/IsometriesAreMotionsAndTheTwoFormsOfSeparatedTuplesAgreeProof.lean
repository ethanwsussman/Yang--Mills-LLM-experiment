import Reconstruction.Continuum.IsometriesAreMotionsAndTheTwoFormsOfSeparatedTuplesAgree
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import Mathlib
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.SeparatedTupleForms
open InfiniteLattice (AmbientSpace)
open TestSpaces Motions
open SeparatedTuples (RealValued SepTuple IsDisjointlySupported push pushList invMap supportedIn)
open SmoothSeparatedTuples (pureTranslation pureTranslation_toFun)
theorem orth_transpose_mul_self {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Rᵀ * R = 1 := by apply _root_.YangMills.Construction.ConfigSpace.orth_transpose_mul_self <;> assumption
theorem euclidNormVec_mulVec_orth {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (w : AmbientSpace) :
    TorusMetric.euclidNormVec (R *ᵥ w) = TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.euclidNormVec_orth_mulVec <;> assumption
theorem inv_mem_orthogonalGroup {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : R⁻¹ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  have h₁ : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hR
  rw [Matrix.inv_eq_right_inv h₁, Matrix.mem_orthogonalGroup_iff]
  simpa using orth_transpose_mul_self hR
theorem contDiff_matrix_mulVec (R : Matrix (Fin 4) (Fin 4) ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k fun u : AmbientSpace => R *ᵥ u := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' R)).contDiff (𝕜 := ℝ) (n := k)
  have e : (⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' R)) : AmbientSpace → AmbientSpace) =
      fun u => R *ᵥ u := by
    funext u
    simp [Matrix.toLin'_apply]
  rwa [e] at h
theorem contDiff_rigidToFun (r : RigidMotion) {k : WithTop ℕ∞} : ContDiff ℝ k r.toFun :=
  (contDiff_matrix_mulVec r.mat).add contDiff_const
theorem contDiff_rigidInvFun (r : RigidMotion) {k : WithTop ℕ∞} : ContDiff ℝ k r.invFun :=
  (contDiff_matrix_mulVec r.mat⁻¹).comp (contDiff_id.sub contDiff_const)
def rigidHomeomorph (r : RigidMotion) : AmbientSpace ≃ₜ AmbientSpace where
  toFun := r.toFun
  invFun := r.invFun
  left_inv := r.invFun_toFun
  right_inv := r.toFun_invFun
  continuous_toFun := (contDiff_rigidToFun r (k := 0)).continuous
  continuous_invFun := (contDiff_rigidInvFun r (k := 0)).continuous
theorem rigid_injective (r : RigidMotion) : Function.Injective r.toFun :=
  (rigidHomeomorph r).injective
theorem invMap_rigid (r : RigidMotion) : invMap r.toFun = r.invFun := by apply _root_.YangMills.SharedProofs.p78111 <;> assumption
theorem tsupport_actOnPointFun (r : RigidMotion) (f : AmbientSpace → ℝ) :
    tsupport (actOnPointFun r f) = r.toFun '' tsupport f := by
  have h : tsupport (actOnPointFun r f) =
      (rigidHomeomorph r).symm ⁻¹' tsupport f :=
    tsupport_comp_eq_preimage f (rigidHomeomorph r).symm
  rw [h]
  exact ((rigidHomeomorph r).image_eq_preimage_symm (tsupport f)).symm
theorem hasCompactSupport_actOnPointFun (r : RigidMotion) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (actOnPointFun r f) :=
  hf.comp_homeomorph (rigidHomeomorph r).symm
theorem actOnTuple_mem {O : Set AmbientSpace} {n : ℕ} {X : Fin n → AmbientSpace → ℝ}
    (hX : X ∈ disjointSupportTuples O n) (r : RigidMotion) :
    actOnTuple r X ∈ disjointSupportTuples (r.toFun '' O) n := by
  refine ⟨fun i => ⟨(hX.1 i).1.comp (contDiff_rigidInvFun r),
    hasCompactSupport_actOnPointFun r (hX.1 i).2.1, ?_⟩, fun i i' hi => ?_⟩
  · change tsupport (actOnPointFun r (X i)) ⊆ _
    rw [tsupport_actOnPointFun]
    exact Set.image_mono (hX.1 i).2.2
  · change Disjoint (tsupport (actOnPointFun r (X i)))
      (tsupport (actOnPointFun r (X i')))
    rw [tsupport_actOnPointFun, tsupport_actOnPointFun]
    exact (Set.disjoint_image_iff (rigid_injective r)).2 (hX.2 hi)
theorem actOnTuple_smooth {O : Set AmbientSpace} {n : ℕ} {X : Fin n → AmbientSpace → ℝ}
    (hX : HasSmoothComponents O X) (r : RigidMotion) :
    HasSmoothComponents (r.toFun '' O) (actOnTuple r X) := by
  refine fun i => ⟨(hX i).1.comp (contDiff_rigidInvFun r),
    hasCompactSupport_actOnPointFun r (hX i).2.1, ?_⟩
  change tsupport (actOnPointFun r (X i)) ⊆ _
  rw [tsupport_actOnPointFun]
  exact Set.image_mono (hX i).2.2
theorem componentList_get (L : List RealValued) : componentList L.get = L := List.ofFn_get L
theorem mem_c1CompactSupp_iff (f : RealValued) (O : Set AmbientSpace) :
    f ∈ c1CompactSupp O ↔ SeparatedTuples.IsC1c f ∧ tsupport f ⊆ O := by
  simp only [c1CompactSupp, SeparatedTuples.IsC1c,
    TestFunctions.IsC1R4, Set.mem_ofPred_eq, and_assoc]
theorem componentList_disjoint_iff {O : Set AmbientSpace} {n : ℕ} (f : Fin n → AmbientSpace → ℝ) :
    (IsDisjointlySupported (componentList f) ∧ ∀ g ∈ componentList f, tsupport g ⊆ O) ↔
      f ∈ disjointSupportTuples O n := by
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    have hmem : ∀ i, f i ∈ componentList f := fun i => (List.mem_ofFn' f _).2 ⟨i, rfl⟩
    refine ⟨fun i => (mem_c1CompactSupp_iff _ _).2 ⟨h₁ _ (hmem i), h₃ _ (hmem i)⟩,
      fun i i' hi => ?_⟩
    have hp := List.pairwise_ofFn.1 h₂
    rcases lt_or_gt_of_ne hi with h | h
    · exact hp h
    · exact (hp h).symm
  · intro hf
    have hall : ∀ g ∈ componentList f, g ∈ c1CompactSupp O := by
      intro g hg
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' f _).1 hg
      exact hf.1 i
    exact ⟨⟨fun g hg => ((mem_c1CompactSupp_iff _ _).1 (hall g hg)).1,
      List.pairwise_ofFn.2 fun i i' h => hf.2 h.ne⟩,
      fun g hg => ((mem_c1CompactSupp_iff _ _).1 (hall g hg)).2⟩
theorem isDisjointlySupported_componentList {O : Set AmbientSpace} {n : ℕ}
    {f : Fin n → AmbientSpace → ℝ}
    (hf : f ∈ disjointSupportTuples O n) : IsDisjointlySupported (componentList f) :=
  ((componentList_disjoint_iff f).2 hf).1
theorem get_mem_disjointSupportTuples {O : Set AmbientSpace} {X : SeparatedTuples.SepTuple}
    (hX : X ∈ supportedIn O) :
    X.1.get ∈ disjointSupportTuples O X.1.length := by
  refine (componentList_disjoint_iff _).1 ?_
  rw [componentList_get]
  exact ⟨X.2, hX⟩
theorem sizedTuples_eq (O : Set AmbientSpace) (n : ℕ) : SizedTuplesEq O n := by
  ext L
  constructor
  · rintro ⟨X, ⟨hX, hn⟩, rfl⟩
    obtain rfl : X.1.length = n := hn
    exact ⟨X.1.get, get_mem_disjointSupportTuples hX, componentList_get X.1⟩
  · rintro ⟨f, hf, rfl⟩
    have h := (componentList_disjoint_iff f).2 hf
    exact ⟨⟨componentList f, h.1⟩, ⟨h.2, List.length_ofFn⟩, rfl⟩
theorem supportedTuples_eq_union (O : Set AmbientSpace) : SupportedTuplesEqUnion O := by
  ext L
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X.1.length, by
      rw [← sizedTuples_eq O X.1.length]
      exact ⟨X, ⟨hX, rfl⟩, rfl⟩⟩
  · rintro ⟨n, hL⟩
    rw [← sizedTuples_eq O n] at hL
    obtain ⟨X, ⟨hX, -⟩, rfl⟩ := hL
    exact ⟨X, hX, rfl⟩
theorem wholeSpaceTuples_eq : WholeSpaceTuplesEq := by
  refine ⟨?_, ?_⟩
  · rintro ⟨m, Y⟩ ⟨m', Y'⟩ h
    have hm : m = m' := by
      have := congrArg List.length h
      simpa [sepTupleComponents, componentList] using this
    subst hm
    have hY : Y.1 = Y'.1 := List.ofFn_injective h
    exact sepTuple_ext Y Y' rfl fun k => congrFun hY k
  · ext L
    constructor
    · rintro ⟨⟨m, Y⟩, rfl⟩
      have h := (componentList_disjoint_iff Y.1).2 Y.2
      exact ⟨⟨componentList Y.1, h.1⟩, h.2, rfl⟩
    · rintro ⟨X, -, rfl⟩
      exact ⟨⟨X.1.length, X.1.get,
        get_mem_disjointSupportTuples fun _ _ => Set.subset_univ _⟩, componentList_get X.1⟩
theorem smoothTuples_eq (O : Set AmbientSpace) (n : ℕ) : SmoothTuplesEq O n := by
  ext L
  constructor
  · rintro ⟨X, ⟨⟨hX, hs⟩, hn⟩, rfl⟩
    obtain rfl : X.1.length = n := hn
    have hmem := get_mem_disjointSupportTuples hX
    refine ⟨X.1.get, ⟨hmem, fun i => ?_⟩, componentList_get X.1⟩
    exact ⟨hs _ (List.get_mem _ _), (hmem.1 i).2.1, (hmem.1 i).2.2⟩
  · rintro ⟨f, ⟨hf, hs⟩, rfl⟩
    have h := (componentList_disjoint_iff f).2 hf
    refine ⟨⟨componentList f, h.1⟩, ⟨⟨h.2, fun g hg => ?_⟩, List.length_ofFn⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' f _).1 hg
    exact (hs i).1
theorem disjointSupportTuples_mono (O O' : Set AmbientSpace) (n : ℕ) :
    DisjointSupportTuplesMono O O' n := fun h _ hf =>
  ⟨fun i => ⟨(hf.1 i).1, (hf.1 i).2.1, (hf.1 i).2.2.trans h⟩, hf.2⟩
theorem motionActions_eq {O : Set AmbientSpace} {n : ℕ} {X : Fin n → AmbientSpace → ℝ}
    (hX : X ∈ disjointSupportTuples O n) (r : RigidMotion) : MotionActionsEq X r := by
  intro Z hZ
  have hlist : pushList r.toFun Z.1 = componentList (actOnTuple r X) := by
    rw [hZ, pushList, invMap_rigid, componentList, List.map_ofFn]
    rfl
  have hsep : IsDisjointlySupported (pushList r.toFun Z.1) := by
    rw [hlist]
    exact isDisjointlySupported_componentList (actOnTuple_mem hX r)
  simp only [push, dif_pos hsep]
  exact hlist
theorem translationActions_eq {O : Set AmbientSpace} {n : ℕ} {X : Fin n → AmbientSpace → ℝ}
    (hX : X ∈ disjointSupportTuples O n) (v : AmbientSpace) : TranslationActionsEq X v := by
  intro Z hZ
  rw [← pureTranslation_toFun]
  exact motionActions_eq hX (pureTranslation v) Z hZ
theorem motion_preserves_tuples {O : Set AmbientSpace} {n : ℕ} {X : Fin n → AmbientSpace → ℝ}
    (hO : IsOpen O) (hX : X ∈ disjointSupportTuples O n) (r : RigidMotion) :
    MotionPreservesTuples O X r :=
  ⟨(rigidHomeomorph r).isOpenMap O hO, actOnTuple_mem hX r,
    fun hs => actOnTuple_smooth hs r⟩
theorem juxt_eq_concat {q q' : ℕ} (X : SepTupleOfCard q) (Y : SepTupleOfCard q') :
    JuxtEqConcat X Y := by
  intro Z W hZ hW
  have hlist : componentList (concatTuple X.1 Y.1) = Z.1 ++ W.1 := by
    rw [hZ, hW]
    exact List.ofFn_fin_append X.1 Y.1
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · refine (componentList_disjoint_iff _).1 ⟨?_, fun _ _ => Set.subset_univ _⟩
    rw [hlist]
    exact (SeparatedTuples.SepTuple.glue Z W h).2
  · have hs := isDisjointlySupported_componentList h
    rw [hlist] at hs
    exact (List.pairwise_append.1 hs.2).2.2
  · rw [SeparatedTuples.SepTuple.juxt_val h, hlist]
theorem twoFormsAgree_of_classification (hI : Tower.OrthogonalMotions.Classification) :
    TwoFormsAgree := by
  refine ⟨fun r => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_, rfl, rfl, fun O hO =>
    ⟨supportedTuples_eq_union O,
    fun n => ⟨sizedTuples_eq O n, smoothTuples_eq O n,
      fun O' _ => disjointSupportTuples_mono O O' n, fun X hX => ⟨fun r =>
        ⟨motion_preserves_tuples hO hX r, fun i => tsupport_actOnPointFun r (X i),
          motionActions_eq hX r⟩,
        fun v => translationActions_eq hX v⟩⟩⟩, wholeSpaceTuples_eq,
    fun _ _ X Y => juxt_eq_concat X Y⟩
  · exact hI.2.1 r h
  · obtain ⟨R, hR, v, hr⟩ := h
    intro x y
    have e : r x - r y = R *ᵥ (x - y) := by
      rw [hr, hr, mulVec_sub]
      abel
    rw [e]
    exact euclidNormVec_mulVec_orth hR _
  · rintro r s ⟨R, hR, v, hr⟩ ⟨S, hS, w, hs⟩
    refine ⟨R * S, mul_mem hR hS, R *ᵥ w + v, fun u => ?_⟩
    simp only [Function.comp_apply, hr, hs, mulVec_add, mulVec_mulVec, add_assoc]
  · intro r
    refine ⟨r.mat⁻¹, inv_mem_orthogonalGroup r.mat_mem, -(r.mat⁻¹ *ᵥ r.shift), fun u => ?_⟩
    change r.mat⁻¹ *ᵥ (u - r.shift) = _
    rw [mulVec_sub, sub_eq_add_neg]
end YangMills.Construction.SeparatedTupleForms
end
