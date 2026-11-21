import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.Continuum.RulesOfTheOrthogonalActionProof
import YangMills.Construction.EuclideanFunctionals.FirstValuesOfTheCentredFunctional
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import Reconstruction.MinkowskiSpace.SelfAdjointnessOfTheFieldOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Function
open scoped InnerProductSpace ContDiff ComplexConjugate
noncomputable section
namespace YangMills.Construction.MidpointSelfAdjoint
open SeparatedTuples FieldFormConditions ProjectionMeasures HilbertToolkit OneLoopNotation
  InsertedFieldForm
open ReflectionPositivity.FormProperties (shiftedSpan)
open ReflectionPositivity.TupleForm (PositiveSpan reflectConj)
open Motions (RigidMotion)
open TupleLists (ofList)
open InfiniteLattice (AmbientSpace)
open TimeAxis (timeIdx)
theorem perm_exists_get_equiv {α : Type*} {l l' : List α} (h : l.Perm l') :
    ∃ e : Fin l.length ≃ Fin l'.length, ∀ i, l'.get (e i) = l.get i := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => i.elim0⟩
  | @cons x l₁ l₂ _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr e).trans (finSuccEquiv _).symm),
      fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using he j
  | swap x y l =>
    refine ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, fun i => ?_⟩
    obtain ⟨i, hi⟩ := i
    match i, hi with
    | 0, _ => simp
    | 1, _ => simp
    | k + 2, hk =>
      have h₁ : (⟨k + 2, hk⟩ : Fin (x :: y :: l).length) ≠ ⟨0, by simp⟩ := by simp [Fin.ext_iff]
      have h₂ : (⟨k + 2, hk⟩ : Fin (x :: y :: l).length) ≠ ⟨1, by simp⟩ := by simp [Fin.ext_iff]
      have hs := Equiv.swap_apply_of_ne_of_ne h₁ h₂
      change (x :: y :: l).get (Equiv.swap _ _ (⟨k + 2, hk⟩ : Fin (x :: y :: l).length)) = _
      rw [hs]
      rfl
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e₁, h₁⟩ := ih₁
    obtain ⟨e₂, h₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun i => (h₂ _).trans (h₁ _)⟩
variable {σ : TestSpaces.SepTuple → ℝ}
theorem eval_eq_of_perm (hs : WightmanReconstruction.IsPermutationInvariant σ) {X Y : SepTuple}
    (hp : X.1.Perm Y.1) (hne : X.1 ≠ []) : σ (ofList X) = σ (ofList Y) := by
  obtain ⟨e, he⟩ := perm_exists_get_equiv hp
  have hl : Y.1.length = X.1.length := hp.length_eq.symm
  have hpos : 1 ≤ Y.1.length := by
    rw [hl]
    exact List.length_pos_iff.2 hne
  let W : TestSpaces.SepTupleOfCard Y.1.length :=
    ⟨Y.1.get, TupleLists.get_mem_disjointSupportTuples Y⟩
  let ς : Equiv.Perm (Fin Y.1.length) := (finCongr hl).trans e
  have h := hs _ hpos W ς
  have hX : (⟨_, WightmanReconstruction.permuteComponents W ς⟩ : TestSpaces.SepTuple) = ofList X :=
    TestSpaces.sepTuple_ext _ _ hl fun k => he _
  rw [← hX, h]
  rfl
theorem eval_motion (hi : ∀ r : RigidMotion, WightmanReconstruction.IsMotionInvariant σ r)
    (r : RigidMotion) {X Z : SepTuple} (hZ : Z.1 = X.1.map (· ∘ r.invFun)) :
    σ (ofList Z) = σ (ofList X) := by
  rw [← hi r (ofList X)]
  congr 1
  obtain ⟨z, hz⟩ := Z
  obtain rfl : z = X.1.map (· ∘ r.invFun) := hZ
  exact (TestSpaces.sepTuple_ext _ _ (by simp [ofList]) fun k => by
    simp [ofList, Motions.actOnTuple, Motions.actOnPointFun]
    rfl).symm
theorem invMap_toFun (r : RigidMotion) : invMap r.toFun = r.invFun := by apply _root_.YangMills.SharedProofs.p78111 <;> assumption
theorem continuous_invFun (r : RigidMotion) : Continuous r.invFun :=
  (UpperHalfTensors.contDiff_invFun r).continuous
theorem isDisjointlySupported_pushList (r : RigidMotion) (X : SepTuple) :
    IsDisjointlySupported (pushList r.toFun X.1) := by
  rw [pushList, invMap_toFun]
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    obtain ⟨h₁, h₂⟩ := X.2.1 g hg
    exact ⟨(show ContDiff ℝ 1 g from h₁).comp (UpperHalfTensors.contDiff_invFun r),
      h₂.comp_homeomorph (UpperHalfTensors.rigidHomeomorph r).symm⟩
  · refine List.pairwise_map.2 (X.2.2.imp fun {f g} h => ?_)
    exact (h.preimage r.invFun).mono
      (tsupport_comp_subset_preimage f (continuous_invFun r))
      (tsupport_comp_subset_preimage g (continuous_invFun r))
theorem push_val (r : RigidMotion) (X : SepTuple) :
    (push r.toFun X).1 = X.1.map (· ∘ r.invFun) := by
  rw [push, dif_pos (isDisjointlySupported_pushList r X)]
  simp only [pushList, invMap_toFun]
theorem push_mem_supportedIn (r : RigidMotion) {X : SepTuple} {O O' : Set AmbientSpace}
    (hX : X ∈ supportedIn O) (h : ∀ x, r.invFun x ∈ O → x ∈ O') :
    push r.toFun X ∈ supportedIn O' := by
  intro f hf x hx
  rw [push_val] at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  exact h x (hX g hg (tsupport_comp_subset_preimage g (continuous_invFun r) hx))
theorem timeReflection_eq_toFun : TimeAxis.timeReflection = RigidMotion.timeReflection.toFun :=
  RigidMotion.timeReflection_toFun.symm
theorem translate_eq_toFun (v : AmbientSpace) :
    SeparatedTuples.translate v = (UpperHalfTensors.translateMotion v).toFun :=
  funext fun x => (UpperHalfTensors.translateMotion_toFun v x).symm
theorem translateMotion_invFun_apply (v x : AmbientSpace) :
    (UpperHalfTensors.translateMotion v).invFun x = x - v := by
  simp [RigidMotion.invFun, UpperHalfTensors.translateMotion]
theorem timeReflection_apply_coord (y : AmbientSpace) (i : Fin 4) :
    TimeAxis.timeReflection y i = if i = timeIdx then - y i else y i := by
  fin_cases i <;> simp [TimeAxis.timeReflection, TimeAxis.timeIdx]
theorem smul_timeUnitVec_apply (c : ℝ) (i : Fin 4) :
    (c • timeUnitVec) i = if i = timeIdx then c else 0 := by
  by_cases h : i = timeIdx
  · subst h
    simp [timeUnitVec, PeriodicLattice.coordVec]
  · simp [timeUnitVec, PeriodicLattice.coordVec, h]
def slabMirror (c : ℝ) : RigidMotion :=
  ⟨RigidMotion.timeReflection.mat, RigidMotion.timeReflection.mat_mem, c • timeUnitVec⟩
theorem slabMirror_toFun (c : ℝ) (y : AmbientSpace) :
    (slabMirror c).toFun y = TimeAxis.timeReflection y + c • timeUnitVec := by
  have h := congrFun timeReflection_eq_toFun y
  rw [h]
  simp [RigidMotion.toFun, slabMirror, show RigidMotion.timeReflection.shift = 0 from rfl]
theorem slabMirror_apply (c : ℝ) (y : AmbientSpace) (i : Fin 4) :
    (slabMirror c).toFun y i = if i = timeIdx then c - y i else y i := by
  rw [slabMirror_toFun, Pi.add_apply, timeReflection_apply_coord, smul_timeUnitVec_apply]
  split_ifs <;> ring
theorem slabMirror_slabMirror (c : ℝ) (y : AmbientSpace) :
    (slabMirror c).toFun ((slabMirror c).toFun y) = y := by
  funext i
  rw [slabMirror_apply, slabMirror_apply]
  split_ifs <;> ring
theorem slabMirror_invFun (c : ℝ) : (slabMirror c).invFun = (slabMirror c).toFun := by
  funext u
  have h := (slabMirror c).invFun_toFun ((slabMirror c).toFun u)
  rwa [slabMirror_slabMirror] at h
theorem slabMirror_time (c : ℝ) (y : AmbientSpace) :
    (slabMirror c).toFun y timeIdx = c - y timeIdx := by
  simp [slabMirror_apply]
theorem comp_timeReflection_comp_slabMirror (c : ℝ) :
    (· ∘ (slabMirror c).invFun) ∘ (· ∘ RigidMotion.timeReflection.invFun) =
      ((· ∘ (UpperHalfTensors.translateMotion (c • timeUnitVec)).invFun) :
        (AmbientSpace → ℝ) → AmbientSpace → ℝ) := by
  funext f x
  simp only [comp_apply, slabMirror_invFun, translateMotion_invFun_apply,
    RigidMotion.timeReflection_invFun]
  congr 1
  funext i
  have := timeReflection_apply_coord ((slabMirror c).toFun x) i
  rw [show TestSpaces.timeReflect ((slabMirror c).toFun x) i = _ from this, slabMirror_apply,
    Pi.sub_apply, smul_timeUnitVec_apply]
  split_ifs <;> ring
theorem comp_translate_comp_slabMirror (c : ℝ) :
    (· ∘ (slabMirror c).invFun) ∘
        (· ∘ (UpperHalfTensors.translateMotion (c • timeUnitVec)).invFun) =
      ((· ∘ RigidMotion.timeReflection.invFun) : (AmbientSpace → ℝ) → AmbientSpace → ℝ) := by
  funext f x
  simp only [comp_apply, slabMirror_invFun, translateMotion_invFun_apply,
    RigidMotion.timeReflection_invFun]
  congr 1
  funext i
  have := timeReflection_apply_coord x i
  rw [show TestSpaces.timeReflect x i = _ from this, Pi.sub_apply, slabMirror_apply,
    smul_timeUnitVec_apply]
  split_ifs <;> ring
theorem push_timeReflection_mem {Y : SepTuple} (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) :
    push TimeAxis.timeReflection Y ∈ supportedIn {x : AmbientSpace | x timeIdx < 0} := by apply _root_.YangMills.Construction.OrthogonalAction.Laws.push_timeReflection_mem <;> assumption
theorem push_translate_mem {c : ℝ} {X : SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) :
    push (translate (c • timeUnitVec)) X ∈ supportedIn {x : AmbientSpace | c < x timeIdx} := by
  rw [translate_eq_toFun]
  refine push_mem_supportedIn _ hX fun x hx => ?_
  rw [translateMotion_invFun_apply] at hx
  have h : 0 < (x - c • timeUnitVec) timeIdx := hx
  rw [Pi.sub_apply, smul_timeUnitVec_apply] at h
  simpa using h
theorem timeSlab_subset_upperHalfSpace {c : ℝ} : timeSlab c ⊆ TimeAxis.upperHalfSpace :=
  fun _ hx => hx.1
theorem juxt_mem_supportedIn {A B : SepTuple} {O : Set AmbientSpace} (hd : SepTuple.Composable A B)
    (hA : A ∈ supportedIn O) (hB : B ∈ supportedIn O) : SepTuple.juxt A B ∈ supportedIn O := by
  intro f hf
  rw [SepTuple.juxt_val hd] at hf
  rcases List.mem_append.1 hf with h | h
  · exact hA f h
  · exact hB f h
theorem supportedIn_mono {O O' : Set AmbientSpace} (h : O ⊆ O') {X : SepTuple}
    (hX : X ∈ supportedIn O) : X ∈ supportedIn O' := fun f hf => (hX f hf).trans h
theorem composable_inner {c : ℝ} {H X : SepTuple} (hH : H ∈ supportedIn (timeSlab c))
    (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) :
    SepTuple.Composable H (push (translate (c • timeUnitVec)) X) :=
  composable_of_mem_supportedIn
    (Set.disjoint_left.2 fun _ hx hy => lt_asymm hx.2 hy) hH (push_translate_mem hX)
theorem inner_mem_upperHalfSpace {c : ℝ} (hc : 0 < c) {H X : SepTuple}
    (hH : H ∈ supportedIn (timeSlab c)) (hX : X ∈ supportedIn TimeAxis.upperHalfSpace) :
    SepTuple.juxt H (push (translate (c • timeUnitVec)) X) ∈
      supportedIn TimeAxis.upperHalfSpace :=
  juxt_mem_supportedIn (composable_inner hH hX)
    (supportedIn_mono timeSlab_subset_upperHalfSpace hH)
    (supportedIn_mono (fun _ hx => lt_trans hc hx) (push_translate_mem hX))
theorem composable_outer {c : ℝ} (hc : 0 < c) {H X Y : SepTuple}
    (hH : H ∈ supportedIn (timeSlab c)) (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) :
    SepTuple.Composable (push TimeAxis.timeReflection Y)
      (SepTuple.juxt H (push (translate (c • timeUnitVec)) X)) :=
  composable_of_mem_supportedIn (O := {x : AmbientSpace | x timeIdx < 0})
    (O' := TimeAxis.upperHalfSpace)
    (Set.disjoint_left.2 fun x hx hy => lt_asymm hx (show 0 < x timeIdx from hy))
    (push_timeReflection_mem hY) (inner_mem_upperHalfSpace hc hH hX)
theorem slabMirror_mem_timeSlab {c : ℝ} {y : AmbientSpace} (hy : y ∈ timeSlab c) :
    (slabMirror c).toFun y ∈ timeSlab c := by
  have h₁ : 0 < y timeIdx := hy.1
  have h₂ : y timeIdx < c := hy.2
  refine ⟨?_, ?_⟩ <;> rw [slabMirror_time] <;> linarith
theorem eval_reflected_juxt (hs : IsSymmetricInvariant σ) {c : ℝ} (hc : 0 < c)
    {X Y H H' : SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) {g : AmbientSpace → ℝ} (hH : H.1 = [g])
    (hH' : H'.1 = [g ∘ (slabMirror c).toFun]) (hHs : H ∈ supportedIn (timeSlab c))
    (hHs' : H' ∈ supportedIn (timeSlab c)) :
    σ (ofList (SepTuple.juxt (push TimeAxis.timeReflection Y)
        (SepTuple.juxt H (push (translate (c • timeUnitVec)) X)))) =
      σ (ofList (SepTuple.juxt (push TimeAxis.timeReflection X)
        (SepTuple.juxt H' (push (translate (c • timeUnitVec)) Y)))) := by
  set P := SepTuple.juxt (push TimeAxis.timeReflection Y)
    (SepTuple.juxt H (push (translate (c • timeUnitVec)) X)) with hP
  set Q := SepTuple.juxt (push TimeAxis.timeReflection X)
    (SepTuple.juxt H' (push (translate (c • timeUnitVec)) Y)) with hQ
  have hPv : P.1 = (push TimeAxis.timeReflection Y).1 ++
      (g :: (push (translate (c • timeUnitVec)) X).1) := by
    rw [hP, SepTuple.juxt_val (composable_outer hc hHs hX hY),
      SepTuple.juxt_val (composable_inner hHs hX), hH]
    rfl
  have hQv : Q.1 = (push TimeAxis.timeReflection X).1 ++
      ((g ∘ (slabMirror c).toFun) :: (push (translate (c • timeUnitVec)) Y).1) := by
    rw [hQ, SepTuple.juxt_val (composable_outer hc hHs' hY hX),
      SepTuple.juxt_val (composable_inner hHs' hY), hH']
    rfl
  have hR : (push (slabMirror c).toFun P).1 = (push (translate (c • timeUnitVec)) Y).1 ++
      ((g ∘ (slabMirror c).toFun) :: (push TimeAxis.timeReflection X).1) := by
    rw [push_val, hPv, List.map_append, List.map_cons]
    rw [timeReflection_eq_toFun, translate_eq_toFun, push_val, push_val, push_val, push_val,
      List.map_map, List.map_map, comp_timeReflection_comp_slabMirror,
      comp_translate_comp_slabMirror, slabMirror_invFun]
  have h₁ : σ (ofList (push (slabMirror c).toFun P)) = σ (ofList P) :=
    eval_motion hs.2 (slabMirror c) (push_val _ _)
  have h₂ : σ (ofList (push (slabMirror c).toFun P)) = σ (ofList Q) := by
    refine eval_eq_of_perm hs.1 ?_ (by rw [hR]; simp)
    rw [hR, hQv]
    exact List.perm_middle.trans ((List.perm_append_comm.cons _).trans List.perm_middle.symm)
  rw [← h₁, h₂]
theorem formalSpan_induction {O : Set AmbientSpace} {p : FormalSpan → Prop}
    (hX : ∀ X ∈ supportedIn O, p (basisVec X)) (h0 : p 0)
    (hadd : ∀ A B, p A → p B → p (A + B)) (hsmul : ∀ (z : ℂ) A, p A → p (z • A))
    {F : FormalSpan} (hF : F ∈ spanIn O) : p F := by
  refine Submodule.span_induction (p := fun A _ => p A) ?_ h0 (fun A B _ _ => hadd A B)
    (fun z A _ => hsmul z A) hF
  rintro _ ⟨X, rfl⟩
  exact hX X.1 X.2
theorem basisVec_mem_spanIn {O : Set AmbientSpace} {X : SepTuple} (h : X ∈ supportedIn O) :
    basisVec X ∈ spanIn O :=
  Submodule.subset_span ⟨⟨X, h⟩, rfl⟩
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ _
theorem pushSpan_translate_mem {c : ℝ} (hc : 0 < c) {A : FormalSpan}
    (hA : A ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate (c • timeUnitVec)) A ∈ spanIn TimeAxis.upperHalfSpace := by
  refine formalSpan_induction (O := TimeAxis.upperHalfSpace)
    (p := fun A => pushSpan (translate (c • timeUnitVec)) A ∈ spanIn TimeAxis.upperHalfSpace)
    (fun X hX => ?_) ?_ (fun A B hA hB => ?_) (fun z A hA => ?_) hA
  · rw [pushSpan_basisVec]
    exact basisVec_mem_spanIn (supportedIn_mono (fun _ hx => lt_trans hc hx) (push_translate_mem hX))
  · rw [map_zero]
    exact Submodule.zero_mem _
  · rw [map_add]
    exact Submodule.add_mem _ hA hB
  · rw [map_smul]
    exact Submodule.smul_mem _ z hA
theorem shiftedSpan_val {c : ℝ} (hc : 0 < c) (F : PositiveSpan) :
    (shiftedSpan (c • timeUnitVec) F).1 = pushSpan (translate (c • timeUnitVec)) F.1 := by
  rw [shiftedSpan, dif_pos (pushSpan_translate_mem hc F.2)]
theorem insertion_mem_spanIn {c : ℝ} (hc : 0 < c) {H : SepTuple}
    (hH : H ∈ supportedIn (timeSlab c)) {A : FormalSpan}
    (hA : A ∈ spanIn TimeAxis.upperHalfSpace) :
    formalMul (basisVec H) (pushSpan (translate (c • timeUnitVec)) A) ∈
      spanIn TimeAxis.upperHalfSpace := by
  refine formalSpan_induction (O := TimeAxis.upperHalfSpace)
    (p := fun A => formalMul (basisVec H)
      (pushSpan (translate (c • timeUnitVec)) A) ∈ spanIn TimeAxis.upperHalfSpace)
    (fun X hX => ?_) ?_ (fun A B hA hB => ?_) (fun z A hA => ?_) hA
  · rw [pushSpan_basisVec, formalMul_basisVec]
    exact basisVec_mem_spanIn (inner_mem_upperHalfSpace hc hH hX)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · simp only [map_add]
    exact Submodule.add_mem _ hA hB
  · simp only [map_smul]
    exact Submodule.smul_mem _ z hA
def insertedPairing (σ : TestSpaces.SepTuple → ℝ) (c : ℝ) (H : SepTuple) (A B : FormalSpan) :
    ℂ :=
  WightmanReconstruction.linearExtension σ
    (formalMul (pushSpan TimeAxis.timeReflection (conjugation A))
      (formalMul (basisVec H) (pushSpan (translate (c • timeUnitVec)) B)))
theorem insertedPairing_basisVec (c : ℝ) (H X Y : SepTuple) :
    insertedPairing σ c H (basisVec Y) (basisVec X) =
      (σ (ofList (SepTuple.juxt (push TimeAxis.timeReflection Y)
        (SepTuple.juxt H (push (translate (c • timeUnitVec)) X)))) : ℂ) := by
  simp only [insertedPairing, conjugation_basisVec, pushSpan_basisVec, formalMul_basisVec,
    WightmanReconstruction.linearExtension, linearExtend_basisVec]
theorem insertedPairing_zero_left (c : ℝ) (H : SepTuple) (B : FormalSpan) :
    insertedPairing σ c H 0 B = 0 := by
  simp [insertedPairing]
theorem insertedPairing_zero_right (c : ℝ) (H : SepTuple) (A : FormalSpan) :
    insertedPairing σ c H A 0 = 0 := by
  simp [insertedPairing]
theorem insertedPairing_add_left (c : ℝ) (H : SepTuple) (A₁ A₂ B : FormalSpan) :
    insertedPairing σ c H (A₁ + A₂) B =
      insertedPairing σ c H A₁ B + insertedPairing σ c H A₂ B := by
  simp [insertedPairing, map_add, LinearMap.add_apply]
theorem insertedPairing_add_right (c : ℝ) (H : SepTuple) (A B₁ B₂ : FormalSpan) :
    insertedPairing σ c H A (B₁ + B₂) =
      insertedPairing σ c H A B₁ + insertedPairing σ c H A B₂ := by
  simp [insertedPairing, map_add]
theorem insertedPairing_smul_left (c : ℝ) (H : SepTuple) (z : ℂ) (A B : FormalSpan) :
    insertedPairing σ c H (z • A) B = conj z * insertedPairing σ c H A B := by
  simp [insertedPairing, map_smulₛₗ, LinearMap.smul_apply]
theorem insertedPairing_smul_right (c : ℝ) (H : SepTuple) (z : ℂ) (A B : FormalSpan) :
    insertedPairing σ c H A (z • B) = z * insertedPairing σ c H A B := by
  simp [insertedPairing, map_smul]
theorem conj_insertedPairing (hs : IsSymmetricInvariant σ) {c : ℝ} (hc : 0 < c)
    {g : AmbientSpace → ℝ} {H H' : SepTuple} (hH : H.1 = [g])
    (hH' : H'.1 = [g ∘ (slabMirror c).toFun])
    (hHs : H ∈ supportedIn (timeSlab c)) (hHs' : H' ∈ supportedIn (timeSlab c)) {A B : FormalSpan}
    (hA : A ∈ spanIn TimeAxis.upperHalfSpace)
    (hB : B ∈ spanIn TimeAxis.upperHalfSpace) :
    conj (insertedPairing σ c H A B) = insertedPairing σ c H' B A := by
  refine formalSpan_induction (O := TimeAxis.upperHalfSpace)
    (p := fun B => ∀ A ∈ spanIn TimeAxis.upperHalfSpace,
      conj (insertedPairing σ c H A B) = insertedPairing σ c H' B A)
    (fun X hX A hA => ?_) (fun A _ => ?_) (fun B₁ B₂ h₁ h₂ A hA => ?_) (fun z B h A hA => ?_)
    hB A hA
  · refine formalSpan_induction (O := TimeAxis.upperHalfSpace)
      (p := fun A => conj (insertedPairing σ c H A (basisVec X)) =
        insertedPairing σ c H' (basisVec X) A)
      (fun Y hY => ?_) ?_ (fun A₁ A₂ h₁ h₂ => ?_) (fun z A h => ?_) hA
    · rw [insertedPairing_basisVec, insertedPairing_basisVec, Complex.conj_ofReal,
        eval_reflected_juxt hs hc hX hY hH hH' hHs hHs']
    · rw [insertedPairing_zero_left, insertedPairing_zero_right, map_zero]
    · rw [insertedPairing_add_left, insertedPairing_add_right, map_add, h₁, h₂]
    · rw [insertedPairing_smul_left, insertedPairing_smul_right, map_mul, Complex.conj_conj, h]
  · rw [insertedPairing_zero_right, insertedPairing_zero_left, map_zero]
  · rw [insertedPairing_add_right, insertedPairing_add_left, map_add, h₁ A hA, h₂ A hA]
  · rw [insertedPairing_smul_right, insertedPairing_smul_left, map_mul, h A hA]
structure IsRealSlabTest (c : ℝ) (g : AmbientSpace → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 g
  hasCompactSupport : HasCompactSupport g
  tsupport_subset : tsupport g ⊆ timeSlab c
theorem IsRealSlabTest.comp_slabMirror {c : ℝ} {g : AmbientSpace → ℝ} (hg : IsRealSlabTest c g) :
    IsRealSlabTest c (g ∘ (slabMirror c).toFun) := by
  have hcd : ContDiff ℝ 1 (slabMirror c).toFun := by
    rw [← slabMirror_invFun]
    exact UpperHalfTensors.contDiff_invFun _
  refine ⟨hg.contDiff.comp hcd,
    hg.hasCompactSupport.comp_homeomorph (UpperHalfTensors.rigidHomeomorph _), fun y hy => ?_⟩
  have h := tsupport_comp_subset_preimage g hcd.continuous hy
  have h' := slabMirror_mem_timeSlab (hg.tsupport_subset h)
  rwa [slabMirror_slabMirror] at h'
theorem IsRealSlabTest.singleton_mem_sepAll {c : ℝ} {g : AmbientSpace → ℝ}
    (hg : IsRealSlabTest c g) : [g] ∈ EuclideanFunctionals.sepAll :=
  ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ 1
    (EuclideanFunctionals.CenteredInitialValues.single_mem_sepN
      (by
        change g ∈ ReflectionPositivity.AxisMirror.Ambient.compactC1
          EuclideanFunctionals.defaultMirrorData ℝ ReflectionPositivity.AxisMirror.Ambient.euclidean
        rw [← FourSpace.C1c_eq_compactC1]
        exact ⟨hg.contDiff, hg.hasCompactSupport⟩))
def IsRealSlabTest.single {c : ℝ} {g : AmbientSpace → ℝ} (hg : IsRealSlabTest c g) : SepTuple :=
  WightmanReconstruction.toSepTuple ⟨[g], hg.singleton_mem_sepAll⟩
theorem IsRealSlabTest.single_val {c : ℝ} {g : AmbientSpace → ℝ} (hg : IsRealSlabTest c g) :
    hg.single.1 = [g] :=
  rfl
theorem IsRealSlabTest.single_mem {c : ℝ} {g : AmbientSpace → ℝ} (hg : IsRealSlabTest c g) :
    hg.single ∈ supportedIn (timeSlab c) := by
  intro f hf
  rw [hg.single_val, List.mem_singleton] at hf
  rw [hf]
  exact hg.tsupport_subset
theorem tsupport_ofReal_comp (g : AmbientSpace → ℝ) :
    tsupport (fun y => (g y : ℂ)) = tsupport g := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem IsRealSlabTest.ofReal_mem_c1CompactSupp {c : ℝ} {g : AmbientSpace → ℝ}
    (hg : IsRealSlabTest c g) :
    (fun y => (g y : ℂ)) ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hg.contDiff, ?_, Set.subset_univ _⟩
  rw [HasCompactSupport, tsupport_ofReal_comp]
  exact hg.hasCompactSupport
theorem IsRealSlabTest.integrable_mul {c : ℝ} {g : AmbientSpace → ℝ} (hg : IsRealSlabTest c g)
    {w : AmbientSpace → ℂ} (hw : ContinuousOn w (timeSlab c)) :
    Integrable (fun y => (g y : ℂ) * w y) := by
  have hcont : ContinuousOn (fun y => (g y : ℂ) * w y) (tsupport g) :=
    (Complex.continuous_ofReal.comp hg.contDiff.continuous).continuousOn.mul
      (hw.mono hg.tsupport_subset)
  refine (hcont.integrableOn_compact hg.hasCompactSupport).integrable_of_forall_notMem_eq_zero
    fun x hx => ?_
  simp [image_eq_zero_of_notMem_tsupport hx]
theorem integral_inner_eq_insertedPairing
    (hinner : ∀ F K : PositiveSpan,
      ⟪stateOf σ F, stateOf σ K⟫_ℂ = FieldFormConditions.pairing σ F K)
    {E : FourBorelSet → BddOp (StateSpace σ)}
    {G : ℝ → (Fin 4 → ℝ) → BddOp (StateSpace σ)} (hG : IsFieldDensity σ E G)
    {c : ℝ} (hc : 0 < c) {g : AmbientSpace → ℝ} (hg : IsRealSlabTest c g) (F F' : PositiveSpan) :
    ∫ y, (g y : ℂ) * ⟪stateOf σ F', G c y (stateOf σ F)⟫_ℂ =
      insertedPairing σ c hg.single F'.1 F.1 := by
  have hi := hG.inner_insertedState c (fun y => (g y : ℂ)) F (stateOf σ F') hc
    hg.ofReal_mem_c1CompactSupp (by rw [tsupport_ofReal_comp]; exact hg.tsupport_subset)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]] at hi
  rw [← hi]
  have key : formalMul (WightmanReconstruction.complexTuple fun y => (g y : ℂ))
      (shiftedSpan (c • timeUnitVec) F).1 =
      formalMul (basisVec hg.single) (pushSpan (translate (c • timeUnitVec)) F.1) := by
    rw [WightmanReconstruction.complexTuple_ofReal g hg.singleton_mem_sepAll, shiftedSpan_val hc]
    rfl
  have hm : formalMul (WightmanReconstruction.complexTuple fun y => (g y : ℂ))
      (shiftedSpan (c • timeUnitVec) F).1 ∈ spanIn TimeAxis.upperHalfSpace := by
    rw [key]
    exact insertion_mem_spanIn hc hg.single_mem F.2
  rw [insertedState, dif_pos hm, hinner]
  change WightmanReconstruction.linearExtension σ (formalMul (reflectConj F')
    (formalMul (WightmanReconstruction.complexTuple fun y => (g y : ℂ))
      (shiftedSpan (c • timeUnitVec) F).1)) = _
  rw [key]
  rfl
theorem measurePreserving_slabMirror (c : ℝ) :
    MeasurePreserving (slabMirror c).toFun (volume : Measure AmbientSpace) volume := by
  classical
  let f : Fin 4 → ℝ → ℝ := fun i => if i = timeIdx then fun a => c - a else id
  have hf : ∀ i, MeasurePreserving (f i) volume volume := by
    intro i
    by_cases h : i = timeIdx
    · simp only [f, h, if_true]
      exact Measure.measurePreserving_sub_left volume c
    · simp only [f, h, if_false]
      exact MeasurePreserving.id _
  have he : (slabMirror c).toFun = fun (a : AmbientSpace) i => f i (a i) := by
    funext a i
    rw [slabMirror_apply]
    by_cases h : i = timeIdx <;> simp [f, h]
  rw [he]
  exact volume_preserving_pi hf
theorem integral_comp_slabMirror (c : ℝ) (φ : AmbientSpace → ℂ) :
    ∫ y, φ ((slabMirror c).toFun y) = ∫ y, φ y :=
  (measurePreserving_slabMirror c).integral_comp
    (UpperHalfTensors.rigidHomeomorph (slabMirror c)).measurableEmbedding φ
theorem isOpen_timeSlab (c : ℝ) : IsOpen (timeSlab c) :=
  (isOpen_lt continuous_const (continuous_apply _)).inter
    (isOpen_lt (continuous_apply _) continuous_const)
theorem slabMirror_fixes_midpoint (s : ℝ) :
    (slabMirror (2 * s)).toFun (s • timeUnitVec) = s • timeUnitVec := by
  funext i
  rw [slabMirror_apply]
  by_cases h : i = timeIdx
  · simp only [h, if_true, smul_timeUnitVec_apply]
    ring
  · simp only [h, if_false]
theorem conj_inner_midpointField
    (hinner : ∀ F K : PositiveSpan,
      ⟪stateOf σ F, stateOf σ K⟫_ℂ = FieldFormConditions.pairing σ F K)
    (hsym : IsSymmetricInvariant σ)
    {E : FourBorelSet → BddOp (StateSpace σ)}
    {G : ℝ → (Fin 4 → ℝ) → BddOp (StateSpace σ)} (hG : IsFieldDensity σ E G)
    {s : ℝ} (hs : 0 < s) (F F' : PositiveSpan) :
    conj ⟪stateOf σ F', midpointField σ G s (stateOf σ F)⟫_ℂ =
      ⟪stateOf σ F, midpointField σ G s (stateOf σ F')⟫_ℂ := by
  set c : ℝ := 2 * s with hcdef
  have hc : 0 < c := by positivity
  set a : AmbientSpace → ℂ := fun y => ⟪stateOf σ F', G c y (stateOf σ F)⟫_ℂ with ha_def
  set b : AmbientSpace → ℂ := fun y => ⟪stateOf σ F, G c y (stateOf σ F')⟫_ℂ with hb_def
  have ha : ContinuousOn a (timeSlab c) := hG.continuousOn_inner c _ _ hc
  have hb : ContinuousOn b (timeSlab c) := hG.continuousOn_inner c _ _ hc
  have hmc : Continuous (slabMirror c).toFun :=
    (UpperHalfTensors.rigidHomeomorph (slabMirror c)).continuous
  have hbm : ContinuousOn (fun y => b ((slabMirror c).toFun y)) (timeSlab c) :=
    hb.comp hmc.continuousOn fun y hy => slabMirror_mem_timeSlab hy
  have hac : ContinuousOn (fun y => conj (a y)) (timeSlab c) :=
    Complex.continuous_conj.comp_continuousOn ha
  set u : AmbientSpace → ℂ := fun y => conj (a y) - b ((slabMirror c).toFun y) with hu_def
  have hu : ContinuousOn u (timeSlab c) := hac.sub hbm
  have hzero : ∀ g : AmbientSpace → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ timeSlab c → ∫ y, g y • u y = 0 := by
    intro g hgs hgc hgt
    have hg : IsRealSlabTest c g := ⟨hgs.of_le (by exact_mod_cast le_top), hgc, hgt⟩
    have h₁ := integral_inner_eq_insertedPairing hinner hG hc hg F F'
    have h₂ := integral_inner_eq_insertedPairing hinner hG hc hg.comp_slabMirror F' F
    have h₃ := conj_insertedPairing hsym hc hg.single_val hg.comp_slabMirror.single_val
      hg.single_mem hg.comp_slabMirror.single_mem F'.2 F.2
    have h₄ : ∫ y, (g y : ℂ) * conj (a y) = conj (∫ y, (g y : ℂ) * a y) := by
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp
    have h₅ : ∫ y, (g y : ℂ) * b ((slabMirror c).toFun y) =
        ∫ y, ((g ∘ (slabMirror c).toFun) y : ℂ) * b y := by
      rw [← integral_comp_slabMirror c fun y => ((g ∘ (slabMirror c).toFun) y : ℂ) * b y]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [slabMirror_slabMirror]
    have h₆ : ∀ y, g y • u y =
        (g y : ℂ) * conj (a y) - (g y : ℂ) * b ((slabMirror c).toFun y) := by
      intro y
      rw [Complex.real_smul, hu_def, mul_sub]
    simp only [h₆]
    rw [integral_sub (hg.integrable_mul hac) (hg.integrable_mul hbm), h₄, h₅, h₁, h₂, h₃,
      sub_self]
  have hae := (isOpen_timeSlab c).ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hu.locallyIntegrableOn (isOpen_timeSlab c).measurableSet) hzero
  have hEq := Measure.eqOn_open_of_ae_eq (μ := volume) (f := u) (g := fun _ => 0)
    ((ae_restrict_iff' (isOpen_timeSlab c).measurableSet).2 hae) (isOpen_timeSlab c) hu
    continuousOn_const
  have hy : s • timeUnitVec ∈ timeSlab c := by
    refine ⟨?_, ?_⟩ <;> simp only [smul_timeUnitVec_apply, if_true] <;> linarith
  have h := hEq hy
  simp only [hu_def, hcdef, slabMirror_fixes_midpoint] at h
  exact sub_eq_zero.1 h
theorem adjointOp_eq_self_of_symm {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] {A : BddOp X} (h : ∀ χ χ', ⟪A χ, χ'⟫_ℂ = ⟪χ, A χ'⟫_ℂ) :
    adjointOp A = A := by
  have hs : IsAdjointOp A (adjointOp A) :=
    Classical.epsilon_spec (p := IsAdjointOp A) ⟨A, h⟩
  refine ContinuousLinearMap.ext fun χ => ext_inner_right ℂ fun χ' => ?_
  rw [hs χ χ', h]
theorem pairing_isPosSemidefHermitianForm (hh : HilbertCompletionExtensionRiesz)
    (hp : PairingPosSemidef σ) :
    FormCompletion.IsPosSemidefHermitianForm (FieldFormConditions.pairing σ) := by
  have hq : SesquilinearForms.IsPosSemidefForm (FieldFormConditions.pairing σ) := hp
  have hherm := (hh.1 _ _ hq).1
  exact ⟨hq.add_left, hq.smul_left, hq.add_right, hq.smul_right, hherm.conj_symm,
    fun F => (Complex.nonneg_iff.1 (hq.nonneg F)).1⟩
theorem midpointSelfAdjointStatement_holds (hc : FormCompletion.FormCompletionIsHilbertSpace)
    (hh : HilbertCompletionExtensionRiesz) : MidpointSelfAdjointStatement := by
  intro σ E p C hcond G hG s hs
  have hq := pairing_isPosSemidefHermitianForm hh hcond.posSemidef
  obtain ⟨-, hcomp, -⟩ := hc _ (FieldFormConditions.pairing σ) hq
  obtain ⟨-, -, -, -, -, -, hinner, -, hdense⟩ := hcomp
  have hcl : ∀ F, stateOf σ F = FormCompletion.classVec (FieldFormConditions.pairing σ) F :=
    fun _ => rfl
  have hsymm := conj_inner_midpointField (σ := σ) (fun F K => hinner F K)
    hcond.symmInvariant hG hs
  refine adjointOp_eq_self_of_symm fun χ χ' => ?_
  have hd : DenseRange (FormCompletion.classVec (FieldFormConditions.pairing σ)) := hdense
  refine hd.induction_on₂
    (p := fun χ χ' => ⟪midpointField σ G s χ, χ'⟫_ℂ = ⟪χ, midpointField σ G s χ'⟫_ℂ)
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun F F' => ?_) χ χ'
  have h := hsymm F F'
  rw [inner_conj_symm] at h
  exact h
end YangMills.Construction.MidpointSelfAdjoint
end
