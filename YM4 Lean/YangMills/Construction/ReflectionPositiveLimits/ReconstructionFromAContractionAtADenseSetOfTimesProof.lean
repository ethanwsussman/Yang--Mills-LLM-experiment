import YangMills.Construction.EnergyMomentum.SemigroupGenerators
import YangMills.Construction.HilbertSpace.BoundedOperatorFacts
import YangMills.Construction.ReflectionPositiveLimits.MovingTestFunctions
import YangMills.Construction.ReflectionPositiveLimits.VacuumErgodicityAndClusteringInTime
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DenseTimeReconstruction
open YangMills.Construction.ReflectionPositivity YangMills.Construction.EnergyMomentum
open YangMills.Construction.EuclideanSpectral YangMills.Construction.PeriodicLattice
open YangMills.Construction.ReflectionPositivity.EuclidIsometry
def timeReflect (v : Space) : Space := v - (2 * v timeAxis) • coordVec timeAxis
theorem reflectIso_toFun_eq_timeReflect (x : Space) :
    timeZeroMirror.reflectIso.toFun x = timeReflect x :=
  timeZeroMirror_reflectIso x
theorem coordVec_timeAxis_self :
    (coordVec timeAxis : Space) timeAxis = 1 := by
  simp [coordVec]
theorem timeReflect_timeAxis (v : Space) : timeReflect v timeAxis = -v timeAxis := by
  simp only [timeReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coordVec_timeAxis_self]
  ring
theorem timeReflect_sub (v w : Space) : timeReflect (v - w) = timeReflect v - timeReflect w := by
  funext ν
  simp only [timeReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem timeReflect_timeReflect (v : Space) : timeReflect (timeReflect v) = v := by
  funext ν
  have hv := timeReflect_timeAxis v
  simp only [timeReflect] at hv ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hv ⊢
  rw [hv]
  ring
theorem timeReflect_of_timeAxis_eq_zero {v : Space} (hv : v timeAxis = 0) : timeReflect v = v := by
  simp [timeReflect, hv]
theorem reflectIso_symm_toFun (x : Space) :
    timeZeroMirror.reflectIso.symm.toFun x = timeReflect x := by
  apply timeZeroMirror.reflectIso.bijective_toFun.1
  rw [toFun_symm, reflectIso_toFun_eq_timeReflect, timeReflect_timeReflect]
theorem push_translate_translate (v w : Space) (X : Tuple) :
    push (translate v) (push (translate w) X) = push (translate (v + w)) X := by
  apply Subtype.ext
  rw [push_translate, push_translate, push_translate, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp [sub_sub]
theorem push_translate_zero (X : Tuple) : push (translate 0) X = X := by
  apply Subtype.ext
  rw [push_translate]
  simp
theorem push_reflectIso_translate (a : Space) (X : Tuple) :
    push timeZeroMirror.reflectIso (push (translate a) X) =
      push (translate (timeReflect a)) (push timeZeroMirror.reflectIso X) := by
  apply Subtype.ext
  change ((X.1.map (pushFn (translate a))).map (pushFn timeZeroMirror.reflectIso)) =
    ((X.1.map (pushFn timeZeroMirror.reflectIso)).map (pushFn (translate (timeReflect a))))
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp only [Function.comp_apply, pushFn, reflectIso_symm_toFun, symm_translate, timeReflect_sub,
    timeReflect_timeReflect]
theorem push_nilTuple (r : EuclidIsometry) : push r nilTuple = nilTuple :=
  Subtype.ext rfl
theorem tupleComb_linearMap_ext {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {f g : TupleComb →ₗ[ℂ] M} (hfg : ∀ X, f (basisOf X) = g (basisOf X)) : f = g :=
  Finsupp.lhom_ext' fun X => LinearMap.ext_ring (hfg X)
theorem pushComb_basisOf (r : EuclidIsometry) (X : Tuple) :
    pushComb r (basisOf X) = basisOf (push r X) := by
  simp [pushComb, basisOf]
theorem pushComb_translate_translate (v w : Space) (Z : TupleComb) :
    pushComb (translate v) (pushComb (translate w) Z) = pushComb (translate (v + w)) Z := by
  have e : pushComb (translate v) ∘ₗ pushComb (translate w) = pushComb (translate (v + w)) :=
    tupleComb_linearMap_ext fun X => by
      simp [pushComb_basisOf, push_translate_translate]
  exact LinearMap.congr_fun e Z
theorem pushComb_translate_zero (Z : TupleComb) : pushComb (translate 0) Z = Z := by
  have e : pushComb (translate 0) = LinearMap.id :=
    tupleComb_linearMap_ext fun X => by simp [pushComb_basisOf, push_translate_zero]
  exact LinearMap.congr_fun e Z
theorem pushComb_reflectIso_translate (a : Space) (Z : TupleComb) :
    pushComb timeZeroMirror.reflectIso (pushComb (translate a) Z) =
      pushComb (translate (timeReflect a)) (pushComb timeZeroMirror.reflectIso Z) := by
  have e : pushComb timeZeroMirror.reflectIso ∘ₗ pushComb (translate a) =
      pushComb (translate (timeReflect a)) ∘ₗ pushComb timeZeroMirror.reflectIso :=
    tupleComb_linearMap_ext fun X => by
      simp [pushComb_basisOf, push_reflectIso_translate]
  exact LinearMap.congr_fun e Z
theorem single_eq_smul_basisOf (X : Tuple) (a : ℂ) :
    (Finsupp.single X a : TupleComb) = a • basisOf X := by
  simp [basisOf]
theorem conjComb_pushComb (r : EuclidIsometry) (Z : TupleComb) :
    conjComb (pushComb r Z) = pushComb r (conjComb Z) := by
  induction Z using Finsupp.induction_linear with
  | zero => simp [conjComb]
  | add Z Z' hZ hZ' => simp only [map_add, conjComb_add, hZ, hZ']
  | single X a =>
    rw [single_eq_smul_basisOf, map_smul, conjComb_smul, conjComb_smul, map_smul,
      pushComb_basisOf]
    have e : ∀ Y, conjComb (basisOf Y) = basisOf Y := fun Y => by
      simp [conjComb, basisOf]
    rw [e, e, pushComb_basisOf]
theorem concatenable_push_iff (r : EuclidIsometry) (X Y : Tuple) :
    Concatenable (push r X) (push r Y) ↔ Concatenable X Y := by
  constructor
  · intro hc f hf g hg
    have h₁ := hc (pushFn r f) (List.mem_map_of_mem hf) (pushFn r g)
      (List.mem_map_of_mem hg)
    rw [tsupport_pushFn, tsupport_pushFn] at h₁
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have a₁ : r.toFun x ∈ r.symm.toFun ⁻¹' tsupport f := by simpa [symm_toFun] using hx
    have a₂ : r.toFun x ∈ r.symm.toFun ⁻¹' tsupport g := by simpa [symm_toFun] using hx'
    exact Set.disjoint_left.1 h₁ a₁ a₂
  · intro hc g hg g' hg'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hg'
    rw [tsupport_pushFn, tsupport_pushFn]
    exact (hc f hf f' hf').preimage _
theorem concatBilin_basisOf (X Y : Tuple) :
    concatBilin (basisOf X) (basisOf Y) = concatBasis X Y := by
  simp [concatBilin, basisOf]
theorem pushComb_concatBasis (r : EuclidIsometry) (X Y : Tuple) :
    pushComb r (concatBasis X Y) = concatBasis (push r X) (push r Y) := by
  by_cases hd : Concatenable X Y
  · have hd' := (concatenable_push_iff r X Y).2 hd
    simp only [concatBasis, dif_pos hd, dif_pos hd', pushComb_basisOf]
    congr 1
    apply Subtype.ext
    simp [push, concat]
  · have hd' := fun hc => hd ((concatenable_push_iff r X Y).1 hc)
    simp [concatBasis, dif_neg hd, dif_neg hd']
theorem pushComb_concatBilin (r : EuclidIsometry) (A B : TupleComb) :
    pushComb r (concatBilin A B) = concatBilin (pushComb r A) (pushComb r B) := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A A' hA hA' => simp only [map_add, LinearMap.add_apply, hA, hA']
  | single X a =>
    induction B using Finsupp.induction_linear with
    | zero => simp
    | add B B' hB hB' => simp only [map_add, hB, hB']
    | single Y b =>
      rw [single_eq_smul_basisOf, single_eq_smul_basisOf]
      simp only [map_smul, LinearMap.smul_apply, concatBilin_basisOf,
        pushComb_basisOf, pushComb_concatBasis]
theorem linearExt_basisOf (σ : Tuple → ℝ) (X : Tuple) :
    linearExt σ (basisOf X) = (σ X : ℂ) := by
  simp [linearExt, basisOf]
theorem linearExt_pushComb {σ : Tuple → ℝ} {r : EuclidIsometry}
    (hr : IsIsomInvariant r σ) (C : TupleComb) :
    linearExt σ (pushComb r C) = linearExt σ C := by
  have e : linearExt σ ∘ₗ pushComb r = linearExt σ :=
    tupleComb_linearMap_ext fun X => by
      simp [pushComb_basisOf, linearExt_basisOf, hr X]
  exact LinearMap.congr_fun e C
theorem translateComb_congr {v w : Space} (e : v = w) (hv : 0 ≤ v timeAxis)
    (hw : 0 ≤ w timeAxis) (Z : combsSupportedIn upperHalfSpace) :
    translateComb v hv Z = translateComb w hw Z := by
  subst e
  rfl
theorem translateComb_translateComb (v w : Space) (hv : 0 ≤ v timeAxis)
    (hw : 0 ≤ w timeAxis) (hs : 0 ≤ (v + w) timeAxis)
    (Z : combsSupportedIn upperHalfSpace) :
    translateComb v hv (translateComb w hw Z) = translateComb (v + w) hs Z :=
  Subtype.ext (pushComb_translate_translate v w Z)
theorem translateComb_zero (h0 : 0 ≤ (0 : Space) timeAxis)
    (Z : combsSupportedIn upperHalfSpace) : translateComb 0 h0 Z = Z :=
  Subtype.ext (pushComb_translate_zero Z)
def translateLinearMap (v : Space) (hv : 0 ≤ v timeAxis) :
    combsSupportedIn upperHalfSpace →ₗ[ℂ] combsSupportedIn upperHalfSpace :=
  (pushComb (translate v)).restrict fun _ hZ => pushComb_translate_mem hv hZ
theorem reflForm_translateComb {σ : Tuple → ℝ} (hσ : IsTranslInvariant σ)
    (a b : Space) (ha : 0 ≤ a timeAxis) (hb : 0 ≤ b timeAxis)
    (hc : 0 ≤ (b - timeReflect a) timeAxis) (Z W : combsSupportedIn upperHalfSpace) :
    reflForm σ (translateComb a ha Z) (translateComb b hb W) =
      reflForm σ Z (translateComb (b - timeReflect a) hc W) := by
  change linearExt σ (concatBilin
      (pushComb timeZeroMirror.reflectIso
        (conjComb (pushComb (translate a) (Z : TupleComb))))
      (pushComb (translate b) (W : TupleComb))) =
    linearExt σ (concatBilin
      (pushComb timeZeroMirror.reflectIso (conjComb (Z : TupleComb)))
      (pushComb (translate (b - timeReflect a)) (W : TupleComb)))
  have e : pushComb (translate b) (W : TupleComb) =
      pushComb (translate (timeReflect a))
        (pushComb (translate (b - timeReflect a)) (W : TupleComb)) := by
    rw [pushComb_translate_translate, add_sub_cancel]
  rw [conjComb_pushComb, pushComb_reflectIso_translate, e,
    ← pushComb_concatBilin, linearExt_pushComb (hσ _)]
theorem reflForm_tupleToComb (σ : Tuple → ℝ) (X Y : Tuple)
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace)
    (hd : Concatenable (push timeZeroMirror.reflectIso X) Y) :
    reflForm σ (tupleToComb X hX) (tupleToComb Y hY) =
      (σ (concat (push timeZeroMirror.reflectIso X) Y hd) : ℂ) := by
  change linearExt σ (concatBilin
      (pushComb timeZeroMirror.reflectIso (conjComb (basisOf X))) (basisOf Y)) = _
  have e : conjComb (basisOf X) = basisOf X := by simp [conjComb, basisOf]
  rw [e, pushComb_basisOf, concatBilin_basisOf, concatBasis, dif_pos hd, linearExt_basisOf]
theorem nilTuple_mem_upper : nilTuple ∈ tuplesSupportedIn upperHalfSpace :=
  fun _ hf => by simp [nilTuple] at hf
theorem concatenable_nil_left (Y : Tuple) :
    Concatenable (push timeZeroMirror.reflectIso nilTuple) Y :=
  fun f hf => by simp [push, nilTuple] at hf
theorem concatenable_nil_right (X : Tuple) :
    Concatenable (push timeZeroMirror.reflectIso X) nilTuple :=
  fun _ _ g hg => by simp [nilTuple] at hg
theorem reflForm_nil_left (σ : Tuple → ℝ) (Y : Tuple)
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace) :
    reflForm σ (tupleToComb nilTuple nilTuple_mem_upper) (tupleToComb Y hY) = (σ Y : ℂ) := by
  rw [reflForm_tupleToComb σ _ _ _ _ (concatenable_nil_left Y)]
  congr 2
theorem reflForm_nil_right (σ : Tuple → ℝ) (X : Tuple)
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) :
    reflForm σ (tupleToComb X hX) (tupleToComb nilTuple nilTuple_mem_upper) =
      (σ (push timeZeroMirror.reflectIso X) : ℂ) := by
  rw [reflForm_tupleToComb σ _ _ _ _ (concatenable_nil_right X)]
  congr 2
  exact Subtype.ext (List.append_nil _)
theorem exists_timeAxis_lower_bound (l : List ScalarField)
    (hl : ∀ f ∈ l, IsCompact (tsupport f)) :
    ∃ b : ℝ, ∀ f ∈ l, ∀ x ∈ tsupport f, b < x timeAxis := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons f l ih =>
    obtain ⟨b, hb⟩ := ih fun g hg => hl g (List.mem_cons_of_mem _ hg)
    have hc : Continuous fun x : Space => x timeAxis := continuous_apply _
    obtain ⟨c, hc'⟩ := ((hl f List.mem_cons_self).image hc).bddBelow
    refine ⟨min b c - 1, fun g hg x hx => ?_⟩
    rcases List.mem_cons.1 hg with rfl | hg
    · have h₁ : c ≤ x timeAxis := hc' (mem_image_of_mem _ hx)
      have h₂ := min_le_right b c
      linarith
    · have h₁ := hb g hg x hx
      have h₂ := min_le_left b c
      linarith
theorem push_translate_mem_upper {v : Space} (hv : 0 ≤ v timeAxis) {Y : Tuple}
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace) :
    push (translate v) Y ∈ tuplesSupportedIn upperHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.push_translate_mem <;> assumption
theorem reflectionInvarianceFollows_holds : ReflectionInvarianceFollows := by
  intro σ _ hT hr X
  have hp := isPosSemidef_reflForm hr
  have key : ∀ (Y : Tuple) (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
      σ (push timeZeroMirror.reflectIso Y) = σ Y := by
    intro Y hY
    have h₁ := hp.isHermitianForm (tupleToComb Y hY) (tupleToComb nilTuple nilTuple_mem_upper)
    rw [reflForm_nil_left, reflForm_nil_right, Complex.conj_ofReal] at h₁
    exact_mod_cast h₁.symm
  obtain ⟨b, hb⟩ := exists_timeAxis_lower_bound X.1 fun f hf => (X.2.1 f hf).2.1
  set t : ℝ := max (-b) 0 with ht
  set a : Space := t • coordVec timeAxis with ha
  have ha₄ : a timeAxis = t := by
    simp [ha, coordVec_timeAxis_self]
  have hm : push (translate a) X ∈ tuplesSupportedIn upperHalfSpace := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    rw [tsupport_pushFn]
    intro y hy
    have hz : b < ((EuclidIsometry.translate a).symm.toFun y) timeAxis := hb f hf _ hy
    rw [symm_translate] at hz
    change 0 < y timeAxis
    have e : (y - a) timeAxis = y timeAxis - a timeAxis := rfl
    have h₂ : -b ≤ t := le_max_left _ _
    rw [e, ha₄] at hz
    linarith
  have h₁ := key _ hm
  rw [push_reflectIso_translate, hT _ (push timeZeroMirror.reflectIso X), hT a X] at h₁
  exact h₁
theorem linearExt_concatBilin_translate (σ : Tuple → ℝ) (X Y : Tuple)
    (u : Space) (hd : Concatenable X (push (translate u) Y)) :
    linearExt σ (concatBilin (basisOf X) (pushComb (translate u) (basisOf Y))) =
      (σ (concat X (push (translate u) Y) hd) : ℂ) := by
  rw [pushComb_basisOf, concatBilin_basisOf, concatBasis, dif_pos hd, linearExt_basisOf]
theorem tendsto_linearExt_tuples {σ : Tuple → ℝ} (hM : TranslateConcatTendsto)
    (hc : IsAdmissiblyContinuous σ) {X Y : Tuple} (hX : X ∈ tuplesSupportedIn lowerHalfSpace)
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace) {w : ℕ → Space} {v : Space}
    (hw : ∀ n, 0 ≤ w n timeAxis) (hv : 0 ≤ v timeAxis) (hwv : Tendsto w atTop (𝓝 v)) :
    Tendsto (fun n => linearExt σ (concatBilin (basisOf X)
        (pushComb (translate (w n)) (basisOf Y)))) atTop
      (𝓝 (linearExt σ (concatBilin (basisOf X)
        (pushComb (translate v) (basisOf Y))))) := by
  have d : ∀ {u : Space}, 0 ≤ u timeAxis → Concatenable X (push (translate u) Y) := fun hu =>
    concatenable_of_disjoint disjoint_lowerHalfSpace_upperHalfSpace hX
      (push_translate_mem_upper hu hY)
  obtain ⟨n₀, -, -, hconv, -⟩ := hM Y X w v hwv (d hv)
  have h₁ := (hc _ _ _ hconv).comp tendsto_natCast_atTop_atTop
  have h₂ := (Complex.continuous_ofReal.tendsto _).comp h₁
  rw [linearExt_concatBilin_translate σ X Y v (d hv)]
  refine h₂.congr fun n => ?_
  rw [linearExt_concatBilin_translate σ X Y (w n) (d (hw n))]
  simp only [Function.comp_apply, Int.toNat_natCast, concatOrNil, dif_pos (d (hw n))]
theorem tendsto_linearExt_combs {σ : Tuple → ℝ} (hM : TranslateConcatTendsto)
    (hc : IsAdmissiblyContinuous σ) {A W : TupleComb} (hA : A ∈ combsSupportedIn lowerHalfSpace)
    (hW : W ∈ combsSupportedIn upperHalfSpace) {w : ℕ → Space} {v : Space}
    (hw : ∀ n, 0 ≤ w n timeAxis) (hv : 0 ≤ v timeAxis) (hwv : Tendsto w atTop (𝓝 v)) :
    Tendsto (fun n => linearExt σ (concatBilin A (pushComb (translate (w n)) W))) atTop
      (𝓝 (linearExt σ (concatBilin A (pushComb (translate v) W)))) := by
  have hA' : A ∈ Submodule.span ℂ (basisOf '' tuplesSupportedIn lowerHalfSpace) := hA
  have hW' : W ∈ Submodule.span ℂ (basisOf '' tuplesSupportedIn upperHalfSpace) := hW
  clear hA hW
  induction hA' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    induction hW' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Y, hY, rfl⟩ := hy
      exact tendsto_linearExt_tuples hM hc hX hY hw hv hwv
    | zero => simp
    | add y y' _ _ hy hy' => simpa only [map_add] using hy.add hy'
    | smul a y _ hy => simpa only [map_smul, smul_eq_mul] using hy.const_mul a
  | zero => simp
  | add x x' _ _ hx hx' => simpa only [map_add, LinearMap.add_apply] using hx.add hx'
  | smul a x _ hx =>
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using hx.const_mul a
theorem continuous_reflForm_translate {σ : Tuple → ℝ} (hM : TranslateConcatTendsto)
    (hc : IsAdmissiblyContinuous σ) {P : Type*} [TopologicalSpace P] [SequentialSpace P]
    (c : P → Space) (hcont : Continuous c) (h0 : ∀ p, 0 ≤ c p timeAxis)
    (Z W : combsSupportedIn upperHalfSpace) :
    Continuous fun p => reflForm σ Z (translateComb (c p) (h0 p) W) := by
  refine continuous_iff_seqContinuous.2 fun x p hx => ?_
  exact tendsto_linearExt_combs hM hc (thetaConj Z).2 W.2 (fun n => h0 (x n)) (h0 p)
    ((hcont.tendsto p).comp hx)
theorem continuous_of_continuous_inner_pairs {P E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (g : P → E)
    (hK : Continuous fun r : P × P => ⟪g r.1, g r.2⟫_ℂ) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have k₁ : Continuous fun p => ⟪g p, g p⟫_ℂ := hK.comp (continuous_id.prodMk continuous_id)
  have k₂ : Continuous fun p => ⟪g p, g p₀⟫_ℂ := hK.comp (continuous_id.prodMk continuous_const)
  have k₃ : Continuous fun p => ⟪g p₀, g p⟫_ℂ := hK.comp (continuous_const.prodMk continuous_id)
  have hsq : ∀ p, ‖g p - g p₀‖ ^ 2 =
      (⟪g p, g p⟫_ℂ - ⟪g p, g p₀⟫_ℂ - ⟪g p₀, g p⟫_ℂ + ⟪g p₀, g p₀⟫_ℂ).re := fun p => by
    rw [← inner_sub_sub_self]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  have hcq : Continuous fun p =>
      (⟪g p, g p⟫_ℂ - ⟪g p, g p₀⟫_ℂ - ⟪g p₀, g p⟫_ℂ + ⟪g p₀, g p₀⟫_ℂ).re :=
    Complex.continuous_re.comp (((k₁.sub k₂).sub k₃).add continuous_const)
  have hlim : Tendsto (fun p => ‖g p - g p₀‖ ^ 2) (𝓝 p₀) (𝓝 0) := by
    have t := hcq.tendsto p₀
    rw [← hsq p₀, sub_self, norm_zero, zero_pow two_ne_zero] at t
    exact t.congr fun p => (hsq p).symm
  have hr := ((Real.continuous_sqrt.tendsto 0).comp hlim).congr fun p =>
    Real.sqrt_sq (norm_nonneg (g p - g p₀))
  rw [Real.sqrt_zero] at hr
  exact hr
theorem continuous_toReconstruction_translate {σ : Tuple → ℝ} (hT : IsTranslInvariant σ)
    (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (h : ReflectionPositiveAt timeZeroMirror σ) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] (c : P → Space) (hcont : Continuous c)
    (h0 : ∀ p, 0 ≤ c p timeAxis) (Z : combsSupportedIn upperHalfSpace) :
    Continuous fun p => toReconstruction σ h (translateComb (c p) (h0 p) Z) := by
  refine continuous_of_continuous_inner_pairs
    (fun p => toReconstruction σ h (translateComb (c p) (h0 p) Z)) ?_
  have hcm : Continuous timeReflect := by
    unfold timeReflect
    fun_prop
  have hs : ∀ r : P × P, 0 ≤ (c r.2 - timeReflect (c r.1)) timeAxis := by
    rintro ⟨p, p'⟩
    show 0 ≤ c p' timeAxis - timeReflect (c p) timeAxis
    linarith [h0 p, h0 p', timeReflect_timeAxis (c p)]
  simp only [inner_toReconstruction, reflForm_translateComb hT _ _ _ _ (hs _)]
  exact continuous_reflForm_translate hM hc (fun r : P × P => c r.2 - timeReflect (c r.1))
    ((hcont.comp continuous_snd).sub (hcm.comp (hcont.comp continuous_fst))) hs Z Z
theorem denseRange_toReconstruction (hF : BoundedOperators.BoundedOperatorFacts)
    {σ : Tuple → ℝ} (h : ReflectionPositiveAt timeZeroMirror σ) :
    DenseRange (toReconstruction σ h) := by
  obtain ⟨-, -, hdense, -⟩ :=
    hF.2.1 (combsSupportedIn upperHalfSpace) (reflForm σ) (isPosSemidef_reflForm h)
  exact hdense
theorem exists_bounded_extension_of_denseRange {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [AddCommGroup V] [Module ℂ V]
    (hF : BoundedOperators.BoundedOperatorFacts) (cl : V →ₗ[ℂ] H) (hcl : DenseRange ⇑cl)
    (L : V →ₗ[ℂ] V) (c : ℝ) (hc : 0 ≤ c) (hL : ∀ Z : V, ‖cl (L Z)‖ ≤ c * ‖cl Z‖) :
    ∃ B : H →L[ℂ] H, (∀ Z : V, B (cl Z) = cl (L Z)) ∧ ‖B‖ ≤ c := by
  have hker : ∀ Z, cl Z = 0 → cl (L Z) = 0 := fun Z hZ => by simpa [hZ] using hL Z
  let q : V ⧸ LinearMap.ker cl →ₗ[ℂ] H :=
    Submodule.liftQ (LinearMap.ker cl) (cl ∘ₗ L) fun Z hZ => hker Z hZ
  let T₀ : LinearMap.range cl →ₗ[ℂ] H :=
    q ∘ₗ (LinearEquiv.toLinearMap (LinearMap.quotKerEquivRange cl).symm)
  have hT₀ : ∀ Z hZ, T₀ ⟨cl Z, hZ⟩ = cl (L Z) := by
    intro Z hZ
    show q ((LinearMap.quotKerEquivRange cl).symm ⟨cl Z, hZ⟩) = cl (L Z)
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ ψ : LinearMap.range cl, ‖T₀ ψ‖ ≤ c * ‖(ψ : H)‖ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨Z, rfl⟩ := LinearMap.mem_range.1 hψ
    rw [hT₀]
    exact hL Z
  have hd : Dense ((LinearMap.range cl : Submodule ℂ H) : Set H) :=
    Dense.mono (LinearMap.coe_range cl).ge hcl
  obtain ⟨B, hBext, hBnorm, -⟩ := (hF.2.2.2.1 H _ hd).1 c T₀ hc hb
  refine ⟨B, fun Z => ?_, hBnorm⟩
  rw [← hT₀ Z (LinearMap.mem_range_self cl Z)]
  exact hBext ⟨cl Z, LinearMap.mem_range_self cl Z⟩
theorem exists_bounded_extension (hF : BoundedOperators.BoundedOperatorFacts) {σ : Tuple → ℝ}
    (h : ReflectionPositiveAt timeZeroMirror σ)
    (L : combsSupportedIn upperHalfSpace →ₗ[ℂ] combsSupportedIn upperHalfSpace) (c : ℝ)
    (hc : 0 ≤ c) (hL : ∀ Z, ‖toReconstruction σ h (L Z)‖ ≤ c * ‖toReconstruction σ h Z‖) :
    ∃ B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h,
      (∀ Z, B (toReconstruction σ h Z) = toReconstruction σ h (L Z)) ∧ ‖B‖ ≤ c :=
  exists_bounded_extension_of_denseRange (hcl := denseRange_toReconstruction hF h) hF _ L c hc hL
theorem ext_on_toReconstruction (hF : BoundedOperators.BoundedOperatorFacts) {σ : Tuple → ℝ}
    (h : ReflectionPositiveAt timeZeroMirror σ)
    {A B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h}
    (e : ∀ Z, A (toReconstruction σ h Z) = B (toReconstruction σ h Z)) : A = B :=
  DFunLike.coe_injective
    ((denseRange_toReconstruction hF h).equalizer A.continuous B.continuous (funext e))
theorem isAdjointPair_of_toReconstruction (hF : BoundedOperators.BoundedOperatorFacts)
    {σ : Tuple → ℝ} (h : ReflectionPositiveAt timeZeroMirror σ)
    {A B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h}
    (e : ∀ Z W, ⟪toReconstruction σ h Z, A (toReconstruction σ h W)⟫_ℂ =
      ⟪B (toReconstruction σ h Z), toReconstruction σ h W⟫_ℂ) : IsAdjointPair A B := by
  have hd : Dense ((LinearMap.range (toReconstruction σ h) : Submodule ℂ _) :
      Set (ReconstructionSpace σ h)) := by
    rw [LinearMap.coe_range]
    exact denseRange_toReconstruction hF h
  refine (hF.2.2.2.1 (ReconstructionSpace σ h) _ hd).2.2.1 A B ?_
  rintro ⟨_, Z, rfl⟩ ⟨_, W, rfl⟩
  exact e Z W
theorem isStrongContinuous_of_toReconstruction (hF : BoundedOperators.BoundedOperatorFacts)
    {σ : Tuple → ℝ} (h : ReflectionPositiveAt timeZeroMirror σ) {P : Type*}
    [TopologicalSpace P] (A : P → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h)
    (hA : ∀ p, ‖A p‖ ≤ 1) (hc : ∀ Z, Continuous fun p => A p (toReconstruction σ h Z)) :
    IsStrongContinuous A := by
  intro ψ
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hu'⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨Z, hZ⟩ := (denseRange_toReconstruction hF h).exists_dist_lt ψ hε
  refine ⟨_, hc Z, fun p => hu' ?_⟩
  rw [dist_eq_norm, ← map_sub]
  calc ‖A p (ψ - toReconstruction σ h Z)‖ ≤ ‖A p‖ * ‖ψ - toReconstruction σ h Z‖ :=
        (A p).le_opNorm _
    _ ≤ 1 * ‖ψ - toReconstruction σ h Z‖ := by gcongr; exact hA p
    _ < ε := by rwa [one_mul, ← dist_eq_norm]
theorem continuous_timeShiftVec : Continuous timeShiftVec := by
  unfold timeShiftVec
  exact NNReal.continuous_coe.smul continuous_const
theorem continuous_embedSpatial : Continuous embedSpatial := by
  refine continuous_pi fun j => ?_
  induction j using Fin.lastCases with
  | last =>
    have e : (fun q => embedSpatial q (Fin.last 3)) = fun _ => (0 : ℝ) :=
      funext fun q => embedSpatial_timeAxis q
    rw [e]
    exact continuous_const
  | cast i =>
    have e : (fun q => embedSpatial q i.castSucc) = fun q : Momentum3 => q i :=
      funext fun q => embedSpatial_spaceAxis q i
    rw [e]
    exact (EuclideanSpace.proj i).continuous
theorem embedSpatial_add (y y' : Momentum3) :
    embedSpatial (y + y') = embedSpatial y + embedSpatial y' := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    have e₁ := embedSpatial_timeAxis (y + y')
    have e₂ := embedSpatial_timeAxis y
    have e₃ := embedSpatial_timeAxis y'
    change embedSpatial (y + y') timeAxis = embedSpatial y timeAxis + embedSpatial y' timeAxis
    rw [e₁, e₂, e₃, add_zero]
  | cast i =>
    change embedSpatial (y + y') (spaceAxis i) =
      embedSpatial y (spaceAxis i) + embedSpatial y' (spaceAxis i)
    simp only [embedSpatial_spaceAxis]
    rfl
theorem embedSpatial_zero : embedSpatial 0 = 0 := by
  funext j
  induction j using Fin.lastCases with
  | last => exact embedSpatial_timeAxis 0
  | cast i => exact embedSpatial_spaceAxis 0 i
theorem timeShiftVec_add (t t' : ℝ≥0) : timeShiftVec t + timeShiftVec t' = timeShiftVec (t + t') := by
  simp only [timeShiftVec, NNReal.coe_add, add_smul]
theorem timeShiftVec_zero : timeShiftVec 0 = 0 := by
  simp [timeShiftVec]
theorem timeShiftVec_sub_timeReflect (t : ℝ≥0) :
    timeShiftVec t - timeReflect (timeShiftVec t) = timeShiftVec (2 * t) := by
  have ht := timeShiftVec_timeAxis t
  simp only [timeReflect, ht]
  simp only [timeShiftVec, NNReal.coe_mul, NNReal.coe_ofNat]
  module
theorem timeShiftComb_add (t t' : ℝ≥0) (Z : combsSupportedIn upperHalfSpace) :
    timeShiftComb t (timeShiftComb t' Z) = timeShiftComb (t + t') Z := by
  unfold timeShiftComb
  rw [translateComb_translateComb _ _ _ _
    (by rw [timeShiftVec_add, timeShiftVec_timeAxis]; exact (t + t').2)]
  exact translateComb_congr (timeShiftVec_add t t') _ _ _
theorem timeShiftComb_zero (Z : combsSupportedIn upperHalfSpace) : timeShiftComb 0 Z = Z := by
  unfold timeShiftComb
  rw [translateComb_congr timeShiftVec_zero _ le_rfl, translateComb_zero]
theorem spaceShiftComb_add (y y' : Momentum3) (Z : combsSupportedIn upperHalfSpace) :
    spaceShiftComb y (spaceShiftComb y' Z) = spaceShiftComb (y + y') Z := by
  unfold spaceShiftComb
  rw [translateComb_translateComb _ _ _ _
    (by rw [← embedSpatial_add, embedSpatial_timeAxis])]
  exact translateComb_congr (embedSpatial_add y y').symm _ _ _
theorem spaceShiftComb_zero (Z : combsSupportedIn upperHalfSpace) : spaceShiftComb 0 Z = Z := by
  unfold spaceShiftComb
  rw [translateComb_congr embedSpatial_zero _ le_rfl, translateComb_zero]
theorem timeShiftComb_spaceShiftComb (t : ℝ≥0) (y : Momentum3)
    (Z : combsSupportedIn upperHalfSpace) :
    timeShiftComb t (spaceShiftComb y Z) = spacetimeShiftComb t y Z := by
  unfold timeShiftComb spaceShiftComb spacetimeShiftComb
  exact translateComb_translateComb _ _ _ _ _ Z
theorem spaceShiftComb_timeShiftComb (t : ℝ≥0) (y : Momentum3)
    (Z : combsSupportedIn upperHalfSpace) :
    spaceShiftComb y (timeShiftComb t Z) = spacetimeShiftComb t y Z := by
  unfold timeShiftComb spaceShiftComb spacetimeShiftComb
  rw [translateComb_translateComb _ _ _ _
    (by rw [add_comm]; simp [timeShiftVec_timeAxis, embedSpatial_timeAxis])]
  exact translateComb_congr (add_comm _ _) _ _ _
section Norms
variable {σ : Tuple → ℝ} (h : ReflectionPositiveAt timeZeroMirror σ)
theorem norm_sq_toReconstruction (Z : combsSupportedIn upperHalfSpace) :
    ((‖toReconstruction σ h Z‖ ^ 2 : ℝ) : ℂ) = reflForm σ Z Z := by
  rw [← inner_toReconstruction σ h, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem reflForm_timeShiftComb_two_mul (hT : IsTranslInvariant σ) (t : ℝ≥0)
    (Z : combsSupportedIn upperHalfSpace) :
    reflForm σ Z (timeShiftComb (2 * t) Z) =
      ((‖toReconstruction σ h (timeShiftComb t Z)‖ ^ 2 : ℝ) : ℂ) := by
  rw [norm_sq_toReconstruction h]
  have hc : 0 ≤ (timeShiftVec t - timeReflect (timeShiftVec t)) timeAxis := by
    rw [timeShiftVec_sub_timeReflect, timeShiftVec_timeAxis]
    exact (2 * t).2
  unfold timeShiftComb
  rw [reflForm_translateComb hT _ _ _ _ hc]
  exact congrArg _ (translateComb_congr (timeShiftVec_sub_timeReflect t).symm _ _ _)
theorem contractsAtTime_iff_norm_le (hT : IsTranslInvariant σ) (t : ℝ≥0) :
    ContractsAtTime σ t ↔
      ∀ Z, ‖toReconstruction σ h (timeShiftComb t Z)‖ ≤ ‖toReconstruction σ h Z‖ := by
  refine forall_congr' fun Z => ?_
  rw [reflForm_timeShiftComb_two_mul h hT, ← norm_sq_toReconstruction h, Complex.real_le_real]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero
include h in
theorem contractsAtTime_of_contractsOnDenseTimes (hT : IsTranslInvariant σ)
    (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hD : ContractsOnDenseTimes σ) (t : ℝ≥0) : ContractsAtTime σ t := by
  rw [contractsAtTime_iff_norm_le h hT]
  intro Z
  obtain ⟨D, -, hcl, hcon⟩ := hD
  have hcont : Continuous fun t => toReconstruction σ h (timeShiftComb t Z) :=
    continuous_toReconstruction_translate hT hM hc h timeShiftVec continuous_timeShiftVec _ Z
  have hclosed : IsClosed {t | ‖toReconstruction σ h (timeShiftComb t Z)‖ ≤
      ‖toReconstruction σ h Z‖} := isClosed_le hcont.norm continuous_const
  have hsub : D ⊆ {t | ‖toReconstruction σ h (timeShiftComb t Z)‖ ≤
      ‖toReconstruction σ h Z‖} := fun s hs =>
    (contractsAtTime_iff_norm_le h hT s).1 (hcon s hs) Z
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from t.2) with rfl | ht
  · rw [timeShiftComb_zero]
  · exact closure_minimal hsub hclosed (hcl ht)
theorem norm_toReconstruction_spaceShiftComb (hT : IsTranslInvariant σ) (y : Momentum3)
    (Z : combsSupportedIn upperHalfSpace) :
    ‖toReconstruction σ h (spaceShiftComb y Z)‖ = ‖toReconstruction σ h Z‖ := by
  have hz : embedSpatial y - timeReflect (embedSpatial y) = 0 := by
    rw [timeReflect_of_timeAxis_eq_zero (embedSpatial_timeAxis y), sub_self]
  have hc : 0 ≤ (embedSpatial y - timeReflect (embedSpatial y)) timeAxis := by
    rw [hz]
    exact le_rfl
  have e : reflForm σ (spaceShiftComb y Z) (spaceShiftComb y Z) = reflForm σ Z Z := by
    unfold spaceShiftComb
    rw [reflForm_translateComb hT _ _ _ _ hc, translateComb_congr hz _ le_rfl,
      translateComb_zero]
  have e₂ : ((‖toReconstruction σ h (spaceShiftComb y Z)‖ ^ 2 : ℝ) : ℂ) =
      ((‖toReconstruction σ h Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_toReconstruction, norm_sq_toReconstruction, e]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (Complex.ofReal_injective e₂)
theorem zero_sub_timeReflect_timeShiftVec (t : ℝ≥0) :
    0 - timeReflect (timeShiftVec t) = timeShiftVec t := by
  have h₁ := timeShiftVec_timeAxis t
  simp only [timeReflect, h₁]
  simp only [timeShiftVec]
  module
theorem reflForm_timeShiftComb_symm (hT : IsTranslInvariant σ) (t : ℝ≥0)
    (Z W : combsSupportedIn upperHalfSpace) :
    reflForm σ Z (timeShiftComb t W) = reflForm σ (timeShiftComb t Z) W := by
  have ha : 0 ≤ timeShiftVec t timeAxis := by
    rw [timeShiftVec_timeAxis]
    exact t.2
  have hc : 0 ≤ ((0 : Space) - timeReflect (timeShiftVec t)) timeAxis := by
    rw [zero_sub_timeReflect_timeShiftVec]
    exact ha
  have e := reflForm_translateComb hT (timeShiftVec t) 0 ha le_rfl hc Z W
  rw [translateComb_zero, translateComb_congr (zero_sub_timeReflect_timeShiftVec t) hc ha] at e
  exact e.symm
theorem toReconstruction_translateComb_nil (v : Space) (hv : 0 ≤ v timeAxis) :
    toReconstruction σ h (translateComb v hv (tupleToComb nilTuple nilTuple_mem_upper)) =
      vacuum σ h := by
  refine congrArg (toReconstruction σ h) (Subtype.ext ?_)
  change pushComb (translate v) (basisOf nilTuple) = basisOf nilTuple
  rw [pushComb_basisOf, push_nilTuple]
theorem formAndVacuumProps_holds (hf : IsNormalizedFunctional σ) : FormAndVacuumProps σ h where
  isHermitian := (isPosSemidef_reflForm h).isHermitianForm
  isPosSemidef := isPosSemidef_reflForm h
  norm_vacuum := by
    have e : ((‖vacuum σ h‖ ^ 2 : ℝ) : ℂ) = (σ nilTuple : ℂ) :=
      (norm_sq_toReconstruction h (tupleToComb nilTuple nilTuple_mem_upper)).trans
        (reflForm_nil_left σ nilTuple nilTuple_mem_upper)
    rw [hf] at e
    have e₂ : ‖vacuum σ h‖ ^ 2 = (1 : ℝ) := by exact_mod_cast e
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [e₂, one_pow])
  inner_class_vacuum X hX := by
    have e := (isPosSemidef_reflForm h).isHermitianForm
      (tupleToComb nilTuple nilTuple_mem_upper) (tupleToComb X hX)
    rw [reflForm_nil_left, Complex.conj_ofReal] at e
    exact (inner_toReconstruction σ h _ _).trans e
  inner_vacuum_class X hX :=
    (inner_toReconstruction σ h _ _).trans (reflForm_nil_left σ X hX)
theorem timeShiftProps_holds (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto)
    (hc : IsAdmissiblyContinuous σ) : TimeShiftProps σ h where
  mem_combsSupportedIn Z t := pushComb_translate_mem
    (by rw [timeShiftVec_timeAxis]; exact t.2) Z.2
  form_eq_norm_sq Z t := reflForm_timeShiftComb_two_mul h hT t Z
  contractsAtTime hD t := contractsAtTime_of_contractsOnDenseTimes h hT hM hc hD t
end Norms
section Families
variable {σ : Tuple → ℝ} (h : ReflectionPositiveAt timeZeroMirror σ)
theorem transferSemigroup_spec (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hcon : ∀ t, ContractsAtTime σ t) :
    IsTransferSemigroup σ h (transferSemigroup σ h) ∧ ∀ t, ‖transferSemigroup σ h t‖ ≤ 1 := by
  have key : ∀ t : ℝ≥0, ∃ B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h,
      (∀ Z, B (toReconstruction σ h Z) = toReconstruction σ h (timeShiftComb t Z)) ∧
        ‖B‖ ≤ 1 := fun t =>
    exists_bounded_extension hF h (translateLinearMap (timeShiftVec t)
      (by rw [timeShiftVec_timeAxis]; exact t.2)) 1 zero_le_one fun Z => by
        rw [one_mul]
        exact (contractsAtTime_iff_norm_le h hT t).1 (hcon t) Z
  choose T hT₁ hT₂ using key
  have hs : IsTransferSemigroup σ h (transferSemigroup σ h) :=
    Classical.epsilon_spec (p := IsTransferSemigroup σ h) ⟨T, hT₁⟩
  have e : transferSemigroup σ h = T :=
    funext fun t => ext_on_toReconstruction hF h fun Z => by rw [hs t Z, hT₁ t Z]
  exact ⟨hs, fun t => by rw [e]; exact hT₂ t⟩
theorem spatialTranslationRep_spec (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) :
    IsSpatialTranslationRep σ h (spatialTranslationRep σ h) ∧
      ∀ y, ‖spatialTranslationRep σ h y‖ ≤ 1 := by
  have key : ∀ y : Momentum3,
      ∃ B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h,
      (∀ Z, B (toReconstruction σ h Z) = toReconstruction σ h (spaceShiftComb y Z)) ∧
        ‖B‖ ≤ 1 := fun y =>
    exists_bounded_extension hF h (translateLinearMap (embedSpatial y)
      (embedSpatial_timeAxis y).ge) 1 zero_le_one fun Z => by
        rw [one_mul]
        exact (norm_toReconstruction_spaceShiftComb h hT y Z).le
  choose U hU₁ hU₂ using key
  have hs : IsSpatialTranslationRep σ h (spatialTranslationRep σ h) :=
    Classical.epsilon_spec (p := IsSpatialTranslationRep σ h) ⟨U, hU₁⟩
  have e : spatialTranslationRep σ h = U :=
    funext fun y => ext_on_toReconstruction hF h fun Z => by rw [hs y Z, hU₁ y Z]
  exact ⟨hs, fun y => by rw [e]; exact hU₂ y⟩
theorem isAdjointPair_transferSemigroup (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hS : IsTransferSemigroup σ h (transferSemigroup σ h))
    (t : ℝ≥0) : IsAdjointPair (transferSemigroup σ h t) (transferSemigroup σ h t) :=
  isAdjointPair_of_toReconstruction hF h fun Z W => by
    rw [hS, hS, inner_toReconstruction, inner_toReconstruction]
    exact reflForm_timeShiftComb_symm hT t Z W
theorem spatialTranslationRep_zero (hF : BoundedOperators.BoundedOperatorFacts)
    (hV : IsSpatialTranslationRep σ h (spatialTranslationRep σ h)) :
    spatialTranslationRep σ h 0 = 1 :=
  ext_on_toReconstruction hF h fun Z => by
    rw [hV, spaceShiftComb_zero]
    rfl
theorem spatialTranslationRep_add (hF : BoundedOperators.BoundedOperatorFacts)
    (hV : IsSpatialTranslationRep σ h (spatialTranslationRep σ h)) (y y' : Momentum3) :
    spatialTranslationRep σ h y * spatialTranslationRep σ h y' =
      spatialTranslationRep σ h (y + y') :=
  ext_on_toReconstruction hF h fun Z => by
    change spatialTranslationRep σ h y (spatialTranslationRep σ h y' _) = _
    rw [hV, hV, hV, spaceShiftComb_add]
theorem isUnitaryOp_spatialTranslationRep (hF : BoundedOperators.BoundedOperatorFacts)
    (hV : IsSpatialTranslationRep σ h (spatialTranslationRep σ h))
    (hn : ∀ y, ‖spatialTranslationRep σ h y‖ ≤ 1) (y : Momentum3) :
    IsUnitaryOp (spatialTranslationRep σ h y) := by
  have l : ∀ ψ, spatialTranslationRep σ h (-y) (spatialTranslationRep σ h y ψ) = ψ :=
    fun ψ => by
      have e := spatialTranslationRep_add h hF hV (-y) y
      rw [neg_add_cancel, spatialTranslationRep_zero h hF hV] at e
      exact congrArg (fun B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h => B ψ) e
  have r : ∀ ψ, spatialTranslationRep σ h y (spatialTranslationRep σ h (-y) ψ) = ψ :=
    fun ψ => by
      have e := spatialTranslationRep_add h hF hV y (-y)
      rw [add_neg_cancel, spatialTranslationRep_zero h hF hV] at e
      exact congrArg (fun B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h => B ψ) e
  have le : ∀ (z : Momentum3) ψ, ‖spatialTranslationRep σ h z ψ‖ ≤ ‖ψ‖ := fun z ψ =>
    ((spatialTranslationRep σ h z).le_opNorm ψ).trans
      (by simpa using mul_le_mul_of_nonneg_right (hn z) (norm_nonneg ψ))
  refine ⟨⟨Function.LeftInverse.injective l, Function.RightInverse.surjective r⟩, fun ψ => ?_⟩
  refine le_antisymm (le y ψ) ?_
  calc ‖ψ‖ = ‖spatialTranslationRep σ h (-y) (spatialTranslationRep σ h y ψ)‖ := by
        rw [l]
    _ ≤ _ := le _ _
theorem transferSemigroup_mul_spatialTranslationRep (hF : BoundedOperators.BoundedOperatorFacts)
    (hS : IsTransferSemigroup σ h (transferSemigroup σ h))
    (hV : IsSpatialTranslationRep σ h (spatialTranslationRep σ h)) (t : ℝ≥0) (y : Momentum3) :
    transferSemigroup σ h t * spatialTranslationRep σ h y =
      spatialTranslationRep σ h y * transferSemigroup σ h t :=
  ext_on_toReconstruction hF h fun Z => by
    change transferSemigroup σ h t (spatialTranslationRep σ h y _) =
      spatialTranslationRep σ h y (transferSemigroup σ h t _)
    rw [hV, hS, hS, hV, timeShiftComb_spaceShiftComb, spaceShiftComb_timeShiftComb]
theorem isStrongContinuous_transferSemigroup (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hS : IsTransferSemigroup σ h (transferSemigroup σ h))
    (hn : ∀ t, ‖transferSemigroup σ h t‖ ≤ 1) :
    IsStrongContinuous (transferSemigroup σ h) :=
  isStrongContinuous_of_toReconstruction hF h _ hn fun Z => by
    simp only [hS _ Z]
    exact continuous_toReconstruction_translate hT hM hc h timeShiftVec continuous_timeShiftVec _ Z
theorem isStrongContinuous_spatialTranslationRep (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hV : IsSpatialTranslationRep σ h (spatialTranslationRep σ h))
    (hn : ∀ y, ‖spatialTranslationRep σ h y‖ ≤ 1) :
    IsStrongContinuous (spatialTranslationRep σ h) :=
  isStrongContinuous_of_toReconstruction hF h _ hn fun Z => by
    simp only [hV _ Z]
    exact continuous_toReconstruction_translate hT hM hc h embedSpatial continuous_embedSpatial _ Z
theorem isContractionSemigroupWithUnitaryGroup_holds (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hcon : ∀ t, ContractsAtTime σ t) :
    IsContractionSemigroupWithUnitaryGroup (transferSemigroup σ h)
      (spatialTranslationRep σ h) := by
  obtain ⟨hS, hSn⟩ := transferSemigroup_spec h hF hT hcon
  obtain ⟨hV, hVn⟩ := spatialTranslationRep_spec h hF hT
  have hu := isUnitaryOp_spatialTranslationRep h hF hV hVn
  exact
    { isSelfAdjoint := fun t => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y =>
        (isAdjointPair_transferSemigroup h hF hT hS t x y).symm
      norm_le_one := hSn
      semigroup_zero := ext_on_toReconstruction hF h fun Z => by
        rw [hS, timeShiftComb_zero]
        rfl
      semigroup_add := fun t t' => ext_on_toReconstruction hF h fun Z => by
        change transferSemigroup σ h t (transferSemigroup σ h t' _) = _
        rw [hS, hS, hS, timeShiftComb_add]
      isUnitary := fun y => ⟨(hu y).bijective, (hu y).norm_map⟩
      group_add := spatialTranslationRep_add h hF hV
      semigroup_mul_group := transferSemigroup_mul_spatialTranslationRep h hF hS hV
      continuous_semigroup := isStrongContinuous_transferSemigroup h hF hT hM hc hS hSn
      continuous_group := isStrongContinuous_spatialTranslationRep h hF hT hM hc hV hVn }
end Families
section Requirements
variable {σ : Tuple → ℝ} (h : ReflectionPositiveAt timeZeroMirror σ)
theorem transferSemigroupProps_holds (hF : BoundedOperators.BoundedOperatorFacts)
    (hJ : EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hcon : ∀ t, ContractsAtTime σ t) : TransferSemigroupProps σ h := by
  obtain ⟨hS, hSn⟩ := transferSemigroup_spec h hF hT hcon
  have hsys := isContractionSemigroupWithUnitaryGroup_holds h hF hT hM hc hcon
  exact
    { existsUnique := ⟨_, hS, fun T' hT' => funext fun t => ext_on_toReconstruction hF h fun Z => by
        rw [hT', hS]⟩
      isTransferSemigroup := hS
      isSelfAdjoint := isAdjointPair_transferSemigroup h hF hT hS
      isContraction := hSn
      isStronglyContinuous := hsys.continuous_semigroup
      zero := hsys.semigroup_zero
      add := hsys.semigroup_add
      kernel_eq := (hJ _ _ _ hsys).2.1
      fixes_vacuum := fun t => (hS t _).trans (toReconstruction_translateComb_nil h _ _) }
theorem spatialRepProps_holds (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hcon : ∀ t, ContractsAtTime σ t) : SpatialRepProps σ h := by
  obtain ⟨hS, -⟩ := transferSemigroup_spec h hF hT hcon
  obtain ⟨hV, hVn⟩ := spatialTranslationRep_spec h hF hT
  have hsys := isContractionSemigroupWithUnitaryGroup_holds h hF hT hM hc hcon
  exact
    { existsUnique := ⟨_, hV, fun U' hU' => funext fun y => ext_on_toReconstruction hF h fun Z => by
        rw [hU', hV]⟩
      isSpatialTranslationRep := hV
      isStronglyContinuous := hsys.continuous_group
      isUnitary := isUnitaryOp_spatialTranslationRep h hF hV hVn
      add := hsys.group_add
      commutes := hsys.semigroup_mul_group
      fixes_vacuum := fun y => (hV y _).trans (toReconstruction_translateComb_nil h _ _) }
theorem matrixElementProps_holds (hF : BoundedOperators.BoundedOperatorFacts)
    (hT : IsTranslInvariant σ) (hcon : ∀ t, ContractsAtTime σ t) :
    MatrixElementProps σ h := by
  obtain ⟨hS, -⟩ := transferSemigroup_spec h hF hT hcon
  obtain ⟨hV, -⟩ := spatialTranslationRep_spec h hF hT
  refine ⟨fun Z W t y => ?_, fun X hX =>
    (inner_toReconstruction σ h _ _).trans (reflForm_nil_left σ X hX)⟩
  rw [hV, hS, timeShiftComb_spaceShiftComb, inner_toReconstruction]
theorem measurable_lineEnergyCoord : Measurable lineEnergyCoord :=
  (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_fst)).measurable
theorem measurable_lineMomentumCoord : Measurable lineMomentumCoord :=
  (Complex.continuous_ofReal.comp continuous_snd).measurable
theorem axisMeasureProps_holds
    (hC : EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hF : BoundedOperators.BoundedOperatorFacts)
    (hJ : EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hcon : ∀ t, ContractsAtTime σ t) (i : Fin 3) : AxisMeasureProps σ h i := by
  have hsys := isContractionSemigroupWithUnitaryGroup_holds h hF hT hM hc hcon
  obtain ⟨hm₁, hm₂⟩ := (hJ _ _ _ hsys).2.2 i
  have hspec : IsAxisSpectralMeasure σ h i (axisSpectralMeasure σ h i) :=
    Classical.epsilon_spec (p := IsAxisSpectralMeasure σ h i) ⟨_, hm₁⟩
  have himage : axisSpectralMeasure σ h i =
      (jointSpectralMeasure σ h).pushforward isEuclideanBorel_energyMomentumLine
        (projMomentum i) (measurable_projMomentum i) := hm₂ _ hspec
  have hB := (hC EnergyMomentumSpace (ReconstructionSpace σ h)
    (jointSpectralMeasure σ h)).2.2.2.2.2.1
  refine ⟨⟨_, hm₁, hm₂⟩, hspec, himage, ?_, ?_⟩
  · rw [himage, hB.pushforward EnergyMomentumLine isEuclideanBorel_energyMomentumLine _
      (measurable_projMomentum i) lineEnergyCoord measurable_lineEnergyCoord]
    rfl
  · rw [himage, hB.pushforward EnergyMomentumLine isEuclideanBorel_energyMomentumLine _
      (measurable_projMomentum i) lineMomentumCoord measurable_lineMomentumCoord]
    rfl
theorem jointMeasureProps_holds (hF : BoundedOperators.BoundedOperatorFacts)
    (hJ : EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hG : EnergyMomentum.Generators.GeneratorsTheorem)
    (hT : IsTranslInvariant σ) (hM : TranslateConcatTendsto) (hc : IsAdmissiblyContinuous σ)
    (hcon : ∀ t, ContractsAtTime σ t) : JointMeasureProps σ h := by
  have hsys := isContractionSemigroupWithUnitaryGroup_holds h hF hT hM hc hcon
  obtain ⟨⟨hE₁, hE₂, -⟩, -, -⟩ := hJ _ _ _ hsys
  obtain ⟨ha, hb, hmom, hd, he⟩ := hG _ _ _ hsys
  obtain ⟨hS, -⟩ := transferSemigroup_spec h hF hT hcon
  obtain ⟨hV, -⟩ := spatialTranslationRep_spec h hF hT
  have hfix : ∀ t, transferSemigroup σ h t (vacuum σ h) = vacuum σ h :=
    fun t => (hS t _).trans (toReconstruction_translateComb_nil h _ _)
  have hfix' : ∀ y, spatialTranslationRep σ h y (vacuum σ h) = vacuum σ h :=
    fun y => (hV y _).trans (toReconstruction_translateComb_nil h _ _)
  exact
    { existsUnique := ⟨_, hE₁, hE₂⟩
      isJointSpectralMeasure := hE₁
      hamiltonian_isSelfAdjoint := ha.hamiltonian_selfAdjoint
      momentum_isSelfAdjoint := ha.momentumOp_selfAdjoint
      hamiltonian_nonneg := ha.hamiltonian_nonneg
      mem_hamiltonian_domain_iff := hb.mem_domain_iff
      tendsto_hamiltonian := hb.tendsto_apply
      mem_momentum_domain_iff := fun i => (hmom i).mem_domain_iff
      tendsto_momentum := fun i => (hmom i).tendsto_apply
      vacuum_mem_hamiltonian_kernel := ((hd.tfae _).out 1 0).1 hfix
      vacuum_mem_momentum_kernel := fun i => ((he i _).out 1 0).1 fun s => hfix' _ }
end Requirements
theorem denseTimeReconstruction_holds
    (hC : EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hF : BoundedOperators.BoundedOperatorFacts)
    (hM : ReflectionPositivity.MovingTestFunctions.statement)
    (hJ : EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hG : EnergyMomentum.Generators.GeneratorsTheorem) : DenseTimeReconstructionHolds := by
  refine ⟨reflectionInvarianceFollows_holds, fun σ hσ => ?_⟩
  have h := hσ.isReflectionPositive
  have hT := hσ.isTranslInvariant
  have hc := hσ.isAdmissiblyContinuous
  have hm := hM.2.1
  refine ⟨formAndVacuumProps_holds _ hσ.isNormalized, timeShiftProps_holds _ hT hm hc, fun hD => ?_⟩
  have hcon := contractsAtTime_of_contractsOnDenseTimes h hT hm hc hD
  exact ⟨transferSemigroupProps_holds _ hF hJ hT hm hc hcon, spatialRepProps_holds _ hF hT hm hc hcon,
    matrixElementProps_holds _ hF hT hcon, axisMeasureProps_holds _ hC hF hJ hT hm hc hcon,
    jointMeasureProps_holds _ hF hJ hG hT hm hc hcon⟩
end YangMills.Construction.ReflectionPositivity.DenseTimeReconstruction
