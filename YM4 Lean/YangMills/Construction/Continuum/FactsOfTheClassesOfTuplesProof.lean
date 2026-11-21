import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.Continuum.FactsOfCentredMomentsMirrorsClassesAndTheSeparatingFamily
import YangMills.Construction.Continuum.FactsOfTheClassesOfTuples
import YangMills.Construction.InfiniteLattice.SeparatedTuplesOfFourSpaceAsSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open Filter YangMills.Construction.AmbientPoints
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.R4TupleForms (FinTuple listOf mem_separatedTuples_iff_ofFn)
open YangMills.Construction.TorusFunctionals (sharpNormAt)
open YangMills.Construction.ReflectionPositivity (maxNorm centredCube)
open YangMills.Construction.PeriodicLattice (adicRationalsPositive)
open scoped ENNReal Topology
section NormAndTranslation
theorem sharpNormAt_euclidean_eq (s : Conventions.StandingParameters) (M : ℕ)
    (f : Pt s .euclidean → ℝ) :
    sharpNormAt s .euclidean M f = TestFunctions.sharpNormR4 (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) :=
  rfl
theorem sharpNormAt_transportFn (s : Conventions.StandingParameters) (M : ℕ)
    (r : Pt s .euclidean ≃ Pt s .euclidean) (hr : IsDistIsometry r)
    (f : Pt s .euclidean → ℝ) :
    sharpNormAt s .euclidean M (transportFn r f) = sharpNormAt s .euclidean M f := by
  rw [sharpNormAt_euclidean_eq, sharpNormAt_euclidean_eq]
  unfold TestFunctions.sharpNormR4
  have hsup : TestFunctions.uniformNorm (transportFn r f : (Fin 4 → ℝ) → ℝ) =
      TestFunctions.uniformNorm (f : (Fin 4 → ℝ) → ℝ) := by
    unfold TestFunctions.uniformNorm
    exact (Equiv.iSup_comp (g := fun x : Pt s .euclidean => ‖f x‖) r.symm)
  have hlip : TestFunctions.lipConstR4 (transportFn r f : (Fin 4 → ℝ) → ℝ) =
      TestFunctions.lipConstR4 (f : (Fin 4 → ℝ) → ℝ) := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    constructor
    · rintro ⟨hC, h⟩
      refine ⟨hC, fun x y => ?_⟩
      have h1 := h (r x) (r y)
      have h2 : TestFunctions.euclidDistR4 (r x) (r y) = TestFunctions.euclidDistR4 x y := hr x y
      have h3 : transportFn r f (r x) = f x := congrArg f (r.symm_apply_apply x)
      have h4 : transportFn r f (r y) = f y := congrArg f (r.symm_apply_apply y)
      rw [h2, h3, h4] at h1
      exact h1
    · rintro ⟨hC, h⟩
      refine ⟨hC, fun x y => ?_⟩
      have h1 := h (r.symm x) (r.symm y)
      have h2 : TestFunctions.euclidDistR4 x y =
          TestFunctions.euclidDistR4 (r.symm x) (r.symm y) :=
        (congrArg₂ (pointDist s .euclidean) (r.apply_symm_apply x)
          (r.apply_symm_apply y)).symm.trans (hr (r.symm x) (r.symm y))
      rw [h2]
      exact h1
  exact congrArg₂ max hsup (congrArg (fun c => 40 * (M : ℝ) * c) hlip)
theorem pi_norm_le_euclidNormVec (z : Fin 4 → ℝ) : ‖z‖ ≤ TorusMetric.euclidNormVec z := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem tendsto_sharpNormR4_sub_translate (M : ℝ) (hM : 0 ≤ M) (f : (Fin 4 → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) (v : Fin 4 → ℝ) :
    Tendsto (fun v' : Fin 4 → ℝ =>
      TestFunctions.sharpNormR4 M (fun x => f (x - v') - f (x - v))) (𝓝 v) (𝓝 0) := by
  have uf : UniformContinuous f := hcs.uniformContinuous_of_continuous hf.continuous
  have hg : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have ug : UniformContinuous (fderiv ℝ f) :=
    (hcs.fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous hg
  have hd : ∀ x, HasFDerivAt f (fderiv ℝ f x) x := fun x =>
    (hf.differentiable (by norm_num) x).hasFDerivAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : 0 < 2 * (1 + 40 * M) := by positivity
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (2 * (1 + 40 * M)) := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ div_pos hε hpos
  have hηε : (1 + 40 * M) * η = ε / 2 := by
    rw [hη]
    field_simp
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1 uf η hη0
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuous_iff.1 ug η hη0
  filter_upwards [Metric.ball_mem_nhds v (lt_min hδ₁ hδ₂)] with v' hv'
  have hv₁ : dist v' v < δ₁ := (Metric.mem_ball.1 hv').trans_le (min_le_left _ _)
  have hv₂ : dist v' v < δ₂ := (Metric.mem_ball.1 hv').trans_le (min_le_right _ _)
  have hclose : ∀ x : Fin 4 → ℝ, dist (x - v') (x - v) = dist v' v := fun x => dist_sub_left _ _ _
  obtain ⟨h, hh⟩ : ∃ h : (Fin 4 → ℝ) → ℝ, h = fun x => f (x - v') - f (x - v) := ⟨_, rfl⟩
  have hsup : TestFunctions.uniformNorm h ≤ η := by
    refine ciSup_le fun x => ?_
    have := h₁ (a := x - v') (b := x - v) (by rw [hclose]; exact hv₁)
    rw [Real.dist_eq] at this
    rw [hh, Real.norm_eq_abs]
    exact this.le
  have hderiv : ∀ x ∈ (Set.univ : Set (Fin 4 → ℝ)),
      HasFDerivWithinAt h (fderiv ℝ f (x - v') - fderiv ℝ f (x - v)) Set.univ x := by
    intro x _
    have e₁ : HasFDerivAt (fun y : Fin 4 → ℝ => f (y - v')) (fderiv ℝ f (x - v')) x :=
      by simpa [Function.comp_def] using
        HasFDerivAt.comp x (hd (x - v')) ((hasFDerivAt_id x).sub_const v')
    have e₂ : HasFDerivAt (fun y : Fin 4 → ℝ => f (y - v)) (fderiv ℝ f (x - v)) x :=
      by simpa [Function.comp_def] using
        HasFDerivAt.comp x (hd (x - v)) ((hasFDerivAt_id x).sub_const v)
    rw [hh]
    exact (e₁.sub e₂).hasFDerivWithinAt
  have hbound : ∀ x ∈ (Set.univ : Set (Fin 4 → ℝ)),
      ‖fderiv ℝ f (x - v') - fderiv ℝ f (x - v)‖ ≤ η := by
    intro x _
    have := h₂ (a := x - v') (b := x - v) (by rw [hclose]; exact hv₂)
    rw [dist_eq_norm] at this
    exact this.le
  have hlipset : η ∈ {C : ℝ | 0 ≤ C ∧ ∀ x y : Fin 4 → ℝ,
      ‖h x - h y‖ ≤ C * TestFunctions.euclidDistR4 x y} := by
    refine ⟨hη0.le, fun x y => ?_⟩
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound convex_univ
      (Set.mem_univ y) (Set.mem_univ x)
    exact this.trans (mul_le_mul_of_nonneg_left (pi_norm_le_euclidNormVec _) hη0.le)
  have hlip : TestFunctions.lipConstR4 h ≤ η :=
    csInf_le ⟨0, fun C hC => hC.1⟩ hlipset
  have hnonneg : 0 ≤ TestFunctions.sharpNormR4 M h :=
    le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
  rw [← hh, Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  refine max_lt (by nlinarith) ?_
  have : 40 * M * TestFunctions.lipConstR4 h ≤ 40 * M * η :=
    mul_le_mul_of_nonneg_left hlip (by positivity)
  nlinarith
theorem translationContinuousSharpNorm_holds (s : Conventions.StandingParameters) :
    TranslationContinuousSharpNorm s := by
  intro M f hC1 hcomp v
  have hcs : @HasCompactSupport (Fin 4 → ℝ) ℝ _ _ f :=
    (R4TupleForms.isCompact_tsupport_pt_iff_hasCompactSupport f).1 hcomp
  exact tendsto_sharpNormR4_sub_translate (M : ℝ) (Nat.cast_nonneg M) f hC1 hcs v
end NormAndTranslation
section MultilinearFunctionals
variable (s : Conventions.StandingParameters)
theorem list_ofFn_update {α : Type*} {n : ℕ} [DecidableEq (Fin n)] (f : Fin n → α) (i : Fin n)
    (a : α) :
    List.ofFn (Function.update f i a) =
      (List.ofFn f).take i ++ a :: (List.ofFn f).drop (i + 1) := by
  have h : List.ofFn (Function.update f i a) = (List.ofFn f).set i a := by
    refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    by_cases hk : k = (i : ℕ)
    · simp [hk]
    · simp [hk, Ne.symm hk]
  rw [h, List.set_eq_take_append_cons_drop, if_pos (by simp)]
theorem mem_separatedTuples_of_c1Submodule {n : ℕ} (A : Fin n → Set (Pt s .euclidean))
    (hA : Pairwise fun i j => PositivelySeparated s .euclidean (A i) (A j))
    (g : (i : Fin n) → c1Submodule (A i)) :
    (fun i => (g i : Pt s .euclidean → ℝ)) ∈ separatedTuples s .euclidean n := by
  refine ⟨fun i => ⟨(g i).2.1, (g i).2.2.1⟩, fun i j hij => ?_⟩
  refine Set.disjoint_left.2 fun x hx hx' => hA hij ?_
  refine le_antisymm ?_ bot_le
  refine (iInf₂_le x ((g i).2.2.2 hx)).trans ((iInf₂_le x ((g j).2.2.2 hx')).trans ?_)
  simp [show pointDist s .euclidean x x = 0 from dist_self (α := Pt s .euclidean) x]
theorem positivelySeparated_of_isCompact {A B : Set (Pt s .euclidean)} (hA : IsCompact A)
    (hB : IsCompact B) (h : Disjoint A B) : PositivelySeparated s .euclidean A B := by
  obtain ⟨r, hr, hab⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed h
  intro h₀
  have hle : (r : ENNReal) ≤ setDist s .euclidean A B :=
    le_iInf₂ fun a ha => le_iInf₂ fun b hb => by
      have := (hab a ha b hb).le
      rwa [edist_dist] at this
  rw [h₀] at hle
  exact absurd (ENNReal.coe_pos.2 hr) (not_lt.2 hle)
variable {s}
theorem tupleFunctional_update_eq (σ : SeparatedTuples.TupleFunctional)
    (hσ : σ.IsEntrywiseLinear) {n : ℕ}
    [DecidableEq (Fin n)] (f : Fin n → SeparatedTuples.RealValued) (i : Fin n)
    (a b c : SeparatedTuples.RealValued) (α α' : ℝ) (hc : c = α • a + α' • b)
    (ha : Function.update f i a ∈ separatedTuples s .euclidean n)
    (hb : Function.update f i b ∈ separatedTuples s .euclidean n)
    (hcm : Function.update f i c ∈ separatedTuples s .euclidean n) :
    σ (listOf (⟨⟨n, Function.update f i c⟩, hcm⟩ : FinTuple s)) =
      α * σ (listOf (⟨⟨n, Function.update f i a⟩, ha⟩ : FinTuple s)) +
        α' * σ (listOf (⟨⟨n, Function.update f i b⟩, hb⟩ : FinTuple s)) := by
  subst hc
  exact hσ _ _ a b α α' _ _ _ (list_ofFn_update f i a) (list_ofFn_update f i b)
    (list_ofFn_update f i _)
theorem isTupleMultilinear_ofLength (σ : SeparatedTuples.TupleFunctional)
    (hσ : σ.IsEntrywiseLinear) (n : ℕ) :
    IsTupleMultilinear (ofLength (fun X : FinTuple s => σ (listOf X)) n) := by
  intro A hA
  have hm := mem_separatedTuples_of_c1Submodule s A hA
  have hcoe : ∀ [DecidableEq (Fin n)] (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (x : c1Submodule (A i)),
      (fun l => ((Function.update m i x l : c1Submodule (A l)) :
        Pt s .euclidean → ℝ)) =
      Function.update (fun l => (m l : Pt s .euclidean → ℝ)) i (x : Pt s .euclidean → ℝ) := by
    intro _ m i x
    funext l
    exact Function.apply_update (fun l (y : c1Submodule (A l)) =>
      (y : Pt s .euclidean → ℝ)) m i x l
  have hval : ∀ [DecidableEq (Fin n)] (m : (i : Fin n) → c1Submodule (A i)) (i : Fin n)
      (x : c1Submodule (A i)),
      ∃ hu : Function.update (fun l => (m l : Pt s .euclidean → ℝ)) i
          (x : Pt s .euclidean → ℝ) ∈ separatedTuples s .euclidean n,
        ofLength (fun X : FinTuple s => σ (listOf X)) n
          ⟨fun l => ((Function.update m i x l : c1Submodule (A l)) :
            Pt s .euclidean → ℝ), hm _⟩ =
        σ (listOf (⟨⟨n, Function.update (fun l => (m l : Pt s .euclidean → ℝ)) i
          (x : Pt s .euclidean → ℝ)⟩, hu⟩ : FinTuple s)) := by
    intro _ m i x
    have h := hm (Function.update m i x)
    rw [hcoe] at h
    refine ⟨h, ?_⟩
    simp only [hcoe]
    rfl
  refine ⟨{ toFun := fun g => ofLength (fun X : FinTuple s => σ (listOf X)) n
              ⟨fun i => (g i : Pt s .euclidean → ℝ), hm g⟩
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun g => rfl⟩
  · intro _ m i x y
    obtain ⟨h₁, e₁⟩ := hval m i (x + y)
    obtain ⟨h₂, e₂⟩ := hval m i x
    obtain ⟨h₃, e₃⟩ := hval m i y
    rw [e₁, e₂, e₃]
    have := tupleFunctional_update_eq σ hσ (fun l => (m l : Pt s .euclidean → ℝ)) i
      (x : Pt s .euclidean → ℝ) (y : Pt s .euclidean → ℝ)
      ((x + y : c1Submodule (A i)) : Pt s .euclidean → ℝ) 1 1 (by
        funext z
        change x.1 z + y.1 z = 1 * x.1 z + 1 * y.1 z
        ring) h₂ h₃ h₁
    simpa using this
  · intro _ m i c x
    obtain ⟨h₁, e₁⟩ := hval m i (c • x)
    obtain ⟨h₂, e₂⟩ := hval m i x
    rw [e₁, e₂]
    have := tupleFunctional_update_eq σ hσ (fun l => (m l : Pt s .euclidean → ℝ)) i
      (x : Pt s .euclidean → ℝ) (x : Pt s .euclidean → ℝ)
      ((c • x : c1Submodule (A i)) : Pt s .euclidean → ℝ) c 0 (by
        funext z
        change c * x.1 z = c * x.1 z + 0 * x.1 z
        ring) h₂ h₂ h₁
    simpa using this
theorem isEntrywiseLinear_of_ofLength (σ : SeparatedTuples.TupleFunctional)
    (hσ : ∀ n, 1 ≤ n →
      IsTupleMultilinear (ofLength (fun X : FinTuple s => σ (listOf X)) n)) :
    σ.IsEntrywiseLinear := by
  intro A B f f' α α' X X' Z hX hX' hZ
  have hn : 1 ≤ (A ++ f :: B).length := by
    rw [List.length_append, List.length_cons]
    omega
  set b : Fin (A ++ f :: B).length → SeparatedTuples.RealValued := (A ++ f :: B).get with hb
  let i : Fin (A ++ f :: B).length := ⟨A.length, by simp⟩
  have key : ∀ h, List.ofFn (Function.update b i h) = A ++ h :: B := fun h => by
    rw [list_ofFn_update, hb, List.ofFn_get]
    simp [i]
  have hsep : ∀ (h) (W : SeparatedTuples.SepTuple), W.1 = A ++ h :: B →
      Function.update b i h ∈ separatedTuples s .euclidean (A ++ f :: B).length := fun h W hW =>
    (mem_separatedTuples_iff_ofFn _).2 (by rw [key, ← hW]; exact W.2)
  have hu := hsep f X hX
  have hu' := hsep f' X' hX'
  set u := Function.update b i f with hudef
  set u' := Function.update b i f' with hu'def
  have hne : ∀ l, l ≠ i → u l = u' l := fun l hl => by
    simp [hudef, hu'def, Function.update_of_ne hl]
  let S : Fin (A ++ f :: B).length → Set (Pt s .euclidean) := fun l =>
    tsupport (u l : Pt s .euclidean → ℝ) ∪ tsupport (u' l : Pt s .euclidean → ℝ)
  have hdis : ∀ l k, l ≠ k → Disjoint (S l) (S k) := fun l k hlk => by
    have d₁ := hu.2 hlk
    have d₂ := hu'.2 hlk
    refine Disjoint.union_left (Disjoint.union_right d₁ ?_) (Disjoint.union_right ?_ d₂)
    · by_cases hk : k = i
      · have hl : l ≠ i := hk ▸ hlk
        rw [hne l hl]
        exact d₂
      · rw [← hne k hk]
        exact d₁
    · by_cases hk : k = i
      · have hl : l ≠ i := hk ▸ hlk
        rw [← hne l hl]
        exact d₁
      · rw [hne k hk]
        exact d₂
  have hcomp : ∀ l, IsCompact (S l) := fun l => (hu.1 l).2.union (hu'.1 l).2
  obtain ⟨L, hL⟩ := hσ _ hn S fun l k hlk =>
    positivelySeparated_of_isCompact s (hcomp l) (hcomp k) (hdis l k hlk)
  let G : (l : Fin (A ++ f :: B).length) → c1Submodule (S l) := fun l =>
    ⟨u l, (hu.1 l).1, (hu.1 l).2, Set.subset_union_left⟩
  let mf : c1Submodule (S i) := G i
  let mf' : c1Submodule (S i) := ⟨u' i, (hu'.1 i).1, (hu'.1 i).2, Set.subset_union_right⟩
  have hmf : mf.1 = f := Function.update_self i f b
  have hmf' : mf'.1 = f' := Function.update_self i f' b
  have hvalue : ∀ (m : c1Submodule (S i)) (h : SeparatedTuples.RealValued), m.1 = h →
      ∀ W : SeparatedTuples.SepTuple, W.1 = A ++ h :: B → L (Function.update G i m) = σ W := by
    intro m h hm W hW
    rw [hL]
    have hcoe : (fun l => (Function.update G i m l).1 :
        Fin (A ++ f :: B).length → SeparatedTuples.RealValued) =
        Function.update b i h := by
      funext l
      by_cases hl : l = i
      · subst hl
        rw [Function.update_self]
        exact hm.trans (Function.update_self i h b).symm
      · rw [Function.update_of_ne hl]
        exact (Function.update_of_ne hl f b).trans (Function.update_of_ne hl h b).symm
    change σ (listOf _) = σ W
    congr 1
    exact Subtype.ext ((congrArg List.ofFn hcoe).trans ((key h).trans hW.symm))
  have e₁ := hvalue mf f hmf X hX
  have e₂ := hvalue mf' f' hmf' X' hX'
  have e₃ := hvalue (α • mf + α' • mf') (α • f + α' • f') (by
    funext z
    exact congrArg₂ (fun a c => α * a + α' * c) (congrFun hmf z) (congrFun hmf' z)) Z hZ
  have : L (Function.update G i (α • mf + α' • mf')) =
      α * L (Function.update G i mf) + α' * L (Function.update G i mf') := by
    rw [L.map_update_add, L.map_update_smul, L.map_update_smul]
    simp
  rw [e₁, e₂, e₃] at this
  exact this
variable (s)
theorem functionalsAgree_holds : FunctionalsAgree s := by
  have key : ∀ σ : SeparatedTuples.TupleFunctional, σ.IsEntrywiseLinear ↔
      ∀ n, 1 ≤ n → IsTupleMultilinear (ofLength (fun X : FinTuple s => σ (listOf X)) n) :=
    fun σ => ⟨fun h n _ => isTupleMultilinear_ofLength σ h n,
      isEntrywiseLinear_of_ofLength σ⟩
  refine ⟨key, fun τ => ⟨fun hτ => ?_, ?_⟩⟩
  · have hτ' : ∀ X : FinTuple s, R4TupleForms.toTupleFunctional τ hτ (listOf X) = τ X :=
      fun X => congrArg τ ((R4TupleForms.finTupleEquiv s).symm_apply_apply X)
    refine ⟨R4TupleForms.toTupleFunctional τ hτ, (key _).2 fun n hn => ?_,
      fun X => (hτ' X).symm⟩
    rw [show (fun X : FinTuple s => R4TupleForms.toTupleFunctional τ hτ (listOf X)) = τ
      from funext hτ']
    exact hτ.2 n hn
  · rintro ⟨σ, hσ, h⟩
    obtain rfl : τ = fun X => σ (listOf X) := funext h
    refine ⟨?_, (key σ).1 hσ⟩
    change σ (listOf _) = 1
    rw [R4TupleForms.listOf_nilTuple]
    exact σ.map_nil
end MultilinearFunctionals
section ClassesAndSupports
variable {s : Conventions.StandingParameters}
theorem ofReal_le_setDist_iff {d : ℝ} {A B : Set (Pt s .euclidean)} :
    ENNReal.ofReal d ≤ setDist s .euclidean A B ↔ ∀ a ∈ A, ∀ b ∈ B, d ≤ dist a b := by
  simp only [setDist, le_iInf_iff]
  refine forall₂_congr fun a _ => forall₂_congr fun b _ => ?_
  change ENNReal.ofReal d ≤ ENNReal.ofReal (dist a b) ↔ _
  rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg]
theorem disjoint_of_ofReal_le_setDist {d : ℝ} (hd : 0 < d) {A B : Set (Pt s .euclidean)}
    (h : ENNReal.ofReal d ≤ setDist s .euclidean A B) : Disjoint A B := by
  refine Set.disjoint_left.2 fun a ha hb => ?_
  have := (ofReal_le_setDist_iff).1 h a ha a hb
  rw [dist_self] at this
  linarith
theorem mem_quarterThickening_iff {d : ℝ} (hd : 0 < d) {A : Set (Pt s .euclidean)}
    {x : Pt s .euclidean} : x ∈ quarterThickening s d A ↔ ∃ a ∈ A, dist x a < d / 4 := by
  have hd4 : 0 < d / 4 := by positivity
  simp only [quarterThickening, setDist, Set.mem_ofPred_eq, iInf_lt_iff, Set.mem_singleton_iff,
    exists_prop]
  constructor
  · rintro ⟨_, rfl, a, ha, h⟩
    exact ⟨a, ha, (ENNReal.ofReal_lt_ofReal_iff hd4).1 h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨x, rfl, a, ha, (ENNReal.ofReal_lt_ofReal_iff hd4).2 h⟩
theorem abs_sub_apply_le_euclidNormVec (x y : Fin 4 → ℝ) (μ : Fin 4) :
    |x μ - y μ| ≤ TorusMetric.euclidNormVec (x - y) := by
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun ν => (x - y) ν ^ 2) (fun ν _ => sq_nonneg _)
    (Finset.mem_univ μ)
theorem abs_apply_le_maxNorm (x : Fin 4 → ℝ) (μ : Fin 4) : |x μ| ≤ maxNorm x :=
  Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
theorem exists_abs_apply_eq_maxNorm (x : Fin 4 → ℝ) : ∃ μ, |x μ| = maxNorm x := by
  obtain ⟨μ, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun μ => |x μ|)
  exact ⟨μ, h.symm⟩
theorem maxNorm_le_of_forall {x : Fin 4 → ℝ} {c : ℝ} (h : ∀ μ, |x μ| ≤ c) : maxNorm x ≤ c :=
  Finset.sup'_le _ _ fun μ _ => h μ
theorem maxNorm_add_le (x y : Fin 4 → ℝ) : maxNorm (x + y) ≤ maxNorm x + maxNorm y :=
  maxNorm_le_of_forall fun μ => (abs_add_le _ _).trans
    (add_le_add (abs_apply_le_maxNorm x μ) (abs_apply_le_maxNorm y μ))
theorem zero_le_maxNorm (x : Fin 4 → ℝ) : 0 ≤ maxNorm x :=
  (abs_nonneg _).trans (abs_apply_le_maxNorm x 0)
def homeoOfDistIsometry (r : Pt s .euclidean ≃ Pt s .euclidean) (hr : IsDistIsometry r) :
    Pt s .euclidean ≃ₜ Pt s .euclidean :=
  (IsometryEquiv.mk r (Isometry.of_dist_eq hr)).toHomeomorph
theorem tsupport_transportFn (r : Pt s .euclidean ≃ Pt s .euclidean)
    (hr : IsDistIsometry r) (f : Pt s .euclidean → ℝ) :
    tsupport (transportFn r f) = r '' tsupport f := by
  have h : Function.support (transportFn r f) = r '' Function.support f := by
    ext x
    simp only [Function.mem_support, transportFn, Function.comp_apply, Set.mem_image]
    exact ⟨fun hx => ⟨r.symm x, hx, r.apply_symm_apply x⟩, by
      rintro ⟨y, hy, rfl⟩
      simpa using hy⟩
  unfold tsupport
  rw [h]
  exact ((homeoOfDistIsometry r hr).image_closure _).symm
theorem isDistIsometry_symm {r : Pt s .euclidean ≃ Pt s .euclidean} (hr : IsDistIsometry r) :
    IsDistIsometry r.symm := by apply _root_.YangMills.Construction.FourSpaceSymbols.isDistIsometry_symm <;> assumption
theorem contDiff_of_isDistIsometry {r : Pt s .euclidean ≃ Pt s .euclidean}
    (hr : IsDistIsometry r) :
    ContDiff ℝ 1 (fun x : Fin 4 → ℝ => (show Fin 4 → ℝ from r x)) := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.contDiff_of_isDistIsometry <;> assumption
theorem isC1Fn_transportFn {r : Pt s .euclidean ≃ Pt s .euclidean}
    (hr : IsDistIsometry r) {f : Pt s .euclidean → ℝ} (hf : IsC1Fn f) :
    IsC1Fn (transportFn r f) :=
  have hg : ContDiff ℝ 1 (show (Fin 4 → ℝ) → ℝ from f) := hf
  hg.comp (contDiff_of_isDistIsometry (isDistIsometry_symm hr))
theorem transportTuple_mem_separatedTuples {r : Pt s .euclidean ≃ Pt s .euclidean}
    (hr : IsDistIsometry r) {n : ℕ} {f : Fin n → Pt s .euclidean → ℝ}
    (hf : f ∈ separatedTuples s .euclidean n) :
    transportTuple r f ∈ separatedTuples s .euclidean n := by
  refine ⟨fun i => ⟨isC1Fn_transportFn hr (hf.1 i).1, ?_⟩, fun i j hij => ?_⟩
  · show IsCompact (tsupport (transportFn r (f i)))
    rw [tsupport_transportFn r hr]
    exact (hf.1 i).2.image (homeoOfDistIsometry r hr).continuous
  · show Disjoint (tsupport (transportFn r (f i))) (tsupport (transportFn r (f j)))
    rw [tsupport_transportFn r hr, tsupport_transportFn r hr]
    exact (Set.disjoint_image_iff r.injective).2 (hf.2 hij)
theorem isSupportedInBalls_transportTuple {r : Pt s .euclidean ≃ Pt s .euclidean}
    (hr : IsDistIsometry r) {n : ℕ} {R : ℝ} {f : Fin n → Pt s .euclidean → ℝ}
    (hf : IsSupportedInBalls R f) : IsSupportedInBalls R (transportTuple r f) := by
  intro i
  obtain ⟨B, ⟨hR, x, rfl⟩, hB⟩ := hf i
  refine ⟨closedBall s .euclidean (r x) R, ⟨hR, r x, rfl⟩, ?_⟩
  show tsupport (transportFn r (f i)) ⊆ _
  rw [tsupport_transportFn r hr]
  rintro _ ⟨y, hy, rfl⟩
  have h1 := hB hy
  show pointDist s .euclidean (r y) (r x) ≤ R
  rw [hr]
  exact h1
theorem pairwiseSupportSep_transportTuple {r : Pt s .euclidean ≃ Pt s .euclidean}
    (hr : IsDistIsometry r) {n : ℕ} {d : ℝ} {f : Fin n → Pt s .euclidean → ℝ}
    (hf : PairwiseSupportSep s d f) : PairwiseSupportSep s d (transportTuple r f) := by
  intro i j hij
  show _ ≤ setDist s .euclidean (tsupport (transportFn r (f i)))
    (tsupport (transportFn r (f j)))
  rw [tsupport_transportFn r hr, tsupport_transportFn r hr,
    ofReal_le_setDist_iff]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have := (ofReal_le_setDist_iff).1 (hf hij) a ha b hb
  rw [show dist (r a) (r b) = dist a b from hr a b]
  exact this
theorem isometryPreservesSharpNorm_holds (s : Conventions.StandingParameters) :
    IsometryPreservesSharpNorm s :=
  fun M r hr f _ _ => sharpNormAt_transportFn s M r hr f
theorem isometryPreservesSupportedTuples_holds (s : Conventions.StandingParameters) :
    IsometryPreservesSupportedTuples s :=
  fun _ hr _ _ _ _ _ hX hR hD => ⟨transportTuple_mem_separatedTuples hr hX,
    isSupportedInBalls_transportTuple hr hR, pairwiseSupportSep_transportTuple hr hD⟩
theorem classesMonotone_holds (s : Conventions.StandingParameters) : ClassesMonotone s := by
  intro ϖ ϖ' d d' R R' _ _ hϖ hd' hdd _ hR hRR X hX
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hX
  refine ⟨h₁, fun i => ?_, fun i x hx => ?_, fun i k hik => ?_⟩
  · obtain ⟨B, ⟨-, y, rfl⟩, hB⟩ := h₂ i
    refine ⟨closedBall s .euclidean y R', ⟨hR.trans_le hRR, y, rfl⟩, hB.trans fun z hz => ?_⟩
    exact le_trans hz hRR
  · have : maxNorm x < ϖ - d / 2 := h₃ i hx
    show maxNorm x < ϖ' - d' / 2
    linarith
  · exact (ENNReal.ofReal_le_ofReal hdd).trans (h₄ hik)
theorem finiteFamilyInOneClass_holds (hfacts : ContinuumSetting.SettingFacts)
    (s : Conventions.StandingParameters) : FiniteFamilyInOneClass s := by
  have hone := hfacts.2.2.2.2.1 s
  intro n
  induction n with
  | zero =>
    intro X _
    obtain ⟨ϖ, hϖ, d, R, hd, hdϖ, hR, -⟩ := hone (nilTuple s .euclidean) nilTuple_mem_allSeparatedTuples
    exact ⟨ϖ, hϖ, d, R, hd, hdϖ, hR, fun b => b.elim0⟩
  | succ n ih =>
    intro X hX
    obtain ⟨ϖ₁, hϖ₁, d₁, R₁, hd₁, hdϖ₁, hR₁, h₁⟩ := ih (fun b => X b.succ) fun b => hX b.succ
    obtain ⟨ϖ₂, hϖ₂, d₂, R₂, hd₂, hdϖ₂, hR₂, h₂⟩ := hone (X 0) (hX 0)
    have hmax : max ϖ₁ ϖ₂ ∈ adicRationalsPositive s.L := by
      rcases max_choice ϖ₁ ϖ₂ with h | h <;> rw [h] <;> assumption
    have hmin : 0 < min d₁ d₂ := lt_min hd₁ hd₂
    have hle : min d₁ d₂ ≤ max ϖ₁ ϖ₂ := (min_le_left _ _).trans (hdϖ₁.trans (le_max_left _ _))
    refine ⟨max ϖ₁ ϖ₂, hmax, min d₁ d₂, max R₁ R₂, hmin, hle, hR₁.trans_le (le_max_left _ _), ?_⟩
    refine Fin.cases ?_ (fun b => ?_)
    · exact classesMonotone_holds s _ _ _ _ _ _ hϖ₂ hmax (le_max_right _ _) hmin
        (min_le_right _ _) hdϖ₂ hR₂ (le_max_right _ _) h₂
    · exact classesMonotone_holds s _ _ _ _ _ _ hϖ₁ hmax (le_max_left _ _) hmin
        (min_le_left _ _) hdϖ₁ hR₁ (le_max_left _ _) (h₁ b)
def signedPermEquiv (s : Conventions.StandingParameters)
    (w : InfiniteLattice.hyperoctahedralLinearGroup) :
    Pt s .euclidean ≃ Pt s .euclidean :=
  (w.1 : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)).toEquiv
theorem signedPermFn_eq (w : InfiniteLattice.hyperoctahedralLinearGroup)
    (f : Pt s .euclidean → ℝ) :
    signedPermFn w f = transportFn (signedPermEquiv s w) f :=
  rfl
theorem euclidNormVec_signedPerm (w : InfiniteLattice.hyperoctahedralLinearGroup)
    (x y : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (w.1 x - w.1 y) = TorusMetric.euclidNormVec (x - y) := by
  obtain ⟨π, ε, h⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w.1).1 w.2
  unfold TorusMetric.euclidNormVec
  congr 1
  have hsq : ∀ μ, (((ε μ : ℤ) : ℝ)) ^ 2 = 1 := fun μ => by
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
  have hterm : ∀ μ, (w.1 x - w.1 y) μ ^ 2 = (x - y) (π μ) ^ 2 := fun μ => by
    rw [Pi.sub_apply, h, h, Pi.sub_apply, ← mul_sub, mul_pow, hsq, one_mul]
  simp only [hterm]
  exact Equiv.sum_comp π (fun μ => (x - y) μ ^ 2)
theorem isDistIsometry_signedPermEquiv (w : InfiniteLattice.hyperoctahedralLinearGroup) :
    IsDistIsometry (signedPermEquiv s w) :=
  fun x y => euclidNormVec_signedPerm w x y
theorem maxNorm_signedPerm_le (w : InfiniteLattice.hyperoctahedralLinearGroup) (x : Fin 4 → ℝ) :
    maxNorm (w.1 x) ≤ maxNorm x := by
  obtain ⟨π, ε, h⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w.1).1 w.2
  refine maxNorm_le_of_forall fun μ => ?_
  have habs : |((ε μ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
  rw [h, abs_mul, habs, one_mul]
  exact abs_apply_le_maxNorm x _
theorem signedPermTuple_mem_classOf (w : InfiniteLattice.hyperoctahedralLinearGroup) {ϖ d R : ℝ}
    {X : FunctionTuple s .euclidean} (hX : X ∈ classOf s ϖ d R) :
    signedPermTuple w X ∈ classOf s ϖ d R := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hX
  have hr := isDistIsometry_signedPermEquiv (s := s) w
  refine ⟨transportTuple_mem_separatedTuples hr h₁, isSupportedInBalls_transportTuple hr h₂,
    fun i => ?_, pairwiseSupportSep_transportTuple hr h₄⟩
  show tsupport (transportFn (signedPermEquiv s w) (X.2 i)) ⊆ _
  rw [tsupport_transportFn _ hr]
  rintro _ ⟨y, hy, rfl⟩
  exact (maxNorm_signedPerm_le w y).trans_lt (h₃ i hy)
theorem signedPermTuple_inv_cancel (w : InfiniteLattice.hyperoctahedralLinearGroup)
    (X : FunctionTuple s .euclidean) :
    signedPermTuple w (signedPermTuple w⁻¹ X) = X := by
  obtain ⟨n, f⟩ := X
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i x
  show f i ((w⁻¹).1.symm (w.1.symm x)) = f i x
  congr 1
  exact w.1.apply_symm_apply x
theorem hyperoctahedralPreservesClasses_holds (s : Conventions.StandingParameters) :
    HyperoctahedralPreservesClasses s := by
  intro w ϖ d R _ _ _ _
  refine ⟨Set.Subset.antisymm ?_ fun X hX => ?_, fun M Cstar C₁ X _ => ⟨?_, ?_⟩⟩
  · rintro _ ⟨X, hX, rfl⟩
    exact signedPermTuple_mem_classOf w hX
  · exact ⟨_, signedPermTuple_mem_classOf w⁻¹ hX, signedPermTuple_inv_cancel w X⟩
  · show momentConst Cstar C₁ X.1 d R * ∏ i, sharpNormAt s .euclidean M
        (signedPermFn w (X.2 i)) = _
    simp only [signedPermFn_eq,
      sharpNormAt_transportFn s M _ (isDistIsometry_signedPermEquiv w)]
    rfl
  · show momentConst Cstar C₁ (2 * X.1) d R * ∏ i, sharpNormAt s .euclidean M
        (signedPermFn w (X.2 i)) ^ 2 = _
    simp only [signedPermFn_eq,
      sharpNormAt_transportFn s M _ (isDistIsometry_signedPermEquiv w)]
    rfl
theorem forall_tupleAppend {X Y : FunctionTuple s .euclidean}
    {p : (Pt s .euclidean → ℝ) → Prop} (hX : ∀ i, p (X.2 i)) (hY : ∀ j, p (Y.2 j)) :
    ∀ i, p ((tupleAppend X Y).2 i) := by
  intro i
  show p (Fin.append X.2 Y.2 i)
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact hX i
  | right j => rw [Fin.append_right]; exact hY j
theorem pairwise_tupleAppend {X Y : FunctionTuple s .euclidean}
    {q : (Pt s .euclidean → ℝ) → (Pt s .euclidean → ℝ) → Prop}
    (hq : ∀ f g, q f g → q g f) (hX : Pairwise fun i j => q (X.2 i) (X.2 j))
    (hY : Pairwise fun i j => q (Y.2 i) (Y.2 j)) (hXY : ∀ i j, q (X.2 i) (Y.2 j)) :
    Pairwise fun i j => q ((tupleAppend X Y).2 i) ((tupleAppend X Y).2 j) := by
  intro a b hab
  show q (Fin.append X.2 Y.2 a) (Fin.append X.2 Y.2 b)
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Fin.append_left, Fin.append_left]
      exact hX fun h => hab (by rw [h])
    | right j =>
      rw [Fin.append_left, Fin.append_right]
      exact hXY i j
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Fin.append_right, Fin.append_left]
      exact hq _ _ (hXY j i)
    | right j =>
      rw [Fin.append_right, Fin.append_right]
      exact hY fun h => hab (by rw [h])
theorem le_euclidNormVec_of_far {ϖ d : ℝ} {a z v : Fin 4 → ℝ} (ha : maxNorm a < ϖ - d / 2)
    (hz : maxNorm z < ϖ - d / 2) (hv : 2 * ϖ < maxNorm v) :
    d ≤ TorusMetric.euclidNormVec (a - (z + v)) := by
  obtain ⟨μ, hμ⟩ := exists_abs_apply_eq_maxNorm v
  have h₁ := abs_apply_le_maxNorm a μ
  have h₂ := abs_apply_le_maxNorm z μ
  have h₃ : |a μ - (z + v) μ| ≤ TorusMetric.euclidNormVec (a - (z + v)) :=
    abs_sub_apply_le_euclidNormVec a (z + v) μ
  have h₄ : (z + v) μ = z μ + v μ := rfl
  rw [h₄] at h₃
  cases abs_cases (v μ) <;> cases abs_cases (a μ - (z μ + v μ)) <;> cases abs_cases (a μ) <;>
    cases abs_cases (z μ) <;> linarith
theorem farTranslatesInClass_holds (s : Conventions.StandingParameters) :
    FarTranslatesInClass s := by
  intro ϖ d R _ hd _ _ X hX Y hY v hv
  obtain ⟨x₁, x₂, x₃, x₄⟩ := hX
  obtain ⟨y₁, y₂, y₃, y₄⟩ := hY
  have hr : IsDistIsometry (R4TupleForms.shiftEquiv s v) :=
    R4TupleForms.isDistIsometry_shiftEquiv v
  have t₁ : (translateTuple v Y).2 ∈ separatedTuples s .euclidean (translateTuple v Y).1 :=
    transportTuple_mem_separatedTuples hr y₁
  have t₂ : IsSupportedInBalls R (translateTuple v Y).2 := isSupportedInBalls_transportTuple hr y₂
  have t₄ : PairwiseSupportSep s d (translateTuple v Y).2 :=
    pairwiseSupportSep_transportTuple hr y₄
  have t₃ : ∀ j : Fin Y.1, tsupport ((translateTuple v Y).2 j) =
      R4TupleForms.shiftEquiv s v '' tsupport (Y.2 j) := fun j =>
    tsupport_transportFn _ hr (Y.2 j)
  have hdist : PairwiseSupportSep s d (tupleAppend X (translateTuple v Y)).2 := by
    refine pairwise_tupleAppend
      (q := fun f g => ENNReal.ofReal d ≤ setDist s .euclidean (tsupport f) (tsupport g))
      (fun f g h => ?_) x₄ t₄ fun i j => ?_
    · rw [ofReal_le_setDist_iff] at h ⊢
      exact fun a ha b hb => (h b hb a ha).trans_eq (dist_comm _ _)
    · show _ ≤ setDist s .euclidean _ (tsupport ((translateTuple v Y).2 j))
      rw [t₃ j, ofReal_le_setDist_iff]
      rintro a ha _ ⟨z, hz, rfl⟩
      exact le_euclidNormVec_of_far (x₃ i ha) (y₃ j hz) hv
  have hsep : tupleAppend X (translateTuple v Y) ∈ allSeparatedTuples s .euclidean :=
    ⟨forall_tupleAppend (p := fun f => IsC1Fn f ∧ IsCompact (tsupport f)) x₁.1 t₁.1,
      fun i j hij => disjoint_of_ofReal_le_setDist hd (hdist hij)⟩
  have hsupp : IsSupportedInBalls R (tupleAppend X (translateTuple v Y)).2 :=
    forall_tupleAppend
      (p := fun f => ∃ B, IsClosedBallRadius s .euclidean R B ∧ tsupport f ⊆ B) x₂ t₂
  refine ⟨hsep, hsupp, hdist, fun ϖ' _ hϖ' => ⟨hsep, hsupp, ?_, hdist⟩⟩
  refine forall_tupleAppend (p := fun f => tsupport f ⊆ centredCube (ϖ' - d / 2))
    (fun i a ha => ?_) fun j => ?_
  · have h₁ : maxNorm a < ϖ - d / 2 := x₃ i ha
    have h₂ := zero_le_maxNorm v
    show maxNorm a < ϖ' - d / 2
    linarith
  · show tsupport ((translateTuple v Y).2 j) ⊆ _
    rw [t₃ j]
    rintro _ ⟨z, hz, rfl⟩
    have h₁ : maxNorm z < ϖ - d / 2 := y₃ j hz
    have h₂ := maxNorm_add_le z v
    show maxNorm ((show Fin 4 → ℝ from z) + v) < ϖ' - d / 2
    linarith
theorem isOpen_quarterThickening {d : ℝ} (hd : 0 < d) (A : Set (Pt s .euclidean)) :
    IsOpen (quarterThickening s d A) := by
  have h : quarterThickening s d A = ⋃ a ∈ A, Metric.ball a (d / 4) := by
    ext x
    simp only [mem_quarterThickening_iff hd, Set.mem_iUnion, Metric.mem_ball, exists_prop]
  rw [h]
  exact isOpen_biUnion fun _ _ => Metric.isOpen_ball
theorem supportNeighbourhoods_holds (s : Conventions.StandingParameters) :
    SupportNeighbourhoods s := by
  intro d R hd hR X _ hX hD
  have hd4 : 0 < d / 4 := by positivity
  refine ⟨fun i => ⟨isOpen_quarterThickening hd _, fun a ha => ?_, ?_⟩, fun i k hik => ?_,
    fun v v' hv i y hy => ?_⟩
  · exact (mem_quarterThickening_iff hd).2 ⟨a, ha, by rwa [dist_self]⟩
  · obtain ⟨B, ⟨-, x, rfl⟩, hB⟩ := hX i
    refine ⟨closedBall s .euclidean x (R + d / 4), ⟨by positivity, x, rfl⟩, fun y hy => ?_⟩
    obtain ⟨a, ha, h⟩ := (mem_quarterThickening_iff hd).1 hy
    have h₁ : dist a x ≤ R := hB ha
    have h₂ := dist_triangle y a x
    show dist y x ≤ R + d / 4
    linarith
  · refine ofReal_le_setDist_iff.2 fun y hy y' hy' => ?_
    obtain ⟨a, ha, h⟩ := (mem_quarterThickening_iff hd).1 hy
    obtain ⟨b, hb, h'⟩ := (mem_quarterThickening_iff hd).1 hy'
    have h₁ := (ofReal_le_setDist_iff).1 (hD hik) a ha b hb
    have h₂ := dist_triangle4 a y y' b
    rw [dist_comm a y] at h₂
    linarith
  · have hr : IsDistIsometry (R4TupleForms.shiftEquiv s v') :=
      R4TupleForms.isDistIsometry_shiftEquiv v'
    have hsupp : tsupport (translateFn v' (X.2 i)) =
        R4TupleForms.shiftEquiv s v' '' tsupport (X.2 i) :=
      tsupport_transportFn _ hr (X.2 i)
    rw [hsupp] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    let z' : Fin 4 → ℝ := z
    refine ⟨(show Pt s .euclidean from z' + v' - v), (mem_quarterThickening_iff hd).2 ⟨z, hz, ?_⟩, ?_⟩
    · have : TorusMetric.euclidNormVec (z' + v' - v - z') = TorusMetric.euclidNormVec (v' - v) := by
        congr 1
        abel
      exact this.trans_lt hv
    · show z' + v' - v + v = z' + v'
      abel
theorem separatingTuplesAreSeparated_holds (s : Conventions.StandingParameters) :
    SeparatingTuplesAreSeparated s := by
  intro X hX
  rcases hX with hX | hX
  · have hX' : X = [] := hX
    subst hX'
    exact ⟨⟨by simp, List.Pairwise.nil⟩, fun h => absurd rfl h⟩
  · obtain ⟨hne, Q, hdis, hQ⟩ := hX
    have hentry : ∀ i : Fin X.length, TestFunctions.IsC1R4 (X.get i) ∧
        HasCompactSupport (X.get i) ∧ tsupport (X.get i) ⊆ (Q i : Set (Fin 4 → ℝ)) := fun i =>
      (TestFunctions.mem_c1ZeroOff_iff (Q i).2).1 (hQ i).2
    have hmem : ∀ f ∈ X, TestFunctions.IsC1R4 f ∧ HasCompactSupport f := fun f hf => by
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
      exact ⟨(hentry i).1, (hentry i).2.1⟩
    have hpair : X.Pairwise fun f h => Disjoint (tsupport f) (tsupport h) :=
      List.pairwise_iff_get.2 fun i k hik =>
        (hdis hik.ne).mono (hentry i).2.2 (hentry k).2.2
    exact ⟨⟨hmem, hpair⟩, fun _ => ⟨hmem, hpair⟩⟩
end ClassesAndSupports
theorem classFacts_holds (hfacts : ContinuumSetting.SettingFacts) : ClassFacts := fun s =>
  ⟨functionalsAgree_holds s, classesMonotone_holds s,
    finiteFamilyInOneClass_holds hfacts s, isometryPreservesSharpNorm_holds s,
    isometryPreservesSupportedTuples_holds s, hyperoctahedralPreservesClasses_holds s,
    farTranslatesInClass_holds s, translationContinuousSharpNorm_holds s,
    supportNeighbourhoods_holds s, separatingTuplesAreSeparated_holds s⟩
end YangMills.Construction.SeparatedClasses
