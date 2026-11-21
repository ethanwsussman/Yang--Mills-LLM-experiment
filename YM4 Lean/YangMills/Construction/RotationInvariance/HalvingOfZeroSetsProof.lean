import YangMills.Construction.Analysis.ZerosOfAnalyticMapsAndThinSets
import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import YangMills.Construction.RotationInvariance.HalvingOfZeroSets
import YangMills.Construction.RotationInvariance.LineSidesAndReflectionByRotations
import YangMills.Construction.RotationInvariance.PositivityOfTheTopHarmonicAcrossEveryLine
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube
open scoped Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.VanishingSetHalving
abbrev PointWithLabel : Type := RealPlane × realLabels
section Append
variable {α β : Type*} {a b : ℕ}
theorem range_finAppend (u : Fin a → α) (v : Fin b → α) :
    Set.range (Fin.append u v) = Set.range u ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simp⟩
    | right j => exact Or.inr ⟨j, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd b i, by simp⟩
    · exact ⟨Fin.natAdd a j, by simp⟩
theorem range_eq_union_castAdd_natAdd (f : Fin (a + b) → α) :
    Set.range f = Set.range (fun i => f (Fin.castAdd b i)) ∪
      Set.range (fun j => f (Fin.natAdd a j)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, rfl⟩
    | right j => exact Or.inr ⟨j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
theorem comp_finAppend (f : α → β) (u : Fin a → α) (v : Fin b → α) :
    (fun i => f (Fin.append u v i)) = Fin.append (fun i => f (u i)) (fun j => f (v j)) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right j => simp
theorem finAppend_injective {u : Fin a → α} {v : Fin b → α} (hu : Function.Injective u)
    (hv : Function.Injective v) (hd : ∀ i j, u i ≠ v j) :
    Function.Injective (Fin.append u v) := by
  intro x y h
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left k =>
      rw [Fin.append_left, Fin.append_left] at h
      rw [hu h]
    | right k =>
      rw [Fin.append_left, Fin.append_right] at h
      exact absurd h (hd i k)
  | right j =>
    induction y using Fin.addCases with
    | left k =>
      rw [Fin.append_right, Fin.append_left] at h
      exact absurd h.symm (hd k j)
    | right k =>
      rw [Fin.append_right, Fin.append_right] at h
      rw [hv h]
theorem injective_right_of_finAppend {u : Fin a → α} {v : Fin b → α}
    (h : Function.Injective (Fin.append u v)) : Function.Injective v := by
  intro i j hij
  have : Fin.append u v (Fin.natAdd a i) = Fin.append u v (Fin.natAdd a j) := by
    rw [Fin.append_right, Fin.append_right, hij]
  exact (Fin.natAdd_injective b a) (h this)
theorem left_ne_right_of_finAppend {u : Fin a → α} {v : Fin b → α}
    (h : Function.Injective (Fin.append u v)) (i : Fin a) (j : Fin b) : u i ≠ v j := by
  intro hij
  have : Fin.append u v (Fin.castAdd b i) = Fin.append u v (Fin.natAdd a j) := by
    rw [Fin.append_left, Fin.append_right, hij]
  have h' := h this
  have hv := congrArg Fin.val h'
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega
end Append
section Enumerations
variable {n : ℕ}
def labelledPointsOf (e : Fin n → PointWithLabel) : LabelledPoints n where
  points := fun i => (e i).1
  labels := fun i => ((e i).2 : RealPlane → ℝ)
  labels_mem := fun i => (e i).2.2
theorem graph_labelledPointsOf (e : Fin n → PointWithLabel) :
    (labelledPointsOf e).graph = Set.range e :=
  rfl
theorem isDistinctLabelledSet_range {e : Fin n → PointWithLabel}
    (he : Function.Injective fun i => (e i).1) :
    IsDistinctLabelledSet n (Set.range e) := by
  have hinj : Function.Injective e := fun i j h => he (congrArg Prod.fst h)
  refine ⟨?_, ?_⟩
  · rw [← Set.image_univ, hinj.encard_image]
    simp
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    rw [he h]
theorem exists_injective_enum {Y : Set PointWithLabel} (hY : IsDistinctLabelledSet n Y) :
    ∃ e : Fin n → PointWithLabel, (Function.Injective fun i => (e i).1) ∧ Set.range e = Y := by
  have hfin : Y.Finite := Set.finite_of_encard_eq_coe hY.card_eq
  have hcard : Nat.card Y = n := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hY.card_eq]
    simp
  have := hfin.to_subtype
  let E := Finite.equivFinOfCardEq hcard
  refine ⟨fun i => (E.symm i).1, ?_, ?_⟩
  · intro i j h
    exact E.symm.injective (Subtype.ext (hY.fst_injOn (E.symm i).2 (E.symm j).2 h))
  · ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact (E.symm i).2
    · intro hp
      exact ⟨E ⟨p, hp⟩, by simp⟩
variable {m : SharpScale} {S : ConnFamily}
theorem pointHarmonic_permute (H : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) (hn : 2 ≤ n) (h : ℤ) (φ : Fin n → realLabels)
    (ς : Equiv.Perm (Fin n)) {y : Fin n → RealPlane} (hy : y ∈ injectivePointTuples n) :
    pointHarmonic S d.angle h n (permuteTuple ς φ) (permuteTuple ς y) =
      pointHarmonic S d.angle h n φ y := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
  exact (H m S d (q + 1) (by omega) h φ).2.2.1 ς y hy
theorem labelledSetHarmonic_range (H : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) (hn : 2 ≤ n) (h : ℤ) {e : Fin n → PointWithLabel}
    (he : Function.Injective fun i => (e i).1) :
    labelledSetHarmonic S d.angle h n (Set.range e) =
      pointHarmonic S d.angle h n (fun i => (e i).2) (fun i => (e i).1) := by
  have hinj : Function.Injective e := fun i j hij => he (congrArg Prod.fst hij)
  have hex : ∃ v, ∃ c : LabelledPoints n,
      Enumerates (Set.range e) c ∧ configHarmonic S d.angle h c = v :=
    ⟨_, labelledPointsOf e, ⟨isDistinctLabelledSet_range he, (graph_labelledPointsOf e).symm⟩, rfl⟩
  obtain ⟨c, ⟨-, hc⟩, hv⟩ := Classical.epsilon_spec hex
  rw [labelledSetHarmonic, ← hv]
  have hmem : ∀ i, ∃ j, e j = (c.points i, c.labelVec i) := fun i => by
    have hi : (c.points i, c.labelVec i) ∈ c.graph := ⟨i, rfl⟩
    rw [← hc] at hi
    exact hi
  choose g hg using hmem
  have hsurj : Function.Surjective g := by
    intro j
    have hj : e j ∈ c.graph := hc ▸ Set.mem_range_self j
    obtain ⟨i, hi⟩ := hj
    exact ⟨i, hinj ((hg i).trans hi)⟩
  have hbij : Function.Bijective g := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hpos : c.points = permuteTuple (Equiv.ofBijective g hbij) (fun i => (e i).1) :=
    funext fun i => by
      show c.points i = (e (g i)).1
      rw [hg]
  have hlab : c.labelVec = permuteTuple (Equiv.ofBijective g hbij) (fun i => (e i).2) :=
    funext fun i => by
      show c.labelVec i = (e (g i)).2
      rw [hg]
  rw [configHarmonic, hlab, hpos]
  exact pointHarmonic_permute H d hn h _ _ he
end Enumerations
section WilsonWeightSeriesExpansion
variable {m : SharpScale} {S : ConnFamily} {k : ℕ}
def reflectPoint (l : Set RealPlane) (p : PointWithLabel) : PointWithLabel :=
  (lineReflection l p.1, p.2)
theorem reflectLabelled_eq_image (l : Set RealPlane) (Y : Set PointWithLabel) :
    reflectLabelled l Y = reflectPoint l '' Y :=
  rfl
def crossTuple (l : Set RealPlane) (ex ez : Fin k → PointWithLabel) :
    Fin (2 * k) → PointWithLabel :=
  fun i => Fin.append (fun i => reflectPoint l (ex i)) ez (Fin.cast (two_mul k) i)
theorem range_crossTuple (l : Set RealPlane) (ex ez : Fin k → PointWithLabel) :
    Set.range (crossTuple l ex ez) =
      reflectLabelled l (Set.range ex) ∪ Set.range ez := by
  have h : Set.range (crossTuple l ex ez) =
      Set.range (Fin.append (fun i => reflectPoint l (ex i)) ez) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast (two_mul k).symm i, by simp [crossTuple]⟩
  rw [h, range_finAppend, reflectLabelled_eq_image, ← Set.range_comp]
  rfl
theorem crossTuple_fst_injective {l P : Set RealPlane}
    (hθ : Function.Injective (lineReflection l))
    (hθP : ∀ y ∈ P, lineReflection l y ∉ P) {ex ez : Fin k → PointWithLabel}
    (hx : Function.Injective fun i => (ex i).1) (hz : Function.Injective fun i => (ez i).1)
    (hxP : ∀ i, (ex i).1 ∈ P) (hzP : ∀ i, (ez i).1 ∈ P) :
    Function.Injective fun i => (crossTuple l ex ez i).1 := by
  have h1 : Function.Injective
      (Fin.append (fun i => lineReflection l (ex i).1) (fun j => (ez j).1)) :=
    finAppend_injective (fun i j h => hx (hθ h)) hz fun i j h => hθP _ (hxP i) (h ▸ hzP j)
  have h2 : (fun i => (crossTuple l ex ez i).1) =
      fun i => Fin.append (fun i => lineReflection l (ex i).1) (fun j => (ez j).1)
        (Fin.cast (two_mul k) i) :=
    funext fun i => congrFun (comp_finAppend Prod.fst (fun i => reflectPoint l (ex i)) ez) _
  rw [h2]
  exact h1.comp (Fin.cast_injective _)
theorem topLabelledHarmonic_cross (H : DistinctHarmonics.Holds)
    (d : PlaneDataWithAperture m S) (hk : 1 ≤ k) {l P : Set RealPlane}
    (hθ : Function.Injective (lineReflection l))
    (hθP : ∀ y ∈ P, lineReflection l y ∉ P) {ex ez : Fin k → PointWithLabel}
    (hx : Function.Injective fun i => (ex i).1) (hz : Function.Injective fun i => (ez i).1)
    (hxP : ∀ i, (ex i).1 ∈ P) (hzP : ∀ i, (ez i).1 ∈ P) :
    topLabelledHarmonic S d.angle k
        (reflectLabelled l (Set.range ex) ∪ Set.range ez) =
      TopCoeffLinePositivity.topCoeffMapAppend S d.angle
        (lineReflection l) (labelledPointsOf ex) (labelledPointsOf ez) := by
  have hinj := crossTuple_fst_injective hθ hθP hx hz hxP hzP
  rw [← range_crossTuple, topLabelledHarmonic,
    labelledSetHarmonic_range H d (by omega) _ hinj]
  have hlab : (fun i => (crossTuple l ex ez i).2) =
      tupleTwoMul (Fin.append (labelledPointsOf ex).labelVec (labelledPointsOf ez).labelVec) :=
    funext fun i => congrFun (comp_finAppend Prod.snd (fun i => reflectPoint l (ex i)) ez) _
  have hpos : (fun i => (crossTuple l ex ez i).1) =
      tupleTwoMul (mapAppend (lineReflection l)
        (labelledPointsOf ex).points (labelledPointsOf ez).points) :=
    funext fun i => congrFun (comp_finAppend Prod.fst (fun i => reflectPoint l (ex i)) ez) _
  rw [hlab, hpos]
  rfl
end WilsonWeightSeriesExpansion
section Analytic
def planeCoordEquiv (p : ℕ) : (Fin p → RealPlane) ≃ₗ[ℝ] (Fin (p * 2) → ℝ) where
  toFun y j := y (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  map_add' x y := by
    ext j
    simp
  map_smul' c y := by
    ext j
    simp
  invFun u i := !₂[u (finProdFinEquiv (i, 0)), u (finProdFinEquiv (i, 1))]
  left_inv y := by
    funext i
    ext b
    fin_cases b <;> simp
  right_inv u := by
    ext j
    obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective j
    fin_cases b <;> simp
theorem planeCoordEquiv_apply {p : ℕ} (y : Fin p → RealPlane) (i : Fin p) (b : Fin 2) :
    planeCoordEquiv p y (finProdFinEquiv (i, b)) = y i b := by
  show y (finProdFinEquiv.symm (finProdFinEquiv (i, b))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, b))).2 = y i b
  rw [Equiv.symm_apply_apply]
theorem analyticOnNhd_of_isRealAnalyticTupleFun
    (H : YangMills.Construction.RealAnalyticity.CoordRealAnalyticIffAnalytic)
    {n : ℕ} {O : Set (Fin n → RealPlane)} {f : (Fin n → RealPlane) → ℂ}
    (hf : IsRealAnalyticTupleFun O f) : AnalyticOnNhd ℝ f O := by
  have hcoord : ∀ y : Fin n → RealPlane,
      (fun j => ((planeCoordEquiv n y j : ℝ) : ℂ)) = pairTupleEquiv n (embedPlaneTuple y) := by
    intro y
    funext j
    obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective j
    fin_cases b
    · show ((planeCoordEquiv n y (finProdFinEquiv (i, 0)) : ℝ) : ℂ) =
        pairTupleEquiv n (embedPlaneTuple y) (finProdFinEquiv (i, 0))
      rw [planeCoordEquiv_apply, pairTupleEquiv_apply_fst]
      rfl
    · show ((planeCoordEquiv n y (finProdFinEquiv (i, 1)) : ℝ) : ℂ) =
        pairTupleEquiv n (embedPlaneTuple y) (finProdFinEquiv (i, 1))
      rw [planeCoordEquiv_apply, pairTupleEquiv_apply_snd]
      rfl
  have hDR : pairTupleEquiv n '' (embedPlaneTuple '' O) ⊆
      YangMills.Construction.Coordinates.ComplexCoordinates.realLocus (n * 2) := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    rw [← hcoord]
    intro j
    simp
  have hscalar : (fun (z : YangMills.Construction.Coordinates.ComplexCoordinates (n * 2))
        (_ : Fin 1) => f (tupleRe ((pairTupleEquiv n).symm z))) =
      fun z => YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.scalarEquiv
        (f (tupleRe ((pairTupleEquiv n).symm z))) := by
    funext z i
    simp [YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.scalarEquiv]
  have hG := (H (n * 2) _ (fun z => f (tupleRe ((pairTupleEquiv n).symm z))) hDR).1
    (by rw [hscalar]; exact hf)
  intro y hy
  have hmem : planeCoordEquiv n y ∈ (fun (u : Fin (n * 2) → ℝ) (j : Fin (n * 2)) => (u j : ℂ)) ⁻¹'
      (pairTupleEquiv n '' (embedPlaneTuple '' O)) := by
    show (fun j => ((planeCoordEquiv n y j : ℝ) : ℂ)) ∈
      pairTupleEquiv n '' (embedPlaneTuple '' O)
    rw [hcoord]
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hR : AnalyticAt ℝ (planeCoordEquiv n) y :=
    ((planeCoordEquiv n).toContinuousLinearEquiv :
      (Fin n → RealPlane) →L[ℝ] (Fin (n * 2) → ℝ)).analyticAt y
  have h2 := (hG.2 _ hmem).comp hR
  have heq : ((fun u : Fin (n * 2) → ℝ =>
      f (tupleRe ((pairTupleEquiv n).symm fun j => (u j : ℂ)))) ∘
        (planeCoordEquiv n)) = f := by
    funext y'
    show f (tupleRe ((pairTupleEquiv n).symm
      fun j => ((planeCoordEquiv n y' j : ℝ) : ℂ))) = f y'
    rw [hcoord, Equiv.symm_apply_apply]
    congr 1
    funext i
    exact vecRe_embedPlane (y' i)
  rwa [heq] at h2
variable {m : SharpScale} {S : ConnFamily}
theorem analyticOnNhd_pointHarmonic (H₁ : DistinctHarmonics.Holds)
    (H₅ : YangMills.Construction.RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (d : PlaneDataWithAperture m S) {n : ℕ}
    (hn : 2 ≤ n) (h : ℤ) (φ : Fin n → realLabels) :
    AnalyticOnNhd ℝ (pointHarmonic S d.angle h n φ) (injectivePointTuples n) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
  exact analyticOnNhd_of_isRealAnalyticTupleFun H₅ (H₁ m S d (q + 1) (by omega) h φ).2.1.1
theorem analyticOnNhd_finAppend_slice {a b : ℕ} (q : Fin a → RealPlane)
    {F : (Fin (a + b) → RealPlane) → ℂ}
    (hF : AnalyticOnNhd ℝ F (injectivePointTuples (a + b))) :
    AnalyticOnNhd ℝ (fun w : Fin b → RealPlane => F (Fin.append q w))
      {w | Fin.append q w ∈ injectivePointTuples (a + b)} := by
  intro w hw
  have hA : AnalyticAt ℝ (fun w : Fin b → RealPlane => Fin.append q w) w := by
    refine (analyticAt_pi_iff (f := fun i (w : Fin b → RealPlane) => Fin.append q w i)).2 ?_
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact analyticAt_const
    | right j =>
      simp only [Fin.append_right]
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => RealPlane) j).analyticAt w
  exact (hF _ hw).comp hA
end Analytic
section Connected
theorem isConnected_compl_fibres {N : ℕ} (hN : 2 ≤ N)
    (H : YangMills.Construction.Analysis.ComplementOfCodimTwoSubspaces N)
    {I : Type} [Finite I] [Nonempty I] (T : I → (Fin N → ℝ) →ₗ[ℝ] RealPlane)
    (hT : ∀ i, Function.Surjective (T i)) (c : I → RealPlane) :
    IsConnected {u : Fin N → ℝ | ∀ i, T i u ≠ c i} := by
  obtain ⟨m, ⟨E⟩⟩ := Finite.exists_equiv_fin I
  have hm : 1 ≤ m := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have := (E i).2
    omega
  choose x₀ hx₀ using fun i => hT i (c i)
  let V : Fin m → AffineSubspace ℝ (Fin N → ℝ) := fun a =>
    AffineSubspace.mk' (x₀ (E.symm a)) (LinearMap.ker (T (E.symm a)))
  have hV := (H hN m hm V (fun a => ⟨x₀ (E.symm a), AffineSubspace.self_mem_mk' _ _⟩) (fun a => by
    have h := LinearMap.finrank_range_add_finrank_ker (T (E.symm a))
    rw [LinearMap.range_eq_top.mpr (hT _), finrank_top, finrank_euclideanSpace_fin,
      Module.finrank_fin_fun] at h
    rw [show (V a).direction = LinearMap.ker (T (E.symm a)) from
      AffineSubspace.direction_mk' _ _]
    omega)).2.2
  have hset : {u : Fin N → ℝ | ∀ i, T i u ≠ c i} = (⋃ a, (V a : Set (Fin N → ℝ)))ᶜ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    have hmem : ∀ a, u ∈ (V a : Set (Fin N → ℝ)) ↔ T (E.symm a) u = c (E.symm a) := by
      intro a
      simp only [V, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker,
        map_sub, hx₀, sub_eq_zero]
    constructor
    · intro h a ha
      exact h _ ((hmem a).1 ha)
    · intro h i hi
      refine h (E i) ((hmem _).2 ?_)
      simpa using hi
  rw [hset]
  exact hV
theorem finAppend_mem_injectivePointTuples_iff {a b : ℕ} {q : Fin a → RealPlane}
    (hq : Function.Injective q) {w : Fin b → RealPlane} :
    Fin.append q w ∈ injectivePointTuples (a + b) ↔
      Function.Injective w ∧ ∀ i j, q i ≠ w j :=
  ⟨fun h => ⟨injective_right_of_finAppend h, left_ne_right_of_finAppend h⟩,
    fun h => finAppend_injective hq h.1 h.2⟩
theorem isPreconnected_free_tuple
    (H : YangMills.Construction.Analysis.ZerosOfAnalyticMapsAndThinSets) {a b : ℕ}
    {q : Fin a → RealPlane} (hq : Function.Injective q) (hb : 1 ≤ b) (hab : 2 ≤ a + b) :
    IsPreconnected {w : Fin b → RealPlane | Fin.append q w ∈ injectivePointTuples (a + b)} := by
  let R := planeCoordEquiv b
  let I : Type := {x : Fin b × Fin b // x.1 ≠ x.2} ⊕ (Fin b × Fin a)
  let T : I → (Fin (b * 2) → ℝ) →ₗ[ℝ] RealPlane :=
    Sum.elim
      (fun x => ((LinearMap.proj x.1.1 : (Fin b → RealPlane) →ₗ[ℝ] RealPlane) -
        LinearMap.proj x.1.2).comp R.symm.toLinearMap)
      (fun x => (LinearMap.proj x.1 : (Fin b → RealPlane) →ₗ[ℝ] RealPlane).comp
        R.symm.toLinearMap)
  let c : I → RealPlane := Sum.elim (fun _ => 0) (fun x => q x.2)
  have hT : ∀ i, Function.Surjective (T i) := by
    rintro (x | x) v
    · refine ⟨R (Pi.single x.1.1 v), ?_⟩
      simp [T, Pi.single_eq_of_ne x.2.symm]
    · refine ⟨R (Pi.single x.1 v), ?_⟩
      simp [T]
  have : Nonempty I := by
    by_cases ha : 1 ≤ a
    · exact ⟨Sum.inr (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    · refine ⟨Sum.inl ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩⟩
      simp [Fin.ext_iff]
  have hC := isConnected_compl_fibres (by omega)
    (H (b * 2) (by omega)).2.2.2 T hT c
  have hmem : ∀ w : Fin b → RealPlane, R w ∈ {u | ∀ i, T i u ≠ c i} ↔
      Fin.append q w ∈ injectivePointTuples (a + b) := by
    intro w
    rw [finAppend_mem_injectivePointTuples_iff hq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro x y hxy
        by_contra hne
        have := h (Sum.inl ⟨(x, y), hne⟩)
        simp [T, c, hxy] at this
      · intro i j hij
        have := h (Sum.inr (j, i))
        simp [T, c, hij] at this
    · rintro ⟨h₁, h₂⟩ (x | x)
      · simp only [T, c, Sum.elim_inl]
        simpa [sub_eq_zero] using fun h => x.2 (h₁ h)
      · simp only [T, c, Sum.elim_inr]
        simpa using fun h => h₂ x.2 x.1 h.symm
  have himage : {w : Fin b → RealPlane | Fin.append q w ∈ injectivePointTuples (a + b)} =
      R.symm.toContinuousLinearEquiv '' {u | ∀ i, T i u ≠ c i} := by
    ext w
    constructor
    · intro hw
      exact ⟨R w, (hmem w).2 hw, by simp⟩
    · rintro ⟨u, hu, rfl⟩
      have : R (R.symm u) ∈ {u | ∀ i, T i u ≠ c i} := by simpa using hu
      exact (hmem _).1 this
  rw [himage]
  exact hC.isPreconnected.image _ R.symm.toContinuousLinearEquiv.continuous.continuousOn
end Connected
section OneSide
variable {m : SharpScale} {S : ConnFamily}
theorem isVanishingSet_reflectLabelled (H₁ : DistinctHarmonics.Holds)
    (H₃ : TopCoeffLinePositivity.AllPositivity)
    (H₄ : YangMills.Construction.Analysis.ZerosOfAnalyticMapsAndThinSets)
    (H₅ : YangMills.Construction.RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (d : PlaneDataWithAperture m S) {j r : ℕ} (hk : 1 ≤ j + r)
    {l P M : Set RealPlane} (hl : IsLine l) (hP : IsOpenSide l P)
    (hinv : ∀ y, lineReflection l (lineReflection l y) = y)
    (hPM : ∀ y ∈ P, lineReflection l y ∈ M) (hMP : ∀ y ∈ M, lineReflection l y ∈ P)
    (hPo : IsOpen P) (hMo : IsOpen M) (hdisj : Disjoint P M)
    (hPinf : P.Infinite) (hMinf : M.Infinite)
    {Q₁ Q₀ : Set PointWithLabel} (hQ₁ : IsDistinctLabelledSetIn j P Q₁)
    (hsub : Q₀ ⊆ reflectLabelled l Q₁ ∪ Q₁) (hz : IsVanishingSet S d.angle (j + r) Q₀) :
    IsVanishingSet S d.angle (j + r) (reflectLabelled l Q₁) := by
  have hθ : Function.Injective (lineReflection l) := fun x y h => by
    rw [← hinv x, h, hinv]
  have hnotP : ∀ y ∈ P, lineReflection l y ∉ P := fun y hy hy' =>
    Set.disjoint_left.1 hdisj hy' (hPM y hy)
  obtain ⟨e₁, he₁, rfl⟩ := exists_injective_enum hQ₁.1
  have hP₁ : ∀ i, (e₁ i).1 ∈ P := fun i => hQ₁.2 ⟨e₁ i, ⟨i, rfl⟩, rfl⟩
  have hrange : reflectLabelled l (Set.range e₁) =
      Set.range fun i => reflectPoint l (e₁ i) := by
    rw [reflectLabelled_eq_image, ← Set.range_comp]
    rfl
  have hq : Function.Injective fun i => lineReflection l (e₁ i).1 :=
    fun x y h => he₁ (hθ h)
  have hqe : Function.Injective fun i => (reflectPoint l (e₁ i)).1 := hq
  have hn : 2 * (j + r) = j + (r + (j + r)) := by omega
  have hn2 : 2 ≤ j + (r + (j + r)) := by omega
  have hkey : ∀ (χ : Fin (r + (j + r)) → realLabels) (w : Fin (r + (j + r)) → RealPlane),
      Fin.append (fun i => lineReflection l (e₁ i).1) w ∈
          injectivePointTuples (j + (r + (j + r))) →
        pointHarmonic S d.angle (-(topIndex S d.angle (j + r) : ℤ))
          (j + (r + (j + r))) (Fin.append (fun i => (e₁ i).2) χ)
          (Fin.append (fun i => lineReflection l (e₁ i).1) w) = 0 := by
    intro χ
    have hvanish : ∀ w : Fin (r + (j + r)) → RealPlane,
        Fin.append (fun i => lineReflection l (e₁ i).1) w ∈
            injectivePointTuples (j + (r + (j + r))) →
        (∀ i, w (Fin.castAdd (j + r) i) ∈ M) → (∀ i, w (Fin.natAdd r i) ∈ P) →
        pointHarmonic S d.angle (-(topIndex S d.angle (j + r) : ℤ))
          (j + (r + (j + r))) (Fin.append (fun i => (e₁ i).2) χ)
          (Fin.append (fun i => lineReflection l (e₁ i).1) w) = 0 := by
      intro w hw hwM hwP
      obtain ⟨hwinj, hqw⟩ := (finAppend_mem_injectivePointTuples_iff hq).1 hw
      let ew : Fin r → PointWithLabel := fun i =>
        (lineReflection l (w (Fin.castAdd (j + r) i)), χ (Fin.castAdd (j + r) i))
      let ez : Fin (j + r) → PointWithLabel := fun i => (w (Fin.natAdd r i), χ (Fin.natAdd r i))
      let ex : Fin (j + r) → PointWithLabel := Fin.append e₁ ew
      have hew : Function.Injective fun i => (ew i).1 := fun x y h =>
        Fin.castAdd_injective _ _ (hwinj (hθ h))
      have hez : Function.Injective fun i => (ez i).1 := fun x y h =>
        Fin.natAdd_injective _ _ (hwinj h)
      have hex : Function.Injective fun i => (ex i).1 := by
        have h := comp_finAppend Prod.fst e₁ ew
        show Function.Injective fun i => Prod.fst (Fin.append e₁ ew i)
        rw [h]
        refine finAppend_injective he₁ hew fun i a hia => ?_
        refine hqw i (Fin.castAdd (j + r) a) ?_
        show lineReflection l (e₁ i).1 = _
        have hia' : (e₁ i).1 = lineReflection l (w (Fin.castAdd (j + r) a)) := hia
        rw [hia', hinv]
      have hexP : ∀ i, (ex i).1 ∈ P := by
        intro i
        induction i using Fin.addCases with
        | left i =>
          show (Fin.append e₁ ew (Fin.castAdd r i)).1 ∈ P
          rw [Fin.append_left]
          exact hP₁ i
        | right i =>
          show (Fin.append e₁ ew (Fin.natAdd j i)).1 ∈ P
          rw [Fin.append_right]
          exact hMP _ (hwM i)
      have hezP : ∀ i, (ez i).1 ∈ P := hwP
      have hQ₁ex : Set.range e₁ ⊆ Set.range ex := by
        show Set.range e₁ ⊆ Set.range (Fin.append e₁ ew)
        rw [range_finAppend]
        exact Set.subset_union_left
      have hdiag : topLabelledHarmonic S d.angle (j + r)
          (reflectLabelled l (Set.range ex) ∪ Set.range ex) = 0 := by
        refine hz.harmonic_vanishes _ ?_ ?_
        · rw [← range_crossTuple]
          exact isDistinctLabelledSet_range (crossTuple_fst_injective hθ hnotP hex hex hexP hexP)
        · refine hsub.trans (Set.union_subset_union ?_ hQ₁ex)
          exact Set.image_mono hQ₁ex
      have hrow : topLabelledHarmonic S d.angle (j + r)
          (reflectLabelled l (Set.range ex) ∪ Set.range ez) = 0 := by
        rw [topLabelledHarmonic_cross H₁ d hk hθ hnotP hex hez hexP hezP]
        rw [topLabelledHarmonic_cross H₁ d hk hθ hnotP hex hex hexP hexP] at hdiag
        exact (H₃ m S d).2.2.2 (j + r) hk l hl P hP
          ⟨labelledPointsOf ex, ⟨hex, hexP⟩⟩ hdiag ⟨labelledPointsOf ez, ⟨hez, hezP⟩⟩
      let ef : Fin (r + (j + r)) → PointWithLabel := fun i => (w i, χ i)
      have hset : reflectLabelled l (Set.range ex) ∪ Set.range ez =
          Set.range (Fin.append (fun i => reflectPoint l (e₁ i)) ef) := by
        have h1 : reflectLabelled l (Set.range ex) =
            Set.range (fun i => reflectPoint l (e₁ i)) ∪
              Set.range (fun i => ef (Fin.castAdd (j + r) i)) := by
          show reflectLabelled l (Set.range (Fin.append e₁ ew)) = _
          rw [range_finAppend, reflectLabelled_eq_image, Set.image_union, ← Set.range_comp,
            ← Set.range_comp]
          congr 2
          funext i
          exact Prod.ext (hinv _) rfl
        rw [h1, range_finAppend, range_eq_union_castAdd_natAdd ef, Set.union_assoc]
      have hinjf : Function.Injective fun i =>
          (Fin.append (fun i => reflectPoint l (e₁ i)) ef i).1 := by
        have h := comp_finAppend Prod.fst (fun i => reflectPoint l (e₁ i)) ef
        show Function.Injective fun i =>
          Prod.fst (Fin.append (fun i => reflectPoint l (e₁ i)) ef i)
        rw [h]
        exact hw
      have hval : labelledSetHarmonic S d.angle
          (-(topIndex S d.angle (j + r) : ℤ)) (2 * (j + r))
          (reflectLabelled l (Set.range ex) ∪ Set.range ez) = 0 := hrow
      rw [hn, hset, labelledSetHarmonic_range H₁ d hn2 _ hinjf,
        show (fun i => (Fin.append (fun i => reflectPoint l (e₁ i)) ef i).2) = _ from
          comp_finAppend Prod.snd (fun i => reflectPoint l (e₁ i)) ef,
        show (fun i => (Fin.append (fun i => reflectPoint l (e₁ i)) ef i).1) = _ from
          comp_finAppend Prod.fst (fun i => reflectPoint l (e₁ i)) ef] at hval
      exact hval
    have hconn := isPreconnected_free_tuple H₄ (b := r + (j + r)) hq (by omega) hn2
    have han := analyticOnNhd_finAppend_slice (fun i => lineReflection l (e₁ i).1)
      (analyticOnNhd_pointHarmonic H₁ H₅ d hn2
        (-(topIndex S d.angle (j + r) : ℤ)) (Fin.append (fun i => (e₁ i).2) χ))
    have hMq : (M \ Set.range fun i => lineReflection l (e₁ i).1).Infinite :=
      hMinf.sdiff (Set.finite_range _)
    let f₁ := Set.Infinite.natEmbedding _ hMq
    let f₂ := Set.Infinite.natEmbedding _ hPinf
    let w₀ : Fin (r + (j + r)) → RealPlane :=
      Fin.append (fun i : Fin r => ((f₁ i : _) : RealPlane))
        (fun i : Fin (j + r) => ((f₂ i : _) : RealPlane))
    have hw₀M : ∀ i, w₀ (Fin.castAdd (j + r) i) ∈ M := fun i => by
      simp only [w₀, Fin.append_left]
      exact (f₁ i).2.1
    have hw₀P : ∀ i, w₀ (Fin.natAdd r i) ∈ P := fun i => by
      simp only [w₀, Fin.append_right]
      exact (f₂ i).2
    have hw₀inj : Function.Injective w₀ :=
      finAppend_injective
        (fun x y h => Fin.val_injective (f₁.injective (Subtype.val_injective h)))
        (fun x y h => Fin.val_injective (f₂.injective (Subtype.val_injective h)))
        (fun x y h => Set.disjoint_left.1 hdisj (f₂ y).2 (h ▸ (f₁ x).2.1))
    have hw₀ : Fin.append (fun i => lineReflection l (e₁ i).1) w₀ ∈
        injectivePointTuples (j + (r + (j + r))) := by
      refine (finAppend_mem_injectivePointTuples_iff hq).2 ⟨hw₀inj, fun i a => ?_⟩
      induction a using Fin.addCases with
      | left a =>
        intro h
        exact (f₁ a).2.2 ⟨i, h.trans (by simp [w₀])⟩
      | right a =>
        intro h
        have h' : lineReflection l (e₁ i).1 ∈ P := h ▸ hw₀P a
        exact hnotP _ (hP₁ i) h'
    have hcont : Continuous fun w : Fin (r + (j + r)) → RealPlane =>
        Fin.append (fun i => lineReflection l (e₁ i).1) w := by
      refine continuous_pi fun i => ?_
      induction i using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact continuous_const
      | right i =>
        simp only [Fin.append_right]
        exact continuous_apply i
    have hopen : IsOpen (injectivePointTuples (j + (r + (j + r)))) := by
      obtain ⟨q', hq'⟩ : ∃ q', j + (r + (j + r)) = q' + 2 := ⟨j + (r + (j + r)) - 2, by omega⟩
      rw [hq']
      exact (H₁ m S d (q' + 1) (by omega) 0 fun _ => ⟨0, contDiff_const, HasCompactSupport.zero⟩).2.1.2.2
    have hU : IsOpen ({w | Fin.append (fun i => lineReflection l (e₁ i).1) w ∈
          injectivePointTuples (j + (r + (j + r)))} ∩
        ((⋂ i, (fun w : Fin (r + (j + r)) → RealPlane => w (Fin.castAdd (j + r) i)) ⁻¹' M) ∩
          ⋂ i, (fun w : Fin (r + (j + r)) → RealPlane => w (Fin.natAdd r i)) ⁻¹' P)) := by
      refine (hopen.preimage hcont).inter (IsOpen.inter ?_ ?_)
      · exact isOpen_iInter_of_finite fun i => hMo.preimage
          (continuous_apply (Fin.castAdd (j + r) i) :
            Continuous fun w : Fin (r + (j + r)) → RealPlane => w (Fin.castAdd (j + r) i))
      · exact isOpen_iInter_of_finite fun i => hPo.preimage
          (continuous_apply (Fin.natAdd r i) :
            Continuous fun w : Fin (r + (j + r)) → RealPlane => w (Fin.natAdd r i))
    have hev : (fun w : Fin (r + (j + r)) → RealPlane =>
        pointHarmonic S d.angle (-(topIndex S d.angle (j + r) : ℤ))
          (j + (r + (j + r))) (Fin.append (fun i => (e₁ i).2) χ)
          (Fin.append (fun i => lineReflection l (e₁ i).1) w)) =ᶠ[𝓝 w₀] 0 := by
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hw₀, ?_, ?_⟩) ?_
      · exact Set.mem_iInter.2 hw₀M
      · exact Set.mem_iInter.2 hw₀P
      · rintro w ⟨hw, h₁, h₂⟩
        exact hvanish w hw (Set.mem_iInter.1 h₁) (Set.mem_iInter.1 h₂)
    intro w hw
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw₀ hev hw
  refine ⟨⟨j, by omega, hrange ▸ isDistinctLabelledSet_range hqe⟩, ?_⟩
  intro Y hY hYsub
  rw [hrange] at hYsub
  have hdiff : IsDistinctLabelledSet (r + (j + r))
      (Y \ Set.range fun i => reflectPoint l (e₁ i)) := by
    refine ⟨?_, hY.fst_injOn.mono Set.sdiff_subset⟩
    have h := Set.encard_sdiff_add_encard_of_subset hYsub
    rw [(isDistinctLabelledSet_range hqe).card_eq, hY.card_eq] at h
    have hne : (Y \ Set.range fun i => reflectPoint l (e₁ i)).encard ≠ ⊤ :=
      ((Set.finite_of_encard_eq_coe hY.card_eq).subset Set.sdiff_subset).encard_lt_top.ne
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hc] at h ⊢
    norm_cast at h ⊢
    omega
  obtain ⟨ew, hew, hrw⟩ := exists_injective_enum hdiff
  have hre : Set.range (Fin.append (fun i => reflectPoint l (e₁ i)) ew) = Y := by
    rw [range_finAppend, hrw, Set.union_sdiff_cancel hYsub]
  have hinje : Function.Injective fun i =>
      (Fin.append (fun i => reflectPoint l (e₁ i)) ew i).1 := by
    have h := comp_finAppend Prod.fst (fun i => reflectPoint l (e₁ i)) ew
    show Function.Injective fun i =>
      Prod.fst (Fin.append (fun i => reflectPoint l (e₁ i)) ew i)
    rw [h]
    refine finAppend_injective hq hew fun i a hia => ?_
    have hmemw : ew a ∈ Y \ Set.range fun i => reflectPoint l (e₁ i) :=
      hrw ▸ Set.mem_range_self a
    have heq : reflectPoint l (e₁ i) = ew a :=
      hY.fst_injOn (hYsub ⟨i, rfl⟩) hmemw.1 hia
    exact hmemw.2 ⟨i, heq⟩
  show labelledSetHarmonic S d.angle (-(topIndex S d.angle (j + r) : ℤ))
    (2 * (j + r)) Y = 0
  rw [hn, ← hre, labelledSetHarmonic_range H₁ d hn2 _ hinje,
    show (fun i => (Fin.append (fun i => reflectPoint l (e₁ i)) ew i).2) = _ from
      comp_finAppend Prod.snd (fun i => reflectPoint l (e₁ i)) ew,
    show (fun i => (Fin.append (fun i => reflectPoint l (e₁ i)) ew i).1) = _ from
      comp_finAppend Prod.fst (fun i => reflectPoint l (e₁ i)) ew]
  refine hkey _ _ ?_
  have h := comp_finAppend Prod.fst (fun i => reflectPoint l (e₁ i)) ew
  have := hinje
  rw [show (fun i => (Fin.append (fun i => reflectPoint l (e₁ i)) ew i).1) = _ from h] at this
  exact this
end OneSide
theorem halvesVanishingSets_of (H₁ : DistinctHarmonics.Holds)
    (H₂ : YangMills.Construction.LineSidesViaRotations.Holds)
    (H₃ : TopCoeffLinePositivity.AllPositivity)
    (H₄ : YangMills.Construction.Analysis.ZerosOfAnalyticMapsAndThinSets)
    (H₅ : YangMills.Construction.RealAnalyticity.CoordRealAnalyticIffAnalytic) :
    HalvesVanishingSets := by
  intro m S d k hk l P hl hP j hj Q' Q hQ' hsub hz
  obtain ⟨r, rfl⟩ : ∃ r, k = j + r := ⟨k - j, by omega⟩
  have hP' := hP
  obtain ⟨u, hu, ν, hν, rfl⟩ := hP
  have hsides : AreOpenSides l (posSide ν u) (negSide ν u) :=
    ⟨u, hu, ν, hν, rfl, rfl⟩
  obtain ⟨-, -, hinv, hbij, hPM, hMP, hPo, hMo, hdisj, hPinf, hMinf⟩ := H₂ l _ _ u hl hsides hu
  have hinv' : ∀ y, lineReflection l (lineReflection l y) = y := fun y => congrFun hinv y
  have hPM' : ∀ y ∈ posSide ν u,
      lineReflection l y ∈ negSide ν u := fun y hy =>
    hPM ▸ Set.mem_image_of_mem _ hy
  have hMP' : ∀ y ∈ negSide ν u,
      lineReflection l y ∈ posSide ν u := fun y hy =>
    hMP ▸ Set.mem_image_of_mem _ hy
  have hM' : IsOpenSide l (negSide ν u) :=
    ⟨u, hu, -ν, ⟨by simpa using hν.1, fun a ha b hb => by
      rw [inner_neg_left, hν.2 a ha b hb, neg_zero]⟩, negSide_eq_posSide_neg ν u⟩
  have h₁ := isVanishingSet_reflectLabelled H₁ H₃ H₄ H₅ d hk hl hP' hinv' hPM' hMP' hPo hMo
    hdisj hPinf hMinf hQ' hsub hz
  have hback : reflectLabelled l (reflectLabelled l Q') = Q' := by
    have hid : (fun p => reflectPoint l (reflectPoint l p)) = id :=
      funext fun p => Prod.ext (hinv' _) rfl
    rw [reflectLabelled_eq_image, reflectLabelled_eq_image, Set.image_image, hid, Set.image_id]
  have hQ'' : IsDistinctLabelledSetIn j (negSide ν u)
      (reflectLabelled l Q') := by
    obtain ⟨e₁, he₁, rfl⟩ := exists_injective_enum hQ'.1
    have hrange : reflectLabelled l (Set.range e₁) =
        Set.range fun i => reflectPoint l (e₁ i) := by
      rw [reflectLabelled_eq_image, ← Set.range_comp]
      rfl
    rw [hrange]
    refine ⟨isDistinctLabelledSet_range fun x y h => he₁ (hbij.1 h), ?_⟩
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hPM' _ (hQ'.2 ⟨e₁ i, ⟨i, rfl⟩, rfl⟩)
  have hsub' : Q ⊆ reflectLabelled l (reflectLabelled l Q') ∪
      reflectLabelled l Q' := by
    rw [hback, Set.union_comm]
    exact hsub
  have h₂ := isVanishingSet_reflectLabelled H₁ H₃ H₄ H₅ d hk hl hM' hinv' hMP' hPM' hMo hPo
    hdisj.symm hMinf hPinf hQ'' hsub' hz
  rw [hback] at h₂
  exact ⟨h₂, h₁⟩
end YangMills.Construction.EuclideanFunctionals.VanishingSetHalving
end
