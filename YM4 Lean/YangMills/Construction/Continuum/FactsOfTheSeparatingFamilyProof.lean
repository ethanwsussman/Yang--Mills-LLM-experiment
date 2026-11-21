import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.FactsOfTheSeparatingFamily
import YangMills.Construction.Continuum.RationalBoxUnionsBetweenCompactAndOpenSets
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoff
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.SeparatingFamily
open TestFunctions ReflectionPositivity.AxisMirror
theorem closedSupport_euclidean_eq_tsupport (D : MirrorData) (u : ScalarField) :
    Ambient.closedSupport D .euclidean u = tsupport u := by apply _root_.YangMills.Construction.R4TupleForms.closedSupport_euclidean_eq <;> assumption
theorem disjoint_closedSupport_iff (D : MirrorData) (u v : ScalarField) :
    Disjoint (Ambient.closedSupport D .euclidean u) (Ambient.closedSupport D .euclidean v) ↔
      Disjoint (tsupport u) (tsupport v) := by
  rw [closedSupport_euclidean_eq_tsupport, closedSupport_euclidean_eq_tsupport]
  exact Iff.rfl
theorem isCompactWrt_euclidean_iff_isCompact (D : MirrorData) (Z : Set (Fin 4 → ℝ)) :
    MetricNotions.IsCompactWrt (Ambient.metric D .euclidean) Z ↔ IsCompact Z :=
  SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) Z
theorem exists_rat_of_mem_adicGridPointsPositive {L : ℕ} {x : ℝ}
    (hx : x ∈ PeriodicLattice.adicGridPointsPositive L) : ∃ q : ℚ, x = q := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPointsPositive_iff L x).1 hx
  refine ⟨(n : ℚ) * (L : ℚ) ^ (-((k : ℕ) : ℤ)), ?_⟩
  push_cast [PeriodicLattice.meshSize]
  rfl
theorem exists_signedPerm_add_of_mem {L : ℕ} {r : Equiv.Perm (Fin 4 → ℝ)}
    (hr : r ∈ adicHyperoctahedralMotions L) :
    ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) (c : Fin 4 → ℚ),
      ∀ (x : Fin 4 → ℝ) (μ : Fin 4), r x μ = ((ε μ : ℤ) : ℝ) * x (σ μ) + c μ := by
  obtain ⟨w, hw, v, hv, h⟩ := hr
  obtain ⟨σ, ε, hε⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).1 hw
  choose c hc using fun μ => exists_rat_of_mem_adicGridPointsPositive (hv μ)
  refine ⟨σ, ε, c, fun x μ => ?_⟩
  have h₁ : r x μ = (w x) μ + v μ := by rw [h]; rfl
  rw [h₁, hε, hc]
theorem adicHyperoctahedralMotions_countable (L : ℕ) :
    (adicHyperoctahedralMotions L : Set (Equiv.Perm (Fin 4 → ℝ))).Countable := by
  let A : (Equiv.Perm (Fin 4) × (Fin 4 → ℤˣ) × (Fin 4 → ℚ)) → Set (Equiv.Perm (Fin 4 → ℝ)) :=
    fun t => {r | ∀ (x : Fin 4 → ℝ) (μ : Fin 4),
      r x μ = ((t.2.1 μ : ℤ) : ℝ) * x (t.1 μ) + t.2.2 μ}
  have hA : ∀ t, (A t).Countable := fun t =>
    Set.Subsingleton.countable fun r hr r' hr' =>
      Equiv.ext fun x => funext fun μ => by rw [hr x μ, hr' x μ]
  refine (countable_iUnion hA).mono fun r hr => ?_
  obtain ⟨σ, ε, c, h⟩ := exists_signedPerm_add_of_mem hr
  exact mem_iUnion.2 ⟨(σ, ε, c), h⟩
theorem isRatBox_image_of_signedPerm_add {r : Equiv.Perm (Fin 4 → ℝ)} {σ : Equiv.Perm (Fin 4)}
    {ε : Fin 4 → ℤˣ} {c : Fin 4 → ℚ}
    (h : ∀ (x : Fin 4 → ℝ) (μ : Fin 4), r x μ = ((ε μ : ℤ) : ℝ) * x (σ μ) + c μ)
    {B : Set (Fin 4 → ℝ)} (hB : IsRatBox B) : IsRatBox (r '' B) := by
  obtain ⟨a, b, hab, rfl⟩ := hB
  let a' : Fin 4 → ℚ := fun μ => if ε μ = 1 then a (σ μ) + c μ else -b (σ μ) + c μ
  let b' : Fin 4 → ℚ := fun μ => if ε μ = 1 then b (σ μ) + c μ else -a (σ μ) + c μ
  have key : ∀ (x : Fin 4 → ℝ) (μ : Fin 4), r x μ ∈ Icc (a' μ : ℝ) (b' μ) ↔
      x (σ μ) ∈ Icc (a (σ μ) : ℝ) (b (σ μ)) := by
    intro x μ
    rw [h x μ]
    rcases Int.units_eq_one_or (ε μ) with h1 | h1
    · simp only [a', b', h1, if_true, mem_Icc, Units.val_one, Int.cast_one, one_mul]
      push_cast
      constructor <;> rintro ⟨u, v⟩ <;> constructor <;> linarith
    · have h2 : (-1 : ℤˣ) ≠ 1 := by decide
      simp only [a', b', h1, h2, if_false, mem_Icc, Units.val_neg, Units.val_one, Int.cast_neg,
        Int.cast_one]
      push_cast
      constructor <;> rintro ⟨u, v⟩ <;> constructor <;> linarith
  refine ⟨a', b', fun μ => ?_, ?_⟩
  · have := hab (σ μ)
    simp only [a', b']
    split_ifs <;> linarith
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ κ _
      exact (key x κ).2 (hx (σ κ) trivial)
    · intro hy
      refine ⟨r.symm y, fun κ _ => ?_, r.apply_symm_apply y⟩
      have h₁ := (key (r.symm y) (σ.symm κ)).1 (by
        rw [r.apply_symm_apply]
        exact hy _ trivial)
      simpa using h₁
theorem image_mem_ratBoxUnions {L : ℕ} {r : Equiv.Perm (Fin 4 → ℝ)}
    (hr : r ∈ adicHyperoctahedralMotions L) {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ ratBoxUnions) :
    ⇑r '' Q ∈ ratBoxUnions := by
  obtain ⟨σ, ε, c, h⟩ := exists_signedPerm_add_of_mem hr
  obtain ⟨𝓑, hfin, hB, rfl⟩ := hQ
  refine ⟨(fun B => ⇑r '' B) '' 𝓑, hfin.image _, ?_, ?_⟩
  · rintro _ ⟨B, hB', rfl⟩
    exact isRatBox_image_of_signedPerm_add h (hB B hB')
  · rw [sUnion_eq_biUnion, sUnion_image, image_iUnion₂]
theorem comp_inv_mem_c1ZeroOff_image {L : ℕ} {r : Equiv.Perm (Fin 4 → ℝ)}
    (hr : r ∈ adicHyperoctahedralMotions L) {Q : Set (Fin 4 → ℝ)} {u : ScalarField}
    (hu : u ∈ c1ZeroOff Q) : u ∘ ⇑r⁻¹ ∈ c1ZeroOff (⇑r '' Q) := by
  obtain ⟨σ, ε, c, h⟩ := exists_signedPerm_add_of_mem (inv_mem hr)
  refine ⟨?_, fun x hx => ?_⟩
  · have hc : ContDiff ℝ 1 (⇑r⁻¹ : (Fin 4 → ℝ) → Fin 4 → ℝ) := by
      rw [contDiff_pi]
      intro μ
      have he : (fun x : Fin 4 → ℝ => (r⁻¹ x) μ) =
          fun x => ((ε μ : ℤ) : ℝ) * x (σ μ) + c μ := funext fun x => h x μ
      rw [he]
      exact (contDiff_const.mul (contDiff_apply ℝ ℝ (σ μ))).add contDiff_const
    exact ContDiff.comp (show ContDiff ℝ 1 u from hu.1) hc
  · refine hu.2 _ fun h' => hx ⟨_, h', ?_⟩
    exact r.apply_symm_apply x
theorem isDenseFamily_fixedDenseSets_of_separation (hb : RatBoxSeparation.separationClaim) :
    IsDenseFamily fixedDenseSets := by
  apply isDenseFamily_fixedDenseSets
  choose F h₁ h₂ h₃ using hb.2.2
  exact ⟨fun Q => F Q.1 Q.2, ⟨fun Q => h₁ Q.1 Q.2, fun Q => h₂ Q.1 Q.2, fun Q => h₃ Q.1 Q.2⟩⟩
theorem exists_mem_c1ZeroOff_of_mem_ratMotionSpan (hb : RatBoxSeparation.separationClaim)
    {L : ℕ} {φ : ScalarField} (hφ : φ ∈ ratMotionSpan L) :
    ∃ Q ∈ ratBoxUnions, φ ∈ c1ZeroOff Q := by
  have hfam := isDenseFamily_fixedDenseSets_of_separation hb
  obtain ⟨n, q, u, r, hu, hr, rfl⟩ := hφ
  have hex : ∀ i, ∃ Q ∈ ratBoxUnions, u i ∘ ⇑(r i)⁻¹ ∈ c1ZeroOff Q := fun i => by
    obtain ⟨Q, hQ⟩ := mem_iUnion.1 (hu i)
    exact ⟨_, image_mem_ratBoxUnions (hr i) Q.2,
      comp_inv_mem_c1ZeroOff_image (hr i) (hfam.subset Q hQ)⟩
  choose P hP huP using hex
  refine ⟨⋃₀ range P, hb.1.2 _ (finite_range P) (range_subset_iff.2 hP), ?_, fun x hx => ?_⟩
  · have he : (∑ i, (q i : ℝ) • (u i ∘ ⇑(r i)⁻¹)) =
        fun x => ∑ i, (q i : ℝ) • (u i ∘ ⇑(r i)⁻¹) x := by
      funext x
      simp [Finset.sum_apply]
    show ContDiff ℝ 1 _
    rw [he]
    exact ContDiff.sum fun i _ =>
      ContDiff.const_smul (q i : ℝ) (show ContDiff ℝ 1 (u i ∘ ⇑(r i)⁻¹) from (huP i).1)
  · rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h₀ : (u i ∘ ⇑(r i)⁻¹) x = 0 :=
      (huP i).2 x fun h' => hx ⟨P i, mem_range_self i, h'⟩
    show ((q i : ℝ) • (u i ∘ ⇑(r i)⁻¹)) x = 0
    rw [Pi.smul_apply, h₀, smul_zero]
theorem comp_inv_mem_ratMotionSpan {L : ℕ} {r : Equiv.Perm (Fin 4 → ℝ)}
    (hr : r ∈ adicHyperoctahedralMotions L) {φ : ScalarField} (hφ : φ ∈ ratMotionSpan L) :
    φ ∘ ⇑r⁻¹ ∈ ratMotionSpan L := by
  obtain ⟨n, q, u, s, hu, hs, rfl⟩ := hφ
  refine ⟨n, q, u, fun i => r * s i, hu, fun i => mul_mem hr (hs i), ?_⟩
  funext x
  simp [Finset.sum_apply, mul_inv_rev]
theorem ratMotionSpan_countable (hb : RatBoxSeparation.separationClaim) (L : ℕ) :
    (ratMotionSpan L).Countable := by
  have hfam := isDenseFamily_fixedDenseSets_of_separation hb
  have hcQ : Countable ratBoxUnions := hb.1.1.to_subtype
  have hU : (⋃ Q, fixedDenseSets Q).Countable := countable_iUnion hfam.countable
  let A : Set ScalarField :=
    image2 (fun (u : ScalarField) (r : Equiv.Perm (Fin 4 → ℝ)) => u ∘ ⇑r⁻¹)
      (⋃ Q, fixedDenseSets Q) (adicHyperoctahedralMotions L)
  have hA : A.Countable := hU.image2 (adicHyperoctahedralMotions_countable L) _
  have hcA : Countable A := hA.to_subtype
  let T : (n : ℕ) → (Fin n → ℚ) × (Fin n → A) → ScalarField :=
    fun n p => ∑ i, ((p.1 i : ℚ) : ℝ) • (p.2 i).1
  refine (countable_iUnion fun n => countable_range (T n)).mono ?_
  rintro φ ⟨n, q, u, r, hu, hr, rfl⟩
  exact mem_iUnion.2 ⟨n, (q, fun i => ⟨u i ∘ ⇑(r i)⁻¹, mem_image2_of_mem (hu i) (hr i)⟩), rfl⟩
theorem motionSpanCountableAndDense_holds (hb : RatBoxSeparation.separationClaim) (L : ℕ) :
    MotionSpanCountableAndDense L := by
  have hfam := isDenseFamily_fixedDenseSets_of_separation hb
  have hsub : ∀ Q : ratBoxUnions, fixedDenseSets Q ⊆ motionDenseSets L Q := fun Q u hu =>
    ⟨⟨1, fun _ => 1, fun _ => u, fun _ => 1, fun _ => mem_iUnion.2 ⟨Q, hu⟩,
      fun _ => one_mem _, by funext _; simp⟩, hfam.subset Q hu⟩
  refine ⟨ratMotionSpan_countable hb L, fun Q =>
    ⟨(ratMotionSpan_countable hb L).mono inter_subset_left, hsub Q, fun u hu ε hε => ?_⟩⟩
  obtain ⟨g, hg, hlt⟩ := hfam.dense Q u hu ε hε
  exact ⟨g, hsub Q hg, hlt⟩
theorem isDenseFamily_motionDenseSets (hb : RatBoxSeparation.separationClaim) (L : ℕ) :
    IsDenseFamily (motionDenseSets L) := by
  have h := (motionSpanCountableAndDense_holds hb L).2
  exact ⟨fun _ => inter_subset_right, fun Q => (h Q).1, fun Q => (h Q).2.2⟩
theorem mem_c1ZeroOff_of_tsupport_subset {Q : Set (Fin 4 → ℝ)} {u : ScalarField}
    (h₁ : IsC1R4 u) (hs : tsupport u ⊆ Q) : u ∈ c1ZeroOff Q :=
  ⟨h₁, fun _ hx => by_contra fun h => hx (hs (subset_tsupport u h))⟩
theorem disjointTupleFamilyEqSpanTuples_holds (hb : RatBoxSeparation.separationClaim)
    (D : MirrorData) : DisjointTupleFamilyEqSpanTuples D := by
  ext X
  constructor
  · intro hX
    refine ⟨hX.1, fun φ hφ => ?_, ?_⟩
    · obtain ⟨-, Q, -, hQ⟩ := hX
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hφ
      exact (hQ i).1
    · exact (pairwise_disjoint_tsupport_of_mem_disjointTupleFamily
        (isDenseFamily_motionDenseSets hb D.L) hX).imp fun {u v} h =>
          (disjoint_closedSupport_iff D u v).2 h
  · rintro ⟨hne, hmem, hdis⟩
    have hn : 1 ≤ X.length := List.length_pos_iff.2 hne
    have hc : ∀ i : Fin X.length, ∃ Q ∈ ratBoxUnions, X.get i ∈ c1ZeroOff Q := fun i =>
      exists_mem_c1ZeroOff_of_mem_ratMotionSpan hb (hmem _ (List.get_mem _ _))
    choose P hP huP using hc
    have hcomp : ∀ i, IsCompact (tsupport (X.get i)) := fun i =>
      (isCompact_of_mem_ratBoxUnions (hP i)).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_subset_of_mem_c1ZeroOff
          (isCompact_of_mem_ratBoxUnions (hP i)).isClosed (huP i))
    have hlt : ∀ i k : Fin X.length, i < k →
        Disjoint (tsupport (X.get i)) (tsupport (X.get k)) := fun i k hik =>
      (disjoint_closedSupport_iff D _ _).1 (List.pairwise_iff_get.1 hdis i k hik)
    have hdisj : Pairwise fun i k : Fin X.length =>
        Disjoint (tsupport (X.get i)) (tsupport (X.get k)) := fun i k hik =>
      (lt_or_gt_of_ne hik).elim (hlt i k) fun h => (hlt k i h).symm
    obtain ⟨Q, hQ, hQd, hCQ⟩ := hb.2.1 X.length hn (fun i => tsupport (X.get i)) (fun _ => univ)
      hcomp hdisj (fun _ => isOpen_univ) (fun _ => subset_univ _)
    exact ⟨hne, fun i => ⟨Q i, hQ i⟩, fun i k hik => hQd hik, fun i =>
      ⟨hmem _ (List.get_mem _ _), mem_c1ZeroOff_of_tsupport_subset (huP i).1 (hCQ i).1⟩⟩
theorem countable_lists_of_countable {s : Set ScalarField} (hs : s.Countable) :
    {X : List ScalarField | ∀ φ ∈ X, φ ∈ s}.Countable := by
  have hc : Countable s := hs.to_subtype
  refine (countable_range (List.map (Subtype.val : s → ScalarField))).mono fun X hX => ?_
  lift X to List s using hX
  exact mem_range_self X
theorem forall_mem_ratMotionSpan_of_mem_separatingTuples (hb : RatBoxSeparation.separationClaim)
    (D : MirrorData) {X : List ScalarField} (hX : X ∈ separatingTuples D.L) :
    ∀ φ ∈ X, φ ∈ ratMotionSpan D.L := by
  rcases hX with rfl | hX
  · simp
  · rw [disjointTupleFamilyEqSpanTuples_holds hb D] at hX
    exact hX.2.1
theorem separatingTuplesCountableAndStable_holds (hb : RatBoxSeparation.separationClaim)
    (hs : AtCutoff.SignFacts.SignFactsHold) (D : MirrorData) :
    SeparatingTuplesCountableAndStable D := by
  have hc := disjointTupleFamilyEqSpanTuples_holds hb D
  refine ⟨(countable_lists_of_countable (ratMotionSpan_countable hb D.L)).mono fun X hX =>
    forall_mem_ratMotionSpan_of_mem_separatingTuples hb D hX, fun r X hX => ?_,
    fun X hX Y hY hXY => ?_⟩
  · rcases hX with rfl | hX
    · exact Or.inl rfl
    · right
      rw [hc] at hX ⊢
      obtain ⟨hne, hmem, hdis⟩ := hX
      refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun φ hφ => ?_, ?_⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hφ
        exact comp_inv_mem_ratMotionSpan r.2 (hmem u hu)
      · refine List.pairwise_map.2 (hdis.imp fun {u v} h => ?_)
        have hsupp := fun w : ScalarField => ((hs D).1 (motionToIsometryEquiv D r)).2.2 ℝ w
        rw [(hsupp u).1, (hsupp v).1]
        exact (disjoint_image_iff (motionToIsometryEquiv D r).toEquiv.injective).2 h
  · by_cases hnil : Ambient.append (D := D) (E := .euclidean) X Y = []
    · rw [hnil]
      exact Or.inl rfl
    · right
      rw [hc]
      refine ⟨hnil, fun φ hφ => ?_, hXY⟩
      rcases List.mem_append.1 hφ with h | h
      · exact forall_mem_ratMotionSpan_of_mem_separatingTuples hb D hX φ h
      · exact forall_mem_ratMotionSpan_of_mem_separatingTuples hb D hY φ h
theorem separatingTuplesApproximate_holds (hb : RatBoxSeparation.separationClaim)
    (hs : AtCutoff.SignFacts.SignFactsHold) (D : MirrorData) (M : ℝ) (hM : 1 ≤ M) :
    SeparatingTuplesApproximate D M := by
  intro k hk u hu O hO hsub
  obtain ⟨-, hsep₁, hsep₂⟩ := hu
  have hu' : ∀ i, u i ∈ Ambient.compactC1 D ℝ .euclidean := fun i =>
    hsep₁ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  have hcomp : ∀ i, IsCompact (tsupport (u i)) := fun i => by
    rw [← closedSupport_euclidean_eq_tsupport D]
    exact (isCompactWrt_euclidean_iff_isCompact D _).1 (hu' i).2
  have hlt : ∀ i j : Fin k, i < j → Disjoint (tsupport (u i)) (tsupport (u j)) := fun i j hij =>
    (disjoint_closedSupport_iff D _ _).1 (List.pairwise_ofFn.1 hsep₂ hij)
  have hdisj : Pairwise fun i j : Fin k => Disjoint (tsupport (u i)) (tsupport (u j)) :=
    fun i j hij => (lt_or_gt_of_ne hij).elim (hlt i j) fun h => (hlt j i h).symm
  have hsub' : ∀ i, tsupport (u i) ⊆ O i := fun i => by
    rw [← closedSupport_euclidean_eq_tsupport D]
    exact hsub i
  obtain ⟨Q, hQ, hQd, hCQ⟩ := hb.2.1 k hk (fun i => tsupport (u i)) O hcomp hdisj hO hsub'
  have huQ : ∀ i, u i ∈ c1ZeroOff (Q i) := fun i =>
    mem_c1ZeroOff_of_tsupport_subset (hu' i).1 (hCQ i).1
  have hdense := (motionSpanCountableAndDense_holds hb D.L).2
  have hex : ∀ (l : ℕ) (i : Fin k), ∃ g ∈ motionDenseSets D.L ⟨Q i, hQ i⟩,
      c1NormR4 (g - u i) < 1 / ((l : ℝ) + 1) := fun l i =>
    (hdense ⟨Q i, hQ i⟩).2.2 (u i) (huQ i) _ (by positivity)
  choose φ hφ hnorm using hex
  have hclosed : ∀ i, IsClosed (Q i) := fun i =>
    (isCompact_of_mem_ratBoxUnions (hQ i)).isClosed
  have hsupp : ∀ l i, tsupport (φ l i) ⊆ Q i := fun l i =>
    tsupport_subset_of_mem_c1ZeroOff (hclosed i) (hφ l i).2
  refine ⟨φ, fun l => Or.inr ?_, fun l i => ?_, fun i => ?_⟩
  · rw [disjointTupleFamilyEqSpanTuples_holds hb D]
    refine ⟨fun h => ?_, fun ψ hψ => ?_, ?_⟩
    · have h₀ := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at h₀
      omega
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hψ
      exact (hφ l i).1
    · refine List.pairwise_ofFn.2 ?_
      intro i j hij
      exact (disjoint_closedSupport_iff D _ _).2 ((hQd hij.ne).mono (hsupp l i) (hsupp l j))
  · rw [closedSupport_euclidean_eq_tsupport]
    exact (hsupp l i).trans (hCQ i).2
  · have hbound : ∀ l : ℕ, sharpNormR4 M (φ l i - u i) ≤ 80 * M * (1 / ((l : ℝ) + 1)) := by
      intro l
      have hC : ContDiff ℝ 1 (φ l i - u i) :=
        ContDiff.sub (show ContDiff ℝ 1 (φ l i) from (hφ l i).2.1)
          (show ContDiff ℝ 1 (u i) from (huQ i).1)
      have hvan : φ l i - u i ∈ c1ZeroOff (Q i) :=
        ⟨hC, fun x hx => by simp [(hφ l i).2.2 x hx, (huQ i).2 x hx]⟩
      have hcs : IsCompact (tsupport (φ l i - u i)) :=
        (isCompact_of_mem_ratBoxUnions (hQ i)).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_subset_of_mem_c1ZeroOff (hclosed i) hvan)
      have hmem : (φ l i - u i) ∈ AtCutoff.cOneIn D .euclidean univ :=
        ⟨⟨hC, by
          rw [closedSupport_euclidean_eq_tsupport]
          exact (isCompactWrt_euclidean_iff_isCompact D _).2 hcs⟩, subset_univ _⟩
      refine (((hs D).2.2.2.2.1 _ hmem).2.2 M hM).trans ?_
      exact mul_le_mul_of_nonneg_left (hnorm l i).le (by linarith)
    have hlim : Tendsto (fun l : ℕ => 80 * M * (1 / ((l : ℝ) + 1))) atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (80 * M)
    refine squeeze_zero (fun l => ?_) hbound hlim
    exact le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem separatingTuplesFacts_holds (hb : RatBoxSeparation.separationClaim)
    (hs : AtCutoff.SignFacts.SignFactsHold) : SeparatingTuplesFacts := fun D =>
  ⟨⟨adicHyperoctahedralMotions_countable D.L, fun _ hr _ hQ => image_mem_ratBoxUnions hr hQ⟩,
    motionSpanCountableAndDense_holds hb D.L, disjointTupleFamilyEqSpanTuples_holds hb D,
    separatingTuplesCountableAndStable_holds hb hs D,
    fun M hM => separatingTuplesApproximate_holds hb hs D M hM⟩
end YangMills.Construction.SeparatingFamily
