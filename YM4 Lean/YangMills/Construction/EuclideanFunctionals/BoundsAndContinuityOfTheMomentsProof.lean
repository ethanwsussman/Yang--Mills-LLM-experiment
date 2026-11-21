import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMoments
import YangMills.Construction.EuclideanFunctionals.CentredFunctionalSeesTensorComponentsOnly
import YangMills.Construction.EuclideanFunctionals.SharpNormOnFunctionsOfClassC1
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.TorusMetric YangMills.Construction.MetricNotions Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.Moments
theorem norm_le_euclidNormVec (v : R4) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : R4) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
abbrev r4Metric : R4 → R4 → ℝ := Ambient.metric defaultMirrorData Ambient.euclidean
theorem r4Metric_apply (x y : R4) : r4Metric x y = euclidNormVec (x - y) := rfl
theorem isOpenWrt_r4Metric_iff (U : Set R4) : IsOpenWrt r4Metric U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hU x hx
    obtain ⟨r, hr, hsub⟩ := hU x hx
    refine ⟨r / 2, by positivity, fun y hy => hsub y ?_⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hy
    have := euclidNormVec_le_two_mul_norm (x - y)
    rw [r4Metric_apply]
    linarith
  · intro hU x hx
    obtain ⟨ε, hε, hsub⟩ := hU x hx
    refine ⟨ε, hε, fun y hy => hsub ?_⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact (norm_le_euclidNormVec _).trans_lt hy
theorem closureWrt_r4Metric_eq (Z : Set R4) : closureWrt r4Metric Z = closure Z := by
  ext x
  rw [Metric.mem_closure_iff]
  constructor
  · intro hx ε hε
    obtain ⟨y, hy, hd⟩ := hx ε hε
    exact ⟨y, hy, by rw [dist_eq_norm]; exact (norm_le_euclidNormVec _).trans_lt hd⟩
  · intro hx r hr
    obtain ⟨y, hy, hd⟩ := hx (r / 2) (by positivity)
    refine ⟨y, hy, ?_⟩
    rw [dist_eq_norm] at hd
    have := euclidNormVec_le_two_mul_norm (x - y)
    rw [r4Metric_apply]
    linarith
theorem isCompactWrt_r4Metric_iff (Z : Set R4) : IsCompactWrt r4Metric Z ↔ IsCompact Z := by
  classical
  constructor
  · intro hZc
    refine isCompact_of_finite_subcover fun {ι} U hU hZ => ?_
    obtain ⟨𝒰', hsub, hfin, hcov⟩ := hZc (Set.range U)
      (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_r4Metric_iff _).2 (hU i)) (by rwa [Set.sUnion_range])
    have hex : ∀ V ∈ 𝒰', ∃ i, U i = V := fun V hV => hsub hV
    choose idx hidx using hex
    refine ⟨hfin.toFinset.attach.image fun V => idx V.1 (hfin.mem_toFinset.1 V.2), fun x hx => ?_⟩
    obtain ⟨V, hV, hxV⟩ := hcov hx
    refine Set.mem_iUnion₂.2 ⟨idx V hV, Finset.mem_image.2
      ⟨⟨V, hfin.mem_toFinset.2 hV⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [hidx V hV]
    exact hxV
  · intro hZc 𝒰 hU hZ
    obtain ⟨t, ht⟩ := hZc.elim_finite_subcover (fun U : 𝒰 => (U : Set R4))
      (fun U => (isOpenWrt_r4Metric_iff _).1 (hU U U.2)) (by rwa [← Set.sUnion_eq_iUnion])
    refine ⟨(fun U : 𝒰 => (U : Set R4)) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
    · rintro _ ⟨U, -, rfl⟩
      exact U.2
    · intro x hx
      obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact ⟨U, ⟨U, hUt, rfl⟩, hxU⟩
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  closureWrt_r4Metric_eq _
theorem mem_C1c_iff_contDiff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by
  have hc : IsCompactWrt r4Metric (supp f) ↔ HasCompactSupport f := by
    rw [isCompactWrt_r4Metric_iff, supp_eq_tsupport]
    rfl
  exact and_congr Iff.rfl hc
theorem setDistR4_anti {A A' B B' : Set R4} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    TestFunctions.setDistR4 A B ≤ TestFunctions.setDistR4 A' B' :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem disjoint_of_ofReal_le_setDistR4 {A B : Set R4} {d : ℝ} (hd : 0 < d)
    (hAB : ENNReal.ofReal d ≤ TestFunctions.setDistR4 A B) : Disjoint A B := by apply _root_.YangMills.Construction.NonGaussianLimits.disjoint_of_le_setDistR4 <;> assumption
section Norms
variable {E : Type*} [NormedAddCommGroup E]
def BoundedLipschitz (f : R4 → E) : Prop :=
  (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x y, ‖f x - f y‖ ≤ K * euclidNormVec (x - y)
theorem uniformNorm_nonneg (f : R4 → E) : 0 ≤ TestFunctions.uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_le_uniformNorm {f : R4 → E} (hf : BoundedLipschitz f) (x : R4) :
    ‖f x‖ ≤ TestFunctions.uniformNorm f := by
  obtain ⟨⟨B, hB⟩, -⟩ := hf
  exact le_ciSup (f := fun x => ‖f x‖) ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩ x
theorem uniformNorm_le_of_forall {f : R4 → E} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) :
    TestFunctions.uniformNorm f ≤ B :=
  Real.iSup_le hf hB
theorem lipConstR4_le_of_forall {f : R4 → E} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x y, ‖f x - f y‖ ≤ K * euclidNormVec (x - y)) : TestFunctions.lipConstR4 f ≤ K :=
  csInf_le ⟨0, fun _ hC => hC.1⟩ ⟨hK, hf⟩
theorem lipConstR4_nonneg (f : R4 → E) : 0 ≤ TestFunctions.lipConstR4 f :=
  Real.sInf_nonneg fun _ hC => hC.1
theorem norm_sub_le_lipConstR4_mul {f : R4 → E} (hf : BoundedLipschitz f) (x y : R4) :
    ‖f x - f y‖ ≤ TestFunctions.lipConstR4 f * euclidNormVec (x - y) := by
  obtain ⟨-, K, hK, hL⟩ := hf
  have hne : {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y}.Nonempty :=
    ⟨K, hK, hL⟩
  have h0 : 0 ≤ euclidNormVec (x - y) := Real.sqrt_nonneg _
  rcases h0.eq_or_lt with h0 | hpos
  · have := hL x y
    rw [← h0] at this ⊢
    simpa using this
  · rw [← div_le_iff₀ hpos]
    refine le_csInf hne fun C hC => ?_
    rw [div_le_iff₀ hpos]
    exact hC.2 x y
theorem sharp_nonneg (c : SharpScale) (f : R4 → E) : 0 ≤ c.sharpNorm f :=
  le_max_of_le_left (uniformNorm_nonneg f)
theorem uniformNorm_le_sharpNorm (c : SharpScale) (f : R4 → E) :
    TestFunctions.uniformNorm f ≤ c.sharpNorm f :=
  le_max_left _ _
theorem lipConstR4_le_sharpNorm (c : SharpScale) (f : R4 → E) :
    40 * c.M * TestFunctions.lipConstR4 f ≤ c.sharpNorm f :=
  le_max_right _ _
theorem sharp_add_le (c : SharpScale) {f g : R4 → E} (hf : BoundedLipschitz f)
    (hg : BoundedLipschitz g) : c.sharpNorm (f + g) ≤ c.sharpNorm f + c.sharpNorm g := by
  have hM : 0 ≤ 40 * c.M := by
    have := c.one_le
    linarith
  have a₁ := uniformNorm_le_sharpNorm c f
  have a₂ := uniformNorm_le_sharpNorm c g
  have b₁ := lipConstR4_le_sharpNorm c f
  have b₂ := lipConstR4_le_sharpNorm c g
  refine max_le ?_ ?_
  · have : TestFunctions.uniformNorm (f + g) ≤
        TestFunctions.uniformNorm f + TestFunctions.uniformNorm g :=
      uniformNorm_le_of_forall (add_nonneg (uniformNorm_nonneg f) (uniformNorm_nonneg g)) fun x =>
        (norm_add_le _ _).trans (add_le_add (norm_le_uniformNorm hf x) (norm_le_uniformNorm hg x))
    linarith
  · have : TestFunctions.lipConstR4 (f + g) ≤
        TestFunctions.lipConstR4 f + TestFunctions.lipConstR4 g := by
      refine lipConstR4_le_of_forall (add_nonneg (lipConstR4_nonneg f) (lipConstR4_nonneg g))
        fun x y => ?_
      have e : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
        simp only [Pi.add_apply]
        abel
      rw [e, add_mul]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_sub_le_lipConstR4_mul hf x y) (norm_sub_le_lipConstR4_mul hg x y))
    have := mul_le_mul_of_nonneg_left this hM
    linarith
end Norms
theorem boundedLipschitz_of_mem {𝕜 : Type*} [RCLike 𝕜] {f : R4 → 𝕜} (hf : f ∈ C1c 𝕜) :
    BoundedLipschitz f := by
  obtain ⟨hc, hs⟩ := (mem_C1c_iff_contDiff f).1 hf
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hc.continuous
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hs hc one_ne_zero
  refine ⟨⟨B, hB⟩, K, K.2, fun x y => ?_⟩
  have := hK.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at this
  exact this.trans (mul_le_mul_of_nonneg_left (norm_le_euclidNormVec _) K.2)
theorem C1c_sub_mem {f g : R4 → ℂ} (hf : f ∈ C1c ℂ) (hg : g ∈ C1c ℂ) : f - g ∈ C1c ℂ := by
  rw [mem_C1c_iff_contDiff] at hf hg ⊢
  refine ⟨hf.1.sub hg.1, ?_⟩
  have hsum := hf.2.add hg.2.neg
  rwa [← sub_eq_add_neg] at hsum
theorem supp_sub_subset (f g : R4 → ℂ) : supp (f - g) ⊆ supp f ∪ supp g := by
  rw [supp_eq_tsupport, supp_eq_tsupport, supp_eq_tsupport]
  exact closure_minimal ((Function.support_sub f g).trans
    (Set.union_subset_union (subset_tsupport f) (subset_tsupport g)))
    ((isClosed_tsupport f).union (isClosed_tsupport g))
theorem partitionConst_nonneg {C : ℕ → ℝ → ℝ → ℝ} {d R : ℝ} (hC : ∀ m, 2 ≤ m → 0 ≤ C m d R)
    (n : ℕ) : 0 ≤ partitionConst C n d R :=
  Finset.sum_nonneg fun _ hπ => Finset.prod_nonneg fun J hJ =>
    hC _ ((Finset.mem_filter.1 hπ).2 J hJ)
theorem abs_centeredFn_le {c : SharpScale} {S : ConnFamily} {C : ℕ → ℝ → ℝ → ℝ}
    (hb : HasClusterBounds S c C) {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (X : sepAll)
    (hball : ∀ i : Fin X.1.length, ∃ x, supp (X.1.get i) ⊆ TestFunctions.closedBallR4 x R)
    (hdist : Pairwise fun i j : Fin X.1.length => ENNReal.ofReal d ≤
      TestFunctions.setDistR4 (supp (X.1.get i)) (supp (X.1.get j))) :
    |centeredFn S X| ≤ partitionConst C X.1.length d R * ∏ i, c.sharpNorm (X.1.get i) := by
  have hsep := isSeparatedList_of_mem_sepAll X.2
  have hblock : ∀ J : Finset (Fin X.1.length), 2 ≤ J.card →
      |S.evalAt J.card (Ambient.subList X.1 J)| ≤
        C J.card d R * ∏ i ∈ J, c.sharpNorm (X.1.get i) := by
    intro J hJ
    have hY := Ambient.subList_mem_separatedN hsep J
    rw [Ambient.ConnectedFamily.evalAt_of_mem S hJ hY]
    have key := hb J.card hJ R d hR hd (fun k => X.1.get (J.orderEmbOfFin rfl k)) hY
      (fun k => hball _) (fun k l hkl => hdist fun e => hkl ((J.orderEmbOfFin rfl).injective e))
    have hprod : ∏ k, c.sharpNorm (X.1.get (J.orderEmbOfFin rfl k)) =
        ∏ i ∈ J, c.sharpNorm (X.1.get i) := by
      have hm := Finset.prod_map Finset.univ (J.orderEmbOfFin rfl).toEmbedding
        fun i => c.sharpNorm (X.1.get i)
      rw [Finset.map_orderEmbOfFin_univ] at hm
      exact hm.symm
    rw [hprod] at key
    exact key
  change |∑ π ∈ SetPartition.nonSingletonPartitions X.1.length,
    ∏ J ∈ π.parts, S.evalAt J.card (Ambient.subList X.1 J)| ≤ _
  unfold partitionConst
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π hπ => ?_)
  have h2 := (Finset.mem_filter.1 hπ).2
  rw [Finset.abs_prod]
  calc ∏ J ∈ π.parts, |S.evalAt J.card (Ambient.subList X.1 J)|
      ≤ ∏ J ∈ π.parts, (C J.card d R * ∏ i ∈ J, c.sharpNorm (X.1.get i)) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun J hJ => hblock J (h2 J hJ)
    _ = (∏ J ∈ π.parts, C J.card d R) * ∏ i, c.sharpNorm (X.1.get i) := by
        rw [Finset.prod_mul_distrib]
        congr 1
        have hu := Finset.prod_biUnion (s := π.parts) (t := id)
          (f := fun i => c.sharpNorm (X.1.get i)) π.disjoint
        rw [π.biUnion_parts] at hu
        exact hu.symm
theorem ofFn_mem_sepN {n : ℕ} {A : Fin n → Set R4} {d : ℝ} (hd : 0 < d)
    (hdist : Pairwise fun k l => ENNReal.ofReal d ≤ TestFunctions.setDistR4 (A k) (A l))
    {g : Fin n → R4 → ℝ} (hg : ∀ l, g l ∈ C1c ℝ)
    (hgA : ∀ l, supp (g l) ⊆ A l) : List.ofFn g ∈ sepN n := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact hg i
  · have hp : List.Pairwise (fun f f' : R4 → ℝ => Disjoint (supp f) (supp f')) (List.ofFn g) :=
      List.pairwise_ofFn.2 fun i j hij =>
        (disjoint_of_ofReal_le_setDistR4 hd (hdist hij.ne)).mono (hgA i) (hgA j)
    exact hp
theorem norm_centeredFnFree_real_le {c : SharpScale} {S : ConnFamily} {C : ℕ → ℝ → ℝ → ℝ}
    (hb : HasClusterBounds S c C) {R d : ℝ} (hR : 0 < R) (hd : 0 < d) {n : ℕ}
    {A : Fin n → Set R4}
    (hball : ∀ l, ∃ x, A l ⊆ TestFunctions.closedBallR4 x R)
    (hdist : Pairwise fun k l => ENNReal.ofReal d ≤ TestFunctions.setDistR4 (A k) (A l))
    {g : Fin n → R4 → ℝ} (hg : ∀ l, g l ∈ C1c ℝ)
    (hgA : ∀ l, supp (g l) ⊆ A l) :
    ‖centeredFnFree S (toFree (List.ofFn g))‖ ≤
      partitionConst C n d R * ∏ l, c.sharpNorm (g l) := by
  have hX : List.ofFn g ∈ sepAll :=
    Ambient.separatedN_subset_separatedAll _ _ n (ofFn_mem_sepN hd hdist hg hgA)
  have e : centeredFnFree S (toFree (List.ofFn g)) =
      ((centeredFn S ⟨_, hX⟩ : ℝ) : ℂ) :=
    liftLin_toFree _ ⟨_, hX⟩
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have hlen : (List.ofFn g).length = n := List.length_ofFn
  have hget : ∀ i : Fin (List.ofFn g).length, (List.ofFn g).get i = g (Fin.cast hlen i) :=
    fun i => List.get_ofFn _ _
  have key := abs_centeredFn_le hb hR hd ⟨_, hX⟩
    (fun i => by
      obtain ⟨x, hx⟩ := hball (Fin.cast hlen i)
      refine ⟨x, ?_⟩
      change supp ((List.ofFn g).get i) ⊆ _
      rw [hget]
      exact (hgA _).trans hx)
    (fun i j hij => by
      change _ ≤ TestFunctions.setDistR4 (supp ((List.ofFn g).get i))
        (supp ((List.ofFn g).get j))
      rw [hget, hget]
      exact (hdist fun e => hij (Fin.cast_injective hlen e)).trans
        (setDistR4_anti (hgA _) (hgA _)))
  have hp : ∏ i, c.sharpNorm ((List.ofFn g).get i) = ∏ l, c.sharpNorm (g l) :=
    Fintype.prod_equiv (finCongr hlen) _ _ fun i => by
      rw [hget]
      rfl
  have hn : partitionConst C (List.ofFn g).length d R = partitionConst C n d R :=
    congrArg (fun m => partitionConst C m d R) hlen
  change |centeredFn S ⟨_, hX⟩| ≤ partitionConst C (List.ofFn g).length d R *
    ∏ i, c.sharpNorm ((List.ofFn g).get i) at key
  rwa [hp, hn] at key
theorem reImPart_mem_and_le (hs : SharpNormC1.Main) (c : SharpScale)
    {h : R4 → ℂ} (hh : h ∈ C1c ℂ) (ε : Fin 2) :
    reOrImPart ε h ∈ C1c ℝ ∧ supp (reOrImPart ε h) ⊆ supp h ∧
      c.sharpNorm (reOrImPart ε h) ≤ c.sharpNorm h := by
  obtain ⟨m₀, m₁, hsub, n₀, n₁⟩ := (hs.2 c).2.1 h hh
  by_cases e : ε = 0
  · have e' : reOrImPart ε h = fun x => (h x).re := by simp [reOrImPart, e]
    rw [e']
    exact ⟨m₀, Set.subset_union_left.trans hsub, n₀⟩
  · have e' : reOrImPart ε h = fun x => (h x).im := by simp [reOrImPart, e]
    rw [e']
    exact ⟨m₁, Set.subset_union_right.trans hsub, n₁⟩
theorem norm_momentAt_le (hT : TensorComponents.CenteredSeesTensorComps)
    (hs : SharpNormC1.Main) {c : SharpScale} {S : ConnFamily} {b : ℝ} (hb0 : 0 ≤ b)
    {n : ℕ} (hn : 1 ≤ n) {A : Fin n → Set R4} (hdisj : Pairwise fun k l => Disjoint (A k) (A l))
    (hreal : ∀ g : Fin n → R4 → ℝ, (∀ l, g l ∈ C1c ℝ) →
      (∀ l, supp (g l) ⊆ A l) →
      ‖centeredFnFree S (toFree (List.ofFn g))‖ ≤ b * ∏ l, c.sharpNorm (g l))
    {h : Fin n → R4 → ℂ} (hh : ∀ l, h l ∈ C1c ℂ)
    (hA : ∀ l, supp (h l) ⊆ A l) :
    ‖momentAt S h‖ ≤ 2 ^ n * b * ∏ l, c.sharpNorm (h l) := by
  have hE : ComplexComponents h := ⟨hn, hh, fun k l hkl => (hdisj hkl).mono (hA k) (hA l)⟩
  unfold momentAt
  rw [(hT S).2.2.2.2 n h hE]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ε : Fin n → Fin 2, ‖(Complex.I ^ ∑ l, (ε l : ℕ)) *
      centeredFnFree S (toFree (List.ofFn fun l => reOrImPart (ε l) (h l)))‖ ≤
        b * ∏ l, c.sharpNorm (h l) := by
    intro ε
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    refine (hreal _ (fun l => (reImPart_mem_and_le hs c (hh l) (ε l)).1)
      (fun l => (reImPart_mem_and_le hs c (hh l) (ε l)).2.1.trans (hA l))).trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => sharp_nonneg c _)
      fun l _ => (reImPart_mem_and_le hs c (hh l) (ε l)).2.2) hb0
  refine (Finset.sum_le_sum fun ε _ => hterm ε).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : Fintype.card (Fin n → Fin 2) = 2 ^ n := by simp
  rw [hcard]
  push_cast
  ring_nf
  exact le_rfl
theorem clusterConst_nonneg {c : SharpScale} {S : ConnFamily} {C : ℕ → ℝ → ℝ → ℝ}
    (hb : HasClusterBounds S c C) {n : ℕ} (hn : 2 ≤ n) {R d : ℝ} (hR : 0 < R) (hd : 0 < d) :
    0 ≤ C n d R := by
  let ctr : Fin n → R4 := fun k => Pi.single 0 (((k : ℕ) : ℝ) * (2 * R + d))
  let φ : ∀ k, ContDiffBump (ctr k) := fun k => ⟨R / 4, R / 2, by positivity, by linarith⟩
  let f : Fin n → R4 → ℝ := fun k x => φ k x
  have hmem : ∀ k, f k ∈ C1c ℝ := fun k =>
    (mem_C1c_iff_contDiff _).2 ⟨(φ k).contDiff, (φ k).hasCompactSupport⟩
  have hsupp : ∀ k, supp (f k) = Metric.closedBall (ctr k) (R / 2) := fun k =>
    (supp_eq_tsupport _).trans (φ k).tsupport_eq
  have hcoord : ∀ k (a : R4), a ∈ Metric.closedBall (ctr k) (R / 2) →
      |a 0 - ((k : ℕ) : ℝ) * (2 * R + d)| ≤ R / 2 := by
    intro k a ha
    have h₁ : ‖a - ctr k‖ ≤ R / 2 := by
      rwa [Metric.mem_closedBall, dist_eq_norm] at ha
    have h₂ := (norm_le_pi_norm (a - ctr k) 0).trans h₁
    simpa [ctr] using h₂
  have hdistance : Pairwise fun k l => ENNReal.ofReal d ≤
      TestFunctions.setDistR4 (supp (f k)) (supp (f l)) := by
    intro k l hkl
    rw [hsupp, hsupp]
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb' => ENNReal.ofReal_le_ofReal ?_
    have a0 := abs_le.1 (hcoord k a ha)
    have b0 := abs_le.1 (hcoord l b hb')
    have ab : |a 0 - b 0| ≤ euclidNormVec (a - b) := by
      have := (norm_le_pi_norm (a - b) 0).trans (norm_le_euclidNormVec _)
      simpa using this
    have hw : 0 < 2 * R + d := by positivity
    refine le_trans ?_ ab
    have hne : (k : ℕ) ≠ (l : ℕ) := fun e => hkl (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h' : ((k : ℕ) : ℝ) + 1 ≤ ((l : ℕ) : ℝ) := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right h' hw.le
      refine le_abs.2 (Or.inr ?_)
      nlinarith [a0.1, a0.2, b0.1, b0.2]
    · have h' : ((l : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right h' hw.le
      refine le_abs.2 (Or.inl ?_)
      nlinarith [a0.1, a0.2, b0.1, b0.2]
  have hsep : List.ofFn f ∈ sepN n :=
    ofFn_mem_sepN (A := fun k => supp (f k)) hd hdistance hmem fun _ => subset_rfl
  have hball : ∀ k, ∃ x, supp (f k) ⊆ TestFunctions.closedBallR4 x R := fun k => by
    refine ⟨ctr k, ?_⟩
    rw [hsupp]
    intro a ha
    have h₁ : ‖a - ctr k‖ ≤ R / 2 := by
      rwa [Metric.mem_closedBall, dist_eq_norm] at ha
    have := euclidNormVec_le_two_mul_norm (a - ctr k)
    change euclidNormVec (a - ctr k) ≤ R
    linarith
  have key := hb n hn R d hR hd f hsep hball hdistance
  have hP : 0 < ∏ k, c.sharpNorm (f k) := Finset.prod_pos fun k _ => by
    have h₁ := norm_le_uniformNorm (boundedLipschitz_of_mem (hmem k)) (ctr k)
    have h₂ : f k (ctr k) = 1 :=
      (φ k).one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    rw [h₂, norm_one] at h₁
    exact lt_of_lt_of_le one_pos (h₁.trans (uniformNorm_le_sharpNorm c _))
  by_contra hneg
  have := mul_neg_of_neg_of_pos (not_le.1 hneg) hP
  linarith [abs_nonneg (S.fn n hn ⟨List.ofFn f, hsep⟩)]
def hybridTuple {n : ℕ} (f f' : Fin n → R4 → ℂ) (l : Fin n) : Fin n → R4 → ℂ :=
  fun k => if k < l then f' k else if k = l then f l - f' l else f k
theorem prod_sub_prod_eq_sum {n : ℕ} (a a' : Fin n → ℂ) :
    ∏ k, a k - ∏ k, a' k =
      ∑ l, ∏ k, (if k < l then a' k else if k = l then a l - a' l else a k) := by
  have ho := Finset.prod_sub_ordered Finset.univ a (fun i => a i - a' i)
  simp only [sub_sub_cancel] at ho
  rw [ho, sub_sub_cancel]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : ∀ k, (if k < l then a' k else if k = l then a l - a' l else a k) =
      (if k = l then a l - a' l else 1) *
        ((if k < l then a' k else 1) * (if l < k then a k else 1)) := by
    intro k
    rcases lt_trichotomy k l with hk | rfl | hk
    · simp [hk, hk.ne, hk.not_gt]
    · simp
    · simp [hk, hk.ne', hk.not_gt]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.prod_filter, mul_assoc]
theorem norm_centeredFnFree_real_le_of_sep {c : SharpScale} {S : ConnFamily}
    {C : ℕ → ℝ → ℝ → ℝ} (hb : HasClusterBounds S c C) {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    {n : ℕ} {A : Fin n → Set R4} (hA : SeparatedInBalls A R d) (g : Fin n → R4 → ℝ)
    (hg : ∀ l, g l ∈ C1c ℝ) (hgA : ∀ l, supp (g l) ⊆ A l) :
    ‖centeredFnFree S (toFree (List.ofFn g))‖ ≤
      partitionConst C n d R * ∏ l, c.sharpNorm (g l) :=
  norm_centeredFnFree_real_le hb hR hd hA.1 hA.2 hg hgA
theorem momentLipschitzBound_holds (hT : TensorComponents.CenteredSeesTensorComps)
    (hs : SharpNormC1.Main) (ht : TupleRules.TupleSpanActionRules)
    {c : SharpScale} {S : ConnFamily} {C : ℕ → ℝ → ℝ → ℝ} (hb : HasClusterBounds S c C) {n : ℕ}
    (hn : 2 ≤ n) {R d : ℝ} (hR : 0 < R) (hd : 0 < d) {A : Fin n → Set R4}
    (hA : SeparatedInBalls A R d) {f f' : Fin n → R4 → ℂ} (hf : EntriesSupportedIn A f)
    (hf' : EntriesSupportedIn A f') : MomentLipschitzBound c S C d R f f' := by
  have hC : ∀ m, 2 ≤ m → 0 ≤ C m d R := fun m hm => clusterConst_nonneg hb hm hR hd
  have hb0 := partitionConst_nonneg hC n
  have hdisj : Pairwise fun k l => Disjoint (A k) (A l) := fun k l hkl =>
    disjoint_of_ofReal_le_setDistR4 hd (hA.2 hkl)
  have hyb : ∀ l k, hybridTuple f f' l k ∈ C1c ℂ ∧
      supp (hybridTuple f f' l k) ⊆ A k := by
    intro l k
    simp only [hybridTuple]
    split_ifs with e₁ e₂
    · exact hf' k
    · subst e₂
      exact ⟨C1c_sub_mem (hf k).1 (hf' k).1, (supp_sub_subset _ _).trans
        (Set.union_subset (hf k).2 (hf' k).2)⟩
    · exact hf k
  have hn1 : 1 ≤ n := by omega
  have tens : ∀ h : Fin n → R4 → ℂ, EntriesSupportedIn A h →
      tensorComp n (complexTuple h) = tensorOfFns h ∧
        tensorCompZero (complexTuple h) = 0 ∧
        ∀ m, 1 ≤ m → m ≠ n → tensorComp m (complexTuple h) = 0 := by
    intro h hh
    have hE : ComplexComponents h :=
      ⟨hn1, fun l => (hh l).1, fun k l hkl => (hdisj hkl).mono (hh k).2 (hh l).2⟩
    obtain ⟨-, -, t₁, t₂, t₃, -⟩ :=
      ht.2.2.2.2.2.2.2.1 Set.univ isOpen_univ timeFlip n h hE fun _ => Set.subset_univ _
    exact ⟨t₁, t₂, t₃⟩
  have Tf := tens f hf
  have Tf' := tens f' hf'
  have Th := fun l => tens (hybridTuple f f' l) (hyb l)
  have same : SameTensors (complexTuple f - complexTuple f')
      (∑ l, complexTuple (hybridTuple f f' l)) := by
    refine ⟨?_, fun m hm => ?_⟩
    · rw [map_sub, map_sum, Tf.2.1, Tf'.2.1, sub_zero]
      exact (Finset.sum_eq_zero fun l _ => (Th l).2.1).symm
    · rw [map_sub, map_sum]
      by_cases hmn : m = n
      · rw [hmn, Tf.1, Tf'.1]
        simp only [(Th _).1]
        funext x
        simp only [Pi.sub_apply, Finset.sum_apply, tensorOfFns_apply]
        rw [prod_sub_prod_eq_sum (fun k => f k (x k)) (fun k => f' k (x k))]
        refine Finset.sum_congr rfl fun l _ => Finset.prod_congr rfl fun k _ => ?_
        simp only [hybridTuple]
        split_ifs with e₁ e₂
        · rfl
        · subst e₂
          rfl
        · rfl
      · rw [Tf.2.2 m hm hmn, Tf'.2.2 m hm hmn, sub_zero]
        exact (Finset.sum_eq_zero fun l _ => (Th l).2.2 m hm hmn).symm
  have agree := (hT S).2.1 _ _ same
  have ediff : momentAt S f - momentAt S f' = ∑ l, momentAt S (hybridTuple f f' l) := by
    unfold momentAt
    rw [← map_sub, ← map_sum]
    exact agree
  have hN : 0 ≤ (2 : ℝ) ^ n * partitionConst C n d R := mul_nonneg (by positivity) hb0
  unfold MomentLipschitzBound
  rw [ediff]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  refine (norm_momentAt_le hT hs hb0 hn1 hdisj (norm_centeredFnFree_real_le_of_sep hb hR hd hA)
    (fun k => (hyb l k).1) (fun k => (hyb l k).2)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hN
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  have hl : hybridTuple f f' l l = f l - f' l := by simp [hybridTuple]
  rw [hl]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => sharp_nonneg c _)
    fun k hk => ?_) (sharp_nonneg c _)
  have hkl : k ≠ l := Finset.ne_of_mem_erase hk
  simp only [hybridTuple]
  split_ifs with e₁
  · exact le_max_right _ _
  · exact le_max_left _ _
theorem momentContinuous_holds (hT : TensorComponents.CenteredSeesTensorComps)
    (hs : SharpNormC1.Main) (ht : TupleRules.TupleSpanActionRules)
    {c : SharpScale} {S : ConnFamily} {C : ℕ → ℝ → ℝ → ℝ} (hb : HasClusterBounds S c C) {n : ℕ}
    (hn : 2 ≤ n) {R d : ℝ} (hR : 0 < R) (hd : 0 < d) {A : Fin n → Set R4}
    (hA : SeparatedInBalls A R d) {h : Fin n → R4 → ℂ} (hh : EntriesSupportedIn A h) :
    MomentContinuous S A h := by
  intro g hg hlim
  have hN : 0 ≤ (2 : ℝ) ^ n * partitionConst C n d R :=
    mul_nonneg (by positivity)
      (partitionConst_nonneg (fun m hm => clusterConst_nonneg hb hm hR hd) n)
  have hu : ∀ l, Tendsto (fun j => c.sharpNorm (g j l - h l)) atTop (𝓝 0) := fun l =>
    (hs.2 c).2.2.1 (fun j => g j l) (h l) (fun j hj => (hg j hj l).1) (hh l).1 (hlim l)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlimit : Tendsto (fun j => 2 ^ n * partitionConst C n d R *
      ∑ l, c.sharpNorm (g j l - h l) *
        ∏ k ∈ Finset.univ.erase l, (c.sharpNorm (h k) + c.sharpNorm (g j k - h k)))
      atTop (𝓝 0) := by
    have e := (tendsto_finsetSum Finset.univ fun l _ => (hu l).mul
      (tendsto_finsetProd (Finset.univ.erase l) fun k _ =>
        (tendsto_const_nhds (x := c.sharpNorm (h k))).add (hu k))).const_mul
      (2 ^ n * partitionConst C n d R)
    simpa using e
  refine squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _) ?_ hlimit
  filter_upwards [eventually_ge_atTop 1] with j hj
  refine (momentLipschitzBound_holds hT hs ht hb hn hR hd hA (hg j hj) hh).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hN
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
    (fun _ _ => le_max_of_le_left (sharp_nonneg c _)) fun k _ => ?_) (sharp_nonneg c _)
  have hs' : 0 ≤ c.sharpNorm (g j k - h k) := sharp_nonneg c _
  refine max_le ?_ (by linarith [sharp_nonneg c (h k)])
  have e := sharp_add_le c (boundedLipschitz_of_mem (hh k).1)
    (boundedLipschitz_of_mem (C1c_sub_mem (hg j hj k).1 (hh k).1))
  rwa [add_sub_cancel] at e
theorem partitionConstLocal_holds (n : ℕ) (d R : ℝ) : PartitionConstLocal n d R := by
  intro C C' e
  refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_
  exact e _ ((Finset.mem_filter.1 hπ).2 J hJ) ((Finset.card_le_univ J).trans_eq (Fintype.card_fin n))
theorem momentBoundsTheorem_holds
    (h₁ : TensorComponents.CenteredSeesTensorComps)
    (h₂ : SharpNormC1.Main) (h₃ : TupleRules.TupleSpanActionRules) :
    MomentBoundsTheorem := by
  intro c S σ n hn R d hR hd A hA h h' hh hh'
  have hb := σ.cluster
  have hC : ∀ m, 2 ≤ m → 0 ≤ σ.clusterConst m d R := fun m hm => clusterConst_nonneg hb hm hR hd
  refine ⟨?_, momentLipschitzBound_holds h₁ h₂ h₃ hb hn hR hd hA hh hh',
    momentContinuous_holds h₁ h₂ h₃ hb hn hR hd hA hh, partitionConstLocal_holds n d R⟩
  exact norm_momentAt_le h₁ h₂ (partitionConst_nonneg hC n) (by omega)
    (fun k l hkl => disjoint_of_ofReal_le_setDistR4 hd (hA.2 hkl))
    (norm_centeredFnFree_real_le_of_sep hb hR hd hA) (fun l => (hh l).1) (fun l => (hh l).2)
end YangMills.Construction.EuclideanFunctionals.Moments
