import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.MetricNotions
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace
section Euclid
variable {S : ℝ}
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem torusEuclidNorm_eq_euclidNormVec_norm (z : Torus4 S) :
    torusEuclidNorm z = euclidNormVec fun μ => ‖z μ‖ := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
theorem exists_torusProj_eq_euclidNormVec_eq (z : Torus4 S) :
    ∃ b, torusProj S b = z ∧ euclidNormVec b = torusEuclidNorm z := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
theorem torusEuclidNorm_torusProj_le (v : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem torusProj_sub (x y : Fin 4 → ℝ) : torusProj S x - torusProj S y = torusProj S (x - y) := by apply _root_.YangMills.SharedProofs.p13492 <;> assumption
theorem dist_le_euclidDistTorus (x y : Torus4 S) : dist x y ≤ euclidDistTorus x y := by
  have h0 : 0 ≤ euclidDistTorus x y := by
    unfold euclidDistTorus
    rw [torusEuclidNorm_eq_euclidNormVec_norm]
    exact euclidNormVec_nonneg _
  refine (dist_pi_le_iff h0).2 fun μ => ?_
  unfold euclidDistTorus
  rw [torusEuclidNorm_eq_euclidNormVec_norm, dist_eq_norm]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun ν => ‖(x - y) ν‖ ^ 2)
    (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
theorem euclidDistTorus_le_two_mul_dist (x y : Torus4 S) :
    euclidDistTorus x y ≤ 2 * dist x y := by
  unfold euclidDistTorus
  rw [torusEuclidNorm_eq_euclidNormVec_norm]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ μ, ‖(x - y) μ‖ ^ 2 ≤ ∑ _μ : Fin 4, dist x y ^ 2 := by
        refine Finset.sum_le_sum fun μ _ => ?_
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        have := dist_le_pi_dist x y μ
        rwa [dist_eq_norm] at this
    _ = (2 * dist x y) ^ 2 := by
        simp
        ring
theorem euclidDistTorus_nonneg (x y : Torus4 S) : 0 ≤ euclidDistTorus x y := by apply _root_.YangMills.SharedProofs.p31350 <;> assumption
theorem isMetricFunction_euclidDistTorus :
    FamilyTopology.IsMetricFunction (euclidDistTorus : Torus4 S → Torus4 S → ℝ) where
  nonneg := euclidDistTorus_nonneg
  eq_zero_iff x y := by
    constructor
    · intro h
      have h1 := dist_le_euclidDistTorus x y
      rw [h] at h1
      exact dist_le_zero.1 h1
    · rintro rfl
      have h1 := euclidDistTorus_le_two_mul_dist x x
      rw [dist_self, mul_zero] at h1
      exact le_antisymm h1 (euclidDistTorus_nonneg x x)
  symm x y := by
    unfold euclidDistTorus
    rw [torusEuclidNorm_eq_euclidNormVec_norm, torusEuclidNorm_eq_euclidNormVec_norm]
    congr 1
    funext μ
    exact norm_sub_rev _ _
  triangle x y z := by
    obtain ⟨b, hb, hb'⟩ := exists_torusProj_eq_euclidNormVec_eq (x - y)
    obtain ⟨c, hc, hc'⟩ := exists_torusProj_eq_euclidNormVec_eq (y - z)
    have hbc : torusProj S (b + c) = x - z := by
      funext μ
      have h1 := congrFun hb μ
      have h2 := congrFun hc μ
      simp only [torusProj, Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
      rw [AddCircle.coe_add, h1, h2]
      abel
    unfold euclidDistTorus
    rw [← hb', ← hc', ← hbc]
    exact (torusEuclidNorm_torusProj_le _).trans (euclidNormVec_add_le b c)
theorem isOpenWrt_euclidDistTorus_iff (U : Set (Torus4 S)) :
    IsOpenWrt euclidDistTorus U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨r, hr, hU⟩ := h x hx
    refine ⟨r / 2, by positivity, fun y hy => hU y ?_⟩
    have h1 := euclidDistTorus_le_two_mul_dist x y
    have h2 : dist x y < r / 2 := by rwa [Metric.mem_ball, dist_comm] at hy
    linarith
  · intro h x hx
    obtain ⟨r, hr, hU⟩ := h x hx
    refine ⟨r, hr, fun y hy => hU ?_⟩
    rw [Metric.mem_ball, dist_comm]
    exact (dist_le_euclidDistTorus x y).trans_lt hy
theorem closureWrt_euclidDistTorus_eq (Z : Set (Torus4 S)) :
    closureWrt euclidDistTorus Z = closure Z := by
  ext x
  rw [Metric.mem_closure_iff]
  constructor
  · intro h r hr
    obtain ⟨y, hy, hd⟩ := h r hr
    exact ⟨y, hy, (dist_le_euclidDistTorus x y).trans_lt hd⟩
  · intro h r hr
    obtain ⟨y, hy, hd⟩ := h (r / 2) (by positivity)
    refine ⟨y, hy, ?_⟩
    have h1 := euclidDistTorus_le_two_mul_dist x y
    linarith
theorem generateFrom_isOpenWrt_eq_borel :
    MeasurableSpace.generateFrom
        {U : Set (Torus4 S) | IsOpenWrt euclidDistTorus U} = borel (Torus4 S) := by
  rw [borel]
  congr 1
  ext U
  exact isOpenWrt_euclidDistTorus_iff U
theorem continuous_of_isLipschitzFor {E : Type*} [NormedAddCommGroup E] {f : Torus4 S → E}
    (hf : IsLipschitzFor euclidDistTorus f) : Continuous f := by
  obtain ⟨C, hC, h⟩ := hf
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (2 * C)) fun x y => ?_).continuous
  rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖f x - f y‖ ≤ C * euclidDistTorus x y := h x y
    _ ≤ C * (2 * dist x y) := by gcongr; exact euclidDistTorus_le_two_mul_dist x y
    _ = 2 * C * dist x y := by ring
theorem latticeTranslate_neg (k : Fin 4 → ℤ) : latticeTranslate S (-k) = -latticeTranslate S k := by
  funext μ
  simp [latticeTranslate]
theorem euclidDistTorus_torusProj_le (x y : Fin 4 → ℝ) :
    euclidDistTorus (torusProj S x) (torusProj S y) ≤ euclidNormVec (x - y) := by apply _root_.YangMills.DeltaSharedProofs.p50059 <;> assumption
theorem isLeast_euclidNormVec_translates (x y : Fin 4 → ℝ) :
    IsLeast (range fun k : Fin 4 → ℤ => euclidNormVec (x - y - latticeTranslate S k))
      (euclidDistTorus (torusProj S x) (torusProj S y)) := by
  unfold euclidDistTorus
  rw [torusProj_sub]
  constructor
  · obtain ⟨b, hb, hb'⟩ := exists_torusProj_eq_euclidNormVec_eq (torusProj S (x - y))
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hb
    refine ⟨-k, ?_⟩
    show euclidNormVec (x - y - latticeTranslate S (-k)) = _
    rw [← hb', hk, latticeTranslate_neg, sub_neg_eq_add]
  · rintro _ ⟨k, rfl⟩
    have h : torusProj S (x - y - latticeTranslate S k) = torusProj S (x - y) := by
      rw [sub_eq_add_neg (x - y), ← latticeTranslate_neg]
      exact torusProj_add_latticeTranslate S (x - y) (-k)
    rw [← h]
    exact torusEuclidNorm_torusProj_le _
end Euclid
section Compact
variable {S : ℝ} [Fact (0 < S)]
theorem isCompactWrt_univ : IsCompactWrt euclidDistTorus (univ : Set (Torus4 S)) := by
  intro 𝒰 hopen hcover
  obtain ⟨𝒰', h𝒰', hfin, hsub⟩ := isCompact_univ.elim_finite_subcover_image (b := 𝒰) (c := id)
    (fun U hU => (isOpenWrt_euclidDistTorus_iff U).1 (hopen U hU))
    (by simpa [sUnion_eq_biUnion] using hcover)
  exact ⟨𝒰', h𝒰', hfin, by simpa [sUnion_eq_biUnion] using hsub⟩
theorem isBoundedFun_of_continuous {E : Type*} [NormedAddCommGroup E] {f : Torus4 S → E}
    (hf : Continuous f) : IsBoundedFun f := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => hC x (mem_univ x)⟩
theorem exists_hasSeparatedSupportsTorus {E : Type*} [NormedAddCommGroup E] {q : ℕ} (hq : 1 ≤ q)
    (h : Fin q → Torus4 S → E)
    (hdisj : ∀ l l', l ≠ l' → tsupport (h l) ∩ tsupport (h l') = ∅) :
    ∃ d : ℝ, HasSeparatedSupportsTorus h d := by
  have hpair : ∀ i k, ∃ r : ℝ, 0 < r ∧
      (i ≠ k → ∀ a ∈ tsupport (h i), ∀ b ∈ tsupport (h k), r ≤ dist a b) := by
    intro i k
    by_cases hik : i = k
    · exact ⟨1, one_pos, fun hne => absurd hik hne⟩
    · obtain ⟨r, hr, hd⟩ := Metric.exists_pos_forall_lt_edist
        (isClosed_tsupport (h i)).isCompact (isClosed_tsupport (h k))
        (Set.disjoint_iff_inter_eq_empty.2 (hdisj i k hik))
      refine ⟨r, by exact_mod_cast hr, fun _ a ha b hb => ?_⟩
      have h1 := hd a ha b hb
      rw [edist_nndist] at h1
      have h2 : r < nndist a b := by exact_mod_cast h1
      exact NNReal.coe_le_coe.2 h2.le
  choose r hr hsep using hpair
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let d := Finset.univ.inf' Finset.univ_nonempty (fun p : Fin q × Fin q => r p.1 p.2)
  have hd0 : 0 < d := (Finset.lt_inf'_iff _).2 fun p _ => hr p.1 p.2
  have hdle : ∀ i k, d ≤ r i k := fun i k =>
    Finset.inf'_le (fun p : Fin q × Fin q => r p.1 p.2) (Finset.mem_univ (i, k))
  refine ⟨d, hd0, fun i k hik => ?_⟩
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
  exact (hdle i k).trans ((hsep i k hik a ha b hb).trans (dist_le_euclidDistTorus a b))
end Compact
section AtTheData
variable (D : MirrorData)
theorem torusSide_pos : 0 < PeriodicLattice.torusSide D.L D.m := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusSide_pos <;> assumption
theorem supp_eq_tsupport {E : Type*} [Zero E] (f : D.Torus → E) : D.supp f = tsupport f :=
  closureWrt_euclidDistTorus_eq _
theorem isBorelFn_of_continuous {E : Type*} [TopologicalSpace E] {f : D.Torus → E}
    (hf : Continuous f) : IsBorelFn D f := by
  intro B hB
  have hm : MeasurableSet[borel D.Torus] (f ⁻¹' B) :=
    @measurable_generateFrom D.Torus E (borel D.Torus) {s | IsOpen s} f
      (fun t ht => MeasurableSpace.measurableSet_generateFrom (hf.isOpen_preimage t ht)) B hB
  show MeasurableSet[MeasurableSpace.generateFrom {U | IsOpenWrt euclidDistTorus U}] (f ⁻¹' B)
  rw [generateFrom_isOpenWrt_eq_borel]
  exact hm
theorem supp_comp {s : D.Torus → D.Torus} (hsurj : Function.Surjective s)
    (hiso : D.IsDistPreserving s) {E : Type*} [Zero E] (h : D.Torus → E) :
    D.supp (h ∘ s) = s ⁻¹' D.supp h := by
  ext x
  change (∀ r : ℝ, 0 < r → ∃ y ∈ {u | (h ∘ s) u ≠ 0}, D.torusDist x y < r) ↔
    (∀ r : ℝ, 0 < r → ∃ y ∈ {u | h u ≠ 0}, D.torusDist (s x) y < r)
  constructor
  · intro hx r hr
    obtain ⟨y, hy, hd⟩ := hx r hr
    exact ⟨s y, hy, by rwa [hiso x y]⟩
  · intro hx r hr
    obtain ⟨y, hy, hd⟩ := hx r hr
    obtain ⟨y', rfl⟩ := hsurj y
    exact ⟨y', hy, by rwa [hiso x y'] at hd⟩
theorem isBorelFn_comp {s : D.Torus → D.Torus} (hiso : D.IsDistPreserving s) {E : Type*}
    [TopologicalSpace E] {h : D.Torus → E} (hh : IsBorelFn D h) :
    IsBorelFn D (h ∘ s) := by
  intro B hB
  let m : MeasurableSpace D.Torus :=
    MeasurableSpace.generateFrom {U | IsOpenWrt D.torusDist U}
  have hm : @Measurable _ _ m m s :=
    @measurable_generateFrom _ _ m _ _ fun U hU =>
      MeasurableSpace.measurableSet_generateFrom (show IsOpenWrt D.torusDist (s ⁻¹' U) from
        fun x hx => by
          obtain ⟨r, hr, hU'⟩ := hU (s x) hx
          exact ⟨r, hr, fun y hy => hU' (s y) (by rwa [hiso x y])⟩)
  exact hm (hh B hB)
theorem compactMetricTorus_holds : CompactMetricTorus D := by
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨torusSide_pos D⟩
  exact ⟨fun x y => isLeast_euclidNormVec_translates x y, isMetricFunction_euclidDistTorus,
    fun x y => euclidDistTorus_torusProj_le x y,
    fun x ε hε => ⟨ε, hε, fun y hy => (euclidDistTorus_torusProj_le x y).trans_lt hy⟩,
    isCompactWrt_univ⟩
theorem lipschitzBoundedBorel_holds : LipschitzBoundedBorel D := by
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨torusSide_pos D⟩
  intro E _ f hf
  have hc : Continuous f := continuous_of_isLipschitzFor hf
  refine ⟨?_, isBoundedFun_of_continuous hc, isBorelFn_of_continuous D hc⟩
  obtain ⟨C, hC, h⟩ := hf
  intro x ε hε
  refine ⟨ε / (C + 1), by positivity, fun y hy => ?_⟩
  have h1 := h x y
  have h0 : 0 ≤ D.torusDist x y := euclidDistTorus_nonneg x y
  have h2 : (C + 1) * D.torusDist x y < ε := by
    rwa [lt_div_iff₀' (by positivity)] at hy
  nlinarith
theorem disjointSuppSeparated_holds : DisjointSuppSeparated D := by
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨torusSide_pos D⟩
  have hts : ∀ {E : Type} [NormedAddCommGroup E] {q : ℕ} (h : Fin q → D.Torus → E),
      MirrorData.PairwiseDisjointSupp (D := D) h →
        ∀ l l', l ≠ l' → tsupport (h l) ∩ tsupport (h l') = ∅ := by
    intro E _ q h hdisj l l' hne
    have h1 := hdisj l l' hne
    rwa [supp_eq_tsupport D, supp_eq_tsupport D] at h1
  refine ⟨fun E _ q h hq hdisj => exists_hasSeparatedSupportsTorus hq h (hts h hdisj), ?_⟩
  intro q h hq hdisj hlip
  have hc : ∀ l, Continuous (h l) := fun l => continuous_of_isLipschitzFor (hlip l)
  obtain ⟨d, hd⟩ := exists_hasSeparatedSupportsTorus (by omega) h (hts h hdisj)
  have hbd : ∀ l, IsBoundedFun (h l) := fun l => isBoundedFun_of_continuous (hc l)
  have hme : ∀ l, Measurable (h l) := fun l => (hc l).measurable
  refine ⟨⟨hbd, hme, d, hd⟩, fun J _ => ⟨fun k => hbd _, fun k => hme _, d, hd.1, ?_⟩⟩
  intro i k hik
  exact hd.2 _ _ fun e => hik ((J.orderEmbOfFin rfl).injective e)
theorem isometryActionOnFunctions_holds : IsometryActionOnFunctions D := by
  intro s hbij hiso
  have hl := Function.leftInverse_surjInv hbij
  have hr := Function.rightInverse_surjInv hbij.2
  refine ⟨⟨Function.surjInv hbij.2, hl, hr, fun x ε hε => ⟨ε, hε, fun y hy => by rwa [hiso x y]⟩,
      fun x ε hε => ⟨ε, hε, fun y hy => ?_⟩⟩,
    fun E _ h => ⟨supp_comp D hbij.2 hiso h, ?_, isBorelFn_comp D hiso, ?_⟩,
    fun h hre u => hre (s u), fun E _ q h => ⟨?_, ?_⟩⟩
  · have h1 := hiso (Function.surjInv hbij.2 x) (Function.surjInv hbij.2 y)
    rw [hr x, hr y] at h1
    rwa [← h1]
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x => hC (s x)⟩
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun x y => ?_⟩
    have h1 := hC (s x) (s y)
    rwa [hiso x y] at h1
  · intro hdisj l l' hne
    show D.supp (h l ∘ s) ∩ D.supp (h l' ∘ s) = ∅
    rw [supp_comp D hbij.2 hiso, supp_comp D hbij.2 hiso, ← preimage_inter,
      hdisj l l' hne, preimage_empty]
  · intro d hsep
    have hmem : ∀ (l : Fin q) (a : D.Torus), a ∈ tsupport (h l ∘ s) → s a ∈ tsupport (h l) := by
      intro l a ha
      have h1 : a ∈ D.supp (h l ∘ s) := by
        rw [supp_eq_tsupport D]
        exact ha
      rw [supp_comp D hbij.2 hiso] at h1
      rw [← supp_eq_tsupport D]
      exact h1
    refine ⟨hsep.1, fun i k hik => ?_⟩
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    have h1 := hsep.2 i k hik
    unfold setEuclidDist at h1
    have h2 := h1.trans ((iInf₂_le (s a) (hmem i a ha)).trans (iInf₂_le (s b) (hmem k b hb)))
    have h3 : torusEuclidNorm (s a - s b) = torusEuclidNorm (a - b) := hiso a b
    rwa [h3] at h2
end AtTheData
theorem metricTorusFacts_holds : MetricTorusFacts := fun D =>
  ⟨compactMetricTorus_holds D, lipschitzBoundedBorel_holds D,
    disjointSuppSeparated_holds D, isometryActionOnFunctions_holds D⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace
end
