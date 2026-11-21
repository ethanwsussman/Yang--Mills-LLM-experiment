import YangMills.Construction.RotationInvariance.HalvingOfZeroSetsProof
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamilies
import YangMills.Construction.TorusOrFourSpace.FinitePartitionsOfUnityOfClassCInfinity
import YangMills.Construction.TorusOrFourSpace.FiniteSumsOfTensorsAreDenseOnAProduct
import YangMills.Construction.TorusOrFourSpace.RulesForTensors
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnSupportsNormsAndTestFunctions
import YangMills.Construction.TorusOrFourSpace.SmoothRealFunctionsInTheTwoSenses
import YangMills.Construction.TorusOrFourSpace.TensorOfASeparatedTupleWithSmoothEntries
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuplesSpanADenseSubspace
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DenseTensorSpan.SpanArgument
open YangMills.Construction.MetricNotions
open YangMills.Construction.PeriodicSpace.Kind.Tuple
open YangMills.Construction.TorusTransport.TestFunctionOrders (tensorMulti)
section MetricComparison
variable {X : Type*} [PseudoMetricSpace X] {d : X → X → ℝ}
theorem isOpenWrt_of_isOpen (hd : ∀ x y, dist x y ≤ d x y) {U : Set X} (hU : IsOpen U) :
    IsOpenWrt d U := by
  intro x hx
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨r, hr, fun y hy => hb ?_⟩
  rw [Metric.mem_ball, dist_comm]
  exact lt_of_le_of_lt (hd x y) hy
theorem isCompact_of_isCompactWrt (hd : ∀ x y, dist x y ≤ d x y) {Z : Set X}
    (hZ : IsCompactWrt d Z) : IsCompact Z := by
  classical
  refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
  obtain ⟨𝒰', hsub, hfin, hcov'⟩ := hZ (Set.range U)
    (by rintro _ ⟨i, rfl⟩; exact isOpenWrt_of_isOpen hd (hU i))
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hx)
      exact ⟨U i, ⟨i, rfl⟩, hi⟩)
  choose f hf using fun u : 𝒰' => hsub u.2
  have : Finite 𝒰' := hfin.to_subtype
  have := Fintype.ofFinite 𝒰'
  refine ⟨Finset.univ.image f, fun x hx => ?_⟩
  obtain ⟨u, hu, hxu⟩ := hcov' hx
  refine Set.mem_iUnion₂.2 ⟨f ⟨u, hu⟩, Finset.mem_image_of_mem f (Finset.mem_univ _), ?_⟩
  rw [hf ⟨u, hu⟩]
  exact hxu
theorem lt_of_dist_lt_of_le_mul {C : ℝ} (hC : 0 ≤ C) (h : ∀ x y, d x y ≤ C * dist x y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y, dist x y < δ → d x y < ε := by
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨ε / (C + 1), div_pos hε hC1, fun x y hxy => ?_⟩
  have h1 : C * dist x y ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hxy.le hC
  have h2 : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ hC1]
    nlinarith
  exact lt_of_le_of_lt ((h x y).trans h1) h2
theorem isOpen_of_isOpenWrt {C : ℝ} (hC : 0 ≤ C) (h : ∀ x y, d x y ≤ C * dist x y) {U : Set X}
    (hU : IsOpenWrt d U) : IsOpen U := by
  refine Metric.isOpen_iff.2 fun x hx => ?_
  obtain ⟨r, hr, hb⟩ := hU x hx
  obtain ⟨δ, hδ, hs⟩ := lt_of_dist_lt_of_le_mul hC h r hr
  refine ⟨δ, hδ, fun y hy => hb y (hs x y ?_)⟩
  rw [Metric.mem_ball, dist_comm] at hy
  exact hy
theorem isCompactWrt_of_isCompact {C : ℝ} (hC : 0 ≤ C) (h : ∀ x y, d x y ≤ C * dist x y)
    {Z : Set X} (hZ : IsCompact Z) : IsCompactWrt d Z := by
  intro 𝒰 hU hcov
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun u : 𝒰 => u.1)
    (fun u => isOpen_of_isOpenWrt hC h (hU _ u.2))
    (by
      intro x hx
      obtain ⟨u, hu, hxu⟩ := hcov hx
      exact Set.mem_iUnion.2 ⟨⟨u, hu⟩, hxu⟩)
  refine ⟨(fun u : 𝒰 => u.1) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
  · rintro _ ⟨u, _, rfl⟩
    exact u.2
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨u.1, ⟨u, hu, rfl⟩, hxu⟩
theorem isOpenWrt_inter {Y : Type*} {e : Y → Y → ℝ} {U V : Set Y} (hU : IsOpenWrt e U)
    (hV : IsOpenWrt e V) : IsOpenWrt e (U ∩ V) := by
  intro x hx
  obtain ⟨r, hr, hb⟩ := hU x hx.1
  obtain ⟨s, hs, hc⟩ := hV x hx.2
  exact ⟨min r s, lt_min hr hs, fun y hy =>
    ⟨hb y (lt_of_lt_of_le hy (min_le_left _ _)), hc y (lt_of_lt_of_le hy (min_le_right _ _))⟩⟩
end MetricComparison
section EuclideanDistances
variable (hspace : WellPosedness.WellPosed) (D : Params)
include hspace
theorem dist_le_quotDist_euclidean (x y : Fin 4 → ℝ) :
    dist x y ≤ Kind.quotDist D Kind.euclidean x y := by
  rw [(hspace D Kind.euclidean).2.2.2.2.2.2.2.1 x y]
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun μ => ?_
  rw [Real.dist_eq]
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun ν => (x - y) ν ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ))
theorem quotDist_euclidean_le (x y : Fin 4 → ℝ) :
    Kind.quotDist D Kind.euclidean x y ≤ 2 * dist x y := by
  rw [(hspace D Kind.euclidean).2.2.2.2.2.2.2.1 x y]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), (x - y) μ ^ 2 ≤ dist x y ^ 2 := by
    intro μ _
    have h2 : |(x - y) μ| ≤ dist x y := by
      have := dist_le_pi_dist x y μ
      rwa [Real.dist_eq] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h3 := Finset.sum_le_card_nsmul _ _ _ h1
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h3
  nlinarith
theorem dist_le_tupleDist {p : ℕ+} (y y' : Fin (p : ℕ) → Fin 4 → ℝ) :
    dist y y' ≤ tupleDist D Kind.euclidean (p := p) y y' := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  refine (dist_le_quotDist_euclidean hspace D (y i) (y' i)).trans ?_
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun j => Kind.quotDist D Kind.euclidean (y j) (y' j) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
theorem tupleDist_le {p : ℕ+} (y y' : Fin (p : ℕ) → Fin 4 → ℝ) :
    tupleDist D Kind.euclidean (p := p) y y' ≤ (2 * (p : ℕ) : ℝ) * dist y y' := by
  have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.pos
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin (p : ℕ))),
      Kind.quotDist D Kind.euclidean (y i) (y' i) ^ 2 ≤ (2 * dist y y') ^ 2 := by
    intro i _
    have h2 := quotDist_euclidean_le hspace D (y i) (y' i)
    have h3 := dist_le_pi_dist y y' i
    have h4 := dist_le_quotDist_euclidean hspace D (y i) (y' i)
    exact pow_le_pow_left₀ (dist_nonneg.trans h4) (h2.trans (by linarith)) 2
  have h3 := Finset.sum_le_card_nsmul _ _ _ h1
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  refine h3.trans ?_
  nlinarith
theorem isCompact_of_isCompactT {p : ℕ+} {K : Set (Fin (p : ℕ) → Fin 4 → ℝ)}
    (hK : IsCompactT D Kind.euclidean (p := p) K) : IsCompact K :=
  isCompact_of_isCompactWrt (d := fun y y' : Fin (p : ℕ) → Fin 4 → ℝ =>
    tupleDist D Kind.euclidean (p := p) y y') (dist_le_tupleDist hspace D) hK
theorem isCompactT_of_isCompact {p : ℕ+} {K : Set (Fin (p : ℕ) → Fin 4 → ℝ)}
    (hK : IsCompact K) : IsCompactT D Kind.euclidean (p := p) K :=
  isCompactWrt_of_isCompact (d := fun y y' : Fin (p : ℕ) → Fin 4 → ℝ =>
    tupleDist D Kind.euclidean (p := p) y y') (by positivity) (tupleDist_le hspace D) hK
theorem isCompactT_image2_appendPts {n n' : ℕ+} {K : Set (Fin (n : ℕ) → Fin 4 → ℝ)}
    {K' : Set (Fin (n' : ℕ) → Fin 4 → ℝ)}
    (hK : IsCompactT D Kind.euclidean (p := n) K)
    (hK' : IsCompactT D Kind.euclidean (p := n') K') :
    IsCompactT D Kind.euclidean (p := n + n')
      (Set.image2 (Euclid.appendPts D (n := n) (n' := n')) K K') := by
  have h1 : IsCompact K := isCompact_of_isCompactT hspace D hK
  have h2 : IsCompact K' := isCompact_of_isCompactT hspace D hK'
  have hc : Continuous fun z : (Fin (n : ℕ) → Fin 4 → ℝ) × (Fin (n' : ℕ) → Fin 4 → ℝ) =>
      (Fin.append z.1 z.2 : Fin ((n : ℕ) + (n' : ℕ)) → Fin 4 → ℝ) := by
    refine continuous_pi fun j => ?_
    induction j using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact (continuous_apply i).comp continuous_fst
    | right i =>
      simp only [Fin.append_right]
      exact (continuous_apply i).comp continuous_snd
  have h3 := (h1.prod h2).image hc
  have h4 : (fun z : (Fin (n : ℕ) → Fin 4 → ℝ) × (Fin (n' : ℕ) → Fin 4 → ℝ) =>
      (Fin.append z.1 z.2 : Fin ((n : ℕ) + (n' : ℕ)) → Fin 4 → ℝ)) '' (K ×ˢ K') =
      Set.image2 (Euclid.appendPts D) K K' := by
    ext z
    constructor
    · rintro ⟨⟨x, x'⟩, ⟨hx, hx'⟩, rfl⟩
      exact ⟨x, hx, x', hx', rfl⟩
    · rintro ⟨x, hx, x', hx', rfl⟩
      exact ⟨⟨x, x'⟩, ⟨hx, hx'⟩, rfl⟩
  rw [h4] at h3
  exact isCompactT_of_isCompact hspace D (p := n + n') h3
theorem tsupport_subset_supportQ (u : (Fin 4 → ℝ) → ℝ) :
    tsupport u ⊆ Kind.supportQ D Kind.euclidean u := by
  intro x hx r hr
  obtain ⟨δ, hδ, hs⟩ := lt_of_dist_lt_of_le_mul (d := fun x y : Fin 4 → ℝ =>
    Kind.quotDist D Kind.euclidean x y) (C := 2) (by norm_num)
    (quotDist_euclidean_le hspace D) r hr
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx δ hδ
  exact ⟨y, hy, hs x y hxy⟩
theorem hasCompactSupportIn_of_supportQ (u : (Fin 4 → ℝ) → ℝ) {O : Set (Fin 4 → ℝ)}
    (hK : Kind.IsCompactQ D Kind.euclidean (Kind.supportQ D Kind.euclidean u))
    (hO : Kind.supportQ D Kind.euclidean u ⊆ O) :
    TorusTransport.HasCompactSupportIn (E := ℝ) u O := by
  have h1 : @IsCompact (Fin 4 → ℝ) _ (Kind.supportQ D Kind.euclidean u) :=
    isCompact_of_isCompactWrt (d := fun x y : Fin 4 → ℝ => Kind.quotDist D Kind.euclidean x y)
      (dist_le_quotDist_euclidean hspace D) hK
  exact ⟨h1.of_isClosed_subset (isClosed_tsupport u) (tsupport_subset_supportQ hspace D u),
    (tsupport_subset_supportQ hspace D u).trans hO⟩
end EuclideanDistances
section AdmissibleFamilies
theorem mem_injTuplesIn_iff {n : ℕ} {O : Set (Fin 4 → ℝ)} {x : Fin n → Fin 4 → ℝ} :
    x ∈ Euclid.injTuplesIn O n ↔ Function.Injective x ∧ ∀ l, x l ∈ O := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : Function.Injective y := hy
    exact ⟨fun l l' h => hy' (Subtype.ext h), fun l => (y l).2⟩
  · rintro ⟨hx, hO⟩
    exact ⟨fun l => ⟨x l, hO l⟩, fun l l' h => hx (congrArg Subtype.val h), rfl⟩
theorem isOpenT_injTuplesIn (hpts : TupleFacts.AllFacts)
    (hdistinct : Kind.AdmissibleProductFacts) (D : Params)
    (n : ℕ+) {O : Set (Kind.euclidean.Pt D)} (hO : Kind.IsOpenQ D Kind.euclidean O) :
    IsOpenT D Kind.euclidean (p := n) (Euclid.injTuplesIn O (n : ℕ)) := by
  have h1 := (hdistinct D Kind.euclidean n).1
  have h2 := ((hpts D Kind.euclidean n).2.2.2.2.2.2.2.2.2.2.2.1 fun _ => O).1 fun _ => hO
  have h3 : Euclid.injTuplesIn O (n : ℕ) =
      Kind.pairwiseDistinct D Kind.euclidean n ∩
        boxSet D Kind.euclidean fun _ => O := by
    ext x
    exact mem_injTuplesIn_iff
  rw [h3]
  exact isOpenWrt_inter h1 h2
theorem admissibleWith_inter {D : Params} {n : ℕ+} {R d : ℝ}
    {G : Fin (n : ℕ) → Set (Kind.euclidean.Pt D)}
    (hG : Kind.AdmissibleWith D Kind.euclidean R d G) {O : Set (Kind.euclidean.Pt D)}
    (hO : Kind.IsOpenQ D Kind.euclidean O) :
    Kind.AdmissibleWith D Kind.euclidean R d fun i => G i ∩ O where
  radius_pos := hG.radius_pos
  sep_pos := hG.sep_pos
  isOpen_mem i := isOpenWrt_inter (hG.isOpen_mem i) hO
  diam_le i := by
    refine le_trans ?_ (hG.diam_le i)
    exact iSup₂_le fun z hz => iSup₂_le fun z' hz' =>
      le_iSup₂_of_le z hz.1 (le_iSup₂_of_le z' hz'.1 le_rfl)
  diam_lt_quarter_of_torus h := by cases h
  sep_le_setInfDist i i' hii' := by
    refine le_trans (hG.sep_le_setInfDist i i' hii') ?_
    exact le_iInf₂ fun z hz => le_iInf₂ fun z' hz' =>
      iInf₂_le_of_le z hz.1 (iInf₂_le_of_le z' hz'.1 le_rfl)
theorem disjoint_of_admissibleWith (hspace : WellPosedness.WellPosed)
    {D : Params} {n : ℕ+} {R d : ℝ} {G : Fin (n : ℕ) → Set (Kind.euclidean.Pt D)}
    (hG : Kind.AdmissibleWith D Kind.euclidean R d G) (i k : Fin (n : ℕ)) (hik : i ≠ k) :
    Disjoint (G i) (G k) := by
  refine Set.disjoint_left.2 fun y hi hk => ?_
  have h1 := hG.sep_le_setInfDist i k hik
  have h2 : Kind.setInfDist D Kind.euclidean (G i) (G k) ≤
      ENNReal.ofReal (Kind.quotDist D Kind.euclidean y y) :=
    iInf₂_le_of_le y hi (iInf₂_le_of_le y hk le_rfl)
  have h3 : Kind.quotDist D Kind.euclidean y y = 0 := by
    have h4 := (hspace D Kind.euclidean).2.2.2.2.2.2.2.1 y y
    have h6 : ∀ v : Fin 4 → ℝ, TorusMetric.euclidNormVec (v - v) = 0 := fun v => by
      simp [TorusMetric.euclidNormVec]
    exact h4.trans (h6 y)
  rw [h3, ENNReal.ofReal_zero] at h2
  have h5 := ENNReal.ofReal_pos.2 hG.sep_pos
  exact absurd (h1.trans h2) (not_le.2 h5)
theorem singleSet_eq_boxSet (D : Params) (H : Set (Kind.euclidean.Pt D)) :
    singleSet D Kind.euclidean H =
      boxSet D Kind.euclidean (n := 1) fun _ => H := by
  ext y
  constructor
  · intro h i
    have hi : i = ⟨0, (1 : ℕ+).pos⟩ := Fin.ext (by
      have := i.2
      simp only [PNat.one_coe] at this
      show (i : ℕ) = 0
      omega)
    rw [hi]
    exact h
  · intro h
    exact h _
theorem real_singleTestFn_facts (hpts : TupleFacts.AllFacts)
    (hsmooth : Kind.SmoothIffSmoothAsTuple) (D : Params)
    {H : Set (Kind.euclidean.Pt D)} {u : Kind.euclidean.Pt D → ℝ}
    (hu : (fun y => (u y : ℂ)) ∈ singleTestFns D Kind.euclidean H) :
    Kind.IsSmoothFn D Kind.euclidean u ∧ Kind.IsC1Fn D Kind.euclidean u ∧
      Kind.IsCompactQ D Kind.euclidean (Kind.supportQ D Kind.euclidean u) ∧
      Kind.supportQ D Kind.euclidean u ⊆ H := by
  obtain ⟨h1, h2, h3⟩ := hu
  have hc : Kind.IsC1Fn D Kind.euclidean u :=
    (((hpts D Kind.euclidean 1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u).1).1 (h1 1)
  have hs := (((hpts D Kind.euclidean 1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u).2 hc).2
  rw [hs] at h2 h3
  refine ⟨(hsmooth D Kind.euclidean u).2 h1, hc, ?_, ?_⟩
  · have h4 := (((hpts D Kind.euclidean 1).2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨0, (1 : ℕ+).pos⟩).2) _ h2
    have h5 : (fun y : Kind.euclidean.Tuple D 1 => y ⟨0, (1 : ℕ+).pos⟩) ''
        singleSet D Kind.euclidean (Kind.supportQ D Kind.euclidean u) =
        Kind.supportQ D Kind.euclidean u := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨fun _ => x, hx, rfl⟩
    rwa [h5] at h4
  · intro x hx
    exact h3 (a := fun _ => x) hx
theorem re_im_mem_singleTestFns (hpts : TupleFacts.AllFacts)
    (D : Params) {H : Set (Kind.euclidean.Pt D)} (hH : Kind.IsOpenQ D Kind.euclidean H)
    {φ : Kind.euclidean.Pt D → ℂ}
    (hφ : φ ∈ singleTestFns D Kind.euclidean H) :
    (fun y => (((φ y).re : ℝ) : ℂ)) ∈ singleTestFns D Kind.euclidean H ∧
      (fun y => (((φ y).im : ℝ) : ℂ)) ∈ singleTestFns D Kind.euclidean H := by
  have hopen : IsOpenT D Kind.euclidean (singleSet D Kind.euclidean H) := by
    rw [singleSet_eq_boxSet]
    exact ((hpts D Kind.euclidean 1).2.2.2.2.2.2.2.2.2.2.2.1 fun _ => H).1 fun _ => hH
  have h := ((hpts D Kind.euclidean 1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hopen).2 _ hφ
  exact ⟨h.1, h.2.1⟩
theorem tensorProd_mem_smoothSepTensorSpan (hpts : TupleFacts.AllFacts)
    (hsmooth : Kind.SmoothIffSmoothAsTuple)
    (hspace : WellPosedness.WellPosed) (D : Params) (n : ℕ+)
    (O : Set (Kind.euclidean.Pt D)) (H : Fin (n : ℕ) → Set (Kind.euclidean.Pt D))
    (hopen : ∀ i, Kind.IsOpenQ D Kind.euclidean (H i)) (hO : ∀ i, H i ⊆ O)
    (hdisj : ∀ i k, i ≠ k → Disjoint (H i) (H k))
    (φ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ)
    (hφ : ∀ i, φ i ∈ singleTestFns D Kind.euclidean (H i)) :
    tensorProd D Kind.euclidean φ ∈ smoothSepTensorSpan D n O := by
  classical
  let u : Bool → Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ :=
    fun b i y => if b then (φ i y).im else (φ i y).re
  have hu : ∀ b i, (fun y => ((u b i y : ℝ) : ℂ)) ∈
      singleTestFns D Kind.euclidean (H i) := by
    intro b i
    cases b
    · exact (re_im_mem_singleTestFns hpts D (hopen i) (hφ i)).1
    · exact (re_im_mem_singleTestFns hpts D (hopen i) (hφ i)).2
  have hf := fun b i => real_singleTestFn_facts hpts hsmooth D (hu b i)
  have hterm : ∀ p : Fin (n : ℕ) → Bool,
      (Kind.tensorFn D Kind.euclidean fun i y => ((u (p i) i y : ℝ) : ℂ)) ∈
        smoothSepTensorSpan D n O := by
    intro p
    refine Submodule.subset_span ⟨fun i => u (p i) i,
      ⟨fun i => (hf _ i).2.1, fun i => (hf _ i).2.2.1, fun i k hik => ?_⟩,
      fun i => (hf _ i).1,
      fun i => hasCompactSupportIn_of_supportQ hspace D _ (hf _ i).2.2.1
        ((hf _ i).2.2.2.trans (hO i)), rfl⟩
    exact (hdisj i k hik).mono (hf _ i).2.2.2 (hf _ k).2.2.2
  have hexp : tensorProd D Kind.euclidean φ =
      ∑ p : Fin (n : ℕ) → Bool, (∏ i, if p i then Complex.I else 1) •
        Kind.tensorFn D Kind.euclidean fun i y => ((u (p i) i y : ℝ) : ℂ) := by
    funext y
    have h1 : ∀ i, φ i (y i) =
        ∑ b : Bool, (if b then Complex.I else 1) * ((u b i (y i) : ℝ) : ℂ) := by
      intro i
      have h2 := Complex.re_add_im (φ i (y i))
      rw [Fintype.sum_bool]
      simp only [u, if_true, Bool.false_eq_true, if_false]
      linear_combination -h2
    have h3 : tensorProd D Kind.euclidean φ y = ∏ i, φ i (y i) := rfl
    rw [h3, Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_univ_sum, Fintype.piFinset_univ,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]
    rfl
  rw [hexp]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hterm p)
end AdmissibleFamilies
section Density
theorem mem_supportT_of_ne_zero (hpts : TupleFacts.AllFacts)
    {D : Params} {n : ℕ+} {F : Kind.euclidean.Tuple D n → ℂ}
    {y : Kind.euclidean.Tuple D n} (hy : F y ≠ 0) :
    y ∈ supportT D Kind.euclidean F := by
  intro r hr
  refine ⟨y, hy, ?_⟩
  rw [(((hpts D Kind.euclidean n).2.2.1.2.1) y y).2 rfl]
  exact hr
theorem cNorm_zero (hpts : TupleFacts.AllFacts)
    {D : Params} {n : ℕ+} (h0 : IsSmoothT D Kind.euclidean
      (0 : Kind.euclidean.Tuple D n → ℂ)) (ν : ℕ) :
    cNorm D Kind.euclidean ν (0 : Kind.euclidean.Tuple D n → ℂ) = 0 := by
  have hz : ∀ (α : CoordIndex n), α.degree ≤ ν → ∀ y,
      partialDeriv D Kind.euclidean α (0 : Kind.euclidean.Tuple D n → ℂ) y = 0 := by
    intro α hα y
    by_contra hne
    have h1 := (hpts D Kind.euclidean n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ν _ (h0 ν) α hα
    have h2 := h1.2.2.2.2.2 (mem_supportT_of_ne_zero hpts hne)
    obtain ⟨y', hy', _⟩ := h2 1 one_pos
    exact hy' rfl
  refine le_antisymm ?_ zero_le
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
  rw [hz α hα y]
  simp
theorem smoothSepTensorSpan_subset (hsupport : Euclid.SmoothSepTensorFacts)
    (htest : SupportNormFacts.Claim) (D : Params) (n : ℕ+)
    (O : Set (Kind.euclidean.Pt D)) (hO : Kind.IsOpenQ D Kind.euclidean O)
    (hΩ : IsOpenT D Kind.euclidean (p := n) (Euclid.injTuplesIn O (n : ℕ))) :
    ∀ F ∈ smoothSepTensorSpan D n O,
      F ∈ Kind.sepTensorSpan D Kind.euclidean (n : ℕ) ∧
        F ∈ testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) := by
  obtain ⟨S, hS⟩ := ((htest D n).2.2.2 _ hΩ).1
  have hle : smoothSepTensorSpan D n O ≤ Kind.sepTensorSpan D Kind.euclidean (n : ℕ) ⊓ S := by
    refine Submodule.span_le.2 ?_
    rintro F ⟨f, hf, hsm, hsupp, rfl⟩
    refine ⟨Submodule.subset_span ⟨f, hf, rfl⟩, ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hsupport D n O hO f hf hsm hsupp
    have h5 : (Kind.tensorFn D Kind.euclidean fun i y => ((f i y : ℝ) : ℂ)) ∈
        testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) :=
      ⟨h1, by rw [h2]; exact h3, by rw [h2]; exact h4⟩
    rw [← hS] at h5
    exact h5
  intro F hF
  have h6 := hle hF
  refine ⟨h6.1, ?_⟩
  rw [← hS]
  exact h6.2
theorem exists_seq_tendsto (hpts : TupleFacts.AllFacts)
    (hdistinct : Kind.AdmissibleProductFacts)
    (hdense : Kind.TensorSpanDenseOnBoxes)
    (hsmooth : Kind.SmoothIffSmoothAsTuple)
    (hspace : WellPosedness.WellPosed)
    (htest : SupportNormFacts.Claim)
    (hunity : SmoothFinitePartitionOfUnity) (D : Params) (n : ℕ+)
    (O : Set (Kind.euclidean.Pt D)) (hO : Kind.IsOpenQ D Kind.euclidean O)
    (hΩ : IsOpenT D Kind.euclidean (p := n) (Euclid.injTuplesIn O (n : ℕ)))
    (F : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ))) :
    ∃ Fs : ℕ+ → testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)),
      (∀ t, (Fs t).1 ∈ smoothSepTensorSpan D n O) ∧ TendstoInTestFns Fs F := by
  classical
  have hd := hdistinct D Kind.euclidean n
  let Good : (Fin (n : ℕ) → Set (Kind.euclidean.Pt D)) → Prop := fun H =>
    (∃ R d : ℝ, Kind.AdmissibleWith D Kind.euclidean R d H) ∧ (∀ i, (H i).Nonempty) ∧
      ∀ i, H i ⊆ O
  let 𝒰 : Set (Set (Kind.euclidean.Tuple D n)) :=
    {U | ∃ H, Good H ∧ U = boxSet D Kind.euclidean H}
  have hopen : ∀ H, Good H → IsOpenT D Kind.euclidean (boxSet D Kind.euclidean H) := by
    rintro H ⟨⟨R, d, hH⟩, -, -⟩
    exact (hd.2.1 H ⟨R, d, hH⟩).1
  have hcover : supportT D Kind.euclidean F.1 ⊆ ⋃₀ 𝒰 := by
    intro x hx
    obtain ⟨hinj, hxO⟩ := mem_injTuplesIn_iff.1 (F.2.2.2 hx)
    obtain ⟨G, ⟨R, d, hG⟩, hxG⟩ := hd.2.2.2.1 x hinj
    exact ⟨boxSet D Kind.euclidean fun i => G i ∩ O,
      ⟨_, ⟨⟨R, d, admissibleWith_inter hG hO⟩, fun i => ⟨x i, hxG i, hxO i⟩,
        fun i => Set.inter_subset_right⟩, rfl⟩, fun i => ⟨hxG i, hxO i⟩⟩
  obtain ⟨𝒰', hsub, hfin, hcov⟩ := F.2.2.1 𝒰
    (by rintro U ⟨H, hH, rfl⟩; exact hopen H hH) hcover
  have : Finite 𝒰' := hfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒰'
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hzero : F.1 = 0 := by
      funext y
      by_contra hne
      obtain ⟨u, hu, -⟩ := hcov (mem_supportT_of_ne_zero hpts hne)
      exact (e ⟨u, hu⟩).elim0
    have h0 : IsSmoothT D Kind.euclidean (0 : Kind.euclidean.Tuple D n → ℂ) :=
      hzero ▸ F.2.1
    refine ⟨fun _ => F, fun _ => ?_, ⟨supportT D Kind.euclidean F.1, F.2.2.1, F.2.2.2,
      subset_rfl, fun _ => subset_rfl⟩, fun ν => ?_⟩
    · rw [hzero]
      exact Submodule.zero_mem _
    · simp only [sub_self]
      rw [cNorm_zero hpts h0 ν]
      exact tendsto_const_nhds
  · let A : ℕ+ := ⟨m, hm⟩
    obtain ⟨e', -⟩ : ∃ e' : 𝒰' ≃ Fin (A : ℕ), True := ⟨e, trivial⟩
    have hgood : ∀ a : Fin (A : ℕ), ∃ H, Good H ∧
        (e'.symm a).1 = boxSet D Kind.euclidean H := fun a => hsub (e'.symm a).2
    choose H hH hP using hgood
    choose R d hadm using fun a => (hH a).1
    have hPopen : ∀ a, IsOpenT D Kind.euclidean (boxSet D Kind.euclidean (H a)) :=
      fun a => hopen _ (hH a)
    have hPsub : ∀ a, boxSet D Kind.euclidean (H a) ⊆
        Euclid.injTuplesIn O (n : ℕ) := by
      intro a y hy
      have h1 := (hd.2.1 (H a) ⟨R a, d a, hadm a⟩).2 hy
      exact mem_injTuplesIn_iff.2 ⟨h1, fun l => (hH a).2.2 l (hy l)⟩
    have hcovP : supportT D Kind.euclidean F.1 ⊆
        ⋃ a, boxSet D Kind.euclidean (H a) := by
      intro x hx
      obtain ⟨u, hu, hxu⟩ := hcov hx
      refine Set.mem_iUnion.2 ⟨e' ⟨u, hu⟩, ?_⟩
      rw [← hP, Equiv.symm_apply_apply]
      exact hxu
    obtain ⟨ψ, hψ, N, -, hKN, hsum⟩ := hunity D n A (supportT D Kind.euclidean F.1)
      (fun a => boxSet D Kind.euclidean (H a)) F.2.2.1 hPopen hcovP
    have hpiece : ∀ a, ψ a * F.1 ∈ testFns D Kind.euclidean
        (boxSet D Kind.euclidean (H a)) :=
      fun a => ((htest D n).2.2.2 _ (hPopen a)).2.1 F.1 (ψ a) F.2.1 (hψ a)
    have hlim := fun a => hdense D Kind.euclidean n (R a) (d a) (H a) (hadm a) (hH a).2.1
      ⟨ψ a * F.1, hpiece a⟩
    choose Fa hFa hconv using hlim
    have incl : ∀ a G, G ∈ testFns D Kind.euclidean
        (boxSet D Kind.euclidean (H a)) →
        G ∈ testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) :=
      fun a G hG => ⟨hG.1, hG.2.1, hG.2.2.trans (hPsub a)⟩
    let Gs : Fin (A : ℕ) → ℕ+ →
        testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) :=
      fun a t => ⟨(Fa a t).1, incl a _ (Fa a t).2⟩
    let L : Fin (A : ℕ) →
        testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) :=
      fun a => ⟨ψ a * F.1, incl a _ (hpiece a)⟩
    have hGs : ∀ a, TendstoInTestFns (Gs a) (L a) := by
      intro a
      obtain ⟨⟨K, hK, hKP, h1, h2⟩, h3⟩ := hconv a
      exact ⟨⟨K, hK, hKP.trans (hPsub a), h1, h2⟩, h3⟩
    obtain ⟨hs, h, hc⟩ := ((htest D n).2.2.2 _ hΩ).2.2.2 A Gs L hGs
    have hF : (⟨∑ a, (L a).1, h⟩ :
        testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ))) = F := by
      refine Subtype.ext ?_
      funext y
      show (∑ a, ψ a * F.1) y = F.1 y
      rw [Finset.sum_apply]
      simp only [Pi.mul_apply]
      by_cases hy : y ∈ N
      · rw [← Finset.sum_mul, hsum y hy, one_mul]
      · have hFy : F.1 y = 0 := by
          by_contra hne
          exact hy (hKN (mem_supportT_of_ne_zero hpts hne))
        simp [hFy]
    refine ⟨fun t => ⟨∑ a, (Gs a t).1, hs t⟩, fun t => ?_, hF ▸ hc⟩
    show ∑ a, (Gs a t).1 ∈ _
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨m', φ, hφ, heq⟩ := hFa a t
    show (Fa a t).1 ∈ _
    rw [heq]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hadm' := hadm a
    exact tensorProd_mem_smoothSepTensorSpan hpts hsmooth hspace D n O (H a) hadm'.isOpen_mem
      (hH a).2.2 (disjoint_of_admissibleWith hspace hadm') (φ k) (hφ k)
theorem distrib_eq_zero_of_vanishes (htest : SupportNormFacts.Claim) (D : Params)
    (n : ℕ+) (O : Set (Kind.euclidean.Pt D))
    (hΩ : IsOpenT D Kind.euclidean (p := n) (Euclid.injTuplesIn O (n : ℕ)))
    (hdens : ∀ F : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)),
      ∃ Fs : ℕ+ → testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)),
        (∀ t, (Fs t).1 ∈ smoothSepTensorSpan D n O) ∧ TendstoInTestFns Fs F)
    (T : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) → ℂ)
    (hT : IsDistrib T) (h0 : ∀ F, F.1 ∈ smoothSepTensorSpan D n O → T F = 0)
    (F : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ))) : T F = 0 := by
  obtain ⟨Fs, hspan, ⟨K, hK, hKΩ, hFK, hFsK⟩, hconv⟩ := hdens F
  obtain ⟨ν, C, hC⟩ := hT.2 K hK hKΩ
  obtain ⟨S, hS⟩ := ((htest D n).2.2.2 _ hΩ).1
  have hmem : ∀ x, x ∈ S ↔
      x ∈ testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) := by
    intro x
    rw [← hS]
    rfl
  have hsub : ∀ t, (Fs t).1 - F.1 ∈
      testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) := fun t =>
    (hmem _).1 (S.sub_mem ((hmem _).2 (Fs t).2) ((hmem _).2 F.2))
  have hW : ∀ t, supportT D Kind.euclidean ((Fs t).1 - F.1) ⊆ K := by
    intro t
    have e : (Fs t).1 - F.1 = (Fs t).1 + (-1 : ℂ) • F.1 := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [e]
    refine ((htest D n).1 (Fs t).1 ((-1 : ℂ) • F.1) (-1)).2.1.trans
      (Set.union_subset (hFsK t) ?_)
    exact ((htest D n).1 F.1 0 (-1)).2.2.1.trans hFK
  have hbound : ∀ t, ENNReal.ofReal ‖T F‖ ≤
      (C : ℝ≥0∞) * cNorm D Kind.euclidean ν ((Fs t).1 - F.1) := by
    intro t
    have h1 := hC ⟨_, hsub t⟩ (hW t)
    have h2 : T (Fs t) = T ⟨_, hsub t⟩ + T F := hT.1.1 ⟨_, hsub t⟩ F (Fs t) (by simp)
    rw [h0 _ (hspan t)] at h2
    have h3 : ‖T F‖ = ‖T ⟨_, hsub t⟩‖ := by
      rw [eq_neg_of_add_eq_zero_right h2.symm, norm_neg]
    rw [h3]
    exact h1
  have hl : Tendsto (fun t => (C : ℝ≥0∞) * cNorm D Kind.euclidean ν ((Fs t).1 - F.1))
      atTop (𝓝 0) := by
    have h4 := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) (hconv ν)
      (Or.inr ENNReal.coe_ne_top)
    simpa using h4
  have h5 : ENNReal.ofReal ‖T F‖ ≤ 0 := ge_of_tendsto' hl hbound
  have h6 : ‖T F‖ ≤ 0 := ENNReal.ofReal_eq_zero.1 (le_antisymm h5 zero_le)
  exact norm_le_zero_iff.1 h6
end Density
section TensorProducts
theorem injective_finAppend {X : Type*} {m m' : ℕ} {x : Fin m → X} {x' : Fin m' → X}
    (hi : Function.Injective x) (hi' : Function.Injective x') (hne : ∀ i j, x i ≠ x' j) :
    Function.Injective (Fin.append x x') := by apply _root_.YangMills.Construction.EuclideanFunctionals.VanishingSetHalving.finAppend_injective <;> assumption
theorem image2_appendPts_subset_pairwiseDistinct {D : Params} {n n' : ℕ+}
    {O O' : Set (Kind.euclidean.Pt D)}
    (hdisj : O ∩ O' = ∅) {K : Set (Fin (n : ℕ) → Fin 4 → ℝ)}
    {K' : Set (Fin (n' : ℕ) → Fin 4 → ℝ)} (hK : K ⊆ Euclid.injTuplesIn O (n : ℕ))
    (hK' : K' ⊆ Euclid.injTuplesIn O' (n' : ℕ)) :
    Set.image2 (Euclid.appendPts D (n := n) (n' := n')) K K' ⊆
      Kind.pairwiseDistinct D Kind.euclidean (n + n') := by
  rintro _ ⟨x, hx, x', hx', rfl⟩
  obtain ⟨hi, ho⟩ := mem_injTuplesIn_iff.1 (hK hx)
  obtain ⟨hi', ho'⟩ := mem_injTuplesIn_iff.1 (hK' hx')
  have hne : ∀ i j, x i ≠ x' j := by
    intro i j h
    have h1 : x i ∈ O ∩ O' := ⟨ho i, h ▸ ho' j⟩
    rw [hdisj] at h1
    exact h1
  exact injective_finAppend hi hi' hne
theorem tendsto_tensorMul (hrules : TensorRules.AllRules)
    (hspace : WellPosedness.WellPosed)
    (htest : SupportNormFacts.Claim) (D : Params) (n n' : ℕ+)
    (O O' : Set (Kind.euclidean.Pt D))
    (hΩ : IsOpenT D Kind.euclidean (p := n) (Euclid.injTuplesIn O (n : ℕ)))
    (hΩ' : IsOpenT D Kind.euclidean (p := n') (Euclid.injTuplesIn O' (n' : ℕ)))
    (hdisj : O ∩ O' = ∅)
    (Fs : ℕ+ → testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
    (F : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
    (Hs : ℕ+ → testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ)))
    (H : testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ)))
    (hF : TendstoInTestFns Fs F) (hH : TendstoInTestFns Hs H) :
    ∃ (hs : ∀ t, tensorMulti n.pos n'.pos (Fs t).1 (Hs t).1 ∈
          testFns D Kind.euclidean (Kind.pairwiseDistinct D Kind.euclidean (n + n')))
      (h : tensorMulti n.pos n'.pos F.1 H.1 ∈
          testFns D Kind.euclidean (Kind.pairwiseDistinct D Kind.euclidean (n + n'))),
      TendstoInTestFns (fun t => ⟨_, hs t⟩) ⟨_, h⟩ := by
  obtain ⟨⟨K, hK, hKΩ, hFK, hFsK⟩, hconvF⟩ := hF
  obtain ⟨⟨K', hK', hKΩ', hHK, hHsK⟩, hconvH⟩ := hH
  have hr := hrules D n n'
  have hsupp := hr.2.2.2.2.2.1
  have hder := hr.2.2.2.2.2.2.2.1
  have hnorm := hr.2.2.2.2.2.2.2.2.2
  have memb : ∀ (A : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
      (B : testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ))),
      Euclid.tensorMul D A.1 B.1 ∈
        testFns D Kind.euclidean (Kind.pairwiseDistinct D Kind.euclidean (n + n')) := by
    intro A B
    refine ⟨(hder A.1 B.1 A.2.1 B.2.1).1, ?_, ?_⟩
    · rw [hsupp]
      exact isCompactT_image2_appendPts hspace D A.2.2.1 B.2.2.1
    · rw [hsupp]
      exact image2_appendPts_subset_pairwiseDistinct hdisj A.2.2.2 B.2.2.2
  obtain ⟨S, hS⟩ := ((htest D n).2.2.2 _ hΩ).1
  obtain ⟨S', hS'⟩ := ((htest D n').2.2.2 _ hΩ').1
  have hmem : ∀ x, x ∈ S ↔
      x ∈ testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) := by
    intro x
    rw [← hS]
    rfl
  have hmem' : ∀ x, x ∈ S' ↔
      x ∈ testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ)) := by
    intro x
    rw [← hS']
    rfl
  have ha : ∀ t, (Fs t).1 - F.1 ∈
      testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)) := fun t =>
    (hmem _).1 (S.sub_mem ((hmem _).2 (Fs t).2) ((hmem _).2 F.2))
  have hb : ∀ t, (Hs t).1 - H.1 ∈
      testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ)) := fun t =>
    (hmem' _).1 (S'.sub_mem ((hmem' _).2 (Hs t).2) ((hmem' _).2 H.2))
  have hfin : ∀ (A : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
      (ν : ℕ), cNorm D Kind.euclidean ν A.1 < ⊤ :=
    fun A ν => (htest D n).2.1 A.1 A.2.1 A.2.2.1 ν
  have hfin' : ∀ (B : testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ)))
      (ν : ℕ), cNorm D Kind.euclidean ν B.1 < ⊤ :=
    fun B ν => (htest D n').2.1 B.1 B.2.1 B.2.2.1 ν
  have hprod : ∀ (A : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
      (B : testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ))) (ν : ℕ),
      cNorm D Kind.euclidean ν (Euclid.tensorMul D A.1 B.1) ≤
        cNorm D Kind.euclidean ν A.1 * cNorm D Kind.euclidean ν B.1 :=
    fun A B ν => hnorm A.1 B.1 ν A.2.1 B.2.1 (hfin A ν) (hfin' B ν)
  have hprodfin : ∀ (A : testFns D Kind.euclidean (Euclid.injTuplesIn O (n : ℕ)))
      (B : testFns D Kind.euclidean (Euclid.injTuplesIn O' (n' : ℕ))) (ν : ℕ),
      cNorm D Kind.euclidean ν (Euclid.tensorMul D A.1 B.1) < ⊤ :=
    fun A B ν => lt_of_le_of_lt (hprod A B ν) (ENNReal.mul_lt_top (hfin A ν) (hfin' B ν))
  have hbound : ∀ (ν : ℕ) (t : ℕ+), cNorm D Kind.euclidean ν
      (Euclid.tensorMul D (Fs t).1 (Hs t).1 - Euclid.tensorMul D F.1 H.1) ≤
      cNorm D Kind.euclidean ν ((Fs t).1 - F.1) *
          (cNorm D Kind.euclidean ν H.1 +
            cNorm D Kind.euclidean ν ((Hs t).1 - H.1)) +
        cNorm D Kind.euclidean ν F.1 *
          cNorm D Kind.euclidean ν ((Hs t).1 - H.1) := by
    intro ν t
    have heq : Euclid.tensorMul D (Fs t).1 (Hs t).1 - Euclid.tensorMul D F.1 H.1 =
        Euclid.tensorMul D ((Fs t).1 - F.1) (Hs t).1 +
          Euclid.tensorMul D F.1 ((Hs t).1 - H.1) := by
      funext z
      have hz : ∀ (A : Kind.euclidean.Tuple D n → ℂ)
          (B : Kind.euclidean.Tuple D n' → ℂ), Euclid.tensorMul D A B z =
            A (fun i => z (Fin.castAdd (n' : ℕ) i)) * B (fun j => z (Fin.natAdd (n : ℕ) j)) :=
        fun _ _ => rfl
      have hs : ∀ (A B : Kind.euclidean.Tuple D n → ℂ) w, (A - B) w = A w - B w :=
        fun _ _ _ => rfl
      have hs' : ∀ (A B : Kind.euclidean.Tuple D n' → ℂ) w, (A - B) w = A w - B w :=
        fun _ _ _ => rfl
      show Euclid.tensorMul D (Fs t).1 (Hs t).1 z - Euclid.tensorMul D F.1 H.1 z =
        Euclid.tensorMul D ((Fs t).1 - F.1) (Hs t).1 z +
          Euclid.tensorMul D F.1 ((Hs t).1 - H.1) z
      rw [hz, hz, hz, hz, hs, hs']
      ring
    have h1 := (htest D (n + n')).2.2.1 _ _ ν
      (memb ⟨_, ha t⟩ (Hs t)).1 (memb F ⟨_, hb t⟩).1
      (hprodfin ⟨_, ha t⟩ (Hs t) ν) (hprodfin F ⟨_, hb t⟩ ν)
    have h2 : cNorm D Kind.euclidean ν (Hs t).1 ≤
        cNorm D Kind.euclidean ν H.1 +
          cNorm D Kind.euclidean ν ((Hs t).1 - H.1) := by
      have h3 := (htest D n').2.2.1 H.1 ((Hs t).1 - H.1) ν H.2.1 (hb t).1 (hfin' H ν)
        (hfin' ⟨_, hb t⟩ ν)
      rwa [add_sub_cancel] at h3
    rw [heq]
    refine h1.trans (add_le_add ?_ (hprod F ⟨_, hb t⟩ ν))
    exact (hprod ⟨_, ha t⟩ (Hs t) ν).trans (mul_le_mul_right h2 _)
  refine ⟨fun t => memb (Fs t) (Hs t), memb F H,
    ⟨Set.image2 (Euclid.appendPts D (n := n) (n' := n')) K K',
      isCompactT_image2_appendPts hspace D hK hK',
      image2_appendPts_subset_pairwiseDistinct hdisj hKΩ hKΩ', ?_,
      fun t => ?_⟩, fun ν => ?_⟩
  · have h1 := hsupp F.1 H.1
    show supportT D Kind.euclidean (Euclid.tensorMul D F.1 H.1) ⊆ _
    rw [h1]
    exact Set.image2_subset hFK hHK
  · have h1 := hsupp (Fs t).1 (Hs t).1
    show supportT D Kind.euclidean (Euclid.tensorMul D (Fs t).1 (Hs t).1) ⊆ _
    rw [h1]
    exact Set.image2_subset (hFsK t) (hHsK t)
  · have hA := hconvF ν
    have hB := hconvH ν
    have hsum : Tendsto (fun t => cNorm D Kind.euclidean ν H.1 +
        cNorm D Kind.euclidean ν ((Hs t).1 - H.1)) atTop
        (𝓝 (cNorm D Kind.euclidean ν H.1 + 0)) := tendsto_const_nhds.add hB
    have hm := ENNReal.Tendsto.mul hA
      (Or.inr (by simpa using (hfin' H ν).ne)) hsum (Or.inr ENNReal.zero_ne_top)
    have hm2 := ENNReal.Tendsto.const_mul (a := cNorm D Kind.euclidean ν F.1) hB
      (Or.inr (hfin F ν).ne)
    have htot := hm.add hm2
    simp only [zero_mul, mul_zero, add_zero] at htot
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htot
      (fun _ => zero_le) (hbound ν)
end TensorProducts
theorem densityStatement_holds (hpts : TupleFacts.AllFacts)
    (hdistinct : Kind.AdmissibleProductFacts)
    (hdense : Kind.TensorSpanDenseOnBoxes)
    (hsmooth : Kind.SmoothIffSmoothAsTuple)
    (hspace : WellPosedness.WellPosed)
    (hrules : TensorRules.AllRules)
    (hsupport : Euclid.SmoothSepTensorFacts)
    (htest : SupportNormFacts.Claim)
    (hunity : SmoothFinitePartitionOfUnity) : DensityStatement := by
  intro D n O hO
  have hΩ := isOpenT_injTuplesIn hpts hdistinct D n hO
  have hdens := exists_seq_tendsto hpts hdistinct hdense hsmooth hspace htest hunity D n O hO hΩ
  refine ⟨smoothSepTensorSpan_subset hsupport htest D n O hO hΩ, hdens,
    fun T hT h0 F => distrib_eq_zero_of_vanishes htest D n O hΩ hdens T hT h0 F, ?_⟩
  intro n' O' hO' hdisj Fs F Hs H hF hH
  exact tendsto_tensorMul hrules hspace htest D n n' O O' hΩ
    (isOpenT_injTuplesIn hpts hdistinct D n' hO') hdisj Fs F Hs H hF hH
end YangMills.Construction.PeriodicSpace.DenseTensorSpan.SpanArgument
