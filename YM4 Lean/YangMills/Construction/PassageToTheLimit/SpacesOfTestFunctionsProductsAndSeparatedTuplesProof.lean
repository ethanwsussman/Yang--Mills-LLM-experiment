import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.MetricNotions YangMills.Construction.TestFunctions YangMills.Construction.FamilyTopology
noncomputable section
namespace YangMills.Construction.LimitSpaces.Ambient.SeparatedTuples
section Distance
variable {X : Type*} {d : X → X → ℝ}
@[reducible] def metricSpaceOfMetricFunction (hd : IsMetricFunction d) : MetricSpace X where
  dist := d
  dist_self x := (hd.eq_zero_iff x x).mpr rfl
  dist_comm := hd.symm
  dist_triangle := hd.triangle
  eq_of_dist_eq_zero {x y} h := (hd.eq_zero_iff x y).mp h
theorem isOpenWrt_iff_isOpen (hd : IsMetricFunction d) (U : Set X) :
    IsOpenWrt d U ↔
      @IsOpen X (metricSpaceOfMetricFunction hd).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U := by
  let _ := metricSpaceOfMetricFunction hd
  rw [Metric.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨r, hr, hU⟩ := h x hx
    refine ⟨r, hr, fun y hy => hU y ?_⟩
    have hy' : d y x < r := hy
    rwa [hd.symm]
  · intro h x hx
    obtain ⟨r, hr, hU⟩ := h x hx
    refine ⟨r, hr, fun y hy => hU ?_⟩
    show d y x < r
    rwa [hd.symm]
theorem closureWrt_eq_closure (hd : IsMetricFunction d) (Z : Set X) :
    closureWrt d Z =
      @closure X (metricSpaceOfMetricFunction hd).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace Z := by
  let _ := metricSpaceOfMetricFunction hd
  ext x
  rw [Metric.mem_closure_iff]
  exact Iff.rfl
theorem isCompactWrt_iff_isCompact (hd : IsMetricFunction d) (Z : Set X) :
    IsCompactWrt d Z ↔
      @IsCompact X (metricSpaceOfMetricFunction hd).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace Z := by
  let _ := metricSpaceOfMetricFunction hd
  constructor
  · intro h
    rw [isCompact_iff_finite_subcover]
    intro ι U hU hcov
    obtain ⟨𝒰', hsub, hfin, hcov'⟩ := h (range U)
      (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_iff_isOpen hd _).mpr (hU i))
      (by rwa [sUnion_range])
    classical
    choose g hg using fun V : 𝒰' => hsub V.2
    have := hfin.fintype
    refine ⟨Finset.univ.image g, fun x hx => ?_⟩
    obtain ⟨V, hV, hxV⟩ := hcov' hx
    refine mem_iUnion₂.mpr ⟨g ⟨V, hV⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [hg ⟨V, hV⟩]
    exact hxV
  · intro h 𝒰 hU hcov
    obtain ⟨t, ht⟩ := h.elim_finite_subcover (fun V : 𝒰 => (V : Set X))
      (fun V => (isOpenWrt_iff_isOpen hd _).mp (hU V V.2)) (by rwa [sUnion_eq_iUnion] at hcov)
    refine ⟨Subtype.val '' (t : Set 𝒰), ?_, t.finite_toSet.image _, fun x hx => ?_⟩
    · rintro _ ⟨V, -, rfl⟩
      exact V.2
    · obtain ⟨V, hV, hxV⟩ := mem_iUnion₂.mp (ht hx)
      exact ⟨V, ⟨V, hV, rfl⟩, hxV⟩
theorem closureWrt_linComb_subset (hd : IsMetricFunction d) (f g : X → ℝ) (a b : ℝ) :
    closureWrt d {x | a * f x + b * g x ≠ 0} ⊆
      closureWrt d {x | f x ≠ 0} ∪ closureWrt d {x | g x ≠ 0} := by
  let _ := metricSpaceOfMetricFunction hd
  simp only [closureWrt_eq_closure hd]
  rw [← closure_union]
  refine closure_mono fun x hx => ?_
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
  exact hx (by simp [hn.1, hn.2])
theorem linComb_compactSupport (hd : IsMetricFunction d) {f g : X → ℝ} (a b : ℝ) {A : Set X}
    (hf : IsCompactWrt d (closureWrt d {x | f x ≠ 0})) (hfA : closureWrt d {x | f x ≠ 0} ⊆ A)
    (hg : IsCompactWrt d (closureWrt d {x | g x ≠ 0})) (hgA : closureWrt d {x | g x ≠ 0} ⊆ A) :
    IsCompactWrt d (closureWrt d {x | a * f x + b * g x ≠ 0}) ∧
      closureWrt d {x | a * f x + b * g x ≠ 0} ⊆ A := by
  refine ⟨?_, (closureWrt_linComb_subset hd f g a b).trans (union_subset hfA hgA)⟩
  let _ := metricSpaceOfMetricFunction hd
  rw [isCompactWrt_iff_isCompact hd] at hf hg ⊢
  refine (hf.union hg).of_isClosed_subset ?_ (closureWrt_linComb_subset hd f g a b)
  rw [closureWrt_eq_closure hd]
  exact isClosed_closure
theorem zero_compactSupport (hd : IsMetricFunction d) (A : Set X) :
    IsCompactWrt d (closureWrt d {x | (0 : X → ℝ) x ≠ 0}) ∧
      closureWrt d {x | (0 : X → ℝ) x ≠ 0} ⊆ A := by
  have h : closureWrt d {x | (0 : X → ℝ) x ≠ 0} = ∅ := by
    let _ := metricSpaceOfMetricFunction hd
    rw [closureWrt_eq_closure hd]
    simp
  rw [h]
  refine ⟨?_, empty_subset _⟩
  let _ := metricSpaceOfMetricFunction hd
  rw [isCompactWrt_iff_isCompact hd]
  exact isCompact_empty
theorem isCompactWrt_iUnion (hd : IsMetricFunction d) {ι : Type*} [Finite ι] {S : ι → Set X}
    (h : ∀ i, IsCompactWrt d (S i)) : IsCompactWrt d (⋃ i, S i) := by
  let _ := metricSpaceOfMetricFunction hd
  rw [isCompactWrt_iff_isCompact hd]
  exact isCompact_iUnion fun i => (isCompactWrt_iff_isCompact hd _).mp (h i)
theorem isContinuousWrt_of_isLipschitzFor {f : X → ℝ} (hf : IsLipschitzFor d f) :
    IsContinuousWrt d dist f := by
  obtain ⟨C, hC, h⟩ := hf
  intro x ε hε
  refine ⟨ε / (C + 1), by positivity, fun y hy => ?_⟩
  have hCpos : 0 < C + 1 := by linarith
  have h1 : ‖f x - f y‖ ≤ C * d x y := h x y
  have h2 : (C + 1) * d x y < ε := by
    rw [lt_div_iff₀ hCpos] at hy
    linarith
  have h3 : 0 ≤ ‖f x - f y‖ := norm_nonneg _
  rw [Real.dist_eq]
  rw [Real.norm_eq_abs] at h1 h3
  nlinarith
theorem isBoundedFun_of_compactSupport (hd : IsMetricFunction d) {f : X → ℝ}
    (hf : IsContinuousWrt d dist f) (hK : IsCompactWrt d (closureWrt d {x | f x ≠ 0})) :
    IsBoundedFun f := by
  let _ := metricSpaceOfMetricFunction hd
  have hc : Continuous f := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨δ, hδ, h⟩ := hf x ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hy' : d y x < δ := hy
    rw [dist_comm]
    exact h y (by rwa [hd.symm])
  obtain ⟨C, hC⟩ :=
    ((isCompactWrt_iff_isCompact hd _).mp hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ closureWrt d {x | f x ≠ 0}
  · exact (hC x hx).trans (le_max_left _ _)
  · have h0 : f x = 0 := by
      by_contra hne
      refine hx fun r hr => ⟨x, hne, ?_⟩
      have : d x x = 0 := (hd.eq_zero_iff x x).mpr rfl
      rwa [this]
    simp [h0]
end Distance
section Seminorms
variable {X : Type*}
theorem uniformNorm_nonneg (f : X → ℝ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_le_uniformNorm {f : X → ℝ} (hf : IsBoundedFun f) (x : X) : ‖f x‖ ≤ uniformNorm f := by apply _root_.YangMills.SharedProofs.p10108 <;> assumption
theorem uniformNorm_smul (a : ℝ) (f : X → ℝ) : uniformNorm (a • f) = |a| * uniformNorm f := by
  unfold uniformNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg a)]
  simp
theorem uniformNorm_add_le {f g : X → ℝ} (hf : IsBoundedFun f)
    (hg : IsBoundedFun g) : uniformNorm (f + g) ≤ uniformNorm f + uniformNorm g :=
  Real.iSup_le
    (fun x => (norm_add_le _ _).trans (add_le_add (norm_le_uniformNorm hf x) (norm_le_uniformNorm hg x)))
    (add_nonneg (uniformNorm_nonneg f) (uniformNorm_nonneg g))
theorem eq_zero_of_uniformNorm_nonpos {f : X → ℝ} (hf : IsBoundedFun f)
    (h : uniformNorm f ≤ 0) : f = 0 := by
  funext x
  have := (norm_le_uniformNorm hf x).trans h
  simpa using this
variable {d : X → X → ℝ}
theorem bestLipschitzConstant_nonneg (f : X → ℝ) : 0 ≤ bestLipschitzConstant d f :=
  Real.sInf_nonneg fun _ hC => hC.1
theorem norm_sub_le_bestLipschitzConstant_mul (hd : IsMetricFunction d) {f : X → ℝ}
    (hf : IsLipschitzFor d f) (x y : X) :
    ‖f x - f y‖ ≤ bestLipschitzConstant d f * d x y := by
  by_cases h0 : d x y = 0
  · have hxy : x = y := (hd.eq_zero_iff x y).mp h0
    rw [h0, hxy]
    simp
  · have hpos : 0 < d x y := lt_of_le_of_ne (hd.nonneg x y) (Ne.symm h0)
    rw [← div_le_iff₀ hpos]
    obtain ⟨C₀, hC₀, hC₀'⟩ := hf
    refine le_csInf ⟨C₀, hC₀, hC₀'⟩ fun C hC => ?_
    rw [div_le_iff₀ hpos]
    exact hC.2 x y
theorem bestLipschitzConstant_smul_le (hd : IsMetricFunction d) {f : X → ℝ}
    (hf : IsLipschitzFor d f) (a : ℝ) :
    bestLipschitzConstant d (a • f) ≤ |a| * bestLipschitzConstant d f := by
  refine csInf_le ⟨0, fun _ hC => hC.1⟩
    ⟨mul_nonneg (abs_nonneg a) (bestLipschitzConstant_nonneg f), fun x y => ?_⟩
  have h : (a • f) x - (a • f) y = a * (f x - f y) := by simp [mul_sub]
  rw [h, norm_mul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_sub_le_bestLipschitzConstant_mul hd hf x y) (abs_nonneg a)
theorem isLipschitzFor_smul {f : X → ℝ} (hf : IsLipschitzFor d f) (a : ℝ) :
    IsLipschitzFor d (a • f) := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, fun x y => ?_⟩
  have h' : (a • f) x - (a • f) y = a * (f x - f y) := by simp [mul_sub]
  rw [h', norm_mul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x y) (abs_nonneg a)
theorem bestLipschitzConstant_smul (hd : IsMetricFunction d) {f : X → ℝ}
    (hf : IsLipschitzFor d f) (a : ℝ) :
    bestLipschitzConstant d (a • f) = |a| * bestLipschitzConstant d f := by
  refine le_antisymm (bestLipschitzConstant_smul_le hd hf a) ?_
  by_cases ha : a = 0
  · simpa [ha] using bestLipschitzConstant_nonneg (d := d) ((0 : ℝ) • f)
  · have h := bestLipschitzConstant_smul_le hd (isLipschitzFor_smul hf a) a⁻¹
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv] at h
    have hpos : 0 < |a| := abs_pos.mpr ha
    rw [inv_mul_eq_div, le_div_iff₀ hpos] at h
    linarith
theorem bestLipschitzConstant_add_le (hd : IsMetricFunction d) {f g : X → ℝ}
    (hf : IsLipschitzFor d f) (hg : IsLipschitzFor d g) :
    bestLipschitzConstant d (f + g) ≤ bestLipschitzConstant d f + bestLipschitzConstant d g := by
  refine csInf_le ⟨0, fun _ hC => hC.1⟩
    ⟨add_nonneg (bestLipschitzConstant_nonneg f) (bestLipschitzConstant_nonneg g), fun x y => ?_⟩
  have h : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by simp; ring
  rw [h, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_sub_le_bestLipschitzConstant_mul hd hf x y)
    (norm_sub_le_bestLipschitzConstant_mul hd hg x y))
theorem isNormOn_max_uniform_lipschitz (hd : IsMetricFunction d) {c : ℝ} (hc : 0 < c)
    {V : Set (X → ℝ)} (hV : ∀ f ∈ V, IsBoundedFun f ∧ IsLipschitzFor d f) :
    Ambient.IsNormOn V fun f => max (uniformNorm f) (c * bestLipschitzConstant d f) := by
  refine ⟨fun f _ => le_max_of_le_left (uniformNorm_nonneg f), fun f hf h => ?_, fun a f hf => ?_,
    fun f hf g hg => ?_⟩
  · exact eq_zero_of_uniformNorm_nonpos (hV f hf).1 (h ▸ le_max_left _ _)
  · show max (uniformNorm (a • f)) (c * bestLipschitzConstant d (a • f)) =
      |a| * max (uniformNorm f) (c * bestLipschitzConstant d f)
    rw [uniformNorm_smul, bestLipschitzConstant_smul hd (hV f hf).2,
      mul_max_of_nonneg _ _ (abs_nonneg a)]
    congr 1
    ring
  · show max (uniformNorm (f + g)) (c * bestLipschitzConstant d (f + g)) ≤ _
    refine max_le ((uniformNorm_add_le (hV f hf).1 (hV g hg).1).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
    refine (mul_le_mul_of_nonneg_left (bestLipschitzConstant_add_le hd (hV f hf).2 (hV g hg).2)
      hc.le).trans ?_
    rw [mul_add]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
theorem isNormOn_max_uniform_partials {ι : Type*} [Finite ι] {V : Set (X → ℝ)}
    {P : ι → (X → ℝ) → X → ℝ} (hV : ∀ f ∈ V, IsBoundedFun f)
    (hP : ∀ f ∈ V, ∀ μ, IsBoundedFun (P μ f))
    (hsmul : ∀ f ∈ V, ∀ (a : ℝ) (μ : ι), P μ (a • f) = a • P μ f)
    (hadd : ∀ f ∈ V, ∀ g ∈ V, ∀ μ : ι, P μ (f + g) = P μ f + P μ g) :
    Ambient.IsNormOn V fun f => max (uniformNorm f) (⨆ μ, uniformNorm (P μ f)) := by
  refine ⟨fun f _ => le_max_of_le_left (uniformNorm_nonneg f), fun f hf h => ?_, fun a f hf => ?_,
    fun f hf g hg => ?_⟩
  · exact eq_zero_of_uniformNorm_nonpos (hV f hf) (h ▸ le_max_left _ _)
  · show max (uniformNorm (a • f)) (⨆ μ, uniformNorm (P μ (a • f))) =
      |a| * max (uniformNorm f) (⨆ μ, uniformNorm (P μ f))
    simp only [hsmul f hf, uniformNorm_smul]
    rw [← Real.mul_iSup_of_nonneg (abs_nonneg a), mul_max_of_nonneg _ _ (abs_nonneg a)]
  · show max (uniformNorm (f + g)) (⨆ μ, uniformNorm (P μ (f + g))) ≤ _
    refine max_le ((uniformNorm_add_le (hV f hf) (hV g hg)).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
    refine Real.iSup_le (fun μ => ?_) (add_nonneg (le_max_of_le_left (uniformNorm_nonneg f))
      (le_max_of_le_left (uniformNorm_nonneg g)))
    rw [hadd f hf g hg]
    refine (uniformNorm_add_le (hP f hf μ) (hP g hg μ)).trans (add_le_add ?_ ?_)
    · exact (le_ciSup (f := fun μ => uniformNorm (P μ f)) (Set.finite_range _).bddAbove μ).trans
        (le_max_right _ _)
    · exact (le_ciSup (f := fun μ => uniformNorm (P μ g)) (Set.finite_range _).bddAbove μ).trans
        (le_max_right _ _)
theorem isFunctionSubspace_of_linComb {V : Set (X → ℝ)} (h0 : (0 : X → ℝ) ∈ V)
    (hc : ∀ f ∈ V, ∀ g ∈ V, ∀ a b : ℝ, (fun x => a * f x + b * g x) ∈ V) :
    Ambient.IsFunctionSubspace V := by
  refine ⟨{ carrier := V, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro f g hf hg
    have := hc f hf g hg 1 1
    have he : (fun x => 1 * f x + 1 * g x) = f + g := by
      funext x
      simp
    rwa [he] at this
  · intro a f hf
    have := hc f hf 0 h0 a 0
    have he : (fun x => a * f x + 0 * (0 : X → ℝ) x) = a • f := by
      funext x
      simp
    rwa [he] at this
end Seminorms
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
section OnTheSpace
variable (s : Conventions.StandingParameters) (E : Ambient)
theorem isLip_iff (f : E.Carrier s → ℝ) :
    E.IsLip s f ↔ IsLipschitzFor (E.pointDist s) f := by
  cases E <;> exact Iff.rfl
theorem normSharp_eq (M : SharpParameter) (f : E.Carrier s → ℝ) :
    E.normSharp s M f =
      max (uniformNorm f) ((40 * (M : ℝ)) * bestLipschitzConstant (E.pointDist s) f) := by
  cases E <;> rfl
variable {s E}
theorem linComb_mem_lipWithin (hd : IsMetricFunction (E.pointDist s)) {A : Set (E.Carrier s)}
    {f g : E.Carrier s → ℝ} (hf : f ∈ E.lipWithin s A)
    (hg : g ∈ E.lipWithin s A) (a b : ℝ) :
    (fun x => a * f x + b * g x) ∈ E.lipWithin s A := by
  refine ⟨?_, linComb_compactSupport hd a b hf.2.1 hf.2.2 hg.2.1 hg.2.2⟩
  obtain ⟨C, hC, h⟩ := (isLip_iff s E f).mp hf.1
  obtain ⟨C', hC', h'⟩ := (isLip_iff s E g).mp hg.1
  refine (isLip_iff s E _).mpr ⟨|a| * C + |b| * C', by positivity, fun x y => ?_⟩
  have he : a * f x + b * g x - (a * f y + b * g y) = a * (f x - f y) + b * (g x - g y) := by ring
  rw [he, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h x y) (abs_nonneg a)
  · rw [norm_mul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h' x y) (abs_nonneg b)
theorem zero_mem_lipWithin (hd : IsMetricFunction (E.pointDist s)) (A : Set (E.Carrier s)) :
    (0 : E.Carrier s → ℝ) ∈ E.lipWithin s A :=
  ⟨(isLip_iff s E _).mpr ⟨0, le_rfl, fun x y => by simp⟩, zero_compactSupport hd A⟩
theorem c1Within_subset_lipWithin (h : AmbientMetric.C1CompactFacts s E)
    (A : Set (E.Carrier s)) : E.c1Within s A ⊆ E.lipWithin s A := by
  intro f hf
  obtain ⟨-, -, -, -, -, -, hl, -⟩ := h f hf.1
  exact ⟨hl, hf.2⟩
theorem lipWithin_mono {A B : Set (E.Carrier s)} (hAB : A ⊆ B) {f : E.Carrier s → ℝ}
    (hf : f ∈ E.lipWithin s A) : f ∈ E.lipWithin s B :=
  ⟨hf.1, hf.2.1, hf.2.2.trans hAB⟩
theorem disjoint_of_positivelySeparated (hd : IsMetricFunction (E.pointDist s))
    {S S' : Set (E.Carrier s)} (h : E.PositivelySeparated s S S') : Disjoint S S' := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h0 : E.infSetDist s S S' ≤ 0 := by
    refine (iInf₂_le x hx).trans ((iInf₂_le x hx').trans ?_)
    rw [(hd.eq_zero_iff x x).mpr rfl]
    simp
  exact absurd h (not_lt.mpr h0)
theorem closedSupports_of_sepLipTuple (hsep : ∀ S S' : Set (E.Carrier s), E.IsCompactSubset s S →
    E.IsCompactSubset s S' → Disjoint S S' → E.PositivelySeparated s S S')
    {n : ℕ} {D : Set (E.Carrier s)} {f : Fin n → E.Carrier s → ℝ}
    (hf : E.IsSepLipTuple s D f) :
    (∀ i, E.closedSupport s (f i) ⊆ D) ∧
      (Pairwise fun i j =>
        E.PositivelySeparated s (E.closedSupport s (f i)) (E.closedSupport s (f j))) ∧
      ∀ i, f i ∈ E.lipWithin s (E.closedSupport s (f i)) :=
  ⟨fun i => (hf.1 i).2.2, fun i j hij => hsep _ _ (hf.1 i).2.1 (hf.1 j).2.1 (hf.2 hij),
    fun i => ⟨(hf.1 i).1, (hf.1 i).2.1, subset_rfl⟩⟩
theorem isSepLipTuple_of_isSepTuple {k : TestKind} {n : ℕ} {D : Set (E.Carrier s)}
    {f : Fin n → E.Carrier s → ℝ} (h : E.IsSepTuple s k D f) :
    E.IsSepLipTuple s D f := by
  cases k with
  | lip => exact h
  | cOne => exact h.1
theorem mem_testWithin_closedSupport {k : TestKind} {n : ℕ} {D : Set (E.Carrier s)}
    {f : Fin n → E.Carrier s → ℝ} (h : E.IsSepTuple s k D f) (i : Fin n) :
    f i ∈ E.testWithin s k (E.closedSupport s (f i)) := by
  have hl := isSepLipTuple_of_isSepTuple h
  cases k with
  | lip => exact ⟨(hl.1 i).1, (hl.1 i).2.1, subset_rfl⟩
  | cOne => exact ⟨h.2 i, (hl.1 i).2.1, subset_rfl⟩
end OnTheSpace
theorem testSpacesNormed_holds
    (s : Conventions.StandingParameters) (E : Ambient)
    (hd : IsMetricFunction (E.pointDist s))
    (hg : AmbientMetric.C1CompactFacts s E)
    (hc : AmbientMetric.LinearCombinationFacts s E)
    (M : SharpParameter) (A : Set (E.Carrier s)) : E.TestSpacesNormed s M A := by
  have hbd : ∀ f ∈ E.lipWithin s A,
      E.IsContinuousInto s f ∧ IsBoundedFun f := fun f hf =>
    have hcont := isContinuousWrt_of_isLipschitzFor ((isLip_iff s E f).mp hf.1)
    ⟨hcont, isBoundedFun_of_compactSupport hd hcont hf.2.1⟩
  have hsub := c1Within_subset_lipWithin hg A
  have hpos : (0 : ℝ) < 40 * (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := M.2
    linarith
  have hcomb : ∀ f ∈ E.c1Within s A, ∀ g ∈ E.c1Within s A, ∀ a b : ℝ,
      (fun x => a * f x + b * g x) ∈ E.c1Within s A := fun f hf g hg' a b =>
    ⟨(hc f hf.1 g hg'.1 a b f hf.1.1 |>.1),
      (linComb_mem_lipWithin hd (hsub hf) (hsub hg') a b).2⟩
  have hgrad : ∀ f ∈ E.c1Within s A, ∀ g ∈ E.c1Within s A, ∀ (a b : ℝ) (μ : Fin 4),
      E.partialDeriv s μ (fun x => a * f x + b * g x) =
        a • E.partialDeriv s μ f + b • E.partialDeriv s μ g := by
    intro f hf g hg' a b μ
    funext x
    have h := (hc f hf.1 g hg'.1 a b f hf.1.1).2.1
    simp only [Ambient.partialDeriv, h]
    rfl
  refine ⟨isFunctionSubspace_of_linComb (zero_mem_lipWithin hd A)
      fun f hf g hg' a b => linComb_mem_lipWithin hd hf hg' a b,
    hbd, ?_, hsub, ?_, ?_⟩
  · refine isFunctionSubspace_of_linComb ?_ hcomb
    exact ⟨⟨(contDiff_const : ContDiff ℝ 1 fun _ : Fin 4 → ℝ => (0 : ℝ)),
      (zero_compactSupport hd A).1⟩, zero_compactSupport hd A⟩
  · have h := isNormOn_max_uniform_lipschitz (V := E.lipWithin s A) hd hpos fun f hf =>
      ⟨(hbd f hf).2, (isLip_iff s E f).mp hf.1⟩
    have he : E.normSharp s M =
        fun f => max (uniformNorm f) ((40 * (M : ℝ)) * bestLipschitzConstant (E.pointDist s) f) :=
      funext (normSharp_eq s E M)
    rw [he]
    exact h
  · have hfun : ∀ f : E.Carrier s → ℝ, ∀ a : ℝ, (a • f) = fun x => a * f x + 0 * f x := by
      intro f a
      funext x
      simp
    have hadd : ∀ f g : E.Carrier s → ℝ, f + g = fun x => 1 * f x + 1 * g x := by
      intro f g
      funext x
      simp
    exact isNormOn_max_uniform_partials (P := fun μ => E.partialDeriv s μ)
      (fun f hf => (hbd f (hsub hf)).2)
      (fun f hf μ => by
        obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := hg f hf.1
        exact ⟨C, fun x => (abs_apply_le_euclidNormVec _ μ).trans (hC x)⟩)
      (fun f hf a μ => by
        rw [hfun f a, hgrad f hf f hf a 0 μ]
        simp)
      (fun f hf g hg' μ => by
        rw [hadd f g, hgrad f hf g hg' 1 1 μ]
        simp)
theorem productsSepTuples_holds (s : Conventions.StandingParameters) (E : Ambient)
    (hd : IsMetricFunction (E.pointDist s))
    (hg : AmbientMetric.C1CompactFacts s E)
    (hsep : ∀ S S' : Set (E.Carrier s), E.IsCompactSubset s S → E.IsCompactSubset s S' →
      Disjoint S S' → E.PositivelySeparated s S S')
    (D : Set (E.Carrier s)) (n : ℕ) : E.ProductsSepTuples s D n := by
  have hl : ∀ A : Fin n → Set (E.Carrier s), (∀ i, A i ⊆ D) →
      (Pairwise fun i j => E.PositivelySeparated s (A i) (A j)) →
      ∀ f : Fin n → E.Carrier s → ℝ, (∀ i, f i ∈ E.lipWithin s (A i)) →
        E.IsSepLipTuple s D f := fun A hA hP f hf =>
    ⟨fun i => lipWithin_mono (hA i) (hf i), fun i j hij =>
      (disjoint_of_positivelySeparated hd (hP hij)).mono (hf i).2.2 (hf j).2.2⟩
  exact ⟨fun A hA hP => ⟨hl A hA hP, fun f hf =>
      ⟨hl A hA hP f fun i => c1Within_subset_lipWithin hg _ (hf i), fun i => (hf i).1⟩⟩,
    fun f hf => closedSupports_of_sepLipTuple hsep hf,
    fun f hf i => ⟨hf.2 i, (hf.1.1 i).2.1, subset_rfl⟩⟩
theorem sepTuplesStable_holds (s : Conventions.StandingParameters) (E : Ambient)
    (hd : IsMetricFunction (E.pointDist s)) (D : Set (E.Carrier s)) : E.SepTuplesStable s D := by
  refine ⟨fun m f hf => hf.1, ?_, fun k m f hf =>
    ⟨fun J => Ambient.IsSepTuple.comp_inj hf (J.orderEmbOfFin rfl).injective,
      fun ς => Ambient.IsSepTuple.comp_inj hf ς.injective⟩, ?_⟩
  · intro k m D' f hD hf
    have hl : ∀ {g : Fin m → E.Carrier s → ℝ}, E.IsSepLipTuple s D' g →
        E.IsSepLipTuple s D g :=
      fun hg => ⟨fun i => lipWithin_mono hD (hg.1 i), hg.2⟩
    cases k with
    | lip => exact hl hf
    | cOne => exact ⟨hl hf.1, hf.2⟩
  · intro r length X hX
    exact isCompactWrt_iUnion hd fun p => isCompactWrt_iUnion hd fun i => ((hX p).1 i).2.1
theorem multilinearRestrictVanish_holds (s : Conventions.StandingParameters) (E : Ambient)
    (hg : AmbientMetric.C1CompactFacts s E)
    (hsep : ∀ S S' : Set (E.Carrier s), E.IsCompactSubset s S → E.IsCompactSubset s S' →
      Disjoint S S' → E.PositivelySeparated s S S')
    (D : Set (E.Carrier s)) (n : ℕ) : E.MultilinearRestrictVanish s D n := by
  refine ⟨fun D' h Ψ hΨ A hA hP i a b X Y Z hX hY hZ hYX hZX hi => ?_,
    fun k Ψ hΨ X i hi => ?_⟩
  · exact hΨ A (fun j => (hA j).trans h) hP i a b
      ⟨X.1, Ambient.IsSepC1Tuple.isSepLipTuple_of_subset h X.2⟩
      ⟨Y.1, Ambient.IsSepC1Tuple.isSepLipTuple_of_subset h Y.2⟩
      ⟨Z.1, Ambient.IsSepC1Tuple.isSepLipTuple_of_subset h Z.2⟩
      (fun j => c1Within_subset_lipWithin hg _ (hX j))
      (fun j => c1Within_subset_lipWithin hg _ (hY j))
      (fun j => c1Within_subset_lipWithin hg _ (hZ j)) hYX hZX hi
  · obtain ⟨hs, hp, -⟩ := closedSupports_of_sepLipTuple hsep (isSepLipTuple_of_isSepTuple X.2)
    have hmem := mem_testWithin_closedSupport X.2
    have h := hΨ (fun j => E.closedSupport s (X.1 j)) hs hp i 0 0 X X X hmem hmem hmem
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hi]; simp)
    simpa using h
theorem testSpacesAndSepTuples_holds (h : AmbientMetric.Claim) : Ambient.testSpacesAndSepTuples := by
  intro s E M A D n _
  obtain ⟨h1, h2, h3, h4, -⟩ := h s E
  obtain ⟨-, hd, -⟩ := h1
  obtain ⟨hsep, -⟩ := h2
  exact ⟨testSpacesNormed_holds s E hd h3 h4 M A, productsSepTuples_holds s E hd h3 hsep D n,
    sepTuplesStable_holds s E hd D, multilinearRestrictVanish_holds s E h3 hsep D n⟩
end YangMills.Construction.LimitSpaces.Ambient.SeparatedTuples
end
