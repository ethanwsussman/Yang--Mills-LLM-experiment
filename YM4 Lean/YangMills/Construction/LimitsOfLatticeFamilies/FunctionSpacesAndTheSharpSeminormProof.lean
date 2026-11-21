import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLift
import YangMills.Construction.LimitsOfLatticeFamilies.FunctionSpacesAndTheSharpSeminorm
import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuplesProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.MetricNotions YangMills.Construction.TestFunctions
noncomputable section
namespace YangMills.Construction.LatticeLimits.SharpSeminorm
section Distance
variable {X : Type*} {d : X → X → ℝ}
structure IsDistanceFun (d : X → X → ℝ) : Prop where
  eq_zero_iff : ∀ x y, d x y = 0 ↔ x = y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z
  nonneg : ∀ x y, 0 ≤ d x y
@[reducible] def metricSpaceOf (hd : IsDistanceFun d) : MetricSpace X where
  dist := d
  dist_self x := (hd.eq_zero_iff x x).mpr rfl
  dist_comm := hd.symm
  dist_triangle := hd.triangle
  eq_of_dist_eq_zero {x y} h := (hd.eq_zero_iff x y).mp h
theorem isOpenWrt_iff_isOpen (hd : IsDistanceFun d) (U : Set X) :
    IsOpenWrt d U ↔
      @IsOpen X (metricSpaceOf hd).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U := by
  let _ := metricSpaceOf hd
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
theorem closureWrt_eq_closure (hd : IsDistanceFun d) (Z : Set X) :
    closureWrt d Z =
      @closure X (metricSpaceOf hd).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace Z := by
  let _ := metricSpaceOf hd
  ext x
  rw [Metric.mem_closure_iff]
  exact Iff.rfl
theorem isCompactWrt_iff_isCompact (hd : IsDistanceFun d) (Z : Set X) :
    IsCompactWrt d Z ↔
      @IsCompact X (metricSpaceOf hd).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace Z := by
  let _ := metricSpaceOf hd
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
theorem closureWrt_support_lincomb_subset (hd : IsDistanceFun d) (f g : X → ℝ) (a b : ℝ) :
    closureWrt d {x | (a • f + b • g) x ≠ 0} ⊆
      closureWrt d {x | f x ≠ 0} ∪ closureWrt d {x | g x ≠ 0} := by
  let _ := metricSpaceOf hd
  simp only [closureWrt_eq_closure hd]
  rw [← closure_union]
  refine closure_mono fun x hx => ?_
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
  exact hx (by simp [hn.1, hn.2])
theorem lincomb_compactSupport (hd : IsDistanceFun d) {f g : X → ℝ} (a b : ℝ) {A : Set X}
    (hf : IsCompactWrt d (closureWrt d {x | f x ≠ 0})) (hfA : closureWrt d {x | f x ≠ 0} ⊆ A)
    (hg : IsCompactWrt d (closureWrt d {x | g x ≠ 0})) (hgA : closureWrt d {x | g x ≠ 0} ⊆ A) :
    IsCompactWrt d (closureWrt d {x | (a • f + b • g) x ≠ 0}) ∧
      closureWrt d {x | (a • f + b • g) x ≠ 0} ⊆ A := by
  refine ⟨?_, (closureWrt_support_lincomb_subset hd f g a b).trans (union_subset hfA hgA)⟩
  let _ := metricSpaceOf hd
  rw [isCompactWrt_iff_isCompact hd] at hf hg ⊢
  refine (hf.union hg).of_isClosed_subset ?_ (closureWrt_support_lincomb_subset hd f g a b)
  rw [closureWrt_eq_closure hd]
  exact isClosed_closure
theorem zero_compactSupport (hd : IsDistanceFun d) (A : Set X) :
    IsCompactWrt d (closureWrt d {x | (0 : X → ℝ) x ≠ 0}) ∧
      closureWrt d {x | (0 : X → ℝ) x ≠ 0} ⊆ A := by
  have h : closureWrt d {x | (0 : X → ℝ) x ≠ 0} = ∅ := by
    let _ := metricSpaceOf hd
    rw [closureWrt_eq_closure hd]
    simp
  rw [h]
  refine ⟨?_, empty_subset _⟩
  let _ := metricSpaceOf hd
  rw [isCompactWrt_iff_isCompact hd]
  exact isCompact_empty
theorem isBoundedFun_of_lipschitz_compactSupport (hd : IsDistanceFun d) {f : X → ℝ}
    (hf : IsLipschitzFor d f) (hK : IsCompactWrt d (closureWrt d {x | f x ≠ 0})) :
    IsBoundedFun f := by
  let _ := metricSpaceOf hd
  obtain ⟨K, hK0, hlip⟩ := hf
  have hc : Continuous f := by
    refine LipschitzWith.continuous (K := ⟨K, hK0⟩) (LipschitzWith.of_dist_le_mul fun x y => ?_)
    rw [Real.dist_eq]
    exact hlip x y
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
theorem uniformNorm_smul (a : ℝ) (f : X → ℝ) : uniformNorm (a • f) = |a| * uniformNorm f := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.SeparatedTuples.uniformNorm_smul <;> assumption
theorem uniformNorm_add_le {f g : X → ℝ} (hf : IsBoundedFun f) (hg : IsBoundedFun g) :
    uniformNorm (f + g) ≤ uniformNorm f + uniformNorm g := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.SeparatedTuples.uniformNorm_add_le <;> assumption
variable {d : X → X → ℝ}
theorem bestLipschitzConstant_nonneg (f : X → ℝ) : 0 ≤ bestLipschitzConstant d f :=
  Real.sInf_nonneg fun _ hC => hC.1
theorem norm_sub_le_bestLipschitzConstant_mul (hd : IsDistanceFun d) {f : X → ℝ}
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
theorem bestLipschitzConstant_smul_le (hd : IsDistanceFun d) {f : X → ℝ}
    (hf : IsLipschitzFor d f) (a : ℝ) :
    bestLipschitzConstant d (a • f) ≤ |a| * bestLipschitzConstant d f := by
  refine csInf_le ⟨0, fun _ hC => hC.1⟩
    ⟨mul_nonneg (abs_nonneg a) (bestLipschitzConstant_nonneg f), fun x y => ?_⟩
  have h : (a • f) x - (a • f) y = a * (f x - f y) := by simp [mul_sub]
  rw [h, norm_mul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_sub_le_bestLipschitzConstant_mul hd hf x y)
    (abs_nonneg a)
theorem isLipschitzFor_smul {f : X → ℝ} (hf : IsLipschitzFor d f) (a : ℝ) :
    IsLipschitzFor d (a • f) := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.SeparatedTuples.isLipschitzFor_smul <;> assumption
theorem isLipschitzFor_add {f g : X → ℝ} (hf : IsLipschitzFor d f) (hg : IsLipschitzFor d g) :
    IsLipschitzFor d (f + g) := by
  obtain ⟨C, hC, h⟩ := hf
  obtain ⟨C', hC', h'⟩ := hg
  refine ⟨C + C', add_nonneg hC hC', fun x y => ?_⟩
  have he : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by simp; ring
  rw [he, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h x y) (h' x y))
theorem bestLipschitzConstant_smul (hd : IsDistanceFun d) {f : X → ℝ}
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
theorem bestLipschitzConstant_add_le (hd : IsDistanceFun d) {f g : X → ℝ}
    (hf : IsLipschitzFor d f) (hg : IsLipschitzFor d g) :
    bestLipschitzConstant d (f + g) ≤ bestLipschitzConstant d f + bestLipschitzConstant d g := by
  refine csInf_le ⟨0, fun _ hC => hC.1⟩
    ⟨add_nonneg (bestLipschitzConstant_nonneg f) (bestLipschitzConstant_nonneg g),
      fun x y => ?_⟩
  have h : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by simp; ring
  rw [h, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_sub_le_bestLipschitzConstant_mul hd hf x y)
    (norm_sub_le_bestLipschitzConstant_mul hd hg x y))
theorem exists_submodule_coe_eq {V : Set (X → ℝ)} (h0 : (0 : X → ℝ) ∈ V)
    (hc : ∀ f ∈ V, ∀ g ∈ V, ∀ a b : ℝ, a • f + b • g ∈ V) :
    ∃ W : Submodule ℝ (X → ℝ), (W : Set (X → ℝ)) = V := by
  refine ⟨{ carrier := V, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro f g hf hg
    simpa using hc f hf g hg 1 1
  · intro a f hf
    simpa using hc f hf 0 h0 a 0
end Seminorms
theorem properties_of_invariantDist_and_c1 (hlen : InvariantDistFromNorm.Claim)
    (hc1 : C1ViaLift.Claim) : Properties := by
  intro s M Y
  obtain ⟨-, -, hnn, hz, hsy, htr, -⟩ := hlen s Y
  have hd : IsDistanceFun (ModelSpace.dist s Y) :=
    ⟨hz, hsy, fun x y w => htr x w y, hnn⟩
  obtain ⟨hiff, -, hcomb⟩ := hc1 s Y
  have hbd : ∀ h ∈ ModelSpace.lipCompactSupp s Y univ,
      IsBoundedFun h ∧ ModelSpace.IsLipschitzReal s Y h :=
    fun h hh => ⟨isBoundedFun_of_lipschitz_compactSupport hd hh.1 hh.2.1, hh.1⟩
  have hform : ∀ f, ModelSpace.sharpNorm s M Y f =
      max (uniformNorm f) (40 * (M.1 : ℝ) * bestLipschitzConstant (ModelSpace.dist s Y) f) :=
    fun f => by
      rw [ModelSpace.sharpNorm_eq_max, ModelSpace.lipNumber_eq_bestLipschitzConstant]
  have hc : (0 : ℝ) ≤ 40 * (M.1 : ℝ) := by positivity
  refine ⟨fun A => ?_, fun A => ?_, hbd, fun h _ => ?_, fun α h hh => ?_, fun h hh h' hh' => ?_⟩
  · refine exists_submodule_coe_eq ?_ fun f hf g hg a b => ?_
    · obtain ⟨h1, h2⟩ := zero_compactSupport hd (d := ModelSpace.dist s Y) A
      exact ⟨⟨0, le_rfl, fun x y => by simp⟩, h1, h2⟩
    · obtain ⟨h1, h2⟩ := lincomb_compactSupport hd a b hf.2.1 hf.2.2 hg.2.1 hg.2.2
      exact ⟨isLipschitzFor_add (isLipschitzFor_smul hf.1 a) (isLipschitzFor_smul hg.1 b),
        h1, h2⟩
  · refine exists_submodule_coe_eq ?_ fun f hf g hg a b => ?_
    · obtain ⟨h1, h2⟩ := zero_compactSupport hd (d := ModelSpace.dist s Y) A
      exact ⟨(hiff 0).2 (contDiff_const (c := (0 : ℝ))), h1, h2⟩
    · obtain ⟨h1, h2⟩ := lincomb_compactSupport hd a b hf.2.1 hf.2.2 hg.2.1 hg.2.2
      exact ⟨(hcomb f g hf.1 hg.1).1 a b, h1, h2⟩
  · rw [hform]
    exact le_max_of_le_left (uniformNorm_nonneg h)
  · rw [hform, hform, uniformNorm_smul, bestLipschitzConstant_smul hd (hbd h hh).2,
      mul_max_of_nonneg _ _ (abs_nonneg α)]
    congr 1
    ring
  · rw [hform, hform, hform]
    refine max_le ((uniformNorm_add_le (hbd h hh).1 (hbd h' hh').1).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
    refine (mul_le_mul_of_nonneg_left
      (bestLipschitzConstant_add_le hd (hbd h hh).2 (hbd h' hh').2) hc).trans ?_
    rw [mul_add]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
end YangMills.Construction.LatticeLimits.SharpSeminorm
end
