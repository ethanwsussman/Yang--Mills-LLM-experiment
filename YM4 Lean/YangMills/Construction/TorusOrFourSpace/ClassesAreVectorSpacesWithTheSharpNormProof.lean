import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBalls
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.VectorClasses
open PeriodicSpace.Kind MetricNotions
section Metric
variable {X : Type*} (d : X → X → ℝ)
private theorem mem_closureWrt_iff {Z : Set X} {x : X} :
    x ∈ closureWrt d Z ↔ ∀ r : ℝ, 0 < r → ∃ y ∈ Z, d x y < r := Iff.rfl
private theorem exists_sep_of_not_mem_closure {Z : Set X} {x : X} (hx : x ∉ closureWrt d Z) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Z, r ≤ d x y := by
  rw [mem_closureWrt_iff] at hx
  push Not at hx
  exact hx
abbrev _root_.YangMills.SharedProofs.p12075 := @exists_sep_of_not_mem_closure
private theorem isClosedWrt_closureWrt (htri : ∀ x y z, d x z ≤ d x y + d y z) (Z : Set X) :
    IsClosedWrt d (closureWrt d Z) := by
  intro x hx
  obtain ⟨r, hr, hsep⟩ := exists_sep_of_not_mem_closure d hx
  refine ⟨r / 2, half_pos hr, fun y hy hyc => ?_⟩
  obtain ⟨z, hz, hyz⟩ := (mem_closureWrt_iff d).1 hyc (r / 2) (half_pos hr)
  have h1 := hsep z hz
  have h2 := htri x y z
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p500759 := @isClosedWrt_closureWrt
abbrev _root_.YangMills.SharedProofs.p11892 := @isClosedWrt_closureWrt
private theorem IsCompactWrt.of_isClosedWrt_subset {S T : Set X} (hS : IsCompactWrt d S)
    (hT : IsClosedWrt d T) (hTS : T ⊆ S) : IsCompactWrt d T := by
  intro 𝒰 hU hcov
  have hopen : ∀ U ∈ insert Tᶜ 𝒰, IsOpenWrt d U := by
    intro U hUi
    rcases hUi with rfl | hU'
    · exact hT
    · exact hU U hU'
  have hcover : S ⊆ ⋃₀ insert Tᶜ 𝒰 := by
    intro x _
    by_cases hxT : x ∈ T
    · obtain ⟨U, hU', hxU⟩ := hcov hxT
      exact ⟨U, Or.inr hU', hxU⟩
    · exact ⟨Tᶜ, Or.inl rfl, hxT⟩
  obtain ⟨𝒱, hV, hfin, hSV⟩ := hS _ hopen hcover
  refine ⟨𝒱 ∩ 𝒰, Set.inter_subset_right, hfin.subset Set.inter_subset_left, fun x hx => ?_⟩
  obtain ⟨V, hV', hxV⟩ := hSV (hTS hx)
  rcases hV hV' with rfl | hVU
  · exact absurd hx hxV
  · exact ⟨V, ⟨hV', hVU⟩, hxV⟩
abbrev _root_.YangMills.DeltaSharedProofs.p500420 := @IsCompactWrt.of_isClosedWrt_subset
abbrev _root_.YangMills.SharedProofs.p5019 := @IsCompactWrt.of_isClosedWrt_subset
private theorem IsCompactWrt.union {S T : Set X} (hS : IsCompactWrt d S) (hT : IsCompactWrt d T) :
    IsCompactWrt d (S ∪ T) := by
  intro 𝒰 hU hcov
  obtain ⟨𝒱, hV, hfin, hSV⟩ := hS 𝒰 hU (Set.subset_union_left.trans hcov)
  obtain ⟨𝒲, hW, hfin', hTW⟩ := hT 𝒰 hU (Set.subset_union_right.trans hcov)
  refine ⟨𝒱 ∪ 𝒲, Set.union_subset hV hW, hfin.union hfin', ?_⟩
  rintro x (hx | hx)
  · obtain ⟨V, hV', hxV⟩ := hSV hx
    exact ⟨V, Or.inl hV', hxV⟩
  · obtain ⟨V, hV', hxV⟩ := hTW hx
    exact ⟨V, Or.inr hV', hxV⟩
abbrev _root_.YangMills.SharedProofs.p57694 := @IsCompactWrt.union
private theorem isCompactWrt_empty : IsCompactWrt d (∅ : Set X) :=
  fun _ _ _ => ⟨∅, Set.empty_subset _, Set.finite_empty, Set.empty_subset _⟩
private theorem closureWrt_ne_zero_subset {g u v : X → ℝ} (hz : ∀ y, u y = 0 → v y = 0 → g y = 0) :
    closureWrt d {y | g y ≠ 0} ⊆ closureWrt d {y | u y ≠ 0} ∪ closureWrt d {y | v y ≠ 0} := by
  intro x hx
  by_contra hn
  rw [Set.mem_union, not_or] at hn
  obtain ⟨r, hr, hsep⟩ := exists_sep_of_not_mem_closure d hn.1
  obtain ⟨r', hr', hsep'⟩ := exists_sep_of_not_mem_closure d hn.2
  obtain ⟨y, hy, hxy⟩ := (mem_closureWrt_iff d).1 hx (min r r') (lt_min hr hr')
  have hu : u y = 0 := by
    by_contra hne
    exact absurd (hxy.trans_le (min_le_left _ _)) (not_lt.2 (hsep y hne))
  have hv : v y = 0 := by
    by_contra hne
    exact absurd (hxy.trans_le (min_le_right _ _)) (not_lt.2 (hsep' y hne))
  exact hy (hz y hu hv)
end Metric
variable (D : Params) (E : Kind)
private theorem isLipschitzQ_iff {u : E.Pt D → ℝ} :
    IsLipschitzQ D E u ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ y y', |u y - u y'| ≤ C * quotDist D E y y' := Iff.rfl
private theorem mem_lipschitzSupportedIn_iff {A : Set (E.Pt D)} {f : E.Pt D → ℝ} :
    f ∈ lipschitzSupportedIn D E A ↔
      IsLipschitzQ D E f ∧ IsCompactQ D E (supportQ D E f) ∧ supportQ D E f ⊆ A := Iff.rfl
private theorem mem_c1SupportedIn_iff {A : Set (E.Pt D)} {f : E.Pt D → ℝ} :
    f ∈ c1SupportedIn D E A ↔
      f ∈ c1Set D E ∧ IsCompactQ D E (supportQ D E f) ∧ supportQ D E f ⊆ A := Iff.rfl
private theorem mem_c1Set_iff {f : E.Pt D → ℝ} :
    f ∈ c1Set D E ↔ ContDiff ℝ 1 (f ∘ E.quotMap D) := Iff.rfl
private theorem mem_lipschitzBounds_iff {u : E.Pt D → ℝ} {C : ℝ} :
    C ∈ WellPosedness.lipschitzBounds D E u ↔
      0 ≤ C ∧ ∀ y y', |u y - u y'| ≤ C * quotDist D E y y' := Iff.rfl
private theorem supportQ_zero : supportQ D E (0 : E.Pt D → ℝ) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨y, hy, -⟩ := (mem_closureWrt_iff (quotDist D E)).1 hx 1 one_pos
  exact hy rfl
private theorem supportQ_linear_comb_subset (f g : E.Pt D → ℝ) (a b : ℝ) :
    supportQ D E (a • f + b • g) ⊆ supportQ D E f ∪ supportQ D E g :=
  closureWrt_ne_zero_subset (quotDist D E) fun y hy hy' => by
    simp [hy, hy']
private theorem IsLipschitzQ.linear_comb {f g : E.Pt D → ℝ} (hf : IsLipschitzQ D E f)
    (hg : IsLipschitzQ D E g) (a b : ℝ) :
    IsLipschitzQ D E (a • f + b • g) := by
  obtain ⟨C, hC, hb⟩ := (isLipschitzQ_iff D E).1 hf
  obtain ⟨C', hC', hb'⟩ := (isLipschitzQ_iff D E).1 hg
  refine (isLipschitzQ_iff D E).2 ⟨|a| * C + |b| * C', by positivity, fun y y' => ?_⟩
  have heq : (a • f + b • g) y - (a • f + b • g) y' =
      a * (f y - f y') + b * (g y - g y') := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  calc |a * (f y - f y') + b * (g y - g y')|
      ≤ |a * (f y - f y')| + |b * (g y - g y')| := abs_add_le _ _
    _ = |a| * |f y - f y'| + |b| * |g y - g y'| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * (C * quotDist D E y y') + |b| * (C' * quotDist D E y y') := by
        gcongr
        · exact hb y y'
        · exact hb' y y'
    _ = (|a| * C + |b| * C') * quotDist D E y y' := by ring
private theorem exists_abs_le_of_compact_support {f : E.Pt D → ℝ} (hf : IsLipschitzQ D E f)
    (hc : IsCompactQ D E (supportQ D E f))
    (hd : ∀ y y' : E.Pt D, 0 ≤ quotDist D E y y')
    (hself : ∀ y : E.Pt D, quotDist D E y y = 0) : ∃ C : ℝ, ∀ y, |f y| ≤ C := by
  obtain ⟨C, hC, hb⟩ := (isLipschitzQ_iff D E).1 hf
  have hopen : ∀ U ∈ Set.range (fun n : ℕ => {y | |f y| < (n : ℝ)}),
      IsOpenWrt (quotDist D E) U := by
    rintro _ ⟨n, rfl⟩ y hy
    have hy' : |f y| < (n : ℝ) := hy
    have hC1 : 0 < C + 1 := by linarith
    refine ⟨((n : ℝ) - |f y|) / (C + 1), div_pos (sub_pos.2 hy') hC1, fun z hz => ?_⟩
    show |f z| < (n : ℝ)
    have h1 : |f z| - |f y| ≤ |f z - f y| := abs_sub_abs_le_abs_sub _ _
    have h2 : |f z - f y| ≤ C * quotDist D E y z := by
      rw [abs_sub_comm]
      exact hb y z
    have h3 : quotDist D E y z * (C + 1) < (n : ℝ) - |f y| := (lt_div_iff₀ hC1).1 hz
    have h4 := hd y z
    nlinarith
  have hcov : supportQ D E f ⊆ ⋃₀ Set.range (fun n : ℕ => {y | |f y| < (n : ℝ)}) := by
    intro y _
    obtain ⟨n, hn⟩ := exists_nat_gt |f y|
    exact ⟨_, ⟨n, rfl⟩, hn⟩
  obtain ⟨𝒰, hsub, hfin, hcov'⟩ := hc _ hopen hcov
  have hch : ∀ U ∈ 𝒰, ∃ n : ℕ, U = {y | |f y| < (n : ℝ)} := by
    intro U hU
    obtain ⟨n, rfl⟩ := hsub hU
    exact ⟨n, rfl⟩
  choose! k hk using hch
  obtain ⟨N, hN⟩ := (hfin.image k).bddAbove
  refine ⟨N, fun y => ?_⟩
  by_cases hy : y ∈ supportQ D E f
  · obtain ⟨U, hU, hyU⟩ := hcov' hy
    have hkN : k U ≤ N := hN ⟨U, hU, rfl⟩
    have hlt : y ∈ {y | |f y| < (k U : ℝ)} := by
      rw [← hk U hU]
      exact hyU
    have hlt' : |f y| < (k U : ℝ) := hlt
    have hcast : (k U : ℝ) ≤ N := by exact_mod_cast hkN
    linarith
  · have h0 : f y = 0 := by
      by_contra hne
      exact hy fun r hr => ⟨y, hne, by rw [hself y]; exact hr⟩
    rw [h0, abs_zero]
    exact Nat.cast_nonneg N
section SharpNorm
variable (hL : WellPosedness.LipConstIsLeastBound D E)
include hL
private theorem lipConstQ_nonneg {u : E.Pt D → ℝ} (hu : IsLipschitzQ D E u) :
    0 ≤ lipConstQ D E u :=
  ((mem_lipschitzBounds_iff D E).1 (hL u hu).2.1).1
private theorem abs_sub_le_lipConstQ_mul {u : E.Pt D → ℝ} (hu : IsLipschitzQ D E u) (y y' : E.Pt D) :
    |u y - u y'| ≤ lipConstQ D E u * quotDist D E y y' :=
  ((mem_lipschitzBounds_iff D E).1 (hL u hu).2.1).2 y y'
private theorem lipConstQ_le_of_bound {u : E.Pt D → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y y', |u y - u y'| ≤ C * quotDist D E y y') : lipConstQ D E u ≤ C :=
  (hL u ((isLipschitzQ_iff D E).2 ⟨C, hC, hb⟩)).2.2 ((mem_lipschitzBounds_iff D E).2 ⟨hC, hb⟩)
private theorem lipConstQ_zero : lipConstQ D E (0 : E.Pt D → ℝ) = 0 := by
  have hz : ∀ y y' : E.Pt D, |(0 : E.Pt D → ℝ) y - (0 : E.Pt D → ℝ) y'| ≤
      0 * quotDist D E y y' := by
    intro y y'
    simp
  exact le_antisymm (lipConstQ_le_of_bound D E hL le_rfl hz)
    (lipConstQ_nonneg D E hL ((isLipschitzQ_iff D E).2 ⟨0, le_rfl, hz⟩))
private theorem lipConstQ_smul_le {f : E.Pt D → ℝ} (hf : IsLipschitzQ D E f) (a : ℝ) :
    lipConstQ D E (a • f) ≤ |a| * lipConstQ D E f := by
  refine lipConstQ_le_of_bound D E hL
    (mul_nonneg (abs_nonneg _) (lipConstQ_nonneg D E hL hf)) fun y y' => ?_
  have heq : (a • f) y - (a • f) y' = a * (f y - f y') := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_sub_le_lipConstQ_mul D E hL hf y y') (abs_nonneg _)
private theorem lipConstQ_smul {f : E.Pt D → ℝ} (hf : IsLipschitzQ D E f)
    (hsf : ∀ a : ℝ, IsLipschitzQ D E (a • f)) (a : ℝ) :
    lipConstQ D E (a • f) = |a| * lipConstQ D E f := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul, abs_zero, zero_mul]
    exact lipConstQ_zero D E hL
  · refine le_antisymm (lipConstQ_smul_le D E hL hf a) ?_
    have h1 := lipConstQ_smul_le D E hL (hsf a) a⁻¹
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv] at h1
    have hpos : 0 < |a| := abs_pos.2 ha
    calc |a| * lipConstQ D E f
        ≤ |a| * (|a|⁻¹ * lipConstQ D E (a • f)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = lipConstQ D E (a • f) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
private theorem lipConstQ_add_le {f g : E.Pt D → ℝ} (hf : IsLipschitzQ D E f)
    (hg : IsLipschitzQ D E g) :
    lipConstQ D E (f + g) ≤ lipConstQ D E f + lipConstQ D E g := by
  refine lipConstQ_le_of_bound D E hL
    (add_nonneg (lipConstQ_nonneg D E hL hf) (lipConstQ_nonneg D E hL hg))
    fun y y' => ?_
  have heq : (f + g) y - (f + g) y' = (f y - f y') + (g y - g y') := by
    simp only [Pi.add_apply]
    ring
  rw [heq, add_mul]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_sub_le_lipConstQ_mul D E hL hf y y') (abs_sub_le_lipConstQ_mul D E hL hg y y'))
end SharpNorm
private theorem supNormQ_smul (f : E.Pt D → ℝ) (a : ℝ) :
    supNormQ D E (a • f) = ENNReal.ofReal |a| * supNormQ D E f := by
  unfold supNormQ
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun y => ?_
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact ENNReal.ofReal_mul (abs_nonneg _)
private theorem ofReal_abs_le_supNormQ (f : E.Pt D → ℝ) (y : E.Pt D) :
    ENNReal.ofReal |f y| ≤ supNormQ D E f :=
  le_iSup (fun y => ENNReal.ofReal |f y|) y
private theorem supNormQ_add_le (f g : E.Pt D → ℝ) :
    supNormQ D E (f + g) ≤ supNormQ D E f + supNormQ D E g := by
  refine iSup_le fun y => ?_
  calc ENNReal.ofReal |(f + g) y|
      ≤ ENNReal.ofReal (|f y| + |g y|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |f y| + ENNReal.ofReal |g y| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ supNormQ D E f + supNormQ D E g :=
        add_le_add (ofReal_abs_le_supNormQ D E f y) (ofReal_abs_le_supNormQ D E g y)
abbrev _root_.YangMills.SharedProofs.p62305 := @supNormQ_add_le
private theorem forty_mul_M_nonneg : 0 ≤ 40 * D.M := by
  have := D.one_le_M
  linarith
private theorem sharpNormQ_eq (f : E.Pt D → ℝ) :
    sharpNormQ D E f =
      max (supNormQ D E f) (ENNReal.ofReal (40 * D.M * lipConstQ D E f)) := rfl
private theorem isLinearSubspaceSet_of {V : Set (E.Pt D → ℝ)} (h0 : (0 : E.Pt D → ℝ) ∈ V)
    (hc : ∀ f ∈ V, ∀ g ∈ V, ∀ a b : ℝ, a • f + b • g ∈ V) : IsLinearSubspaceSet D E V := by
  unfold IsLinearSubspaceSet
  refine ⟨{ carrier := V, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro f g hf hg
    simpa using hc f hf g hg 1 1
  · intro c x hx
    simpa using hc x hx 0 h0 c 0
section LinearClasses
variable (htri : ∀ y y' y'' : E.Pt D,
  quotDist D E y y'' ≤ quotDist D E y y' + quotDist D E y' y'')
include htri
private theorem isCompactQ_supportQ_linear_comb {f g : E.Pt D → ℝ}
    (hc : IsCompactQ D E (supportQ D E f)) (hc' : IsCompactQ D E (supportQ D E g))
    (a b : ℝ) : IsCompactQ D E (supportQ D E (a • f + b • g)) :=
  IsCompactWrt.of_isClosedWrt_subset (quotDist D E) (IsCompactWrt.union (quotDist D E) hc hc')
    (isClosedWrt_closureWrt (quotDist D E) htri _) (supportQ_linear_comb_subset D E f g a b)
private theorem lipschitzSupportedIn_linear_comb (A : Set (E.Pt D)) :
    ∀ f ∈ lipschitzSupportedIn D E A, ∀ g ∈ lipschitzSupportedIn D E A, ∀ a b : ℝ,
      a • f + b • g ∈ lipschitzSupportedIn D E A := by
  intro f hf g hg a b
  obtain ⟨hl, hc, hs⟩ := (mem_lipschitzSupportedIn_iff D E).1 hf
  obtain ⟨hl', hc', hs'⟩ := (mem_lipschitzSupportedIn_iff D E).1 hg
  exact (mem_lipschitzSupportedIn_iff D E).2 ⟨IsLipschitzQ.linear_comb D E hl hl' a b,
    isCompactQ_supportQ_linear_comb D E htri hc hc' a b,
    (supportQ_linear_comb_subset D E f g a b).trans (Set.union_subset hs hs')⟩
private theorem c1SupportedIn_linear_comb (A : Set (E.Pt D)) :
    ∀ f ∈ c1SupportedIn D E A, ∀ g ∈ c1SupportedIn D E A, ∀ a b : ℝ,
      a • f + b • g ∈ c1SupportedIn D E A := by
  intro f hf g hg a b
  obtain ⟨hl, hc, hs⟩ := (mem_c1SupportedIn_iff D E).1 hf
  obtain ⟨hl', hc', hs'⟩ := (mem_c1SupportedIn_iff D E).1 hg
  have h1 := (mem_c1Set_iff D E).1 hl
  have h2 := (mem_c1Set_iff D E).1 hl'
  have h3 : ContDiff ℝ 1 ((a • f + b • g) ∘ E.quotMap D) :=
    (h1.const_smul a).add (h2.const_smul b)
  exact (mem_c1SupportedIn_iff D E).2 ⟨(mem_c1Set_iff D E).2 h3,
    isCompactQ_supportQ_linear_comb D E htri hc hc' a b,
    (supportQ_linear_comb_subset D E f g a b).trans (Set.union_subset hs hs')⟩
end LinearClasses
private theorem zero_mem_lipschitzSupportedIn (A : Set (E.Pt D)) :
    (0 : E.Pt D → ℝ) ∈ lipschitzSupportedIn D E A := by
  refine (mem_lipschitzSupportedIn_iff D E).2
    ⟨(isLipschitzQ_iff D E).2 ⟨0, le_rfl, fun y y' => ?_⟩, ?_, ?_⟩
  · simp
  · rw [supportQ_zero]
    exact isCompactWrt_empty (quotDist D E)
  · rw [supportQ_zero]
    exact Set.empty_subset _
private theorem zero_mem_c1SupportedIn (A : Set (E.Pt D)) :
    (0 : E.Pt D → ℝ) ∈ c1SupportedIn D E A := by
  have h1 : ContDiff ℝ 1 ((0 : E.Pt D → ℝ) ∘ E.quotMap D) :=
    contDiff_const (c := (0 : ℝ))
  refine (mem_c1SupportedIn_iff D E).2 ⟨(mem_c1Set_iff D E).2 h1, ?_, ?_⟩
  · rw [supportQ_zero]
    exact isCompactWrt_empty (quotDist D E)
  · rw [supportQ_zero]
    exact Set.empty_subset _
private theorem isNormOn_sharpNormQ
    (hL : WellPosedness.LipConstIsLeastBound D E)
    (hbound : ∀ f ∈ lipschitzSupportedIn D E Set.univ, ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    IsNormOn D E (lipschitzSupportedIn D E Set.univ) (sharpNormQ D E) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨C, hC⟩ := hbound f hf
    rw [sharpNormQ_eq]
    exact max_lt ((iSup_le fun y => ENNReal.ofReal_le_ofReal (hC y)).trans_lt
      ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  · intro f _
    constructor
    · intro h0
      funext y
      have h1 : ENNReal.ofReal |f y| ≤ 0 := by
        refine (ofReal_abs_le_supNormQ D E f y).trans ?_
        rw [← h0, sharpNormQ_eq]
        exact le_max_left _ _
      have h2 : |f y| ≤ 0 := ENNReal.ofReal_eq_zero.1 (nonpos_iff_eq_zero.1 h1)
      exact abs_nonpos_iff.1 h2
    · rintro rfl
      rw [sharpNormQ_eq, lipConstQ_zero D E hL]
      simp [supNormQ]
  · intro f hf a
    have hl := ((mem_lipschitzSupportedIn_iff D E).1 hf).1
    have hsl : ∀ c : ℝ, IsLipschitzQ D E (c • f) := fun c => by
      simpa using IsLipschitzQ.linear_comb D E hl hl c 0
    rw [sharpNormQ_eq, sharpNormQ_eq, supNormQ_smul, lipConstQ_smul D E hL hl hsl a]
    have h1 : ENNReal.ofReal (40 * D.M * (|a| * lipConstQ D E f)) =
        ENNReal.ofReal |a| * ENNReal.ofReal (40 * D.M * lipConstQ D E f) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      ring
    rw [h1]
    have hmono : Monotone (fun t : ℝ≥0∞ => ENNReal.ofReal |a| * t) := by
      intro s t hst
      dsimp only
      gcongr
    exact (hmono.map_max).symm
  · intro f hf g hg
    have hl := ((mem_lipschitzSupportedIn_iff D E).1 hf).1
    have hl' := ((mem_lipschitzSupportedIn_iff D E).1 hg).1
    have h40 := forty_mul_M_nonneg D
    have hb : ENNReal.ofReal (40 * D.M * lipConstQ D E (f + g)) ≤
        ENNReal.ofReal (40 * D.M * lipConstQ D E f) +
          ENNReal.ofReal (40 * D.M * lipConstQ D E g) := by
      rw [← ENNReal.ofReal_add (mul_nonneg h40 (lipConstQ_nonneg D E hL hl))
        (mul_nonneg h40 (lipConstQ_nonneg D E hL hl'))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (lipConstQ_add_le D E hL hl hl') h40
    rw [sharpNormQ_eq, sharpNormQ_eq, sharpNormQ_eq]
    exact max_le
      ((supNormQ_add_le D E f g).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (hb.trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
theorem claim_holds (hballs : BallCompactnessAndTorusLifts)
    (hquot : Kind.QuotientCompactC1.Claim)
    (hwell : WellPosedness.WellPosed) : Claim := by
  intro D E
  obtain ⟨hd, hz, -, htri, -, -⟩ := (hquot D E).1
  have hL : WellPosedness.LipConstIsLeastBound D E :=
    (hwell D E).2.2.2.2.2.2.2.2.2.2.2
  have hself : ∀ y : E.Pt D, quotDist D E y y = 0 := fun y => (hz y y).2 rfl
  have hbound : ∀ f ∈ lipschitzSupportedIn D E Set.univ, ∃ C : ℝ, ∀ y, |f y| ≤ C := by
    intro f hf
    obtain ⟨hl, hc, -⟩ := (mem_lipschitzSupportedIn_iff D E).1 hf
    exact exists_abs_le_of_compact_support D E hl hc hd hself
  refine ⟨fun A => ?_, ?_, fun A hA => ?_⟩
  · unfold ClassesLinear
    refine ⟨isLinearSubspaceSet_of D E (zero_mem_lipschitzSupportedIn D E A)
        (lipschitzSupportedIn_linear_comb D E htri A),
      isLinearSubspaceSet_of D E (zero_mem_c1SupportedIn D E A)
        (c1SupportedIn_linear_comb D E htri A), ?_, ?_⟩
    · intro f _ g _ a b
      exact supportQ_linear_comb_subset D E f g a b
    · intro f _ g _ a b
      exact supportQ_linear_comb_subset D E f g a b
  · unfold BoundedAndSharpNorm
    refine ⟨fun f hf => ?_, isNormOn_sharpNormQ D E hL hbound⟩
    obtain ⟨C, hC⟩ := hbound f hf
    show ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C
    exact ⟨C, fun y => hC y⟩
  · obtain ⟨S, R, ⟨hR, x, rfl⟩, hAS⟩ := hA
    have hcb : IsCompactQ D E (closedBallAbout D E x R) := (hballs D).1 E x R hR
    have hcl : ∀ T : Set (E.Pt D), IsClosedQ D E T → T ⊆ A → IsCompactQ D E T :=
      fun T hT hTA => IsCompactWrt.of_isClosedWrt_subset (quotDist D E) hcb hT (hTA.trans hAS)
    have hsupp : ∀ f : E.Pt D → ℝ, supportQ D E f ⊆ A → IsCompactQ D E (supportQ D E f) :=
      fun f hs => hcl _ (isClosedWrt_closureWrt (quotDist D E) htri _) hs
    unfold CompactFreeInBall
    refine ⟨hcl, ?_, ?_⟩
    · ext f
      rw [mem_lipschitzSupportedIn_iff, Set.mem_ofPred_eq]
      exact ⟨fun hf => ⟨hf.1, hf.2.2⟩, fun hf => ⟨hf.1, hsupp f hf.2, hf.2⟩⟩
    · ext f
      rw [mem_c1SupportedIn_iff, Set.mem_ofPred_eq]
      exact ⟨fun hf => ⟨hf.1, hf.2.2⟩, fun hf => ⟨hf.1, hsupp f hf.2, hf.2⟩⟩
end YangMills.Construction.PeriodicSpace.VectorClasses
