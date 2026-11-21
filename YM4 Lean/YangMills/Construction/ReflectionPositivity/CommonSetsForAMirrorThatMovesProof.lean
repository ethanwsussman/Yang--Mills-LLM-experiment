import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.ReflectionPositivity.CentredFunctionalsAlongAConvergentSequence
import YangMills.Construction.ReflectionPositivity.CommonSetsForAMirrorThatMoves
import YangMills.Construction.ReflectionPositivity.MirrorsAndSides
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirrorSets
section Distance
variable {α : Type*} {d : α → α → ℝ}
def setGap (d : α → α → ℝ) (A B : Set α) : ℝ≥0∞ := ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (d a b)
theorem le_setGap {A B : Set α} {r : ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, r ≤ d a b) :
    ENNReal.ofReal r ≤ setGap d A B :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (h a ha b hb)
theorem setGap_le {A B : Set α} {a b : α} (ha : a ∈ A) (hb : b ∈ B) :
    setGap d A B ≤ ENNReal.ofReal (d a b) :=
  iInf₂_le_of_le a ha (iInf₂_le b hb)
theorem setGap_anti_left {A A' M : Set α} (h : A' ⊆ A) : setGap d A M ≤ setGap d A' M :=
  le_iInf₂ fun a ha => iInf₂_le a (h ha)
theorem setGap_comm_le (hd : FamilyTopology.IsMetricFunction d) (A B : Set α) :
    setGap d A B ≤ setGap d B A :=
  le_iInf₂ fun b hb => le_iInf₂ fun a ha => by
    rw [hd.symm b a]
    exact setGap_le ha hb
theorem disjoint_of_setGap_pos (hd : FamilyTopology.IsMetricFunction d) {A B : Set α}
    (h : 0 < setGap d A B) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hA hB
  have h₁ : setGap d A B ≤ ENNReal.ofReal (d x x) := setGap_le hA hB
  rw [(hd.eq_zero_iff x x).2 rfl, ENNReal.ofReal_zero] at h₁
  exact absurd h (not_lt.2 h₁)
theorem exists_close_of_setGap_le {B : Set α} {x : α} {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε)
    (h : setGap d {x} B ≤ ENNReal.ofReal η) : ∃ b ∈ B, d x b < η + ε := by
  by_contra hcon
  push Not at hcon
  have h₁ : ENNReal.ofReal (η + ε) ≤ setGap d {x} B :=
    le_setGap fun a ha b hb => by
      rw [Set.mem_singleton_iff.1 ha]
      exact hcon b hb
  have h₂ := (ENNReal.ofReal_le_ofReal_iff hη).1 (h₁.trans h)
  linarith
theorem isClosedWrt_thickening (hd : FamilyTopology.IsMetricFunction d) (B : Set α) {η : ℝ}
    (hη : 0 ≤ η) : MetricNotions.IsClosedWrt d {x | setGap d {x} B ≤ ENNReal.ofReal η} := by
  intro x hx
  have hlt : ENNReal.ofReal η < setGap d {x} B := not_le.1 hx
  obtain ⟨r, hr₁, hr₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hηr : η < r := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal hη ENNReal.coe_ne_top).1 hr₁
    simpa using this
  refine ⟨r - η, sub_pos.2 hηr, fun y hy hyZ => ?_⟩
  have hε : 0 < ((r : ℝ) - η - d x y) / 2 := by linarith
  obtain ⟨b, hb, hyb⟩ := exists_close_of_setGap_le hη hε hyZ
  have h₁ := hd.triangle x y b
  have h₂ : d x b ≤ r := by linarith
  have h₃ : setGap d {x} B ≤ ENNReal.ofReal (d x b) := setGap_le (Set.mem_singleton x) hb
  have h₄ : ENNReal.ofReal (d x b) ≤ (r : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h₂
  exact absurd (h₃.trans h₄) (not_le.2 hr₂)
theorem isCompactWrt_of_closed_subset {Z W : Set α} (hZ : MetricNotions.IsCompactWrt d Z)
    (hW : MetricNotions.IsClosedWrt d W) (h : W ⊆ Z) : MetricNotions.IsCompactWrt d W := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
theorem isCompactWrt_union {A B : Set α} (hA : MetricNotions.IsCompactWrt d A)
    (hB : MetricNotions.IsCompactWrt d B) : MetricNotions.IsCompactWrt d (A ∪ B) := by apply _root_.YangMills.SharedProofs.p57694 <;> assumption
theorem isCompactWrt_biUnion_list {β : Type*} (L : List β) (g : β → Set α)
    (h : ∀ f ∈ L, MetricNotions.IsCompactWrt d (g f)) :
    MetricNotions.IsCompactWrt d (⋃ f ∈ L, g f) := by
  induction L with
  | nil =>
    intro 𝒰 _ _
    exact ⟨∅, Set.empty_subset _, Set.finite_empty, by simp⟩
  | cons a L ih =>
    have e : (⋃ f ∈ a :: L, g f) = g a ∪ ⋃ f ∈ L, g f := by
      ext x
      simp
    rw [e]
    exact isCompactWrt_union (h a (by simp))
      (ih fun f hf => h f (List.mem_cons_of_mem a hf))
theorem exists_dist_bound (hd : FamilyTopology.IsMetricFunction d) {Z : Set α}
    (hZ : MetricNotions.IsCompactWrt d Z) (o : α) : ∃ R : ℝ, ∀ z ∈ Z, d o z ≤ R := by
  obtain ⟨𝒱, h𝒱, hf, hc⟩ := hZ (Set.range fun n : ℕ => {y | d o y < n})
    (by
      rintro _ ⟨n, rfl⟩ x hx
      refine ⟨n - d o x, sub_pos.2 hx, fun y hy => ?_⟩
      have h₁ := hd.triangle o x y
      show d o y < n
      linarith)
    (by
      intro z _
      obtain ⟨n, hn⟩ := exists_nat_gt (d o z)
      exact ⟨_, ⟨n, rfl⟩, hn⟩)
  choose! n hn using fun U (h : U ∈ 𝒱) => h𝒱 h
  obtain ⟨N, hN⟩ := (hf.image n).bddAbove
  refine ⟨N, fun z hz => ?_⟩
  obtain ⟨U, hU, hzU⟩ := hc hz
  rw [← hn U hU] at hzU
  have h₁ : n U ≤ N := hN ⟨U, hU, rfl⟩
  have h₂ : (n U : ℝ) ≤ N := by exact_mod_cast h₁
  exact (le_of_lt hzU).trans h₂
theorem le_setGap_thickenings (hd : FamilyTopology.IsMetricFunction d) {B B' : Set α} {η : ℝ}
    (hη : 0 ≤ η) (h : ∀ b ∈ B, ∀ b' ∈ B', 3 * η ≤ d b b') :
    ENNReal.ofReal η ≤
      setGap d {x | setGap d {x} B ≤ ENNReal.ofReal η} {x | setGap d {x} B' ≤ ENNReal.ofReal η} := by
  refine le_setGap fun x hx x' hx' => ?_
  by_contra hcon
  push Not at hcon
  have hε : 0 < (η - d x x') / 2 := by linarith
  obtain ⟨b, hb, h₁⟩ := exists_close_of_setGap_le hη hε hx
  obtain ⟨b', hb', h₂⟩ := exists_close_of_setGap_le hη hε hx'
  have h₃ := h b hb b' hb'
  have h₄ := hd.triangle b x b'
  have h₅ := hd.triangle x x' b'
  have h₆ := hd.symm b x
  linarith
theorem le_setGap_thickening_left (hd : FamilyTopology.IsMetricFunction d) {B A : Set α} {η : ℝ}
    (hη : 0 ≤ η) (h : ∀ b ∈ B, ∀ x' ∈ A, 6 * η ≤ d x' b) :
    ENNReal.ofReal η ≤ setGap d {x | setGap d {x} B ≤ ENNReal.ofReal η} A := by
  refine le_setGap fun x hx x' hx' => ?_
  by_contra hcon
  push Not at hcon
  have hpos : 0 < η := (hd.nonneg x x').trans_lt hcon
  obtain ⟨b, hb, h₁⟩ := exists_close_of_setGap_le hη hpos hx
  have h₃ := h b hb x' hx'
  have h₄ := hd.triangle x' x b
  have h₆ := hd.symm x x'
  linarith
end Distance
section Lists
variable {β γ : Type*}
theorem forall₂_map_of_forall {ι : Type*} {R : β → γ → Prop} (u : ι → β) (v : ι → γ) (L : List ι)
    (h : ∀ f ∈ L, R (u f) (v f)) : List.Forall₂ R (L.map u) (L.map v) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons a L ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih fun f hf => h f (List.mem_cons_of_mem a hf))
theorem forall₂_append' {R : β → γ → Prop} {a c : List β} {b e : List γ}
    (h₁ : List.Forall₂ R a b) (h₂ : List.Forall₂ R c e) : List.Forall₂ R (a ++ c) (b ++ e) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact List.Forall₂.cons h ih
theorem exists_mem_of_forall₂ {R : β → γ → Prop} {a : List β} {b : List γ}
    (h : List.Forall₂ R a b) {g : β} (hg : g ∈ a) : ∃ A ∈ b, R g A := by
  induction h with
  | nil => simp at hg
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.1 hg with rfl | h₁
    · exact ⟨y, by simp, hxy⟩
    · obtain ⟨A, hA, hR⟩ := ih h₁
      exact ⟨A, List.mem_cons_of_mem y hA, hR⟩
theorem pairwise_of_forall₂' {R : β → γ → Prop} {T : γ → γ → Prop} {S : β → β → Prop}
    (hS : ∀ {g A g' A'}, R g A → R g' A' → T A A' → S g g') {a : List β} {b : List γ}
    (h : List.Forall₂ R a b) (hb : b.Pairwise T) : a.Pairwise S := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons x y _ _ hxy htl ih =>
    obtain ⟨h₁, h₂⟩ := List.pairwise_cons.1 hb
    refine List.pairwise_cons.2 ⟨fun g' hg' => ?_, ih h₂⟩
    obtain ⟨A', hA', hR⟩ := exists_mem_of_forall₂ htl hg'
    exact hS hxy hR (h₁ A' hA')
end Lists
section Numbers
theorem third_min_props {δ t : ℝ≥0∞} (hδ : 0 < δ) (ht : 0 < t) :
    0 < (min 1 (min δ t)).toReal / 3 ∧ (min 1 (min δ t)).toReal / 3 ≤ 1 / 3 ∧
      ENNReal.ofReal (3 * ((min 1 (min δ t)).toReal / 3)) ≤ δ ∧
      ENNReal.ofReal (3 * ((min 1 (min δ t)).toReal / 3)) ≤ t := by
  have hm1 : min 1 (min δ t) ≤ 1 := min_le_left _ _
  have hm0 : 0 < min 1 (min δ t) := lt_min one_pos (lt_min hδ ht)
  have hmt : min 1 (min δ t) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hm1
  have hpos := ENNReal.toReal_pos hm0.ne' hmt
  have hle : (min 1 (min δ t)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hm1
  have e : ENNReal.ofReal (3 * ((min 1 (min δ t)).toReal / 3)) = min 1 (min δ t) := by
    rw [mul_div_cancel₀ _ (three_ne_zero : (3 : ℝ) ≠ 0), ENNReal.ofReal_toReal hmt]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [e]
    exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [e]
    exact (min_le_right _ _).trans (min_le_right _ _)
theorem euclidNormVec_smul_stdBasisVec (t : ℝ) (μ : Fin 4) :
    TorusMetric.euclidNormVec (t • LimitSpaces.stdBasisVec μ) = |t| := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.euclidNormVec_smul_stdBasisVec <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem abs_apply_le_euclidDistR4 (x : Fin 4 → ℝ) (μ : Fin 4) :
    |x μ| ≤ TestFunctions.euclidDistR4 0 x := by
  have h := abs_apply_le_euclidNormVec (0 - x) μ
  have e : (0 - x) μ = -x μ := by simp
  rw [e, abs_neg] at h
  exact h
end Numbers
section FourSpace
theorem isCompactWrt_of_isCompact {d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ}
    (hc : ∀ x, Continuous (d x)) (h0 : ∀ x, d x x = 0) {Z : Set (Fin 4 → ℝ)} (hZ : IsCompact Z) :
    MetricNotions.IsCompactWrt d Z := by
  intro 𝒰 hU hcov
  have hopen : ∀ U ∈ 𝒰, IsOpen U := fun U hU' => by
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨r, hr, h⟩ := hU U hU' x hx
    have h₁ : {y | d x y < r} ∈ nhds x :=
      (isOpen_lt (hc x) continuous_const).mem_nhds (by simpa [h0 x] using hr)
    exact Filter.mem_of_superset h₁ fun y hy => h y hy
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun U : 𝒰 => (U : Set (Fin 4 → ℝ)))
    (fun U => hopen U U.2)
    (by
      intro x hx
      obtain ⟨U, hU₁, hx₁⟩ := hcov hx
      exact Set.mem_iUnion.2 ⟨⟨U, hU₁⟩, hx₁⟩)
  refine ⟨(fun U : 𝒰 => (U : Set (Fin 4 → ℝ))) '' (t : Set 𝒰), ?_, (t.finite_toSet).image _, ?_⟩
  · rintro _ ⟨U, -, rfl⟩
    exact U.2
  · intro x hx
    obtain ⟨U, hU₁, hx₁⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨U, ⟨U, hU₁, rfl⟩, hx₁⟩
theorem continuous_euclidDistR4 (x : Fin 4 → ℝ) : Continuous (TestFunctions.euclidDistR4 x) := by
  show Continuous fun y : Fin 4 → ℝ => Real.sqrt (∑ ν, (x ν - y ν) ^ 2)
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun ν _ => (continuous_const.sub (continuous_apply ν)).pow 2)
theorem isCompactWrt_cube (h0 : ∀ x, TestFunctions.euclidDistR4 x x = 0) (r : ℝ) :
    MetricNotions.IsCompactWrt TestFunctions.euclidDistR4
      (Set.pi Set.univ fun _ : Fin 4 => Set.Icc (-r) r) :=
  isCompactWrt_of_isCompact continuous_euclidDistR4 h0
    (isCompact_univ_pi fun _ => isCompact_Icc)
end FourSpace
section OnTheSpace
variable (D : MirrorData) (P : LimitSpaces.Ambient)
def radius (μ : Fin 4) (c : ℝ) (X Y : List (P.Carrier D.toStandingParameters → ℝ)) : ℝ :=
  (min 1 (min (P.infSetDist D.toStandingParameters
      (P.listSupport D.toStandingParameters X ∪ P.listSupport D.toStandingParameters Y)
      (Sides.hyperplane D P μ c)) (P.listGap D.toStandingParameters X))).toReal / 3
def imageThickening (θ : P.Carrier D.toStandingParameters → P.Carrier D.toStandingParameters)
    (η : ℝ) (f : P.Carrier D.toStandingParameters → ℝ) : Set (P.Carrier D.toStandingParameters) :=
  {x | P.infSetDist D.toStandingParameters {x} (θ '' P.closedSupport D.toStandingParameters f) ≤
    ENNReal.ofReal η}
def thickenedSupports (θ : P.Carrier D.toStandingParameters → P.Carrier D.toStandingParameters)
    (η : ℝ) (X Y : List (P.Carrier D.toStandingParameters → ℝ)) :
    List (Set (P.Carrier D.toStandingParameters)) :=
  X.map (imageThickening D P θ η) ++ Y.map (P.closedSupport D.toStandingParameters)
theorem isCompactSubset_thickening (hT : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hd : FamilyTopology.IsMetricFunction (P.pointDist D.toStandingParameters))
    {B : Set (P.Carrier D.toStandingParameters)} (hB : P.IsCompactSubset D.toStandingParameters B)
    {η : ℝ} (hη : 0 ≤ η) :
    P.IsCompactSubset D.toStandingParameters
      {x | P.infSetDist D.toStandingParameters {x} B ≤ ENNReal.ofReal η} := by
  have hcl : MetricNotions.IsClosedWrt (P.pointDist D.toStandingParameters)
      {x | P.infSetDist D.toStandingParameters {x} B ≤ ENNReal.ofReal η} :=
    isClosedWrt_thickening hd B hη
  cases P with
  | periodic =>
    have hU : MetricNotions.IsCompactWrt
        (LimitSpaces.Ambient.periodic.pointDist D.toStandingParameters) Set.univ :=
      (hT { D.toStandingParameters with coupling := D.β, coupling_pos := D.β_pos, dir := 0 }).1.2.2.2.2
    exact isCompactWrt_of_closed_subset hU hcl (Set.subset_univ _)
  | euclidean =>
    obtain ⟨R, hR⟩ := exists_dist_bound hd hB (0 : Fin 4 → ℝ)
    have h0 : ∀ x, TestFunctions.euclidDistR4 x x = 0 := fun x => (hd.eq_zero_iff x x).2 rfl
    refine isCompactWrt_of_closed_subset (isCompactWrt_cube h0 (R + η + 1)) hcl ?_
    intro x hx μ _
    obtain ⟨b, hb, hxb⟩ := exists_close_of_setGap_le hη one_pos hx
    have h₁ := hd.triangle 0 b x
    have h₂ := hR b hb
    have h₃ := hd.symm b x
    have h₄ : |x μ| ≤ LimitSpaces.Ambient.euclidean.pointDist D.toStandingParameters 0 x :=
      abs_apply_le_euclidDistR4 x μ
    have h₆ : LimitSpaces.Ambient.euclidean.pointDist D.toStandingParameters 0 b +
        LimitSpaces.Ambient.euclidean.pointDist D.toStandingParameters b x ≤ R + (η + 1) :=
      add_le_add h₂ (h₃.le.trans hxb.le)
    have h₅ : |x μ| ≤ R + (η + 1) := (h₄.trans h₁).trans h₆
    rw [← add_assoc] at h₅
    exact abs_le.1 h₅
theorem pointDist_proj_le
    (hπ : ∀ x y : Fin 4 → ℝ,
      LimitSpaces.Ambient.periodic.pointDist D.toStandingParameters
          (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x)
          (LimitSpaces.Ambient.periodic.proj D.toStandingParameters y) ≤
        TorusMetric.euclidNormVec (x - y))
    (v : Fin 4 → ℝ) :
    P.pointDist D.toStandingParameters (P.proj D.toStandingParameters v) 0 ≤
      TorusMetric.euclidNormVec v := by
  have h0 : P.proj D.toStandingParameters 0 = 0 :=
    (P.mem_periodGroup_iff D.toStandingParameters 0).1 (zero_mem _)
  cases P with
  | periodic =>
    have h₁ := hπ v 0
    rw [h0, sub_zero] at h₁
    exact h₁
  | euclidean =>
    show TorusMetric.euclidNormVec (v - 0) ≤ _
    rw [sub_zero]
theorem pairwise_listGap_le (X : List (P.Carrier D.toStandingParameters → ℝ)) :
    X.Pairwise fun f g => P.listGap D.toStandingParameters X ≤
      P.infSetDist D.toStandingParameters (P.closedSupport D.toStandingParameters f)
        (P.closedSupport D.toStandingParameters g) := by
  have key : ∀ p ∈ (Finset.univ.offDiag : Finset (Fin X.length × Fin X.length)),
      P.listGap D.toStandingParameters X ≤
        P.infSetDist D.toStandingParameters (P.closedSupport D.toStandingParameters (X.get p.1))
          (P.closedSupport D.toStandingParameters (X.get p.2)) := by
    cases P with
    | periodic => exact Finset.le_inf_iff.1 (le_refl _)
    | euclidean => exact Finset.le_inf_iff.1 (le_refl _)
  refine List.pairwise_iff_get.2 fun i j hij => ?_
  exact key (i, j) (Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hij.ne⟩)
theorem isSepLipList_of_disjoint
    (hlip : ∀ f ∈ P.c1Compact D.toStandingParameters, P.IsLip D.toStandingParameters f)
    {X : List (P.Carrier D.toStandingParameters → ℝ)}
    (hc : ∀ f ∈ X, f ∈ P.c1Compact D.toStandingParameters)
    (hdis : X.Pairwise fun f g =>
      Disjoint (P.closedSupport D.toStandingParameters f)
        (P.closedSupport D.toStandingParameters g)) :
    Sides.IsSepLipList D P X := by
  refine ⟨fun i => ⟨hlip _ (hc _ (List.get_mem _ _)), (hc _ (List.get_mem _ _)).2,
    Set.subset_univ _⟩, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact List.pairwise_iff_get.1 hdis i j h
  · exact (List.pairwise_iff_get.1 hdis j i h).symm
end OnTheSpace
section Core
variable {D : MirrorData} {P : LimitSpaces.Ambient}
theorem infSetDist_le_distToHyperplane {K : Set (P.Carrier D.toStandingParameters)} {μ : Fin 4}
    {c : ℝ} {x : P.Carrier D.toStandingParameters} (hx : x ∈ K) :
    P.infSetDist D.toStandingParameters K (Sides.hyperplane D P μ c) ≤
      Sides.distToHyperplane D P μ c x :=
  setGap_anti_left (d := P.pointDist D.toStandingParameters) (Set.singleton_subset_iff.2 hx)
theorem sharedSets_compact_apart (hM : Sides.HyperplaneSidesClaim)
    (hT : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    {μ : Fin 4} {c : ℝ}
    {θ : P.Carrier D.toStandingParameters → P.Carrier D.toStandingParameters}
    (hθ : θ = P.reflect D.toStandingParameters μ c)
    {X Y : List (P.Carrier D.toStandingParameters → ℝ)}
    (hXc : ∀ f ∈ X, f ∈ P.c1Compact D.toStandingParameters)
    (hXd : X.Pairwise fun f g =>
      Disjoint (P.closedSupport D.toStandingParameters f)
        (P.closedSupport D.toStandingParameters g))
    (hXp : ∀ f ∈ X, P.closedSupport D.toStandingParameters f ⊆ Sides.openHalf D P μ c)
    (hYc : ∀ f ∈ Y, f ∈ P.c1Compact D.toStandingParameters)
    (hYd : Y.Pairwise fun f g =>
      Disjoint (P.closedSupport D.toStandingParameters f)
        (P.closedSupport D.toStandingParameters g))
    (hYp : ∀ f ∈ Y, P.closedSupport D.toStandingParameters f ⊆ Sides.openHalf D P μ c) :
    0 < radius D P μ c X Y ∧ radius D P μ c X Y ≤ 1 / 3 ∧
      (∀ A ∈ thickenedSupports D P θ (radius D P μ c X Y) X Y,
        P.IsCompactSubset D.toStandingParameters A) ∧
      0 < min (ENNReal.ofReal (radius D P μ c X Y)) (P.listGap D.toStandingParameters Y) ∧
      (thickenedSupports D P θ (radius D P μ c X Y) X Y).Pairwise fun A B =>
        min (ENNReal.ofReal (radius D P μ c X Y)) (P.listGap D.toStandingParameters Y) ≤
          P.infSetDist D.toStandingParameters A B := by
  subst hθ
  obtain ⟨ha, -, hfar, hcomp, hsep, -, -⟩ := (hM D μ c).1 P
  obtain ⟨hd, -, -, hiso, -, hsupp, -, hC⟩ := ha
  have hlip : ∀ f ∈ P.c1Compact D.toStandingParameters, P.IsLip D.toStandingParameters f :=
    fun f hf => (hC f hf).2.2
  have hK : P.IsCompactSubset D.toStandingParameters
      (P.listSupport D.toStandingParameters X ∪ P.listSupport D.toStandingParameters Y) :=
    isCompactWrt_union
      (isCompactWrt_biUnion_list X (P.closedSupport D.toStandingParameters)
        fun f hf => (hXc f hf).2)
      (isCompactWrt_biUnion_list Y (P.closedSupport D.toStandingParameters)
        fun f hf => (hYc f hf).2)
  have hKsub : P.listSupport D.toStandingParameters X ∪ P.listSupport D.toStandingParameters Y ⊆
      Sides.openHalf D P μ c := by
    refine Set.union_subset (Set.iUnion₂_subset hXp) (Set.iUnion₂_subset hYp)
  have hδ := (hcomp _ hK hKsub).1
  have hsX := hsep.2 X (isSepLipList_of_disjoint D P hlip hXc hXd)
  have hsY := hsep.2 Y (isSepLipList_of_disjoint D P hlip hYc hYd)
  obtain ⟨hη0, hη3, h3δ, h3s⟩ := third_min_props hδ hsX
  change 0 < radius D P μ c X Y at hη0
  change radius D P μ c X Y ≤ 1 / 3 at hη3
  change ENNReal.ofReal (3 * radius D P μ c X Y) ≤ _ at h3δ
  change ENNReal.ofReal (3 * radius D P μ c X Y) ≤ _ at h3s
  generalize radius D P μ c X Y = η at *
  have hpos : 0 < min (ENNReal.ofReal η) (P.listGap D.toStandingParameters Y) :=
    lt_min (ENNReal.ofReal_pos.2 hη0) hsY
  refine ⟨hη0, hη3, ?_, hpos, ?_⟩
  · intro A hA
    rcases List.mem_append.1 hA with h | h
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 h
      have hB : P.IsCompactSubset D.toStandingParameters
          (P.reflect D.toStandingParameters μ c '' P.closedSupport D.toStandingParameters f) := by
        rw [← (hsupp ℝ f 0).1]
        exact (hC f (hXc f hf)).1.2
      exact isCompactSubset_thickening D P hT hd hB hη0.le
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 h
      exact (hYc f hf).2
  · refine List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, List.pairwise_map.2 ?_, ?_⟩
    · refine (pairwise_listGap_le D P X).imp fun {f g} hfg => ?_
      refine (min_le_left _ _).trans ?_
      refine le_setGap_thickenings hd hη0.le ?_
      rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      rw [hiso]
      have h₁ : ENNReal.ofReal (3 * η) ≤
          ENNReal.ofReal (P.pointDist D.toStandingParameters y y') :=
        (h3s.trans hfg).trans (setGap_le hy hy')
      exact (ENNReal.ofReal_le_ofReal_iff (hd.nonneg _ _)).1 h₁
    · exact (pairwise_listGap_le D P Y).imp fun {f g} hfg => (min_le_right _ _).trans hfg
    · intro A hA B hB
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hA
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hB
      refine (min_le_left _ _).trans ?_
      refine le_setGap_thickening_left hd hη0.le ?_
      rintro _ ⟨y, hy, rfl⟩ x' hx'
      have hy₁ : y ∈ P.listSupport D.toStandingParameters X ∪
          P.listSupport D.toStandingParameters Y :=
        Or.inl (Set.mem_iUnion₂.2 ⟨f, hf, hy⟩)
      have hx₁ : x' ∈ P.listSupport D.toStandingParameters X ∪
          P.listSupport D.toStandingParameters Y :=
        Or.inr (Set.mem_iUnion₂.2 ⟨g, hg, hx'⟩)
      have h₁ := hfar x' (hKsub hx₁) y (hKsub hy₁)
      have h₂ := h3δ.trans (infSetDist_le_distToHyperplane (μ := μ) (c := c) hx₁)
      have h₃ := h3δ.trans (infSetDist_le_distToHyperplane (μ := μ) (c := c) hy₁)
      have h₄ : ENNReal.ofReal (3 * η + 3 * η) ≤ ENNReal.ofReal
          (P.pointDist D.toStandingParameters x' (P.reflect D.toStandingParameters μ c y)) := by
        rw [ENNReal.ofReal_add (by linarith) (by linarith)]
        exact (add_le_add h₂ h₃).trans h₁
      have h₅ := (ENNReal.ofReal_le_ofReal_iff (hd.nonneg _ _)).1 h₄
      linarith
end Core
section Moved
variable {D : MirrorData} {P : LimitSpaces.Ambient}
theorem moved_list_supported (hM : Sides.HyperplaneSidesClaim)
    (hMove : LimitSpaces.MirrorTranslation.Claim)
    {μ : Fin 4} {c c' η : ℝ}
    {θ θ' : P.Carrier D.toStandingParameters → P.Carrier D.toStandingParameters}
    (hθ : θ = P.reflect D.toStandingParameters μ c)
    (hθ' : θ' = P.reflect D.toStandingParameters μ c')
    {X Y : List (P.Carrier D.toStandingParameters → ℝ)}
    (hXc : ∀ f ∈ X, f ∈ P.c1Compact D.toStandingParameters)
    (hYc : ∀ f ∈ Y, f ∈ P.c1Compact D.toStandingParameters)
    {r : ℝ≥0∞} (hr : 0 < r)
    (hpw : (thickenedSupports D P θ η X Y).Pairwise fun A B =>
      r ≤ P.infSetDist D.toStandingParameters A B)
    (hc : 2 * |c' - c| ≤ η) :
    List.Forall₂ (fun g A => P.SupportedWithin D.toStandingParameters A g)
        (X.map (fun f => f ∘ θ') ++ Y) (thickenedSupports D P θ η X Y) ∧
      (X.map (fun f => f ∘ θ') ++ Y).Pairwise (fun f g =>
        Disjoint (P.closedSupport D.toStandingParameters f)
          (P.closedSupport D.toStandingParameters g)) ∧
      ∀ g ∈ X.map (fun f => f ∘ θ') ++ Y, g ∈ P.c1Compact D.toStandingParameters := by
  subst hθ hθ'
  obtain ⟨ha, -, -, -, -, -, -⟩ := (hM D μ c).1 P
  obtain ⟨hd, hπ, htr, -, -, hsupp, -, -⟩ := ha
  obtain ⟨ha', -, -, -, -, -, -⟩ := (hM D μ c').1 P
  have hC' := ha'.2.2.2.2.2.2.2
  have hX : ∀ f ∈ X, P.SupportedWithin D.toStandingParameters
      (imageThickening D P (P.reflect D.toStandingParameters μ c) η f)
      (f ∘ P.reflect D.toStandingParameters μ c') := by
    intro f hf
    refine ⟨(hC' f (hXc f hf)).1.2, ?_⟩
    intro x hx
    have hmv := ((hMove D.toStandingParameters ⟨1, Set.mem_Ici.2 le_rfl⟩ P μ).1 c c' 0 f).1
    have hx' : x ∈ P.closedSupport D.toStandingParameters
        (P.reflectFun D.toStandingParameters μ c' f) := hx
    rw [hmv] at hx'
    have e := (hsupp ℝ (P.reflectFun D.toStandingParameters μ c f)
      (P.proj D.toStandingParameters ((2 * (c' - c)) • LimitSpaces.stdBasisVec μ))).2
    change x ∈ P.closedSupport D.toStandingParameters
      (P.translateFun D.toStandingParameters _ _) at hx'
    rw [e] at hx'
    obtain ⟨b, hb, rfl⟩ := hx'
    rw [(hsupp ℝ f 0).1] at hb
    refine (setGap_le (d := P.pointDist D.toStandingParameters) (Set.mem_singleton _) hb).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h₁ : P.pointDist D.toStandingParameters
        (P.proj D.toStandingParameters ((2 * (c' - c)) • LimitSpaces.stdBasisVec μ) + b)
        (0 + b) = P.pointDist D.toStandingParameters
          (P.proj D.toStandingParameters ((2 * (c' - c)) • LimitSpaces.stdBasisVec μ)) 0 :=
      htr b _ 0
    rw [zero_add, add_comm] at h₁
    rw [h₁]
    refine (pointDist_proj_le D P hπ _).trans ?_
    rw [euclidNormVec_smul_stdBasisVec, abs_mul, abs_two]
    exact hc
  have hY : List.Forall₂ (fun g A => P.SupportedWithin D.toStandingParameters A g) Y
      (Y.map (P.closedSupport D.toStandingParameters)) := by
    have h₁ := forall₂_map_of_forall
      (R := fun g A => P.SupportedWithin D.toStandingParameters A g) id
      (P.closedSupport D.toStandingParameters) Y fun f hf => ⟨(hYc f hf).2, subset_rfl⟩
    rwa [List.map_id] at h₁
  have hF : List.Forall₂ (fun g A => P.SupportedWithin D.toStandingParameters A g)
      (X.map (fun f => f ∘ P.reflect D.toStandingParameters μ c') ++ Y)
      (thickenedSupports D P (P.reflect D.toStandingParameters μ c) η X Y) :=
    forall₂_append' (forall₂_map_of_forall _ _ X hX) hY
  refine ⟨hF, ?_, ?_⟩
  · exact pairwise_of_forall₂' (fun hg hg' hT =>
      (disjoint_of_setGap_pos hd (hr.trans_le hT)).mono hg.2 hg'.2) hF hpw
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 h
      exact (hC' f (hXc f hf)).1
    · exact hYc g h
end Moved
theorem isSeparatedList_of_mem {D : MirrorData} {E : Ambient} {Z : Ambient.FnList D E}
    (h : Z ∈ Ambient.separatedAll D E) : Ambient.IsSeparatedList D E Z := by apply _root_.YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient.isSeparatedList_of_mem_separatedAll <;> assumption
theorem get_rel_of_pairwise {β : Type*} {R : β → β → Prop} (hR : ∀ {a b}, R a b → R b a)
    {L : List β} (h : L.Pairwise R) (l l' : Fin L.length) (hne : l ≠ l') :
    R (L.get l) (L.get l') := by
  rcases lt_or_gt_of_ne hne with h₁ | h₁
  · exact List.pairwise_iff_get.1 h l l' h₁
  · exact hR (List.pairwise_iff_get.1 h l' l h₁)
theorem le_infSetDist_symm {D : MirrorData} {P : LimitSpaces.Ambient}
    (hM : Sides.HyperplaneSidesClaim) {r : ℝ≥0∞} {A B : Set (P.Carrier D.toStandingParameters)}
    (h : r ≤ P.infSetDist D.toStandingParameters A B) :
    r ≤ P.infSetDist D.toStandingParameters B A :=
  h.trans (setGap_comm_le ((hM D 0 0).1 P).1.1 A B)
theorem sharedSetsProperties_holds (h₁ : Sides.HyperplaneSidesClaim)
    (h₂ : LimitSpaces.MirrorTranslation.Claim)
    (h₃ : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    SharedSetsProperties := by
  intro D E μ c X Y hX hY
  have hXs := isSeparatedList_of_mem hX.1
  have hYs := isSeparatedList_of_mem hY.1
  cases E with
  | torus =>
    have hθ := Sides.reflect_torus D μ c
    obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := sharedSets_compact_apart (P := .periodic) h₁ h₃ hθ hXs.1
      hXs.2 hX.2 hYs.1 hYs.2 hY.2
    refine ⟨⟨a₁, a₂, a₃, a₄, get_rel_of_pairwise (le_infSetDist_symm (P := .periodic) h₁) a₅⟩,
      fun c' hc' => ?_, fun K' β' hβ => ⟨rfl, rfl⟩⟩
    obtain ⟨b₁, b₂, b₃⟩ := moved_list_supported (P := .periodic) h₁ h₂ hθ
      (Sides.reflect_torus D μ c') hXs.1 hYs.1 a₄ a₅ hc'
    exact ⟨b₁, by simp [CoordMirror.reflectAppend, Ambient.append, CoordMirror.reflectList],
      b₃, b₂⟩
  | euclidean =>
    have hθ := Sides.reflect_euclidean D μ c
    obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := sharedSets_compact_apart (P := .euclidean) h₁ h₃ hθ hXs.1
      hXs.2 hX.2 hYs.1 hYs.2 hY.2
    refine ⟨⟨a₁, a₂, a₃, a₄, get_rel_of_pairwise (le_infSetDist_symm (P := .euclidean) h₁) a₅⟩,
      fun c' hc' => ?_, fun K' β' hβ => ⟨rfl, rfl⟩⟩
    obtain ⟨b₁, b₂, b₃⟩ := moved_list_supported (P := .euclidean) h₁ h₂ hθ
      (Sides.reflect_euclidean D μ c') hXs.1 hYs.1 a₄ a₅ hc'
    exact ⟨b₁, by simp [CoordMirror.reflectAppend, Ambient.append, CoordMirror.reflectList],
      b₃, b₂⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirrorSets
end
