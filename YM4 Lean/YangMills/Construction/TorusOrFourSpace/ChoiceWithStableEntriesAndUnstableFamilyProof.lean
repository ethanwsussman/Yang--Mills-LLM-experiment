import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegionsProof
import YangMills.Construction.TorusOrFourSpace.BoundOnTheDiameterBearsOnBoxesNotOnUnions
import YangMills.Construction.TorusOrFourSpace.ChoiceWithStableEntriesAndUnstableFamily
import YangMills.Construction.TorusOrFourSpace.CountableClosedSaturatedChoicesAndTheirFamily
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.DisjointMembersOfTheStock
import YangMills.Construction.TorusOrFourSpace.GroupOfAdicIsometriesAndItsActions
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import YangMills.Construction.TorusOrFourSpace.SpacesC1OfTheStock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.StableEntriesUnstableFamily
open PeriodicLattice (SignedFrame)
open Kind SupportAdapted
theorem mem_outerBox_toSet {x : Fin 4 → ℝ} :
    x ∈ outerBox.toSet ↔ ∀ μ, 1 / 4 ≤ x μ ∧ x μ ≤ 1 / 2 := by
  simp only [RationalBox.toSet, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
  norm_num [outerBox]
theorem leftSlab_subset_outerBox : leftSlab.toSet ⊆ outerBox.toSet := by
  intro x hx
  rw [mem_outerBox_toSet]
  intro μ
  have h := hx μ (Set.mem_univ μ)
  fin_cases μ <;> norm_num [leftSlab] at h ⊢ <;> constructor <;> linarith [h.1, h.2]
theorem rightSlab_subset_outerBox : rightSlab.toSet ⊆ outerBox.toSet := by
  intro x hx
  rw [mem_outerBox_toSet]
  intro μ
  have h := hx μ (Set.mem_univ μ)
  fin_cases μ <;> norm_num [rightSlab] at h ⊢ <;> constructor <;> linarith [h.1, h.2]
theorem leftSlab_coord_zero_le {x : Fin 4 → ℝ} (hx : x ∈ leftSlab.toSet) : x 0 ≤ 5 / 16 := by
  have h := hx 0 (Set.mem_univ 0)
  norm_num [leftSlab] at h
  linarith [h.2]
theorem le_rightSlab_coord_zero {x : Fin 4 → ℝ} (hx : x ∈ rightSlab.toSet) : 3 / 8 ≤ x 0 := by
  have h := hx 0 (Set.mem_univ 0)
  norm_num [rightSlab] at h
  linarith [h.1]
theorem one_le_L_pow_m (D : Params) : (1 : ℝ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := by
  have hL : (1 : ℝ) ≤ (D.L : ℝ) := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  exact one_le_pow₀ hL
theorem two_le_side (D : Params) : (2 : ℝ) ≤ D.side := by
  have := one_le_L_pow_m D
  simp only [Params.side, PeriodicLattice.torusSide]
  linarith
theorem outerBox_diam_le : outerBox.diam ≤ 1 / 2 := by
  simp only [RationalBox.diam, TorusMetric.euclidNormVec]
  rw [Real.sqrt_le_iff]
  norm_num [outerBox, Fin.sum_univ_four]
theorem leftSlab_diam_le : leftSlab.diam ≤ 1 / 2 := by
  simp only [RationalBox.diam, TorusMetric.euclidNormVec]
  rw [Real.sqrt_le_iff]
  have e2 : (![5 / 16, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℚ) 2 = 1 / 2 := rfl
  have e3 : (![5 / 16, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℚ) 3 = 1 / 2 := rfl
  norm_num [leftSlab, Fin.sum_univ_four, e2, e3]
theorem rightSlab_diam_le : rightSlab.diam ≤ 1 / 2 := by
  simp only [RationalBox.diam, TorusMetric.euclidNormVec]
  rw [Real.sqrt_le_iff]
  have e2 : (![3 / 8, 1 / 4, 1 / 4, 1 / 4] : Fin 4 → ℚ) 2 = 1 / 4 := rfl
  have e3 : (![3 / 8, 1 / 4, 1 / 4, 1 / 4] : Fin 4 → ℚ) 3 = 1 / 4 := rfl
  norm_num [rightSlab, Fin.sum_univ_four, e2, e3]
theorem admitsBox_of_diam_le (D : Params) (E : Kind) {b : RationalBox} (hb : b.diam ≤ 1 / 2) :
    E.AdmitsBox D b := by
  cases E with
  | euclidean => trivial
  | torus =>
    show b.diam < D.side / 2
    have := two_le_side D
    linarith
variable (D : Params) (E : Kind)
theorem boxImage_mem_supportStock {b : RationalBox} (hb : E.AdmitsBox D b) :
    boxImage D E b ∈ supportStock D E := ⟨1, fun _ => b, fun _ => hb, (Set.iUnion_const _).symm⟩
theorem quotMap_injOn_outerBox (hbox : TorusBoxDiameterBound) :
    Set.InjOn (E.quotMap D) outerBox.toSet := by
  cases E with
  | euclidean =>
    intro x _ y _ h
    exact h
  | torus =>
    exact ((hbox D).2.2.1 outerBox (admitsBox_of_diam_le D torus outerBox_diam_le)).2.1
def lineBump (c t : ℝ) : ℝ := expNegInvGlue ((1 / 32) ^ 2 - (t - c) ^ 2)
theorem lineBump_contDiff (c : ℝ) : ContDiff ℝ 1 (lineBump c) := by
  unfold lineBump
  exact expNegInvGlue.contDiff.comp (by fun_prop)
theorem lineBump_self_ne_zero (c : ℝ) : lineBump c c ≠ 0 := by
  unfold lineBump
  exact (expNegInvGlue.pos_of_pos (by norm_num)).ne'
theorem abs_sub_lt_of_lineBump_ne_zero {c t : ℝ} (h : lineBump c t ≠ 0) : |t - c| < 1 / 32 := by
  by_contra hc
  apply h
  unfold lineBump
  apply expNegInvGlue.zero_of_nonpos
  have h1 : (1 / 32 : ℝ) ≤ |t - c| := not_lt.mp hc
  have h2 : (1 / 32 : ℝ) ^ 2 ≤ |t - c| ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  rw [sq_abs] at h2
  linarith
def circleBump (S c t : ℝ) : ℝ :=
  expNegInvGlue (Real.cos (2 * Real.pi * (t - c) / S) - Real.cos (2 * Real.pi * (1 / 32) / S))
theorem circleBump_contDiff (S c : ℝ) : ContDiff ℝ 1 (circleBump S c) := by
  unfold circleBump
  refine expNegInvGlue.contDiff.comp (ContDiff.sub ?_ contDiff_const)
  exact Real.contDiff_cos.comp (by fun_prop)
theorem circleBump_periodic {S : ℝ} (hS : 2 ≤ S) (c : ℝ) :
    Function.Periodic (circleBump S c) S := by
  intro t
  unfold circleBump
  have hne : S ≠ 0 := by linarith
  have : 2 * Real.pi * (t + S - c) / S = 2 * Real.pi * (t - c) / S + 2 * Real.pi := by
    field_simp
    ring
  rw [this, Real.cos_add_two_pi]
theorem circleBump_self_ne_zero {S : ℝ} (hS : 2 ≤ S) (c : ℝ) : circleBump S c c ≠ 0 := by
  unfold circleBump
  have hSpos : 0 < S := by linarith
  refine (expNegInvGlue.pos_of_pos ?_).ne'
  have hρ : 0 < 2 * Real.pi * (1 / 32) / S := by positivity
  have hρ' : 2 * Real.pi * (1 / 32) / S ≤ Real.pi := by
    rw [div_le_iff₀ hSpos]
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hρ' hρ
  simp only [sub_self, mul_zero, zero_div]
  linarith
theorem exists_abs_sub_lt_of_circleBump_ne_zero {S : ℝ} (hS : 2 ≤ S) {c t : ℝ}
    (h : circleBump S c t ≠ 0) : ∃ k : ℤ, |t - c - k * S| < 1 / 32 := by
  have hSpos : 0 < S := by linarith
  have hne : S ≠ 0 := hSpos.ne'
  refine ⟨round ((t - c) / S), ?_⟩
  set k : ℤ := round ((t - c) / S) with hk
  set s : ℝ := (t - c) / S - k with hs
  have hs2 : |s| ≤ 1 / 2 := abs_sub_round _
  have hts : t - c - k * S = s * S := by
    rw [hs]
    field_simp
  have hθ : Real.cos (2 * Real.pi * (t - c) / S) = Real.cos (2 * Real.pi * |s|) := by
    have h1 : 2 * Real.pi * (t - c) / S = 2 * Real.pi * s + k * (2 * Real.pi) := by
      rw [hs]
      field_simp
      ring
    rw [h1, Real.cos_add_int_mul_two_pi]
    rcases abs_cases s with ⟨h2, _⟩ | ⟨h2, _⟩
    · rw [h2]
    · rw [h2, mul_neg, Real.cos_neg]
  have hlt : Real.cos (2 * Real.pi * (1 / 32) / S) < Real.cos (2 * Real.pi * |s|) := by
    by_contra hc
    apply h
    unfold circleBump
    apply expNegInvGlue.zero_of_nonpos
    rw [hθ]
    linarith [not_lt.mp hc]
  have hρ : 2 * Real.pi * |s| < 2 * Real.pi * (1 / 32) / S := by
    by_contra hc
    have hρ0 : 0 ≤ 2 * Real.pi * (1 / 32) / S := by positivity
    have hle : 2 * Real.pi * |s| ≤ Real.pi := by nlinarith [Real.pi_pos]
    exact absurd (Real.cos_le_cos_of_nonneg_of_le_pi hρ0 hle (not_lt.mp hc)) (not_le.mpr hlt)
  have h3 : |s| * S < 1 / 32 := by
    have h4 : 2 * Real.pi * (|s| * S) < 2 * Real.pi * (1 / 32) := by
      have := (lt_div_iff₀ hSpos).mp hρ
      linarith
    exact lt_of_mul_lt_mul_left h4 (by positivity)
  rw [hts, abs_mul, abs_of_pos hSpos]
  exact h3
theorem mem_toSet_of_close {b : RationalBox} {c x : Fin 4 → ℝ}
    (hc : ∀ μ, (b.lo μ : ℝ) ≤ c μ - 1 / 32 ∧ c μ + 1 / 32 ≤ (b.hi μ : ℝ))
    (hx : ∀ μ, |x μ - c μ| < 1 / 32) : x ∈ b.toSet := by
  intro μ _
  have h := abs_lt.mp (hx μ)
  exact ⟨by linarith [(hc μ).1, h.1], by linarith [(hc μ).2, h.2]⟩
theorem exists_c1_boxImage_ne_zero (hw : WellPosedness.WellPosed) {b : RationalBox}
    {c : Fin 4 → ℝ}
    (hc : ∀ μ, (b.lo μ : ℝ) ≤ c μ - 1 / 32 ∧ c μ + 1 / 32 ≤ (b.hi μ : ℝ)) :
    ∃ u ∈ c1VanishingOutside D E (boxImage D E b), u ≠ 0 := by
  cases E with
  | euclidean =>
    let u : (Fin 4 → ℝ) → ℝ := fun x => ∏ μ, lineBump (c μ) (x μ)
    have hu : ContDiff ℝ 1 u :=
      contDiff_prod fun μ _ => (lineBump_contDiff (c μ)).comp (contDiff_apply ℝ ℝ μ)
    refine ⟨u, ⟨hu, fun y hy => ?_⟩, fun h0 => ?_⟩
    · by_contra hne
      apply hy
      refine ⟨y, mem_toSet_of_close hc fun μ => ?_, rfl⟩
      exact abs_sub_lt_of_lineBump_ne_zero (Finset.prod_ne_zero_iff.mp hne μ (Finset.mem_univ μ))
    · have h1 : u c = 0 := congrFun h0 c
      exact (Finset.prod_ne_zero_iff.mpr fun μ _ => lineBump_self_ne_zero (c μ)) h1
  | torus =>
    have hS := two_le_side D
    let H : (Fin 4 → ℝ) → ℝ := fun x => ∏ μ, circleBump D.side (c μ) (x μ)
    have hH : ContDiff ℝ 1 H :=
      contDiff_prod fun μ _ => (circleBump_contDiff D.side (c μ)).comp (contDiff_apply ℝ ℝ μ)
    let u : D.Torus → ℝ := fun y => ∏ μ, (circleBump_periodic hS (c μ)).lift (y μ)
    have huH : ∀ x, u (quotMap D torus x) = H x := by
      intro x
      refine Finset.prod_congr rfl fun μ _ => ?_
      exact Function.Periodic.lift_coe _ _
    obtain ⟨hadd, hsurj, hker⟩ := (hw D torus).1
    refine ⟨u, ⟨?_, fun y hy => ?_⟩, fun h0 => ?_⟩
    · have : u ∘ quotMap D torus = H := funext huH
      show ContDiff ℝ 1 (u ∘ quotMap D torus)
      rw [this]
      exact hH
    · by_contra hne
      apply hy
      obtain ⟨x, rfl⟩ := hsurj y
      rw [huH] at hne
      have hfac := fun μ => Finset.prod_ne_zero_iff.mp hne μ (Finset.mem_univ μ)
      choose k hk using fun μ => exists_abs_sub_lt_of_circleBump_ne_zero hS (hfac μ)
      let p : Fin 4 → ℝ := fun μ => (k μ : ℝ) * D.side
      have hp : p ∈ periodGroup D torus := ⟨k, fun _ => rfl⟩
      refine ⟨x - p, mem_toSet_of_close hc fun μ => ?_, ?_⟩
      · have := hk μ
        have e : (x - p) μ - c μ = x μ - c μ - (k μ : ℝ) * D.side := by
          simp only [Pi.sub_apply, p]
          ring
        rw [e]
        exact this
      · have h1 := hadd (x - p) p
        rw [(hker p).mpr hp, add_zero, sub_add_cancel] at h1
        exact h1.symm
    · have h1 : u (quotMap D torus c) = 0 := congrFun h0 _
      rw [huH] at h1
      exact (Finset.prod_ne_zero_iff.mpr fun μ _ => circleBump_self_ne_zero hS (c μ)) h1
theorem exists_c1_leftSlab (hw : WellPosedness.WellPosed) :
    ∃ u ∈ c1VanishingOutside D E (boxImage D E leftSlab), u ≠ 0 := by
  refine exists_c1_boxImage_ne_zero D E hw (c := ![9 / 32, 3 / 8, 3 / 8, 3 / 8]) fun μ => ?_
  fin_cases μ <;> norm_num [leftSlab]
theorem exists_c1_rightSlab (hw : WellPosedness.WellPosed) :
    ∃ u ∈ c1VanishingOutside D E (boxImage D E rightSlab), u ≠ 0 := by
  refine exists_c1_boxImage_ne_zero D E hw (c := ![7 / 16, 3 / 8, 3 / 8, 3 / 8]) fun μ => ?_
  fin_cases μ <;> norm_num [rightSlab]
theorem quotDist_self (hw : WellPosedness.WellPosed) (y : E.Pt D) :
    quotDist D E y y = 0 := by
  obtain ⟨x, rfl⟩ := (hw D E).1.2.1 y
  obtain ⟨⟨k, -, hk⟩, hmin⟩ := (hw D E).2.2.2.2.2.2.1 x x
  have h0 : (0 : ℝ) ∈ WellPosedness.translateNorms D E x x :=
    ⟨0, zero_mem _, by simp [TorusMetric.euclidNormVec]⟩
  refine le_antisymm (hmin h0) ?_
  rw [hk]
  exact Real.sqrt_nonneg _
variable {D E}
theorem mem_supportQ_of_ne_zero (hw : WellPosedness.WellPosed)
    {f : E.Pt D → ℝ} {y : E.Pt D} (h : f y ≠ 0) : y ∈ supportQ D E f := by
  show ∀ r : ℝ, 0 < r → ∃ z ∈ {z | f z ≠ 0}, quotDist D E y z < r
  intro r hr
  exact ⟨y, h, by rw [quotDist_self D E hw]; exact hr⟩
theorem supportQ_nonempty (hw : WellPosedness.WellPosed)
    {f : E.Pt D → ℝ} (h : f ≠ 0) : (supportQ D E f).Nonempty := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp h
  exact ⟨y, mem_supportQ_of_ne_zero hw hy⟩
theorem supportQ_subset (hsp : C1OfStock.Holds) {Q : Set (E.Pt D)}
    (hQ : Q ∈ supportStock D E) {f : E.Pt D → ℝ} (hf : f ∈ c1VanishingOutside D E Q) :
    supportQ D E f ⊆ Q :=
  ((hsp D E Q hQ).1.1 f hf.1).mp hf
theorem c1VanishingOutside_mono {A B : Set (E.Pt D)} (h : A ⊆ B) {f : E.Pt D → ℝ}
    (hf : f ∈ c1VanishingOutside D E A) : f ∈ c1VanishingOutside D E B :=
  ⟨hf.1, fun y hy => hf.2 y fun h' => hy (h h')⟩
variable (D E)
theorem leftImage_subset_outerImage : boxImage D E leftSlab ⊆ boxImage D E outerBox :=
  Set.image_mono leftSlab_subset_outerBox
theorem rightImage_subset_outerImage : boxImage D E rightSlab ⊆ boxImage D E outerBox :=
  Set.image_mono rightSlab_subset_outerBox
theorem leftImage_inter_rightImage (hbox : TorusBoxDiameterBound) :
    boxImage D E leftSlab ∩ boxImage D E rightSlab = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨x, hx, rfl⟩, ⟨x', hx', h⟩⟩
  have e := quotMap_injOn_outerBox D E hbox (rightSlab_subset_outerBox hx')
    (leftSlab_subset_outerBox hx) h
  have h1 := leftSlab_coord_zero_le hx
  have h2 := le_rightSlab_coord_zero hx'
  rw [e] at h2
  linarith
theorem slabsInOuterBox (hw : WellPosedness.WellPosed) (hbox : TorusBoxDiameterBound) :
    SlabsInOuterBox D E := by
  obtain ⟨u, hu, hu0⟩ := exists_c1_leftSlab D E hw
  obtain ⟨v, hv, hv0⟩ := exists_c1_rightSlab D E hw
  refine ⟨admitsBox_of_diam_le D E outerBox_diam_le, admitsBox_of_diam_le D E leftSlab_diam_le,
    admitsBox_of_diam_le D E rightSlab_diam_le, quotMap_injOn_outerBox D E hbox,
    leftImage_inter_rightImage D E hbox,
    Set.union_subset (leftImage_subset_outerImage D E) (rightImage_subset_outerImage D E),
    fun h => ?_, fun h => ?_⟩
  · rw [h] at hu
    exact hu0 hu
  · rw [h] at hv
    exact hv0 hv
theorem nonempty_of_c1_ne_zero {A : Set (E.Pt D)} {u : E.Pt D → ℝ}
    (hu : u ∈ c1VanishingOutside D E A) (h0 : u ≠ 0) : A.Nonempty := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp h0
  by_contra hne
  exact hy (hu.2 y fun hy' => hne ⟨y, hy'⟩)
theorem leftImage_ne_outerImage (hw : WellPosedness.WellPosed) (hbox : TorusBoxDiameterBound) :
    boxImage D E leftSlab ≠ boxImage D E outerBox := by
  intro h
  obtain ⟨v, hv, hv0⟩ := exists_c1_rightSlab D E hw
  obtain ⟨y, hy⟩ := nonempty_of_c1_ne_zero D E hv hv0
  have h1 : y ∈ boxImage D E leftSlab := h ▸ rightImage_subset_outerImage D E hy
  have h2 : y ∈ boxImage D E leftSlab ∩ boxImage D E rightSlab := ⟨h1, hy⟩
  rw [leftImage_inter_rightImage D E hbox] at h2
  exact h2
variable {D E}
theorem exists_choice_mem_ne_zero {C : supportStock D E → Set (E.Pt D → ℝ)}
    (hC : IsDenseChoice D E C) {A : Set (E.Pt D)} (hA : A ∈ supportStock D E)
    {u : E.Pt D → ℝ} (hu : u ∈ c1VanishingOutside D E A) (h0 : u ≠ 0) :
    ∃ φ ∈ C ⟨A, hA⟩, φ ≠ 0 := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp h0
  have hy' : u y ≠ 0 := hy
  obtain ⟨g, hg, hN⟩ := (hC ⟨A, hA⟩).2 u hu |u y| (abs_pos.mpr hy')
  refine ⟨g, hg, ?_⟩
  rintro rfl
  have h1 : ENNReal.ofReal |(u - 0) y| ≤ euclidC1Norm D E (u - 0) :=
    le_trans (le_iSup (fun z => ENNReal.ofReal |(u - 0) z|) y) (le_max_left _ _)
  simp only [sub_zero] at h1 hN
  exact absurd hN (not_lt.mpr h1)
structure ElementPairContext (C : supportStock D E → Set (E.Pt D → ℝ))
    (φ₀ ψ : E.Pt D → ℝ) : Prop where
  wellPosed : WellPosedness.WellPosed
  boxBound : TorusBoxDiameterBound
  c1Stock : C1OfStock.Holds
  countFamily : CountableChoiceFamilyFacts
  disjointStock : DisjointStockMembers.Statement
  isoGroup : AdicIsometryGroup.Claim
  countable : IsCountableDenseChoice D E C
  closed : HasClosedValues D E C
  saturated : IsSaturated D E C
  ratSub : SaturatedChoices.ChoiceSetsAreRatSubmodules D E C
  pair : IsComponentPair D E C φ₀ ψ
namespace ElementPairContext
variable {C : supportStock D E → Set (E.Pt D → ℝ)} {φ₀ ψ : E.Pt D → ℝ}
theorem outer_mem (_ : ElementPairContext C φ₀ ψ) : boxImage D E outerBox ∈ supportStock D E :=
  boxImage_mem_supportStock D E (admitsBox_of_diam_le D E outerBox_diam_le)
theorem left_mem (_ : ElementPairContext C φ₀ ψ) : boxImage D E leftSlab ∈ supportStock D E :=
  boxImage_mem_supportStock D E (admitsBox_of_diam_le D E leftSlab_diam_le)
theorem right_mem (_ : ElementPairContext C φ₀ ψ) : boxImage D E rightSlab ∈ supportStock D E :=
  boxImage_mem_supportStock D E (admitsBox_of_diam_le D E rightSlab_diam_le)
variable (S : ElementPairContext C φ₀ ψ)
include S
theorem fst_ne_zero : φ₀ ≠ 0 := fun h => S.pair.1.2 h
theorem snd_ne_zero : ψ ≠ 0 := fun h => S.pair.2.2 h
theorem fst_mem : φ₀ ∈ C ⟨_, S.left_mem⟩ := S.pair.1.1.2
theorem snd_mem : ψ ∈ C ⟨_, S.right_mem⟩ := S.pair.2.1.2
theorem fst_c1 : φ₀ ∈ c1VanishingOutside D E (boxImage D E leftSlab) :=
  (S.countable.1 _).1 S.fst_mem
theorem snd_c1 : ψ ∈ c1VanishingOutside D E (boxImage D E rightSlab) :=
  (S.countable.1 _).1 S.snd_mem
theorem fst_supportQ : supportQ D E φ₀ ⊆ boxImage D E leftSlab :=
  supportQ_subset S.c1Stock S.left_mem S.fst_c1
theorem snd_supportQ : supportQ D E ψ ⊆ boxImage D E rightSlab :=
  supportQ_subset S.c1Stock S.right_mem S.snd_c1
theorem disjoint_supportQ : Disjoint (supportQ D E φ₀) (supportQ D E ψ) := by
  rw [Set.disjoint_left]
  intro y h1 h2
  have h3 : y ∈ boxImage D E leftSlab ∩ boxImage D E rightSlab :=
    ⟨S.fst_supportQ h1, S.snd_supportQ h2⟩
  rw [leftImage_inter_rightImage D E S.boxBound] at h3
  exact h3
theorem fst_mem_choice : φ₀ ∈ choiceComponents D E C := Set.mem_iUnion.mpr ⟨_, S.fst_mem⟩
theorem snd_member : ψ ∈ choiceComponents D E C := Set.mem_iUnion.mpr ⟨_, S.snd_mem⟩
theorem fst_mem_outer : φ₀ ∈ C ⟨_, S.outer_mem⟩ := by
  rw [S.saturated ⟨_, S.outer_mem⟩]
  exact ⟨S.fst_mem_choice, c1VanishingOutside_mono (leftImage_subset_outerImage D E) S.fst_c1⟩
theorem snd_ne_fst : ψ ≠ φ₀ := by
  intro h
  obtain ⟨y, hy⟩ := supportQ_nonempty S.wellPosed S.fst_ne_zero
  have h1 : y ∈ supportQ D E ψ := by rw [h]; exact hy
  exact Set.disjoint_left.mp S.disjoint_supportQ hy h1
end ElementPairContext
section Erase
variable {C : supportStock D E → Set (E.Pt D → ℝ)} {φ₀ ψ : E.Pt D → ℝ}
theorem choiceErase_of_eq {Q : supportStock D E}
    (h : (Q : Set (E.Pt D)) = boxImage D E outerBox) :
    choiceErase D E C φ₀ Q = C Q :=
  if_pos h
theorem choiceErase_of_ne {Q : supportStock D E}
    (h : (Q : Set (E.Pt D)) ≠ boxImage D E outerBox) :
    choiceErase D E C φ₀ Q = C Q \ {φ₀} :=
  if_neg h
theorem choiceErase_subset (Q : supportStock D E) : choiceErase D E C φ₀ Q ⊆ C Q := by
  by_cases h : (Q : Set (E.Pt D)) = boxImage D E outerBox
  · rw [choiceErase_of_eq h]
  · rw [choiceErase_of_ne h]
    exact Set.sdiff_subset
theorem mem_choiceErase {Q : supportStock D E} {f : E.Pt D → ℝ} (hf : f ∈ C Q) (h : f ≠ φ₀) :
    f ∈ choiceErase D E C φ₀ Q := by
  by_cases hQ : (Q : Set (E.Pt D)) = boxImage D E outerBox
  · rw [choiceErase_of_eq hQ]
    exact hf
  · rw [choiceErase_of_ne hQ]
    exact ⟨hf, h⟩
theorem not_mem_choiceErase {Q : supportStock D E}
    (h : (Q : Set (E.Pt D)) ≠ boxImage D E outerBox) :
    φ₀ ∉ choiceErase D E C φ₀ Q := by
  rw [choiceErase_of_ne h]
  exact fun hf => hf.2 rfl
namespace ElementPairContext
variable (S : ElementPairContext C φ₀ ψ)
include S
theorem erase_isCountableDenseChoice : IsCountableDenseChoice D E (choiceErase D E C φ₀) := by
  refine ⟨fun Q => ⟨(choiceErase_subset Q).trans (S.countable.1 Q).1, ?_⟩,
    fun Q => (S.countable.2 Q).mono (choiceErase_subset Q)⟩
  intro f hf ε hε
  by_cases hQ : (Q : Set (E.Pt D)) = boxImage D E outerBox
  · rw [choiceErase_of_eq hQ]
    exact (S.countable.1 Q).2 f hf ε hε
  obtain ⟨g, hg, hN⟩ := (S.countable.1 Q).2 f hf (ε / 2) (half_pos hε)
  by_cases hgφ : g = φ₀
  swap
  · exact ⟨g, mem_choiceErase hg hgφ,
      hN.trans ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))⟩
  have hg0 : g ≠ 0 := hgφ ▸ S.fst_ne_zero
  have hnorm := ((S.countFamily D E).2.1 Q Q.2).2.2.1.1
  have hgV := (S.countable.1 Q).1 hg
  have hfin := hnorm.finite g hgV
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (euclidC1Norm D E g).toReal / ε)
  rw [div_lt_iff₀ hε] at hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set a := (euclidC1Norm D E g).toReal with ha
  set t : ℝ := 1 / ((k : ℝ) + 1) with ht
  have ht0 : 0 < t := by positivity
  have hta : t * a < ε / 2 := by
    rw [ht, one_div, inv_mul_lt_iff₀ hk1]
    nlinarith
  let c : ℚ := 1 + 1 / ((k : ℚ) + 1)
  have hc : (c : ℝ) = 1 + t := by
    simp [c, ht]
  have hg' : c • g = g + t • g := by
    funext y
    simp only [Pi.smul_apply, Pi.add_apply, Rat.smul_def, smul_eq_mul, hc]
    ring
  have hmem : c • g ∈ C Q := by
    obtain ⟨V, hV⟩ := S.ratSub Q
    rw [← hV] at hg ⊢
    exact V.smul_mem c hg
  have hne : c • g ≠ φ₀ := by
    rw [← hgφ, hg']
    intro h
    have h2 : t • g = 0 := by simpa using congrArg (· - g) h
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact ht0.ne' h3
    · exact hg0 h3
  refine ⟨c • g, mem_choiceErase hmem hne, ?_⟩
  have hfg : f - g ∈ c1VanishingOutside D E Q := by
    have := hnorm.lincomb_mem f hf g hgV 1 (-1)
    simpa [sub_eq_add_neg] using this
  have htg : (-t) • g ∈ c1VanishingOutside D E Q := by
    have := hnorm.lincomb_mem g hgV g hgV (-t) 0
    simpa using this
  have he : f - c • g = (f - g) + (-t) • g := by
    rw [hg', neg_smul]
    abel
  have h3 : euclidC1Norm D E ((-t) • g) = ENNReal.ofReal (t * a) := by
    rw [hnorm.homog g hgV, abs_neg, abs_of_pos ht0, ENNReal.ofReal_mul ht0.le, ha,
      ENNReal.ofReal_toReal hfin.ne]
  calc euclidC1Norm D E (f - c • g)
      ≤ euclidC1Norm D E (f - g) + euclidC1Norm D E ((-t) • g) := by
        rw [he]
        exact hnorm.triangle _ hfg _ htg
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add hN (by
          rw [h3]
          exact (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mpr hta)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
theorem erase_choiceComponents :
    choiceComponents D E (choiceErase D E C φ₀) = choiceComponents D E C := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono choiceErase_subset
  · intro f hf
    obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp hf
    by_cases h : f = φ₀
    · rw [h]
      refine Set.mem_iUnion.mpr ⟨⟨_, S.outer_mem⟩, ?_⟩
      rw [choiceErase_of_eq rfl]
      exact S.fst_mem_outer
    · exact Set.mem_iUnion.mpr ⟨Q, mem_choiceErase hQ h⟩
theorem erase_hasClosedComponents : HasClosedValues D E (choiceErase D E C φ₀) := by
  unfold HasClosedValues
  rw [S.erase_choiceComponents]
  exact S.closed
theorem erase_choiceAt_left_ne :
    choiceAt D E (choiceErase D E C φ₀) (boxImage D E leftSlab) ≠
      choiceComponents D E C ∩ c1VanishingOutside D E (boxImage D E leftSlab) := by
  intro h
  have h1 : φ₀ ∈ choiceAt D E (choiceErase D E C φ₀) (boxImage D E leftSlab) := by
    rw [h]
    exact ⟨S.fst_mem_choice, S.fst_c1⟩
  obtain ⟨hA, hf⟩ := h1
  exact not_mem_choiceErase (Q := ⟨_, hA⟩) (leftImage_ne_outerImage D E S.wellPosed S.boxBound) hf
theorem erase_not_saturated : ¬ IsSaturated D E (choiceErase D E C φ₀) := by
  intro h
  have h1 := h ⟨_, S.left_mem⟩
  rw [S.erase_choiceComponents] at h1
  have h2 : φ₀ ∈ choiceErase D E C φ₀ ⟨_, S.left_mem⟩ := by
    rw [h1]
    exact ⟨S.fst_mem_choice, S.fst_c1⟩
  exact not_mem_choiceErase (leftImage_ne_outerImage D E S.wellPosed S.boxBound) h2
theorem erase_closed_not_saturated : ErasedClosedNotSaturated D E C φ₀ :=
  ⟨S.erase_isCountableDenseChoice, S.erase_choiceComponents, S.erase_hasClosedComponents,
    S.erase_not_saturated, S.erase_choiceAt_left_ne⟩
end ElementPairContext
theorem mem_choiceTupleFamily {F : supportStock D E → Set (E.Pt D → ℝ)} {n : ℕ} (hn : 1 ≤ n)
    {p : Fin n → E.Pt D → ℝ} {Q : Fin n → supportStock D E}
    (h : IsBuiltFrom D E F p Q) :
    (⟨n, p⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ choiceTupleFamily D E F :=
  ⟨hn, fun i => (Q i : Set (E.Pt D)), fun i => (Q i).2, h.1, h.2⟩
theorem pairwise_disjoint_fin_two {X : Type*} {A : Fin 2 → Set X} (h : Disjoint (A 0) (A 1)) :
    Pairwise fun i k => Disjoint (A i) (A k) := by
  intro i k hik
  fin_cases i <;> fin_cases k
  · exact absurd rfl hik
  · exact h
  · exact h.symm
  · exact absurd rfl hik
namespace ElementPairContext
variable (S : ElementPairContext C φ₀ ψ)
include S
theorem pair_not_mem_family (p : Fin 2 → E.Pt D → ℝ) (h0 : p 0 = φ₀) (h1 : p 1 = ψ) :
    (⟨2, p⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∉
      choiceTupleFamily D E (choiceErase D E C φ₀) := by
  rintro ⟨-, Q, hQ, hdis, hmem⟩
  have m0 : p 0 ∈ choiceErase D E C φ₀ ⟨Q 0, hQ 0⟩ := hmem 0
  have m1 : p 1 ∈ choiceErase D E C φ₀ ⟨Q 1, hQ 1⟩ := hmem 1
  rw [h0] at m0
  rw [h1] at m1
  have hq0 : Q 0 = boxImage D E outerBox := by
    by_contra hne
    exact not_mem_choiceErase (Q := ⟨Q 0, hQ 0⟩) hne m0
  have s1 : supportQ D E ψ ⊆ Q 1 :=
    supportQ_subset S.c1Stock (hQ 1) ((S.countable.1 _).1 (choiceErase_subset _ m1))
  have s2 : supportQ D E ψ ⊆ Q 0 := by
    rw [hq0]
    exact S.snd_supportQ.trans (rightImage_subset_outerImage D E)
  obtain ⟨y, hy⟩ := supportQ_nonempty S.wellPosed S.snd_ne_zero
  exact Set.disjoint_left.mp (hdis (show (0 : Fin 2) ≠ 1 by decide)) (s2 hy) (s1 hy)
theorem family_subset_disjointTuples :
    choiceTupleFamily D E (choiceErase D E C φ₀) ⊆
      disjointTuplesOf D E (choiceComponents D E C) := by
  rintro ⟨n, p⟩ ⟨hn, Q, hQ, hdis, hmem⟩
  have hsupp : ∀ i, supportQ D E (p i) ⊆ Q i := fun i =>
    supportQ_subset S.c1Stock (hQ i) ((S.countable.1 _).1 (choiceErase_subset _ (hmem i)))
  exact ⟨hn, fun i => Set.mem_iUnion.mpr ⟨_, choiceErase_subset _ (hmem i)⟩,
    fun i k hik => (hdis hik).mono (hsupp i) (hsupp k)⟩
theorem appendNotInFamily : AppendNotInFamily D E C φ₀ ψ := by
  have hWm : φ₀ ∈ choiceErase D E C φ₀ ⟨_, S.outer_mem⟩ := by
    rw [choiceErase_of_eq rfl]
    exact S.fst_mem_outer
  have hUm : ψ ∈ choiceErase D E C φ₀ ⟨_, S.right_mem⟩ :=
    mem_choiceErase S.snd_mem S.snd_ne_fst
  have f1 : IsBuiltFrom D E (choiceErase D E C φ₀) ![φ₀] fun _ => ⟨_, S.outer_mem⟩ :=
    ⟨Subsingleton.pairwise, fun i => by fin_cases i; exact hWm⟩
  have f2 : IsBuiltFrom D E (choiceErase D E C φ₀) ![ψ] fun _ => ⟨_, S.right_mem⟩ :=
    ⟨Subsingleton.pairwise, fun i => by fin_cases i; exact hUm⟩
  have hnot := S.pair_not_mem_family ![φ₀, ψ] rfl rfl
  refine ⟨mem_choiceTupleFamily le_rfl f1, ⟨_, rfl, f1⟩, mem_choiceTupleFamily le_rfl f2,
    ⟨_, rfl, f2⟩, ?_, S.pair_not_mem_family _ rfl rfl, ?_⟩
  · intro i j
    fin_cases i
    fin_cases j
    exact S.disjoint_supportQ
  · refine (Set.ssubset_iff_of_subset S.family_subset_disjointTuples).mpr
      ⟨⟨2, ![φ₀, ψ]⟩, ?_, hnot⟩
    refine ⟨by norm_num, Fin.forall_fin_two.mpr ⟨S.fst_mem_choice, S.snd_member⟩, ?_⟩
    exact pairwise_disjoint_fin_two (A := fun i => supportQ D E ((![φ₀, ψ] : Fin 2 → _) i))
      S.disjoint_supportQ
end ElementPairContext
end Erase
section Maps
variable (D E)
theorem intCast_mem_adicGridPoints (L : ℕ) (n : ℤ) : (n : ℝ) ∈ PeriodicLattice.adicGridPoints L :=
  (PeriodicLattice.mem_adicGridPoints_iff L _).mpr ⟨0, n, by simp [PeriodicLattice.meshSize]⟩
theorem zero_mem_adicPoints4 (L : ℕ) : (0 : Fin 4 → ℝ) ∈ adicPoints4 L := fun _ => by
  simpa using intCast_mem_adicGridPoints L 0
theorem e1_apply_eq (μ : Fin 4) :
    e1 μ = (((![1, 0, 0, 0] : Fin 4 → ℤ) μ : ℤ) : ℝ) := by
  fin_cases μ <;> simp [e1]
theorem e1_mem (L : ℕ) : e1 ∈ adicPoints4 L := fun μ => by
  rw [e1_apply_eq]
  exact intCast_mem_adicGridPoints L _
theorem neg_e1_mem (L : ℕ) : -e1 ∈ adicPoints4 L := fun μ => by
  rw [Pi.neg_apply, e1_apply_eq, ← Int.cast_neg]
  exact intCast_mem_adicGridPoints L _
theorem negFrame_actOnVector (x : Fin 4 → ℝ) :
    negFrame.actOnVector x = -x := by
  funext μ
  simp [SignedFrame.actOnVector, negFrame]
theorem frameInv_negFrame_actOnVector (x : Fin 4 → ℝ) :
    (frameInv negFrame).actOnVector x = -x := by
  funext μ
  simp [SignedFrame.actOnVector, negFrame, frameInv]
theorem one_actOnVector (x : Fin 4 → ℝ) : (1 : SignedFrame).actOnVector x = x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.actOnVector_one <;> assumption
variable (hw : WellPosedness.WellPosed)
include hw
theorem quotMap_add (x x' : Fin 4 → ℝ) :
    E.quotMap D (x + x') = E.quotMap D x + E.quotMap D x' :=
  (hw D E).1.1 x x'
theorem quotMap_neg (x : Fin 4 → ℝ) : E.quotMap D (-x) = -E.quotMap D x :=
  map_neg (AddMonoidHom.mk' (E.quotMap D) (hw D E).1.1) x
theorem negEquiv_inducedBy {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : ∀ x, s x = -x) :
    InducedBy D E s (negEquiv D E) := by
  funext x
  show -(E.quotMap D x) = E.quotMap D (s x)
  rw [hs, quotMap_neg D E hw]
theorem shiftE1_inducedBy :
    InducedBy D E (translateR4 e1) (shiftE1 D E) := by
  funext x
  show E.quotMap D x + E.quotMap D e1 = E.quotMap D (x + e1)
  rw [quotMap_add D E hw]
theorem mapsInduced : MapsInduced D E :=
  ⟨negEquiv_inducedBy D E hw negFrame_actOnVector, e1_mem D.L, shiftE1_inducedBy D E hw⟩
theorem negEquiv_mem : ⇑(negEquiv D E) ∈ adicIsometriesQ D E := by
  refine ⟨translateR4 0 ∘ negFrame.actOnVector,
    ⟨0, zero_mem_adicPoints4 D.L, _, rfl⟩, negEquiv_inducedBy D E hw fun x => ?_⟩
  simp [translateR4, negFrame_actOnVector]
theorem shiftE1_mem : ⇑(shiftE1 D E) ∈ adicIsometriesQ D E := by
  refine ⟨translateR4 e1 ∘ (1 : SignedFrame).actOnVector,
    ⟨_, e1_mem D.L, 1, rfl⟩, ?_⟩
  have h := shiftE1_inducedBy D E hw
  have e : translateR4 e1 ∘ (1 : SignedFrame).actOnVector = translateR4 e1 := by
    funext x
    simp [one_actOnVector]
  rw [e]
  exact h
omit hw in
theorem period_coord_zero {k : Fin 4 → ℝ} (hk : k ∈ E.periodGroup D) : k 0 = 0 ∨ 2 ≤ |k 0| := by
  cases E with
  | euclidean =>
    left
    have h : k = 0 := AddSubgroup.mem_bot.mp hk
    simp [h]
  | torus =>
    obtain ⟨n, hn⟩ := hk
    rw [hn 0]
    by_cases h : n 0 = 0
    · left
      simp [h]
    · right
      have h1 : (1 : ℝ) ≤ |(n 0 : ℝ)| := by
        exact_mod_cast Int.one_le_abs h
      have h2 := two_le_side D
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < D.side)]
      nlinarith
theorem negEquiv_image_disjoint :
    negEquiv D E '' boxImage D E outerBox ∩ boxImage D E outerBox = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨y, ⟨x, hx, rfl⟩, rfl⟩, ⟨x', hx', h⟩⟩
  have h' : E.quotMap D x' = -E.quotMap D x := h
  have hk : x' + x ∈ E.periodGroup D := by
    apply ((hw D E).1.2.2 _).mp
    rw [quotMap_add D E hw, h', neg_add_cancel]
  have a1 := mem_outerBox_toSet.mp hx 0
  have a2 := mem_outerBox_toSet.mp hx' 0
  rcases period_coord_zero D E hk with h0 | h2
  · rw [Pi.add_apply] at h0
    linarith [a1.1, a2.1]
  · rw [Pi.add_apply, abs_of_nonneg (by linarith [a1.1, a2.1])] at h2
    linarith [a1.2, a2.2]
theorem shiftE1_image_disjoint :
    shiftE1 D E '' boxImage D E outerBox ∩ boxImage D E outerBox = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨y, ⟨x, hx, rfl⟩, rfl⟩, ⟨x', hx', h⟩⟩
  have h' : E.quotMap D x' = E.quotMap D x + E.quotMap D e1 := h
  have hk : x + e1 - x' ∈ E.periodGroup D := by
    apply ((hw D E).1.2.2 _).mp
    have h3 := quotMap_add D E hw (x + e1 - x') x'
    rw [sub_add_cancel, quotMap_add D E hw, ← h'] at h3
    exact add_eq_right.mp h3.symm
  have a1 := mem_outerBox_toSet.mp hx 0
  have a2 := mem_outerBox_toSet.mp hx' 0
  have he1 : e1 0 = 1 := by
    simp [e1]
  have e : (x + e1 - x') 0 = x 0 + 1 - x' 0 := by
    rw [Pi.sub_apply, Pi.add_apply, he1]
  rcases period_coord_zero D E hk with h0 | h2
  · rw [e] at h0
    linarith [a1.1, a2.2]
  · rw [e, abs_of_nonneg (by linarith [a1.1, a2.2])] at h2
    linarith [a1.2, a2.1]
theorem descendedMap_eq {s : (Fin 4 → ℝ) → Fin 4 → ℝ} {r : E.Pt D → E.Pt D}
    (h : InducedBy D E s r) : descendedMap D E s = r := by
  have hs : InducedBy D E s (descendedMap D E s) :=
    Classical.epsilon_spec (p := InducedBy D E s) ⟨r, h⟩
  funext y
  obtain ⟨x, rfl⟩ := (hw D E).1.2.1 y
  exact (congrFun hs x).trans (congrFun h x).symm
end Maps
section Pushed
variable {C : supportStock D E → Set (E.Pt D → ℝ)} {φ₀ ψ : E.Pt D → ℝ}
namespace ElementPairContext
variable (S : ElementPairContext C φ₀ ψ)
include S
theorem pushedPairWitness (r : E.Pt D ≃ E.Pt D) (hr : ⇑r ∈ adicIsometriesQ D E)
    (hdisj : r '' boxImage D E outerBox ∩ boxImage D E outerBox = ∅) :
    PushedPairWitness D E C φ₀ ψ r := by
  obtain ⟨-, -, -, ⟨-, hiso, -⟩, -, -, -, -, -, -, -, -, hsupp, hclass, -⟩ := S.isoGroup D E
  have hrs : ⇑r.symm ∈ adicIsometriesQ D E := by
    obtain ⟨r', hr', -, h2⟩ := hiso.2.2.2 r hr
    have e : ⇑r.symm = r' := by
      funext y
      have := congrFun h2 (r.symm y)
      simpa using this.symm
    rw [e]
    exact hr'
  have hφk := ((S.c1Stock D E _ S.left_mem).1.2 φ₀ S.fst_c1).1
  have hψk := ((S.c1Stock D E _ S.right_mem).1.2 ψ S.snd_c1).1
  obtain ⟨hφ1, hφ2⟩ := hclass r hr φ₀ S.fst_c1.1 hφk
  obtain ⟨hψ1, hψ2⟩ := hclass r hr ψ S.snd_c1.1 hψk
  have hs1 : supportQ D E (pushFn D E r φ₀) = r '' supportQ D E φ₀ := hsupp r hr φ₀
  have hs2 : supportQ D E (pushFn D E r ψ) = r '' supportQ D E ψ := hsupp r hr ψ
  have hdis0 : Disjoint (supportQ D E (pushFn D E r φ₀))
      (supportQ D E (pushFn D E r ψ)) := by
    rw [hs1, hs2]
    exact (Set.disjoint_image_iff r.injective).mpr S.disjoint_supportQ
  have hne : ∀ f : E.Pt D → ℝ, supportQ D E f ⊆ boxImage D E outerBox →
      pushFn D E r f ≠ φ₀ := by
    intro f hf h
    have h1 : supportQ D E φ₀ ⊆ r '' boxImage D E outerBox := by
      rw [← h, hsupp r hr f]
      exact Set.image_mono hf
    obtain ⟨y, hy⟩ := supportQ_nonempty S.wellPosed S.fst_ne_zero
    have h2 : y ∈ r '' boxImage D E outerBox ∩ boxImage D E outerBox :=
      ⟨h1 hy, leftImage_subset_outerImage D E (S.fst_supportQ hy)⟩
    rw [hdisj] at h2
    exact h2
  obtain ⟨Q, hQ, hdis, hin⟩ := S.disjointStock D E 2 (by norm_num)
    ![supportQ D E (pushFn D E r φ₀), supportQ D E (pushFn D E r ψ)]
    (fun _ => Set.univ) (Fin.forall_fin_two.mpr ⟨hφ2, hψ2⟩) (pairwise_disjoint_fin_two hdis0)
    (fun _ x _ => ⟨1, one_pos, fun _ _ => trivial⟩) (fun _ _ _ => trivial)
  have hmem : ∀ (i : Fin 2) (f : E.Pt D → ℝ), f ∈ choiceComponents D E C →
      IsC1Fn D E f → supportQ D E f ⊆ Q i → f ≠ φ₀ →
      f ∈ choiceErase D E C φ₀ ⟨Q i, hQ i⟩ := by
    intro i f he h1 h2 h3
    refine mem_choiceErase ?_ h3
    rw [S.saturated ⟨Q i, hQ i⟩]
    exact ⟨he, ((S.c1Stock D E _ (hQ i)).1.1 f h1).mpr h2⟩
  have m0 := hmem 0 _ (S.closed.1 r hr φ₀ S.fst_mem_choice) hφ1 (hin 0).1
    (hne φ₀ (S.fst_supportQ.trans (leftImage_subset_outerImage D E)))
  have m1 := hmem 1 _ (S.closed.1 r hr ψ S.snd_member) hψ1 (hin 1).1
    (hne ψ (S.snd_supportQ.trans (rightImage_subset_outerImage D E)))
  refine ⟨hr, hdisj, ⟨by norm_num, Q, hQ, hdis, Fin.forall_fin_two.mpr ⟨m0, m1⟩⟩, hrs, ?_,
    S.pair_not_mem_family _ rfl rfl⟩
  funext i y
  simp [pushTuple, pushFn]
theorem negEquiv_witness : PushedPairWitness D E C φ₀ ψ (negEquiv D E) :=
  S.pushedPairWitness _ (negEquiv_mem D E S.wellPosed) (negEquiv_image_disjoint D E S.wellPosed)
theorem shiftE1_witness :
    PushedPairWitness D E C φ₀ ψ (shiftE1 D E) :=
  S.pushedPairWitness _ (shiftE1_mem D E S.wellPosed) (shiftE1_image_disjoint D E S.wellPosed)
theorem familyNotStable : FamilyNotStable D E C φ₀ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hneg := S.negEquiv_witness
    have h1 := (isStableUnder_ofMap_iff _ _).mp
      (h negFrame (Set.mem_univ _)) _ hneg.2.2.1
    have hm : signedFrameMap D E (frameInv negFrame) = negEquiv D E :=
      descendedMap_eq D E S.wellPosed
        (negEquiv_inducedBy D E S.wellPosed frameInv_negFrame_actOnVector)
    have e : frameActTuple D E negFrame
        (pushTuple D E (negEquiv D E) ![φ₀, ψ]) = ![φ₀, ψ] := by
      funext i y
      show (![φ₀, ψ] : Fin 2 → _) i ((negEquiv D E).symm
        (signedFrameMap D E (frameInv negFrame) y)) = _
      rw [hm]
      simp [negEquiv]
    have h2 : (⟨2, frameActTuple D E negFrame
        (pushTuple D E (negEquiv D E) ![φ₀, ψ])⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈
        choiceTupleFamily D E (choiceErase D E C φ₀) := h1
    rw [e] at h2
    exact hneg.2.2.2.2.2 h2
  · have htr := S.shiftE1_witness
    have h1 := (isStableUnder_ofMap_iff _ _).mp
      (h (E.quotMap D (-e1)) ⟨_, neg_e1_mem D.L, rfl⟩) _ htr.2.2.1
    have e : shiftTuple D E (E.quotMap D (-e1))
        (pushTuple D E (shiftE1 D E) ![φ₀, ψ]) = ![φ₀, ψ] := by
      funext i y
      show (![φ₀, ψ] : Fin 2 → _) i ((shiftE1 D E).symm
        (y - E.quotMap D (-e1))) = _
      rw [quotMap_neg D E S.wellPosed]
      simp [shiftE1]
    have h2 : (⟨2, shiftTuple D E (E.quotMap D (-e1))
        (pushTuple D E (shiftE1 D E) ![φ₀, ψ])⟩ :
        Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈
        choiceTupleFamily D E (choiceErase D E C φ₀) := h1
    rw [e] at h2
    exact htr.2.2.2.2.2 h2
end ElementPairContext
end Pushed
theorem statement_holds (hw : WellPosedness.WellPosed)
    (hbox : TorusBoxDiameterBound)
    (hch : SaturatedChoices.Claim)
    (hdj : DisjointStockMembers.Statement)
    (hgrp : AdicIsometryGroup.Claim)
    (hsp : C1OfStock.Holds)
    (hfc : CountableChoiceFamilyFacts) : Statement := by
  intro D E C hCc hcl hsat
  have hvec : SaturatedChoices.ChoiceSetsAreRatSubmodules D E C :=
    ((hch D E).2.2.1 C hCc.1 hcl hsat).1
  have setting : ∀ φ₀ ψ, IsComponentPair D E C φ₀ ψ → ElementPairContext C φ₀ ψ := fun φ₀ ψ h =>
    ⟨hw, hbox, hsp, hfc, hdj, hgrp, hCc, hcl, hsat, hvec, h⟩
  refine ⟨slabsInOuterBox D E hw hbox, ⟨?_, fun φ₀ ψ h => ?_⟩, mapsInduced D E hw,
    fun φ₀ ψ h => ?_⟩
  · have hL := boxImage_mem_supportStock D E (admitsBox_of_diam_le D E leftSlab_diam_le)
    have hU := boxImage_mem_supportStock D E (admitsBox_of_diam_le D E rightSlab_diam_le)
    obtain ⟨u, hu, hu0⟩ := exists_c1_leftSlab D E hw
    obtain ⟨v, hv, hv0⟩ := exists_c1_rightSlab D E hw
    obtain ⟨φ, hφ, hφ0⟩ := exists_choice_mem_ne_zero hCc.1 hL hu hu0
    obtain ⟨ψ, hψ, hψ0⟩ := exists_choice_mem_ne_zero hCc.1 hU hv hv0
    exact ⟨φ, ψ, ⟨⟨hL, hφ⟩, hφ0⟩, ⟨⟨hU, hψ⟩, hψ0⟩⟩
  · have S := setting φ₀ ψ h
    exact ⟨supportQ_nonempty hw S.fst_ne_zero, supportQ_nonempty hw S.snd_ne_zero,
      S.disjoint_supportQ, S.outer_mem, S.fst_mem_outer⟩
  · have S := setting φ₀ ψ h
    exact ⟨S.erase_closed_not_saturated, S.appendNotInFamily, S.negEquiv_witness,
      S.shiftE1_witness, S.familyNotStable⟩
end YangMills.Construction.PeriodicSpace.StableEntriesUnstableFamily
