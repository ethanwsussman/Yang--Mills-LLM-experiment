import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayer
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.VectorsOfARectangularPeriodLattice
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace BoxQuotient
open NormalFamilies
open PeriodicLattice (coordVec)
theorem coordVec_dotProduct (μ : Fin 4) (v : AmbientSpace) : coordVec μ ⬝ᵥ v = v μ := by
  simp [coordVec]
theorem axisStep_coe (μ : Fin 4) : ((axisStep 1 μ : LatticePoint 1) : AmbientSpace) = coordVec μ := rfl
theorem exists_int_coord (x : LatticePoint 1) (μ : Fin 4) : ∃ m : ℤ, (x : AmbientSpace) μ = m := by
  obtain ⟨w, hw⟩ := x.2
  exact ⟨w μ, by simpa using hw μ⟩
theorem normalVector_props {n : AmbientSpace} (h : IsNormalVector n) :
    (∀ v : AmbientSpace, |n ⬝ᵥ v| ≤ 2 * ‖v‖) ∧
      (∀ x : LatticePoint 1, ∃ m : ℤ, n ⬝ᵥ (x : AmbientSpace) = m) ∧
        ∃ μ, n ⬝ᵥ ((axisStep 1 μ : LatticePoint 1) : AmbientSpace) = 1 := by
  have hcoord : ∀ (v : AmbientSpace) (μ : Fin 4), |v μ| ≤ ‖v‖ := fun v μ => norm_le_pi_norm v μ
  rcases h with ⟨μ, rfl⟩ | ⟨μ, ν, hμν, rfl | rfl⟩
  · refine ⟨fun v => ?_, fun x => ?_, μ, ?_⟩
    · rw [coordVec_dotProduct]
      have := hcoord v μ
      have := norm_nonneg v
      linarith
    · rw [coordVec_dotProduct]
      exact exists_int_coord x μ
    · rw [axisStep_coe, coordVec_dotProduct]
      simp [coordVec]
  · have hne : μ ≠ ν := ne_of_lt hμν
    refine ⟨fun v => ?_, fun x => ?_, μ, ?_⟩
    · rw [add_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      have h1 := hcoord v μ
      have h2 := hcoord v ν
      have := abs_add_le (v μ) (v ν)
      linarith
    · rw [add_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      obtain ⟨a, ha⟩ := exists_int_coord x μ
      obtain ⟨b, hb⟩ := exists_int_coord x ν
      exact ⟨a + b, by rw [ha, hb]; push_cast; ring⟩
    · rw [axisStep_coe, add_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      simp [coordVec, Pi.single_eq_of_ne hne.symm]
  · have hne : μ ≠ ν := ne_of_lt hμν
    refine ⟨fun v => ?_, fun x => ?_, μ, ?_⟩
    · rw [sub_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      have h1 := hcoord v μ
      have h2 := hcoord v ν
      have := abs_sub (v μ) (v ν)
      linarith
    · rw [sub_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      obtain ⟨a, ha⟩ := exists_int_coord x μ
      obtain ⟨b, hb⟩ := exists_int_coord x ν
      exact ⟨a - b, by rw [ha, hb]; push_cast; ring⟩
    · rw [axisStep_coe, sub_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
      simp [coordVec, Pi.single_eq_of_ne hne.symm]
section Heights
variable (F : OrthogonalNormalFrame)
def levelInt (i : Fin 4) (x : LatticePoint 1) : ℤ := ⌊F.vec i ⬝ᵥ (x : AmbientSpace)⌋
theorem levelInt_cast (i : Fin 4) (x : LatticePoint 1) :
    (levelInt F i x : ℝ) = F.vec i ⬝ᵥ (x : AmbientSpace) := by
  obtain ⟨m, hm⟩ := (normalVector_props (F.isNormal i)).2.1 x
  simp [levelInt, hm]
def levelHom (i : Fin 4) : LatticePoint 1 →+ ℤ :=
  AddMonoidHom.mk' (levelInt F i) fun x y => by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_add, levelInt_cast, levelInt_cast, levelInt_cast]
    simp [dotProduct_add]
theorem levelHom_cast (i : Fin 4) (x : LatticePoint 1) :
    (levelHom F i x : ℝ) = F.vec i ⬝ᵥ (x : AmbientSpace) :=
  levelInt_cast F i x
variable (s : Fin 4 → ℕ+)
theorem mem_fundamentalBox_iff (x : LatticePoint 1) :
    x ∈ F.fundamentalBox s ↔ ∀ i, 0 ≤ levelHom F i x ∧ levelHom F i x < ((s i : ℕ) : ℤ) := by
  refine forall_congr' fun i => ?_
  have h := levelHom_cast F i x
  simp only [linearHeight, ← h]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
theorem vec_dotProduct_sideSum (hF : RectangularPeriodVectors)
    (k : Fin 4 → ℤ) (j : Fin 4) :
    F.vec j ⬝ᵥ (∑ i, (k i : ℝ) • F.sideVec s i) = (k j : ℝ) * ((s j : ℕ) : ℝ) := by
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, (hF F s).1]
  simp
end Heights
section Periods
variable {F : OrthogonalNormalFrame} {s : Fin 4 → ℕ+} {Γ : PeriodSublattice 1}
theorem quotientMap_eq_iff (a b : LatticePoint 1) :
    Γ.quotientMap a = Γ.quotientMap b ↔ a - b ∈ Γ.periods := by
  rw [← sub_eq_zero, ← map_sub]
  exact QuotientAddGroup.eq_zero_iff _
theorem exists_side_coeffs (hΓ : Γ.IsBoxShaped F s) {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) :
    ∃ k : Fin 4 → ℤ, (γ : AmbientSpace) = ∑ i, (k i : ℝ) • F.sideVec s i := by
  have h : (γ : AmbientSpace) ∈ F.sideSpan s := by
    rw [← hΓ.1]
    exact ⟨γ, hγ, rfl⟩
  exact h
theorem levelHom_period (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) :
    ∃ k : Fin 4 → ℤ, (γ : AmbientSpace) = ∑ i, (k i : ℝ) • F.sideVec s i ∧
      ∀ j, levelHom F j γ = k j * ((s j : ℕ) : ℤ) := by
  obtain ⟨k, hk⟩ := exists_side_coeffs hΓ hγ
  refine ⟨k, hk, fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  rw [levelHom_cast, hk, vec_dotProduct_sideSum F s hF]
  push_cast
  rfl
theorem eq_of_mem_fundamentalBox (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) {x y : LatticePoint 1} (hx : x ∈ F.fundamentalBox s)
    (hy : y ∈ F.fundamentalBox s) (h : x - y ∈ Γ.periods) : x = y := by
  obtain ⟨k, hk, hh⟩ := levelHom_period hF hΓ h
  have hz : ∀ j, k j = 0 := fun j => by
    have h1 := (mem_fundamentalBox_iff F s x).1 hx j
    have h2 := (mem_fundamentalBox_iff F s y).1 hy j
    have h3 := hh j
    rw [map_sub] at h3
    rcases lt_trichotomy (k j) 0 with hl | hl | hl
    · nlinarith
    · exact hl
    · nlinarith
  have h0 : ((x - y : LatticePoint 1) : AmbientSpace) = 0 := by
    rw [hk]
    simp [hz]
  rw [← sub_eq_zero]
  exact Subtype.ext h0
theorem exists_period_add_mem_fundamentalBox (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) (x : LatticePoint 1) :
    ∃ γ ∈ Γ.periods, x + γ ∈ F.fundamentalBox s := by
  let k : Fin 4 → ℤ := fun i => -(levelHom F i x / ((s i : ℕ) : ℤ))
  have hv : (∑ i, (k i : ℝ) • F.sideVec s i) ∈ F.sideSpan s := ⟨k, rfl⟩
  rw [← hΓ.1] at hv
  obtain ⟨γ, hγ, hγv⟩ := hv
  refine ⟨γ, hγ, (mem_fundamentalBox_iff F s _).2 fun j => ?_⟩
  have hs : (0 : ℤ) < ((s j : ℕ) : ℤ) := by exact_mod_cast (s j).pos
  have hγj : levelHom F j γ = k j * ((s j : ℕ) : ℤ) := by
    apply Int.cast_injective (α := ℝ)
    rw [levelHom_cast]
    have : ((γ : LatticePoint 1) : AmbientSpace) = ∑ i, (k i : ℝ) • F.sideVec s i := hγv
    rw [this, vec_dotProduct_sideSum F s hF]
    push_cast
    rfl
  have hmod : levelHom F j (x + γ) = levelHom F j x % ((s j : ℕ) : ℤ) := by
    rw [map_add, hγj, Int.emod_def]
    simp only [k]
    ring
  rw [hmod]
  exact ⟨Int.emod_nonneg _ hs.ne', Int.emod_lt_of_pos _ hs⟩
theorem existsUnique_mem_fundamentalBox (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) (c : Γ.QuotientTorus) :
    ∃! x : LatticePoint 1, x ∈ F.fundamentalBox s ∧ Γ.quotientMap x = c := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Γ.periods c
  obtain ⟨γ, hγ, hbox⟩ := exists_period_add_mem_fundamentalBox hF hΓ x
  have hq : Γ.quotientMap (x + γ) = Γ.quotientMap x := by
    rw [quotientMap_eq_iff]
    simpa using hγ
  refine ⟨x + γ, ⟨hbox, hq⟩, ?_⟩
  rintro y ⟨hy, hyc⟩
  refine eq_of_mem_fundamentalBox hF hΓ hy hbox ?_
  rw [← quotientMap_eq_iff, hq]
  exact hyc
theorem existsUnique_boxLink (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) (c : Γ.QuotientLink) :
    ∃! b : PositiveLink 1, b ∈ (c : Set (PositiveLink 1)) ∧ b.1 ∈ F.boxLinks s := by
  obtain ⟨_, b₀, rfl⟩ := c
  obtain ⟨γ, hγ, hbox⟩ := exists_period_add_mem_fundamentalBox hF hΓ b₀.1.initial
  obtain ⟨μ, hμ⟩ := b₀.2
  refine ⟨b₀.translate γ, ⟨⟨γ, hγ, rfl⟩, b₀.1.initial + γ, hbox, μ, ?_⟩, ?_⟩
  · refine Link.ext rfl ?_
    show b₀.1.terminal + γ = b₀.1.initial + γ + axisStep 1 μ
    rw [← hμ]
    abel
  · rintro b ⟨⟨γ', hγ', rfl⟩, x, hx, ν, hb⟩
    have hini : b₀.1.initial + γ' = x := congrArg Link.initial hb
    have hdiff : b₀.1.initial + γ' - (b₀.1.initial + γ) ∈ Γ.periods := by
      simpa using Γ.periods.sub_mem hγ' hγ
    have heq : b₀.1.initial + γ' = b₀.1.initial + γ :=
      eq_of_mem_fundamentalBox hF hΓ (hini ▸ hx) hbox hdiff
    rw [add_left_cancel heq]
end Periods
theorem card_filter_mem_mul {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] (n : ℕ) [NeZero n]
    (χ : G →+ ZMod n) (hχ : Function.Surjective χ) (Y : Finset (ZMod n)) :
    n * (Finset.univ.filter fun g => χ g ∈ Y).card = Y.card * Fintype.card G := by
  classical
  have hfib : ∀ y : ZMod n, (Finset.univ.filter fun g => χ g = y).card =
      (Finset.univ.filter fun g => χ g = 0).card := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range χ (hχ y) (hχ 0)
  have hall : Fintype.card G = n * (Finset.univ.filter fun g => χ g = 0).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := χ) (t := Finset.univ)
      (fun g _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    simp only [hfib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hY : (Finset.univ.filter fun g => χ g ∈ Y).card =
      Y.card * (Finset.univ.filter fun g => χ g = 0).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := χ) (t := Y)
      (fun g hg => Finset.mem_coe.2 (Finset.mem_filter.1 hg).2)]
    have : ∀ y ∈ Y, (Finset.filter (fun g => χ g = y)
        (Finset.univ.filter fun g => χ g ∈ Y)).card =
        (Finset.univ.filter fun g => χ g = 0).card := fun y hy => by
      rw [← hfib y, Finset.filter_filter]
      congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hy, h⟩⟩
    rw [Finset.sum_congr rfl this]
    simp
  rw [hY, hall]
  ring
section Shell
variable {F : OrthogonalNormalFrame} {s : Fin 4 → ℕ+} {Γ : PeriodSublattice 1}
def levelMod (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) (i : Fin 4) : Γ.QuotientTorus →+ ZMod (s i : ℕ) :=
  QuotientAddGroup.lift Γ.periods ((Int.castAddHom (ZMod (s i : ℕ))).comp (levelHom F i))
    fun γ hγ => by
      obtain ⟨k, -, hk⟩ := levelHom_period hF hΓ hγ
      simp [hk i]
theorem levelMod_quotientMap (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) (i : Fin 4) (x : LatticePoint 1) :
    levelMod hF hΓ i (Γ.quotientMap x) = (levelHom F i x : ZMod (s i : ℕ)) :=
  rfl
theorem levelMod_surjective (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) (i : Fin 4) : Function.Surjective (levelMod hF hΓ i) := by
  intro y
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective y
  obtain ⟨μ, hμ⟩ := (normalVector_props (F.isNormal i)).2.2
  have h1 : levelHom F i (axisStep 1 μ) = 1 := by
    apply Int.cast_injective (α := ℝ)
    rw [levelHom_cast, hμ]
    simp
  refine ⟨Γ.quotientMap (m • axisStep 1 μ), ?_⟩
  rw [levelMod_quotientMap, map_zsmul, h1]
  simp
theorem exists_levelHom_near_end {ϱ : ℕ+} {x : LatticePoint 1} (hx : x ∈ F.boundaryShell s ϱ) :
    ∃ i, levelHom F i x ∈
      Finset.Icc (0 : ℤ) (2 * ((ϱ : ℕ) : ℤ) - 1) ∪
        Finset.Icc (((s i : ℕ) : ℤ) - 2 * ((ϱ : ℕ) : ℤ)) (((s i : ℕ) : ℤ) - 1) := by
  obtain ⟨hbox, y, hy, hxy⟩ := hx
  rw [mem_fundamentalBox_iff] at hy
  push Not at hy
  obtain ⟨i, hi⟩ := hy
  have hb : |levelHom F i y - levelHom F i x| ≤ 2 * ((ϱ : ℕ) : ℤ) := by
    have hr : ((|levelHom F i y - levelHom F i x| : ℤ) : ℝ) ≤ ((2 * ((ϱ : ℕ) : ℤ) : ℤ) : ℝ) := by
      push_cast
      rw [levelHom_cast, levelHom_cast, ← dotProduct_sub]
      refine ((normalVector_props (F.isNormal i)).1 _).trans ?_
      linarith
    exact_mod_cast hr
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  obtain ⟨h0, h1⟩ := (mem_fundamentalBox_iff F s x).1 hbox i
  refine ⟨i, ?_⟩
  simp only [Finset.mem_union, Finset.mem_Icc]
  by_cases hy0 : 0 ≤ levelHom F i y
  · have := hi hy0
    right
    omega
  · left
    omega
theorem ncard_boundaryShell_le (hF : RectangularPeriodVectors)
    (hΓ : Γ.IsBoxShaped F s) [Finite Γ.QuotientTorus] (ϱ : ℕ+) :
    ((F.boundaryShell s ϱ).ncard : ℝ) ≤
      4 * ((ϱ : ℕ) : ℝ) * (Nat.card Γ.QuotientTorus : ℝ) * ∑ i, (((s i : ℕ) : ℝ))⁻¹ := by
  classical
  have := Fintype.ofFinite Γ.QuotientTorus
  let Y : ∀ i, Finset (ZMod (s i : ℕ)) := fun i =>
    (Finset.Icc (0 : ℤ) (2 * ((ϱ : ℕ) : ℤ) - 1) ∪
      Finset.Icc (((s i : ℕ) : ℤ) - 2 * ((ϱ : ℕ) : ℤ)) (((s i : ℕ) : ℤ) - 1)).image
        fun m : ℤ => (m : ZMod (s i : ℕ))
  let A : Fin 4 → Finset Γ.QuotientTorus := fun i =>
    Finset.univ.filter fun g => levelMod hF hΓ i g ∈ Y i
  have hsub : (F.boundaryShell s ϱ).ncard ≤ (Finset.univ.biUnion A).card := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn Γ.quotientMap ?_ ?_ (Finset.finite_toSet _)
    · intro x hx
      obtain ⟨i, hi⟩ := exists_levelHom_near_end hx
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_image.2 ⟨_, hi, rfl⟩⟩⟩)
    · intro x hx y hy h
      exact eq_of_mem_fundamentalBox hF hΓ hx.1 hy.1 ((quotientMap_eq_iff x y).1 h)
  have hA : ∀ i, ((A i).card : ℝ) ≤
      4 * ((ϱ : ℕ) : ℝ) * (Nat.card Γ.QuotientTorus : ℝ) * (((s i : ℕ) : ℝ))⁻¹ := fun i => by
    have : NeZero (s i : ℕ) := ⟨(s i).ne_zero⟩
    have h1 := card_filter_mem_mul (s i : ℕ) (levelMod hF hΓ i)
      (levelMod_surjective hF hΓ i) (Y i)
    have hY : (Y i).card ≤ 4 * (ϱ : ℕ) := by
      refine Finset.card_image_le.trans ((Finset.card_union_le _ _).trans ?_)
      simp only [Int.card_Icc]
      omega
    have hsr : (0 : ℝ) < ((s i : ℕ) : ℝ) := by exact_mod_cast (s i).pos
    have h2 : ((A i).card : ℝ) * ((s i : ℕ) : ℝ) =
        ((Y i).card : ℝ) * (Nat.card Γ.QuotientTorus : ℝ) := by
      rw [Nat.card_eq_fintype_card, mul_comm]
      exact_mod_cast h1
    have hYr : ((Y i).card : ℝ) ≤ 4 * ((ϱ : ℕ) : ℝ) := by exact_mod_cast hY
    rw [← div_eq_mul_inv, le_div_iff₀ hsr, h2]
    exact mul_le_mul_of_nonneg_right hYr (Nat.cast_nonneg _)
  calc ((F.boundaryShell s ϱ).ncard : ℝ) ≤ ((Finset.univ.biUnion A).card : ℝ) := by
        exact_mod_cast hsub
    _ ≤ ∑ i, ((A i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ i, 4 * ((ϱ : ℕ) : ℝ) * (Nat.card Γ.QuotientTorus : ℝ) * (((s i : ℕ) : ℝ))⁻¹ :=
        Finset.sum_le_sum fun i _ => hA i
    _ = 4 * ((ϱ : ℕ) : ℝ) * (Nat.card Γ.QuotientTorus : ℝ) * ∑ i, (((s i : ℕ) : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
end Shell
theorem representsQuotientWithThinShell_holds (hV : RectangularPeriodVectors)
    (hFin : FiniteTorusPartitionsAndLifts) : FundamentalBox.RepresentsQuotientWithThinShell := by
  intro F s Γ hΓ
  have : Finite Γ.QuotientTorus := ((hFin 1 one_pos Γ).1 Γ.periods le_rfl).finite_quotientTorus
  have hbij : Function.Bijective fun x : F.fundamentalBox s => Γ.quotientMap (x : LatticePoint 1) := by
    constructor
    · intro x y h
      exact Subtype.ext (eq_of_mem_fundamentalBox hV hΓ x.2 y.2 ((quotientMap_eq_iff _ _).1 h))
    · intro c
      obtain ⟨x, ⟨hx, hc⟩, -⟩ := existsUnique_mem_fundamentalBox hV hΓ c
      exact ⟨⟨x, hx⟩, hc⟩
  have hcard : Nat.card (F.fundamentalBox s) = Nat.card Γ.QuotientTorus :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  have : Finite (F.fundamentalBox s) := Finite.of_injective _ hbij.1
  have hfinite : (F.fundamentalBox s).Finite := Set.toFinite _
  have hncard : (F.fundamentalBox s).ncard = Nat.card Γ.QuotientTorus := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  refine ⟨existsUnique_mem_fundamentalBox hV hΓ, ?_, existsUnique_boxLink hV hΓ, fun ϱ => ?_⟩
  · rw [← hfinite.cast_ncard_eq, hncard]
    rfl
  · rw [hncard]
    simpa [Constants.BoxTorus.layerNumber] using ncard_boundaryShell_le hV hΓ ϱ
end BoxQuotient
end InfiniteLattice
end YangMills.Construction
