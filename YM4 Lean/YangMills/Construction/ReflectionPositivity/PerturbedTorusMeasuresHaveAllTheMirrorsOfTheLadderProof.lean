import YangMills.Construction.InfiniteLattice.LowerTangentUpperTangentAndTheInequalityInFiniteVolumeProof
import YangMills.Construction.ReflectionPositivity.PerturbedTorusMeasuresHaveAllTheMirrorsOfTheLadder
import YangMills.Construction.ReflectionPositivity.ReflectionPositivityOnSplitTori
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Matrix ComplexOrder
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
namespace RungReflection
theorem plusHalf_eq_iUnion_slabAt (S : SlabDecomposition) (k : ℤ) :
    S.period.plusHalf S.normal S.halfPeriod (S.level k) =
      ⋃ i : Fin S.count, S.slabAt (k + ((i : ℕ) : ℤ)) := by
  have hpos : (0 : ℝ) < (S.width : ℝ) := by
    have := S.two_le_width
    exact_mod_cast (by omega : 0 < S.width)
  have hJ := S.one_le_count
  have hlevel : ∀ m : ℤ, S.level (k + m) = S.level k + (m : ℝ) * (S.width : ℝ) := by
    intro m
    simp only [SlabDecomposition.level]
    push_cast
    ring
  have hz : (S.halfPeriod : ℝ) = (S.count : ℝ) * (S.width : ℝ) := by
    simp [SlabDecomposition.halfPeriod]
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu, h1, h2⟩
    set x : ℝ := (u - S.level k) / (S.width : ℝ) with hx
    have hu' : u = S.level k + x * (S.width : ℝ) := by
      rw [hx]
      field_simp
      ring
    have hx0 : 0 ≤ x := div_nonneg (by linarith) hpos.le
    have hxJ : x ≤ (S.count : ℝ) := by
      rw [hx, div_le_iff₀ hpos]
      rw [hz] at h2
      linarith
    have hexists : ∃ i : ℕ, i < S.count ∧ (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
      by_cases hf : ⌊x⌋₊ < S.count
      · exact ⟨⌊x⌋₊, hf, Nat.floor_le hx0, (Nat.lt_floor_add_one x).le⟩
      · refine ⟨S.count - 1, by omega, ?_, ?_⟩
        · have h3 : (S.count : ℝ) ≤ x := by
            have h4 : ((S.count : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast not_lt.mp hf
            exact h4.trans (Nat.floor_le hx0)
          have h5 : ((S.count - 1 : ℕ) : ℝ) ≤ (S.count : ℝ) := by exact_mod_cast Nat.sub_le _ _
          linarith
        · have : ((S.count - 1 : ℕ) : ℝ) = (S.count : ℝ) - 1 := by
            rw [Nat.cast_sub hJ]
            simp
          rw [this]
          linarith
    obtain ⟨i, hi, hxi, hxi'⟩ := hexists
    refine ⟨⟨i, hi⟩, u, hu, ?_, ?_⟩
    · change S.level (k + (i : ℤ)) ≤ u
      rw [hlevel, hu']
      have := mul_le_mul_of_nonneg_right hxi hpos.le
      push_cast
      linarith
    · change u ≤ S.level (k + (i : ℤ) + 1)
      rw [add_assoc, hlevel, hu']
      have := mul_le_mul_of_nonneg_right hxi' hpos.le
      push_cast
      linarith
  · rintro ⟨i, u, hu, h1, h2⟩
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (S.count : ℝ) := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨u, hu, ?_, ?_⟩
    · rw [hlevel] at h1
      have := mul_nonneg hi0 hpos.le
      push_cast at h1
      linarith
    · rw [add_assoc, hlevel] at h2
      rw [hz]
      have := mul_le_mul_of_nonneg_right hi hpos.le
      push_cast at h2
      linarith
theorem quotientMap_add_of_mem (Γ : PeriodSublattice 1) (x : LatticePoint 1) {γ : LatticePoint 1}
    (hγ : γ ∈ Γ.periods) : Γ.quotientMap (x + γ) = Γ.quotientMap x := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.quotientMap_add_period <;> assumption
theorem periodize_mem_boundedAlgebra {Γ : PeriodSublattice 1} (hext : Γ.QuotientLiftFacts)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) {T : Set Γ.QuotientTorus}
    (hT : ∀ b ∈ observableSupport F, Γ.quotientMap b.initial ∈ T ∧ Γ.quotientMap b.terminal ∈ T) :
    Γ.periodize F ∈ Γ.boundedAlgebra (Γ.linksInside T) := by
  obtain ⟨C, hC⟩ := hF.1.2
  refine ⟨(hext.continuous_periodize F hF).measurable, ⟨C, fun U => hC _⟩, ?_⟩
  intro U U' h
  refine hext.periodize_dependsOn F hF U U' fun c hc => h c ?_
  obtain ⟨b, hb, rfl⟩ := hc
  obtain ⟨γ, hγ, hrep⟩ := Γ.exists_linkRep_eq b
  intro s hs
  rw [PeriodSublattice.linkEndpoints, hrep] at hs
  rcases hs with rfl | hs
  · change Γ.quotientMap (b.1.initial + γ) ∈ T
    rw [quotientMap_add_of_mem Γ _ hγ]
    exact (hT b.1 hb).1
  · have hs' : s = Γ.quotientMap (b.1.terminal + γ) := hs
    rw [hs', quotientMap_add_of_mem Γ _ hγ]
    exact (hT b.1 hb).2
theorem pullbackField_shift_add (v γ : LatticePoint 1) (W : GaugeField 1) :
    (shift (v + γ)).pullbackField W =
      (shift v).pullbackField ((shift γ).pullbackField W) := by
  refine Subtype.ext (funext fun b => ?_)
  change W.1 _ = W.1 _
  refine congrArg W.1 (Link.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · change (b.initial : AmbientSpace) + ((v + γ : LatticePoint 1) : AmbientSpace) =
      ((b.initial : AmbientSpace) + v) + γ
    rw [AddSubgroup.coe_add, add_assoc]
  · change (b.terminal : AmbientSpace) + ((v + γ : LatticePoint 1) : AmbientSpace) =
      ((b.terminal : AmbientSpace) + v) + γ
    rw [AddSubgroup.coe_add, add_assoc]
theorem periodize_translate_congr (𝔸 : LocalObservableArray) {Γ : PeriodSublattice 1}
    (hext : Γ.QuotientLiftFacts) {v v' : 𝔸.sublattice}
    (h : (v : 𝔸.Cosets Γ) = v') (ι : Fin 𝔸.size) :
    Γ.periodize (𝔸.translate (v, ι)) = Γ.periodize (𝔸.translate (v', ι)) := by
  have hmem : (((-v + v' : 𝔸.sublattice)) : LatticePoint 1) ∈ Γ.periods :=
    AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h)
  have hv : (v' : LatticePoint 1) = (v : LatticePoint 1) + ((-v + v' : 𝔸.sublattice) : LatticePoint 1) := by
    simp
  funext U
  change 𝔸.gen ι ((shift (v : LatticePoint 1)).pullbackField (Γ.lift U)) =
    𝔸.gen ι ((shift (v' : LatticePoint 1)).pullbackField (Γ.lift U))
  rw [hv, pullbackField_shift_add, hext.lift_shift_invariant U _ hmem]
theorem finsum_mem_eq_sum_ite {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] (f : I → ℂ) :
    ∑ᶠ (c : I) (_ : P c), f c = ∑ c, if P c then f c else 0 := by
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun c _ => finsum_eq_if
theorem reflected_residue_iff (J : ℕ) (hJ : 1 ≤ J) (j k : ℤ) :
    (∃ i : ℕ, i < J ∧ (((2 * k - 1 - j : ℤ)) : ZMod (2 * J)) = ((k + (i : ℤ) : ℤ) : ZMod (2 * J))) ↔
      ¬ ∃ i : ℕ, i < J ∧ ((j : ℤ) : ZMod (2 * J)) = ((k + (i : ℤ) : ℤ) : ZMod (2 * J)) := by
  have hN : (0 : ℤ) < ((2 * J : ℕ) : ℤ) := by
    have : 0 < 2 * J := by omega
    exact_mod_cast this
  set N : ℤ := ((2 * J : ℕ) : ℤ) with hNdef
  have hiff : ∀ a b : ℤ, ((a : ℤ) : ZMod (2 * J)) = ((b : ℤ) : ZMod (2 * J)) ↔ N ∣ b - a :=
    fun a b => ZMod.intCast_eq_intCast_iff_dvd_sub a b (2 * J)
  simp only [hiff]
  set m : ℤ := (j - k) % N with hm
  have hm0 : 0 ≤ m := Int.emod_nonneg _ hN.ne'
  have hmN : m < N := Int.emod_lt_of_pos _ hN
  obtain ⟨q, hq⟩ : ∃ q : ℤ, j - k = m + N * q :=
    ⟨(j - k) / N, by rw [hm]; exact (Int.emod_add_mul_ediv _ _).symm⟩
  have hsmall : ∀ x : ℤ, 0 < x → x < N → ¬ N ∣ x := fun x h0 h1 h =>
    absurd (Int.le_of_dvd h0 h) (by omega)
  by_cases hmJ : m < (J : ℤ)
  · constructor
    · rintro ⟨i, hi, hd⟩
      exfalso
      have h1 : N ∣ m + 1 + (i : ℤ) := by
        have : m + 1 + (i : ℤ) = (k + (i : ℤ) - (2 * k - 1 - j)) - N * q := by
          linear_combination -hq
        rw [this]
        exact dvd_sub hd (dvd_mul_right _ _)
      exact hsmall _ (by omega) (by omega) h1
    · intro hneg
      exfalso
      apply hneg
      refine ⟨m.toNat, by omega, ?_⟩
      rw [Int.toNat_of_nonneg hm0]
      have : k + m - j = -(N * q) := by linear_combination -hq
      rw [this]
      exact (dvd_neg).mpr (dvd_mul_right _ _)
  · constructor
    · rintro - ⟨i, hi, hd⟩
      have h1 : N ∣ m - (i : ℤ) := by
        have : m - (i : ℤ) = -(k + (i : ℤ) - j) - N * q := by linear_combination -hq
        rw [this]
        exact dvd_sub ((dvd_neg).mpr hd) (dvd_mul_right _ _)
      exact hsmall _ (by omega) (by omega) h1
    · intro _
      refine ⟨(N - 1 - m).toNat, by omega, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      have : k + (N - 1 - m) - (2 * k - 1 - j) = N * (q + 1) := by linear_combination hq
      rw [this]
      exact dvd_mul_right _ _
variable {L : MirrorLadder}
theorem normalLevelPair_ext {P Q : NormalLevelPair 1} (h₁ : P.normal = Q.normal)
    (h₂ : P.level = Q.level) : P = Q := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.normalLevelPair_ext <;> assumption
theorem levelPair_eq_rungAt {w : ℤ} {S : SlabDecomposition} (hS : L.IsAdaptedSlabDecomposition w S)
    (k : ℤ) : S.levelPair k = L.rungAt k :=
  normalLevelPair_ext hS.normal_eq (by
    change S.baseLevel + (k : ℝ) * (S.width : ℝ) = L.offset + (k : ℝ) * (L.spacing : ℝ)
    rw [hS.baseLevel_eq, hS.width_eq])
theorem quotientMap_mem_slabAt {w : ℤ} {S : SlabDecomposition} (hS : L.IsAdaptedSlabDecomposition w S)
    {j : ℤ} {x : LatticePoint 1} (hx : (x : AmbientSpace) ∈ L.slab j) :
    S.period.quotientMap x ∈ S.slabAt j := by
  refine ⟨S.normal ⬝ᵥ (x : AmbientSpace), ⟨x, rfl, 0, by simp⟩, ?_, ?_⟩
  · change S.baseLevel + (j : ℝ) * (S.width : ℝ) ≤ _
    rw [hS.baseLevel_eq, hS.width_eq, hS.normal_eq]
    exact hx.1
  · change _ ≤ S.baseLevel + ((j + 1 : ℤ) : ℝ) * (S.width : ℝ)
    rw [hS.baseLevel_eq, hS.width_eq, hS.normal_eq]
    push_cast
    exact hx.2
theorem isAdaptedTorus (hAd : AdaptedTorusProperties) {w : ℤ} {S : SlabDecomposition}
    (hS : L.IsAdaptedSlabDecomposition w S) : L.IsAdaptedTorus S.period S.count where
  one_le := S.one_le_count
  le_normalSublattice := by
    intro x hx
    have hle := (hAd L.normal L.normal_mem L.spacing (S.count : ℤ) w hS.admissible).2.2.2.2.1
    have hx' : (x : AmbientSpace) ∈ S.period.toAmbient := ⟨x, hx, rfl⟩
    rw [hS.toAmbient_eq] at hx'
    exact AddSubgroup.mem_addSubgroupOf.mpr (hle hx')
  splits := by
    have h := S.splits
    rwa [hS.normal_eq, hS.width_eq] at h
theorem linearReflect_sub (n x y : AmbientSpace) :
    linearReflect n x - linearReflect n y = linearReflect n (x - y) := by
  simp only [linearReflect_apply, dotProduct_sub, mul_sub, sub_smul]
  abel
theorem linearReflect_involutive {n : AmbientSpace} (hn : n ∈ normalSet) (x : AmbientSpace) :
    linearReflect n (linearReflect n x) = x := by apply _root_.YangMills.Construction.NormalFamilies.FiniteVolumeTangentBounds.linearReflect_linearReflect <;> assumption
theorem coset_eq_iff (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1) (v v' : 𝔸.sublattice) :
    (v : 𝔸.Cosets Γ) = v' ↔
      ((v' : LatticePoint 1) : AmbientSpace) - ((v : LatticePoint 1) : AmbientSpace) ∈ Γ.toAmbient := by
  constructor
  · intro h
    have hmem : (((-v + v' : 𝔸.sublattice)) : LatticePoint 1) ∈ Γ.periods :=
      AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h)
    refine ⟨_, hmem, ?_⟩
    change ((((-v + v' : 𝔸.sublattice)) : LatticePoint 1) : AmbientSpace) = _
    simp only [AddSubgroup.coe_add, NegMemClass.coe_neg]
    abel
  · rintro ⟨γ, hγ, h⟩
    refine QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
    have : (((-v + v' : 𝔸.sublattice)) : LatticePoint 1) = γ := by
      refine Subtype.ext ?_
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg]
      rw [show ((γ : LatticePoint 1) : AmbientSpace) = _ from h]
      abel
    rw [this]
    exact hγ
theorem exists_bijective_on_cosets (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1)
    [Finite (𝔸.Cosets Γ)]
    (lin : AmbientSpace → AmbientSpace) (hsub : ∀ x y, lin x - lin y = lin (x - y))
    (hinv : ∀ x, lin (lin x) = x) (hΓ : ∀ x ∈ Γ.toAmbient, lin x ∈ Γ.toAmbient)
    (d : AmbientSpace) (e : 𝔸.Label ≃ 𝔸.Label)
    (he₁ : ∀ i, (((e i).1 : LatticePoint 1) : AmbientSpace) = lin ((i.1 : LatticePoint 1) : AmbientSpace) + d)
    (he₂ : ∀ i, (e i).2 = Fin.rev i.2) :
    ∃ g : 𝔸.Cosets Γ × Fin 𝔸.size → 𝔸.Cosets Γ × Fin 𝔸.size, Function.Bijective g ∧
      ∀ i : 𝔸.Label, g ((i.1 : 𝔸.Cosets Γ), i.2) = (((e i).1 : 𝔸.Cosets Γ), (e i).2) := by
  have hcong : ∀ i i' : 𝔸.Label, (i.1 : 𝔸.Cosets Γ) = i'.1 ↔
      ((e i).1 : 𝔸.Cosets Γ) = (e i').1 := by
    intro i i'
    rw [coset_eq_iff, coset_eq_iff, he₁, he₁, add_sub_add_right_eq_sub, hsub]
    exact ⟨hΓ _, fun h => by simpa only [hinv] using hΓ _ h⟩
  refine ⟨fun c => (((e (Quotient.out c.1, c.2)).1 : 𝔸.Cosets Γ), (e (Quotient.out c.1, c.2)).2),
    Finite.injective_iff_bijective.mp ?_, fun i => ?_⟩
  · intro c c' h
    refine Prod.ext ?_ ?_
    · have h₁ := (hcong (Quotient.out c.1, c.2) (Quotient.out c'.1, c'.2)).mpr
        (congrArg Prod.fst h)
      simpa only [QuotientAddGroup.out_eq'] using h₁
    · have h₂ := congrArg Prod.snd h
      simp only [he₂] at h₂
      exact Fin.rev_injective h₂
  · refine Prod.ext ?_ ?_
    · exact (hcong (Quotient.out (i.1 : 𝔸.Cosets Γ), i.2) i).mp (QuotientAddGroup.out_eq' _)
    · simp only [he₂]
theorem upperHalf_properties (hAd : AdaptedTorusProperties) (hDe : SplitTorusDescent)
    (hEx : PeriodicQuotient.FinitenessClaim)
    (hFo : FoldedArrayMirrorProperties) (hPu : SplitTorusPullbacks)
    {β : ℝ} (hβ : 0 < β) (A : L.SlabZeroGenerator) {w : ℤ} {S : SlabDecomposition}
    (hS : L.IsAdaptedSlabDecomposition w S) (t : ℝ) (k : ℤ) :
    (∀ U, (A.upperHalfFoldedSum S.period S.count t k U).im = 0) ∧
    A.upperHalfFoldedSum S.period S.count t k ∈
      S.period.plusAlgebra S.normal S.halfPeriod (S.level k) ∧
    (fun U => ((t * A.foldedArray.periodicSum S.period U : ℝ) : ℂ)) =
      (fun U => A.upperHalfFoldedSum S.period S.count t k U +
        S.reflectAct k (A.upperHalfFoldedSum S.period S.count t k) U) := by
  classical
  have hext := hEx.1 S.period
  have hfil := isAdaptedTorus hAd hS
  have hJ := S.one_le_count
  have hfin : Finite (A.foldedArray.Cosets S.period) := by
    have := hext.periods_finiteIndex
    exact AddSubgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (A.foldedArray.Cosets S.period × Fin A.foldedArray.size)
  obtain ⟨-, -, -, hlies, -, -, -, hk⟩ := hFo L A
  obtain ⟨-, -, e, he, hefile⟩ := hk k
  have hd := hDe S.period S.normal S.normal_mem S.halfPeriod (S.level k)
    (S.level_allowed k) 0 S.splits
  obtain ⟨-, -, -, -, -, hlin, -⟩ := hd
  rw [hS.normal_eq] at hlin
  obtain ⟨g, hg, hgi⟩ := exists_bijective_on_cosets A.foldedArray S.period (linearReflect L.normal)
    (linearReflect_sub L.normal) (linearReflect_involutive L.normal_mem)
    (fun x hx => by
      have hx' : linearReflect L.normal x ∈
          linearReflect L.normal '' (S.period.toAmbient : Set AmbientSpace) := ⟨x, hx, rfl⟩
      rw [hlin] at hx'
      exact hx')
    _ e (fun i => (he i).1) (fun i => (he i).2.1)
  set T : A.foldedArray.Cosets S.period × Fin A.foldedArray.size →
      S.period.QuotientField → ℂ :=
    fun c => S.period.periodize
      (A.foldedArray.translate (A.foldedArray.cosetRep S.period c.1, c.2)) with hT
  set P : A.foldedArray.Cosets S.period × Fin A.foldedArray.size → Prop :=
    fun c => A.TermInUpperHalf S.period S.count k c with hP
  have hE : ∀ U, A.upperHalfFoldedSum S.period S.count t k U =
      (t : ℂ) * ∑ c, if P c then T c U else 0 := fun U =>
    congrArg _ (finsum_mem_eq_sum_ite P fun c => T c U)
  have hreal : ∀ c U, (T c U).im = 0 := fun c U => A.foldedArray.gen_im c.2 _
  have hterm : ∀ i : A.foldedArray.Label, A.foldedArray.translate i ∈ continuousLocalFunctions 1 :=
    fun i => actOn_mem_continuousLocalFunctions _ (continuous_add_const _)
      (A.foldedArray.gen_mem i.2)
  have hout : ∀ c : A.foldedArray.Cosets S.period × Fin A.foldedArray.size,
      ((A.foldedArray.cosetRep S.period c.1 : A.foldedArray.sublattice) :
        A.foldedArray.Cosets S.period) = c.1 := fun c => QuotientAddGroup.out_eq' _
  have hmemT : ∀ c, P c → T c ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level k) := by
    rintro c ⟨r, hr, hfile⟩
    obtain ⟨j, hj⟩ := MirrorLadder.exists_foldedLabelInSlab A
      (A.foldedArray.cosetRep S.period c.1, c.2)
    have hcls : ((j : ℤ) : ZMod (2 * S.count)) = ((k + (r : ℤ) : ℤ) : ZMod (2 * S.count)) :=
      (MirrorLadder.termInSlabClass_folded_iff A hfil c _ (hout c) hj).mp hfile
    have hslab : S.slabAt j = S.slabAt (k + (r : ℤ)) := by
      rw [← S.slabOfClass_intCast j, hcls, S.slabOfClass_intCast]
    have hsub : S.slabAt j ⊆ S.period.plusHalf S.normal S.halfPeriod (S.level k) := by
      rw [hslab, plusHalf_eq_iUnion_slabAt]
      exact Set.subset_iUnion (fun i : Fin S.count => S.slabAt (k + ((i : ℕ) : ℤ))) ⟨r, hr⟩
    have hl := hlies j _ hj
    exact periodize_mem_boundedAlgebra hext (hterm _) fun b hb =>
      ⟨hsub (quotientMap_mem_slabAt hS (hl b hb).1), hsub (quotientMap_mem_slabAt hS (hl b hb).2)⟩
  have hEfun : A.upperHalfFoldedSum S.period S.count t k =
      (t : ℂ) • ∑ c, if P c then T c else 0 := by
    funext U
    rw [hE, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    split_ifs <;> rfl
  have hR : S.reflectSym k = (L.rungAt k).reflectSymmetry := by
    rw [SlabDecomposition.reflectSym, levelPair_eq_rungAt hS]
  have hiso : IsClassIsometry S.normal (S.reflectSym k).toFun :=
    isClassIsometry_reflectAcross (S.level_allowed k)
  have hpull := (hPu β hβ S.period S.normal S.normal_mem S.halfPeriod S.splits).2.1 _ hiso
  have hgT : ∀ c U, T c (S.period.pullbackField (S.reflectSym k) U) = T (g c) U := by
    intro c U
    have hc := hgi (A.foldedArray.cosetRep S.period c.1, c.2)
    have hc' : (((A.foldedArray.cosetRep S.period c.1 : A.foldedArray.sublattice) :
        A.foldedArray.Cosets S.period), c.2) = c := Prod.ext (hout c) rfl
    rw [hc'] at hc
    have h₁ := hpull.2.2.2.2.2.1 _ (hterm (A.foldedArray.cosetRep S.period c.1, c.2))
    have h₂ : (S.reflectSym k).actOn
        (A.foldedArray.translate (A.foldedArray.cosetRep S.period c.1, c.2)) =
        A.foldedArray.translate (e (A.foldedArray.cosetRep S.period c.1, c.2)) := by
      rw [hR]
      exact (he _).2.2
    rw [h₂] at h₁
    have h₃ := congrFun h₁ U
    change _ = T c (S.period.pullbackField (S.reflectSym k) U) at h₃
    rw [← h₃, hc]
    exact congrFun (periodize_translate_congr A.foldedArray hext (hout (_, _)).symm _) U
  have hgP : ∀ c, P (g c) ↔ ¬ P c := by
    intro c
    obtain ⟨j, hj⟩ := MirrorLadder.exists_foldedLabelInSlab A
      (A.foldedArray.cosetRep S.period c.1, c.2)
    have hc := hgi (A.foldedArray.cosetRep S.period c.1, c.2)
    have hc' : (((A.foldedArray.cosetRep S.period c.1 : A.foldedArray.sublattice) :
        A.foldedArray.Cosets S.period), c.2) = c := Prod.ext (hout c) rfl
    rw [hc'] at hc
    have hj' := (hefile _ j).mp hj
    have hiff₁ : ∀ r : ZMod (2 * S.count),
        MirrorLadder.TermInSlabClass A.foldedArray
          (MirrorLadder.FoldedLabelInSlab A) S.period S.count c r ↔
          ((j : ℤ) : ZMod (2 * S.count)) = r := fun r =>
      MirrorLadder.termInSlabClass_folded_iff A hfil c r (hout c) hj
    have hiff₂ : ∀ r : ZMod (2 * S.count),
        MirrorLadder.TermInSlabClass A.foldedArray
          (MirrorLadder.FoldedLabelInSlab A) S.period S.count (g c) r ↔
          (((2 * k - 1 - j : ℤ)) : ZMod (2 * S.count)) = r := fun r => by
      rw [hc]
      exact MirrorLadder.termInSlabClass_folded_iff A hfil _ r rfl hj'
    simp only [hP, MirrorLadder.SlabZeroGenerator.TermInUpperHalf, hiff₁, hiff₂]
    exact reflected_residue_iff S.count hJ j k
  have hsum : ∀ U, (∑ c, if P c then T c (S.period.pullbackField (S.reflectSym k) U)
      else 0) = ∑ c, if ¬ P c then T c U else 0 := by
    intro U
    rw [← hg.sum_comp fun c => if ¬ P c then T c U else 0]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hgT, hgP, not_not]
  have hfinsum : ∀ U, A.foldedArray.periodicSum S.period U = ∑ c, (T c U).re := fun U =>
    finsum_eq_sum_of_fintype _
  refine ⟨fun U => ?_, ?_, ?_⟩
  · rw [hE]
    have h0 : (∑ c, if P c then T c U else 0).im = 0 := by
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      split_ifs
      · exact hreal c U
      · rfl
    simp [Complex.mul_im, h0]
  · rw [hEfun]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun c _ => ?_) _
    split_ifs with h
    · exact hmemT c h
    · exact zero_mem _
  · funext U
    change _ = A.upperHalfFoldedSum S.period S.count t k U +
      A.upperHalfFoldedSum S.period S.count t k
        (S.period.pullbackField (S.reflectSym k) U)
    rw [hE, hE, hsum, ← mul_add, ← Finset.sum_add_distrib, hfinsum]
    push_cast
    refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    have : ((T c U).re : ℂ) = T c U := Complex.ext rfl (by simp [hreal c U])
    rw [this]
    by_cases h : P c <;> simp [h]
theorem integral_perturbedReflMeasure (Γ : PeriodSublattice 1) (β : ℝ) (P : NormalLevelPair 1)
    (E : Γ.QuotientField → ℝ) (hW : Measurable (Γ.perturbedReflWeight β P E))
    (hW₀ : ∀ U, 0 ≤ Γ.perturbedReflWeight β P E U) (G : Γ.QuotientField → ℂ) :
    ∫ U, G U ∂(Γ.perturbedReflMeasure β P E) =
      ((ENNReal.ofReal (∫ U, Γ.perturbedReflWeight β P E U ∂Γ.quotientHaar))⁻¹).toReal •
        ∫ U, G U * (Γ.perturbedReflWeight β P E U : ℂ) ∂Γ.quotientHaar := by
  have hwd := integral_withDensity_eq_integral_toReal_smul (μ := Γ.quotientHaar)
    (f := fun U => ENNReal.ofReal (Γ.perturbedReflWeight β P E U))
    (ENNReal.measurable_ofReal.comp hW) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) G
  rw [PeriodSublattice.perturbedReflMeasure, integral_smul_measure, hwd]
  refine congrArg _ (integral_congr_ae (ae_of_all _ fun U => ?_))
  change (ENNReal.ofReal _).toReal • G U = _
  rw [ENNReal.toReal_ofReal (hW₀ U), Complex.real_smul, mul_comm]
theorem measurable_boltzmannWeight {Γ : PeriodSublattice 1} (hext : Γ.QuotientLiftFacts)
    (β : ℝ) : Measurable (Γ.boltzmannWeight β) := by
  have h : Continuous fun U : Γ.QuotientField =>
      ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := by
    have := hext.finite_quotientPlaquette
    have := Fintype.ofFinite Γ.QuotientPlaquette
    simp only [finsum_eq_sum_of_fintype]
    exact continuous_finsetSum _ fun p _ => hext.continuous_quotientFaceEnergy p
  exact (Real.continuous_exp.comp (continuous_const.mul h)).measurable
theorem tiltedTorusMeasureReflectsAtEveryRung (hAd : AdaptedTorusProperties)
    (hDe : SplitTorusDescent) (hEx : PeriodicQuotient.FinitenessClaim)
    (hFo : FoldedArrayMirrorProperties) (hPu : SplitTorusPullbacks)
    (hRP : SplitTorusReflectionPositivity) :
    TiltedTorusMeasureReflectsAtEveryRung := by
  intro β hβ L A w S hS t k E μ
  have hfacts : (∀ U, (E U).im = 0) ∧
      E ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level k) ∧
      (fun U => ((t * A.foldedArray.periodicSum S.period U : ℝ) : ℂ)) =
        (fun U => E U + S.reflectAct k E U) :=
    upperHalf_properties hAd hDe hEx hFo hPu hβ A hS t k
  obtain ⟨hEre, hEmem, hEq⟩ := hfacts
  have hext := hEx.1 S.period
  let Er : S.period.QuotientField → ℝ := fun U => (E U).re
  have hEc : (fun U => (Er U : ℂ)) = E := funext fun U => Complex.ext rfl (by simp [Er, hEre U])
  obtain ⟨-, -, -, -, -, -, h4⟩ := hRP β hβ S.period S.normal S.normal_mem S.halfPeriod S.splits
    (S.level k) (S.level_allowed k)
  obtain ⟨-, hpres, hpos⟩ := h4 Er (by rw [hEc]; exact hEmem)
  have hw : A.foldedArray.tiltedWeight S.period β t =
      S.period.perturbedReflWeight β (S.levelPair k) Er := by
    funext U
    have h := congrArg Complex.re (congrFun hEq U)
    simp only [Complex.ofReal_re, Complex.add_re] at h
    have h' : S.period.compPullback (S.levelPair k).reflectSymmetry Er U =
        (S.reflectAct k E U).re := rfl
    have h'' : Er U = (E U).re := rfl
    rw [LocalObservableArray.tiltedWeight, PeriodSublattice.perturbedReflWeight,
      PeriodSublattice.boltzmannWeight, ← Real.exp_add, h', h'', ← h]
    congr 1
    ring
  have hμ : μ = S.period.perturbedReflMeasure β (S.levelPair k) Er := by
    change A.foldedArray.tiltedMeasure S.period β t = _
    rw [LocalObservableArray.tiltedMeasure, LocalObservableArray.tiltedPartition, hw]
    rfl
  have hiso : IsClassIsometry S.normal (S.reflectSym k).toFun :=
    isClassIsometry_reflectAcross (S.level_allowed k)
  have hpull := (hPu β hβ S.period S.normal S.normal_mem S.halfPeriod S.splits).2.1 _ hiso
  have hErm : Measurable Er := Complex.measurable_re.comp hEmem.1
  have hWm : Measurable (S.period.perturbedReflWeight β (S.levelPair k) Er) := by
    have h₁ : Measurable fun U => Er (S.period.pullbackField (S.reflectSym k) U) :=
      hErm.comp hpull.1.continuous.measurable
    exact (Real.measurable_exp.comp (hErm.add h₁)).mul (measurable_boltzmannWeight hext β)
  have hW₀ : ∀ U, 0 ≤ S.period.perturbedReflWeight β (S.levelPair k) Er U := fun U =>
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  refine ⟨plusHalf_eq_iUnion_slabAt S k, hEre, hEmem, hEq, ?_, fun F hF => ?_⟩
  · rw [hμ]
    exact hpres
  · have key := integral_perturbedReflMeasure S.period β (S.levelPair k) Er hWm hW₀
      (fun U => S.conjReflectAt k F U * F U)
    rw [hμ, key, Complex.real_smul]
    exact mul_nonneg (Complex.zero_le_real.mpr ENNReal.toReal_nonneg) (hpos F hF)
end RungReflection
end YangMills.Construction.NormalFamilies
