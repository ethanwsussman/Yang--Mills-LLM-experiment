import YangMills.Construction.Continuum.FirstFactsOnSmoothTestFunctionsAndTuples
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Continuum.TheTwoFamiliesOfSeminormsCompared
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace.TupleFacts
open SmoothMaps TestFunctions
variable {n : ℕ}
theorem mem_smoothRealTupleSet_iff_complex (f : FnTuple n) :
    f ∈ smoothRealTupleSet n ↔ f ∈ smoothComplexTupleSet n ∧ ∀ i, IsRealValued (f i) := by
  constructor
  · rintro ⟨⟨hf₁, hf₂⟩, hf₃⟩
    exact ⟨⟨fun i => ⟨hf₃ i, (hf₁ i).2.2.1⟩, hf₂⟩, fun i => (hf₁ i).1⟩
  · rintro ⟨⟨hf₁, hf₂⟩, hf₃⟩
    exact ⟨⟨fun i => ⟨hf₃ i, (hf₁ i).1.of_le (by exact_mod_cast le_top), (hf₁ i).2,
      subset_univ _⟩, hf₂⟩, fun i => (hf₁ i).1⟩
section SupportBounds
variable {E : Type*} [TopologicalSpace E]
theorem tsupport_add_sub_union (u v : E → ℂ) : tsupport (u + v) ⊆ tsupport u ∪ tsupport v :=
  closure_minimal
    ((Function.support_add u v).trans (union_subset_union (subset_tsupport _) (subset_tsupport _)))
    ((isClosed_tsupport _).union (isClosed_tsupport _))
theorem tsupport_const_smul_sub (c : ℂ) (u : E → ℂ) : tsupport (c • u) ⊆ tsupport u :=
  closure_mono (Function.support_const_smul_subset c u)
theorem hasCompactSupport_add_of_both {u v : E → ℂ} (hu : HasCompactSupport u)
    (hv : HasCompactSupport v) : HasCompactSupport (u + v) :=
  IsCompact.of_isClosed_subset (IsCompact.union hu hv) (isClosed_tsupport _)
    (tsupport_add_sub_union u v)
theorem hasCompactSupport_const_smul_of (c : ℂ) {u : E → ℂ} (hu : HasCompactSupport u) :
    HasCompactSupport (c • u) :=
  IsCompact.of_isClosed_subset hu (isClosed_tsupport _) (tsupport_const_smul_sub c u)
end SupportBounds
theorem cylinderSet_eq_univ_pi (S : Fin n → Set (Fin 4 → ℝ)) : cylinderSet S = Set.pi univ S := by
  ext x
  simp [cylinderSet]
theorem tsupport_tensorProd_sub_cylinder (f : FnTuple n) :
    tsupport (tensorProd f) ⊆ cylinderSet fun i => tsupport (f i) := by
  refine closure_minimal (fun x hx i => subset_tsupport _ fun hzero => ?_) ?_
  · exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  · rw [cylinderSet_eq_univ_pi]
    exact isClosed_set_pi fun i _ => isClosed_tsupport _
theorem tensorProd_isTestFn {f : FnTuple n} (hf : f ∈ smoothComplexTupleSet n) :
    TensorIsTestFn f := by
  have hsub := tsupport_tensorProd_sub_cylinder f
  refine ⟨⟨?_, ?_, ?_⟩, hsub⟩
  · exact contDiff_prod fun i _ => (hf.1 i).1.comp (contDiff_apply ℝ (Fin 4 → ℝ) i)
  · refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hsub
    rw [cylinderSet_eq_univ_pi]
    exact isCompact_univ_pi fun i => (hf.1 i).2
  · intro x hx i j hxx
    by_contra hij
    have hx' := hsub hx
    exact Set.disjoint_left.1 (hf.2 i j hij) (hx' i) (hxx ▸ hx' j)
def offDiagTestFnSubmodule (n : ℕ) : Submodule ℂ (Config n → ℂ) where
  carrier := testFnOffDiag n
  add_mem' := fun {u v} hu hv =>
    ⟨hu.1.add hv.1, hasCompactSupport_add_of_both hu.2.1 hv.2.1,
      (tsupport_add_sub_union u v).trans (union_subset hu.2.2 hv.2.2)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩
  smul_mem' := fun c u hu =>
    ⟨contDiff_const.smul hu.1, hasCompactSupport_const_smul_of c hu.2.1,
      (tsupport_const_smul_sub c u).trans hu.2.2⟩
theorem tensorSpaceFacts_holds (hS : seminormComparison) (hn : 2 ≤ n) :
    TensorSpaceFacts n :=
  ⟨fun _ hf => tensorProd_isTestFn hf,
    fun f hf => tensorProd_isTestFn ((mem_smoothRealTupleSet_iff_complex f).1 hf).1,
    offDiagTestFnSubmodule n, rfl, (hS n (by omega)).2.2⟩
theorem seminormMonotone_holds : SeminormMonotone n := by
  intro φ _ k l k' l' hk hl
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  refine le_trans ?_ (le_iSup_of_le α (le_iSup_of_le (hα.trans hl) (le_iSup_of_le x le_rfl)))
  have hx : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hk) (norm_nonneg _))
theorem update_mem_smoothComplexTupleSet {h : FnTuple n} (hh : h ∈ smoothComplexTupleSet n)
    (i : Fin n) {g : (Fin 4 → ℝ) → ℂ} (hg : g ∈ smoothCompactSet (Fin 4 → ℝ))
    (hs : ∀ k, k ≠ i → Disjoint (tsupport g) (tsupport (h k))) :
    Function.update h i g ∈ smoothComplexTupleSet n := by
  refine ⟨fun k => ?_, fun k l hkl => ?_⟩
  · by_cases hk : k = i
    · subst hk
      simpa using hg
    · simpa [Function.update_of_ne hk] using hh.1 k
  · by_cases hk : k = i
    · subst hk
      rw [Function.update_self, Function.update_of_ne hkl.symm]
      exact hs l hkl.symm
    · rw [Function.update_of_ne hk]
      by_cases hl : l = i
      · subst hl
        rw [Function.update_self]
        exact (hs k hk).symm
      · rw [Function.update_of_ne hl]
        exact hh.2 k l hkl
theorem isRealValued_add {u v : (Fin 4 → ℝ) → ℂ} (hu : IsRealValued u) (hv : IsRealValued v) :
    IsRealValued (u + v) :=
  fun x => by simp [hu x, hv x]
theorem isRealValued_smul_of_im_zero {c : ℂ} (hc : c.im = 0) {u : (Fin 4 → ℝ) → ℂ}
    (hu : IsRealValued u) : IsRealValued (c • u) :=
  fun x => by simp [hu x, hc]
theorem isRealValued_update {h : FnTuple n} (hh : ∀ k, IsRealValued (h k)) (i : Fin n)
    {g : (Fin 4 → ℝ) → ℂ} (hg : IsRealValued g) (k : Fin n) :
    IsRealValued (Function.update h i g k) := by
  by_cases hk : k = i
  · subst hk
    simpa using hg
  · simpa [Function.update_of_ne hk] using hh k
theorem closedUnderEntryOps_holds : ClosedUnderComponentOps n := by
  intro i h h' hh hh' hag c
  have hsum : Function.update h i (h i + h' i) ∈ smoothComplexTupleSet n := by
    refine update_mem_smoothComplexTupleSet hh i
      ⟨(hh.1 i).1.add (hh'.1 i).1, hasCompactSupport_add_of_both (hh.1 i).2 (hh'.1 i).2⟩
      fun k hk => ?_
    refine Disjoint.mono_left (tsupport_add_sub_union _ _)
      (disjoint_union_left.2 ⟨hh.2 i k hk.symm, ?_⟩)
    rw [hag k hk]
    exact hh'.2 i k hk.symm
  have hmul : Function.update h i (c • h i) ∈ smoothComplexTupleSet n :=
    update_mem_smoothComplexTupleSet hh i
      ⟨contDiff_const.smul (hh.1 i).1, hasCompactSupport_const_smul_of c (hh.1 i).2⟩ fun k hk =>
        Disjoint.mono_left (tsupport_const_smul_sub _ _) (hh.2 i k hk.symm)
  refine ⟨hsum, hmul, fun hr hr' hc => ?_⟩
  have hre := ((mem_smoothRealTupleSet_iff_complex h).1 hr).2
  have hre' := ((mem_smoothRealTupleSet_iff_complex h').1 hr').2
  exact ⟨(mem_smoothRealTupleSet_iff_complex _).2
      ⟨hsum, isRealValued_update hre i (isRealValued_add (hre i) (hre' i))⟩,
    (mem_smoothRealTupleSet_iff_complex _).2
      ⟨hmul, isRealValued_update hre i (isRealValued_smul_of_im_zero hc (hre i))⟩⟩
theorem multilinearZeroComponent_holds : MultilinearZeroCoordinate n := by
  constructor
  · rintro T hT f ⟨i, hi⟩
    have h := (hT i f f fun _ _ => rfl).2 0 f (by simp [hi])
    simpa using h
  · rintro T hT f ⟨i, hi⟩
    have h := (hT i f f fun _ _ => rfl).2 0 f (by simp [hi])
    simpa using h
theorem minSupportSepPos_holds (hn : 2 ≤ n) : MinSupportSepPos n := by
  intro f hf
  have hpos : ∀ i j, i ≠ j → 0 < setDistR4 (tsupport (f i)) (tsupport (f j)) :=
    fun i j hij => SeparatedTuplesR4.setDistR4_pos_of_disjoint (hf.1 i).2
      (isClosed_tsupport _) (hf.2 i j hij)
  constructor
  · let G : Fin n × Fin n → ℝ≥0∞ := fun p =>
      if p.1 ≠ p.2 then setDistR4 (tsupport (f p.1)) (tsupport (f p.2)) else ⊤
    have hG : 0 < Finset.univ.inf G := by
      refine (Finset.lt_inf_iff (by simp)).2 fun p _ => ?_
      by_cases hp : p.1 ≠ p.2
      · simpa [G, hp] using hpos p.1 p.2 hp
      · simp only [G]
        rw [if_neg hp]
        exact ENNReal.zero_lt_top
    refine hG.trans_le (le_iInf fun i => le_iInf fun j => le_iInf fun hij => ?_)
    have hle := Finset.inf_le (f := G) (Finset.mem_univ (i, j))
    simpa [G, hij] using hle
  · intro hne
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    obtain ⟨a, ha⟩ := Function.ne_iff.1 (hne i)
    obtain ⟨b, hb⟩ := Function.ne_iff.1 (hne j)
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top
      (r := TorusMetric.euclidNormVec (a - b)))
    refine (iInf_le _ i).trans ((iInf_le _ j).trans ((iInf_le _ hij).trans ?_))
    exact (iInf₂_le a (subset_tsupport _ ha)).trans (iInf₂_le b (subset_tsupport _ hb))
theorem quotDist_euclidean (P : PeriodicSpace.Params) (y y' : Fin 4 → ℝ) :
    PeriodicSpace.Kind.quotDist P .euclidean y y' = TorusMetric.euclidNormVec (y - y') := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem tsupport_toComplexTuple (P : PeriodicSpace.Params)
    (g : PeriodicSpace.Kind.FnTuple P .euclidean n) (i : Fin n) :
    tsupport (toComplexTuple P g i) = PeriodicSpace.Kind.supportQ P .euclidean (g i) := by
  have hsupp : Function.support (toComplexTuple P g i) = {y | g i y ≠ 0} := by
    ext y
    simp only [Function.mem_support, toComplexTuple, ne_eq, Complex.ofReal_eq_zero]
    exact Iff.rfl
  rw [tsupport, hsupp]
  exact (SeparatedTuplesR4.closureWrt_euclid_eq_closure (quotDist_euclidean P) _).symm
theorem toComplexTuple_mem_iff (P : PeriodicSpace.Params)
    (g : PeriodicSpace.Kind.FnTuple P .euclidean n) :
    toComplexTuple P g ∈ smoothRealTupleSet n ↔
      g ∈ PeriodicSpace.Kind.sepC1Tuples P .euclidean n ∧
        ∀ i, PeriodicSpace.Kind.IsSmoothFn P .euclidean (g i) := by
  have hc : ∀ i, PeriodicSpace.Kind.IsCompactQ P .euclidean
      (PeriodicSpace.Kind.supportQ P .euclidean (g i)) ↔
      HasCompactSupport (toComplexTuple P g i) := fun i => by
    rw [HasCompactSupport, tsupport_toComplexTuple]
    exact SeparatedTuplesR4.isCompactWrt_euclid_iff (quotDist_euclidean P) _
  have hsmooth : ∀ i, PeriodicSpace.Kind.IsSmoothFn P .euclidean (g i) ↔
      ContDiff ℝ ∞ (toComplexTuple P g i) := fun i => by
    constructor
    · intro h
      exact Complex.ofRealCLM.contDiff.comp h
    · intro h
      exact Complex.reCLM.contDiff.comp h
  rw [mem_smoothRealTupleSet_iff_complex]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, -⟩
    have hs : ∀ i, PeriodicSpace.Kind.IsSmoothFn P .euclidean (g i) :=
      fun i => (hsmooth i).2 (h₁ i).1
    refine ⟨⟨fun i => ?_, fun i => (hc i).2 (h₁ i).2, fun i k hik => ?_⟩, hs⟩
    · have hinf : ContDiff ℝ ∞ (g i ∘ PeriodicSpace.Kind.quotMap P .euclidean) := hs i
      exact show ContDiff ℝ 1 (g i ∘ PeriodicSpace.Kind.quotMap P .euclidean) from
        hinf.of_le (by exact_mod_cast le_top)
    · have h := h₂ i k hik
      rwa [tsupport_toComplexTuple, tsupport_toComplexTuple] at h
  · rintro ⟨⟨-, h₂, h₃⟩, hs⟩
    refine ⟨⟨fun i => ⟨(hsmooth i).1 (hs i), (hc i).1 (h₂ i)⟩, fun i k hik => ?_⟩,
      fun i y => by simp [toComplexTuple]⟩
    rw [tsupport_toComplexTuple, tsupport_toComplexTuple]
    exact h₃ i k hik
theorem exists_toComplexTuple_eq (P : PeriodicSpace.Params) {f : FnTuple n}
    (hf : f ∈ smoothRealTupleSet n) :
    ∃ g : PeriodicSpace.Kind.FnTuple P .euclidean n, toComplexTuple P g = f := by
  refine ⟨fun i y => (f i y).re, funext fun i => funext fun y => ?_⟩
  have him : (f i y).im = 0 := ((mem_smoothRealTupleSet_iff_complex f).1 hf).2 i y
  exact Complex.ext (by simp [toComplexTuple]) (by simp [toComplexTuple, him])
theorem euclideanCompat_holds : EuclideanCompat n := by
  intro P
  constructor
  · ext f
    constructor
    · intro hf
      obtain ⟨g, rfl⟩ := exists_toComplexTuple_eq P hf
      exact ⟨g, (toComplexTuple_mem_iff P g).1 hf, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact (toComplexTuple_mem_iff P g).2 hg
  · intro Ψ T hΨ hT i h h' hag
    obtain ⟨g, hgr⟩ := exists_toComplexTuple_eq P h.2
    obtain ⟨g', hgr'⟩ := exists_toComplexTuple_eq P h'.2
    have hg : g ∈ PeriodicSpace.Kind.sepC1Tuples P .euclidean n :=
      ((toComplexTuple_mem_iff P g).1 (hgr ▸ h.2)).1
    have hg' : g' ∈ PeriodicSpace.Kind.sepC1Tuples P .euclidean n :=
      ((toComplexTuple_mem_iff P g').1 (hgr' ▸ h'.2)).1
    have hagree : ∀ l, l ≠ i → g l = g' l := fun l hl => funext fun y =>
      Complex.ofReal_injective (by
        have := congrFun (hag l hl) y
        rw [← hgr, ← hgr'] at this
        exact this)
    obtain ⟨hsum, hsc⟩ := hΨ i ⟨g, hg⟩ ⟨g', hg'⟩ hagree
    have hTg := hT h ⟨g, hg⟩ hgr
    have hTg' := hT h' ⟨g', hg'⟩ hgr'
    constructor
    · intro s hs
      have hread : toComplexTuple P (Function.update g i (g i + g' i)) = s.1 := by
        rw [hs]
        funext l y
        by_cases hl : l = i
        · subst hl
          rw [← hgr, ← hgr']
          simp only [toComplexTuple, Function.update_self, Pi.add_apply]
          exact Complex.ofReal_add _ _
        · rw [Function.update_of_ne hl, ← hgr]
          simp [toComplexTuple, Function.update_of_ne hl]
      have hmem := ((toComplexTuple_mem_iff P _).1 (hread ▸ s.2)).1
      rw [hT s ⟨_, hmem⟩ hread, hTg, hTg']
      exact hsum hmem
    · intro c s hs
      have hread : toComplexTuple P (Function.update g i (c • g i)) = s.1 := by
        rw [hs]
        funext l y
        by_cases hl : l = i
        · subst hl
          rw [← hgr]
          simp only [toComplexTuple, Function.update_self, Pi.smul_apply, smul_eq_mul]
          exact Complex.ofReal_mul _ _
        · rw [Function.update_of_ne hl, ← hgr]
          simp [toComplexTuple, Function.update_of_ne hl]
      have hmem := ((toComplexTuple_mem_iff P _).1 (hread ▸ s.2)).1
      rw [hT s ⟨_, hmem⟩ hread, hTg]
      exact hsc c hmem
theorem realMultilinearRestrict_holds : RealMultilinearRestrict n := by
  intro Φ hΦ i h h' hag
  constructor
  · intro s hs
    have := hΦ i 1 1 ⟨h.1, h.2.1⟩ ⟨h'.1, h'.2.1⟩ ⟨s.1, s.2.1⟩ hag (by simpa using hs)
    simpa using this
  · intro c s hs
    have := hΦ i c 0 ⟨h.1, h.2.1⟩ ⟨h.1, h.2.1⟩ ⟨s.1, s.2.1⟩ (fun _ _ => rfl) (by simpa using hs)
    simpa using this
theorem basicFacts_of_seminormComparison (hS : seminormComparison) : BasicFacts := fun n hn =>
  ⟨by ext f; exact mem_smoothRealTupleSet_iff_complex f, tensorSpaceFacts_holds hS hn,
    seminormMonotone_holds, closedUnderEntryOps_holds,
    multilinearZeroComponent_holds, minSupportSepPos_holds hn,
    euclideanCompat_holds, realMultilinearRestrict_holds⟩
end YangMills.Construction.ConfigSpace.TupleFacts
end
