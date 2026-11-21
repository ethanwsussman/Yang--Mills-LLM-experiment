import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import YangMills.Construction.TorusOrFourSpace.PartialsOfSumsAndProducts
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnSupportsNormsAndTestFunctions
import YangMills.Construction.TorusOrFourSpace.SumsProductsAndTestFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
namespace YangMills.Construction.PeriodicSpace.SupportNormFacts
open Kind Kind.Tuple MetricNotions
theorem isCompactWrt_iUnion {X ι : Type*} [Finite ι] (d : X → X → ℝ) {K : ι → Set X}
    (h : ∀ a, IsCompactWrt d (K a)) : IsCompactWrt d (⋃ a, K a) := by
  intro U hU hc
  choose V hV hfin hcov using fun a => h a U hU fun x hx => hc (Set.mem_iUnion.2 ⟨a, hx⟩)
  refine ⟨⋃ a, V a, Set.iUnion_subset hV, Set.finite_iUnion hfin, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
  exact Set.sUnion_subset_sUnion (Set.subset_iUnion V a) (hcov a ha)
theorem iterPartial_zero {p : ℕ+} (G : Coords p → ℂ) :
    Coords.iterPartial (0 : CoordIndex p) G = G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_zero <;> assumption
theorem supportT_subset_of_eq_zero_off {D : Params} {E : Kind} {p : ℕ+} (F : E.Tuple D p → ℂ)
    {C : Set (E.Tuple D p)} (hC : IsClosedT D E C) (h : ∀ y, y ∉ C → F y = 0) :
    supportT D E F ⊆ C := by
  intro x hx
  by_contra hxC
  obtain ⟨r, hr, hball⟩ := hC x hxC
  obtain ⟨y, hy, hd⟩ := hx r hr
  exact hy (h y (hball y hd))
theorem claim_holds
    (sums : AlgebraOfTestFns.Claim)
    (derivatives : TupleDerivatives.Statement)
    (lifts : TupleMetric.QuotientDistanceAndLifts)
    (partials : SumsProductsPartials.LeibnizRules) : Claim := by
  intro D n
  obtain ⟨⟨surj, -⟩, -, ⟨-, dist0, -, -⟩, -, -⟩ := lifts D Kind.euclidean n
  obtain ⟨der, fin⟩ := derivatives D Kind.euclidean n
  obtain ⟨hsupp, hclass, htest, hempty⟩ := sums D Kind.euclidean n
  have hmemsupp : ∀ (F : Kind.euclidean.Tuple D n → ℂ) (y), F y ≠ 0 →
      y ∈ supportT D Kind.euclidean F :=
    fun F y hy r hr => ⟨y, hy, by rw [(dist0 y y).2 rfl]; exact hr⟩
  have hadd : ∀ F H : Kind.euclidean.Tuple D n → ℂ, IsSmoothT D Kind.euclidean F →
      IsSmoothT D Kind.euclidean H → IsSmoothT D Kind.euclidean (F + H) :=
    fun F H hF hH ν => by simpa using (hclass ν F H (hF ν) (hH ν)).1 1 1
  have hzeroSmooth : IsSmoothT D Kind.euclidean (0 : Kind.euclidean.Tuple D n → ℂ) := by
    have h : (0 : Kind.euclidean.Tuple D n → ℂ) ∈
        testFns D Kind.euclidean (∅ : Set (Kind.euclidean.Tuple D n)) := by
      rw [hempty]
      rfl
    exact h.1
  have hderadd : ∀ F H : Kind.euclidean.Tuple D n → ℂ, IsSmoothT D Kind.euclidean F →
      IsSmoothT D Kind.euclidean H → ∀ (α : CoordIndex n) (y),
      _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α (F + H) y =
        _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α F y + _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α H y := by
    intro F H hF hH α y
    obtain ⟨x, rfl⟩ := surj y
    have d1 := congrFun (der α.degree (F + H) (hadd F H hF hH _) α le_rfl).2.1 x
    have d2 := congrFun (der α.degree F (hF _) α le_rfl).2.1 x
    have d3 := congrFun (der α.degree H (hH _) α le_rfl).2.1 x
    have lin := (partials n (F ∘ proj D Kind.euclidean)
      (H ∘ proj D Kind.euclidean) hF hH).2.2.2.2.1 1 1 α
    have hcomp : (F + H) ∘ proj D Kind.euclidean =
        (1 : ℂ) • (F ∘ proj D Kind.euclidean) +
          (1 : ℂ) • (H ∘ proj D Kind.euclidean) := by
      funext z
      simp
    rw [Function.comp_apply] at d1 d2 d3
    rw [d1, d2, d3, hcomp, lin]
    simp
  have hle : ∀ (ν : ℕ) (G : Kind.euclidean.Tuple D n → ℂ)
      (α : CoordIndex n), α.degree ≤ ν → ∀ y,
      ENNReal.ofReal ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α G y‖ ≤ cNorm D Kind.euclidean ν G :=
    fun ν G α hα y => le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le y le_rfl))
  have hnormadd : ∀ (ν : ℕ) (F H : Kind.euclidean.Tuple D n → ℂ),
      IsSmoothT D Kind.euclidean F → IsSmoothT D Kind.euclidean H →
      cNorm D Kind.euclidean ν (F + H) ≤
        cNorm D Kind.euclidean ν F + cNorm D Kind.euclidean ν H := by
    intro ν F H hF hH
    refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
    rw [hderadd F H hF hH α y]
    calc ENNReal.ofReal ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α F y + _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α H y‖
        ≤ ENNReal.ofReal (‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α F y‖ +
            ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α H y‖) :=
          ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ENNReal.ofReal ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α F y‖ +
            ENNReal.ofReal ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α H y‖ :=
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ _ := add_le_add (hle ν F α hα y) (hle ν H α hα y)
  have hnormzero : ∀ ν : ℕ,
      cNorm D Kind.euclidean ν (0 : Kind.euclidean.Tuple D n → ℂ) = 0 := by
    intro ν
    refine le_antisymm (iSup_le fun α => iSup_le fun _ => iSup_le fun y => ?_) zero_le
    have h := hderadd 0 0 hzeroSmooth hzeroSmooth α y
    rw [add_zero] at h
    have h0 : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean α (0 : Kind.euclidean.Tuple D n → ℂ) y = 0 := by
      simpa using h
    simp [h0]
  have hsumnorm : ∀ {ι : Type} (s : Finset ι) (h : ι → Kind.euclidean.Tuple D n → ℂ),
      (∀ a, IsSmoothT D Kind.euclidean (h a)) →
      IsSmoothT D Kind.euclidean (∑ a ∈ s, h a) ∧ ∀ ν : ℕ,
        cNorm D Kind.euclidean ν (∑ a ∈ s, h a) ≤
          ∑ a ∈ s, cNorm D Kind.euclidean ν (h a) := by
    classical
    intro ι s h hh
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using hzeroSmooth, fun ν => ?_⟩
      simp [hnormzero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine ⟨hadd _ _ (hh a) ih.1, fun ν => ?_⟩
      rw [Finset.sum_insert ha]
      exact (hnormadd ν _ _ (hh a) ih.1).trans (add_le_add le_rfl (ih.2 ν))
  have hsuppzero : supportT D Kind.euclidean (0 : Kind.euclidean.Tuple D n → ℂ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨z, hz, -⟩ := hy 1 one_pos
    exact hz rfl
  have hsuppadd : ∀ F H : Kind.euclidean.Tuple D n → ℂ,
      supportT D Kind.euclidean (F + H) ⊆
        supportT D Kind.euclidean F ∪ supportT D Kind.euclidean H :=
    fun F H => by simpa using (hsupp F H 1 1).1
  have hsuppsum : ∀ {ι : Type} (s : Finset ι) (h : ι → Kind.euclidean.Tuple D n → ℂ)
      (K : Set (Kind.euclidean.Tuple D n)), (∀ a, supportT D Kind.euclidean (h a) ⊆ K) →
      supportT D Kind.euclidean (∑ a ∈ s, h a) ⊆ K := by
    classical
    intro ι s h K hK
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, hsuppzero]
      exact Set.empty_subset _
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hsuppadd _ _).trans (Set.union_subset (hK a) ih)
  have horderzero : ∀ (G : Kind.euclidean.Tuple D n → ℂ),
      IsSmoothT D Kind.euclidean G → ∀ y,
      ENNReal.ofReal ‖G y‖ ≤ cNorm D Kind.euclidean 0 G := by
    intro G hG y
    have h0 : (0 : CoordIndex n).degree ≤ 0 := by simp [CoordIndex.degree]
    have hd : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.partialDeriv D Kind.euclidean (0 : CoordIndex n) G y = G y := by
      obtain ⟨x, rfl⟩ := surj y
      have d1 := congrFun (der 0 G (hG 0) 0 h0).2.1 x
      rw [iterPartial_zero] at d1
      exact d1
    have h := hle 0 G 0 h0 y
    rwa [hd] at h
  refine ⟨fun F H c => ⟨fun C hC h => supportT_subset_of_eq_zero_off F hC h, hsuppadd F H,
      by simpa using (hsupp F F c 0).1, (hsupp F H 0 0).2⟩,
    fun F hF hK ν => fin ν F (hF ν) hK, fun F H ν hF hH _ _ => hnormadd ν F H hF hH,
    fun Ω hΩ => ?_⟩
  obtain ⟨⟨S, hS⟩, hΩ'⟩ := htest Ω hΩ
  have hmem : ∀ G, G ∈ S ↔ G ∈ testFns D Kind.euclidean Ω := fun G => by
    rw [← hS]
    rfl
  refine ⟨⟨S, hS⟩, fun F ψ hF hψ => ?_, fun Fs F hconv C hC hsub => ?_, fun A Fs F hconv => ?_⟩
  · have h := (hΩ' ψ hψ).2.2.2.1 F hF
    rwa [mul_comm] at h
  · refine supportT_subset_of_eq_zero_off _ hC fun y hy => ?_
    have hzero : ∀ t, (Fs t).1 y = 0 :=
      fun t => by_contra fun h => hy (hsub t (hmemsupp _ y h))
    have hsm : ∀ t, IsSmoothT D Kind.euclidean ((Fs t).1 - F.1) :=
      fun t => ((hmem _).1 (S.sub_mem ((hmem _).2 (Fs t).2) ((hmem _).2 F.2))).1
    have hbound : ∀ t, ENNReal.ofReal ‖F.1 y‖ ≤
        cNorm D Kind.euclidean 0 ((Fs t).1 - F.1) := by
      intro t
      have h := horderzero _ (hsm t) y
      simpa [hzero t] using h
    have hlim := ge_of_tendsto' (hconv.2 0) hbound
    simpa using hlim
  · choose K hKc hKΩ hKF hKt using fun a => (hconv a).1
    have hsumt : ∀ t, ∑ a, (Fs a t).1 ∈ testFns D Kind.euclidean Ω :=
      fun t => (hmem _).1 (S.sum_mem fun a _ => (hmem _).2 (Fs a t).2)
    have hsumF : ∑ a, (F a).1 ∈ testFns D Kind.euclidean Ω :=
      (hmem _).1 (S.sum_mem fun a _ => (hmem _).2 (F a).2)
    refine ⟨hsumt, hsumF, ⟨⋃ a, K a, isCompactWrt_iUnion _ hKc, Set.iUnion_subset hKΩ,
      hsuppsum Finset.univ _ _ fun a => (hKF a).trans (Set.subset_iUnion K a),
      fun t => hsuppsum Finset.univ _ _ fun a => (hKt a t).trans (Set.subset_iUnion K a)⟩, fun ν => ?_⟩
    have hsm : ∀ t a, IsSmoothT D Kind.euclidean ((Fs a t).1 - (F a).1) :=
      fun t a => ((hmem _).1 (S.sub_mem ((hmem _).2 (Fs a t).2) ((hmem _).2 (F a).2))).1
    have hbound : ∀ t, cNorm D Kind.euclidean ν (∑ a, (Fs a t).1 - ∑ a, (F a).1) ≤
        ∑ a, cNorm D Kind.euclidean ν ((Fs a t).1 - (F a).1) := by
      intro t
      rw [← Finset.sum_sub_distrib]
      exact (hsumnorm Finset.univ _ (hsm t)).2 ν
    have hlim : Tendsto
        (fun t => ∑ a, cNorm D Kind.euclidean ν ((Fs a t).1 - (F a).1)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun a _ => (hconv a).2 ν
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hbound
end YangMills.Construction.PeriodicSpace.SupportNormFacts
