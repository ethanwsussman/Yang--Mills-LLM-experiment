import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasures
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.FirstFactsOnArraysAndPerturbedSpecifications
import YangMills.Construction.InfiniteLattice.PerturbedSpecificationsAreUniformlyCloseAtSmallParameter
import YangMills.Construction.InfiniteLattice.PositivityAtAMirrorExtendsFromContinuousLocalObservables
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamily
import YangMills.Construction.InfiniteLattice.TorusMeasureSatisfiesThePerturbedEquationOfAWindow
import YangMills.Construction.InfiniteLattice.WeakLimitsOfTorusMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ComplexOrder
noncomputable section
namespace YangMills.Construction
open NormalFamilies
namespace InfiniteLattice
namespace WeakClusterPoint
theorem continuous_of_mem {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    Continuous F := by
  obtain ⟨-, -, hc⟩ := hF
  exact hc
theorem integrable_of_mem {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1)
    (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν] : Integrable F ν := by
  obtain ⟨⟨hm, C, hC⟩, -⟩ := hF
  exact Integrable.of_bound (C := C) hm.aestronglyMeasurable (ae_of_all _ hC)
theorem stateEval_eq_of_eventually_eq {μ : ℕ → Measure (GaugeField 1)} {ν : Measure (GaugeField 1)}
    (hν : IsWeakClusterPointUnitSpacing μ ν) {G G' : GaugeField 1 → ℂ}
    (hG : Continuous G) (hG' : Continuous G') (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → stateEval (μ n) G = stateEval (μ n) G') :
    stateEval ν G = stateEval ν G' := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨k, hk, hkF⟩ := hν {G, G'} (Set.toFinite _)
    (by rintro F (rfl | rfl) <;> assumption) (ε / 2) (half_pos hε) (max n₀ 1) (le_max_right _ _)
  have h1 := hkF G (by simp)
  have h2 := hkF G' (by simp)
  have h3 := h k ((le_max_left _ _).trans hk)
  rw [h3] at h1
  rw [dist_eq_norm]
  have h4 : stateEval ν G - stateEval ν G' =
      (stateEval (μ k) G' - stateEval ν G') - (stateEval (μ k) G' - stateEval ν G) := by
    ring
  rw [h4]
  exact (norm_sub_le _ _).trans (by linarith)
theorem stateEval_nonneg_of_eventually_nonneg {μ : ℕ → Measure (GaugeField 1)}
    {ν : Measure (GaugeField 1)}
    (hν : IsWeakClusterPointUnitSpacing μ ν) {G : GaugeField 1 → ℂ}
    (hG : Continuous G) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → 0 ≤ stateEval (μ n) G) :
    0 ≤ stateEval ν G := by
  have hc : IsClosed (Set.Ici (0 : ℂ)) := isClosed_Ici
  have hm : stateEval ν G ∈ closure (Set.Ici (0 : ℂ)) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨k, hk, hkF⟩ := hν {G} (Set.finite_singleton _) (by rintro F rfl; exact hG) (ε / 2)
      (half_pos hε) (max n₀ 1) (le_max_right _ _)
    refine ⟨stateEval (μ k) G, h k ((le_max_left _ _).trans hk), ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (hkF G rfl).trans_lt (half_lt_self hε)
  rw [hc.closure_eq] at hm
  exact hm
theorem minSupPeriod_le (Λ : PeriodSublattice 1) {γ : LatticePoint 1} (hγ : γ ∈ Λ.periods)
    (h0 : γ ≠ 0) :
    Λ.minSupPeriod ≤ WholeSpace.maxNorm (γ : AmbientSpace) := by
  refine csInf_le ⟨0, ?_⟩ ⟨γ, hγ, h0, rfl⟩
  rintro s ⟨g, -, -, rfl⟩
  exact (abs_nonneg _).trans
    (Finset.le_sup' (fun a => |(g : AmbientSpace) a|) (Finset.mem_univ (0 : Fin 4)))
def trivialArray (h : (fun _ => (0 : ℂ)) ∈ continuousLocalFunctions 1) : LocalObservableArray where
  sublattice := ⊤
  sublattice_finiteIndex := inferInstance
  size := 1
  one_le_size := le_rfl
  gen := fun _ _ => 0
  gen_mem := fun _ => h
  gen_im := fun _ _ => rfl
theorem mem_tiltedGibbsClass
    (hTorus : TiltedTorusMeasureWindowEquation.Statement)
    (hFirst : BasicTiltedKernelFacts)
    {β : ℝ} (hβ : 0 < β) (A : LocalObservableArray) (t : ℝ) {Λ : ℕ → PeriodSublattice 1}
    (hD : ∀ n, 1 ≤ n → A.FitsPeriods (Λ n)) (hΛ : PeriodsDiverge Λ)
    {ν : Measure (GaugeField 1)} [hp : IsProbabilityMeasure ν]
    (hν : IsWeakClusterPointUnitSpacing (fun n => A.tiltedLiftMeasure (Λ n) β t) ν) :
    ν ∈ A.tiltedGibbsClass β t := by
  refine ⟨hp, fun W F hF => ?_⟩
  obtain ⟨w, hw⟩ := hTorus β hβ A t W F hF
  obtain ⟨n₁, hn₁⟩ := tendsto_atTop_atTop.1 hΛ (w + 1)
  have hK := (hFirst β hβ A W t).2.2.2 F hF
  refine stateEval_eq_of_eventually_eq hν (continuous_of_mem hK) (continuous_of_mem hF)
    (max n₁ 1) fun n hn => ?_
  refine (hw (Λ n) (hD n ((le_max_right _ _).trans hn)) fun γ hγ h0 => ?_).symm
  have h1 := hn₁ n ((le_max_left _ _).trans hn)
  have h2 := minSupPeriod_le (Λ n) hγ h0
  linarith
theorem isSymmetricUnder_of_descended
    (hDense : ContinuousLocalDensity.Statement)
    (hInduced : LatticeSymmetriesDescendToQuotient)
    (hFinite : FiniteTorusPartitionsAndLifts)
    (hFacts : ToriArraysAndTiltedMeasuresFacts)
    {β : ℝ} (hβ : 0 < β) (A : LocalObservableArray) (t : ℝ) {Λ : ℕ → PeriodSublattice 1}
    (hD : ∀ n, 1 ≤ n → A.FitsPeriods (Λ n)) (r : LatticeSymmetry 1)
    (hr : ∀ n, 1 ≤ n → (Λ n).OrthogonalPartPreserves r)
    (hinv : ∀ n, 1 ≤ n → PeriodSublattice.IsHomeomorphInvariant (A.tiltedMeasure (Λ n) β t)
      ((Λ n).descendedPullback r))
    {ν : Measure (GaugeField 1)} [IsProbabilityMeasure ν]
    (hν : IsWeakClusterPointUnitSpacing (fun n => A.tiltedLiftMeasure (Λ n) β t) ν) :
    IsSymmetricUnder ν r := by
  have hd := (hDense ν).2.2.1 r
  refine hd.2.2 fun F hF => ?_
  have hrF := hd.2.1 F hF
  refine stateEval_eq_of_eventually_eq hν (continuous_of_mem hrF) (continuous_of_mem hF) 1
    fun n hn => ?_
  have hE := ((hFinite β hβ (Λ n)).2 A (hD n hn) t).2.integral_tiltedLift
  have hb := ((hInduced β hβ (Λ n)).1 r (hr n hn)).2.2.2.2.2 F hF
  have hc := ((hFacts β hβ).1 1 one_pos (Λ n)).2.1.continuous_periodize F hF
  calc stateEval (A.tiltedLiftMeasure (Λ n) β t) (r.actOn F)
      = PeriodSublattice.integralOf (A.tiltedMeasure (Λ n) β t)
          ((Λ n).periodize (r.actOn F)) := hE _ hrF
    _ = PeriodSublattice.integralOf (A.tiltedMeasure (Λ n) β t)
          ((Λ n).periodize F ∘ (Λ n).descendedPullback r) := by rw [hb]
    _ = PeriodSublattice.integralOf (A.tiltedMeasure (Λ n) β t) ((Λ n).periodize F) :=
        hinv n hn ⟨(Λ n).periodize F, hc⟩
    _ = stateEval (A.tiltedLiftMeasure (Λ n) β t) F := (hE F hF).symm
theorem isSymmetricUnder_shift
    (hDense : ContinuousLocalDensity.Statement)
    (hInduced : LatticeSymmetriesDescendToQuotient)
    (hFinite : FiniteTorusPartitionsAndLifts)
    (hFacts : ToriArraysAndTiltedMeasuresFacts)
    {β : ℝ} (hβ : 0 < β) (A : LocalObservableArray) (t : ℝ) {Λ : ℕ → PeriodSublattice 1}
    (hD : ∀ n, 1 ≤ n → A.FitsPeriods (Λ n)) {v : LatticePoint 1} (hv : v ∈ A.sublattice)
    {ν : Measure (GaugeField 1)} [IsProbabilityMeasure ν]
    (hν : IsWeakClusterPointUnitSpacing (fun n => A.tiltedLiftMeasure (Λ n) β t) ν) :
    IsSymmetricUnder ν (shift v) := by
  refine isSymmetricUnder_of_descended hDense hInduced hFinite hFacts hβ A t hD (shift v)
    (fun n hn => ?_) (fun n hn => ((hInduced β hβ (Λ n)).2 A (hD n hn) t v hv).2) hν
  have h1 := ((hInduced β hβ (Λ n)).2 A (hD n hn) t v hv).1
  have h2 : Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) = id := funext Matrix.one_mulVec
  unfold PeriodSublattice.OrthogonalPartPreserves
  rw [h1, h2, Set.image_id]
theorem mem_gibbsClass_of_tendsto
    (hClose : TiltedKernelsUniformlyCloseNearZero)
    (hFirst : BasicTiltedKernelFacts)
    (hFacts : ToriArraysAndTiltedMeasuresFacts)
    {β : ℝ} (hβ : 0 < β) (A : LocalObservableArray) (t : ℕ → ℝ) (ν : ℕ → Measure (GaugeField 1))
    (ν₀ : Measure (GaugeField 1)) (hp : IsProbabilityMeasure ν₀)
    (ht : Tendsto t atTop (𝓝 0)) (hνk : ∀ k, 1 ≤ k → ν k ∈ A.tiltedGibbsClass β (t k))
    (hconv : WeakConvergesUnitSpacing ν ν₀) :
    ν₀ ∈ gibbsClass one_pos β := by
  rw [← ((hFacts β hβ).2.1 A 0).2.1.tiltedGibbsClass_zero]
  refine ⟨hp, fun W F hF => ?_⟩
  obtain ⟨C, -, hb⟩ := hClose β hβ A W F hF
  have hK := (hFirst β hβ A W 0).2.2.2 F hF
  have h1 := hconv F (continuous_of_mem hF)
  have h2 := hconv _ (continuous_of_mem hK)
  have hlim := (h1.sub h2).norm
  have hr : Tendsto (fun k => observableSupNorm F * (Real.exp (C * |t k|) - 1)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun k => observableSupNorm F * (Real.exp (C * |t k|) - 1)) atTop
        (𝓝 (observableSupNorm F * (Real.exp (C * |(0 : ℝ)|) - 1))) :=
      (((ht.abs.const_mul C).rexp).sub_const 1).const_mul _
    simpa using h3
  have hle := le_of_tendsto_of_tendsto hlim hr (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
  · exact (sub_eq_zero.1 (norm_le_zero_iff.1 hle)).symm
  · obtain ⟨hpk, heq⟩ := hνk k hk
    have hKk := (hFirst β hβ A W (t k)).2.2.2 F hF
    have h4 : stateEval (ν k) F - stateEval (ν k) (A.tiltedKernel β 0 W F) =
        ∫ U, (A.tiltedKernel β (t k) W F U - A.tiltedKernel β 0 W F U) ∂ν k := by
      rw [integral_sub (integrable_of_mem hKk _) (integrable_of_mem hK _), heq W F hF]
      rfl
    beta_reduce
    rw [h4]
    have h5 := norm_integral_le_of_norm_le_const (μ := ν k) (ae_of_all _ fun U => hb (t k) U)
    simpa [observableSupNorm] using h5
end WeakClusterPoint
open WeakClusterPoint in
theorem torusMeasureWeakLimits_holds
    (hTorus : TiltedTorusMeasureWindowEquation.Statement)
    (hClose : TiltedKernelsUniformlyCloseNearZero)
    (hPositive : ReflectionPositivityExtendsFromLocal)
    (hDense : ContinuousLocalDensity.Statement)
    (hInduced : LatticeSymmetriesDescendToQuotient)
    (hFinite : FiniteTorusPartitionsAndLifts)
    (hFirst : BasicTiltedKernelFacts)
    (hFacts : ToriArraysAndTiltedMeasuresFacts)
    (hElementary : ElementaryLatticeFacts)
    (hReflections : ReflectionIdentities.Statement) :
    TorusMeasureWeakLimits := by
  intro β hβ
  have hLocal : LocalFunctionProperties 1 := (hElementary 1 β one_pos hβ).2.2.2.1
  refine ⟨?_, fun A t ν ν₀ hp ht hνk hconv =>
    mem_gibbsClass_of_tendsto hClose hFirst hFacts hβ A t ν ν₀ hp ht hνk hconv,
    hPositive, ?_⟩
  · intro Λ hΛ ν hp hν
    have := hp
    let B : LocalObservableArray := trivialArray (hLocal.2.2.1 0)
    have hD : ∀ n, B.FitsPeriods (Λ n) := fun _ => le_top
    have hseq : (fun n => (Λ n).liftedGibbsMeasure β) =
        fun n => B.tiltedLiftMeasure (Λ n) β 0 := by
      funext n
      have h := (((hFacts β hβ).2.1 B 0).2.2 (Λ n) (hD n)).tiltedMeasure_zero
      unfold LocalObservableArray.tiltedLiftMeasure PeriodSublattice.liftedGibbsMeasure
      rw [h]
    rw [hseq] at hν
    have h0 := mem_tiltedGibbsClass hTorus hFirst hβ B 0 (fun n _ => hD n) hΛ hν
    rw [((hFacts β hβ).2.1 B 0).2.1.tiltedGibbsClass_zero] at h0
    exact ⟨h0, fun v _ => isSymmetricUnder_shift hDense hInduced hFinite hFacts hβ B 0
      (fun n _ => hD n) (AddSubgroup.mem_top v) hν⟩
  · intro A t Λ hD hΛ
    refine ⟨fun ν hp hν => ?_, fun r hr => ⟨fun n hn => ?_, fun hinv ν hp hν => ?_⟩,
      fun P hP ν hp hν F hF => ?_⟩
    · have := hp
      exact ⟨mem_tiltedGibbsClass hTorus hFirst hβ A t hD hΛ hν, fun v hv =>
        isSymmetricUnder_shift hDense hInduced hFinite hFacts hβ A t hD hv hν⟩
    · have h := (hInduced β hβ (Λ n)).1 r (hr n hn)
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.2.1⟩
    · have := hp
      exact isSymmetricUnder_of_descended hDense hInduced hFinite hFacts hβ A t hD r hr hinv hν
    · obtain ⟨n₀, hn₀⟩ := hP F hF
      have R := hReflections P.normal P.normal_mem P.level P.level P.allowed P.allowed 0
      have hside : P.conjReflectObservable '' halfSpaceContinuousLocal 1 P.normal P.level 1 =
          halfSpaceContinuousLocal 1 P.normal P.level (-1) :=
        R.2.2.2.2.2.2.2.2.2.2.2.2.1 1
      have hΘ : P.conjReflectObservable F ∈ continuousLocalFunctions 1 :=
        (hside.subset ⟨F, hF, rfl⟩).2
      have hprod : P.conjReflectObservable F * F ∈ continuousLocalFunctions 1 :=
        (hLocal.1 _ hΘ F hF.2).2
      refine stateEval_nonneg_of_eventually_nonneg hν (continuous_of_mem hprod) (max n₀ 1)
        fun n hn => ?_
      have h1 : 1 ≤ n := (le_max_right _ _).trans hn
      have hE := ((hFinite β hβ (Λ n)).2 A (hD n h1) t).2.integral_tiltedLift _ hprod
      show 0 ≤ ∫ U, (P.conjReflectObservable F * F) U ∂(A.tiltedLiftMeasure (Λ n) β t)
      rw [hE]
      exact hn₀ n h1 ((le_max_left _ _).trans hn)
end InfiniteLattice
end YangMills.Construction
