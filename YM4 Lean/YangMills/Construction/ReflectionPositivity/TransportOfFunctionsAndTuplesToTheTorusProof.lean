import YangMills.Construction.ReflectionPositivity.MirrorsAndSides
import YangMills.Construction.ReflectionPositivity.ReflectionOfAMirrorOfOneTorusProof
import YangMills.Construction.ReflectionPositivity.TransportOfFunctionsAndTuplesToTheTorus
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.MetricNotions YangMills.Construction.FamilyTopology YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LimitSpaces.Periodization
section Metrics
variable {X Y : Type*} {d : X → X → ℝ} {d' : Y → Y → ℝ}
theorem isCompactWrt_image {g : X → Y} (hg : IsContinuousWrt d d' g) {K : Set X}
    (hK : IsCompactWrt d K) : IsCompactWrt d' (g '' K) := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.isCompactWrt_image <;> assumption
theorem closureWrt_subset_of_isCompactWrt (hd : IsMetricFunction d) {A C : Set X}
    (hC : IsCompactWrt d C) (hAC : A ⊆ C) : closureWrt d A ⊆ C := by
  intro u hu
  by_contra huC
  let U : ℕ → Set X := fun n => {v | 1 / ((n : ℝ) + 1) < d u v}
  obtain ⟨𝒱, h𝒱, hfin, hc⟩ := hC (range U)
    (by
      rintro _ ⟨n, rfl⟩ v hv
      refine ⟨d u v - 1 / ((n : ℝ) + 1), sub_pos.mpr hv, fun w hw => ?_⟩
      have h1 := hd.triangle u w v
      have h2 := hd.symm w v
      show 1 / ((n : ℝ) + 1) < d u w
      linarith)
    (by
      intro v hv
      have hne : u ≠ v := fun h => huC (h ▸ hv)
      have hpos : 0 < d u v :=
        lt_of_le_of_ne (hd.nonneg u v) fun h => hne ((hd.eq_zero_iff u v).mp h.symm)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨U n, ⟨n, rfl⟩, hn⟩)
  obtain ⟨t, -, htfin, htc⟩ := (exists_subset_image_finite_and (f := U) (s := univ)
    (p := fun 𝒱 => C ⊆ ⋃₀ 𝒱)).mp ⟨𝒱, by rwa [image_univ], hfin, hc⟩
  obtain ⟨N, hN⟩ := htfin.bddAbove
  obtain ⟨y, hy, hdy⟩ := hu (1 / ((N : ℝ) + 1)) (by positivity)
  obtain ⟨_, ⟨n, hn, rfl⟩, hyn⟩ := htc (hAC hy)
  have hle : 1 / ((N : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (n : ℝ) ≤ N := by exact_mod_cast hN hn
    linarith
  have : 1 / ((n : ℝ) + 1) < d u y := hyn
  linarith
end Metrics
theorem side_le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (TestFunctions.latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
theorem latticeTranslate_zero (ℓ : ℝ) : TestFunctions.latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem side_pos (s : Conventions.StandingParameters) : 0 < s.side := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusMirrors.AxisReflection.side_pos <;> assumption
variable {s : Conventions.StandingParameters}
theorem euclidNormVec_le_sub_add (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (a γ : Fin 4 → ℝ) : euclidNormVec γ ≤ euclidNormVec (a - γ) + euclidNormVec a := by
  have h1 : euclidNormVec (γ - 0) ≤ euclidNormVec (γ - a) + euclidNormVec (a - 0) :=
    hd.triangle γ a 0
  have h2 : euclidNormVec (γ - a) = euclidNormVec (a - γ) := hd.symm γ a
  simpa [h2] using h1
theorem pointDist_proj (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) {x y : Fin 4 → ℝ}
    (h : euclidNormVec (x - y) ≤ s.side / 2) :
    Ambient.periodic.pointDist s (Ambient.periodic.proj s x) (Ambient.periodic.proj s y) =
      euclidNormVec (x - y) := by
  obtain ⟨⟨γ, hγ, hγe⟩, -⟩ := (hT.1 x y).1
  refine le_antisymm (hT.1 x y).2 ?_
  rw [← hγe]
  by_cases h0 : γ = 0
  · subst h0
    simp
  · obtain ⟨n, hn⟩ := hγ
    have hγk : γ = TestFunctions.latticeTranslate s.side n := by
      funext μ
      simp [hn μ, TestFunctions.latticeTranslate, mul_comm]
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact h0 (by rw [hγk, latticeTranslate_zero])
    have h1 := side_le_euclidNormVec_latticeTranslate (side_pos s) hn0
    rw [← hγk] at h1
    have h2 := euclidNormVec_le_sub_add hd (x - y) γ
    show euclidNormVec (x - y) ≤ euclidNormVec (x - y - γ)
    linarith
def HasCloseSupport (s : Conventions.StandingParameters) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ x y, f x ≠ 0 → f y ≠ 0 → euclidNormVec (x - y) ≤ s.side / 2
theorem mem_closedSupport_of_ne (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (hx : f x ≠ 0) :
    x ∈ Ambient.euclidean.closedSupport s f := fun r hr =>
  ⟨x, hx, by rw [(hd.eq_zero_iff x x).mpr rfl]; exact hr⟩
theorem hasCloseSupport_of_supportedWithin (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    {S : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ} (hS : TestFunctions.HasDiameterLE S (s.side / 2))
    (hf : Ambient.euclidean.SupportedWithin s S f) : HasCloseSupport s f := fun x y hx hy =>
  hS x (hf.2 (mem_closedSupport_of_ne hd hx)) y (hf.2 (mem_closedSupport_of_ne hd hy))
section SingleFunction
variable {f : (Fin 4 → ℝ) → ℝ}
theorem latticeIndex_unique (hN : HasCloseSupport s f) (y : Fin 4 → ℝ) {k k' : Fin 4 → ℤ}
    (h : f (y + TestFunctions.latticeTranslate s.side k) ≠ 0)
    (h' : f (y + TestFunctions.latticeTranslate s.side k') ≠ 0) : k = k' := by
  by_contra hne
  have h1 := side_le_euclidNormVec_latticeTranslate (side_pos s) (sub_ne_zero.mpr hne)
  have h2 := hN _ _ h h'
  have e : y + TestFunctions.latticeTranslate s.side k -
      (y + TestFunctions.latticeTranslate s.side k') =
      TestFunctions.latticeTranslate s.side (k - k') := by
    funext μ
    simp [TestFunctions.latticeTranslate, mul_sub]
  rw [e] at h2
  linarith [side_pos s]
theorem periodizeFun_proj_of_ne (hN : HasCloseSupport s f) (y : Fin 4 → ℝ) {k : Fin 4 → ℤ}
    (h : f (y + TestFunctions.latticeTranslate s.side k) ≠ 0) :
    periodizeFun s f (Ambient.periodic.proj s y) =
      f (y + TestFunctions.latticeTranslate s.side k) := by
  show TestFunctions.periodize s.side f (torusProj s.side y) = _
  rw [TestFunctions.periodize_torusProj]
  exact tsum_eq_single k fun k' hk' => by_contra fun hne => hk' (latticeIndex_unique hN y hne h)
theorem periodizeFun_proj_self (hN : HasCloseSupport s f) {y : Fin 4 → ℝ} (h : f y ≠ 0) :
    periodizeFun s f (Ambient.periodic.proj s y) = f y := by
  have h0 : f (y + TestFunctions.latticeTranslate s.side 0) ≠ 0 := by
    simpa [latticeTranslate_zero] using h
  simpa [latticeTranslate_zero] using periodizeFun_proj_of_ne hN y h0
theorem proj_add_latticeTranslate (y : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    Ambient.periodic.proj s (y + TestFunctions.latticeTranslate s.side k) =
      Ambient.periodic.proj s y :=
  TestFunctions.torusProj_add_latticeTranslate s.side y k
theorem exists_of_periodizeFun_ne (hN : HasCloseSupport s f) {u : s.Torus}
    (h : periodizeFun s f u ≠ 0) :
    ∃ x, Ambient.periodic.proj s x = u ∧ f x ≠ 0 ∧ periodizeFun s f u = f x := by
  obtain ⟨y, rfl⟩ := Ambient.periodic.proj_surjective s u
  by_contra hcon
  apply h
  have hz : ∀ k, f (y + TestFunctions.latticeTranslate s.side k) = 0 := by
    intro k
    by_contra hk
    exact hcon ⟨y + TestFunctions.latticeTranslate s.side k, proj_add_latticeTranslate y k, hk,
      periodizeFun_proj_of_ne hN y hk⟩
  show TestFunctions.periodize s.side f (torusProj s.side y) = 0
  rw [TestFunctions.periodize_torusProj]
  simp [TestFunctions.periodicSum, hz]
end SingleFunction
section Periodized
variable {f h : (Fin 4 → ℝ) → ℝ}
theorem summable_translates (hN : HasCloseSupport s f) (y : Fin 4 → ℝ) :
    Summable fun k => f (y + TestFunctions.latticeTranslate s.side k) :=
  summable_of_hasFiniteSupport
    (Set.Subsingleton.finite fun _ hk _ hk' => latticeIndex_unique hN y hk hk')
theorem periodizeFun_linear (hNf : HasCloseSupport s f) (hNh : HasCloseSupport s h) (u u' : ℝ) :
    periodizeFun s (u • f + u' • h) =
      u • periodizeFun s f + u' • periodizeFun s h := by
  funext w
  obtain ⟨y, rfl⟩ := Ambient.periodic.proj_surjective s w
  have key : ∀ g : (Fin 4 → ℝ) → ℝ, periodizeFun s g (Ambient.periodic.proj s y) =
      ∑' k, g (y + TestFunctions.latticeTranslate s.side k) :=
    fun g => TestFunctions.periodize_torusProj s.side g y
  have e : (u • periodizeFun s f + u' • periodizeFun s h) (Ambient.periodic.proj s y) =
      u * periodizeFun s f (Ambient.periodic.proj s y) +
        u' * periodizeFun s h (Ambient.periodic.proj s y) := rfl
  rw [e, key f, key h, key (u • f + u' • h)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [((summable_translates hNf y).mul_left u).tsum_add ((summable_translates hNh y).mul_left u'),
    tsum_mul_left, tsum_mul_left]
theorem closedSupport_periodizeFun (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) (hN : HasCloseSupport s f)
    (hK : Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s f)) :
    Ambient.periodic.closedSupport s (periodizeFun s f) =
      Ambient.periodic.proj s '' Ambient.euclidean.closedSupport s f := by
  have hc : IsCompactWrt (Ambient.periodic.pointDist s)
      (Ambient.periodic.proj s '' Ambient.euclidean.closedSupport s f) :=
    isCompactWrt_image (d := TestFunctions.euclidDistR4) hT.2.2.2.2 hK
  apply subset_antisymm
  · refine closureWrt_subset_of_isCompactWrt hT.2.1 hc ?_
    intro u hu
    obtain ⟨x, rfl, hx, -⟩ := exists_of_periodizeFun_ne hN hu
    exact ⟨x, mem_closedSupport_of_ne hd hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ r hr
    obtain ⟨y, hy, hxy⟩ := hx r hr
    refine ⟨Ambient.periodic.proj s y, ?_, lt_of_le_of_lt (hT.1 x y).2 hxy⟩
    show periodizeFun s f (Ambient.periodic.proj s y) ≠ 0
    rw [periodizeFun_proj_self hN hy]
    exact hy
theorem isCompactSubset_closedSupport_periodizeFun
    (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) (hN : HasCloseSupport s f)
    (hK : Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s f)) :
    Ambient.periodic.IsCompactSubset s (Ambient.periodic.closedSupport s (periodizeFun s f)) := by
  rw [closedSupport_periodizeFun hd hT hN hK]
  exact isCompactWrt_image (d := TestFunctions.euclidDistR4) hT.2.2.2.2 hK
theorem uniformNorm_periodizeFun (hN : HasCloseSupport s f) (hb : TestFunctions.IsBoundedFun f) :
    TestFunctions.uniformNorm (periodizeFun s f) = TestFunctions.uniformNorm f ∧
      TestFunctions.IsBoundedFun (periodizeFun s f) := by
  obtain ⟨C, hC⟩ := hb
  have hbdd : BddAbove (range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have h0 : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  have hval : ∀ u, ‖periodizeFun s f u‖ ≤ TestFunctions.uniformNorm f := by
    intro u
    by_cases hu : periodizeFun s f u = 0
    · rw [hu, norm_zero]
      exact h0
    · obtain ⟨x, -, -, hx⟩ := exists_of_periodizeFun_ne hN hu
      rw [hx]
      exact le_ciSup hbdd x
  have hb' : BddAbove (range fun u => ‖periodizeFun s f u‖) :=
    ⟨TestFunctions.uniformNorm f, by rintro _ ⟨u, rfl⟩; exact hval u⟩
  refine ⟨le_antisymm (ciSup_le hval) (ciSup_le fun x => ?_), TestFunctions.uniformNorm f, hval⟩
  by_cases hx : f x = 0
  · rw [hx, norm_zero]
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  · have h1 : ‖periodizeFun s f (Ambient.periodic.proj s x)‖ ≤
        TestFunctions.uniformNorm (periodizeFun s f) := le_ciSup hb' _
    rwa [periodizeFun_proj_self hN hx] at h1
theorem periodizeFun_lipschitz_bound (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) (hN : HasCloseSupport s f) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y)
    (u v : s.Torus) :
    ‖periodizeFun s f u - periodizeFun s f v‖ ≤ C * Ambient.periodic.pointDist s u v := by
  have one : ∀ u v : s.Torus, periodizeFun s f u ≠ 0 → periodizeFun s f v = 0 →
      ‖periodizeFun s f u - periodizeFun s f v‖ ≤ C * Ambient.periodic.pointDist s u v := by
    intro u v hu hv
    obtain ⟨x, rfl, hx, hux⟩ := exists_of_periodizeFun_ne hN hu
    obtain ⟨w, hw, hwd⟩ := hT.2.2.2.1 (Ambient.periodic.proj s x) v x rfl
    have hw' : Ambient.periodic.proj s w = v := hw
    subst hw'
    have hfw : f w = 0 := by
      by_contra hne
      have h1 := periodizeFun_proj_self hN hne
      rw [hv] at h1
      exact hne h1.symm
    rw [hux, hv, ← hwd]
    have h2 := hC x w
    rw [hfw] at h2
    exact h2
  by_cases hu : periodizeFun s f u = 0
  · by_cases hv : periodizeFun s f v = 0
    · rw [hu, hv, sub_self, norm_zero]
      exact mul_nonneg hC0 (hT.2.1.nonneg u v)
    · rw [norm_sub_rev, hT.2.1.symm u v]
      exact one v u hv hu
  · by_cases hv : periodizeFun s f v = 0
    · exact one u v hu hv
    · obtain ⟨x, rfl, hx, hux⟩ := exists_of_periodizeFun_ne hN hu
      obtain ⟨y, rfl, hy, hvy⟩ := exists_of_periodizeFun_ne hN hv
      rw [hux, hvy, pointDist_proj hd hT (hN x y hx hy)]
      exact hC x y
theorem isLip_periodizeFun (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) (hN : HasCloseSupport s f)
    (hf : Ambient.euclidean.IsLip s f) :
    Ambient.periodic.IsLip s (periodizeFun s f) := by
  obtain ⟨C, h0, hC⟩ := hf
  exact ⟨C, h0, periodizeFun_lipschitz_bound hd hT hN h0 hC⟩
theorem lipConst_periodizeFun_le (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) (hN : HasCloseSupport s f)
    (hf : Ambient.euclidean.IsLip s f) :
    Ambient.periodic.lipConst s (periodizeFun s f) ≤ Ambient.euclidean.lipConst s f := by
  refine csInf_le_csInf ⟨0, fun c hc => hc.1⟩ ?_ ?_
  · obtain ⟨C, h0, hC⟩ := hf
    exact ⟨C, h0, hC⟩
  · rintro C ⟨h0, hC⟩
    exact ⟨h0, periodizeFun_lipschitz_bound hd hT hN h0 hC⟩
theorem contDiff_periodicSum (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hN : HasCloseSupport s f) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (TestFunctions.periodicSum s.side f) := by
  have hs := side_pos s
  have tri : ∀ a b c : Fin 4 → ℝ,
      euclidNormVec (a - c) ≤ euclidNormVec (a - b) + euclidNormVec (b - c) := hd.triangle
  have sym : ∀ a b : Fin 4 → ℝ, euclidNormVec (a - b) = euclidNormVec (b - a) := hd.symm
  rw [contDiff_iff_contDiffAt]
  intro y₀
  have hnb : {y : Fin 4 → ℝ | euclidNormVec (y - y₀) < s.side / 8} ∈ nhds y₀ := by
    have hc : Continuous fun y : Fin 4 → ℝ => euclidNormVec (y - y₀) := by
      unfold euclidNormVec
      fun_prop
    refine hc.continuousAt (Iio_mem_nhds ?_)
    simp only [euclidNormVec, sub_self, Pi.zero_apply]
    simp
    linarith
  by_cases hex : ∃ (y : Fin 4 → ℝ) (k : Fin 4 → ℤ), euclidNormVec (y - y₀) < s.side / 8 ∧
      f (y + TestFunctions.latticeTranslate s.side k) ≠ 0
  · obtain ⟨y₁, k₀, hy₁, hk₀⟩ := hex
    have huniq : ∀ (y : Fin 4 → ℝ) (k : Fin 4 → ℤ), euclidNormVec (y - y₀) < s.side / 8 →
        f (y + TestFunctions.latticeTranslate s.side k) ≠ 0 → k = k₀ := by
      intro y k hy hk
      by_contra hne
      have h1 := side_le_euclidNormVec_latticeTranslate hs (sub_ne_zero.mpr hne)
      have h2 := hN _ _ hk hk₀
      have e : TestFunctions.latticeTranslate s.side (k - k₀) =
          (y₀ + TestFunctions.latticeTranslate s.side k) -
            (y₀ + TestFunctions.latticeTranslate s.side k₀) := by
        funext μ
        simp [TestFunctions.latticeTranslate, mul_sub]
      have e1 : (y₀ + TestFunctions.latticeTranslate s.side k) -
          (y + TestFunctions.latticeTranslate s.side k) = y₀ - y := by abel
      have e2 : (y₁ + TestFunctions.latticeTranslate s.side k₀) -
          (y₀ + TestFunctions.latticeTranslate s.side k₀) = y₁ - y₀ := by abel
      have t1 := tri (y₀ + TestFunctions.latticeTranslate s.side k)
        (y + TestFunctions.latticeTranslate s.side k)
        (y₀ + TestFunctions.latticeTranslate s.side k₀)
      have t2 := tri (y + TestFunctions.latticeTranslate s.side k)
        (y₁ + TestFunctions.latticeTranslate s.side k₀)
        (y₀ + TestFunctions.latticeTranslate s.side k₀)
      rw [e1] at t1
      rw [e2] at t2
      rw [e] at h1
      have h3 := sym y₀ y
      linarith
    have heq : TestFunctions.periodicSum s.side f =ᶠ[nhds y₀]
        fun y => f (y + TestFunctions.latticeTranslate s.side k₀) := by
      filter_upwards [hnb] with y hy
      exact tsum_eq_single k₀ fun k hk => by_contra fun hne => hk (huniq y k hy hne)
    exact (hf.comp (contDiff_id.add contDiff_const)).contDiffAt.congr_of_eventuallyEq heq
  · simp only [not_exists, not_and, ne_eq, not_not] at hex
    have heq : TestFunctions.periodicSum s.side f =ᶠ[nhds y₀] fun _ => (0 : ℝ) := by
      filter_upwards [hnb] with y hy
      simp [TestFunctions.periodicSum, hex y _ hy]
    exact contDiffAt_const.congr_of_eventuallyEq heq
theorem periodizeFun_mem_c1Compact (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) (hN : HasCloseSupport s f)
    (hf : f ∈ Ambient.euclidean.c1Compact s) :
    periodizeFun s f ∈ Ambient.periodic.c1Compact s := by
  refine ⟨?_, isCompactSubset_closedSupport_periodizeFun hd hT hN hf.2⟩
  have e : Ambient.periodic.liftFun s (periodizeFun s f) = TestFunctions.periodicSum s.side f := by
    funext y
    exact TestFunctions.periodize_torusProj s.side f y
  show ContDiff ℝ 1 (Ambient.periodic.liftFun s (periodizeFun s f))
  rw [e]
  exact contDiff_periodicSum hd hN hf.1
theorem periodizeFun_reflectFun (μ : Fin 4) (c : ℝ) (f : (Fin 4 → ℝ) → ℝ) :
    periodizeFun s (Ambient.euclidean.reflectFun s μ c f) =
      Ambient.periodic.reflectFun s μ c (periodizeFun s f) := by
  funext u
  obtain ⟨y, rfl⟩ := Ambient.periodic.proj_surjective s u
  have h1 : Ambient.periodic.reflect s μ c (Ambient.periodic.proj s y) =
      Ambient.periodic.proj s (reflectR4 μ c y) :=
    congrFun (Ambient.periodic.reflect_comp_proj s μ c) y
  have e1 : periodizeFun s (Ambient.euclidean.reflectFun s μ c f) (Ambient.periodic.proj s y) =
      ∑' k, f (reflectR4 μ c (y + TestFunctions.latticeTranslate s.side k)) := by
    refine (TestFunctions.periodize_torusProj s.side
      (Ambient.euclidean.reflectFun s μ c f) y).trans ?_
    exact tsum_congr fun k => congrArg f (Ambient.reflect_euclidean s μ c _)
  have e2 : periodizeFun s f (Ambient.periodic.proj s (reflectR4 μ c y)) =
      ∑' k, f (reflectR4 μ c y + TestFunctions.latticeTranslate s.side k) :=
    TestFunctions.periodize_torusProj s.side f _
  show periodizeFun s (Ambient.euclidean.reflectFun s μ c f) (Ambient.periodic.proj s y) =
    periodizeFun s f (Ambient.periodic.reflect s μ c (Ambient.periodic.proj s y))
  rw [h1, e1, e2]
  let σ : (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) :=
    Function.Involutive.toPerm (fun k ν => if ν = μ then -k ν else k ν) (by
      intro k
      funext ν
      by_cases hν : ν = μ <;> simp [hν])
  rw [← σ.tsum_eq (fun k => f (reflectR4 μ c y + TestFunctions.latticeTranslate s.side k))]
  refine tsum_congr fun k => ?_
  congr 1
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [reflectR4, stdBasisVec, TestFunctions.latticeTranslate, σ,
      Function.Involutive.toPerm]
    ring
  · simp [reflectR4, stdBasisVec, TestFunctions.latticeTranslate, σ,
      Function.Involutive.toPerm, hν]
end Periodized
theorem projIsometricOn_of_diam (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) {S : Set (Fin 4 → ℝ)}
    (hS : TestFunctions.HasDiameterLE S (s.side / 2)) : ProjIsometricOn s S := by
  refine ⟨fun x hx y hy => pointDist_proj hd hT (hS x hx y hy), fun A B hA hB => ?_⟩
  show (⨅ x ∈ Ambient.periodic.proj s '' A, ⨅ y ∈ Ambient.periodic.proj s '' B,
      ENNReal.ofReal (Ambient.periodic.pointDist s x y)) =
    ⨅ x ∈ A, ⨅ y ∈ B, ENNReal.ofReal (Ambient.euclidean.pointDist s x y)
  simp only [iInf_image]
  refine iInf_congr fun a => iInf_congr fun ha => iInf_congr fun b => iInf_congr fun hb => ?_
  rw [pointDist_proj hd hT (hS a (hA ha) b (hB hb))]
  rfl
theorem listGap_periodizeList (X : List ((Fin 4 → ℝ) → ℝ))
    (hX : ∀ f ∈ X, ∀ g ∈ X,
      Ambient.periodic.infSetDist s (Ambient.periodic.closedSupport s (periodizeFun s f))
          (Ambient.periodic.closedSupport s (periodizeFun s g)) =
        Ambient.euclidean.infSetDist s (Ambient.euclidean.closedSupport s f)
          (Ambient.euclidean.closedSupport s g)) :
    Ambient.periodic.listGap s (periodizeList s X) = Ambient.euclidean.listGap s X := by
  have hlen : (periodizeList s X).length = X.length := by simp [periodizeList]
  have hget : ∀ i : Fin X.length, (periodizeList s X).get (Fin.cast hlen.symm i) =
      periodizeFun s (X.get i) := by
    intro i
    simp [periodizeList]
    rfl
  have hdist : ∀ i j : Fin X.length,
      ReflectionPositivity.TorusCutoffs.setDist
          (ReflectionPositivity.TorusTuples.supp (s := s)
            ((periodizeList s X).get (Fin.cast hlen.symm i)))
          (ReflectionPositivity.TorusTuples.supp (s := s)
            ((periodizeList s X).get (Fin.cast hlen.symm j))) =
        Ambient.euclidean.infSetDist s (Ambient.euclidean.closedSupport s (X.get i))
          (Ambient.euclidean.closedSupport s (X.get j)) := by
    intro i j
    rw [hget, hget]
    exact hX _ (List.get_mem _ _) _ (List.get_mem _ _)
  show ((Finset.univ.offDiag :
        Finset (Fin (periodizeList s X).length × Fin (periodizeList s X).length)).inf fun p =>
      ReflectionPositivity.TorusCutoffs.setDist
        (ReflectionPositivity.TorusTuples.supp (s := s) ((periodizeList s X).get p.1))
        (ReflectionPositivity.TorusTuples.supp (s := s) ((periodizeList s X).get p.2))) =
    (Finset.univ.offDiag : Finset (Fin X.length × Fin X.length)).inf fun p =>
      Ambient.euclidean.infSetDist s (Ambient.euclidean.closedSupport s (X.get p.1))
        (Ambient.euclidean.closedSupport s (X.get p.2))
  apply le_antisymm
  · refine Finset.le_inf fun p hp => ?_
    exact (Finset.inf_le (b := (Fin.cast hlen.symm p.1, Fin.cast hlen.symm p.2))
      (by simpa [Finset.mem_offDiag, Fin.ext_iff] using hp)).trans_eq (hdist p.1 p.2)
  · refine Finset.le_inf fun p hp => ?_
    have h1 : Fin.cast hlen.symm (Fin.cast hlen p.1) = p.1 := Fin.ext rfl
    have h2 : Fin.cast hlen.symm (Fin.cast hlen p.2) = p.2 := Fin.ext rfl
    have e := hdist (Fin.cast hlen p.1) (Fin.cast hlen p.2)
    rw [h1, h2] at e
    exact (Finset.inf_le (b := (Fin.cast hlen p.1, Fin.cast hlen p.2))
      (by simpa [Finset.mem_offDiag, Fin.ext_iff] using hp)).trans_eq e.symm
theorem periodizeSeparatedTuple_holds (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) {n : ℕ}
    (g : Fin n → (Fin 4 → ℝ) → ℝ) : PeriodizeSeparatedTuple s g := by
  intro h1 h2
  have hS : TestFunctions.HasDiameterLE (⋃ i, Ambient.euclidean.closedSupport s (g i))
      (s.side / 2) := by
    have e := Ambient.listSupport_ofFn s Ambient.euclidean (Z := ℝ) g
    intro x hx y hy
    exact h2.2 x (e.superset hx) y (e.superset hy)
  have hsub : ∀ i, Ambient.euclidean.closedSupport s (g i) ⊆
      ⋃ i, Ambient.euclidean.closedSupport s (g i) :=
    fun i => subset_iUnion (fun i => Ambient.euclidean.closedSupport s (g i)) i
  have hK : ∀ i, Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s (g i)) :=
    fun i => (h1.1 i).2.1
  have hN : ∀ i, HasCloseSupport s (g i) :=
    fun i => hasCloseSupport_of_supportedWithin hd hS ⟨hK i, hsub i⟩
  have hsupp : ∀ i, Ambient.periodic.closedSupport s (periodizeFun s (g i)) =
      Ambient.periodic.proj s '' Ambient.euclidean.closedSupport s (g i) :=
    fun i => closedSupport_periodizeFun hd hT (hN i) (hK i)
  have hlip : ∀ i, periodizeFun s (g i) ∈ Ambient.periodic.lipWithin s univ := fun i =>
    ⟨isLip_periodizeFun hd hT (hN i) (h1.1 i).1,
      isCompactSubset_closedSupport_periodizeFun hd hT (hN i) (hK i), subset_univ _⟩
  have hdisj : Pairwise fun i j =>
      Disjoint (Ambient.periodic.closedSupport s (periodizeFun s (g i)))
        (Ambient.periodic.closedSupport s (periodizeFun s (g j))) := by
    intro i j hij
    rw [hsupp, hsupp, Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hdist := pointDist_proj hd hT (hS x (hsub i hx) y (hsub j hy))
    rw [← hxy, (hT.2.1.eq_zero_iff _ _).mpr rfl] at hdist
    have hxy' : x = y := (hd.eq_zero_iff x y).mp hdist.symm
    subst hxy'
    exact Set.disjoint_left.mp (h1.2 hij) hx hy
  refine ⟨⟨hlip, hdisj⟩, ?_, ?_, fun hc => ⟨⟨hlip, hdisj⟩, fun i =>
    periodizeFun_mem_c1Compact hd hT (hN i) (hc.2 i)⟩⟩
  · refine listGap_periodizeList _ ?_
    intro f hf h hh
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hf
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hh
    rw [hsupp i, hsupp j]
    exact (projIsometricOn_of_diam hd hT hS).2 _ _ (hsub i) (hsub j)
  · intro J
    rw [periodizeList_ofFn]
    rfl
theorem periodizeReflectAppend_holds (hSpace : AmbientMetric.Claim)
    (hSides : ReflectionPositivity.AxisMirror.Sides.HyperplaneSidesClaim)
    (D : ReflectionPositivity.AxisMirror.MirrorData)
    (X Y : List ((Fin 4 → ℝ) → ℝ)) : PeriodizeReflectAppend D X Y := by
  intro hX hY μ c hfit
  have hθ := (hSpace D.toStandingParameters .euclidean).2.2.2.2.2.1 μ c
  have hsupp : ∀ f : (Fin 4 → ℝ) → ℝ,
      Ambient.euclidean.closedSupport D.toStandingParameters
          (Ambient.euclidean.reflectFun D.toStandingParameters μ c f) =
        Ambient.euclidean.reflect D.toStandingParameters μ c ''
          Ambient.euclidean.closedSupport D.toStandingParameters f :=
    fun f => (((hSides D μ c).1 .euclidean).1.2.2.2.2.2.1 ℝ f 0).1
  have hconc : (⟨μ, c⟩ : ReflectionPositivity.AxisMirror.CoordMirror).reflectAppend D .euclidean
      X Y =
      (X.map (Ambient.euclidean.reflectFun D.toStandingParameters μ c) :
        List ((Fin 4 → ℝ) → ℝ)) ++ Y := by
    show (X.map (ReflectionPositivity.AxisMirror.CoordMirror.pullback D ⟨μ, c⟩ .euclidean) :
      List ((Fin 4 → ℝ) → ℝ)) ++ Y = _
    congr 1
    exact List.map_congr_left fun f _ =>
      congrArg (fun t => f ∘ t) (ReflectionPositivity.AxisMirror.Sides.reflect_euclidean D μ c)
  rw [hconc] at hfit ⊢
  have hdiam := hfit.2
  have hXmem : ∀ x ∈ Ambient.euclidean.listSupport D.toStandingParameters X,
      Ambient.euclidean.reflect D.toStandingParameters μ c x ∈
        Ambient.euclidean.listSupport D.toStandingParameters
          ((X.map (Ambient.euclidean.reflectFun D.toStandingParameters μ c) :
            List ((Fin 4 → ℝ) → ℝ)) ++ Y) := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨Ambient.euclidean.reflectFun D.toStandingParameters μ c f,
      List.mem_append_left _ (List.mem_map_of_mem hf), ?_⟩
    exact (hsupp f).superset (mem_image_of_mem _ hxf)
  have hYmem : Ambient.euclidean.listSupport D.toStandingParameters Y ⊆
      Ambient.euclidean.listSupport D.toStandingParameters
        ((X.map (Ambient.euclidean.reflectFun D.toStandingParameters μ c) :
          List ((Fin 4 → ℝ) → ℝ)) ++ Y) := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨f, List.mem_append_right _ hf, hxf⟩
  refine ⟨⟨hX, fun x hx y hy => (hθ.2.1 x y).symm.le.trans
      (hdiam _ (hXmem x hx) _ (hXmem y hy))⟩,
    ⟨hY, fun x hx y hy => hdiam x (hYmem hx) y (hYmem hy)⟩, ?_⟩
  have hrt : ∀ f : (Fin 4 → ℝ) → ℝ,
      periodizeFun D.toStandingParameters
          (Ambient.euclidean.reflectFun D.toStandingParameters μ c f) =
        ReflectionPositivity.AxisMirror.CoordMirror.pullback D ⟨μ, c⟩ .torus
          (periodizeFun D.toStandingParameters f) := fun f =>
    (periodizeFun_reflectFun μ c f).trans
      (congrArg (fun t => periodizeFun D.toStandingParameters f ∘ t)
        (ReflectionPositivity.AxisMirror.Sides.reflect_torus D μ c).symm)
  show List.map (periodizeFun D.toStandingParameters)
      ((X.map (Ambient.euclidean.reflectFun D.toStandingParameters μ c) :
        List ((Fin 4 → ℝ) → ℝ)) ++ Y) =
    (List.map (ReflectionPositivity.AxisMirror.CoordMirror.pullback D ⟨μ, c⟩ .torus)
      (List.map (periodizeFun D.toStandingParameters) X) : List (D.Torus → ℝ)) ++
        List.map (periodizeFun D.toStandingParameters) Y
  have hmap : ∀ L : List ((Fin 4 → ℝ) → ℝ),
      List.map (periodizeFun D.toStandingParameters)
          (L.map (Ambient.euclidean.reflectFun D.toStandingParameters μ c) :
            List ((Fin 4 → ℝ) → ℝ)) =
        (List.map (ReflectionPositivity.AxisMirror.CoordMirror.pullback D ⟨μ, c⟩ .torus)
          (List.map (periodizeFun D.toStandingParameters) L) : List (D.Torus → ℝ)) := by
    intro L
    induction L with
    | nil => rfl
    | cons f L ih => exact congrArg₂ List.cons (hrt f) ih
  rw [List.map_append]
  exact congrArg (fun Z => Z ++ List.map (periodizeFun D.toStandingParameters) Y) (hmap X)
theorem periodizePreservesNormsAndClasses_holds
    (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) {f : (Fin 4 → ℝ) → ℝ}
    (hN : HasCloseSupport s f)
    (hb : Ambient.euclidean.IsLip s f → TestFunctions.IsBoundedFun f) :
    PeriodizePreservesNormsAndClasses s f := by
  refine ⟨fun h => uniformNorm_periodizeFun hN h, fun hl => ⟨isLip_periodizeFun hd hT hN hl,
    lipConst_periodizeFun_le hd hT hN hl, fun M => ?_⟩,
    fun hc => periodizeFun_mem_c1Compact hd hT hN hc⟩
  show max (TestFunctions.uniformNorm (periodizeFun s f))
      (40 * (M : ℝ) * Ambient.periodic.lipConst s (periodizeFun s f)) ≤
    max (TestFunctions.uniformNorm f) (40 * (M : ℝ) * Ambient.euclidean.lipConst s f)
  rw [(uniformNorm_periodizeFun hN (hb hl)).1]
  have hM : (0 : ℝ) ≤ 40 * (M : ℝ) := by
    have := M.2
    simp only [Set.mem_Ici] at this
    linarith
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_left (lipConst_periodizeFun_le hd hT hN hl) hM)
theorem supportOfPeriodize_holds (hd : IsMetricFunction (Ambient.euclidean.pointDist s))
    (hT : AmbientMetric.EuclidDistFacts s .periodic) {f : (Fin 4 → ℝ) → ℝ}
    (hN : HasCloseSupport s f)
    (hK : Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s f)) :
    SupportOfPeriodize s f := by
  refine ⟨closedSupport_periodizeFun hd hT hN hK, fun x R _ _ hball => ?_⟩
  rw [closedSupport_periodizeFun hd hT hN hK]
  rintro _ ⟨y, hy, rfl⟩
  exact (hT.1 y x).2.trans (hball hy)
theorem periodizeCommutesWithReflect_holds (hSpace : AmbientMetric.Claim)
    (hSides : ReflectionPositivity.AxisMirror.Sides.HyperplaneSidesClaim)
    (D : ReflectionPositivity.AxisMirror.MirrorData)
    {S : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hS : TestFunctions.HasDiameterLE S (D.side / 2))
    (hf : Ambient.euclidean.SupportedWithin D.toStandingParameters S f) :
    PeriodizeCommutesWithReflect D.toStandingParameters S f := by
  intro μ c
  have hθ := (hSpace D.toStandingParameters .euclidean).2.2.2.2.2.1 μ c
  have hcont : IsContinuousWrt (Ambient.euclidean.pointDist D.toStandingParameters)
      (Ambient.euclidean.pointDist D.toStandingParameters)
      (Ambient.euclidean.reflect D.toStandingParameters μ c) :=
    fun x ε hε => ⟨ε, hε, fun y hy => by rw [hθ.2.1 x y]; exact hy⟩
  have hsupp : Ambient.euclidean.closedSupport D.toStandingParameters
        (Ambient.euclidean.reflectFun D.toStandingParameters μ c f) =
      Ambient.euclidean.reflect D.toStandingParameters μ c ''
        Ambient.euclidean.closedSupport D.toStandingParameters f :=
    (((hSides D μ c).1 .euclidean).1.2.2.2.2.2.1 ℝ f 0).1
  refine ⟨⟨?_, ?_⟩, ?_, periodizeFun_reflectFun μ c f⟩
  · rw [hsupp]
    exact isCompactWrt_image hcont hf.1
  · rw [hsupp]
    exact image_mono hf.2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hθ.2.1 a b).le.trans (hS a ha b hb)
theorem periodizeSupportedInOpenSlab_holds {D : ReflectionPositivity.AxisMirror.MirrorData}
    (hd : IsMetricFunction (Ambient.euclidean.pointDist D.toStandingParameters))
    (hT : AmbientMetric.EuclidDistFacts D.toStandingParameters .periodic)
    {f : (Fin 4 → ℝ) → ℝ} (hN : HasCloseSupport D.toStandingParameters f)
    (hK : Ambient.euclidean.IsCompactSubset D.toStandingParameters
      (Ambient.euclidean.closedSupport D.toStandingParameters f)) :
    PeriodizeSupportedInOpenSlab D f := by
  intro μ c h
  refine ⟨isCompactSubset_closedSupport_periodizeFun hd hT hN hK, ?_⟩
  rw [closedSupport_periodizeFun hd hT hN hK]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h1, h2⟩ := h hy
  refine (?_ : _ ∈ D.projection '' ReflectionPositivity.AxisMirror.coordSet μ
    fun t => 0 < t - c ∧ t - c < D.side / 2)
  refine ⟨y, ?_, rfl⟩
  show 0 < y μ - c ∧ y μ - c < D.side / 2
  constructor <;> linarith
theorem properties_holds (hSpace : AmbientMetric.Claim)
    (hProducts : Ambient.testSpacesAndSepTuples)
    (hSides : ReflectionPositivity.AxisMirror.Sides.HyperplaneSidesClaim) : Properties := by
  intro D
  have hT := (hSpace D.toStandingParameters .periodic).1
  have hd := (hSpace D.toStandingParameters .euclidean).1.2.1
  refine ⟨fun S f h hS hf hh => ?_, fun n g => periodizeSeparatedTuple_holds hd hT g,
    fun X Y => periodizeReflectAppend_holds hSpace hSides D X Y⟩
  have hNf := hasCloseSupport_of_supportedWithin hd hS hf
  have hNh := hasCloseSupport_of_supportedWithin hd hS hh
  have hb : Ambient.euclidean.IsLip D.toStandingParameters f → TestFunctions.IsBoundedFun f :=
    fun hl =>
      (((hProducts D.toStandingParameters .euclidean ⟨1, Set.mem_Ici.mpr le_rfl⟩ S univ 1
        le_rfl).1.2.1 f ⟨hl, hf⟩).2)
  exact ⟨projIsometricOn_of_diam hd hT hS,
    fun y => ⟨TestFunctions.periodize_torusProj D.side f y,
      fun _ hk _ hk' => latticeIndex_unique hNf y hk hk'⟩,
    fun u u' => periodizeFun_linear hNf hNh u u',
    supportOfPeriodize_holds hd hT hNf hf.1,
    periodizePreservesNormsAndClasses_holds hd hT hNf hb,
    periodizeCommutesWithReflect_holds hSpace hSides D hS hf,
    periodizeSupportedInOpenSlab_holds hd hT hNf hf.1⟩
end YangMills.Construction.LimitSpaces.Periodization
