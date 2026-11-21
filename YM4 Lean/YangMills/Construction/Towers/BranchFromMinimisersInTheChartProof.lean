import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOne
import YangMills.Construction.Towers.BranchFromMinimisersInTheChart
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurations
import YangMills.Construction.Towers.CriticalPointsAndHessiansThroughAChart
import YangMills.Construction.Towers.CurvesReadInTheChartAtOne
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersion
import YangMills.Construction.Towers.MapsReadBackFromTheChartAtOne
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.IdentityExpChart YangMills.Construction.ConstrainedMinima
theorem minimizerChartGivesFibreSection_of_charts
    (hStep : CriticalStepInExpChart)
    (hChart : IdentityChartOnFields)
    (hCurves : IdentityChartCurvesStatement)
    (hMaps : IdentityChartPullback.Statement)
    (hSm : SmoothingOnIdentityLieBallStatement)
    (hRead : Geometry.ChartedCriticalPoints.Statement)
    (hFib : SubmersionFibresAreSubmanifolds) :
    MinimizerChartGivesFibreSection := by
  intro L n k i hL hn hi _ _ F hF hgrad hpos
  obtain ⟨hcm, hdm, hdf⟩ := hStep L n k i hL hn hi F hF hgrad hpos
  have hik : i ≤ k := hi.le
  have hik' : i + 1 ≤ k := hi
  obtain ⟨hSo, hS0, hE0, hEL, hEo, hEt, hLt, hball, hballm, hfam, hfam'⟩ :=
    hChart L n k i hL hn hik
  obtain ⟨hSo', hS0', hE0', hEL', hEo', hEt', hLt', hball', hballm', hfam2, hfam2'⟩ :=
    hChart L n k (i + 1) hL hn hik'
  obtain ⟨hQ, T, hT, hTS, hTM, hTA⟩ := hSm L n k i hL hn hi
  obtain ⟨hCv1, hCv2, hCv3⟩ := hCurves L n k i hL hn hik
  refine ⟨T, hT, ?_⟩
  intro 𝒩 O 𝒲 ρ c b hc h𝒩T
  have h𝒩S := h𝒩T.trans hTS
  have : CompleteSpace Matrices.ComplexMatrix2.LieElement := FiniteDimensional.complete ℝ _
  have : CompleteSpace (tangentKernel (smoothingInExpChart L n k i)) :=
    FiniteDimensional.complete ℝ _
  have hSmE : ∀ y ∈ T, smoothingStep L n k i (identityChartPoint y) =
      identityChartPoint (smoothingInExpChart L n k i y) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hTM hy
    have hzy' : identityChartPoint z = smoothingStep L n k i (identityChartPoint y) := hzy
    have h1 : smoothingInExpChart L n k i y = z := by
      change identityChartLog (smoothingStep L n k i (identityChartPoint y)) = z
      rw [← hzy']
      exact (hEL' z hz).2
    rw [h1, hzy']
  set s := fiberMinimizer c b with hs_def
  have hsmem : ∀ Z ∈ 𝒲, s Z ∈ 𝒩 := fun Z hZ =>
    hc.chart_mem_nhd (b Z) (hc.min_mem Z hZ) Z hZ
  have hsan : AnalyticOnNhd ℝ s 𝒲 := by
    intro Z hZ
    have h1 : AnalyticAt ℝ (fun Z => (b Z, Z)) Z :=
      (hc.analyticOnNhd_min Z hZ).prod analyticAt_id
    have h2 : AnalyticAt ℝ (fun q : tangentKernel (smoothingInExpChart L n k i) ×
        (PositiveEdge L n k (i + 1) → Matrices.ComplexMatrix2.LieElement) => c q.1 q.2)
        ((fun Z => (b Z, Z)) Z) :=
      hc.analyticOnNhd_chart (b Z, Z) ⟨hc.min_mem Z hZ, hZ⟩
    exact AnalyticAt.comp (f := fun Z => (b Z, Z)) (x := Z) h2 h1
  have hs0 : s 0 = 0 := by
    change c (b 0) 0 = 0
    rw [hc.min_zero, hc.chart_zero_zero]
  have hlog1 : identityChartLog (trivialField L n k (i + 1)) = 0 := by
    rw [← hE0']
    exact (hEL' 0 hS0').2
  set 𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2) := identityChartPoint '' 𝒩 with h𝒰_def
  have h𝒰open := hEo 𝒩 hc.isOpen_nhd h𝒩S
  have h𝒰one : trivialField L n k i ∈ 𝒰 := ⟨0, hc.zero_mem_nhd, hE0⟩
  obtain ⟨ε, hε, hεs⟩ := hball 𝒩 (hc.isOpen_nhd.mem_nhds hc.zero_mem_nhd)
  have hsmall' := hSo'.mem_nhds hS0'
  obtain ⟨ε', hε', hεs'⟩ := hball' _ hsmall'
  set p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2 :=
    fun W => identityChartPoint (s (identityChartLog W)) with hp_def
  obtain ⟨hMan, hMfirst⟩ := hMaps L n k i (i + 1) hL hn hik hik' s
  have hAopen := hc.isOpen_values.inter hSo'
  have hnear : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      identityChartLog W ∈ 𝒲 ∧ identityChartPoint (identityChartLog W) = W := by
    filter_upwards [hLt' (hc.isOpen_values.mem_nhds hc.zero_mem_values), hballm' ε' hε'] with W h1 h2
    obtain ⟨z, hz, rfl⟩ := hεs' h2
    exact ⟨h1, by rw [(hEL' z hz).2]⟩
  have hpball : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      p W ∈ nearIdentityBall L n k i ε := by
    have ht1 : Tendsto (fun W => s (identityChartLog W))
        (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1)) (𝓝 0) := by
      have h1 := (hsan 0 hc.zero_mem_values).continuousAt.tendsto
      rw [hs0] at h1
      exact h1.comp hLt'
    have ht2 := hEt.comp ht1
    have ht3 : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
        p W ∈ fieldSpace L n k i :=
      hnear.mono fun W h => (hEL _ (h𝒩S (hsmem _ h.1))).1
    exact (tendsto_nhdsWithin_iff.mpr ⟨ht2, ht3⟩).eventually (hballm ε hε)
  have hsec : ∀ W, identityChartLog W ∈ 𝒲 → identityChartPoint (identityChartLog W) = W →
      smoothingStep L n k i (p W) = W := by
    intro W hZ hW
    have h1 : smoothingStep L n k i (identityChartPoint (s (identityChartLog W))) =
        identityChartPoint (smoothingInExpChart L n k i (s (identityChartLog W))) :=
      hSmE _ (h𝒩T (hsmem _ hZ))
    have h2 : smoothingInExpChart L n k i (s (identityChartLog W)) = identityChartLog W :=
      hc.map_chart _ (hc.min_mem _ hZ) _ hZ
    change smoothingStep L n k i (identityChartPoint (s (identityChartLog W))) = W
    rw [h1, h2, hW]
  have hN : ∀ W, ∀ V ∈ CriticalBranchData.levelFibre 𝒰 W, identityChartLog V ∈ 𝒩 ∧
      V = identityChartPoint (identityChartLog V) ∧
      smoothingInExpChart L n k i (identityChartLog V) = identityChartLog W := by
    rintro W V ⟨⟨y, hy, rfl⟩, hV⟩
    have hly := (hEL y (h𝒩S hy)).2
    rw [hly]
    refine ⟨hy, rfl, ?_⟩
    change identityChartLog (smoothingStep L n k i (identityChartPoint y)) = _
    rw [hV]
  have hcy : ∀ W, ∀ V ∈ CriticalBranchData.levelFibre 𝒰 W,
      c (ρ (identityChartLog V)) (identityChartLog W) = identityChartLog V ∧
        ρ (identityChartLog V) ∈ O := by
    intro W V hV
    obtain ⟨h1, -, h3⟩ := hN W V hV
    obtain ⟨o1, -, o3⟩ := hc.chart_surj _ h1
    rw [h3] at o3
    exact ⟨o3, o1⟩
  have hfibS : ∀ W, CriticalBranchData.levelFibre 𝒰 W ⊆
      identityChartPoint '' lieBall (PositiveEdge L n k i) (1 / 2) :=
    fun W V hV => image_mono h𝒩S hV.1
  have hczan : ∀ Z ∈ 𝒲, AnalyticOnNhd ℝ (fun x => c x Z) O := by
    intro Z hZ x hx
    have h1 : AnalyticAt ℝ (fun x : tangentKernel (smoothingInExpChart L n k i) => (x, Z)) x :=
      analyticAt_id.prod analyticAt_const
    have h2 : AnalyticAt ℝ (fun q : tangentKernel (smoothingInExpChart L n k i) ×
        (PositiveEdge L n k (i + 1) → Matrices.ComplexMatrix2.LieElement) => c q.1 q.2)
        ((fun x : tangentKernel (smoothingInExpChart L n k i) => (x, Z)) x) :=
      hc.analyticOnNhd_chart (x, Z) ⟨hx, hZ⟩
    exact AnalyticAt.comp (f := fun x : tangentKernel (smoothingInExpChart L n k i) => (x, Z))
      (x := x) h2 h1
  choose! Dy hDinj hDtan using hCv3
  have hread : ∀ W, identityChartLog W ∈ 𝒲 → identityChartPoint (identityChartLog W) = W →
      (fieldCurveData L n k i).IsChartedBy (CriticalBranchData.levelFibre 𝒰 W) O
        (fun x => identityChartPoint (c x (identityChartLog W))) (fun V => ρ (identityChartLog V))
        (fun x => (Dy (c x (identityChartLog W))).comp
          (fderiv ℝ (fun x => c x (identityChartLog W)) x).toLinearMap) := by
    intro W hZ hW
    have hcan := hczan _ hZ
    have hcdAt : ∀ x ∈ O, DifferentiableAt ℝ (fun x => c x (identityChartLog W)) x :=
      fun x hx => (hcan x hx).differentiableAt
    have hcd : DifferentiableOn ℝ (fun x => c x (identityChartLog W)) O :=
      fun x hx => (hcdAt x hx).differentiableWithinAt
    have hcsmall : ∀ x ∈ O, c x (identityChartLog W) ∈ lieBall (PositiveEdge L n k i) (1 / 2) :=
      fun x hx => h𝒩S (hc.chart_mem_nhd x hx _ hZ)
    refine
      { isOpen_domain := hc.isOpen_params
        mapsTo_param := ?_
        coord_mem := fun V hV => (hcy W V hV).2
        param_coord := ?_
        coord_param := ?_
        isInterval := fun I γ h => h.1
        coord_differentiableOn := ?_
        twice_coord := ?_
        param_isCurve := ?_
        param_isTwiceDiffCurve := ?_
        tangent_eq := ?_
        injective_diff := ?_ }
    · intro x hx
      refine ⟨⟨_, hc.chart_mem_nhd x hx _ hZ, rfl⟩, ?_⟩
      change smoothingStep L n k i (identityChartPoint (c x (identityChartLog W))) = W
      rw [hSmE _ (h𝒩T (hc.chart_mem_nhd x hx _ hZ)), hc.map_chart x hx _ hZ, hW]
    · intro V hV
      rw [(hcy W V hV).1]
      exact (hN W V hV).2.1.symm
    · intro x hx
      rw [(hEL _ (hcsmall x hx)).2]
      exact hc.proj_chart x hx _ hZ
    · intro I γ h hm
      exact ρ.differentiable.comp_differentiableOn
        (hCv1 I γ h (hm.mono_right (hfibS W))).1
    · rintro I γ ⟨h1, h2⟩
      refine ⟨h1, fun hm => ?_⟩
      have hu := hCv1 I γ h1 (hm.mono_right (hfibS W))
      have hopen : IsOpen I := h1.1.1
      refine (ρ.differentiable.comp_differentiableOn (hu.2 h2)).congr ?_
      intro t ht
      have hdt : DifferentiableAt ℝ (fun t => identityChartLog (γ t)) t :=
        (hu.1 t ht).differentiableAt (hopen.mem_nhds ht)
      exact (ρ.hasFDerivAt.comp_hasDerivAt t hdt.hasDerivAt).deriv
    · intro I x hI hx hm
      have hy : DifferentiableOn ℝ (fun t => c (x t) (identityChartLog W)) I := hcd.comp hx hm
      exact (hCv2 I (fun t => c (x t) (identityChartLog W)) hI hy fun t ht => hcsmall _ (hm ht)).1
    · intro I x hI hx hx' hm
      have hy : DifferentiableOn ℝ (fun t => c (x t) (identityChartLog W)) I := hcd.comp hx hm
      have hC := hCv2 I (fun t => c (x t) (identityChartLog W)) hI hy fun t ht => hcsmall _ (hm ht)
      have hfd : DifferentiableOn ℝ (fderiv ℝ fun x => c x (identityChartLog W)) O :=
        hcan.fderiv.differentiableOn
      have hd : DifferentiableOn ℝ (deriv fun t => c (x t) (identityChartLog W)) I := by
        refine (DifferentiableOn.clm_apply (hfd.comp hx hm) hx').congr ?_
        intro t ht
        have hxt : DifferentiableAt ℝ x t := (hx t ht).differentiableAt (hI.1.mem_nhds ht)
        exact ((hcdAt _ (hm ht)).hasFDerivAt.comp_hasDerivAt t hxt.hasDerivAt).deriv
      exact And.intro hC.1 (hC.2 hd)
    · intro I γ h hm
      have hI : IsOpenIntervalAroundZero I := h.1
      have h0 : (0 : ℝ) ∈ I := hI.2.2
      have hγ0 := hm h0
      have hsm : identityChartLog (γ 0) ∈ lieBall (PositiveEdge L n k i) (1 / 2) :=
        h𝒩S (hN W _ hγ0).1
      have ht := (hDtan _ hsm) I γ h (hm.mono_right (hfibS W)) rfl
      have hy0 := (hcy W _ hγ0).1
      have hev : (fun t => identityChartLog (γ t)) =ᶠ[𝓝 0]
          fun t => c (ρ (identityChartLog (γ t))) (identityChartLog W) := by
        filter_upwards [hI.1.mem_nhds h0] with t ht
        exact ((hcy W _ (hm ht)).1).symm
      have hx : DifferentiableAt ℝ (fun t => ρ (identityChartLog (γ t))) 0 :=
        (ρ.differentiable.comp_differentiableOn
          (hCv1 I γ h (hm.mono_right (hfibS W))).1 0 h0).differentiableAt (hI.1.mem_nhds h0)
      have hder : deriv (fun t => identityChartLog (γ t)) 0 =
          fderiv ℝ (fun x => c x (identityChartLog W)) (ρ (identityChartLog (γ 0)))
            (deriv (fun t => ρ (identityChartLog (γ t))) 0) := by
        rw [hev.deriv_eq]
        exact ((hcdAt _ (hcy W _ hγ0).2).hasFDerivAt.comp_hasDerivAt 0 hx.hasDerivAt).deriv
      change curveTangent γ = Dy (c (ρ (identityChartLog (γ 0))) (identityChartLog W))
        (fderiv ℝ (fun x => c x (identityChartLog W)) (ρ (identityChartLog (γ 0)))
          (deriv (fun t => ρ (identityChartLog (γ t))) 0))
      rw [ht, hy0, hder]
    · intro x hx
      have hinv : ∀ h, ρ (fderiv ℝ (fun x => c x (identityChartLog W)) x h) = h := by
        have hev : (fun x' => ρ (c x' (identityChartLog W))) =ᶠ[𝓝 x] fun x' => x' := by
          filter_upwards [hc.isOpen_params.mem_nhds hx] with x' hx'
          exact hc.proj_chart x' hx' _ hZ
        have h1 : HasFDerivAt (fun x' => ρ (c x' (identityChartLog W)))
            (ρ.comp (fderiv ℝ (fun x => c x (identityChartLog W)) x)) x :=
          ρ.hasFDerivAt.comp x (hcdAt x hx).hasFDerivAt
        have h2 : HasFDerivAt (fun x' => ρ (c x' (identityChartLog W)))
            (ContinuousLinearMap.id ℝ _) x :=
          (hasFDerivAt_id x).congr_of_eventuallyEq hev
        have h3 := h1.unique h2
        intro h
        exact DFunLike.congr_fun h3 h
      intro h h' e
      have h1 := hDinj _ (hcsmall x hx) e
      rw [← hinv h, ← hinv h']
      exact congrArg ρ h1
  have hgcd : ∀ Z ∈ 𝒲, ContDiffOn ℝ 2 (fun x => F (identityChartPoint (c x Z))) O := by
    intro Z hZ x hx
    have h1 : AnalyticAt ℝ (fnInExpChart F) ((fun x => c x Z) x) :=
      hc.analyticOnNhd_fun _ (hc.chart_mem_nhd x hx Z hZ)
    have h2 : AnalyticAt ℝ (fun x => fnInExpChart F (c x Z)) x :=
      AnalyticAt.comp (f := fun x => c x Z) (x := x) h1 (hczan Z hZ x hx)
    exact h2.contDiffAt.contDiffWithinAt
  have hfzero : formValues (0 : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = 0 := by
    funext e'
    have h0 : restrictToPositiveEdges (0 : Edge L n k (i + 1) → Matrices.ComplexMatrix2) e' ∈
        Matrices.ComplexMatrix2.hermitianTraceless :=
      Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
    unfold formValues toLieFamily
    exact (dif_pos h0).trans rfl
  have hfirst : ∀ B ∈ edgeFormSpace L n k (i + 1),
      leftDifferential p (trivialField L n k (i + 1)) B =
        ofValues (fderiv ℝ s 0 (formValues B)) :=
    hMfirst hs0 (hsan 0 hc.zero_mem_values).differentiableAt
  refine ⟨𝒰, ε, p,
    { isOpenNhd := ⟨h𝒰open, h𝒰one⟩
      radius_pos := hε
      ball_subset := hεs
      ball_mem_nhds := hballm ε hε
      analytic_section := ?_
      section_trivial := ?_
      smoothing_section := hnear.mono fun W h => hsec W h.1 h.2
      fibre_structure := ?_
      unique_critical := ?_
      isMin_fibre := ?_
      deriv_section := ?_
      deriv_orthogonal := ?_ }⟩
  · exact ⟨identityChartPoint '' (𝒲 ∩ lieBall (PositiveEdge L n k (i + 1)) (1 / 2)),
      ⟨hEo' _ hAopen inter_subset_right, ⟨0, ⟨hc.zero_mem_values, hS0'⟩, hE0'⟩⟩,
      hMan _ hAopen inter_subset_right (hsan.mono inter_subset_left)
        fun Z hZ => h𝒩S (hsmem Z hZ.1)⟩
  · change identityChartPoint (s (identityChartLog (trivialField L n k (i + 1)))) = _
    rw [hlog1, hs0, hE0]
  · refine Eventually.of_forall fun W => ?_
    have hA := hTA 𝒩 hc.isOpen_nhd h𝒩T
    have h := hFib L n k i (i + 1) hL hn hik hik' 𝒰 (smoothingStep L n k i) hA.1 hA.2 W
    exact ⟨h.1, fun V hV B => h.2 V hV.1 hV.2 B⟩
  · refine (hnear.and hpball).mono ?_
    rintro W ⟨⟨hZ, hW⟩, hb⟩
    have hR := hread W hZ hW
    have hRd := hRead _ _ _ _ _ _ _ _ _ F hR (hgcd _ hZ)
    have hbm := hc.min_mem _ hZ
    have hcrit0 : fderiv ℝ (fun x => F (identityChartPoint (c x (identityChartLog W))))
        (b (identityChartLog W)) = 0 :=
      hc.fderiv_min_eq_zero _ hZ
    have hcrit := (hRd _ hbm).1.mpr hcrit0
    refine ⟨⟨hb, hcrit, ?_⟩, (hRd _ hbm).2 hcrit0
      fun h hne => hc.hessian_pos_params _ hZ _ hbm h hne⟩
    intro V _ hV
    have hVN : V ∈ CriticalBranchData.levelFibre 𝒰 W := hV.1
    have hx := hR.coord_mem V hVN
    have hVp : identityChartPoint (c (ρ (identityChartLog V)) (identityChartLog W)) = V :=
      hR.param_coord V hVN
    have hc1 : (fieldCurveData L n k i).IsCriticalOn (CriticalBranchData.levelFibre 𝒰 W) F
        (identityChartPoint (c (ρ (identityChartLog V)) (identityChartLog W))) := by
      rw [hVp]
      exact hV
    have h2 := hc.eq_min_of_critical _ hZ _ hx ((hRd _ hx).1.mp hc1)
    rw [← hVp, h2]
    rfl
  · refine hnear.mono ?_
    rintro W ⟨hZ, hW⟩ V hV hne
    have hR := hread W hZ hW
    have hx := hR.coord_mem V hV
    have hVp : identityChartPoint (c (ρ (identityChartLog V)) (identityChartLog W)) = V :=
      hR.param_coord V hV
    have hxne : ρ (identityChartLog V) ≠ b (identityChartLog W) := by
      intro e
      apply hne
      rw [← hVp, e]
      rfl
    have h1 := hc.min_lt _ hZ _ hx hxne
    have h2 : F (identityChartPoint (c (b (identityChartLog W)) (identityChartLog W))) <
        F (identityChartPoint (c (ρ (identityChartLog V)) (identityChartLog W))) := h1
    rw [hVp] at h2
    exact h2
  · intro B hB
    rw [hfirst B hB]
    refine ⟨(hfam _).1, ?_⟩
    have h1 := hc.fderiv_section (formValues B)
    rw [hdm] at h1
    have h2 := congrArg ofValues h1
    rwa [hfam2' _ (hQ _ (hfam _).1), hfam2' B hB] at h2
  · intro B hB ξ hξ hQξ
    rw [hfirst B hB]
    have hk : formValues ξ ∈ tangentKernel (smoothingInExpChart L n k i) := by
      rw [LinearMap.mem_ker]
      change fderiv ℝ (smoothingInExpChart L n k i) 0 (formValues ξ) = 0
      rw [hdm, hfam' ξ hξ, hQξ, hfzero]
    have h1 := hc.hessian_orthogonal (formValues B) ⟨_, hk⟩
    change fderiv ℝ (fderiv ℝ (fnInExpChart F)) 0 _ (formValues ξ) = 0 at h1
    rw [hdf, hfam' ξ hξ] at h1
    exact h1
end YangMills.Construction.Tower
end
