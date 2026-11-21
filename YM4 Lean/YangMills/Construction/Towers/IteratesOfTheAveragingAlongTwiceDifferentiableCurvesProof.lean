import YangMills.Construction.Matrices.CompositesOfDifferentiableMapsOnPowersOfGProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.IteratesOfTheAveragingAlongTwiceDifferentiableCurves
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiableProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace CurveSmoothing
variable {L n k j : ℕ}
private theorem fieldOfPositiveValues_restrict {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem finrank_traceless : Module.finrank ℂ Matrices.ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem positiveEdge_nonempty (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem exists_lieElement_retraction :
    ∃ P : Matrices.ComplexMatrix2 →L[ℝ] Matrices.ComplexMatrix2.LieElement,
      ∀ Y : Matrices.ComplexMatrix2.LieElement, P Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
private theorem contDiffAt_two_comp_curve {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {G : E → E'} {h : ℝ → E} {t₀ : ℝ}
    (hG : ContDiffAt ℝ 2 G (h t₀)) (h1 : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ h t)
    (h2 : DifferentiableAt ℝ (deriv h) t₀) :
    (∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ (G ∘ h) t) ∧
      DifferentiableAt ℝ (deriv (G ∘ h)) t₀ := by
  have hc : ContinuousAt h t₀ := h1.self_of_nhds.continuousAt
  have hGd : ∀ᶠ x in 𝓝 (h t₀), DifferentiableAt ℝ G x :=
    (hG.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hev : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ G (h t) := hc.eventually hGd
  refine ⟨(hev.and h1).mono fun t ht => ht.1.comp t ht.2, ?_⟩
  have hderiv : deriv (G ∘ h) =ᶠ[𝓝 t₀] fun t => fderiv ℝ G (h t) (deriv h t) :=
    (hev.and h1).mono fun t ht => (ht.1.hasFDerivAt.comp_hasDerivAt t ht.2.hasDerivAt).deriv
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hderiv
  have hfd : DifferentiableAt ℝ (fderiv ℝ G) (h t₀) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : DifferentiableAt ℝ (fun t => fderiv ℝ G (h t)) t₀ :=
    hfd.comp t₀ h1.self_of_nhds
  exact hcomp.clm_apply h2
private theorem exists_isOpen_values {𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    ∃ O : Set (PositiveEdge L n k j → Matrices.ComplexMatrix2), IsOpen O ∧
      ∀ V ∈ fieldSpace L n k j, V ∈ 𝒰 ↔ restrictToPositiveEdges V ∈ O := by apply _root_.YangMills.SharedProofs.p1531 <;> assumption
private theorem eventually_mem_of_isOpenNhdOfOne
    {𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k j] trivialField L n k j, V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.eventually_mem_of_isOpenNhdOfOne <;> assumption
private theorem exists_subinterval_mapsTo {𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) {I : Set ℝ}
    {γ : ℝ → Edge L n k j → Matrices.ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) (h0 : γ 0 ∈ 𝒰) :
    ∃ J : Set ℝ, IsOpenIntervalAroundZero J ∧ J ⊆ I ∧ MapsTo γ J 𝒰 := by
  obtain ⟨O, hO, hOU⟩ := exists_isOpen_values h
  obtain ⟨hI, hmaps, hd⟩ := hγ
  have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  have hc : ContinuousAt (fun t => restrictToPositiveEdges (γ t)) 0 :=
    continuousAt_pi.2 fun b => (hd b.1 b.2 0 hI.2.2).differentiableAt hI0 |>.continuousAt
  have hO0 : restrictToPositiveEdges (γ 0) ∈ O := (hOU _ (h.1 h0)).mp h0
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), restrictToPositiveEdges (γ t) ∈ O :=
    hc.eventually (hO.mem_nhds hO0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hI0 hev)
  refine ⟨Metric.ball 0 ε, ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hε⟩,
    fun t ht => (hball ht).1, fun t ht => ?_⟩
  · rw [Real.ball_eq_Ioo]
    exact ordConnected_Ioo
  · exact (hOU _ (hmaps (hball ht).1)).mpr (hball ht).2
private theorem analytic_comp_twiceDiffCurve {a b : ℕ} (hC : Matrices.PowerExpCharts.ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k) {𝒰 : Set (Edge L n k a → Matrices.ComplexMatrix2)}
    {m : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒰 m)
    {I : Set ℝ} {γ : ℝ → Edge L n k a → Matrices.ComplexMatrix2}
    (hγ : (fieldCurveData L n k a).IsTwiceDiffCurve I γ) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hV : γ t₀ ∈ 𝒰) (e : Edge L n k b) (he : e.IsPositivelyOriented) :
    DifferentiableAt ℝ (fun t => m (γ t) e) t₀ ∧
      DifferentiableAt ℝ (deriv fun t => m (γ t) e) t₀ := by
  obtain ⟨hopen, hmaps', f₁, f₂, hra⟩ := hm
  let := f₁
  let := f₂
  have := positiveEdge_nonempty hE hL hn ha
  have := positiveEdge_nonempty hE hL hn hb
  let β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ Matrices.ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, -, -, -, -, -, -, hread⟩ := hC (PositiveEdge L n k a) (PositiveEdge L n k b)
  have hO : Matrices.specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  let f : (PositiveEdge L n k a → Matrices.ComplexMatrix2) →
      PositiveEdge L n k b → Matrices.ComplexMatrix2 :=
    fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))
  have hinto : MapsTo f (restrictToPositiveEdges '' 𝒰)
      (Matrices.specialUnitaryPower (PositiveEdge L n k b)) := by
    rintro _ ⟨U, hU, rfl⟩
    show restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈ _
    rw [hconf hU]
    exact fun c => (hmaps' hU).1 c (mem_univ _)
  have hrest : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct β) asGroupFactors
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k a ⊕ Empty → Matrices.ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2.2.2 _ hq
    refine ⟨𝒳, Ψ, hp𝒳, hΨ β, ?_⟩
    rintro _ ⟨V, hV', rfl⟩ hx
    refine heq ⟨hx, ?_, ?_⟩
    · exact (Submodule.mem_bot ℝ).2 (funext fun e => e.elim)
    · exact fun c => (hopen.1 hV').1 c (mem_univ _)
  let p₀ : PositiveEdge L n k a → Matrices.ComplexMatrix2 := restrictToPositiveEdges (γ t₀)
  obtain ⟨N, hN, -, hsm, -⟩ :=
    (((hread β).1 _ hO).2.2.2 f hinto hrest).1.1 p₀ ⟨_, hV, rfl⟩
  have hp₀ : p₀ ∈ Matrices.specialUnitaryPower (PositiveEdge L n k a) :=
    fun c => (hopen.1 hV).1 c (mem_univ _)
  obtain ⟨-, hform, hε⟩ := hcharts p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨P, hP⟩ := exists_lieElement_retraction
  let G₁ : (PositiveEdge L n k a → Matrices.ComplexMatrix2) →
      PositiveEdge L n k a → Matrices.ComplexMatrix2.LieElement :=
    fun X s => P (logChart p₀ X s)
  have hz : (0 : Matrices.ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0 : expChartI p₀ 0 = p₀ := by
    rw [(hform 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : PositiveEdge L n k a → Matrices.ComplexMatrix2.LieElement) ∈
      smallBall (PositiveEdge L n k a) (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  have hG₁0 : G₁ p₀ = 0 := by
    funext s
    have hl := congrFun (hleft 0 h0small) s
    rw [hchart0] at hl
    show P (logChart p₀ p₀ s) = 0
    rw [hl]
    exact hP 0
  have hG₁ : ContDiffAt ℝ 2 G₁ p₀ := by
    have hl : ContDiffAt ℝ 2 (logChart p₀) p₀ :=
      (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hp₀img))).of_le ENat.LEInfty.out
    exact contDiffAt_pi.2 fun s => P.contDiff.contDiffAt.comp p₀ (contDiffAt_pi.1 hl s)
  have hG₂ : ContDiffAt ℝ 2 (f ∘ expChartI p₀) (G₁ p₀) := by
    rw [hG₁0]
    exact (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  let c : ℝ → PositiveEdge L n k a → Matrices.ComplexMatrix2 :=
    fun t => restrictToPositiveEdges (γ t)
  have hct : c t₀ = p₀ := rfl
  obtain ⟨⟨hI, hcurve, hd⟩, hdd⟩ := hγ
  have hIt : I ∈ 𝓝 t₀ := hI.1.mem_nhds ht₀
  have hc1 : ∀ t ∈ I, DifferentiableAt ℝ c t := fun t ht =>
    differentiableAt_pi.2 fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hcd : ∀ t ∈ I, deriv c t = fun b => deriv (fun s => γ s b.1) t := fun t ht =>
    deriv_pi fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hc2 : DifferentiableAt ℝ (deriv c) t₀ := by
    have hb' : DifferentiableAt ℝ (fun t (b : PositiveEdge L n k a) =>
        deriv (fun s => γ s b.1) t) t₀ :=
      differentiableAt_pi.2 fun b => (hdd b.1 b.2 t₀ ht₀).differentiableAt hIt
    exact hb'.congr_of_eventuallyEq (Filter.eventually_of_mem hIt hcd)
  have hG : ContDiffAt ℝ 2 ((f ∘ expChartI p₀) ∘ G₁) (c t₀) := by
    rw [hct]
    exact hG₂.comp p₀ hG₁
  have hnear : (fun s => restrictToPositiveEdges (m (γ s))) =ᶠ[𝓝 t₀]
      ((f ∘ expChartI p₀) ∘ G₁) ∘ c := by
    have hp₀Ω : p₀ ∈ Ω := (himg ▸ hp₀img : p₀ ∈ Ω ∩ _).1
    have hcΩ : ∀ᶠ t in 𝓝 t₀, c t ∈ Ω :=
      (hc1 t₀ ht₀).continuousAt.eventually (hΩ.mem_nhds (by rwa [hct]))
    filter_upwards [hcΩ, hIt] with t ht htI
    have hcG : c t ∈ Matrices.specialUnitaryPower (PositiveEdge L n k a) :=
      fun b => (hcurve htI).1 b (mem_univ _)
    have hmem : c t ∈ expChartI p₀ '' smallBall (PositiveEdge L n k a) (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨ht, hcG⟩
    obtain ⟨Y, hY, hYc⟩ := hmem
    have hG₁Y : G₁ (c t) = Y := by
      funext s
      show P (logChart p₀ (c t) s) = Y s
      rw [← hYc, hleft Y hY]
      exact hP (Y s)
    show restrictToPositiveEdges (m (γ t)) = f (expChartI p₀ (G₁ (c t)))
    rw [hG₁Y, hYc]
    show restrictToPositiveEdges (m (γ t)) =
      restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges (γ t))))
    rw [fieldOfPositiveValues_restrict (hcurve htI)]
  obtain ⟨h1, h2⟩ := contDiffAt_two_comp_curve hG (Filter.eventually_of_mem hIt hc1) hc2
  have hev : ∀ᶠ t in 𝓝 t₀,
      DifferentiableAt ℝ (fun s => restrictToPositiveEdges (m (γ s))) t := by
    filter_upwards [hnear.eventuallyEq_nhds, h1] with t ht hdt
    exact hdt.congr_of_eventuallyEq ht
  have hder : DifferentiableAt ℝ (deriv fun s => restrictToPositiveEdges (m (γ s))) t₀ :=
    h2.congr_of_eventuallyEq hnear.deriv
  refine ⟨differentiableAt_pi.1 hev.self_of_nhds ⟨e, he⟩, ?_⟩
  have hmember : (deriv fun t => m (γ t) e) =ᶠ[𝓝 t₀]
      fun t => deriv (fun s => restrictToPositiveEdges (m (γ s))) t ⟨e, he⟩ := by
    filter_upwards [hev] with t ht
    exact (congrFun (deriv_pi fun b => differentiableAt_pi.1 ht b) ⟨e, he⟩).symm
  exact (differentiableAt_pi.1 hder ⟨e, he⟩).congr_of_eventuallyEq hmember
private theorem smoothingIter_zero_differentiable (hE : BondSetFields.ProductStructureHolds)
    (hComp : Matrices.specialUnitaryPower.Composition.CompositionProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    IsDifferentiableFieldMap (fieldSpace L n k 0) (smoothingIter L n k 0) := by
  obtain ⟨hfin, -, -, -, -, -, -, hread, -⟩ := ((hE L hL k 0 (Nat.zero_le k)).1 n hn).2
  have himg : Matrices.ComplexMatrix2.IsRelativelyOpen
      (Matrices.specialUnitaryPower (PositiveEdge L n k 0))
      (restrictToPositiveEdges '' fieldSpace L n k 0) :=
    (hread _ subset_rfl).1 ⟨univ, isOpen_univ, by simp⟩
  have : Finite (Edge L n k 0) := Set.finite_univ_iff.mp hfin
  have : Finite (PositiveEdge L n k 0) :=
    Finite.of_injective (fun b : PositiveEdge L n k 0 => b.1) Subtype.val_injective
  let fin : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  have := positiveEdge_nonempty (k := k) (j := 0) hE hL hn (Nat.zero_le k)
  obtain ⟨-, -, hdiff, -, -⟩ := hComp (PositiveEdge L n k 0) (PositiveEdge L n k 0)
  have hid := (hdiff id).1
  have heq : (fun w : PositiveEdge L n k 0 → Matrices.ComplexMatrix2 =>
      restrictToPositiveEdges (smoothingIter L n k 0 (fieldOfPositiveValues w))) =
      fun w t => w (id t) := by
    funext w b
    show fieldOfPositiveValues w b.1 = w b
    simp [fieldOfPositiveValues, b.2]
  have hsub : restrictToPositiveEdges '' fieldSpace L n k 0 ⊆
      Matrices.specialUnitaryPower (PositiveEdge L n k 0) := by
    rintro _ ⟨U, hU, rfl⟩
    exact fun c => hU.1 c (mem_univ _)
  refine ⟨⟨subset_rfl, himg⟩, fun U hU => hU, fin, fin, ?_⟩
  have hgoal : Matrices.specialUnitaryPower.IsDifferentiableInto
      (restrictToPositiveEdges '' fieldSpace L n k 0) (fun w t => w (id t)) :=
    ⟨⟨himg, fun c => (hid.2 c).mono fun u hu => ⟨hu.1, hsub hu.2⟩⟩, fun w hw => hsub hw⟩
  rw [heq]
  exact hgoal
end CurveSmoothing
open CurveSmoothing in
theorem smoothingIterAlongTwiceDiffCurves_holds
    (hIt : SmoothingIterAnalyticNearOne)
    (hDiff : AnalyticMapDifferentiableStatement)
    (hFacts : LeftChartFacts.HoldEverywhere)
    (hC : Matrices.PowerExpCharts.ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds)
    (hComp : Matrices.specialUnitaryPower.Composition.CompositionProperties) :
    SmoothingIterAlongTwiceDiffCurves := by
  intro L n k i hL hn hi
  obtain ⟨-, hside, -⟩ := hFacts L k 0 i i hL (Nat.zero_le k) hi hi
  obtain ⟨-, hcurves, -⟩ := hside n hn
  rcases i with _ | i
  · have hd := smoothingIter_zero_differentiable (k := k) hE hComp hL hn
    unfold EventuallyNearIdentity
    filter_upwards [self_mem_nhdsWithin] with U hU I γ hγ hγ0 _
    exact ⟨I, hγ.1.1, subset_rfl, hγ, (hcurves.1 _ _ hd U hU I γ hγ.1 hγ0).2⟩
  · obtain ⟨𝒰, h𝒰, hra, -⟩ := hIt L n k i hL hn (by omega)
    have hd := hDiff L n k 0 (i + 1) hL hn (Nat.zero_le k) hi 𝒰 _ hra
    unfold EventuallyNearIdentity
    filter_upwards [eventually_mem_of_isOpenNhdOfOne h𝒰] with U hU I γ hγ hγ0 _
    obtain ⟨J, hJ, hJI, hJ𝒰⟩ :=
      exists_subinterval_mapsTo hra.1 hγ.1 (by rw [hγ0]; exact hU)
    have hall : ∀ t ∈ J, ∀ e : Edge L n k (i + 1), e.IsPositivelyOriented → _ := fun t ht e he =>
      analytic_comp_twiceDiffCurve hC hE hL hn (Nat.zero_le k) hi hra hγ (hJI ht) (hJ𝒰 ht) e he
    exact ⟨J, hJ, hJI,
      ⟨⟨hJ, fun t ht => hra.2.1 (hJ𝒰 ht),
        fun e he t ht => (hall t ht e he).1.differentiableWithinAt⟩,
        fun e he t ht => (hall t ht e he).2.differentiableWithinAt⟩,
      (hcurves.1 _ _ hd U hU I γ hγ.1 hγ0).2⟩
end YangMills.Construction.Tower
end
