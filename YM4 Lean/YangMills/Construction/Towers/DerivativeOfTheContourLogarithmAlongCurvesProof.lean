import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurves
import YangMills.Construction.Towers.LogarithmsOfAveragedContoursAlongCurves
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace ContourLogDerivAlongCurves
open ContourLogarithms (expCurve vertexCubePairs)
private theorem exists_entrywiseAnalytic_eventuallyEq {ι : Type} [Fintype ι]
    {D : Set (ι → Matrices.ComplexMatrix2)}
    {f : (ι → Matrices.ComplexMatrix2) → Fin 1 → Matrices.ComplexMatrix2}
    (hf : Matrices.ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : ι => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => Matrices.ComplexMatrix2.FactorKind.group) D f)
    {p : ι → Matrices.ComplexMatrix2} (hp : p ∈ D) :
    ∃ Φ : (ι → Matrices.ComplexMatrix2) → Fin 1 → Matrices.ComplexMatrix2,
      AnalyticAt ℂ Φ p ∧ ∀ᶠ q in 𝓝[D] p, f q = Φ q := by
  obtain ⟨⟨O', -, hD⟩, hloc⟩ := hf
  obtain ⟨W, g, hpW, ⟨⟨O, hO, hW⟩, -, hW'⟩, hfg⟩ := hloc p hp
  obtain ⟨Φ, hΦ, hgΦ⟩ := hW' p hpW
  refine ⟨Φ, hΦ, ?_⟩
  have hpO : p ∈ O := by
    rw [hW] at hpW
    exact hpW.1
  have hsub : ∀ q ∈ D, q ∈ Matrices.ComplexMatrix2.complexifiedProduct
      fun _ : ι => Matrices.ComplexMatrix2.FactorKind.group := by
    intro q hq s
    rw [hD] at hq
    exact (Matrix.mem_specialUnitaryGroup_iff.mp (hq.2 s)).2
  rw [eventually_nhdsWithin_iff] at hgΦ
  filter_upwards [nhdsWithin_le_nhds hgΦ, self_mem_nhdsWithin, hfg,
    nhdsWithin_le_nhds (hO.mem_nhds hpO)] with q h₁ h₂ h₃ h₄
  rw [h₃, h₁]
  rw [hW]
  exact ⟨h₄, hsub q h₂⟩
abbrev _root_.YangMills.SharedProofs.p99213 := @exists_entrywiseAnalytic_eventuallyEq
private theorem differentiableAt_logSeries
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {A : Matrices.ComplexMatrix2}
    (hA : Matrices.ComplexMatrix2.operatorNorm (A - 1) < 1) :
    DifferentiableAt ℝ Matrices.ComplexMatrix2.logSeries A := by
  let e : Matrices.ComplexMatrix2 ≃L[ℂ] Coordinates.ComplexCoordinates 4 :=
    LinearEquiv.toContinuousLinearEquiv
      { Coordinates.ComplexCoordinates.matrixEquiv with
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have he : ∀ C, e C = Coordinates.ComplexCoordinates.matrixEquiv C := fun _ => rfl
  have hlg := hH.2.2.2.2.2
  have hsm := ((hH.1 4 _ hlg.1).1 4 _ hlg).2.1
  have hmem : e A ∈ Coordinates.ComplexCoordinates.matrixEquiv ''
      Matrices.ComplexMatrix2.logBall :=
    ⟨A, hA, (he A).symm⟩
  have hd : DifferentiableAt ℝ
      (Coordinates.ComplexCoordinates.matrixEquiv ∘ Matrices.ComplexMatrix2.logSeries ∘
        Coordinates.ComplexCoordinates.matrixEquiv.symm) (e A) :=
    ((hsm.contDiffAt (hlg.1.mem_nhds hmem)).differentiableAt (by simp))
  have heR : DifferentiableAt ℝ (fun C : Matrices.ComplexMatrix2 => e C) A :=
    (e.differentiableAt (x := A)).restrictScalars ℝ
  have hes : DifferentiableAt ℝ (fun w : Coordinates.ComplexCoordinates 4 => e.symm w)
      ((Coordinates.ComplexCoordinates.matrixEquiv ∘ Matrices.ComplexMatrix2.logSeries ∘
        Coordinates.ComplexCoordinates.matrixEquiv.symm) (e A)) :=
    (e.symm.differentiableAt).restrictScalars ℝ
  have hall := hes.comp A (hd.comp A heR)
  refine hall.congr_of_eventuallyEq (Eventually.of_forall fun C => ?_)
  have h₁ : Coordinates.ComplexCoordinates.matrixEquiv.symm (e C) = C := by simp [he]
  have h₂ : ∀ Z, e.symm (Coordinates.ComplexCoordinates.matrixEquiv Z) = Z :=
    fun Z => by simp [← he]
  simp [Function.comp, h₁, h₂]
abbrev _root_.YangMills.SharedProofs.p25178 := @differentiableAt_logSeries
private theorem inv_I_smul_logSeries_mem (hExp : Matrices.ComplexMatrix2.ExpLogEstimates)
    {A : Matrices.ComplexMatrix2} (hA : A ∈ PeriodicLattice.compactGaugeGroup)
    (hs : Matrices.ComplexMatrix2.operatorNorm (A - 1) < 1) :
    Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries A ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  obtain ⟨H, -, hlg, -, -, -, hrest⟩ := hExp.2.2.2.2.2.2.2.1 A hu hs
  obtain ⟨-, hH, -⟩ := hrest hdet
  rw [hlg, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  exact hH
abbrev _root_.YangMills.SharedProofs.p12580 := @inv_I_smul_logSeries_mem
private theorem hasDerivAt_mem_of_eventually {f : ℝ → Matrices.ComplexMatrix2}
    {d : Matrices.ComplexMatrix2} (hf : HasDerivAt f d 0)
    (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    d ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  have hcl : IsClosed (Matrices.ComplexMatrix2.hermitianTraceless :
      Set Matrices.ComplexMatrix2) := Submodule.closed_of_finiteDimensional _
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hf
  refine hcl.mem_of_tendsto hslope ?_
  have hshift : ∀ᶠ t in 𝓝 (0 : ℝ), f (0 + t) ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
    simpa using hmem
  filter_upwards [nhdsWithin_le_nhds hshift] with t ht
  exact Matrices.ComplexMatrix2.hermitianTraceless.smul_mem _
    (Matrices.ComplexMatrix2.hermitianTraceless.sub_mem ht hmem.self_of_nhds)
abbrev _root_.YangMills.SharedProofs.p35912 := @hasDerivAt_mem_of_eventually
variable {L n k i : ℕ}
private theorem isPositivelyOriented_or_opposite (e : Edge L n k i) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem fieldOfPositiveValues_restrict {U : Edge L n k i → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k i) : fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem exists_isOpen_restrict_iff {𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    ∃ O : Set (PositiveEdge L n k i → Matrices.ComplexMatrix2), IsOpen O ∧
      ∀ U ∈ fieldSpace L n k i, U ∈ 𝒰 ↔ restrictToPositiveEdges U ∈ O := by
  obtain ⟨hsub, O, hO, himg⟩ := h
  refine ⟨O, hO, fun U hU => ⟨fun hU𝒰 => ?_, fun hUO => ?_⟩⟩
  · have : restrictToPositiveEdges U ∈ restrictToPositiveEdges '' 𝒰 := mem_image_of_mem _ hU𝒰
    rw [himg] at this
    exact this.1
  · have hmem : restrictToPositiveEdges U ∈ restrictToPositiveEdges '' 𝒰 := by
      rw [himg]
      exact ⟨hUO, fun e => hU.1 _ (mem_univ _)⟩
    obtain ⟨U', hU', he⟩ := hmem
    have : U' = U := by
      rw [← fieldOfPositiveValues_restrict (hsub hU'), he, fieldOfPositiveValues_restrict hU]
    exact this ▸ hU'
abbrev _root_.YangMills.SharedProofs.p1531 := @exists_isOpen_restrict_iff
private theorem continuous_restrictToPositiveEdges :
    Continuous (restrictToPositiveEdges :
      (Edge L n k i → Matrices.ComplexMatrix2) → PositiveEdge L n k i → Matrices.ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
private theorem expCurve_eq_expTwist (U B : Edge L n k i → Matrices.ComplexMatrix2) (t : ℝ) :
    expCurve U B t = PeriodicLattice.expTwist (t • B) U := by
  have : ((t : ℂ) • B) = t • B := by
    funext e
    ext r s
    simp
  rw [expCurve, this]
abbrev _root_.YangMills.SharedProofs.p66923 := @expCurve_eq_expTwist
private theorem expCurve_zero {U : Edge L n k i → Matrices.ComplexMatrix2}
    (B : Edge L n k i → Matrices.ComplexMatrix2)
    (hU : U ∈ fieldSpace L n k i) : expCurve U B 0 = U := by
  funext e
  have hoo : e.opposite.opposite = e := PeriodicLattice.Bond.ext rfl rfl
  have hexp : Matrices.ComplexMatrix2.matExp (0 : Matrices.ComplexMatrix2) = 1 := by
    simp [Matrices.ComplexMatrix2.matExp]
  by_cases h : e.IsPositivelyOriented
  · simp [expCurve, PeriodicLattice.expTwist, h]
  · have hinv := hU.2 e.opposite (mem_univ _)
    simp only [expCurve, PeriodicLattice.expTwist, if_neg h]
    simp only [Complex.ofReal_zero, zero_smul, Pi.zero_apply, smul_zero, hexp, one_mul]
    rw [← hinv, hoo]
abbrev _root_.YangMills.DeltaSharedProofs.p500778 := @expCurve_zero
abbrev _root_.YangMills.SharedProofs.p30759 := @expCurve_zero
private theorem meanContourHolonomy_mem {W : Edge L n k i → Matrices.ComplexMatrix2}
    {y : Vertex L n k (i + 1)} {x : Vertex L n k i}
    (h : PeriodicLattice.HasContourMean W y x) :
    PeriodicLattice.meanContourHolonomy W y x ∈ PeriodicLattice.compactGaugeGroup :=
  (Classical.epsilon_spec (p := Matrices.ComplexMatrix2.IsLogMean
    PeriodicLattice.compactGaugeGroup (PeriodicLattice.contourHolonomies W y x)) h.exists).1
abbrev _root_.YangMills.SharedProofs.p41932 := @meanContourHolonomy_mem
private theorem hasDerivAt_logSeries_comp [Fintype (PositiveEdge L n k i)]
    {𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2)}
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {F : (Edge L n k i → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    {Φ : (PositiveEdge L n k i → Matrices.ComplexMatrix2) → Fin 1 → Matrices.ComplexMatrix2}
    {U : Edge L n k i → Matrices.ComplexMatrix2} (hU : U ∈ 𝒰)
    (hFΦ : ∀ᶠ y in 𝓝[restrictToPositiveEdges '' 𝒰] restrictToPositiveEdges U,
      (fun _ : Fin 1 => F (fieldOfPositiveValues y)) = Φ y)
    (hdg : DifferentiableAt ℝ (fun y => Matrices.ComplexMatrix2.logSeries (Φ y 0))
      (restrictToPositiveEdges U))
    {η : ℝ → Edge L n k i → Matrices.ComplexMatrix2}
    {D : PositiveEdge L n k i → Matrices.ComplexMatrix2}
    (hfield : ∀ᶠ t in 𝓝 (0 : ℝ), η t ∈ fieldSpace L n k i)
    (hd : HasDerivAt (fun t => restrictToPositiveEdges (η t)) D 0) (h0 : η 0 = U) :
    HasDerivAt (fun t => Matrices.ComplexMatrix2.logSeries (F (η t)))
      (fderiv ℝ (fun y => Matrices.ComplexMatrix2.logSeries (Φ y 0))
        (restrictToPositiveEdges U) D) 0 := by
  obtain ⟨O, hO, hO𝒰⟩ := exists_isOpen_restrict_iff hopen
  have hr0 : restrictToPositiveEdges (η 0) = restrictToPositiveEdges U := by rw [h0]
  have hUfield : U ∈ fieldSpace L n k i := hopen.1 hU
  have hrO : ∀ᶠ t : ℝ in 𝓝 0, restrictToPositiveEdges (η t) ∈ O := by
    refine hd.continuousAt.eventually_mem (hO.mem_nhds ?_)
    rw [hr0]
    exact (hO𝒰 U hUfield).mp hU
  have h𝒰 : ∀ᶠ t : ℝ in 𝓝 0, η t ∈ 𝒰 := by
    filter_upwards [hrO, hfield] with t ht hc
    exact (hO𝒰 _ hc).mpr ht
  have htend : Tendsto (fun t => restrictToPositiveEdges (η t)) (𝓝 0)
      (𝓝[restrictToPositiveEdges '' 𝒰] restrictToPositiveEdges U) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hd.continuousAt.tendsto
      rwa [hr0] at this
    · filter_upwards [h𝒰] with t ht
      exact mem_image_of_mem _ ht
  have hcomp : HasDerivAt
      (fun t => Matrices.ComplexMatrix2.logSeries (Φ (restrictToPositiveEdges (η t)) 0))
      (fderiv ℝ (fun y => Matrices.ComplexMatrix2.logSeries (Φ y 0))
        (restrictToPositiveEdges U) D) 0 := by
    have hfd := hdg.hasFDerivAt
    rw [← hr0] at hfd
    have := hfd.comp_hasDerivAt (0 : ℝ) hd
    rw [hr0] at this
    exact this
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [htend.eventually hFΦ, hfield] with t ht hc
  have h₁ := congrFun ht 0
  simp only [fieldOfPositiveValues_restrict hc] at h₁
  rw [h₁]
abbrev _root_.YangMills.SharedProofs.p678 := @hasDerivAt_logSeries_comp
private theorem curveTangent_eq {U B : Edge L n k i → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k i) (hB : B ∈ edgeFormSpace L n k i)
    {γ : ℝ → Edge L n k i → Matrices.ComplexMatrix2} (h0 : γ 0 = U)
    (hY : ∀ e : PositiveEdge L n k i, deriv (fun t => γ t e) 0 = Complex.I • B e * U e) :
    curveTangent γ = B := by
  have hpos : ∀ e : Edge L n k i, e.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => γ t e) 0 * (γ 0 e)⁻¹) = B e := by
    intro e he
    have hu : IsUnit (U e).det := by
      have := (Matrix.mem_specialUnitaryGroup_iff.mp (hU.1 e (mem_univ _))).2
      rw [this]
      exact isUnit_one
    rw [hY ⟨e, he⟩, h0]
    show Complex.I⁻¹ • (Complex.I • B e * U e * (U e)⁻¹) = B e
    rw [mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext e
  by_cases h : e.IsPositivelyOriented
  · simp only [curveTangent, extendOddly, if_pos h]
    exact hpos e h
  · have h' := (isPositivelyOriented_or_opposite e).resolve_left h
    simp only [curveTangent, extendOddly, if_neg h]
    rw [hpos _ h', hB.2 e, neg_neg]
end ContourLogDerivAlongCurves
open ContourLogarithms (expCurve vertexCubePairs) in
open ContourLogDerivAlongCurves in
theorem ContourLogDerivAlongCurves.holds
    (hG : ContourLogarithms.ContourLogDifferentiable)
    (hAvg : SmoothingNearIdentity)
    (hVal : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hBlocks : BlockStructure)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hExp : Matrices.ComplexMatrix2.ExpLogEstimates) :
    ContourLogDerivAlongCurves.Statement := by
  intro L n k i hL hn hi
  obtain ⟨-, hnear⟩ := hG L n k hL hn i hi
  obtain ⟨𝒰, h𝒰, -, hcontour⟩ := ((hAvg.1 L hL).1 n k i hn hi).1.analytic
  have hclauses := ((hChart.2.2 L k i hL hi.le).1 n hn).1
  have hcurve : ∀ U ∈ fieldSpace L n k i, ∀ B ∈ edgeFormSpace L n k i, ∀ t : ℝ,
      expCurve U B t ∈ fieldSpace L n k i := by
    intro U hU B hB t
    rw [expCurve_eq_expTwist]
    exact (hVal L n k hL hn (by omega)).2 i hi.le (t • B)
      ((edgeFormSpace L n k i).smul_mem t hB) U hU
  have hderiv : ∀ U ∈ fieldSpace L n k i, ∀ B ∈ edgeFormSpace L n k i,
      ∀ e : PositiveEdge L n k i,
      HasDerivAt (fun t : ℝ => expCurve U B t e) (Complex.I • B e * U e) 0 := by
    intro U hU B hB e
    have hd := (hclauses.1.1 U hU B hB e).2
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    have he : (e : Edge L n k i).IsPositivelyOriented := e.2
    simp [expCurve, PeriodicLattice.expTwist, he, LeftChartFields.leftExpMul,
      LeftChartFields.LatticeData.onPositive, LeftChartFields.finiteData]
  have hcentre : ∀ x : FineOnlyVertex L n k i, (cubeCentre x, x.1) ∈ vertexCubePairs L n k i := by
    intro x
    obtain ⟨-, hsort, -⟩ := (hBlocks L k (i + 1) hL (by omega) (by omega) hi).1 n hn
    obtain ⟨y, hy, -⟩ := hsort.2.2 x.1 x.2
    have hex : ∃ y : Vertex L n k (i + 1),
        x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y ∧
        (x.1 : PeriodicLattice.FourTorus L n) ≠ y := ⟨y, hy.1, hy.2⟩
    exact (Classical.epsilon_spec hex).1
  obtain ⟨O, hO, hO𝒰⟩ := exists_isOpen_restrict_iff h𝒰.1
  have hin𝒰 : ∀ᶠ U in 𝓝[fieldSpace L n k i] trivialField L n k i, U ∈ 𝒰 := by
    have hpos1 := (hO𝒰 _ (h𝒰.1.1 h𝒰.2)).mp h𝒰.2
    have hOn : ∀ᶠ U in 𝓝 (trivialField L n k i), restrictToPositiveEdges U ∈ O :=
      continuous_restrictToPositiveEdges.continuousAt.eventually_mem (hO.mem_nhds hpos1)
    filter_upwards [nhdsWithin_le_nhds hOn, self_mem_nhdsWithin] with U h₁ h₂
    exact (hO𝒰 U h₂).mpr h₁
  refine (hnear.and (hin𝒰.and self_mem_nhdsWithin)).mono ?_
  rintro U ⟨hUnear, hU𝒰, hUfield⟩ I γ hγ h0 x
  have hI : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.mem_nhds hγ.1.2.2
  have hp := hcentre x
  have hfam : (LeftChartFields.finiteData L n k i).IsCurveTangent U
      (fun e : PositiveEdge L n k i => deriv (fun t => γ t e) 0) :=
    ⟨I, γ, hγ, h0, fun e => rfl⟩
  have hform : ∃ B : Edge L n k i → Matrices.ComplexMatrix2, B ∈ edgeFormSpace L n k i ∧
      ∀ e : PositiveEdge L n k i, deriv (fun t => γ t e) 0 = Complex.I • B e * U e :=
    ((hclauses.2.1 U hUfield).1 _).mp hfam
  obtain ⟨B, hB, hYB⟩ := hform
  have htan : curveTangent γ = B := curveTangent_eq hUfield hB h0 hYB
  rw [htan]
  obtain ⟨hdef, hopen, inst, hra⟩ := hcontour (cubeCentre x) x.1 hp
  obtain ⟨hev, -⟩ := hUnear _ hp B hB
  have hz := expCurve_zero B hUfield
  have hsmall : Matrices.ComplexMatrix2.operatorNorm
      (PeriodicLattice.meanContourHolonomy U (cubeCentre x) x.1 - 1) < 1 := by
    have := hev.self_of_nhds.2
    rwa [hz] at this
  obtain ⟨Φ, hΦ, hFΦ⟩ :=
    exists_entrywiseAnalytic_eventuallyEq hra (mem_image_of_mem restrictToPositiveEdges hU𝒰)
  have hval : Φ (restrictToPositiveEdges U) 0 =
      PeriodicLattice.meanContourHolonomy U (cubeCentre x) x.1 := by
    have h₁ := hFΦ.self_of_nhdsWithin (mem_image_of_mem restrictToPositiveEdges hU𝒰)
    have h₂ := congrFun h₁ 0
    rw [← h₂]
    simp only [fieldOfPositiveValues_restrict hUfield]
  have hdg : DifferentiableAt ℝ (fun y => Matrices.ComplexMatrix2.logSeries (Φ y 0))
      (restrictToPositiveEdges U) := by
    have hlg : DifferentiableAt ℝ Matrices.ComplexMatrix2.logSeries
        (Φ (restrictToPositiveEdges U) 0) := by
      rw [hval]
      exact differentiableAt_logSeries hH hsmall
    have hΦr : DifferentiableAt ℝ (fun y => Φ y 0) (restrictToPositiveEdges U) :=
      differentiableAt_pi.mp (hΦ.differentiableAt.restrictScalars ℝ) 0
    exact DifferentiableAt.comp (g := Matrices.ComplexMatrix2.logSeries)
      (f := fun y => Φ y 0) _ hlg hΦr
  have hdγ : HasDerivAt (fun t => restrictToPositiveEdges (γ t))
      (fun e : PositiveEdge L n k i => Complex.I • B e * U e) 0 := by
    refine hasDerivAt_pi.mpr fun e => ?_
    have := ((hγ.2.2 e e.2 0 hγ.1.2.2).differentiableAt hI).hasDerivAt
    rw [hYB e] at this
    exact this
  have hdc : HasDerivAt (fun t => restrictToPositiveEdges (expCurve U B t))
      (fun e : PositiveEdge L n k i => Complex.I • B e * U e) 0 :=
    hasDerivAt_pi.mpr (hderiv U hUfield B hB)
  have hfieldγ : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ fieldSpace L n k i := by
    filter_upwards [hI] with t ht
    exact hγ.2.1 ht
  have hAγ := hasDerivAt_logSeries_comp
    (F := fun W => PeriodicLattice.meanContourHolonomy W (cubeCentre x) x.1) hopen hU𝒰
    hFΦ hdg hfieldγ hdγ h0
  have hAc := hasDerivAt_logSeries_comp
    (F := fun W => PeriodicLattice.meanContourHolonomy W (cubeCentre x) x.1) hopen hU𝒰
    hFΦ hdg (Eventually.of_forall (hcurve U hUfield B hB)) hdc hz
  have hvalue : contourLogDeriv L n k i U B x =
      Complex.I⁻¹ • fderiv ℝ (fun y => Matrices.ComplexMatrix2.logSeries (Φ y 0))
        (restrictToPositiveEdges U)
        (fun e : PositiveEdge L n k i => Complex.I • B e * U e) := by
    have := hAc.deriv
    simp only [contourLogDeriv]
    rw [← this]
    rfl
  rw [hvalue]
  refine ⟨hAγ.const_smul Complex.I⁻¹,
    hasDerivAt_mem_of_eventually (hAc.const_smul Complex.I⁻¹) ?_⟩
  filter_upwards [hev] with t ht
  exact inv_I_smul_logSeries_mem hExp (meanContourHolonomy_mem ht.1) ht.2
end YangMills.Construction.Tower
end
