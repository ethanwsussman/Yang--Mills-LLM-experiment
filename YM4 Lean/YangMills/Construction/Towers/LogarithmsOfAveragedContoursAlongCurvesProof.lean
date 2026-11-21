import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurvesProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
namespace ContourLogarithms
private theorem exists_analyticAt_eventuallyEq {ι : Type} [Fintype ι] {D : Set (ι → ComplexMatrix2)}
    {f : (ι → ComplexMatrix2) → Fin 1 → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D f) {x : ι → ComplexMatrix2} (hx : x ∈ D) :
    ∃ Φ : (ι → ComplexMatrix2) → Fin 1 → ComplexMatrix2, AnalyticAt ℂ Φ x ∧ ∀ᶠ y in 𝓝[D] x, f y = Φ y := by apply _root_.YangMills.SharedProofs.p99213 <;> assumption
private theorem differentiableAt_logSeries
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {X : ComplexMatrix2}
    (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) : DifferentiableAt ℝ ComplexMatrix2.logSeries X := by apply _root_.YangMills.SharedProofs.p25178 <;> assumption
variable {L n k i : ℕ}
private theorem fieldOfPositiveValues_restrict {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem exists_isOpen_values {U : Set (Edge L n k i → ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U) :
    ∃ O : Set (PositiveEdge L n k i → ComplexMatrix2), IsOpen O ∧
      ∀ V ∈ fieldSpace L n k i, V ∈ U ↔ restrictToPositiveEdges V ∈ O := by apply _root_.YangMills.SharedProofs.p1531 <;> assumption
private theorem continuous_restrictToPositiveEdges :
    Continuous (restrictToPositiveEdges :
      (Edge L n k i → ComplexMatrix2) → PositiveEdge L n k i → ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
private theorem meanContourHolonomy_trivialField (y : Vertex L n k (i + 1)) (x : Vertex L n k i)
    (h : PeriodicLattice.HasContourMean (trivialField L n k i) y x) :
    PeriodicLattice.meanContourHolonomy (trivialField L n k i) y x = 1 := by
  have hone : ∀ s, PeriodicLattice.contourHolonomies (trivialField L n k i) y x s = 1 := by
    intro s
    simp [PeriodicLattice.contourHolonomies, PeriodicLattice.pathHolonomy]
  have hlog : ComplexMatrix2.logSeries 1 = 0 := by simp [ComplexMatrix2.logSeries]
  have hmean : ComplexMatrix2.IsLogMean PeriodicLattice.compactGaugeGroup
      (PeriodicLattice.contourHolonomies (trivialField L n k i) y x) 1 := by
    refine ⟨one_mem _, fun s => ?_, ?_⟩
    · simp [hone]
    · simp [hone, hlog]
  have hav : ComplexMatrix2.IsLogMean PeriodicLattice.compactGaugeGroup
      (PeriodicLattice.contourHolonomies (trivialField L n k i) y x)
      (PeriodicLattice.meanContourHolonomy (trivialField L n k i) y x) :=
    Classical.epsilon_spec (p := ComplexMatrix2.IsLogMean PeriodicLattice.compactGaugeGroup _) ⟨1, hmean⟩
  exact h.unique hav hmean
private theorem expCurve_eq_expTwist_real (V B : Edge L n k i → ComplexMatrix2) (t : ℝ) :
    expCurve V B t = PeriodicLattice.expTwist (t • B) V := by apply _root_.YangMills.SharedProofs.p66923 <;> assumption
private theorem expCurve_zero {V : Edge L n k i → ComplexMatrix2} (B : Edge L n k i → ComplexMatrix2)
    (hV : V ∈ fieldSpace L n k i) : expCurve V B 0 = V := by apply _root_.YangMills.SharedProofs.p30759 <;> assumption
private theorem eventually_mem_and_differentiableAt [Fintype (PositiveEdge L n k i)]
    {U : Set (Edge L n k i → ComplexMatrix2)} (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U)
    {F : (Edge L n k i → ComplexMatrix2) → ComplexMatrix2}
    (hF : ComplexMatrix2.IsRealAnalyticBetween (fun _ : PositiveEdge L n k i => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' U)
      fun v _ => F (fieldOfPositiveValues v))
    {V B : Edge L n k i → ComplexMatrix2} (hV : V ∈ U)
    (hfield : ∀ t : ℝ, expCurve V B t ∈ fieldSpace L n k i)
    (hderiv : ∀ b : PositiveEdge L n k i, HasDerivAt (fun t : ℝ => expCurve V B t b)
      (Complex.I • B b * V b) 0) (hzero : expCurve V B 0 = V) :
    (∀ᶠ t : ℝ in 𝓝 0, expCurve V B t ∈ U) ∧
      DifferentiableAt ℝ (fun t : ℝ => F (expCurve V B t)) 0 := by
  obtain ⟨O, hO, hOU⟩ := exists_isOpen_values hopen
  set γ : ℝ → PositiveEdge L n k i → ComplexMatrix2 :=
    fun t => restrictToPositiveEdges (expCurve V B t) with hγ
  have hγd : HasDerivAt γ (fun b => Complex.I • B b * V b) 0 := hasDerivAt_pi.mpr hderiv
  have hγ0 : γ 0 = restrictToPositiveEdges V := by simp only [hγ, hzero]
  have hVfield : V ∈ fieldSpace L n k i := hzero ▸ hfield 0
  have hγO : ∀ᶠ t : ℝ in 𝓝 0, γ t ∈ O := by
    refine hγd.continuousAt.eventually_mem (hO.mem_nhds ?_)
    rw [hγ0]
    exact (hOU V hVfield).mp hV
  have hU : ∀ᶠ t : ℝ in 𝓝 0, expCurve V B t ∈ U := by
    filter_upwards [hγO] with t ht
    exact (hOU _ (hfield t)).mpr ht
  refine ⟨hU, ?_⟩
  obtain ⟨Φ, hΦ, hFΦ⟩ := exists_analyticAt_eventuallyEq hF (mem_image_of_mem restrictToPositiveEdges hV)
  have htend : Tendsto γ (𝓝 0) (𝓝[restrictToPositiveEdges '' U] restrictToPositiveEdges V) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hγd.continuousAt.tendsto
      rwa [hγ0] at this
    · filter_upwards [hU] with t ht
      exact mem_image_of_mem _ ht
  have hcomp : DifferentiableAt ℝ (fun t => Φ (γ t)) 0 := by
    have hΦd : DifferentiableAt ℝ Φ (γ 0) := by
      rw [hγ0]
      exact hΦ.differentiableAt.restrictScalars ℝ
    exact hΦd.comp (0 : ℝ) hγd.differentiableAt
  have hfirst : DifferentiableAt ℝ (fun t => Φ (γ t) 0) 0 := differentiableAt_pi.mp hcomp 0
  refine hfirst.congr_of_eventuallyEq ?_
  filter_upwards [htend.eventually hFΦ] with t ht
  have := congrFun ht 0
  simpa [hγ, fieldOfPositiveValues_restrict (hfield t)] using this
private theorem eventually_operatorNorm_sub_one_lt [Fintype (PositiveEdge L n k i)]
    {U : Set (Edge L n k i → ComplexMatrix2)} (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U)
    {F : (Edge L n k i → ComplexMatrix2) → ComplexMatrix2}
    (hF : ComplexMatrix2.IsRealAnalyticBetween (fun _ : PositiveEdge L n k i => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' U)
      fun v _ => F (fieldOfPositiveValues v))
    (hone : trivialField L n k i ∈ U) (hF1 : F (trivialField L n k i) = 1) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i,
      ComplexMatrix2.operatorNorm (F V - 1) < 1 := by
  obtain ⟨O, hO, hOU⟩ := exists_isOpen_values hopen
  have hfield1 := hopen.1 hone
  have hpos1 : restrictToPositiveEdges (trivialField L n k i) ∈ O := (hOU _ hfield1).mp hone
  have hinU : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ U := by
    have hOn : ∀ᶠ V in 𝓝 (trivialField L n k i), restrictToPositiveEdges V ∈ O :=
      continuous_restrictToPositiveEdges.continuousAt.eventually_mem (hO.mem_nhds hpos1)
    filter_upwards [nhdsWithin_le_nhds hOn, self_mem_nhdsWithin] with V h₁ h₂
    exact (hOU V h₂).mpr h₁
  obtain ⟨Φ, hΦ, hFΦ⟩ := exists_analyticAt_eventuallyEq hF (mem_image_of_mem restrictToPositiveEdges hone)
  have htend : Tendsto restrictToPositiveEdges
      (𝓝[fieldSpace L n k i] trivialField L n k i)
      (𝓝[restrictToPositiveEdges '' U] restrictToPositiveEdges (trivialField L n k i)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_restrictToPositiveEdges.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [hinU] with V hV
      exact mem_image_of_mem _ hV
  have hval : Φ (restrictToPositiveEdges (trivialField L n k i)) 0 = 1 := by
    have h₁ := hFΦ.self_of_nhdsWithin (mem_image_of_mem restrictToPositiveEdges hone)
    have h₂ := congrFun h₁ 0
    rw [← h₂, fieldOfPositiveValues_restrict hfield1, hF1]
  have hcont : ContinuousAt (fun V : Edge L n k i → ComplexMatrix2 => Φ (restrictToPositiveEdges V) 0)
      (trivialField L n k i) :=
    (continuous_apply (0 : Fin 1)).continuousAt.comp
      (hΦ.continuousAt.comp continuous_restrictToPositiveEdges.continuousAt)
  have hsmall : ∀ᶠ V in 𝓝 (trivialField L n k i),
      ComplexMatrix2.operatorNorm (Φ (restrictToPositiveEdges V) 0 - 1) < 1 := by
    have h₁ : ContinuousAt
        (fun V : Edge L n k i → ComplexMatrix2 => ‖Φ (restrictToPositiveEdges V) 0 - 1‖)
        (trivialField L n k i) := (hcont.sub continuousAt_const).norm
    exact h₁.tendsto.eventually_lt_const (by simp [hval])
  filter_upwards [nhdsWithin_le_nhds hsmall, htend.eventually hFΦ, self_mem_nhdsWithin]
    with V h₁ h₂ h₃
  have h₄ := congrFun h₂ 0
  simp only [fieldOfPositiveValues_restrict h₃] at h₄
  rw [h₄]
  exact h₁
theorem contourLogDifferentiable_holds
    (hAvg : SmoothingNearIdentity)
    (hVal : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ContourLogDifferentiable := by
  intro L n k hL hn i hi
  have hfinVertices : ∀ r, r ≤ k → Finite (Vertex L n k r) := by
    intro r hr
    obtain ⟨-, hq, -⟩ := hLat L hL n r k hn hr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfin, -, -⟩ := hq
    exact hfin
  have hfinPairs : (vertexCubePairs L n k i).Finite := by
    have := hfinVertices (i + 1) hi
    have := hfinVertices i hi.le
    exact Set.toFinite _
  refine ⟨hfinPairs, ?_⟩
  obtain ⟨U, hU, -, hcontour⟩ := ((hAvg.1 L hL).1 n k i hn hi).1.analytic
  have hcurve : ∀ V ∈ fieldSpace L n k i, ∀ B ∈ edgeFormSpace L n k i, ∀ t : ℝ,
      expCurve V B t ∈ fieldSpace L n k i := by
    intro V hV B hB t
    rw [expCurve_eq_expTwist_real]
    exact (hVal L n k hL hn (by omega)).2 i hi.le (t • B) ((edgeFormSpace L n k i).smul_mem t hB) V hV
  have hclauses := ((hChart.2.2 L k i hL hi.le).1 n hn).1
  have hderiv : ∀ V ∈ fieldSpace L n k i, ∀ B ∈ edgeFormSpace L n k i, ∀ b : PositiveEdge L n k i,
      HasDerivAt (fun t : ℝ => expCurve V B t b) (Complex.I • B b * V b) 0 := by
    intro V hV B hB b
    have hd := (hclauses.1.1 V hV B hB b).2
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    have hb : (b : Edge L n k i).IsPositivelyOriented := b.2
    simp [expCurve, PeriodicLattice.expTwist, hb, LeftChartFields.leftExpMul,
      LeftChartFields.LatticeData.onPositive, LeftChartFields.finiteData]
  have hsmall : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i,
      ∀ p ∈ vertexCubePairs L n k i,
        ComplexMatrix2.operatorNorm (PeriodicLattice.meanContourHolonomy V p.1 p.2 - 1) < 1 := by
    refine (eventually_all_finite hfinPairs).mpr fun p hp => ?_
    obtain ⟨hdef, hopen, inst, hra⟩ := hcontour p.1 p.2 hp
    exact eventually_operatorNorm_sub_one_lt
      (F := fun W => PeriodicLattice.meanContourHolonomy W p.1 p.2) hopen hra hU.2
      (meanContourHolonomy_trivialField p.1 p.2 (hdef _ hU.2))
  obtain ⟨O, hO, hOU⟩ := exists_isOpen_values hU.1
  have hinU : ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ U := by
    have hpos1 := (hOU _ (hU.1.1 hU.2)).mp hU.2
    have hOn : ∀ᶠ V in 𝓝 (trivialField L n k i), restrictToPositiveEdges V ∈ O :=
      continuous_restrictToPositiveEdges.continuousAt.eventually_mem (hO.mem_nhds hpos1)
    filter_upwards [nhdsWithin_le_nhds hOn, self_mem_nhdsWithin] with V h₁ h₂
    exact (hOU V h₂).mpr h₁
  refine (hsmall.and (hinU.and self_mem_nhdsWithin)).mono ?_
  rintro V ⟨hVsmall, hVU, hVfield⟩ p hp B hB
  obtain ⟨hdef, hopen, inst, hra⟩ := hcontour p.1 p.2 hp
  have h0 := expCurve_zero B hVfield
  obtain ⟨hstay, hdiff⟩ := eventually_mem_and_differentiableAt
    (F := fun W => PeriodicLattice.meanContourHolonomy W p.1 p.2)
    hopen hra hVU (hcurve V hVfield B hB)
    (hderiv V hVfield B hB) h0
  have hval : ComplexMatrix2.operatorNorm
      (PeriodicLattice.meanContourHolonomy (expCurve V B 0) p.1 p.2 - 1) < 1 := by
    rw [h0]
    exact hVsmall p hp
  refine ⟨?_, ?_⟩
  · have hnear : ∀ᶠ t : ℝ in 𝓝 0,
        ComplexMatrix2.operatorNorm
          (PeriodicLattice.meanContourHolonomy (expCurve V B t) p.1 p.2 - 1) < 1 := by
      have h₁ : ContinuousAt (fun t : ℝ =>
          ‖PeriodicLattice.meanContourHolonomy (expCurve V B t) p.1 p.2 - 1‖) 0 :=
        (hdiff.continuousAt.sub continuousAt_const).norm
      exact h₁.tendsto.eventually_lt_const hval
    filter_upwards [hstay, hnear] with t h₁ h₂
    exact ⟨hdef _ h₁, h₂⟩
  · have hlogd : DifferentiableAt ℝ ComplexMatrix2.logSeries
        (PeriodicLattice.meanContourHolonomy (expCurve V B 0) p.1 p.2) :=
      differentiableAt_logSeries hH hval
    exact DifferentiableAt.comp (g := ComplexMatrix2.logSeries)
      (f := fun t : ℝ => PeriodicLattice.meanContourHolonomy (expCurve V B t) p.1 p.2)
      (0 : ℝ) hlogd hdiff
end ContourLogarithms
end YangMills.Construction.Tower
end
