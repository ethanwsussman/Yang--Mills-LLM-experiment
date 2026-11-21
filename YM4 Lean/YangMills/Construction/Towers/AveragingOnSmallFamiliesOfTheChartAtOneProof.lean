import YangMills.Construction.Matrices.RestrictionsSumsAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOne
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurations
import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.TrivialConfigurationAtAStep
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
namespace IdentityLieBallSmoothing
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
variable {L n k a b j : ℕ}
theorem isPositivelyOriented_or_opposite {m : ℕ} {i : ℤ} (c : PeriodicLattice.Bond L m i) :
    c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem inv_eq_adjugate_of_mem {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ = X.adjugate := by
  have hdet : X.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
  simp [Matrix.inv_def, hdet]
theorem fieldOfPositiveValues_restrict {V : Edge L n k a → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k a) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem continuousWithinAt_of_positivelyOriented {Y : Type} [TopologicalSpace Y]
    {m : Y → Edge L n k a → ComplexMatrix2} {s : Set Y} {y : Y} (hy : y ∈ s)
    (hfield : MapsTo m s (fieldSpace L n k a))
    (hpos : ∀ c : Edge L n k a, c.IsPositivelyOriented →
      ContinuousWithinAt (fun y => m y c) s y) :
    ContinuousWithinAt m s y := by
  refine continuousWithinAt_pi.2 fun c => ?_
  rcases isPositivelyOriented_or_opposite c with hc | hc
  · exact hpos c hc
  · have h1 : ContinuousWithinAt (fun y => (m y c.opposite).adjugate) s y :=
      ((Continuous.matrix_adjugate continuous_id).continuousAt).comp_continuousWithinAt (hpos _ hc)
    have hval : ∀ y' ∈ s, m y' c = (m y' c.opposite).adjugate := by
      intro y' hy'
      have h2 := (hfield hy').2 c.opposite (mem_univ _)
      rw [← inv_eq_adjugate_of_mem ((hfield hy').1 c.opposite (mem_univ _)), ← h2]
      rfl
    exact h1.congr hval (hval y hy)
theorem eventually_mem_of_tendsto_trivialField {X : Type} {l : Filter X}
    {f : X → Edge L n k a → ComplexMatrix2}
    {U : Set (Edge L n k a → ComplexMatrix2)} (h : IsOpenNhdOfOne U)
    (hf : Tendsto f l (𝓝 (trivialField L n k a)))
    (hfield : ∀ᶠ x in l, f x ∈ fieldSpace L n k a) : ∀ᶠ x in l, f x ∈ U := by
  obtain ⟨O, hO, heq⟩ := h.1.2
  have hρ : Continuous (fun V : Edge L n k a → ComplexMatrix2 => restrictToPositiveEdges V) :=
    continuous_pi fun c => continuous_apply _
  have h1 : restrictToPositiveEdges (trivialField L n k a) ∈ O := by
    have h2 : restrictToPositiveEdges (trivialField L n k a) ∈ restrictToPositiveEdges '' U :=
      ⟨_, h.2, rfl⟩
    rw [heq] at h2
    exact h2.1
  have h3 : ∀ᶠ x in l, restrictToPositiveEdges (f x) ∈ O :=
    (hρ.continuousAt.tendsto.comp hf).eventually (hO.mem_nhds h1)
  filter_upwards [h3, hfield] with x hx hx'
  have h4 : restrictToPositiveEdges (f x) ∈ restrictToPositiveEdges '' U := by
    rw [heq]
    exact ⟨hx, fun c => hx'.1 c.1 (mem_univ _)⟩
  obtain ⟨V, hV, hVe⟩ := h4
  have h5 := congrArg fieldOfPositiveValues hVe
  rw [fieldOfPositiveValues_restrict (h.1.1 hV),
    fieldOfPositiveValues_restrict hx'] at h5
  exact h5 ▸ hV
theorem isOpenInSubspaceTimesGroup_of_isOpenFieldSet [Fintype (PositiveEdge L n k a)]
    {U : Set (Edge L n k a → ComplexMatrix2)} (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U) :
    IsOpenInSubspaceTimesGroup (R := PositiveEdge L n k a) (S := Empty) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ U} := by apply _root_.YangMills.SharedProofs.p979 <;> assumption
theorem isAnalyticFieldMap_mono
    (hS : Matrices.GroupLieProduct.Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    {U U' : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap U m) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U')
    (hsub : U' ⊆ U) :
    IsAnalyticFieldMap U' m := by
  obtain ⟨-, hm, i₁, i₂, hA⟩ := h
  exact ⟨h', hm.mono_left hsub, i₁, i₂,
    ((hS Empty (PositiveEdge L n k a) Empty (PositiveEdge L n k b) ⊥ ⊥ bot_le bot_le _ hA.1).1 _
      (fun q hq => hsub hq) (isOpenInSubspaceTimesGroup_of_isOpenFieldSet h').2).2 _ hA⟩
theorem continuousOn_of_isAnalyticFieldMap
    (hK : Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement)
    {U : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap U m) : ContinuousOn m U := by
  have hU : U ⊆ fieldSpace L n k a := h.1.1
  obtain ⟨-, hm, i₀, i₁, hA⟩ := h
  have hc := ((((hK Empty (PositiveEdge L n k a) Empty (PositiveEdge L n k b)).2.2.2
    ⊥ ⊥ bot_le bot_le).2.2.1 _ hA.1).2.2.1 _ hA).1
  intro V hV
  refine continuousWithinAt_of_positivelyOriented hV hm fun e he => ?_
  let ρ : (Edge L n k a → ComplexMatrix2) → (PositiveEdge L n k a ⊕ Empty → ComplexMatrix2) :=
    fun V' => ofParts (restrictToPositiveEdges V') Empty.elim
  have hρ : Continuous ρ := by
    refine continuous_pi fun r => ?_
    rcases r with r | e
    · exact continuous_apply _
    · exact e.elim
  have hρW : MapsTo ρ U {q | fieldOfPositiveValues (groupComponent q) ∈ U} := by
    intro V' h'
    change fieldOfPositiveValues (restrictToPositiveEdges V') ∈ U
    rw [fieldOfPositiveValues_restrict (hU h')]
    exact h'
  have hcomp := ((continuous_apply (Sum.inl ⟨e, he⟩ :
      PositiveEdge L n k b ⊕ Empty)).continuousAt.comp_continuousWithinAt
    (hc (ρ V) (hρW hV))).comp hρ.continuousWithinAt hρW
  have hval : ∀ V' ∈ U, m V' e = ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues
      (groupComponent (ρ V'))))) (Empty.elim : Empty → ComplexMatrix2) (Sum.inl ⟨e, he⟩) := by
    intro V' h'
    change m V' e = restrictToPositiveEdges (m (fieldOfPositiveValues
      (restrictToPositiveEdges V'))) ⟨e, he⟩
    rw [fieldOfPositiveValues_restrict (hU h')]
    rfl
  exact hcomp.congr hval (hval V hV)
theorem linearSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.linearSmoothing_mem_edgeFormSpace <;> assumption
end IdentityLieBallSmoothing
open Matrices IdentityLieBallSmoothing in
theorem smoothingOnIdentityLieBall_holds
    (hF : SmoothingFibres)
    (hC : IdentityChartOnFields)
    (hT : TrivialFieldAtStep)
    (hR : AxisPathReversal.MainStatement)
    (hS : Matrices.GroupLieProduct.Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    (hK : Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement) :
    SmoothingOnIdentityLieBallStatement := by
  intro L n k i hL hn hi _ _
  refine ⟨fun ξ hξ => linearSmoothing_mem_edgeFormSpace hR hL hn hi hξ, ?_⟩
  obtain ⟨U, hU, -, hA, hOnto⟩ := (hF L n k i hL hn hi).2.2.2.1
  obtain ⟨hsmall, h0, -, hcp, hopen, ht, -⟩ := hC L n k i hL hn hi.le
  obtain ⟨hsmall', h0', -, -, -, -, -, hball', hnear', -⟩ := hC L n k (i + 1) hL hn hi
  have hone : smoothingStep L n k i (trivialField L n k i) =
      trivialField L n k (i + 1) := (hT L n k i hL hn hi).2.1
  have hm : Tendsto (smoothingStep L n k i) (𝓝[U] trivialField L n k i)
      (𝓝 (trivialField L n k (i + 1))) := by
    have h := continuousOn_of_isAnalyticFieldMap hK hA _ hU.2
    rwa [ContinuousWithinAt, hone] at h
  have hfield : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
      identityChartPoint y ∈ fieldSpace L n k i := by
    filter_upwards [hsmall.mem_nhds h0] with y hy using (hcp y hy).1
  have hin : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
      identityChartPoint y ∈ U :=
    eventually_mem_of_tendsto_trivialField hU ht hfield
  have hcomp : Tendsto (fun y => smoothingStep L n k i (identityChartPoint y)) (𝓝 0)
      (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1)) :=
    tendsto_nhdsWithin_iff.2 ⟨hm.comp (tendsto_nhdsWithin_iff.2 ⟨ht, hin⟩),
      hin.mono fun y hy => hA.2.1 hy⟩
  obtain ⟨ε, hε, hb⟩ := hball' _ (hsmall'.mem_nhds h0')
  have hev : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
      smoothingStep L n k i (identityChartPoint y) ∈
        identityChartPoint '' IdentityExpChart.lieBall (PositiveEdge L n k (i + 1)) (1 / 2) :=
    Filter.mem_of_superset (hcomp (hnear' ε hε)) fun y hy => hb hy
  refine ⟨{y | y ∈ IdentityExpChart.lieBall (PositiveEdge L n k i) (1 / 2) ∧
      identityChartPoint y ∈ U ∧
      smoothingStep L n k i (identityChartPoint y) ∈
        identityChartPoint '' IdentityExpChart.lieBall (PositiveEdge L n k (i + 1)) (1 / 2)}, ?_,
    fun y h => h.1, fun y h => h.2.2, fun A hAo hAT => ?_⟩
  · filter_upwards [hsmall.mem_nhds h0, hin, hev] with y h₁ h₂ h₃ using ⟨h₁, h₂, h₃⟩
  · have hsub : identityChartPoint '' A ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hAT hy).2.1
    exact ⟨isAnalyticFieldMap_mono hS hA (hopen A hAo fun y hy => (hAT hy).1) hsub,
      fun V hV B' hB' => hOnto V (hsub hV) B' hB'⟩
end YangMills.Construction.Tower
end
