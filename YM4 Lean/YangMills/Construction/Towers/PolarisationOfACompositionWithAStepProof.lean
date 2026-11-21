import YangMills.Construction.Towers.DilationNearTheTrivialConfigurationProof
import YangMills.Construction.Matrices.CalculusOfHolomorphicMaps
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverageProof
import YangMills.Construction.Towers.FamilyOfACompositionIsGivenAtLargeSides
import YangMills.Construction.Towers.PolarisationOfACompositionWithAStep
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOne
import YangMills.Construction.Towers.TheCriticalBranch
import YangMills.Construction.Towers.TheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.HessianOfStepComposite
open YangMills.Construction YangMills.Construction.Matrices YangMills.Construction.Coordinates YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.Tower YangMills.Construction.PeriodicOperators.Tempered.OneStep YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.OneLoopLaw.GaugeColourMomenta
section Renaming
variable {σ σ' ι ι' κ E : Type}
def pullAlong (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) : σ → ComplexMatrix2 := A ∘ τ
abbrev relabelGroupFactors (r : ι ≃ ι') (κ : Type) : ι ⊕ κ ≃ ι' ⊕ κ := r.sumCongr (Equiv.refl κ)
def coordTuple {N : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : σ ≃ Fin N)
    (w : ComplexCoordinates (N * 3)) (x : σ) : ComplexMatrix2 :=
  ComplexCoordinates.tracelessTuple b w (ν x)
theorem isHolomorphicToCoords_pullAlong [Fintype ι] [Fintype ι'] [Fintype κ] {l : ℕ}
    (r : ι ≃ ι') {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ) :
    IsHolomorphicToCoords b e (pullAlong (relabelGroupFactors r κ) ⁻¹' W)
      (Φ ∘ pullAlong (relabelGroupFactors r κ)) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.isHolomorphicToCoords_precomp <;> assumption
theorem isHolomorphicToCoords_of_basis [Fintype ι] [Fintype κ] {l : ℕ}
    (hCh : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {e : E ≃ ComplexCoordinates l} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ) : IsHolomorphicToCoords b' e W Φ := by
  obtain ⟨hW, hc, hp⟩ := h
  refine ⟨hW, hc, fun p hpW => ?_⟩
  obtain ⟨O, h0, hA, hO⟩ := hp p hpW
  exact ⟨O, h0, hA, ((hCh.2.1 (ι ⊕ κ)).2.1 E l e b b' O _).1 hO⟩
end Renaming
section Bonds
variable {L n k i n₂ k₂ i₂ n₃ k₃ i₃ : ℕ}
structure PreservesOrientation (e : Edge L n k i ≃ Edge L n₂ k₂ i₂) : Prop where
  isPositive_iff : ∀ b, (e b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  map_opposite : ∀ b, e b.opposite = (e b).opposite
theorem PreservesOrientation.symm {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) : PreservesOrientation e.symm where
  isPositive_iff b := by rw [← he.isPositive_iff, e.apply_symm_apply]
  map_opposite b := by
    apply e.injective
    rw [he.map_opposite, e.apply_symm_apply, e.apply_symm_apply]
theorem PreservesOrientation.trans {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    {e' : Edge L n₂ k₂ i₂ ≃ Edge L n₃ k₃ i₃} (he : PreservesOrientation e)
    (he' : PreservesOrientation e') : PreservesOrientation (e.trans e') where
  isPositive_iff b := (he'.isPositive_iff _).trans (he.isPositive_iff b)
  map_opposite b := by
    simp only [Equiv.trans_apply]
    rw [he.map_opposite, he'.map_opposite]
def positiveEdgeEquiv {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e) :
    PositiveEdge L n k i ≃ PositiveEdge L n₂ k₂ i₂ :=
  e.subtypeEquiv fun b => (he.isPositive_iff b).symm
theorem transportTotal_mem_fieldSpace {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) :
    transportTotal e V ∈ fieldSpace L n₂ k₂ i₂ := by
  refine ⟨fun b _ => hV.1 _ (mem_univ _), fun b _ => ?_⟩
  change V (e.symm b.opposite) = (V (e.symm b))⁻¹
  rw [he.symm.map_opposite]
  exact hV.2 _ (mem_univ _)
theorem transportTotal_mem_edgeFormSpace {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e)
    {B : Edge L n k i → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k i) :
    transportTotal e B ∈ edgeFormSpace L n₂ k₂ i₂ := by
  refine ⟨fun b hb => hB.1 _ ((he.symm.isPositive_iff b).2 hb), fun b => ?_⟩
  change B (e.symm b.opposite) = -B (e.symm b)
  rw [he.symm.map_opposite]
  exact hB.2 _
theorem fieldOfPositiveValues_restrict {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k i → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem transportTotal_expTwist {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (X U : Edge L n k i → ComplexMatrix2) :
    transportTotal e (PeriodicLattice.expTwist X U) =
      PeriodicLattice.expTwist (transportTotal e X) (transportTotal e U) := by
  funext b
  have hpos := he.symm.isPositive_iff b
  have hopp := he.symm.map_opposite b
  simp only [transportTotal, Function.comp, PeriodicLattice.expTwist]
  by_cases h : b.IsPositivelyOriented
  · rw [if_pos h, if_pos (hpos.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hpos.1 h')), hopp]
theorem leftSecondDeriv_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e)
    (g : (Edge L n₂ k₂ i₂ → ComplexMatrix2) → ℝ) (X Y : Edge L n k i → ComplexMatrix2) :
    leftSecondDeriv (fun V => g (transportTotal e V)) (fun _ => 1) X Y =
      leftSecondDeriv g (fun _ => 1) (transportTotal e X) (transportTotal e Y) := by
  have key : ∀ s t : ℝ, transportTotal e (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • X + algebraMap ℝ ℂ t • Y) fun _ => 1) =
      PeriodicLattice.expTwist (algebraMap ℝ ℂ s • transportTotal e X +
        algebraMap ℝ ℂ t • transportTotal e Y) fun _ => 1 := fun s t => by
    rw [transportTotal_expTwist he]
    rfl
  simp only [leftSecondDeriv, mixedDirectionalDeriv, key]
theorem leftDeriv_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (g : (Edge L n₂ k₂ i₂ → ComplexMatrix2) → ℝ) (X : Edge L n k i → ComplexMatrix2) :
    leftDeriv (fun V => g (transportTotal e V)) (fun _ => 1) X =
      leftDeriv g (fun _ => 1) (transportTotal e X) := by
  have key : ∀ t : ℝ, transportTotal e (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ t • X) fun _ => 1) =
      PeriodicLattice.expTwist (algebraMap ℝ ℂ t • transportTotal e X) fun _ => 1 := fun t => by
    rw [transportTotal_expTwist he]
    rfl
  simp only [leftDeriv, directionalDeriv, key]
structure PreservesEndpoints (e : Edge L n k i ≃ Edge L n₂ k₂ i₂)
    (s : Vertex L n k i ≃ Vertex L n₂ k₂ i₂) : Prop where
  map_target : ∀ b, (e b).target = s b.target
  map_source : ∀ b, (e b).source = s b.source
theorem PreservesEndpoints.trans {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    {s : Vertex L n k i ≃ Vertex L n₂ k₂ i₂}
    {e' : Edge L n₂ k₂ i₂ ≃ Edge L n₃ k₃ i₃} {s' : Vertex L n₂ k₂ i₂ ≃ Vertex L n₃ k₃ i₃}
    (h : PreservesEndpoints e s) (h' : PreservesEndpoints e' s') :
    PreservesEndpoints (e.trans e') (s.trans s') where
  map_target b := by
    simp only [Equiv.trans_apply]
    rw [h'.map_target, h.map_target]
  map_source b := by
    simp only [Equiv.trans_apply]
    rw [h'.map_source, h.map_source]
theorem transportTotal_vertexCoboundary {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    {s : Vertex L n k i ≃ Vertex L n₂ k₂ i₂} (h : PreservesEndpoints e s)
    (l : Vertex L n k i → ComplexMatrix2) :
    transportTotal e (vertexCoboundary l) = vertexCoboundary (transportTotal s l) := by
  funext b
  have h₁ : s.symm b.target = (e.symm b).target := by
    rw [Equiv.symm_apply_eq, ← h.map_target, e.apply_symm_apply]
  have h₂ : s.symm b.source = (e.symm b).source := by
    rw [Equiv.symm_apply_eq, ← h.map_source, e.apply_symm_apply]
  change l (e.symm b).target - l (e.symm b).source = l (s.symm b.target) - l (s.symm b.source)
  rw [h₁, h₂]
theorem vertexCoboundary_mem_edgeFormSpace {l : Vertex L n k i → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n k i) :
    vertexCoboundary l ∈ edgeFormSpace L n k i := by apply _root_.YangMills.Construction.Tower.ClosedFormsSmoothing.vertexCoboundary_mem <;> assumption
end Bonds
theorem deriv_ofReal_comp_zero (g : ℝ → ℝ) :
    deriv (fun t : ℝ => (g t : ℂ)) 0 = ((deriv g 0 : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ g 0
  · exact h.hasDerivAt.ofReal_comp.deriv
  · rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt]
    · simp
    · intro h'
      apply h
      have h₁ := Complex.reCLM.differentiableAt.comp (0 : ℝ) h'
      simpa [Function.comp_def] using h₁
section Analytic
variable {L n k i m : ℕ}
theorem analytic_transport (hE : BondSetFields.ProductStructureHolds)
    (hCh : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hCalc : GroupLieProduct.HolomorphicCalculus.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hi : i ≤ k) {e : Edge L n k i ≃ Edge L m 0 0} (he : PreservesOrientation e)
    {f : (UnitEdge L m → ComplexMatrix2) → ℝ} (hf : IsAnalyticNearIdentity f) :
    ∃ U : Set (Edge L n k i → ComplexMatrix2), IsOpenNhdOfOne U ∧
      IsAnalyticFieldFunction U fun V => f (transportTotal e V) := by
  obtain ⟨instP, O, ⟨O₂, hO₂, rfl⟩, h1O, hf⟩ := hf
  let instR : Fintype (PositiveEdge L n k i) := Fintype.ofEquiv _ (positiveEdgeEquiv he).symm
  have hT : IsOpen ((fun V : Edge L n k i → ComplexMatrix2 =>
      restrictToPositiveEdges (transportTotal e V)) ⁻¹' O₂) :=
    hO₂.preimage (continuous_pi fun b => continuous_apply _)
  obtain ⟨U, hU⟩ : ∃ U : Set (Edge L n k i → ComplexMatrix2), U =
      ((fun V : Edge L n k i → ComplexMatrix2 =>
        restrictToPositiveEdges (transportTotal e V)) ⁻¹' O₂) ∩ fieldSpace L n k i := ⟨_, rfl⟩
  have hsub : U ⊆ fieldSpace L n k i := by
    rw [hU]
    exact inter_subset_right
  have hop : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U :=
    ⟨hsub, (((hE L hS k i hi).1 n hn).2.2.2.2.2.2.2.2.1 U hsub).1 ⟨_, hT, hU⟩⟩
  obtain ⟨O₃, hO₃, himg⟩ := hop.2
  have hone : trivialField L n k i ∈ U := by
    rw [hU]
    exact ⟨h1O.1, fun _ _ => Submonoid.one_mem _, fun _ _ => by simp⟩
  refine ⟨U, ⟨hop, hone⟩, hop, instR, ?_⟩
  have hcov : ∀ q : PositiveEdge L n k i ⊕ Empty → ComplexMatrix2,
      fieldOfPositiveValues (groupComponent q) ∈ U →
        groupComponent q ∈ O₃ ∧
          groupComponent q ∈ edgePower L n k i PeriodicLattice.compactGaugeGroup := by
    intro q hq
    have h₂ : groupComponent q ∈ restrictToPositiveEdges '' U :=
      ⟨_, hq, restrict_fieldOfPositiveValues _⟩
    rw [himg] at h₂
    exact h₂
  have hprop : ∀ w : PositiveEdge L n k i → ComplexMatrix2, w ∈ O₃ →
      w ∈ edgePower L n k i PeriodicLattice.compactGaugeGroup →
      fieldOfPositiveValues w ∈ U ∧
        pullAlong (positiveEdgeEquiv he).symm w ∈
          O₂ ∩ specialUnitaryPower (PositiveEdge L m 0 0) ∧
        fieldOfPositiveValues (k := 0) (j := 0) (pullAlong (positiveEdgeEquiv he).symm w) =
          transportTotal e (fieldOfPositiveValues w) := by
    intro w h₁ h₂
    have h₃ : w ∈ restrictToPositiveEdges '' U := by
      rw [himg]
      exact ⟨h₁, h₂⟩
    obtain ⟨V, hV, rfl⟩ := h₃
    have hVc := hsub hV
    have hVO : restrictToPositiveEdges (transportTotal e V) ∈ O₂ := by
      have hV' := hV
      rw [hU] at hV'
      exact hV'.1
    have htr := transportTotal_mem_fieldSpace he hVc
    have hpull : pullAlong (positiveEdgeEquiv he).symm (restrictToPositiveEdges V) =
        restrictToPositiveEdges (transportTotal e V) := rfl
    rw [fieldOfPositiveValues_restrict hVc, hpull, fieldOfPositiveValues_restrict htr]
    exact ⟨hV, ⟨hVO, fun b => htr.1 _ (mem_univ _)⟩, rfl⟩
  have hpg : ∀ q : PositiveEdge L n k i ⊕ Empty → ComplexMatrix2,
      asGroupFactors (pullAlong (positiveEdgeEquiv he).symm (groupComponent q)) =
        pullAlong (relabelGroupFactors (positiveEdgeEquiv he).symm Empty) q := by
    intro q
    funext x
    cases x with
    | inl a => rfl
    | inr z => exact z.elim
  refine ⟨⟨bot_le, groupComponent ⁻¹' O₃,
    hO₃.preimage (continuous_pi fun b => continuous_apply _), ?_⟩, fun p hp => ?_⟩
  · ext q
    constructor
    · intro hq
      obtain ⟨h₁, h₂⟩ := hcov q hq
      exact ⟨h₁, (Submodule.mem_bot _).2 (funext fun x => x.elim), h₂⟩
    · rintro ⟨h₁, -, h₂⟩
      exact (hprop _ h₁ h₂).1
  · obtain ⟨hp₃, hp₄⟩ := hcov p hp
    obtain ⟨-, hxO, -⟩ := hprop _ hp₃ hp₄
    obtain ⟨W, Φ, hxW, hΦ, hEq⟩ := hf β _ hxO
    have hW₁ := isHolomorphicToCoords_pullAlong (κ := Empty) (positiveEdgeEquiv he).symm
      (b := β) (e := (Equiv.funUnique (Fin 1) ℂ).symm) (W := W) (Φ := Φ) hΦ
    obtain ⟨X, hX⟩ : ∃ X : Set (PositiveEdge L n k i ⊕ Empty → ComplexMatrix2), X =
        (pullAlong (relabelGroupFactors (positiveEdgeEquiv he).symm Empty) ⁻¹' W) ∩
          groupComponent ⁻¹' O₃ := ⟨_, rfl⟩
    have hXopen : ComplexMatrix2.IsRelativelyOpen
        (GroupLieProduct (PositiveEdge L n k i) Empty) X := by
      obtain ⟨A, hA, hAeq⟩ := hW₁.1
      refine ⟨A ∩ groupComponent ⁻¹' O₃,
        hA.inter (hO₃.preimage (continuous_pi fun b => continuous_apply _)), ?_⟩
      rw [hX, hAeq]
      ext q
      simp only [mem_inter_iff, mem_preimage]
      tauto
    have hW₂ := (hCalc.2.2.2.2.2.2.2.1 (PositiveEdge L n k i) Empty) β _ X _ _ _ _ hW₁ hXopen
      (by rw [hX]; exact inter_subset_left)
    refine ⟨X, ?_, hXopen, fun q hq => ?_,
      fun q => (Equiv.funUnique (Fin 1) ℂ).symm
        (Φ (pullAlong (relabelGroupFactors (positiveEdgeEquiv he).symm Empty) q)),
      fun b => ?_, fun q hq => ?_⟩
    · rw [hX]
      refine ⟨?_, hp₃⟩
      rw [mem_preimage, ← hpg]
      exact hxW
    · rw [hX] at hq
      exact (hprop _ hq.1.2 hq.2.2).1
    · exact isHolomorphicToCoords_of_basis hCh b hW₂
    · rw [hX] at hq
      obtain ⟨⟨hq₁, hq₂⟩, -, hq₃⟩ := hq
      obtain ⟨-, hy, hcv⟩ := hprop _ hq₂ hq₃
      have h₅ := hEq _ hy (by rw [hpg]; exact hq₁)
      rw [hpg] at h₅
      change (Equiv.funUnique (Fin 1) ℂ).symm
        (Φ (pullAlong (relabelGroupFactors (positiveEdgeEquiv he).symm Empty) q)) = _
      rw [h₅]
      beta_reduce
      rw [hcv]
      rfl
theorem leftGradient_transport_eq_zero (hD : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i ≤ k)
    {e : Edge L n k i ≃ Edge L m 0 0} (he : PreservesOrientation e)
    {f : (UnitEdge L m → ComplexMatrix2) → ℝ} {U : Set (Edge L n k i → ComplexMatrix2)}
    (hU : IsOpenNhdOfOne U)
    (hra : IsAnalyticFieldFunction U fun V => f (transportTotal e V))
    (hfirst : ∀ C ∈ edgeFormSpace L m 0 0,
      leftDeriv (k := 0) (j := 0) f (fun _ => 1) C = 0) :
    leftGradient (fieldSpace L n k i) (fun V => (f (transportTotal e V) : ℂ))
      (trivialField L n k i) = 0 := by
  have hder : ∀ B ∈ edgeFormSpace L n k i, leftDeriv (fun V => (f (transportTotal e V) : ℂ))
      (trivialField L n k i) B = 0 := by
    intro B hB
    have h₁ : leftDeriv (fun V => (f (transportTotal e V) : ℂ)) (trivialField L n k i) B =
        ((leftDeriv (fun V => f (transportTotal e V)) (fun _ => 1) B : ℝ) : ℂ) :=
      deriv_ofReal_comp_zero _
    rw [h₁, leftDeriv_transport he, hfirst _ (transportTotal_mem_edgeFormSpace he hB)]
    simp
  have hzero : ∀ D : Set (Edge L n k i → ComplexMatrix2),
      IsLeftGradient D (fun V => (f (transportTotal e V) : ℂ)) (trivialField L n k i) 0 :=
    fun D =>
    ⟨⟨fun _ _ => ComplexMatrix2.traceless.zero_mem, fun _ => by simp⟩,
      fun _ => ⟨fun _ _ => ComplexMatrix2.hermitianTraceless.zero_mem, fun _ => by simp⟩,
      fun B hB _ => by
        rw [hder B hB]
        simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges,
          ComplexMatrix2.halfTrace]⟩
  have hUniq := (((hD L n k i i hS hn hi hi U hU.1).1
    (fun V => (f (transportTotal e V) : ℂ)) hra).2.2.2 _ hU.2).1
  have hspec : IsLeftGradient (fieldSpace L n k i) (fun V => (f (transportTotal e V) : ℂ))
      (trivialField L n k i)
      (leftGradient (fieldSpace L n k i) (fun V => (f (transportTotal e V) : ℂ))
        (trivialField L n k i)) :=
    Classical.epsilon_spec ⟨0, hzero _⟩
  have h₁ := hUniq.2.2 0 (hzero U)
  have h₂ := hUniq.2.2 _ ⟨hspec.1, fun _ => hspec.2.1 fun V _ => by simp, hspec.2.2⟩
  rw [h₂, ← h₁]
end Analytic
section Step
variable {L n i : ℕ}
theorem cast_isPositivelyOriented {m : ℕ} {d d' : ℤ} (h : d = d')
    (b : PeriodicLattice.Bond L m d) :
    (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b).IsPositivelyOriented ↔
      b.IsPositivelyOriented := by
  subst h
  rfl
theorem cast_opposite {m : ℕ} {d d' : ℤ} (h : d = d') (b : PeriodicLattice.Bond L m d) :
    Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b.opposite =
      (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b).opposite := by
  subst h
  rfl
theorem cast_target {m : ℕ} {d d' : ℤ} (h : d = d') (b : PeriodicLattice.Bond L m d) :
    (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b).target =
      Equiv.cast (congrArg (PeriodicLattice.Site L m) h) b.target := by
  subst h
  rfl
theorem cast_source {m : ℕ} {d d' : ℤ} (h : d = d') (b : PeriodicLattice.Bond L m d) :
    (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b).source =
      Equiv.cast (congrArg (PeriodicLattice.Site L m) h) b.source := by
  subst h
  rfl
theorem levelDepth_self (k : ℕ) :
    PeriodicLattice.levelDepth k k = PeriodicLattice.levelDepth 0 0 := by
  simp [PeriodicLattice.levelDepth]
abbrev topVertexEquiv (L n k : ℕ) : Vertex L n k k ≃ Vertex L n 0 0 :=
  Equiv.cast (congrArg (PeriodicLattice.Site L n) (levelDepth_self k))
theorem preservesOrientation_topEdgeEquiv (L n k : ℕ) :
    PreservesOrientation (topEdgeEquiv L n k) :=
  ⟨cast_isPositivelyOriented (levelDepth_self k), cast_opposite (levelDepth_self k)⟩
theorem preservesEndpoints_topEdgeEquiv (L n k : ℕ) :
    PreservesEndpoints (topEdgeEquiv L n k) (topVertexEquiv L n k) :=
  ⟨cast_target (levelDepth_self k), cast_source (levelDepth_self k)⟩
theorem preservesOrientation_cast {m m' : ℕ} (h : m = m') :
    PreservesOrientation (Equiv.cast (congrArg (UnitEdge L) h)) := by
  subst h
  exact ⟨fun _ => Iff.rfl, fun _ => rfl⟩
theorem preservesEndpoints_cast {m m' : ℕ} (h : m = m') :
    PreservesEndpoints (Equiv.cast (congrArg (UnitEdge L) h))
      (Equiv.cast (congrArg (fun x => Vertex L x 0 0) h)) := by
  subst h
  exact ⟨fun _ => rfl, fun _ => rfl⟩
theorem scaleEdge_preserves (hX : ScalingPropertiesStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L) (hn : 0 < n) :
    PreservesOrientation (scaleEdge (n := n) hL (Nat.le_succ i) i) ∧
      PreservesEndpoints (scaleEdge (n := n) hL (Nat.le_succ i) i)
        (scaleVertex (n := n) hL (Nat.le_succ i) i).toEquiv := by
  have hat := ((hX L (i + 1) i hS (Nat.le_succ i)).1 n hn).atLevel i le_rfl
  refine ⟨⟨fun b => ?_, hat.edge_opposite⟩, ⟨hat.edge_target, hat.edge_source⟩⟩
  have himg := hat.image_positive
  constructor
  · intro hb
    have hmem : scaleEdge (n := n) hL (Nat.le_succ i) i b ∈
        scaleEdge (n := n) hL (Nat.le_succ i) i '' {b | b.IsPositivelyOriented} := by
      rw [himg]
      exact hb
    obtain ⟨b', hb', hEq⟩ := hmem
    rw [← (scaleEdge (n := n) hL (Nat.le_succ i) i).injective hEq]
    exact hb'
  · intro hb
    have hmem : scaleEdge (n := n) hL (Nat.le_succ i) i b ∈
        scaleEdge (n := n) hL (Nat.le_succ i) i '' {b | b.IsPositivelyOriented} :=
      mem_image_of_mem _ hb
    rw [himg] at hmem
    exact hmem
def stepVertexEquiv (hL : 0 < L) (n i : ℕ) : Vertex L n (i + 1) i ≃ Vertex L (n + 1) 0 0 :=
  (scaleVertex hL (Nat.le_succ i) i).toEquiv.trans
    ((topVertexEquiv L (scaledExponent n (i + 1) i) i).trans
      (Equiv.cast (congrArg (fun x => Vertex L x 0 0) (scaledExponent_succ_self n i))))
theorem preservesOrientation_stepEdgeEquiv (hX : ScalingPropertiesStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L) (hn : 0 < n) :
    PreservesOrientation (stepEdgeEquiv hL n i) :=
  (scaleEdge_preserves hX hS hL hn).1.trans
    ((preservesOrientation_topEdgeEquiv _ _ _).trans
      (preservesOrientation_cast (scaledExponent_succ_self n i)))
theorem preservesEndpoints_stepEdgeEquiv (hX : ScalingPropertiesStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L) (hn : 0 < n) :
    PreservesEndpoints (stepEdgeEquiv hL n i) (stepVertexEquiv hL n i) :=
  (scaleEdge_preserves hX hS hL hn).2.trans
    ((preservesEndpoints_topEdgeEquiv _ _ _).trans
      (preservesEndpoints_cast (scaledExponent_succ_self n i)))
theorem leftDifferential_topLevelForm_decomp
    (hD : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hX : ScalingPropertiesStatement) (hS : Conventions.IsAdmissibleBlockingFactor L)
    (hL : 0 < L) (hn : 0 < n) {W : Set (Edge L n (i + 1) (i + 1) → ComplexMatrix2)}
    (hW : IsOpenNhdOfOne W) (hp : IsAnalyticFieldMap W (chosenProlong L n (i + 1) i))
    (hprolong : ∀ B ∈ edgeFormSpace L n (i + 1) (i + 1),
      CriticalBranchResponse.ProlongDerivativeCondition L n i B)
    {A : UnitEdge L n → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n 0 0) :
    topLevelForm L n (i + 1) A ∈ edgeFormSpace L n (i + 1) (i + 1) ∧
      stepPushforward hL n i A ∈ edgeFormSpace L (n + 1) 0 0 ∧
      ∃ l : Vertex L (n + 1) 0 0 → ComplexMatrix2,
        (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) ∧
        vertexCoboundary l ∈ edgeFormSpace L (n + 1) 0 0 ∧
        transportTotal (stepEdgeEquiv hL n i) (leftDifferential (chosenProlong L n (i + 1) i)
          (trivialField L n (i + 1) (i + 1)) (topLevelForm L n (i + 1) A)) =
          stepPushforward hL n i A + vertexCoboundary l := by
  have he := preservesOrientation_stepEdgeEquiv (i := i) hX hS hL hn
  have hends := preservesEndpoints_stepEdgeEquiv (i := i) hX hS hL hn
  have hT : topLevelForm L n (i + 1) A ∈ edgeFormSpace L n (i + 1) (i + 1) :=
    transportTotal_mem_edgeFormSpace (preservesOrientation_topEdgeEquiv L n (i + 1)).symm hA
  obtain ⟨l, hl, heq⟩ := hprolong _ hT
  have hlin := (((hD L n (i + 1) (i + 1) i hS hn le_rfl (Nat.le_succ i) W hW.1).2.1 _ hp).2.2 _
    hW.2).2 ⟨_, hT⟩
  have hY : leftDifferential (chosenProlong L n (i + 1) i)
      (trivialField L n (i + 1) (i + 1)) (topLevelForm L n (i + 1) A) ∈
      edgeFormSpace L n (i + 1) i := by
    rw [← hlin]
    exact Subtype.property _
  have hdl := vertexCoboundary_mem_edgeFormSpace hl
  have hXf : crossingSmoothingIter L n (i + 1) i (CriticalBranchResponse.meshScaledResponse L n
      (i + 1) (topLevelForm L n (i + 1) A) : Edge L n (i + 1) 0 → ComplexMatrix2) ∈
      edgeFormSpace L n (i + 1) i := by
    have h₁ := (edgeFormSpace L n (i + 1) i).sub_mem hY hdl
    rw [heq, sub_sub_cancel] at h₁
    exact h₁
  have hscale : transportTotal (stepEdgeEquiv hL n i) (vertexCoboundary l) =
      vertexCoboundary (transportTotal (stepVertexEquiv hL n i) l) :=
    transportTotal_vertexCoboundary hends l
  refine ⟨hT, transportTotal_mem_edgeFormSpace he hXf,
    transportTotal (stepVertexEquiv hL n i) l, fun x => (hl _ (mem_univ _)).2, ?_, ?_⟩
  · rw [← hscale]
    exact transportTotal_mem_edgeFormSpace he hdl
  · rw [← hscale]
    conv_rhs => rw [heq]
    have hsum : stepPushforward hL n i A = transportTotal (stepEdgeEquiv hL n i)
        (crossingSmoothingIter L n (i + 1) i (CriticalBranchResponse.meshScaledResponse L n
          (i + 1) (topLevelForm L n (i + 1) A) : Edge L n (i + 1) 0 → ComplexMatrix2)) := rfl
    rw [hsum]
    funext b
    simp [transportTotal]
theorem mem_complexEdgeForms_of_mem {m : ℕ} {B : UnitEdge L m → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m 0 0) : B ∈ complexEdgeForms L m 0 0 := by apply _root_.YangMills.DeltaSharedProofs.p8199 <;> assumption
theorem hessianAtIdentity_compStep (hComp : CompositeSecondOrderAtIdentity)
    (hD : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hE : BondSetFields.ProductStructureHolds)
    (hCh : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hCalc : GroupLieProduct.HolomorphicCalculus.Properties)
    (hX : ScalingPropertiesStatement) (hM : OneLoopLaw.ComplexHessianOfMember.Statement)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L)
    (hn : 0 < n) {F : FieldFamily L} (hbranch : (chosenCriticalBranch L n (i + 1)).IsCritical)
    (hmem : IsAdmissibleMember (F (n + 1))) (hfirst : FirstVariationVanishes F (n + 1))
    (hdiff : HessianKillsCoboundaries F (n + 1))
    (hprolong : ∀ B ∈ edgeFormSpace L n (i + 1) (i + 1),
      CriticalBranchResponse.ProlongDerivativeCondition L n i B)
    {A A' : UnitEdge L n → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n 0 0)
    (hA' : A' ∈ edgeFormSpace L n 0 0) :
    stepPushforward hL n i A ∈ edgeFormSpace L (n + 1) 0 0 ∧
      stepPushforward hL n i A' ∈ edgeFormSpace L (n + 1) 0 0 ∧
      hessianAtIdentity (compStep hL i F) n A A' =
        hessianAtIdentity F (n + 1) (stepPushforward hL n i A) (stepPushforward hL n i A') := by
  have he := preservesOrientation_stepEdgeEquiv (i := i) hX hS hL hn
  obtain ⟨U, hU, hra⟩ := analytic_transport hE hCh hCalc β hS hn (Nat.le_succ i) he
    hmem.analytic
  obtain ⟨W, hW, hp⟩ := hbranch.analytic_prolong i (Nat.lt_succ_self i)
  have hp' : IsAnalyticFieldMap W (chosenProlong L n (i + 1) i) := hp
  have hgrad := leftGradient_transport_eq_zero hD hS hn (Nat.le_succ i) he hU hra hfirst
  obtain ⟨-, -, -, hchain⟩ := hComp L n (i + 1) i hS hn (Nat.lt_succ_self i) U W _
    (chosenProlong L n (i + 1) i) hU hra hW hp' (hbranch.prolong_trivial i (Nat.lt_succ_self i))
    hgrad
  obtain ⟨hT, hSf, l, hl, hdl, hdec⟩ :=
    leftDifferential_topLevelForm_decomp hD hX hS hL hn hW hp' hprolong hA
  obtain ⟨hT', hSf', l', hl', hdl', hdec'⟩ :=
    leftDifferential_topLevelForm_decomp hD hX hS hL hn hW hp' hprolong hA'
  refine ⟨hSf, hSf', ?_⟩
  have hfacts := hM L (n + 1) hS (Nat.succ_pos n) F hmem
  have hleft : hessianAtIdentity (compStep hL i F) n A A' =
      hessianAtIdentity F (n + 1)
        (transportTotal (stepEdgeEquiv hL n i) (leftDifferential (chosenProlong L n (i + 1) i)
          (trivialField L n (i + 1) (i + 1)) (topLevelForm L n (i + 1) A)))
        (transportTotal (stepEdgeEquiv hL n i) (leftDifferential (chosenProlong L n (i + 1) i)
          (trivialField L n (i + 1) (i + 1)) (topLevelForm L n (i + 1) A'))) := by
    have h₁ := leftSecondDeriv_transport (preservesOrientation_topEdgeEquiv L n (i + 1))
      (compStep hL i F n) (topLevelForm L n (i + 1) A) (topLevelForm L n (i + 1) A')
    have hc : ∀ C : UnitEdge L n → ComplexMatrix2,
        transportTotal (topEdgeEquiv L n (i + 1)) (topLevelForm L n (i + 1) C) = C := fun C => by
      funext b
      simp [transportTotal, topLevelForm]
    rw [hc, hc] at h₁
    have h₂ : (fun V => compStep hL i F n (transportTotal (topEdgeEquiv L n (i + 1)) V)) =
        fun V => F (n + 1) (transportTotal (stepEdgeEquiv hL n i)
          (chosenProlong L n (i + 1) i V)) :=
      funext fun V => compStep_transportTotal hL i n F V
    have h₃ : leftSecondDeriv
        (fun V => F (n + 1) (transportTotal (stepEdgeEquiv hL n i)
          (chosenProlong L n (i + 1) i V)))
        (trivialField L n (i + 1) (i + 1))
        (topLevelForm L n (i + 1) A) (topLevelForm L n (i + 1) A') =
      leftSecondDeriv (fun V => F (n + 1) (transportTotal (stepEdgeEquiv hL n i) V))
        (trivialField L n (i + 1) i)
        (leftDifferential (chosenProlong L n (i + 1) i)
          (trivialField L n (i + 1) (i + 1)) (topLevelForm L n (i + 1) A))
        (leftDifferential (chosenProlong L n (i + 1) i)
          (trivialField L n (i + 1) (i + 1)) (topLevelForm L n (i + 1) A')) :=
      hchain _ hT _ hT'
    rw [h₂] at h₁
    exact h₁.symm.trans (h₃.trans (leftSecondDeriv_transport he (F (n + 1)) _ _))
  rw [hleft, hdec, hdec']
  have cS := mem_complexEdgeForms_of_mem hSf
  have cS' := mem_complexEdgeForms_of_mem hSf'
  have cD := mem_complexEdgeForms_of_mem hdl
  have cD' := mem_complexEdgeForms_of_mem hdl'
  have cSD := (complexEdgeForms L (n + 1) 0 0).add_mem cS cD
  have cSD' := (complexEdgeForms L (n + 1) 0 0).add_mem cS' cD'
  have add_left : ∀ X ∈ complexEdgeForms L (n + 1) 0 0, ∀ Y ∈ complexEdgeForms L (n + 1) 0 0,
      ∀ Z ∈ complexEdgeForms L (n + 1) 0 0, complexHessian F (n + 1) Y Z = 0 →
      complexHessian F (n + 1) (X + Y) Z = complexHessian F (n + 1) X Z := by
    intro X hX' Y hY Z hZ h0
    have h := hfacts.linear_left 1 X hX' Y hY Z hZ
    rwa [one_smul, one_mul, h0, add_zero] at h
  have h₁ := add_left _ cS _ cD _ cSD' (hdiff l hl _ cSD')
  have h₂ : complexHessian F (n + 1) (stepPushforward hL n i A)
      (stepPushforward hL n i A' + vertexCoboundary l') =
      complexHessian F (n + 1) (stepPushforward hL n i A) (stepPushforward hL n i A') := by
    rw [hfacts.symm _ cS _ cSD', add_left _ cS' _ cD' _ cS (hdiff l' hl' _ cS),
      hfacts.symm _ cS' _ cS]
  have h₃ := hfacts.ofReal _ ((edgeFormSpace L (n + 1) 0 0).add_mem hSf hdl) _
    ((edgeFormSpace L (n + 1) 0 0).add_mem hSf' hdl')
  have h₄ := hfacts.ofReal _ hSf _ hSf'
  rw [h₁, h₂, h₄] at h₃
  exact Complex.ofReal_injective h₃.symm
end Step
section Complex
variable {L n : ℕ}
private theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
private theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
theorem eventuallyForSides_and {P Q : ℕ → Prop} (hP : EventuallyForSides L P)
    (hQ : EventuallyForSides L Q) : EventuallyForSides L fun n => P n ∧ Q n := by apply _root_.YangMills.SharedProofs.p21504 <;> assumption
end Complex
theorem claim_holds (hB : CriticalBranchExists)
    (hR : CriticalBranchResponse.ResponseConditions)
    (hG : GaugeColourMomentumClaim)
    (hComp : CompositeSecondOrderAtIdentity) (hM : OneLoopLaw.ComplexHessianOfMember.Statement)
    (hFam : CompStepEventuallyDefined)
    (hX : ScalingPropertiesStatement)
    (hD : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hE : BondSetFields.ProductStructureHolds)
    (hCh : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hCalc : GroupLieProduct.HolomorphicCalculus.Properties)
    (hP : OneLoop.PauliMatrixRelations) : Claim := by
  intro L hL hS F i hF
  obtain ⟨-, -, -, ⟨β, -⟩, -⟩ := hP
  have hdef : IsDefinedOn L F {n | IsAdmissibleMember (F n) ∧ FirstVariationVanishes F n ∧
      HessianKillsCoboundaries F n} (fun _ => univ) :=
    { eventually := by
        have h := eventuallyForSides_and hF
          (eventuallyForSides_and ((hG L hL hS).1 F hF) ((hG L hL hS).1 F hF))
        obtain ⟨s₀, hs₀, hl⟩ := h
        exact ⟨s₀, hs₀, fun s hs hle n hn e => by
          obtain ⟨h₁, h₂, -⟩ := hl s hs hle n hn e
          exact ⟨h₁, h₂.1, h₂.2.2.1⟩⟩
      admissible := fun _ hn _ => hn.1
      nhdsIdentity := fun _ _ _ => Filter.Eventually.of_forall fun _ => mem_univ _ }
  obtain ⟨s₀, hs₀, hl⟩ := eventuallyForSides_and (hFam L hS F _ _ hdef i).2.1 (hR L hS i)
  refine ⟨s₀, hs₀, fun s hs hle n hn e => ?_⟩
  obtain ⟨⟨hmem, hfirst, hdiff⟩, hall⟩ := hl s hs hle n hn e
  have hbranch : (chosenCriticalBranch L n (i + 1)).IsCritical :=
    Classical.epsilon_spec (hB L n (i + 1) hS hn)
  have hprolong : ∀ B ∈ edgeFormSpace L n (i + 1) (i + 1),
      CriticalBranchResponse.ProlongDerivativeCondition L n i B :=
    fun B hB' => (hall B hB').2.2
  have hfacts := hM L (n + 1) hS (Nat.succ_pos n) F hmem
  intro B hB₁ B' hB₂
  have hRe := realComponent_mem hB₁
  have hIm := imagComponent_mem hB₁
  have hRe' := realComponent_mem hB₂
  have hIm' := imagComponent_mem hB₂
  obtain ⟨fa, fa', k₁⟩ := hessianAtIdentity_compStep hComp hD hE hCh hCalc hX hM β hS hL hn
    hbranch hmem hfirst hdiff hprolong hRe hRe'
  obtain ⟨fb, fb', k₂⟩ := hessianAtIdentity_compStep hComp hD hE hCh hCalc hX hM β hS hL hn
    hbranch hmem hfirst hdiff hprolong hIm hIm'
  have k₃ := (hessianAtIdentity_compStep hComp hD hE hCh hCalc hX hM β hS hL hn
    hbranch hmem hfirst hdiff hprolong hRe hIm').2.2
  have k₄ := (hessianAtIdentity_compStep hComp hD hE hCh hCalc hX hM β hS hL hn
    hbranch hmem hfirst hdiff hprolong hIm hRe').2.2
  have hleft : complexHessian (compStep hL i F) n B B' =
      ((hessianAtIdentity (compStep hL i F) n (realComponent B) (realComponent B') -
        hessianAtIdentity (compStep hL i F) n (imagComponent B)
          (imagComponent B') : ℝ) : ℂ) +
      Complex.I * ((hessianAtIdentity (compStep hL i F) n (realComponent B)
        (imagComponent B') +
        hessianAtIdentity (compStep hL i F) n (imagComponent B)
          (realComponent B') : ℝ) : ℂ) := rfl
  rw [hleft, k₁, k₂, k₃, k₄]
  have hright : complexStepPushforward hL n i B =
      stepPushforward hL n i (realComponent B) +
        Complex.I • stepPushforward hL n i (imagComponent B) := rfl
  have hright' : complexStepPushforward hL n i B' =
      stepPushforward hL n i (realComponent B') +
        Complex.I • stepPushforward hL n i (imagComponent B') := rfl
  rw [hright, hright']
  generalize stepPushforward hL n i (realComponent B) = a at *
  generalize stepPushforward hL n i (imagComponent B) = b at *
  generalize stepPushforward hL n i (realComponent B') = a' at *
  generalize stepPushforward hL n i (imagComponent B') = b' at *
  have ca := mem_complexEdgeForms_of_mem fa
  have cb := mem_complexEdgeForms_of_mem fb
  have ca' := mem_complexEdgeForms_of_mem fa'
  have cb' := mem_complexEdgeForms_of_mem fb'
  have hlin : ∀ X ∈ complexEdgeForms L (n + 1) 0 0, ∀ Y ∈ complexEdgeForms L (n + 1) 0 0,
      ∀ Z ∈ complexEdgeForms L (n + 1) 0 0, complexHessian F (n + 1) (X + Complex.I • Y) Z =
        Complex.I * complexHessian F (n + 1) Y Z + complexHessian F (n + 1) X Z := by
    intro X hX' Y hY Z hZ
    rw [add_comm X]
    exact hfacts.linear_left _ Y hY X hX' Z hZ
  have cZ' := (complexEdgeForms L (n + 1) 0 0).add_mem ca'
    ((complexEdgeForms L (n + 1) 0 0).smul_mem Complex.I cb')
  have hsecond : ∀ X ∈ complexEdgeForms L (n + 1) 0 0,
      complexHessian F (n + 1) X (a' + Complex.I • b') =
        Complex.I * complexHessian F (n + 1) X b' + complexHessian F (n + 1) X a' := by
    intro X hX'
    rw [hfacts.symm _ hX' _ cZ', hlin _ ca' _ cb' _ hX',
      hfacts.symm _ cb' _ hX', hfacts.symm _ ca' _ hX']
  rw [hlin _ ca _ cb _ cZ', hsecond _ cb, hsecond _ ca, hfacts.ofReal _ fa _ fa',
    hfacts.ofReal _ fa _ fb', hfacts.ofReal _ fb _ fa', hfacts.ofReal _ fb _ fb']
  push_cast
  linear_combination (-(hessianAtIdentity F (n + 1) b b' : ℂ)) * Complex.I_mul_I
end YangMills.Construction.Tower.HessianOfStepComposite
end
