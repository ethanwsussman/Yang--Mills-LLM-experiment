import YangMills.Construction.Towers.HessianOfTheLastPartialSumProof
import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOneProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
namespace PartialGaugedActionProof
section Curves
variable {X T : Type} [TopologicalSpace X] {R : Geometry.CurveData X T} {N : Set X}
  {F F' : X → ℝ} {x : X}
theorem isCriticalOn_congr (hR : R.HasLocalCurves) (h : EqOn F F' N)
    (hc : R.IsCriticalOn N F x) : R.IsCriticalOn N F' x := by
  refine ⟨hc.1, fun I γ hγ hmaps h0 => ?_⟩
  have hI := (hR.isCurve_local I γ hγ).1
  have hev : (fun t => F (γ t)) =ᶠ[𝓝 0] fun t => F' (γ t) := by
    filter_upwards [hI.1.mem_nhds hI.2.2] with t ht
    exact h (hmaps ht)
  rw [← hev.deriv_eq]
  exact hc.2 I γ hγ hmaps h0
theorem isHessianFormAt_congr {S : Type} {ι : S → T} {Q : S → ℝ} (hR : R.HasLocalCurves)
    (h : EqOn F F' N) (hc : R.IsHessianFormAt ι N F x Q) : R.IsHessianFormAt ι N F' x Q := by
  intro I γ v hγ hmaps h0 ht
  have hI := (hR.isTwiceDiffCurve_local I γ hγ).1
  have hev : (fun t => F (γ t)) =ᶠ[𝓝 0] fun t => F' (γ t) := by
    filter_upwards [hI.1.mem_nhds hI.2.2] with t ht
    exact h (hmaps ht)
  rw [← hev.deriv.deriv_eq]
  exact hc I γ v hγ hmaps h0 ht
theorem hessianForm_congr [AddCommGroup T] [Module ℝ T] {S : Type} [AddCommGroup S] [Module ℝ S]
    (ι : S → T) (hR : R.HasLocalCurves) (h : EqOn F F' N) :
    R.hessianForm ι N F x = R.hessianForm ι N F' x := by
  unfold Geometry.CurveData.hessianForm
  congr 1
  funext Q
  exact propext ⟨isHessianFormAt_congr hR h, isHessianFormAt_congr hR h.symm⟩
end Curves
section Bonds
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_restrictToPositiveEdges {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem trivialField_mem_fieldSpace (j : ℕ) :
    trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
end Bonds
section Analytic
variable {L n k a b c : ℕ}
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k)
    (𝒰 : Set (Edge L n k a → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰 := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem isAnalyticFieldMap_mono (hS : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldMap 𝒰' m := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.isAnalyticFieldMap_mono <;> assumption
theorem isAnalyticFieldFunction_mono (hS : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k a → ComplexMatrix2)} {F : (Edge L n k a → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction 𝒰 F) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldFunction 𝒰' F := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mono <;> assumption
theorem isAnalyticFieldFunction_add (hS : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)} {F₁ F₂ : (Edge L n k a → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction 𝒰 F₁) (h₂ : IsAnalyticFieldFunction 𝒰 F₂) :
    IsAnalyticFieldFunction 𝒰 fun V => F₁ V + F₂ V := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_add <;> assumption
theorem isAnalyticFieldFunction_congr {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {F F' : (Edge L n k a → ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction 𝒰 F)
    (hFF : EqOn F F' 𝒰) : IsAnalyticFieldFunction 𝒰 F' := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_congr <;> assumption
theorem isSubspaceAnalyticToProduct_congr {S R S' R' : Type} [Fintype S] [Fintype R]
    {E : Submodule ℝ (S → ComplexMatrix2)} {E' : Submodule ℝ (S' → ComplexMatrix2)}
    {𝒲 𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {f g : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2} (h𝒲 : 𝒲 = 𝒲')
    (hfg : EqOn f g 𝒲) (hf : IsSubspaceAnalyticToProduct E E' 𝒲 f) :
    IsSubspaceAnalyticToProduct E E' 𝒲' g := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.isSubspaceAnalyticToProduct_congr <;> assumption
theorem isSubspaceAnalyticToCoords_congr {S R : Type} [Fintype S] [Fintype R] {l : ℕ}
    {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {f g : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l} (h𝒲 : 𝒲 = 𝒲')
    (hfg : EqOn f g 𝒲) (hf : IsSubspaceAnalyticToCoords E 𝒲 f) :
    IsSubspaceAnalyticToCoords E 𝒲' g := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isSubspaceAnalyticToCoords_congr <;> assumption
theorem continuousOn_of_isAnalyticFieldMap (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousOn_of_isAnalyticFieldMap <;> assumption
theorem isAnalyticFieldMap_comp (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m₁ : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {m₂ : (Edge L n k b → ComplexMatrix2) → Edge L n k c → ComplexMatrix2}
    (h₁ : IsAnalyticFieldMap 𝒰₁ m₁) (h₂ : IsAnalyticFieldMap 𝒰₂ m₂)
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (compositeDomain 𝒰₁ 𝒰₂ m₁)) :
    IsAnalyticFieldMap (compositeDomain 𝒰₁ 𝒰₂ m₁) (m₂ ∘ m₁) := by
  obtain ⟨-, hmap₁, i₀, i₁, hA₁⟩ := h₁
  obtain ⟨-, hmap₂, i₁', i₂, hA₂⟩ := h₂
  obtain rfl : i₁' = i₁ := Subsingleton.elim _ _
  refine ⟨hopen, fun U hU => hmap₂ hU.2, i₀, i₂, ?_⟩
  have hback : ∀ q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2,
      fieldOfPositiveValues (groupComponent q) ∈ 𝒰₁ →
      fieldOfPositiveValues (restrictToPositiveEdges (m₁ (fieldOfPositiveValues (groupComponent q)))) =
        m₁ (fieldOfPositiveValues (groupComponent q)) :=
    fun q hq => fieldOfPositiveValues_restrictToPositiveEdges (hmap₁ hq)
  have hcomp := ((((hK Empty (PositiveEdge L n k a) Empty (PositiveEdge L n k b)).2.2.2
    ⊥ ⊥ bot_le bot_le).2.2.1 _ hA₁.1).2.2.1 _ hA₁).2 _ hA₂.1
  refine isSubspaceAnalyticToProduct_congr ?_ ?_
    (hcomp.2.2 Empty (PositiveEdge L n k c) ⊥ _ hA₂)
  · ext q
    constructor
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      have hq'' : fieldOfPositiveValues (restrictToPositiveEdges
          (m₁ (fieldOfPositiveValues (groupComponent q)))) ∈ 𝒰₂ := hq'
      rwa [hback q hq] at hq''
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      change fieldOfPositiveValues (restrictToPositiveEdges
        (m₁ (fieldOfPositiveValues (groupComponent q)))) ∈ 𝒰₂
      rwa [hback q hq]
  · rintro q ⟨hq, -⟩
    change ofParts (restrictToPositiveEdges (m₂ (fieldOfPositiveValues (restrictToPositiveEdges
      (m₁ (fieldOfPositiveValues (groupComponent q))))))) Empty.elim = _
    rw [hback q hq]
    rfl
theorem isAnalyticFieldFunction_comp (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {g : (Edge L n k b → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldMap 𝒰₁ m) (h₂ : IsAnalyticFieldFunction 𝒰₂ g)
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (compositeDomain 𝒰₁ 𝒰₂ m)) :
    IsAnalyticFieldFunction (compositeDomain 𝒰₁ 𝒰₂ m) (g ∘ m) := by
  obtain ⟨-, hmap₁, i₀, i₁, hA₁⟩ := h₁
  obtain ⟨-, i₁', hA₂⟩ := h₂
  obtain rfl : i₁' = i₁ := Subsingleton.elim _ _
  refine ⟨hopen, i₀, ?_⟩
  have hback : ∀ q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2,
      fieldOfPositiveValues (groupComponent q) ∈ 𝒰₁ →
      fieldOfPositiveValues (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent q)))) =
        m (fieldOfPositiveValues (groupComponent q)) :=
    fun q hq => fieldOfPositiveValues_restrictToPositiveEdges (hmap₁ hq)
  have hcomp := ((((hK Empty (PositiveEdge L n k a) Empty (PositiveEdge L n k b)).2.2.2
    ⊥ ⊥ bot_le bot_le).2.2.1 _ hA₁.1).2.2.1 _ hA₁).2 _ hA₂.1
  refine isSubspaceAnalyticToCoords_congr ?_ ?_ (hcomp.2.1 1 _ hA₂)
  · ext q
    constructor
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      have hq'' : fieldOfPositiveValues (restrictToPositiveEdges
          (m (fieldOfPositiveValues (groupComponent q)))) ∈ 𝒰₂ := hq'
      rwa [hback q hq] at hq''
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      change fieldOfPositiveValues (restrictToPositiveEdges
        (m (fieldOfPositiveValues (groupComponent q)))) ∈ 𝒰₂
      rwa [hback q hq]
  · rintro q ⟨hq, -⟩
    funext x
    change ((g (fieldOfPositiveValues (restrictToPositiveEdges
      (m (fieldOfPositiveValues (groupComponent q))))) : ℝ) : ℂ) = _
    rw [hback q hq]
    rfl
theorem eventuallyNearIdentity_of_isOpenNhdOfOne
    (hop : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    EventuallyNearIdentity (fieldSpace L n k a) fun V => V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.LastPartialHessian.eventuallyNearIdentity_mem <;> assumption
theorem exists_isOpenNhdOfOne_of_eventually
    (hop : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    {P : (Edge L n k a → ComplexMatrix2) → Prop} (hP : EventuallyNearIdentity (fieldSpace L n k a) P) :
    ∃ 𝒰 : Set (Edge L n k a → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ ∀ V ∈ 𝒰, P V := by
  obtain ⟨O, hO, h1, hsub⟩ := mem_nhdsWithin.1 hP
  exact ⟨O ∩ fieldSpace L n k a, ⟨(hop _).2 ⟨inter_subset_right, O, hO, rfl⟩,
    ⟨h1, trivialField_mem_fieldSpace a⟩⟩, fun V hV => hsub hV⟩
theorem isOpenNhdOfOne_inter
    (hop : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    {𝒰₁ 𝒰₂ : Set (Edge L n k a → ComplexMatrix2)} (h₁ : IsOpenNhdOfOne 𝒰₁)
    (h₂ : IsOpenNhdOfOne 𝒰₂) : IsOpenNhdOfOne (𝒰₁ ∩ 𝒰₂) := by
  obtain ⟨hs₁, O₁, hO₁, e₁⟩ := (hop 𝒰₁).1 h₁.1
  obtain ⟨-, O₂, hO₂, e₂⟩ := (hop 𝒰₂).1 h₂.1
  refine ⟨(hop _).2 ⟨inter_subset_left.trans hs₁, O₁ ∩ O₂, hO₁.inter hO₂, ?_⟩, h₁.2, h₂.2⟩
  rw [e₁, e₂]
  ext V
  simp only [mem_inter_iff]
  tauto
theorem isOpenNhdOfOne_compositeDomain (hK : AnalyticCalculus.AnalyticCalculusStatement)
    (hopa : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    (hopb : ∀ 𝒰 : Set (Edge L n k b → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k b ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k b) 𝒰)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h₁ : IsOpenNhdOfOne 𝒰₁) (hm : IsAnalyticFieldMap 𝒰₁ m)
    (hone : m (trivialField L n k a) = trivialField L n k b) (h₂ : IsOpenNhdOfOne 𝒰₂) :
    IsOpenNhdOfOne (compositeDomain 𝒰₁ 𝒰₂ m) := by
  obtain ⟨hs₁, O₁, hO₁, e₁⟩ := (hopa 𝒰₁).1 h₁.1
  obtain ⟨-, O₂, hO₂, e₂⟩ := (hopb 𝒰₂).1 h₂.1
  obtain ⟨u, hu, hue⟩ :=
    continuousOn_iff'.1 (continuousOn_of_isAnalyticFieldMap hK hm) O₂ hO₂
  have hmem : ∀ V ∈ 𝒰₁, (m V ∈ 𝒰₂ ↔ V ∈ u) := by
    intro V hV
    have hc : m V ∈ fieldSpace L n k b := hm.2.1 hV
    constructor
    · intro h
      rw [e₂] at h
      have : V ∈ m ⁻¹' O₂ ∩ 𝒰₁ := ⟨h.1, hV⟩
      rw [hue] at this
      exact this.1
    · intro h
      have : V ∈ u ∩ 𝒰₁ := ⟨h, hV⟩
      rw [← hue] at this
      rw [e₂]
      exact ⟨this.1, hc⟩
  refine ⟨(hopa _).2 ⟨fun V hV => hs₁ hV.1, u ∩ O₁, hu.inter hO₁, ?_⟩, h₁.2, ?_⟩
  · ext V
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := h1
      rw [e₁] at h3
      exact ⟨⟨(hmem V h1).1 h2, h3.1⟩, h3.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : V ∈ 𝒰₁ := by
        rw [e₁]
        exact ⟨h2, h3⟩
      exact ⟨h4, (hmem V h4).2 h1⟩
  · change m (trivialField L n k a) ∈ 𝒰₂
    rw [hone]
    exact h₂.2
end Analytic
section Branch
variable {L n k : ℕ}
structure Hypotheses : Prop where
  branch : CriticalBranchExists
  fibreNhds : FibreNeighbourhoodsOfSteps
  twoStages : TwoStageConstraintHolds
  smoothingFibres : SmoothingFibres
  axial : AxialFunctionFacts.statement
  bondFields : BondSetFields.ProductStructureHolds
  calculus : AnalyticCalculus.AnalyticCalculusStatement
  localAnalytic : LocalAnalyticity.LocalAnalyticityStatement
  leftChart : LeftChartFacts.HoldEverywhere
  expansion : LeftChartStepExpansion
  prolongs : ProlongCompositesAndVertexLayers.Statement
  fibreForm : CriticalFibreHessianPosDef
theorem chosenCriticalBranch_isCritical (Y : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    (chosenCriticalBranch L n k).IsCritical :=
  Classical.epsilon_spec (Y.branch L n k hL hn)
theorem chosenFibreNhd_isFibreNhd (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i < k) :
    (chosenCriticalBranch L n k).IsFibreNhd i (chosenFibreNhd L n k i) :=
  Classical.epsilon_spec
    (Y.fibreNhds.2.2.2 L n k hL hn (by omega) _ (chosenCriticalBranch_isCritical Y hL hn) i hi)
theorem tendsto_chosenProlong (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i < k) :
    Tendsto (chosenProlong L n k i)
      (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
  have hb := chosenCriticalBranch_isCritical (k := k) Y hL hn
  obtain ⟨𝒰l, hl1, hl2⟩ := hb.analytic_prolong i hi
  have hcl := continuousOn_of_isAnalyticFieldMap Y.calculus hl2
  have hnear : 𝒰l ∈ 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1) :=
    eventuallyNearIdentity_of_isOpenNhdOfOne (isOpenFieldSet_iff Y.bondFields hL hn hi) hl1
  have ht := (hcl _ hl1.2).tendsto_nhdsWithin hl2.2.1
  rw [hb.prolong_trivial i hi] at ht
  exact ht.mono_left (nhdsWithin_le_of_mem hnear)
theorem tendsto_chosenProlongComp (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∀ j, j ≤ k → Tendsto (chosenProlongComp L n k j)
      (𝓝[fieldSpace L n k j] trivialField L n k j)
      (𝓝[fieldSpace L n k 0] trivialField L n k 0)
  | 0, _ => tendsto_id
  | j + 1, h => (tendsto_chosenProlongComp Y hL hn j (by omega)).comp
      (tendsto_chosenProlong Y hL hn (by omega))
theorem exists_analytic_chosenProlongComp (Y : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j + 1 ≤ k → ∃ 𝒰 : Set (Edge L n k (j + 1) → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldMap 𝒰 (chosenProlongComp L n k (j + 1))
  | 0, h => (chosenCriticalBranch_isCritical Y hL hn).analytic_prolong 0 (by omega)
  | j + 1, h => by
    have hb := chosenCriticalBranch_isCritical (k := k) Y hL hn
    obtain ⟨𝒰c, hc1, hc2⟩ := exists_analytic_chosenProlongComp Y hL hn j (by omega)
    obtain ⟨𝒰l, hl1, hl2⟩ := hb.analytic_prolong (j + 1) (by omega)
    have hd := isOpenNhdOfOne_compositeDomain Y.calculus
      (isOpenFieldSet_iff Y.bondFields hL hn h) (isOpenFieldSet_iff Y.bondFields hL hn (by omega))
      hl1 hl2 (hb.prolong_trivial (j + 1) (by omega)) hc1
    exact ⟨_, hd, isAnalyticFieldMap_comp Y.calculus hl2 hc2 hd.1⟩
theorem smoothingIter_trivialField (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∀ j, j ≤ k → smoothingIter L n k j (trivialField L n k 0) = trivialField L n k j
  | 0, _ => rfl
  | j + 1, h => by
    change smoothingStep L n k j (smoothingIter L n k j _) = _
    rw [smoothingIter_trivialField Y hL hn j (by omega)]
    exact (Y.axial L n k j hL hn (by omega)).smoothingStep_trivial
theorem exists_analytic_partialGaugedAction (Y : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ i, i + 1 ≤ k → ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldFunction 𝒰 (partialGaugedAction L n k (i + 1))
  | 0, h => by
    have hb := chosenCriticalBranch_isCritical (k := k) Y hL hn
    have hf := chosenFibreNhd_isFibreNhd (k := k) Y hL hn (i := 0) (by omega)
    have hop := isOpenFieldSet_iff (k := k) (a := 0) Y.bondFields hL hn (Nat.zero_le k)
    obtain ⟨𝒵, h𝒵, hz⟩ := exists_isOpenNhdOfOne_of_eventually hop hb.energy_bottom
    have h𝒲 := isOpenNhdOfOne_inter hop hf.isOpenNhd h𝒵
    refine ⟨_, h𝒲, isAnalyticFieldFunction_congr (isAnalyticFieldFunction_mono Y.localAnalytic
      hf.analytic_gaugeFixedEnergy h𝒲.1 inter_subset_left) ?_⟩
    intro V hV
    change (chosenCriticalBranch L n k).energy 0 V + axialFunction L n k 0 V =
      plaquetteAction L n k V + axialFunction L n k 0 V
    rw [hz V hV.2]
  | i + 1, h => by
    obtain ⟨𝒰F, hF1, hF2⟩ := exists_analytic_partialGaugedAction Y hL hn i (by omega)
    obtain ⟨𝒰g, hg1, -, hg3⟩ := (Y.axial L n k (i + 1) hL hn (by omega)).analytic_near_identity
    obtain ⟨-, -, -, -, ⟨𝒰m, hm1, -, hm3, -⟩, -, -⟩ := Y.smoothingFibres L n k i hL hn (by omega)
    have hop0 := isOpenFieldSet_iff (k := k) (a := 0) Y.bondFields hL hn (Nat.zero_le k)
    have hop1 := isOpenFieldSet_iff (k := k) (a := i + 1) Y.bondFields hL hn (by omega)
    have hd := isOpenNhdOfOne_compositeDomain Y.calculus hop0 hop1 hm1 hm3
      (smoothingIter_trivialField Y hL hn (i + 1) (by omega)) hg1
    have h𝒲 := isOpenNhdOfOne_inter hop0 hF1 hd
    exact ⟨_, h𝒲, isAnalyticFieldFunction_add Y.localAnalytic
      (isAnalyticFieldFunction_mono Y.localAnalytic hF2 h𝒲.1 inter_subset_left)
      (isAnalyticFieldFunction_mono Y.localAnalytic
        (isAnalyticFieldFunction_comp Y.calculus hm3 hg3 hd.1) h𝒲.1 inter_subset_right)⟩
theorem prolongIter_self (b : CriticalBranchData L n k) {t : ℕ}
    (W : Edge L n k t → ComplexMatrix2) : b.prolongIter (le_refl t) W = W := by
  simp [CriticalBranchData.prolongIter, Nat.leRec_self]
theorem prolongIter_succ (b : CriticalBranchData L n k) {j t : ℕ} (h : j ≤ t) (h' : j ≤ t + 1)
    (V : Edge L n k (t + 1) → ComplexMatrix2) :
    b.prolongIter h' V = b.prolongIter h (b.prolong t V) := by
  simp [CriticalBranchData.prolongIter, Nat.leRec_succ, h]
theorem kernelHessian_posDef_of_eq {a c : ℕ}
    {M M' : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k c} (h : M = M')
    {N : Set (Edge L n k a → ComplexMatrix2)} {F : (Edge L n k a → ComplexMatrix2) → ℝ}
    {x : Edge L n k a → ComplexMatrix2}
    (hp : (fibreHessianOnKernel M N F x).PosDef) : (fibreHessianOnKernel M' N F x).PosDef := by
  subst h
  exact hp
theorem constrainedGaussian_congr {a c : ℕ}
    {M M' : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k c} (h : M = M')
    {N : Set (Edge L n k a → ComplexMatrix2)} {F : (Edge L n k a → ComplexMatrix2) → ℝ}
    {x : Edge L n k a → ComplexMatrix2} :
    constrainedGaussianOnEdgeForms M (fibreHessianOnKernel M N F x) =
      constrainedGaussianOnEdgeForms M' (fibreHessianOnKernel M' N F x) := by
  subst h
  rfl
theorem leftDifferentialLinear_apply {a c : ℕ}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k c → ComplexMatrix2}
    {U : Edge L n k a → ComplexMatrix2}
    (h : ∃ T : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k c, ∀ B : edgeFormSpace L n k a,
      (T B : Edge L n k c → ComplexMatrix2) = leftDifferential m U B)
    (B : edgeFormSpace L n k a) :
    (leftDifferentialLinear m U B : Edge L n k c → ComplexMatrix2) = leftDifferential m U B :=
  Classical.epsilon_spec (p := fun T : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k c =>
    ∀ B : edgeFormSpace L n k a, (T B : Edge L n k c → ComplexMatrix2) = leftDifferential m U B) h B
theorem isRelativelyOpen_fibreWithin {a c : ℕ}
    (hop : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    {𝒲 𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k c → ComplexMatrix2}
    {W : Edge L n k c → ComplexMatrix2} (h𝒲 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒲)
    (hs : 𝒲 ⊆ 𝒰) (h𝒰 : 𝒰 ⊆ fieldSpace L n k a) :
    ComplexMatrix2.IsRelativelyOpen (fibreWithin 𝒰 m W) (fibreWithin 𝒲 m W) := by
  obtain ⟨-, O, hO, hOe⟩ := (hop 𝒲).1 h𝒲
  refine ⟨O, hO, ?_⟩
  ext V
  constructor
  · rintro ⟨hV, hVq⟩
    have h2 := hV
    rw [hOe] at h2
    exact ⟨h2.1, hs hV, hVq⟩
  · rintro ⟨hVO, hVf, hVq⟩
    refine ⟨?_, hVq⟩
    rw [hOe]
    exact ⟨hVO, h𝒰 hVf⟩
theorem partialGaugedActionAt_one (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {𝒰₀ : Set (Edge L n k 0 → ComplexMatrix2)}
    (h𝒰₀ : IsOpenNhdOfOne 𝒰₀) :
    EventuallyNearIdentity (fieldSpace L n k 1) fun W' => PartialGaugedActionAt 𝒰₀ W' := by
  have hb := chosenCriticalBranch_isCritical (k := k) Y hL hn
  have hf := chosenFibreNhd_isFibreNhd (k := k) Y hL hn (i := 0) (by omega)
  have hop := isOpenFieldSet_iff (k := k) (a := 0) Y.bondFields hL hn (Nat.zero_le k)
  have hloc := Y.fibreNhds.2.2.1 L n k 0
  obtain ⟨𝒵, h𝒵, hz⟩ := exists_isOpenNhdOfOne_of_eventually hop hb.energy_bottom
  obtain ⟨𝒲, h𝒲, s₀, s₁, s₂⟩ : ∃ 𝒲 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒲 ∧
      𝒲 ⊆ 𝒰₀ ∧ 𝒲 ⊆ chosenFibreNhd L n k 0 ∧ 𝒲 ⊆ 𝒵 :=
    ⟨_, isOpenNhdOfOne_inter hop (isOpenNhdOfOne_inter hop h𝒰₀ hf.isOpenNhd) h𝒵,
      fun _ h => h.1.1, fun _ h => h.1.2, fun _ h => h.2⟩
  have hnear := (tendsto_chosenProlong (k := k) Y hL hn (i := 0) (by omega)).eventually
    (eventuallyNearIdentity_of_isOpenNhdOfOne hop h𝒲)
  filter_upwards [hnear, Y.fibreForm L n k hL hn 0 (by omega), hb.prolong_section 0 (by omega)]
    with W' hW hform hsec
  obtain ⟨hcrit, -, -, -, hpos⟩ := hform
  obtain ⟨hq, -, -, hval⟩ := hsec
  have hNf : ComplexMatrix2.IsRelativelyOpen (chosenLevelFibre L n k 0 W')
      (fibreWithin 𝒲 (smoothingStep L n k 0) W') :=
    isRelativelyOpen_fibreWithin hop h𝒲.1 s₁ hf.isOpenNhd.1.1
  have hN0 : ComplexMatrix2.IsRelativelyOpen (fibreWithin 𝒰₀ (smoothingIter L n k 1) W')
      (fibreWithin 𝒲 (smoothingStep L n k 0) W') :=
    isRelativelyOpen_fibreWithin (m := smoothingStep L n k 0) hop h𝒲.1 s₀ h𝒰₀.1.1
  have hEq : EqOn (chosenGaugeFixedEnergy L n k 0) (partialGaugedAction L n k 1)
      (fibreWithin 𝒲 (smoothingStep L n k 0) W') := by
    intro V hV
    change (chosenCriticalBranch L n k).energy 0 V + axialFunction L n k 0 V =
      plaquetteAction L n k V + axialFunction L n k 0 V
    rw [hz V (s₂ hV.1)]
  have hy : chosenProlong L n k 0 W' ∈ fibreWithin 𝒲 (smoothingStep L n k 0) W' := ⟨hW, hq⟩
  have h1 := Y.fibreNhds.1 _ _ (fieldCurveData L n k 0) hloc _ _
    (chosenGaugeFixedEnergy L n k 0) hNf (chosenProlong L n k 0 W')
  have h2 := Y.fibreNhds.1 _ _ (fieldCurveData L n k 0) hloc _ _
    (partialGaugedAction L n k 1) hN0 (chosenProlong L n k 0 W')
  have c1 := h1.1.2 ⟨hy, hcrit⟩
  have c2 := isCriticalOn_congr hloc hEq c1
  have e1 := (h1.2 c1).2 (LinearMap.ker (constraintDifferential L n k 0 W')) (fun B => B.1.1)
  have e2 := (h2.2 c2).2 (LinearMap.ker (constraintDifferential L n k 0 W')) (fun B => B.1.1)
  have e3 := hessianForm_congr (x := chosenProlong L n k 0 W')
    (fun B : LinearMap.ker (constraintDifferential L n k 0 W') => B.1.1) hloc hEq
  have hess : partialFibreHessian L n k 1 𝒰₀ W' (chosenProlong L n k 0 W') =
      fibreHessianForm L n k 0 W' :=
    e2.symm.trans (e3.symm.trans e1)
  refine ⟨(h2.1.1 c2).2, ?_, ?_, ?_⟩
  · change (partialFibreHessian L n k 1 𝒰₀ W' (chosenProlong L n k 0 W')).PosDef
    rw [hess]
    exact hpos
  · change plaquetteAction L n k (chosenProlong L n k 0 W') +
        axialFunction L n k 0 (chosenProlong L n k 0 W') = (chosenCriticalBranch L n k).energy 1 W'
    rw [hval]
    change _ = (chosenCriticalBranch L n k).energy 0 (chosenProlong L n k 0 W') +
      axialFunction L n k 0 (chosenProlong L n k 0 W')
    rw [hz _ (s₂ hW)]
  · rw [Fin.prod_univ_one]
    change constrainedGaussianOnEdgeForms (constraintDifferential L n k 0 W')
        (partialFibreHessian L n k 1 𝒰₀ W' (chosenProlong L n k 0 W')) =
      gaussianNormaliser L n k 0 ((chosenCriticalBranch L n k).prolongIter (le_refl 1) W')
    rw [prolongIter_self, hess]
    rfl
end Branch
section Step
variable {L n k : ℕ}
theorem partialGaugedActionAt_succ (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i + 2 ≤ k)
    (ih : ∀ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 →
      EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W' => PartialGaugedActionAt 𝒰 W')
    {𝒰₀ : Set (Edge L n k 0 → ComplexMatrix2)} (h𝒰₀ : IsOpenNhdOfOne 𝒰₀) :
    EventuallyNearIdentity (fieldSpace L n k (i + 1 + 1)) fun W' => PartialGaugedActionAt 𝒰₀ W' := by
  have hb := chosenCriticalBranch_isCritical (k := k) Y hL hn
  have hf := chosenFibreNhd_isFibreNhd (k := k) Y hL hn (i := i + 1) (by omega)
  have hop0 := isOpenFieldSet_iff (k := k) (a := 0) Y.bondFields hL hn (Nat.zero_le k)
  have hop1 := isOpenFieldSet_iff (k := k) (a := i + 1) Y.bondFields hL hn (by omega)
  have hloc0 := Y.fibreNhds.2.2.1 L n k 0
  have hloc1 := Y.fibreNhds.2.2.1 L n k (i + 1)
  obtain ⟨-, -, -, ⟨𝒰q, hq1, hq2, hq3, hq4⟩, -, -, -⟩ :=
    Y.smoothingFibres L n k (i + 1) hL hn (by omega)
  obtain ⟨-, -, -, -, ⟨𝒰m, hm1, hm2, hm3, hm4⟩, -, -⟩ := Y.smoothingFibres L n k i hL hn (by omega)
  obtain ⟨𝒰g, hg1, -, hg3⟩ := (Y.axial L n k (i + 1) hL hn (by omega)).analytic_near_identity
  obtain ⟨𝒰F, hF1, hF2⟩ := exists_analytic_partialGaugedAction (n := n) (k := k) Y hL hn i (by omega)
  obtain ⟨𝒰c, hc1, hc2⟩ := exists_analytic_chosenProlongComp (n := n) (k := k) Y hL hn i (by omega)
  obtain ⟨𝒴, h𝒴, y₁, y₂, y₃⟩ : ∃ 𝒴 : Set (Edge L n k (i + 1) → ComplexMatrix2),
      IsOpenNhdOfOne 𝒴 ∧ 𝒴 ⊆ chosenFibreNhd L n k (i + 1) ∧ 𝒴 ⊆ 𝒰g ∧ 𝒴 ⊆ 𝒰q :=
    ⟨_, isOpenNhdOfOne_inter hop1
      (isOpenNhdOfOne_inter hop1 hf.isOpenNhd hg1) hq1,
      fun _ h => h.1.1, fun _ h => h.1.2, fun _ h => h.2⟩
  obtain ⟨𝒳₀, h𝒳₀, x₁, x₂, x₃⟩ : ∃ 𝒳₀ : Set (Edge L n k 0 → ComplexMatrix2),
      IsOpenNhdOfOne 𝒳₀ ∧ 𝒳₀ ⊆ 𝒰₀ ∧ 𝒳₀ ⊆ 𝒰m ∧ 𝒳₀ ⊆ 𝒰F :=
    ⟨_, isOpenNhdOfOne_inter hop0 (isOpenNhdOfOne_inter hop0 h𝒰₀ hm1) hF1,
      fun _ h => h.1.1, fun _ h => h.1.2, fun _ h => h.2⟩
  have hm𝒳₀ := isAnalyticFieldMap_mono Y.localAnalytic hm3 h𝒳₀.1 x₂
  obtain ⟨𝒳, h𝒳, z₀, z₁⟩ : ∃ 𝒳 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒳 ∧
      𝒳 ⊆ 𝒳₀ ∧ MapsTo (smoothingIter L n k (i + 1)) 𝒳 𝒴 :=
    ⟨_, isOpenNhdOfOne_compositeDomain Y.calculus hop0 hop1 h𝒳₀ hm𝒳₀
      (smoothingIter_trivialField Y hL hn (i + 1) (by omega)) h𝒴, fun _ h => h.1, fun _ h => h.2⟩
  obtain ⟨𝒰, h𝒰, hP⟩ := exists_isOpenNhdOfOne_of_eventually hop1
    ((ih 𝒳 h𝒳).and ((eventuallyNearIdentity_of_isOpenNhdOfOne hop1 h𝒴).and
      (eventuallyNearIdentity_of_isOpenNhdOfOne hop1 hc1)))
  have hdata : TwoStageData 𝒳 𝒴 𝒰 (smoothingIter L n k (i + 1)) (smoothingStep L n k (i + 1))
      (partialGaugedAction L n k (i + 1)) (chosenEnergy L n k (i + 1))
      (axialFunction L n k (i + 1)) (chosenProlongComp L n k (i + 1)) :=
    { mapsTo := z₁
      analytic_first := isAnalyticFieldMap_mono Y.localAnalytic hm3 h𝒳.1 (z₀.trans x₂)
      surjective_first := fun V hV => hm4 V (x₂ (z₀ hV))
      analytic_second := isAnalyticFieldMap_mono Y.localAnalytic hq3 h𝒴.1 y₃
      surjective_second := fun V hV => hq4 V (y₃ hV)
      analytic_fn := isAnalyticFieldFunction_mono Y.localAnalytic hF2 h𝒳.1 (z₀.trans x₃)
      analytic_add := isAnalyticFieldFunction_mono Y.localAnalytic hg3 h𝒴.1 y₂
      subset := fun y hy => (hP y hy).2.1
      analytic_section :=
        isAnalyticFieldMap_mono Y.localAnalytic hc2 h𝒰.1 fun y hy => (hP y hy).2.2
      section_mapsTo := fun y hy => (hP y hy).1.isCritical.1.1
      section_right_inv := fun y hy => (hP y hy).1.isCritical.1.2
      value_eq := fun y hy => (hP y hy).1.value_eq.symm
      critical := fun y hy => (hP y hy).1.isCritical
      posDef := fun y hy => (hP y hy).1.hessian_posDef }
  have hLin := (Y.prolongs.1 L n k hL hn (by omega)).2.1
  have hlift := tendsto_chosenProlong (k := k) Y hL hn (i := i + 1) (by omega)
  have hy := hlift.eventually (eventuallyNearIdentity_of_isOpenNhdOfOne hop1 h𝒰)
  have hyE := hlift.eventually (Y.expansion L n k (i + 1) hL hn (by omega))
  have hx := (tendsto_chosenProlongComp (k := k) Y hL hn (i + 2) (by omega)).eventually
    ((hLin.iterDifferential_linear (i + 1) (by omega)).and
      (hLin.iterDifferential_linear (i + 2) (by omega)))
  filter_upwards [hy, hyE, hx, Y.fibreForm L n k hL hn (i + 1) (by omega),
    hb.prolong_section (i + 1) (by omega)] with W' hWy hWe hWx hform hsec
  obtain ⟨hcrit, -, -, -, hpos⟩ := hform
  obtain ⟨hq, -, -, hval⟩ := hsec
  replace hq : smoothingStep L n k (i + 1) (chosenProlong L n k (i + 1) W') = W' := hq
  obtain ⟨hP₁, hP₂, -⟩ := hP _ hWy
  have hmx : smoothingIter L n k (i + 1)
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) =
        chosenProlong L n k (i + 1) W' := hP₁.isCritical.1.2
  have hset : fibreWithin 𝒴 (smoothingStep L n k (i + 1))
      (smoothingStep L n k (i + 1) (chosenProlong L n k (i + 1) W')) ∩ 𝒰 =
      fibreWithin 𝒰 (smoothingStep L n k (i + 1)) W' := by
    ext V
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, h2.trans hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(hP V h1).2.1, h2.trans hq.symm⟩, h1⟩
  have hNf : ComplexMatrix2.IsRelativelyOpen (chosenLevelFibre L n k (i + 1) W')
      (fibreWithin 𝒰 (smoothingStep L n k (i + 1)) W') :=
    isRelativelyOpen_fibreWithin hop1 h𝒰.1 (fun V h => y₁ (hP V h).2.1) hf.isOpenNhd.1.1
  have hymem : chosenProlong L n k (i + 1) W' ∈
      fibreWithin 𝒰 (smoothingStep L n k (i + 1)) W' := ⟨hWy, hq⟩
  have h1 := Y.fibreNhds.1 _ _ (fieldCurveData L n k (i + 1)) hloc1 _ _
    (chosenGaugeFixedEnergy L n k (i + 1)) hNf (chosenProlong L n k (i + 1) W')
  have c1 := h1.1.2 ⟨hymem, hcrit⟩
  have e1 := (h1.2 c1).2 (LinearMap.ker (constraintDifferential L n k (i + 1) W')) (fun B => B.1.1)
  have cy : (fieldCurveData L n k (i + 1)).IsCriticalOn
      (fibreWithin 𝒴 (smoothingStep L n k (i + 1))
        (smoothingStep L n k (i + 1) (chosenProlong L n k (i + 1) W')) ∩ 𝒰)
      (fun y => chosenEnergy L n k (i + 1) y + axialFunction L n k (i + 1) y)
      (chosenProlong L n k (i + 1) W') := by
    rw [hset]
    exact c1
  have hK₂ : fibreHessianOnKernel
      (leftDifferentialLinear (smoothingStep L n k (i + 1)) (chosenProlong L n k (i + 1) W'))
      (fibreWithin 𝒴 (smoothingStep L n k (i + 1))
        (smoothingStep L n k (i + 1) (chosenProlong L n k (i + 1) W')) ∩ 𝒰)
      (fun y => chosenEnergy L n k (i + 1) y + axialFunction L n k (i + 1) y)
      (chosenProlong L n k (i + 1) W') =
      fibreHessianForm L n k (i + 1) W' := by
    rw [hset]
    exact e1
  have py : (fibreHessianOnKernel
      (leftDifferentialLinear (smoothingStep L n k (i + 1)) (chosenProlong L n k (i + 1) W'))
      (fibreWithin 𝒴 (smoothingStep L n k (i + 1))
        (smoothingStep L n k (i + 1) (chosenProlong L n k (i + 1) W')) ∩ 𝒰)
      (fun y => chosenEnergy L n k (i + 1) y + axialFunction L n k (i + 1) y)
      (chosenProlong L n k (i + 1) W')).PosDef := by
    rw [hK₂]
    exact hpos
  obtain ⟨t1, t2, t3⟩ := Y.twoStages L n k 0 (i + 1) (i + 2) hL hn (Nat.zero_le k) (by omega)
    (by omega) 𝒳 𝒴 𝒰 _ _ _ _ _ _ (chosenProlong L n k (i + 1) W') hdata hWy cy py
  have hPset : fibreWithin 𝒳 (smoothingStep L n k (i + 1) ∘ smoothingIter L n k (i + 1))
      (smoothingStep L n k (i + 1) (chosenProlong L n k (i + 1) W')) =
      fibreWithin 𝒳 (smoothingIter L n k (i + 2)) W' := by
    rw [hq]
    rfl
  have t1' : (fieldCurveData L n k 0).IsCriticalOn
      (fibreWithin 𝒳 (smoothingIter L n k (i + 2)) W') (partialGaugedAction L n k (i + 2))
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) := by
    rw [← hPset]
    exact t1
  have hX : ComplexMatrix2.IsRelativelyOpen (fibreWithin 𝒰₀ (smoothingIter L n k (i + 2)) W')
      (fibreWithin 𝒳 (smoothingIter L n k (i + 2)) W') :=
    isRelativelyOpen_fibreWithin hop0 h𝒳.1 (z₀.trans x₁) h𝒰₀.1.1
  have h2 := Y.fibreNhds.1 _ _ (fieldCurveData L n k 0) hloc0 _ _
    (partialGaugedAction L n k (i + 2)) hX
    (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))
  have hD : (leftDifferentialLinear (smoothingStep L n k (i + 1))
        (chosenProlong L n k (i + 1) W')) ∘ₗ
      (leftDifferentialLinear (smoothingIter L n k (i + 1))
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) =
      smoothingIterDifferential L n k (i + 2)
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) := by
    obtain ⟨-, hTy, -⟩ := hWe.2.1
    obtain ⟨hT₁, hT₂⟩ := hWx
    refine LinearMap.ext fun B => Subtype.ext ?_
    have hchain := (((Y.leftChart L k 0 (i + 1) (i + 2) hL (Nat.zero_le k) (by omega)
      (by omega)).2.1 n hn).2.2.1.1 𝒰m 𝒰q _ _ hm2 hq2).2
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))
      ⟨x₂ (z₀ hP₁.isCritical.1.1), by
        change smoothingIter L n k (i + 1)
          (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) ∈ 𝒰q
        rw [hmx]
        exact y₃ hP₂⟩ B.1 B.2
    have s₁ := leftDifferentialLinear_apply hTy
      ((leftDifferentialLinear (smoothingIter L n k (i + 1))
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) B)
    have s₂ := leftDifferentialLinear_apply hT₁ B
    have s₃ := leftDifferentialLinear_apply hT₂ B
    rw [hmx] at hchain
    change ((leftDifferentialLinear (smoothingStep L n k (i + 1)) (chosenProlong L n k (i + 1) W'))
        ((leftDifferentialLinear (smoothingIter L n k (i + 1))
          (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) B) :
          Edge L n k (i + 2) → ComplexMatrix2) =
      (leftDifferentialLinear (smoothingIter L n k (i + 2))
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) B :
          Edge L n k (i + 2) → ComplexMatrix2)
    rw [s₁]
    refine Eq.trans ?_ s₃.symm
    refine Eq.trans ?_ hchain.symm
    exact congrArg (leftDifferential (smoothingStep L n k (i + 1))
      (chosenProlong L n k (i + 1) W')) s₂
  have e2 := (h2.2 t1').2 (LinearMap.ker (smoothingIterDifferential L n k (i + 2)
    (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))) (fun B => B.1.1)
  have t2' : (fibreHessianOnKernel (smoothingIterDifferential L n k (i + 2)
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))
      (fibreWithin 𝒳 (smoothingIter L n k (i + 2)) W') (partialGaugedAction L n k (i + 2))
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))).PosDef := by
    rw [← hPset]
    exact kernelHessian_posDef_of_eq hD t2
  have hH : fibreHessianOnKernel (smoothingIterDifferential L n k (i + 2)
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))
      (fibreWithin 𝒳 (smoothingIter L n k (i + 2)) W') (partialGaugedAction L n k (i + 2))
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) =
      partialFibreHessian L n k (i + 2) 𝒰₀ W'
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) := e2
  have hnum : constrainedGaussianOnEdgeForms (smoothingIterDifferential L n k (i + 2)
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))
      (partialFibreHessian L n k (i + 2) 𝒰₀ W'
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) =
      constrainedGaussianOnEdgeForms (leftDifferentialLinear (smoothingIter L n k (i + 1))
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))
        (fibreHessianOnKernel (leftDifferentialLinear (smoothingIter L n k (i + 1))
          (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))
          (fibreWithin 𝒳 (smoothingIter L n k (i + 1)) (chosenProlong L n k (i + 1) W'))
          (partialGaugedAction L n k (i + 1))
          (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) *
        gaussianNormaliser L n k (i + 1) W' := by
    rw [← hH]
    have t3' := t3
    rw [hPset, hK₂] at t3'
    exact (constrainedGaussian_congr hD).symm.trans t3'
  refine ⟨(h2.1.1 t1').2, ?_, ?_, ?_⟩
  · change (partialFibreHessian L n k (i + 2) 𝒰₀ W'
      (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))).PosDef
    rw [← hH]
    exact t2'
  · change partialGaugedAction L n k (i + 1)
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')) +
      axialFunction L n k (i + 1) (smoothingIter L n k (i + 1)
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) =
      (chosenCriticalBranch L n k).energy (i + 2) W'
    rw [hP₁.value_eq, hmx, hval]
    rfl
  · change constrainedGaussianOnEdgeForms (smoothingIterDifferential L n k (i + 2)
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W')))
      (partialFibreHessian L n k (i + 2) 𝒰₀ W'
        (chosenProlongComp L n k (i + 1) (chosenProlong L n k (i + 1) W'))) = _
    rw [hnum, Fin.prod_univ_castSucc]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine hP₁.gaussian_eq.trans (Finset.prod_congr rfl fun j _ => ?_)
      exact congrArg _ (prolongIter_succ _ _ _ _).symm
    · change gaussianNormaliser L n k (i + 1) W' =
        gaussianNormaliser L n k (i + 1)
          ((chosenCriticalBranch L n k).prolongIter (le_refl (i + 2)) W')
      rw [prolongIter_self]
end Step
end PartialGaugedActionProof
open PartialGaugedActionProof in
theorem partialGaugedActionsHold_of_hypotheses (hBranch : CriticalBranchExists)
    (hNeighbourhood : FibreNeighbourhoodsOfSteps)
    (hTwoStages : TwoStageConstraintHolds)
    (hFibres : SmoothingFibres)
    (hAxial : AxialFunctionFacts.statement)
    (hBondFields : BondSetFields.ProductStructureHolds)
    (hCalculus : AnalyticCalculus.AnalyticCalculusStatement)
    (hLocal : LocalAnalyticity.LocalAnalyticityStatement)
    (hLeftChart : LeftChartFacts.HoldEverywhere)
    (hExpansion : LeftChartStepExpansion)
    (hProlongs : ProlongCompositesAndVertexLayers.Statement)
    (hForm : CriticalFibreHessianPosDef) :
    PartialGaugedActionsHold := by
  have Y : Hypotheses := ⟨hBranch, hNeighbourhood, hTwoStages, hFibres, hAxial, hBondFields,
    hCalculus, hLocal, hLeftChart, hExpansion, hProlongs, hForm⟩
  intro L n k i hL hn h1 hik
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  clear h1
  induction i with
  | zero =>
    intro 𝒰 h𝒰
    exact partialGaugedActionAt_one Y hL hn hik h𝒰
  | succ i ih =>
    intro 𝒰 h𝒰
    exact partialGaugedActionAt_succ Y hL hn hik (fun 𝒰' h' => ih (by omega) 𝒰' h') h𝒰
end YangMills.Construction.Tower
end
