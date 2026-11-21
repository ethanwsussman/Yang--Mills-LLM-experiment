import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOneProof
import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASideProof
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersionProof
import YangMills.Construction.Towers.QuadraticFormOfAStepOfTheBranchProof
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOne
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.CompositeSecondOrder
section Calculus
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
theorem hasDerivAt_smul_line {ψ : V → W} (h : DifferentiableAt ℝ ψ 0) (u : V) :
    HasDerivAt (fun t : ℝ => ψ (t • u)) (fderiv ℝ ψ 0 u) 0 := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.hasDerivAt_comp_smul_line <;> assumption
theorem eventually_differentiableAt_of_contDiffAt_two {ψ : V → W} (h : ContDiffAt ℝ 2 ψ 0) :
    ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt ℝ ψ y :=
  (h.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)
theorem differentiableAt_fderiv_of_contDiffAt_two {ψ : V → W} (h : ContDiffAt ℝ 2 ψ 0) :
    DifferentiableAt ℝ (fderiv ℝ ψ) 0 :=
  (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
theorem deriv_deriv_plane_eq {ψ : V → ℝ} (h : ContDiffAt ℝ 2 ψ 0) (u v : V) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => ψ (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ ψ) 0 u v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
variable {φ : W → ℝ} {ξ : V → W}
theorem fderiv_comp_at_zero (hφ : ContDiffAt ℝ 2 φ 0) (hξ : ContDiffAt ℝ 2 ξ 0) (h0 : ξ 0 = 0) :
    fderiv ℝ (fun y => φ (ξ y)) 0 = (fderiv ℝ φ 0).comp (fderiv ℝ ξ 0) := by
  have a : DifferentiableAt ℝ φ (ξ 0) := by
    rw [h0]
    exact hφ.differentiableAt (by norm_num)
  have h := fderiv_comp (0 : V) a (hξ.differentiableAt (by norm_num))
  rw [h0] at h
  exact h
theorem fderiv_fderiv_comp_at_zero (hφ : ContDiffAt ℝ 2 φ 0) (hξ : ContDiffAt ℝ 2 ξ 0)
    (h0 : ξ 0 = 0) (hD : fderiv ℝ φ 0 = 0) (u v : V) :
    fderiv ℝ (fderiv ℝ fun y => φ (ξ y)) 0 u v =
      fderiv ℝ (fderiv ℝ φ) 0 (fderiv ℝ ξ 0 u) (fderiv ℝ ξ 0 v) := by
  have ht : Tendsto ξ (𝓝 0) (𝓝 (0 : W)) := by
    have := hξ.continuousAt.tendsto
    rwa [h0] at this
  have e : (fderiv ℝ fun y => φ (ξ y)) =ᶠ[𝓝 0]
      fun y => (fderiv ℝ φ (ξ y)).comp (fderiv ℝ ξ y) := by
    filter_upwards [ht.eventually (eventually_differentiableAt_of_contDiffAt_two hφ),
      eventually_differentiableAt_of_contDiffAt_two hξ] with y a b
    exact fderiv_comp y a b
  rw [e.fderiv_eq]
  have h1 : HasFDerivAt (fun y => fderiv ℝ φ (ξ y))
      ((fderiv ℝ (fderiv ℝ φ) 0).comp (fderiv ℝ ξ 0)) 0 := by
    have a : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) 0) (ξ 0) := by
      rw [h0]
      exact (differentiableAt_fderiv_of_contDiffAt_two hφ).hasFDerivAt
    exact a.comp (0 : V) (hξ.differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ ξ) (fderiv ℝ (fderiv ℝ ξ) 0) 0 :=
    (differentiableAt_fderiv_of_contDiffAt_two hξ).hasFDerivAt
  rw [(h1.clm_comp h2).fderiv]
  simp [h0, hD]
end Calculus
section Edges
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem opposite_not_positive (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) (b : Edge L n k j) (h : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p24505 <;> assumption
theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem trivialField_mem (j : ℕ) :
    trivialField L n k j ∈ fieldSpace L n k j :=
  ⟨fun _ _ => one_mem _, fun _ _ => by simp [trivialField]⟩
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
theorem nonempty_positiveEdge (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
theorem exists_projection_lieElement :
    ∃ P : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ Y : ComplexMatrix2.LieElement, P Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
def edgeLieValues :
    edgeFormSpace L n k j →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2.LieElement) where
  toFun B s := (⟨(B : Edge L n k j → ComplexMatrix2) s.1, B.2.1 s.1 s.2⟩ :
    ComplexMatrix2.hermitianTraceless)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def fieldOfLieValues (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b => open Classical in
    if h : b.IsPositivelyOriented then (y ⟨b, h⟩).toMatrix else 0
theorem fieldOfLieValues_apply_positive (y : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    fieldOfLieValues y b = (y ⟨b, h⟩).toMatrix := by apply _root_.YangMills.Construction.Tower.IdentityChart.ofValues_of_positive <;> assumption
theorem fieldOfLieValues_mem
    (hnr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    fieldOfLieValues y ∈ edgeFormSpace L n k j := by
  refine ⟨fun b h => ?_, fun b => ?_⟩
  · rw [fieldOfLieValues_apply_positive y h]
    exact (y ⟨b, h⟩).2
  · by_cases h : b.IsPositivelyOriented
    · have h' := hnr b h
      simp [fieldOfLieValues, extendOddly, h, h', opposite_opposite]
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      simp [fieldOfLieValues, extendOddly, h, h']
def formOfLieValues
    (hnr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) : edgeFormSpace L n k j :=
  ⟨fieldOfLieValues y, fieldOfLieValues_mem hnr y⟩
theorem edgeLieValues_formOfLieValues
    (hnr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    edgeLieValues (formOfLieValues hnr y) = y := by
  funext ⟨b, h⟩
  apply Subtype.ext
  exact fieldOfLieValues_apply_positive y h
theorem extendOddly_congr {f f' : Edge L n k j → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → f b = f' b) : extendOddly f = extendOddly f' := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
theorem expTwist_trivial_eq [Fintype (PositiveEdge L n k j)] (B : edgeFormSpace L n k j) :
    PeriodicLattice.expTwist (B : Edge L n k j → ComplexMatrix2) (trivialField L n k j) =
      fieldOfPositiveValues
        (expChartI (restrictToPositiveEdges (trivialField L n k j)) (edgeLieValues B)) := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, fieldOfPositiveValues, if_pos h, dif_pos h]
    rfl
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [PeriodicLattice.expTwist, fieldOfPositiveValues, if_neg h, dif_neg h, dif_pos h']
    rfl
end Edges
section Analyticity
variable {L n k a b : ℕ}
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k)
    (𝒰 : Set (Edge L n k a → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰 := by
  have A := ((hE L hL k a ha).1 n hn).2.2.2.2.2.2.2.2.1
  exact ⟨fun h => ⟨h.1, (A 𝒰 h.1).2 h.2⟩, fun h => ⟨h.1, (A 𝒰 h.1).1 h.2⟩⟩
theorem continuousOn_of_isAnalyticFieldMap (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousOn_of_isAnalyticFieldMap <;> assumption
theorem isSubspaceAnalyticToCoords_congr {S R : Type} [Fintype S] [Fintype R] {l : ℕ}
    {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {f g : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l} (h𝒲 : 𝒲 = 𝒲')
    (hfg : EqOn f g 𝒲) (hf : IsSubspaceAnalyticToCoords E 𝒲 f) :
    IsSubspaceAnalyticToCoords E 𝒲' g := by
  subst h𝒲
  refine ⟨hf.1, fun p hp => ?_⟩
  obtain ⟨𝒳, hp𝒳, hO, hsub, Φ, hΦ, heq⟩ := hf.2 p hp
  exact ⟨𝒳, hp𝒳, hO, hsub, Φ, hΦ, fun q hq => (heq hq).trans (hfg (hsub hq))⟩
theorem isAnalyticFieldFunction_comp (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {g : (Edge L n k b → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldMap 𝒰₁ m) (h₂ : IsAnalyticFieldFunction 𝒰₂ g)
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰₁ ∩ m ⁻¹' 𝒰₂)) :
    IsAnalyticFieldFunction (𝒰₁ ∩ m ⁻¹' 𝒰₂) fun W => g (m W) := by
  obtain ⟨-, hmap₁, i₀, i₁, hA₁⟩ := h₁
  obtain ⟨-, i₁', hA₂⟩ := h₂
  obtain rfl : i₁' = i₁ := Subsingleton.elim _ _
  refine ⟨hopen, i₀, ?_⟩
  have hback : ∀ q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2,
      fieldOfPositiveValues (groupComponent q) ∈ 𝒰₁ →
      fieldOfPositiveValues (restrictToPositiveEdges
          (m (fieldOfPositiveValues (groupComponent q)))) =
        m (fieldOfPositiveValues (groupComponent q)) :=
    fun q hq => fieldOfPositiveValues_restrict (hmap₁ hq)
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
theorem mem_nhdsWithin_trivialField (hop : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    𝒰 ∈ 𝓝[fieldSpace L n k a] trivialField L n k a := by
  obtain ⟨-, O, hO, heq⟩ := (hop 𝒰).1 h.1
  have h1 := h.2
  rw [heq] at h1
  refine mem_nhdsWithin.2 ⟨O, hO, h1.1, fun V hV => ?_⟩
  rw [heq]
  exact hV
theorem isOpenNhdOfOne_inter_preimage
    (hopa : ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰)
    (hopb : ∀ 𝒰 : Set (Edge L n k b → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k b ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k b) 𝒰)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h₁ : IsOpenNhdOfOne 𝒰₁)
    (hcont : ContinuousOn m 𝒰₁) (hmaps : MapsTo m 𝒰₁ (fieldSpace L n k b))
    (hone : m (trivialField L n k a) = trivialField L n k b)
    (h₂ : IsOpenNhdOfOne 𝒰₂) : IsOpenNhdOfOne (𝒰₁ ∩ m ⁻¹' 𝒰₂) := by
  obtain ⟨hs₁, O₁, hO₁, e₁⟩ := (hopa 𝒰₁).1 h₁.1
  obtain ⟨-, O₂, hO₂, e₂⟩ := (hopb 𝒰₂).1 h₂.1
  obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 hcont O₂ hO₂
  refine ⟨(hopa _).2 ⟨fun V hV => hs₁ hV.1, u ∩ O₁, hu.inter hO₁, ?_⟩, h₁.2, ?_⟩
  · ext V
    constructor
    · rintro ⟨hV₁, hV₂⟩
      have h3 : m V ∈ O₂ := by
        have : m V ∈ 𝒰₂ := hV₂
        rw [e₂] at this
        exact this.1
      have h4 : V ∈ u ∩ 𝒰₁ := by
        rw [← hue]
        exact ⟨h3, hV₁⟩
      have h5 : V ∈ O₁ ∩ fieldSpace L n k a := by
        rw [← e₁]
        exact hV₁
      exact ⟨⟨h4.1, h5.1⟩, h5.2⟩
    · rintro ⟨⟨hVu, hVO⟩, hVc⟩
      have hV₁ : V ∈ 𝒰₁ := by
        rw [e₁]
        exact ⟨hVO, hVc⟩
      have h4 : V ∈ m ⁻¹' O₂ ∩ 𝒰₁ := by
        rw [hue]
        exact ⟨hVu, hV₁⟩
      refine ⟨hV₁, ?_⟩
      show m V ∈ 𝒰₂
      rw [e₂]
      exact ⟨h4.1, hmaps hV₁⟩
  · show m _ ∈ 𝒰₂
    rw [hone]
    exact h₂.2
end Analyticity
section BlockEvaluations
variable {L n k j : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
def IsChartObservable (T : edgeFormSpace L n k j →ₗ[ℝ] W)
    (G : (Edge L n k j → ComplexMatrix2) → ℝ) (ψ : W → ℝ) : Prop :=
  ContDiffAt ℝ 2 ψ 0 ∧ ∀ᶠ y in 𝓝 (0 : W), ∀ B : edgeFormSpace L n k j, T B = y →
    G (PeriodicLattice.expTwist (B : Edge L n k j → ComplexMatrix2) (trivialField L n k j)) =
      ψ y
variable {T : edgeFormSpace L n k j →ₗ[ℝ] W} {G : (Edge L n k j → ComplexMatrix2) → ℝ}
  {ψ : W → ℝ}
theorem eventually_plane_eq (hψ : IsChartObservable T G ψ) (B B' : edgeFormSpace L n k j) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ᶠ t : ℝ in 𝓝 0,
      G (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • (B : Edge L n k j → ComplexMatrix2) +
        algebraMap ℝ ℂ t • (B' : Edge L n k j → ComplexMatrix2)) (trivialField L n k j)) =
      ψ (s • T B + t • T B') := by
  have hc : Tendsto (fun q : ℝ × ℝ => q.1 • T B + q.2 • T B') (𝓝 (0, 0)) (𝓝 (0 : W)) := by
    have : Continuous fun q : ℝ × ℝ => q.1 • T B + q.2 • T B' := by fun_prop
    simpa using this.tendsto (0, 0)
  have h := hc.eventually hψ.2
  rw [nhds_prod_eq] at h
  refine h.curry.mono fun s hs => hs.mono fun t ht => ?_
  have e : algebraMap ℝ ℂ s • (B : Edge L n k j → ComplexMatrix2) +
      algebraMap ℝ ℂ t • (B' : Edge L n k j → ComplexMatrix2) =
      ((s • B + t • B' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) := by
    rw [algebraMap_smul, algebraMap_smul]
    rfl
  rw [e]
  exact ht _ (by rw [map_add, map_smul, map_smul])
theorem leftSecondDeriv_trivial_eq (hψ : IsChartObservable T G ψ) (B B' : edgeFormSpace L n k j) :
    leftSecondDeriv G (trivialField L n k j) (B : Edge L n k j → ComplexMatrix2)
        (B' : Edge L n k j → ComplexMatrix2) = fderiv ℝ (fderiv ℝ ψ) 0 (T B) (T B') := by
  rw [← deriv_deriv_plane_eq hψ.1]
  show deriv (fun s : ℝ => deriv (fun t : ℝ => G (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ s • (B : Edge L n k j → ComplexMatrix2) +
      algebraMap ℝ ℂ t • (B' : Edge L n k j → ComplexMatrix2))
    (trivialField L n k j))) 0) 0 = _
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_plane_eq hψ B B'] with s hs
  exact Filter.EventuallyEq.deriv_eq hs
theorem leftDeriv_trivial_eq (hψ : IsChartObservable T G ψ) (B : edgeFormSpace L n k j) :
    leftDeriv (fun V => (G V : ℂ)) (trivialField L n k j)
        (B : Edge L n k j → ComplexMatrix2) = ((fderiv ℝ ψ 0 (T B) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ ψ 0 := hψ.1.differentiableAt (by norm_num)
  have h2 : HasDerivAt (fun t : ℝ => ((ψ (t • T B) : ℝ) : ℂ))
      ((fderiv ℝ ψ 0 (T B) : ℝ) : ℂ) 0 :=
    (hasDerivAt_smul_line hd (T B)).ofReal_comp
  have hline : Tendsto (fun t : ℝ => t • T B) (𝓝 0) (𝓝 (0 : W)) := by
    have : Continuous fun t : ℝ => t • T B := by fun_prop
    simpa using this.tendsto 0
  have e : (fun t : ℝ => ((G (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ t • (B : Edge L n k j → ComplexMatrix2))
      (trivialField L n k j)) : ℝ) : ℂ)) =ᶠ[𝓝 0] fun t => ((ψ (t • T B) : ℝ) : ℂ) := by
    filter_upwards [hline.eventually hψ.2] with t ht
    have e₁ : algebraMap ℝ ℂ t • (B : Edge L n k j → ComplexMatrix2) =
        ((t • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) := by
      rw [algebraMap_smul]
      rfl
    rw [e₁, ht _ (map_smul T t B)]
  show deriv (fun t : ℝ => ((G (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • (B : Edge L n k j → ComplexMatrix2)) (trivialField L n k j)) : ℝ) : ℂ))
    0 = _
  rw [e.deriv_eq]
  exact h2.deriv
theorem exists_chartCoordinates [inst : Fintype (PositiveEdge L n k j)]
    (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h1 : trivialField L n k j ∈ 𝒰) (hF : IsAnalyticFieldFunction 𝒰 F) :
    ∃ ψ, IsChartObservable (edgeLieValues (L := L) (n := n) (k := k) (j := j)) F ψ := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  obtain rfl : f₁ = inst := Subsingleton.elim _ _
  have := nonempty_positiveEdge hE hL hn hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨-, -, -, -, -, -, -, hread⟩ := hC (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  let p₀ : PositiveEdge L n k j → ComplexMatrix2 := restrictToPositiveEdges (trivialField L n k j)
  obtain ⟨Nb, hNb, -, hsm, -⟩ :=
    (((hread β).1 _ hO).1 f hrest).1.1 p₀ ⟨_, h1, rfl⟩
  refine ⟨f ∘ expChartI p₀, (hsm.contDiffAt hNb).of_le ENat.LEInfty.out,
    Eventually.of_forall fun y B hB => ?_⟩
  show F _ = F _
  rw [expTwist_trivial_eq B, hB]
theorem exists_inner_eq {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] (ℓ : edgeFormSpace L n k j →ₗ[ℝ] ℝ) :
    ∃ X : edgeFormSpace L n k j, ∀ B, c.inner X B = ℓ B := by apply _root_.YangMills.Construction.Tower.StepQuadraticFormProof.exists_inner_eq <;> assumption
theorem isLeftGradient_leftGradient {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] (hψ : IsChartObservable T G ψ) :
    IsLeftGradient (fieldSpace L n k j) (fun V => (G V : ℂ)) (trivialField L n k j)
      (leftGradient (fieldSpace L n k j) (fun V => (G V : ℂ)) (trivialField L n k j)) := by
  obtain ⟨X, hX⟩ := exists_inner_eq (c := c) ((fderiv ℝ ψ 0 : W →ₗ[ℝ] ℝ) ∘ₗ T)
  refine Classical.epsilon_spec (p := IsLeftGradient (fieldSpace L n k j) _ _)
    ⟨(X : Edge L n k j → ComplexMatrix2), ⟨fun b hb => (X.2.1 b hb).2, X.2.2⟩, fun _ => X.2,
      fun B hB _ => ?_⟩
  rw [leftDeriv_trivial_eq hψ ⟨B, hB⟩, hc X ⟨B, hB⟩, hX]
  rfl
theorem edgeFormPairing_zero_left {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    (B : edgeFormSpace L n k j) :
    edgeFormPairing (0 : Edge L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) =
      0 := by
  have e₁ := c.add_left 0 0 B
  rw [add_zero] at e₁
  have e₂ : c.inner 0 B = 0 := by linarith
  have e := hc 0 B
  rw [e₂] at e
  simpa using e
theorem fderiv_evaluation_eq_zero [Finite (PositiveEdge L n k j)]
    {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] (hψ : IsChartObservable T G ψ)
    (h0 : leftGradient (fieldSpace L n k j) (fun V => (G V : ℂ)) (trivialField L n k j) = 0)
    (B : edgeFormSpace L n k j) : fderiv ℝ ψ 0 (T B) = 0 := by
  have h₁ := (isLeftGradient_leftGradient hc hψ).2.2 B B.2 (Set.toFinite _)
  rw [h0, leftDeriv_trivial_eq hψ B, edgeFormPairing_zero_left hc B] at h₁
  exact_mod_cast h₁.symm
theorem leftGradient_eq_zero [Finite (PositiveEdge L n k j)]
    {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    (hψ : IsChartObservable T G ψ) (hD : fderiv ℝ ψ 0 = 0) :
    leftGradient (fieldSpace L n k j) (fun V => (G V : ℂ)) (trivialField L n k j) = 0 := by
  have hG : IsLeftGradient (fieldSpace L n k j) (fun V => (G V : ℂ))
      (trivialField L n k j) ((0 : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) := by
    refine ⟨⟨fun b hb => ((0 : edgeFormSpace L n k j).2.1 b hb).2,
      (0 : edgeFormSpace L n k j).2.2⟩, fun _ => (0 : edgeFormSpace L n k j).2,
      fun B hB _ => ?_⟩
    rw [leftDeriv_trivial_eq hψ ⟨B, hB⟩, hD]
    simpa using edgeFormPairing_zero_left hc ⟨B, hB⟩
  have hY : IsLeftGradient (fieldSpace L n k j) (fun V => (G V : ℂ)) (trivialField L n k j)
      (leftGradient (fieldSpace L n k j) (fun V => (G V : ℂ)) (trivialField L n k j)) :=
    Classical.epsilon_spec ⟨_, hG⟩
  have hYf : leftGradient (fieldSpace L n k j) (fun V => (G V : ℂ))
      (trivialField L n k j) ∈ edgeFormSpace L n k j :=
    hY.2.1 fun V _ => Complex.ofReal_im _
  have h1 := hY.2.2 _ hYf (Set.toFinite _)
  have h2 := leftDeriv_trivial_eq hψ ⟨_, hYf⟩
  have h3 := hc ⟨_, hYf⟩ ⟨_, hYf⟩
  have h4 : ((c.inner ⟨_, hYf⟩ ⟨_, hYf⟩ : ℝ) : ℂ) = 0 := by
    rw [← h3]
    refine h1.trans (h2.trans ?_)
    rw [hD]
    simp
  have h5 := c.definite _ (by exact_mod_cast h4)
  exact congrArg Subtype.val h5
end BlockEvaluations
section MapRestrictions
variable {L n k a b : ℕ}
theorem exists_chart_map_coords [iA : Fintype (PositiveEdge L n k a)]
    [iB : Fintype (PositiveEdge L n k b)] (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (ha : a ≤ k) (hb : b ≤ k)
    (hnr : ∀ c : Edge L n k b, c.IsPositivelyOriented → ¬ c.opposite.IsPositivelyOriented)
    {𝒲 : Set (Edge L n k a → ComplexMatrix2)}
    {p : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h1 : trivialField L n k a ∈ 𝒲) (hp : IsAnalyticFieldMap 𝒲 p)
    (hp1 : p (trivialField L n k a) = trivialField L n k b) :
    ∃ ξ : (PositiveEdge L n k a → ComplexMatrix2.LieElement) →
        PositiveEdge L n k b → ComplexMatrix2.LieElement,
      ContDiffAt ℝ 2 ξ 0 ∧ ξ 0 = 0 ∧
      ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k a → ComplexMatrix2.LieElement),
        ∀ B : edgeFormSpace L n k a, edgeLieValues B = y →
        p (PeriodicLattice.expTwist (B : Edge L n k a → ComplexMatrix2) (trivialField L n k a)) =
          PeriodicLattice.expTwist (formOfLieValues hnr (ξ y) : Edge L n k b → ComplexMatrix2)
            (trivialField L n k b) ∧
        ∀ c : PositiveEdge L n k b, (1 / Complex.I) • ComplexMatrix2.logSeries
          (p (PeriodicLattice.expTwist (B : Edge L n k a → ComplexMatrix2)
            (trivialField L n k a)) c.1) = (ξ y c).toMatrix := by
  obtain ⟨hopen, hmaps, f₁, f₂, hra⟩ := hp
  obtain rfl : f₁ = iA := Subsingleton.elim _ _
  obtain rfl : f₂ = iB := Subsingleton.elim _ _
  have := nonempty_positiveEdge hE hL hn ha
  have := nonempty_positiveEdge hE hL hn hb
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hread := ((hC (PositiveEdge L n k a) (PositiveEdge L n k b)).2.2.2.2.2.2.2 β).1
  have hchartsA := (hC (PositiveEdge L n k a) (PositiveEdge L n k b)).1
  have hchartsB := (hC (PositiveEdge L n k b) (PositiveEdge L n k a)).1
  have hconf : ∀ {U}, U ∈ 𝒲 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  let g : (PositiveEdge L n k a → ComplexMatrix2) → PositiveEdge L n k b → ComplexMatrix2 :=
    fun w => restrictToPositiveEdges (p (fieldOfPositiveValues w))
  have hinto : MapsTo g (restrictToPositiveEdges '' 𝒲)
      (specialUnitaryPower (PositiveEdge L n k b)) := by
    rintro _ ⟨U, hU, rfl⟩
    show restrictToPositiveEdges (p (fieldOfPositiveValues (restrictToPositiveEdges U))) ∈ _
    rw [hconf hU]
    exact fun c => (hmaps hU).1 c (mem_univ _)
  have hrest : IsLocallyHolomorphicRestriction
      (IsHolomorphicToProduct β) asGroupFactors (restrictToPositiveEdges '' 𝒲) g := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k a ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒲} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒲
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2.2.2 _ hq
    refine ⟨𝒳, Ψ, hp𝒳, hΨ β, ?_⟩
    rintro _ ⟨V, hV, rfl⟩ hx
    refine heq ⟨hx, ?_, ?_⟩
    · exact (Submodule.mem_bot ℝ).2 (funext fun e => e.elim)
    · exact fun c => (hopen.1 hV).1 c (mem_univ _)
  let pa : PositiveEdge L n k a → ComplexMatrix2 := restrictToPositiveEdges (trivialField L n k a)
  let pb : PositiveEdge L n k b → ComplexMatrix2 := restrictToPositiveEdges (trivialField L n k b)
  obtain ⟨N, hN, hform, hsm, -⟩ :=
    ((hread _ hopen.2).2.2.2 _ hinto hrest).1.1 pa ⟨_, h1, rfl⟩
  have hpa : pa ∈ specialUnitaryPower (PositiveEdge L n k a) :=
    fun c => (trivialField_mem (L := L) (n := n) (k := k) a).1 c (mem_univ _)
  have hpb : pb ∈ specialUnitaryPower (PositiveEdge L n k b) :=
    fun c => (trivialField_mem (L := L) (n := n) (k := k) b).1 c (mem_univ _)
  obtain ⟨-, hformA, -⟩ := hchartsA pa hpa
  obtain ⟨-, hformB, hε⟩ := hchartsB pb hpb
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hpbimg, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨P, hP⟩ := exists_projection_lieElement
  let G₁ : (PositiveEdge L n k b → ComplexMatrix2) → PositiveEdge L n k b →
      ComplexMatrix2.LieElement :=
    fun X s => P (logChart pb X s)
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0A : expChartI pa 0 = pa := by
    rw [(hformA 0).2.1]
    funext s
    simp [hz]
  have hchart0B : expChartI pb 0 = pb := by
    rw [(hformB 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : PositiveEdge L n k b → ComplexMatrix2.LieElement) ∈
      smallBall (PositiveEdge L n k b) (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  have hG₁0 : G₁ pb = 0 := by
    funext s
    have hl := congrFun (hleft 0 h0small) s
    rw [hchart0B] at hl
    show P (logChart pb pb s) = 0
    rw [hl]
    exact hP 0
  have hG₁ : ContDiffAt ℝ 2 G₁ pb := by
    have hl : ContDiffAt ℝ 2 (logChart pb) pb :=
      (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hpbimg))).of_le ENat.LEInfty.out
    exact contDiffAt_pi.2 fun s => P.contDiff.contDiffAt.comp pb (contDiffAt_pi.1 hl s)
  let Γ : (PositiveEdge L n k a → ComplexMatrix2.LieElement) → PositiveEdge L n k b →
      ComplexMatrix2 := g ∘ expChartI pa
  have hΓ : ContDiffAt ℝ 2 Γ 0 := (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  have hcOV : fieldOfPositiveValues pa = trivialField L n k a := hconf h1
  have hΓ0 : Γ 0 = pb := by
    show restrictToPositiveEdges (p (fieldOfPositiveValues (expChartI pa 0))) = pb
    rw [hchart0A, hcOV, hp1]
  have hpbΩ : pb ∈ Ω := (himg ▸ hpbimg : pb ∈ Ω ∩ _).1
  have hΓΩ : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k a → ComplexMatrix2.LieElement), Γ y ∈ Ω :=
    hΓ.continuousAt.eventually_mem (hΩ.mem_nhds (by rw [hΓ0]; exact hpbΩ))
  refine ⟨G₁ ∘ Γ, ContDiffAt.comp (0 : PositiveEdge L n k a → ComplexMatrix2.LieElement)
    (by rw [hΓ0]; exact hG₁) hΓ, ?_, ?_⟩
  · show G₁ (Γ 0) = 0
    rw [hΓ0]
    exact hG₁0
  filter_upwards [hN, hΓΩ] with y hyN hyΩ B hB
  obtain ⟨U, hU, hUe⟩ := hform hyN
  have hcU : fieldOfPositiveValues (expChartI pa y) = U := by
    rw [← hUe]
    exact hconf hU
  have hexp : PeriodicLattice.expTwist (B : Edge L n k a → ComplexMatrix2)
      (trivialField L n k a) = U := by
    have e : PeriodicLattice.expTwist (B : Edge L n k a → ComplexMatrix2)
        (trivialField L n k a) =
        fieldOfPositiveValues (expChartI pa (edgeLieValues B)) := expTwist_trivial_eq B
    rw [e, hB, hcU]
  have hΓy : Γ y = restrictToPositiveEdges (p U) := by
    show restrictToPositiveEdges (p (fieldOfPositiveValues (expChartI pa y))) = _
    rw [hcU]
  have hmem : Γ y ∈ expChartI pb '' smallBall (PositiveEdge L n k b) (Real.log (19 / 10)) := by
    rw [himg]
    refine ⟨hyΩ, ?_⟩
    rw [hΓy]
    exact fun c => (hmaps hU).1 c (mem_univ _)
  obtain ⟨Y, hY, hYc⟩ := hmem
  have hξY : (G₁ ∘ Γ) y = Y := by
    funext s
    show P (logChart pb (Γ y) s) = Y s
    rw [← hYc, hleft Y hY]
    exact hP (Y s)
  rw [hexp, hξY]
  refine ⟨?_, fun c => ?_⟩
  · have e₁ : PeriodicLattice.expTwist (formOfLieValues hnr Y : Edge L n k b → ComplexMatrix2)
        (trivialField L n k b) =
        fieldOfPositiveValues (expChartI pb (edgeLieValues (formOfLieValues hnr Y))) :=
      expTwist_trivial_eq _
    rw [e₁, edgeLieValues_formOfLieValues, hYc, hΓy, fieldOfPositiveValues_restrict (hmaps hU)]
  · have h5 := congrFun (hleft Y hY) c
    rw [hYc, hΓy] at h5
    have h6 : logChart pb (restrictToPositiveEdges (p U)) c =
        (1 / Complex.I) • ComplexMatrix2.logSeries (p U c.1) := by
      show (1 / Complex.I) • ComplexMatrix2.logSeries
        (restrictToPositiveEdges (p U) c * (1 : ComplexMatrix2)⁻¹) = _
      simp [restrictToPositiveEdges]
    rw [← h6]
    exact h5
theorem leftDifferential_trivial_eq [Fintype (PositiveEdge L n k a)]
    [Fintype (PositiveEdge L n k b)]
    (hnr : ∀ c : Edge L n k b, c.IsPositivelyOriented → ¬ c.opposite.IsPositivelyOriented)
    {p : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hp1 : p (trivialField L n k a) = trivialField L n k b)
    {ξ : (PositiveEdge L n k a → ComplexMatrix2.LieElement) →
      PositiveEdge L n k b → ComplexMatrix2.LieElement}
    (hξ : ContDiffAt ℝ 2 ξ 0)
    (hnear : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k a → ComplexMatrix2.LieElement),
      ∀ B : edgeFormSpace L n k a, edgeLieValues B = y → ∀ c : PositiveEdge L n k b,
        (1 / Complex.I) • ComplexMatrix2.logSeries (p
          (PeriodicLattice.expTwist (B : Edge L n k a → ComplexMatrix2)
            (trivialField L n k a)) c.1) = (ξ y c).toMatrix)
    (B : edgeFormSpace L n k a) :
    leftDifferential p (trivialField L n k a) (B : Edge L n k a → ComplexMatrix2) =
      (formOfLieValues hnr (fderiv ℝ ξ 0 (edgeLieValues B)) :
        Edge L n k b → ComplexMatrix2) := by
  show extendOddly _ = fieldOfLieValues _
  unfold fieldOfLieValues
  refine extendOddly_congr fun c hc => ?_
  rw [dif_pos hc]
  have hline : Tendsto (fun t : ℝ => t • edgeLieValues B) (𝓝 0)
      (𝓝 (0 : PositiveEdge L n k a → ComplexMatrix2.LieElement)) := by
    have : Continuous fun t : ℝ => t • edgeLieValues B := by fun_prop
    simpa using this.tendsto 0
  have e : (fun t : ℝ => ComplexMatrix2.logSeries (p (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ t • (B : Edge L n k a → ComplexMatrix2)) (trivialField L n k a)) c *
      (p (trivialField L n k a) c)⁻¹)) =ᶠ[𝓝 0]
      fun t => Complex.I • (ξ (t • edgeLieValues B) ⟨c, hc⟩).toMatrix := by
    filter_upwards [hline.eventually hnear] with t ht
    have e₁ : algebraMap ℝ ℂ t • (B : Edge L n k a → ComplexMatrix2) =
        ((t • B : edgeFormSpace L n k a) : Edge L n k a → ComplexMatrix2) := by
      rw [algebraMap_smul]
      rfl
    have h := ht (t • B) (map_smul edgeLieValues t B) ⟨c, hc⟩
    rw [e₁, hp1, ← h, smul_smul]
    simp [trivialField]
  have hd : HasDerivAt (fun t : ℝ => ξ (t • edgeLieValues B))
      (fderiv ℝ ξ 0 (edgeLieValues B)) 0 :=
    hasDerivAt_smul_line (hξ.differentiableAt (by norm_num)) _
  have hd2 := hasDerivAt_pi.1 hd ⟨c, hc⟩
  let M : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
    LinearMap.toContinuousLinearMap
      (ComplexMatrix2.hermitianTraceless.subtype : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2)
  have hd3 : HasDerivAt (fun t : ℝ => (ξ (t • edgeLieValues B) ⟨c, hc⟩).toMatrix)
      (fderiv ℝ ξ 0 (edgeLieValues B) ⟨c, hc⟩).toMatrix 0 :=
    M.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hd4 : HasDerivAt (fun t : ℝ => Complex.I • (ξ (t • edgeLieValues B) ⟨c, hc⟩).toMatrix)
      (Complex.I • (fderiv ℝ ξ 0 (edgeLieValues B) ⟨c, hc⟩).toMatrix) 0 :=
    hd3.const_smul Complex.I
  show Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (p (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • (B : Edge L n k a → ComplexMatrix2)) (trivialField L n k a)) c *
    (p (trivialField L n k a) c)⁻¹)) 0 = _
  rw [e.deriv_eq, hd4.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
end MapRestrictions
theorem compositeSecondOrderAtIdentity_holds (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds)
    (hK : AnalyticCalculus.AnalyticCalculusStatement)
    (hSp : FiniteSideFormSpaces) : CompositeSecondOrderAtIdentity := by
  intro L n k i hL hn hi 𝒰 𝒲 F p h𝒰 hF h𝒲 hp hp1 hgrad
  obtain ⟨hfinA, hfdA, -, cA, hcA⟩ := hSp L n k i hL hn hi.le
  obtain ⟨hfinB, hfdB, -, cB, hcB⟩ := hSp L n k (i + 1) hL hn hi
  let _ : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k (i + 1)) := Fintype.ofFinite _
  have hnr : ∀ b : Edge L n k i, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    opposite_not_positive hL hn hi.le
  have hopA := isOpenFieldSet_iff hE hL hn hi.le
  have hopB := isOpenFieldSet_iff hE hL hn hi
  obtain ⟨ψ, hψ⟩ := exists_chartCoordinates hC hE hL hn hi.le h𝒰.2 hF
  obtain ⟨ξ, hξ, hξ0, hnear⟩ := exists_chart_map_coords hC hE hL hn hi hi.le hnr h𝒲.2 hp hp1
  have hψD : fderiv ℝ ψ 0 = 0 := by
    refine ContinuousLinearMap.ext fun y => ?_
    have h := fderiv_evaluation_eq_zero hcA hψ hgrad (formOfLieValues hnr y)
    rw [edgeLieValues_formOfLieValues] at h
    simpa using h
  have ht : Tendsto ξ (𝓝 0) (𝓝 0) := by
    have := hξ.continuousAt.tendsto
    rwa [hξ0] at this
  have hcomp : IsChartObservable edgeLieValues (fun W => F (p W)) fun y => ψ (ξ y) := by
    refine ⟨ContDiffAt.comp _ (by rw [hξ0]; exact hψ.1) hξ, ?_⟩
    filter_upwards [hnear, ht.eventually hψ.2] with y h₁ h₂ B hB
    show F (p _) = _
    rw [(h₁ B hB).1]
    exact h₂ _ (edgeLieValues_formOfLieValues hnr _)
  have hD2 : fderiv ℝ (fun y => ψ (ξ y)) 0 = 0 := by
    rw [fderiv_comp_at_zero hψ.1 hξ hξ0, hψD]
    simp
  have hcont := continuousOn_of_isAnalyticFieldMap hK hp
  refine ⟨?_, ?_, leftGradient_eq_zero hcB hcomp hD2, ?_⟩
  · have hd := isOpenNhdOfOne_inter_preimage hopB hopA h𝒲 hcont hp.2.1 hp1 h𝒰
    exact ⟨_, hd, isAnalyticFieldFunction_comp hK hp hF hd.1⟩
  · intro P hP
    have hm := mem_nhdsWithin_trivialField hopB h𝒲
    have h2 := (hcont _ h𝒲.2).tendsto_nhdsWithin hp.2.1
    rw [hp1] at h2
    exact (h2.mono_left (nhdsWithin_le_of_mem hm)).eventually hP
  · intro B hB B' hB'
    have hnear' : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k (i + 1) → ComplexMatrix2.LieElement),
        ∀ B : edgeFormSpace L n k (i + 1), edgeLieValues B = y → ∀ c : PositiveEdge L n k i,
          (1 / Complex.I) • ComplexMatrix2.logSeries (p (PeriodicLattice.expTwist
            (B : Edge L n k (i + 1) → ComplexMatrix2)
            (trivialField L n k (i + 1))) c.1) = (ξ y c).toMatrix :=
      hnear.mono fun y h B hB => (h B hB).2
    have e₁ := leftDifferential_trivial_eq hnr hp1 hξ hnear' ⟨B, hB⟩
    have e₂ := leftDifferential_trivial_eq hnr hp1 hξ hnear' ⟨B', hB'⟩
    have e₃ := leftSecondDeriv_trivial_eq hcomp ⟨B, hB⟩ ⟨B', hB'⟩
    refine e₃.trans ?_
    rw [fderiv_fderiv_comp_at_zero hψ.1 hξ hξ0 hψD]
    show _ = leftSecondDeriv F _
      (leftDifferential p _ ((⟨B, hB⟩ : edgeFormSpace L n k (i + 1)) : _))
      (leftDifferential p _ ((⟨B', hB'⟩ : edgeFormSpace L n k (i + 1)) : _))
    rw [e₁, e₂, leftSecondDeriv_trivial_eq hψ, edgeLieValues_formOfLieValues,
      edgeLieValues_formOfLieValues]
end YangMills.Construction.Tower.CompositeSecondOrder
end
