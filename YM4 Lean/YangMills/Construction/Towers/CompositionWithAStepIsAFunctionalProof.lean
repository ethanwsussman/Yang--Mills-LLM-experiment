import YangMills.Construction.Towers.DilationNearTheTrivialConfigurationProof
import YangMills.Construction.Matrices.CalculusOfHolomorphicMaps
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.CompositionWithAStepIsAFunctional
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.FamilyOfACompositionIsGivenAtLargeSides
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.TheCriticalBranch
import YangMills.Construction.Towers.WhatTheDilationKeeps
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.StepComposition
open YangMills.Construction.Conventions YangMills.Construction.Matrices YangMills.Construction.Coordinates YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.Tower YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
section Relabelling
variable {σ σ' ι ι' κ κ' E : Type}
def reindexFamily (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) : σ → ComplexMatrix2 := A ∘ τ
abbrev relabelGroupFactors (r : ι ≃ ι') (κ : Type) : ι ⊕ κ ≃ ι' ⊕ κ :=
  r.sumCongr (Equiv.refl κ)
def familyOfCoords {N : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : σ ≃ Fin N)
    (w : ComplexCoordinates (N * 3)) (j : σ) : ComplexMatrix2 :=
  ComplexCoordinates.tracelessTuple b w (ν j)
theorem isSubspaceAnalyticToProduct_reindex [Fintype ι] [Fintype ι'] [Fintype κ] {R' R₂ : Type}
    (r : ι ≃ ι') (t : R' ≃ R₂) {F : Submodule ℝ (κ → ComplexMatrix2)}
    {F' : Submodule ℝ (κ' → ComplexMatrix2)}
    {𝒲 : Set (ι ⊕ κ → ComplexMatrix2)} {f : (ι ⊕ κ → ComplexMatrix2) → R' ⊕ κ' → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct F F' 𝒲 f) :
    IsSubspaceAnalyticToProduct F F' (reindexFamily (relabelGroupFactors r κ) ⁻¹' 𝒲)
      fun q => reindexFamily (relabelGroupFactors t.symm κ')
        (f (reindexFamily (relabelGroupFactors r κ) q)) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.isSubspaceAnalyticToProduct_precomp <;> assumption
end Relabelling
section Edges
variable {L n k i n₂ k₂ i₂ n₃ k₃ i₃ : ℕ}
theorem continuous_transportTotal_of_equiv {X Y : Type} (e : X ≃ Y) :
    Continuous (transportTotal e : (X → ComplexMatrix2) → Y → ComplexMatrix2) :=
  continuous_pi fun y => continuous_apply (e.symm y)
structure PreservesOrientation (e : Edge L n k i ≃ Edge L n₂ k₂ i₂) : Prop where
  isPositivelyOriented_iff : ∀ b, (e b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  map_opposite : ∀ b, e b.opposite = (e b).opposite
theorem PreservesOrientation.symm {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) : PreservesOrientation e.symm where
  isPositivelyOriented_iff b := by rw [← he.isPositivelyOriented_iff, e.apply_symm_apply]
  map_opposite b := by
    apply e.injective
    rw [he.map_opposite, e.apply_symm_apply, e.apply_symm_apply]
theorem PreservesOrientation.trans {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    {e' : Edge L n₂ k₂ i₂ ≃ Edge L n₃ k₃ i₃} (he : PreservesOrientation e)
    (he' : PreservesOrientation e') : PreservesOrientation (e.trans e') where
  isPositivelyOriented_iff b :=
    (he'.isPositivelyOriented_iff _).trans (he.isPositivelyOriented_iff b)
  map_opposite b := by
    simp only [Equiv.trans_apply]
    rw [he.map_opposite, he'.map_opposite]
def positiveEdgeEquiv {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e) :
    PositiveEdge L n k i ≃ PositiveEdge L n₂ k₂ i₂ :=
  e.subtypeEquiv fun b => (he.isPositivelyOriented_iff b).symm
theorem transportTotal_mem_fieldSpace {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ fieldSpace L n k i) :
    transportTotal e V ∈ fieldSpace L n₂ k₂ i₂ := by
  refine ⟨fun b _ => hV.1 _ (mem_univ _), fun b _ => ?_⟩
  change V (e.symm b.opposite) = (V (e.symm b))⁻¹
  rw [he.symm.map_opposite]
  exact hV.2 _ (mem_univ _)
theorem transportTotal_fieldOfPositiveValues {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (w : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :
    transportTotal e (fieldOfPositiveValues (reindexFamily (positiveEdgeEquiv he) w)) =
      fieldOfPositiveValues w := by
  funext b
  change fieldOfPositiveValues (reindexFamily (positiveEdgeEquiv he) w) (e.symm b) = _
  have hp := he.symm.isPositivelyOriented_iff b
  have hr := he.symm.isPositivelyOriented_iff b.opposite
  rw [he.symm.map_opposite] at hr
  unfold fieldOfPositiveValues
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h, dif_pos (hp.2 h)]
    exact congrArg w (Subtype.ext (e.apply_symm_apply b))
  · rw [dif_neg h, dif_neg (fun h' => h (hp.1 h'))]
    by_cases h' : b.opposite.IsPositivelyOriented
    · rw [dif_pos h', dif_pos (hr.2 h')]
      refine congrArg (· ⁻¹) (congrArg w (Subtype.ext ?_))
      change e (e.symm b).opposite = b.opposite
      rw [he.map_opposite, e.apply_symm_apply]
    · rw [dif_neg h', dif_neg (fun h'' => h' (hr.1 h''))]
theorem fieldOfPositiveValues_comp {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (w : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :
    fieldOfPositiveValues w ∘ e = fieldOfPositiveValues (reindexFamily (positiveEdgeEquiv he) w) := by
  rw [← transportTotal_fieldOfPositiveValues he w]
  funext b
  simp [transportTotal]
theorem fieldOfPositiveValues_restrict {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
end Edges
section Composite
open YangMills.Construction.Matrices.PowerExpCharts
theorem isLocallyHolomorphicRestriction_comp {P₀ P₃ : Type} [Fintype P₀] [Fintype P₃]
    (hC : HolomorphicCalculus.Properties)
    {𝒲 : Set (P₀ ⊕ Empty → ComplexMatrix2)} {Q : (P₀ ⊕ Empty → ComplexMatrix2) → P₃ ⊕ Empty → ComplexMatrix2}
    (hQ : IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) 𝒲 Q)
    {O : Set (P₃ → ComplexMatrix2)} {φ : (P₃ → ComplexMatrix2) → ℝ}
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (hφ : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal O φ)
    {O₀ : Set (P₀ → ComplexMatrix2)} {ψ : (P₀ → ComplexMatrix2) → ℝ}
    (hO₀ : ∀ x ∈ O₀, asGroupFactors x ∈ 𝒲 ∧ x ∈ compactPi P₀ ∧
      groupComponent (Q (asGroupFactors x)) ∈ O ∧
      ψ x = φ (groupComponent (Q (asGroupFactors x)))) :
    IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal O₀ ψ := by
  have hpt : ∀ q : P₃ ⊕ Empty → ComplexMatrix2, asGroupFactors (groupComponent q) = q := by
    intro q
    funext x
    cases x with
    | inl a => rfl
    | inr e => exact e.elim
  intro x hx
  obtain ⟨hx𝒲, -, hxO, -⟩ := hO₀ x hx
  obtain ⟨𝒳, hx𝒳, h𝒳, -, Ψ, hΨ, hEq⟩ := hQ.2.2.2 _ hx𝒲
  have hmem : ∀ y : P₀ → ComplexMatrix2, y ∈ compactPi P₀ →
      asGroupFactors y ∈ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) P₀ :=
    fun y hy => ⟨(Submodule.mem_bot ℝ).2 (funext fun e => e.elim), hy⟩
  have hxs := hmem x (hO₀ x hx).2.1
  obtain ⟨W, Φ, hW, hΦ, hv⟩ := hφ _ hxO
  have hcomp := (hC.1 P₀ Empty P₃ Empty) β 𝒳 Ψ h𝒳 (hΨ β) ℂ 1
    (Equiv.funUnique (Fin 1) ℂ).symm W Φ hΦ
  refine ⟨𝒳 ∩ Ψ ⁻¹' W, Φ ∘ Ψ, ⟨hx𝒳, ?_⟩, hcomp.2.2, fun y hy hyW => ?_⟩
  · change Ψ (asGroupFactors x) ∈ W
    rw [hEq ⟨hx𝒳, hxs⟩, ← hpt (Q (asGroupFactors x))]
    simpa only [hpt] using hW
  · obtain ⟨-, hyG, hyO, hψ⟩ := hO₀ y hy
    have hq := hEq ⟨hyW.1, hmem y hyG⟩
    have h₂ := hv _ hyO (by
      rw [hpt, ← hq]
      exact hyW.2)
    rw [hpt] at h₂
    change Φ (Ψ (asGroupFactors y)) = _
    rw [hq, h₂, hψ]
end Composite
section Analytic
open YangMills.Construction.Matrices.PowerExpCharts
variable {L n m k i : ℕ}
theorem isAnalyticNearIdentity_comp (hC : HolomorphicCalculus.Properties)
    (hE : BondSetFields.ProductStructureHolds) (hS : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {e₀ : Edge L n k k ≃ Edge L n 0 0} (he₀ : PreservesOrientation e₀)
    {e : Edge L n k i ≃ Edge L m 0 0} (he : PreservesOrientation e)
    {𝒰 : Set (Edge L n k k → ComplexMatrix2)} (h𝒰 : IsOpenNhdOfOne 𝒰)
    {p : (Edge L n k k → ComplexMatrix2) → Edge L n k i → ComplexMatrix2}
    (hp : IsAnalyticFieldMap 𝒰 p) (hc : ContinuousOn p 𝒰)
    (h1 : p (trivialField L n k k) = trivialField L n k i)
    {f : (UnitEdge L m → ComplexMatrix2) → ℝ} (hf : IsAnalyticNearIdentity f) :
    IsAnalyticNearIdentity fun U : UnitEdge L n → ComplexMatrix2 =>
      f (transportTotal e (p (U ∘ e₀))) := by
  obtain ⟨instF, O, ⟨O₂, hO₂, rfl⟩, h1O, hf⟩ := hf
  obtain ⟨-, hmaps, inst₁, inst₂, hRA⟩ := hp
  let inst₀ : Fintype (PositiveUnitEdge L n) := Fintype.ofEquiv _ (positiveEdgeEquiv he₀)
  obtain ⟨Ou, hOu, heq⟩ :=
    ((((hE L hS k k le_rfl).1 n hn).2.2.2.2.2.2.2.2.1) 𝒰 h𝒰.1.1).2 h𝒰.1.2
  have hψc : ContinuousOn (fun W => transportTotal e (p W)) 𝒰 :=
    (continuous_transportTotal_of_equiv e).comp_continuousOn hc
  have hT : IsOpen ((restrictToPositiveEdges :
      (Edge L m 0 0 → ComplexMatrix2) → PositiveEdge L m 0 0 → ComplexMatrix2) ⁻¹' O₂) :=
    hO₂.preimage (continuous_pi fun b => continuous_apply b.1)
  obtain ⟨V, hV, hVeq⟩ := continuousOn_iff'.1 hψc _ hT
  have hρ : Continuous fun U : Edge L n 0 0 → ComplexMatrix2 => U ∘ e₀ :=
    continuous_pi fun b => continuous_apply (e₀ b)
  have hρm : ∀ U ∈ fieldSpace L n 0 0, U ∘ e₀ ∈ fieldSpace L n k k :=
    fun U hU => transportTotal_mem_fieldSpace he₀.symm hU
  have hS₀ : ∀ U ∈ (fun U : Edge L n 0 0 → ComplexMatrix2 => U ∘ e₀) ⁻¹' (V ∩ Ou) ∩
      fieldSpace L n 0 0,
      U ∘ e₀ ∈ 𝒰 ∧ restrictToPositiveEdges (transportTotal e (p (U ∘ e₀))) ∈ O₂ := by
    rintro U ⟨⟨h₁, h₂⟩, h₃⟩
    have hU : U ∘ e₀ ∈ 𝒰 := by
      rw [heq]
      exact ⟨h₂, hρm U h₃⟩
    have h₄ : U ∘ e₀ ∈ V ∩ 𝒰 := ⟨h₁, hU⟩
    rw [← hVeq] at h₄
    exact ⟨hU, h₄.1⟩
  have himg := (((hE L hS 0 0 le_rfl).1 n hn).2.2.2.2.2.2.2.2.1
    ((fun U : Edge L n 0 0 → ComplexMatrix2 => U ∘ e₀) ⁻¹' (V ∩ Ou) ∩ fieldSpace L n 0 0)
    inter_subset_right).1 ⟨_, (hV.inter hOu).preimage hρ, rfl⟩
  refine ⟨inst₀, _, himg, ?_, fun β => ?_⟩
  · have hone : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n 0 0 :=
      ⟨fun _ _ => Submonoid.one_mem _, fun _ _ => by simp⟩
    refine ⟨fun _ => 1, ⟨?_, hone⟩, rfl⟩
    have h₄ : trivialField L n k k ∈ _ ∩ 𝒰 :=
      (⟨?_, h𝒰.2⟩ : trivialField L n k k ∈
        (fun W => transportTotal e (p W)) ⁻¹'
          ((restrictToPositiveEdges :
            (Edge L m 0 0 → ComplexMatrix2) → PositiveEdge L m 0 0 → ComplexMatrix2) ⁻¹' O₂) ∩ 𝒰)
    · rw [hVeq] at h₄
      have h₅ : trivialField L n k k ∈ Ou := by
        have := h𝒰.2
        rw [heq] at this
        exact this.1
      exact ⟨h₄.1, h₅⟩
    · change restrictToPositiveEdges (transportTotal e (p (trivialField L n k k))) ∈ O₂
      rw [h1]
      exact h1O.1
  · refine isLocallyHolomorphicRestriction_comp hC
      (isSubspaceAnalyticToProduct_reindex (positiveEdgeEquiv he₀) (positiveEdgeEquiv he) hRA)
      (hf β) ?_
    rintro _ ⟨U, hU, rfl⟩
    obtain ⟨hU𝒰, hUO⟩ := hS₀ U hU
    have hUc : U ∈ fieldSpace L n 0 0 := hU.2
    have hvx : BondSetFields.readAllPositive (k := 0) (j := 0) U = restrictToPositiveEdges U := rfl
    rw [hvx]
    have hback : fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
      fieldOfPositiveValues_restrict hUc
    have key : fieldOfPositiveValues
        (reindexFamily (positiveEdgeEquiv he₀) (restrictToPositiveEdges U)) = U ∘ e₀ := by
      rw [← fieldOfPositiveValues_comp he₀, hback]
    have hq : groupComponent (reindexFamily (relabelGroupFactors (positiveEdgeEquiv he₀) Empty)
        (asGroupFactors (restrictToPositiveEdges U))) =
        reindexFamily (positiveEdgeEquiv he₀) (restrictToPositiveEdges U) := rfl
    have hcfg : transportTotal e (p (U ∘ e₀)) ∈ fieldSpace L m 0 0 :=
      transportTotal_mem_fieldSpace he (hmaps hU𝒰)
    have hval : groupComponent (reindexFamily (relabelGroupFactors (positiveEdgeEquiv he).symm Empty)
        (ofParts (restrictToPositiveEdges (p (fieldOfPositiveValues (groupComponent
          (reindexFamily (relabelGroupFactors (positiveEdgeEquiv he₀) Empty)
            (asGroupFactors (restrictToPositiveEdges U)))))))
          Empty.elim)) = restrictToPositiveEdges (transportTotal e (p (U ∘ e₀))) := by
      rw [hq, key]
      rfl
    refine ⟨?_, fun b => hUc.1 _ (mem_univ _), ?_, ?_⟩
    · change fieldOfPositiveValues (groupComponent
        (reindexFamily (relabelGroupFactors (positiveEdgeEquiv he₀) Empty)
          (asGroupFactors (restrictToPositiveEdges U)))) ∈ 𝒰
      rw [hq, key]
      exact hU𝒰
    · rw [hval]
      exact ⟨hUO, fun b => hcfg.1 _ (mem_univ _)⟩
    · beta_reduce
      rw [hval, fieldOfPositiveValues_restrict hcfg, hback]
end Analytic
section Casts
variable {L m : ℕ} {d d' : ℤ}
abbrev edgeCast (L m : ℕ) {d d' : ℤ} (h : d = d') :
    PeriodicLattice.Bond L m d ≃ PeriodicLattice.Bond L m d' :=
  Equiv.cast (congrArg (PeriodicLattice.Bond L m) h)
abbrev vertexCast (L m : ℕ) {d d' : ℤ} (h : d = d') :
    PeriodicLattice.Site L m d ≃ PeriodicLattice.Site L m d' :=
  Equiv.cast (congrArg (PeriodicLattice.Site L m) h)
theorem edgeCast_isPositivelyOriented (h : d = d') (b : PeriodicLattice.Bond L m d) :
    (edgeCast L m h b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  subst h
  rfl
theorem edgeCast_opposite (h : d = d') (b : PeriodicLattice.Bond L m d) :
    edgeCast L m h b.opposite = (edgeCast L m h b).opposite := by
  subst h
  rfl
theorem gaugeTransform_comp_edgeCast (h : d = d') (u : PeriodicLattice.Site L m d' → ComplexMatrix2)
    (U : PeriodicLattice.Bond L m d' → ComplexMatrix2) :
    PeriodicLattice.gaugeTransform u U ∘ edgeCast L m h =
      PeriodicLattice.gaugeTransform (u ∘ vertexCast L m h) (U ∘ edgeCast L m h) := by
  subst h
  rfl
theorem transportTotal_edgeCast_gaugeTransform (h : d = d')
    (u : PeriodicLattice.Site L m d → ComplexMatrix2) (U : PeriodicLattice.Bond L m d → ComplexMatrix2) :
    transportTotal (edgeCast L m h) (PeriodicLattice.gaugeTransform u U) =
      PeriodicLattice.gaugeTransform (transportTotal (vertexCast L m h) u)
        (transportTotal (edgeCast L m h) U) := by
  subst h
  rfl
def pushFieldAtDepth (d : ℤ)
    (f : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m)
    (V : PeriodicLattice.Bond L m d → ComplexMatrix2) : PeriodicLattice.Bond L m d → ComplexMatrix2 :=
  fun b => V (Classical.epsilon fun b' : PeriodicLattice.Bond L m d =>
    b'.source = (Classical.epsilon fun x' : PeriodicLattice.Site L m d => f x' = b.source) ∧
      b'.target = (Classical.epsilon fun x' : PeriodicLattice.Site L m d => f x' = b.target))
theorem pushFieldAtDepth_comp_edgeCast (h : d = d')
    (f : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m)
    (U : PeriodicLattice.Bond L m d' → ComplexMatrix2) :
    pushFieldAtDepth d' f U ∘ edgeCast L m h = pushFieldAtDepth d f (U ∘ edgeCast L m h) := by
  subst h
  rfl
theorem transportTotal_edgeCast_pushFieldAtDepth (h : d = d')
    (f : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m)
    (U : PeriodicLattice.Bond L m d → ComplexMatrix2) :
    transportTotal (edgeCast L m h) (pushFieldAtDepth d f U) =
      pushFieldAtDepth d' f (transportTotal (edgeCast L m h) U) := by
  subst h
  rfl
theorem isAdmissibleMember_cast {L m m' : ℕ} (h : m = m') {f : (UnitEdge L m' → ComplexMatrix2) → ℝ}
    (hf : IsAdmissibleMember f) :
    IsAdmissibleMember fun U : UnitEdge L m → ComplexMatrix2 =>
      f (transportTotal (Equiv.cast (congrArg (UnitEdge L) h)) U) := by
  subst h
  exact hf
end Casts
section Member
variable {L n i : ℕ}
theorem levelDepth_self (k : ℕ) :
    PeriodicLattice.levelDepth k k = PeriodicLattice.levelDepth 0 0 := by
  simp [PeriodicLattice.levelDepth]
abbrev topVertexEquiv (L n k : ℕ) : Vertex L n k k ≃ Vertex L n 0 0 :=
  vertexCast L n (levelDepth_self k)
theorem preservesOrientation_topEdgeEquiv (L n k : ℕ) : PreservesOrientation (topEdgeEquiv L n k) :=
  ⟨edgeCast_isPositivelyOriented (levelDepth_self k), edgeCast_opposite (levelDepth_self k)⟩
def stepEdgeEquiv (hL : 0 < L) (n i : ℕ) :
    Edge L n (i + 1) i ≃ UnitEdge L (scaledExponent n (i + 1) i) :=
  (scaleEdge hL (Nat.le_succ i) i).trans (topEdgeEquiv L (scaledExponent n (i + 1) i) i)
def stepVertexEquiv (hL : 0 < L) (n i : ℕ) :
    Vertex L n (i + 1) i ≃ Vertex L (scaledExponent n (i + 1) i) 0 0 :=
  (scaleVertex hL (Nat.le_succ i) i).toEquiv.trans (topVertexEquiv L (scaledExponent n (i + 1) i) i)
def scaledGauge (hL : 0 < L) (n i : ℕ) (v : Vertex L n (i + 1) (i + 1) → ComplexMatrix2) :
    Vertex L (scaledExponent n (i + 1) i) 0 0 → ComplexMatrix2 :=
  transportTotal (stepVertexEquiv hL n i) (blockGaugeLift v)
theorem continuous_scaledGauge (hL : 0 < L) (n i : ℕ) : Continuous (scaledGauge hL n i) :=
  continuous_pi fun _ => continuous_apply _
theorem preservesOrientation_stepEdgeEquiv (hX : ScalingPropertiesStatement)
    (hS : IsAdmissibleBlockingFactor L) (hL : 0 < L) (hn : 0 < n) :
    PreservesOrientation (stepEdgeEquiv hL n i) := by
  have hat := ((hX L (i + 1) i hS (Nat.le_succ i)).1 n hn).atLevel i le_rfl
  have hd : PreservesOrientation (scaleEdge (n := n) hL (Nat.le_succ i) i) :=
    { isPositivelyOriented_iff := fun b => by
        have himg := hat.image_positive
        constructor
        · intro hb
          have hmem : scaleEdge (n := n) hL (Nat.le_succ i) i b ∈
              scaleEdge (n := n) hL (Nat.le_succ i) i '' {b | b.IsPositivelyOriented} := by
            rw [himg]
            exact hb
          obtain ⟨b', hb', hE⟩ := hmem
          rw [← (scaleEdge (n := n) hL (Nat.le_succ i) i).injective hE]
          exact hb'
        · intro hb
          have hmem : scaleEdge (n := n) hL (Nat.le_succ i) i b ∈
              scaleEdge (n := n) hL (Nat.le_succ i) i '' {b | b.IsPositivelyOriented} :=
            mem_image_of_mem _ hb
          rw [himg] at hmem
          exact hmem
      map_opposite := hat.edge_opposite }
  exact hd.trans (preservesOrientation_topEdgeEquiv _ _ _)
theorem mem_nhdsWithin_trivialField_of_isOpenNhdOfOne
    (hE : BondSetFields.ProductStructureHolds) (hL : IsAdmissibleBlockingFactor L) {n k a : ℕ}
    (hn : 0 < n) (ha : a ≤ k) {𝒰 : Set (Edge L n k a → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    𝒰 ∈ 𝓝[fieldSpace L n k a] trivialField L n k a := by
  obtain ⟨O, hO, heq⟩ :=
    ((((hE L hL k a ha).1 n hn).2.2.2.2.2.2.2.2.1) 𝒰 h.1.1).2 h.1.2
  have h1 : trivialField L n k a ∈ 𝒰 := h.2
  rw [heq] at h1
  refine mem_nhdsWithin.2 ⟨O, hO, h1.1, fun V hV => ?_⟩
  rw [heq]
  exact hV
theorem mem_complexGaugeGroup {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
theorem isGaugeField_complex {k j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V :=
  ⟨fun b hb => mem_complexGaugeGroup (hV.1 b hb), hV.2⟩
theorem isAdmissibleMember_comp (hC : HolomorphicCalculus.Properties)
    (hE : BondSetFields.ProductStructureHolds) (hK : ScalingCompatibility.Statement)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hX : ScalingPropertiesStatement)
    (hS : IsAdmissibleBlockingFactor L) (hL : 0 < L) (hn : 0 < n)
    {𝒰 : Set (Edge L n (i + 1) (i + 1) → ComplexMatrix2)} (h𝒰 : IsOpenNhdOfOne 𝒰)
    {p : (Edge L n (i + 1) (i + 1) → ComplexMatrix2) → Edge L n (i + 1) i → ComplexMatrix2}
    (hra : IsAnalyticFieldMap 𝒰 p) (hc : ContinuousOn p 𝒰)
    (hone : p (trivialField L n (i + 1) (i + 1)) = trivialField L n (i + 1) i)
    (hgauge : ForGaugesNearOneOrConstant (L := L) (n := n) (k := i + 1) (j := i + 1) fun v W =>
      p (PeriodicLattice.gaugeTransform v W) =
        PeriodicLattice.gaugeTransform (blockGaugeLift v) (p W))
    (hiso : EventuallyNearIdentity (fieldSpace L n (i + 1) (i + 1)) fun W =>
      ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
        IsLevelSymmetry (i + 1) (i + 1) f → p (pushField f W) = pushField f (p W))
    {f : (UnitEdge L (scaledExponent n (i + 1) i) → ComplexMatrix2) → ℝ}
    (hf : IsAdmissibleMember f) :
    IsAdmissibleMember fun U : UnitEdge L n → ComplexMatrix2 =>
      f (transportTotal (stepEdgeEquiv hL n i) (p (U ∘ topEdgeEquiv L n (i + 1)))) := by
  have he₀ := preservesOrientation_topEdgeEquiv L n (i + 1)
  have he : PreservesOrientation (stepEdgeEquiv hL n i) :=
    preservesOrientation_stepEdgeEquiv hX hS hL hn
  have hmaps := hra.2.1
  have h𝒰mem := mem_nhdsWithin_trivialField_of_isOpenNhdOfOne hE hS hn le_rfl h𝒰
  have hρ : Tendsto (fun U : UnitEdge L n → ComplexMatrix2 => U ∘ topEdgeEquiv L n (i + 1))
      (𝓝[fieldSpace L n 0 0] fun _ => (1 : ComplexMatrix2))
      (𝓝[fieldSpace L n (i + 1) (i + 1)] fun _ => (1 : ComplexMatrix2)) :=
    (continuous_pi fun b => continuous_apply (topEdgeEquiv L n (i + 1) b)
      : Continuous fun U : UnitEdge L n → ComplexMatrix2 =>
        U ∘ topEdgeEquiv L n (i + 1)).continuousWithinAt.tendsto_nhdsWithin
      fun U hU => transportTotal_mem_fieldSpace he₀.symm hU
  have hψ : Tendsto (fun W => transportTotal (stepEdgeEquiv hL n i) (p W))
      (𝓝[fieldSpace L n (i + 1) (i + 1)] fun _ => (1 : ComplexMatrix2))
      (𝓝[fieldSpace L (scaledExponent n (i + 1) i) 0 0] fun _ => (1 : ComplexMatrix2)) := by
    have hcw : ContinuousWithinAt (fun W => transportTotal (stepEdgeEquiv hL n i) (p W)) 𝒰
        (trivialField L n (i + 1) (i + 1)) :=
      (continuous_transportTotal_of_equiv (stepEdgeEquiv hL n i)).continuousAt.comp_continuousWithinAt
        (hc _ h𝒰.2)
    have h₁ := hcw.tendsto_nhdsWithin (t := fieldSpace L (scaledExponent n (i + 1) i) 0 0)
      fun W hW => transportTotal_mem_fieldSpace he (hmaps hW)
    have hval : transportTotal (stepEdgeEquiv hL n i)
        (p (trivialField L n (i + 1) (i + 1))) = fun _ => (1 : ComplexMatrix2) := by
      rw [hone]
      rfl
    rw [hval] at h₁
    exact h₁.mono_left (nhdsWithin_le_of_mem h𝒰mem)
  have keepsGauge : ∀ (V : Edge L n (i + 1) i → ComplexMatrix2)
      (u : Vertex L n (i + 1) i → ComplexMatrix2),
      V ∈ fieldSpace L n (i + 1) i → (∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) →
      transportTotal (stepEdgeEquiv hL n i) (PeriodicLattice.gaugeTransform u V) =
        PeriodicLattice.gaugeTransform (transportTotal (stepVertexEquiv hL n i) u)
          (transportTotal (stepEdgeEquiv hL n i) V) := by
    intro V u hV hu
    have h₁ := ((hK L hS hL (i + 1) i i (Nat.le_succ i) le_rfl).1 n hn).2.1 V u
      (isGaugeField_complex hV) fun x => mem_complexGaugeGroup (hu x)
    change transportTotal (topEdgeEquiv L _ i) (transportTotal (scaleEdge hL (Nat.le_succ i) i)
      (PeriodicLattice.gaugeTransform u V)) = _
    rw [h₁]
    exact transportTotal_edgeCast_gaugeTransform (levelDepth_self i) _ _
  have hgaugeMem : ∀ v : Vertex L n (i + 1) (i + 1) → ComplexMatrix2,
      (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) →
      ∀ x, blockGaugeLift v x ∈ PeriodicLattice.compactGaugeGroup := fun v hv x => hv _
  refine ⟨isAnalyticNearIdentity_comp hC hE hS hn he₀ he h𝒰 hra hc hone hf.analytic,
    ?_, ?_, ?_, ?_⟩
  · change f (transportTotal (stepEdgeEquiv hL n i) (p (trivialField L n (i + 1) (i + 1)))) = 0
    rw [hone]
    exact hf.map_identity
  · obtain ⟨Wf, hWf, hinv⟩ := hf.locallyGauge
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 hgauge.1
    have ht₂ : Tendsto (fun v : Vertex L n 0 0 → ComplexMatrix2 => v ∘ topVertexEquiv L n (i + 1))
        (𝓝[gaugeGroupAt L n 0 0] fun _ => (1 : ComplexMatrix2))
        (𝓝[gaugeGroupAt L n (i + 1) (i + 1)] fun _ => (1 : ComplexMatrix2)) :=
      (continuous_pi fun b => continuous_apply (topVertexEquiv L n (i + 1) b)
        : Continuous fun v : Vertex L n 0 0 → ComplexMatrix2 =>
          v ∘ topVertexEquiv L n (i + 1)).continuousWithinAt.tendsto_nhdsWithin
        fun v hv x => hv _
    have ht₃ : Tendsto (scaledGauge hL n i)
        (𝓝[gaugeGroupAt L n (i + 1) (i + 1)] fun _ => (1 : ComplexMatrix2))
        (𝓝[gaugeGroupAt L (scaledExponent n (i + 1) i) 0 0] fun _ => (1 : ComplexMatrix2)) :=
      (continuous_scaledGauge hL n i).continuousWithinAt.tendsto_nhdsWithin
        fun v hv x => hv _
    refine ⟨{v | pa (v ∘ topVertexEquiv L n (i + 1)) ∧
      scaledGauge hL n i (v ∘ topVertexEquiv L n (i + 1)) ∈ Wf}, ?_, ?_⟩
    · exact (ht₂.eventually hpa).and (ht₂.eventually (ht₃.eventually hWf))
    · have a₁ : ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)),
          pb (U ∘ topEdgeEquiv L n (i + 1)) := hρ.eventually hpb
      have a₂ : ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)),
          U ∘ topEdgeEquiv L n (i + 1) ∈ 𝒰 := hρ.eventually h𝒰mem
      have a₃ := hρ.eventually (hψ.eventually hinv)
      change ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)), _
      filter_upwards [a₁, a₂, a₃] with U h₁ h₂ h₃ v hv hvW
      have h₄ : PeriodicLattice.gaugeTransform v U ∘ topEdgeEquiv L n (i + 1) =
          PeriodicLattice.gaugeTransform (v ∘ topVertexEquiv L n (i + 1))
            (U ∘ topEdgeEquiv L n (i + 1)) :=
        gaugeTransform_comp_edgeCast (levelDepth_self (i + 1)) v U
      have h₅ : p (PeriodicLattice.gaugeTransform (v ∘ topVertexEquiv L n (i + 1))
            (U ∘ topEdgeEquiv L n (i + 1))) =
          PeriodicLattice.gaugeTransform (blockGaugeLift (v ∘ topVertexEquiv L n (i + 1)))
            (p (U ∘ topEdgeEquiv L n (i + 1))) := hab hvW.1 h₁
      change f (transportTotal (stepEdgeEquiv hL n i)
        (p (PeriodicLattice.gaugeTransform v U ∘ topEdgeEquiv L n (i + 1)))) = _
      rw [h₄, h₅, keepsGauge _ _ (hmaps h₂)
        (hgaugeMem (v ∘ topVertexEquiv L n (i + 1)) fun x => hv _)]
      exact h₃ _ (fun x => hv _) hvW.2
  · have a₁ := hρ.eventually hgauge.2
    have a₂ : ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)),
        U ∘ topEdgeEquiv L n (i + 1) ∈ 𝒰 := hρ.eventually h𝒰mem
    have a₃ := hρ.eventually (hψ.eventually hf.globalGauge)
    change ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)), _
    filter_upwards [a₁, a₂, a₃] with U h₁ h₂ h₃ g hg
    have h₄ : PeriodicLattice.gaugeTransform (fun _ : Vertex L n 0 0 => g) U ∘
          topEdgeEquiv L n (i + 1) =
        PeriodicLattice.gaugeTransform (fun _ : Vertex L n (i + 1) (i + 1) => g)
          (U ∘ topEdgeEquiv L n (i + 1)) :=
      gaugeTransform_comp_edgeCast (levelDepth_self (i + 1)) (fun _ => g) U
    have h₅ := h₁ (fun _ => g) (fun _ => hg) fun _ _ => rfl
    change f (transportTotal (stepEdgeEquiv hL n i)
      (p (PeriodicLattice.gaugeTransform (fun _ => g) U ∘ topEdgeEquiv L n (i + 1)))) = _
    rw [h₄, h₅, keepsGauge _ _ (hmaps h₂) (hgaugeMem _ fun _ => hg)]
    exact h₃ g hg
  · have a₁ := hρ.eventually hiso
    have a₃ := hρ.eventually (hψ.eventually hf.symmetry)
    have a₂ : ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)),
        U ∘ topEdgeEquiv L n (i + 1) ∈ 𝒰 := hρ.eventually h𝒰mem
    change ∀ᶠ U in 𝓝[fieldSpace L n 0 0] (fun _ => (1 : ComplexMatrix2)), _
    filter_upwards [a₁, a₂, a₃] with U h₁ h₂ h₃ σ hσ hσ₀
    have hσk : MapsSublatticeOnto (i + 1) (i + 1) σ := by
      unfold MapsSublatticeOnto at hσ₀ ⊢
      rw [levelDepth_self (i + 1)]
      exact hσ₀
    have h₄ : pushField (k := 0) (j := 0) σ U ∘ topEdgeEquiv L n (i + 1) =
        pushField (k := i + 1) (j := i + 1) σ (U ∘ topEdgeEquiv L n (i + 1)) :=
      pushFieldAtDepth_comp_edgeCast (levelDepth_self (i + 1)) σ U
    have h₅ := h₁ σ ⟨hσ, hσk⟩
    have hσi : MapsSublatticeOnto (i + 1) i σ :=
      (((hT L hL hS (i + 1)).2.2.2.1 n hn (i + 1) le_rfl σ hσ hσk).2 i (Nat.le_succ i)).1
    have hKi : ScalingPreservesSymmetry hL (Nat.le_succ i) i σ :=
      ((hK L hS hL (i + 1) i i (Nat.le_succ i) le_rfl).1 n hn).2.2 σ hσ hσi
    have hσ' : MapsSublatticeOnto 0 0 (conjMap (scaling hL n (i + 1) i).toEquiv σ) := by
      have h := hKi.mapsSublattice
      unfold MapsSublatticeOnto at h ⊢
      rw [← levelDepth_self i]
      exact h
    have h₆ : transportTotal (stepEdgeEquiv hL n i)
        (pushField σ (p (U ∘ topEdgeEquiv L n (i + 1)))) =
        pushField (k := 0) (j := 0) (conjMap (scaling hL n (i + 1) i).toEquiv σ)
          (transportTotal (stepEdgeEquiv hL n i) (p (U ∘ topEdgeEquiv L n (i + 1)))) := by
      change transportTotal (topEdgeEquiv L _ i) (transportTotal (scaleEdge hL (Nat.le_succ i) i)
        (pushField σ (p (U ∘ topEdgeEquiv L n (i + 1))))) = _
      rw [hKi.field_comm _ (Or.inl (hmaps h₂))]
      exact transportTotal_edgeCast_pushFieldAtDepth (levelDepth_self i) _ _
    change f (transportTotal (stepEdgeEquiv hL n i)
      (p (pushField (k := 0) (j := 0) σ U ∘ topEdgeEquiv L n (i + 1)))) = _
    rw [h₄, h₅, h₆]
    exact h₃ _ hKi.distancePreserving hσ'
end Member
theorem compStepPreservesFunctionals_proof (hB : CriticalBranchExists)
    (hA : AnalyticMapsAlongCurves) (hE : BondSetFields.ProductStructureHolds)
    (hFam : CompStepEventuallyDefined) (hX : ScalingPropertiesStatement)
    (hK : ScalingCompatibility.Statement)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hC : HolomorphicCalculus.Properties) : CompStepPreservesFunctionals := by
  intro L hL hS F i hF
  obtain ⟨s₀, hs₀, hlarge⟩ := (hFam L hS F _ _ (isDefinedOn_of_isLatticeFunctional hF) i).2.1
  refine ⟨s₀, hs₀, fun s hs hle n hn e => ?_⟩
  have hmem : IsAdmissibleMember (F (n + 1)) := hlarge s hs hle n hn e
  have hbranch : (chosenCriticalBranch L n (i + 1)).IsCritical :=
    Classical.epsilon_spec (hB L n (i + 1) hS hn)
  obtain ⟨𝒰, h𝒰, hra⟩ := hbranch.analytic_prolong i (Nat.lt_succ_self i)
  have hc := ((hA L n (i + 1) (i + 1) i hS hn le_rfl (Nat.le_succ i)).1 𝒰 _ hra).1
  exact isAdmissibleMember_comp hC hE hK hT hX hS hL hn h𝒰 hra hc
    (hbranch.prolong_trivial i (Nat.lt_succ_self i))
    (hbranch.prolong_gauge_equivariant i (Nat.lt_succ_self i))
    (hbranch.prolong_symmetry_equivariant i (Nat.lt_succ_self i))
    (isAdmissibleMember_cast (scaledExponent_succ_self n i) hmem)
end YangMills.Construction.Tower.StepComposition
end
