import YangMills.Construction.Towers.DilationNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import YangMills.Construction.Towers.RealAnalyticSubmanifoldsUnderTheDilation
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace AnalyticSubmanifoldTransport
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Coordinates
section Reindexing
variable {σ σ' ι ι' κ κ' E : Type}
def precomp (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) : σ → ComplexMatrix2 := A ∘ τ
abbrev sumReindex (r : ι ≃ ι') (s : κ ≃ κ') : ι ⊕ κ ≃ ι' ⊕ κ' := r.sumCongr s
theorem precomp_precomp_symm (τ : σ ≃ σ') (w : σ → ComplexMatrix2) :
    precomp τ (precomp τ.symm w) = w := by
  funext i
  simp [precomp]
theorem precomp_symm_precomp (τ : σ ≃ σ') (w : σ' → ComplexMatrix2) :
    precomp τ.symm (precomp τ w) = w := by
  funext i
  simp [precomp]
theorem continuous_precomp (τ : σ ≃ σ') : Continuous (precomp τ) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.continuous_precomp <;> assumption
theorem isRelativelyOpen_precomp (τ : σ ≃ σ') {P : Set (σ → ComplexMatrix2)}
    {P' : Set (σ' → ComplexMatrix2)} (hP : ∀ q, q ∈ P' ↔ precomp τ q ∈ P)
    {W : Set (σ → ComplexMatrix2)} (h : ComplexMatrix2.IsRelativelyOpen P W) :
    ComplexMatrix2.IsRelativelyOpen P' (precomp τ ⁻¹' W) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.isRelativelyOpen_precomp <;> assumption
theorem precomp_mem_tracelessPi (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) :
    precomp τ A ∈ tracelessPi σ ↔ A ∈ tracelessPi σ' := by apply _root_.YangMills.Construction.Tower.ScalingTransport.precomp_mem_tracelessPi <;> assumption
theorem supNorm_precomp (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) :
    supNorm (precomp τ A) = supNorm A := by apply _root_.YangMills.Construction.Tower.ScalingTransport.supNorm_precomp <;> assumption
theorem isSupOpen_precomp (τ : σ ≃ σ') {O : Set (σ → ComplexMatrix2)} (h : IsSupOpen O) :
    IsSupOpen (precomp τ ⁻¹' O) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.isSupOpen_precomp <;> assumption
def coordFamily {N : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : σ ≃ Fin N)
    (w : ComplexCoordinates (N * 3)) (i : σ) : ComplexMatrix2 :=
  ComplexCoordinates.tracelessTuple b w (ν i)
theorem isHolomorphicIn_precomp {l N N' : ℕ} (hN : N = N')
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ ComplexCoordinates l) (τ : σ ≃ σ') {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → E}
    (H : ∀ ν : σ ≃ Fin N,
      ComplexCoordinates.IsHolomorphicIn (coordFamily b ν ⁻¹' O) (e ∘ f ∘ coordFamily b ν))
    (ν' : σ' ≃ Fin N') :
    ComplexCoordinates.IsHolomorphicIn (coordFamily b ν' ⁻¹' (precomp τ ⁻¹' O))
      (e ∘ (f ∘ precomp τ) ∘ coordFamily b ν') := by
  subst hN
  exact H (τ.trans ν')
theorem isHolomorphicOnTraceless_precomp [Fintype σ] [Fintype σ'] {l : ℕ} (τ : σ ≃ σ')
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : E ≃ ComplexCoordinates l}
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    (h : IsHolomorphicOnTraceless b e O f) :
    IsHolomorphicOnTraceless b e (precomp τ ⁻¹' O) (f ∘ precomp τ) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.isHolomorphicOnTraceless_precomp <;> assumption
theorem precomp_expChartAt (r : ι ≃ ι') (s : κ ≃ κ') (p A : ι' ⊕ κ' → ComplexMatrix2) :
    precomp (sumReindex r s) (expChartAt p A) =
      expChartAt (precomp (sumReindex r s) p) (precomp (sumReindex r s) A) := by
  funext x
  cases x <;> rfl
theorem precomp_mem_groupLieProduct (r : ι ≃ ι') (s : κ ≃ κ') (q : ι' ⊕ κ' → ComplexMatrix2) :
    q ∈ GroupLieProduct ι' κ' ↔ precomp (sumReindex r s) q ∈ GroupLieProduct ι κ := by
  constructor
  · intro h x
    cases x with
    | inl i => exact h (.inl (r i))
    | inr c => exact h (.inr (s c))
  · intro h x
    cases x with
    | inl i => simpa [precomp] using h (.inl (r.symm i))
    | inr c => simpa [precomp] using h (.inr (s.symm c))
theorem isHolomorphicToCoords_precomp [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {l : ℕ} (r : ι ≃ ι') (s : κ ≃ κ') {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ) :
    IsHolomorphicToCoords b e (precomp (sumReindex r s) ⁻¹' W)
      (Φ ∘ precomp (sumReindex r s)) := by
  obtain ⟨hW, hc, hp⟩ := h
  refine ⟨isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r s) hW,
    hc.comp (continuous_precomp _).continuousOn (mapsTo_preimage _ _), fun p hpW => ?_⟩
  obtain ⟨O, h0, hA, hO⟩ := hp _ hpW
  refine ⟨precomp (sumReindex r s) ⁻¹' O, h0, fun A hA' => ?_, ?_⟩
  · rw [mem_preimage, precomp_expChartAt]
    exact hA _ hA'
  · have hfun : (Φ ∘ precomp (sumReindex r s)) ∘ expChartAt p =
        (Φ ∘ expChartAt (precomp (sumReindex r s) p)) ∘ precomp (sumReindex r s) := by
      funext A
      simp only [Function.comp, precomp_expChartAt]
    rw [hfun]
    exact isHolomorphicOnTraceless_precomp _ hO
theorem isHolomorphicToTraceless_precomp [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (r : ι ≃ ι') (s : κ ≃ κ') {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToTraceless b W Φ) :
    IsHolomorphicToTraceless b (precomp (sumReindex r s) ⁻¹' W)
      (Φ ∘ precomp (sumReindex r s)) :=
  ⟨fun _ hq => h.1 hq, isHolomorphicToCoords_precomp r s h.2⟩
theorem isHolomorphicToUnimodular_precomp [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (r : ι ≃ ι') (s : κ ≃ κ') {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToUnimodular b W Φ) :
    IsHolomorphicToUnimodular b (precomp (sumReindex r s) ⁻¹' W)
      (Φ ∘ precomp (sumReindex r s)) := by
  obtain ⟨hW, hm, hc, hp⟩ := h
  refine ⟨isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r s) hW, fun _ hq => hm hq,
    hc.comp (continuous_precomp _).continuousOn (mapsTo_preimage _ _), fun p hpW => ?_⟩
  obtain ⟨O, h0, hA, hO⟩ := hp _ hpW
  refine ⟨precomp (sumReindex r s) ⁻¹' O, h0, fun A hA' => ?_, ?_⟩
  · simp only [mem_preimage, Function.comp, precomp_expChartAt]
    exact hA _ hA'
  · have hfun : (fun A => ComplexMatrix2.logSeries
        ((Φ ∘ precomp (sumReindex r s)) (expChartAt p A) *
        ((Φ ∘ precomp (sumReindex r s)) p)⁻¹)) =
        (fun A => ComplexMatrix2.logSeries (Φ (expChartAt (precomp (sumReindex r s) p) A) *
          (Φ (precomp (sumReindex r s) p))⁻¹)) ∘ precomp (sumReindex r s) := by
      funext A
      simp only [Function.comp, precomp_expChartAt]
    rw [hfun]
    exact isHolomorphicOnTraceless_precomp _ hO
theorem isHolomorphicToProduct_precomp [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {R₁ R₂ κ₁ κ₂ : Type} (r : ι ≃ ι') (s : κ ≃ κ') (t : R₁ ≃ R₂) (u : κ₁ ≃ κ₂)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → R₁ ⊕ κ₁ → ComplexMatrix2}
    (h : IsHolomorphicToProduct b W Ψ) :
    IsHolomorphicToProduct b (precomp (sumReindex r s) ⁻¹' W)
      fun q => precomp (sumReindex t.symm u.symm) (Ψ (precomp (sumReindex r s) q)) := by
  obtain ⟨hW, hg, ha⟩ := h
  refine ⟨isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r s) hW,
    fun i => ?_, fun c => ?_⟩
  · have hfun : (fun p => precomp (sumReindex t.symm u.symm)
        (Ψ (precomp (sumReindex r s) p)) (.inl i)) =
        (fun p => Ψ p (.inl (t.symm i))) ∘ precomp (sumReindex r s) := rfl
    rw [hfun]
    exact isHolomorphicToUnimodular_precomp r s (hg (t.symm i))
  · have hfun : (fun p => precomp (sumReindex t.symm u.symm)
        (Ψ (precomp (sumReindex r s) p)) (.inr c)) =
        (fun p => Ψ p (.inr (u.symm c))) ∘ precomp (sumReindex r s) := rfl
    rw [hfun]
    exact isHolomorphicToTraceless_precomp r s (ha (u.symm c))
theorem precomp_mem_compactPi (τ : σ ≃ σ') (w : σ' → ComplexMatrix2) :
    precomp τ w ∈ compactPi σ ↔ w ∈ compactPi σ' := by apply _root_.YangMills.Construction.Tower.ScalingTransport.precomp_mem_compactPi <;> assumption
theorem precomp_mem_hermitianTracelessFunctions (τ : σ ≃ σ') (w : σ' → ComplexMatrix2) :
    precomp τ w ∈ hermitianTracelessFunctions σ ↔ w ∈ hermitianTracelessFunctions σ' :=
  ⟨fun h i _ => by simpa [precomp] using h (τ.symm i) (mem_univ _),
    fun h i _ => h (τ i) (mem_univ _)⟩
theorem precomp_mem_subspaceTimesGroup (r : ι ≃ ι') (s : κ ≃ κ')
    {F : Submodule ℝ (κ → ComplexMatrix2)} {F' : Submodule ℝ (κ' → ComplexMatrix2)}
    (hF : ∀ w, w ∈ F' ↔ precomp s w ∈ F) (q : ι' ⊕ κ' → ComplexMatrix2) :
    q ∈ subspaceTimesGroup F' ι' ↔ precomp (sumReindex r s) q ∈ subspaceTimesGroup F ι := by
  change (algebraComponent q ∈ F' ∧ groupComponent q ∈ compactPi ι') ↔
    (precomp s (algebraComponent q) ∈ F ∧ precomp r (groupComponent q) ∈ compactPi ι)
  rw [precomp_mem_compactPi, hF]
theorem isSubspaceAnalyticToProduct_precomp [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {R₁ R₂ κ₁ κ₂ : Type} (r : ι ≃ ι') (s : κ ≃ κ') (t : R₁ ≃ R₂) (u : κ₁ ≃ κ₂)
    {F : Submodule ℝ (κ → ComplexMatrix2)} {F' : Submodule ℝ (κ' → ComplexMatrix2)}
    {G : Submodule ℝ (κ₁ → ComplexMatrix2)} {G' : Submodule ℝ (κ₂ → ComplexMatrix2)}
    (hF : ∀ w, w ∈ F' ↔ precomp s w ∈ F) (hG : ∀ w, w ∈ G ↔ precomp u.symm w ∈ G')
    {𝒲 : Set (ι ⊕ κ → ComplexMatrix2)} {f : (ι ⊕ κ → ComplexMatrix2) → R₁ ⊕ κ₁ → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct F G 𝒲 f) :
    IsSubspaceAnalyticToProduct F' G' (precomp (sumReindex r s) ⁻¹' 𝒲)
      fun q => precomp (sumReindex t.symm u.symm) (f (precomp (sumReindex r s) q)) := by
  obtain ⟨⟨hFr, h𝒲⟩, hGr, hm, hp⟩ := h
  refine ⟨⟨fun w hw => (precomp_mem_hermitianTracelessFunctions s w).1 (hFr ((hF w).1 hw)),
    isRelativelyOpen_precomp _ (precomp_mem_subspaceTimesGroup r s hF) h𝒲⟩, fun w hw => ?_,
    fun q hq => (precomp_mem_subspaceTimesGroup t.symm u.symm hG _).1 (hm hq),
    fun p hpW => ?_⟩
  · have hw' : precomp u w ∈ G := by
      rw [hG, precomp_symm_precomp]
      exact hw
    exact (precomp_mem_hermitianTracelessFunctions u w).1 (hGr hw')
  obtain ⟨𝒳, hp𝒳, h𝒳, hsub, Ψ, hΨ, hEq⟩ := hp _ hpW
  refine ⟨precomp (sumReindex r s) ⁻¹' 𝒳, hp𝒳,
    isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r s) h𝒳,
    fun q hq => hsub ⟨hq.1, (precomp_mem_subspaceTimesGroup r s hF q).1 hq.2⟩,
    fun q => precomp (sumReindex t.symm u.symm) (Ψ (precomp (sumReindex r s) q)),
    fun b => isHolomorphicToProduct_precomp r s t u (hΨ b), fun q hq => ?_⟩
  exact congrArg (precomp (sumReindex t.symm u.symm))
    (hEq ⟨hq.1, (precomp_mem_subspaceTimesGroup r s hF q).1 hq.2⟩)
def reindexCLE [Fintype σ] [Fintype σ'] (τ : σ ≃ σ') :
    (σ → ComplexMatrix2) ≃L[ℝ] (σ' → ComplexMatrix2) where
  toFun := precomp τ.symm
  invFun := precomp τ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := precomp_precomp_symm τ
  right_inv := precomp_symm_precomp τ
  continuous_toFun := continuous_pi fun i => continuous_apply (τ.symm i)
  continuous_invFun := continuous_pi fun i => continuous_apply (τ i)
end Reindexing
section Charts
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem isRelativelyOpen_map (T : E ≃L[ℝ] F) {M S : Set E}
    (h : ComplexMatrix2.IsRelativelyOpen M S) :
    ComplexMatrix2.IsRelativelyOpen (T '' M) (T '' S) := by
  obtain ⟨O, hO, rfl⟩ := h
  exact ⟨T '' O, T.toHomeomorph.isOpenMap _ hO, image_inter T.injective⟩
def chartMap (T : E ≃L[ℝ] F) {M : Set E} (c : EmbeddedSubmanifold.Chart M) :
    EmbeddedSubmanifold.Chart (T '' M) where
  dim := c.dim
  source := c.source
  param := T ∘ c.param
  isOpen_source := c.isOpen_source
  contDiffOn_param := T.contDiff.comp_contDiffOn c.contDiffOn_param
  injective_fderiv_param u hu := by
    rw [T.comp_fderiv]
    exact T.injective.comp (c.injective_fderiv_param u hu)
  injOn_param := T.injective.comp_injOn c.injOn_param
  isRelativelyOpen_image W hW hWo := by
    rw [image_comp]
    exact isRelativelyOpen_map T (c.isRelativelyOpen_image W hW hWo)
theorem isChartedSubset_image (T : E ≃L[ℝ] F) {M : Set E}
    (h : EmbeddedSubmanifold.IsChartedSubset M) :
    EmbeddedSubmanifold.IsChartedSubset (T '' M) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, u, hu, hc⟩ := h x hx
  exact ⟨chartMap T c, u, hu, congrArg T hc⟩
end Charts
section Edges
variable {L n k i n₂ k₂ i₂ : ℕ}
structure PreservesOrientation (e : Edge L n k i ≃ Edge L n₂ k₂ i₂) : Prop where
  positive : ∀ b, (e b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  opposite : ∀ b, e b.opposite = (e b).opposite
theorem PreservesOrientation.symm {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) : PreservesOrientation e.symm where
  positive b := by rw [← he.positive, e.apply_symm_apply]
  opposite b := by
    apply e.injective
    rw [he.opposite, e.apply_symm_apply, e.apply_symm_apply]
def positiveEdgeEquiv {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e) :
    PositiveEdge L n k i ≃ PositiveEdge L n₂ k₂ i₂ :=
  e.subtypeEquiv fun b => (he.positive b).symm
theorem transportTotal_injective {V : Type} (e : Edge L n k i ≃ Edge L n₂ k₂ i₂) :
    Function.Injective (transportTotal e : (Edge L n k i → V) → Edge L n₂ k₂ i₂ → V) := by
  intro f g h
  funext b
  have hb := congrFun h (e b)
  simpa [transportTotal] using hb
theorem expTwist_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (B V : Edge L n k i → ComplexMatrix2) :
    transportTotal e (PeriodicLattice.expTwist B V) =
      PeriodicLattice.expTwist (transportTotal e B) (transportTotal e V) := by
  funext b
  have hp := he.symm.positive b
  simp only [transportTotal, Function.comp, PeriodicLattice.expTwist, he.symm.opposite]
  by_cases h : b.IsPositivelyOriented
  · rw [if_pos h, if_pos (hp.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hp.1 h'))]
theorem transport_edgeFormOfPositiveValues {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (w : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :
    transportTotal e (edgeFormOfPositiveValues (precomp (positiveEdgeEquiv he) w)) =
      edgeFormOfPositiveValues w := by
  funext b
  change edgeFormOfPositiveValues (precomp (positiveEdgeEquiv he) w) (e.symm b) = _
  have hp := he.symm.positive b
  have hr := he.symm.positive b.opposite
  rw [he.symm.opposite] at hr
  unfold edgeFormOfPositiveValues
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h, dif_pos (hp.2 h)]
    exact congrArg w (Subtype.ext (e.apply_symm_apply b))
  · rw [dif_neg h, dif_neg (fun h' => h (hp.1 h'))]
    by_cases h' : b.opposite.IsPositivelyOriented
    · rw [dif_pos h', dif_pos (hr.2 h')]
      refine congrArg Neg.neg (congrArg w (Subtype.ext ?_))
      change e (e.symm b).opposite = b.opposite
      rw [he.opposite, e.apply_symm_apply]
    · rw [dif_neg h', dif_neg (fun h'' => h' (hr.1 h''))]
theorem image_restrictToPositiveEdges_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) [Fintype (PositiveEdge L n k i)]
    [Fintype (PositiveEdge L n₂ k₂ i₂)] (N : Set (Edge L n k i → ComplexMatrix2)) :
    restrictToPositiveEdges '' (transportTotal e '' N) =
      reindexCLE (positiveEdgeEquiv he) '' (restrictToPositiveEdges '' N) := by
  rw [image_image, image_image]
  rfl
def reindexSubmodule {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (E : Submodule ℝ (PositiveEdge L n k i → ComplexMatrix2)) :
    Submodule ℝ (PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :=
  E.comap (LinearEquiv.funCongrLeft ℝ ComplexMatrix2 (positiveEdgeEquiv he)).toLinearMap
theorem mem_reindexSubmodule {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (E : Submodule ℝ (PositiveEdge L n k i → ComplexMatrix2))
    (w : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :
    w ∈ reindexSubmodule he E ↔ precomp (positiveEdgeEquiv he) w ∈ E := Iff.rfl
theorem reindexSubmodule_sup {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    {E E' : Submodule ℝ (PositiveEdge L n k i → ComplexMatrix2)}
    (h : E ⊔ E' = hermitianTracelessFunctions (PositiveEdge L n k i)) :
    reindexSubmodule he E ⊔ reindexSubmodule he E' =
      hermitianTracelessFunctions (PositiveEdge L n₂ k₂ i₂) := by
  have hc : reindexSubmodule he E ⊔ reindexSubmodule he E' =
      reindexSubmodule he (E ⊔ E') := by
    simp only [reindexSubmodule, Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]
  rw [hc, h]
  ext w
  rw [mem_reindexSubmodule, precomp_mem_hermitianTracelessFunctions]
theorem reindexSubmodule_inf {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    {E E' : Submodule ℝ (PositiveEdge L n k i → ComplexMatrix2)} (h : E ⊓ E' = ⊥) :
    reindexSubmodule he E ⊓ reindexSubmodule he E' = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hz : precomp (positiveEdgeEquiv he) w ∈ E ⊓ E' := hw
  rw [h, Submodule.mem_bot] at hz
  have := precomp_symm_precomp (positiveEdgeEquiv he) w
  rw [hz] at this
  rw [Submodule.mem_bot, ← this]
  rfl
def reindexMap {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (f : (PositiveEdge L n k i → ComplexMatrix2) → PositiveEdge L n k i → ComplexMatrix2) :
    (PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) → PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2 :=
  fun w => precomp (positiveEdgeEquiv he).symm (f (precomp (positiveEdgeEquiv he) w))
theorem isAnalyticOnSubspace_reindex {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) [Fintype (PositiveEdge L n k i)]
    [Fintype (PositiveEdge L n₂ k₂ i₂)]
    {E E' : Submodule ℝ (PositiveEdge L n k i → ComplexMatrix2)}
    {O : Set (PositiveEdge L n k i → ComplexMatrix2)}
    {f : (PositiveEdge L n k i → ComplexMatrix2) → PositiveEdge L n k i → ComplexMatrix2}
    (h : IsAnalyticOnSubspace E E' O f) :
    IsAnalyticOnSubspace (reindexSubmodule he E) (reindexSubmodule he E')
      (precomp (positiveEdgeEquiv he) ⁻¹' O) (reindexMap he f) := by
  have hG : ∀ w, w ∈ E' ↔ precomp (positiveEdgeEquiv he).symm w ∈ reindexSubmodule he E' :=
    fun w => by rw [mem_reindexSubmodule, precomp_precomp_symm]
  have key := isSubspaceAnalyticToProduct_precomp (Equiv.refl Empty) (positiveEdgeEquiv he)
    (Equiv.refl Empty) (positiveEdgeEquiv he) (mem_reindexSubmodule he E) hG h
  have hfun : (fun q : Empty ⊕ PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2 =>
      ofParts (Empty.elim : Empty → ComplexMatrix2) (reindexMap he f (algebraComponent q))) =
      fun q => precomp (sumReindex (Equiv.refl Empty).symm (positiveEdgeEquiv he).symm)
        (ofParts (Empty.elim : Empty → ComplexMatrix2) (f (algebraComponent
          (precomp (sumReindex (Equiv.refl Empty) (positiveEdgeEquiv he)) q)))) := by
    funext q x
    cases x with
    | inl c => exact c.elim
    | inr b => rfl
  unfold IsAnalyticOnSubspace
  rw [hfun]
  exact key
theorem isAnalyticFieldSubmanifold_transport {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e)
    (hconf : ∀ V ∈ fieldSpace L n k i, transportTotal e V ∈ fieldSpace L n₂ k₂ i₂)
    (hopen : ∀ S : Set (Edge L n k i → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup S →
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup (transportTotal e '' S))
    {N : Set (Edge L n k i → ComplexMatrix2)} (hN : IsAnalyticFieldSubmanifold N) :
    IsAnalyticFieldSubmanifold (transportTotal e '' N) := by
  obtain ⟨⟨hNc, hman⟩, hgraph⟩ := hN
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact hconf V (hNc hV)
  · obtain ⟨_, hman⟩ := hman
    obtain ⟨fin'⟩ : Nonempty (Fintype (PositiveEdge L n₂ k₂ i₂)) :=
      ⟨Fintype.ofEquiv _ (positiveEdgeEquiv he)⟩
    refine ⟨fin', ?_⟩
    rw [image_restrictToPositiveEdges_transport he]
    exact isChartedSubset_image _ hman
  obtain ⟨_, hgraph⟩ := hgraph
  obtain ⟨fin'⟩ : Nonempty (Fintype (PositiveEdge L n₂ k₂ i₂)) :=
    ⟨Fintype.ofEquiv _ (positiveEdgeEquiv he)⟩
  refine ⟨fin', ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨𝒰, p, E, E', O, O', f, h𝒰, hx𝒰, hp, hsup, hinf, hO, hO', hf, hU⟩ := hgraph x hx
    have hinj := transportTotal_injective (V := ComplexMatrix2) e
    have hmemE : ∀ (G : Submodule ℝ (PositiveEdge L n k i → ComplexMatrix2)) q,
        q ∈ ((reindexSubmodule he G : Submodule ℝ _) :
            Set (PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2)) ↔
          precomp (positiveEdgeEquiv he) q ∈ (G : Set (PositiveEdge L n k i → ComplexMatrix2)) :=
      fun _ _ => Iff.rfl
    have hword : ∀ Y : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2,
        PeriodicLattice.expTwist (edgeFormOfPositiveValues Y) (transportTotal e p) =
          transportTotal e (PeriodicLattice.expTwist
            (edgeFormOfPositiveValues (precomp (positiveEdgeEquiv he) Y)) p) := fun Y => by
      rw [expTwist_transport he, transport_edgeFormOfPositiveValues he]
    refine ⟨transportTotal e '' 𝒰, transportTotal e p, reindexSubmodule he E,
      reindexSubmodule he E', precomp (positiveEdgeEquiv he) ⁻¹' O,
      precomp (positiveEdgeEquiv he) ⁻¹' O', reindexMap he f,
      hopen _ h𝒰, mem_image_of_mem _ hx𝒰, hconf p hp, reindexSubmodule_sup he hsup,
      reindexSubmodule_inf he hinf, isRelativelyOpen_precomp _ (hmemE E) hO,
      isRelativelyOpen_precomp _ (hmemE E') hO', isAnalyticOnSubspace_reindex he hf, ?_⟩
    rintro _ ⟨V, hV, rfl⟩
    obtain ⟨⟨P, ⟨hP₁, hP₂, hPV⟩, huniq⟩, hiff⟩ := hU V hV
    refine ⟨⟨(precomp (positiveEdgeEquiv he).symm P.1, precomp (positiveEdgeEquiv he).symm P.2),
      ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · change precomp _ (precomp _ _) ∈ O
      rwa [precomp_precomp_symm]
    · change precomp _ (precomp _ _) ∈ O'
      rwa [precomp_precomp_symm]
    · have hsum : precomp (positiveEdgeEquiv he) (precomp (positiveEdgeEquiv he).symm P.1 +
          precomp (positiveEdgeEquiv he).symm P.2) = P.1 + P.2 := by
        funext b
        simp [precomp]
      rw [hword, hsum, ← hPV]
    · rintro ⟨Y, Y'⟩ ⟨hY, hY', hE⟩
      rw [hword] at hE
      have hV' := hinj hE
      have hadd : precomp (positiveEdgeEquiv he) (Y + Y') =
          precomp (positiveEdgeEquiv he) Y + precomp (positiveEdgeEquiv he) Y' := rfl
      rw [hadd] at hV'
      have := huniq (precomp (positiveEdgeEquiv he) Y, precomp (positiveEdgeEquiv he) Y')
        ⟨hY, hY', hV'⟩
      rw [← this]
      simp only [precomp_symm_precomp]
    · intro Y hY Y' hY' hE
      rw [hword] at hE
      have hV' := hinj hE
      have hadd : precomp (positiveEdgeEquiv he) (Y + Y') =
          precomp (positiveEdgeEquiv he) Y + precomp (positiveEdgeEquiv he) Y' := rfl
      rw [hadd] at hV'
      rw [hinj.mem_set_image, hiff _ hY _ hY' hV']
      constructor
      · intro h
        change Y' = precomp (positiveEdgeEquiv he).symm (f (precomp (positiveEdgeEquiv he) Y))
        rw [← h, precomp_symm_precomp]
      · intro h
        rw [h]
        exact precomp_precomp_symm _ _
end Edges
end AnalyticSubmanifoldTransport
open AnalyticSubmanifoldTransport in
theorem analyticSubmanifoldScaling_proof
    (h₁ : ScalingPropertiesStatement)
    (h₂ : ScalingNearTrivialField) :
    AnalyticSubmanifoldScaling := by
  intro L n k j hL hj hS hn l hl N hN
  have hat := ((h₁ L k j hS hj).1 n hn).atLevel
  have keeps : PreservesOrientation (scaleEdge (n := n) hL hj l) :=
    { positive := fun b => by
        have himg := (hat l hl).image_positive
        constructor
        · intro hb
          have hmem : scaleEdge (n := n) hL hj l b ∈
              scaleEdge (n := n) hL hj l '' {b | b.IsPositivelyOriented} := by
            rw [himg]
            exact hb
          obtain ⟨b', hb', hE⟩ := hmem
          rw [← (scaleEdge (n := n) hL hj l).injective hE]
          exact hb'
        · intro hb
          have hmem : scaleEdge (n := n) hL hj l b ∈
              scaleEdge (n := n) hL hj l '' {b | b.IsPositivelyOriented} :=
            mem_image_of_mem _ hb
          rw [himg] at hmem
          exact hmem
      opposite := (hat l hl).edge_opposite }
  obtain ⟨hcf, hop, -⟩ := h₂ L n k j l l hL hj hS hn hl hl
  exact isAnalyticFieldSubmanifold_transport keeps (fun V hV => hcf.1.mapsTo hV)
    (fun S hS' => (hop.2.1 S hS'.1).1 hS') hN
end YangMills.Construction.Tower
end
