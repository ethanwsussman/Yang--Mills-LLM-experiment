import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
namespace ScalingTransport
open Matrices Coordinates
open Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
section Reindexing
variable {σ σ' ι ι' κ κ' E : Type}
def precomp (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) : σ → ComplexMatrix2 := A ∘ τ
abbrev sumReindex (r : ι ≃ ι') (κ : Type) : ι ⊕ κ ≃ ι' ⊕ κ := r.sumCongr (Equiv.refl κ)
theorem continuous_precomp (τ : σ ≃ σ') : Continuous (precomp τ) :=
  continuous_pi fun i => continuous_apply (τ i)
theorem isRelativelyOpen_precomp (τ : σ ≃ σ') {P : Set (σ → ComplexMatrix2)}
    {P' : Set (σ' → ComplexMatrix2)} (hP : ∀ q, q ∈ P' ↔ precomp τ q ∈ P)
    {W : Set (σ → ComplexMatrix2)} (h : ComplexMatrix2.IsRelativelyOpen P W) :
    ComplexMatrix2.IsRelativelyOpen P' (precomp τ ⁻¹' W) := by
  obtain ⟨O, hO, rfl⟩ := h
  refine ⟨precomp τ ⁻¹' O, hO.preimage (continuous_precomp τ), ?_⟩
  ext q
  simp only [mem_preimage, mem_inter_iff, hP]
theorem precomp_mem_tracelessPi (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) :
    precomp τ A ∈ tracelessPi σ ↔ A ∈ tracelessPi σ' :=
  ⟨fun h i => by simpa [precomp] using h (τ.symm i), fun h i => h (τ i)⟩
theorem supNorm_precomp (τ : σ ≃ σ') (A : σ' → ComplexMatrix2) :
    supNorm (precomp τ A) = supNorm A :=
  τ.iSup_comp (g := fun i => ComplexMatrix2.operatorNorm (A i))
theorem isSupOpen_precomp (τ : σ ≃ σ') {O : Set (σ → ComplexMatrix2)} (h : IsSupOpen O) :
    IsSupOpen (precomp τ ⁻¹' O) := by
  obtain ⟨hO, hA⟩ := h
  refine ⟨fun A hA' => (precomp_mem_tracelessPi τ A).1 (hO hA'), fun A hA' => ?_⟩
  obtain ⟨s, hs, hB⟩ := hA _ hA'
  refine ⟨s, hs, fun B hBm hlt => hB _ ((precomp_mem_tracelessPi τ B).2 hBm) ?_⟩
  have hsub : precomp τ B - precomp τ A = precomp τ (B - A) := rfl
  rw [hsub, supNorm_precomp]
  exact hlt
def tracelessFamily {N : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : σ ≃ Fin N)
    (w : ComplexCoordinates (N * 3)) (i : σ) : ComplexMatrix2 :=
  ComplexCoordinates.tracelessTuple b w (ν i)
theorem isHolomorphicIn_precomp {l N N' : ℕ} (hN : N = N')
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ ComplexCoordinates l) (τ : σ ≃ σ') {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → E}
    (H : ∀ ν : σ ≃ Fin N,
      ComplexCoordinates.IsHolomorphicIn (tracelessFamily b ν ⁻¹' O) (e ∘ f ∘ tracelessFamily b ν))
    (ν' : σ' ≃ Fin N') :
    ComplexCoordinates.IsHolomorphicIn (tracelessFamily b ν' ⁻¹' (precomp τ ⁻¹' O))
      (e ∘ (f ∘ precomp τ) ∘ tracelessFamily b ν') := by
  subst hN
  exact H (τ.trans ν')
theorem isHolomorphicOnTraceless_precomp [Fintype σ] [Fintype σ'] {l : ℕ} (τ : σ ≃ σ')
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : E ≃ ComplexCoordinates l}
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    (h : IsHolomorphicOnTraceless b e O f) :
    IsHolomorphicOnTraceless b e (precomp τ ⁻¹' O) (f ∘ precomp τ) :=
  ⟨isSupOpen_precomp τ h.1, fun ν' => isHolomorphicIn_precomp (Fintype.card_congr τ) b e τ h.2 ν'⟩
theorem precomp_expChartAt (r : ι ≃ ι') (p A : ι' ⊕ κ → ComplexMatrix2) :
    precomp (sumReindex r κ) (expChartAt p A) =
      expChartAt (precomp (sumReindex r κ) p) (precomp (sumReindex r κ) A) := by
  funext x
  cases x <;> rfl
theorem precomp_mem_groupLieProduct (r : ι ≃ ι') (q : ι' ⊕ κ → ComplexMatrix2) :
    q ∈ GroupLieProduct ι' κ ↔ precomp (sumReindex r κ) q ∈ GroupLieProduct ι κ := by
  constructor
  · intro h x
    cases x with
    | inl i => exact h (.inl (r i))
    | inr c => exact h (.inr c)
  · intro h x
    cases x with
    | inl i => simpa [precomp] using h (.inl (r.symm i))
    | inr c => exact h (.inr c)
theorem isHolomorphicToCoords_precomp [Fintype ι] [Fintype ι'] [Fintype κ] {l : ℕ}
    (r : ι ≃ ι') {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ) :
    IsHolomorphicToCoords b e (precomp (sumReindex r κ) ⁻¹' W)
      (Φ ∘ precomp (sumReindex r κ)) := by
  obtain ⟨hW, hc, hp⟩ := h
  refine ⟨isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r) hW,
    hc.comp (continuous_precomp _).continuousOn (mapsTo_preimage _ _), fun p hpW => ?_⟩
  obtain ⟨O, h0, hA, hO⟩ := hp _ hpW
  refine ⟨precomp (sumReindex r κ) ⁻¹' O, h0, fun A hA' => ?_, ?_⟩
  · rw [mem_preimage, precomp_expChartAt]
    exact hA _ hA'
  · have hfun : (Φ ∘ precomp (sumReindex r κ)) ∘ expChartAt p =
        (Φ ∘ expChartAt (precomp (sumReindex r κ) p)) ∘ precomp (sumReindex r κ) := by
      funext A
      simp only [Function.comp, precomp_expChartAt]
    rw [hfun]
    exact isHolomorphicOnTraceless_precomp _ hO
theorem isHolomorphicToTraceless_precomp [Fintype ι] [Fintype ι'] [Fintype κ] (r : ι ≃ ι')
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToTraceless b W Φ) :
    IsHolomorphicToTraceless b (precomp (sumReindex r κ) ⁻¹' W)
      (Φ ∘ precomp (sumReindex r κ)) :=
  ⟨fun _ hq => h.1 hq, isHolomorphicToCoords_precomp r h.2⟩
theorem isHolomorphicToUnimodular_precomp [Fintype ι] [Fintype ι'] [Fintype κ] (r : ι ≃ ι')
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToUnimodular b W Φ) :
    IsHolomorphicToUnimodular b (precomp (sumReindex r κ) ⁻¹' W)
      (Φ ∘ precomp (sumReindex r κ)) := by
  obtain ⟨hW, hm, hc, hp⟩ := h
  refine ⟨isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r) hW, fun _ hq => hm hq,
    hc.comp (continuous_precomp _).continuousOn (mapsTo_preimage _ _), fun p hpW => ?_⟩
  obtain ⟨O, h0, hA, hO⟩ := hp _ hpW
  refine ⟨precomp (sumReindex r κ) ⁻¹' O, h0, fun A hA' => ?_, ?_⟩
  · simp only [mem_preimage, Function.comp, precomp_expChartAt]
    exact hA _ hA'
  · have hfun : (fun A => ComplexMatrix2.logSeries
        ((Φ ∘ precomp (sumReindex r κ)) (expChartAt p A) *
          ((Φ ∘ precomp (sumReindex r κ)) p)⁻¹)) =
        (fun A => ComplexMatrix2.logSeries (Φ (expChartAt (precomp (sumReindex r κ) p) A) *
          (Φ (precomp (sumReindex r κ) p))⁻¹)) ∘ precomp (sumReindex r κ) := by
      funext A
      simp only [Function.comp, precomp_expChartAt]
    rw [hfun]
    exact isHolomorphicOnTraceless_precomp _ hO
theorem isHolomorphicToProduct_precomp [Fintype ι] [Fintype ι'] [Fintype κ] {R' R₂ : Type}
    (r : ι ≃ ι') (t : R' ≃ R₂) {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → R' ⊕ κ' → ComplexMatrix2}
    (h : IsHolomorphicToProduct b W Ψ) :
    IsHolomorphicToProduct b (precomp (sumReindex r κ) ⁻¹' W)
      fun q => precomp (sumReindex t.symm κ') (Ψ (precomp (sumReindex r κ) q)) := by
  obtain ⟨hW, hg, ha⟩ := h
  refine ⟨isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r) hW, fun i => ?_, fun c => ?_⟩
  · have hfun : (fun p => precomp (sumReindex t.symm κ')
        (Ψ (precomp (sumReindex r κ) p)) (.inl i)) =
        (fun p => Ψ p (.inl (t.symm i))) ∘ precomp (sumReindex r κ) := rfl
    rw [hfun]
    exact isHolomorphicToUnimodular_precomp r (hg (t.symm i))
  · have hfun : (fun p => precomp (sumReindex t.symm κ')
        (Ψ (precomp (sumReindex r κ) p)) (.inr c)) =
        (fun p => Ψ p (.inr c)) ∘ precomp (sumReindex r κ) := rfl
    rw [hfun]
    exact isHolomorphicToTraceless_precomp r (ha c)
theorem precomp_mem_compactPi (τ : σ ≃ σ') (w : σ' → ComplexMatrix2) :
    precomp τ w ∈ compactPi σ ↔ w ∈ compactPi σ' :=
  ⟨fun h i => by simpa [precomp] using h (τ.symm i), fun h i => h (τ i)⟩
theorem precomp_mem_subspaceTimesGroup (r : ι ≃ ι') (F : Submodule ℝ (κ → ComplexMatrix2))
    (q : ι' ⊕ κ → ComplexMatrix2) :
    q ∈ subspaceTimesGroup F ι' ↔ precomp (sumReindex r κ) q ∈ subspaceTimesGroup F ι := by
  change (algebraComponent q ∈ F ∧ groupComponent q ∈ compactPi ι') ↔
    (algebraComponent q ∈ F ∧ precomp r (groupComponent q) ∈ compactPi ι)
  rw [precomp_mem_compactPi]
theorem isSubspaceAnalyticToCoords_precomp [Fintype ι] [Fintype ι'] [Fintype κ] {l : ℕ}
    (r : ι ≃ ι') {F : Submodule ℝ (κ → ComplexMatrix2)} {𝒲 : Set (ι ⊕ κ → ComplexMatrix2)}
    {f : (ι ⊕ κ → ComplexMatrix2) → ComplexCoordinates l}
    (h : IsSubspaceAnalyticToCoords F 𝒲 f) :
    IsSubspaceAnalyticToCoords F (precomp (sumReindex r κ) ⁻¹' 𝒲)
      (f ∘ precomp (sumReindex r κ)) := by
  obtain ⟨⟨hF, h𝒲⟩, hp⟩ := h
  refine ⟨⟨hF, isRelativelyOpen_precomp _ (precomp_mem_subspaceTimesGroup r F) h𝒲⟩,
    fun p hpW => ?_⟩
  obtain ⟨𝒳, hp𝒳, h𝒳, hsub, Φ, hΦ, hEq⟩ := hp _ hpW
  exact ⟨precomp (sumReindex r κ) ⁻¹' 𝒳, hp𝒳,
    isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r) h𝒳,
    fun q hq => hsub ⟨hq.1, (precomp_mem_subspaceTimesGroup r F q).1 hq.2⟩,
    Φ ∘ precomp (sumReindex r κ),
    fun b => isHolomorphicToCoords_precomp r (hΦ b),
    fun q hq => hEq ⟨hq.1, (precomp_mem_subspaceTimesGroup r F q).1 hq.2⟩⟩
theorem isSubspaceAnalyticToProduct_precomp [Fintype ι] [Fintype ι'] [Fintype κ] {R' R₂ : Type}
    (r : ι ≃ ι') (t : R' ≃ R₂) {F : Submodule ℝ (κ → ComplexMatrix2)}
    {F' : Submodule ℝ (κ' → ComplexMatrix2)}
    {𝒲 : Set (ι ⊕ κ → ComplexMatrix2)} {f : (ι ⊕ κ → ComplexMatrix2) → R' ⊕ κ' → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct F F' 𝒲 f) :
    IsSubspaceAnalyticToProduct F F' (precomp (sumReindex r κ) ⁻¹' 𝒲)
      fun q => precomp (sumReindex t.symm κ') (f (precomp (sumReindex r κ) q)) := by
  obtain ⟨⟨hF, h𝒲⟩, hF', hm, hp⟩ := h
  refine ⟨⟨hF, isRelativelyOpen_precomp _ (precomp_mem_subspaceTimesGroup r F) h𝒲⟩, hF',
    fun q hq => (precomp_mem_subspaceTimesGroup t.symm F' _).1 (hm hq), fun p hpW => ?_⟩
  obtain ⟨𝒳, hp𝒳, h𝒳, hsub, Ψ, hΨ, hEq⟩ := hp _ hpW
  refine ⟨precomp (sumReindex r κ) ⁻¹' 𝒳, hp𝒳,
    isRelativelyOpen_precomp _ (precomp_mem_groupLieProduct r) h𝒳,
    fun q hq => hsub ⟨hq.1, (precomp_mem_subspaceTimesGroup r F q).1 hq.2⟩,
    fun q => precomp (sumReindex t.symm κ') (Ψ (precomp (sumReindex r κ) q)),
    fun b => isHolomorphicToProduct_precomp r t (hΨ b), fun q hq => ?_⟩
  exact congrArg (precomp (sumReindex t.symm κ'))
    (hEq ⟨hq.1, (precomp_mem_subspaceTimesGroup r F q).1 hq.2⟩)
end Reindexing
section Transport
variable {ι ι' : Type}
theorem transportTotal_symm_transportTotal {V : Type} (e : ι ≃ ι') (f : ι → V) :
    transportTotal e.symm (transportTotal e f) = f := by
  funext x
  simp [transportTotal]
theorem transportTotal_transportTotal_symm {V : Type} (e : ι ≃ ι') (f : ι' → V) :
    transportTotal e (transportTotal e.symm f) = f := by
  funext x
  simp [transportTotal]
theorem transportTotal_injective {V : Type} (e : ι ≃ ι') :
    Function.Injective (transportTotal e : (ι → V) → ι' → V) :=
  Function.LeftInverse.injective (transportTotal_symm_transportTotal e)
theorem image_transportTotal_symm_image {V : Type} (e : ι ≃ ι') (S : Set (ι → V)) :
    transportTotal e.symm '' (transportTotal e '' S) = S := by
  rw [image_image]
  simp only [transportTotal_symm_transportTotal, image_id']
def transportHomeomorph (e : ι ≃ ι') : (ι → ComplexMatrix2) ≃ₜ (ι' → ComplexMatrix2) where
  toFun := transportTotal e
  invFun := transportTotal e.symm
  left_inv := transportTotal_symm_transportTotal e
  right_inv := transportTotal_transportTotal_symm e
  continuous_toFun := continuous_precomp e.symm
  continuous_invFun := continuous_precomp e
theorem preservesOpenAndNhdsOfOne_transportTotal (e : ι ≃ ι') {P : Set (ι → ComplexMatrix2)}
    {P' : Set (ι' → ComplexMatrix2)} (hP : transportTotal e '' P = P') :
    PreservesOpenAndNhdsOfOne P P' (transportTotal e) := by
  intro S hS
  have hinj : Function.Injective (transportTotal e : (ι → ComplexMatrix2) → ι' → ComplexMatrix2) :=
    transportTotal_injective e
  constructor
  · constructor
    · rintro ⟨O, hO, rfl⟩
      refine ⟨transportTotal e '' O, (transportHomeomorph e).isOpenMap _ hO, ?_⟩
      rw [image_inter hinj, hP]
    · rintro ⟨O', hO', hE⟩
      refine ⟨transportTotal e ⁻¹' O', hO'.preimage (transportHomeomorph e).continuous, ?_⟩
      ext V
      constructor
      · intro hV
        have hmem : transportTotal e V ∈ O' ∩ P' := hE ▸ mem_image_of_mem _ hV
        exact ⟨hmem.1, hS hV⟩
      · rintro ⟨hV, hVP⟩
        have hmem : transportTotal e V ∈ transportTotal e '' S := by
          rw [hE]
          exact ⟨hV, hP ▸ mem_image_of_mem _ hVP⟩
        exact hinj.mem_set_image.1 hmem
  · have hone : transportTotal e (fun _ : ι => (1 : ComplexMatrix2)) = fun _ => 1 := rfl
    have hmap : map (transportTotal e) (𝓝[P] fun _ : ι => (1 : ComplexMatrix2)) =
        𝓝[P'] fun _ : ι' => (1 : ComplexMatrix2) := by
      have := (transportHomeomorph e).isEmbedding.map_nhdsWithin_eq P
        fun _ : ι => (1 : ComplexMatrix2)
      rw [← hP, ← hone]
      exact this
    unfold EventuallyNearIdentity
    rw [← hmap, Filter.eventually_map]
    simp only [hinj.mem_set_image]
end Transport
section Edges
variable {L n k i n₂ k₂ i₂ n₃ k₃ i₃ n₄ k₄ i₄ : ℕ}
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
theorem transportTotal_mem_fieldsIn {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) {𝒢 : Set ComplexMatrix2} {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i 𝒢) :
    transportTotal e V ∈ fieldsIn L n₂ k₂ i₂ 𝒢 := by
  refine ⟨fun b _ => hV.1 _ (mem_univ _), fun b _ => ?_⟩
  change V (e.symm b.opposite) = (V (e.symm b))⁻¹
  rw [he.symm.opposite]
  exact hV.2 _ (mem_univ _)
theorem transportTotal_mem_fieldSpace {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) :
    transportTotal e V ∈ fieldSpace L n₂ k₂ i₂ :=
  transportTotal_mem_fieldsIn he hV
theorem image_fieldSpace {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e) :
    transportTotal e '' fieldSpace L n k i = fieldSpace L n₂ k₂ i₂ := by
  apply Subset.antisymm
  · rintro _ ⟨V, hV, rfl⟩
    exact transportTotal_mem_fieldSpace he hV
  · intro W hW
    exact ⟨transportTotal e.symm W, transportTotal_mem_fieldSpace he.symm hW,
      transportTotal_transportTotal_symm e W⟩
theorem transportTotal_mem_edgeFormSpace {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e)
    {B : Edge L n k i → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k i) :
    transportTotal e B ∈ edgeFormSpace L n₂ k₂ i₂ := by
  refine ⟨fun b hb => hB.1 _ ((he.symm.positive b).2 hb), fun b => ?_⟩
  change B (e.symm b.opposite) = -B (e.symm b)
  rw [he.symm.opposite]
  exact hB.2 _
def edgeFormEquiv {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e) :
    edgeFormSpace L n k i ≃ₗ[ℝ] edgeFormSpace L n₂ k₂ i₂ where
  toFun B := ⟨transportTotal e B, transportTotal_mem_edgeFormSpace he B.2⟩
  invFun B := ⟨transportTotal e.symm B, transportTotal_mem_edgeFormSpace he.symm B.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv B := Subtype.ext (transportTotal_symm_transportTotal e B.1)
  right_inv B := Subtype.ext (transportTotal_transportTotal_symm e B.1)
theorem edgeFormEquiv_apply {e : Edge L n k i ≃ Edge L n₂ k₂ i₂} (he : PreservesOrientation e)
    (B : edgeFormSpace L n k i) :
    (edgeFormEquiv he B : Edge L n₂ k₂ i₂ → ComplexMatrix2) =
      transportTotal e (B : Edge L n k i → ComplexMatrix2) := rfl
theorem edgeFormOfPositiveValues_mem
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k i → ComplexMatrix2}
    (hw : w ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k i)) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k i := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [edgeFormOfPositiveValues, dif_pos hb]
    exact hw _ (mem_univ _)
  · rcases hX b with ⟨hb, hb'⟩ | ⟨hb', hb⟩
    · have hbb : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [edgeFormOfPositiveValues, dif_pos hb, dif_neg hb', dif_pos hbb]
      rfl
    · simp only [edgeFormOfPositiveValues, dif_pos hb', dif_neg hb]
      simp
def edgeFormEquivPositiveValues
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    edgeFormSpace L n k i ≃ₗ[ℝ]
      Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k i) :=
  LinearEquiv.ofBijective
    { toFun := fun B => ⟨restrictToPositiveEdges (B : Edge L n k i → ComplexMatrix2),
        fun b _ => B.2.1 _ b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } (by
    constructor
    · intro B B' h
      have hpos : ∀ b : Edge L n k i, b.IsPositivelyOriented →
          (B : Edge L n k i → ComplexMatrix2) b = (B' : Edge L n k i → ComplexMatrix2) b :=
        fun b hb => congrFun (congrArg Subtype.val h) ⟨b, hb⟩
      refine Subtype.ext (funext fun b => ?_)
      rcases hX b with ⟨hb, -⟩ | ⟨hb, -⟩
      · exact hpos b hb
      · have hB := B.2.2 b.opposite
        have hB' := B'.2.2 b.opposite
        have hrr : b.opposite.opposite = b := rfl
        rw [hrr] at hB hB'
        rw [hB, hB', hpos _ hb]
    · intro w
      refine ⟨⟨edgeFormOfPositiveValues w.1, edgeFormOfPositiveValues_mem hX w.2⟩, ?_⟩
      refine Subtype.ext (funext fun b => ?_)
      change edgeFormOfPositiveValues w.1 b.1 = w.1 b
      simp only [edgeFormOfPositiveValues, dif_pos b.2])
theorem edgeFormPairing_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (B B' : Edge L n k i → ComplexMatrix2) :
    edgeFormPairing (transportTotal e B) (transportTotal e B') = edgeFormPairing B B' := by
  unfold edgeFormPairing traceFinsumPairing
  rw [← finsum_comp_equiv (positiveEdgeEquiv he)]
  refine finsum_congr fun b => ?_
  simp [restrictToPositiveEdges, transportTotal, positiveEdgeEquiv]
theorem transportTotal_expTwist {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (B V : Edge L n k i → ComplexMatrix2) :
    transportTotal e (PeriodicLattice.expTwist B V) =
      PeriodicLattice.expTwist (transportTotal e B) (transportTotal e V) := by
  funext b
  have hp := he.symm.positive b
  simp only [transportTotal, Function.comp, PeriodicLattice.expTwist, he.symm.opposite]
  by_cases h : b.IsPositivelyOriented
  · rw [if_pos h, if_pos (hp.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hp.1 h'))]
theorem restrictToPositiveEdges_image {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (𝔇 : Set (Edge L n k i → ComplexMatrix2)) :
    restrictToPositiveEdges '' (transportTotal e '' 𝔇) =
      precomp (positiveEdgeEquiv he) ⁻¹' (restrictToPositiveEdges '' 𝔇) := by
  ext w
  constructor
  · rintro ⟨_, ⟨V, hV, rfl⟩, rfl⟩
    refine ⟨V, hV, ?_⟩
    funext b
    simp [restrictToPositiveEdges, precomp, transportTotal, positiveEdgeEquiv]
  · rintro ⟨V, hV, hw⟩
    refine ⟨_, ⟨V, hV, rfl⟩, ?_⟩
    funext b
    have hb := congrFun hw ((positiveEdgeEquiv he).symm b)
    simp only [precomp, Function.comp, Equiv.apply_symm_apply] at hb
    rw [← hb]
    rfl
theorem isOpenFieldSet_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e)
    {𝒢 : Set ComplexMatrix2} {𝔇 : Set (Edge L n k i → ComplexMatrix2)} (h : IsOpenFieldSet 𝒢 𝔇) :
    IsOpenFieldSet 𝒢 (transportTotal e '' 𝔇) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact transportTotal_mem_fieldsIn he (h.1 hV)
  · rw [restrictToPositiveEdges_image he]
    refine isRelativelyOpen_precomp _ (fun q => ?_) h.2
    exact ⟨fun hq b => hq _, fun hq b => by simpa [precomp] using hq ((positiveEdgeEquiv he).symm b)⟩
theorem isOpenFieldSet_iff_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e)
    {𝒢 : Set ComplexMatrix2} {𝔇 : Set (Edge L n k i → ComplexMatrix2)} :
    IsOpenFieldSet 𝒢 𝔇 ↔ IsOpenFieldSet 𝒢 (transportTotal e '' 𝔇) :=
  ⟨isOpenFieldSet_transportTotal he, fun h => by
    simpa only [image_transportTotal_symm_image] using isOpenFieldSet_transportTotal he.symm h⟩
theorem transportTotal_fieldOfPositiveValues {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (w : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :
    transportTotal e (fieldOfPositiveValues (precomp (positiveEdgeEquiv he) w)) =
      fieldOfPositiveValues w := by
  funext b
  change fieldOfPositiveValues (precomp (positiveEdgeEquiv he) w) (e.symm b) = _
  have hp := he.symm.positive b
  have hr := he.symm.positive b.opposite
  rw [he.symm.opposite] at hr
  unfold fieldOfPositiveValues
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h, dif_pos (hp.2 h)]
    exact congrArg w (Subtype.ext (e.apply_symm_apply b))
  · rw [dif_neg h, dif_neg (fun h' => h (hp.1 h'))]
    by_cases h' : b.opposite.IsPositivelyOriented
    · rw [dif_pos h', dif_pos (hr.2 h')]
      refine congrArg (· ⁻¹) (congrArg w (Subtype.ext ?_))
      change e (e.symm b).opposite = b.opposite
      rw [he.opposite, e.apply_symm_apply]
    · rw [dif_neg h', dif_neg (fun h'' => h' (hr.1 h''))]
theorem fieldOfPositiveValues_comp {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (w : PositiveEdge L n₂ k₂ i₂ → ComplexMatrix2) :
    fieldOfPositiveValues w ∘ e = fieldOfPositiveValues (precomp (positiveEdgeEquiv he) w) := by
  rw [← transportTotal_fieldOfPositiveValues he w]
  funext b
  simp [transportTotal]
theorem positiveValues_preimage_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) (D : Set (Edge L n k i → ComplexMatrix2)) :
    {q : PositiveEdge L n₂ k₂ i₂ ⊕ Empty → ComplexMatrix2 |
        fieldOfPositiveValues (groupComponent q) ∈ transportTotal e '' D} =
      precomp (sumReindex (positiveEdgeEquiv he) Empty) ⁻¹'
        {q | fieldOfPositiveValues (groupComponent q) ∈ D} := by
  ext q
  change fieldOfPositiveValues (groupComponent q) ∈ transportTotal e '' D ↔
    fieldOfPositiveValues (precomp (positiveEdgeEquiv he) (groupComponent q)) ∈ D
  rw [← transportTotal_fieldOfPositiveValues he (groupComponent q),
    (transportTotal_injective e).mem_set_image]
theorem isSubspaceAnalyticToCoords_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) [Fintype (PositiveEdge L n k i)]
    [Fintype (PositiveEdge L n₂ k₂ i₂)] {D : Set (Edge L n k i → ComplexMatrix2)}
    {G : (Edge L n k i → ComplexMatrix2) → ComplexCoordinates 1}
    (h : IsSubspaceAnalyticToCoords (R := PositiveEdge L n k i) (S := Empty) (l := 1) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ D}
      fun q => G (fieldOfPositiveValues (groupComponent q))) :
    IsSubspaceAnalyticToCoords (R := PositiveEdge L n₂ k₂ i₂) (S := Empty) (l := 1) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ transportTotal e '' D}
      fun q => transportTotalScalar e G (fieldOfPositiveValues (groupComponent q)) := by
  have hfun : (fun q : PositiveEdge L n₂ k₂ i₂ ⊕ Empty → ComplexMatrix2 =>
      transportTotalScalar e G (fieldOfPositiveValues (groupComponent q))) =
      (fun q => G (fieldOfPositiveValues (groupComponent q))) ∘
        precomp (sumReindex (positiveEdgeEquiv he) Empty) := by
    funext q
    change G (fieldOfPositiveValues (groupComponent q) ∘ e) = _
    rw [fieldOfPositiveValues_comp he]
    rfl
  rw [positiveValues_preimage_transportTotal he, hfun]
  exact isSubspaceAnalyticToCoords_precomp _ h
theorem transportTotalScalar_symm {W : Type} (e : Edge L n k i ≃ Edge L n₂ k₂ i₂)
    (F : (Edge L n k i → ComplexMatrix2) → W) :
    transportTotalScalar e.symm (transportTotalScalar e F) = F := by
  funext X
  change F ((X ∘ e.symm) ∘ e) = F X
  congr 1
  funext b
  simp
theorem isAnalyticFieldFunction_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) {D : Set (Edge L n k i → ComplexMatrix2)}
    {F : (Edge L n k i → ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction D F) :
    IsAnalyticFieldFunction (transportTotal e '' D) (transportTotalScalar e F) := by
  obtain ⟨hD, _, hA⟩ := h
  let _ : Fintype (PositiveEdge L n₂ k₂ i₂) := Fintype.ofEquiv _ (positiveEdgeEquiv he)
  exact ⟨isOpenFieldSet_transportTotal he hD, inferInstance,
    isSubspaceAnalyticToCoords_transportTotal he (G := fun V _ => (F V : ℂ)) hA⟩
theorem isAnalyticComplexFieldFunction_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    (he : PreservesOrientation e) {D : Set (Edge L n k i → ComplexMatrix2)}
    {F : (Edge L n k i → ComplexMatrix2) → ℂ} (h : IsAnalyticComplexFieldFunction D F) :
    IsAnalyticComplexFieldFunction (transportTotal e '' D) (transportTotalScalar e F) := by
  obtain ⟨hD, _, hA⟩ := h
  let _ : Fintype (PositiveEdge L n₂ k₂ i₂) := Fintype.ofEquiv _ (positiveEdgeEquiv he)
  exact ⟨isOpenFieldSet_transportTotal he hD, inferInstance,
    isSubspaceAnalyticToCoords_transportTotal he (G := fun V _ => F V) hA⟩
theorem isAnalyticFieldMap_transportTotal {e : Edge L n k i ≃ Edge L n₂ k₂ i₂}
    {e' : Edge L n k i₃ ≃ Edge L n₂ k₂ i₄} (he : PreservesOrientation e)
    (he' : PreservesOrientation e') {D : Set (Edge L n k i → ComplexMatrix2)}
    {m : (Edge L n k i → ComplexMatrix2) → Edge L n k i₃ → ComplexMatrix2}
    (h : IsAnalyticFieldMap D m) :
    IsAnalyticFieldMap (transportTotal e '' D) (transportTotalFunValued e e' m) := by
  obtain ⟨hD, hm, _, _, hA⟩ := h
  let _ : Fintype (PositiveEdge L n₂ k₂ i₂) := Fintype.ofEquiv _ (positiveEdgeEquiv he)
  let _ : Fintype (PositiveEdge L n₂ k₂ i₄) := Fintype.ofEquiv _ (positiveEdgeEquiv he')
  refine ⟨isOpenFieldSet_transportTotal he hD, ?_, inferInstance, inferInstance, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    rw [transportTotalFunValued_transportTotal]
    exact transportTotal_mem_fieldSpace he' (hm hV)
  · have hfun : (fun q : PositiveEdge L n₂ k₂ i₂ ⊕ Empty → ComplexMatrix2 =>
        ofParts (restrictToPositiveEdges (transportTotalFunValued e e' m
          (fieldOfPositiveValues (groupComponent q)))) (Empty.elim : Empty → ComplexMatrix2)) =
        fun q => precomp (sumReindex (positiveEdgeEquiv he').symm Empty)
          ((fun q : PositiveEdge L n k i ⊕ Empty → ComplexMatrix2 =>
            ofParts (restrictToPositiveEdges (m (fieldOfPositiveValues (groupComponent q))))
              (Empty.elim : Empty → ComplexMatrix2))
            (precomp (sumReindex (positiveEdgeEquiv he) Empty) q)) := by
      funext q x
      cases x with
      | inr c => exact c.elim
      | inl b =>
        change transportTotal e' (m (fieldOfPositiveValues (groupComponent q) ∘ e)) b.1 = _
        rw [fieldOfPositiveValues_comp he]
        rfl
    rw [positiveValues_preimage_transportTotal he, hfun]
    exact isSubspaceAnalyticToProduct_precomp _ _ hA
end Edges
end ScalingTransport
open ScalingTransport in
theorem scalingNearTrivialField_holds (h₁ : ScalingPropertiesStatement)
    (h₂ : PeriodicLattice.LevelBondOrientationDichotomy) :
    ScalingNearTrivialField := by
  intro L n k j i i' hL hj hS hn hi hi'
  have hat := ((h₁ L k j hS hj).1 n hn).atLevel
  have keeps : ∀ a ≤ j, PreservesOrientation (scaleEdge (n := n) hL hj a) := fun a ha =>
    { positive := fun b => by
        have himg := (hat a ha).image_positive
        constructor
        · intro hb
          have hmem : scaleEdge (n := n) hL hj a b ∈
              scaleEdge (n := n) hL hj a '' {b | b.IsPositivelyOriented} := by
            rw [himg]
            exact hb
          obtain ⟨b', hb', hE⟩ := hmem
          rw [← (scaleEdge (n := n) hL hj a).injective hE]
          exact hb'
        · intro hb
          have hmem : scaleEdge (n := n) hL hj a b ∈
              scaleEdge (n := n) hL hj a '' {b | b.IsPositivelyOriented} :=
            mem_image_of_mem _ hb
          rw [himg] at hmem
          exact hmem
      opposite := (hat a ha).edge_opposite }
  have he := keeps i hi
  have he' := keeps i' hi'
  have hX : ∀ b : Edge L (scaledExponent n k j) j i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
    have key : ∀ d : ℤ, d = PeriodicLattice.levelDepth (j + 1) (i + 1) →
        ∀ b : PeriodicLattice.Bond L (scaledExponent n k j) d,
          Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
      rintro _ rfl b
      exact h₂ L _ (j + 1) hS (by simp only [scaledExponent]; omega) (by omega) (i + 1)
        (by omega) b
    exact key _ (by simp [PeriodicLattice.levelDepth])
  have hsite : transportTotal (scaleVertex (n := n) hL hj i).toEquiv ''
      gaugeGroupAt L n k i = gaugeGroupAt L (scaledExponent n k j) j i := by
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩ x
      exact hu _
    · intro u hu
      exact ⟨transportTotal (scaleVertex (n := n) hL hj i).toEquiv.symm u, fun x => hu _,
        transportTotal_transportTotal_symm _ u⟩
  refine ⟨⟨?_, rfl, ⟨(edgeFormEquiv he).trans (edgeFormEquivPositiveValues hX), fun B => rfl⟩,
    ⟨edgeFormEquiv he, edgeFormEquiv_apply he⟩,
    fun B _ B' _ => edgeFormPairing_transportTotal he B B',
    fun V _ B _ => transportTotal_expTwist he B V⟩,
    ⟨preservesOpenAndNhdsOfOne_transportTotal _ (image_fieldSpace he),
    fun S _ => isOpenFieldSet_iff_transportTotal he, ?_,
    preservesOpenAndNhdsOfOne_transportTotal _ hsite⟩, ?_⟩
  · refine ⟨fun V hV => transportTotal_mem_fieldSpace he hV,
      (transportTotal_injective _).injOn, ?_⟩
    rw [SurjOn, image_fieldSpace he]
  · rw [← hsite]
    exact mapsTo_image _ _
  · intro D _
    refine ⟨fun F => ⟨isAnalyticFieldFunction_transportTotal he, fun h => ?_⟩,
      fun F => ⟨isAnalyticComplexFieldFunction_transportTotal he, fun h => ?_⟩,
      fun m _ => ⟨isAnalyticFieldMap_transportTotal he he', fun h => ?_⟩⟩
    · simpa only [image_transportTotal_symm_image, transportTotalScalar_symm] using
        isAnalyticFieldFunction_transportTotal he.symm h
    · simpa only [image_transportTotal_symm_image, transportTotalScalar_symm] using
        isAnalyticComplexFieldFunction_transportTotal he.symm h
    · have hback := isAnalyticFieldMap_transportTotal he.symm he'.symm h
      rw [image_transportTotal_symm_image] at hback
      have hm : transportTotalFunValued (scaleEdge (n := n) hL hj i).symm
          (scaleEdge (n := n) hL hj i').symm
          (transportTotalFunValued (scaleEdge hL hj i) (scaleEdge hL hj i') m) = m := by
        funext X b
        simp [transportTotalFunValued, transportTotal, Function.comp_def]
      rwa [hm] at hback
end YangMills.Construction.Tower
end
