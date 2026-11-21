import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.RestrictionsSumsAndCoordinatesOfRealAnalyticMaps
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.Subspaces.LocalAnalyticity
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
open YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy
open YangMills.Construction.Coordinates
section HolomorphicMaps
variable {ι κ ι' κ' T : Type}
theorem isRelativelyOpen_inter_open {X : Type} [TopologicalSpace X] {P D U : Set X}
    (hD : ComplexMatrix2.IsRelativelyOpen P D) (hU : IsOpen U) :
    ComplexMatrix2.IsRelativelyOpen P (D ∩ U) := by
  obtain ⟨V, hV, rfl⟩ := hD
  refine ⟨V ∩ U, hV.inter hU, ?_⟩
  ext x
  simp only [mem_inter_iff]
  tauto
theorem isSupOpen_inter {σ : Type} {O₁ O₂ : Set (σ → ComplexMatrix2)} (h₁ : IsSupOpen O₁)
    (h₂ : IsSupOpen O₂) : IsSupOpen (O₁ ∩ O₂) := by apply _root_.YangMills.SharedProofs.p44648 <;> assumption
theorem isHolomorphicOnTraceless_mono {σ : Type} [Fintype σ] {l : ℕ}
    (hT : TracelessTopologiesAgree σ) {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : T ≃ ComplexCoordinates l} {O O' : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → T}
    (h : IsHolomorphicOnTraceless b e O f) (hO' : IsSupOpen O') (hs : O' ⊆ O) :
    IsHolomorphicOnTraceless b e O' f := by
  refine ⟨hO', fun ν => ?_⟩
  obtain ⟨-, hcont, hdiff⟩ := h.2 ν
  exact ⟨((hT O' hO'.1).2 b ν).1 hO', hcont.mono (preimage_mono hs),
    fun a ha j => hdiff a (hs ha) j⟩
variable [Fintype ι] [Fintype κ]
theorem isSupOpen_inter_expChartAt_preimage (hT : TracelessTopologiesAgree (ι ⊕ κ))
    (hC : ExpChartLocalHomeomorph ι κ) {p : ι ⊕ κ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct ι κ) {O 𝒳 : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsSupOpen O)
    (h𝒳 : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) 𝒳) :
    IsSupOpen (O ∩ expChartAt p ⁻¹' 𝒳) := by
  obtain ⟨-, hcont, hmaps, -, -⟩ := hC p hp
  obtain ⟨U, hU, rfl⟩ := h𝒳
  obtain ⟨V, hV, hVO⟩ := ((hT O hO.1).1).1 hO
  obtain ⟨V', hV', hVeq⟩ := continuousOn_iff'.1 hcont U hU
  have hsub : O ∩ expChartAt p ⁻¹' (U ∩ GroupLieProduct ι κ) ⊆ tracelessPi (ι ⊕ κ) :=
    fun A hA => hO.1 hA.1
  refine ((hT _ hsub).1).2 ⟨V ∩ V', hV.inter hV', ?_⟩
  ext A
  constructor
  · rintro ⟨hAO, hAU, -⟩
    have hAa := hO.1 hAO
    have h1 : A ∈ expChartAt p ⁻¹' U ∩ tracelessPi (ι ⊕ κ) := ⟨hAU, hAa⟩
    rw [hVeq] at h1
    have h2 : A ∈ V ∩ tracelessPi (ι ⊕ κ) := hVO ▸ hAO
    exact ⟨⟨h2.1, h1.1⟩, hAa⟩
  · rintro ⟨⟨hAV, hAV'⟩, hAa⟩
    have h1 : A ∈ expChartAt p ⁻¹' U ∩ tracelessPi (ι ⊕ κ) := by
      rw [hVeq]
      exact ⟨hAV', hAa⟩
    have h2 : A ∈ O := by
      rw [hVO]
      exact ⟨hAV, hAa⟩
    exact ⟨h2, h1.1, hmaps hAa⟩
theorem subset_of_isRelativelyOpen {X : Type} [TopologicalSpace X] {P D : Set X}
    (hD : ComplexMatrix2.IsRelativelyOpen P D) : D ⊆ P := by apply _root_.YangMills.SharedProofs.p9583 <;> assumption
theorem isHolomorphicToCoords_mono (hT : TracelessTopologiesAgree (ι ⊕ κ))
    (hC : ExpChartLocalHomeomorph ι κ) {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : T ≃ ComplexCoordinates l}
    {𝒳 𝒳' : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → T}
    (h : IsHolomorphicToCoords b e 𝒳 Φ) (hs : 𝒳' ⊆ 𝒳)
    (ho : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) 𝒳') :
    IsHolomorphicToCoords b e 𝒳' Φ := by
  refine ⟨ho, h.2.1.mono hs, fun p hp => ?_⟩
  obtain ⟨O, h0, hin, hO⟩ := h.2.2 p (hs hp)
  have hpP := subset_of_isRelativelyOpen ho hp
  have hex0 : expChartAt p 0 = p := (hC p hpP).2.2.2.1
  refine ⟨O ∩ expChartAt p ⁻¹' 𝒳', ⟨h0, ?_⟩, fun A hA => hA.2,
    isHolomorphicOnTraceless_mono hT hO (isSupOpen_inter_expChartAt_preimage hT hC hpP hO.1 ho)
      inter_subset_left⟩
  rw [mem_preimage, hex0]
  exact hp
theorem isHolomorphicToUnimodular_mono (hT : TracelessTopologiesAgree (ι ⊕ κ))
    (hC : ExpChartLocalHomeomorph ι κ)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {𝒳 𝒳' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToUnimodular b 𝒳 Φ)
    (hs : 𝒳' ⊆ 𝒳) (ho : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) 𝒳') :
    IsHolomorphicToUnimodular b 𝒳' Φ := by
  refine ⟨ho, h.2.1.mono_left hs, h.2.2.1.mono hs, fun p hp => ?_⟩
  obtain ⟨O, h0, hin, hO⟩ := h.2.2.2 p (hs hp)
  have hpP := subset_of_isRelativelyOpen ho hp
  have hex0 : expChartAt p 0 = p := (hC p hpP).2.2.2.1
  refine ⟨O ∩ expChartAt p ⁻¹' 𝒳', ⟨h0, ?_⟩, fun A hA => ⟨hA.2, (hin A hA.1).2⟩,
    isHolomorphicOnTraceless_mono hT hO (isSupOpen_inter_expChartAt_preimage hT hC hpP hO.1 ho)
      inter_subset_left⟩
  rw [mem_preimage, hex0]
  exact hp
theorem isHolomorphicToProduct_mono (hT : TracelessTopologiesAgree (ι ⊕ κ))
    (hC : ExpChartLocalHomeomorph ι κ)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {𝒳 𝒳' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2} (h : IsHolomorphicToProduct b 𝒳 Ψ)
    (hs : 𝒳' ⊆ 𝒳) (ho : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) 𝒳') :
    IsHolomorphicToProduct b 𝒳' Ψ :=
  ⟨ho, fun i => isHolomorphicToUnimodular_mono hT hC (h.2.1 i) hs ho,
    fun k => ⟨(h.2.2 k).1.mono_left hs,
      isHolomorphicToCoords_mono hT hC (h.2.2 k).2 hs ho⟩⟩
theorem isHolomorphicIn_add {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'} (hf : ComplexCoordinates.IsHolomorphicIn O f)
    (hg : ComplexCoordinates.IsHolomorphicIn O g) :
    ComplexCoordinates.IsHolomorphicIn O fun z => f z + g z := by
  refine ⟨hf.1, hf.2.1.add hg.2.1, fun a ha j => ?_⟩
  filter_upwards [hf.2.2 a ha j, hg.2.2 a ha j] with ζ h₁ h₂
  exact h₁.add h₂
theorem isHolomorphicToCoords_add (hT : TracelessTopologiesAgree (ι ⊕ κ)) {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {𝒳 : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ₁ Φ₂ : (ι ⊕ κ → ComplexMatrix2) → ComplexCoordinates l}
    (h₁ : IsHolomorphicToCoords b (Equiv.refl _) 𝒳 Φ₁)
    (h₂ : IsHolomorphicToCoords b (Equiv.refl _) 𝒳 Φ₂) :
    IsHolomorphicToCoords b (Equiv.refl _) 𝒳 fun p => Φ₁ p + Φ₂ p := by
  refine ⟨h₁.1, h₁.2.1.add h₂.2.1, fun p hp => ?_⟩
  obtain ⟨O₁, h01, hin, hO₁⟩ := h₁.2.2 p hp
  obtain ⟨O₂, h02, -, hO₂⟩ := h₂.2.2 p hp
  have hO := isSupOpen_inter hO₁.1 hO₂.1
  have a₁ := isHolomorphicOnTraceless_mono hT hO₁ hO inter_subset_left
  have a₂ := isHolomorphicOnTraceless_mono hT hO₂ hO inter_subset_right
  exact ⟨O₁ ∩ O₂, ⟨h01, h02⟩, fun A hA => hin A hA.1, hO,
    fun ν => isHolomorphicIn_add (a₁.2 ν) (a₂.2 ν)⟩
end HolomorphicMaps
variable {S R S' R' : Type}
theorem subspaceTimesGroup_subset {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) :
    subspaceTimesGroup E R ⊆ GroupLieProduct R S := by apply _root_.YangMills.SharedProofs.p6041 <;> assumption
def basisExpChartArg [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) (z : ParamSpace n R) : R ⊕ S → ComplexMatrix2 :=
  ofParts (fun ρ => Complex.I • pauliSum (angularPart ν z) ρ)
    (∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2))
theorem basisExpChart_eq_expChartAt [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) (w₀ : R ⊕ S → ComplexMatrix2)
    (z : ParamSpace n R) :
    basisExpChart e ν w₀ z = expChartAt w₀ (basisExpChartArg e ν z) := by
  funext x
  cases x <;> rfl
theorem continuous_basisExpChartArg [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) : Continuous (basisExpChartArg e ν) := by
  refine continuous_pi fun x => ?_
  cases x with
  | inl ρ =>
    change Continuous fun z : ParamSpace n R =>
      Complex.I • ∑ a, angularPart ν z ρ a • pauliFamily a
    have h : Continuous fun z : ParamSpace n R =>
        ∑ a, angularPart ν z ρ a • pauliFamily a :=
      continuous_finsetSum _ fun a _ => (continuous_apply _).smul continuous_const
    exact h.const_smul Complex.I
  | inr s =>
    change Continuous fun z : ParamSpace n R =>
      (∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2)) s
    have h : Continuous fun z : ParamSpace n R =>
        ∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2) :=
      continuous_finsetSum _ fun i _ => (continuous_apply _).smul continuous_const
    exact (continuous_apply s).comp h
theorem basisExpChartArg_mem_tracelessPi [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R)
    (z : ParamSpace n R) : basisExpChartArg e ν z ∈ tracelessPi (R ⊕ S) := by
  intro x
  cases x with
  | inl ρ =>
    refine ComplexMatrix2.traceless.smul_mem _
      (ComplexMatrix2.traceless.sum_mem fun a _ => ComplexMatrix2.traceless.smul_mem _ ?_)
    exact (pauliFamily_mem_hermitianTraceless a).2
  | inr s =>
    change (∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2)) s ∈ ComplexMatrix2.traceless
    rw [Finset.sum_apply]
    refine ComplexMatrix2.traceless.sum_mem fun i _ => ComplexMatrix2.traceless.smul_mem _ ?_
    exact ((Submodule.mem_pi.1 (hE (e i).2)) s (mem_univ s)).2
theorem continuousOn_basisExpChart [Fintype S] [Fintype R] (hC : ExpChartLocalHomeomorph R S)
    {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)} (hE : E ≤ hermitianTracelessFunctions S)
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) {w₀ : R ⊕ S → ComplexMatrix2}
    (hw : w₀ ∈ GroupLieProduct R S) (D : Set (ParamSpace n R)) :
    ContinuousOn (basisExpChart e ν w₀) D := by
  have h := (hC w₀ hw).2.1.comp (continuous_basisExpChartArg e ν).continuousOn
    (s := D) fun z _ => basisExpChartArg_mem_tracelessPi hE e ν z
  exact h.congr fun z _ => basisExpChart_eq_expChartAt e ν w₀ z
theorem zero_mem_basisExpChartSource [Fintype R] (n : ℕ) (ν : IndexEnum R) :
    (0 : ParamSpace n R) ∈ basisExpChartSource n ν := by
  refine ⟨fun j => rfl, fun ρ => ?_⟩
  have h : 0 < Real.log 2 := Real.log_pos one_lt_two
  simpa [angularPart] using pow_pos h 2
section RealAnalyticMaps
variable [Fintype S] [Fintype R]
theorem isSubspaceAnalyticToCoords_mono (hT : TracelessTopologiesAgree (R ⊕ S))
    (hC : ExpChartLocalHomeomorph R S) {E : Submodule ℝ (S → ComplexMatrix2)}
    {𝒲 𝒲₁ : Set (R ⊕ S → ComplexMatrix2)} {l : ℕ} {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
    (h : IsSubspaceAnalyticToCoords E 𝒲 f) (hs : 𝒲₁ ⊆ 𝒲)
    (ho : ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) 𝒲₁) :
    IsSubspaceAnalyticToCoords E 𝒲₁ f := by
  refine ⟨⟨h.1.1, ho⟩, fun p hp => ?_⟩
  obtain ⟨U, hU, hW⟩ := ho
  obtain ⟨𝒳, hp𝒳, h𝒳, -, Φ, hΦ, heq⟩ := h.2 p (hs hp)
  have hpU : p ∈ U := by rw [hW] at hp; exact hp.1
  have ho' := isRelativelyOpen_inter_open h𝒳 hU
  refine ⟨𝒳 ∩ U, ⟨hp𝒳, hpU⟩, ho', ?_, Φ, fun b =>
    isHolomorphicToCoords_mono hT hC (hΦ b) inter_subset_left ho', ?_⟩
  · rintro q ⟨⟨-, hqU⟩, hq⟩
    rw [hW]
    exact ⟨hqU, hq⟩
  · have hsub : (𝒳 ∩ U) ∩ subspaceTimesGroup E R ⊆ 𝒳 ∩ subspaceTimesGroup E R :=
      fun q hq => ⟨hq.1.1, hq.2⟩
    exact heq.mono hsub
theorem isSubspaceAnalyticToProduct_mono (hT : TracelessTopologiesAgree (R ⊕ S))
    (hC : ExpChartLocalHomeomorph R S) {E : Submodule ℝ (S → ComplexMatrix2)}
    {E' : Submodule ℝ (S' → ComplexMatrix2)} {𝒲 𝒲₁ : Set (R ⊕ S → ComplexMatrix2)}
    {f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct E E' 𝒲 f)
    (hs : 𝒲₁ ⊆ 𝒲) (ho : ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) 𝒲₁) :
    IsSubspaceAnalyticToProduct E E' 𝒲₁ f := by
  refine ⟨⟨h.1.1, ho⟩, h.2.1, h.2.2.1.mono_left hs, fun p hp => ?_⟩
  obtain ⟨U, hU, hW⟩ := ho
  obtain ⟨𝒳, hp𝒳, h𝒳, -, Ψ, hΨ, heq⟩ := h.2.2.2 p (hs hp)
  have hpU : p ∈ U := by rw [hW] at hp; exact hp.1
  have ho' := isRelativelyOpen_inter_open h𝒳 hU
  refine ⟨𝒳 ∩ U, ⟨hp𝒳, hpU⟩, ho', ?_, Ψ, fun b =>
    isHolomorphicToProduct_mono hT hC (hΨ b) inter_subset_left ho', ?_⟩
  · rintro q ⟨⟨-, hqU⟩, hq⟩
    rw [hW]
    exact ⟨hqU, hq⟩
  · have hsub : (𝒳 ∩ U) ∩ subspaceTimesGroup E R ⊆ 𝒳 ∩ subspaceTimesGroup E R :=
      fun q hq => ⟨hq.1.1, hq.2⟩
    exact heq.mono hsub
theorem isSubspaceAnalyticToCoords_of_local {E : Submodule ℝ (S → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)} (hW : IsOpenInSubspaceTimesGroup E 𝒲) {l : ℕ}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
    (h : ∀ p ∈ 𝒲, ∃ 𝒲₁ : Set (R ⊕ S → ComplexMatrix2), 𝒲₁ ⊆ 𝒲 ∧ p ∈ 𝒲₁ ∧
      ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) 𝒲₁ ∧
        IsSubspaceAnalyticToCoords E 𝒲₁ f) :
    IsSubspaceAnalyticToCoords E 𝒲 f := by
  refine ⟨hW, fun p hp => ?_⟩
  obtain ⟨𝒲₁, hs, hp₁, -, hf⟩ := h p hp
  obtain ⟨𝒳, hp𝒳, h𝒳, hsub, Φ, hΦ, heq⟩ := hf.2 p hp₁
  exact ⟨𝒳, hp𝒳, h𝒳, hsub.trans hs, Φ, hΦ, heq⟩
theorem isSubspaceAnalyticToCoords_add (hT : TracelessTopologiesAgree (R ⊕ S))
    (hC : ExpChartLocalHomeomorph R S) {E : Submodule ℝ (S → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)} {l : ℕ}
    {f g : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
    (hf : IsSubspaceAnalyticToCoords E 𝒲 f) (hg : IsSubspaceAnalyticToCoords E 𝒲 g) :
    IsSubspaceAnalyticToCoords E 𝒲 fun p => f p + g p := by
  refine ⟨hf.1, fun p hp => ?_⟩
  obtain ⟨𝒳₁, hp₁, ho₁, hs₁, Φ₁, hΦ₁, he₁⟩ := hf.2 p hp
  obtain ⟨𝒳₂, hp₂, ho₂, -, Φ₂, hΦ₂, he₂⟩ := hg.2 p hp
  have ho : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (𝒳₁ ∩ 𝒳₂) := by
    obtain ⟨U, hU, hU₂⟩ := ho₂
    have h := isRelativelyOpen_inter_open ho₁ hU
    have heq : 𝒳₁ ∩ 𝒳₂ = 𝒳₁ ∩ U := by
      ext q
      constructor
      · rintro ⟨h₁, h₂⟩
        rw [hU₂] at h₂
        exact ⟨h₁, h₂.1⟩
      · rintro ⟨h₁, h₂⟩
        refine ⟨h₁, ?_⟩
        rw [hU₂]
        exact ⟨h₂, subset_of_isRelativelyOpen ho₁ h₁⟩
    rwa [heq]
  refine ⟨𝒳₁ ∩ 𝒳₂, ⟨hp₁, hp₂⟩, ho, ?_, fun q => Φ₁ q + Φ₂ q, fun b =>
    isHolomorphicToCoords_add hT
      (isHolomorphicToCoords_mono hT hC (hΦ₁ b) inter_subset_left ho)
      (isHolomorphicToCoords_mono hT hC (hΦ₂ b) inter_subset_right ho), ?_⟩
  · rintro q ⟨⟨h₁, -⟩, hq⟩
    exact hs₁ ⟨h₁, hq⟩
  · rintro q ⟨⟨h₁, h₂⟩, hq⟩
    change Φ₁ q + Φ₂ q = f q + g q
    rw [he₁ ⟨h₁, hq⟩, he₂ ⟨h₂, hq⟩]
end RealAnalyticMaps
theorem localAnalyticityStatement_holds
    (hH : YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hK : YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement) :
    YangMills.Construction.Matrices.GroupLieProduct.Subspaces.LocalAnalyticity.LocalAnalyticityStatement := by
  intro S R S' R' _ _ _ _ E E' hE hE' 𝒲 hW
  have hT : TracelessTopologiesAgree (R ⊕ S) := (hH.2.1 (R ⊕ S)).1
  have hC : ExpChartLocalHomeomorph R S := (hH.2.2.2.1 R S).1
  have hKE := (hK S R S' R').2.2.2 E E' hE hE'
  have hWs : 𝒲 ⊆ subspaceTimesGroup E R := subset_of_isRelativelyOpen hW.2
  refine ⟨fun 𝒲₁ hs ho => ⟨fun l f h => isSubspaceAnalyticToCoords_mono hT hC h hs ho,
      fun f h => isSubspaceAnalyticToProduct_mono hT hC h hs ho⟩,
    ⟨fun l f h => isSubspaceAnalyticToCoords_of_local hW h, fun f hf h => ?_⟩,
    fun l f g hf hg => isSubspaceAnalyticToCoords_add hT hC hf hg, fun ν => ⟨?_, ?_⟩⟩
  · refine ⟨hW, hE', hf, fun p hp => ?_⟩
    obtain ⟨𝒲₁, hs, hp₁, -, hf₁⟩ := h p hp
    obtain ⟨𝒳, hp𝒳, h𝒳, hsub, Ψ, hΨ, heq⟩ := hf₁.2.2.2 p hp₁
    exact ⟨𝒳, hp𝒳, h𝒳, hsub.trans hs, Ψ, hΨ, heq⟩
  · intro n e w₀ hw₀
    obtain ⟨hchart, hread, -⟩ := hKE.2.2.2 n e ν w₀ hw₀
    obtain ⟨hmaps, h0, -, -, himg⟩ := hchart
    have hcont := continuousOn_basisExpChart hC hE e ν (subspaceTimesGroup_subset hE hw₀)
    have hopen : ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n ν)
        (basisExpChartSource n ν ∩ basisExpChart e ν w₀ ⁻¹' 𝒲) := by
      obtain ⟨U, hU, hWU⟩ := hW.2
      obtain ⟨V, hV, hVeq⟩ := continuousOn_iff'.1 (hcont (basisExpChartSource n ν)) U hU
      refine ⟨V, hV, ?_⟩
      ext z
      constructor
      · rintro ⟨hzD, hz⟩
        rw [mem_preimage, hWU] at hz
        have h1 : z ∈ basisExpChart e ν w₀ ⁻¹' U ∩ basisExpChartSource n ν := ⟨hz.1, hzD⟩
        rw [hVeq] at h1
        exact ⟨h1.1, hzD⟩
      · rintro ⟨hzV, hzD⟩
        have h1 : z ∈ V ∩ basisExpChartSource n ν := ⟨hzV, hzD⟩
        rw [← hVeq] at h1
        refine ⟨hzD, ?_⟩
        rw [mem_preimage, hWU]
        exact ⟨h1.1, hmaps hzD.1⟩
    refine ⟨⟨hcont _, hmaps, h0, hopen, fun hw => ?_⟩, fun hw T hTo hT0 hTs => ?_⟩
    · have h0m : (0 : ParamSpace n R) ∈ basisExpChartSource n ν ∩ basisExpChart e ν w₀ ⁻¹' 𝒲 := by
        refine ⟨zero_mem_basisExpChartSource n ν, ?_⟩
        rw [mem_preimage, h0]
        exact hw
      refine ⟨h0m, _, hopen, h0m, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · have hTo' := himg T hTo
      have hr := hread T hTo
      refine ⟨hTo', ⟨0, hT0, h0⟩, fun l f hf => ?_, fun f hf => ?_⟩
      · have hf₁ := isSubspaceAnalyticToCoords_mono hT hC hf hTs hTo'
        exact ⟨hf₁, hr.1 l f hf₁⟩
      · have hf₁ := isSubspaceAnalyticToProduct_mono hT hC hf hTs hTo'
        exact ⟨hf₁, fun k μ => hr.2 k μ f hf₁⟩
  · intro l f h
    refine isSubspaceAnalyticToCoords_of_local hW fun w₀ hw₀ => ?_
    obtain ⟨n, e, T, hTo, hT0, hTs, hf⟩ := h w₀ hw₀
    obtain ⟨hchart, -, hconv⟩ := hKE.2.2.2 n e ν w₀ (hWs hw₀)
    exact ⟨basisExpChart e ν w₀ '' T, hTs, ⟨0, hT0, hchart.2.1⟩, hchart.2.2.2.2 T hTo,
      hconv T hTo l f hf⟩
end YangMills.Construction.Matrices.GroupLieProduct.Subspaces.LocalAnalyticity
end
