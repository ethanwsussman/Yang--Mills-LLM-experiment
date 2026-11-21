import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
open Set Filter YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
open YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy renaming ExpChartTheory → ChartFacts
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy renaming
  Properties → SeriesFacts
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open YangMills.Construction.Matrices.ComplexMatrix2 renaming ExpLogEstimates → LogFacts,
  UnitaryLogarithmProperties → IntrinsicFacts
open YangMills.Construction.OneLoop renaming PauliMatrixRelations → PauliFacts
section
variable {σ ι κ ι' κ' : Type}
private theorem isHolomorphicIn_iff_differentiableOn (hM : SeriesFacts) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'} :
    ComplexCoordinates.IsHolomorphicIn O f ↔ IsOpen O ∧ DifferentiableOn ℂ f O := by
  constructor
  · intro h
    refine ⟨h.1, fun a ha => ?_⟩
    obtain ⟨L, hL⟩ := ((hM.1 N O h.1).1 N' f h).2.2.1 a ha
    exact (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt.differentiableWithinAt
  · rintro ⟨ho, hd⟩
    refine ⟨ho, hd.continuousOn, fun a ha j => ?_⟩
    have hl : Continuous fun ζ : ℂ => a + ζ • stdBasisVector j := by fun_prop
    have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ O :=
      hl.continuousAt.eventually_mem (by simpa using ho.mem_nhds ha)
    filter_upwards [hmem] with ζ hζ
    exact (hd.differentiableAt (ho.mem_nhds hζ)).comp ζ (by fun_prop)
abbrev _root_.YangMills.SharedProofs.p123 := @isHolomorphicIn_iff_differentiableOn
private def entriesEquivL : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private def piEntriesEquivL [Fintype σ] {k : ℕ} (ν : σ ≃ Fin k) : (σ → ComplexMatrix2) ≃L[ℂ]
    ComplexCoordinates (productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixPiEquiv ν with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem differentiable_matrixEquiv :
    Differentiable ℂ (matrixEquiv : ComplexMatrix2 → _) :=
  entriesEquivL.differentiable
private theorem isHolomorphicVia_of_differentiableOn (hM : SeriesFacts) [Fintype σ] {k l : ℕ}
    {E : Type} (e : E ≃ ComplexCoordinates l) (ν : σ ≃ Fin k) {O : Set (σ → ComplexMatrix2)}
    (hO : IsOpen O) {Φ : (σ → ComplexMatrix2) → E} (hΦ : DifferentiableOn ℂ (e ∘ Φ) O) :
    ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e O Φ := by
  have himg : matrixPiEquiv ν '' O = (piEntriesEquivL ν).symm ⁻¹' O := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (matrixPiEquiv ν).symm (matrixPiEquiv ν x) ∈ O
      simpa using hx
    · intro hz
      exact ⟨(matrixPiEquiv ν).symm z, hz, by simp⟩
  refine (isHolomorphicIn_iff_differentiableOn hM).2 ⟨?_, ?_⟩
  · rw [himg]
    exact hO.preimage (piEntriesEquivL ν).symm.continuous
  · rw [himg]
    exact hΦ.comp (piEntriesEquivL ν).symm.differentiable.differentiableOn (fun _ h => h)
private theorem differentiableOn_of_isHolomorphicVia (hM : SeriesFacts) {O : Set ComplexMatrix2}
    {f : ComplexMatrix2 → ComplexMatrix2}
    (h : ComplexCoordinates.IsHolomorphicVia matrixEquiv matrixEquiv O f) :
    DifferentiableOn ℂ f O := by
  obtain ⟨-, hd⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 h
  have hf : f = entriesEquivL.symm ∘ (matrixEquiv ∘ f ∘ matrixEquiv.symm) ∘ entriesEquivL := by
    funext X
    exact (entriesEquivL.symm_apply_apply (f X)).symm.trans (by simp [entriesEquivL])
  rw [hf]
  refine entriesEquivL.symm.differentiable.comp_differentiableOn (hd.comp
    entriesEquivL.differentiable.differentiableOn ?_)
  intro X hX
  exact ⟨X, hX, rfl⟩
abbrev _root_.YangMills.SharedProofs.p53137 := @differentiableOn_of_isHolomorphicVia
private theorem differentiable_matExp (hM : SeriesFacts) :
    Differentiable ℂ ComplexMatrix2.matExp := by
  have h := differentiableOn_of_isHolomorphicVia hM hM.2.2.2.2.1
  exact differentiableOn_univ.1 h
abbrev _root_.YangMills.SharedProofs.p11731 := @differentiable_matExp
private theorem differentiableOn_logSeries (hM : SeriesFacts) :
    DifferentiableOn ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall :=
  differentiableOn_of_isHolomorphicVia hM hM.2.2.2.2.2
abbrev _root_.YangMills.SharedProofs.p36036 := @differentiableOn_logSeries
private theorem continuous_expChartAt (hM : SeriesFacts) (p : ι ⊕ κ → ComplexMatrix2) :
    Continuous (expChartAt p) := by
  refine continuous_pi ?_
  rintro (i | k)
  · exact ((differentiable_matExp hM).continuous.comp (continuous_apply _)).mul continuous_const
  · exact continuous_const.add (continuous_apply _)
private theorem expChartAt_zero (p : ι ⊕ κ → ComplexMatrix2) : expChartAt p 0 = p := by
  funext i
  cases i <;> simp [expChartAt, ComplexMatrix2.matExp]
abbrev _root_.YangMills.SharedProofs.p39871 := @expChartAt_zero
private theorem subset_of_isRelativelyOpen {E : Type} [TopologicalSpace E] {P D : Set E}
    (h : ComplexMatrix2.IsRelativelyOpen P D) : D ⊆ P := by
  obtain ⟨O, -, rfl⟩ := h
  exact inter_subset_right
abbrev _root_.YangMills.SharedProofs.p9583 := @subset_of_isRelativelyOpen
private theorem coords_mono (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι] [Fintype κ]
    {E : Type} {l : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hs : W' ⊆ W) :
    IsHolomorphicToCoords b e W' Φ := by
  obtain ⟨hW, hc, hp⟩ := h
  refine ⟨hW', hc.mono hs, fun p hpW' => ?_⟩
  obtain ⟨O, h0, hmap, hT, hhol⟩ := hp p (hs hpW')
  obtain ⟨U, hU, hUe⟩ := hW'
  have hagree := (hH.2.1 (ι ⊕ κ)).1
  have hOsub : O ⊆ tracelessPi (ι ⊕ κ) := hT.1
  have hsub' : O ∩ expChartAt p ⁻¹' U ⊆ tracelessPi (ι ⊕ κ) :=
    inter_subset_left.trans hOsub
  have hopen : IsSupOpen (O ∩ expChartAt p ⁻¹' U) := by
    obtain ⟨V, hV, hVe⟩ := ((hagree O hOsub).1).1 hT
    refine ((hagree _ hsub').1).2 ⟨V ∩ expChartAt p ⁻¹' U,
      hV.inter (hU.preimage (continuous_expChartAt hM p)), ?_⟩
    rw [hVe]
    ext A
    simp only [mem_inter_iff, mem_preimage]
    tauto
  refine ⟨O ∩ expChartAt p ⁻¹' U, ⟨h0, ?_⟩, fun A hA => ?_, hopen, fun ν => ?_⟩
  · rw [mem_preimage, expChartAt_zero]
    rw [hUe] at hpW'
    exact hpW'.1
  · rw [hUe]
    exact ⟨hA.2, subset_of_isRelativelyOpen hW (hmap A hA.1)⟩
  · refine ⟨((hagree _ hsub').2 b ν).1 hopen, (hhol ν).2.1.mono ?_, fun a ha j => ?_⟩
    · exact fun z hz => hz.1
    · exact (hhol ν).2.2 a ha.1 j
end
section
variable {σ ι κ ι' κ' S R S' R' : Type}
private theorem isRelativelyOpen_self {E : Type} [TopologicalSpace E] (P : Set E) :
    ComplexMatrix2.IsRelativelyOpen P P :=
  ⟨univ, isOpen_univ, (univ_inter P).symm⟩
private theorem isRelativelyOpen_inter {E : Type} [TopologicalSpace E] {P A B : Set E}
    (hA : ComplexMatrix2.IsRelativelyOpen P A) (hB : ComplexMatrix2.IsRelativelyOpen P B) :
    ComplexMatrix2.IsRelativelyOpen P (A ∩ B) := by
  obtain ⟨U, hU, rfl⟩ := hA
  obtain ⟨V, hV, rfl⟩ := hB
  refine ⟨U ∩ V, hU.inter hV, ?_⟩
  ext x
  simp only [mem_inter_iff]
  tauto
abbrev _root_.YangMills.SharedProofs.p7081 := @isRelativelyOpen_inter
private theorem coords_of_differentiableOn (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι]
    [Fintype κ] {E : Type} {l : ℕ} (e : E ≃ ComplexCoordinates l)
    {O W : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsOpen O)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → E} (hΦ : DifferentiableOn ℂ (e ∘ Φ) O)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (hWO : W ⊆ O)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) : IsHolomorphicToCoords b e W Φ := by
  have h := (hH.2.2.2.1 ι κ).2.2 E l _ e (Fintype.equivFin _) O Φ
    (isHolomorphicVia_of_differentiableOn hM e _ hO hΦ)
  exact coords_mono hM hH (h.2 b) hW fun x hx => ⟨hWO hx, subset_of_isRelativelyOpen hW hx⟩
private theorem traceless_of_differentiableOn (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι]
    [Fintype κ] {O W : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsOpen O)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : DifferentiableOn ℂ Φ O) (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hWO : W ⊆ O) (hmaps : MapsTo Φ W (ComplexMatrix2.traceless : Set ComplexMatrix2))
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToTraceless b W Φ :=
  ⟨hmaps, coords_of_differentiableOn hM hH matrixEquiv hO
    (differentiable_matrixEquiv.comp_differentiableOn hΦ) hW hWO b⟩
private theorem unimodular_of_differentiableOn (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι]
    [Fintype κ] {O W : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsOpen O)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : DifferentiableOn ℂ Φ O) (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hWO : W ⊆ O) (hmaps : MapsTo Φ W ComplexMatrix2.unitDeterminant)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToUnimodular b W Φ :=
  ((hH.2.2.2.1 ι κ).2.1 b W Φ hW hmaps).2 (coords_of_differentiableOn hM hH matrixEquiv hO
    (differentiable_matrixEquiv.comp_differentiableOn hΦ) hW hWO b)
private theorem unimodular_mono (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToUnimodular b W Φ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hs : W' ⊆ W) :
    IsHolomorphicToUnimodular b W' Φ := by
  have g := (hH.2.2.2.1 ι κ).2.1 b
  exact (g W' Φ hW' (h.2.1.mono_left hs)).2
    (coords_mono hM hH ((g W Φ h.1 h.2.1).1 h) hW' hs)
private theorem traceless_mono (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToTraceless b W Φ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hs : W' ⊆ W) :
    IsHolomorphicToTraceless b W' Φ :=
  ⟨h.1.mono_left hs, coords_mono hM hH h.2 hW' hs⟩
private theorem product_mono (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2} (h : IsHolomorphicToProduct b W Ψ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hs : W' ⊆ W) :
    IsHolomorphicToProduct b W' Ψ :=
  ⟨hW', fun i => unimodular_mono hM hH (h.2.1 i) hW' hs,
    fun k => traceless_mono hM hH (h.2.2 k) hW' hs⟩
private theorem coords_iff_refl [Fintype ι] [Fintype κ] {E : Type} {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} (e : E ≃ ComplexCoordinates l)
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E} :
    IsHolomorphicToCoords b e W Φ ↔
      IsHolomorphicToCoords b (Equiv.refl _) W (e ∘ Φ) := Iff.rfl
private theorem coords_comp_family (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι] [Fintype κ]
    {I : Type} [Fintype I] {l l' : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {Φ : I → (ι ⊕ κ → ComplexMatrix2) → ComplexCoordinates l}
    (hΦ : ∀ i, IsHolomorphicToCoords b (Equiv.refl _) W (Φ i))
    {T : (I → ComplexCoordinates l) → ComplexCoordinates l'} (hT : Differentiable ℂ T) :
    IsHolomorphicToCoords b (Equiv.refl _) W fun q => T fun i => Φ i q := by
  refine ⟨hW, ?_, fun p hp => ?_⟩
  · exact hT.continuous.comp_continuousOn (continuousOn_pi.2 fun i => (hΦ i).2.1)
  choose O h0 hmap hTu hhol using fun i => (hΦ i).2.2 p hp
  obtain ⟨U, hU, hUe⟩ := hW
  have hagree := (hH.2.1 (ι ⊕ κ)).1
  have hpG : p ∈ GroupLieProduct ι κ := by
    rw [hUe] at hp
    exact hp.2
  have hex := (hH.2.2.2.1 ι κ).1 p hpG
  set Oc : Set (ι ⊕ κ → ComplexMatrix2) :=
    (⋂ i, O i) ∩ (tracelessPi (ι ⊕ κ) ∩ expChartAt p ⁻¹' U) with hOc
  have hsub : Oc ⊆ tracelessPi (ι ⊕ κ) := fun A hA => hA.2.1
  have hopen : IsSupOpen Oc := by
    refine ((hagree _ hsub).1).2 ?_
    choose V hV hVe using fun i => ((hagree _ (hTu i).1).1).1 (hTu i)
    refine ⟨(⋂ i, V i) ∩ expChartAt p ⁻¹' U,
      (isOpen_iInter_of_finite hV).inter (hU.preimage (continuous_expChartAt hM p)), ?_⟩
    ext A
    simp only [hOc, mem_inter_iff, mem_iInter, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨fun i => ?_, h3⟩, h2⟩
      have := h1 i
      rw [hVe i] at this
      exact this.1
    · rintro ⟨⟨h1, h3⟩, h2⟩
      refine ⟨fun i => ?_, h2, h3⟩
      rw [hVe i]
      exact ⟨h1 i, h2⟩
  refine ⟨Oc, ⟨mem_iInter.2 h0, ?_, ?_⟩, fun A hA => ?_, hopen, fun ν => ?_⟩
  · exact fun _ => ComplexMatrix2.traceless.zero_mem
  · rw [mem_preimage, expChartAt_zero]
    rw [hUe] at hp
    exact hp.1
  · rw [hUe]
    exact ⟨hA.2.2, hex.2.2.1 hA.2.1⟩
  · have hpre : IsOpen (tupleOfCoords b ν ⁻¹' Oc) := ((hagree _ hsub).2 b ν).1 hopen
    refine (isHolomorphicIn_iff_differentiableOn hM).2 ⟨hpre, ?_⟩
    have hd : ∀ i, DifferentiableOn ℂ ((Φ i ∘ expChartAt p) ∘ tupleOfCoords b ν)
        (tupleOfCoords b ν ⁻¹' Oc) := fun i =>
      (((isHolomorphicIn_iff_differentiableOn hM).1 (hhol i ν)).2).mono
        fun z hz => mem_iInter.1 hz.1 i
    exact hT.comp_differentiableOn (differentiableOn_pi.2 hd)
end
section
variable {σ ι κ ι' κ' S R S' R' : Type}
private theorem subspaceTimesGroup_subset {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) :
    subspaceTimesGroup E R ⊆ GroupLieProduct R S := by
  rintro q ⟨h1, h2⟩ (r | s)
  · have h : q (.inl r) ∈ ComplexMatrix2.specialUnitary := h2 r
    exact (Matrix.mem_specialUnitaryGroup_iff.1 h).2
  · have h : algebraComponent q s ∈ ComplexMatrix2.hermitianTraceless := hE h1 s (mem_univ s)
    exact h.2
abbrev _root_.YangMills.SharedProofs.p6041 := @subspaceTimesGroup_subset
private theorem exists_ambient_open {E : Submodule ℝ (S → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    (h : IsOpenInSubspaceTimesGroup E 𝒲) : ∃ 𝒳₁ : Set (R ⊕ S → ComplexMatrix2),
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) 𝒳₁ ∧
        𝒳₁ ∩ subspaceTimesGroup E R = 𝒲 := by
  obtain ⟨hE, O, hO, rfl⟩ := h
  refine ⟨O ∩ GroupLieProduct R S, ⟨O, hO, rfl⟩, ?_⟩
  ext q
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, subspaceTimesGroup_subset hE h2⟩, h2⟩
private theorem subset_subspaceTimesGroup {E : Submodule ℝ (S → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    (h : IsOpenInSubspaceTimesGroup E 𝒲) : 𝒲 ⊆ subspaceTimesGroup E R :=
  subset_of_isRelativelyOpen h.2
private theorem analyticToCoords_of_global (hM : SeriesFacts) (hH : ChartFacts) [Fintype S]
    [Fintype R] {l : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    (h𝒲 : IsOpenInSubspaceTimesGroup E 𝒲)
    {f Φ : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
    (hΦ : ∀ b, IsHolomorphicToCoords b (Equiv.refl _) (GroupLieProduct R S) Φ)
    (hEq : EqOn Φ f 𝒲) : IsSubspaceAnalyticToCoords E 𝒲 f := by
  obtain ⟨𝒳₁, h𝒳₁, he⟩ := exists_ambient_open h𝒲
  refine ⟨h𝒲, fun p hp => ⟨𝒳₁, ?_, h𝒳₁, he.le, Φ, fun b => ?_, ?_⟩⟩
  · rw [← he] at hp
    exact hp.1
  · exact coords_mono hM hH (hΦ b) h𝒳₁ (subset_of_isRelativelyOpen h𝒳₁)
  · rw [he]
    exact hEq
private theorem analyticToProduct_of_global (hM : SeriesFacts) (hH : ChartFacts) [Fintype S]
    [Fintype R] [Fintype S'] [Fintype R'] {E : Submodule ℝ (S → ComplexMatrix2)}
    {E' : Submodule ℝ (S' → ComplexMatrix2)}
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)} (h𝒲 : IsOpenInSubspaceTimesGroup E 𝒲)
    (hE' : E' ≤ hermitianTracelessFunctions S')
    {f Ψ : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2}
    (hmaps : MapsTo f 𝒲 (subspaceTimesGroup E' R'))
    (hΨ : ∀ b, IsHolomorphicToProduct b (GroupLieProduct R S) Ψ) (hEq : EqOn Ψ f 𝒲) :
    IsSubspaceAnalyticToProduct E E' 𝒲 f := by
  obtain ⟨𝒳₁, h𝒳₁, he⟩ := exists_ambient_open h𝒲
  refine ⟨h𝒲, hE', hmaps, fun p hp => ⟨𝒳₁, ?_, h𝒳₁, he.le, Ψ, fun b => ?_, ?_⟩⟩
  · rw [← he] at hp
    exact hp.1
  · exact product_mono hM hH (hΨ b) h𝒳₁ (subset_of_isRelativelyOpen h𝒳₁)
  · rw [he]
    exact hEq
private theorem analytic_iff_extensions (hM : SeriesFacts) (hH : ChartFacts) [Fintype S]
    [Fintype R] [Fintype S'] [Fintype R'] {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    (h𝒲 : IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions S) 𝒲) :
    AnalyticIffHolomorphicExtensions S' R' 𝒲 := by
  obtain ⟨𝒳₁, h𝒳₁, he⟩ := exists_ambient_open h𝒲
  have hsub : 𝒲 ⊆ subspaceTimesGroup (hermitianTracelessFunctions S) R :=
    subset_subspaceTimesGroup h𝒲
  have key : ∀ {𝒳 : Set (R ⊕ S → ComplexMatrix2)},
      (𝒳 ∩ 𝒳₁) ∩ subspaceTimesGroup (hermitianTracelessFunctions S) R = 𝒳 ∩ 𝒲 := by
    intro 𝒳
    rw [inter_assoc, he]
  have hp₁ : ∀ {p}, p ∈ 𝒲 → p ∈ 𝒳₁ := fun {p} hp => by
    rw [← he] at hp
    exact hp.1
  refine ⟨fun l f => ⟨?_, ?_⟩, fun f hf => ⟨?_, ?_⟩⟩
  · rintro ⟨-, h⟩
    refine ⟨h𝒲.2, fun p hp => ?_⟩
    obtain ⟨𝒳, hp𝒳, h𝒳, -, Φ, hΦ, hEq⟩ := h p hp
    exact ⟨𝒳, hp𝒳, h𝒳, Φ, hΦ, hEq.mono (inter_subset_inter_right _ hsub)⟩
  · rintro ⟨-, h⟩
    refine ⟨h𝒲, fun p hp => ?_⟩
    obtain ⟨𝒳, hp𝒳, h𝒳, Φ, hΦ, hEq⟩ := h p hp
    have ho := isRelativelyOpen_inter h𝒳 h𝒳₁
    refine ⟨𝒳 ∩ 𝒳₁, ⟨hp𝒳, hp₁ hp⟩, ho, ?_, Φ, fun b => ?_, ?_⟩
    · rw [key]
      exact inter_subset_right
    · exact coords_mono hM hH (hΦ b) ho inter_subset_left
    · rw [key]
      exact hEq
  · rintro ⟨-, -, -, h⟩
    refine ⟨h𝒲.2, hf, fun p hp => ?_⟩
    obtain ⟨𝒳, hp𝒳, h𝒳, -, Ψ, hΨ, hEq⟩ := h p hp
    exact ⟨𝒳, hp𝒳, h𝒳, Ψ, hΨ, hEq.mono (inter_subset_inter_right _ hsub)⟩
  · rintro ⟨-, -, h⟩
    refine ⟨h𝒲, le_rfl, hf, fun p hp => ?_⟩
    obtain ⟨𝒳, hp𝒳, h𝒳, Ψ, hΨ, hEq⟩ := h p hp
    have ho := isRelativelyOpen_inter h𝒳 h𝒳₁
    refine ⟨𝒳 ∩ 𝒳₁, ⟨hp𝒳, hp₁ hp⟩, ho, ?_, Ψ, fun b => ?_, ?_⟩
    · rw [key]
      exact inter_subset_right
    · exact product_mono hM hH (hΨ b) ho inter_subset_left
    · rw [key]
      exact hEq
private theorem finiteDimensional_submodules [Fintype S] : FiniteDimensionalSubmodules S := by
  intro E _
  have : FiniteDimensional ℝ (S → ComplexMatrix2) := by
    have : FiniteDimensional ℝ ComplexMatrix2 := FiniteDimensional.complexToReal ComplexMatrix2
    infer_instance
  infer_instance
private theorem differentiable_algebraComponent [Fintype ι] [Fintype κ] :
    Differentiable ℂ (algebraComponent : (ι ⊕ κ → ComplexMatrix2) → κ → ComplexMatrix2) :=
  differentiable_pi.2 fun _ => differentiable_apply _
private theorem traceless_apply_inr {ι κ : Type} {q : ι ⊕ κ → ComplexMatrix2}
    (hq : q ∈ GroupLieProduct ι κ) (k : κ) :
    q (.inr k) ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2) := hq (.inr k)
private theorem unimodular_apply_inl {ι κ : Type} {q : ι ⊕ κ → ComplexMatrix2}
    (hq : q ∈ GroupLieProduct ι κ) (i : ι) : q (.inl i) ∈ ComplexMatrix2.unitDeterminant :=
  hq (.inl i)
private theorem projections_analytic (hM : SeriesFacts) (hH : ChartFacts) [Fintype S] [Fintype R]
    {E : Submodule ℝ (S → ComplexMatrix2)} (hE : E ≤ hermitianTracelessFunctions S) :
    ProjectionsAnalytic E R := by
  have hopen : IsOpenInSubspaceTimesGroup E (subspaceTimesGroup E R) :=
    ⟨hE, isRelativelyOpen_self _⟩
  have hG : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (GroupLieProduct R S) :=
    isRelativelyOpen_self _
  refine ⟨?_, ?_⟩
  · refine analyticToProduct_of_global hM hH hopen hE ?_
      (fun b => ⟨hG, fun i => i.elim, fun k => ?_⟩) (fun _ _ => rfl)
    · intro q hq
      exact ⟨hq.1, fun i => i.elim⟩
    · exact traceless_of_differentiableOn hM hH isOpen_univ
        (differentiable_apply (Sum.inr k)).differentiableOn hG (subset_univ _)
        (fun q hq => traceless_apply_inr hq k) b
  · refine analyticToProduct_of_global hM hH hopen bot_le ?_
      (fun b => ⟨hG, fun i => ?_, fun k => k.elim⟩) (fun _ _ => rfl)
    · intro q hq
      refine ⟨?_, hq.2⟩
      rw [Submodule.mem_bot]
      exact Subsingleton.elim _ _
    · exact unimodular_of_differentiableOn hM hH isOpen_univ
        (differentiable_apply (Sum.inl i)).differentiableOn hG (subset_univ _)
        (fun q hq => unimodular_apply_inl hq i) b
private theorem constants_analytic (hM : SeriesFacts) (hH : ChartFacts) [Fintype S] [Fintype R]
    [Fintype S'] [Fintype R'] {E : Submodule ℝ (S → ComplexMatrix2)}
    {E' : Submodule ℝ (S' → ComplexMatrix2)}
    (hE' : E' ≤ hermitianTracelessFunctions S') {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    (h𝒲 : IsOpenInSubspaceTimesGroup E 𝒲) : ConstantMapsAnalytic E E' R' 𝒲 := by
  have hG : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (GroupLieProduct R S) :=
    isRelativelyOpen_self _
  refine ⟨fun l c => ?_, fun c hc => ?_⟩
  · exact analyticToCoords_of_global hM hH h𝒲 (fun b => coords_of_differentiableOn hM hH _
      isOpen_univ (differentiableOn_const _) hG (subset_univ _) b) (fun _ _ => rfl)
  · have hcG := subspaceTimesGroup_subset hE' hc
    refine analyticToProduct_of_global hM hH h𝒲 hE' (fun _ _ => hc)
      (fun b => ⟨hG, fun i => ?_, fun k => ?_⟩) (fun _ _ => rfl)
    · exact unimodular_of_differentiableOn hM hH isOpen_univ (differentiableOn_const _) hG
        (subset_univ _) (fun _ _ => unimodular_apply_inl hcG i) b
    · exact traceless_of_differentiableOn hM hH isOpen_univ (differentiableOn_const _) hG
        (subset_univ _) (fun _ _ => traceless_apply_inr hcG k) b
end
section
variable {σ ι κ ι' κ' S R S' R' : Type}
private def pauliCoeff (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ComplexMatrix2.halfTrace (X * pauliFamily a)
  map_add' X Y := by
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, add_mul, Matrix.trace_add, mul_add]
  map_smul' c X := by
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul]
    ring
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • pauliFamily a = X := by
  have ht : X 0 0 + X 1 1 = 0 := by
    have h : ComplexMatrix2.fullTrace X = 0 := hX
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using h
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCoeff, Fin.sum_univ_three, pauliFamily, OneLoop.pauliX,
      OneLoop.pauliY, OneLoop.pauliZ, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-1 / 2 : ℂ) * ht
  · linear_combination (-(1 / 2) * (X 0 1 - X 1 0)) * hI
  · linear_combination ((1 / 2) * (X 0 1 - X 1 0)) * hI
  · linear_combination (-1 / 2 : ℂ) * ht
private theorem pauliCoeff_sum_smul (υ : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, υ b • pauliFamily b) = υ a := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  fin_cases a <;>
    simp [pauliCoeff, Fin.sum_univ_three, pauliFamily, OneLoop.pauliX,
      OneLoop.pauliY, OneLoop.pauliZ, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
      Matrix.trace_fin_two]
  · ring
  · linear_combination (-υ 1) * hI
  · ring
private theorem pauliCoeff_im {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by
  have h := ComplexMatrix2.LieElement.star_fullTrace_mul
    (⟨X, hX⟩ : ComplexMatrix2.hermitianTraceless)
    (⟨pauliFamily a, pauliFamily_mem_hermitianTraceless a⟩ : ComplexMatrix2.hermitianTraceless)
  have h' : (starRingEnd ℂ) (ComplexMatrix2.fullTrace (X * pauliFamily a)) =
      ComplexMatrix2.fullTrace (X * pauliFamily a) := h
  have him := Complex.conj_eq_iff_im.1 h'
  simp [pauliCoeff, ComplexMatrix2.halfTrace, Complex.mul_im, him]
private theorem ofReal_smul_eq {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (r : ℝ) (v : V) : (r : ℂ) • v = r • v := by
  have h : (r : ℂ) = r • (1 : ℂ) := by simp
  rw [h, smul_assoc, one_smul]
open Classical in
private def pauliDirection (s : S) (a : Fin 3) : S → ComplexMatrix2 := Pi.single s (pauliFamily a)
private def complexifyMap [Fintype S] {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    (g : (S → ComplexMatrix2) →ₗ[ℝ] V) : (S → ComplexMatrix2) →ₗ[ℂ] V where
  toFun Z := ∑ s, ∑ a, pauliCoeff a (Z s) • g (pauliDirection s a)
  map_add' Y Z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by simp [mul_smul, Finset.smul_sum]
private theorem complexifyMap_apply [Fintype S] {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module ℝ V] (g : (S → ComplexMatrix2) →ₗ[ℝ] V) (Z : S → ComplexMatrix2) :
    complexifyMap g Z = ∑ s, ∑ a, pauliCoeff a (Z s) • g (pauliDirection s a) := rfl
private theorem eq_sum_pauliDirection [Fintype S] {X : S → ComplexMatrix2}
    (hX : X ∈ hermitianTracelessFunctions S) :
    X = ∑ s, ∑ a, (pauliCoeff a (X s)).re • pauliDirection s a := by
  classical
  funext t
  have ht : X t ∈ ComplexMatrix2.hermitianTraceless := hX t (mem_univ t)
  have hsl : X t ∈ ComplexMatrix2.traceless := ht.2
  simp only [Finset.sum_apply, Pi.smul_apply, pauliDirection]
  rw [Finset.sum_eq_single t]
  · conv_lhs => rw [← sum_pauliCoeff_smul hsl]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hre : pauliCoeff a (X t) = ((pauliCoeff a (X t)).re : ℂ) := by
      apply Complex.ext <;> simp [pauliCoeff_im ht a]
    rw [Pi.single_eq_same]
    conv_lhs => rw [hre]
    exact ofReal_smul_eq _ _
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Pi.single_eq_of_ne (Ne.symm hs), smul_zero]
  · simp
private theorem complexifyMap_of_real [Fintype S] {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module ℝ V] [IsScalarTower ℝ ℂ V] (g : (S → ComplexMatrix2) →ₗ[ℝ] V)
    {X : S → ComplexMatrix2} (hX : X ∈ hermitianTracelessFunctions S) :
    complexifyMap g X = g X := by
  conv_rhs => rw [eq_sum_pauliDirection hX]
  rw [complexifyMap_apply, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs : X s ∈ ComplexMatrix2.hermitianTraceless := hX s (mem_univ s)
  have hre : pauliCoeff a (X s) = ((pauliCoeff a (X s)).re : ℂ) := by
    apply Complex.ext <;> simp [pauliCoeff_im hs a]
  rw [map_smul]
  conv_lhs => rw [hre]
  exact ofReal_smul_eq _ _
private theorem exists_complex_extension [Fintype S] {E : Submodule ℝ (S → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) (c : E →ₗ[ℝ] ℝ) :
    ∃ lam : (S → ComplexMatrix2) →ₗ[ℂ] ℂ, ∀ (x : S → ComplexMatrix2) (hx : x ∈ E),
      lam x = (c ⟨x, hx⟩ : ℂ) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend c
  refine ⟨complexifyMap (Complex.ofRealCLM.toLinearMap ∘ₗ g), fun x hx => ?_⟩
  rw [complexifyMap_of_real _ (hE hx)]
  have h := LinearMap.congr_fun hg ⟨x, hx⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  simp [h]
private theorem differentiable_linearMap [Fintype S] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (C : (S → ComplexMatrix2) →ₗ[ℂ] F) [FiniteDimensional ℂ F] :
    Differentiable ℂ C :=
  (LinearMap.toContinuousLinearMap C).differentiable
private theorem linearMaps_analytic (hM : SeriesFacts) (hH : ChartFacts) [Fintype S] [Fintype S']
    {E : Submodule ℝ (S → ComplexMatrix2)} {E' : Submodule ℝ (S' → ComplexMatrix2)}
    (hE : E ≤ hermitianTracelessFunctions S) (hE' : E' ≤ hermitianTracelessFunctions S') :
    LinearMapsAnalytic E E' := by
  intro L f hf
  obtain ⟨g, hg⟩ := LinearMap.exists_extend L
  set C := complexifyMap (E'.subtype ∘ₗ g) with hC
  have hval : ∀ x ∈ E, C x = f x := by
    intro x hx
    rw [hC, complexifyMap_of_real _ (hE hx)]
    have h := LinearMap.congr_fun hg ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h ⊢
    rw [h]
    exact (hf ⟨x, hx⟩).symm
  have hCmem : ∀ Z k, C Z k ∈ ComplexMatrix2.traceless := by
    intro Z k
    rw [hC, complexifyMap_apply]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Submodule.sum_mem _ fun s _ => Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ ?_
    have h : (E'.subtype ∘ₗ g) (pauliDirection s a) ∈ hermitianTracelessFunctions S' :=
      hE' (g (pauliDirection s a)).2
    exact (h k (mem_univ k)).2
  have h𝒲 : IsOpenInSubspaceTimesGroup E
      {q : Empty ⊕ S → ComplexMatrix2 | algebraComponent q ∈ (E : Set (S → ComplexMatrix2))} := by
    refine ⟨hE, univ, isOpen_univ, ?_⟩
    ext q
    simp only [mem_ofPred_eq, univ_inter, subspaceTimesGroup, SetLike.mem_coe]
    exact ⟨fun h => ⟨h, fun i => i.elim⟩, fun h => h.1⟩
  have hG : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty S) (GroupLieProduct Empty S) :=
    isRelativelyOpen_self _
  refine analyticToProduct_of_global hM hH h𝒲 hE'
    (Ψ := fun q => ofParts Empty.elim (C (algebraComponent q)))
    ?_ (fun b => ⟨hG, fun i => i.elim, fun k => ?_⟩) ?_
  · intro q hq
    refine ⟨?_, fun i => i.elim⟩
    have h := hf ⟨algebraComponent q, hq⟩
    change f (algebraComponent q) ∈ E'
    rw [show f (algebraComponent q) = _ from h]
    exact (L _).2
  · refine traceless_of_differentiableOn hM hH isOpen_univ ?_ hG (subset_univ _)
      (fun q _ => hCmem _ k) b
    have hd : Differentiable ℂ fun q : Empty ⊕ S → ComplexMatrix2 => C (algebraComponent q) k :=
      (differentiable_apply k).comp
        ((differentiable_linearMap C).comp differentiable_algebraComponent)
    exact hd.differentiableOn
  · intro q hq
    change ofParts Empty.elim (C (algebraComponent q)) =
      ofParts Empty.elim (f (algebraComponent q))
    rw [hval _ hq]
end
section
variable {σ ι κ ι' κ' S R S' R' : Type}
private theorem pairing_analytic (hM : SeriesFacts) (hH : ChartFacts) [Fintype S] [Fintype R]
    (E : Submodule ℝ (S → ComplexMatrix2)) (𝒲 : Set (R ⊕ S → ComplexMatrix2)) :
    PairingAnalytic E 𝒲 := by
  intro S₁ S₂ R₁ R₂ _ _ _ _ E₁ E₂ f₁ f₂ h₁ h₂
  refine ⟨h₁.1, ?_, ?_, fun p hp => ?_⟩
  · rintro x ⟨hx₁, hx₂⟩ (s | s) _
    · exact h₁.2.1 hx₁ s (mem_univ s)
    · exact h₂.2.1 hx₂ s (mem_univ s)
  · intro p hp
    obtain ⟨a₁, g₁⟩ := h₁.2.2.1 hp
    obtain ⟨a₂, g₂⟩ := h₂.2.2.1 hp
    refine ⟨⟨a₁, a₂⟩, ?_⟩
    rintro (r | r)
    · exact g₁ r
    · exact g₂ r
  · obtain ⟨𝒳₁, hp₁, ho₁, hs₁, Ψ₁, hΨ₁, hE₁⟩ := h₁.2.2.2 p hp
    obtain ⟨𝒳₂, hp₂, ho₂, hs₂, Ψ₂, hΨ₂, hE₂⟩ := h₂.2.2.2 p hp
    have ho := isRelativelyOpen_inter ho₁ ho₂
    refine ⟨𝒳₁ ∩ 𝒳₂, ⟨hp₁, hp₂⟩, ho, fun x hx => hs₁ ⟨hx.1.1, hx.2⟩,
      fun q => pairPoint (Ψ₁ q) (Ψ₂ q), fun b => ⟨ho, ?_, ?_⟩, fun q hq => ?_⟩
    · rintro (r | r)
      · exact unimodular_mono hM hH ((hΨ₁ b).2.1 r) ho inter_subset_left
      · exact unimodular_mono hM hH ((hΨ₂ b).2.1 r) ho inter_subset_right
    · rintro (s | s)
      · exact traceless_mono hM hH ((hΨ₁ b).2.2 s) ho inter_subset_left
      · exact traceless_mono hM hH ((hΨ₂ b).2.2 s) ho inter_subset_right
    · change pairPoint (Ψ₁ q) (Ψ₂ q) = pairPoint (f₁ q) (f₂ q)
      rw [hE₁ ⟨hq.1.1, hq.2⟩, hE₂ ⟨hq.1.2, hq.2⟩]
private theorem composition_analytic (hM : SeriesFacts) (hH : ChartFacts)
    (b₀ : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    [Fintype S] [Fintype R] [Fintype S'] [Fintype R'] {E : Submodule ℝ (S → ComplexMatrix2)}
    {E' : Submodule ℝ (S' → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    (h𝒲 : IsOpenInSubspaceTimesGroup E 𝒲) : CompositionAnalytic E E' R' 𝒲 := by
  intro f hf
  have comp := hH.2.2.2.2.1 R S R' S'
  have hW := subset_subspaceTimesGroup h𝒲
  have hsP := subspaceTimesGroup_subset (R := R) h𝒲.1
  have hmapsf := hf.2.2.1
  have hcont : ContinuousOn f 𝒲 := by
    intro p hp
    obtain ⟨𝒳, hp𝒳, h𝒳, hsub, Ψ, hΨ, hEq⟩ := hf.2.2.2 p hp
    have hempty : IsHolomorphicToCoords b₀ (Equiv.refl (ComplexCoordinates 0))
        (∅ : Set (R' ⊕ S' → ComplexMatrix2)) (fun _ => 0) :=
      ⟨⟨∅, isOpen_empty, by simp⟩, continuousOn_empty _, by simp⟩
    have hΨc : ContinuousOn Ψ 𝒳 := (comp b₀ 𝒳 Ψ h𝒳 (hΨ b₀) _ _ _ _ _ hempty).1
    obtain ⟨U, hU, hUe⟩ := h𝒳
    have hmem : 𝒳 ∈ 𝓝[𝒲] p := by
      refine mem_nhdsWithin.2 ⟨U, hU, ?_, fun x hx => ?_⟩
      · rw [hUe] at hp𝒳
        exact hp𝒳.1
      · rw [hUe]
        exact ⟨hx.1, hsP (hW hx.2)⟩
    have h1 : ContinuousWithinAt Ψ 𝒲 p := (hΨc p hp𝒳).mono_of_mem_nhdsWithin hmem
    refine h1.congr_of_eventuallyEq ?_ (hEq ⟨hp𝒳, hW hp⟩).symm
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx𝒲
    exact (hEq ⟨hx, hW hx𝒲⟩).symm
  refine ⟨hcont, fun 𝒲' h𝒲' => ?_⟩
  have hopen : ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) (𝒲 ∩ f ⁻¹' 𝒲') := by
    obtain ⟨O', hO', hO'e⟩ := h𝒲'.2
    obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 hcont O' hO'
    obtain ⟨O, hO, hOe⟩ := h𝒲.2
    refine ⟨u ∩ O, hu.inter hO, ?_⟩
    have e1 : 𝒲 ∩ f ⁻¹' 𝒲' = f ⁻¹' O' ∩ 𝒲 := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        rw [mem_preimage, hO'e] at h2
        exact ⟨h2.1, h1⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        rw [mem_preimage, hO'e]
        exact ⟨h1, hmapsf h2⟩
    rw [e1, hue, inter_assoc, ← hOe]
  have hX : ∀ (𝒳 : Set (R ⊕ S → ComplexMatrix2)) (𝒳' : Set (R' ⊕ S' → ComplexMatrix2))
      (Ψ : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2),
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) 𝒳 →
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R' S') 𝒳' →
      (∀ b, IsHolomorphicToProduct b 𝒳 Ψ) →
      𝒳 ∩ subspaceTimesGroup E R ⊆ 𝒲 → 𝒳' ∩ subspaceTimesGroup E' R' ⊆ 𝒲' →
      EqOn Ψ f (𝒳 ∩ subspaceTimesGroup E R) →
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (𝒳 ∩ Ψ ⁻¹' 𝒳') ∧
        (𝒳 ∩ Ψ ⁻¹' 𝒳') ∩ subspaceTimesGroup E R ⊆ 𝒲 ∩ f ⁻¹' 𝒲' := by
    intro 𝒳 𝒳' Ψ h𝒳 h𝒳' hΨ hs hs' hEq
    have hc : IsHolomorphicToCoords b₀ (Equiv.refl (ComplexCoordinates 0)) 𝒳' (fun _ => 0) :=
      coords_of_differentiableOn hM hH _ isOpen_univ (differentiableOn_const _) h𝒳'
        (subset_univ _) b₀
    refine ⟨(comp b₀ 𝒳 Ψ h𝒳 (hΨ b₀) _ _ _ _ _ hc).2.1, ?_⟩
    rintro q ⟨⟨hq₁, hq₂⟩, hq₃⟩
    have hqW := hs ⟨hq₁, hq₃⟩
    refine ⟨hqW, hs' ⟨?_, hmapsf hqW⟩⟩
    rw [← hEq ⟨hq₁, hq₃⟩]
    exact hq₂
  refine ⟨hopen, fun l f' hf' => ⟨⟨h𝒲.1, hopen⟩, fun p hp => ?_⟩, fun S'' R'' _ _ E'' f' hf' =>
    ⟨⟨h𝒲.1, hopen⟩, hf'.2.1, fun p hp => hf'.2.2.1 (hmapsf hp.1 |> fun _ => hp.2),
      fun p hp => ?_⟩⟩
  · obtain ⟨𝒳, hp𝒳, h𝒳, hs, Ψ, hΨ, hEq⟩ := hf.2.2.2 p hp.1
    obtain ⟨𝒳', hp𝒳', h𝒳', hs', Φ, hΦ, hEq'⟩ := hf'.2 (f p) hp.2
    obtain ⟨hXo, hXs⟩ := hX 𝒳 𝒳' Ψ h𝒳 h𝒳' hΨ hs hs' hEq
    have hΨp : Ψ p = f p := hEq ⟨hp𝒳, hW hp.1⟩
    refine ⟨𝒳 ∩ Ψ ⁻¹' 𝒳', ⟨hp𝒳, ?_⟩, hXo, hXs, Φ ∘ Ψ,
      fun b => (comp b 𝒳 Ψ h𝒳 (hΨ b) _ _ _ _ _ (hΦ b)).2.2, fun q hq => ?_⟩
    · rw [mem_preimage, hΨp]
      exact hp𝒳'
    · have hqΨ : Ψ q = f q := hEq ⟨hq.1.1, hq.2⟩
      have h2 : Ψ q ∈ 𝒳' := hq.1.2
      rw [hqΨ] at h2
      change Φ (Ψ q) = f' (f q)
      rw [hqΨ]
      exact hEq' ⟨h2, hmapsf (hs ⟨hq.1.1, hq.2⟩)⟩
  · obtain ⟨𝒳, hp𝒳, h𝒳, hs, Ψ, hΨ, hEq⟩ := hf.2.2.2 p hp.1
    obtain ⟨𝒳', hp𝒳', h𝒳', hs', Ψ', hΨ', hEq'⟩ := hf'.2.2.2 (f p) hp.2
    obtain ⟨hXo, hXs⟩ := hX 𝒳 𝒳' Ψ h𝒳 h𝒳' hΨ hs hs' hEq
    have hΨp : Ψ p = f p := hEq ⟨hp𝒳, hW hp.1⟩
    refine ⟨𝒳 ∩ Ψ ⁻¹' 𝒳', ⟨hp𝒳, ?_⟩, hXo, hXs, Ψ' ∘ Ψ, fun b => ⟨hXo, fun i => ?_, fun k => ?_⟩,
      fun q hq => ?_⟩
    · rw [mem_preimage, hΨp]
      exact hp𝒳'
    · have hm := (hΨ' b).2.1 i
      have hc := ((hH.2.2.2.1 R' S').2.1 b 𝒳' _ h𝒳' hm.2.1).1 hm
      have hcc := (comp b 𝒳 Ψ h𝒳 (hΨ b) _ _ _ _ _ hc).2.2
      exact ((hH.2.2.2.1 R S).2.1 b _ _ hXo (fun q hq => hm.2.1 hq.2)).2 hcc
    · have hm := (hΨ' b).2.2 k
      exact ⟨fun q hq => hm.1 hq.2, (comp b 𝒳 Ψ h𝒳 (hΨ b) _ _ _ _ _ hm.2).2.2⟩
    · have hqΨ : Ψ q = f q := hEq ⟨hq.1.1, hq.2⟩
      have h2 : Ψ q ∈ 𝒳' := hq.1.2
      rw [hqΨ] at h2
      change Ψ' (Ψ q) = f' (f q)
      rw [hqΨ]
      exact hEq' ⟨h2, hmapsf (hs ⟨hq.1.1, hq.2⟩)⟩
private theorem scalarEquiv_apply (z : ℂ) (j : Fin 1) : scalarEquiv z j = z := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
private theorem differentiable_scalarEquiv : Differentiable ℂ (scalarEquiv : ℂ → _) :=
  differentiable_pi.2 fun j => by
    have h : (fun z => scalarEquiv z j) = id := funext fun z => scalarEquiv_apply z j
    rw [h]
    exact differentiable_id
private theorem isRelativelyOpen_inter_iInter {E I : Type} [TopologicalSpace E] [Finite I]
    {P A : Set E} {B : I → Set E} (hA : ComplexMatrix2.IsRelativelyOpen P A)
    (hB : ∀ i, ComplexMatrix2.IsRelativelyOpen P (B i)) :
    ComplexMatrix2.IsRelativelyOpen P (A ∩ ⋂ i, B i) := by
  obtain ⟨U, hU, rfl⟩ := hA
  choose V hV hVe using hB
  refine ⟨U ∩ ⋂ i, V i, hU.inter (isOpen_iInter_of_finite hV), ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iInter, hVe]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun i => (h3 i).1⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨⟨h1, h2⟩, fun i => ⟨h3 i, h2⟩⟩
private theorem coefficients_analytic (hM : SeriesFacts) (hH : ChartFacts) [Fintype S] [Fintype R]
    [Fintype S'] {E : Submodule ℝ (S → ComplexMatrix2)} {E' : Submodule ℝ (S' → ComplexMatrix2)}
    (hE' : E' ≤ hermitianTracelessFunctions S')
    {𝒲 : Set (R ⊕ S → ComplexMatrix2)} (h𝒲 : IsOpenInSubspaceTimesGroup E 𝒲) :
    AnalyticIffCoefficientsAnalytic E E' 𝒲 := by
  intro n' e' f φ hsum
  have hmem : ∀ p ∈ 𝒲, f p ∈ E' := fun p hp => by
    rw [hsum p hp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e' i).2
  constructor
  · intro hf i
    obtain ⟨lam, hlam⟩ := exists_complex_extension hE' (e'.coord i)
    have hval : ∀ p ∈ 𝒲, lam (f p) = (φ i p : ℂ) := by
      intro p hp
      rw [hlam _ (hmem p hp)]
      have h : (⟨f p, hmem p hp⟩ : E') = ∑ j, φ j p • e' j := by
        apply Subtype.ext
        change f p = ((∑ j, φ j p • e' j : E') : S' → ComplexMatrix2)
        rw [hsum p hp]
        simp
      rw [h]
      simp [Module.Basis.coord_apply, Finsupp.single_apply]
    refine ⟨hf.1, fun p hp => ?_⟩
    obtain ⟨𝒳, hp𝒳, h𝒳, hs, Ψ, hΨ, hEq⟩ := hf.2.2.2 p hp
    have hG : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty S')
        (GroupLieProduct Empty S') :=
      isRelativelyOpen_self _
    have hd : Differentiable ℂ fun w : Empty ⊕ S' → ComplexMatrix2 =>
        scalarEquiv (lam (algebraComponent w)) :=
      differentiable_scalarEquiv.comp
        ((differentiable_linearMap lam).comp differentiable_algebraComponent)
    refine ⟨𝒳, hp𝒳, h𝒳, hs, (fun w => scalarEquiv (lam (algebraComponent w))) ∘ Ψ, fun b => ?_,
      fun q hq => ?_⟩
    · have hc := ((hH.2.2.2.2.1 R S Empty S') b 𝒳 Ψ h𝒳 (hΨ b) _ _ (Equiv.refl _)
        (GroupLieProduct Empty S') (fun w => scalarEquiv (lam (algebraComponent w)))
        (coords_of_differentiableOn hM hH (Equiv.refl _) isOpen_univ hd.differentiableOn hG
          (subset_univ _) b)).2.2
      have hset : 𝒳 ∩ Ψ ⁻¹' GroupLieProduct Empty S' = 𝒳 := by
        refine inter_eq_left.2 fun q hq => ?_
        rintro (i | k)
        · exact i.elim
        · exact (hΨ b).2.2 k |>.1 hq
      rwa [hset] at hc
    · change scalarEquiv (lam (algebraComponent (Ψ q))) = scalarEquiv (φ i q : ℂ)
      rw [hEq hq]
      exact congrArg _ (hval q (hs hq))
  · intro hφ
    refine ⟨h𝒲, hE', fun p hp => ⟨hmem p hp, fun i => i.elim⟩, fun p hp => ?_⟩
    choose 𝒳 hp𝒳 h𝒳 hsub Φ hΦ hEq using fun i => (hφ i).2 p hp
    obtain ⟨𝒳₁, h𝒳₁, he⟩ := exists_ambient_open h𝒲
    have ho := isRelativelyOpen_inter_iInter h𝒳₁ h𝒳
    have hsubX : ∀ {q}, q ∈ (𝒳₁ ∩ ⋂ i, 𝒳 i) ∩ subspaceTimesGroup E R → q ∈ 𝒲 := fun {q} hq => by
      rw [← he]
      exact ⟨hq.1.1, hq.2⟩
    refine ⟨𝒳₁ ∩ ⋂ i, 𝒳 i, ⟨?_, mem_iInter.2 hp𝒳⟩, ho, fun q hq => hsubX hq,
      fun q => ofParts Empty.elim fun k => ∑ i, Φ i q 0 • ((e' i : E') : S' → ComplexMatrix2) k,
      fun b => ⟨ho, fun i => i.elim, fun k => ⟨fun q _ => ?_, ?_⟩⟩, fun q hq => ?_⟩
    · rw [← he] at hp
      exact hp.1
    · change ∑ i, Φ i q 0 • ((e' i : E') : S' → ComplexMatrix2) k ∈ ComplexMatrix2.traceless
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact (hE' (e' i).2 k (mem_univ k)).2
    · have hT : Differentiable ℂ fun v : Fin n' → ComplexCoordinates 1 =>
          matrixEquiv (∑ i, v i 0 • ((e' i : E') : S' → ComplexMatrix2) k) := by
        refine differentiable_matrixEquiv.comp ?_
        refine Differentiable.fun_sum fun i _ => ?_
        have hv : Differentiable ℂ fun v : Fin n' → ComplexCoordinates 1 => v i 0 := by fun_prop
        exact hv.smul_const _
      refine (coords_iff_refl _).2 (coords_comp_family hM hH ho (Φ := Φ) (fun i => ?_) hT)
      exact coords_mono hM hH (hΦ i b) ho fun x hx => mem_iInter.1 hx.2 i
    · have hqW := hsubX hq
      have hv : ∀ i, Φ i q 0 = (φ i q : ℂ) := by
        intro i
        have h := hEq i (⟨mem_iInter.1 hq.1.2 i, hq.2⟩ : q ∈ 𝒳 i ∩ subspaceTimesGroup E R)
        rw [h]
        exact scalarEquiv_apply _ _
      change ofParts Empty.elim _ = ofParts Empty.elim (f q)
      congr 1
      rw [hsum q hqW]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, hv]
      exact Finset.sum_congr rfl fun i _ => ofReal_smul_eq _ _
end
section
variable {σ ι κ ι' κ' S R S' R' : Type}
private theorem coords_change_basis (hH : ChartFacts) [Fintype ι] [Fintype κ] {E : Type} {l : ℕ}
    {b b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : E ≃ ComplexCoordinates l}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ) : IsHolomorphicToCoords b' e W Φ := by
  refine ⟨h.1, h.2.1, fun p hp => ?_⟩
  obtain ⟨O, h0, hmap, hhol⟩ := h.2.2 p hp
  exact ⟨O, h0, hmap, ((hH.2.1 (ι ⊕ κ)).2.1 E l e b b' O _).1 hhol⟩
private theorem product_change_basis (hH : ChartFacts) [Fintype ι] [Fintype κ]
    {b b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2} (h : IsHolomorphicToProduct b W Ψ) :
    IsHolomorphicToProduct b' W Ψ := by
  refine ⟨h.1, fun i => ?_, fun k => ⟨(h.2.2 k).1, coords_change_basis hH (h.2.2 k).2⟩⟩
  have hi := h.2.1 i
  exact ((hH.2.2.2.1 ι κ).2.1 b' W _ h.1 hi.2.1).2
    (coords_change_basis hH (((hH.2.2.2.1 ι κ).2.1 b W _ h.1 hi.2.1).1 hi))
private theorem asGroupFactors_groupComponent (q : R ⊕ Empty → ComplexMatrix2) :
    asGroupFactors (groupComponent q) = q := by
  funext i
  rcases i with r | k
  · rfl
  · exact k.elim
abbrev _root_.YangMills.DeltaSharedProofs.p4358 := @asGroupFactors_groupComponent
private theorem continuous_asGroupFactors :
    Continuous (asGroupFactors : (R → ComplexMatrix2) → R ⊕ Empty → ComplexMatrix2) := by
  refine continuous_pi ?_
  rintro (r | k)
  · exact continuous_apply r
  · exact k.elim
abbrev _root_.YangMills.SharedProofs.p11373 := @continuous_asGroupFactors
private theorem asGroupFactors_mem {V : R → ComplexMatrix2} (hV : V ∈ specialUnitaryPower R) :
    asGroupFactors V ∈ subspaceTimesGroup (hermitianTracelessFunctions Empty) R :=
  ⟨fun i => i.elim, hV⟩
private theorem analyticToCoords_iff_restriction (hM : SeriesFacts) (hH : ChartFacts) [Fintype R]
    {T : Type} {l : ℕ} (e : T ≃ ComplexCoordinates l)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝒲 : Set (R ⊕ Empty → ComplexMatrix2)}
    (h𝒲 : IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions Empty) 𝒲)
    (f : (R → ComplexMatrix2) → T) :
    IsSubspaceAnalyticToCoords (hermitianTracelessFunctions Empty) 𝒲
        (fun q => e (f (groupComponent q))) ↔
      IsLocallyHolomorphicRestriction (IsHolomorphicToCoords b e) id (asGroupFactors ⁻¹' 𝒲) f := by
  have hW := subset_subspaceTimesGroup h𝒲
  obtain ⟨𝒳₁, h𝒳₁, he⟩ := exists_ambient_open h𝒲
  constructor
  · rintro ⟨-, h⟩ p hp
    obtain ⟨𝒳, hp𝒳, h𝒳, hs, Φ, hΦ, hEq⟩ := h _ hp
    refine ⟨𝒳, e.symm ∘ Φ, hp𝒳, ?_, fun x hx hx𝒳 => ?_⟩
    · refine (coords_iff_refl e).2 ?_
      have hee : e ∘ e.symm ∘ Φ = Φ := by
        funext q
        simp
      rw [hee]
      exact hΦ b
    · have h1 := hEq ⟨hx𝒳, hW hx⟩
      change e.symm (Φ (asGroupFactors x)) = f x
      rw [h1]
      exact e.symm_apply_apply (f x)
  · intro h
    refine ⟨h𝒲, fun p hp => ?_⟩
    have hp' : groupComponent p ∈ asGroupFactors ⁻¹' 𝒲 := by
      rw [mem_preimage, asGroupFactors_groupComponent]
      exact hp
    obtain ⟨W, Φ, hpW, hΦ, hEq⟩ := h _ hp'
    rw [asGroupFactors_groupComponent] at hpW
    have ho := isRelativelyOpen_inter hΦ.1 h𝒳₁
    refine ⟨W ∩ 𝒳₁, ⟨hpW, ?_⟩, ho, ?_, e ∘ Φ, fun b' => ?_, fun q hq => ?_⟩
    · rw [← he] at hp
      exact hp.1
    · intro q hq
      rw [← he]
      exact ⟨hq.1.2, hq.2⟩
    · exact (coords_iff_refl e).1
        (coords_change_basis hH (coords_mono hM hH hΦ ho inter_subset_left))
    · have hq𝒲 : q ∈ 𝒲 := by
        rw [← he]
        exact ⟨hq.1.2, hq.2⟩
      have h1 := hEq (groupComponent q)
        (by rw [mem_preimage, asGroupFactors_groupComponent]; exact hq𝒲)
        (by rw [asGroupFactors_groupComponent]; exact hq.1.1)
      rw [asGroupFactors_groupComponent] at h1
      change e (Φ q) = e (f (groupComponent q))
      rw [h1]
      rfl
private theorem analyticToProduct_iff_restriction (hM : SeriesFacts) (hH : ChartFacts) [Fintype R]
    [Fintype R'] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝒲 : Set (R ⊕ Empty → ComplexMatrix2)}
    (h𝒲 : IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions Empty) 𝒲)
    (f : (R → ComplexMatrix2) → R' → ComplexMatrix2)
    (hf : MapsTo f (asGroupFactors ⁻¹' 𝒲) (specialUnitaryPower R')) :
    IsSubspaceAnalyticToProduct (hermitianTracelessFunctions Empty)
        (hermitianTracelessFunctions Empty) 𝒲 (fun q => asGroupFactors (f (groupComponent q))) ↔
      IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors
        (asGroupFactors ⁻¹' 𝒲) f := by
  have hW := subset_subspaceTimesGroup h𝒲
  obtain ⟨𝒳₁, h𝒳₁, he⟩ := exists_ambient_open h𝒲
  constructor
  · rintro ⟨-, -, -, h⟩ p hp
    obtain ⟨𝒳, hp𝒳, h𝒳, hs, Ψ, hΨ, hEq⟩ := h _ hp
    exact ⟨𝒳, Ψ, hp𝒳, hΨ b, fun x hx hx𝒳 => hEq ⟨hx𝒳, hW hx⟩⟩
  · intro h
    refine ⟨h𝒲, le_rfl, fun q hq => ?_, fun p hp => ?_⟩
    · refine asGroupFactors_mem (hf ?_)
      rw [mem_preimage, asGroupFactors_groupComponent]
      exact hq
    have hp' : groupComponent p ∈ asGroupFactors ⁻¹' 𝒲 := by
      rw [mem_preimage, asGroupFactors_groupComponent]
      exact hp
    obtain ⟨W, Ψ, hpW, hΨ, hEq⟩ := h _ hp'
    rw [asGroupFactors_groupComponent] at hpW
    have ho := isRelativelyOpen_inter hΨ.1 h𝒳₁
    refine ⟨W ∩ 𝒳₁, ⟨hpW, ?_⟩, ho, ?_, Ψ, fun b' => ?_, fun q hq => ?_⟩
    · rw [← he] at hp
      exact hp.1
    · intro q hq
      rw [← he]
      exact ⟨hq.1.2, hq.2⟩
    · exact product_change_basis hH (product_mono hM hH hΨ ho inter_subset_left)
    · have hq𝒲 : q ∈ 𝒲 := by
        rw [← he]
        exact ⟨hq.1.2, hq.2⟩
      have h1 := hEq (groupComponent q)
        (by rw [mem_preimage, asGroupFactors_groupComponent]; exact hq𝒲)
        (by rw [asGroupFactors_groupComponent]; exact hq.1.1)
      rw [asGroupFactors_groupComponent] at h1
      exact h1
private theorem groupPower_analyticity (hM : SeriesFacts) (hH : ChartFacts) [Fintype R]
    [Fintype R'] : GroupPowerAnalyticity R R' := by
  intro 𝒲 h𝒲
  refine ⟨?_, fun b => ⟨fun f => ?_, fun f => ?_, fun f hf => ?_⟩⟩
  · obtain ⟨O, hO, hOe⟩ := h𝒲.2
    refine ⟨asGroupFactors ⁻¹' O, hO.preimage continuous_asGroupFactors, ?_⟩
    rw [hOe]
    ext V
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, asGroupFactors_mem h2⟩
  · exact analyticToCoords_iff_restriction hM hH _ b h𝒲 f
  · exact analyticToCoords_iff_restriction hM hH _ b h𝒲 f
  · exact analyticToProduct_iff_restriction hM hH b h𝒲 f hf
end
section
variable {S R : Type} {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
private theorem pauliSum_mem_traceless (υ : R → Fin 3 → ℂ) (ρ : R) :
    pauliSum υ ρ ∈ ComplexMatrix2.traceless :=
  Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (pauliFamily_mem_hermitianTraceless a).2
private theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])
private theorem pauliSum_mem_hermitianTraceless {υ : R → Fin 3 → ℂ} {ρ : R}
    (h : ∀ a, (υ ρ a).im = 0) : pauliSum υ ρ ∈ ComplexMatrix2.hermitianTraceless := by
  refine Submodule.sum_mem _ fun a _ => ?_
  have hre := eq_ofReal_re_of_im_eq_zero (h a)
  change υ ρ a • pauliFamily a ∈ ComplexMatrix2.hermitianTraceless
  rw [hre, ofReal_smul_eq]
  exact ComplexMatrix2.hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitianTraceless a)
private theorem inv_mem_specialUnitary {W : ComplexMatrix2} (h : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem mul_inv_of_mem_specialUnitary {W : ComplexMatrix2}
    (h : W ∈ ComplexMatrix2.specialUnitary) : W * W⁻¹ = 1 := by
  refine Matrix.mul_nonsing_inv W ?_
  rw [(Matrix.mem_specialUnitaryGroup_iff.1 h).2]
  exact isUnit_one
abbrev _root_.YangMills.SharedProofs.p21267 := @mul_inv_of_mem_specialUnitary
private theorem inv_mul_of_mem_specialUnitary {W : ComplexMatrix2}
    (h : W ∈ ComplexMatrix2.specialUnitary) : W⁻¹ * W = 1 := by
  refine Matrix.nonsing_inv_mul W ?_
  rw [(Matrix.mem_specialUnitaryGroup_iff.1 h).2]
  exact isUnit_one
abbrev _root_.YangMills.SharedProofs.p1227 := @inv_mul_of_mem_specialUnitary
private theorem basisExpChart_mem [Fintype R] (hI : IntrinsicFacts) (e : Module.Basis (Fin n) ℝ E)
    (ν : IndexEnum R) {w₀ : R ⊕ S → ComplexMatrix2} (hw : w₀ ∈ subspaceTimesGroup E R)
    {z : ParamSpace n R} (hz : z ∈ realLocus (n + 3 * Fintype.card R)) :
    basisExpChart e ν w₀ z ∈ subspaceTimesGroup E R := by
  refine ⟨?_, fun ρ => ?_⟩
  · change algebraComponent w₀ + ∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2) ∈ E
    refine E.add_mem hw.1 (Submodule.sum_mem _ fun i _ => ?_)
    have hre : linearPart z i = ((linearPart z i).re : ℂ) := eq_ofReal_re_of_im_eq_zero (hz _)
    rw [hre, ofReal_smul_eq]
    exact E.smul_mem _ (e i).2
  · have hY : pauliSum (angularPart ν z) ρ ∈ ComplexMatrix2.hermitianTraceless :=
      pauliSum_mem_hermitianTraceless fun a => hz _
    exact Submonoid.mul_mem _ (hI.1 _ hY).2.2.2 (hw.2 ρ)
private theorem basisExpChart_zero [Fintype R] (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R)
    (w₀ : R ⊕ S → ComplexMatrix2) : basisExpChart e ν w₀ 0 = w₀ := by
  have h0 : angularPart ν (0 : ParamSpace n R) = 0 := rfl
  funext i
  rcases i with ρ | s
  · change ComplexMatrix2.matExp (Complex.I • pauliSum (angularPart ν 0) ρ) *
      groupComponent w₀ ρ = _
    simp [h0, pauliSum, ComplexMatrix2.matExp, groupComponent]
  · change (algebraComponent w₀ + ∑ i, linearPart (0 : ParamSpace n R) i • _) s = _
    simp [linearPart, algebraComponent]
private def logParams [Fintype R] (lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ) (ν : IndexEnum R)
    (w₀ q : R ⊕ S → ComplexMatrix2) : ParamSpace n R :=
  Fin.append (fun i => lam i (algebraComponent q - algebraComponent w₀)) fun k =>
    pauliCoeff (ν.symm k).2 ((1 / Complex.I) •
      ComplexMatrix2.logSeries (q (.inl (ν.symm k).1) * (w₀ (.inl (ν.symm k).1))⁻¹))
private theorem linearPart_logParams [Fintype R] (lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ)
    (ν : IndexEnum R) (w₀ q : R ⊕ S → ComplexMatrix2) (i : Fin n) :
    linearPart (logParams lam ν w₀ q) i = lam i (algebraComponent q - algebraComponent w₀) := by
  simp [linearPart, logParams]
private theorem angularPart_logParams [Fintype R] (lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ)
    (ν : IndexEnum R) (w₀ q : R ⊕ S → ComplexMatrix2) (ρ : R) (a : Fin 3) :
    angularPart ν (logParams lam ν w₀ q) ρ a =
      pauliCoeff a ((1 / Complex.I) • ComplexMatrix2.logSeries (q (.inl ρ) * (w₀ (.inl ρ))⁻¹)) := by
  simp [angularPart, logParams]
private def nearBall [Fintype R] (w₀ : R ⊕ S → ComplexMatrix2) : Set (R ⊕ S → ComplexMatrix2) :=
  {q | ∀ ρ, ComplexMatrix2.operatorNorm (q (.inl ρ) * (w₀ (.inl ρ))⁻¹ - 1) < 1}
private theorem isOpen_nearBall [Fintype R] (w₀ : R ⊕ S → ComplexMatrix2) :
    IsOpen (nearBall w₀) := by
  have h : nearBall w₀ = ⋂ ρ : R,
      {q | ComplexMatrix2.operatorNorm (q (.inl ρ) * (w₀ (.inl ρ))⁻¹ - 1) < 1} := by
    ext q
    simp [nearBall]
  rw [h]
  refine isOpen_iInter_of_finite fun ρ => isOpen_lt ?_ continuous_const
  exact (((continuous_apply _).mul continuous_const).sub continuous_const).norm
private theorem differentiable_pauliCoeff (a : Fin 3) : Differentiable ℂ (pauliCoeff a) :=
  (LinearMap.toContinuousLinearMap (pauliCoeff a)).differentiable
private theorem differentiableOn_logParams [Fintype R] [Fintype S] (hM : SeriesFacts)
    (lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ) (ν : IndexEnum R) (w₀ : R ⊕ S → ComplexMatrix2) :
    DifferentiableOn ℂ (logParams lam ν w₀) (nearBall w₀) := by
  refine differentiableOn_pi.2 fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · simp only [logParams, Fin.append_left]
    have hd : Differentiable ℂ fun q : R ⊕ S → ComplexMatrix2 =>
        lam i (algebraComponent q - algebraComponent w₀) :=
      (differentiable_linearMap (lam i)).comp (differentiable_algebraComponent.sub_const _)
    exact hd.differentiableOn
  · simp only [logParams, Fin.append_right]
    have hin : DifferentiableOn ℂ (fun q : R ⊕ S → ComplexMatrix2 =>
        ComplexMatrix2.logSeries (q (.inl (ν.symm k).1) * (w₀ (.inl (ν.symm k).1))⁻¹))
        (nearBall w₀) :=
      (differentiableOn_logSeries hM).comp
        ((differentiable_apply _).mul_const _).differentiableOn (fun q hq => hq _)
    have h2 : DifferentiableOn ℂ (fun q : R ⊕ S → ComplexMatrix2 => (1 / Complex.I) •
        ComplexMatrix2.logSeries (q (.inl (ν.symm k).1) * (w₀ (.inl (ν.symm k).1))⁻¹))
        (nearBall w₀) :=
      hin.const_smul (1 / Complex.I)
    exact (differentiable_pauliCoeff _).comp_differentiableOn h2
private theorem operatorNorm_pauliSum_lt [Fintype R] (hP : PauliFacts) {ν : IndexEnum R}
    {z : ParamSpace n R} (hz : z ∈ basisExpChartSource n ν) (ρ : R) :
    ComplexMatrix2.operatorNorm (Complex.I • pauliSum (angularPart ν z) ρ) < Real.log 2 := by
  obtain ⟨hre, hlt⟩ := hz
  have him : ∀ a, (angularPart ν z ρ a).im = 0 := fun a => hre _
  have hY : pauliSum (angularPart ν z) ρ ∈ ComplexMatrix2.hermitianTraceless :=
    pauliSum_mem_hermitianTraceless him
  have hsl := pauliSum_mem_traceless (angularPart ν z) ρ
  have h8 := hP.2.2.2.2.2.2.2.1 ⟨_, hsl⟩ hY
  have h5 := hP.2.2.2.2.1 ⟨_, hsl⟩ ⟨_, hsl⟩ (angularPart ν z ρ) (angularPart ν z ρ)
    rfl rfl
  rw [h5] at h8
  have hsq : ComplexMatrix2.operatorNorm (pauliSum (angularPart ν z) ρ) ^ 2 =
      ∑ a, (angularPart ν z ρ a).re ^ 2 := by
    have h := congrArg Complex.re h8
    simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, him, mul_zero, sub_zero] at h
    simpa [pow_two] using h
  have hlt' := hlt ρ
  rw [← hsq] at hlt'
  have hnorm : ComplexMatrix2.operatorNorm (Complex.I • pauliSum (angularPart ν z) ρ) =
      ComplexMatrix2.operatorNorm (pauliSum (angularPart ν z) ρ) := by
    simp [ComplexMatrix2.operatorNorm, norm_smul]
  rw [hnorm]
  exact lt_of_pow_lt_pow_left₀ 2 (Real.log_nonneg one_le_two) hlt'
private theorem logParams_basisExpChart [Fintype R] [Fintype S] (hP : PauliFacts) (hL : LogFacts)
    {e : Module.Basis (Fin n) ℝ E} {lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ}
    (hlam : ∀ i x (hx : x ∈ E), lam i x = (e.coord i ⟨x, hx⟩ : ℂ)) (ν : IndexEnum R)
    {w₀ : R ⊕ S → ComplexMatrix2} (hw : w₀ ∈ subspaceTimesGroup E R) {z : ParamSpace n R}
    (hz : z ∈ basisExpChartSource n ν) :
    basisExpChart e ν w₀ z ∈ nearBall w₀ ∧ logParams lam ν w₀ (basisExpChart e ν w₀ z) = z := by
  have hquot : ∀ ρ, basisExpChart e ν w₀ z (.inl ρ) * (w₀ (.inl ρ))⁻¹ =
      ComplexMatrix2.matExp (Complex.I • pauliSum (angularPart ν z) ρ) := by
    intro ρ
    change ComplexMatrix2.matExp _ * groupComponent w₀ ρ * _ = _
    rw [mul_assoc]
    have hh : groupComponent w₀ ρ * (w₀ (.inl ρ))⁻¹ = 1 := mul_inv_of_mem_specialUnitary (hw.2 ρ)
    rw [hh, mul_one]
  have h5 := fun ρ => hL.2.2.2.2.1 _ (operatorNorm_pauliSum_lt hP hz ρ)
  refine ⟨fun ρ => ?_, ?_⟩
  · rw [hquot]
    exact (h5 ρ).1
  · funext j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · change linearPart (logParams lam ν w₀ (basisExpChart e ν w₀ z)) i = linearPart z i
      rw [linearPart_logParams]
      have hdiff : algebraComponent (basisExpChart e ν w₀ z) - algebraComponent w₀ =
          ∑ j, linearPart z j • ((e j : E) : S → ComplexMatrix2) := by
        change algebraComponent w₀ + _ - algebraComponent w₀ = _
        simp
      rw [hdiff, map_sum]
      have hδ : ∀ j, lam i ((e j : E) : S → ComplexMatrix2) = if j = i then 1 else 0 := by
        intro j
        rw [hlam i _ (e j).2]
        simp only [Subtype.coe_eta, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply]
        split_ifs <;> simp
      simp [hδ]
    · obtain ⟨⟨ρ, a⟩, rfl⟩ := ν.surjective k
      change angularPart ν (logParams lam ν w₀ (basisExpChart e ν w₀ z)) ρ a =
        angularPart ν z ρ a
      rw [angularPart_logParams, hquot, (h5 ρ).2, smul_smul]
      have hone : (1 / Complex.I) * Complex.I = 1 := by simp
      rw [hone, one_smul]
      exact pauliCoeff_sum_smul (angularPart ν z ρ) a
private theorem basisExpChart_logParams [Fintype R] [Fintype S] (hL : LogFacts)
    {e : Module.Basis (Fin n) ℝ E} {lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ}
    (hlam : ∀ i x (hx : x ∈ E), lam i x = (e.coord i ⟨x, hx⟩ : ℂ)) (ν : IndexEnum R)
    {w₀ : R ⊕ S → ComplexMatrix2} (hw : w₀ ∈ subspaceTimesGroup E R) {q : R ⊕ S → ComplexMatrix2}
    (hq : q ∈ nearBall w₀) (hqs : q ∈ subspaceTimesGroup E R) :
    logParams lam ν w₀ q ∈ realLocus (n + 3 * Fintype.card R) ∧
      basisExpChart e ν w₀ (logParams lam ν w₀ q) = q := by
  have hv : algebraComponent q - algebraComponent w₀ ∈ E := E.sub_mem hqs.1 hw.1
  have hlin : ∀ i, lam i (algebraComponent q - algebraComponent w₀) =
      (e.repr ⟨_, hv⟩ i : ℂ) := by
    intro i
    rw [hlam i _ hv]
    simp [Module.Basis.coord_apply]
  have hgrp : ∀ ρ, ∃ H ∈ ComplexMatrix2.hermitianTraceless,
      (1 / Complex.I) • ComplexMatrix2.logSeries (q (.inl ρ) * (w₀ (.inl ρ))⁻¹) = H ∧
        ComplexMatrix2.matExp (Complex.I • H) = q (.inl ρ) * (w₀ (.inl ρ))⁻¹ := by
    intro ρ
    have hA : q (.inl ρ) * (w₀ (.inl ρ))⁻¹ ∈ ComplexMatrix2.specialUnitary :=
      Submonoid.mul_mem _ (hqs.2 ρ) (inv_mem_specialUnitary (hw.2 ρ))
    have hAm := Matrix.mem_specialUnitaryGroup_iff.1 hA
    obtain ⟨H, -, hlog, -, hexp, -, hdet⟩ := hL.2.2.2.2.2.2.2.1 _ hAm.1 (hq ρ)
    obtain ⟨-, hH, -⟩ := hdet hAm.2
    refine ⟨H, hH, ?_, hexp⟩
    rw [hlog, smul_smul]
    have hone : (1 / Complex.I) * Complex.I = 1 := by simp
    rw [hone, one_smul]
  choose H hH hlogH hexpH using hgrp
  have hcoef : ∀ ρ a, angularPart ν (logParams lam ν w₀ q) ρ a = pauliCoeff a (H ρ) := by
    intro ρ a
    rw [angularPart_logParams, hlogH]
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · change (linearPart (logParams lam ν w₀ q) i).im = 0
      rw [linearPart_logParams, hlin]
      simp
    · obtain ⟨⟨ρ, a⟩, rfl⟩ := ν.surjective k
      change (angularPart ν (logParams lam ν w₀ q) ρ a).im = 0
      rw [hcoef]
      exact pauliCoeff_im (hH ρ) a
  · funext i
    rcases i with ρ | s
    · change ComplexMatrix2.matExp (Complex.I • pauliSum _ ρ) * w₀ (.inl ρ) = q (.inl ρ)
      have hY : pauliSum (angularPart ν (logParams lam ν w₀ q)) ρ = H ρ := by
        change ∑ a, angularPart ν (logParams lam ν w₀ q) ρ a • pauliFamily a = H ρ
        simp only [hcoef]
        exact sum_pauliCoeff_smul (hH ρ).2
      have hh : (w₀ (.inl ρ))⁻¹ * w₀ (.inl ρ) = 1 := inv_mul_of_mem_specialUnitary (hw.2 ρ)
      rw [hY, hexpH, mul_assoc, hh, mul_one]
    · change (algebraComponent w₀ + ∑ i, linearPart (logParams lam ν w₀ q) i •
        ((e i : E) : S → ComplexMatrix2)) s = q (.inr s)
      have hsum : ∑ i, linearPart (logParams lam ν w₀ q) i • ((e i : E) : S → ComplexMatrix2) =
          algebraComponent q - algebraComponent w₀ := by
        have h := congrArg (Subtype.val) (e.sum_repr ⟨_, hv⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        rw [← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [linearPart_logParams, hlin]
        exact ofReal_smul_eq _ _
      rw [hsum]
      simp [algebraComponent]
end
section
variable {S R S' R' ι κ : Type} {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
private theorem exists_complex_extensions [Fintype S] (hE : E ≤ hermitianTracelessFunctions S)
    (e : Module.Basis (Fin n) ℝ E) :
    ∃ lam : Fin n → (S → ComplexMatrix2) →ₗ[ℂ] ℂ,
      ∀ i x (hx : x ∈ E), lam i x = (e.coord i ⟨x, hx⟩ : ℂ) := by
  choose lam h using fun i => exists_complex_extension hE (e.coord i)
  exact ⟨lam, h⟩
private def smallAngles [Fintype R] (n : ℕ) (ν : IndexEnum R) : Set (ParamSpace n R) :=
  {z | ∀ ρ, ∑ a, (angularPart ν z ρ a).re ^ 2 < Real.log 2 ^ 2}
private theorem isOpen_smallAngles [Fintype R] (ν : IndexEnum R) :
    IsOpen (smallAngles n ν) := by
  have h : smallAngles n ν =
      ⋂ ρ : R, {z | ∑ a, (angularPart ν z ρ a).re ^ 2 < Real.log 2 ^ 2} := by
    ext z
    simp [smallAngles]
  rw [h]
  refine isOpen_iInter_of_finite fun ρ => isOpen_lt ?_ continuous_const
  refine continuous_finsetSum _ fun a _ => ?_
  exact (Complex.continuous_re.comp (continuous_apply _)).pow 2
private theorem basisExpChartSource_eq [Fintype R] (ν : IndexEnum R) :
    basisExpChartSource n ν = smallAngles n ν ∩ realLocus (n + 3 * Fintype.card R) := by
  ext z
  exact and_comm
private theorem basisExpChart_isChart [Fintype S] [Fintype R] (hM : SeriesFacts) (hP : PauliFacts)
    (hL : LogFacts) (hI : IntrinsicFacts) (hE : E ≤ hermitianTracelessFunctions S)
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) {w₀ : R ⊕ S → ComplexMatrix2}
    (hw : w₀ ∈ subspaceTimesGroup E R) : BasisExpChartIsChart e ν w₀ := by
  obtain ⟨lam, hlam⟩ := exists_complex_extensions hE e
  refine ⟨fun z hz => basisExpChart_mem hI e ν hw hz, basisExpChart_zero e ν w₀,
    ⟨_, isOpen_smallAngles ν, basisExpChartSource_eq ν⟩, ?_, ?_⟩
  · intro z₁ h₁ z₂ h₂ h
    calc z₁ = logParams lam ν w₀ (basisExpChart e ν w₀ z₁) :=
          (logParams_basisExpChart hP hL hlam ν hw h₁).2.symm
      _ = logParams lam ν w₀ (basisExpChart e ν w₀ z₂) := by rw [h]
      _ = z₂ := (logParams_basisExpChart hP hL hlam ν hw h₂).2
  · rintro T ⟨U, hU, rfl⟩
    have hcont : ContinuousOn (logParams lam ν w₀) (nearBall w₀) :=
      (differentiableOn_logParams hM lam ν w₀).continuousOn
    refine ⟨nearBall w₀ ∩ logParams lam ν w₀ ⁻¹' (U ∩ smallAngles n ν),
      hcont.isOpen_inter_preimage (isOpen_nearBall _) (hU.inter (isOpen_smallAngles ν)), ?_⟩
    ext q
    constructor
    · rintro ⟨z, ⟨hzU, hzD⟩, rfl⟩
      have h := logParams_basisExpChart hP hL hlam ν hw hzD
      refine ⟨⟨h.1, ?_⟩, basisExpChart_mem hI e ν hw hzD.1⟩
      rw [mem_preimage, h.2]
      exact ⟨hzU, hzD.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h := basisExpChart_logParams hL hlam ν hw h1 h3
      refine ⟨logParams lam ν w₀ q, ⟨h2.1, h.1, h2.2⟩, h.2⟩
private def chartTangent [Fintype R] (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R)
    (z : ParamSpace n R) : R ⊕ S → ComplexMatrix2 :=
  ofParts (fun ρ => Complex.I • pauliSum (angularPart ν z) ρ)
    (∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2))
private theorem basisExpChart_eq [Fintype R] (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R)
    (w₀ : R ⊕ S → ComplexMatrix2) (z : ParamSpace n R) :
    basisExpChart e ν w₀ z = expChartAt w₀ (chartTangent e ν z) := by
  funext i
  rcases i with ρ | s <;> rfl
private theorem differentiable_chartTangent [Fintype R] [Fintype S] (e : Module.Basis (Fin n) ℝ E)
    (ν : IndexEnum R) : Differentiable ℂ (chartTangent (R := R) e ν) := by
  refine differentiable_pi.2 ?_
  rintro (ρ | s)
  · have hc : ∀ a, Differentiable ℂ fun z : ParamSpace n R => angularPart ν z ρ a :=
      fun a => differentiable_apply _
    have hs : Differentiable ℂ fun z : ParamSpace n R =>
        ∑ a, angularPart ν z ρ a • pauliFamily a :=
      Differentiable.fun_sum fun a _ => (hc a).smul_const _
    exact hs.const_smul Complex.I
  · have hc : ∀ i, Differentiable ℂ fun z : ParamSpace n R => linearPart z i :=
      fun i => differentiable_apply _
    have hs : Differentiable ℂ fun z : ParamSpace n R =>
        ∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2) :=
      Differentiable.fun_sum fun i _ => (hc i).smul_const _
    exact (differentiable_apply s).comp hs
private theorem chartTangent_mem [Fintype R] (hE : E ≤ hermitianTracelessFunctions S)
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) (z : ParamSpace n R) :
    chartTangent e ν z ∈ tracelessPi (R ⊕ S) := by
  rintro (ρ | s)
  · exact Submodule.smul_mem _ _ (pauliSum_mem_traceless _ ρ)
  · change (∑ i, linearPart z i • ((e i : E) : S → ComplexMatrix2)) s ∈ ComplexMatrix2.traceless
    rw [Finset.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (hE (e i).2 s (mem_univ s)).2
private theorem isHolomorphicIn_comp_expChartAt (hM : SeriesFacts) (hH : ChartFacts) [Fintype ι]
    [Fintype κ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {N l : ℕ}
    {j : ComplexCoordinates N → ι ⊕ κ → ComplexMatrix2}
    (hj : Differentiable ℂ j) (hjm : ∀ z, j z ∈ tracelessPi (ι ⊕ κ)) {p : ι ⊕ κ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct ι κ) {𝒳 : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexCoordinates l}
    (hΦ : IsHolomorphicToCoords b (Equiv.refl _) 𝒳 Φ) :
    ComplexCoordinates.IsHolomorphicIn ((expChartAt p ∘ j) ⁻¹' 𝒳)
      (Φ ∘ expChartAt p ∘ j) := by
  classical
  have hex := (hH.2.2.2.1 ι κ).1 p hp
  set Ψ : (Empty ⊕ (ι ⊕ κ) → ComplexMatrix2) → ι ⊕ κ → ComplexMatrix2 :=
    fun q => expChartAt p fun i => q (.inr i) with hΨdef
  have hG : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty (ι ⊕ κ))
      (GroupLieProduct Empty (ι ⊕ κ)) := isRelativelyOpen_self _
  have hΨG : ∀ q ∈ GroupLieProduct Empty (ι ⊕ κ), Ψ q ∈ GroupLieProduct ι κ :=
    fun q hq => hex.2.2.1 fun i => hq (.inr i)
  have hΨ : IsHolomorphicToProduct b (GroupLieProduct Empty (ι ⊕ κ)) Ψ := by
    refine ⟨hG, fun i => ?_, fun k => ?_⟩
    · have hd : Differentiable ℂ fun q : Empty ⊕ (ι ⊕ κ) → ComplexMatrix2 =>
          ComplexMatrix2.matExp (q (.inr (.inl i))) * p (.inl i) :=
        ((differentiable_matExp hM).comp (differentiable_apply _)).mul_const _
      exact unimodular_of_differentiableOn hM hH isOpen_univ hd.differentiableOn hG
        (subset_univ _) (fun q hq => unimodular_apply_inl (hΨG q hq) i) b
    · have hd : Differentiable ℂ fun q : Empty ⊕ (ι ⊕ κ) → ComplexMatrix2 =>
          p (.inr k) + q (.inr (.inr k)) :=
        (differentiable_apply _).const_add _
      exact traceless_of_differentiableOn hM hH isOpen_univ hd.differentiableOn hG
        (subset_univ _) (fun q hq => traceless_apply_inr (hΨG q hq) k) b
  have comp := (hH.2.2.2.2.1 Empty (ι ⊕ κ) ι κ) b _ Ψ hG hΨ _ _ (Equiv.refl _) 𝒳 Φ hΦ
  have tup := ((hH.2.2.2.2.2.2 Empty (ι ⊕ κ)) _ _ (Equiv.refl _) b _ (Φ ∘ Ψ) comp.2.1).1 comp.2.2
  set μ := Fintype.equivFin (Empty ⊕ (ι ⊕ κ)) with hμ
  obtain ⟨-, hhd⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 (tup.2 μ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := ComplexMatrix2.traceless) b.equivFun.toLinearMap
  have hgs : ∀ A ∈ ComplexMatrix2.traceless, ∑ c, g A c • (b c : ComplexMatrix2) = A := by
    intro A hA
    have h := LinearMap.congr_fun hg ⟨A, hA⟩
    have h2 := congrArg Subtype.val (b.sum_equivFun ⟨A, hA⟩)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [h]
    exact h2
  set jσ : ComplexCoordinates N → Empty ⊕ (ι ⊕ κ) → ComplexMatrix2 :=
    fun z => Sum.elim Empty.elim (j z) with hjσ
  have hjσd : Differentiable ℂ jσ := by
    refine differentiable_pi.2 ?_
    rintro (x | i)
    · exact x.elim
    · exact differentiable_pi.1 hj i
  set J : ComplexCoordinates N → ComplexCoordinates (Fintype.card (Empty ⊕ (ι ⊕ κ)) * 3) :=
    fun z m => g (jσ z (μ.symm (finProdFinEquiv.symm m).1)) (finProdFinEquiv.symm m).2 with hJdef
  have hJ : ∀ z, tupleOfCoords b μ (J z) = jσ z := by
    intro z
    funext i
    have hmem : jσ z i ∈ ComplexMatrix2.traceless := by
      rcases i with x | i
      · exact x.elim
      · exact hjm z i
    have hval : ∀ c, J z (finProdFinEquiv (μ i, c)) = g (jσ z i) c := by
      intro c
      change g (jσ z (μ.symm (finProdFinEquiv.symm (finProdFinEquiv (μ i, c))).1))
        (finProdFinEquiv.symm (finProdFinEquiv (μ i, c))).2 = _
      simp only [Equiv.symm_apply_apply]
    change ∑ c, J z (finProdFinEquiv (μ i, c)) • (b c : ComplexMatrix2) = jσ z i
    simp only [hval]
    exact hgs _ hmem
  have hJd : Differentiable ℂ J := by
    refine differentiable_pi.2 fun m => ?_
    have hgd : Differentiable ℂ g := (LinearMap.toContinuousLinearMap g).differentiable
    exact (differentiable_apply _).comp (hgd.comp ((differentiable_apply _).comp hjσd))
  have hΨj : ∀ z, Ψ (jσ z) = expChartAt p (j z) := fun z => rfl
  have hcomp : Φ ∘ expChartAt p ∘ j =
      (Equiv.refl _ ∘ (Φ ∘ Ψ) ∘ tupleOfCoords b μ) ∘ J := by
    funext z
    simp [hJ, hΨj]
  obtain ⟨-, hexc, hexm, -⟩ := id hex
  have hcj : Continuous (expChartAt p ∘ j) :=
    (continuous_expChartAt hM p).comp hj.continuous
  refine (isHolomorphicIn_iff_differentiableOn hM).2 ⟨?_, ?_⟩
  · obtain ⟨U, hU, hUe⟩ := hΦ.1
    have hset : (expChartAt p ∘ j) ⁻¹' 𝒳 = (expChartAt p ∘ j) ⁻¹' U := by
      ext z
      rw [hUe]
      exact ⟨fun h => h.1, fun h => ⟨h, hexm (hjm z)⟩⟩
    rw [hset]
    exact hU.preimage hcj
  · rw [hcomp]
    refine hhd.comp hJd.differentiableOn fun z hz => ?_
    rw [mem_preimage, hJ]
    refine ⟨?_, ?_⟩
    · rintro (x | i)
      · exact x.elim
      · exact hjm z i
    · exact hz
private theorem analyticInParams_of_local (hM : SeriesFacts) {N l : ℕ}
    {T : Set (ComplexCoordinates N)}
    (hT : ComplexMatrix2.IsRelativelyOpen (realLocus N) T)
    {g : ComplexCoordinates N → ComplexCoordinates l}
    (h : ∀ ζ ∈ T, ∃ 𝒪 : Set (ComplexCoordinates N), IsOpen 𝒪 ∧ ζ ∈ 𝒪 ∧
      ∃ h' : ComplexCoordinates N → ComplexCoordinates l, ComplexCoordinates.IsHolomorphicIn 𝒪 h' ∧
        ∀ z ∈ 𝒪, z ∈ T → h' z = g z) : IsAnalyticInParams T g := by
  obtain ⟨U, hU, hUe⟩ := hT
  have hmemT : ∀ {z}, z ∈ U → z ∈ realLocus N → z ∈ T := fun {z} h1 h2 => by
    rw [hUe]
    exact ⟨h1, h2⟩
  have hTU : ∀ {z}, z ∈ T → z ∈ U ∧ z ∈ realLocus N := fun {z} hz => by
    rw [hUe] at hz
    exact hz
  refine ⟨fun ζ hζ => ?_, fun u hu => ?_, ⟨U, hU, hUe⟩, fun a ha => ?_⟩
  · obtain ⟨𝒪, ho, hζ𝒪, h', hh, heq⟩ := h ζ hζ
    refine ⟨𝒪 ∩ U, ho.inter hU, ⟨hζ𝒪, (hTU hζ).1⟩, fun z hz => hmemT hz.1.2 hz.2, h', ?_, ?_⟩
    · exact ⟨ho.inter hU, hh.2.1.mono inter_subset_left, fun a ha j => hh.2.2 a ha.1 j⟩
    · exact fun z hz => heq z hz.1.1 (hmemT hz.1.2 hz.2)
  · obtain ⟨𝒪, ho, hζ𝒪, h', hh, heq⟩ := h _ hu
    have hc : ContDiffOn ℝ ∞ h' 𝒪 := ((hM.1 N 𝒪 ho).1 l h' hh).2.1
    have hcat : ContDiffAt ℝ ∞ h' (ofRealVector u) := hc.contDiffAt (ho.mem_nhds hζ𝒪)
    have hpt : ContDiff ℝ ∞ (ofRealVector : (Fin N → ℝ) → ComplexCoordinates N) :=
      contDiff_pi.2 fun j => Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ j)
    have hcomp : ContDiffAt ℝ ∞ (h' ∘ ofRealVector) u := hcat.comp u hpt.contDiffAt
    refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
    have hopen : IsOpen (ofRealVector ⁻¹' (𝒪 ∩ U) : Set (Fin N → ℝ)) :=
      (ho.inter hU).preimage hpt.continuous
    filter_upwards [hopen.mem_nhds ⟨hζ𝒪, (hTU hu).1⟩] with v hv
    have hreal : ofRealVector v ∈ realLocus N := fun j => by
      simp [ofRealVector]
    exact (heq _ hv.1 (hmemT hv.2 hreal)).symm
  · obtain ⟨𝒪, ho, ha𝒪, h', hh, heq⟩ := h a ha
    have hra := ((hM.1 N 𝒪 ho).1 l h' hh).2.2.2.2
    obtain ⟨c, hc⟩ := hra.2 a ⟨ha𝒪, (hTU ha).2⟩
    refine ⟨c, ?_⟩
    have hnb : 𝒪 ∩ U ∈ 𝓝[realLocus N] a :=
      mem_nhdsWithin_of_mem_nhds ((ho.inter hU).mem_nhds ⟨ha𝒪, (hTU ha).1⟩)
    filter_upwards [hc, hnb, self_mem_nhdsWithin] with z h1 h2 h3
    rw [← heq z h2.1 (hmemT h2.2 h3)]
    exact h1
end
section
variable {S R S' R' ι κ : Type} {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
private theorem analyticInChart_of_analytic [Fintype S] [Fintype R] [Fintype S'] (hM : SeriesFacts)
    (hH : ChartFacts) (hI : IntrinsicFacts) (b₀ : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hE : E ≤ hermitianTracelessFunctions S)
    (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type) [Fintype R']
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) {w₀ : R ⊕ S → ComplexMatrix2}
    (hw : w₀ ∈ subspaceTimesGroup E R) : AnalyticInChartOfAnalytic E' R' e ν w₀ := by
  intro T hT
  have hTo : ComplexMatrix2.IsRelativelyOpen (realLocus (n + 3 * Fintype.card R)) T := by
    obtain ⟨U, hU, rfl⟩ := hT
    refine ⟨U ∩ smallAngles n ν, hU.inter (isOpen_smallAngles ν), ?_⟩
    rw [basisExpChartSource_eq, inter_assoc]
  have hsubT : T ⊆ basisExpChartSource n ν := subset_of_isRelativelyOpen hT
  have hchart : ∀ z ∈ T, basisExpChart e ν w₀ z ∈ subspaceTimesGroup E R :=
    fun z hz => basisExpChart_mem hI e ν hw (hsubT hz).1
  have hwG := subspaceTimesGroup_subset hE hw
  have key : ∀ {l : ℕ} {𝒳 : Set (R ⊕ S → ComplexMatrix2)}
      {Φ : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
      {g : ParamSpace n R → ComplexCoordinates l} {ζ : ParamSpace n R},
      IsHolomorphicToCoords b₀ (Equiv.refl _) 𝒳 Φ → basisExpChart e ν w₀ ζ ∈ 𝒳 →
      (∀ z ∈ T, basisExpChart e ν w₀ z ∈ 𝒳 → Φ (basisExpChart e ν w₀ z) = g z) →
      ∃ 𝒪 : Set (ComplexCoordinates (n + 3 * Fintype.card R)), IsOpen 𝒪 ∧ ζ ∈ 𝒪 ∧
        ∃ h' : ComplexCoordinates (n + 3 * Fintype.card R) → ComplexCoordinates l,
          ComplexCoordinates.IsHolomorphicIn 𝒪 h' ∧ ∀ z ∈ 𝒪, z ∈ T → h' z = g z := by
    intro l 𝒳 Φ g ζ hΦ hζ heq
    have hh := isHolomorphicIn_comp_expChartAt hM hH b₀ (differentiable_chartTangent e ν)
      (chartTangent_mem hE e ν) hwG hΦ
    refine ⟨_, hh.1, ?_, _, hh, fun z hz hzT => ?_⟩
    · rw [mem_preimage, Function.comp_apply, ← basisExpChart_eq]
      exact hζ
    · have hz' : basisExpChart e ν w₀ z ∈ 𝒳 := by
        rw [basisExpChart_eq]
        exact hz
      have h1 := heq z hzT hz'
      rw [basisExpChart_eq] at h1
      exact h1
  refine ⟨fun l f hf => analyticInParams_of_local hM hTo fun ζ hζ => ?_,
    fun k μ f hf => analyticInParams_of_local hM hTo fun ζ hζ => ?_⟩
  · obtain ⟨𝒳, hp, -, -, Φ, hΦ, hEq⟩ := hf.2 _ (mem_image_of_mem _ hζ)
    exact key (hΦ b₀) hp fun z hz hz𝒳 => hEq ⟨hz𝒳, hchart z hz⟩
  · obtain ⟨𝒳, hp, h𝒳, -, Ψ, hΨ, hEq⟩ := hf.2.2.2 _ (mem_image_of_mem _ hζ)
    have hcomp : ∀ i : R' ⊕ S', IsHolomorphicToCoords b₀ (Equiv.refl _) 𝒳
        (matrixEquiv ∘ fun q => Ψ q i) := by
      rintro (r | s)
      · have hm := (hΨ b₀).2.1 r
        exact (coords_iff_refl _).1 (((hH.2.2.2.1 R S).2.1 b₀ 𝒳 _ h𝒳 hm.2.1).1 hm)
      · exact (coords_iff_refl _).1 ((hΨ b₀).2.2 s).2
    have hTd : Differentiable ℂ fun v : R' ⊕ S' → ComplexCoordinates 4 =>
        piEntriesEquivL μ fun i => entriesEquivL.symm (v i) :=
      (piEntriesEquivL μ).differentiable.comp
        (differentiable_pi.2 fun i =>
          entriesEquivL.symm.differentiable.comp (differentiable_apply i))
    have hc := coords_comp_family hM hH h𝒳 hcomp hTd
    have hfun : (fun q => piEntriesEquivL μ fun i =>
        entriesEquivL.symm ((matrixEquiv ∘ fun q => Ψ q i) q)) = matrixPiEquiv μ ∘ Ψ := by
      funext q
      have : (fun i => entriesEquivL.symm ((matrixEquiv ∘ fun q => Ψ q i) q)) = Ψ q := by
        funext i
        exact entriesEquivL.symm_apply_apply (Ψ q i)
      rw [this]
      rfl
    rw [hfun] at hc
    refine key hc hp fun z hz hz𝒳 => ?_
    change matrixPiEquiv μ (Ψ (basisExpChart e ν w₀ z)) =
      matrixPiEquiv μ (f (basisExpChart e ν w₀ z))
    rw [hEq ⟨hz𝒳, hchart z hz⟩]
private theorem exists_holomorphic_of_hasSum {N l : ℕ} {a : ComplexCoordinates N}
    {c : (Fin N → ℕ) → ComplexCoordinates l} {g : ComplexCoordinates N → ComplexCoordinates l}
    {P : ComplexCoordinates N → Prop} (ha : a ∈ realLocus N)
    (hev : ∀ᶠ z in 𝓝[realLocus N] a, P z ∧
      HasSum (fun m : Fin N → ℕ => (∏ j, (z j - a j) ^ m j) • c m) (g z)) :
    ∃ ϱ > 0, ∃ h : ComplexCoordinates N → ComplexCoordinates l,
      ComplexCoordinates.IsHolomorphicIn (openPolydisk a ϱ) h ∧
        ∀ z ∈ openPolydisk a ϱ, z ∈ realLocus N → P z ∧ h z = g z := by
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ϱ : ℝ := ε / 2 with hϱdef
  have hϱ : 0 < ϱ := by positivity
  have hclose : ∀ z : ComplexCoordinates N, (∀ j, ‖z j - a j‖ ≤ ϱ) → dist z a < ε := by
    intro z hz
    have h1 : dist z a ≤ ϱ := (dist_pi_le_iff hϱ.le).2 fun j => by
      rw [dist_eq_norm]
      exact hz j
    linarith
  set z₁ : ComplexCoordinates N := fun j => a j + (ϱ : ℂ) with hz₁
  have hz₁r : z₁ ∈ realLocus N := fun j => by
    simp [hz₁, ha j]
  have hz₁n : ∀ j, ‖z₁ j - a j‖ = ϱ := fun j => by
    simp [hz₁, abs_of_pos hϱ]
  have hsum₁ := (hball (hclose z₁ fun j => (hz₁n j).le) hz₁r).2
  have hsn : Summable fun m : Fin N → ℕ => ‖(∏ j, (z₁ j - a j) ^ m j) • c m‖ :=
    summable_norm_iff.2 hsum₁.summable
  have hb : ∀ (m : Fin N → ℕ) (z : ComplexCoordinates N), z ∈ openPolydisk a ϱ →
      ‖(∏ j, (z j - a j) ^ m j) • c m‖ ≤ ‖(∏ j, (z₁ j - a j) ^ m j) • c m‖ := by
    intro m z hz
    rw [norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_prod, norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [norm_pow, norm_pow, hz₁n]
    exact pow_le_pow_left₀ (norm_nonneg _) (hz j).le _
  have hopen : IsOpen (openPolydisk a ϱ) := by
    have h : openPolydisk a ϱ = ⋂ j, {z : ComplexCoordinates N | ‖z j - a j‖ < ϱ} := by
      ext z
      simp [openPolydisk]
    rw [h]
    refine isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact ((continuous_apply j).sub continuous_const).norm
  refine ⟨ϱ, hϱ, fun z => ∑' m : Fin N → ℕ, (∏ j, (z j - a j) ^ m j) • c m,
    ⟨hopen, ?_, fun a' ha' j => ?_⟩, fun z hz hzr => ?_⟩
  · refine continuousOn_tsum (fun m => ?_) hsn hb
    have : Continuous fun z : ComplexCoordinates N => (∏ j, (z j - a j) ^ m j) • c m := by
      fun_prop
    exact this.continuousOn
  · have hl : Continuous fun ζ : ℂ => a' + ζ • stdBasisVector j := by fun_prop
    have hUo : IsOpen ((fun ζ : ℂ => a' + ζ • stdBasisVector j) ⁻¹' openPolydisk a ϱ) :=
      hopen.preimage hl
    have h0 : (0 : ℂ) ∈ (fun ζ : ℂ => a' + ζ • stdBasisVector j) ⁻¹' openPolydisk a ϱ := by
      simpa using ha'
    have hD := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun (m : Fin N → ℕ) (ζ : ℂ) =>
        (∏ j', ((a' + ζ • stdBasisVector j) j' - a j') ^ m j') • c m)
      hsn (fun m => ?_) hUo (fun m ζ hζ => hb m _ hζ)
    · filter_upwards [hUo.mem_nhds h0] with ζ hζ
      exact hD.differentiableAt (hUo.mem_nhds hζ)
    · have hp : Differentiable ℂ fun ζ : ℂ =>
          ∏ j', ((a' + ζ • stdBasisVector j) j' - a j') ^ m j' := by
        fun_prop
      exact (hp.smul_const _).differentiableOn
  · obtain ⟨h1, h2⟩ := hball (hclose z fun j => (hz j).le) hzr
    exact ⟨h1, h2.tsum_eq⟩
private theorem analytic_of_analyticInChart [Fintype S] [Fintype R] (hM : SeriesFacts)
    (hH : ChartFacts) (hP : PauliFacts) (hL : LogFacts) (hI : IntrinsicFacts)
    (hE : E ≤ hermitianTracelessFunctions S)
    (e : Module.Basis (Fin n) ℝ E) (ν : IndexEnum R) {w₀ : R ⊕ S → ComplexMatrix2}
    (hw : w₀ ∈ subspaceTimesGroup E R) : AnalyticOfAnalyticInChart e ν w₀ := by
  intro T hT l f hra
  obtain ⟨lam, hlam⟩ := exists_complex_extensions hE e
  have hcs := basisExpChart_isChart hM hP hL hI hE e ν hw
  have hsubT : T ⊆ basisExpChartSource n ν := subset_of_isRelativelyOpen hT
  refine ⟨⟨hE, hcs.2.2.2.2 T hT⟩, ?_⟩
  rintro _ ⟨a, haT, rfl⟩
  obtain ⟨c, hc⟩ := hra.2 a haT
  have haD := hsubT haT
  have hTe : T ∈ 𝓝[realLocus (n + 3 * Fintype.card R)] a := by
    obtain ⟨U, hU, hUe⟩ := hra.1
    rw [hUe] at haT ⊢
    exact mem_nhdsWithin.2 ⟨U, hU, haT.1, fun x hx => hx⟩
  obtain ⟨ϱ, hϱ, h, hh, hagree⟩ := exists_holomorphic_of_hasSum (P := fun z => z ∈ T) haD.1
    (by filter_upwards [hTe, hc] with z h1 h2 using ⟨h1, h2⟩)
  set x := logParams lam ν w₀ with hx
  have hd := differentiableOn_logParams hM lam ν w₀
  have hcont : ContinuousOn x (nearBall w₀) := hd.continuousOn
  obtain ⟨hopenI, hhd⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 hh
  have hO : IsOpen (nearBall w₀ ∩ x ⁻¹' openPolydisk a ϱ) :=
    hcont.isOpen_inter_preimage (isOpen_nearBall _) hopenI
  have hFd : DifferentiableOn ℂ (h ∘ x) (nearBall w₀ ∩ x ⁻¹' openPolydisk a ϱ) :=
    hhd.comp (hd.mono inter_subset_left) fun q hq => hq.2
  have hlc := logParams_basisExpChart hP hL hlam ν hw haD
  have hXo : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S)
      ((nearBall w₀ ∩ x ⁻¹' openPolydisk a ϱ) ∩ GroupLieProduct R S) := ⟨_, hO, rfl⟩
  have hfix : ∀ q ∈ (nearBall w₀ ∩ x ⁻¹' openPolydisk a ϱ) ∩ GroupLieProduct R S,
      q ∈ subspaceTimesGroup E R → x q ∈ T ∧ h (x q) = f q := by
    intro q hq hqs
    have hcl := basisExpChart_logParams hL hlam ν hw hq.1.1 hqs
    obtain ⟨h1, h2⟩ := hagree (x q) hq.1.2 hcl.1
    refine ⟨h1, ?_⟩
    rw [h2]
    change f (basisExpChart e ν w₀ (x q)) = f q
    rw [hcl.2]
  refine ⟨(nearBall w₀ ∩ x ⁻¹' openPolydisk a ϱ) ∩ GroupLieProduct R S,
    ⟨⟨hlc.1, ?_⟩, subspaceTimesGroup_subset hE (basisExpChart_mem hI e ν hw haD.1)⟩, hXo, ?_,
    h ∘ x, fun b => coords_of_differentiableOn hM hH (Equiv.refl _) hO hFd hXo inter_subset_left b,
    ?_⟩
  · rw [mem_preimage, hx, hlc.2]
    intro j
    simpa using hϱ
  · intro q hq
    exact ⟨x q, (hfix q hq.1 hq.2).1, (basisExpChart_logParams hL hlam ν hw hq.1.1.1 hq.2).2⟩
  · intro q hq
    exact (hfix q hq.1 hq.2).2
theorem analyticCalculusStatement_holds (hM : SeriesFacts) (hH : ChartFacts) (hL : LogFacts)
    (hI : IntrinsicFacts) (hP : PauliFacts) : AnalyticCalculusStatement := by
  intro S R S' R' _ _ _ _
  obtain ⟨b₀, -⟩ := hP.2.2.2.1
  refine ⟨finiteDimensional_submodules, fun 𝒲 h => analytic_iff_extensions hM hH h,
    groupPower_analyticity hM hH, fun E E' hE hE' => ⟨linearMaps_analytic hM hH hE hE',
      projections_analytic hM hH hE,
      fun 𝒲 h => ⟨constants_analytic hM hH hE' h, pairing_analytic hM hH E 𝒲,
        composition_analytic hM hH b₀ h, coefficients_analytic hM hH hE' h⟩,
      fun n e ν w₀ hw => ⟨basisExpChart_isChart hM hP hL hI hE e ν hw,
        analyticInChart_of_analytic hM hH hI b₀ hE E' R' e ν hw,
        analytic_of_analyticInChart hM hH hP hL hI hE e ν hw⟩⟩⟩
end
end YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
