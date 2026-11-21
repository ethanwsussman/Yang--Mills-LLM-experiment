import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOneProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.Tower.StepFibreNeighbourhoods
open YangMills.Construction.Matrices YangMills.Construction.Geometry
open YangMills.Construction.Coordinates
section Curves
variable {X T : Type} [TopologicalSpace X] {R : CurveData X T} {N N' : Set X}
theorem exists_subinterval_mapsTo {I : Set ℝ} {γ : ℝ → X} (hN : ComplexMatrix2.IsRelativelyOpen N N')
    (hI : IsOpenIntervalAroundZero I) (hγ : ContinuousAt γ 0) (hmaps : MapsTo γ I N)
    (h0 : γ 0 ∈ N') :
    ∃ J, IsOpenIntervalAroundZero J ∧ J ⊆ I ∧ MapsTo γ J N' := by
  obtain ⟨O, hO, rfl⟩ := hN
  have h1 : γ ⁻¹' O ∈ 𝓝 (0 : ℝ) := hγ (hO.mem_nhds h0.1)
  have h2 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem h1 h2)
  refine ⟨Metric.ball 0 ε, ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hε⟩,
    fun t ht => (hball ht).2, fun t ht => ⟨(hball ht).1, hmaps (hball ht).2⟩⟩
  rw [Real.ball_eq_Ioo]
  exact ordConnected_Ioo
theorem isCriticalOn_relOpen_iff (hR : R.HasLocalCurves) (hN : ComplexMatrix2.IsRelativelyOpen N N')
    (F : X → ℝ) (x : X) :
    R.IsCriticalOn N' F x ↔ x ∈ N' ∧ R.IsCriticalOn N F x := by
  have hsub : N' ⊆ N := by
    obtain ⟨O, -, rfl⟩ := hN
    exact inter_subset_right
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, hsub hx, fun I γ hγ hmaps h0 => ?_⟩
    obtain ⟨hI, hc, hcut⟩ := hR.isCurve_local I γ hγ
    obtain ⟨J, hJ, hJI, hJ'⟩ := exists_subinterval_mapsTo hN hI hc hmaps (h0 ▸ hx)
    exact h J γ (hcut J hJ hJI) hJ' h0
  · rintro ⟨hx, -, h⟩
    exact ⟨hx, fun I γ hγ hmaps h0 => h I γ hγ (hmaps.mono_right hsub) h0⟩
theorem tangentSpan_relOpen_eq [AddCommGroup T] [Module ℝ T] (hR : R.HasLocalCurves)
    (hN : ComplexMatrix2.IsRelativelyOpen N N') {x : X} (hx : x ∈ N') :
    R.tangentSpan N' x = R.tangentSpan N x := by
  have hsub : N' ⊆ N := by
    obtain ⟨O, -, rfl⟩ := hN
    exact inter_subset_right
  unfold CurveData.tangentSpan
  congr 1
  ext v
  constructor
  · rintro ⟨I, γ, hγ, hmaps, h0, hv⟩
    exact ⟨I, γ, hγ, hmaps.mono_right hsub, h0, hv⟩
  · rintro ⟨I, γ, hγ, hmaps, h0, hv⟩
    obtain ⟨hI, hc, hcut⟩ := hR.isCurve_local I γ hγ
    obtain ⟨J, hJ, hJI, hJ'⟩ := exists_subinterval_mapsTo hN hI hc hmaps (h0.symm ▸ hx)
    exact ⟨J, γ, hcut J hJ hJI, hJ', h0, hv⟩
theorem isHessianFormAt_relOpen_iff {S : Type} (hR : R.HasLocalCurves)
    (hN : ComplexMatrix2.IsRelativelyOpen N N') {x : X}
    (hx : x ∈ N') (ι : S → T) (F : X → ℝ) (Q : S → ℝ) :
    R.IsHessianFormAt ι N' F x Q ↔ R.IsHessianFormAt ι N F x Q := by
  have hsub : N' ⊆ N := by
    obtain ⟨O, -, rfl⟩ := hN
    exact inter_subset_right
  constructor
  · intro h I γ v hγ hmaps h0 hv
    obtain ⟨hI, hc, hcut⟩ := hR.isTwiceDiffCurve_local I γ hγ
    obtain ⟨J, hJ, hJI, hJ'⟩ := exists_subinterval_mapsTo hN hI hc hmaps (h0.symm ▸ hx)
    exact h J γ v (hcut J hJ hJI) hJ' h0 hv
  · intro h I γ v hγ hmaps h0 hv
    exact h I γ v hγ (hmaps.mono_right hsub) h0 hv
theorem hessianForm_relOpen_eq {S : Type} [AddCommGroup S] [Module ℝ S] (hR : R.HasLocalCurves)
    (hN : ComplexMatrix2.IsRelativelyOpen N N') {x : X} (hx : x ∈ N') (ι : S → T) (F : X → ℝ) :
    R.hessianForm ι N' F x = R.hessianForm ι N F x := by
  unfold CurveData.hessianForm
  congr 1
  funext Q
  exact propext (isHessianFormAt_relOpen_iff hR hN hx ι F Q)
end Curves
theorem vectorCurveData_hasLocalCurves (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (EmbeddedSubmanifold.vectorCurveData E).HasLocalCurves where
  isCurve_local _ _ h := ⟨h.1, h.2.continuousOn.continuousAt (h.1.1.mem_nhds h.1.2.2),
    fun _ hJ hJI => ⟨hJ, h.2.mono hJI⟩⟩
  isTwiceDiffCurve_local _ _ h := ⟨h.1, h.2.1.continuousOn.continuousAt (h.1.1.mem_nhds h.1.2.2),
    fun _ hJ hJI => ⟨hJ, h.2.1.mono hJI, h.2.2.mono hJI⟩⟩
section Bonds
variable {L n k j : ℕ}
theorem continuousWithinAt_of_positiveEdges {Y : Type} [TopologicalSpace Y]
    {m : Y → Edge L n k j → ComplexMatrix2} {s : Set Y} {y : Y} (hy : y ∈ s)
    (hconf : MapsTo m s (fieldSpace L n k j))
    (hpos : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      ContinuousWithinAt (fun y => m y c) s y) : ContinuousWithinAt m s y := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousWithinAt_of_positivelyOriented <;> assumption
theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
end Bonds
theorem fieldCurveData_hasLocalCurves (L n k j : ℕ) : (fieldCurveData L n k j).HasLocalCurves := by
  have key : ∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2),
      IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ → ContinuousAt γ 0 := by
    intro I γ h
    have h0 : (0 : ℝ) ∈ I := h.1.2.2
    have := continuousWithinAt_of_positiveEdges (m := γ) h0 h.2.1
      (fun c hc => (h.2.2 c hc).continuousOn.continuousWithinAt h0)
    exact this.continuousAt (h.1.1.mem_nhds h0)
  exact
  { isCurve_local := fun I γ h => ⟨h.1, key I γ h, fun J hJ hJI =>
      ⟨hJ, h.2.1.mono_left hJI, fun b hb => (h.2.2 b hb).mono hJI⟩⟩
    isTwiceDiffCurve_local := fun I γ h => ⟨h.1.1, key I γ h.1, fun J hJ hJI =>
      ⟨⟨hJ, h.1.2.1.mono_left hJI, fun b hb => (h.1.2.2 b hb).mono hJI⟩,
        fun b hb => (h.2 b hb).mono hJI⟩⟩ }
section Holomorphy
open GroupLieProduct GroupLieProduct.Subspaces
variable {ι κ ι' κ' E : Type} [Fintype ι] [Fintype κ]
theorem subset_of_isRelativelyOpen {Y : Type} [TopologicalSpace Y] {P D : Set Y}
    (h : ComplexMatrix2.IsRelativelyOpen P D) : D ⊆ P := by apply _root_.YangMills.SharedProofs.p9583 <;> assumption
theorem isSupOpen_inter_expChart_preimage (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {p : ι ⊕ κ → ComplexMatrix2} (hp : p ∈ GroupLieProduct ι κ) {O Ω : Set (ι ⊕ κ → ComplexMatrix2)}
    (hO : IsSupOpen O) (hΩ : IsOpen Ω) : IsSupOpen (O ∩ expChartAt p ⁻¹' Ω) := by
  have agree := ((H.2.1 (ι ⊕ κ)).1)
  have hc := ((H.2.2.2.1 ι κ).1 p hp).2.1
  have hsub : O ∩ expChartAt p ⁻¹' Ω ⊆ tracelessPi (ι ⊕ κ) :=
    inter_subset_left.trans hO.1
  refine ((agree _ hsub).1).2 ?_
  obtain ⟨O₀, hO₀, hOeq⟩ := ((agree O hO.1).1).1 hO
  obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.1 hc Ω hΩ
  refine ⟨O₀ ∩ u, hO₀.inter hu, ?_⟩
  ext A
  constructor
  · rintro ⟨hA, hA'⟩
    have hAP := hO.1 hA
    have h2 : A ∈ expChartAt p ⁻¹' Ω ∩ tracelessPi (ι ⊕ κ) := ⟨hA', hAP⟩
    rw [hueq] at h2
    rw [hOeq] at hA
    exact ⟨⟨hA.1, h2.1⟩, hAP⟩
  · rintro ⟨⟨h1, h2⟩, hAP⟩
    have h3 : A ∈ u ∩ tracelessPi (ι ⊕ κ) := ⟨h2, hAP⟩
    rw [← hueq] at h3
    refine ⟨?_, h3.1⟩
    rw [hOeq]
    exact ⟨h1, hAP⟩
theorem isHolomorphicOnTraceless_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {σ : Type} [Fintype σ] {l : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} {O O' : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    (h : IsHolomorphicOnTraceless b e O f) (hO' : IsSupOpen O') (hsub : O' ⊆ O) :
    IsHolomorphicOnTraceless b e O' f := by
  refine ⟨hO', fun ν => ⟨?_, (h.2 ν).2.1.mono (preimage_mono hsub),
    fun a ha j => (h.2 ν).2.2 a (hsub ha) j⟩⟩
  exact (((H.2.1 σ).1 O' hO'.1).2 b ν).1 hO'
theorem isHolomorphicToCoords_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {l : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {e : E ≃ ComplexCoordinates l}
    {W W' : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W Φ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W')
    (hsub : W' ⊆ W) : IsHolomorphicToCoords b e W' Φ := by
  refine ⟨hW', h.2.1.mono hsub, fun p hp => ?_⟩
  obtain ⟨O, h0, hO, hhol⟩ := h.2.2 p (hsub hp)
  obtain ⟨Ω, hΩ, hWeq⟩ := hW'
  have hpP : p ∈ GroupLieProduct ι κ := subset_of_isRelativelyOpen h.1 (hsub hp)
  have hpΩ : p ∈ Ω := by rw [hWeq] at hp; exact hp.1
  have hex : expChartAt p 0 = p := ((H.2.2.2.1 ι κ).1 p hpP).2.2.2.1
  refine ⟨O ∩ expChartAt p ⁻¹' Ω, ⟨h0, ?_⟩, fun A hA => ?_, ?_⟩
  · change expChartAt p 0 ∈ Ω
    rw [hex]; exact hpΩ
  · rw [hWeq]
    exact ⟨hA.2, subset_of_isRelativelyOpen h.1 (hO A hA.1)⟩
  · exact isHolomorphicOnTraceless_mono H hhol
      (isSupOpen_inter_expChart_preimage H hpP hhol.1 hΩ) inter_subset_left
theorem isHolomorphicToUnimodular_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToUnimodular b W Φ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hsub : W' ⊆ W) :
    IsHolomorphicToUnimodular b W' Φ := by
  refine ⟨hW', h.2.1.mono_left hsub, h.2.2.1.mono hsub, fun p hp => ?_⟩
  obtain ⟨O, h0, hO, hhol⟩ := h.2.2.2 p (hsub hp)
  obtain ⟨Ω, hΩ, hWeq⟩ := hW'
  have hpP : p ∈ GroupLieProduct ι κ := subset_of_isRelativelyOpen h.1 (hsub hp)
  have hpΩ : p ∈ Ω := by rw [hWeq] at hp; exact hp.1
  have hex : expChartAt p 0 = p := ((H.2.2.2.1 ι κ).1 p hpP).2.2.2.1
  refine ⟨O ∩ expChartAt p ⁻¹' Ω, ⟨h0, ?_⟩, fun A hA => ⟨?_, (hO A hA.1).2⟩, ?_⟩
  · change expChartAt p 0 ∈ Ω
    rw [hex]; exact hpΩ
  · rw [hWeq]
    exact ⟨hA.2, subset_of_isRelativelyOpen h.1 (hO A hA.1).1⟩
  · exact isHolomorphicOnTraceless_mono H hhol
      (isSupOpen_inter_expChart_preimage H hpP hhol.1 hΩ) inter_subset_left
theorem isHolomorphicToProduct_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2} (h : IsHolomorphicToProduct b W Ψ)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hsub : W' ⊆ W) :
    IsHolomorphicToProduct b W' Ψ :=
  ⟨hW', fun i => isHolomorphicToUnimodular_mono H (h.2.1 i) hW' hsub,
    fun k => ⟨(h.2.2 k).1.mono_left hsub, isHolomorphicToCoords_mono H (h.2.2 k).2 hW' hsub⟩⟩
theorem isHolomorphicToCoords_add {l : ℕ} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ₁ Φ₂ : (ι ⊕ κ → ComplexMatrix2) → ComplexCoordinates l}
    (h₁ : IsHolomorphicToCoords b (Equiv.refl _) W Φ₁)
    (h₂ : IsHolomorphicToCoords b (Equiv.refl _) W Φ₂) :
    IsHolomorphicToCoords b (Equiv.refl _) W fun q => Φ₁ q + Φ₂ q := by
  refine ⟨h₁.1, h₁.2.1.add h₂.2.1, fun p hp => ?_⟩
  obtain ⟨O₁, h01, hO₁, hol₁⟩ := h₁.2.2 p hp
  obtain ⟨O₂, h02, hO₂, hol₂⟩ := h₂.2.2 p hp
  refine ⟨O₁ ∩ O₂, ⟨h01, h02⟩, fun A hA => hO₁ A hA.1, ⟨inter_subset_left.trans hol₁.1.1, ?_⟩, ?_⟩
  · rintro A ⟨hA₁, hA₂⟩
    obtain ⟨s₁, hs₁, hB₁⟩ := hol₁.1.2 A hA₁
    obtain ⟨s₂, hs₂, hB₂⟩ := hol₂.1.2 A hA₂
    refine ⟨min s₁ s₂, lt_min hs₁ hs₂, fun B hB hlt => ⟨hB₁ B hB (hlt.trans_le (min_le_left _ _)),
      hB₂ B hB (hlt.trans_le (min_le_right _ _))⟩⟩
  · intro ν
    have c₁ := hol₁.2 ν
    have c₂ := hol₂.2 ν
    refine ⟨c₁.1.inter c₂.1, ?_, fun a ha j => ?_⟩
    · exact (c₁.2.1.mono (preimage_mono inter_subset_left) |>.add
        (c₂.2.1.mono (preimage_mono inter_subset_right)))
    · filter_upwards [c₁.2.2 a ha.1 j, c₂.2.2 a ha.2 j] with ζ d₁ d₂
      exact d₁.add d₂
variable {R S R' S' : Type} [Fintype R] [Fintype S]
theorem isSubspaceAnalyticToCoords_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {l : ℕ} {Es : Submodule ℝ (S → ComplexMatrix2)} {𝒲 𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l} (h : IsSubspaceAnalyticToCoords Es 𝒲 f)
    (hW : IsOpenInSubspaceTimesGroup Es 𝒲') (hsub : 𝒲' ⊆ 𝒲) :
    IsSubspaceAnalyticToCoords Es 𝒲' f := by
  refine ⟨hW, fun p hp => ?_⟩
  obtain ⟨𝒳, hp𝒳, ⟨Ω₀, hΩ₀, h𝒳⟩, hin, Φ, hΦ, heq⟩ := h.2 p (hsub hp)
  obtain ⟨Ω, hΩ, hWeq⟩ := hW.2
  have hX' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (𝒳 ∩ Ω) := by
    refine ⟨Ω₀ ∩ Ω, hΩ₀.inter hΩ, ?_⟩
    rw [h𝒳]
    ext q
    simp only [mem_inter_iff]
    tauto
  refine ⟨𝒳 ∩ Ω, ⟨hp𝒳, ?_⟩, hX', ?_, Φ, fun b => isHolomorphicToCoords_mono H (hΦ b) hX'
    inter_subset_left, heq.mono (inter_subset_inter_left _ inter_subset_left)⟩
  · rw [hWeq] at hp; exact hp.1
  · rintro q ⟨⟨-, hq⟩, hq'⟩
    rw [hWeq]
    exact ⟨hq, hq'⟩
theorem isSubspaceAnalyticToProduct_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {Es : Submodule ℝ (S → ComplexMatrix2)} {Es' : Submodule ℝ (S' → ComplexMatrix2)}
    {𝒲 𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct Es Es' 𝒲 f)
    (hW : IsOpenInSubspaceTimesGroup Es 𝒲') (hsub : 𝒲' ⊆ 𝒲) :
    IsSubspaceAnalyticToProduct Es Es' 𝒲' f := by
  refine ⟨hW, h.2.1, h.2.2.1.mono_left hsub, fun p hp => ?_⟩
  obtain ⟨𝒳, hp𝒳, ⟨Ω₀, hΩ₀, h𝒳⟩, hin, Ψ, hΨ, heq⟩ := h.2.2.2 p (hsub hp)
  obtain ⟨Ω, hΩ, hWeq⟩ := hW.2
  have hX' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (𝒳 ∩ Ω) := by
    refine ⟨Ω₀ ∩ Ω, hΩ₀.inter hΩ, ?_⟩
    rw [h𝒳]
    ext q
    simp only [mem_inter_iff]
    tauto
  refine ⟨𝒳 ∩ Ω, ⟨hp𝒳, ?_⟩, hX', ?_, Ψ, fun b => isHolomorphicToProduct_mono H (hΨ b) hX'
    inter_subset_left, heq.mono (inter_subset_inter_left _ inter_subset_left)⟩
  · rw [hWeq] at hp; exact hp.1
  · rintro q ⟨⟨-, hq⟩, hq'⟩
    rw [hWeq]
    exact ⟨hq, hq'⟩
theorem isSubspaceAnalyticToCoords_add (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {l : ℕ} {Es : Submodule ℝ (S → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    {f₁ f₂ : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l}
    (h₁ : IsSubspaceAnalyticToCoords Es 𝒲 f₁) (h₂ : IsSubspaceAnalyticToCoords Es 𝒲 f₂) :
    IsSubspaceAnalyticToCoords Es 𝒲 fun q => f₁ q + f₂ q := by
  refine ⟨h₁.1, fun p hp => ?_⟩
  obtain ⟨𝒳₁, hp₁, ⟨Ω₁, hΩ₁, hX₁⟩, hin₁, Φ₁, hΦ₁, heq₁⟩ := h₁.2 p hp
  obtain ⟨𝒳₂, hp₂, ⟨Ω₂, hΩ₂, hX₂⟩, hin₂, Φ₂, hΦ₂, heq₂⟩ := h₂.2 p hp
  have hX : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) (𝒳₁ ∩ 𝒳₂) := by
    refine ⟨Ω₁ ∩ Ω₂, hΩ₁.inter hΩ₂, ?_⟩
    rw [hX₁, hX₂]
    ext q
    simp only [mem_inter_iff]
    tauto
  refine ⟨𝒳₁ ∩ 𝒳₂, ⟨hp₁, hp₂⟩, hX, fun q hq => hin₁ ⟨hq.1.1, hq.2⟩, fun q => Φ₁ q + Φ₂ q,
    fun b => isHolomorphicToCoords_add
      (isHolomorphicToCoords_mono H (hΦ₁ b) hX inter_subset_left)
      (isHolomorphicToCoords_mono H (hΦ₂ b) hX inter_subset_right), fun q hq => ?_⟩
  change Φ₁ q + Φ₂ q = f₁ q + f₂ q
  rw [heq₁ ⟨hq.1.1, hq.2⟩, heq₂ ⟨hq.1.2, hq.2⟩]
end Holomorphy
def tracelessEntries : ComplexMatrix2.traceless ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := ![(X : ComplexMatrix2) 0 0, (X : ComplexMatrix2) 0 1, (X : ComplexMatrix2) 1 0]
  map_add' X Y := by
    ext a
    fin_cases a <;> simp
  map_smul' c X := by
    ext a
    fin_cases a <;> simp
  invFun z := ⟨!![z 0, z 1; z 2, -z 0], by
    change Matrix.trace _ = 0
    simp [Matrix.trace_fin_two]⟩
  left_inv X := by
    have h : Matrix.trace (X : ComplexMatrix2) = 0 := X.2
    rw [Matrix.trace_fin_two] at h
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;> simp
    linear_combination -h
  right_inv z := by
    ext a
    fin_cases a <;> simp
section FieldSpaces
open GroupLieProduct GroupLieProduct.Subspaces
variable {L n k j j' : ℕ}
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 1 ≤ n) (hj : j ≤ k)
    (𝒰 : Set (Edge L n k j → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) 𝒰 := by
  have A := ((hE L hL k j hj).1 n hn).2.2.2.2.2.2.2.2.1
  exact ⟨fun h => ⟨h.1, (A 𝒰 h.1).2 h.2⟩, fun h => ⟨h.1, (A 𝒰 h.1).1 h.2⟩⟩
theorem isOpenInSubspaceTimesGroup_of_isOpenFieldSet [Fintype (PositiveEdge L n k j)]
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    IsOpenInSubspaceTimesGroup (R := PositiveEdge L n k j) (S := Empty) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by apply _root_.YangMills.SharedProofs.p979 <;> assumption
theorem isAnalyticFieldMap_mono (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {𝒰 𝒰' : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldMap 𝒰' m := by
  obtain ⟨-, hm, i₁, i₂, hA⟩ := h
  exact ⟨h', hm.mono_left hsub, i₁, i₂, isSubspaceAnalyticToProduct_mono H hA
    (isOpenInSubspaceTimesGroup_of_isOpenFieldSet h') fun q hq => hsub hq⟩
theorem isAnalyticFieldFunction_add (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {𝒰 𝒰₁ 𝒰₂ : Set (Edge L n k j → ComplexMatrix2)} {F₁ F₂ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction 𝒰₁ F₁) (h₂ : IsAnalyticFieldFunction 𝒰₂ F₂)
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) (s₁ : 𝒰 ⊆ 𝒰₁) (s₂ : 𝒰 ⊆ 𝒰₂) :
    IsAnalyticFieldFunction 𝒰 fun V => F₁ V + F₂ V := by
  obtain ⟨-, i₁, a₁⟩ := h₁
  obtain ⟨-, i₂, a₂⟩ := h₂
  obtain rfl : i₂ = i₁ := Subsingleton.elim _ _
  refine ⟨h, i₂, ?_⟩
  have hs := isSubspaceAnalyticToCoords_add H
    (isSubspaceAnalyticToCoords_mono H a₁ (isOpenInSubspaceTimesGroup_of_isOpenFieldSet h)
      fun q hq => s₁ hq)
    (isSubspaceAnalyticToCoords_mono H a₂ (isOpenInSubspaceTimesGroup_of_isOpenFieldSet h)
      fun q hq => s₂ hq)
  convert hs using 1
  funext q x
  simp
theorem continuousOn_of_isAnalyticFieldMap {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by
  have b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless := Module.Basis.ofEquivFun tracelessEntries
  have h𝒰 : 𝒰 ⊆ fieldSpace L n k j := h.1.1
  obtain ⟨-, hm, i₁, i₂, hA⟩ := h
  intro V hV
  refine continuousWithinAt_of_positiveEdges hV hm fun c hc => ?_
  let ρ : (Edge L n k j → ComplexMatrix2) → (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) :=
    fun V' => ofParts (restrictToPositiveEdges V') Empty.elim
  have hρ : Continuous ρ := by
    refine continuous_pi fun r => ?_
    rcases r with r | e
    · exact continuous_apply _
    · exact e.elim
  have hρ𝒲 : ∀ V' ∈ 𝒰, ρ V' ∈ {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
    intro V' h'
    change fieldOfPositiveValues (restrictToPositiveEdges V') ∈ 𝒰
    rw [fieldOfPositiveValues_restrict (h𝒰 h')]
    exact h'
  obtain ⟨𝒳, hp, ⟨Ω, hΩ, hX⟩, hin, Ψ, hΨ, heq⟩ := hA.2.2.2 (ρ V) (hρ𝒲 V hV)
  have hΨc : ContinuousOn (fun q => Ψ q (.inl ⟨c, hc⟩)) 𝒳 := ((hΨ b).2.1 ⟨c, hc⟩).2.2.1
  have hpΩ : ρ V ∈ Ω := by
    rw [hX] at hp
    exact hp.1
  have hSP : ∀ V' ∈ 𝒰, ρ V' ∈ subspaceTimesGroup ⊥ (PositiveEdge L n k j) :=
    fun V' h' => subset_of_isRelativelyOpen hA.1.2 (hρ𝒲 V' h')
  have hP : ∀ V' ∈ 𝒰, ρ V' ∈ GroupLieProduct (PositiveEdge L n k j) Empty := by
    intro V' h' r
    rcases r with r | e
    · exact (Matrix.mem_specialUnitaryGroup_iff.1 ((hSP V' h').2 r)).2
    · exact e.elim
  have hval : ∀ V' ∈ 𝒰, ρ V' ∈ 𝒳 → m V' c = Ψ (ρ V') (.inl ⟨c, hc⟩) := by
    intro V' h' hX'
    rw [heq ⟨hX', hSP V' h'⟩]
    change m V' c =
      restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges V'))) ⟨c, hc⟩
    rw [fieldOfPositiveValues_restrict (h𝒰 h')]
    rfl
  have hev : ∀ᶠ V' in 𝓝[𝒰] V, V' ∈ 𝒰 ∧ ρ V' ∈ 𝒳 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hρ.continuousAt (hΩ.mem_nhds hpΩ))] with V' h1 h2
    refine ⟨h1, ?_⟩
    rw [hX]
    exact ⟨h2, hP V' h1⟩
  have hcomp : ContinuousWithinAt (fun V' => Ψ (ρ V') (.inl ⟨c, hc⟩)) 𝒰 V :=
    (hΨc _ hp).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hρ.continuousWithinAt.tendsto, hev.mono fun _ h => h.2⟩)
  exact hcomp.congr_of_eventuallyEq (hev.mono fun V' h => hval V' h.1 h.2) (hval V hV hp)
theorem isChartedSubset_inter {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {M O : Set E}
    (hM : EmbeddedSubmanifold.IsChartedSubset M) (hO : IsOpen O) :
    EmbeddedSubmanifold.IsChartedSubset (O ∩ M) := by
  rintro x ⟨hxO, hxM⟩
  obtain ⟨c, u, hu, hx⟩ := hM x hxM
  have hsub : c.source ∩ c.param ⁻¹' O ⊆ c.source := inter_subset_left
  refine ⟨
    { dim := c.dim
      source := c.source ∩ c.param ⁻¹' O
      param := c.param
      isOpen_source := c.contDiffOn_param.continuousOn.isOpen_inter_preimage
        c.isOpen_source hO
      contDiffOn_param := c.contDiffOn_param.mono hsub
      injective_fderiv_param := fun u hu => c.injective_fderiv_param u hu.1
      injOn_param := c.injOn_param.mono hsub
      isRelativelyOpen_image := fun W hW hWo => ?_ }, u, ⟨hu, ?_⟩, hx⟩
  · obtain ⟨O', hO', heq⟩ := c.isRelativelyOpen_image W (hW.trans hsub) hWo
    refine ⟨O', hO', ?_⟩
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h1 : c.param w ∈ O' ∩ M := heq ▸ mem_image_of_mem _ hw
      exact ⟨h1.1, (hW hw).2, h1.2⟩
    · rintro ⟨h1, -, h2⟩
      have h3 : y ∈ O' ∩ M := ⟨h1, h2⟩
      rwa [← heq] at h3
  · change c.param u ∈ O
    rw [hx]
    exact hxO
theorem isAnalyticFieldSubmanifold_inter
    (hop : ∀ 𝒰 : Set (Edge L n k j → ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
        𝒰 ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) 𝒰)
    {N Ω : Set (Edge L n k j → ComplexMatrix2)} (hΩ : IsOpen Ω) (hN : IsAnalyticFieldSubmanifold N) :
    IsAnalyticFieldSubmanifold (Ω ∩ N) := by
  obtain ⟨⟨hNc, i₁, hman⟩, i₂, hloc⟩ := hN
  obtain rfl : i₂ = i₁ := Subsingleton.elim _ _
  refine ⟨⟨inter_subset_right.trans hNc, i₂, ?_⟩, i₂, fun x hx => ?_⟩
  · obtain ⟨Op, hOp, heq⟩ := ((hop (Ω ∩ fieldSpace L n k j)).2
      ⟨inter_subset_right, Ω, hΩ, rfl⟩).2
    have himg : restrictToPositiveEdges '' (Ω ∩ N) = Op ∩ restrictToPositiveEdges '' N := by
      ext w
      constructor
      · rintro ⟨V, ⟨h1, h2⟩, rfl⟩
        have h3 : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' (Ω ∩ fieldSpace L n k j) :=
          mem_image_of_mem _ ⟨h1, hNc h2⟩
        rw [heq] at h3
        exact ⟨h3.1, mem_image_of_mem _ h2⟩
      · rintro ⟨h1, V, hV, rfl⟩
        have h3 : restrictToPositiveEdges V ∈ Op ∩ edgePower L n k j PeriodicLattice.compactGaugeGroup :=
          ⟨h1, fun b => (hNc hV).1 b.1 (mem_univ _)⟩
        rw [← heq] at h3
        obtain ⟨V', hV', he⟩ := h3
        have : V' = V := by
          rw [← fieldOfPositiveValues_restrict hV'.2, he,
            fieldOfPositiveValues_restrict (hNc hV)]
        subst this
        exact mem_image_of_mem _ ⟨hV'.1, hV⟩
    rw [himg]
    exact isChartedSubset_inter hman hOp
  · obtain ⟨𝒰, p, E, E', O, O', f, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hloc x hx.2
    obtain ⟨hc, O₀, hO₀, hO₀eq⟩ := (hop 𝒰).1 h1
    refine ⟨𝒰 ∩ Ω, p, E, E', O, O', f, (hop _).2 ⟨inter_subset_left.trans hc, O₀ ∩ Ω,
      hO₀.inter hΩ, ?_⟩, ⟨h2, hx.1⟩, h3, h4, h5, h6, h7, h8, fun U hU =>
        ⟨(h9 U hU.1).1, fun X hX X' hX' e => ?_⟩⟩
    · rw [hO₀eq]
      ext q
      simp only [mem_inter_iff]
      tauto
    · rw [← (h9 U hU.1).2 X hX X' hX' e]
      exact ⟨fun h => h.2, fun h => ⟨hU.2, h⟩⟩
end FieldSpaces
section Neighbourhood
open YangMills.Construction.Tower.CriticalBranchData
variable {L n k : ℕ}
theorem levelFibre_eq_inter {i : ℕ} {𝒰 𝒰₁ : Set (Edge L n k i → ComplexMatrix2)}
    {Ω : Set (Edge L n k i → ComplexMatrix2)} (h𝒰 : 𝒰 = Ω ∩ fieldSpace L n k i)
    (h₁ : 𝒰₁ ⊆ fieldSpace L n k i) (hsub : 𝒰 ⊆ 𝒰₁) (W : Edge L n k (i + 1) → ComplexMatrix2) :
    levelFibre 𝒰 W = Ω ∩ levelFibre 𝒰₁ W := by
  ext V
  constructor
  · rintro ⟨hV, hW⟩
    exact ⟨(h𝒰 ▸ hV : V ∈ Ω ∩ _).1, hsub hV, hW⟩
  · rintro ⟨hΩ, hV, hW⟩
    exact ⟨h𝒰 ▸ (⟨hΩ, h₁ hV⟩ : V ∈ Ω ∩ _), hW⟩
theorem hasPosDefHessian_of_relOpen {i : ℕ} {N N' : Set (Edge L n k i → ComplexMatrix2)}
    {F : (Edge L n k i → ComplexMatrix2) → ℝ} {x : Edge L n k i → ComplexMatrix2}
    (hN : ComplexMatrix2.IsRelativelyOpen N N') (hx : x ∈ N') (h : HasPosDefHessian N F x) :
    HasPosDefHessian N' F x := by
  have hR := fieldCurveData_hasLocalCurves L n k i
  have hT := tangentSpan_relOpen_eq hR hN hx
  unfold HasPosDefHessian at h ⊢
  rw [hessianForm_relOpen_eq hR hN hx]
  generalize (fieldCurveData L n k i).tangentSpan N' x = T at hT ⊢
  subst hT
  exact h
theorem exists_open_energyIsActionAtBase {b : CriticalBranchData L n k} (hb : b.IsCritical) :
    ∀ i : ℕ, ∃ Z : Set (Edge L n k i → ComplexMatrix2), IsOpen Z ∧ trivialField L n k i ∈ Z ∧
      ∀ 𝒰 : Set (Edge L n k i → ComplexMatrix2), 𝒰 ⊆ Z ∩ fieldSpace L n k i →
        b.EnergyIsActionAtBase i 𝒰
  | 0 => by
    obtain ⟨O, hO, h1, hsub⟩ := mem_nhdsWithin.1 hb.energy_bottom
    exact ⟨O, hO, h1, fun 𝒰 h𝒰 V hV => hsub (h𝒰 hV)⟩
  | _ + 1 => ⟨univ, isOpen_univ, mem_univ _, fun _ _ => trivial⟩
theorem exists_isFibreNhd (hF : SmoothingFibres) (hG : AxialFunctionFacts.statement)
    (hE : BondSetFields.ProductStructureHolds)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (b : CriticalBranchData L n k)
    (hb : b.IsCritical) (i : ℕ) (hi : i < k) :
    ∃ 𝒰 : Set (Edge L n k i → ComplexMatrix2), b.IsFibreNhd i 𝒰 := by
  have hop := isOpenFieldSet_iff (j := i) hE hL hn hi.le
  have hop' := isOpenFieldSet_iff (j := i + 1) hE hL hn hi
  obtain ⟨-, -, -, ⟨𝒰s, hs1, -, hs3, hs4⟩, -, -, -⟩ := hF L n k i hL hn hi
  have hGi := hG L n k i hL hn hi
  obtain ⟨𝒰g, hg1, hg2, hg3⟩ := hGi.analytic_near_identity
  obtain ⟨𝒰S, hS1, hS2⟩ := hb.analytic_energy i hi.le
  obtain ⟨𝒰l, hl1, hl2⟩ := hb.analytic_prolong i hi
  obtain ⟨𝒰₁, h11, h12, 𝒪, h𝒪, h13⟩ := hb.fibre_structure i hi
  obtain ⟨Z, hZ, hZ1, hZact⟩ := exists_open_energyIsActionAtBase hb i
  obtain ⟨-, Os, hOs, hOseq⟩ := (hop 𝒰s).1 hs1.1
  obtain ⟨-, Og, hOg, hOgeq⟩ := (hop 𝒰g).1 hg1.1
  obtain ⟨-, OS, hOS, hOSeq⟩ := (hop 𝒰S).1 hS1.1
  obtain ⟨hc₁, O₁, hO₁, hO₁eq⟩ := (hop 𝒰₁).1 h11.1
  obtain ⟨u𝒪, hu𝒪, h1𝒪, hu𝒪sub⟩ := mem_nhdsWithin.1 h𝒪
  obtain ⟨A, hA, h1A, hAsub⟩ := mem_nhdsWithin.1 h12
  obtain ⟨uA, huA, huAeq⟩ := continuousOn_iff'.1 (continuousOn_of_isAnalyticFieldMap hs3) A hA
  set one := trivialField L n k i with hone
  have hone_conf : one ∈ fieldSpace L n k i := hs1.1.1 hs1.2
  have hmem : ∀ {𝒰 O : Set (Edge L n k i → ComplexMatrix2)}, one ∈ 𝒰 →
      𝒰 = O ∩ fieldSpace L n k i → one ∈ O := by
    intro 𝒰 O h e
    rw [e] at h
    exact h.1
  have hoA : one ∈ uA := by
    have : one ∈ smoothingStep L n k i ⁻¹' A ∩ 𝒰s := ⟨by
      change smoothingStep L n k i one ∈ A
      rw [hGi.smoothingStep_trivial]
      exact h1A, hs1.2⟩
    rw [huAeq] at this
    exact this.1
  let Ω : Set (Edge L n k i → ComplexMatrix2) := Os ∩ Og ∩ OS ∩ O₁ ∩ u𝒪 ∩ uA ∩ Z
  have hΩ : IsOpen Ω := (((((hOs.inter hOg).inter hOS).inter hO₁).inter hu𝒪).inter huA).inter hZ
  let 𝒰 : Set (Edge L n k i → ComplexMatrix2) := Ω ∩ fieldSpace L n k i
  have h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 :=
    (hop 𝒰).2 ⟨inter_subset_right, Ω, hΩ, rfl⟩
  have hone𝒰 : one ∈ 𝒰 := ⟨⟨⟨⟨⟨⟨⟨hmem hs1.2 hOseq, hmem hg1.2 hOgeq⟩, hmem hS1.2 hOSeq⟩,
    hmem h11.2 hO₁eq⟩, h1𝒪⟩, hoA⟩, hZ1⟩, hone_conf⟩
  have hs𝒰 : 𝒰 ⊆ 𝒰s := fun V hV => by
    rw [hOseq]; exact ⟨hV.1.1.1.1.1.1.1, hV.2⟩
  have hg𝒰 : 𝒰 ⊆ 𝒰g := fun V hV => by
    rw [hOgeq]; exact ⟨hV.1.1.1.1.1.1.2, hV.2⟩
  have hS𝒰 : 𝒰 ⊆ 𝒰S := fun V hV => by
    rw [hOSeq]; exact ⟨hV.1.1.1.1.1.2, hV.2⟩
  have h₁𝒰 : 𝒰 ⊆ 𝒰₁ := fun V hV => by
    rw [hO₁eq]; exact ⟨hV.1.1.1.1.2, hV.2⟩
  have h𝒪𝒰 : 𝒰 ⊆ 𝒪 := fun V hV => hu𝒪sub ⟨hV.1.1.1.2, hV.2⟩
  have hA𝒰 : ∀ V ∈ 𝒰, smoothingStep L n k i V ∈ A := by
    intro V hV
    have : V ∈ uA ∩ 𝒰s := ⟨hV.1.1.2, hs𝒰 hV⟩
    rw [← huAeq] at this
    exact this.1
  have hfib := levelFibre_eq_inter (𝒰 := 𝒰) (𝒰₁ := 𝒰₁) (Ω := Ω) rfl hc₁ h₁𝒰
  have hopen : ∀ W, ComplexMatrix2.IsRelativelyOpen (levelFibre 𝒰₁ W) (levelFibre 𝒰 W) :=
    fun W => ⟨Ω, hΩ, hfib W⟩
  have hR := fieldCurveData_hasLocalCurves L n k i
  refine ⟨𝒰, ⟨h𝒰, hone𝒰⟩, isAnalyticFieldMap_mono H hs3 h𝒰 hs𝒰, fun V hV => hg2 (hg𝒰 hV),
    isAnalyticFieldFunction_add H hS2 hg3 h𝒰 hS𝒰 hg𝒰, fun V hV => hs4 V (hs𝒰 hV), ?_, ?_,
    hZact 𝒰 fun V hV => ⟨hV.1.2, hV.2⟩⟩
  · intro W hW
    by_cases hne : levelFibre 𝒰 W = ∅
    · exact Or.inl hne
    · right
      obtain ⟨V, hV⟩ := nonempty_iff_ne_empty.2 hne
      have hWA : W ∈ A := by
        have := hA𝒰 V hV.1
        rwa [hV.2] at this
      obtain ⟨hra, hker⟩ := hAsub (⟨hWA, hW⟩ : W ∈ A ∩ _)
      refine ⟨?_, fun V' hV' B => ?_⟩
      · rw [hfib W]
        exact isAnalyticFieldSubmanifold_inter hop hΩ hra
      · rw [tangentSpan_relOpen_eq hR (hopen W) hV']
        refine hker V' ?_ B
        rw [hfib W] at hV'
        exact hV'.2
  · have hcl := continuousOn_of_isAnalyticFieldMap hl2
    obtain ⟨-, Ol, hOl, hOleq⟩ := (hop' 𝒰l).1 hl1.1
    have h1l := hl1.2
    have hlift1 : b.prolong i (trivialField L n k (i + 1)) = one := hb.prolong_trivial i hi
    have hnear : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W => W ∈ 𝒰l := by
      have h1Ol : trivialField L n k (i + 1) ∈ Ol := by
        have h2 := h1l
        rw [hOleq] at h2
        exact h2.1
      refine mem_nhdsWithin.2 ⟨Ol, hOl, h1Ol, fun W hW => ?_⟩
      rw [hOleq]
      exact hW
    have hnearΩ : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W => b.prolong i W ∈ Ω := by
      have ht := (hcl _ h1l).tendsto
      rw [hlift1] at ht
      have h2 : ∀ᶠ W in 𝓝[𝒰l] (trivialField L n k (i + 1)), b.prolong i W ∈ Ω :=
        ht (hΩ.mem_nhds hone𝒰.1)
      have h3 : 𝓝[𝒰l] (trivialField L n k (i + 1)) =
          𝓝[fieldSpace L n k (i + 1)] (trivialField L n k (i + 1)) := by
        refine le_antisymm (nhdsWithin_mono _ ?_) ?_
        · rw [hOleq]; exact inter_subset_right
        · exact nhdsWithin_le_of_mem hnear
      rw [h3] at h2
      exact h2
    have hsec := hb.prolong_section i hi
    filter_upwards [h13, hnear, hnearΩ, hsec] with W hW hWl hWΩ hWs
    have hxc : b.prolong i W ∈ fieldSpace L n k i := hl2.2.1 hWl
    have hx𝒰 : b.prolong i W ∈ 𝒰 := ⟨hWΩ, hxc⟩
    have hxf : b.prolong i W ∈ levelFibre 𝒰 W := ⟨hx𝒰, hWs.1⟩
    obtain ⟨⟨-, hcrit, huniq⟩, hpos⟩ := hW
    refine ⟨⟨hxf, (isCriticalOn_relOpen_iff hR (hopen W) _ _).2 ⟨hxf, hcrit⟩, fun V hV hVc => ?_⟩,
      hasPosDefHessian_of_relOpen (hopen W) hxf hpos⟩
    exact huniq V (h𝒪𝒰 hV.1) ((isCriticalOn_relOpen_iff hR (hopen W) _ _).1 hVc).2
end Neighbourhood
theorem fibreNeighbourhoodsOfSteps_holds (hF : SmoothingFibres) (hG : AxialFunctionFacts.statement)
    (hE : BondSetFields.ProductStructureHolds)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) :
    FibreNeighbourhoodsOfSteps := by
  refine ⟨?_, fun E _ _ => vectorCurveData_hasLocalCurves E, fieldCurveData_hasLocalCurves, ?_⟩
  · intro X T _ _ _ R hR N N' F hN x
    refine ⟨isCriticalOn_relOpen_iff hR hN F x, fun hc => ?_⟩
    have hx : x ∈ N' := hc.1
    exact ⟨tangentSpan_relOpen_eq hR hN hx, fun S _ _ ι => hessianForm_relOpen_eq hR hN hx ι F⟩
  · intro L n k hL hn _ b hb i hi
    exact exists_isFibreNhd hF hG hE H hL hn b hb i hi
end YangMills.Construction.Tower.StepFibreNeighbourhoods
