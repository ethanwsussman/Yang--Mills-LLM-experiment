import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOneProof
import YangMills.Construction.Towers.NormaliserLogarithmIsRealAnalyticNearOne
import YangMills.Construction.Towers.SurjectiveDifferentialsNearTheTrivialConfigurationProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LogNormaliserAnalyticity
open YangMills.Construction.Tower YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
variable {L n k j : ℕ}
theorem nonempty_basis_traceless :
    Nonempty (Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.traceless_basis_nonempty <;> assumption
theorem exists_supNorm_lt_subset_of_mem_nhds {σ : Type} [Fintype σ]
    {A : σ → Matrices.ComplexMatrix2} {N : Set (σ → Matrices.ComplexMatrix2)}
    (hN : N ∈ 𝓝 A) : ∃ s > 0, ∀ B : σ → Matrices.ComplexMatrix2, supNorm (B - A) < s → B ∈ N := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, fun B hB => hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hB
  exact le_ciSup (f := fun i => Matrices.ComplexMatrix2.operatorNorm ((B - A) i))
    (Set.finite_range _).bddAbove i
theorem continuous_expChartAt {ι κ : Type} (q : ι ⊕ κ → Matrices.ComplexMatrix2) :
    Continuous (expChartAt q) := by apply _root_.YangMills.Construction.Tower.NearIdentitySurjectivity.continuous_expChartAt <;> assumption
theorem expChartAt_zero {ι κ : Type} (q : ι ⊕ κ → Matrices.ComplexMatrix2) :
    expChartAt q 0 = q := by apply _root_.YangMills.SharedProofs.p39871 <;> assumption
def slitCoords : Set (Coordinates.ComplexCoordinates 1) := {z | z 0 ∈ Complex.slitPlane}
theorem isOpen_slitCoords : IsOpen slitCoords :=
  Complex.isOpen_slitPlane.preimage (continuous_apply 0)
theorem isHolomorphicToCoords_log_sub {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    {𝒳 : Set (ι ⊕ κ → Matrices.ComplexMatrix2)}
    {Φ : (ι ⊕ κ → Matrices.ComplexMatrix2) → Coordinates.ComplexCoordinates 1} (c : ℂ)
    (hΦ : IsHolomorphicToCoords b (Equiv.refl _) 𝒳 Φ) :
    IsHolomorphicToCoords b (Equiv.refl (Coordinates.ComplexCoordinates 1)) (𝒳 ∩ Φ ⁻¹' slitCoords)
      (fun p _ => Complex.log (Φ p 0) - c) := by
  obtain ⟨⟨O₀, hO₀, e₀⟩, hc, hh⟩ := hΦ
  have hcont : ContinuousOn Φ 𝒳 := hc
  obtain ⟨U, hU, hUe⟩ := continuousOn_iff'.1 hcont _ isOpen_slitCoords
  refine ⟨⟨U ∩ O₀, hU.inter hO₀, ?_⟩, ?_, ?_⟩
  · have hrew : 𝒳 ∩ Φ ⁻¹' slitCoords = U ∩ 𝒳 := by
      rw [inter_comm, hUe]
    rw [hrew, e₀, inter_assoc]
  · refine continuousOn_pi.2 fun _ => ?_
    exact (ContinuousOn.clog ((continuous_apply (0 : Fin 1)).comp_continuousOn
      (hcont.mono inter_subset_left)) fun p hp => hp.2).sub continuousOn_const
  · intro q hq
    obtain ⟨O, h0, hmaps, hOt, hOc⟩ := hh q hq.1
    refine ⟨O ∩ expChartAt q ⁻¹' (Φ ⁻¹' slitCoords), ⟨h0, ?_⟩,
      fun A hA => ⟨hmaps A hA.1, hA.2⟩, ⟨fun A hA => hOt.1 hA.1, fun A hA => ?_⟩, fun ν => ?_⟩
    · change Φ (expChartAt q 0) ∈ slitCoords
      rw [expChartAt_zero]
      exact hq.2
    · obtain ⟨s₁, hs₁, hb₁⟩ := hOt.2 A hA.1
      have hg : ContinuousWithinAt (Φ ∘ expChartAt q) O A :=
        (hcont _ (hmaps A hA.1)).comp (continuous_expChartAt q).continuousWithinAt hmaps
      have hev : (Φ ∘ expChartAt q) ⁻¹' slitCoords ∈ 𝓝[O] A :=
        hg (isOpen_slitCoords.mem_nhds hA.2)
      obtain ⟨N, hN, hNs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
      obtain ⟨s₂, hs₂, hb₂⟩ := exists_supNorm_lt_subset_of_mem_nhds hN
      refine ⟨min s₁ s₂, lt_min hs₁ hs₂, fun B hB hlt => ?_⟩
      have hBO := hb₁ B hB (lt_of_lt_of_le hlt (min_le_left _ _))
      exact ⟨hBO, hNs ⟨hb₂ B (lt_of_lt_of_le hlt (min_le_right _ _)), hBO⟩⟩
    · obtain ⟨hopen, hcn, hd⟩ := hOc ν
      have hcn' : ContinuousOn (fun w => Φ (expChartAt q (tupleOfCoords b ν w)))
          (tupleOfCoords b ν ⁻¹' O) := hcn
      have hset : IsOpen (tupleOfCoords b ν ⁻¹'
          (O ∩ expChartAt q ⁻¹' (Φ ⁻¹' slitCoords))) :=
        hcn'.isOpen_inter_preimage hopen isOpen_slitCoords
      refine ⟨hset, ?_, fun a ha i => ?_⟩
      · refine continuousOn_pi.2 fun _ => ?_
        exact (ContinuousOn.clog ((continuous_apply (0 : Fin 1)).comp_continuousOn
          (hcn'.mono fun w hw => hw.1)) fun w hw => hw.2).sub continuousOn_const
      · have hline : Continuous fun ζ : ℂ =>
            a + ζ • Coordinates.ComplexCoordinates.stdBasisVector i :=
          continuous_const.add (continuous_id.smul continuous_const)
        have hnear : ∀ᶠ ζ : ℂ in 𝓝 0, a + ζ • Coordinates.ComplexCoordinates.stdBasisVector i ∈
            tupleOfCoords b ν ⁻¹' (O ∩ expChartAt q ⁻¹' (Φ ⁻¹' slitCoords)) :=
          hline.continuousAt.eventually_mem (hset.mem_nhds (by simpa using ha))
        filter_upwards [hd a ha.1 i, hnear] with ζ d1 d2
        refine differentiableAt_pi.2 fun _ => ?_
        have d3 := differentiableAt_pi.1 d1 0
        exact (DifferentiableAt.clog d3 d2.2).sub_const c
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k j ∧ Matrices.ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) 𝒰 := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem isAnalyticFieldFunction_mono (H : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction 𝒰 F) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldFunction 𝒰' F := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mono <;> assumption
theorem isAnalyticFieldFunction_log_sub {𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction 𝒰 F)
    (hpos : ∀ V ∈ 𝒰, 0 < F V) (c : ℝ) :
    IsAnalyticFieldFunction 𝒰 fun V => Real.log (F V) - c := by
  obtain ⟨hop, i, a⟩ := h
  refine ⟨hop, i, a.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := a.2 p hp
  obtain ⟨b⟩ := nonempty_basis_traceless
  have hpm : p ∈ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → Matrices.ComplexMatrix2))
      (PositiveEdge L n k j) := by
    obtain ⟨O, -, e⟩ := a.1.2
    rw [e] at hp
    exact hp.2
  have hval : ∀ q ∈ 𝒳 ∩ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → Matrices.ComplexMatrix2))
      (PositiveEdge L n k j),
      Φ q 0 = (F (fieldOfPositiveValues (groupComponent q)) : ℂ) := fun q hq => congrFun (he hq) 0
  have hpX : p ∈ 𝒳 ∩ Φ ⁻¹' slitCoords := by
    refine ⟨h1, ?_⟩
    change Φ p 0 ∈ Complex.slitPlane
    rw [hval p ⟨h1, hpm⟩]
    exact Complex.ofReal_mem_slitPlane.2 (hpos _ hp)
  have hl := fun b' => isHolomorphicToCoords_log_sub b' (c : ℂ) (hΦ b')
  refine ⟨_, hpX, (hl b).1, fun q hq => h3 ⟨hq.1.1, hq.2⟩, _, hl, fun q hq => ?_⟩
  have hq𝒰 : fieldOfPositiveValues (groupComponent q) ∈ 𝒰 := h3 ⟨hq.1.1, hq.2⟩
  funext x
  simp only [hval q ⟨hq.1.1, hq.2⟩]
  rw [Complex.ofReal_sub, Complex.ofReal_log (hpos _ hq𝒰).le]
theorem logGaussianNormaliser_analytic (h₁ : GaussianNormaliserAnalyticNearIdentity)
    (h₂ : GaussianNormaliserPositiveNearOne)
    (h₃ : BondSetFields.ProductStructureHolds)
    (h₄ : LocalAnalyticity.LocalAnalyticityStatement) :
    LogNormaliserAnalyticNearOne := by
  intro L n k hL hn i hi
  obtain ⟨𝒰₀, ho, ha⟩ := h₁ L n k hL hn i hi
  have hop := isOpenFieldSet_iff (n := n) (k := k) (j := i + 1) h₃ hL hn hi
  obtain ⟨-, O₀, hO₀, e₀⟩ := (hop 𝒰₀).1 ho.1
  have hne : {W | 0 < gaussianNormaliser L n k i W} ∈
      𝓝[fieldSpace L n k (i + 1)] (trivialField L n k (i + 1)) :=
    h₂ L n k hL hn i hi
  obtain ⟨O, hO, h1O, hOs⟩ := mem_nhdsWithin.1 hne
  have h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup
      ((O ∩ O₀) ∩ fieldSpace L n k (i + 1)) :=
    (hop _).2 ⟨inter_subset_right, O ∩ O₀, hO.inter hO₀, rfl⟩
  have hsub : (O ∩ O₀) ∩ fieldSpace L n k (i + 1) ⊆ 𝒰₀ := fun V hV => by
    rw [e₀]
    exact ⟨hV.1.2, hV.2⟩
  have h2 : trivialField L n k (i + 1) ∈ O₀ ∩ fieldSpace L n k (i + 1) := by
    rw [← e₀]
    exact ho.2
  exact ⟨_, ⟨h𝒰, ⟨⟨h1O, h2.1⟩, h2.2⟩⟩, isAnalyticFieldFunction_log_sub
    (isAnalyticFieldFunction_mono h₄ ha h𝒰 hsub) (fun V hV => hOs ⟨hV.1.1, hV.2⟩) _⟩
end YangMills.Construction.Tower.LogNormaliserAnalyticity
end
