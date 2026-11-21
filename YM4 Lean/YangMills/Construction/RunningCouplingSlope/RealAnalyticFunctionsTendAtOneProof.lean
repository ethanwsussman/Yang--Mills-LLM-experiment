import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import YangMills.Construction.RunningCouplingSlope.RealAnalyticFunctionsTendAtOne
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.Matrices.GroupLieProduct.Subspaces in
theorem analyticFieldFunctionTendsAtOne_holds : AnalyticFieldFunctionTendsAtOne := by
  intro L n k j hL hn hj 𝒰 F h𝒰 hF
  classical
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hX : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  obtain ⟨-, inst, hR⟩ := hF
  let q : (Tower.Edge L n k j → Matrices.ComplexMatrix2) →
      (Tower.PositiveEdge L n k j ⊕ Empty → Matrices.ComplexMatrix2) := fun U =>
    ofParts (Tower.restrictToPositiveEdges U) Empty.elim
  have hcfg : ∀ U ∈ Tower.fieldSpace L n k j,
      Tower.fieldOfPositiveValues (Tower.restrictToPositiveEdges U) = U := by
    intro U hU
    funext b
    rcases hX b with ⟨hp, hn'⟩ | ⟨hp, hn'⟩
    · simp only [Tower.fieldOfPositiveValues, dif_pos hp]
      rfl
    · simp only [Tower.fieldOfPositiveValues, dif_neg hn', dif_pos hp]
      change (U b.opposite)⁻¹ = U b
      rw [hU.2 b (Set.mem_univ b)]
      have hd : Matrix.det (U b) = 1 :=
        (Matrix.mem_specialUnitaryGroup_iff.1 (hU.1 b (Set.mem_univ b))).2
      exact Matrix.nonsing_inv_nonsing_inv _ (by rw [hd]; exact isUnit_one)
  have hone : (fun _ : Tower.Edge L n k j => (1 : Matrices.ComplexMatrix2)) ∈ Tower.fieldSpace L n k j :=
    h𝒰.1.1 h𝒰.2
  have hq𝒲 : q (fun _ => 1) ∈ {q' | Tower.fieldOfPositiveValues (groupComponent q') ∈ 𝒰} := by
    change Tower.fieldOfPositiveValues
      (Tower.restrictToPositiveEdges fun _ => (1 : Matrices.ComplexMatrix2)) ∈ 𝒰
    rw [hcfg _ hone]
    exact h𝒰.2
  obtain ⟨𝒳, hp𝒳, ⟨O, hO, hXeq⟩, -, Φ, hhol, heq⟩ := hR.2 _ hq𝒲
  let bas : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless :=
    Module.Basis.ofEquivFun OneLoop.pauliCoordinateEquiv
  have hcont := (hhol bas).2.1
  have hqc : Continuous q := by
    refine continuous_pi fun r => ?_
    rcases r with r | r
    · exact continuous_apply _
    · exact r.elim
  have hreal : ∀ U ∈ Tower.fieldSpace L n k j,
      q U ∈ Matrices.GroupLieProduct (Tower.PositiveEdge L n k j) Empty ∧
      q U ∈ subspaceTimesGroup ⊥ (Tower.PositiveEdge L n k j) := by
    intro U hU
    refine ⟨?_, ?_, ?_⟩
    · rintro (r | r)
      · exact (Matrix.mem_specialUnitaryGroup_iff.1 (hU.1 r.1 (Set.mem_univ _))).2
      · exact r.elim
    · exact (Submodule.mem_bot ℝ).2 (funext fun r => r.elim)
    · exact fun r => hU.1 r.1 (Set.mem_univ _)
  have hev : ∀ᶠ U in 𝓝[Tower.fieldSpace L n k j] (fun _ => (1 : Matrices.ComplexMatrix2)), q U ∈ 𝒳 ∧
      q U ∈ subspaceTimesGroup ⊥ (Tower.PositiveEdge L n k j) := by
    have h1 : q (fun _ => 1) ∈ O := by
      rw [hXeq] at hp𝒳
      exact hp𝒳.1
    have h2 : ∀ᶠ U in 𝓝 (fun _ : Tower.Edge L n k j => (1 : Matrices.ComplexMatrix2)), q U ∈ O :=
      hqc.continuousAt.eventually (hO.mem_nhds h1)
    filter_upwards [h2.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with U f₁ f₂
    refine ⟨?_, (hreal U f₂).2⟩
    rw [hXeq]
    exact ⟨f₁, (hreal U f₂).1⟩
  have hT : Tendsto q (𝓝[Tower.fieldSpace L n k j] fun _ => (1 : Matrices.ComplexMatrix2))
      (𝓝[𝒳] q fun _ => 1) :=
    tendsto_nhdsWithin_iff.2 ⟨(hqc.tendsto _).mono_left nhdsWithin_le_nhds,
      hev.mono fun U h => h.1⟩
  have hlim := (hcont _ hp𝒳).tendsto.comp hT
  have hval : ∀ U ∈ Tower.fieldSpace L n k j, q U ∈ 𝒳 →
      q U ∈ subspaceTimesGroup ⊥ (Tower.PositiveEdge L n k j) →
      Φ (q U) = fun _ => ((F U : ℝ) : ℂ) := by
    intro U hU h1 h2
    have := heq ⟨h1, h2⟩
    rw [this]
    funext i
    change ((F (Tower.fieldOfPositiveValues (Tower.restrictToPositiveEdges U)) : ℝ) : ℂ) = _
    rw [hcfg U hU]
  have h0 := hval _ hone hp𝒳 (hreal _ hone).2
  have hlim2 : Tendsto (fun U => (Φ (q U)) 0)
      (𝓝[Tower.fieldSpace L n k j] fun _ => (1 : Matrices.ComplexMatrix2))
      (𝓝 (((F fun _ => 1 : ℝ)) : ℂ)) := by
    have h3 := (continuous_apply (0 : Fin 1)).continuousAt.tendsto.comp hlim
    have h4 : (Equiv.refl _ ∘ Φ) (q fun _ => 1) 0 = ((F fun _ => 1 : ℝ) : ℂ) := by
      simp only [Function.comp, Equiv.refl_apply, h0]
    rw [h4] at h3
    exact h3
  have hlim3 := (Complex.continuous_re.tendsto _).comp hlim2
  rw [Complex.ofReal_re] at hlim3
  refine hlim3.congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with U f₁ f₂
  simp only [Function.comp, hval U f₂ f₁.1 f₁.2, Complex.ofReal_re]
end YangMills.Construction.RunningCouplingSlope
end
