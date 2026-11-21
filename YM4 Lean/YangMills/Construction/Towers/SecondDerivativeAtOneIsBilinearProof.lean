import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import YangMills.Construction.Towers.SecondDerivativeAtOneIsBilinear
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces
open YangMills.Construction.Matrices.PowerExpCharts
open YangMills.Construction.IdentityExpChart (formValues toLieFamily)
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftSecondDerivAtIdentityBilinear
variable {L n k j : ℕ}
private theorem edge_positive_or_opposite (e : Edge L n k j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem finrank_traceless : Module.finrank ℂ Matrices.ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem nonempty_positiveEdge (hprod : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {W : Set (σ ⊕ Empty → Matrices.ComplexMatrix2)}
    {Ψ : (σ ⊕ Empty → Matrices.ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords β (Equiv.refl _) W Ψ) :
    HolomorphicScalar β W fun q => Ψ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
set_option maxHeartbeats 400000 in
private theorem mixed_deriv_eq_fderiv_fderiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V → ℝ} (hg : ContDiffAt ℝ 2 g 0) (v w : V) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => g (s • v + t • w)) 0) 0 =
      fderiv ℝ (fderiv ℝ g) 0 v w := by
  have hnear : ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hline₀ : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const v
    rw [one_smul] at h
    exact h
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ g (s • v) := by
    have h : Tendsto (fun s : ℝ => s • v) (𝓝 0) (𝓝 0) := by
      have h' := hline₀.continuousAt.tendsto
      rwa [zero_smul] at h'
    exact h.eventually hnear
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => g (s • v + t • w)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ g (s • v) w := by
    filter_upwards [hs] with s h
    have hline : HasDerivAt (fun t : ℝ => s • v + t • w) w 0 := by
      have h' := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (s • v)
      rw [one_smul] at h'
      exact h'
    have h₁ : HasFDerivAt g (fderiv ℝ g (s • v)) ((fun t : ℝ => s • v + t • w) 0) := by
      have e : (fun t : ℝ => s • v + t • w) 0 = s • v := by simp
      rw [e]
      exact h.hasFDerivAt
    exact (h₁.comp_hasDerivAt (0 : ℝ) hline).deriv
  rw [hinner.deriv_eq]
  have hdiff : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₁ : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) ((fun s : ℝ => s • v) 0) := by
    have e : (fun s : ℝ => s • v) 0 = 0 := by simp
    rw [e]
    exact hdiff.hasFDerivAt
  have h₂ := (h₁.comp_hasDerivAt (0 : ℝ) hline₀).clm_apply (hasDerivAt_const (0 : ℝ) w)
  have h₃ := h₂.deriv
  simp only [map_zero, add_zero] at h₃
  exact h₃
abbrev _root_.YangMills.SharedProofs.p87674 := @mixed_deriv_eq_fderiv_fderiv
private theorem formValues_toMatrix {A : Edge L n k j → Matrices.ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (e : PositiveEdge L n k j) :
    (formValues A e).toMatrix = A e.1 := by
  have h : restrictToPositiveEdges A e ∈ Matrices.ComplexMatrix2.hermitianTraceless := hA.1 e.1 e.2
  have hv : toLieFamily (restrictToPositiveEdges A) e =
      (⟨A e.1, h⟩ : Matrices.ComplexMatrix2.hermitianTraceless) := dif_pos h
  exact congrArg Matrices.ComplexMatrix2.LieElement.toMatrix hv
abbrev _root_.YangMills.SharedProofs.p338 := @formValues_toMatrix
private theorem fieldOfPositiveValues_expTwist (X : Edge L n k j → Matrices.ComplexMatrix2) :
    fieldOfPositiveValues (fun e : PositiveEdge L n k j =>
        Matrices.ComplexMatrix2.matExp (Complex.I • X e.1) *
          restrictToPositiveEdges (trivialField L n k j) e) =
      PeriodicLattice.expTwist X (trivialField L n k j) := by
  funext e
  by_cases h : e.IsPositivelyOriented
  · simp [fieldOfPositiveValues, PeriodicLattice.expTwist, h, restrictToPositiveEdges]
  · have h' := (edge_positive_or_opposite e).resolve_left h
    simp [fieldOfPositiveValues, PeriodicLattice.expTwist, h, h', restrictToPositiveEdges]
theorem holds (hcharts₀ : Matrices.PowerExpCharts.ExpChartsStatement)
    (hprod : BondSetFields.ProductStructureHolds) : LeftSecondDerivAtIdentityBilinear := by
  intro L n k j hL hn hj 𝒰 G h𝒰 hG
  obtain ⟨hopen, f₁, hra⟩ := hG
  let := f₁
  have := nonempty_positiveEdge hprod hL hn hj
  let β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ Matrices.ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, -, -, -, -, -, -, hread⟩ :=
    hcharts₀ (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : Matrices.specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hfield : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U := by
    intro U hU
    funext e
    have hoo : e.opposite.opposite = e := PeriodicLattice.Bond.ext rfl rfl
    by_cases h : e.IsPositivelyOriented
    · simp [fieldOfPositiveValues, h, restrictToPositiveEdges]
    · have h' := (edge_positive_or_opposite e).resolve_left h
      have hinv := (hopen.1 hU).2 e.opposite (mem_univ _)
      simp only [fieldOfPositiveValues, dif_neg h, dif_pos h', restrictToPositiveEdges]
      rw [← hinv, hoo]
  let f : (PositiveEdge L n k j → Matrices.ComplexMatrix2) → ℝ :=
    fun w => G (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → Matrices.ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hfield hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Ψ q 0, hp𝒳, holomorphicScalar_of_coords (hΨ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  let p₀ : PositiveEdge L n k j → Matrices.ComplexMatrix2 :=
    restrictToPositiveEdges (trivialField L n k j)
  obtain ⟨N, hN, -, hsm, -⟩ :=
    (((hread β).1 _ hO).1 f hrest).1.1 p₀ ⟨_, h𝒰.2, rfl⟩
  have hp₀ : p₀ ∈ Matrices.specialUnitaryPower (PositiveEdge L n k j) :=
    fun c => (hopen.1 h𝒰.2).1 c (mem_univ _)
  obtain ⟨-, hform, -⟩ := hcharts p₀ hp₀
  let g : (PositiveEdge L n k j → Matrices.ComplexMatrix2.LieElement) → ℝ := f ∘ expChartI p₀
  have hg : ContDiffAt ℝ 2 g 0 := (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ g) 0 v w = fderiv ℝ (fderiv ℝ g) 0 w v :=
    fun v w => hg.isSymmSndFDerivAt (by simp) v w
  have hsecond : ∀ A ∈ edgeFormSpace L n k j, ∀ A' ∈ edgeFormSpace L n k j,
      leftSecondDeriv G (trivialField L n k j) A A' =
        fderiv ℝ (fderiv ℝ g) 0 (formValues A) (formValues A') := by
    intro A hA A' hA'
    rw [← mixed_deriv_eq_fderiv_fderiv hg]
    refine congrArg (fun φ : ℝ → ℝ => deriv φ 0) (funext fun s => ?_)
    refine congrArg (fun φ : ℝ → ℝ => deriv φ 0) (funext fun t => ?_)
    show G (PeriodicLattice.expTwist _ _) = G (fieldOfPositiveValues (expChartI p₀ _))
    rw [(hform _).2.1, ← fieldOfPositiveValues_expTwist]
    congr 2
    funext e
    congr 3
    have hm : ((s • formValues A + t • formValues A') e).toMatrix =
        s • (formValues A e).toMatrix + t • (formValues A' e).toMatrix := rfl
    rw [hm, formValues_toMatrix hA, formValues_toMatrix hA']
    simp
  have hlin : ∀ A₁ ∈ edgeFormSpace L n k j, ∀ A₂ ∈ edgeFormSpace L n k j, ∀ c : ℝ,
      formValues (c • A₁ + A₂) = c • formValues A₁ + formValues A₂ := by
    intro A₁ h₁ A₂ h₂ c
    funext e
    apply Subtype.ext
    show (formValues (c • A₁ + A₂) e).toMatrix =
      c • (formValues A₁ e).toMatrix + (formValues A₂ e).toMatrix
    rw [formValues_toMatrix
        ((edgeFormSpace L n k j).add_mem ((edgeFormSpace L n k j).smul_mem c h₁) h₂),
      formValues_toMatrix h₁, formValues_toMatrix h₂]
    rfl
  refine ⟨fun A hA A' hA' => ?_, fun A₁ h₁ A₂ h₂ A' hA' c => ?_⟩
  · rw [hsecond A hA A' hA', hsecond A' hA' A hA, hsymm]
  · rw [hsecond _ ((edgeFormSpace L n k j).add_mem ((edgeFormSpace L n k j).smul_mem c h₁) h₂)
        A' hA', hsecond A₁ h₁ A' hA', hsecond A₂ h₂ A' hA', hlin A₁ h₁ A₂ h₂ c]
    simp
end YangMills.Construction.Tower.LeftSecondDerivAtIdentityBilinear
end
