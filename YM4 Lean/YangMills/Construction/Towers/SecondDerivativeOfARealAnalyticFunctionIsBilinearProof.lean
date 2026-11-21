import YangMills.Construction.Towers.SecondDerivativeAtOneIsBilinearProof
import YangMills.Construction.Towers.SecondDerivativeOfARealAnalyticFunctionIsBilinear
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces
open YangMills.Construction.Matrices.PowerExpCharts
open YangMills.Construction.IdentityExpChart (formValues toLieFamily)
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftSecondDerivBilinear
variable {L n k j : ℕ}
private theorem isPositivelyOriented_or_opposite (e : Edge L n k j) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem positiveEdge_nonempty (hprod : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem holomorphicScalar_of_coords {ι : Type} [Fintype ι]
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Ψ : (ι ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords β (Equiv.refl _) W Ψ) :
    HolomorphicScalar β W fun q => Ψ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
set_option maxHeartbeats 400000 in
private theorem mixedDeriv_eq_fderiv_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (v w : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => φ (s • v + t • w)) 0) 0 =
      fderiv ℝ (fderiv ℝ φ) 0 v w := by apply _root_.YangMills.SharedProofs.p87674 <;> assumption
private theorem formValues_toMatrix {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (e : PositiveEdge L n k j) : (formValues B e).toMatrix = B e.1 := by apply _root_.YangMills.SharedProofs.p338 <;> assumption
private theorem fieldOfPositiveValues_matExp (X V : Edge L n k j → ComplexMatrix2) :
    fieldOfPositiveValues (fun e : PositiveEdge L n k j =>
        ComplexMatrix2.matExp (Complex.I • X e.1) * restrictToPositiveEdges V e) =
      PeriodicLattice.expTwist X V := by
  funext e
  by_cases h : e.IsPositivelyOriented
  · simp [fieldOfPositiveValues, PeriodicLattice.expTwist, h, restrictToPositiveEdges]
  · have h' := (isPositivelyOriented_or_opposite e).resolve_left h
    simp [fieldOfPositiveValues, PeriodicLattice.expTwist, h, h', restrictToPositiveEdges]
abbrev _root_.YangMills.DeltaSharedProofs.p502431 := @fieldOfPositiveValues_matExp
theorem holds (hC : ExpChartsStatement)
    (hprod : BondSetFields.ProductStructureHolds) : LeftSecondDerivBilinear := by
  intro L n k j hL hn hj 𝒰 G hG V hV
  obtain ⟨hopen, f₁, hra⟩ := hG
  let := f₁
  have := positiveEdge_nonempty hprod hL hn hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, -, -, -, -, -, -, hread⟩ := hC (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hfield : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U := by
    intro U hU
    funext e
    have hopp : e.opposite.opposite = e := PeriodicLattice.Bond.ext rfl rfl
    by_cases h : e.IsPositivelyOriented
    · simp [fieldOfPositiveValues, h, restrictToPositiveEdges]
    · have h' := (isPositivelyOriented_or_opposite e).resolve_left h
      have hinv := (hopen.1 hU).2 e.opposite (mem_univ _)
      simp only [fieldOfPositiveValues, dif_neg h, dif_pos h', restrictToPositiveEdges]
      rw [← hinv, hopp]
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => G (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
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
  let p₀ : PositiveEdge L n k j → ComplexMatrix2 := restrictToPositiveEdges V
  obtain ⟨N, hN, -, hsm, -⟩ :=
    (((hread β).1 _ hO).1 f hrest).1.1 p₀ ⟨V, hV, rfl⟩
  have hp₀ : p₀ ∈ specialUnitaryPower (PositiveEdge L n k j) :=
    fun c => (hopen.1 hV).1 c (mem_univ _)
  obtain ⟨-, hform, -⟩ := hcharts p₀ hp₀
  let g : (PositiveEdge L n k j → ComplexMatrix2.LieElement) → ℝ := f ∘ expChartI p₀
  have hg : ContDiffAt ℝ 2 g 0 := (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ g) 0 v w = fderiv ℝ (fderiv ℝ g) 0 w v :=
    fun v w => hg.isSymmSndFDerivAt (by simp) v w
  have hsecond : ∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
      leftSecondDeriv G V B B' =
        fderiv ℝ (fderiv ℝ g) 0 (formValues B) (formValues B') := by
    intro B hB B' hB'
    rw [← mixedDeriv_eq_fderiv_fderiv hg]
    refine congrArg (fun φ : ℝ → ℝ => deriv φ 0) (funext fun s => ?_)
    refine congrArg (fun φ : ℝ → ℝ => deriv φ 0) (funext fun t => ?_)
    show G (PeriodicLattice.expTwist _ _) = G (fieldOfPositiveValues (expChartI p₀ _))
    rw [(hform _).2.1, ← fieldOfPositiveValues_matExp]
    congr 2
    funext e
    congr 3
    have hm : ((s • formValues B + t • formValues B') e).toMatrix =
        s • (formValues B e).toMatrix + t • (formValues B' e).toMatrix := rfl
    rw [hm, formValues_toMatrix hB, formValues_toMatrix hB']
    simp
  have hlin : ∀ B₁ ∈ edgeFormSpace L n k j, ∀ B₂ ∈ edgeFormSpace L n k j, ∀ c : ℝ,
      formValues (c • B₁ + B₂) = c • formValues B₁ + formValues B₂ := by
    intro B₁ h₁ B₂ h₂ c
    funext e
    apply Subtype.ext
    show (formValues (c • B₁ + B₂) e).toMatrix =
      c • (formValues B₁ e).toMatrix + (formValues B₂ e).toMatrix
    rw [formValues_toMatrix ((edgeFormSpace L n k j).add_mem ((edgeFormSpace L n k j).smul_mem c h₁) h₂),
      formValues_toMatrix h₁, formValues_toMatrix h₂]
    rfl
  refine ⟨fun B hB B' hB' => ?_, fun B₁ h₁ B₂ h₂ B' hB' c => ?_⟩
  · rw [hsecond B hB B' hB', hsecond B' hB' B hB, hsymm]
  · rw [hsecond _ ((edgeFormSpace L n k j).add_mem ((edgeFormSpace L n k j).smul_mem c h₁) h₂) B' hB',
      hsecond B₁ h₁ B' hB', hsecond B₂ h₂ B' hB', hlin B₁ h₁ B₂ h₂ c]
    simp
end YangMills.Construction.Tower.LeftSecondDerivBilinear
end
