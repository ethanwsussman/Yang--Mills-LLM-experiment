import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
namespace YangMills.Construction.OneLoopLaw.ComplexHessianOfMember
noncomputable section
open Tower PeriodicOperators.Tempered Matrices Matrices.PowerExpCharts
section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem deriv_deriv_line_eq_fderiv_fderiv {f : V → ℝ} (hf : ContDiffAt ℝ 2 f 0) (u v : V) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => f (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ f) 0 u v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
end Calculus
section Edges
variable {L n : ℕ}
private theorem opposite_isPositivelyOriented_of_not {e : UnitEdge L n}
    (he : ¬ e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p9846 <;> assumption
private theorem fieldOfPositiveValues_exp (X : UnitEdge L n → ComplexMatrix2) :
    fieldOfPositiveValues (k := 0) (j := 0)
        (fun e : PositiveUnitEdge L n => ComplexMatrix2.matExp (Complex.I • X e.1) * 1) =
      PeriodicLattice.expTwist X (identityField L n) := by apply _root_.YangMills.SharedProofs.p49750 <;> assumption
private def toLieFamily (B : UnitEdge L n → ComplexMatrix2) (hB : B ∈ edgeFormSpace L n 0 0) :
    PositiveUnitEdge L n → ComplexMatrix2.LieElement :=
  fun e => (⟨B e.1, hB.1 e.1 e.2⟩ : ComplexMatrix2.hermitianTraceless)
private theorem toLieFamily_smul_add (a : ℝ) {B₁ B₂ : UnitEdge L n → ComplexMatrix2}
    (h₁ : B₁ ∈ edgeFormSpace L n 0 0) (h₂ : B₂ ∈ edgeFormSpace L n 0 0)
    (h : a • B₁ + B₂ ∈ edgeFormSpace L n 0 0) :
    toLieFamily (a • B₁ + B₂) h = a • toLieFamily B₁ h₁ + toLieFamily B₂ h₂ := rfl
private theorem exists_symm_bilinear (hc : ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) {F : FieldFamily L} (hF : IsAdmissibleMember (F n)) :
    ∃ (_ : Fintype (PositiveUnitEdge L n))
      (Q : (PositiveUnitEdge L n → ComplexMatrix2.LieElement) →L[ℝ]
        (PositiveUnitEdge L n → ComplexMatrix2.LieElement) →L[ℝ] ℝ),
      (∀ u v, Q u v = Q v u) ∧
      ∀ (B : UnitEdge L n → ComplexMatrix2) (hB : B ∈ edgeFormSpace L n 0 0)
        (B' : UnitEdge L n → ComplexMatrix2) (hB' : B' ∈ edgeFormSpace L n 0 0),
        hessianAtIdentity F n B B' = Q (toLieFamily B hB) (toLieFamily B' hB') := by
  obtain ⟨inst, O, hO, hone, hfO⟩ := hF.analytic
  obtain ⟨β, -⟩ := hp.2.2.2.1
  have : Nonempty (PositiveUnitEdge L n) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  obtain ⟨hcharts, -, -, -, -, -, -, hpull⟩ := hc (PositiveUnitEdge L n) Unit
  set g₀ : PositiveUnitEdge L n → ComplexMatrix2 := fun _ => 1 with hg₀
  have hg₀G : g₀ ∈ specialUnitaryPower (PositiveUnitEdge L n) := by
    obtain ⟨O', -, hEq⟩ := hO
    rw [hEq] at hone
    exact hone.2
  have hchart : ∀ u, expChartI g₀ u =
      fun s => ComplexMatrix2.matExp (Complex.I • (u s).toMatrix) * g₀ s :=
    fun u => ((hcharts g₀ hg₀G).2.1 u).2.1
  obtain ⟨N, hN, -, hsm, -⟩ := (((hpull β).1 O hO).1 _ (hfO β)).1.1 g₀ hone
  set f : (PositiveUnitEdge L n → ComplexMatrix2.LieElement) → ℝ :=
    (fun w => F n (fieldOfPositiveValues (k := 0) (j := 0) w)) ∘ expChartI g₀ with hf
  have htwo : ContDiffAt ℝ 2 f 0 := (hsm.contDiffAt hN).of_le
    (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  refine ⟨inst, fderiv ℝ (fderiv ℝ f) 0, fun u v => ?_, fun B hB B' hB' => ?_⟩
  · exact htwo.isSymmSndFDerivAt (by simp) u v
  · have hline : ∀ s t : ℝ, F n (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') (identityField L n)) =
        f (s • toLieFamily B hB + t • toLieFamily B' hB') := by
      intro s t
      rw [← fieldOfPositiveValues_exp]
      simp only [hf, Function.comp, hchart]
      congr 2
    unfold hessianAtIdentity leftSecondDeriv mixedDirectionalDeriv
    simp only [hline]
    exact deriv_deriv_line_eq_fderiv_fderiv htwo _ _
private theorem hessianAtIdentity_linear_and_symm (hc : ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) {F : FieldFamily L} (hF : IsAdmissibleMember (F n)) :
    (∀ a : ℝ, ∀ B₁ ∈ edgeFormSpace L n 0 0, ∀ B₂ ∈ edgeFormSpace L n 0 0,
      ∀ B' ∈ edgeFormSpace L n 0 0,
      hessianAtIdentity F n (a • B₁ + B₂) B' =
        a * hessianAtIdentity F n B₁ B' + hessianAtIdentity F n B₂ B') ∧
    ∀ B ∈ edgeFormSpace L n 0 0, ∀ B' ∈ edgeFormSpace L n 0 0,
      hessianAtIdentity F n B B' = hessianAtIdentity F n B' B := by
  obtain ⟨_, Q, hQs, hQ⟩ := exists_symm_bilinear hc hp hF
  refine ⟨fun a B₁ h₁ B₂ h₂ B' h' => ?_, fun B h B' h' => ?_⟩
  · have hmem := add_mem (Submodule.smul_mem _ a h₁) h₂
    rw [hQ _ hmem _ h', hQ _ h₁ _ h', hQ _ h₂ _ h', toLieFamily_smul_add a h₁ h₂ hmem]
    simp
  · rw [hQ _ h _ h', hQ _ h' _ h, hQs]
private theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
private theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
private theorem realComponent_smul_add (c : ℂ) (B₁ B₂ : UnitEdge L n → ComplexMatrix2) :
    realComponent (c • B₁ + B₂) =
      c.re • realComponent B₁ + ((-c.im) • imagComponent B₁ + realComponent B₂) := by
  funext e
  ext i j
  simp [realComponent, imagComponent, Matrix.conjTranspose_smul]
  apply Complex.ext <;> simp <;> ring
private theorem imagComponent_smul_add (c : ℂ) (B₁ B₂ : UnitEdge L n → ComplexMatrix2) :
    imagComponent (c • B₁ + B₂) =
      c.im • realComponent B₁ + (c.re • imagComponent B₁ + imagComponent B₂) := by
  funext e
  ext i j
  simp [realComponent, imagComponent, Matrix.conjTranspose_smul]
  apply Complex.ext <;> simp <;> ring
private theorem conjTranspose_apply_of_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) (e : UnitEdge L n) : (B e).conjTranspose = B e := by
  obtain ⟨hlie, hop⟩ := hB
  by_cases he : e.IsPositivelyOriented
  · exact (hlie e he).1.symm
  · have hneg : B e = -B e.opposite := by rw [hop e, neg_neg]
    rw [hneg, Matrix.conjTranspose_neg,
      (hlie _ (opposite_isPositivelyOriented_of_not he)).1.symm]
private theorem realComponent_of_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : realComponent B = B := by
  funext e
  rw [realComponent, conjTranspose_apply_of_mem hB, ← two_smul ℂ, smul_smul]
  simp
private theorem imagComponent_of_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n 0 0) : imagComponent B = 0 := by
  funext e
  simp [imagComponent, conjTranspose_apply_of_mem hB]
end Edges
theorem holds (hc : ExpChartsStatement) (hp : OneLoop.PauliMatrixRelations) : Statement := by
  intro L n _ _ F hF
  obtain ⟨hlin, hsym⟩ := hessianAtIdentity_linear_and_symm hc hp hF
  have hR := fun {B : UnitEdge L n → ComplexMatrix2} (h : B ∈ complexEdgeForms L n 0 0) =>
    realComponent_mem h
  have hS := fun {B : UnitEdge L n → ComplexMatrix2} (h : B ∈ complexEdgeForms L n 0 0) =>
    imagComponent_mem h
  have hzero : ∀ B ∈ edgeFormSpace L n 0 0, hessianAtIdentity F n 0 B = 0 := by
    intro B h
    have h0 := hlin 1 0 (zero_mem _) 0 (zero_mem _) B h
    simpa using h0
  refine ⟨fun c B₁ h₁ B₂ h₂ B' h' => ?_, fun B h B' h' => ?_, fun B h B' h' => ?_⟩
  · have hm : ∀ {x y}, x ∈ edgeFormSpace L n 0 0 → y ∈ edgeFormSpace L n 0 0 → ∀ a : ℝ,
        a • x + y ∈ edgeFormSpace L n 0 0 := fun hx hy a => add_mem (Submodule.smul_mem _ a hx) hy
    simp only [complexHessian, realComponent_smul_add, imagComponent_smul_add]
    rw [hlin _ _ (hR h₁) _ (hm (hS h₁) (hR h₂) _) _ (hR h'),
      hlin _ _ (hS h₁) _ (hR h₂) _ (hR h'),
      hlin _ _ (hR h₁) _ (hm (hS h₁) (hS h₂) _) _ (hS h'),
      hlin _ _ (hS h₁) _ (hS h₂) _ (hS h'),
      hlin _ _ (hR h₁) _ (hm (hS h₁) (hR h₂) _) _ (hS h'),
      hlin _ _ (hS h₁) _ (hR h₂) _ (hS h'),
      hlin _ _ (hR h₁) _ (hm (hS h₁) (hS h₂) _) _ (hR h'),
      hlin _ _ (hS h₁) _ (hS h₂) _ (hR h')]
    apply Complex.ext <;> simp <;> ring
  · simp only [complexHessian]
    rw [hsym _ (hR h) _ (hR h'), hsym _ (hS h) _ (hS h'), hsym _ (hR h) _ (hS h'),
      hsym _ (hS h) _ (hR h')]
    apply Complex.ext <;> simp <;> ring
  · simp only [complexHessian, realComponent_of_mem h, realComponent_of_mem h',
      imagComponent_of_mem h, imagComponent_of_mem h']
    have h00 := hzero 0 (zero_mem _)
    have h0 := hzero B' h'
    have h1 : hessianAtIdentity F n B 0 = 0 := by rw [hsym B h 0 (zero_mem _), hzero B h]
    rw [h00, h0, h1]
    simp
end
end YangMills.Construction.OneLoopLaw.ComplexHessianOfMember
