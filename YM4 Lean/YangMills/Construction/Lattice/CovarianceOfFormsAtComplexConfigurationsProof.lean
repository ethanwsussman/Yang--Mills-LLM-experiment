import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.Lattice.CovarianceOfFormsAtComplexConfigurations
import YangMills.Construction.Lattice.CovariantAdjointFormulas
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposes
import YangMills.Construction.Lattice.HolomorphicIdentitiesUnderIsometries
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Lattice.TwistedActionOnFluctuationsAndLattices
import YangMills.Construction.Matrices.ComplexifiedAlgebraExp
import YangMills.Construction.Matrices.ExpChartHolomorphy
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Coordinates
namespace PeriodicLattice.ComplexTransportCovarianceProof
open YangMills.Construction.PeriodicLattice.ComplexTransport
section Bridge
theorem isHolomorphicVia_of_analyticAt {τ : Type} [Fintype τ] {T : Type} [NormedAddCommGroup T]
    [NormedSpace ℂ T] [FiniteDimensional ℂ T] {l k : ℕ} (eT : T ≃ ComplexCoordinates l)
    (hadd : ∀ x y, eT (x + y) = eT x + eT y) (hsmul : ∀ (t : ℂ) x, eT (t • x) = t • eT x)
    (ν : τ ≃ Fin k) {N : Set (τ → ComplexMatrix2)} (hN : IsOpen N) {F : (τ → ComplexMatrix2) → T}
    (hF : ∀ y ∈ N, AnalyticAt ℂ F y) :
    ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) eT N F := by
  let e := matrixPiEquiv ν
  let pos : Fin (ComplexCoordinates.productDim
      fun _ : Fin k => ComplexCoordinates.Component.matrix) → (i : Fin k) × Fin 4 := fun q =>
    (finSigmaFinEquiv
      (n := fun i => ((fun _ : Fin k => ComplexCoordinates.Component.matrix) i).dim)).symm q
  have key : ∀ (z : τ → ComplexMatrix2) (q), e z q =
      ComplexCoordinates.matrixEquiv (z (ν.symm (pos q).1)) (pos q).2 := fun _ _ => rfl
  let eL : (τ → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates (ComplexCoordinates.productDim
      fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
    { e with
      map_add' := fun x y => by
        funext q
        exact key (x + y) q
      map_smul' := fun t x => by
        funext q
        exact key (t • x) q }
  let eC := eL.toContinuousLinearEquiv
  let mL : T ≃ₗ[ℂ] ComplexCoordinates l :=
    { eT with
      map_add' := hadd
      map_smul' := hsmul }
  let mC := mL.toContinuousLinearEquiv
  have hopen : IsOpen (e '' N) := eC.toHomeomorph.isOpenMap N hN
  have han : ∀ w ∈ e '' N, AnalyticAt ℂ (eT ∘ F ∘ e.symm) w := by
    rintro _ ⟨y, hy, rfl⟩
    have h₁ : AnalyticAt ℂ eC.symm (e y) := eC.symm.toContinuousLinearMap.analyticAt _
    have e₁ : eC.symm (e y) = y := e.symm_apply_apply y
    have h₂ : AnalyticAt ℂ F (eC.symm (e y)) := by
      rw [e₁]
      exact hF y hy
    have h₃ : AnalyticAt ℂ (F ∘ eC.symm) (e y) := AnalyticAt.comp h₂ h₁
    exact AnalyticAt.comp (g := mC) (mC.toContinuousLinearMap.analyticAt _) h₃
  refine ⟨hopen, fun w hw => (han w hw).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • (ComplexCoordinates.stdBasisVector j) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • (ComplexCoordinates.stdBasisVector j) ∈ e '' N :=
    hline.continuousAt.eventually (by
      simp only [zero_smul, add_zero]
      exact hopen.mem_nhds ha)
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • (ComplexCoordinates.stdBasisVector j)) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := eT ∘ F ∘ e.symm) ζ (han _ hζ).differentiableAt hd
theorem isHolomorphicIn_congr {M M' : ℕ} {O : Set (ComplexCoordinates M)}
    {f g : ComplexCoordinates M → ComplexCoordinates M'} (h : ComplexCoordinates.IsHolomorphicIn O f)
    (hfg : ∀ z ∈ O, g z = f z) : ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.SharedProofs.p63802 <;> assumption
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem isHolomorphicToCoords_congr {E : Type} {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {e : E ≃ ComplexCoordinates l} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {G f : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords b e W G) (hfg : ∀ p ∈ W, f p = G p) :
    IsHolomorphicToCoords b e W f := by
  obtain ⟨hW, hc, hp⟩ := h
  refine ⟨hW, hc.congr fun p hp' => by simp only [Function.comp_apply, hfg p hp'],
    fun p hpW => ?_⟩
  obtain ⟨O, h0, hO, hT, hH⟩ := hp p hpW
  refine ⟨O, h0, hO, hT, fun ν => isHolomorphicIn_congr (hH ν) fun z hz => ?_⟩
  simp only [Function.comp_apply]
  rw [hfg _ (hO _ hz)]
def unitDetLocus (ι κ : Type) : Set (ι ⊕ κ → ComplexMatrix2) := {p | ∀ i, (p (.inl i)).det ≠ 0}
theorem isOpen_unitDetLocus : IsOpen (unitDetLocus ι κ) := by
  have h : unitDetLocus ι κ =
      ⋂ i, (fun p : ι ⊕ κ → ComplexMatrix2 => (p (.inl i)).det) ⁻¹' {0}ᶜ := by
    ext p
    simp [unitDetLocus]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton.preimage (by fun_prop)
theorem groupLieProduct_subset_unitDetLocus : GroupLieProduct ι κ ⊆ unitDetLocus ι κ :=
  fun p hp i => by
  have h : (p (.inl i)).det = 1 := hp (.inl i)
  rw [h]
  exact one_ne_zero
theorem isHolomorphicToCoords_of_analyticAt
    (hR : GroupLieProduct.ExpChartHolomorphy.ProductRestrictionHolomorphy ι κ)
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T] [FiniteDimensional ℂ T] {l : ℕ}
    (eT : T ≃ ComplexCoordinates l) (hadd : ∀ x y, eT (x + y) = eT x + eT y)
    (hsmul : ∀ (t : ℂ) x, eT (t • x) = t • eT x) {F : (ι ⊕ κ → ComplexMatrix2) → T}
    (hF : ∀ y ∈ unitDetLocus ι κ, AnalyticAt ℂ F y)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToCoords b eT (GroupLieProduct ι κ) F := by
  have h := (hR T l _ eT (Fintype.equivFin (ι ⊕ κ)) (unitDetLocus ι κ) F
    (isHolomorphicVia_of_analyticAt eT hadd hsmul _ isOpen_unitDetLocus hF)).2 b
  rwa [inter_eq_right.2 groupLieProduct_subset_unitDetLocus] at h
theorem groupLieProduct_isRelativelyOpen_self :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (GroupLieProduct ι κ) :=
  ⟨univ, isOpen_univ, (univ_inter _).symm⟩
theorem matrix_isHolomorphicToCoords
    (hR : GroupLieProduct.ExpChartHolomorphy.ProductRestrictionHolomorphy ι κ)
    {F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hF : ∀ y ∈ unitDetLocus ι κ, AnalyticAt ℂ F y)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv
      (GroupLieProduct ι κ) F :=
  isHolomorphicToCoords_of_analyticAt hR _ (fun _ _ => rfl) (fun _ _ => rfl) hF b
theorem scalar_isHolomorphicToCoords
    (hR : GroupLieProduct.ExpChartHolomorphy.ProductRestrictionHolomorphy ι κ)
    {F : (ι ⊕ κ → ComplexMatrix2) → ℂ} (hF : ∀ y ∈ unitDetLocus ι κ, AnalyticAt ℂ F y)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm
      (GroupLieProduct ι κ) F :=
  isHolomorphicToCoords_of_analyticAt hR _ (fun _ _ => rfl) (fun _ _ => rfl) hF b
theorem isHolomorphicToUnimodular_of_analyticAt
    (hR : GroupLieProduct.ExpChartHolomorphy.ProductRestrictionHolomorphy ι κ)
    (hG : GroupLieProduct.ExpChartHolomorphy.UnimodularValuedHolomorphy ι κ)
    {F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (hF : ∀ y ∈ unitDetLocus ι κ, AnalyticAt ℂ F y)
    (hM : MapsTo F (GroupLieProduct ι κ) ComplexMatrix2.unitDeterminant)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToUnimodular b (GroupLieProduct ι κ) F :=
  (hG b _ F groupLieProduct_isRelativelyOpen_self hM).2 (matrix_isHolomorphicToCoords hR hF b)
end Bridge
section Families
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {N : Set P}
def IsAnalyticUnitFamily (N : Set P) (F : P → ComplexMatrix2) : Prop :=
  AnalyticOnNhd ℂ F N ∧ ∀ y ∈ N, (F y).det ≠ 0
theorem IsAnalyticUnitFamily.inv {F : P → ComplexMatrix2} (h : IsAnalyticUnitFamily N F) :
    IsAnalyticUnitFamily N fun p => (F p)⁻¹ := by
  refine ⟨fun y hy => (analyticAt_inv_of_det_ne_zero (h.2 y hy)).comp (h.1 y hy), fun y hy => ?_⟩
  have h₁ := h.2 y hy
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero h₁
theorem IsAnalyticUnitFamily.mul {F G : P → ComplexMatrix2} (hF : IsAnalyticUnitFamily N F)
    (hG : IsAnalyticUnitFamily N G) : IsAnalyticUnitFamily N fun p => F p * G p :=
  ⟨fun y hy => (hF.1 y hy).mul (hG.1 y hy), fun y hy => by
    rw [Matrix.det_mul]
    exact mul_ne_zero (hF.2 y hy) (hG.2 y hy)⟩
theorem isAnalyticUnitFamily_one : IsAnalyticUnitFamily N fun _ : P => (1 : ComplexMatrix2) :=
  ⟨fun _ _ => analyticAt_const, fun _ _ => by simp⟩
theorem isAnalyticUnitFamily_matExp {F : P → ComplexMatrix2} (h : AnalyticOnNhd ℂ F N) :
    IsAnalyticUnitFamily N fun p => ComplexMatrix2.matExp (F p) :=
  ⟨fun y hy => (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp (h y hy), fun y _ =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp (F y))).ne_zero⟩
theorem analyticOnNhd_const_smul (c : ℂ) {F : P → ComplexMatrix2} (h : AnalyticOnNhd ℂ F N) :
    AnalyticOnNhd ℂ (fun p => c • F p) N :=
  fun y hy => (analyticAt_const (v := c)).fun_smul (h y hy)
theorem analyticOnNhd_conjugateBy {V A : P → ComplexMatrix2} (hV : IsAnalyticUnitFamily N V)
    (hA : AnalyticOnNhd ℂ A N) :
    AnalyticOnNhd ℂ (fun p => ComplexMatrix2.conjugateBy (V p) (A p)) N :=
  fun y hy => ((hV.1 y hy).mul (hA y hy)).mul (hV.inv.1 y hy)
variable {L m : ℕ} {j : ℤ}
theorem isAnalyticUnitFamily_pathHolonomy {U : P → Bond L m j → ComplexMatrix2}
    (hU : ∀ c, IsAnalyticUnitFamily N fun p => U p c) (Γ : List (Bond L m j)) :
    IsAnalyticUnitFamily N fun p => pathHolonomy (U p) Γ := by
  induction Γ with
  | nil => simpa [pathHolonomy] using isAnalyticUnitFamily_one
  | cons b Γ ih => simpa [pathHolonomy] using (hU b).mul ih
theorem analyticOnNhd_curvatureAt {U : P → Bond L m j → ComplexMatrix2}
    (hU : ∀ c, IsAnalyticUnitFamily N fun p => U p c) (ξ : ℝ) (q : Plaquette L m j) :
    AnalyticOnNhd ℂ (fun p => curvatureAt ξ (U p) q) N := by
  have h := isAnalyticUnitFamily_pathHolonomy hU q.boundaryBonds
  exact analyticOnNhd_const_smul _
    (analyticOnNhd_const_smul _ fun y hy => (h.1 y hy).sub (h.inv.1 y hy))
theorem analyticOnNhd_curvature {U : P → Bond L m j → ComplexMatrix2}
    (hU : ∀ c, IsAnalyticUnitFamily N fun p => U p c) (ξ : ℝ) (μ ν : Fin 4) (x : Site L m j) :
    AnalyticOnNhd ℂ (fun p => curvature ξ (U p) μ ν x) N := by
  unfold curvature plaquetteFormOf
  by_cases h : μ < ν
  · simp only [dif_pos h]
    exact analyticOnNhd_curvatureAt hU ξ _
  · by_cases h' : ν < μ
    · simp only [dif_neg h, dif_pos h']
      exact fun y hy => (analyticOnNhd_curvatureAt hU ξ _ y hy).neg
    · simp only [dif_neg h, dif_neg h']
      exact fun _ _ => analyticAt_const
theorem analyticOnNhd_covDerivAdjointSum {U : P → Bond L m j → ComplexMatrix2}
    (hU : ∀ c, IsAnalyticUnitFamily N fun p => U p c) (ξ ξ' : ℝ) (μ : Fin 4) (x : Site L m j) :
    AnalyticOnNhd ℂ
      (fun p => TransposeFormulas.covDerivAdjointSum ξ' (U p) (curvature ξ (U p)) μ x) N := by
  intro y hy
  unfold TransposeFormulas.covDerivAdjointSum
  refine Finset.analyticAt_fun_sum _ fun ν _ => ?_
  unfold covDerivAdjointComponent
  refine analyticOnNhd_const_smul _ (fun y hy => (analyticOnNhd_conjugateBy (hU _).inv
    (analyticOnNhd_curvature hU ξ ν μ _) y hy).sub (analyticOnNhd_curvature hU ξ ν μ _ y hy)) y hy
theorem analyticOnNhd_twistedTransportForm {V A : P → Bond L m j → ComplexMatrix2}
    (hV : ∀ c, IsAnalyticUnitFamily N fun p => V p c)
    (hA : ∀ c, AnalyticOnNhd ℂ (fun p => A p c) N)
    (σ : FourTorus L m ≃ FourTorus L m) (c : Bond L m j) :
    AnalyticOnNhd ℂ (fun p => twistedTransportForm σ (V p) (A p) c) N := by
  have hval : ∀ c : Bond L m j,
      AnalyticOnNhd ℂ (fun p => twistedFormValue σ (V p) (A p) c) N := by
    intro c
    unfold twistedFormValue
    by_cases h : (bondPreimage σ c).IsPositivelyOriented
    · simp only [if_pos h]
      exact hA _
    · simp only [if_neg h]
      exact fun y hy => (analyticOnNhd_conjugateBy (hV _).inv (hA _) y hy).neg
  unfold twistedTransportForm
  by_cases h : c.IsPositivelyOriented
  · simp only [if_pos h]
    exact hval c
  · simp only [if_neg h]
    exact fun y hy => (hval _ y hy).neg
theorem isAnalyticUnitFamily_expTwist {V A : P → Bond L m j → ComplexMatrix2}
    (hV : ∀ c, IsAnalyticUnitFamily N fun p => V p c)
    (hA : ∀ c, AnalyticOnNhd ℂ (fun p => A p c) N)
    (c : Bond L m j) : IsAnalyticUnitFamily N fun p => expTwist (A p) (V p) c := by
  have hone : ∀ c : Bond L m j, IsAnalyticUnitFamily N
      fun p => ComplexMatrix2.matExp (Complex.I • A p c) * V p c := fun c =>
    (isAnalyticUnitFamily_matExp (analyticOnNhd_const_smul _ (hA c))).mul (hV c)
  unfold expTwist
  by_cases h : c.IsPositivelyOriented
  · simp only [if_pos h]
    exact hone c
  · simp only [if_neg h]
    exact (hone _).inv
def traceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
theorem analyticOnNhd_bondFormInner [Fintype (Site L m j)] {A B : P → Bond L m j → ComplexMatrix2}
    (hA : ∀ c, AnalyticOnNhd ℂ (fun p => A p c) N)
    (hB : ∀ c, AnalyticOnNhd ℂ (fun p => B p c) N)
    (ξ : ℝ) : AnalyticOnNhd ℂ (fun p => bondFormInner ξ (A p) (B p)) N := by
  intro y hy
  unfold bondFormInner
  simp only [finsum_eq_sum_of_fintype]
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ =>
    Finset.analyticAt_fun_sum _ fun μ _ => analyticAt_const.mul ?_)
  exact (traceCLM.analyticAt _).comp ((hA _ y hy).mul (hB _ y hy))
end Families
section Values
variable {L m : ℕ} {j : ℤ}
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem det_ne_zero_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X.det ≠ 0 := by
  have h₁ : X.det = 1 := h
  rw [h₁]
  exact one_ne_zero
theorem conjugateBy_mem_complexLieAlgebra {X A : ComplexMatrix2} (hX : X.det ≠ 0)
    (hA : A ∈ complexLieAlgebra) :
    ComplexMatrix2.conjugateBy X A ∈ complexLieAlgebra := by
  have h₁ : Matrix.trace A = 0 := hA
  change Matrix.trace (X * A * X⁻¹) = 0
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hX),
    one_mul, h₁]
theorem analyticOnNhd_eval {τ : Type} [Fintype τ] (s : τ) {N : Set (τ → ComplexMatrix2)} :
    AnalyticOnNhd ℂ (fun p : τ → ComplexMatrix2 => p s) N :=
  fun y _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ComplexMatrix2) s).analyticAt y
theorem gaugeFieldOfPoint_mem (ℬ : Set (Bond L m j)) {κ : Type}
    {p : PositiveBondOf ℬ ⊕ κ → ComplexMatrix2} (hp : p ∈ GroupLieProduct (PositiveBondOf ℬ) κ)
    (c : Bond L m j) : gaugeFieldOfPoint ℬ p c ∈ ComplexMatrix2.unitDeterminant := by
  unfold gaugeFieldOfPoint gaugeFieldOfPositiveValues
  by_cases h : c ∈ ℬ ∧ c.IsPositivelyOriented
  · simp only [dif_pos h]
    exact hp (.inl _)
  · by_cases h' : c.opposite ∈ ℬ ∧ c.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact inv_mem_unitDeterminant (hp (.inl _))
    · simp only [dif_neg h, dif_neg h']
      change Matrix.det (1 : ComplexMatrix2) = 1
      simp
theorem isAnalyticUnitFamily_gaugeFieldOfPoint (ℬ : Set (Bond L m j))
    [Fintype (PositiveBondOf ℬ)] (κ : Type) [Fintype κ] (c : Bond L m j) :
    IsAnalyticUnitFamily (unitDetLocus (PositiveBondOf ℬ) κ) fun p => gaugeFieldOfPoint ℬ p c := by
  unfold gaugeFieldOfPoint gaugeFieldOfPositiveValues
  by_cases h : c ∈ ℬ ∧ c.IsPositivelyOriented
  · simp only [dif_pos h]
    exact ⟨analyticOnNhd_eval _, fun y hy => hy _⟩
  · by_cases h' : c.opposite ∈ ℬ ∧ c.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact IsAnalyticUnitFamily.inv ⟨analyticOnNhd_eval _, fun y hy => hy _⟩
    · simp only [dif_neg h, dif_neg h']
      exact isAnalyticUnitFamily_one
theorem analyticOnNhd_bondFormOfPositiveValues {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℂ P] {N : Set P}
    (ℬ : Set (Bond L m j)) {a : P → PositiveBondOf ℬ → ComplexMatrix2}
    (ha : ∀ i, AnalyticOnNhd ℂ (fun p => a p i) N) (c : Bond L m j) :
    AnalyticOnNhd ℂ (fun p => bondFormOfPositiveValues ℬ (a p) c) N := by
  unfold bondFormOfPositiveValues
  by_cases h : c ∈ ℬ ∧ c.IsPositivelyOriented
  · simp only [dif_pos h]
    exact ha _
  · by_cases h' : c.opposite ∈ ℬ ∧ c.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact fun y hy => (ha _ y hy).neg
    · simp only [dif_neg h, dif_neg h']
      exact fun _ _ => analyticAt_const
theorem bondFormOfPositiveValues_mem (ℬ : Set (Bond L m j)) {a : PositiveBondOf ℬ → ComplexMatrix2}
    (ha : ∀ i, a i ∈ complexLieAlgebra) (c : Bond L m j) :
    bondFormOfPositiveValues ℬ a c ∈ complexLieAlgebra := by
  unfold bondFormOfPositiveValues
  by_cases h : c ∈ ℬ ∧ c.IsPositivelyOriented
  · simp only [dif_pos h]
    exact ha _
  · by_cases h' : c.opposite ∈ ℬ ∧ c.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact ComplexMatrix2.traceless.neg_mem (ha _)
    · simp only [dif_neg h, dif_neg h']
      exact ComplexMatrix2.traceless.zero_mem
theorem twistedTransportForm_mem {V A : Bond L m j → ComplexMatrix2}
    (hV : ∀ c, V c ∈ ComplexMatrix2.unitDeterminant)
    (hA : ∀ c, A c ∈ complexLieAlgebra) (σ : FourTorus L m ≃ FourTorus L m) (c : Bond L m j) :
    twistedTransportForm σ V A c ∈ complexLieAlgebra := by
  have hval : ∀ c : Bond L m j, twistedFormValue σ V A c ∈ complexLieAlgebra := by
    intro c
    unfold twistedFormValue
    by_cases h : (bondPreimage σ c).IsPositivelyOriented
    · simp only [if_pos h]
      exact hA _
    · simp only [if_neg h]
      exact ComplexMatrix2.traceless.neg_mem (conjugateBy_mem_complexLieAlgebra
        (det_ne_zero_of_mem_unitDeterminant (inv_mem_unitDeterminant (hV _))) (hA _))
  unfold twistedTransportForm
  by_cases h : c.IsPositivelyOriented
  · simp only [if_pos h]
    exact hval c
  · simp only [if_neg h]
    exact ComplexMatrix2.traceless.neg_mem (hval _)
theorem expTwist_mem
    (hX : ∀ Y ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.unitDeterminant)
    {V A : Bond L m j → ComplexMatrix2} (hV : ∀ c, V c ∈ ComplexMatrix2.unitDeterminant)
    (hA : ∀ c, A c ∈ complexLieAlgebra) (c : Bond L m j) :
    expTwist A V c ∈ ComplexMatrix2.unitDeterminant := by
  have hone : ∀ c : Bond L m j,
      ComplexMatrix2.matExp (Complex.I • A c) * V c ∈ ComplexMatrix2.unitDeterminant := by
    intro c
    have h₁ : (ComplexMatrix2.matExp (Complex.I • A c)).det = 1 := hX _ (hA c)
    have h₂ : (V c).det = 1 := hV c
    change (ComplexMatrix2.matExp (Complex.I • A c) * V c).det = 1
    rw [Matrix.det_mul, h₁, h₂, one_mul]
  unfold expTwist
  by_cases h : c.IsPositivelyOriented
  · simp only [if_pos h]
    exact hone c
  · simp only [if_neg h]
    exact inv_mem_unitDeterminant (hone _)
theorem isGaugeField_gaugeFieldOfPoint (hL : 2 ≤ L) (hj : -(m : ℤ) < j)
    (ℬ : Set (Bond L m j)) {κ : Type} {p : PositiveBondOf ℬ ⊕ κ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct (PositiveBondOf ℬ) κ) :
    IsGaugeField complexGaugeGroup univ (gaugeFieldOfPoint ℬ p) := by
  refine ⟨fun c _ => gaugeFieldOfPoint_mem ℬ hp c, fun c _ => ?_⟩
  have hrr : c.opposite.opposite = c := Bond.ext rfl rfl
  unfold gaugeFieldOfPoint gaugeFieldOfPositiveValues
  by_cases h₁ : c ∈ ℬ ∧ c.IsPositivelyOriented
  · have h₂ : ¬ (c.opposite ∈ ℬ ∧ c.opposite.IsPositivelyOriented) := fun h => by
      rcases MatrixValued.xor_isPositivelyOriented_opposite hL hj c with ⟨_, hr⟩ | ⟨_, hb⟩
      · exact hr h.2
      · exact hb h₁.2
    have h₃ : c.opposite.opposite ∈ ℬ ∧ c.opposite.opposite.IsPositivelyOriented := by rwa [hrr]
    simp only [dif_pos h₁, dif_neg h₂, dif_pos h₃]
    congr 2
  · by_cases h₂ : c.opposite ∈ ℬ ∧ c.opposite.IsPositivelyOriented
    · simp only [dif_neg h₁, dif_pos h₂]
      rw [Matrix.nonsing_inv_nonsing_inv]
      have h₃ : (p (.inl ⟨c.opposite, h₂⟩)).det = 1 := hp (.inl _)
      rw [h₃]
      exact isUnit_one
    · have h₃ : ¬ (c.opposite.opposite ∈ ℬ ∧ c.opposite.opposite.IsPositivelyOriented) := by
        rwa [hrr]
      simp only [dif_neg h₁, dif_neg h₂, dif_neg h₃, inv_one]
theorem mem_of_isBondForm (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {A : Bond L m j → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) (c : Bond L m j) : A c ∈ complexLieAlgebra := by
  rcases MatrixValued.xor_isPositivelyOriented_opposite hL hj c with ⟨hb, _⟩ | ⟨hr, _⟩
  · exact hA.1 c hb
  · have h := hA.2 c.opposite
    have hrr : c.opposite.opposite = c := Bond.ext rfl rfl
    rw [hrr] at h
    rw [h]
    exact ComplexMatrix2.traceless.neg_mem (hA.1 _ hr)
theorem bondImage_bijective_and_preimage [Finite (Bond L m j)] {σ : FourTorus L m ≃ FourTorus L m}
    (h : ∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target) :
    Function.Bijective (bondImage σ : Bond L m j → Bond L m j) ∧
      ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b := by
  have hinj : Function.Injective (bondImage σ : Bond L m j → Bond L m j) := by
    intro b b' e
    refine Bond.ext (Subtype.ext (σ.injective ?_)) (Subtype.ext (σ.injective ?_))
    · rw [← (h b).1, ← (h b').1, e]
    · rw [← (h b).2, ← (h b').2, e]
  refine ⟨⟨hinj, Finite.injective_iff_surjective.1 hinj⟩, fun b => ?_⟩
  have hex : ∃ b' : Bond L m j, (b'.source : FourTorus L m) = σ.symm (bondImage σ b).source ∧
      (b'.target : FourTorus L m) = σ.symm (bondImage σ b).target :=
    ⟨b, by rw [(h b).1]; simp, by rw [(h b).2]; simp⟩
  unfold bondPreimage
  rw [dif_pos hex]
  refine Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [hex.choose_spec.1, (h b).1]
    simp
  · rw [hex.choose_spec.2, (h b).2]
    simp
theorem transportGaugeField_extendByOne {σ : FourTorus L m ≃ FourTorus L m}
    (hbij : Function.Bijective (bondImage σ : Bond L m j → Bond L m j))
    (hpull : ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b)
    (ℬ : Set (Bond L m j)) (V : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ (extendByOne ℬ V) =
      extendByOne (bondSetTransport σ ℬ) (transportGaugeField σ V) := by
  funext c
  obtain ⟨b, rfl⟩ := hbij.2 c
  have hmem : bondImage σ b ∈ bondSetTransport σ ℬ ↔ b ∈ ℬ := hbij.1.mem_set_image
  simp only [transportGaugeField, extendByOne]
  by_cases hb : b ∈ ℬ
  · rw [if_pos (by rwa [hpull]), if_pos (hmem.2 hb), hpull]
  · rw [if_neg (by rwa [hpull]), if_neg fun h => hb (hmem.1 h)]
end Values
section Transpose
variable {L m : ℕ} {j : ℤ}
theorem bondFormInner_smul_left [Fintype (Site L m j)] (ξ : ℝ) (c : ℂ)
    (B A : Bond L m j → ComplexMatrix2) :
    bondFormInner ξ (c • B) A = c * bondFormInner ξ B A := by
  unfold bondFormInner bondFormComponent
  simp only [finsum_eq_sum_of_fintype, Pi.smul_apply, smul_mul_assoc, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
  ring
theorem plaquetteFormInner_smul_right [Fintype (Site L m j)] (ξ : ℝ) (c : ℂ)
    (F H : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) :
    plaquetteFormInner ξ F (fun μ ν x => c • H μ ν x) = c * plaquetteFormInner ξ F H := by
  unfold plaquetteFormInner
  simp only [finsum_eq_sum_of_fintype, mul_smul_comm, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  ring
theorem bondFormInner_rescale {ξ ξ' : ℝ} (hξ' : ξ' ≠ 0) (B A : Bond L m j → ComplexMatrix2) :
    bondFormInner ξ B A = (((ξ / ξ') ^ 4 : ℝ) : ℂ) * bondFormInner ξ' B A := by
  unfold bondFormInner
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp
theorem plaquetteFormInner_rescale {ξ ξ' : ℝ} (hξ' : ξ' ≠ 0)
    (F H : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) :
    plaquetteFormInner ξ F H = (((ξ / ξ') ^ 4 : ℝ) : ℂ) * plaquetteFormInner ξ' F H := by
  unfold plaquetteFormInner
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp
theorem covExteriorDeriv_rescale {ξ ξ' : ℝ} (hξ : ξ ≠ 0) (hξ' : ξ' ≠ 0)
    (U A : Bond L m j → ComplexMatrix2) :
    covExteriorDeriv ξ U A =
      fun μ ν x => ((ξ' / ξ : ℝ) : ℂ) • covExteriorDeriv ξ' U A μ ν x := by
  have h : ((ξ⁻¹ : ℝ) : ℂ) = ((ξ' / ξ : ℝ) : ℂ) * ((ξ'⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  funext μ ν x
  unfold covExteriorDeriv covDeriv
  rw [h]
  simp only [mul_smul, smul_sub]
theorem covExteriorDerivAdjoint_rescale (hForm : LieInnerProduct.PeriodicLatticePairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    {ξ ξ' : ℝ} (hξ : 0 < ξ)
    (hξ' : 0 < ξ') {U : Bond L m j → ComplexMatrix2} (hU : IsGaugeField complexGaugeGroup univ U)
    {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2} (hF : IsPlaquetteForm complexLieAlgebra F) :
    IsBondForm complexLieAlgebra (covExteriorDerivAdjoint ξ U F) ∧
      covExteriorDerivAdjoint ξ U F =
        ((ξ' / ξ : ℝ) : ℂ) • covExteriorDerivAdjoint ξ' U F := by
  obtain ⟨hfs, h₂, h₃, -, hT⟩ := hForm L m j ξ hL hm hj hξ
  obtain ⟨h₁', h₂', h₃', -, hT'⟩ := hForm L m j ξ' hL hm hj hξ'
  letI : Fintype (Site L m j) := Fintype.ofFinite _
  obtain ⟨-, -, -, -, -, hiff⟩ := hT U hU
  obtain ⟨-, -, -, -, -, hiff'⟩ := hT' U hU
  have spec' := (hiff' ⟨F, hF⟩ _).2 rfl
  have hB : IsBondForm complexLieAlgebra
        (((ξ' / ξ : ℝ) : ℂ) • covExteriorDerivAdjoint ξ' U F) ∧
      ∀ A, IsBondForm complexLieAlgebra A →
        bondFormInner ξ (((ξ' / ξ : ℝ) : ℂ) • covExteriorDerivAdjoint ξ' U F) A =
          plaquetteFormInner ξ F (covExteriorDeriv ξ U A) := by
    refine ⟨⟨fun b hb => ComplexMatrix2.traceless.smul_mem _ (spec'.1.1 b hb), fun b => ?_⟩,
      fun A hA => ?_⟩
    · simp only [Pi.smul_apply, spec'.1.2 b, smul_neg]
    · rw [bondFormInner_smul_left, bondFormInner_rescale hξ'.ne', spec'.2 A hA,
        covExteriorDeriv_rescale hξ.ne' hξ'.ne', plaquetteFormInner_smul_right,
        plaquetteFormInner_rescale (ξ := ξ) hξ'.ne']
  have heq := (hiff ⟨F, hF⟩ _).1 hB
  exact ⟨heq ▸ hB.1, heq.symm⟩
theorem pathHolonomy_mem {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ c, U c ∈ ComplexMatrix2.unitDeterminant)
    (Γ : List (Bond L m j)) : pathHolonomy U Γ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.pathHolonomy_mem_complexGaugeGroup <;> assumption
theorem isPlaquetteForm_curvature {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ c, U c ∈ ComplexMatrix2.unitDeterminant)
    (ξ : ℝ) : IsPlaquetteForm complexLieAlgebra (curvature ξ U) := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.curvature_isPlaquetteForm <;> assumption
theorem isBondForm_yangMillsCurrent (hForm : LieInnerProduct.PeriodicLatticePairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    {ξ : ℝ} (hξ : 0 < ξ)
    {U : Bond L m j → ComplexMatrix2} (hU : IsGaugeField complexGaugeGroup univ U) :
    IsBondForm complexLieAlgebra (yangMillsCurrent ξ U) :=
  (covExteriorDerivAdjoint_rescale hForm hL hm hj hξ hξ hU
    (isPlaquetteForm_curvature (fun c => hU.1 c (mem_univ c)) ξ)).1
theorem yangMillsCurrent_eq_smul_covDerivAdjointSum
    (hEx : TransposeFormulas.ExplicitAdjointFormulas)
    (hForm : LieInnerProduct.PeriodicLatticePairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    {ξ : ℝ} (hξ : 0 < ξ) (c : Bond L m j) :
    ∃ (s : ℂ) (μ : Fin 4) (x : Site L m j), ∀ U, IsGaugeField complexGaugeGroup univ U →
      yangMillsCurrent ξ U c = s • TransposeFormulas.covDerivAdjointSum
        (toLevelUnits L 1 0 (meshSize L j)) U (curvature ξ U) μ x := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hξ' : 0 < toLevelUnits L 1 0 (meshSize L j) := by
    unfold toLevelUnits meshSize
    positivity
  have hfwd : ∀ (μ : Fin 4) (x : Site L m j) (U : Bond L m j → ComplexMatrix2),
      IsGaugeField complexGaugeGroup univ U →
      yangMillsCurrent ξ U (Bond.forwardFrom x μ) =
        ((toLevelUnits L 1 0 (meshSize L j) / ξ : ℝ) : ℂ) •
          TransposeFormulas.covDerivAdjointSum (toLevelUnits L 1 0 (meshSize L j)) U
            (curvature ξ U) μ x := by
    intro μ x U hU
    have hF := isPlaquetteForm_curvature (fun c => hU.1 c (mem_univ c)) ξ
    have h₁ := (covExteriorDerivAdjoint_rescale hForm hL hm hj hξ hξ' hU hF).2
    have h₂ := (((hEx.1 L m 1 0 hL.1 hL.2 hm one_pos (Nat.zero_le _) j hj _ rfl).1 U hU).1
      (curvature ξ U) hF μ x).1
    have h₃ : yangMillsCurrent ξ U = covExteriorDerivAdjoint ξ U (curvature ξ U) := rfl
    rw [h₃, h₁, Pi.smul_apply, ← h₂]
    rfl
  rcases MatrixValued.xor_isPositivelyOriented_opposite hL2 hj c with ⟨⟨μ, hμ⟩, _⟩ | ⟨⟨μ, hμ⟩, _⟩
  · have e : Bond.forwardFrom c.source μ = c :=
      Bond.ext rfl (by
        change c.source + unitStep L m j μ = c.target
        rw [← hμ]
        abel)
    refine ⟨((toLevelUnits L 1 0 (meshSize L j) / ξ : ℝ) : ℂ), μ, c.source, fun U hU => ?_⟩
    have h := hfwd μ c.source U hU
    rwa [e] at h
  · have e : Bond.forwardFrom c.opposite.source μ = c.opposite :=
      Bond.ext rfl (by
        change c.opposite.source + unitStep L m j μ = c.opposite.target
        rw [← hμ]
        abel)
    refine ⟨-((toLevelUnits L 1 0 (meshSize L j) / ξ : ℝ) : ℂ), μ, c.opposite.source,
      fun U hU => ?_⟩
    have h := hfwd μ c.opposite.source U hU
    rw [e] at h
    have h' := (isBondForm_yangMillsCurrent hForm hL hm hj hξ hU).2 c
    rw [h] at h'
    rw [neg_smul, h', neg_neg]
end Transpose
theorem complexTransportCovariance_holds (hTw : TwistedTransportIsometryInvariance)
    (hAct : TwistedTransportOfFluctuations)
    (hEx : TransposeFormulas.ExplicitAdjointFormulas)
    (hForm : LieInnerProduct.Statement)
    (hCh : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hExp : Matrices.ComplexifiedAlgebra.ComplexifiedAlgebraExponential) :
    ComplexTransportCovariance := by
  intro L m i σ hL hm hi hσ j hj hij ℬ hℬ
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨-, h2, h3, -⟩ := hTw L m i σ hL hm hi hσ
  obtain ⟨-, -, hTwist, -⟩ := h3 j hj hij ℬ hℬ
  have hFL : LieInnerProduct.PeriodicLatticePairings := hForm.2.2.2.2.2.2.2
  obtain ⟨hfs, -⟩ : Finite (Site L m j) ∧ True := by
    obtain ⟨h₁, -⟩ := hFL L m j 1 hL hm hj one_pos
    exact ⟨h₁, trivial⟩
  letI : Fintype (Site L m j) := Fintype.ofFinite _
  haveI hfb : Finite (Bond L m j) :=
    Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' h =>
      Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  letI iB : Fintype (PositiveBondOf ℬ) := Fintype.ofFinite _
  obtain ⟨hbij, hpull⟩ :=
    bondImage_bijective_and_preimage ((hAct L m i σ hL hm hi hσ).2 j hij).2.1
  have hX := hExp.2.1
  have hCharts := hCh.2.2.2.1
  have himg : bondSetTransport σ (univ : Set (Bond L m j)) = univ := by
    unfold bondSetTransport
    exact image_univ_of_surjective hbij.2
  have hisom : ∀ U : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
      IsGaugeField complexGaugeGroup univ (transportGaugeField σ U) := by
    intro U hU
    have h := ((h2 j hij univ fun b _ => mem_univ _) U).2 hU
    rwa [himg] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V₀ hV A hA b hb
    exact (hTwist V₀ hV).transport_expTwist A hA (bondImage σ b) ⟨b, hb, rfl⟩
  · intro b _
    have hR := (hCharts (PositiveBondOf ℬ) (PositiveBondOf ℬ)).2.2
    have hG := (hCharts (PositiveBondOf ℬ) (PositiveBondOf ℬ)).2.1
    have hV := isAnalyticUnitFamily_gaugeFieldOfPoint ℬ (PositiveBondOf ℬ)
    have hA : ∀ c, AnalyticOnNhd ℂ (fun p : PositiveBondOf ℬ ⊕ PositiveBondOf ℬ → ComplexMatrix2 =>
        bondFormOfPositiveValues ℬ (algebraPartOfPoint p) c) (unitDetLocus _ _) :=
      analyticOnNhd_bondFormOfPositiveValues ℬ fun k => analyticOnNhd_eval (Sum.inr k)
    have hVm := fun {p} (hp : p ∈ GroupLieProduct (PositiveBondOf ℬ) (PositiveBondOf ℬ)) =>
      gaugeFieldOfPoint_mem ℬ hp
    have hAm : ∀ {p}, p ∈ GroupLieProduct (PositiveBondOf ℬ) (PositiveBondOf ℬ) →
        ∀ c, bondFormOfPositiveValues ℬ (algebraPartOfPoint p) c ∈ complexLieAlgebra :=
      fun hp => bondFormOfPositiveValues_mem ℬ fun k => hp (.inr k)
    refine ⟨iB, iB, fun β => ⟨isHolomorphicToUnimodular_of_analyticAt hR hG ?_ ?_ β,
      isHolomorphicToUnimodular_of_analyticAt hR hG ?_ ?_ β⟩⟩
    · exact (isAnalyticUnitFamily_expTwist hV hA _).1
    · exact fun p hp => expTwist_mem hX (hVm hp) (hAm hp) _
    · exact (isAnalyticUnitFamily_expTwist
        (V := fun p => transportGaugeField σ (gaugeFieldOfPoint ℬ p))
        (fun c => hV _) (analyticOnNhd_twistedTransportForm hV hA σ) _).1
    · exact fun p hp => expTwist_mem hX (fun c => hVm hp _)
        (twistedTransportForm_mem (hVm hp) (hAm hp) σ) _
  · intro ξ hξ V₀ hV A hA B hB
    exact (hTwist V₀ hV).inner_eq ξ hξ A hA B hB
  · intro ξ _
    have hR := (hCharts (PositiveBondOf ℬ) (PositiveBondOf ℬ ⊕ PositiveBondOf ℬ)).2.2
    have hV := isAnalyticUnitFamily_gaugeFieldOfPoint ℬ (PositiveBondOf ℬ ⊕ PositiveBondOf ℬ)
    have hA₁ : ∀ c, AnalyticOnNhd ℂ
        (fun p : PositiveBondOf ℬ ⊕ (PositiveBondOf ℬ ⊕ PositiveBondOf ℬ) → ComplexMatrix2 =>
          bondFormOfPositiveValues ℬ (firstAlgebraPart p) c) (unitDetLocus _ _) :=
      analyticOnNhd_bondFormOfPositiveValues ℬ fun k => analyticOnNhd_eval (Sum.inr (Sum.inl k))
    have hA₂ : ∀ c, AnalyticOnNhd ℂ
        (fun p : PositiveBondOf ℬ ⊕ (PositiveBondOf ℬ ⊕ PositiveBondOf ℬ) → ComplexMatrix2 =>
          bondFormOfPositiveValues ℬ (secondAlgebraPart p) c) (unitDetLocus _ _) :=
      analyticOnNhd_bondFormOfPositiveValues ℬ fun k => analyticOnNhd_eval (Sum.inr (Sum.inr k))
    exact ⟨iB, inferInstance, fun β =>
      ⟨scalar_isHolomorphicToCoords hR (analyticOnNhd_bondFormInner
        (analyticOnNhd_twistedTransportForm hV hA₁ σ)
        (analyticOnNhd_twistedTransportForm hV hA₂ σ) ξ) β,
       scalar_isHolomorphicToCoords hR (analyticOnNhd_bondFormInner hA₁ hA₂ ξ) β⟩⟩
  · intro ξ hξ V₀ hV b hq
    have ht := hTwist V₀ hV
    have hb' : bondImage σ b ∈ currentDomain (bondSetTransport σ ℬ) := by
      rw [ht.currentDomain_image]
      exact ⟨b, hq, rfl⟩
    rw [transportGaugeField_extendByOne hbij hpull]
    exact ht.current_transport ξ hξ _ hb'
  · intro ξ hξ b _
    have hR := (hCharts (PositiveBondOf ℬ) Empty).2.2
    have hV := isAnalyticUnitFamily_gaugeFieldOfPoint ℬ Empty
    have hVc : ∀ {p}, p ∈ GroupLieProduct (PositiveBondOf ℬ) Empty →
        IsGaugeField complexGaugeGroup univ (gaugeFieldOfPoint ℬ p) :=
      fun hp => isGaugeField_gaugeFieldOfPoint hL2 hj ℬ hp
    choose s μ x hcur using yangMillsCurrent_eq_smul_covDerivAdjointSum (ξ := ξ) hEx hFL hL hm hj hξ
    have hGL : ∀ c, AnalyticOnNhd ℂ (fun p : PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2 =>
        s c • TransposeFormulas.covDerivAdjointSum (toLevelUnits L 1 0 (meshSize L j))
          (gaugeFieldOfPoint ℬ p) (curvature ξ (gaugeFieldOfPoint ℬ p)) (μ c) (x c))
        (unitDetLocus _ _) :=
      fun c => analyticOnNhd_const_smul _ (analyticOnNhd_covDerivAdjointSum hV ξ _ _ _)
    have hGI : ∀ c, AnalyticOnNhd ℂ (fun p : PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2 =>
        s c • TransposeFormulas.covDerivAdjointSum (toLevelUnits L 1 0 (meshSize L j))
          (transportGaugeField σ (gaugeFieldOfPoint ℬ p))
          (curvature ξ (transportGaugeField σ (gaugeFieldOfPoint ℬ p))) (μ c) (x c))
        (unitDetLocus _ _) :=
      fun c => analyticOnNhd_const_smul _ (analyticOnNhd_covDerivAdjointSum
        (U := fun p => transportGaugeField σ (gaugeFieldOfPoint ℬ p))
        (fun c => hV _) ξ _ _ _)
    have hcm : ∀ {U : Bond L m j → ComplexMatrix2}, IsGaugeField complexGaugeGroup univ U →
        ∀ c, yangMillsCurrent ξ U c ∈ complexLieAlgebra :=
      fun hU c => mem_of_isBondForm hL2 hj (isBondForm_yangMillsCurrent hFL hL hm hj hξ hU) c
    refine ⟨iB, inferInstance, fun β => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · exact fun p hp => hcm (hisom _ (hVc hp)) _
    · exact isHolomorphicToCoords_congr
        (matrix_isHolomorphicToCoords hR (hGI (bondImage σ b)) β)
        fun p hp => hcur _ _ (hisom _ (hVc hp))
    · exact fun p hp => twistedTransportForm_mem (gaugeFieldOfPoint_mem ℬ hp) (hcm (hVc hp)) σ _
    · refine isHolomorphicToCoords_congr (matrix_isHolomorphicToCoords hR
        (analyticOnNhd_twistedTransportForm hV hGL σ (bondImage σ b)) β) fun p hp => ?_
      have e : yangMillsCurrent ξ (gaugeFieldOfPoint ℬ p) = fun c =>
          s c • TransposeFormulas.covDerivAdjointSum (toLevelUnits L 1 0 (meshSize L j))
            (gaugeFieldOfPoint ℬ p) (curvature ξ (gaugeFieldOfPoint ℬ p)) (μ c) (x c) :=
        funext fun c => hcur c _ (hVc hp)
      rw [e]
end PeriodicLattice.ComplexTransportCovarianceProof
end YangMills.Construction
