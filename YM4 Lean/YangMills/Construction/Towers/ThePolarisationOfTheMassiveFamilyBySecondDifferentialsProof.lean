import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Towers.ThePolarisationOfTheMassiveFamilyBySecondDifferentials
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.HessianBySecondDerivs
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (scalarSecondDeriv IsHolomorphicScalarIn asLine)
theorem deriv_ofReal_of_eventuallyEq {u : ℝ → ℝ} {w : ℝ → ℂ}
    (hw : ∀ᶠ t in 𝓝 (0 : ℝ), (u t : ℂ) = w t)
    (hdw : DifferentiableAt ℝ w 0) : deriv w 0 = ((deriv u 0 : ℝ) : ℂ) := by
  have heq : (fun t => (u t : ℂ)) =ᶠ[𝓝 0] w := hw
  have hre : HasDerivAt (fun t => (w t).re) (deriv w 0).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdw.hasDerivAt
  have hu : HasDerivAt u (deriv w 0).re 0 := by
    refine hre.congr_of_eventuallyEq (heq.mono fun t ht => ?_)
    have ht' : (u t : ℂ) = w t := ht
    show u t = (w t).re
    rw [← ht']
    simp
  rw [hu.deriv]
  exact (hu.ofReal_comp.congr_of_eventuallyEq heq.symm).deriv
theorem mixedDirectionalDeriv_eq_sub {ι : Type*} {k : ℕ}
    (hlog : Coordinates.ComplexCoordinates.LogDetSecondDeriv.Claim)
    {U₁ U₂ : Set (Coordinates.ComplexCoordinates k)} {g₁ g₂ : Coordinates.ComplexCoordinates k → ℂ}
    (hU₁ : IsOpen U₁) (h0₁ : 0 ∈ U₁) (hg₁ : IsHolomorphicScalarIn U₁ g₁)
    (hU₂ : IsOpen U₂) (h0₂ : 0 ∈ U₂) (hg₂ : IsHolomorphicScalarIn U₂ g₂)
    {F : (ι → Matrices.ComplexMatrix2) → ℝ} {A A' : ι → Matrices.ComplexMatrix2}
    {v w : Coordinates.ComplexCoordinates k}
    (hF : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
      ((F (algebraMap ℝ ℂ p.1 • A + algebraMap ℝ ℂ p.2 • A') : ℝ) : ℂ) =
        g₁ (p.1 • v + p.2 • w) - 1 / 2 * g₂ (p.1 • v + p.2 • w)) :
    ((mixedDirectionalDeriv ℝ F A A' : ℝ) : ℂ) =
      scalarSecondDeriv g₁ 0 v w - 1 / 2 * scalarSecondDeriv g₂ 0 v w := by
  obtain ⟨-, d₁, e₁⟩ := hlog.2 k U₁ g₁ hU₁ h0₁ hg₁ v w
  obtain ⟨-, d₂, e₂⟩ := hlog.2 k U₂ g₂ hU₂ h0₂ hg₂ v w
  have hcurry : ∀ᶠ s : ℝ in 𝓝 0, ∀ᶠ t : ℝ in 𝓝 0,
      ((F (algebraMap ℝ ℂ s • A + algebraMap ℝ ℂ t • A') : ℝ) : ℂ) =
        g₁ (s • v + t • w) - 1 / 2 * g₂ (s • v + t • w) :=
    Filter.Eventually.curry_nhds hF
  have houter : HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      g₁ (s • v + t • w) - 1 / 2 * g₂ (s • v + t • w)) 0)
      (scalarSecondDeriv g₁ 0 v w - 1 / 2 * scalarSecondDeriv g₂ 0 v w) 0 := by
    refine (e₁.sub (e₂.const_mul (1 / 2 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [d₁, d₂] with s hd₁ hd₂
    rw [deriv_fun_sub hd₁ (hd₂.const_mul _), deriv_const_mul _ hd₂]
    rfl
  have hinner : ∀ᶠ s : ℝ in 𝓝 0, deriv (fun t : ℝ =>
      g₁ (s • v + t • w) - 1 / 2 * g₂ (s • v + t • w)) 0 =
      ((deriv (fun t : ℝ => F (algebraMap ℝ ℂ s • A + algebraMap ℝ ℂ t • A')) 0 : ℝ) : ℂ) := by
    filter_upwards [hcurry, d₁, d₂] with s hs hd₁ hd₂
    exact deriv_ofReal_of_eventuallyEq hs (hd₁.sub (hd₂.const_mul _))
  have hreal : HasDerivAt (fun s : ℝ =>
      ((deriv (fun t : ℝ => F (algebraMap ℝ ℂ s • A + algebraMap ℝ ℂ t • A')) 0 : ℝ) : ℂ))
      (scalarSecondDeriv g₁ 0 v w - 1 / 2 * scalarSecondDeriv g₂ 0 v w) 0 :=
    houter.congr_of_eventuallyEq (hinner.mono fun _ h => h.symm)
  unfold mixedDirectionalDeriv
  rw [← hreal.deriv]
  exact (deriv_ofReal_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    hreal.differentiableAt).symm
theorem scalarSecondDeriv_re_add_im {k : ℕ}
    (hball : SeparatedFrame.HolomorphicDerivatives.Claim)
    {U : Set (Coordinates.ComplexCoordinates k)} {g : Coordinates.ComplexCoordinates k → ℂ}
    (h0 : 0 ∈ U) (hg : IsHolomorphicScalarIn U g) (v v' w w' : Coordinates.ComplexCoordinates k) :
    scalarSecondDeriv g 0 ((1 : ℂ) • v + Complex.I • v') ((1 : ℂ) • w + Complex.I • w') =
      (scalarSecondDeriv g 0 v w - scalarSecondDeriv g 0 v' w') +
        Complex.I * (scalarSecondDeriv g 0 v w' + scalarSecondDeriv g 0 v' w) := by
  obtain ⟨Φ, hΦ⟩ := ((hball k 1 U (asLine g) hg).2 0 h0).2.1
  have hform : ∀ a b, scalarSecondDeriv g 0 a b = Φ a b 0 := fun a b => by
    rw [hΦ]
    rfl
  simp only [hform, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (Φ v' w' 0) * hI
section QuotientEvaluation
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators.Tempered (realComponent imagComponent UnitEdge)
variable {L n : ℕ}
theorem projPositiveEdge_shiftEdge (hc : ProjCellsClassified L n 0 0) (b : PeriodicOperators.PosEdge L 0 0)
    (m : Fin 4 → ℤ) :
    projPositiveEdge L n 0 0 (shiftEdge ((2 * L ^ n) • m) b) =
      projPositiveEdge L n 0 0 b :=
  (((hc .edge).2 b (shiftEdge ((2 * L ^ n) • m) b)).2 ⟨m, rfl⟩).symm
theorem remainderQuotField_linComb (hc : ProjCellsClassified L n 0 0)
    {A A' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) (hA' : A' ∈ complexEdgeForms L n 0 0) (c d : ℂ)
    (x : (colourEdges L 0 0).QuotMod (2 * L ^ n)) :
    remainderQuotField (c • A + d • A') x =
      c * remainderQuotField A x + d * remainderQuotField A' x := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.remainderQuotField_add_smul <;> assumption
theorem realComponent_mem {A : UnitEdge L n → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) :
    realComponent A ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
theorem imagComponent_mem {A : UnitEdge L n → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) :
    imagComponent A ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
theorem mem_complexEdgeForms_of_mem {R : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) :
    R ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.DeltaSharedProofs.p8199 <;> assumption
theorem eq_realComponent_add_imagComponent (A : UnitEdge L n → Matrices.ComplexMatrix2) :
    A = (1 : ℂ) • realComponent A + Complex.I • imagComponent A := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.eq_realComponent_add_I_imagComponent <;> assumption
theorem finite_positiveEdge (hc : ProjCellsClassified L n 0 0) {k : ℕ}
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)) :
    Finite (Tower.PositiveEdge L n 0 0) := by
  have : Finite ((colourEdges L 0 0).QuotMod (2 * L ^ n)) := Finite.of_equiv _ e
  let f : (colourEdges L 0 0).QuotMod (2 * L ^ n) → Tower.PositiveEdge L n 0 0 :=
    Quot.lift (fun ι => projPositiveEdge L n 0 0 ι.2) (by
      rintro ι _ ⟨m, rfl⟩
      exact (projPositiveEdge_shiftEdge hc ι.2 m).symm)
  refine Finite.of_surjective f fun b => ?_
  obtain ⟨x, hx⟩ := (hc .edge).1 b
  exact ⟨Quot.mk _ ((0 : Fin 3), x), hx⟩
end QuotientEvaluation
section HessianInCoordinates
open LocalKernels.Periodisation
open PeriodicOperators.Tempered (realComponent imagComponent UnitEdge hessianAtIdentity complexHessian
  identityField)
open scoped Matrix.Norms.L2Operator
variable {L n k : ℕ}
abbrev edgeFormCoords (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    (A : Edge L n 0 0 → Matrices.ComplexMatrix2) : Coordinates.ComplexCoordinates k :=
  toCoords e (remainderQuotField A)
abbrev vertexLogDet (L : ℕ) (z : ℝ) {n k : ℕ}
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)) : Coordinates.ComplexCoordinates k → ℂ :=
  logDetInCoords (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L z) e
abbrev edgeLogDet (L : ℕ) (z : ℝ) {n k : ℕ}
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)) : Coordinates.ComplexCoordinates k → ℂ :=
  logDetInCoords (colourEdges L 0 0) (colourEdges L 0 0) (edgeOpFun L z) e
theorem ofCoords_real_linComb (hc : ProjCellsClassified L n 0 0)
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    {R R' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) (s t : ℝ) :
    ofCoords e (s • edgeFormCoords e R + t • edgeFormCoords e R') =
      remainderQuotField (algebraMap ℝ ℂ s • R + algebraMap ℝ ℂ t • R') := by
  funext c
  rw [remainderQuotField_linComb hc (mem_complexEdgeForms_of_mem hR)
    (mem_complexEdgeForms_of_mem hR')]
  simp [ofCoords, toCoords]
theorem edgeFormCoords_eq_parts (hc : ProjCellsClassified L n 0 0)
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    {A : UnitEdge L n → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) :
    edgeFormCoords e A =
      (1 : ℂ) • edgeFormCoords e (realComponent A) +
        Complex.I • edgeFormCoords e (imagComponent A) := by
  funext j
  have h := remainderQuotField_linComb hc (mem_complexEdgeForms_of_mem (realComponent_mem hA))
    (mem_complexEdgeForms_of_mem (imagComponent_mem hA)) 1 Complex.I (e j)
  rw [← eq_realComponent_add_imagComponent A] at h
  simpa [toCoords] using h
theorem eventually_norm_lt [Finite (Tower.PositiveEdge L n 0 0)]
    {R R' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ b : Edge L n 0 0,
      Matrices.ComplexMatrix2.operatorNorm ((algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R') b) < r := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.eventually_norm_lt <;> assumption
theorem real_linComb_mem {R R' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) (s t : ℝ) :
    algebraMap ℝ ℂ s • R + algebraMap ℝ ℂ t • R' ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.ofReal_smul_add_mem <;> assumption
theorem hessianAtIdentity_eq [Finite (Tower.PositiveEdge L n 0 0)]
    (hlog : Coordinates.ComplexCoordinates.LogDetSecondDeriv.Claim)
    (hc : ProjCellsClassified L n 0 0) {z r : ℝ} (hr : 0 < r)
    (hid : LogarithmsNearIdentity.IdentitiesBelow L n z r)
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    {U₁ U₂ : Set (Coordinates.ComplexCoordinates k)}
    (hU₁ : IsOpen U₁) (h0₁ : 0 ∈ U₁) (hg₁ : IsHolomorphicScalarIn U₁ (vertexLogDet L z e))
    (hU₂ : IsOpen U₂) (h0₂ : 0 ∈ U₂) (hg₂ : IsHolomorphicScalarIn U₂ (edgeLogDet L z e))
    {R R' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) :
    ((hessianAtIdentity (massiveFieldFamily L z) n R R' : ℝ) : ℂ) =
      scalarSecondDeriv (vertexLogDet L z e) 0 (edgeFormCoords e R) (edgeFormCoords e R') -
        1 / 2 * scalarSecondDeriv (edgeLogDet L z e) 0 (edgeFormCoords e R)
          (edgeFormCoords e R') := by
  unfold hessianAtIdentity leftSecondDeriv
  refine mixedDirectionalDeriv_eq_sub hlog hU₁ h0₁ hg₁ hU₂ h0₂ hg₂ ?_
  filter_upwards [eventually_norm_lt hR hR' hr] with p hp
  have h := (hid _ (real_linComb_mem hR hR' p.1 p.2) hp).2
  show ((massiveLogDetFunctional L n z _ : ℝ) : ℂ) = _
  rw [h]
  simp only [vertexLogDet, edgeLogDet, logDetInCoords,
    ofCoords_real_linComb hc e hR hR']
theorem complexHessian_eq [Finite (Tower.PositiveEdge L n 0 0)]
    (hlog : Coordinates.ComplexCoordinates.LogDetSecondDeriv.Claim)
    (hball : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hc : ProjCellsClassified L n 0 0) {z r : ℝ} (hr : 0 < r)
    (hid : LogarithmsNearIdentity.IdentitiesBelow L n z r)
    (e : Fin k ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n))
    {U₁ U₂ : Set (Coordinates.ComplexCoordinates k)}
    (hU₁ : IsOpen U₁) (h0₁ : 0 ∈ U₁) (hg₁ : IsHolomorphicScalarIn U₁ (vertexLogDet L z e))
    (hU₂ : IsOpen U₂) (h0₂ : 0 ∈ U₂) (hg₂ : IsHolomorphicScalarIn U₂ (edgeLogDet L z e))
    {A A' : Edge L n 0 0 → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) (hA' : A' ∈ complexEdgeForms L n 0 0) :
    complexHessian (massiveFieldFamily L z) n A A' =
      logDetSecondDeriv (colourEdges L 0 0) (colourVertices L 0 0)
          (vertexOpFun L z) e (remainderQuotField A) (remainderQuotField A') -
        1 / 2 * logDetSecondDeriv (colourEdges L 0 0) (colourEdges L 0 0)
          (edgeOpFun L z) e (remainderQuotField A) (remainderQuotField A') := by
  have r₁ := realComponent_mem hA
  have i₁ := imagComponent_mem hA
  have r₂ := realComponent_mem hA'
  have i₂ := imagComponent_mem hA'
  have hp := fun {R R' : Edge L n 0 0 → Matrices.ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
      (hR' : R' ∈ edgeFormSpace L n 0 0) =>
    hessianAtIdentity_eq hlog hc hr hid e hU₁ h0₁ hg₁ hU₂ h0₂ hg₂ hR hR'
  unfold complexHessian logDetSecondDeriv
  show _ = scalarSecondDeriv (vertexLogDet L z e) 0 (edgeFormCoords e A)
      (edgeFormCoords e A') -
    1 / 2 * scalarSecondDeriv (edgeLogDet L z e) 0 (edgeFormCoords e A)
      (edgeFormCoords e A')
  rw [edgeFormCoords_eq_parts hc e hA, edgeFormCoords_eq_parts hc e hA',
    scalarSecondDeriv_re_add_im hball h0₁ hg₁, scalarSecondDeriv_re_add_im hball h0₂ hg₂]
  push_cast
  rw [hp r₁ r₂, hp i₁ i₂, hp r₁ i₂, hp i₁ r₂]
  ring
end HessianInCoordinates
section LargeSides
open PeriodicOperators.Tempered (EventuallyForSides)
variable {L : ℕ}
theorem exists_forall_ge_of_eventuallyForSides (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) :
    ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → P n := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
theorem eventuallyForSides_of_forall_ge (hL : 2 ≤ L) {P : ℕ → Prop} {n₀ : ℕ}
    (h : ∀ n, n₀ ≤ n → P n) :
    EventuallyForSides L P := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.eventuallyForSides_of_forall_ge <;> assumption
end LargeSides
open PeriodicOperators.Tempered (EventuallyForSides)
theorem hessianIdentity_holds (h₁ : LogarithmsNearIdentity.Claim) (h₂ : Locality.OpFunsLocal)
    (h₃ : PeriodicOperators.LogDetSecondDerivs.Claim)
    (h₄ : Coordinates.ComplexCoordinates.LogDetSecondDeriv.Claim)
    (h₅ : SeparatedFrame.HolomorphicDerivatives.Claim)
    (h₆ : PeriodicOperators.TowerIndexSets.Claim)
    (h₇ : LocalKernels.PeriodicLiftCells.CellsAndClassesHold) : HessianIdentity := by
  classical
  intro L hL z hz
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨hS, hBd, -⟩ := h₆ L hL 0 0 le_rfl
  obtain ⟨loc₁, loc₂, -, -, un₁, un₂⟩ := (h₂ L hL z hz).1
  obtain ⟨δ₁, -, -, ⟨t₁, C₁, c₁, -, -, cl₁⟩, -⟩ := h₃ _ _ hBd hS _ loc₁ un₁
  obtain ⟨δ₂, -, -, ⟨t₂, C₂, c₂, -, -, cl₂⟩, -⟩ := h₃ _ _ hBd hBd _ loc₂ un₂
  obtain ⟨n₂, hn₂, hnear⟩ := exists_forall_ge_of_eventuallyForSides hL2 (h₁ L hL z hz)
  refine eventuallyForSides_of_forall_ge hL2 (n₀ := max n₂ (max t₁ t₂))
    fun n hn k e A hA A' hA' => ?_
  have g₂ : n₂ ≤ n := by omega
  have g₃ : t₁ ≤ n := by omega
  have g₄ : t₂ ≤ n := by omega
  have hn0 : 0 < n := by omega
  obtain ⟨hc, -⟩ := (h₇ L hL 0 n hn0).1 0 le_rfl
  obtain ⟨r, hr, hid⟩ := hnear n g₂
  have hs : n ≤ 2 * L ^ n := by
    have := Nat.lt_pow_self (n := n) (by omega : 1 < L)
    omega
  obtain ⟨⟨U₁, hU₁, h0₁, -, hg₁⟩, -⟩ := (cl₁ (2 * L ^ n) (by omega)).2 k e
  obtain ⟨⟨U₂, hU₂, h0₂, -, hg₂⟩, -⟩ := (cl₂ (2 * L ^ n) (by omega)).2 k e
  have := finite_positiveEdge hc e
  exact complexHessian_eq h₄ h₅ hc hr hid e hU₁ h0₁ hg₁ hU₂ h0₂ hg₂ hA hA'
end YangMills.Construction.Tower.MassiveOpFunctions.HessianBySecondDerivs
end
