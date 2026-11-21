import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Matrices.ProductAnalyticInMatrices
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.EntriesOfTheActionAndOfTheCovariantDifferenceProof
import YangMills.Construction.Towers.TheEntriesOfTheAveragesAtElementaryFunctions
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ElementaryEntries
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Coordinates
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.LocalKernels (FieldIdx FieldComponent)
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions (backgroundCoords)
section PauliCoefficients
def pauliEntryCoeff (a : Fin 3) (X : ComplexMatrix2) : ℂ :=
  ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
theorem pauliCoeff_eq_pauliEntryCoeff (a : Fin 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a X = pauliEntryCoeff a X := by
  rw [pauliCoeff, dif_pos hX]
  rfl
theorem differentiable_pauliEntryCoeff (a : Fin 3) : Differentiable ℂ (pauliEntryCoeff a) := by
  have he : ∀ i j : Fin 2, Differentiable ℂ (fun X : ComplexMatrix2 => X i j) := fun i j =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable
  fin_cases a
  · change Differentiable ℂ (fun X : ComplexMatrix2 => (X 0 1 + X 1 0) / 2)
    simp only [div_eq_mul_inv]
    exact ((he 0 1).fun_add (he 1 0)).mul_const _
  · change Differentiable ℂ (fun X : ComplexMatrix2 => (X 1 0 - X 0 1) / (2 * Complex.I))
    simp only [div_eq_mul_inv]
    exact ((he 1 0).fun_sub (he 0 1)).mul_const _
  · exact he 0 0
end PauliCoefficients
section FiniteIndexSets
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ}
theorem fieldExtend_apply (e : Fin l ≃ S) (z : ComplexCoordinates l) (j : Fin l) :
    fieldExtend e z ((e j : S) : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem fieldExtend_isSupBelow (e : Fin l ≃ S) {z : ComplexCoordinates l} {r ρ : ℝ} (hr : 0 ≤ r)
    (hρ : r < ρ) (hz : ∀ j, ‖z j‖ ≤ r) : IsSupBelow F (fieldExtend e z) ρ := by
  refine ⟨r, hρ, fun κ => ?_⟩
  by_cases h : ∃ j, ((e j : S) : F.Carrier) = κ
  · obtain ⟨j, rfl⟩ := h
    rw [fieldExtend_apply]
    exact hz j
  · have h' : fieldExtend e z κ = 0 := Function.extend_apply' _ _ _ h
    rw [h']
    simpa using hr
theorem fieldExtend_isSupBelow_of_lt (e : Fin l ≃ S) {z : ComplexCoordinates l} {ρ : ℝ}
    (hρ : 0 < ρ) (hz : ∀ j, ‖z j‖ < ρ) : IsSupBelow F (fieldExtend e z) ρ :=
  fieldExtend_isSupBelow e (norm_nonneg z) ((pi_norm_lt_iff hρ).2 hz) fun j => norm_le_pi_norm z j
theorem isOpen_coordPolydisc (ρ : ℝ) : IsOpen {z : ComplexCoordinates l | ∀ j, ‖z j‖ < ρ} := by
  have h : {z : ComplexCoordinates l | ∀ j, ‖z j‖ < ρ} = ⋂ j, {z | ‖z j‖ < ρ} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
theorem holomorphicInValuesBelow_of_contDiffAt {ρ : ℝ} (hρ : 0 < ρ) (hS : S.Finite)
    {X : (F.Carrier → ℂ) → ComplexMatrix2} (a : Fin 3)
    (hmem : ∀ ζ, IsSupBelow F ζ ρ → X ζ ∈ ComplexMatrix2.traceless)
    (hdep : ∀ ζ ζ', IsSupBelow F ζ ρ → IsSupBelow F ζ' ρ → (∀ κ ∈ S, ζ κ = ζ' κ) → X ζ = X ζ')
    (hsm : ∀ (l : ℕ) (e : Fin l ≃ S) (z : ComplexCoordinates l), (∀ j, ‖z j‖ < ρ) →
      ContDiffAt ℂ ∞ (fun z : ComplexCoordinates l => X (fieldExtend e z)) z) :
    HolomorphicInValuesBelow F ρ S fun ζ => pauliCoeff a (X ζ) := by
  have := hS.to_subtype
  let e : Fin (Nat.card S) ≃ S := (Finite.equivFin S).symm
  let h : ComplexCoordinates (Nat.card S) → ℂ := fun z => pauliEntryCoeff a (X (fieldExtend e z))
  have hO : ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
      (0 : ComplexCoordinates (Nat.card S)) ρ = {z | ∀ j, ‖z j‖ < ρ} := by
    ext z
    show (∀ j, ‖z j - (0 : ComplexCoordinates (Nat.card S)) j‖ < ρ) ↔ ∀ j, ‖z j‖ < ρ
    exact forall_congr' fun j => by
      rw [show (0 : ComplexCoordinates (Nat.card S)) j = 0 from rfl, sub_zero]
  have hd : ∀ z : ComplexCoordinates (Nat.card S), (∀ j, ‖z j‖ < ρ) → DifferentiableAt ℂ h z :=
    fun z hz => (differentiable_pauliEntryCoeff a _).comp z
      ((hsm _ e z hz).differentiableAt (by simp))
  refine ⟨Nat.card S, e, h, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hO]
    exact isOpen_coordPolydisc ρ
  · intro z hz
    rw [hO] at hz
    exact (continuousAt_pi.2 fun _ => (hd z hz).continuousAt).continuousWithinAt
  · intro z hz j
    rw [hO] at hz
    have hline : ∀ ζ : ℂ, DifferentiableAt ℂ
        (fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector j) ζ := fun ζ =>
      (differentiableAt_const _).add (differentiableAt_id.smul_const _)
    have hc : Tendsto (fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector j) (𝓝 0) (𝓝 z) := by
      have h0 : z + (0 : ℂ) • ComplexCoordinates.stdBasisVector j = z := by
        rw [zero_smul, add_zero]
      have := (hline 0).continuousAt.tendsto
      rwa [h0] at this
    filter_upwards [hc.eventually ((isOpen_coordPolydisc ρ).mem_nhds hz)] with ζ hζ
    have hcomp : DifferentiableAt ℂ
        (fun ζ : ℂ => h (z + ζ • ComplexCoordinates.stdBasisVector j)) ζ :=
      DifferentiableAt.comp (g := h) ζ (hd _ hζ) (hline ζ)
    exact differentiableAt_pi.2 fun _ => hcomp
  · intro ζ hζ
    obtain ⟨r, hr, hb⟩ := hζ
    have hb' : IsSupBelow F (fieldExtend e (fieldValues e ζ)) ρ :=
      fieldExtend_isSupBelow e (r := max r 0) (le_max_right _ _) (max_lt hr hρ)
        fun j => (hb _).trans (le_max_left _ _)
    have hag : X ζ = X (fieldExtend e (fieldValues e ζ)) := by
      refine hdep _ _ ⟨r, hr, hb⟩ hb' fun κ hκ => ?_
      obtain ⟨j, hj⟩ := e.surjective ⟨κ, hκ⟩
      have hk : κ = ((e j : S) : F.Carrier) := by rw [hj]
      rw [hk, fieldExtend_apply]
      rfl
    show pauliCoeff a (X ζ) = pauliEntryCoeff a (X (fieldExtend e (fieldValues e ζ)))
    rw [hag, pauliCoeff_eq_pauliEntryCoeff a (hmem _ hb')]
end FiniteIndexSets
section ParameterDerivatives
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y]
theorem contDiffAt_deriv_snd {H : E × ℂ → Y} {x : E} (hH : ContDiffAt ℂ ∞ H (x, 0)) :
    ContDiffAt ℂ ∞ (fun y : E => deriv (fun t : ℂ => H (y, t)) 0) x := by
  have h1 : ContDiffAt ℂ ∞ (fderiv ℂ H) (x, 0) := hH.fderiv_right (m := ∞) (by simp)
  have hin : ContDiffAt ℂ ∞ (fun y : E => (y, (0 : ℂ))) x := contDiffAt_id.prodMk contDiffAt_const
  have h2 : ContDiffAt ℂ ∞ (fun y : E => fderiv ℂ H (y, 0) ((0 : E), (1 : ℂ))) x :=
    (ContDiffAt.comp x h1 hin).clm_apply contDiffAt_const
  refine h2.congr_of_eventuallyEq ?_
  have hH1 : ContDiffAt ℂ 1 H (x, 0) := hH.of_le (by simp)
  have hev : ∀ᶠ p in 𝓝 (x, (0 : ℂ)), DifferentiableAt ℂ H p := by
    filter_upwards [hH1.eventually (by simp)] with p hp
    exact hp.differentiableAt (by simp)
  have hc : Tendsto (fun y : E => (y, (0 : ℂ))) (𝓝 x) (𝓝 (x, 0)) := hin.continuousAt.tendsto
  filter_upwards [hc.eventually hev] with y hy
  have hcurve : HasDerivAt (fun t : ℂ => (y, t)) ((0 : E), (1 : ℂ)) 0 :=
    (hasDerivAt_const (0 : ℂ) y).prodMk (hasDerivAt_id (0 : ℂ))
  exact (hy.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hcurve).deriv
theorem contDiff_matExp : ContDiff ℂ ∞ (fun Z : ComplexMatrix2 => ComplexMatrix2.matExp Z) :=
  contDiff_iff_contDiffAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℂ) Z).contDiffAt
theorem contDiffAt_matrix_inv {A : E → ComplexMatrix2} {x : E} (hA : ContDiffAt ℂ ∞ A x)
    (hx : (A x).det = 1) : ContDiffAt ℂ ∞ (fun y => (A y)⁻¹) x := by
  have hu : IsUnit (A x) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hx]; exact isUnit_one)
  obtain ⟨u, hu⟩ := hu
  have h := contDiffAt_ringInverse ℂ (n := ∞) u
  rw [hu] at h
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact ContDiffAt.comp x h hA
omit [NormedSpace ℂ E] in
theorem eventually_mem_of_isRelativelyOpen {T : Type} [TopologicalSpace T] {P O : Set T}
    (h : ComplexMatrix2.IsRelativelyOpen P O) {γ : E → T} {x : E} (hc : ContinuousAt γ x)
    (hx : γ x ∈ O) (hP : ∀ᶠ y in 𝓝 x, γ y ∈ P) : ∀ᶠ y in 𝓝 x, γ y ∈ O := by
  obtain ⟨O', hO', rfl⟩ := h
  filter_upwards [hc.tendsto.eventually (hO'.mem_nhds hx.1), hP] with y h₁ h₂
  exact ⟨h₁, h₂⟩
end ParameterDerivatives
section UnimodularMaps
variable {τ : Type} [Fintype τ]
structure UnimodularRepresentation (𝔇 : Set (τ → ComplexMatrix2))
    (Φ : (τ → ComplexMatrix2) → ComplexMatrix2) : Prop where
  exists_lift : ∃ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (τ ⊕ Empty → ComplexMatrix2)) (Ψ : (τ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicToUnimodular b W Ψ ∧
      (∀ v, Ψ (Sum.elim v Empty.elim) = Φ v) ∧ ∀ v ∈ 𝔇, Sum.elim v Empty.elim ∈ W
theorem UnimodularRepresentation.det_eq_one {𝔇 : Set (τ → ComplexMatrix2)}
    {Φ : (τ → ComplexMatrix2) → ComplexMatrix2} (h : UnimodularRepresentation 𝔇 Φ)
    {v : τ → ComplexMatrix2} (hv : v ∈ 𝔇) : (Φ v).det = 1 := by
  obtain ⟨b, W, Ψ, hΨ, he, hW⟩ := h.exists_lift
  have := hΨ.2.1 (hW v hv)
  rw [he] at this
  exact this
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem UnimodularRepresentation.contDiffAt_comp (hAn : HolomorphicMatrixAnalyticity)
    {𝔇 : Set (τ → ComplexMatrix2)} {Φ : (τ → ComplexMatrix2) → ComplexMatrix2}
    (h : UnimodularRepresentation 𝔇 Φ) {g : E → τ → ComplexMatrix2} {x : E}
    (hg : ∀ s, ContDiffAt ℂ ∞ (fun y => g y s) x) (hx : g x ∈ 𝔇)
    (hgrp : ∀ᶠ y in 𝓝 x, g y ∈ unimodularPi τ) : ContDiffAt ℂ ∞ (fun y => Φ (g y)) x := by
  obtain ⟨b, W, Ψ, hΨ, he, hW⟩ := h.exists_lift
  have hp := hW _ hx
  obtain ⟨F, hF, hev⟩ := hAn τ Empty b W Ψ (Or.inr hΨ) _ hp
  have hg' : ContDiffAt ℂ ∞
      (fun y => (Sum.elim (g y) Empty.elim : τ ⊕ Empty → ComplexMatrix2)) x :=
    contDiffAt_pi.2 fun i => by
      rcases i with s | e
      · exact hg s
      · exact e.elim
  have hmem : ∀ᶠ y in 𝓝 x, (Sum.elim (g y) Empty.elim : τ ⊕ Empty → ComplexMatrix2) ∈
      GroupLieProduct τ Empty := by
    filter_upwards [hgrp] with y hy
    intro i
    rcases i with s | e
    · exact hy s
    · exact e.elim
  have hW' := eventually_mem_of_isRelativelyOpen hΨ.1 hg'.continuousAt hp hmem
  have hc : Tendsto (fun y => (Sum.elim (g y) Empty.elim : τ ⊕ Empty → ComplexMatrix2)) (𝓝 x)
      (𝓝 (Sum.elim (g x) Empty.elim)) := hg'.continuousAt.tendsto
  refine (ContDiffAt.comp x (hF.contDiffAt (n := ∞)) hg').congr_of_eventuallyEq ?_
  filter_upwards [hc.eventually hev, hW'] with y h₁ h₂
  simp only [Function.comp_apply]
  rw [← h₁ h₂, he]
theorem contDiffAt_log_mul_inv (hAn : HolomorphicMatrixAnalyticity)
    (hlog : PeriodicLattice.LogSeriesNearOne)
    {𝔇 : Set (τ → ComplexMatrix2)} {Φ : (τ → ComplexMatrix2) → ComplexMatrix2}
    (h : UnimodularRepresentation 𝔇 Φ) {g₀ g₁ : E → τ → ComplexMatrix2} {x : E}
    (hg₀ : ∀ s, ContDiffAt ℂ ∞ (fun y => g₀ y s) x) (hg₁ : ∀ s, ContDiffAt ℂ ∞ (fun y => g₁ y s) x)
    (hx : g₀ x ∈ 𝔇) (hagree : g₁ x = g₀ x)
    (hgrp₀ : ∀ᶠ y in 𝓝 x, g₀ y ∈ unimodularPi τ) (hgrp₁ : ∀ᶠ y in 𝓝 x, g₁ y ∈ unimodularPi τ) :
    ContDiffAt ℂ ∞ (fun y => ComplexMatrix2.logSeries (Φ (g₁ y) * (Φ (g₀ y))⁻¹)) x := by
  have hA := h.contDiffAt_comp hAn hg₁ (hagree ▸ hx) hgrp₁
  have hB := h.contDiffAt_comp hAn hg₀ hx hgrp₀
  have hdet := h.det_eq_one hx
  have hq := hA.mul (contDiffAt_matrix_inv hB hdet)
  have hone : Φ (g₁ x) * (Φ (g₀ x))⁻¹ = 1 := by
    rw [hagree]
    exact Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
  have hdom : Φ (g₁ x) * (Φ (g₀ x))⁻¹ ∈ ComplexMatrix2.logBall := by
    rw [hone]
    simp [ComplexMatrix2.logBall, ComplexMatrix2.operatorNorm]
  exact ContDiffAt.comp (g := ComplexMatrix2.logSeries) x ((hlog.1 _ hdom).contDiffAt (n := ∞)) hq
end UnimodularMaps
section Links
variable {a : ℝ}
theorem matExp_mul_mem_unitDeterminant (hEL : ComplexMatrix2.ExpLogEstimates) {X g : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    ComplexMatrix2.matExp (Complex.I • X) * g ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.AsDifferentials.expChart_mem_unitDeterminant <;> assumption
theorem expTwist_isFieldIn (hEL : ComplexMatrix2.ExpLogEstimates) (ha : 0 < a)
    {U C : InfiniteLattice.Link a → ComplexMatrix2} (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U)
    (hC : C ∈ complexEdgeForms a) : IsFieldIn PeriodicLattice.complexGaugeGroup (expTwist C U) := by apply _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.expTwist_mem <;> assumption
theorem conjugateBy_mem_traceless {X A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy X A ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
end Links
section TowerFacts
variable {L k : ℕ}
open YangMills.Construction.Tower.SupportOfMeans (definedLocus RepresentsMean IsHolomorphicOnProduct
  HolomorphicInRestriction)
open YangMills.Construction.Tower.SupportOfMeans.Unbounded (supportEdges baseFields meanAt)
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (levelwiseMean)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (iterMean iterRatio
  topLogRatio topDeriv complexQuadraticTerm)
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule quadraticTerm quadraticTermAt
  HasDerivAtZeroAlong)
structure Hypotheses (L k : ℕ) : Prop where
  analytic : HolomorphicMatrixAnalyticity
  expLog : ComplexMatrix2.ExpLogEstimates
  logSeries : PeriodicLattice.LogSeriesNearOne
  support : SupportOfMeans.Unbounded.SideRequirements L k
  derivs : AsDifferentials.Requirements L k
  stable : MeanStableFields.Infinite.MeanStableConditions L k
  iterated : IteratedMeans.Unbounded.SpaceConditions L k
  mesh_pos : ∀ i, 0 < meshAt L k i
  doubleBlock : ∀ j < k, ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    DoubleBlockPolydisc.Infinite.PolydiscPropertiesAt L k j (polydiscRadius L) c
  contour_eq : ∀ j < k, ∀ y : Vertex L k (j + 1),
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
    ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))) →
    ∀ V' : Edge L k j → ComplexMatrix2, V' ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      ComplexMatrix2.operatorNorm (V' b - 1) < polydiscRadius L) →
    ∀ W : Edge L k j → ComplexMatrix2,
    (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W b = V' b) →
    complexContourMean L W y x = complexContourMean L V' y x
  cube_finite : ∀ j < k, ∀ y : Vertex L k (j + 1),
    (cubeVertices L (meshAt L k j) y).Finite
def meanFamily (U : Edge L k 0 → ComplexMatrix2) : ∀ i : ℕ, Edge L k i → ComplexMatrix2 :=
  fun i => complexIter L k i U
theorem isMeanSequenceFrom_of_small (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) :
    MeanStableFields.Infinite.IsMeanSequenceFrom k U (meanFamily U) := by
  refine ⟨⟨fun i hi => ?_, fun i hi b => (hU.2 i hi).2 b, fun i hi c hc => rfl⟩, rfl⟩
  cases i with
  | zero => exact hU.1
  | succ i => exact s.iterated.meanStep_mem i (by omega) _ (hU.2 i (by omega))
theorem levelwiseMean_of_small (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k)
    (c : Edge L k i) : levelwiseMean U i c = some (complexIter L k i U c) :=
  s.stable.eq_levelwiseMean k le_rfl U _ (isMeanSequenceFrom_of_small s hU) i hi c
theorem valuesOrOne_of_small (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k) :
    valuesOrOne (levelwiseMean U i) = complexIter L k i U := by
  funext c
  simp [valuesOrOne, levelwiseMean_of_small s hU hi c]
abbrev locus {u : ℕ} (c : Edge L k u) (F : Finset (Edge L k 0)) : Set (F → ComplexMatrix2) :=
  definedLocus (baseFields L k) F (meanAt c)
def twistTuple {F : Finset (Edge L k 0)} (C : Edge L k 0 → ComplexMatrix2) (w : F → ComplexMatrix2) :
    F → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • C b) * w b
theorem twistTuple_zero {F : Finset (Edge L k 0)} {C : Edge L k 0 → ComplexMatrix2}
    (w : F → ComplexMatrix2) (hC : ∀ b : F, C b = 0) : twistTuple C w = w := by
  funext b
  simp [twistTuple, hC b, ComplexMatrix2.matExp]
theorem twistTuple_mem (s : Hypotheses L k) {F : Finset (Edge L k 0)}
    {C : Edge L k 0 → ComplexMatrix2} {w : F → ComplexMatrix2} (hw : w ∈ unimodularPi F)
    (hC : ∀ b : F, C b ∈ ComplexMatrix2.traceless) : twistTuple C w ∈ unimodularPi F :=
  fun b => matExp_mul_mem_unitDeterminant s.expLog (hC b) (hw b)
theorem restrict_mem_unimodularPi {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ baseFields L k) (F : Finset (Edge L k 0)) :
    (fun b : F => U b) ∈ unimodularPi F :=
  fun b => hU.1 b
theorem restrict_expTwist {F : Finset (Edge L k 0)} (hpos : ∀ b ∈ F, b.IsPositivelyOriented)
    (U C : Edge L k 0 → ComplexMatrix2) :
    (fun b : F => expTwist C U b) = twistTuple C fun b : F => U b := by
  funext b
  exact if_pos (hpos b b.2)
theorem isPositivelyOriented_of_mem {u : ℕ} {c : Edge L k u} {F : Finset (Edge L k 0)}
    (hF : (F : Set (Edge L k 0)) = supportEdges c) : ∀ b ∈ F, b.IsPositivelyOriented := by
  intro b hb
  have : b ∈ (F : Set (Edge L k 0)) := hb
  rw [hF] at this
  exact this.1
theorem mem_locus_and_eq_of_small (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {u : ℕ} (hu : u ≤ k) (c : Edge L k u)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : RepresentsMean (baseFields L k) F (meanAt c) (locus c F) Φ) :
    (fun b : F => U b) ∈ locus c F ∧ Φ (fun b : F => U b) = complexIter L k u U c := by
  have r := s.support.dependsOnlyOn u hu c F hF
  have hl := levelwiseMean_of_small s hU hu c
  have hin : (fun b : F => U b) ∈ locus c F :=
    (r.isSome_iff U hU.1).1 (by
      show (levelwiseMean U u c).isSome
      rw [hl]
      rfl)
  refine ⟨hin, ?_⟩
  have hv := hΦ.eq_some U hU.1 hin
  have hv' : levelwiseMean U u c = some (Φ fun b : F => U b) := hv
  rw [hl] at hv'
  exact (Option.some.inj hv').symm
theorem iterMean_expTwist (s : Hypotheses L k) {U C : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ baseFields L k) (hC : C ∈ complexEdgeForms (meshAt L k 0)) {u : ℕ}
    (c : Edge L k u)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : RepresentsMean (baseFields L k) F (meanAt c) (locus c F) Φ)
    (hm : twistTuple C (fun b : F => U b) ∈ locus c F) :
    iterMean (expTwist C U) u c = Φ (twistTuple C fun b : F => U b) := by
  have hW : expTwist C U ∈ baseFields L k := expTwist_isFieldIn s.expLog (s.mesh_pos 0) hU hC
  have e := restrict_expTwist (isPositivelyOriented_of_mem hF) U C
  rw [← e] at hm ⊢
  have hv : levelwiseMean (expTwist C U) u c = some (Φ fun b : F => expTwist C U b) :=
    hΦ.eq_some _ hW hm
  simp [iterMean, valuesOrOne, hv]
theorem iterLogRatio_eventually_eq (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {u : ℕ} (hu : u ≤ k) (c : Edge L k u)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : RepresentsMean (baseFields L k) F (meanAt c) (locus c F) Φ)
    {B B' : Edge L k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k 0))
    (hB' : B' ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), AsDifferentials.iterLogRatio U u c (p.1 • B + p.2 • B') =
      Complex.I⁻¹ • ComplexMatrix2.logSeries (Φ (twistTuple (p.1 • B + p.2 • B') fun b : F => U b) *
        (Φ fun b : F => U b)⁻¹) := by
  have hpos := isPositivelyOriented_of_mem hF
  have r := s.support.dependsOnlyOn u hu c F hF
  obtain ⟨hin, hval⟩ := mem_locus_and_eq_of_small s hU hu c hF hΦ
  have hform : ∀ p : ℂ × ℂ, p.1 • B + p.2 • B' ∈ complexEdgeForms (meshAt L k 0) := fun p =>
    (complexEdgeForms _).add_mem ((complexEdgeForms _).smul_mem _ hB)
      ((complexEdgeForms _).smul_mem _ hB')
  have hsl : ∀ (p : ℂ × ℂ) (b : F), (p.1 • B + p.2 • B') b ∈ ComplexMatrix2.traceless :=
    fun p b => (hform p).1 b.1 (hpos b b.2)
  have hcont : ContinuousAt (fun p : ℂ × ℂ => twistTuple (p.1 • B + p.2 • B') fun b : F => U b)
      ((0 : ℂ), (0 : ℂ)) := by
    refine continuousAt_pi.2 fun b => ?_
    have h1 : Continuous (fun p : ℂ × ℂ => Complex.I • (p.1 • B b.1 + p.2 • B' b.1)) := by
      fun_prop
    exact (((contDiff_matExp.continuous.comp h1).mul continuous_const)).continuousAt
  have hat : twistTuple ((0 : ℂ) • B + (0 : ℂ) • B') (fun b : F => U b) = fun b : F => U b :=
    twistTuple_zero _ fun b => by simp
  have hev := eventually_mem_of_isRelativelyOpen r.isOpen hcont (by simpa only [hat] using hin)
    (Eventually.of_forall fun p =>
      twistTuple_mem s (restrict_mem_unimodularPi hU.1 F) (hsl p))
  filter_upwards [hev] with p hp
  have hv := iterMean_expTwist s hU.1 (hform p) c hF hΦ hp
  have h0 : iterMean U u c = Φ fun b : F => U b := by
    rw [hval]
    simp [iterMean, valuesOrOne, levelwiseMean_of_small s hU hu c]
  simp only [AsDifferentials.iterLogRatio, iterRatio, hv, h0]
def firstDeriv {F : Finset (Edge L k 0)} (Φ : (F → ComplexMatrix2) → ComplexMatrix2)
    (B : Edge L k 0 → ComplexMatrix2) (w : F → ComplexMatrix2) : ComplexMatrix2 :=
  deriv (fun t : ℂ => Complex.I⁻¹ • ComplexMatrix2.logSeries (Φ (twistTuple (t • B) w) * (Φ w)⁻¹)) 0
def secondDeriv {F : Finset (Edge L k 0)} (Φ : (F → ComplexMatrix2) → ComplexMatrix2)
    (B B' : Edge L k 0 → ComplexMatrix2) (w : F → ComplexMatrix2) : ComplexMatrix2 :=
  deriv (fun s : ℂ => deriv (fun t : ℂ =>
    Complex.I⁻¹ • ComplexMatrix2.logSeries (Φ (twistTuple (s • B + t • B') w) * (Φ w)⁻¹)) 0) 0
theorem complexIterDeriv_eq_firstDeriv (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i < k) {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : RepresentsMean (baseFields L k) F (meanAt c) (locus c F) Φ)
    {B : Edge L k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    complexIterDeriv L k (i + 1) U B c = firstDeriv Φ B fun b : F => U b := by
  have hs := s.derivs.1 i hi _ (hU.2 i hi) U hU
  have hd : HasDerivAt (fun t : ℂ => AsDifferentials.iterLogRatio U (i + 1) c (t • B))
      (complexIterDeriv L k (i + 1) U B c) 0 := hs.deriv_iter c hc B hB
  have hev := iterLogRatio_eventually_eq s hU (Nat.succ_le_of_lt hi) c hF hΦ hB hB
  have ht : Tendsto (fun t : ℂ => ((0 : ℂ), t)) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (Continuous.prodMk continuous_const continuous_id).continuousAt.tendsto
  have heq : (fun t : ℂ => AsDifferentials.iterLogRatio U (i + 1) c (t • B)) =ᶠ[𝓝 0]
      fun t : ℂ => Complex.I⁻¹ • ComplexMatrix2.logSeries (Φ (twistTuple (t • B) fun b : F => U b) *
        (Φ fun b : F => U b)⁻¹) := by
    filter_upwards [ht.eventually hev] with t h
    simpa using h
  rw [← hd.deriv, heq.deriv_eq]
  rfl
theorem complexQuadraticTerm_eq_secondDeriv (s : Hypotheses L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) (c : PositiveEdge (meshAt L k k))
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c.1)
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : RepresentsMean (baseFields L k) F (meanAt c.1) (locus c.1 F) Φ)
    {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)))
    (hB' : B' ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0))) :
    complexQuadraticTerm L k U B B' c = secondDeriv Φ B B' (fun b : F => U b) ∧
      complexQuadraticTerm L k U B B' c ∈ ComplexMatrix2.traceless := by
  have hterm := (s.derivs.2 U hU).2.2 ⟨B, hB⟩ ⟨B', hB'⟩ c
  have e : complexQuadraticTerm L k U B B' c =
      quadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
        (topDeriv L k U) ⟨B, hB⟩ ⟨B', hB'⟩ c := by
    simp only [complexQuadraticTerm, quadraticTermAt]
    rw [dif_pos (⟨hB, hB'⟩ : _ ∧ _)]
  refine ⟨?_, e ▸ hterm.2⟩
  rw [e, ← hterm.1]
  have hev := iterLogRatio_eventually_eq s hU le_rfl c.1 hF hΦ hB.1 hB'.1
  simp only [mixedDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  have heq : (fun σ : ℂ => deriv (fun t : ℂ => topLogRatio L k U c (σ • B + t • B')) 0) =ᶠ[𝓝 0]
      fun σ : ℂ => deriv (fun t : ℂ => Complex.I⁻¹ • ComplexMatrix2.logSeries
        (Φ (twistTuple (σ • B + t • B') fun b : F => U b) * (Φ fun b : F => U b)⁻¹)) 0 := by
    filter_upwards [hev.curry_nhds] with σ hσ
    exact Filter.EventuallyEq.deriv_eq hσ
  rw [heq.deriv_eq]
  rfl
section SmoothDerivs
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup P]
  [NormedSpace ℂ P]
theorem contDiffAt_twistTuple {F : Finset (Edge L k 0)} {C : P → Edge L k 0 → ComplexMatrix2}
    {T : P → F → ComplexMatrix2} {x : P} (hC : ∀ b : F, ContDiffAt ℂ ∞ (fun p => C p b) x)
    (hT : ∀ b, ContDiffAt ℂ ∞ (fun p => T p b) x) (b : F) :
    ContDiffAt ℂ ∞ (fun p => twistTuple (C p) (T p) b) x :=
  (ContDiffAt.comp x contDiff_matExp.contDiffAt ((hC b).const_smul Complex.I)).mul (hT b)
theorem contDiffAt_firstDeriv (s : Hypotheses L k) {F : Finset (Edge L k 0)}
    (hpos : ∀ b ∈ F, b.IsPositivelyOriented) {𝔇 : Set (F → ComplexMatrix2)}
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : UnimodularRepresentation 𝔇 Φ) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) {T : E → F → ComplexMatrix2} {x : E}
    (hT : ∀ b, ContDiffAt ℂ ∞ (fun z => T z b) x) (hx : T x ∈ 𝔇)
    (hgrp : ∀ᶠ z in 𝓝 x, T z ∈ unimodularPi F) :
    ContDiffAt ℂ ∞ (fun z => firstDeriv Φ B (T z)) x := by
  have hfst : Tendsto (fun p : E × ℂ => p.1) (𝓝 (x, 0)) (𝓝 x) := continuousAt_fst.tendsto
  have hT' : ∀ b, ContDiffAt ℂ ∞ (fun p : E × ℂ => T p.1 b) (x, 0) := fun b =>
    ContDiffAt.comp (x, (0 : ℂ)) (hT b) contDiffAt_fst
  have hH : ContDiffAt ℂ ∞ (fun p : E × ℂ => Complex.I⁻¹ • ComplexMatrix2.logSeries
      (Φ (twistTuple (p.2 • B) (T p.1)) * (Φ (T p.1))⁻¹)) (x, 0) := by
    refine ContDiffAt.const_smul _ (contDiffAt_log_mul_inv s.analytic s.logSeries hΦ
      (g₀ := fun p : E × ℂ => T p.1) (g₁ := fun p : E × ℂ => twistTuple (p.2 • B) (T p.1)) hT'
      (contDiffAt_twistTuple (fun b => contDiffAt_snd.smul contDiffAt_const) hT') hx ?_
      (hfst.eventually hgrp) ?_)
    · exact twistTuple_zero _ fun b => by simp
    · filter_upwards [hfst.eventually hgrp] with p hp
      exact twistTuple_mem s hp fun b =>
        (complexEdgeForms _).smul_mem _ hB |>.1 b.1 (hpos b b.2)
  exact contDiffAt_deriv_snd hH
theorem contDiffAt_secondDeriv (s : Hypotheses L k) {F : Finset (Edge L k 0)}
    (hpos : ∀ b ∈ F, b.IsPositivelyOriented) {𝔇 : Set (F → ComplexMatrix2)}
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : UnimodularRepresentation 𝔇 Φ) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    {T : E → F → ComplexMatrix2} {x : E}
    (hT : ∀ b, ContDiffAt ℂ ∞ (fun z => T z b) x) (hx : T x ∈ 𝔇)
    (hgrp : ∀ᶠ z in 𝓝 x, T z ∈ unimodularPi F) :
    ContDiffAt ℂ ∞ (fun z => secondDeriv Φ B B' (T z)) x := by
  have hfst : Tendsto (fun p : (E × ℂ) × ℂ => p.1.1) (𝓝 ((x, 0), 0)) (𝓝 x) :=
    (continuous_fst.comp continuous_fst).continuousAt.tendsto
  have hT' : ∀ b, ContDiffAt ℂ ∞ (fun p : (E × ℂ) × ℂ => T p.1.1 b) ((x, 0), 0) := fun b =>
    ContDiffAt.comp (((x, (0 : ℂ)), (0 : ℂ))) (hT b) (contDiffAt_fst.comp _ contDiffAt_fst)
  have hH : ContDiffAt ℂ ∞ (fun p : (E × ℂ) × ℂ => Complex.I⁻¹ • ComplexMatrix2.logSeries
      (Φ (twistTuple (p.1.2 • B + p.2 • B') (T p.1.1)) * (Φ (T p.1.1))⁻¹)) ((x, 0), 0) := by
    refine ContDiffAt.const_smul _ (contDiffAt_log_mul_inv s.analytic s.logSeries hΦ
      (g₀ := fun p : (E × ℂ) × ℂ => T p.1.1)
      (g₁ := fun p : (E × ℂ) × ℂ => twistTuple (p.1.2 • B + p.2 • B') (T p.1.1)) hT'
      (contDiffAt_twistTuple (fun b => ?_) hT') hx ?_ (hfst.eventually hgrp) ?_)
    · exact ((contDiffAt_snd.comp _ contDiffAt_fst).smul contDiffAt_const).add
        (contDiffAt_snd.smul contDiffAt_const)
    · exact twistTuple_zero _ fun b => by simp
    · filter_upwards [hfst.eventually hgrp] with p hp
      exact twistTuple_mem s hp fun b => ((complexEdgeForms _).add_mem
        ((complexEdgeForms _).smul_mem _ hB) ((complexEdgeForms _).smul_mem _ hB')).1 b.1
          (hpos b b.2)
  exact contDiffAt_deriv_snd (contDiffAt_deriv_snd hH)
end SmoothDerivs
section BasisForms
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem extendOddly_mem {a : ℝ} (ha : 0 < a) {g : InfiniteLattice.Link a → ComplexMatrix2}
    (hg : ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → g c ∈ ComplexMatrix2.traceless) :
    extendOddly g ∈ complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
theorem backgroundOfCoeffs_apply (hL : 0 < L) (f : FieldIdx L k hL → ℂ) {c : Edge L k 0}
    (hc : c.IsPositivelyOriented) :
    backgroundOfCoeffs hL f c = ∑ a, f ⟨.background, (a, ⟨c, hc⟩)⟩ • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.backgroundOfCoeffs_apply <;> assumption
theorem backgroundOfCoeffs_mem (hL : 0 < L) (s : 0 < meshAt L k 0) (f : FieldIdx L k hL → ℂ) :
    backgroundOfCoeffs hL f ∈ complexEdgeForms (meshAt L k 0) := by
  classical
  refine extendOddly_mem s fun c hc => ?_
  simp only [dif_pos hc]
  exact ComplexMatrix2.traceless.sum_mem fun a _ =>
    ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
theorem backgroundOfCoeffs_congr (hL : 0 < L) {f f' : FieldIdx L k hL → ℂ} {c : Edge L k 0}
    (hc : c.IsPositivelyOriented)
    (h : ∀ a : Fin 3, f ⟨.background, (a, ⟨c, hc⟩)⟩ = f' ⟨.background, (a, ⟨c, hc⟩)⟩) :
    backgroundOfCoeffs hL f c = backgroundOfCoeffs hL f' c := by
  simp only [backgroundOfCoeffs_apply hL _ hc, h]
theorem contDiff_backgroundOfCoeffs (hL : 0 < L) {S : Set (fieldPeriodicData L k hL).Carrier}
    {l : ℕ} (e : Fin l ≃ S) {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    ContDiff ℂ ∞ (fun z : ComplexCoordinates l => backgroundOfCoeffs hL (fieldExtend e z) c) := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.contDiff_backgroundOfCoeffs <;> assumption
theorem backgroundCoords_finite (hL : 0 < L) {T : Set (Edge L k 0)} (hT : T.Finite) :
    (backgroundCoords L k hL T).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.backgroundCoords_finite <;> assumption
theorem expForm_of_isPositivelyOriented (A : Edge L k 0 → ComplexMatrix2) {b : Edge L k 0}
    (hb : b.IsPositivelyOriented) : expForm A b = ComplexMatrix2.matExp (Complex.I • A b) := by apply _root_.YangMills.Construction.Tower.FullSpace.SmallIterates.expForm_of_pos <;> assumption
theorem gaugeFieldOfCoeffs_mem (s : Hypotheses L k) (hL : 0 < L) (f : FieldIdx L k hL → ℂ) :
    FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ baseFields L k :=
  expTwist_isFieldIn s.expLog (s.mesh_pos 0)
    ⟨fun _ => by show Matrix.det (1 : ComplexMatrix2) = 1; simp, fun _ => by simp⟩
    (backgroundOfCoeffs_mem hL (s.mesh_pos 0) f)
theorem basisForm_mem {j : ℕ} (ha : 0 < meshAt L k j) (a : Fin 3)
    (b : PositiveEdge (meshAt L k j)) :
    basisForm a b ∈ complexEdgeForms (meshAt L k j) := by
  classical
  refine extendOddly_mem ha fun c _ => ?_
  by_cases h : c = b.1
  · simp only [if_pos h]
    exact pauliFamily_mem_traceless a
  · simp only [if_neg h]
    exact ComplexMatrix2.traceless.zero_mem
theorem basisForm_mem_bounded (ha : 0 < meshAt L k 0) (a : Fin 3)
    (b : PositiveEdge (meshAt L k 0)) :
    basisForm a b ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) := by
  classical
  refine ⟨basisForm_mem ha a b, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily a),
    fun c => ?_⟩
  by_cases hc : c.IsPositivelyOriented
  · have e : basisForm a b c = if c = b.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos hc
    rw [e]
    split_ifs
    · exact le_rfl
    · simp [ComplexMatrix2.operatorNorm]
  · have e : basisForm a b c =
        -(if c.opposite = b.1 then ComplexMatrix2.pauliFamily a else 0) := if_neg hc
    rw [e]
    split_ifs
    · simp [ComplexMatrix2.operatorNorm]
    · simp [ComplexMatrix2.operatorNorm]
theorem singleSiteFunction_mem {σ : Type} (a : Fin 3) (x y : σ) :
    singleSiteFunction a x y ∈ ComplexMatrix2.traceless := by
  classical
  by_cases h : y = x
  · simpa [singleSiteFunction, h] using pauliFamily_mem_traceless a
  · simp [singleSiteFunction, h]
end BasisForms
section EdgeValues
variable {ρ : ℝ}
theorem UnimodularRepresentation.of_isHolomorphicOnProduct {τ : Type} [Fintype τ]
    {O : Set (τ → ComplexMatrix2)} {f : (τ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicOnProduct O f) : UnimodularRepresentation O f :=
  ⟨⟨OneLoop.pauliBasis, _, _, h OneLoop.pauliBasis, fun _ => rfl, fun v hv => ⟨v, hv, rfl⟩⟩⟩
theorem exists_representsMean (s : Hypotheses L k) {u : ℕ} (hu : u ≤ k) (c : Edge L k u)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c) :
    ∃ Φ, RepresentsMean (baseFields L k) F (meanAt c) (locus c F) Φ ∧
      UnimodularRepresentation (locus c F) Φ := by
  have r := s.support.dependsOnlyOn u hu c F hF
  obtain ⟨Φ, hΦ⟩ := r.exists_representation
  exact ⟨Φ, hΦ, UnimodularRepresentation.of_isHolomorphicOnProduct (r.representation_holomorphic Φ hΦ)⟩
def edgeValues (hL : 0 < L) (F : Finset (Edge L k 0)) (f : FieldIdx L k hL → ℂ) :
    F → ComplexMatrix2 :=
  fun b => FieldValueFunctions.gaugeFieldOfCoeffs hL f b
theorem contDiffAt_edgeValues (hL : 0 < L) {F : Finset (Edge L k 0)}
    (hpos : ∀ b ∈ F, b.IsPositivelyOriented) {S : Set (fieldPeriodicData L k hL).Carrier} {l : ℕ}
    (e : Fin l ≃ S) (z : ComplexCoordinates l) (b : F) :
    ContDiffAt ℂ ∞ (fun z : ComplexCoordinates l => edgeValues hL F (fieldExtend e z) b) z := by
  simp only [edgeValues, FieldValueFunctions.gaugeFieldOfCoeffs,
    expForm_of_isPositivelyOriented _ (hpos b b.2)]
  exact (contDiff_matExp.comp
    ((contDiff_backgroundOfCoeffs hL e (hpos b b.2)).const_smul Complex.I)).contDiffAt
theorem dependsOnCubesOf_of_edgeValues (hL : 0 < L) (hρ : 0 < ρ) {u : ℕ} {c : Edge L k u}
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    {X : ((fieldPeriodicData L k hL).Carrier → ℂ) → ComplexMatrix2}
    {G : (F → ComplexMatrix2) → ComplexMatrix2} (a : Fin 3)
    (hmem : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ → X f ∈ ComplexMatrix2.traceless)
    (hX : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ → X f = G (edgeValues hL F f))
    (hsm : ∀ (l : ℕ) (e : Fin l ≃ backgroundCoords L k hL (supportEdges c))
      (z : ComplexCoordinates l), (∀ j, ‖z j‖ < ρ) →
      ContDiffAt ℂ ∞ (fun z : ComplexCoordinates l => G (edgeValues hL F (fieldExtend e z))) z) :
    DependsOnCubesOf L k hL ρ c fun f => pauliCoeff a (X f) := by
  have hpos := isPositivelyOriented_of_mem hF
  refine holomorphicInValuesBelow_of_contDiffAt hρ
    (backgroundCoords_finite hL (hF ▸ F.finite_toSet)) a hmem ?_ ?_
  · intro ζ ζ' hζ hζ' hag
    have ht : edgeValues hL F ζ = edgeValues hL F ζ' := by
      funext b
      have hb : b.1 ∈ supportEdges c := by
        rw [← hF]
        exact b.2
      simp only [edgeValues, FieldValueFunctions.gaugeFieldOfCoeffs,
        expForm_of_isPositivelyOriented _ (hpos b b.2)]
      rw [backgroundOfCoeffs_congr hL (hpos b b.2) fun a' => hag _ ⟨a', ⟨b.1, hpos b b.2⟩, hb, rfl⟩]
    rw [hX ζ hζ, hX ζ' hζ', ht]
  · intro l e z hz
    refine (hsm l e z hz).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_coordPolydisc ρ).mem_nhds hz] with z' hz'
    exact hX _ (fieldExtend_isSupBelow_of_lt e hρ hz')
theorem edgeValues_mem_locus (s : Hypotheses L k) (hL : 0 < L) (hρ : 0 < ρ)
    (hsmall : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    {u : ℕ} (hu : u ≤ k) {c : Edge L k u}
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    {Φ : (F → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : RepresentsMean (baseFields L k) F (meanAt c) (locus c F) Φ)
    {S : Set (fieldPeriodicData L k hL).Carrier} {l : ℕ} (e : Fin l ≃ S) {z : ComplexCoordinates l}
    (hz : ∀ j, ‖z j‖ < ρ) :
    edgeValues hL F (fieldExtend e z) ∈ locus c F ∧
      ∀ᶠ z' in 𝓝 z, edgeValues hL F (fieldExtend e z') ∈ unimodularPi F :=
  ⟨(mem_locus_and_eq_of_small s (hsmall _ (fieldExtend_isSupBelow_of_lt e hρ hz)) hu c hF hΦ).1,
    Eventually.of_forall fun _ => restrict_mem_unimodularPi (gaugeFieldOfCoeffs_mem s hL _) F⟩
end EdgeValues
section MeanEntries
variable {ρ : ℝ}
theorem dependsOnCubesOf_iterDeriv (s : Hypotheses L k) (hL : 0 < L) (hρ : 0 < ρ)
    (hsmall : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    {i : ℕ} (hi : i < k) {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    (a' a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    DependsOnCubesOf L k hL ρ c fun f => pauliCoeff a'
      (complexIterDeriv L k (i + 1) (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
        (basisForm a b) c) := by
  obtain ⟨Φ, hΦ, hG⟩ := exists_representsMean s (Nat.succ_le_of_lt hi) c hF
  have hB := basisForm_mem (s.mesh_pos 0) a b
  have hpos := isPositivelyOriented_of_mem hF
  refine dependsOnCubesOf_of_edgeValues hL hρ hF a' (G := firstDeriv Φ (basisForm a b)) ?_ ?_ ?_
  · intro f hf
    have hU := hsmall f hf
    exact (s.derivs.1 i hi _ (hU.2 i hi) _ hU).mem_iter c hc _ hB
  · intro f hf
    exact complexIterDeriv_eq_firstDeriv s (hsmall f hf) hi hc hF hΦ hB
  · intro l e z hz
    obtain ⟨h₁, h₂⟩ := edgeValues_mem_locus s hL hρ hsmall (Nat.succ_le_of_lt hi) hF hΦ e hz
    exact contDiffAt_firstDeriv s hpos hG hB (contDiffAt_edgeValues hL hpos e z) h₁ h₂
theorem dependsOnCubesOf_quadratic (s : Hypotheses L k) (hL : 0 < L) (hρ : 0 < ρ)
    (hsmall : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    (c : PositiveEdge (meshAt L k k))
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c.1)
    (a'' a a' : Fin 3) (b b' : PositiveEdge (meshAt L k 0)) :
    DependsOnCubesOf L k hL ρ c.1 fun f => pauliCoeff a''
      (complexQuadraticTerm L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
        (basisForm a b) (basisForm a' b') c) := by
  obtain ⟨Φ, hΦ, hG⟩ := exists_representsMean s le_rfl c.1 hF
  have hB := basisForm_mem_bounded (s.mesh_pos 0) a b
  have hB' := basisForm_mem_bounded (s.mesh_pos 0) a' b'
  have hpos := isPositivelyOriented_of_mem hF
  refine dependsOnCubesOf_of_edgeValues hL hρ hF a''
    (G := secondDeriv Φ (basisForm a b) (basisForm a' b')) ?_ ?_ ?_
  · intro f hf
    exact (complexQuadraticTerm_eq_secondDeriv s (hsmall f hf) c hF hΦ hB hB').2
  · intro f hf
    exact (complexQuadraticTerm_eq_secondDeriv s (hsmall f hf) c hF hΦ hB hB').1
  · intro l e z hz
    obtain ⟨h₁, h₂⟩ := edgeValues_mem_locus s hL hρ hsmall le_rfl hF hΦ e hz
    exact contDiffAt_secondDeriv s hpos hG hB.1 hB'.1 (contDiffAt_edgeValues hL hpos e z) h₁ h₂
theorem contDiffAt_conjugateBy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → ComplexMatrix2} {x : E} (hA : ContDiffAt ℂ ∞ A x) (hx : (A x).det = 1)
    (M : ComplexMatrix2) :
    ContDiffAt ℂ ∞ (fun y => ComplexMatrix2.conjugateBy (A y) M) x :=
  (hA.mul contDiffAt_const).mul (contDiffAt_matrix_inv hA hx)
theorem dependsOnCubesOf_covDiff (s : Hypotheses L k) (hL : 0 < L) (hρ : 0 < ρ)
    (hsmall : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    {i : ℕ} (hi : i < k) {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    (a' a : Fin 3) (x : Vertex L k (i + 1)) :
    DependsOnCubesOf L k hL ρ c fun f => pauliCoeff a'
      (covDiff
        (complexIter L k (i + 1) (FieldValueFunctions.gaugeFieldOfCoeffs hL f))
        (singleSiteFunction a x) c) := by
  obtain ⟨Φ, hΦ, hG⟩ := exists_representsMean s (Nat.succ_le_of_lt hi) c hF
  have hpos := isPositivelyOriented_of_mem hF
  have hval : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      covDiff
        (complexIter L k (i + 1) (FieldValueFunctions.gaugeFieldOfCoeffs hL f))
        (singleSiteFunction a x) c =
      ComplexMatrix2.conjugateBy (Φ (edgeValues hL F f)) (singleSiteFunction a x c.terminal) -
        singleSiteFunction a x c.initial := fun f hf => by
    have e := (mem_locus_and_eq_of_small s (hsmall f hf) (Nat.succ_le_of_lt hi) c hF hΦ).2
    have e' : Φ (edgeValues hL F f) = _ := e
    rw [e']
    exact if_pos hc
  refine dependsOnCubesOf_of_edgeValues hL hρ hF a' (G := fun w => ComplexMatrix2.conjugateBy (Φ w)
    (singleSiteFunction a x c.terminal) - singleSiteFunction a x c.initial) ?_ hval ?_
  · intro f hf
    rw [hval f hf]
    exact ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless (singleSiteFunction_mem a x _)) (singleSiteFunction_mem a x _)
  · intro l e z hz
    obtain ⟨h₁, h₂⟩ := edgeValues_mem_locus s hL hρ hsmall (Nat.succ_le_of_lt hi) hF hΦ e hz
    exact (contDiffAt_conjugateBy
      (hG.contDiffAt_comp s.analytic (contDiffAt_edgeValues hL hpos e z) h₁ h₂)
      (hG.det_eq_one h₁) _).sub contDiffAt_const
theorem dependsOnCubesOf_cubeAverage (s : Hypotheses L k) (hL : 0 < L) (hρ : 0 < ρ)
    (hsmall : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    {i : ℕ} (hi : i < k) {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    (a' a : Fin 3) (x : Vertex L k i) :
    DependsOnCubesOf L k hL ρ c fun f => pauliCoeff a'
      (adjointCubeAverage (complexIter L k i (FieldValueFunctions.gaugeFieldOfCoeffs hL f))
        (singleSiteFunction a x) c.initial) := by
  classical
  obtain ⟨Φ, hΦ, -⟩ := exists_representsMean s (Nat.succ_le_of_lt hi) c hF
  have hpos := isPositivelyOriented_of_mem hF
  have step := s.support.step i hi c hc F hF
  have hy : c.initial ∈ ({c.initial, c.terminal} : Set (Vertex L k (i + 1))) := Or.inl rfl
  have hch : ∀ x' : Vertex L k i, ∃ g : (F → ComplexMatrix2) → ComplexMatrix2,
      x' ∈ cubeVertices L (meshAt L k i) c.initial → UnimodularRepresentation (locus c F) g ∧
        ∀ W ∈ baseFields L k, (fun b : F => W b) ∈ locus c F →
          g (fun b : F => W b) = complexContourMean L
            (valuesOrOne (levelwiseMean W i)) c.initial x' := fun x' => by
    by_cases hx' : x' ∈ cubeVertices L (meshAt L k i) c.initial
    · obtain ⟨g, hg, hv⟩ := step.holomorphic_contour c.initial hy x' hx'
      exact ⟨g, fun _ => ⟨UnimodularRepresentation.of_isHolomorphicOnProduct hg, hv⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx'⟩
  choose g hg using hch
  have hfin := s.cube_finite i hi c.initial
  let G : (F → ComplexMatrix2) → ComplexMatrix2 := fun w =>
    PeriodicLattice.inverseFourthPowerWeight L •
      ∑ x' ∈ hfin.toFinset, ComplexMatrix2.conjugateBy (g x' w) (singleSiteFunction a x x')
  have hval : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      adjointCubeAverage (complexIter L k i (FieldValueFunctions.gaugeFieldOfCoeffs hL f))
        (singleSiteFunction a x) c.initial = G (edgeValues hL F f) := fun f hf => by
    have hU := hsmall f hf
    have hin := (mem_locus_and_eq_of_small s hU (Nat.succ_le_of_lt hi) c hF hΦ).1
    show PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x' ∈ cubeVertices L (meshAt L k i) c.initial,
      ComplexMatrix2.conjugateBy (complexContourMean L _ c.initial x')
        (singleSiteFunction a x x') = _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine congrArg _ (Finset.sum_congr rfl fun x' hx' => ?_)
    have h := (hg x' (hfin.mem_toFinset.1 hx')).2 _ hU.1 hin
    rw [valuesOrOne_of_small s hU hi.le] at h
    have h' : g x' (edgeValues hL F f) = _ := h
    rw [h']
  refine dependsOnCubesOf_of_edgeValues hL hρ hF a' (G := G) ?_ hval ?_
  · intro f hf
    rw [hval f hf]
    exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sum_mem fun x' _ =>
      conjugateBy_mem_traceless (singleSiteFunction_mem a x x'))
  · intro l e z hz
    obtain ⟨h₁, h₂⟩ := edgeValues_mem_locus s hL hρ hsmall (Nat.succ_le_of_lt hi) hF hΦ e hz
    refine ContDiffAt.const_smul _ (ContDiffAt.sum fun x' hx' => ?_)
    have hgx := (hg x' (hfin.mem_toFinset.1 hx')).1
    exact contDiffAt_conjugateBy
      (hgx.contDiffAt_comp s.analytic (contDiffAt_edgeValues hL hpos e z) h₁ h₂)
      (hgx.det_eq_one h₁) _
end MeanEntries
section ContourDrift
variable {ρ : ℝ} {i : ℕ}
open YangMills.Construction.Tower.DoubleBlockPolydisc (IsHolomorphicWithEntries leftComponents)
open YangMills.Construction.Tower.DoubleBlockPolydisc.Infinite (doubleBlockBonds
  positiveDoubleBlockBonds polydiscPositive)
theorem eqOn_of_isPositivelyOriented {a : ℝ} (ha : 0 < a) {P : Set (InfiniteLattice.Link a)}
    (hrev : ∀ b ∈ P, b.opposite ∈ P) {W W' : InfiniteLattice.Link a → ComplexMatrix2}
    (hW : IsFieldOn PeriodicLattice.complexGaugeGroup P W)
    (hW' : IsFieldOn PeriodicLattice.complexGaugeGroup P W')
    (hag : ∀ b ∈ P, b.IsPositivelyOriented → W b = W' b) : ∀ b ∈ P, W b = W' b := by apply _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.eqOn_of_positive <;> assumption
theorem extendFromPositive_eq {a : ℝ} (ha : 0 < a) {P : Set (InfiniteLattice.Link a)}
    (hrev : ∀ b ∈ P, b.opposite ∈ P) {W : InfiniteLattice.Link a → ComplexMatrix2}
    (hW : IsFieldOn PeriodicLattice.complexGaugeGroup P W) :
    ∀ b ∈ P, extendFromPositive P (fun b : PositiveEdgeOf P => W b.1) b = W b := by apply _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.extendFromPositive_eq <;> assumption
theorem isFieldOn_doubleBlockBonds {c : Edge L k (i + 1)} {W : Edge L k i → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup) :
    IsFieldOn PeriodicLattice.complexGaugeGroup (doubleBlockBonds L k i c) W :=
  ⟨fun b _ => hW.1 b, fun b _ => hW.2 b⟩
theorem mem_polydisc_of_eqOn {c : Edge L k (i + 1)} {r : ℝ}
    (hrev : ∀ b ∈ doubleBlockBonds L k i c, b.opposite ∈ doubleBlockBonds L k i c)
    {W W' : Edge L k i → ComplexMatrix2} (hW : W ∈ nearIdentityPolydisc L k i r c)
    (hag : ∀ b ∈ doubleBlockBonds L k i c, W' b = W b) :
    W' ∈ nearIdentityPolydisc L k i r c := by apply _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.mem_polydisc_of_eqOn <;> assumption
theorem mem_polydisc_of_positive (s : Hypotheses L k) (hi : i < k)
    {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented) {W : Edge L k i → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup)
    (h : (fun b : positiveDoubleBlockBonds L k i c => W b.1) ∈
      polydiscPositive L k i (polydiscRadius L) c) :
    W ∈ nearIdentityPolydisc L k i (polydiscRadius L) c := by
  have hfo := (s.doubleBlock i hi c hc).finite_open
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, h⟩ := h
  have hag := eqOn_of_isPositivelyOriented (s.mesh_pos i) hfo.opposite_mem hW₀.1
    (isFieldOn_doubleBlockBonds hW) fun b hb hp => congrFun h ⟨b, hb, hp⟩
  exact mem_polydisc_of_eqOn hfo.opposite_mem hW₀ fun b hb => (hag b hb).symm
theorem UnimodularRepresentation.of_holomorphicWithEntries {τ : Type} [inst : Fintype τ]
    {W : Set (τ → ComplexMatrix2)} {Φ : (τ → ComplexMatrix2) → ComplexMatrix2}
    (h : ∃ _ : Fintype τ, IsHolomorphicWithEntries W Φ) : UnimodularRepresentation W Φ := by
  obtain ⟨i', h⟩ := h
  obtain rfl : i' = inst := Subsingleton.elim _ _
  exact ⟨⟨OneLoop.pauliBasis, _, _, h.toUnimodular OneLoop.pauliBasis,
    fun _ => rfl, fun _ hv => hv⟩⟩
def twistPositive {c : Edge L k (i + 1)} (C : Edge L k i → ComplexMatrix2)
    (v : positiveDoubleBlockBonds L k i c → ComplexMatrix2) :
    positiveDoubleBlockBonds L k i c → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • C b.1) * v b
def contourOfValues (c : Edge L k (i + 1)) (y : Vertex L k (i + 1)) (x : Vertex L k i)
    (v : positiveDoubleBlockBonds L k i c → ComplexMatrix2) : ComplexMatrix2 :=
  complexContourMean L (DoubleBlockPolydisc.Infinite.fieldOfValues L k i c v) y x
def driftDeriv (c : Edge L k (i + 1)) (y : Vertex L k (i + 1)) (x : Vertex L k i)
    (B : Edge L k i → ComplexMatrix2) (v : positiveDoubleBlockBonds L k i c → ComplexMatrix2) :
    ComplexMatrix2 :=
  deriv (fun t : ℂ => ComplexMatrix2.logSeries
    (contourOfValues c y x (twistPositive (t • B) v) * (contourOfValues c y x v)⁻¹)) 0
theorem contourOfValues_twist (s : Hypotheses L k) (hi : i < k) {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented)
    {y : Vertex L k (i + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (i + 1))))
    {x : Vertex L k i} (hx : x ∈ cubeVertices L (meshAt L k i) y)
    {V C : Edge L k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L k i)
    (hC : C ∈ complexEdgeForms (meshAt L k i))
    (hm : twistPositive C (fun b : positiveDoubleBlockBonds L k i c => V b.1) ∈
      polydiscPositive L k i (polydiscRadius L) c) :
    contourOfValues c y x (twistPositive C fun b : positiveDoubleBlockBonds L k i c => V b.1) =
      complexContourMean L (expTwist C V) y x := by
  have hW : expTwist C V ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup :=
    expTwist_isFieldIn s.expLog (s.mesh_pos i) hV.1 hC
  have e : twistPositive C (fun b : positiveDoubleBlockBonds L k i c => V b.1) =
      fun b : positiveDoubleBlockBonds L k i c => expTwist C V b.1 :=
    funext fun b => (if_pos b.2.2).symm
  rw [e] at hm ⊢
  have hWp := mem_polydisc_of_positive s hi hc hW hm
  have hfo := (s.doubleBlock i hi c hc).finite_open
  exact s.contour_eq i hi y x hx c hc hy _ hW hWp.2 _
    (extendFromPositive_eq (s.mesh_pos i) hfo.opposite_mem (isFieldOn_doubleBlockBonds hW))
theorem contourOfValues_restrict (s : Hypotheses L k) (hi : i < k) {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented)
    {y : Vertex L k (i + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (i + 1))))
    {x : Vertex L k i} (hx : x ∈ cubeVertices L (meshAt L k i) y)
    {V : Edge L k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L k i) :
    contourOfValues c y x (fun b : positiveDoubleBlockBonds L k i c => V b.1) =
      complexContourMean L V y x := by
  have hfo := (s.doubleBlock i hi c hc).finite_open
  exact s.contour_eq i hi y x hx c hc hy _ hV.1 (fun b _ => hV.2 b) _
    (extendFromPositive_eq (s.mesh_pos i) hfo.opposite_mem (isFieldOn_doubleBlockBonds hV.1))
theorem restrict_mem_polydiscPositive (s : Hypotheses L k) (hi : i < k) {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented)
    {V : Edge L k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L k i) :
    (fun b : positiveDoubleBlockBonds L k i c => V b.1) ∈
      polydiscPositive L k i (polydiscRadius L) c :=
  ⟨BondSetFields.restrictTo (doubleBlockBonds L k i c) V,
    ⟨V, s.stable.mem_polydisc i hi c hc V hV, rfl⟩, rfl⟩
theorem twistPositive_mem (s : Hypotheses L k) {c : Edge L k (i + 1)}
    {C : Edge L k i → ComplexMatrix2} {v : positiveDoubleBlockBonds L k i c → ComplexMatrix2}
    (hv : v ∈ unimodularPi (positiveDoubleBlockBonds L k i c))
    (hC : C ∈ complexEdgeForms (meshAt L k i)) :
    twistPositive C v ∈ unimodularPi (positiveDoubleBlockBonds L k i c) :=
  fun b => matExp_mul_mem_unitDeterminant s.expLog (hC.1 b.1 b.2.2) (hv b)
theorem twistPositive_zero {c : Edge L k (i + 1)} {C : Edge L k i → ComplexMatrix2}
    (v : positiveDoubleBlockBonds L k i c → ComplexMatrix2)
    (hC : ∀ b : positiveDoubleBlockBonds L k i c, C b.1 = 0) :
    twistPositive C v = v := by
  funext b
  simp [twistPositive, hC b, ComplexMatrix2.matExp]
theorem logDirectionalDeriv_eq_driftDeriv (s : Hypotheses L k) (hi : i < k) {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented)
    {y : Vertex L k (i + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (i + 1))))
    {x : Vertex L k i} (hx : x ∈ cubeVertices L (meshAt L k i) y)
    {V B : Edge L k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L k i)
    (hB : B ∈ complexEdgeForms (meshAt L k i)) :
    logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
      (complexContourMean L V y x) B =
    Complex.I⁻¹ • driftDeriv c y x B (fun b : positiveDoubleBlockBonds L k i c => V b.1) := by
  have hfo := (s.doubleBlock i hi c hc).finite_open
  have hv : (fun b : positiveDoubleBlockBonds L k i c => V b.1) ∈
      unimodularPi (positiveDoubleBlockBonds L k i c) :=
    fun b => hV.1.1 b.1
  have hcont : ContinuousAt (fun t : ℂ => twistPositive (t • B)
      (fun b : positiveDoubleBlockBonds L k i c => V b.1)) 0 := by
    refine continuousAt_pi.2 fun b => ?_
    have h1 : Continuous (fun t : ℂ => Complex.I • (t • B b.1)) := by fun_prop
    exact (((contDiff_matExp.continuous.comp h1).mul continuous_const)).continuousAt
  have hat : twistPositive ((0 : ℂ) • B) (fun b : positiveDoubleBlockBonds L k i c => V b.1) =
      fun b : positiveDoubleBlockBonds L k i c => V b.1 :=
    twistPositive_zero _ fun b => by simp
  have hev := eventually_mem_of_isRelativelyOpen hfo.isRelativelyOpen hcont
    (by simpa only [hat] using restrict_mem_polydiscPositive s hi hc hV)
    (Eventually.of_forall fun t =>
      twistPositive_mem s hv ((complexEdgeForms _).smul_mem t hB))
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply, driftDeriv]
  refine congrArg (fun X : ComplexMatrix2 => Complex.I⁻¹ • X) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [hev] with t ht
  rw [contourOfValues_twist s hi hc hy hx hV ((complexEdgeForms _).smul_mem t hB) ht,
    contourOfValues_restrict s hi hc hy hx hV]
theorem contDiffAt_driftDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Hypotheses L k) {c : Edge L k (i + 1)} [Fintype (positiveDoubleBlockBonds L k i c)]
    {y : Vertex L k (i + 1)} {x : Vertex L k i}
    (hγ : UnimodularRepresentation (polydiscPositive L k i (polydiscRadius L) c)
      (contourOfValues c y x))
    {B : Edge L k i → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k i))
    {T : E → positiveDoubleBlockBonds L k i c → ComplexMatrix2} {z : E}
    (hT : ∀ b, ContDiffAt ℂ ∞ (fun z => T z b) z)
    (hz : T z ∈ polydiscPositive L k i (polydiscRadius L) c)
    (hgrp : ∀ᶠ z' in 𝓝 z, T z' ∈ unimodularPi (positiveDoubleBlockBonds L k i c)) :
    ContDiffAt ℂ ∞ (fun z => driftDeriv c y x B (T z)) z := by
  have hfst : Tendsto (fun p : E × ℂ => p.1) (𝓝 (z, 0)) (𝓝 z) := continuousAt_fst.tendsto
  have hT' : ∀ b, ContDiffAt ℂ ∞ (fun p : E × ℂ => T p.1 b) (z, 0) := fun b =>
    ContDiffAt.comp (z, (0 : ℂ)) (hT b) contDiffAt_fst
  have hH : ContDiffAt ℂ ∞ (fun p : E × ℂ => ComplexMatrix2.logSeries
      (contourOfValues c y x (twistPositive (p.2 • B) (T p.1)) *
        (contourOfValues c y x (T p.1))⁻¹)) (z, 0) := by
    refine contDiffAt_log_mul_inv s.analytic s.logSeries hγ
      (g₀ := fun p : E × ℂ => T p.1) (g₁ := fun p : E × ℂ => twistPositive (p.2 • B) (T p.1)) hT'
      (fun b => ?_) hz ?_ (hfst.eventually hgrp) ?_
    · exact (ContDiffAt.comp _ contDiff_matExp.contDiffAt
        ((contDiffAt_snd.smul contDiffAt_const).const_smul Complex.I)).mul (hT' b)
    · exact twistPositive_zero _ fun b => by simp
    · filter_upwards [hfst.eventually hgrp] with p hp
      exact twistPositive_mem s hp ((complexEdgeForms _).smul_mem _ hB)
  exact contDiffAt_deriv_snd hH
theorem dependsOnCubesOf_contourLogDrift (s : Hypotheses L k) (hL : 0 < L) (hρ : 0 < ρ)
    (hsmall : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    (hi : i < k) {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented)
    {F : Finset (Edge L k 0)} (hF : (F : Set (Edge L k 0)) = supportEdges c)
    (a' a : Fin 3) (b : PositiveEdge (meshAt L k i)) :
    DependsOnCubesOf L k hL ρ c fun f => pauliCoeff a'
      (contourLogDrift (complexIter L k i (FieldValueFunctions.gaugeFieldOfCoeffs hL f))
        (basisForm a b) c.initial) := by
  classical
  obtain ⟨Φ, hΦ, -⟩ := exists_representsMean s (Nat.succ_le_of_lt hi) c hF
  have hpos := isPositivelyOriented_of_mem hF
  have step := s.support.step i hi c hc F hF
  have hd := s.doubleBlock i hi c hc
  have hfo := hd.finite_open
  have r := s.support.dependsOnlyOn (i + 1) (Nat.succ_le_of_lt hi) c F hF
  let _ : Fintype (positiveDoubleBlockBonds L k i c) := hfo.positive_finite.fintype
  have hy : c.initial ∈ ({c.initial, c.terminal} : Set (Vertex L k (i + 1))) := Or.inl rfl
  have hB := basisForm_mem (s.mesh_pos i) a b
  have hch : ∀ b' : Edge L k i, ∃ ψ : (F → ComplexMatrix2) → ComplexMatrix2,
      b' ∈ doubleBlockBonds L k i c → UnimodularRepresentation (locus c F) ψ ∧
        ∀ W ∈ baseFields L k, (fun b : F => W b) ∈ locus c F →
          ψ (fun b : F => W b) = valuesOrOne (levelwiseMean W i) b' := fun b' => by
    by_cases hb' : b' ∈ doubleBlockBonds L k i c
    · obtain ⟨ψ, hψ, hv⟩ := step.holomorphic_edge b' hb'
      exact ⟨ψ, fun _ => ⟨UnimodularRepresentation.of_isHolomorphicOnProduct hψ, hv⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hb'⟩
  choose ψ hψ using hch
  have hfin := s.cube_finite i hi c.initial
  let base : (F → ComplexMatrix2) → positiveDoubleBlockBonds L k i c → ComplexMatrix2 :=
    fun w b' => ψ b'.1 w
  let G : (F → ComplexMatrix2) → ComplexMatrix2 := fun w =>
    PeriodicLattice.inverseFourthPowerWeight L •
      ∑ x' ∈ hfin.toFinset, Complex.I⁻¹ • driftDeriv c c.initial x' (basisForm a b) (base w)
  have hbase : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ → base (edgeValues hL F f) =
      fun b' : positiveDoubleBlockBonds L k i c =>
        complexIter L k i (FieldValueFunctions.gaugeFieldOfCoeffs hL f) b'.1 := fun f hf => by
    have hU := hsmall f hf
    have hin := (mem_locus_and_eq_of_small s hU (Nat.succ_le_of_lt hi) c hF hΦ).1
    funext b'
    have h := (hψ b'.1 b'.2.1).2 _ hU.1 hin
    rw [valuesOrOne_of_small s hU hi.le] at h
    exact h
  have hval : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      contourLogDrift (complexIter L k i (FieldValueFunctions.gaugeFieldOfCoeffs hL f))
        (basisForm a b) c.initial = G (edgeValues hL F f) := fun f hf => by
    have hU := hsmall f hf
    show PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x' ∈ cubeVertices L (meshAt L k i) c.initial,
      logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X _) c.initial x')
        (complexContourMean L _ c.initial x') (basisForm a b) = _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine congrArg _ (Finset.sum_congr rfl fun x' hx' => ?_)
    rw [logDirectionalDeriv_eq_driftDeriv s hi hc hy (hfin.mem_toFinset.1 hx') (hU.2 i hi) hB,
      hbase f hf]
  refine dependsOnCubesOf_of_edgeValues hL hρ hF a' (G := G) ?_ hval ?_
  · intro f hf
    have hU := hsmall f hf
    exact (s.derivs.1 i hi _ (hU.2 i hi) _ hU).mem_contour c.initial _ hB
  · intro l e z hz
    obtain ⟨h₁, h₂⟩ := edgeValues_mem_locus s hL hρ hsmall (Nat.succ_le_of_lt hi) hF hΦ e hz
    have hbelow := fieldExtend_isSupBelow_of_lt e hρ hz
    have hT : ∀ (b' : positiveDoubleBlockBonds L k i c), ContDiffAt ℂ ∞
        (fun z => base (edgeValues hL F (fieldExtend e z)) b') z := fun b' =>
      (hψ b'.1 b'.2.1).1.contDiffAt_comp s.analytic (contDiffAt_edgeValues hL hpos e z) h₁ h₂
    have hcont : ContinuousAt (fun z : ComplexCoordinates l =>
        edgeValues hL F (fieldExtend e z)) z :=
      continuousAt_pi.2 fun b' => (contDiffAt_edgeValues hL hpos e z b').continuousAt
    have hin := eventually_mem_of_isRelativelyOpen r.isOpen hcont h₁ h₂
    have hgrp : ∀ᶠ z' in 𝓝 z, base (edgeValues hL F (fieldExtend e z')) ∈
        unimodularPi (positiveDoubleBlockBonds L k i c) := by
      filter_upwards [hin] with z' hz' b'
      exact (hψ b'.1 b'.2.1).1.det_eq_one hz'
    have hz₀ : base (edgeValues hL F (fieldExtend e z)) ∈
        polydiscPositive L k i (polydiscRadius L) c := by
      rw [hbase _ hbelow]
      exact restrict_mem_polydiscPositive s hi hc ((hsmall _ hbelow).2 i hi)
    refine ContDiffAt.const_smul _ (ContDiffAt.sum fun x' hx' => ContDiffAt.const_smul _ ?_)
    exact contDiffAt_driftDeriv s
      (UnimodularRepresentation.of_holomorphicWithEntries
        (hd.holomorphic_contourMean c.initial hy x' (hfin.mem_toFinset.1 hx')))
      hB hT hz₀ hgrp
end ContourDrift
end TowerFacts
section Assembly
variable {L k : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) : 0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem cubeVertices_finite (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k) (y : Vertex L k (i + 1)) :
    (cubeVertices L (meshAt L k i) y).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.cubeVertices_finite <;> assumption
end Assembly
theorem entriesHolomorphic
    (hSmall : SmallIterates.SmallIteratesNearOne)
    (hD : YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hR : YangMills.Construction.Tower.SupportOfMeans.SupportOfMeansHolds)
    (hAn : HolomorphicMatrixAnalyticity)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hElem : PeriodicLattice.ElementaryStepFacts)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hO : IteratedMeans.IteratedMeansHold)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hB : PairContourIndependence.Statement)
    (hZ : BlockStructure) :
    EntriesHolomorphic := by
  classical
  intro L hL hst k hk
  have s : Hypotheses L k :=
    { analytic := hAn
      expLog := hEL
      logSeries := (hElem L 1 1 0 hst one_pos zero_lt_one).2.2.1
      support := (hR L hst k hk).2
      derivs := (hD L hst k hk).2
      stable := (hW L hst k hk).2
      iterated := (hO L hst k hk).2
      mesh_pos := meshAt_pos hst
      doubleBlock := fun j hj c hc => (hP L hst k j hj).2 c hc
      contour_eq := fun j hj y x hx c hc hy V' hconf hw W hr =>
        ((hB L hst k j hj).2 y x hx c c hc hc hy hy V' hconf hw hw W V' hr
          (fun _ _ => rfl)).2.2
      cube_finite := fun j hj y => cubeVertices_finite hZ hst hj y }
  obtain ⟨ρ, hρ, hsmall⟩ := (hSmall L hL hst k hk).2
  refine ⟨ρ, hρ, fun i hi c hc => ?_, fun c => ?_⟩
  · have hF := (s.support.finite_nonempty (i + 1) (Nat.succ_le_of_lt hi) c).1.coe_toFinset
    exact ⟨fun a' a b => dependsOnCubesOf_iterDeriv s hL hρ hsmall hi hc hF a' a b,
      fun a' a x => dependsOnCubesOf_covDiff s hL hρ hsmall hi hc hF a' a x,
      fun a' a x => dependsOnCubesOf_cubeAverage s hL hρ hsmall hi hc hF a' a x,
      fun a' a b => dependsOnCubesOf_contourLogDrift s hL hρ hsmall hi hc hF a' a b⟩
  · have hF := (s.support.finite_nonempty k le_rfl c.1).1.coe_toFinset
    exact fun a'' a a' b b' => dependsOnCubesOf_quadratic s hL hρ hsmall c hF a'' a a' b b'
end YangMills.Construction.Tower.FullSpace.ElementaryEntries
end
