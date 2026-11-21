import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.HolomorphicExtensionOfTheOperations
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.StepKernelsNearOneOnASideProof
import YangMills.Construction.Towers.EntriesOfTheActionAndOfTheCovariantDifference
import YangMills.Construction.Towers.TermsOfTheUnsymmetrisedBackgroundKernel
import Mathlib
import YangMills.Construction.Towers.TheSiteFunctionAndTheShiftAtAnElementaryForm
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.FullSpace.KernelTermsLocality
open PeriodicOperators FieldValueFunctions UnsymmetrisedKernelTerms
open FieldValueFunctions.LocalComponents (hessianEntry)
def ActionAndSourceTermsLocal : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (a' : Fin 3) (b' : PositiveEdge (meshAt L k 0)) (a : Fin 3)
      (b : PositiveEdge (meshAt L k 0)),
      IsLocalTerm L k hL ρ b' b (hessianEntry L k hL a' b' a b) ∧
      IsLocalTerm L k hL ρ b' b (sourceBracketTerm L k hL a' b' a b) ∧
      IsLocalTerm L k hL ρ b' b (sourceBracketCovTerm L k hL a' b' a b)
end YangMills.Construction.Tower.FullSpace.KernelTermsLocality
end

noncomputable section
namespace YangMills.Construction.Tower.FullSpace.KernelTermsLocality
open Matrices
open PeriodicOperators FieldValueFunctions IteratedKernelEntries
open UnsymmetrisedKernelTerms
open PeriodicOperators.HolomorphicCoordinateClosure
open FieldValueFunctions.LocalComponents
open FaceEdgeFinsets.Unbounded (facesMeeting)
open LocalKernels (FieldIdx FieldComponent)
open TorusMetric (euclidNormVec)
theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {θ : ℝ} (h : ∀ i, |v i| < θ) :
    euclidNormVec v ≤ 2 * θ := by
  have hθ : 0 < θ := lt_of_le_of_lt (abs_nonneg _) (h 0)
  have hsq : ∀ i, v i ^ 2 ≤ θ ^ 2 := fun i => by
    rw [← sq_abs (v i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i).le 2
  unfold euclidNormVec
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ μ, v μ ^ 2 ≤ ∑ _μ : Fin 4, θ ^ 2 := Finset.sum_le_sum fun i _ => hsq i
    _ = (2 * θ) ^ 2 := by simp; ring
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem eq_sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.eq_sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem halfTrace_mul_sum_smul (j x : Fin 3 → ℂ) :
    ComplexMatrix2.halfTrace ((∑ e, j e • ComplexMatrix2.pauliFamily e) *
        ∑ a, x a • ComplexMatrix2.pauliFamily a) =
      ∑ e, ∑ a, j e * x a *
        ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily e * ComplexMatrix2.pauliFamily a) := by
  rw [Finset.sum_mul_sum]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_sum, Finset.mul_sum,
    smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  ring
theorem conjugateBy_sum_smul (V : ComplexMatrix2) (c : Fin 3 → ℂ) :
    ComplexMatrix2.conjugateBy V (∑ a, c a • ComplexMatrix2.pauliFamily a) =
      ∑ a, c a • ComplexMatrix2.conjugateBy V (ComplexMatrix2.pauliFamily a) := by
  simp only [ComplexMatrix2.conjugateBy, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]
theorem conjugateBy_zero (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
variable {L k : ℕ} {hL : 0 < L}
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L k 0 :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_le_one (hL : 0 < L) : meshAt L k 0 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold meshAt
  exact zpow_le_one_of_nonpos₀ h1 (by simp)
theorem axisStep_apply_eq_zero_or (a : ℝ) (μ i : Fin 4) :
    ((InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) :
        InfiniteLattice.AmbientSpace) i = 0 ∨
      ((InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) :
        InfiniteLattice.AmbientSpace) i = a := by
  by_cases h : i = μ
  · subst h
    right
    simp [InfiniteLattice.axisStep]
  · left
    simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
theorem abs_terminal_sub_initial_le_one (hL : 0 < L) (c : Edge L k 0) (i : Fin 4) :
    |(c.terminal : InfiniteLattice.AmbientSpace) i -
      (c.initial : InfiniteLattice.AmbientSpace) i| ≤ 1 := by
  have hs := meshAt_pos (k := k) hL
  have h1 := meshAt_le_one (k := k) hL
  obtain ⟨μ, h | h⟩ := c.isAdjacent
  · have e : (c.terminal : InfiniteLattice.AmbientSpace) i -
        (c.initial : InfiniteLattice.AmbientSpace) i =
        ((InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.LatticePoint _) :
          InfiniteLattice.AmbientSpace) i := by
      rw [← h]; rfl
    rw [e]
    rcases axisStep_apply_eq_zero_or (meshAt L k 0) μ i with h' | h' <;> rw [h']
    · simp
    · rw [abs_of_pos hs]; exact h1
  · have e : (c.terminal : InfiniteLattice.AmbientSpace) i -
        (c.initial : InfiniteLattice.AmbientSpace) i =
        -((InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.LatticePoint _) :
          InfiniteLattice.AmbientSpace) i := by
      rw [show -((InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.LatticePoint _) :
          InfiniteLattice.AmbientSpace) i =
        ((-InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.LatticePoint _) :
          InfiniteLattice.AmbientSpace) i from rfl,
        ← h]
      rfl
    rw [e, abs_neg]
    rcases axisStep_apply_eq_zero_or (meshAt L k 0) μ i with h' | h' <;> rw [h']
    · simp
    · rw [abs_of_pos hs]; exact h1
theorem initial_ne_terminal (hL : 0 < L) (c : Edge L k 0) : c.initial ≠ c.terminal := by
  intro h
  have hs := meshAt_pos (k := k) hL
  obtain ⟨μ, e | e⟩ := c.isAdjacent
  · rw [h, sub_self] at e
    have := congrArg (fun y : InfiniteLattice.LatticePoint _ =>
      (y : InfiniteLattice.AmbientSpace) μ) e
    simp [InfiniteLattice.axisStep] at this
    first | exact hs.ne this | exact hs.ne' this
  · rw [h, sub_self] at e
    have := congrArg (fun y : InfiniteLattice.LatticePoint _ =>
      (y : InfiniteLattice.AmbientSpace) μ) e
    simp [InfiniteLattice.axisStep] at this
    first | exact hs.ne this | exact hs.ne' this
theorem initial_sub_corner_bounds (hL : 0 < L) {p : Face L k 0} {c : Edge L k 0}
    (hc : c ∈ faceEdges p) (i : Fin 4) :
    0 ≤ (c.initial : InfiniteLattice.AmbientSpace) i -
        (p.corner : InfiniteLattice.AmbientSpace) i ∧
      (c.initial : InfiniteLattice.AmbientSpace) i -
        (p.corner : InfiniteLattice.AmbientSpace) i ≤ 1 := by
  have hs := meshAt_pos (k := k) hL
  have h1 := meshAt_le_one (k := k) hL
  have key : ∀ μ : Fin 4,
      0 ≤ ((p.corner + InfiniteLattice.axisStep (meshAt L k 0) μ :
          InfiniteLattice.LatticePoint _) : InfiniteLattice.AmbientSpace) i -
        (p.corner : InfiniteLattice.AmbientSpace) i ∧
      ((p.corner + InfiniteLattice.axisStep (meshAt L k 0) μ :
          InfiniteLattice.LatticePoint _) : InfiniteLattice.AmbientSpace) i -
        (p.corner : InfiniteLattice.AmbientSpace) i ≤ 1 := by
    intro μ
    have e : ((p.corner + InfiniteLattice.axisStep (meshAt L k 0) μ :
        InfiniteLattice.LatticePoint _) : InfiniteLattice.AmbientSpace) i -
        (p.corner : InfiniteLattice.AmbientSpace) i =
        ((InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.LatticePoint _) :
          InfiniteLattice.AmbientSpace) i := by
      show (p.corner : InfiniteLattice.AmbientSpace) i +
        ((InfiniteLattice.axisStep (meshAt L k 0) μ : InfiniteLattice.LatticePoint _) :
          InfiniteLattice.AmbientSpace) i -
        (p.corner : InfiniteLattice.AmbientSpace) i = _
      ring
    rw [e]
    rcases axisStep_apply_eq_zero_or (meshAt L k 0) μ i with h' | h' <;> rw [h']
    · simp
    · exact ⟨hs.le, h1⟩
  simp only [faceEdges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h <;> subst h
  · simp [InfiniteLattice.Link.forwardFrom]
  · exact key _
  · exact key _
  · simp [InfiniteLattice.Link.forwardFrom]
theorem sourceOfCoeffs_apply (hL : 0 < L) (f : FieldIdx L k hL → ℂ) {c : Edge L k 0}
    (hc : c.IsPositivelyOriented) :
    sourceOfCoeffs hL f c = ∑ a, f ⟨.source, (a, ⟨c, hc⟩)⟩ • ComplexMatrix2.pauliFamily a := by
  classical
  simp [sourceOfCoeffs, edgePauliCoordinates, extendOddly, hc, ofPauliCoeffs]
  rfl
theorem levelBracketTerm_apply (U : Edge L k 0 → ComplexMatrix2) (l : Vertex L k 0 → ComplexMatrix2)
    (B : Edge L k 0 → ComplexMatrix2) {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    levelBracketTerm U l B c =
      (Complex.I / 2) • ⁅l c.initial + ComplexMatrix2.conjugateBy (U c) (l c.terminal), B c⁆ :=
  if_pos hc
theorem basisForm_apply_self (a : Fin 3) (c : PositiveEdge (meshAt L k 0)) :
    basisForm a c c.1 = ComplexMatrix2.pauliFamily a := by
  classical
  have e : basisForm a c c.1 = if c.1 = c.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos c.2
  rw [e, if_pos rfl]
theorem basisForm_apply_of_ne (a : Fin 3) {b c : PositiveEdge (meshAt L k 0)} (h : c ≠ b) :
    basisForm a b c.1 = 0 := by
  classical
  have e : basisForm a b c.1 = if c.1 = b.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos c.2
  rw [e, if_neg fun h' => h (Subtype.ext h')]
theorem basisForm_mem_traceless (a : Fin 3) (b c : PositiveEdge (meshAt L k 0)) :
    basisForm a b c.1 ∈ ComplexMatrix2.traceless := by
  by_cases h : c = b
  · subst h
    rw [basisForm_apply_self]
    exact pauliFamily_mem_traceless a
  · rw [basisForm_apply_of_ne a h]
    exact ComplexMatrix2.traceless.zero_mem
theorem levelBracketTerm_eq_zero_of_form (U : Edge L k 0 → ComplexMatrix2)
    (l : Vertex L k 0 → ComplexMatrix2)
    {B : Edge L k 0 → ComplexMatrix2} {c : Edge L k 0} (hc : c.IsPositivelyOriented) (h : B c = 0) :
    levelBracketTerm U l B c = 0 := by
  rw [levelBracketTerm_apply U l B hc, h]
  simp [Ring.lie_def]
theorem levelBracketTerm_eq_zero_of_vertices (U : Edge L k 0 → ComplexMatrix2)
    {l : Vertex L k 0 → ComplexMatrix2}
    (B : Edge L k 0 → ComplexMatrix2) {c : Edge L k 0} (hc : c.IsPositivelyOriented)
    (h₁ : l c.initial = 0) (h₂ : l c.terminal = 0) : levelBracketTerm U l B c = 0 := by
  rw [levelBracketTerm_apply U l B hc, h₁, h₂, conjugateBy_zero]
  simp [Ring.lie_def]
theorem levelBracketTerm_eq_sum (hL : 0 < L) (U : Edge L k 0 → ComplexMatrix2)
    (c : PositiveEdge (meshAt L k 0)) {l : Vertex L k 0 → ComplexMatrix2}
    {B : Edge L k 0 → ComplexMatrix2} {s s' t : Fin 3 → ℂ}
    (h₁ : l c.1.initial = ∑ a, s a • ComplexMatrix2.pauliFamily a)
    (h₂ : l c.1.terminal = ∑ a, s' a • ComplexMatrix2.pauliFamily a)
    (h₃ : B c.1 = ∑ e, t e • ComplexMatrix2.pauliFamily e) :
    levelBracketTerm U l B c.1 = ∑ a, ∑ e,
      ((s a * t e) • levelBracketTerm U (vertexBasisFunction a c.1.initial)
          (basisForm e c) c.1 +
        (s' a * t e) • levelBracketTerm U (vertexBasisFunction a c.1.terminal)
          (basisForm e c) c.1) := by
  have hne := initial_ne_terminal hL c.1
  have v₁ : ∀ a, vertexBasisFunction a c.1.initial c.1.initial = ComplexMatrix2.pauliFamily a :=
    fun a => by simp [vertexBasisFunction]
  have v₂ : ∀ a, vertexBasisFunction a c.1.initial c.1.terminal = 0 := fun a => by
    simp [vertexBasisFunction, hne.symm]
  have v₃ : ∀ a, vertexBasisFunction a c.1.terminal c.1.initial = 0 := fun a => by
    simp [vertexBasisFunction, hne]
  have v₄ : ∀ a, vertexBasisFunction a c.1.terminal c.1.terminal = ComplexMatrix2.pauliFamily a :=
    fun a => by simp [vertexBasisFunction]
  simp only [levelBracketTerm_apply U _ _ c.2, v₁, v₂, v₃, v₄, basisForm_apply_self, h₁, h₂, h₃,
    conjugateBy_sum_smul, conjugateBy_zero, add_zero, zero_add]
  simp only [Fin.sum_univ_three, Ring.lie_def, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module
theorem levelBracketTerm_mem_traceless (U : Edge L k 0 → ComplexMatrix2)
    (l : Vertex L k 0 → ComplexMatrix2)
    (B : Edge L k 0 → ComplexMatrix2) {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    levelBracketTerm U l B c ∈ ComplexMatrix2.traceless := by
  rw [levelBracketTerm_apply U l B hc]
  refine ComplexMatrix2.traceless.smul_mem _ ?_
  change Matrix.trace _ = 0
  rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
section Holomorphy
variable {ρ : ℝ} {T : Set (fieldPeriodicData L k hL).Carrier}
theorem holomorphic_pauliCoeff {P : Type} {T₀ : Set (fieldPeriodicData L k hL).Carrier} {S : Set P}
    {Φ : ((fieldPeriodicData L k hL).Carrier → ℂ) → P → ComplexMatrix2}
    (hT : ClosureProperties (fieldPeriodicData L k hL) ρ T)
    (hV : CoeffsHolomorphicOn (fieldPeriodicData L k hL) ρ T₀ S Φ)
    (h₀ : T₀ ⊆ T) (a : Fin 3) (p : P) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T fun ζ => pauliCoeff a (Φ ζ p) := by
  by_cases hp : p ∈ S
  · exact hT.of_subset _ _ h₀ (hV.holomorphic_coeff p hp a)
  · refine hT.congr_below _ _ (fun ζ hζ => ?_) (hT.const 0)
    rw [hV.eq_zero_of_not_mem ζ hζ p hp, pauliCoeff_zero]
theorem holomorphic_halfTrace_source_mul_bracket (hT : ClosureProperties (fieldPeriodicData L k hL) ρ T)
    (c : PositiveEdge (meshAt L k 0))
    (hE : ∀ (a' a e : Fin 3) (x : Vertex L k 0),
      HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T (bracketEntry L k hL a' c a x e c))
    (hcur : ∀ e : Fin 3, (⟨.source, (e, c)⟩ : FieldIdx L k hL) ∈ T)
    {l : ((fieldPeriodicData L k hL).Carrier → ℂ) → Vertex L k 0 → ComplexMatrix2}
    {B : ((fieldPeriodicData L k hL).Carrier → ℂ) → Edge L k 0 → ComplexMatrix2}
    {s : Fin 3 → Vertex L k 0 → ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ}
    {t : Fin 3 → ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ}
    (hs : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → ∀ x,
      l ζ x = ∑ a, s a x ζ • ComplexMatrix2.pauliFamily a)
    (hsr : ∀ a x, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T (s a x))
    (ht : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ →
      B ζ c.1 = ∑ e, t e ζ • ComplexMatrix2.pauliFamily e)
    (htr : ∀ e, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T (t e)) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T fun ζ =>
      ComplexMatrix2.halfTrace (sourceOfCoeffs hL ζ c.1 *
        levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (l ζ) (B ζ) c.1) := by
  let x : Fin 3 → ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ := fun a' ζ => ∑ a, ∑ e,
    (s a c.1.initial ζ * t e ζ * bracketEntry L k hL a' c a c.1.initial e c ζ +
      s a c.1.terminal ζ * t e ζ * bracketEntry L k hL a' c a c.1.terminal e c ζ)
  have hx : ∀ a', HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T (x a') := fun a' =>
    hT.sum _ _ fun a _ => hT.sum _ _ fun e _ => hT.add _ _
      (hT.mul _ _ (hT.mul _ _ (hsr _ _) (htr _)) (hE _ _ _ _))
      (hT.mul _ _ (hT.mul _ _ (hsr _ _) (htr _)) (hE _ _ _ _))
  have hR : HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ T fun ζ => ∑ e, ∑ a',
      ζ ⟨.source, (e, c)⟩ * x a' ζ *
        ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily e * ComplexMatrix2.pauliFamily a') :=
    hT.sum _ _ fun e _ => hT.sum _ _ fun a' _ => hT.mul _ _
      (hT.mul _ _ (hT.coord _ (hcur e)) (hx a')) (hT.const _)
  refine hT.congr_below _ _ (fun ζ hζ => ?_) hR
  have hW : ∀ (a e : Fin 3) (y : Vertex L k 0),
      levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (vertexBasisFunction a y)
        (basisForm e c) c.1 =
      ∑ a', bracketEntry L k hL a' c a y e c ζ • ComplexMatrix2.pauliFamily a' := fun a e y =>
    eq_sum_pauliCoeff_smul (levelBracketTerm_mem_traceless _ _ _ c.2)
  have hX : levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (l ζ) (B ζ) c.1 =
      ∑ a', x a' ζ • ComplexMatrix2.pauliFamily a' := by
    rw [levelBracketTerm_eq_sum hL _ c (hs ζ hζ _) (hs ζ hζ _) (ht ζ hζ)]
    have step : ∀ a e : Fin 3,
        (s a c.1.initial ζ * t e ζ) •
            (∑ a', bracketEntry L k hL a' c a c.1.initial e c ζ • ComplexMatrix2.pauliFamily a') +
          (s a c.1.terminal ζ * t e ζ) •
            (∑ a', bracketEntry L k hL a' c a c.1.terminal e c ζ • ComplexMatrix2.pauliFamily a') =
        ∑ a', (s a c.1.initial ζ * t e ζ * bracketEntry L k hL a' c a c.1.initial e c ζ +
          s a c.1.terminal ζ * t e ζ * bracketEntry L k hL a' c a c.1.terminal e c ζ) •
            ComplexMatrix2.pauliFamily a' :=
      fun a e => by
        simp only [Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
    simp only [hW, step, x, Finset.sum_smul]
    exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  rw [sourceOfCoeffs_apply hL ζ c.2, hX, halfTrace_mul_sum_smul]
  rfl
end Holomorphy
theorem indicesWithin_finite (hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite)
    (x : InfiniteLattice.AmbientSpace) (r : ℝ) : (indicesWithin L k hL x r).Finite :=
  (hfin x (2 * r)).subset fun κ hκ =>
    euclidNormVec_le_two_mul (v := (fieldPeriodicData L k hL).pos κ - x) (θ := r) fun i => hκ i
theorem not_abs_sub_lt_half {x y y' : InfiniteLattice.AmbientSpace} {i : Fin 4}
    (h : 6 ≤ |y i - y' i|) (hx : |x i - y i| ≤ 5) : ¬ |x i - y' i| < 1 / 2 := by
  intro hn
  have h₁ := abs_sub_le (y i) (x i) (y' i)
  rw [abs_sub_comm (y i) (x i)] at h₁
  linarith
theorem edgeFormPairing_eq_finsum (A B : Edge L k 0 → ComplexMatrix2) :
    finiteEdgePairing A B = ∑ᶠ c : PositiveEdge (meshAt L k 0),
      ComplexMatrix2.halfTrace (A c.1 * B c.1) := rfl
theorem halfTrace_mul_zero (X : ComplexMatrix2) : ComplexMatrix2.halfTrace (X * 0) = 0 := by
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem actionAndSourceTermsLocal_holds (hC : ClosureHolds)
    (hFin : CovariantFiniteRange.Claim)
    (hTower : LocalKernels.IndexSetPeriodicity.Statement)
    (hE : FieldValueFunctions.LocalComponents.EntriesAreLocalAndEntire)
    (hS : BasisFormLocality.ElementaryFormLocality) : ActionAndSourceTermsLocal := by
  intro L hL hStd k hk
  obtain ⟨ρ, hρ, hS⟩ := hS L hL hStd k hk
  have hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite :=
    (hFin.1 _ ((hTower L hStd k).2 _).1).1
  obtain ⟨hE₁, -, hE₃⟩ := hE L hL hStd k
  refine ⟨ρ, hρ, fun a' b' a b => ?_⟩
  have hT : ClosureProperties (fieldPeriodicData L k hL) ρ
      (indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2)) :=
    hC _ ρ _ hρ ((indicesWithin_finite hfin _ _).union (indicesWithin_finite hfin _ _))
  have σ₁ := (hS a' b').1
  have τ₂ := (hS a b).2.1
  have h₁ : backgroundCoords L k hL (edgesNear L k b'.1.initial (7 / 2)) ⊆
      indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2) := by
    rintro _ ⟨e, c, hc, rfl⟩
    refine Or.inl fun i => ?_
    have := (hc i).1
    show |(c.1.initial : InfiniteLattice.AmbientSpace) i -
      (b'.1.initial : InfiniteLattice.AmbientSpace) i| < 9 / 2
    linarith
  have h₂ : backgroundCoords L k hL (edgesNear L k b.1.initial (7 / 2)) ⊆
      indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2) := by
    rintro _ ⟨e, c, hc, rfl⟩
    exact Or.inr fun i => (hc i).1
  have hcomm : ∀ c : PositiveEdge (meshAt L k 0),
      (∀ i, |(c.1.initial : InfiniteLattice.AmbientSpace) i -
        (b.1.initial : InfiniteLattice.AmbientSpace) i| < 7 / 2) →
      ∀ (e' e₁ e₂ : Fin 3) (x : Vertex L k 0),
        HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
          (indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2))
          (bracketEntry L k hL e' c e₁ x e₂ c) := by
    intro c hc e' e₁ e₂ x
    refine hT.of_subset _ _ ?_ (hE₃ e' e₁ e₂ c c x ρ hρ)
    rintro _ ⟨e, d, hd, rfl⟩
    have hd' : d.1 = c.1 := hd
    refine Or.inr fun i => ?_
    show |(d.1.initial : InfiniteLattice.AmbientSpace) i -
      (b.1.initial : InfiniteLattice.AmbientSpace) i| < 7 / 2
    rw [hd']
    exact hc i
  have hcur : ∀ c : PositiveEdge (meshAt L k 0),
      (∀ i, |(c.1.initial : InfiniteLattice.AmbientSpace) i -
        (b.1.initial : InfiniteLattice.AmbientSpace) i| < 7 / 2) →
      ∀ e : Fin 3, (⟨.source, (e, c)⟩ : FieldIdx L k hL) ∈
        indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2) :=
    fun c hc e => Or.inr hc
  have hs : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → ∀ x,
      gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a' b') x =
        ∑ e, pauliCoeff e (gaugeParam
          (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a' b') x) •
            ComplexMatrix2.pauliFamily e :=
    fun ζ hζ x => eq_sum_pauliCoeff_smul (σ₁.mem_traceless ζ hζ x)
  have hsr := holomorphic_pauliCoeff hT σ₁ h₁
  have hfar : ∀ (i : Fin 4), 6 ≤ |(b.1.initial : InfiniteLattice.AmbientSpace) i -
      (b'.1.initial : InfiniteLattice.AmbientSpace) i| →
      ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ →
      ∀ x : Vertex L k 0,
      |(x : InfiniteLattice.AmbientSpace) i - (b.1.initial : InfiniteLattice.AmbientSpace) i| ≤ 5 →
      gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
        (basisForm a' b') x = 0 := by
    intro i hi ζ hζ x hx
    exact σ₁.eq_zero_of_not_mem ζ hζ x fun hn => not_abs_sub_lt_half hi hx (hn i)
  have hmem : b ∈ positiveEdgesWithin L k b.1.initial (3 / 2) := fun i =>
    ⟨by simp <;> norm_num, by have := abs_terminal_sub_initial_le_one hL b.1 i; linarith⟩
  have hD : ∀ (ζ) (c : PositiveEdge (meshAt L k 0)),
      covDiff (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
        (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
          (basisForm a b)) c.1 =
      shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b) c.1 -
        basisForm a b c.1 := by
    intro ζ c
    simp [shiftedForm]
  have hD₀ : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → ∀ c : PositiveEdge (meshAt L k 0),
      c ∉ positiveEdgesWithin L k b.1.initial (3 / 2) →
      covDiff (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
        (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
          (basisForm a b)) c.1 = 0 := by
    intro ζ hζ c hc
    have e₁ : shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b) c.1 = 0 :=
      τ₂.eq_zero_of_not_mem ζ hζ c hc
    have hne : c ≠ b := fun h => hc (h ▸ hmem)
    rw [hD, e₁, basisForm_apply_of_ne a hne, sub_zero]
  have hsum : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ →
      sourceBracketCovTerm L k hL a' b' a b ζ = ∑ c ∈ τ₂.finite.toFinset,
        ComplexMatrix2.halfTrace (sourceOfCoeffs hL ζ c.1 *
          levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
            (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
              (basisForm a' b'))
            (covDiff (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
              (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
                (basisForm a b))) c.1) := by
    intro ζ hζ
    unfold sourceBracketCovTerm
    rw [edgeFormPairing_eq_finsum]
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    by_contra hn
    refine hc ?_
    have hn' : c ∉ positiveEdgesWithin L k b.1.initial (3 / 2) := by simpa using hn
    beta_reduce
    rw [levelBracketTerm_eq_zero_of_form _ _ c.2 (hD₀ ζ hζ c hn')]
    exact halfTrace_mul_zero _
  have hfirst : ∀ ζ, sourceBracketTerm L k hL a' b' a b ζ =
      2 * ComplexMatrix2.halfTrace (sourceOfCoeffs hL ζ b.1 *
        levelBracketTerm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
          (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
            (basisForm a' b')) (basisForm a b) b.1) := by
    intro ζ
    unfold sourceBracketTerm
    rw [edgeFormPairing_eq_finsum, finsum_eq_single _ b fun c hc => ?_]
    beta_reduce
    rw [levelBracketTerm_eq_zero_of_form _ _ c.2 (basisForm_apply_of_ne a hc)]
    exact halfTrace_mul_zero _
  refine ⟨⟨?_, fun _ => hT.of_subset _ _ ?_ ((hE₁ a' a b' b).2 ρ hρ)⟩, ⟨?_, fun _ => ?_⟩,
    ⟨?_, fun _ => ?_⟩⟩
  · rintro ⟨i, hi⟩ ζ -
    refine (hE₁ a' a b' b).1 ?_ ζ
    rintro ⟨p, g₁, g₂⟩
    have u₁ := initial_sub_corner_bounds hL g₁ i
    have u₂ := initial_sub_corner_bounds hL g₂ i
    have : |(b.1.initial : InfiniteLattice.AmbientSpace) i -
        (b'.1.initial : InfiniteLattice.AmbientSpace) i| ≤ 1 :=
      abs_le.2 ⟨by linarith [u₁.1, u₁.2, u₂.1, u₂.2], by linarith [u₁.1, u₁.2, u₂.1, u₂.2]⟩
    linarith
  · rintro _ ⟨e, c, ⟨p, ⟨d, hd, hdp⟩, hc⟩, rfl⟩
    rcases hd with rfl | hd
    · refine Or.inl fun i => ?_
      have u₁ := initial_sub_corner_bounds hL hdp i
      have u₂ := initial_sub_corner_bounds hL hc i
      show |(c.1.initial : InfiniteLattice.AmbientSpace) i -
        (b'.1.initial : InfiniteLattice.AmbientSpace) i| < 9 / 2
      have : |(c.1.initial : InfiniteLattice.AmbientSpace) i -
          (b'.1.initial : InfiniteLattice.AmbientSpace) i| ≤ 1 :=
        abs_le.2 ⟨by linarith [u₁.1, u₁.2, u₂.1, u₂.2], by linarith [u₁.1, u₁.2, u₂.1, u₂.2]⟩
      linarith
    · have hd' : d = b.1 := hd
      subst hd'
      refine Or.inr fun i => ?_
      have u₁ := initial_sub_corner_bounds hL hdp i
      have u₂ := initial_sub_corner_bounds hL hc i
      show |(c.1.initial : InfiniteLattice.AmbientSpace) i -
        (b.1.initial : InfiniteLattice.AmbientSpace) i| < 7 / 2
      have : |(c.1.initial : InfiniteLattice.AmbientSpace) i -
          (b.1.initial : InfiniteLattice.AmbientSpace) i| ≤ 1 :=
        abs_le.2 ⟨by linarith [u₁.1, u₁.2, u₂.1, u₂.2], by linarith [u₁.1, u₁.2, u₂.1, u₂.2]⟩
      linarith
  · rintro ⟨i, hi⟩ ζ hζ
    rw [hfirst, levelBracketTerm_eq_zero_of_vertices _ _ b.2 (hfar i hi ζ hζ _ (by simp))
      (hfar i hi ζ hζ _ (by have := abs_terminal_sub_initial_le_one hL b.1 i; linarith)),
      halfTrace_mul_zero, mul_zero]
  · refine hT.congr_below _ _ (fun ζ _ => (hfirst ζ).symm) (hT.mul _ _ (hT.const 2) ?_)
    exact holomorphic_halfTrace_source_mul_bracket hT b (hcomm b fun i => by simp <;> norm_num)
      (hcur b fun i => by simp <;> norm_num)
      (s := fun e x ζ => pauliCoeff e (gaugeParam
        (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a' b') x))
      (t := fun e _ => pauliCoeff e (basisForm a b b.1))
      hs (fun e x => hsr e x) (fun _ _ => eq_sum_pauliCoeff_smul (basisForm_mem_traceless a b b))
      (fun e => hT.const _)
  · rintro ⟨i, hi⟩ ζ hζ
    rw [hsum ζ hζ]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' : c ∈ positiveEdgesWithin L k b.1.initial (3 / 2) := by simpa using hc
    rw [levelBracketTerm_eq_zero_of_vertices _ _ c.2 (hfar i hi ζ hζ _ (by have := (hc' i).1; linarith))
      (hfar i hi ζ hζ _ (by have := (hc' i).2; linarith))]
    exact halfTrace_mul_zero _
  · refine hT.congr_below _ _ (fun ζ hζ => (hsum ζ hζ).symm) (hT.sum _ _ fun c hc => ?_)
    have hc' : c ∈ positiveEdgesWithin L k b.1.initial (3 / 2) := by simpa using hc
    have hnear : ∀ i, |(c.1.initial : InfiniteLattice.AmbientSpace) i -
        (b.1.initial : InfiniteLattice.AmbientSpace) i| < 7 / 2 := fun i => by
      have := (hc' i).1
      linarith
    exact holomorphic_halfTrace_source_mul_bracket hT c (hcomm c hnear) (hcur c hnear)
      (s := fun e x ζ => pauliCoeff e (gaugeParam
        (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a' b') x))
      (t := fun e ζ => pauliCoeff e (shiftedForm
        (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b) c.1) +
          -pauliCoeff e (basisForm a b c.1))
      hs (fun e x => hsr e x)
      (fun ζ hζ => by
        have e₁ : shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
            (basisForm a b) c.1 = _ := eq_sum_pauliCoeff_smul (τ₂.mem_traceless ζ hζ c)
        have e₂ := eq_sum_pauliCoeff_smul (basisForm_mem_traceless a b c)
        rw [hD]
        simp only [add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
        rw [← e₂, sub_eq_add_neg]
        exact congrArg (· + -basisForm a b c.1) e₁)
      (fun e => hT.add _ _ (holomorphic_pauliCoeff hT τ₂ h₂ e c) (hT.const _))
end YangMills.Construction.Tower.FullSpace.KernelTermsLocality
end
