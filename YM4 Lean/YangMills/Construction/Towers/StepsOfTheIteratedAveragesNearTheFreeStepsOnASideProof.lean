import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheFreeStepProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.SmoothingStepsNearFree
open Matrices
open Conventions (IsAdmissibleBlockingFactor)
open PeriodicOperators (wOpNorm OpNormSummable wNorm NormSummable wUnitBall)
open StepKernels
open NearIdentityStepKernels (doubleBlockDistToOne)
section Sums
theorem finset_card_le_of_subset_encard {α : Type} {q : α → Prop} {S : Set α} {N : ℕ}
    (F : Finset {x // q x}) (hF : ∀ x ∈ F, x.1 ∈ S) (h : S.encard ≤ N) : F.card ≤ N := by apply _root_.YangMills.SharedProofs.p8419 <;> assumption
theorem finsum_mem_eq_sum_filter_subtype {α : Type} [Finite α] {q : α → Prop}
    [Fintype {x // q x}] (S : Set α) (hS : ∀ x ∈ S, q x) (φ : α → ComplexMatrix2) :
    open Classical in
    ∑ᶠ e ∈ S, φ e = ∑ p ∈ Finset.univ.filter (fun p : {x // q x} => p.1 ∈ S), φ p.1 := by apply _root_.YangMills.SharedProofs.p107629 <;> assumption
end Sums
section Norms
variable {σ σ' : Type}
theorem normSummable_of_finite [Finite σ] (w : Fin 3 × σ → ℝ) (f : Fin 3 × σ → ℂ) :
    NormSummable w f := by apply _root_.YangMills.SharedProofs.p57614 <;> assumption
theorem mapNormLE_of_bound {r r' : PauliComponentsOfSymmetricKernel} (hfin : Finite r'.Place) {a a' c : ℝ}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2} (hc : 0 ≤ c)
    (hb : ∀ f, wNorm (meshWeight a') (r.mapOnCoeffs r' m f) ≤
      c * wNorm (meshWeight a) f) :
    MapNormLE a a' r r' m c := by
  refine ⟨fun f _ => normSummable_of_finite _ _, iSup₂_le fun f hf => ?_⟩
  exact ENNReal.ofReal_le_ofReal
    ((hb f).trans ((mul_le_mul_of_nonneg_left hf.2.2 hc).trans (by simp)))
open Classical in
theorem wNorm_le_of_local_bound [Fintype σ] [Fintype σ'] {a a' κ N M c : ℝ}
    (T : σ' → Finset σ) (f : Fin 3 × σ → ℂ) (F : σ → ComplexMatrix2) (G : σ' → ComplexMatrix2)
    (hF : ∀ x, pauliNorm (F x) ^ 2 = ∑ i, ‖f (i, x)‖ ^ 2) (hc : 0 ≤ c) (hN0 : 0 ≤ N)
    (hN : ∀ y, ((T y).card : ℝ) ≤ N)
    (hM : ∀ x, (((Finset.univ.filter fun y => x ∈ T y).card : ℕ) : ℝ) ≤ M)
    (hb : ∀ y, pauliNorm (G y) ≤ κ * ∑ x ∈ T y, pauliNorm (F x))
    (hnum : a' ^ 4 * (κ ^ 2 * N * M) ≤ c ^ 2 * a ^ 4) :
    wNorm (meshWeight a') (toPauliCoeffs G) ≤ c * wNorm (meshWeight a) f := by apply _root_.YangMills.SharedProofs.p19244 <;> assumption
end Norms
section Coefficients
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem pauliNorm_ofPauliCoeffs_sq {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    pauliNorm (ofPauliCoeffs c x) ^ 2 = ∑ i, ‖c (i, x)‖ ^ 2 := by apply _root_.YangMills.SharedProofs.p49452 <;> assumption
theorem real_smul_eq_complex_smul (t : ℝ) (X : ComplexMatrix2) : t • X = (t : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
end Coefficients
structure Hypotheses : Prop where
  nearIdentity : NearIdentityStepKernels.StepKernelNearIdentityBound
  kernelBounds : StepKernels.StepKernelBounds
  blockGeometry : BlockPathContourPivotStatement
  coeffNorm : PauliCoefficientNorm.Claim
  trivialSteps : RescaledTrivialSteps
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteEdges : BondSetFields.ProductStructureHolds
section Tower
variable {L n k j : ℕ}
theorem edge_xor_opposite (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {i : ℕ} (hi : i ≤ k) (e : Edge L n k i) :
    Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented :=
  ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 e).2.2.2.2.2
theorem finite_edge (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ}
    (hi : i ≤ k) : Finite (Edge L n k i) :=
  Set.finite_univ_iff.1 ((G.finiteEdges L hL k i hi).1 n hn).2.1
theorem finite_vertex (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ}
    (hi : i ≤ k) : Finite (Vertex L n k i) :=
  have := finite_edge G hL hn hi
  Finite.of_injective (fun x : Vertex L n k i => PeriodicLattice.Bond.forwardFrom x 0)
    fun _ _ h => congrArg PeriodicLattice.Bond.source h
theorem ofCoeffs_edge_of_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {e : Edge L n k j}
    (h : e.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c e = ofPauliCoeffs c ⟨e, h⟩ := by apply _root_.YangMills.SharedProofs.p19922 <;> assumption
theorem ofCoeffs_edge_mem
    (hx : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j := by apply _root_.YangMills.SharedProofs.p1053 <;> assumption
theorem meshAt_succ (hL : IsAdmissibleBlockingFactor L) (k m : ℕ) :
    meshAt L k (m + 1) = L * meshAt L k m := by apply _root_.YangMills.SharedProofs.p23229 <;> assumption
theorem distFromOne_nonneg (V : Edge L n k j → ComplexMatrix2) : 0 ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V :=
  ENNReal.toReal_nonneg
theorem operatorNorm_sub_one_le_distFromOne {V : Edge L n k j → ComplexMatrix2} {ρ : ℝ}
    (hV : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < ρ) (e : Edge L n k j) :
    ComplexMatrix2.operatorNorm (V e - 1) ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by apply _root_.YangMills.SharedProofs.p53627 <;> assumption
theorem doubleBlockDistToOne_le {V : Edge L n k j → ComplexMatrix2} {ρ : ℝ}
    (hV : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < ρ) (c : Edge L n k (j + 1)) :
    doubleBlockDistToOne V c ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by
  refine Real.sSup_le ?_ (_root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne_nonneg V)
  rintro _ ⟨e, _, rfl⟩
  exact operatorNorm_sub_one_le_distFromOne hV e
theorem polydiscRadius_pos_of_near {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2) :
    0 < polydiscRadius L := by apply _root_.YangMills.SharedProofs.p94894 <;> assumption
theorem one_mem_fieldsIn : (fun _ => 1 : Edge L n k j → ComplexMatrix2) ∈
    fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p71645 <;> assumption
end Tower
section Numbers
theorem edge_constant_ineq {l a D s : ℝ} (hl : 0 < l) :
    (l * a) ^ 4 * ((l⁻¹ * (D * s * Real.sqrt 2)) ^ 2 * (8 * l ^ 4) * 8) ≤
      ((12 * l ^ 3 + 2) * (2 * D) * s) ^ 2 * a ^ 4 := by apply _root_.YangMills.SharedProofs.p115257 <;> assumption
theorem vertex_constant_ineq {l a D s : ℝ} (hl : 1 ≤ l) :
    (l * a) ^ 4 * (((l ^ 4)⁻¹ * (D * s * Real.sqrt 2)) ^ 2 * l ^ 4 * 1) ≤
      ((12 * l ^ 3 + 2) * (2 * D) * s) ^ 2 * a ^ 4 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e₁ : (l * a) ^ 4 * (((l ^ 4)⁻¹ * (D * s * Real.sqrt 2)) ^ 2 * l ^ 4 * 1) =
      2 * ((D * s) ^ 2 * a ^ 4) := by
    rw [mul_pow (l ^ 4)⁻¹, mul_pow (D * s), h2]
    field_simp
  have e₂ : ((12 * l ^ 3 + 2) * (2 * D) * s) ^ 2 * a ^ 4 =
      ((12 * l ^ 3 + 2) ^ 2 * 4) * ((D * s) ^ 2 * a ^ 4) := by ring
  rw [e₁, e₂]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h₃ : 0 < l ^ 3 := by positivity
  nlinarith [sq_nonneg (l ^ 3)]
theorem norm_inverseFourthPowerWeight {L : ℕ} (h : 0 < (L : ℝ)) :
    ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
  unfold PeriodicLattice.inverseFourthPowerWeight
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), zpow_neg]
  norm_cast
end Numbers
section Values
variable {L n k j : ℕ}
open Classical in
def doubleBlockPlaces [Fintype (PositiveEdge L n k j)] (c : Edge L n k (j + 1)) :
    Finset (PositiveEdge L n k j) :=
  Finset.univ.filter fun p => p.1 ∈ positiveDoubleBlockEdges c
open Classical in
theorem mem_doubleBlockPlaces [Fintype (PositiveEdge L n k j)] {c : Edge L n k (j + 1)}
    {p : PositiveEdge L n k j} :
    p ∈ doubleBlockPlaces c ↔ p.1 ∈ positiveDoubleBlockEdges c :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
def blockPlaces [Finite (Vertex L n k j)] (y : Vertex L n k (j + 1)) :
    Finset (Vertex L n k j) :=
  (Set.toFinite (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)).toFinset
theorem edge_difference_bound (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) [Finite (Edge L n k j)] [Fintype (PositiveEdge L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hs : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    pauliNorm ((L : ℝ)⁻¹ •
        (covariantSmoothingDeriv V B c - crossingSmoothing L n k j B c)) ≤
      (L : ℝ)⁻¹ * (1280 * (polydiscRadius L)⁻¹ ^ 2 * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * Real.sqrt 2) *
        ∑ p ∈ doubleBlockPlaces c, pauliNorm (B p.1) := by
  have hk : 1 ≤ k := by omega
  have hρ := polydiscRadius_pos_of_near hs
  have hL0 : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
  have hsmall : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < 3 / 4 * polydiscRadius L :=
    fun e => (hs e).trans (by linarith)
  have hone : ∀ e, ComplexMatrix2.operatorNorm
      ((fun _ => 1 : Edge L n k j → ComplexMatrix2) e - 1) < 3 / 4 * polydiscRadius L :=
    fun e => by
      have : (0 : ℝ) < 3 / 4 * polydiscRadius L := by linarith
      simpa using this
  obtain ⟨hV₁, hV₂, -⟩ := G.kernelBounds L hL n k j hn hj c hc V hV hsmall
  obtain ⟨hO₁, hO₂, -⟩ := G.kernelBounds L hL n k j hn hj c hc _ one_mem_fieldsIn hone
  have hnear := (G.nearIdentity L hL n k j hn hj c hc V hV hs).1
  have hcr : crossingSmoothing L n k j B c =
      covariantSmoothingDeriv (fun _ => 1 : Edge L n k j → ComplexMatrix2) B c :=
    (congrFun (((((G.trivialSteps L hL k hk n hn).2 j hj).2.2.2.2.1) B hB).2.2) c).symm
  have hsum : ∀ φ : Edge L n k j → ComplexMatrix2,
      ∑ᶠ e ∈ positiveDoubleBlockEdges c, φ e = ∑ p ∈ doubleBlockPlaces c, φ p.1 := fun φ =>
    finsum_mem_eq_sum_filter_subtype (positiveDoubleBlockEdges c) (fun _ h => h.2) φ
  have hplace : ∀ p ∈ doubleBlockPlaces c, p.1 ∈ positiveDoubleBlockEdges c :=
    fun p hp => mem_doubleBlockPlaces.1 hp
  have hval : ∀ p : PositiveEdge L n k j, B p.1 ∈ ComplexMatrix2.traceless :=
    fun p => hB.1 p.1 p.2
  rw [hV₁ B hB, hcr, hO₁ B hB, hsum, hsum, ← Finset.sum_sub_distrib, real_smul_eq_complex_smul]
  have hX : ∑ p ∈ doubleBlockPlaces c, (stepKernel V c p.1 (B p.1) -
      stepKernel (fun _ => 1) c p.1 (B p.1)) ∈ ComplexMatrix2.traceless :=
    Submodule.sum_mem _ fun p hp => ComplexMatrix2.traceless.sub_mem
      ((hV₂ p.1 (hplace p hp)).mapsTo _ (hval p))
      ((hO₂ p.1 (hplace p hp)).mapsTo _ (hval p))
  refine ((G.coeffNorm.2.1.1 ⟨_, ComplexMatrix2.traceless.smul_mem _ hX⟩).1).trans ?_
  show ‖(((L : ℝ)⁻¹ : ℝ) : ℂ) • ∑ p ∈ doubleBlockPlaces c, (stepKernel V c p.1 (B p.1) -
      stepKernel (fun _ => 1) c p.1 (B p.1))‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hL0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL0
  have hD0 : 0 ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 := by positivity
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have h₁ := hnear p.1 (hplace p hp) (B p.1) (hval p)
  have h₂ : ComplexMatrix2.operatorNorm (B p.1) ≤ Real.sqrt 2 * pauliNorm (B p.1) :=
    (G.coeffNorm.2.1.1 ⟨_, hval p⟩).2
  have h₃ := doubleBlockDistToOne_le hs c
  calc _ ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 * doubleBlockDistToOne V c *
        ComplexMatrix2.operatorNorm (B p.1) := h₁
    _ ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 * distFromOne V *
        (Real.sqrt 2 * pauliNorm (B p.1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h₃ hD0) h₂ (norm_nonneg _)
        (mul_nonneg hD0 (distFromOne_nonneg V))
    _ = _ := by ring
theorem vertex_difference_bound (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hs : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2)
    {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.traceless)
    (y : Vertex L n k (j + 1)) :
    pauliNorm (adjointCubeAverage V l y - vertexSmoothing L n k j l y) ≤
      ‖PeriodicLattice.inverseFourthPowerWeight L‖ *
          (1280 * (polydiscRadius L)⁻¹ ^ 2 * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * Real.sqrt 2) *
        ∑ x ∈ blockPlaces y, pauliNorm (l x) := by
  have hρ := polydiscRadius_pos_of_near hs
  have hsmall : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < 3 / 4 * polydiscRadius L :=
    fun e => (hs e).trans (by linarith)
  obtain ⟨c, hc, hy⟩ : ∃ c : Edge L n k (j + 1), c.IsPositivelyOriented ∧ c.source = y :=
    ⟨PeriodicLattice.Bond.forwardFrom y 0, ⟨0, add_sub_cancel_left _ _⟩, rfl⟩
  have hyc : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) := Or.inl hy.symm
  obtain ⟨-, -, hAd⟩ := G.kernelBounds L hL n k j hn hj c hc V hV hsmall
  have hnear := (G.nearIdentity L hL n k j hn hj c hc V hV hs).2 y hyc
  have hplace : ∀ x ∈ blockPlaces y,
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :=
    fun x hx => (Set.Finite.mem_toFinset _).1 hx
  have e₁ : adjointCubeAverage V l y = PeriodicLattice.inverseFourthPowerWeight L •
      ∑ x ∈ blockPlaces y, ComplexMatrix2.conjugateBy
        (PeriodicLattice.complexMeanContourHolonomy V y x) (l x) := by
    unfold adjointCubeAverage
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
    rfl
  have e₂ : vertexSmoothing L n k j l y = PeriodicLattice.inverseFourthPowerWeight L •
      ∑ x ∈ blockPlaces y, l x := by
    unfold vertexSmoothing
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
    rfl
  rw [e₁, e₂, ← smul_sub, ← Finset.sum_sub_distrib]
  have hX : ∑ x ∈ blockPlaces y, (ComplexMatrix2.conjugateBy
      (PeriodicLattice.complexMeanContourHolonomy V y x) (l x) - l x) ∈
        ComplexMatrix2.traceless :=
    Submodule.sum_mem _ fun x hx =>
      ComplexMatrix2.traceless.sub_mem ((hAd y hyc x (hplace x hx)).mapsTo _ (hl x)) (hl x)
  refine ((G.coeffNorm.2.1.1 ⟨_, ComplexMatrix2.traceless.smul_mem _ hX⟩).1).trans ?_
  show ‖PeriodicLattice.inverseFourthPowerWeight L • ∑ x ∈ blockPlaces y,
      (ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x) -
        l x)‖ ≤ _
  rw [norm_smul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hD0 : 0 ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 := by positivity
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have h₁ := hnear x (hplace x hx) (l x) (hl x)
  have h₂ : ComplexMatrix2.operatorNorm (l x) ≤ Real.sqrt 2 * pauliNorm (l x) :=
    (G.coeffNorm.2.1.1 ⟨_, hl x⟩).2
  have h₃ := doubleBlockDistToOne_le hs c
  calc _ ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 * doubleBlockDistToOne V c *
        ComplexMatrix2.operatorNorm (l x) := h₁
    _ ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 * distFromOne V *
        (Real.sqrt 2 * pauliNorm (l x)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h₃ hD0) h₂ (norm_nonneg _)
        (mul_nonneg hD0 (distFromOne_nonneg V))
    _ = _ := by ring
end Values
section Parts
variable {L n k j : ℕ}
theorem smoothingStepConstant_mul (L : ℕ) (s : ℝ) :
    smoothingStepConstant L * s = (12 * (L : ℝ) ^ 3 + 2) *
      (2 * (1280 * (polydiscRadius L)⁻¹ ^ 2)) * s := by
  unfold smoothingStepConstant
  ring
theorem one_le_factor (hL : IsAdmissibleBlockingFactor L) : (1 : ℝ) ≤ L := by
  have := hL.2
  have h : 1 ≤ L := by omega
  exact_mod_cast h
theorem smoothingStepConstant_mul_nonneg (hL : IsAdmissibleBlockingFactor L)
    (V : Edge L n k j → ComplexMatrix2) : 0 ≤ smoothingStepConstant L * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by
  rw [smoothingStepConstant_mul]
  have := _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne_nonneg V
  have h := one_le_factor hL
  positivity
theorem edge_part_bound (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hs : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2)
    (f : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
        ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
          (fun B => (L : ℝ)⁻¹ • (covariantSmoothingDeriv V B - crossingSmoothing L n k j B)) f) ≤
      smoothingStepConstant L * distFromOne V * wNorm (meshWeight (meshAt L k j)) f := by
  classical
  have hk : 1 ≤ k := by omega
  have hl := one_le_factor hL
  have hl0 : (0 : ℝ) < L := by linarith
  have he₀ : Finite (Edge L n k j) := finite_edge G hL hn hj.le
  have he₁ : Finite (Edge L n k (j + 1)) := finite_edge G hL hn hj
  let _ : Fintype (PositiveEdge L n k j) :=
    @Fintype.ofFinite _
      (inferInstanceAs (Finite {e : Edge L n k j // e.IsPositivelyOriented}))
  let _ : Fintype (PositiveEdge L n k (j + 1)) :=
    @Fintype.ofFinite _
      (inferInstanceAs (Finite {e : Edge L n k (j + 1) // e.IsPositivelyOriented}))
  obtain ⟨B, hBe⟩ : ∃ B, B = (edgePauliCoordinates L n k j).ofCoeffs f := ⟨_, rfl⟩
  have hB : B ∈ complexEdgeForms L n k j := by
    rw [hBe]
    exact ofCoeffs_edge_mem (edge_xor_opposite G hL hn hk hj.le) f
  have hBv : ∀ p : PositiveEdge L n k j, B p.1 = ofPauliCoeffs f p := fun p => by
    rw [hBe]
    exact ofCoeffs_edge_of_pos f p.2
  have hsb := ((G.blockGeometry L hL k 1 (j + 1) hk (by omega) hj).1 n hn).2.2.2.2.1
  have key := wNorm_le_of_local_bound (a := meshAt L k j) (a' := meshAt L k (j + 1))
    (κ := (L : ℝ)⁻¹ *
      (1280 * (polydiscRadius L)⁻¹ ^ 2 * distFromOne V * Real.sqrt 2))
    (N := 8 * (L : ℝ) ^ 4) (M := 8) (c := smoothingStepConstant L * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V)
    (fun c : PositiveEdge L n k (j + 1) => doubleBlockPlaces c.1) f
    (fun p => B p.1)
    (fun c : PositiveEdge L n k (j + 1) => (L : ℝ)⁻¹ •
      (covariantSmoothingDeriv V B c.1 - crossingSmoothing L n k j B c.1))
    (fun p => by
      rw [hBv p]
      exact pauliNorm_ofPauliCoeffs_sq f p)
    (smoothingStepConstant_mul_nonneg hL V) (by positivity) ?_ ?_
    (fun c => edge_difference_bound G hL hn hj hV hs hB c.2) ?_
  · rw [hBe] at key
    exact key
  · intro c
    have h : (doubleBlockPlaces (L := L) (n := n) (k := k) (j := j) c.1).card ≤
        8 * L ^ (4 * 1) := by
      refine finset_card_le_of_subset_encard
        (q := fun e : Edge L n k j => e.IsPositivelyOriented) _ (fun p hp => ?_)
        (hsb.bonds_encard_le c.1 c.2)
      have hp' := mem_doubleBlockPlaces.1 hp
      exact ⟨p.2, hp'.1.1, hp'.1.2⟩
    have h' : ((doubleBlockPlaces (L := L) (n := n) (k := k) (j := j) c.1).card : ℝ) ≤
        ((8 * L ^ (4 * 1) : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  · intro p
    have h : ∀ F : Finset (PositiveEdge L n k (j + 1)),
        (∀ c ∈ F, p ∈ doubleBlockPlaces c.1) → (F.card : ℝ) ≤ 8 := by
      intro F hF
      have h₁ : F.card ≤ 8 := by
        refine finset_card_le_of_subset_encard
          (q := fun e : Edge L n k (j + 1) => e.IsPositivelyOriented) F
          (fun c hc => ?_) (by simpa using hsb.encard_le_eight p.1)
        have hc' := mem_doubleBlockPlaces.1 (hF c hc)
        exact ⟨c.2, hc'.1.1, hc'.1.2⟩
      exact_mod_cast h₁
    exact h _ fun c hc => by simpa using hc
  · rw [meshAt_succ hL, smoothingStepConstant_mul]
    exact edge_constant_ineq hl0
theorem vertex_part_bound (G : Hypotheses) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hs : ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2)
    (f : (vertexCoordinate (Vertex L n k j)).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
        ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs (vertexCoordinate (Vertex L n k (j + 1)))
          (fun l => adjointCubeAverage V l - vertexSmoothing L n k j l) f) ≤
      smoothingStepConstant L * distFromOne V * wNorm (meshWeight (meshAt L k j)) f := by
  classical
  have hk : 1 ≤ k := by omega
  have hl := one_le_factor hL
  have hl0 : (0 : ℝ) < L := by linarith
  have hv₀ : Finite (Vertex L n k j) := finite_vertex G hL hn hj.le
  have hv₁ : Finite (Vertex L n k (j + 1)) := finite_vertex G hL hn hj
  let _ : Fintype (Vertex L n k j) := Fintype.ofFinite _
  let _ : Fintype (Vertex L n k (j + 1)) := Fintype.ofFinite _
  have hbl := ((G.blockGeometry L hL k 1 (j + 1) hk (by omega) hj).1 n hn).1
  have key := wNorm_le_of_local_bound (a := meshAt L k j) (a' := meshAt L k (j + 1))
    (κ := ‖PeriodicLattice.inverseFourthPowerWeight L‖ *
      (1280 * (polydiscRadius L)⁻¹ ^ 2 * distFromOne V * Real.sqrt 2))
    (N := (L : ℝ) ^ 4) (M := 1) (c := smoothingStepConstant L * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V)
    (fun y : Vertex L n k (j + 1) => blockPlaces y) f
    (ofPauliCoeffs f)
    (fun y => adjointCubeAverage V (ofPauliCoeffs f) y -
      vertexSmoothing L n k j (ofPauliCoeffs f) y)
    (pauliNorm_ofPauliCoeffs_sq f)
    (smoothingStepConstant_mul_nonneg hL V) (by positivity) ?_ ?_
    (vertex_difference_bound G hL hn hj hV hs (ofPauliCoeffs_mem_traceless f)) ?_
  · exact key
  · intro y
    have hpos : 0 < (PeriodicLattice.refinedBlock 1 y).ncard := by
      rw [hbl.ncard_eq y]
      have : 0 < L := by exact_mod_cast hl0
      positivity
    have hfin := Set.finite_of_ncard_pos hpos
    have hinj : Set.InjOn (fun x : Vertex L n k j => (x : PeriodicLattice.FourTorus L n))
        (blockPlaces y : Finset (Vertex L n k j)) := fun _ _ _ _ h => Subtype.ext h
    have h₁ : ((blockPlaces y).image
        (fun x : Vertex L n k j => (x : PeriodicLattice.FourTorus L n))).card =
          (blockPlaces y).card :=
      Finset.card_image_of_injOn hinj
    have h₂ : (((blockPlaces y).image
        (fun x : Vertex L n k j => (x : PeriodicLattice.FourTorus L n)) : Finset _) :
          Set (PeriodicLattice.FourTorus L n)).ncard ≤
            (PeriodicLattice.refinedBlock 1 y).ncard := by
      refine Set.ncard_le_ncard ?_ hfin
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
      exact show x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y from
        (Set.Finite.mem_toFinset _).1 hx
    rw [Set.ncard_coe_finset, h₁, hbl.ncard_eq y] at h₂
    have h₃ : ((blockPlaces (L := L) (n := n) (k := k) (j := j) y).card : ℝ) ≤
        ((L ^ (4 * 1) : ℕ) : ℝ) := by exact_mod_cast h₂
    simpa using h₃
  · intro x
    have h : ∀ F : Finset (Vertex L n k (j + 1)), (∀ y ∈ F, x ∈ blockPlaces y) →
        (F.card : ℝ) ≤ 1 := by
      intro F hF
      have h₀ : F.card ≤ 1 := by
        refine Finset.card_le_one.2 fun y hy y' hy' => ?_
        have h₁ : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :=
          (Set.Finite.mem_toFinset _).1 (hF y hy)
        have h₂ : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y' :=
          (Set.Finite.mem_toFinset _).1 (hF y' hy')
        exact (hbl.existsUnique_mem x).unique h₁ h₂
      exact_mod_cast h₀
    exact h _ fun y hy => by simpa using hy
  · rw [meshAt_succ hL, smoothingStepConstant_mul, norm_inverseFourthPowerWeight hl0]
    exact vertex_constant_ineq hl
end Parts
theorem claim_holds (near : NearIdentityStepKernels.StepKernelNearIdentityBound)
    (kernels : StepKernels.StepKernelBounds)
    (blocks : BlockPathContourPivotStatement)
    (coeffs : PauliCoefficientNorm.Claim)
    (steps : RescaledTrivialSteps)
    (orientation : PeriodicLattice.BondEndpointsOrientation.Statement)
    (finiteEdges : BondSetFields.ProductStructureHolds) : Claim := by
  intro L hL n k j hn hj V hV hs
  have G : Hypotheses := ⟨near, kernels, blocks, coeffs, steps, orientation, finiteEdges⟩
  have hc := smoothingStepConstant_mul_nonneg hL V
  have he₁ : Finite (Edge L n k (j + 1)) := finite_edge G hL hn hj
  refine ⟨mapNormLE_of_bound
      (inferInstanceAs (Finite {e : Edge L n k (j + 1) // e.IsPositivelyOriented})) hc
      (edge_part_bound G hL hn hj hV hs),
    mapNormLE_of_bound (finite_vertex G hL hn hj) hc (vertex_part_bound G hL hn hj hV hs)⟩
end YangMills.Construction.Tower.SmoothingStepsNearFree
end
