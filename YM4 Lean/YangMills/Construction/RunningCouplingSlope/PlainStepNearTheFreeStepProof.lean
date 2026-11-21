import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheCovariantStep
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.StepKernelsNearOneOnASide
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set Filter Metric
open scoped Topology ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanStepNearFree
open Conventions Matrices Tower PeriodicOperators
open SmoothingStepsNearFree (MapNormLE distFromOne)
open StepKernels (positiveDoubleBlockEdges stepKernel)
open NearIdentityStepKernels (doubleBlockDistToOne)
section Sums
variable {P P' : Type}
open Classical in
private theorem sum_sq_le_of_cover [Fintype P] [Fintype P'] (T : P' → Finset P) {N M κ : ℝ}
    (u : P → ℝ) (v : P' → ℝ) (hv : ∀ p', 0 ≤ v p') (hN0 : 0 ≤ N)
    (hN : ∀ p', ((T p').card : ℝ) ≤ N)
    (hM : ∀ p, (((Finset.univ.filter fun p' => p ∈ T p').card : ℕ) : ℝ) ≤ M)
    (hb : ∀ p', v p' ≤ κ * ∑ p ∈ T p', u p) :
    ∑ p', v p' ^ 2 ≤ κ ^ 2 * N * M * ∑ p, u p ^ 2 := by
  have h₁ : ∀ p', v p' ^ 2 ≤ κ ^ 2 * N * ∑ p ∈ T p', u p ^ 2 := by
    intro p'
    have e₁ : v p' ^ 2 ≤ (κ * ∑ p ∈ T p', u p) ^ 2 := pow_le_pow_left₀ (hv p') (hb p') 2
    have e₂ : (∑ p ∈ T p', u p) ^ 2 ≤ ((T p').card : ℝ) * ∑ p ∈ T p', u p ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have e₃ : 0 ≤ ∑ p ∈ T p', u p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have e₄ : ((T p').card : ℝ) * ∑ p ∈ T p', u p ^ 2 ≤ N * ∑ p ∈ T p', u p ^ 2 :=
      mul_le_mul_of_nonneg_right (hN p') e₃
    calc v p' ^ 2 ≤ κ ^ 2 * (∑ p ∈ T p', u p) ^ 2 := by rw [← mul_pow]; exact e₁
      _ ≤ κ ^ 2 * (N * ∑ p ∈ T p', u p ^ 2) :=
        mul_le_mul_of_nonneg_left (e₂.trans e₄) (sq_nonneg _)
      _ = _ := by ring
  have h₂ : ∑ p', ∑ p ∈ T p', u p ^ 2 ≤ M * ∑ p, u p ^ 2 := by
    have e : ∑ p', ∑ p ∈ T p', u p ^ 2 =
        ∑ p, ((Finset.univ.filter fun p' => p ∈ T p').card : ℝ) * u p ^ 2 := by
      rw [Finset.sum_comm' (t' := Finset.univ)
        (s' := fun p => Finset.univ.filter fun p' => p ∈ T p')]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
      · intro x y
        simp
    rw [e, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hM p) (sq_nonneg _)
  calc ∑ p', v p' ^ 2 ≤ ∑ p', κ ^ 2 * N * ∑ p ∈ T p', u p ^ 2 :=
        Finset.sum_le_sum fun p' _ => h₁ p'
    _ = κ ^ 2 * N * ∑ p', ∑ p ∈ T p', u p ^ 2 := by rw [Finset.mul_sum]
    _ ≤ κ ^ 2 * N * (M * ∑ p, u p ^ 2) :=
        mul_le_mul_of_nonneg_left h₂ (mul_nonneg (sq_nonneg _) hN0)
    _ = _ := by ring
private theorem finset_card_le_of_encard {α : Type} {q : α → Prop} {S : Set α} {N : ℕ}
    (F : Finset {x // q x}) (hF : ∀ x ∈ F, x.1 ∈ S) (h : S.encard ≤ N) : F.card ≤ N := by
  classical
  have e : ((F.map (Function.Embedding.subtype q) : Finset α) : Set α).encard ≤ S.encard := by
    refine Set.encard_le_encard ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hx)
    exact hF y hy
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_map] at e
  exact_mod_cast e.trans h
abbrev _root_.YangMills.SharedProofs.p8419 := @finset_card_le_of_encard
private theorem finsum_mem_eq_subtype_sum {α : Type} [Finite α] {q : α → Prop} [Fintype {x // q x}]
    (S : Set α) (hS : ∀ x ∈ S, q x) (φ : α → ComplexMatrix2) :
    open Classical in
    ∑ᶠ b ∈ S, φ b = ∑ p ∈ Finset.univ.filter (fun p : {x // q x} => p.1 ∈ S), φ p.1 := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ S.toFinite]
  symm
  refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    exact (Set.Finite.mem_toFinset _).2 (Finset.mem_filter.1 hp).2
  · intro p _ p' _ h
    exact Subtype.ext h
  · intro b hb
    have hb' := (Set.Finite.mem_toFinset _).1 hb
    exact ⟨⟨b, hS b hb'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hb'⟩, rfl⟩
  · intro _ _
    rfl
abbrev _root_.YangMills.SharedProofs.p107629 := @finsum_mem_eq_subtype_sum
end Sums
section Norms
variable {σ σ' : Type}
private theorem wNorm_meshWeight_sq [Fintype σ] (a : ℝ) (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) f ^ 2 = a ^ 4 * ∑ x, ∑ i, ‖f (i, x)‖ ^ 2 := by
  unfold wNorm
  rw [Real.sq_sqrt, tsum_fintype, Fintype.sum_prod_type_right, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    rfl
  · refine tsum_nonneg fun i => mul_nonneg ?_ (sq_nonneg _)
    show 0 ≤ a ^ 4
    positivity
private theorem normSummable_of_finite [Finite σ] (w : Fin 3 × σ → ℝ) (f : Fin 3 × σ → ℂ) :
    NormSummable w f := by apply _root_.YangMills.SharedProofs.p57614 <;> assumption
private theorem mapNormLE_of_bound {r r' : PauliComponentsOfSymmetricKernel} (hfin : Finite r'.Place) {a a' c : ℝ}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2} (hc : 0 ≤ c)
    (hb : ∀ f, wNorm (meshWeight a') (r.mapOnCoeffs r' m f) ≤
      c * wNorm (meshWeight a) f) :
    MapNormLE a a' r r' m c := by
  refine ⟨fun f _ => normSummable_of_finite _ _, iSup₂_le fun f hf => ?_⟩
  exact ENNReal.ofReal_le_ofReal
    ((hb f).trans ((mul_le_mul_of_nonneg_left hf.2.2 hc).trans (by simp)))
private theorem pauliNorm_sq (X : ComplexMatrix2) : pauliNorm X ^ 2 = ∑ a, ‖pauliCoeff a X‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
open Classical in
private theorem wNorm_le_of_local [Fintype σ] [Fintype σ'] {a a' κ N M c : ℝ} (T : σ' → Finset σ)
    (f : Fin 3 × σ → ℂ) (F : σ → ComplexMatrix2) (G : σ' → ComplexMatrix2)
    (hF : ∀ x, pauliNorm (F x) ^ 2 = ∑ i, ‖f (i, x)‖ ^ 2) (hc : 0 ≤ c) (hN0 : 0 ≤ N)
    (hN : ∀ y, ((T y).card : ℝ) ≤ N)
    (hM : ∀ x, (((Finset.univ.filter fun y => x ∈ T y).card : ℕ) : ℝ) ≤ M)
    (hb : ∀ y, pauliNorm (G y) ≤ κ * ∑ x ∈ T y, pauliNorm (F x))
    (hnum : a' ^ 4 * (κ ^ 2 * N * M) ≤ c ^ 2 * a ^ 4) :
    wNorm (meshWeight a') (toPauliCoeffs G) ≤ c * wNorm (meshWeight a) f := by
  have h₁ := sum_sq_le_of_cover T (fun x => pauliNorm (F x)) (fun y => pauliNorm (G y))
    (fun y => Real.sqrt_nonneg _) hN0 hN hM hb
  have h₂ : wNorm (meshWeight a') (toPauliCoeffs G) ^ 2 =
      a' ^ 4 * ∑ y, pauliNorm (G y) ^ 2 := by
    rw [wNorm_meshWeight_sq]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [pauliNorm_sq]
    rfl
  have h₃ : wNorm (meshWeight a) f ^ 2 = a ^ 4 * ∑ x, pauliNorm (F x) ^ 2 := by
    rw [wNorm_meshWeight_sq]
    congr 1
    exact Finset.sum_congr rfl fun x _ => (hF x).symm
  have h₄ : 0 ≤ ∑ x, pauliNorm (F x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h₅ : 0 ≤ a' ^ 4 := by positivity
  have h₆ : wNorm (meshWeight a') (toPauliCoeffs G) ^ 2 ≤
      (c * wNorm (meshWeight a) f) ^ 2 := by
    rw [mul_pow, h₂, h₃]
    calc a' ^ 4 * ∑ y, pauliNorm (G y) ^ 2
        ≤ a' ^ 4 * (κ ^ 2 * N * M * ∑ x, pauliNorm (F x) ^ 2) :=
          mul_le_mul_of_nonneg_left h₁ h₅
      _ = (a' ^ 4 * (κ ^ 2 * N * M)) * ∑ x, pauliNorm (F x) ^ 2 := by ring
      _ ≤ (c ^ 2 * a ^ 4) * ∑ x, pauliNorm (F x) ^ 2 := mul_le_mul_of_nonneg_right hnum h₄
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))
    two_ne_zero).1 h₆
abbrev _root_.YangMills.SharedProofs.p19244 := @wNorm_le_of_local
end Norms
section Coefficients
private theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem pauliNorm_ofPauliCoeffs_sq {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    pauliNorm (ofPauliCoeffs c x) ^ 2 = ∑ i, ‖c (i, x)‖ ^ 2 := by
  rw [pauliNorm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ofPauliCoeffs c x = ∑ a, c (a, x) • ComplexMatrix2.pauliFamily a from rfl,
    pauliCoeff_combination fun a => c (a, x)]
abbrev _root_.YangMills.SharedProofs.p49452 := @pauliNorm_ofPauliCoeffs_sq
private theorem real_smul_eq_complex_smul (t : ℝ) (X : ComplexMatrix2) : t • X = (t : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
end Coefficients
private structure Inputs : Prop where
  near : NearIdentityStepKernels.StepKernelNearIdentityBound
  kernels : StepKernels.StepKernelBounds
  blocks : BlockPathContourPivotStatement
  coeffs : PauliCoefficientNorm.Claim
  rescaled : RescaledTrivialSteps
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteEdges : BondSetFields.ProductStructureHolds
section Lattice
variable {L n k j : ℕ}
private theorem edge_xor_opposite (G : Inputs) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {i : ℕ} (hi : i ≤ k) (b : Edge L n k i) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 b).2.2.2.2.2
private theorem edge_finite (G : Inputs) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ}
    (hi : i ≤ k) : Finite (Edge L n k i) :=
  Set.finite_univ_iff.1 ((G.finiteEdges L hL k i hi).1 n hn).2.1
private theorem extendOddly_opposite (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.SharedProofs.p17859 <;> assumption
private def positiveValues (c : (edgePauliCoordinates L n k j).Index → ℂ) : Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
private theorem edgePauliCoordinates_ofCoeffs_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, h⟩ := by apply _root_.YangMills.SharedProofs.p19922 <;> assumption
private theorem edgePauliCoordinates_ofCoeffs_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j :=
  ⟨fun b hb => by
    rw [edgePauliCoordinates_ofCoeffs_pos c hb]
    exact ofPauliCoeffs_mem_traceless c _, fun b => extendOddly_opposite (positiveValues c) (hx b)⟩
abbrev _root_.YangMills.SharedProofs.p1053 := @edgePauliCoordinates_ofCoeffs_mem
private theorem meshAt_succ (hL : IsAdmissibleBlockingFactor L) (k m : ℕ) :
    meshAt L k (m + 1) = L * meshAt L k m := by apply _root_.YangMills.SharedProofs.p23229 <;> assumption
private theorem distFromOne_nonneg (V : Edge L n k j → ComplexMatrix2) : 0 ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V :=
  ENNReal.toReal_nonneg
private theorem opNorm_sub_one_le_distFromOne {V : Edge L n k j → ComplexMatrix2} {ρ : ℝ}
    (hV : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ)
    (b : Edge L n k j) : ComplexMatrix2.operatorNorm (V b - 1) ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by
  have hfin : maxOperatorNorm (fun b => V b - 1) ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (b := ENNReal.ofReal ρ) ?_
    exact iSup_le fun b => ENNReal.ofReal_le_ofReal (hV b).le
  have h₁ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)) ≤
      maxOperatorNorm fun b => V b - 1 :=
    le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1))) b
  have h₂ := ENNReal.toReal_mono hfin h₁
  rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h₂
abbrev _root_.YangMills.SharedProofs.p53627 := @opNorm_sub_one_le_distFromOne
private theorem doubleBlockDist_le {V : Edge L n k j → ComplexMatrix2} {ρ : ℝ}
    (hV : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) (c : Edge L n k (j + 1)) :
    doubleBlockDistToOne V c ≤ _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by
  refine Real.sSup_le ?_ (distFromOne_nonneg V)
  rintro _ ⟨b, _, rfl⟩
  exact opNorm_sub_one_le_distFromOne hV b
private theorem polydiscRadius_pos_of_near {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L / 2) :
    0 < polydiscRadius L := by
  have h := hV (PeriodicLattice.Bond.forwardFrom 0 0)
  have h₀ : 0 ≤ ComplexMatrix2.operatorNorm (V (PeriodicLattice.Bond.forwardFrom 0 0) - 1) :=
    norm_nonneg _
  linarith
abbrev _root_.YangMills.SharedProofs.p94894 := @polydiscRadius_pos_of_near
private theorem one_mem_fieldsIn : (fun _ => 1 : Edge L n k j → ComplexMatrix2) ∈
    fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun _ _ => ?_, fun _ _ => ?_⟩
  · show Matrix.det (1 : ComplexMatrix2) = 1
    simp
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p502112 := @one_mem_fieldsIn
abbrev _root_.YangMills.SharedProofs.p71645 := @one_mem_fieldsIn
end Lattice
section Numbers
private theorem constant_inequality {l a D s : ℝ} (hl : 0 < l) :
    (l * a) ^ 4 * ((l⁻¹ * (D * s * Real.sqrt 2)) ^ 2 * (8 * l ^ 4) * 8) ≤
      ((12 * l ^ 3 + 2) * (2 * D) * s) ^ 2 * a ^ 4 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e₁ : (l * a) ^ 4 * ((l⁻¹ * (D * s * Real.sqrt 2)) ^ 2 * (8 * l ^ 4) * 8) =
      128 * l ^ 6 * ((D * s) ^ 2 * a ^ 4) := by
    rw [mul_pow l⁻¹, mul_pow (D * s), h2]
    field_simp
    ring
  have e₂ : ((12 * l ^ 3 + 2) * (2 * D) * s) ^ 2 * a ^ 4 =
      ((12 * l ^ 3 + 2) ^ 2 * 4) * ((D * s) ^ 2 * a ^ 4) := by ring
  rw [e₁, e₂]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h₃ : 0 < l ^ 3 := by positivity
  nlinarith [sq_nonneg (l ^ 3)]
abbrev _root_.YangMills.SharedProofs.p115257 := @constant_inequality
end Numbers
section Values
variable {L n k j : ℕ}
open Classical in
private def doubleBlockPlaces [Fintype (PositiveEdge L n k j)] (c : Edge L n k (j + 1)) :
    Finset (PositiveEdge L n k j) :=
  Finset.univ.filter fun p => p.1 ∈ positiveDoubleBlockEdges c
open Classical in
private theorem mem_doubleBlockPlaces [Fintype (PositiveEdge L n k j)] {c : Edge L n k (j + 1)}
    {p : PositiveEdge L n k j} :
    p ∈ doubleBlockPlaces c ↔ p.1 ∈ positiveDoubleBlockEdges c :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
end Values
section Value
variable {L n k j : ℕ}
private theorem pauliNorm_step_diff_le (G : Inputs) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) [Finite (Edge L n k j)] [Fintype (PositiveEdge L n k j)] {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hs₂ : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L / 2)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    (hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)))
    (hX : ∀ s β : ℝ, 0 ≤ s → 0 ≤ β →
      (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        ComplexMatrix2.operatorNorm (V b - 1) ≤ s) →
      (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        ComplexMatrix2.operatorNorm (B b) ≤ β) →
      ComplexMatrix2.operatorNorm (meanCovariantStep V B c - covariantSmoothingDeriv V B c) ≤
        C₀ * s * β) :
    pauliNorm ((L : ℝ)⁻¹ • (meanCovariantStep V B c - crossingSmoothing L n k j B c)) ≤
      (L : ℝ)⁻¹ * ((1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀) *
        _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * Real.sqrt 2) * ∑ p ∈ doubleBlockPlaces c, pauliNorm (B p.1) := by
  classical
  have hk : 1 ≤ k := by omega
  have hρL0 : 0 < polydiscRadius L := polydiscRadius_pos_of_near hs₂
  have hL0 : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
  have hs₃ : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < 3 / 4 * polydiscRadius L := fun b =>
    (hs₂ b).trans (by linarith)
  have hone : ∀ b, ComplexMatrix2.operatorNorm ((fun _ => 1 : Edge L n k j → ComplexMatrix2) b - 1) <
      3 / 4 * polydiscRadius L := fun b => by
    have : (0 : ℝ) < 3 / 4 * polydiscRadius L := by linarith
    simpa using this
  obtain ⟨hV₁, hV₂, -⟩ := G.kernels L hL n k j hn hj c hc V hV hs₃
  obtain ⟨hO₁, hO₂, -⟩ := G.kernels L hL n k j hn hj c hc _ one_mem_fieldsIn hone
  have hnear := (G.near L hL n k j hn hj c hc V hV hs₂).1
  have hcr : crossingSmoothing L n k j B c =
      covariantSmoothingDeriv (fun _ => 1 : Edge L n k j → ComplexMatrix2) B c :=
    (congrFun (((((G.rescaled L hL k hk n hn).2 j hj).2.2.2.2.1) B hB).2.2) c).symm
  have hsum : ∀ φ : Edge L n k j → ComplexMatrix2, ∑ᶠ b ∈ positiveDoubleBlockEdges c, φ b =
      ∑ p ∈ doubleBlockPlaces c, φ p.1 := fun φ =>
    finsum_mem_eq_subtype_sum (positiveDoubleBlockEdges c) (fun _ h => h.2) φ
  have hplace : ∀ p ∈ doubleBlockPlaces c, p.1 ∈ positiveDoubleBlockEdges c :=
    fun p hp => mem_doubleBlockPlaces.1 hp
  have hval : ∀ p : PositiveEdge L n k j, B p.1 ∈ ComplexMatrix2.traceless := fun p => hB.1 p.1 p.2
  have hD₀ : 0 ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 := by positivity
  have hdist := distFromOne_nonneg V
  have hfirst : ‖covariantSmoothingDeriv V B c - crossingSmoothing L n k j B c‖ ≤
      1280 * (polydiscRadius L)⁻¹ ^ 2 * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V *
        ∑ p ∈ doubleBlockPlaces c, ‖B p.1‖ := by
    rw [hV₁ B hB, hcr, hO₁ B hB, hsum, hsum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    have h₁ := hnear p.1 (hplace p hp) (B p.1) (hval p)
    have h₃ := doubleBlockDist_le hs₂ c
    calc _ ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 * doubleBlockDistToOne V c *
          ComplexMatrix2.operatorNorm (B p.1) := h₁
      _ ≤ 1280 * (polydiscRadius L)⁻¹ ^ 2 * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * ‖B p.1‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₃ hD₀) (norm_nonneg _)
  have hxor := edge_xor_opposite G hL hn hk hj.le
  have hrev : ∀ b : Edge L n k j, b.opposite.opposite = b := fun b =>
    ((G.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.1
  have hβ : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      ComplexMatrix2.operatorNorm (B b) ≤ ∑ p ∈ doubleBlockPlaces c, ‖B p.1‖ := by
    have hpos : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        ∀ hp : b.IsPositivelyOriented, ‖B b‖ ≤ ∑ p ∈ doubleBlockPlaces c, ‖B p.1‖ := by
      intro b hb hp
      obtain ⟨q, hq⟩ : ∃ q : PositiveEdge L n k j, q.1 = b := ⟨⟨b, hp⟩, rfl⟩
      have hb' : q.1 ∈ positiveDoubleBlockEdges c := by
        rw [hq]
        exact And.intro hb hp
      have hm : q ∈ doubleBlockPlaces c := mem_doubleBlockPlaces.2 hb'
      have h := Finset.single_le_sum (s := doubleBlockPlaces c)
        (f := fun p : PositiveEdge L n k j => ‖B p.1‖) (fun _ _ => norm_nonneg _) hm
      rw [← hq]
      exact h
    intro b hb
    by_cases hp : b.IsPositivelyOriented
    · exact hpos b hb hp
    · have h₁ := hB.2 b.opposite
      rw [hrev b] at h₁
      show ‖B b‖ ≤ _
      rw [h₁, norm_neg]
      have hr : b.opposite.IsPositivelyOriented := by
        rcases hxor b with h | h
        exacts [absurd h.1 hp, h.1]
      exact hpos _ (hclosed b hb) hr
  have hsecond : ‖meanCovariantStep V B c - covariantSmoothingDeriv V B c‖ ≤
      C₀ * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * ∑ p ∈ doubleBlockPlaces c, ‖B p.1‖ :=
    hX _ _ hdist (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (fun b _ => opNorm_sub_one_le_distFromOne hs₂ b) hβ
  have hsq : ∑ p ∈ doubleBlockPlaces c, ‖B p.1‖ ≤
      Real.sqrt 2 * ∑ p ∈ doubleBlockPlaces c, pauliNorm (B p.1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => (G.coeffs.2.1.1 ⟨_, hval p⟩).2
  have hcol0 : 0 ≤ ∑ p ∈ doubleBlockPlaces c, pauliNorm (B p.1) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  obtain ⟨Y, hY⟩ : ∃ Y : ComplexMatrix2,
      Y = (L : ℝ)⁻¹ • (meanCovariantStep V B c - crossingSmoothing L n k j B c) := ⟨_, rfl⟩
  rw [← hY]
  have hRHS : 0 ≤ (L : ℝ)⁻¹ * ((1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀) *
      _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * Real.sqrt 2) *
        ∑ p ∈ doubleBlockPlaces c, pauliNorm (B p.1) := by positivity
  by_cases hmem : Y ∈ ComplexMatrix2.traceless
  · refine ((G.coeffs.2.1.1 ⟨_, hmem⟩).1).trans ?_
    show ‖Y‖ ≤ _
    have hnY : ‖Y‖ ≤ (L : ℝ)⁻¹ *
        ‖meanCovariantStep V B c - crossingSmoothing L n k j B c‖ := by
      rw [hY, real_smul_eq_complex_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hL0]
    have htri : ‖meanCovariantStep V B c - crossingSmoothing L n k j B c‖ ≤
        ‖meanCovariantStep V B c - covariantSmoothingDeriv V B c‖ +
          ‖covariantSmoothingDeriv V B c - crossingSmoothing L n k j B c‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    refine hnY.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    refine htri.trans ((add_le_add hsecond hfirst).trans ?_)
    have hD₁ : 0 ≤ (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀) *
        _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by positivity
    calc _ = (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀) *
          _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * ∑ p ∈ doubleBlockPlaces c, ‖B p.1‖ := by ring
      _ ≤ (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀) *
          _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * (Real.sqrt 2 * ∑ p ∈ doubleBlockPlaces c,
            pauliNorm (B p.1)) := mul_le_mul_of_nonneg_left hsq hD₁
      _ = _ := by ring
  · have h0 : pauliNorm Y = 0 := by
      simp [pauliNorm, pauliCoeff, hmem]
    rw [h0]
    exact hRHS
end Value
private theorem wNorm_step_diff_le (G : Inputs) {L n k j : ℕ} (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hs₂ : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L / 2)
    (hclosed : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)))
    (hX : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → ∀ B ∈ complexEdgeForms L n k j,
      ∀ s β : ℝ, 0 ≤ s → 0 ≤ β →
      (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        ComplexMatrix2.operatorNorm (V b - 1) ≤ s) →
      (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        ComplexMatrix2.operatorNorm (B b) ≤ β) →
      ComplexMatrix2.operatorNorm (meanCovariantStep V B c - covariantSmoothingDeriv V B c) ≤
        C₀ * s * β)
    (f : (edgePauliCoordinates L n k j).Index → ℂ) :
    wNorm (meshWeight (meshAt L k (j + 1)))
        ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
          (fun B => (L : ℝ)⁻¹ • (meanCovariantStep V B - crossingSmoothing L n k j B)) f) ≤
      (12 * (L : ℝ) ^ 3 + 2) * (2 * (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀)) * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V *
        wNorm (meshWeight (meshAt L k j)) f := by
  classical
  have hk : 1 ≤ k := by omega
  have hl : (1 : ℝ) ≤ L := by
    have := hL.2
    have h : 1 ≤ L := by omega
    exact_mod_cast h
  have hl0 : (0 : ℝ) < L := by linarith
  have hb₀ : Finite (Edge L n k j) := edge_finite G hL hn hj.le
  have hb₁ : Finite (Edge L n k (j + 1)) := edge_finite G hL hn hj
  let _ : Fintype (PositiveEdge L n k j) :=
    @Fintype.ofFinite _ (inferInstanceAs (Finite {b : Edge L n k j // b.IsPositivelyOriented}))
  let _ : Fintype (PositiveEdge L n k (j + 1)) :=
    @Fintype.ofFinite _
      (inferInstanceAs (Finite {b : Edge L n k (j + 1) // b.IsPositivelyOriented}))
  obtain ⟨B, hBe⟩ : ∃ B, B = (edgePauliCoordinates L n k j).ofCoeffs f := ⟨_, rfl⟩
  have hB : B ∈ complexEdgeForms L n k j := by
    rw [hBe]
    exact edgePauliCoordinates_ofCoeffs_mem (edge_xor_opposite G hL hn hk hj.le) f
  have hBv : ∀ p : PositiveEdge L n k j, B p.1 = ofPauliCoeffs f p := fun p => by
    rw [hBe]
    exact edgePauliCoordinates_ofCoeffs_pos f p.2
  have hsb := ((G.blocks L hL k 1 (j + 1) hk (by omega) hj).1 n hn).2.2.2.2.1
  have hρL0 : 0 < polydiscRadius L := polydiscRadius_pos_of_near hs₂
  have hdist := distFromOne_nonneg V
  have key := wNorm_le_of_local (a := meshAt L k j) (a' := meshAt L k (j + 1))
    (κ := (L : ℝ)⁻¹ * ((1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀) *
      _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V * Real.sqrt 2))
    (N := 8 * (L : ℝ) ^ 4) (M := 8)
    (c := (12 * (L : ℝ) ^ 3 + 2) * (2 * (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀)) * _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V)
    (fun c : PositiveEdge L n k (j + 1) => doubleBlockPlaces c.1) f
    (fun p => B p.1)
    (fun c : PositiveEdge L n k (j + 1) => (L : ℝ)⁻¹ •
      (meanCovariantStep V B c.1 - crossingSmoothing L n k j B c.1))
    (fun p => by
      rw [hBv p]
      exact pauliNorm_ofPauliCoeffs_sq f p)
    (by positivity) (by positivity) ?_ ?_
    (fun c => pauliNorm_step_diff_le G hL hn hj hC₀ hV hs₂ hB c.2 (hclosed c.1 c.2)
      (hX c.1 c.2 B hB)) ?_
  · rw [hBe] at key
    exact key
  · intro c
    have h : (doubleBlockPlaces (L := L) (n := n) (k := k) (j := j) c.1).card ≤
        8 * L ^ (4 * 1) := by
      refine finset_card_le_of_encard (q := fun b : Edge L n k j => b.IsPositivelyOriented) _
        (fun p hp => ?_) (hsb.bonds_encard_le c.1 c.2)
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
        refine finset_card_le_of_encard
          (q := fun b : Edge L n k (j + 1) => b.IsPositivelyOriented) F
          (fun c hc => ?_) (by simpa using hsb.encard_le_eight p.1)
        have hc' := mem_doubleBlockPlaces.1 (hF c hc)
        exact ⟨c.2, hc'.1.1, hc'.1.2⟩
      exact_mod_cast h₁
    exact h _ fun c hc => by simpa using hc
  · rw [meshAt_succ hL]
    exact constant_inequality hl0
theorem claim_holds (near : NearIdentityStepKernels.StepKernelNearIdentityBound)
    (kernels : StepKernels.StepKernelBounds)
    (blocks : BlockPathContourPivotStatement)
    (coeffs : PauliCoefficientNorm.Claim)
    (rescaled : RescaledTrivialSteps)
    (orientation : PeriodicLattice.BondEndpointsOrientation.Statement)
    (finiteEdges : BondSetFields.ProductStructureHolds)
    (smoothing : SmoothingNearIdentity)
    (polydiscs : DoubleBlockPolydisc.PolydiscsHold)
    (covariant : MeanStepNearCovariantDeriv.Claim) :
    MeanStepNearFree.Claim := by
  intro L hL
  have G : Inputs := ⟨near, kernels, blocks, coeffs, rescaled, orientation, finiteEdges⟩
  obtain ⟨ρ₀, C₀, hρ₀, hC₀, hX⟩ := covariant L hL
  have hrad := (smoothing.1 L hL).2.2
  have hρL := hrad.pos
  have hl : (1 : ℝ) ≤ L := by
    have := hL.2
    have h : 1 ≤ L := by omega
    exact_mod_cast h
  refine ⟨min ρ₀ (polydiscRadius L / 2), (12 * (L : ℝ) ^ 3 + 2) *
    (2 * (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀)),
    lt_min hρ₀ (by linarith), by positivity, ?_⟩
  intro n k j hn hj V hV hs
  have hb₁ : Finite (Edge L n k (j + 1)) := edge_finite G hL hn hj
  have hdist := distFromOne_nonneg V
  have hc : 0 ≤ (12 * (L : ℝ) ^ 3 + 2) * (2 * (1280 * (polydiscRadius L)⁻¹ ^ 2 + C₀)) *
      _root_.YangMills.Construction.Tower.SmoothingStepsNearFree.distFromOne V := by positivity
  exact mapNormLE_of_bound
    (inferInstanceAs (Finite {b : Edge L n k (j + 1) // b.IsPositivelyOriented})) hc
    (wNorm_step_diff_le G hL hn hj hC₀ hV (fun b => (hs b).trans_le (min_le_right _ _))
      (fun c hc => ((polydiscs L hL k j hj).1 n hn c hc).finite_open.opposite_mem)
      (hX n k j hn hj V hV (fun b => (hs b).trans_le (min_le_left _ _))))
end YangMills.Construction.RunningCouplingSlope.MeanStepNearFree
end
