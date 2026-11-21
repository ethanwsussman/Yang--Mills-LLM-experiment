import YangMills.Construction.Towers.StepKernelsAreHolomorphicOnASideProof
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheCovariantStepProof
import YangMills.Construction.Towers.StepKernelsAreHolomorphicOnASide
import YangMills.Construction.Towers.StepKernelsNearOneOnASide
import YangMills.Construction.Towers.TrivialConfigurationAtAStep
import Mathlib
set_option autoImplicit false
open Set Filter Metric
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.NearIdentityStepKernels
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Tower.StepKernels
open YangMills.Construction.Tower.StepKernelHolomorphy (IsHolomorphicOnProduct)
open YangMills.Construction.Tower.DoubleBlockPolydisc
  (doubleBlockBonds positiveDoubleBlockBonds polydiscPositive leftComponents)
theorem norm_sub_le_of_differentiableOn_ball {f : ℂ → ComplexMatrix2} {R M : ℝ} (hR : 1 < R)
    (hd : DifferentiableOn ℂ f (ball 0 R)) (hb : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    ‖f 1 - f 0‖ ≤ 2 * M / R := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self (by linarith)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) (2 * M)) := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]
    have e₁ := hb z hz
    have e₂ := hb 0 h0
    have e₃ := norm_sub_le (f z) (f 0)
    linarith
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1
  rw [dist_eq_norm, dist_eq_norm] at h
  simpa using h
theorem norm_sub_le_of_differentiable_small {f : ℂ → ComplexMatrix2} {ρ s x : ℝ} (hρ : 0 < ρ)
    (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hd : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → ‖f z‖ ≤ 80 * ρ⁻¹ * x)
    (h₀ : ‖f 0‖ ≤ 80 * ρ⁻¹ * x) (h₁ : ‖f 1‖ ≤ 80 * ρ⁻¹ * x) :
    ‖f 1 - f 0‖ ≤ 1280 * ρ⁻¹ ^ 2 * s * x := by
  have hone : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ.ne'
  by_cases hbig : ρ / 8 ≤ s
  · have e := norm_sub_le (f 1) (f 0)
    have h2 : 160 * ρ⁻¹ * x ≤ 1280 * ρ⁻¹ ^ 2 * s * x := by
      have h3 : 160 * ρ⁻¹ * x = 1280 * ρ⁻¹ ^ 2 * (ρ / 8) * x := by
        have : ρ⁻¹ ^ 2 * ρ = ρ⁻¹ := by rw [pow_two, mul_assoc, hone, mul_one]
        calc 160 * ρ⁻¹ * x = 160 * (ρ⁻¹ ^ 2 * ρ) * x := by rw [this]
          _ = _ := by ring
      rw [h3]
      have : 0 ≤ 1280 * ρ⁻¹ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbig this) hx
    linarith
  · rw [not_le] at hbig
    set K : ℝ := 960 * ρ⁻¹ ^ 2 * x with hK
    have hK0 : 0 ≤ K := by positivity
    have key : ∀ t : ℝ, s < t → t < ρ / 6 → ‖f 1 - f 0‖ ≤ K * t := by
      intro t hst ht
      have ht0 : 0 < t := lt_of_le_of_lt hs hst
      have hR : 1 < ρ / (6 * t) := by
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have hin : ∀ z ∈ ball (0 : ℂ) (ρ / (6 * t)), ‖z‖ * s < ρ / 6 := by
        intro z hz
        have hz' : ‖z‖ < ρ / (6 * t) := by simpa using hz
        have h4 : ‖z‖ * t < ρ / 6 := by
          rw [lt_div_iff₀ (by positivity)] at hz'
          linarith
        have h5 : ‖z‖ * s ≤ ‖z‖ * t := mul_le_mul_of_nonneg_left hst.le (norm_nonneg z)
        linarith
      have h := norm_sub_le_of_differentiableOn_ball hR
        (fun z hz => (hd z (hin z hz)).differentiableWithinAt) (fun z hz => hb z (hin z hz))
      refine h.trans (le_of_eq ?_)
      rw [hK]
      field_simp
      ring
    refine le_trans ?_ (?_ : K * s ≤ 1280 * ρ⁻¹ ^ 2 * s * x)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      set δ : ℝ := min ((ρ / 6 - s) / 2) (ε / (K + 1)) with hδ
      have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
      have hδ1 : δ ≤ (ρ / 6 - s) / 2 := min_le_left _ _
      have hδ2 : δ ≤ ε / (K + 1) := min_le_right _ _
      have h := key (s + δ) (by linarith) (by linarith)
      have h3 : K * δ ≤ ε := by
        have : K * δ ≤ (K + 1) * (ε / (K + 1)) :=
          mul_le_mul (by linarith) hδ2 hδ0.le (by linarith)
        rwa [mul_div_cancel₀ _ (by positivity : K + 1 ≠ 0)] at this
      nlinarith
    · rw [hK]
      have : 0 ≤ ρ⁻¹ ^ 2 * s * x := by positivity
      nlinarith
theorem eq_sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by
  have e := congrArg Subtype.val (OneLoop.pauliCoordinateEquiv.symm_apply_apply ⟨X, hX⟩)
  simp only [pauliCoeff, dif_pos hX, Fin.sum_univ_three]
  exact e.symm
theorem matExp_smul_mul_matExp_smul (Z : ComplexMatrix2) (z w : ℂ) :
    ComplexMatrix2.matExp (z • Z) * ComplexMatrix2.matExp (w • Z) =
      ComplexMatrix2.matExp ((z + w) • Z) := by
  rw [add_smul]
  exact (Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left z).smul_right w)).symm
theorem matExp_smul_inv (Z : ComplexMatrix2) (z : ℂ) :
    (ComplexMatrix2.matExp (z • Z))⁻¹ = ComplexMatrix2.matExp ((-z) • Z) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [matExp_smul_mul_matExp_smul, add_neg_cancel, zero_smul]
  exact NormedSpace.exp_zero
theorem matExp_smul_mem_unitDeterminant (hEL : ComplexMatrix2.ExpLogEstimates)
    {Z : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.traceless) (z : ℂ) :
    ComplexMatrix2.matExp (z • Z) ∈ ComplexMatrix2.unitDeterminant := by
  have hZ' : ComplexMatrix2.fullTrace Z = 0 := hZ
  show (ComplexMatrix2.matExp (z • Z)).det = 1
  rw [hEL.2.2.2.2.2.1]
  simp [ComplexMatrix2.fullTrace, Matrix.trace_smul] at hZ' ⊢
  rw [hZ']
  simp
theorem differentiableAt_comp_matExp_line {σ : Type} [Fintype σ]
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {W : Set (σ → ComplexMatrix2)} {φ : (σ → ComplexMatrix2) → ℂ} (hφ : IsHolomorphicOnProduct W φ)
    {Z : σ → ComplexMatrix2} (hZ : ∀ s, Z s ∈ ComplexMatrix2.traceless) {z₀ : ℂ}
    (hz : (fun s => ComplexMatrix2.matExp (z₀ • Z s)) ∈ W) :
    DifferentiableAt ℂ (fun z : ℂ => φ fun s => ComplexMatrix2.matExp (z • Z s)) z₀ := by
  classical
  let bs := OneLoop.pauliBasis
  obtain ⟨-, -, hchart⟩ := hφ bs
  let p : σ ⊕ Empty → ComplexMatrix2 :=
    Sum.elim (fun s => ComplexMatrix2.matExp (z₀ • Z s)) fun e => e.elim
  have hp : p ∈ leftComponents ⁻¹' W := hz
  obtain ⟨O, hO0, -, -, hhol⟩ := hchart p hp
  let ν : σ ⊕ Empty ≃ Fin (Fintype.card (σ ⊕ Empty)) := Fintype.equivFin _
  have hh := hhol ν
  let A : σ ⊕ Empty → ComplexMatrix2.traceless := Sum.elim (fun s => ⟨Z s, hZ s⟩) fun e => e.elim
  let w : Coordinates.ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3) := fun m =>
    bs.repr (A (ν.symm (finProdFinEquiv.symm m).1)) (finProdFinEquiv.symm m).2
  have hT : ∀ ζ : ℂ, tupleOfCoords bs ν (ζ • w) = fun i => ζ • (A i : ComplexMatrix2) := by
    intro ζ
    funext i
    have e := bs.sum_repr (A i)
    have e' := congrArg Subtype.val e
    simp only [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, Pi.smul_apply, w,
      Equiv.symm_apply_apply, smul_eq_mul, mul_smul]
    rw [← Finset.smul_sum]
    congr 1
  have h0 : (0 : Coordinates.ComplexCoordinates _) ∈ tupleOfCoords bs ν ⁻¹' O := by
    have := hT 0
    simp only [zero_smul] at this
    show tupleOfCoords bs ν 0 ∈ O
    rw [this]
    exact hO0
  obtain ⟨Lc, hL⟩ := ((hM.1 _ _ hh.1).1 _ _ hh).2.2.1 0 h0
  have hF := hasFDerivAt_of_restrictScalars ℝ hL rfl
  have hline : HasDerivAt (fun ζ : ℂ => ζ • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
  have hcomp : DifferentiableAt ℂ (fun ζ : ℂ => ((Equiv.funUnique (Fin 1) ℂ).symm ∘
      ((φ ∘ leftComponents) ∘ expChartAt p) ∘ tupleOfCoords bs ν) (ζ • w)) 0 := by
    have hF' : DifferentiableAt ℂ ((Equiv.funUnique (Fin 1) ℂ).symm ∘
        ((φ ∘ leftComponents) ∘ expChartAt p) ∘ tupleOfCoords bs ν) ((0 : ℂ) • w) := by
      rw [zero_smul]
      exact hF.differentiableAt
    exact DifferentiableAt.comp (f := fun ζ : ℂ => ζ • w) (0 : ℂ) hF' hline.differentiableAt
  have hcoord := (differentiableAt_pi.1 hcomp) 0
  have hval : ∀ ζ : ℂ, ((Equiv.funUnique (Fin 1) ℂ).symm ∘
      ((φ ∘ leftComponents) ∘ expChartAt p) ∘ tupleOfCoords bs ν) (ζ • w) 0 =
        φ fun s => ComplexMatrix2.matExp ((ζ + z₀) • Z s) := by
    intro ζ
    simp only [Function.comp_apply, hT]
    show φ (leftComponents (expChartAt p _)) = _
    congr 1
    funext s
    show ComplexMatrix2.matExp (ζ • Z s) * ComplexMatrix2.matExp (z₀ • Z s) = _
    exact matExp_smul_mul_matExp_smul _ _ _
  simp only [hval] at hcoord
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z - z₀) z₀ := by fun_prop
  have hcoord' : DifferentiableAt ℂ
      (fun ζ : ℂ => φ fun s => ComplexMatrix2.matExp ((ζ + z₀) • Z s)) (z₀ - z₀) := by
    rwa [sub_self]
  have := DifferentiableAt.comp (f := fun z : ℂ => z - z₀) z₀ hcoord' hshift
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp
section Setting
variable {L n k j : ℕ} {c : Edge L n k (j + 1)}
structure EdgeStructure (c : Edge L n k (j + 1)) : Prop where
  xor_opposite : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  opposite_opposite : ∀ b : Edge L n k j, b.opposite.opposite = b
  opposite_mem : ∀ b ∈ doubleBlockBonds c, b.opposite ∈ doubleBlockBonds c
theorem EdgeStructure.opposite_pos_of_not (F : EdgeStructure c) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases F.xor_opposite b with h | h
  exacts [absurd h.1 hb, h.1]
theorem EdgeStructure.not_opposite_pos (F : EdgeStructure c) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases F.xor_opposite b with h | h
  exacts [h.2, absurd hb h.2]
abbrev fieldOn (c : Edge L n k (j + 1)) (v : positiveDoubleBlockBonds c → ComplexMatrix2) :
    Edge L n k j → ComplexMatrix2 :=
  DoubleBlockPolydisc.fieldOfValues c v
theorem fieldOn_of_pos {v : positiveDoubleBlockBonds c → ComplexMatrix2} {b : Edge L n k j}
    (hb : b ∈ doubleBlockBonds c) (hp : b.IsPositivelyOriented) : fieldOn c v b = v ⟨b, hb, hp⟩ := by apply _root_.YangMills.Construction.Tower.StepKernelHolomorphy.fieldOf_of_positive <;> assumption
theorem fieldOn_opposite (F : EdgeStructure c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {b : Edge L n k j} (hb : b ∈ doubleBlockBonds c) (hp : b.IsPositivelyOriented) :
    fieldOn c v b.opposite = (v ⟨b, hb, hp⟩)⁻¹ := by
  have hr := F.not_opposite_pos hp
  have h' : b.opposite.opposite ∈ doubleBlockBonds c ∧ b.opposite.opposite.IsPositivelyOriented := by
    rw [F.opposite_opposite b]
    exact ⟨hb, hp⟩
  unfold fieldOn DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  rw [dif_neg (show ¬ (b.opposite ∈ doubleBlockBonds c ∧ b.opposite.IsPositivelyOriented) from
    fun h => hr h.2), dif_pos h']
  congr 2
theorem fieldOn_of_not_pos (F : EdgeStructure c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {b : Edge L n k j} (hb : b ∈ doubleBlockBonds c) (hp : ¬ b.IsPositivelyOriented) :
    fieldOn c v b = (v ⟨b.opposite, F.opposite_mem b hb, F.opposite_pos_of_not hp⟩)⁻¹ := by
  have h := fieldOn_opposite F (v := v) (F.opposite_mem b hb) (F.opposite_pos_of_not hp)
  rwa [F.opposite_opposite b] at h
theorem fieldOn_of_not_mem (F : EdgeStructure c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {b : Edge L n k j} (hb : b ∉ doubleBlockBonds c) : fieldOn c v b = 1 := by
  have h' : ¬ (b.opposite ∈ doubleBlockBonds c ∧ b.opposite.IsPositivelyOriented) := fun h => by
    have := F.opposite_mem _ h.1
    rw [F.opposite_opposite b] at this
    exact hb this
  unfold fieldOn DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  rw [dif_neg (show ¬ (b ∈ doubleBlockBonds c ∧ b.IsPositivelyOriented) from fun h => hb h.1),
    dif_neg h']
theorem inv_mem_unitDeterminant {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem fieldOn_mem (F : EdgeStructure c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    (hv : ∀ s, v s ∈ PeriodicLattice.complexGaugeGroup) :
    fieldOn c v ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b ∈ doubleBlockBonds c
    · by_cases hp : b.IsPositivelyOriented
      · rw [fieldOn_of_pos hb hp]
        exact hv _
      · rw [fieldOn_of_not_pos F hb hp]
        exact inv_mem_unitDeterminant (hv _)
    · rw [fieldOn_of_not_mem F hb]
      exact Matrix.det_one
  · by_cases hb : b ∈ doubleBlockBonds c
    · by_cases hp : b.IsPositivelyOriented
      · rw [fieldOn_opposite F hb hp, fieldOn_of_pos hb hp]
      · have hr := F.opposite_pos_of_not hp
        have hrb := F.opposite_mem b hb
        rw [fieldOn_of_not_pos F hb hp, fieldOn_of_pos hrb hr, inv_inv_of_mem_unitDeterminant (hv _)]
    · have hrb : b.opposite ∉ doubleBlockBonds c := fun h => by
        have := F.opposite_mem _ h
        rw [F.opposite_opposite b] at this
        exact hb this
      rw [fieldOn_of_not_mem F hb, fieldOn_of_not_mem F hrb, inv_one]
theorem fieldOn_eqOn (F : EdgeStructure c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (h : ∀ t : positiveDoubleBlockBonds c, v t = W t.1) :
    EqOn (fieldOn c v) W (doubleBlockBonds c) := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · rw [fieldOn_of_pos hb hp, h]
  · have e := hW.2 b.opposite (mem_univ _)
    rw [F.opposite_opposite b] at e
    rw [fieldOn_of_not_pos F hb hp, h, e]
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem apply_eq_sum_pauli {T : ComplexMatrix2 → ComplexMatrix2} {C : ℝ}
    (h : IsBoundedTracelessEndo T C) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    T X = ∑ a, ∑ a', (pauliCoeff a X * pauliCoeff a' (T (ComplexMatrix2.pauliFamily a))) •
      ComplexMatrix2.pauliFamily a' := by
  have hs : ∀ (z : ℂ) (a : Fin 3), z • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless :=
    fun z a => ComplexMatrix2.traceless.smul_mem z (pauliFamily_mem_traceless a)
  have hsum : T X = ∑ a, pauliCoeff a X • T (ComplexMatrix2.pauliFamily a) := by
    conv_lhs => rw [eq_sum_pauliCoeff_smul hX]
    simp only [Fin.sum_univ_three]
    rw [h.map_add _ (ComplexMatrix2.traceless.add_mem (hs _ _) (hs _ _)) _ (hs _ _),
      h.map_add _ (hs _ _) _ (hs _ _),
      h.map_smul _ _ (pauliFamily_mem_traceless 0), h.map_smul _ _ (pauliFamily_mem_traceless 1),
      h.map_smul _ _ (pauliFamily_mem_traceless 2)]
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [eq_sum_pauliCoeff_smul (h.mapsTo _ (pauliFamily_mem_traceless a))]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a' _ => (mul_smul _ _ _).symm
theorem norm_matExp_sub_one_le (hEL : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : ‖Z‖ ≤ 1) : ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * ‖Z‖ := by apply _root_.YangMills.SharedProofs.p10567 <;> assumption
structure AdmissibleKernels (ρ : ℝ) (c : Edge L n k (j + 1))
    (T : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2 → ComplexMatrix2) : Prop where
  bounded : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ‖V b - 1‖ < 3 / 4 * ρ) → IsBoundedTracelessEndo (T V) (80 * ρ⁻¹)
  coeff_local : ∀ V ∈ nearIdentityPolydisc (3 / 4 * ρ) c,
    ∀ V' ∈ nearIdentityPolydisc (3 / 4 * ρ) c, EqOn V V' (doubleBlockBonds c) → ∀ a' a,
      pauliCoeff a' (T V (ComplexMatrix2.pauliFamily a)) =
        pauliCoeff a' (T V' (ComplexMatrix2.pauliFamily a))
  coeff_holomorphic : ∀ a' a, ∃ _ : Fintype (positiveDoubleBlockBonds c),
    IsHolomorphicOnProduct (polydiscPositive (3 / 4 * ρ) c) fun v =>
      pauliCoeff a' (T (fieldOn c v) (ComplexMatrix2.pauliFamily a))
theorem AdmissibleKernels.norm_sub_le {ρ : ℝ}
    {T : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2 → ComplexMatrix2}
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hEL : ComplexMatrix2.ExpLogEstimates) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (F : EdgeStructure c)
    (K : AdmissibleKernels ρ c T) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hsmall : ∀ b, ‖V b - 1‖ < ρ / 2) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∀ b ∈ doubleBlockBonds c, ‖V b - 1‖ ≤ s) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ‖T V X - T (fun _ => 1) X‖ ≤ 1280 * ρ⁻¹ ^ 2 * s * ‖X‖ := by
  classical
  have hgroup : ∀ b, V b ∈ ComplexMatrix2.unitDeterminant := fun b => hV.1 b (mem_univ b)
  obtain ⟨Z, hZ⟩ : ∃ Z : positiveDoubleBlockBonds c → ComplexMatrix2,
      ∀ t, Z t ∈ ComplexMatrix2.traceless ∧ ‖Z t‖ ≤ 2 * s ∧
        ComplexMatrix2.matExp (Z t) = V t.1 := by
    refine ⟨fun t => ComplexMatrix2.logSeries (V t.1), fun t => ?_⟩
    have he := hsmall t.1
    have hs' := hs t.1 t.2.1
    have h := hEL.2.2.2.1 (V t.1 - 1) (by show ‖V t.1 - 1‖ < 1; linarith)
    have e : 1 + (V t.1 - 1) = V t.1 := by abel
    rw [e] at h
    obtain ⟨h₁, h₂, -, -, h₅⟩ := h
    have h₇ := hEL.2.2.2.2.2.2.1 (V t.1) (hgroup t.1) (by show ‖V t.1 - 1‖ ≤ 9 / 10; linarith)
    refine ⟨h₇.2, ?_, h₅⟩
    have h₃ : ‖V t.1 - 1‖ / (1 - ‖V t.1 - 1‖) ≤ 2 * ‖V t.1 - 1‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (V t.1 - 1)]
    linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℂ → Edge L n k j → ComplexMatrix2,
      ∀ z, C z = fieldOn c fun t => ComplexMatrix2.matExp (z • Z t) := ⟨_, fun _ => rfl⟩
  have hexp : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → ∀ t,
      ‖ComplexMatrix2.matExp (z • Z t) - 1‖ < 3 / 4 * ρ := by
    intro z hz t
    have h1 : ‖z • Z t‖ ≤ ρ / 3 := by
      rw [norm_smul]
      have := mul_le_mul_of_nonneg_left (hZ t).2.1 (norm_nonneg z)
      linarith
    have h2 := norm_matExp_sub_one_le hEL (h1.trans (by linarith))
    linarith
  have hCmem : ∀ z : ℂ, ‖z‖ * s < ρ / 6 →
      C z ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b, ‖C z b - 1‖ < 3 / 4 * ρ := by
    intro z hz
    rw [hCdef]
    refine ⟨fieldOn_mem F fun t => matExp_smul_mem_unitDeterminant hEL (hZ t).1 z, fun b => ?_⟩
    by_cases hb : b ∈ doubleBlockBonds c
    · by_cases hp : b.IsPositivelyOriented
      · rw [fieldOn_of_pos hb hp]
        exact hexp z hz _
      · rw [fieldOn_of_not_pos F hb hp, matExp_smul_inv]
        exact hexp (-z) (by simpa using hz) _
    · rw [fieldOn_of_not_mem F hb, sub_self, norm_zero]
      positivity
  have hpoly : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ‖W b - 1‖ < 3 / 4 * ρ) → W ∈ nearIdentityPolydisc (3 / 4 * ρ) c :=
    fun W hW hn => ⟨⟨fun b _ => hW.1 b (mem_univ b), fun b _ => hW.2 b (mem_univ b)⟩,
      fun b _ => hn b⟩
  have hW : ∀ z : ℂ, ‖z‖ * s < ρ / 6 →
      (fun t => ComplexMatrix2.matExp (z • Z t)) ∈ polydiscPositive (3 / 4 * ρ) c := by
    intro z hz
    refine ⟨BondSetFields.restrictTo (doubleBlockBonds c) (C z),
      ⟨C z, hpoly _ (hCmem z hz).1 (hCmem z hz).2, rfl⟩, funext fun t => ?_⟩
    show C z t.1 = ComplexMatrix2.matExp (z • Z t)
    rw [hCdef, fieldOn_of_pos t.2.1 t.2.2]
  have hent : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → ∀ a' a, DifferentiableAt ℂ
      (fun z => pauliCoeff a' (T (C z) (ComplexMatrix2.pauliFamily a))) z := by
    intro z hz a' a
    obtain ⟨inst, hφ⟩ := K.coeff_holomorphic a' a
    simp only [hCdef]
    exact differentiableAt_comp_matExp_line hM hφ (fun t => (hZ t).1) (hW z hz)
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ → ComplexMatrix2, ∀ z, f z = ∑ a, ∑ a',
      (pauliCoeff a X * pauliCoeff a' (T (C z) (ComplexMatrix2.pauliFamily a))) •
        ComplexMatrix2.pauliFamily a' :=
    ⟨_, fun _ => rfl⟩
  have hf : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → DifferentiableAt ℂ f z := by
    intro z hz
    rw [funext hfdef]
    refine DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun a' _ => ?_
    exact ((hent z hz a' a).const_mul _).smul_const _
  have hfe : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → f z = T (C z) X := fun z hz => by
    rw [hfdef]
    exact (apply_eq_sum_pauli (K.bounded _ (hCmem z hz).1 (hCmem z hz).2) hX).symm
  have hb : ∀ z : ℂ, ‖z‖ * s < ρ / 6 → ‖f z‖ ≤ 80 * ρ⁻¹ * ‖X‖ := by
    intro z hz
    rw [hfe z hz]
    exact (K.bounded _ (hCmem z hz).1 (hCmem z hz).2).norm_le X hX
  have hone : (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun _ _ => Matrix.det_one, fun _ _ => by simp⟩
  have hone' : ∀ b : Edge L n k j,
      ‖(fun _ : Edge L n k j => (1 : ComplexMatrix2)) b - 1‖ < 3 / 4 * ρ :=
    fun _ => by
      simp only [sub_self, norm_zero]
      positivity
  have hVclose : ∀ b, ‖V b - 1‖ < 3 / 4 * ρ := fun b => (hsmall b).trans (by linarith)
  have h00 : ‖(0 : ℂ)‖ * s < ρ / 6 := by
    simp only [norm_zero, zero_mul]
    positivity
  have hf0 : f 0 = T (fun _ => 1) X := by
    have eq0 : EqOn (C 0) (fun _ => 1) (doubleBlockBonds c) := by
      rw [hCdef]
      exact fieldOn_eqOn F hone fun t => by
        simp only [zero_smul]
        exact NormedSpace.exp_zero
    rw [apply_eq_sum_pauli (K.bounded _ hone hone') hX, hfdef]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [K.coeff_local _ (hpoly _ (hCmem 0 h00).1 (hCmem 0 h00).2) _ (hpoly _ hone hone') eq0 a' a]
  have eq1 : EqOn (C 1) V (doubleBlockBonds c) := by
    rw [hCdef]
    exact fieldOn_eqOn F hV fun t => by
      rw [one_smul]
      exact (hZ t).2.2
  have hC1 : C 1 ∈ nearIdentityPolydisc (3 / 4 * ρ) c := by
    refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
    · rw [eq1 hb]
      exact hgroup b
    · rw [eq1 hb, eq1 (F.opposite_mem b hb)]
      exact hV.2 b (mem_univ b)
    · rw [eq1 hb]
      exact hVclose b
  have hf1 : f 1 = T V X := by
    rw [apply_eq_sum_pauli (K.bounded _ hV hVclose) hX, hfdef]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [K.coeff_local _ hC1 _ (hpoly _ hV hVclose) eq1 a' a]
  have h₀ : ‖f 0‖ ≤ 80 * ρ⁻¹ * ‖X‖ := by
    rw [hf0]
    exact (K.bounded _ hone hone').norm_le X hX
  have h₁ : ‖f 1‖ ≤ 80 * ρ⁻¹ * ‖X‖ := by
    rw [hf1]
    exact (K.bounded _ hV hVclose).norm_le X hX
  have h := norm_sub_le_of_differentiable_small hρ hs0 (norm_nonneg X) hf hb h₀ h₁
  rwa [hf1, hf0] at h
theorem complexMeanContourHolonomy_trivial (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) {L n k i : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    PeriodicLattice.complexMeanContourHolonomy (trivialField L n k i) y x = 1 := by
  have hk : 1 ≤ k := by omega
  have hc : (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (i + 1)).IsPositivelyOriented :=
    ⟨0, by show y + PeriodicLattice.unitStep L n _ 0 - y = _; abel⟩
  have hone : trivialField L n k i ∈ fieldSpace L n k i :=
    ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
  have hnear := ((hH L hL k hk).1 n hn).agree_near_identity i hi _ hc y (Or.inl rfl) x hx
  have h1 := Filter.Eventually.self_of_nhdsWithin hnear hone
  rw [h1.2.2.2.1]
  exact (hT L n k i hL hn hi).1 y x hx
end Setting
theorem stepKernelNearIdentityBound_holds
    (hHol : StepKernelHolomorphy.StepKernelsHolomorphic)
    (hKer : StepKernels.StepKernelBounds)
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hS : SmoothingNearIdentity)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hCx : LevelwiseMeans.LevelwiseMeansHold)
    (hTr : TrivialFieldAtStep) :
    StepKernelNearIdentityBound := by
  classical
  intro L hL n k j hn hj c hc V hV hsmall
  have hk : 1 ≤ k := by omega
  have hρ := (hS.1 L hL).2.2
  have hd := (hP L hL k j hj).1 n hn c hc
  have F : EdgeStructure c :=
    { xor_opposite := fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.2.2
      opposite_opposite := fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.1
      opposite_mem := hd.finite_open.opposite_mem }
  have hbdd : BddAbove ((fun b => ComplexMatrix2.operatorNorm (V b - 1)) ''
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))) :=
    ⟨polydiscRadius L / 2, by
      rintro _ ⟨b, -, rfl⟩
      exact (hsmall b).le⟩
  have hs0 : 0 ≤ doubleBlockDistToOne V c :=
    Real.sSup_nonneg (by
      rintro _ ⟨b, -, rfl⟩
      exact norm_nonneg _)
  have hs : ∀ b ∈ doubleBlockBonds c, ‖V b - 1‖ ≤ doubleBlockDistToOne V c :=
    fun b hb => le_csSup hbdd ⟨b, hb, rfl⟩
  have hH := hHol L hL n k j hn hj c hc
  have hK := hKer L hL n k j hn hj c hc
  refine ⟨fun b hb X hX => ?_, fun y hy x hx X hX => ?_⟩
  · have K : AdmissibleKernels (polydiscRadius L) c fun W => stepKernel W c b :=
      { bounded := fun W hW hn => (hK W hW hn).2.1 b hb
        coeff_local := fun W hW W' hW' he a' a =>
          hH.smoothing_local W hW W' hW' he ⟨b, hb.2⟩ hb.1 a' a
        coeff_holomorphic := fun a' a => hH.smoothing_holomorphic ⟨b, hb.2⟩ hb.1 a' a }
    exact K.norm_sub_le hM hEL hρ.pos hρ.le_one F hV hsmall hs0 hs hX
  · have h3 : (3 : ℝ) ≤ 80 * (polydiscRadius L)⁻¹ := by
      have h1 : 1 ≤ (polydiscRadius L)⁻¹ := (one_le_inv₀ hρ.pos).2 hρ.le_one
      linarith
    have K : AdmissibleKernels (polydiscRadius L) c
        fun W => ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy W y x) :=
      { bounded := fun W hW hn => by
          have h := (hK W hW hn).2.2 y hy x hx
          exact ⟨h.mapsTo, h.map_add, h.map_smul, fun X hX =>
            (h.norm_le X hX).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg X))⟩
        coeff_local := fun W hW W' hW' he a' a =>
          hH.conjugation_local W hW W' hW' he y hy x hx a' a
        coeff_holomorphic := fun a' a => hH.conjugation_holomorphic y hy x hx a' a }
    have h := K.norm_sub_le hM hEL hρ.pos hρ.le_one F hV hsmall hs0 hs hX
    have e : PeriodicLattice.complexMeanContourHolonomy
        (fun _ : Edge L n k j => (1 : ComplexMatrix2)) y x = 1 :=
      complexMeanContourHolonomy_trivial hCx hTr hL hn hj y hx
    simp only [e] at h
    simpa [ComplexMatrix2.conjugateBy] using h
end YangMills.Construction.Tower.NearIdentityStepKernels
end
