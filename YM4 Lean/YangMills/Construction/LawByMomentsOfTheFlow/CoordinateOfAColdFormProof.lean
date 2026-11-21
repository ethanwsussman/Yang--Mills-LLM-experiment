import YangMills.Construction.LawByMomentsOfTheFlow.CoordinateOfAColdForm
import YangMills.Construction.ResponseInTheExpansion.CoordinateOfASmallFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses
namespace MomentMethod
namespace ColdFormCoordinate
variable {F : BlockFrame}
private def allTopBonds (F : BlockFrame) : Finset (F.Site F.top × Fin 4) := finiteCells F ×ˢ Finset.univ
private theorem mem_allTopBonds (hs : ∀ i, 0 < F.extent i) (b : F.Site F.top × Fin 4) : b ∈ allTopBonds F :=
  Finset.mem_product.2 ⟨TopLevelSites.mem_finiteCells hs _, Finset.mem_univ _⟩
private theorem norm_sub_sub_deriv_le_of_deriv2 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ → E) (K : ℝ)
    (hp : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 p u)
    (hK : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖deriv (deriv p) u‖ ≤ K) : ‖p 1 - p 0 - deriv p 0‖ ≤ K := by apply _root_.YangMills.SharedProofs.p29740 <;> assumption
private theorem contDiffAt_line_and_derivs {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : P → E) (v : P) (hJ : ContDiffAt ℝ 3 J 0) :
    ContDiffAt ℝ 3 (fun τ : ℝ => J (τ • v)) 0 ∧ deriv (fun τ : ℝ => J (τ • v)) 0 = fderiv ℝ J 0 v ∧
      deriv (deriv fun τ : ℝ => J (τ • v)) 0 = iteratedFDeriv ℝ 2 J 0 ![v, v] := by apply _root_.YangMills.SharedProofs.p62688 <;> assumption
section Estimates
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem estimatesAt_of (hc : c.Admissible a L) (hF : IsBlockTorus L F) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) : c.EstimatesAt a c.σA W :=
  hc.estimates F c.σA W hF hc.positivity.2.2.2.1 le_rfl hW
private theorem contDiffThree_coordinate (hc : c.Admissible a L) (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top} (hW : IsSmallCurvature c.σA W) :
    ContDiffThreeAlongBonds (torusCoordinate a c.ρA b) W := fun k cc X =>
  (((estimatesAt_of hc hF hW).coordinates b hb).1 k cc X).contDiffAt
private theorem norm_bondDeriv_coordinate_le (hc : c.Admissible a L) (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top} (hW : IsSmallCurvature c.σA W) {k : ℕ}
    (cc : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) (hX : AreUnitVectors X) :
    ‖bondDeriv (torusCoordinate a c.ρA b) W cc X‖ ≤
      c.N k * Real.exp (-c.δ₁ * bondListDistance (enclosingCell b.1) cc) :=
  ((estimatesAt_of hc hF hW).coordinates b hb).2 k cc X hk hX
private def halfRateWeight (δ : ℝ) (Y : F.Cell) (e : ↥(allTopBonds F)) : ℝ :=
  Real.exp (-(δ / 2 * (cellSupDist Y e.1.1 : ℝ)))
private theorem halfRateWeight_nonneg (δ : ℝ) (Y : F.Cell) (e : ↥(allTopBonds F)) : 0 ≤ halfRateWeight δ Y e :=
  (Real.exp_pos _).le
private theorem norm_iteratedFDeriv_two_composition_le (hJ : FormCompositionJet) (hc : c.Admissible a L)
    (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) (v : ↥(allTopBonds F) → imaginaryQuaternions) :
    ‖iteratedFDeriv ℝ 2 (formComposition (allTopBonds F) (torusCoordinate a c.ρA b) W) 0 ![v, v]‖ ≤
      c.N 2 * (∑ e, halfRateWeight c.δ₁ (enclosingCell b.1) e * ‖v e‖) ^ 2 := by
  classical
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hN : 0 < c.N 2 := hc.positivity.2.2.2.2.2.1 2
  set Y : F.Cell := enclosingCell b.1 with hY
  have hjet := (hJ imaginaryQuaternions F F.top (allTopBonds F) (torusCoordinate a c.ρA b) W
    (contDiffThree_coordinate hc hF hb hW)).2.2 2
    (fun cc => c.N 2 * (halfRateWeight c.δ₁ Y (cc 0) * halfRateWeight c.δ₁ Y (cc 1))) (by norm_num)
    (fun cc => mul_nonneg hN.le (mul_nonneg (halfRateWeight_nonneg _ _ _) (halfRateWeight_nonneg _ _ _)))
    (fun cc X hX => by
      refine (norm_bondDeriv_coordinate_le hc hF hb hW _ X (by norm_num) hX).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hN.le
      unfold halfRateWeight
      rw [← Real.exp_add, Real.exp_le_exp]
      have h0 : cellSupDist Y (cc 0).1.1 ≤ bondListDistance Y (fun l => (cc l).1) :=
        Finset.le_sup (f := fun l => cellSupDist Y ((fun l => (cc l).1) l).1) (Finset.mem_univ (0 : Fin 2))
      have h1 : cellSupDist Y (cc 1).1.1 ≤ bondListDistance Y (fun l => (cc l).1) :=
        Finset.le_sup (f := fun l => cellSupDist Y ((fun l => (cc l).1) l).1) (Finset.mem_univ (1 : Fin 2))
      have h0' : (cellSupDist Y (cc 0).1.1 : ℝ) ≤ bondListDistance Y (fun l => (cc l).1) := by exact_mod_cast h0
      have h1' : (cellSupDist Y (cc 1).1.1 : ℝ) ≤ bondListDistance Y (fun l => (cc l).1) := by exact_mod_cast h1
      nlinarith) ![v, v]
  refine hjet.trans (le_of_eq ?_)
  set f : ↥(allTopBonds F) → ℝ := fun e => halfRateWeight c.δ₁ Y e * ‖v e‖ with hf
  have h2 : ∑ cc : Fin 2 → ↥(allTopBonds F), f (cc 0) * f (cc 1) = (∑ e, f e) ^ 2 := by
    have := Finset.prod_univ_sum (fun _ : Fin 2 => (Finset.univ : Finset ↥(allTopBonds F))) (fun _ e => f e)
    rw [Fintype.piFinset_univ, Fin.prod_univ_two] at this
    simp only [Fin.prod_univ_two] at this
    rw [sq]
    exact this.symm
  rw [← h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun cc _ => ?_
  rw [Fin.prod_univ_two]
  simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring
private theorem bondDeriv_eq_fderiv_composition (hJ : FormCompositionJet) (hc : c.Admissible a L)
    (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) (e : ↥(allTopBonds F)) (v : imaginaryQuaternions) :
    bondDeriv (torusCoordinate a c.ρA b) W ![e.1] ![v] =
      fderiv ℝ (formComposition (allTopBonds F) (torusCoordinate a c.ρA b) W) 0 (singleBondForm e v) := by apply _root_.YangMills.DeltaSharedProofs.p502378 <;> assumption
private theorem bondDeriv_uniform_eq_smul (hFl : FlatCoordinatesScalar) (hJ : FormCompositionJet)
    (hL : Odd L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hW : IsSmallCurvature c.σA (uniformField F F.top))
    (e : ↥(allTopBonds F)) (X v : imaginaryQuaternions) (hX : ‖X‖ = 1) :
    bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e.1] ![v] = flatCoefficient a c.ρA X b e.1 • v := by apply _root_.YangMills.DeltaSharedProofs.p500538 <;> assumption
end Estimates
private theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
private theorem sum_halfRateWeight_eq (δ : ℝ) (Y : F.Cell) (D : F.Cell → Fin 4 → imaginaryQuaternions) :
    ∑ e : ↥(allTopBonds F), halfRateWeight δ Y e * ‖D e.1.1 e.1.2‖ = decayWeightedNorm δ Y D := by
  classical
  unfold halfRateWeight decayWeightedNorm
  rw [Finset.sum_coe_sort (allTopBonds F) fun e => Real.exp (-(δ / 2 * (cellSupDist Y e.1 : ℝ))) * ‖D e.1 e.2‖]
  unfold allTopBonds
  rw [Finset.sum_product]
end ColdFormCoordinate
open ColdFormCoordinate in
theorem coldFormCoordinateStatement_holds (hFl : FlatCoordinatesScalar)
    (hJ : FormCompositionJet) : coldFormCoordinateStatement := by
  intro a L c hL hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hN1 : 0 < c.N 1 := hc.positivity.2.2.2.2.2.1 1
  have hN2 : 0 < c.N 2 := hc.positivity.2.2.2.2.2.1 2
  refine ⟨c.N 2 + c.N 1, by positivity, ?_⟩
  intro F b D X hF hb hX hsmall
  classical
  obtain ⟨n, hn, hext⟩ := hF.2
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hext i]; omega
  set G := torusCoordinate a c.ρA b with hG
  set v : ↥(allTopBonds F) → imaginaryQuaternions := fun e => D e.1.1 e.1.2 with hv
  set P : ℝ → F.GaugeField F.top := fun u => leftTranslate (fun y i => u • D y i) (uniformField F F.top) with hP
  set p : ℝ → imaginaryQuaternions := fun u => G (P u) with hp
  set Sz := decayWeightedNorm c.δ₁ (enclosingCell b.1) D with hSz
  have hSz0 : 0 ≤ Sz := by
    refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun i _ => by positivity
  have hsmall' : ∀ u ∈ Set.Icc (0 : ℝ) 1, IsSmallCurvature c.σA (P u) := fun u hu => hsmall u hu.1 hu.2
  have hzero : ∀ τ : ℝ, extendByZero (τ • v) = fun y i => τ • D y i := fun τ => by
    funext y i
    unfold extendByZero
    rw [dif_pos (mem_allTopBonds hs _)]
    rfl
  have hshift : ∀ u τ : ℝ, P (u + τ) = leftTranslate (extendByZero (τ • v)) (P u) := fun u τ => by
    rw [hzero]
    funext y i
    simp only [hP, leftTranslate, ColdStepAtMirrorFrames.uniformField, mul_one]
    rw [add_comm u τ, _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits.expUnit_add_smul]
  have hline : ∀ u : ℝ, (fun τ : ℝ => formComposition (allTopBonds F) G (P u) (τ • v)) = fun τ => p (u + τ) :=
    fun u => by
      funext τ
      simp only [hp, hshift, formComposition]
  have hstep : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 p u ∧ ‖deriv (deriv p) u‖ ≤ c.N 2 * Sz ^ 2 := by
    intro u hu
    have hW := hsmall' u hu
    obtain ⟨hc3, -, -⟩ := hJ imaginaryQuaternions F F.top (allTopBonds F) G (P u) (contDiffThree_coordinate hc hF hb hW)
    obtain ⟨l1, -, l3⟩ := contDiffAt_line_and_derivs _ v hc3
    rw [hline u] at l1 l3
    constructor
    · have h1 : ContDiffAt ℝ 3 (fun x : ℝ => x - u) u := contDiffAt_id.sub contDiffAt_const
      have l1' : ContDiffAt ℝ 3 (fun τ => p (u + τ)) (u - u) := by simpa using l1
      have h2 := ContDiffAt.comp (g := fun τ => p (u + τ)) (f := fun x : ℝ => x - u) u l1' h1
      have e : (fun τ => p (u + τ)) ∘ (fun x : ℝ => x - u) = p := by
        funext x
        simp
      rwa [e] at h2
    · have e1 : deriv (fun τ => p (u + τ)) = fun τ => deriv p (u + τ) :=
        funext fun τ => deriv_comp_const_add p u τ
      rw [e1, deriv_comp_const_add (deriv p) u 0, add_zero] at l3
      rw [l3]
      have := norm_iteratedFDeriv_two_composition_le hJ hc hF hb hW v
      rwa [sum_halfRateWeight_eq] at this
  have hunif : P 0 = uniformField F F.top := by
    funext y i
    simp only [hP, leftTranslate, zero_smul, ColdStepAtMirrorFrames.uniformField, mul_one]
    exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits.expUnit_zero
  have hW0 : IsSmallCurvature c.σA (uniformField F F.top) := by
    rw [← hunif]
    exact hsmall' 0 (by simp)
  have hp0 : p 0 = 0 := by
    simp only [hp, hunif, hG]
    exact (hFl a L c hL hc F b (0, 0) X hF hX).1
  have hp1 : p 1 = torusCoordinate a c.ρA b (leftTranslate D (uniformField F F.top)) := by
    simp only [hp, hP, one_smul, hG]
  have hd0 : deriv p 0 = flatLinearPart a c.ρA X b D := by
    obtain ⟨hc3, -, -⟩ := hJ imaginaryQuaternions F F.top (allTopBonds F) G (uniformField F F.top)
      (contDiffThree_coordinate hc hF hb hW0)
    obtain ⟨-, l2, -⟩ := contDiffAt_line_and_derivs _ v hc3
    have e1 : (fun τ : ℝ => formComposition (allTopBonds F) G (uniformField F F.top) (τ • v)) = p := by
      funext τ
      simp only [formComposition, hzero, hp, hP]
    rw [e1] at l2
    rw [l2]
    have e2 : v = ∑ e, singleBondForm e (v e) := by
      unfold singleBondForm
      exact (Finset.univ_sum_single v).symm
    nth_rewrite 1 [e2]
    rw [map_sum]
    have e3 : ∀ e : ↥(allTopBonds F),
        fderiv ℝ (formComposition (allTopBonds F) G (uniformField F F.top)) 0 (singleBondForm e (v e)) =
          flatCoefficient a c.ρA X b e.1 • D e.1.1 e.1.2 := fun e => by
      rw [← bondDeriv_eq_fderiv_composition hJ hc hF hb hW0]
      exact bondDeriv_uniform_eq_smul hFl hJ hL hc hF hb hW0 e X _ hX
    simp only [e3]
    rw [Finset.sum_coe_sort (allTopBonds F) fun e => flatCoefficient a c.ρA X b e • D e.1 e.2]
    unfold allTopBonds flatLinearPart
    rw [Finset.sum_product]
  have hT := norm_sub_sub_deriv_le_of_deriv2 p _ (fun u hu => (hstep u hu).1) (fun u hu => (hstep u hu).2)
  rw [hp0, sub_zero, hp1, hd0] at hT
  have hlin : ‖((flatLinearPart a c.ρA X b D : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ c.N 1 * Sz := by
    have hcoef : ∀ e : F.Site F.top × Fin 4, |flatCoefficient a c.ρA X b e| ≤
        c.N 1 * Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1) e.1 : ℝ))) := by
      intro e
      have h1 := norm_bondDeriv_coordinate_le hc hF hb hW0 ![e] ![X] (by norm_num) (fun l => by fin_cases l; exact hX)
      have h2 : |flatCoefficient a c.ρA X b e| ≤
          ‖bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e] ![X]‖ := by
        unfold flatCoefficient
        rw [abs_neg]
        refine (abs_re_le_norm _).trans ?_
        rw [norm_mul]
        have hX' : ‖(X : ℍ[ℝ])‖ = 1 := hX
        rw [hX', mul_one]
        rfl
      refine h2.trans (h1.trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hN1.le
      rw [Real.exp_le_exp]
      have h3 : bondListDistance (enclosingCell b.1) ![e] = cellSupDist (enclosingCell b.1) e.1 := by
        unfold bondListDistance
        simp [Finset.univ_unique]
      rw [h3]
      nlinarith
    unfold flatLinearPart
    change ‖(∑ z ∈ finiteCells F, ∑ i : Fin 4, flatCoefficient a c.ρA X b (z, i) • D z i : imaginaryQuaternions)‖ ≤ _
    calc ‖(∑ z ∈ finiteCells F, ∑ i : Fin 4, flatCoefficient a c.ρA X b (z, i) • D z i : imaginaryQuaternions)‖
        ≤ ∑ z ∈ finiteCells F, ∑ i : Fin 4, |flatCoefficient a c.ρA X b (z, i)| * ‖D z i‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ z ∈ finiteCells F, ∑ i : Fin 4,
            c.N 1 * (Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1) z : ℝ))) * ‖D z i‖) :=
          Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun i _ => by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (hcoef (z, i)) (norm_nonneg _)
      _ = c.N 1 * Sz := by
          simp only [hSz, decayWeightedNorm, Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · refine le_trans hT ?_
    nlinarith
  · refine hlin.trans ?_
    nlinarith
end MomentMethod
end YangMills.Construction
end
