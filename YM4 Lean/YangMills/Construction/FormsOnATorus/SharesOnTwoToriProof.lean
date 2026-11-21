import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMovesProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.FormsOnATorus.ActionOnTwoToriProof
import YangMills.Construction.FormsOnATorus.SharesOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusComparison
open TorusFields TorusLumps TorusPaths TorusChain LevelAction StepCosts ColdChain BlockAverages TorusContours
section
variable {n k : ℕ}
section
private def plaquetteWord (p : TorusPlaquette n) : BondWord n :=
  [((p.1, p.2.1), true), ((p.1 + TorusFields.unitStep n p.2.1, p.2.2), true),
    ((p.1 + TorusFields.unitStep n p.2.2, p.2.1), false),
    ((p.1, p.2.2), false)]
private theorem holonomy_eq_wordHolonomy (W : TorusField n) (p : TorusPlaquette n) :
    holonomy W p.1 p.2.1 p.2.2 = wordHolonomy W (plaquetteWord p) := by apply _root_.YangMills.Construction.LevelAction.holonomy_eq_wordHolonomy_plaquetteWord <;> assumption
private def realPartCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
private theorem norm_realPartCLM_le : ‖realPartCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  show |q.re| ≤ 1 * ‖q‖
  rw [one_mul]
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg q)
  have h : ‖q‖ ^ 2 = Quaternion.normSq q := by rw [Quaternion.normSq_eq_norm_mul_self]; ring
  rw [h, Quaternion.normSq_def']
  nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
private def perturbedEnergy (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n)
    (p : TorusPlaquette n) (σ : Fin k → ℝ) : ℝ :=
  plaquetteEnergy (perturb c Xs σ W) p.1 p.2.1 p.2.2
private theorem perturbedEnergy_eq (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n)
    (p : TorusPlaquette n) :
    perturbedEnergy c Xs W p = (fun _ => (1 : ℝ)) + -(realPartCLM ∘ perturbedHolonomy c Xs W (plaquetteWord p)) := by
  funext σ
  show 1 - ((holonomy (perturb c Xs σ W) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]).re =
    1 + -((wordHolonomy (perturb c Xs σ W) (plaquetteWord p) : UnitQuaternion) : ℍ[ℝ]).re
  rw [holonomy_eq_wordHolonomy, sub_eq_add_neg]
private theorem contDiff_perturbedEnergy (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (W : TorusField n) (p : TorusPlaquette n) : ContDiff ℝ ⊤ (perturbedEnergy c Xs W p) := by
  rw [perturbedEnergy_eq]
  exact contDiff_const.add (realPartCLM.contDiff.comp (contDiff_perturbedHolonomy c Xs W _)).neg
private def perturbedEnergyMixed (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n)
    (p : TorusPlaquette n) : ℝ :=
  iteratedFDeriv ℝ k (perturbedEnergy c Xs W p) 0 fun l => Pi.single l 1
private theorem abs_perturbedEnergyMixed_le (hk1 : 1 ≤ k) (hk : k ≤ 3) (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) (hX : AreUnitVectors Xs) (W : TorusField n) (p : TorusPlaquette n) :
    |perturbedEnergyMixed c Xs W p| ≤ (8 * letterDerivBound) ^ 4 := by
  have hg : ContDiff ℝ ⊤ (realPartCLM ∘ perturbedHolonomy c Xs W (plaquetteWord p)) :=
    realPartCLM.contDiff.comp (contDiff_perturbedHolonomy c Xs W _)
  have h1 : iteratedFDeriv ℝ k (perturbedEnergy c Xs W p) 0 =
      -(realPartCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (perturbedHolonomy c Xs W (plaquetteWord p)) 0)) := by
    have hg' : ContDiffAt ℝ k (-(realPartCLM ∘ perturbedHolonomy c Xs W (plaquetteWord p))) 0 :=
      (hg.neg.contDiffAt).of_le le_top
    have hc' : ContDiffAt ℝ k (fun _ : Fin k → ℝ => (1 : ℝ)) 0 := contDiff_const.contDiffAt
    rw [perturbedEnergy_eq, iteratedFDeriv_add_apply hc' hg']
    have h0 : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (1 : ℝ)) = 0 :=
      iteratedFDeriv_const_of_ne (by omega) 1
    rw [h0, Pi.zero_apply, zero_add, iteratedFDeriv_neg_apply,
      realPartCLM.iteratedFDeriv_comp_left (n := ⊤) (contDiff_perturbedHolonomy c Xs W _).contDiffAt
        (by exact_mod_cast le_top)]
  have h2 : ‖iteratedFDeriv ℝ k (perturbedEnergy c Xs W p) 0‖ ≤ (8 * letterDerivBound) ^ 4 := by
    rw [h1, norm_neg]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h3 := norm_iteratedFDeriv_perturbedHolonomy_le c Xs hX hk W (plaquetteWord p) hk
    have h4 : (plaquetteWord p).length = 4 := rfl
    rw [h4] at h3
    calc _ ≤ 1 * (8 * letterDerivBound) ^ 4 := mul_le_mul norm_realPartCLM_le h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact (Real.norm_eq_abs _ ▸ norm_iteratedFDeriv_coordinates_le (perturbedEnergy c Xs W p)).trans h2
private theorem perturbedEnergyMixed_eq_zero (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (W : TorusField n) (p : TorusPlaquette n) (l₀ : Fin k) (hl : ∀ e ∈ plaquetteWord p, c l₀ ≠ e.1) :
    perturbedEnergyMixed c Xs W p = 0 := by
  refine congrArg (fun z => z) (iteratedFDeriv_coordinates_eq_zero_of_update (contDiff_perturbedEnergy c Xs W p) l₀
    fun σ => ?_) |>.trans rfl
  unfold perturbedEnergy plaquetteEnergy
  rw [holonomy_eq_wordHolonomy, holonomy_eq_wordHolonomy, wordHolonomy_perturb_update c Xs σ W _ l₀ 0 hl]
private theorem fst_mem_plaquetteVertices (p : TorusPlaquette n) {e : TorusBond n × Bool} (he : e ∈ plaquetteWord p) :
    e.1.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by apply _root_.YangMills.Construction.LevelAction.fst_fst_mem_plaquetteVertices <;> assumption
private theorem card_plaquettes_mem_vertices_le [NeZero n] (y : TorusSite n) :
    (Finset.univ.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2).card ≤ 64 := by apply _root_.YangMills.Construction.LevelAction.card_plaquettes_with_vertex_le <;> assumption
private theorem mixedDeriv_weightedSum [NeZero n] (P : Finset (TorusPlaquette n)) (w : TorusPlaquette n → ℝ)
    (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n) :
    mixedDeriv (fun W' => ∑ p ∈ P, w p * plaquetteEnergy W' p.1 p.2.1 p.2.2) W c Xs =
      ∑ p ∈ P, w p * perturbedEnergyMixed c Xs W p := by
  unfold mixedDeriv
  have hf : ∀ p ∈ P, ContDiffAt ℝ k (fun σ => w p • perturbedEnergy c Xs W p σ) 0 := fun p _ =>
    ((contDiff_perturbedEnergy c Xs W p).const_smul (w p)).contDiffAt.of_le le_top
  have h1 : (fun σ : Fin k → ℝ => ∑ p ∈ P, w p * plaquetteEnergy (perturb c Xs σ W) p.1 p.2.1 p.2.2) =
      fun σ => ∑ p ∈ P, (fun σ' => w p • perturbedEnergy c Xs W p σ') σ := rfl
  rw [h1, iteratedFDeriv_fun_sum_apply hf, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h2 : iteratedFDeriv ℝ k (fun σ' => w p • perturbedEnergy c Xs W p σ') 0 =
      w p • iteratedFDeriv ℝ k (perturbedEnergy c Xs W p) 0 :=
    iteratedFDeriv_const_smul_apply' ((contDiff_perturbedEnergy c Xs W p).contDiffAt.of_le le_top)
  rw [h2]
  rfl
private theorem abs_weightedMixed_le [NeZero n] (hk1 : 1 ≤ k) (hk : k ≤ 3) (P : Finset (TorusPlaquette n))
    (w : TorusPlaquette n → ℝ) (y : TorusSite n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors Xs) (W : TorusField n) (hw : ∀ p, |w p| ≤ 1)
    (hy : ∀ p, y ∉ plaquetteVertices p.1 p.2.1 p.2.2 → w p * perturbedEnergyMixed c Xs W p = 0) :
    |∑ p ∈ P, w p * perturbedEnergyMixed c Xs W p| ≤ 64 * (8 * letterDerivBound) ^ 4 := by
  classical
  set B := (8 * letterDerivBound) ^ 4 with hB
  have hB0 : 0 ≤ B := by
    have := one_le_letterDerivBound
    positivity
  have h1 : ∑ p ∈ P, w p * perturbedEnergyMixed c Xs W p =
      ∑ p ∈ P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2,
        w p * perturbedEnergyMixed c Xs W p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rfl
    · exact hy p h
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h2 : ∀ p ∈ P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2,
      |w p * perturbedEnergyMixed c Xs W p| ≤ B := by
    intro p _
    rw [abs_mul]
    calc |w p| * |perturbedEnergyMixed c Xs W p| ≤ 1 * B :=
          mul_le_mul (hw p) (abs_perturbedEnergyMixed_le hk1 hk c Xs hX W p) (abs_nonneg _) zero_le_one
      _ = B := one_mul _
  refine (Finset.sum_le_card_nsmul _ _ B h2).trans ?_
  rw [nsmul_eq_mul]
  have h3 : ((P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2).card : ℝ) ≤ 64 := by
    have : (P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2).card ≤ 64 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
        (card_plaquettes_mem_vertices_le y)
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right h3 hB0
end
section
variable [NeZero n]
private def vertexWeight (y : TorusSite n) (p : TorusPlaquette n) : ℝ :=
  (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4
private theorem abs_vertexWeight_le (y : TorusSite n) (p : TorusPlaquette n) : |vertexWeight y p| ≤ 1 := by
  unfold vertexWeight
  have h : (plaquetteVertices p.1 p.2.1 p.2.2).count y ≤ 4 := List.count_le_length
  have h' : (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h
  rw [abs_of_nonneg (by positivity)]
  linarith
private theorem vertexWeight_eq_zero {y : TorusSite n} {p : TorusPlaquette n}
    (h : y ∉ plaquetteVertices p.1 p.2.1 p.2.2) : vertexWeight y p = 0 := by
  simp [vertexWeight, List.count_eq_zero_of_not_mem h]
private theorem levelShare_zero (a : ℝ) (L : ℕ) (X : Finset (TorusSite n)) (y : TorusSite n) :
    levelShare a L 0 X y = fun W' => ∑ p ∈ plaquettesIn X, vertexWeight y p * plaquetteEnergy W' p.1 p.2.1 p.2.2 :=
  rfl
private theorem actionAtLevel_zero_eq_sum (a : ℝ) (L : ℕ) (X : Finset (TorusSite n)) :
    actionAtLevel a L 0 X = fun W'' => ∑ y, levelShare a L 0 X y W'' := by apply _root_.YangMills.Construction.LevelAction.actionAtLevel_zero_eq_sum <;> assumption
private theorem one_le_exp_one_mul_exp {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) {d : ℕ} (hd : d ≤ 4) :
    (1 : ℝ) ≤ Real.exp 1 * Real.exp (-δ * d) := by apply _root_.YangMills.Construction.LevelAction.one_le_exp_one_mul_exp <;> assumption
private def baseLevelBound : ℝ := 64 * (8 * letterDerivBound) ^ 4 * Real.exp 1
private theorem baseLevelBound_nonneg : 0 ≤ baseLevelBound := by
  have := one_le_letterDerivBound
  unfold baseLevelBound
  positivity
private theorem abs_mixedDeriv_levelShare_zero_le {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (a : ℝ) (L : ℕ)
    (X : Finset (TorusSite n)) (W : TorusField n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (l₀ : Fin k) (hk1 : 1 ≤ k) (hk : k ≤ 3) (hX : AreUnitVectors Xs) (y : TorusSite n) :
    |mixedDeriv (levelShare a L 0 X y) W c Xs| ≤ baseLevelBound * Real.exp (-δ * supDist y (c l₀).1) := by
  rw [levelShare_zero, mixedDeriv_weightedSum]
  by_cases hd : supDist y (c l₀).1 ≤ 4
  · have h1 := abs_weightedMixed_le hk1 hk (plaquettesIn X) (vertexWeight y) y c Xs hX W (abs_vertexWeight_le y)
      fun p hp => by rw [vertexWeight_eq_zero hp, zero_mul]
    have h2 := one_le_exp_one_mul_exp hδ hδ8 hd
    have h3 : 0 ≤ 64 * (8 * letterDerivBound) ^ 4 := by
      have := one_le_letterDerivBound
      positivity
    calc _ ≤ 64 * (8 * letterDerivBound) ^ 4 := h1
      _ ≤ 64 * (8 * letterDerivBound) ^ 4 * (Real.exp 1 * Real.exp (-δ * supDist y (c l₀).1)) :=
        le_mul_of_one_le_right h3 h2
      _ = _ := by unfold baseLevelBound; ring
  · have h0 : ∑ p ∈ plaquettesIn X, vertexWeight y p * perturbedEnergyMixed c Xs W p = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hy : y ∈ plaquetteVertices p.1 p.2.1 p.2.2
      · rw [perturbedEnergyMixed_eq_zero c Xs W p l₀ ?_, mul_zero]
        intro e he hce
        have hm := fst_mem_plaquetteVertices p he
        rw [← hce] at hm
        exact hd (supDist_le_four_of_mem_plaquetteVertices p hy hm)
      · rw [vertexWeight_eq_zero hy, zero_mul]
    rw [h0, abs_zero]
    have := baseLevelBound_nonneg
    positivity
private theorem contDiff_weightedEnergy (P : Finset (TorusPlaquette n)) (w : TorusPlaquette n → ℝ)
    (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n) :
    ContDiff ℝ ⊤ fun σ : Fin k → ℝ => ∑ p ∈ P, w p * plaquetteEnergy (perturb c Xs σ W) p.1 p.2.1 p.2.2 :=
  ContDiff.sum fun p _ => contDiff_const.mul (contDiff_perturbedEnergy c Xs W p)
end
end
section
variable {n : ℕ} [NeZero n]
private theorem siteOfInt_inj_of_offsetInBox {u v : Fin 4 → ℤ} {q : ℕ} (hu : OffsetInBox q u) (hv : OffsetInBox q v)
    (hq : 2 * q < n) (h : (siteOfInt u : TorusSite n) = siteOfInt v) : u = v := by apply _root_.YangMills.SharedProofs.p64386 (n := n) <;> assumption
end
section
variable {n k : ℕ} [NeZero n]
private def offsetValue (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (u : Fin 4 → ℤ) (i : Fin 4) : UnitQuaternion :=
  open Classical in expUnit (∑ l, if c l = (u, i) then σ l • Xs l else 0)
private theorem perturb_trivialField_add_siteOfInt {c : Fin k → (Fin 4 → ℤ) × Fin 4}
    (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) (z : TorusSite n) {q : ℕ} (hq : 2 * q < n)
    (hc : ∀ l, OffsetInBox q (c l).1) {u : Fin 4 → ℤ} (hu : OffsetInBox q u) (i : Fin 4) :
    perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n) (z + siteOfInt u) i = offsetValue c Xs σ u i := by
  classical
  show expUnit (∑ l, if bondFrom z (c l) = (z + siteOfInt u, i) then σ l • Xs l else 0) * 1 = _
  rw [mul_one]
  unfold offsetValue
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = (u, i)
  · have : bondFrom z (c l) = (z + siteOfInt u, i) := by rw [h]; rfl
    rw [if_pos this, if_pos h]
  · have : ¬ bondFrom z (c l) = (z + siteOfInt u, i) := by
      intro he
      apply h
      have h1 : z + siteOfInt (c l).1 = z + siteOfInt u := congrArg Prod.fst he
      have h2 : (c l).2 = i := congrArg Prod.snd he
      exact Prod.ext (siteOfInt_inj_of_offsetInBox (hc l) hu hq (add_left_cancel h1)) h2
    rw [if_neg this, if_neg h]
private def offsetEnergy (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (h : Fin 4 → ℤ) (μ ν : Fin 4) : ℝ :=
  1 - ((offsetValue c Xs σ h μ * offsetValue c Xs σ (h + Pi.single μ 1) ν *
    (offsetValue c Xs σ (h + Pi.single ν 1) μ)⁻¹ * (offsetValue c Xs σ h ν)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re
private theorem add_siteOfInt_add_unitStep (z : TorusSite n) (h : Fin 4 → ℤ) (μ : Fin 4) :
    z + siteOfInt h + TorusFields.unitStep n μ = z + siteOfInt (h + Pi.single μ 1) := by apply _root_.YangMills.Construction.AbelianSecondOrder.add_siteOfInt_unitStep <;> assumption
private theorem plaquetteEnergy_perturb_trivialField {c : Fin k → (Fin 4 → ℤ) × Fin 4}
    (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) (z : TorusSite n) {q : ℕ} (hq : 2 * q < n)
    (hc : ∀ l, OffsetInBox q (c l).1) {h : Fin 4 → ℤ} (hh : OffsetInBox (q - 1) h) (hq1 : 1 ≤ q) (μ ν : Fin 4) :
    plaquetteEnergy (perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n)) (z + siteOfInt h) μ ν =
      offsetEnergy c Xs σ h μ ν := by
  have h0 : OffsetInBox q h := fun i => (hh i).trans (by omega)
  have h1 : ∀ μ : Fin 4, OffsetInBox q (h + Pi.single μ 1) := by
    intro μ i
    have a := abs_le.mp (hh i)
    by_cases hi : i = μ
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      rw [abs_le]
      constructor <;> omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
      exact h0 i
  unfold plaquetteEnergy holonomy offsetEnergy
  rw [add_siteOfInt_add_unitStep, add_siteOfInt_add_unitStep,
    perturb_trivialField_add_siteOfInt Xs σ z hq hc h0, perturb_trivialField_add_siteOfInt Xs σ z hq hc (h1 μ),
    perturb_trivialField_add_siteOfInt Xs σ z hq hc (h1 ν), perturb_trivialField_add_siteOfInt Xs σ z hq hc h0]
private def vertexOffsets (h : Fin 4 → ℤ) (μ ν : Fin 4) : List (Fin 4 → ℤ) :=
  [h, h + Pi.single μ 1, h + Pi.single ν 1, h + Pi.single μ 1 + Pi.single ν 1]
private theorem offsetInBox_of_mem_vertexOffsets {h : Fin 4 → ℤ} {q : ℕ} (hh : OffsetInBox q h) (μ ν : Fin 4)
    {u : Fin 4 → ℤ} (hu : u ∈ vertexOffsets h μ ν) : OffsetInBox (q + 2) u := by apply _root_.YangMills.DeltaSharedProofs.p501882 <;> assumption
open Classical in
private def offsetPlaquettes (q : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(q : ℤ)) (q : ℤ)) ×ˢ
    (Finset.univ : Finset (Fin 4 × Fin 4))).filter fun τ => τ.2.1 < τ.2.2
private theorem mem_offsetPlaquettes {q : ℕ} {τ : (Fin 4 → ℤ) × Fin 4 × Fin 4} :
    τ ∈ offsetPlaquettes q ↔ OffsetInBox q τ.1 ∧ τ.2.1 < τ.2.2 := by apply _root_.YangMills.DeltaSharedProofs.p502338 <;> assumption
private theorem add_siteOfInt_zero {p : ℕ} (w : TorusSite p) : w + siteOfInt (0 : Fin 4 → ℤ) = w := by
  funext i
  simp [siteOfInt]
private theorem count_map_add_siteOfInt (z : TorusSite n) {q : ℕ} (hq : 2 * q < n) (l : List (Fin 4 → ℤ))
    (hl : ∀ u ∈ l, OffsetInBox q u) : (l.map fun u => z + siteOfInt u).count z = l.count 0 := by
  classical
  induction l with
  | nil => simp
  | cons u r ih =>
    have h1 := ih fun v hv => hl v (List.mem_cons_of_mem _ hv)
    have h2 := hl u List.mem_cons_self
    by_cases hu : u = 0
    · subst hu
      rw [List.map_cons, add_siteOfInt_zero, List.count_cons_self, List.count_cons_self, h1]
    · have h3 : z + siteOfInt u ≠ z := by
        intro he
        apply hu
        have h4 : (siteOfInt u : TorusSite n) = siteOfInt 0 := by
          have h5 : (z + siteOfInt u : TorusSite n) = z + siteOfInt 0 := by rw [he, add_siteOfInt_zero]
          exact add_left_cancel h5
        exact siteOfInt_inj_of_offsetInBox h2 (fun i => by simp) hq h4
      rw [List.map_cons, List.count_cons_of_ne h3, List.count_cons_of_ne hu, h1]
private theorem count_plaquetteVertices (z : TorusSite n) {h : Fin 4 → ℤ} {q : ℕ} (hh : OffsetInBox q h)
    (hq : 2 * (q + 2) < n) (μ ν : Fin 4) :
    (plaquetteVertices (z + siteOfInt h) μ ν).count z = (vertexOffsets h μ ν).count 0 := by
  have e : plaquetteVertices (z + siteOfInt h) μ ν = (vertexOffsets h μ ν).map fun u => z + siteOfInt u := by
    simp only [plaquetteVertices, vertexOffsets, List.map_cons, List.map_nil]
    rw [add_siteOfInt_add_unitStep, add_siteOfInt_add_unitStep, add_siteOfInt_add_unitStep]
  rw [e]
  exact count_map_add_siteOfInt z hq _ fun u hu => offsetInBox_of_mem_vertexOffsets hh μ ν hu
private theorem offsetInBox_neg_single (μ : Fin 4) : OffsetInBox 1 (-(Pi.single μ 1) : Fin 4 → ℤ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.offsetInBox_neg_single <;> assumption
private theorem offsetInBox_neg_single_sub_single {μ ν : Fin 4} (hne : μ ≠ ν) :
    OffsetInBox 1 (-(Pi.single μ 1) - Pi.single ν 1 : Fin 4 → ℤ) := by
  intro i
  by_cases hi : i = μ
  · subst hi
    simp [Pi.single_eq_of_ne hne]
  · by_cases hj : i = ν
    · subst hj
      simp [Pi.single_eq_of_ne hi]
    · simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]
private theorem siteOfInt_neg_single (μ : Fin 4) :
    (siteOfInt (-(Pi.single μ 1) : Fin 4 → ℤ) : TorusSite n) = - TorusFields.unitStep n μ := by
  have h := siteOfInt_single (m := n) μ
  rw [← h]
  funext i
  simp [siteOfInt]
private theorem mem_plaquettesIn_iff_lt_and_vertices [NeZero n] {S : Finset (TorusSite n)}
    {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by
  simp [plaquettesIn]
open Classical in
private theorem levelShare_zero_perturb {c : Fin k → (Fin 4 → ℤ) × Fin 4} (Xs : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (a : ℝ) (L : ℕ) (z : TorusSite n) {r w : ℕ} (hw : 1 ≤ w) (hc : ∀ l, OffsetInBox r (c l).1)
    (hn : 2 * (r + w + 2) < n) :
    levelShare a L 0 (Finset.univ : Finset (TorusSite n)) z
        (perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n)) =
      ∑ τ ∈ offsetPlaquettes w, (((vertexOffsets τ.1 τ.2.1 τ.2.2).count 0 : ℕ) : ℝ) / 4 *
        offsetEnergy c Xs σ τ.1 τ.2.1 τ.2.2 := by
  set W := perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n) with hW
  have hcq : ∀ l, OffsetInBox (r + w + 1) (c l).1 := fun l i => (hc l i).trans (by push_cast; omega)
  show ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), vertexWeight z p * plaquetteEnergy W p.1 p.2.1 p.2.2 = _
  set ι : (Fin 4 → ℤ) × Fin 4 × Fin 4 → TorusPlaquette n := fun τ => (z + siteOfInt τ.1, τ.2.1, τ.2.2) with hι
  have hbox : ∀ τ ∈ offsetPlaquettes w, OffsetInBox w τ.1 := fun τ hτ => (mem_offsetPlaquettes.mp hτ).1
  have hinj : Set.InjOn ι (offsetPlaquettes w) := by
    rintro ⟨h, μ, ν⟩ h1 ⟨h', μ', ν'⟩ h2 he
    have e1 : z + siteOfInt h = z + siteOfInt h' := congrArg Prod.fst he
    have e2 : (μ, ν) = (μ', ν') := congrArg Prod.snd he
    have e3 : h = h' :=
      siteOfInt_inj_of_offsetInBox (q := w) (hbox _ h1) (hbox _ h2) (by omega) (add_left_cancel e1)
    rw [e3, e2]
  have hsub : (offsetPlaquettes w).image ι ⊆ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
    intro p hp
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hp
    exact mem_plaquettesIn_iff_lt_and_vertices.mpr ⟨(mem_offsetPlaquettes.mp hτ).2, fun _ _ => Finset.mem_univ _⟩
  have hzero : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), p ∉ (offsetPlaquettes w).image ι →
      vertexWeight z p * plaquetteEnergy W p.1 p.2.1 p.2.2 = 0 := by
    rintro ⟨x, μ, ν⟩ hp hnot
    have hlt : μ < ν := (mem_plaquettesIn_iff_lt_and_vertices.mp hp).1
    rw [vertexWeight_eq_zero, zero_mul]
    intro hz
    apply hnot
    have hex : ∃ h : Fin 4 → ℤ, OffsetInBox w h ∧ x = z + siteOfInt h := by
      simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h | h | h
      · exact ⟨0, fun i => by rw [Pi.zero_apply, abs_zero]; omega, by rw [add_siteOfInt_zero, h]⟩
      · refine ⟨-(Pi.single μ 1), fun i => (offsetInBox_neg_single μ i).trans (by push_cast; omega), ?_⟩
        rw [siteOfInt_neg_single, h]
        abel
      · refine ⟨-(Pi.single ν 1), fun i => (offsetInBox_neg_single ν i).trans (by push_cast; omega), ?_⟩
        rw [siteOfInt_neg_single, h]
        abel
      · refine ⟨-(Pi.single μ 1) - Pi.single ν 1,
          fun i => (offsetInBox_neg_single_sub_single hlt.ne i).trans (by push_cast; omega), ?_⟩
        have e : (siteOfInt (-(Pi.single μ 1) - Pi.single ν 1 : Fin 4 → ℤ) : TorusSite n) =
            - TorusFields.unitStep n μ - TorusFields.unitStep n ν := by
          rw [sub_eq_add_neg, siteOfInt_add, siteOfInt_neg_single, siteOfInt_neg_single]
          abel
        rw [e, h]
        abel
    obtain ⟨h, hh, rfl⟩ := hex
    exact Finset.mem_image.mpr ⟨(h, μ, ν), mem_offsetPlaquettes.mpr ⟨hh, hlt⟩, rfl⟩
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  have hb := hbox τ hτ
  have e1 : plaquetteEnergy W (ι τ).1 (ι τ).2.1 (ι τ).2.2 = offsetEnergy c Xs σ τ.1 τ.2.1 τ.2.2 :=
    plaquetteEnergy_perturb_trivialField Xs σ z (by omega) hcq (fun i => (hb i).trans (by push_cast; omega))
      (by omega) _ _
  rw [e1]
  congr 1
  unfold vertexWeight
  rw [show (ι τ).1 = z + siteOfInt τ.1 from rfl, show (ι τ).2.1 = τ.2.1 from rfl,
    show (ι τ).2.2 = τ.2.2 from rfl, count_plaquetteVertices z hb (by omega)]
end
section
private theorem levelShare_succ_trivialField {n : ℕ} [NeZero n] (hSA : SharesSumToAction) {a δ lam ρ σA cg : ℝ}
    {L : ℕ} {N : ℕ → ℝ} (ha : 0 < a) (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ)
    (hn : 64 ≤ n) {X : Finset (TorusSite n)} (hreg : IsRegularRegion X 1024) :
    (actionAtLevel a L (t + 1) X = fun W'' => ∑ y, levelShare a L (t + 1) X y W'') ∧
    (∀ y, ContDiffThreeAt (levelShare a L (t + 1) X y) (trivialField n)) ∧
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (l₀ : Fin k) (y : TorusSite n),
      1 ≤ k → k ≤ 3 → AreUnitVectors Xs →
      |mixedDeriv (levelShare a L (t + 1) X y) (trivialField n) c Xs| ≤
        (N 1 + N 2 + N 3) * Real.exp (-δ * supDist y (c l₀).1) := by apply _root_.YangMills.SharedProofs.p19727 <;> assumption
private theorem abs_sub_mixedDeriv_levelShare_succ_le {n n' : ℕ} [NeZero n] [NeZero n'] {a δ lam ρ σA cg : ℝ}
    {L : ℕ} {N : ℕ → ℝ} (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n)
    (hn' : 64 ≤ n') {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')} (hreg : IsRegularRegion X 1024)
    (hreg' : IsRegularRegion X' 1024) {z : TorusSite n} {z' : TorusSite n'} {m r : ℕ} (hm : 2 * m + 2 < n)
    (hm' : 2 * m + 2 < n') (hr : 4 * r + 4 ≤ m)
    (hXX : ∀ h, OffsetInBox (2 * m) h → (z + siteOfInt h ∈ X ↔ z' + siteOfInt h ∈ X'))
    (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions) (hk : k ≤ 2) (hk1 : 1 ≤ k)
    (hX : AreUnitVectors Xs) (hcz : ∀ l, OffsetInBox r (c l).1) (u : Fin 4 → ℤ) (hu : OffsetInBox (m / 2) u) :
    |mixedDeriv (levelShare a L (t + 1) X (z + siteOfInt u)) (trivialField n) (fun l => bondFrom z (c l)) Xs -
      mixedDeriv (levelShare a L (t + 1) X' (z' + siteOfInt u)) (trivialField n') (fun l => bondFrom z' (c l)) Xs| ≤
      (1 + σA) * (N 1 + N 2 + N 3) * Real.exp (-δ * m) := by apply _root_.YangMills.SharedProofs.p46974 <;> assumption
end
private theorem isRegularRegion_univ {n : ℕ} [NeZero n] :
    IsRegularRegion (Finset.univ : Finset (TorusSite n)) 1024 :=
  fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
theorem flatSharesOnTwoTori_of_sharesSumToAction (hSA : SharesSumToAction) : FlatSharesOnTwoTori := by
  intro a δ L lam ρ σA cg N ha hL hc
  have hc0 := hc
  obtain ⟨hδ, hδ8, -, -, -, hσ, -, hN, -⟩ := hc
  have hN1 := hN 1
  have hN2 := hN 2
  have hN3 := hN 3
  have hz := baseLevelBound_nonneg
  set M := N 1 + N 2 + N 3 with hM
  have hM0 : 0 ≤ M := by positivity
  set D := 1 + baseLevelBound + (1 + σA) * M with hD
  have hDpos : 0 < D := by positivity
  have hMD : M ≤ D := by
    have : 0 ≤ σA * M := by positivity
    rw [hD]
    nlinarith
  have hzD : baseLevelBound ≤ D := by
    have : 0 ≤ (1 + σA) * M := by positivity
    rw [hD]
    linarith
  have hSD : (1 + σA) * M ≤ D := by
    rw [hD]
    linarith
  refine ⟨D, hDpos, fun t n _ hn => ?_, fun t n n' _ _ z z' m r hn hn' hm hm' hr k c Xs hk1 hk hX hcz => ?_⟩
  · cases t with
    | zero =>
      refine ⟨actionAtLevel_zero_eq_sum a L _, fun y k c Xs => ?_, fun k c Xs l₀ y a1 a2 a3 => ?_⟩
      · rw [levelShare_zero]
        exact ((contDiff_weightedEnergy (plaquettesIn Finset.univ) (vertexWeight y) c Xs
          (trivialField n)).of_le le_top).contDiffAt
      · exact (abs_mixedDeriv_levelShare_zero_le hδ hδ8 a L _ (trivialField n) c Xs l₀ a1 a2 a3 y).trans
          (mul_le_mul_of_nonneg_right hzD (Real.exp_pos _).le)
    | succ t =>
      obtain ⟨s1, s2, s3⟩ := levelShare_succ_trivialField hSA ha hL hc0 t hn isRegularRegion_univ (N := N)
      exact ⟨s1, s2, fun k c Xs l₀ y a1 a2 a3 => (s3 k c Xs l₀ y a1 a2 a3).trans
        (mul_le_mul_of_nonneg_right hMD (Real.exp_pos _).le)⟩
  · cases t with
    | zero =>
      have hf : (fun σ : Fin k → ℝ => levelShare a L 0 (Finset.univ : Finset (TorusSite n)) z
            (perturb (fun l => bondFrom z (c l)) Xs σ (trivialField n))) =
          fun σ => levelShare a L 0 (Finset.univ : Finset (TorusSite n')) z'
            (perturb (fun l => bondFrom z' (c l)) Xs σ (trivialField n')) := by
        funext σ
        rw [levelShare_zero_perturb Xs σ a L z (w := 1) le_rfl hcz (by omega),
          levelShare_zero_perturb Xs σ a L z' (w := 1) le_rfl hcz (by omega)]
      have he : mixedDeriv (levelShare a L 0 (Finset.univ : Finset (TorusSite n)) z) (trivialField n)
            (fun l => bondFrom z (c l)) Xs =
          mixedDeriv (levelShare a L 0 (Finset.univ : Finset (TorusSite n')) z') (trivialField n')
            (fun l => bondFrom z' (c l)) Xs := by
        unfold mixedDeriv
        rw [hf]
      rw [he, sub_self, abs_zero]
      positivity
    | succ t =>
      have h := abs_sub_mixedDeriv_levelShare_succ_le (z := z) (z' := z') hL hc0 t hn hn' isRegularRegion_univ
        isRegularRegion_univ hm hm' hr (fun _ _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
        k c Xs hk hk1 hX hcz 0 (fun i => by rw [Pi.zero_apply, abs_zero]; omega)
      rw [add_siteOfInt_zero, add_siteOfInt_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_right hSD (Real.exp_pos _).le)
end YangMills.Construction.TorusComparison
end
