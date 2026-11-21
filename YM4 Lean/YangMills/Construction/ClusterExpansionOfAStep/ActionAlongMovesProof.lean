import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.MovesDefs
import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LevelAction
open BlockAverages hiding unitStep gaugeTransform
open TorusFields TorusPaths TorusLumps TorusChain StepCosts TorusContours ColdChain
variable {n k : ℕ}
section Plaquettes
def plaquetteWord (p : TorusPlaquette n) : BondWord n :=
  [((p.1, p.2.1), true), ((p.1 + unitStep n p.2.1, p.2.2), true), ((p.1 + unitStep n p.2.2, p.2.1), false),
    ((p.1, p.2.2), false)]
theorem holonomy_eq_wordHolonomy_plaquetteWord (W : TorusField n) (p : TorusPlaquette n) :
    holonomy W p.1 p.2.1 p.2.2 = wordHolonomy W (plaquetteWord p) := by
  simp [holonomy, wordHolonomy, plaquetteWord, orientedValue, mul_assoc]
def realPartCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
theorem norm_realPartCLM_le : ‖realPartCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  show |q.re| ≤ 1 * ‖q‖
  rw [one_mul]
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg q)
  have h : ‖q‖ ^ 2 = Quaternion.normSq q := by rw [Quaternion.normSq_eq_norm_mul_self]; ring
  rw [h, Quaternion.normSq_def']
  nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
def perturbedPlaquetteEnergy (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n)
    (p : TorusPlaquette n) (σ : Fin k → ℝ) : ℝ :=
  plaquetteEnergy (perturb c Xs σ W) p.1 p.2.1 p.2.2
theorem perturbedPlaquetteEnergy_eq (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n)
    (p : TorusPlaquette n) :
    perturbedPlaquetteEnergy c Xs W p =
      (fun _ => (1 : ℝ)) + -(realPartCLM ∘ perturbedHolonomy c Xs W (plaquetteWord p)) := by
  funext σ
  show 1 - ((holonomy (perturb c Xs σ W) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]).re =
    1 + -((wordHolonomy (perturb c Xs σ W) (plaquetteWord p) : UnitQuaternion) : ℍ[ℝ]).re
  rw [holonomy_eq_wordHolonomy_plaquetteWord, sub_eq_add_neg]
theorem contDiff_perturbedPlaquetteEnergy (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (W : TorusField n) (p : TorusPlaquette n) :
    ContDiff ℝ ⊤ (perturbedPlaquetteEnergy c Xs W p) := by
  rw [perturbedPlaquetteEnergy_eq]
  exact contDiff_const.add (realPartCLM.contDiff.comp (contDiff_perturbedHolonomy c Xs W _)).neg
def plaquetteEnergyMixedDeriv (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n)
    (p : TorusPlaquette n) : ℝ :=
  iteratedFDeriv ℝ k (perturbedPlaquetteEnergy c Xs W p) 0 fun l => Pi.single l 1
theorem abs_plaquetteEnergyMixedDeriv_le (hk1 : 1 ≤ k) (hk : k ≤ 3) (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) (hX : AreUnitVectors Xs) (W : TorusField n) (p : TorusPlaquette n) :
    |plaquetteEnergyMixedDeriv c Xs W p| ≤ (8 * letterDerivBound) ^ 4 := by
  have hg : ContDiff ℝ ⊤ (realPartCLM ∘ perturbedHolonomy c Xs W (plaquetteWord p)) :=
    realPartCLM.contDiff.comp (contDiff_perturbedHolonomy c Xs W _)
  have h1 : iteratedFDeriv ℝ k (perturbedPlaquetteEnergy c Xs W p) 0 =
      -(realPartCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (perturbedHolonomy c Xs W (plaquetteWord p)) 0)) := by
    have hg' : ContDiffAt ℝ k (-(realPartCLM ∘ perturbedHolonomy c Xs W (plaquetteWord p))) 0 :=
      (hg.neg.contDiffAt).of_le le_top
    have hc' : ContDiffAt ℝ k (fun _ : Fin k → ℝ => (1 : ℝ)) 0 := contDiff_const.contDiffAt
    rw [perturbedPlaquetteEnergy_eq, iteratedFDeriv_add_apply hc' hg']
    have h0 : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (1 : ℝ)) = 0 :=
      iteratedFDeriv_const_of_ne (by omega) 1
    rw [h0, Pi.zero_apply, zero_add, iteratedFDeriv_neg_apply,
      realPartCLM.iteratedFDeriv_comp_left (n := ⊤) (contDiff_perturbedHolonomy c Xs W _).contDiffAt
        (by exact_mod_cast le_top)]
  have h2 : ‖iteratedFDeriv ℝ k (perturbedPlaquetteEnergy c Xs W p) 0‖ ≤ (8 * letterDerivBound) ^ 4 := by
    rw [h1, norm_neg]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h3 := norm_iteratedFDeriv_perturbedHolonomy_le c Xs hX hk W (plaquetteWord p) hk
    have h4 : (plaquetteWord p).length = 4 := rfl
    rw [h4] at h3
    calc _ ≤ 1 * (8 * letterDerivBound) ^ 4 := mul_le_mul norm_realPartCLM_le h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact (Real.norm_eq_abs _ ▸ norm_iteratedFDeriv_coordinates_le (perturbedPlaquetteEnergy c Xs W p)).trans h2
theorem plaquetteEnergyMixedDeriv_eq_zero (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (W : TorusField n) (p : TorusPlaquette n) (l₀ : Fin k) (hl : ∀ e ∈ plaquetteWord p, c l₀ ≠ e.1) :
    plaquetteEnergyMixedDeriv c Xs W p = 0 := by
  refine congrArg (fun z => z) (iteratedFDeriv_coordinates_eq_zero_of_update
    (contDiff_perturbedPlaquetteEnergy c Xs W p) l₀ fun σ => ?_) |>.trans rfl
  unfold perturbedPlaquetteEnergy plaquetteEnergy
  rw [holonomy_eq_wordHolonomy_plaquetteWord, holonomy_eq_wordHolonomy_plaquetteWord,
    wordHolonomy_perturb_update c Xs σ W _ l₀ 0 hl]
theorem fst_fst_mem_plaquetteVertices (p : TorusPlaquette n) {e : TorusBond n × Bool} (he : e ∈ plaquetteWord p) :
    e.1.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
  simp only [plaquetteWord, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp [plaquetteVertices]
theorem card_plaquettes_with_vertex_le [NeZero n] (y : TorusSite n) :
    (Finset.univ.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2).card ≤ 64 := by
  classical
  set I : Finset (Fin 4 × Fin 4 × Fin 4) := Finset.univ with hI
  set f : Fin 4 × Fin 4 × Fin 4 → TorusPlaquette n := fun q =>
    ((![y, y - unitStep n q.1, y - unitStep n q.2.1, y - unitStep n q.1 - unitStep n q.2.1] q.2.2), q.1, q.2.1)
    with hf
  have hsub : (Finset.univ.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2) ⊆
      I.image f := by
    rintro ⟨x, μ, ν⟩ hp
    have hy : y ∈ plaquetteVertices x μ ν := (Finset.mem_filter.mp hp).2
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨(μ, ν, 0), Finset.mem_univ _, by simp [hf]⟩
    · exact Finset.mem_image.mpr ⟨(μ, ν, 1), Finset.mem_univ _, by simp [hf]⟩
    · exact Finset.mem_image.mpr ⟨(μ, ν, 2), Finset.mem_univ _, by simp [hf]⟩
    · exact Finset.mem_image.mpr ⟨(μ, ν, 3), Finset.mem_univ _, by simp [hf, add_assoc, sub_sub]⟩
  calc _ ≤ (I.image f).card := Finset.card_le_card hsub
    _ ≤ I.card := Finset.card_image_le
    _ = 64 := by simp [hI]
theorem mixedDeriv_weighted_sum [NeZero n] (P : Finset (TorusPlaquette n)) (w : TorusPlaquette n → ℝ)
    (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (W : TorusField n) :
    mixedDeriv (fun W' => ∑ p ∈ P, w p * plaquetteEnergy W' p.1 p.2.1 p.2.2) W c Xs =
      ∑ p ∈ P, w p * plaquetteEnergyMixedDeriv c Xs W p := by
  unfold mixedDeriv
  have hf : ∀ p ∈ P, ContDiffAt ℝ k (fun σ => w p • perturbedPlaquetteEnergy c Xs W p σ) 0 := fun p _ =>
    ((contDiff_perturbedPlaquetteEnergy c Xs W p).const_smul (w p)).contDiffAt.of_le le_top
  have h1 : (fun σ : Fin k → ℝ => ∑ p ∈ P, w p * plaquetteEnergy (perturb c Xs σ W) p.1 p.2.1 p.2.2) =
      fun σ => ∑ p ∈ P, (fun σ' => w p • perturbedPlaquetteEnergy c Xs W p σ') σ := rfl
  rw [h1, iteratedFDeriv_fun_sum_apply hf, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h2 : iteratedFDeriv ℝ k (fun σ' => w p • perturbedPlaquetteEnergy c Xs W p σ') 0 =
      w p • iteratedFDeriv ℝ k (perturbedPlaquetteEnergy c Xs W p) 0 :=
    iteratedFDeriv_const_smul_apply' ((contDiff_perturbedPlaquetteEnergy c Xs W p).contDiffAt.of_le le_top)
  rw [h2]
  rfl
theorem abs_weighted_sum_mixedDeriv_le [NeZero n] (hk1 : 1 ≤ k) (hk : k ≤ 3) (P : Finset (TorusPlaquette n))
    (w : TorusPlaquette n → ℝ) (y : TorusSite n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors Xs) (W : TorusField n) (hw : ∀ p, |w p| ≤ 1)
    (hy : ∀ p, y ∉ plaquetteVertices p.1 p.2.1 p.2.2 → w p * plaquetteEnergyMixedDeriv c Xs W p = 0) :
    |∑ p ∈ P, w p * plaquetteEnergyMixedDeriv c Xs W p| ≤ 64 * (8 * letterDerivBound) ^ 4 := by
  classical
  set B := (8 * letterDerivBound) ^ 4 with hB
  have hB0 : 0 ≤ B := by
    have := one_le_letterDerivBound
    positivity
  have h1 : ∑ p ∈ P, w p * plaquetteEnergyMixedDeriv c Xs W p =
      ∑ p ∈ P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2,
        w p * plaquetteEnergyMixedDeriv c Xs W p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rfl
    · exact hy p h
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h2 : ∀ p ∈ P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2,
      |w p * plaquetteEnergyMixedDeriv c Xs W p| ≤ B := by
    intro p _
    rw [abs_mul]
    calc |w p| * |plaquetteEnergyMixedDeriv c Xs W p| ≤ 1 * B :=
          mul_le_mul (hw p) (abs_plaquetteEnergyMixedDeriv_le hk1 hk c Xs hX W p) (abs_nonneg _) zero_le_one
      _ = B := one_mul _
  refine (Finset.sum_le_card_nsmul _ _ B h2).trans ?_
  rw [nsmul_eq_mul]
  have h3 : ((P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2).card : ℝ) ≤ 64 := by
    have : (P.filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2).card ≤ 64 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
        (card_plaquettes_with_vertex_le y)
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right h3 hB0
end Plaquettes
section Levels
variable [NeZero n]
def vertexWeight (y : TorusSite n) (p : TorusPlaquette n) : ℝ :=
  (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4
theorem abs_vertexWeight_le (y : TorusSite n) (p : TorusPlaquette n) : |vertexWeight y p| ≤ 1 := by
  unfold vertexWeight
  have h : (plaquetteVertices p.1 p.2.1 p.2.2).count y ≤ 4 := List.count_le_length
  have h' : (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h
  rw [abs_of_nonneg (by positivity)]
  linarith
theorem vertexWeight_eq_zero {y : TorusSite n} {p : TorusPlaquette n}
    (h : y ∉ plaquetteVertices p.1 p.2.1 p.2.2) : vertexWeight y p = 0 := by
  simp [vertexWeight, List.count_eq_zero_of_not_mem h]
theorem levelShare_zero (a : ℝ) (L : ℕ) (X : Finset (TorusSite n)) (y : TorusSite n) :
    levelShare a L 0 X y =
      fun W' => ∑ p ∈ plaquettesIn X, vertexWeight y p * plaquetteEnergy W' p.1 p.2.1 p.2.2 := rfl
theorem sum_count_eq_length (l : List (TorusSite n)) : ∑ y : TorusSite n, ((l.count y : ℕ) : ℝ) = l.length := by apply _root_.YangMills.Construction.FreeBonds.sum_count_cast <;> assumption
theorem actionAtLevel_zero_eq_sum (a : ℝ) (L : ℕ) (X : Finset (TorusSite n)) :
    actionAtLevel a L 0 X = fun W'' => ∑ y, levelShare a L 0 X y W'' := by
  funext W''
  show wilsonAction X W'' = _
  simp only [levelShare_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_mul]
  have : ∑ y : TorusSite n, vertexWeight y p = 1 := by
    unfold vertexWeight
    rw [← Finset.sum_div, sum_count_eq_length]
    simp [plaquetteVertices]
  rw [this, one_mul]
theorem one_le_exp_one_mul_exp {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) {d : ℕ} (hd : d ≤ 4) :
    (1 : ℝ) ≤ Real.exp 1 * Real.exp (-δ * d) := by
  rw [← Real.exp_add]
  apply Real.one_le_exp
  have : (d : ℝ) ≤ 4 := by exact_mod_cast hd
  nlinarith
def baseLevelBound : ℝ := 64 * (8 * letterDerivBound) ^ 4 * Real.exp 1
theorem baseLevelBound_nonneg : 0 ≤ baseLevelBound := by
  have := one_le_letterDerivBound
  unfold baseLevelBound
  positivity
theorem abs_mixedDeriv_levelShare_zero_le {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (a : ℝ) (L : ℕ)
    (X : Finset (TorusSite n)) (W : TorusField n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (l₀ : Fin k) (hk1 : 1 ≤ k) (hk : k ≤ 3) (hX : AreUnitVectors Xs) (y : TorusSite n) :
    |mixedDeriv (levelShare a L 0 X y) W c Xs| ≤ baseLevelBound * Real.exp (-δ * supDist y (c l₀).1) := by
  rw [levelShare_zero, mixedDeriv_weighted_sum]
  by_cases hd : supDist y (c l₀).1 ≤ 4
  · have h1 := abs_weighted_sum_mixedDeriv_le hk1 hk (plaquettesIn X) (vertexWeight y) y c Xs hX W
      (abs_vertexWeight_le y) fun p hp => by rw [vertexWeight_eq_zero hp, zero_mul]
    have h2 := one_le_exp_one_mul_exp hδ hδ8 hd
    have h3 : 0 ≤ 64 * (8 * letterDerivBound) ^ 4 := by
      have := one_le_letterDerivBound
      positivity
    calc _ ≤ 64 * (8 * letterDerivBound) ^ 4 := h1
      _ ≤ 64 * (8 * letterDerivBound) ^ 4 * (Real.exp 1 * Real.exp (-δ * supDist y (c l₀).1)) :=
        le_mul_of_one_le_right h3 h2
      _ = _ := by unfold baseLevelBound; ring
  · have h0 : ∑ p ∈ plaquettesIn X, vertexWeight y p * plaquetteEnergyMixedDeriv c Xs W p = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hy : y ∈ plaquetteVertices p.1 p.2.1 p.2.2
      · rw [plaquetteEnergyMixedDeriv_eq_zero c Xs W p l₀ ?_, mul_zero]
        intro e he hce
        have hm := fst_fst_mem_plaquetteVertices p he
        rw [← hce] at hm
        exact hd (supDist_le_four_of_mem_plaquetteVertices p hy hm)
      · rw [vertexWeight_eq_zero hy, zero_mul]
    rw [h0, abs_zero]
    have := baseLevelBound_nonneg
    positivity
theorem abs_mixedDeriv_actionAtLevel_zero_le {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (a : ℝ) (L : ℕ)
    (X : Finset (TorusSite n)) (W : TorusField n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (hk1 : 1 ≤ k) (hk : k ≤ 3) (hX : AreUnitVectors Xs) :
    |mixedDeriv (actionAtLevel a L 0 X) W c Xs| ≤ baseLevelBound * Real.exp (-δ * bondListSpread c) := by
  have hw : actionAtLevel a L 0 X =
      fun W' => ∑ p ∈ plaquettesIn X, (fun _ => (1 : ℝ)) p * plaquetteEnergy W' p.1 p.2.1 p.2.2 := by
    funext W'
    simp only [one_mul]
    rfl
  rw [hw, mixedDeriv_weighted_sum]
  set l₀ : Fin k := ⟨0, hk1⟩
  by_cases hd : bondListSpread c ≤ 4
  · have h1 := abs_weighted_sum_mixedDeriv_le hk1 hk (plaquettesIn X) (fun _ => (1 : ℝ)) (c l₀).1 c Xs hX W
      (by simp) fun p hp => by
        rw [plaquetteEnergyMixedDeriv_eq_zero c Xs W p l₀ ?_, mul_zero]
        intro e he hce
        have hm := fst_fst_mem_plaquetteVertices p he
        rw [← hce] at hm
        exact hp hm
    have h2 := one_le_exp_one_mul_exp hδ hδ8 hd
    have h3 : 0 ≤ 64 * (8 * letterDerivBound) ^ 4 := by
      have := one_le_letterDerivBound
      positivity
    calc _ ≤ 64 * (8 * letterDerivBound) ^ 4 := h1
      _ ≤ 64 * (8 * letterDerivBound) ^ 4 * (Real.exp 1 * Real.exp (-δ * bondListSpread c)) :=
        le_mul_of_one_le_right h3 h2
      _ = _ := by unfold baseLevelBound; ring
  · have hlt : 4 < bondListSpread c := not_le.mp hd
    unfold bondListSpread at hlt
    obtain ⟨l, -, hl⟩ := Finset.lt_sup_iff.mp hlt
    obtain ⟨l', -, hl'⟩ := Finset.lt_sup_iff.mp hl
    have h0 : ∑ p ∈ plaquettesIn X, (fun _ => (1 : ℝ)) p * plaquetteEnergyMixedDeriv c Xs W p = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hy : (c l).1 ∈ plaquetteVertices p.1 p.2.1 p.2.2
      · rw [plaquetteEnergyMixedDeriv_eq_zero c Xs W p l' ?_, mul_zero]
        intro e he hce
        have hm := fst_fst_mem_plaquetteVertices p he
        rw [← hce] at hm
        exact absurd (supDist_le_four_of_mem_plaquetteVertices p hy hm) (by omega)
      · rw [plaquetteEnergyMixedDeriv_eq_zero c Xs W p l ?_, mul_zero]
        intro e he hce
        have hm := fst_fst_mem_plaquetteVertices p he
        rw [← hce] at hm
        exact hy hm
    rw [h0, abs_zero]
    have := baseLevelBound_nonneg
    positivity
theorem contDiff_weighted_sum (P : Finset (TorusPlaquette n)) (w : TorusPlaquette n → ℝ) (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) (W : TorusField n) :
    ContDiff ℝ ⊤ fun σ : Fin k → ℝ => ∑ p ∈ P, w p * plaquetteEnergy (perturb c Xs σ W) p.1 p.2.1 p.2.2 :=
  ContDiff.sum fun p _ => contDiff_const.mul (contDiff_perturbedPlaquetteEnergy c Xs W p)
theorem perturb_congr (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    {W W' : TorusField n} {u : TorusSite n} {i : Fin 4}
    (h : W u i = W' u i) : perturb c Xs σ W u i = perturb c Xs σ W' u i := by
  unfold perturb
  rw [h]
theorem mixedDeriv_levelShare_zero_congr (a : ℝ) (L : ℕ) {X X' : Finset (TorusSite n)} {W W' : TorusField n}
    (y : TorusSite n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions)
    (hXX : ∀ u, supDist u y ≤ 4 → (u ∈ X ↔ u ∈ X'))
    (hWW : ∀ u i, supDist u y ≤ 4 → supDist (u + unitStep n i) y ≤ 4 → W u i = W' u i) :
    mixedDeriv (levelShare a L 0 X y) W c Xs = mixedDeriv (levelShare a L 0 X' y) W' c Xs := by
  classical
  unfold mixedDeriv
  have hf : (fun σ : Fin k → ℝ => levelShare a L 0 X y (perturb c Xs σ W)) =
      fun σ => levelShare a L 0 X' y (perturb c Xs σ W') := by
    funext σ
    simp only [levelShare_zero]
    have hred : ∀ (A : Finset (TorusSite n)) (G : TorusField n),
        ∑ p ∈ plaquettesIn A, vertexWeight y p * plaquetteEnergy (perturb c Xs σ G) p.1 p.2.1 p.2.2 =
          ∑ p ∈ (plaquettesIn A).filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2,
            vertexWeight y p * plaquetteEnergy (perturb c Xs σ G) p.1 p.2.1 p.2.2 := by
      intro A G
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs with h
      · rfl
      · rw [vertexWeight_eq_zero h, zero_mul]
    rw [hred X W, hred X' W']
    have hset : ((plaquettesIn X).filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2) =
        (plaquettesIn X').filter fun p : TorusPlaquette n => y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
      ext p
      simp only [Finset.mem_filter, mem_plaquettesIn_iff_forall_vertex]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, fun z hz =>
          (hXX z (supDist_le_four_of_mem_plaquetteVertices p hz h3)).mp (h2 z hz)⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, fun z hz =>
          (hXX z (supDist_le_four_of_mem_plaquetteVertices p hz h3)).mpr (h2 z hz)⟩, h3⟩
    rw [hset]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hy : y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := (Finset.mem_filter.mp hp).2
    have m1 : p.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by simp [plaquetteVertices]
    have m2 : p.1 + unitStep n p.2.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by simp [plaquetteVertices]
    have m3 : p.1 + unitStep n p.2.2 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by simp [plaquetteVertices]
    have m4 : p.1 + unitStep n p.2.1 + unitStep n p.2.2 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
      simp [plaquetteVertices]
    have m4' : p.1 + unitStep n p.2.2 + unitStep n p.2.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
      rw [add_right_comm]
      exact m4
    have e1 := perturb_congr c Xs σ (hWW p.1 p.2.1 (supDist_le_four_of_mem_plaquetteVertices p m1 hy)
      (supDist_le_four_of_mem_plaquetteVertices p m2 hy))
    have e2 := perturb_congr c Xs σ (hWW (p.1 + unitStep n p.2.1) p.2.2
      (supDist_le_four_of_mem_plaquetteVertices p m2 hy) (supDist_le_four_of_mem_plaquetteVertices p m4 hy))
    have e3 := perturb_congr c Xs σ (hWW (p.1 + unitStep n p.2.2) p.2.1
      (supDist_le_four_of_mem_plaquetteVertices p m3 hy) (supDist_le_four_of_mem_plaquetteVertices p m4' hy))
    have e4 := perturb_congr c Xs σ (hWW p.1 p.2.2 (supDist_le_four_of_mem_plaquetteVertices p m1 hy)
      (supDist_le_four_of_mem_plaquetteVertices p m3 hy))
    unfold plaquetteEnergy holonomy
    rw [e1, e2, e3, e4]
  rw [hf]
theorem mixedDeriv_sum_sites {sh : TorusSite n → TorusField n → ℝ} {W : TorusField n}
    (hs : ∀ y, ContDiffThreeAt (sh y) W) (hk : k ≤ 3) (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W'' => ∑ y, sh y W'') W c Xs = ∑ y, mixedDeriv (sh y) W c Xs := by
  unfold mixedDeriv
  have hc : ∀ y ∈ (Finset.univ : Finset (TorusSite n)),
      ContDiffAt ℝ k (fun σ : Fin k → ℝ => sh y (perturb c Xs σ W)) 0 := fun y _ =>
    (hs y k c Xs).of_le (by exact_mod_cast hk)
  rw [iteratedFDeriv_fun_sum_apply hc, ContinuousMultilinearMap.sum_apply]
def tailSumConstant (δ : ℝ) : ℝ := (2 / (1 - Real.exp (-(δ / 2 / 2) / 4))) ^ 4
theorem tailSumConstant_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ tailSumConstant δ := by
  unfold tailSumConstant
  have h : Real.exp (-(δ / 2 / 2) / 4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have : 0 < 1 - Real.exp (-(δ / 2 / 2) / 4) := by linarith
  positivity
theorem abs_mixedDeriv_sub_le {sh sh' : TorusSite n → TorusField n → ℝ} {A A' : TorusField n → ℝ}
    {W W' : TorusField n} {z : TorusSite n} {m : ℕ}
    {δ D Ee : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D) (hE : 0 ≤ Ee) (hk1 : 1 ≤ k) (hk : k ≤ 3) (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) (hA : A = fun W'' => ∑ y, sh y W'') (hA' : A' = fun W'' => ∑ y, sh' y W'')
    (hs : ∀ y, ContDiffThreeAt (sh y) W) (hs' : ∀ y, ContDiffThreeAt (sh' y) W')
    (hd : ∀ y l, |mixedDeriv (sh y) W c Xs| ≤ D * Real.exp (-δ * supDist y (c l).1))
    (hd' : ∀ y l, |mixedDeriv (sh' y) W' c Xs| ≤ D * Real.exp (-δ * supDist y (c l).1))
    (hc : ∀ l, 4 * supDist (c l).1 z + 4 ≤ m)
    (hn : ∀ y, 2 * supDist y z ≤ m →
      |mixedDeriv (sh y) W c Xs - mixedDeriv (sh' y) W' c Xs| ≤ Ee * Real.exp (-δ * m)) :
    |mixedDeriv A W c Xs - mixedDeriv A' W' c Xs| ≤
      (Ee + 2 * D * tailSumConstant δ) * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by
  rw [hA, hA', mixedDeriv_sum_sites hs hk, mixedDeriv_sum_sites hs' hk]
  set l₀ : Fin k := ⟨0, hk1⟩
  have hfar : ∀ y, m < 2 * supDist y z →
      |mixedDeriv (sh y) W c Xs| ≤ D * Real.exp (-(δ / 2) * supDist y z) ∧
      |mixedDeriv (sh' y) W' c Xs| ≤ D * Real.exp (-(δ / 2) * supDist y z) := by
    intro y hy
    have h1 := supDist_triangle y (c l₀).1 z
    have h2 := hc l₀
    have h3 : (supDist y z : ℝ) ≤ 2 * supDist y (c l₀).1 := by
      have : supDist y z ≤ 2 * supDist y (c l₀).1 := by omega
      exact_mod_cast this
    have h4 : Real.exp (-δ * supDist y (c l₀).1) ≤ Real.exp (-(δ / 2) * supDist y z) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact ⟨(hd y l₀).trans (mul_le_mul_of_nonneg_left h4 hD),
      (hd' y l₀).trans (mul_le_mul_of_nonneg_left h4 hD)⟩
  have hmain := abs_sum_sub_sum_le_of_near_of_far (half_pos hδ) hD (mul_nonneg hE (Real.exp_pos _).le) hn hfar
  refine hmain.trans ?_
  have hK := tailSumConstant_nonneg hδ
  have he1 : Real.exp (-δ * m) ≤ Real.exp (-δ * m / 8) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ δ * m := by positivity
    nlinarith
  have he2 : Real.exp (-(δ / 2) * m / 4) = Real.exp (-δ * m / 8) := by
    congr 1
    ring
  have hp1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := one_le_pow₀ (by
    have : (0 : ℝ) ≤ m := by positivity
    linarith)
  rw [he2]
  have hF : (2 / (1 - Real.exp (-(δ / 2 / 2) / 4))) ^ 4 = tailSumConstant δ := rfl
  rw [hF]
  set P := ((m : ℝ) + 1) ^ 4
  set e8 := Real.exp (-δ * m / 8)
  have t1 : P * (Ee * Real.exp (-δ * m)) ≤ P * (Ee * e8) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he1 hE) (by positivity)
  have t2 : 2 * D * e8 * tailSumConstant δ ≤ 2 * D * tailSumConstant δ * P * e8 := by
    have : 0 ≤ 2 * D * tailSumConstant δ * e8 := by positivity
    nlinarith
  nlinarith
end Levels
section Positive
variable [NeZero n]
theorem torusFrame_period_top (L t n : ℕ) (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
theorem torusFrame_period_neZero (L t n : ℕ) [NeZero L] [NeZero n] (j : ℕ) (i : Fin 4) :
    NeZero ((torusFrame L t n).period j i) :=
  ⟨by
    show n * L ^ _ ≠ 0
    exact mul_ne_zero (NeZero.ne n) (pow_ne_zero _ (NeZero.ne L))⟩
theorem one_lt_torusFrame_period_zero (L t n : ℕ) (hL : 1 ≤ L) (hn : 2 ≤ n) (i : Fin 4) :
    1 < (torusFrame L t n).period 0 i := by
  show 1 < n * L ^ _
  have h2 : 1 ≤ L ^ ((torusFrame L t n).top - 0) := Nat.one_le_pow _ _ hL
  nlinarith
theorem readAtLevel_gaugeTransform {F : BlockFrame} [∀ i, NeZero (F.period F.top i)] (hp : ∀ i, F.period F.top i = n)
    (g : TorusSite n → UnitQuaternion) (W : TorusField n) :
    readAtLevel F F.top (gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun y => g (toTorusSite n y)) (readAtLevel F F.top W) := by
  funext y i
  show g (toTorusSite n y) * W (toTorusSite n y) i * (g (toTorusSite n y + unitStep n i))⁻¹ =
    g (toTorusSite n y) * W (toTorusSite n y) i * (g (toTorusSite n (y + BlockAverages.unitStep F.top i)))⁻¹
  rw [toTorusSite_add hp, toTorusSite_unitStep hp]
def LevelEstimates (a : ℝ) (L t : ℕ) (δ D : ℝ) (X : Finset (TorusSite n)) (W : TorusField n) : Prop :=
  (actionAtLevel a L t X = fun W'' => ∑ y, levelShare a L t X y W'') ∧
  (∀ y, ContDiffThreeAt (levelShare a L t X y) W) ∧
  ContDiffThreeAt (actionAtLevel a L t X) W ∧
  (∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (l₀ : Fin k) (y : TorusSite n),
    1 ≤ k → k ≤ 3 → AreUnitVectors Xs →
    |mixedDeriv (levelShare a L t X y) W c Xs| ≤ D * Real.exp (-δ * supDist y (c l₀).1)) ∧
  (∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions), 2 ≤ k → k ≤ 3 → AreUnitVectors Xs →
    |mixedDeriv (actionAtLevel a L t X) W c Xs| ≤ D * Real.exp (-δ * bondListSpread c)) ∧
  ∀ g : TorusSite n → UnitQuaternion, actionAtLevel a L t X (gaugeTransform g W) = actionAtLevel a L t X W
theorem LevelEstimates.mono {a : ℝ} {L t : ℕ} {δ D D' : ℝ} {X : Finset (TorusSite n)} {W : TorusField n}
    (h : LevelEstimates a L t δ D X W) (hD : D ≤ D') : LevelEstimates a L t δ D' X W := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, fun k c Xs l₀ y a1 a2 a3 => (h4 k c Xs l₀ y a1 a2 a3).trans ?_,
    fun k c Xs a1 a2 a3 => (h5 k c Xs a1 a2 a3).trans ?_, h6⟩
  · exact mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
theorem levelEstimates_zero {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (a : ℝ) (L : ℕ) (X : Finset (TorusSite n))
    (W : TorusField n) : LevelEstimates a L 0 δ baseLevelBound X W := by
  have hw : actionAtLevel a L 0 X =
      fun W' => ∑ p ∈ plaquettesIn X, (fun _ => (1 : ℝ)) p * plaquetteEnergy W' p.1 p.2.1 p.2.2 := by
    funext W'
    simp only [one_mul]
    rfl
  refine ⟨actionAtLevel_zero_eq_sum a L X, fun y k c Xs => ?_, fun k c Xs => ?_,
    fun k c Xs l₀ y a1 a2 a3 => abs_mixedDeriv_levelShare_zero_le hδ hδ8 a L X W c Xs l₀ a1 a2 a3 y,
    fun k c Xs a1 a2 a3 => abs_mixedDeriv_actionAtLevel_zero_le hδ hδ8 a L X W c Xs (by omega) a2 a3,
    fun g => ?_⟩
  · rw [levelShare_zero]
    exact ((contDiff_weighted_sum (plaquettesIn X) (vertexWeight y) c Xs W).of_le le_top).contDiffAt
  · rw [hw]
    exact ((contDiff_weighted_sum (plaquettesIn X) (fun _ => (1 : ℝ)) c Xs W).of_le le_top).contDiffAt
  · exact wilsonAction_gaugeTransform X g W
theorem levelEstimates_succ (hLV : minimalChainExistenceStatement) {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ}
    (ha : 0 < a) (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n)
    {X : Finset (TorusSite n)} {W : TorusField n} (hreg : IsRegularRegion X 1024) (hcold : IsColdOn σA X W) :
    LevelEstimates a L (t + 1) δ (N 1 + N 2 + N 3) X W := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
  haveI : NeZero L := ⟨hL.pos.ne'⟩
  haveI hinst : ∀ j i, NeZero ((torusFrame L t n).period j i) := fun j i => torusFrame_period_neZero L t n j i
  have hp := torusFrame_period_top L t n
  have h1 : ∀ i, 1 < (torusFrame L t n).period 0 i := one_lt_torusFrame_period_zero L t n hL.pos (by omega)
  have hamb : IsAdmissibleAmbient (torusFrame L t n) := Or.inr fun _ => hn
  have hreg' : IsOrthantRegular (cellsOfSites (torusFrame L t n) X) 1024 :=
    isOrthantRegular_of_isRegularRegion hp hreg
  have hcold' := isCold_of_isColdOn (F := torusFrame L t n) hp hcold
  obtain ⟨-, -, H3, -⟩ := hch (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) X) rfl hamb le_rfl hreg' σA _
    hσ le_rfl hcold'
  obtain ⟨hAn, hSn, -, hG, -, hTot, hShare, -, -⟩ := H3
  have hNk : ∀ k, 1 ≤ k → k ≤ 3 → N k ≤ N 1 + N 2 + N 3 := by
    intro k a1 a2
    have n1 := hN 1
    have n2 := hN 2
    have n3 := hN 3
    interval_cases k <;> linarith
  have hsum : actionAtLevel a L (t + 1) X = fun W'' => ∑ y, levelShare a L (t + 1) X y W'' := by
    funext W''
    show minimalAction a (cellsOfSites (torusFrame L t n) X) (torusFrame L t n).top
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top W'') =
      ∑ y, minimalCellShare a (cellsOfSites (torusFrame L t n) X)
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top W'')
    rw [minimalAction_eq_sum_minimalCellShare hLV h1 ha.le]
    exact (Equiv.sum_comp (torusSiteEquivCell hp) fun Y => minimalCellShare a (cellsOfSites (torusFrame L t n) X) Y
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W'')).symm
  refine ⟨hsum, fun y => contDiffThreeAt_of_isBondAnalyticAt hp (hSn _),
    contDiffThreeAt_of_isBondAnalyticAt hp hAn, ?_, ?_, fun g => ?_⟩
  · intro k c Xs l₀ y a1 a2 a3
    have e : mixedDeriv (levelShare a L (t + 1) X y) W c Xs =
        mixedBondDerivative (minimalCellShare a (cellsOfSites (torusFrame L t n) X)
            (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y))
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
          (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) Xs :=
      mixedDeriv_readAtLevel hp (minimalCellShare a (cellsOfSites (torusFrame L t n) X)
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)) W c Xs
    rw [e]
    refine (hShare _ k _ Xs a1 a3).trans ?_
    have hd : (supDist y (c l₀).1 : ℝ) ≤
        (bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) : ℝ) := by
      have h2 : cellSupDist (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l₀).1) ≤
          bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
            (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) :=
        Finset.le_sup (f := fun l : Fin k => cellSupDist (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1)) (Finset.mem_univ l₀)
      rw [cellSupDist_torusSiteInFrame hp] at h2
      exact_mod_cast h2
    have he : Real.exp (-δ * (bondListDistance (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) : ℝ)) ≤
        Real.exp (-δ * supDist y (c l₀).1) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact mul_le_mul (hNk k a1 a2) he (Real.exp_pos _).le (by have := hN 1; have := hN 2; have := hN 3; linarith)
  · intro k c Xs a1 a2 a3
    have e : mixedDeriv (actionAtLevel a L (t + 1) X) W c Xs =
        mixedBondDerivative (minimalAction a (cellsOfSites (torusFrame L t n) X) (torusFrame L t n).top)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
          (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) Xs :=
      mixedDeriv_readAtLevel hp (minimalAction a (cellsOfSites (torusFrame L t n) X) (torusFrame L t n).top) W c Xs
    rw [e]
    refine (hTot k _ Xs a1 a3).trans ?_
    have hs : bondListDiameter
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) =
        bondListSpread c := by
      unfold bondListDiameter bondListSpread
      simp only [cellSupDist_torusSiteInFrame hp]
    rw [hs]
    exact mul_le_mul_of_nonneg_right (hNk k (by omega) a2) (Real.exp_pos _).le
  · have hg : ∀ y, levelShare a L (t + 1) X y (gaugeTransform g W) = levelShare a L (t + 1) X y W := by
      intro y
      show minimalCellShare a (cellsOfSites (torusFrame L t n) X)
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top (gaugeTransform g W)) =
        minimalCellShare a (cellsOfSites (torusFrame L t n) X)
          (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      rw [readAtLevel_gaugeTransform hp]
      exact hG _ _
    rw [hsum]
    exact Finset.sum_congr rfl fun y _ => hg y
theorem abs_mixedDeriv_levelShare_succ_sub_le {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ} (hL : Odd L)
    (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) (hn : 64 ≤ n) {X X' : Finset (TorusSite n)}
    {W W' : TorusField n} (hreg : IsRegularRegion X 1024) (hcold : IsColdOn σA X W)
    (hreg' : IsRegularRegion X' 1024) (hcold' : IsColdOn σA X' W') {z : TorusSite n} {m : ℕ}
    (hm : 2 * m + 2 < n) (hXX : ∀ y, supDist y z ≤ 2 * m → (y ∈ X ↔ y ∈ X'))
    (hWW : ∀ y i, supDist y z ≤ 2 * m → supDist (y + unitStep n i) z ≤ 2 * m → W y i = W' y i)
    (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (hk1 : 1 ≤ k) (hk : k ≤ 2)
    (hX : AreUnitVectors Xs) (hcz : ∀ l, 4 * supDist (c l).1 z + 4 ≤ m) (y : TorusSite n)
    (hy : 2 * supDist y z ≤ m) :
    |mixedDeriv (levelShare a L (t + 1) X y) W c Xs - mixedDeriv (levelShare a L (t + 1) X' y) W' c Xs| ≤
      (1 + σA) * (N 1 + N 2 + N 3) * Real.exp (-δ * m) := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
  haveI : NeZero L := ⟨hL.pos.ne'⟩
  haveI hinst : ∀ j i, NeZero ((torusFrame L t n).period j i) := fun j i => torusFrame_period_neZero L t n j i
  have hp := torusFrame_period_top L t n
  have hamb : IsAdmissibleAmbient (torusFrame L t n) := Or.inr fun _ => hn
  have hR : IsOrthantRegular (cellsOfSites (torusFrame L t n) X) 1024 :=
    isOrthantRegular_of_isRegularRegion hp hreg
  have hR' : IsOrthantRegular (cellsOfSites (torusFrame L t n) X') 1024 :=
    isOrthantRegular_of_isRegularRegion hp hreg'
  have hC := isCold_of_isColdOn (F := torusFrame L t n) hp hcold
  have hC' := isCold_of_isColdOn (F := torusFrame L t n) hp hcold'
  obtain ⟨-, -, -, -, -, H⟩ :=
    hch (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) X) rfl hamb le_rfl hR σA _ hσ le_rfl hC
  set Y := torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y with hYdef
  have hshift : ∀ h : Fin 4 → ℤ, Y + siteOfCoords (torusFrame L t n).top h =
      torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (y + siteOfInt h) := by
    intro h
    rw [torusSiteInFrame_add hp, torusSiteInFrame_siteOfInt hp]
  have hzy : supDist y z ≤ m := by omega
  have hagree : AgreeOnBall (cellsOfSites (torusFrame L t n) X)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (cellsOfSites (torusFrame L t n) X') (readAtLevel (torusFrame L t n) (torusFrame L t n).top W') Y Y m := by
    refine ⟨fun _ => Or.inr hm, fun _ => Or.inr hm, fun h hh => ?_, fun b hb => ?_⟩
    · rw [hshift, mem_cellsOfSites_iff hp, mem_cellsOfSites_iff hp, toTorusSite_torusSiteInFrame hp]
      refine hXX _ ?_
      have h2 := supDist_add_siteOfInt_le y h m fun i => by
        have := hh i
        rw [Int.abs_eq_natAbs] at this
        omega
      have h3 := supDist_triangle (y + siteOfInt h) y z
      rw [supDist_comm (y + siteOfInt h) y] at h3
      omega
    · rw [hshift]
      show W (toTorusSite n (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (y + siteOfInt b.1))) b.2 =
        W' (toTorusSite n (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (y + siteOfInt b.1))) b.2
      rw [toTorusSite_torusSiteInFrame hp]
      have h2 := supDist_add_siteOfInt_le y b.1 m fun i => by
        have := hb.1 i
        rw [Int.abs_eq_natAbs] at this
        omega
      have h3 := supDist_triangle (y + siteOfInt b.1) y z
      rw [supDist_comm (y + siteOfInt b.1) y] at h3
      have h4 : y + siteOfInt b.1 + unitStep n b.2 = y + siteOfInt (b.1 + Pi.single b.2 1) := by
        rw [siteOfInt_add, siteOfInt_single, add_assoc]
      have h5 := supDist_add_siteOfInt_le y (b.1 + Pi.single b.2 1) m fun i => by
        have := hb.2 i
        rw [Int.abs_eq_natAbs] at this
        omega
      have h6 := supDist_triangle (y + siteOfInt (b.1 + Pi.single b.2 1)) y z
      rw [supDist_comm (y + siteOfInt (b.1 + Pi.single b.2 1)) y] at h6
      refine hWW _ _ (by omega) ?_
      rw [h4]
      omega
  have HL := (H (torusFrame L t n) (cellsOfSites (torusFrame L t n) X') _ Y Y m rfl rfl hamb hR' hC' hagree).1
  choose e he hb using fun l => exists_offset_of_supDist y (c l).1
  have hbonds : offsetBonds Y (fun l => (e l, (c l).2)) =
      fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2) := by
    funext l
    refine Prod.ext ?_ rfl
    show Y + siteOfCoords (torusFrame L t n).top (e l) =
      torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1
    rw [hshift, ← he l]
  have hbox : ∀ l, BondWithinRadius m (e l, (c l).2) := by
    intro l
    have h1 := hcz l
    have h2 := supDist_triangle y z (c l).1
    rw [supDist_comm z (c l).1] at h2
    have h3 : supDist y (c l).1 + 1 ≤ m := by omega
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := hb l i
      show |e l i| ≤ (m : ℤ)
      rw [Int.abs_eq_natAbs]
      omega
    · have h4 := hb l i
      show |((e l + Pi.single (c l).2 1 : Fin 4 → ℤ)) i| ≤ (m : ℤ)
      rw [Int.abs_eq_natAbs]
      by_cases hi : i = (c l).2
      · subst hi
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
        omega
  have hfin := HL k (fun l => (e l, (c l).2)) Xs hbox hX
  rw [hbonds] at hfin
  have e1 : mixedDeriv (levelShare a L (t + 1) X y) W c Xs =
      mixedBondDerivative (minimalCellShare a (cellsOfSites (torusFrame L t n) X) Y)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) Xs :=
    mixedDeriv_readAtLevel hp (minimalCellShare a (cellsOfSites (torusFrame L t n) X) Y) W c Xs
  have e2 : mixedDeriv (levelShare a L (t + 1) X' y) W' c Xs =
      mixedBondDerivative (minimalCellShare a (cellsOfSites (torusFrame L t n) X') Y)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top W')
        (fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)) Xs :=
    mixedDeriv_readAtLevel hp (minimalCellShare a (cellsOfSites (torusFrame L t n) X') Y) W' c Xs
  rw [e1, e2]
  refine hfin.trans ?_
  have hcf : derivativeScale σA k ≤ 1 + σA := by
    unfold derivativeScale
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0]
    split_ifs <;> linarith
  have hNk : N k ≤ N 1 + N 2 + N 3 := by
    have n1 := hN 1
    have n2 := hN 2
    have n3 := hN 3
    interval_cases k <;> linarith
  have hNk0 : 0 ≤ N k := (hN k).le
  have hcf0 : 0 ≤ derivativeScale σA k := by
    unfold derivativeScale
    split_ifs <;> first | positivity | exact hσ.le | norm_num
  have h1 : derivativeScale σA k * N k ≤ (1 + σA) * (N 1 + N 2 + N 3) :=
    mul_le_mul hcf hNk hNk0 (by linarith)
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
end Positive
def siteSumConstant (δ : ℝ) : ℝ := (2 / (1 - Real.exp (-δ / 4))) ^ 4
theorem siteSumConstant_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ siteSumConstant δ := by
  unfold siteSumConstant
  have h : Real.exp (-δ / 4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have : 0 < 1 - Real.exp (-δ / 4) := by linarith
  positivity
theorem abs_mixedDeriv_actionAtLevel_one_le [NeZero n] {a : ℝ} {L t : ℕ} {δ D : ℝ} {X : Finset (TorusSite n)}
    {W : TorusField n} (hδ : 0 < δ) (hD : 0 ≤ D) (hF : LevelEstimates a L t δ D X W) (c : Fin 1 → TorusBond n)
    (Xs : Fin 1 → imaginaryQuaternions) (hX : AreUnitVectors Xs) :
    |mixedDeriv (actionAtLevel a L t X) W c Xs| ≤ D * siteSumConstant δ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
  rw [h1, mixedDeriv_sum_sites h2 (by norm_num)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h7 : ∀ y ∈ (Finset.univ : Finset (TorusSite n)), |mixedDeriv (levelShare a L t X y) W c Xs| ≤
      D * Real.exp (-δ * supDist y (c 0).1) := fun y _ => h4 1 c Xs 0 y le_rfl (by norm_num) hX
  refine (Finset.sum_le_sum h7).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_exp_neg_mul_supDist_le hδ _) hD
theorem bondListSpread_of_fin_one (c : Fin 1 → TorusBond n) [NeZero n] : bondListSpread c = 0 := by
  unfold bondListSpread
  refine Nat.le_zero.mp (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  rw [Subsingleton.elim l l', supDist_self]
theorem actionSmoothAlongMoves_of_minimalChain (hLV : minimalChainExistenceStatement) :
    ActionSmoothAlongMoves := by
  intro a δ L lam ρ σA cg N ha hL hc
  have hc0 := hc
  obtain ⟨hδ, hδ8, -, -, -, hσ, -, hN, -⟩ := hc
  have hN1 := hN 1
  have hN2 := hN 2
  have hN3 := hN 3
  have hz := baseLevelBound_nonneg
  set D := baseLevelBound + (N 1 + N 2 + N 3) with hDdef
  have hD : 0 ≤ D := by positivity
  have hK1 := siteSumConstant_nonneg hδ
  have hK2 := tailSumConstant_nonneg hδ
  set C := 1 + D + D * siteSumConstant δ + (1 + σA) * D + 2 * D * tailSumConstant δ with hCdef
  have hCpos : 0 < C := by positivity
  refine ⟨C, hCpos, fun t n _ hn X W hreg hcold => ?_⟩
  have facts : ∀ {X' : Finset (TorusSite n)} {W' : TorusField n}, IsRegularRegion X' 1024 → IsColdOn σA X' W' →
      LevelEstimates a L t δ D X' W' := by
    intro X' W' h1 h2
    cases t with
    | zero => exact (levelEstimates_zero hδ hδ8 a L X' W').mono (by rw [hDdef]; linarith)
    | succ t => exact (levelEstimates_succ hLV ha hL hc0 t hn h1 h2).mono (by rw [hDdef]; linarith)
  have hF := facts hreg hcold
  refine ⟨hF.2.2.1, fun k c Xs hk1 hk hX => ?_,
    fun X' W' z m hreg' hcold' hm hXX hWW k c Xs hk1 hk2 hX hcz => ?_⟩
  · rcases Nat.lt_or_ge 1 k with h2 | h2
    · refine (hF.2.2.2.2.1 k c Xs h2 hk hX).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have : 0 ≤ D * siteSumConstant δ := by positivity
      have : 0 ≤ (1 + σA) * D := by positivity
      have : 0 ≤ 2 * D * tailSumConstant δ := by positivity
      rw [hCdef]
      linarith
    · obtain rfl : k = 1 := by omega
      refine (abs_mixedDeriv_actionAtLevel_one_le hδ hD hF c Xs hX).trans ?_
      rw [bondListSpread_of_fin_one, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      have : 0 ≤ (1 + σA) * D := by positivity
      have : 0 ≤ 2 * D * tailSumConstant δ := by positivity
      rw [hCdef]
      linarith
  · have hF' := facts hreg' hcold'
    have hnear : ∀ y, 2 * supDist y z ≤ m →
        |mixedDeriv (levelShare a L t X y) W c Xs - mixedDeriv (levelShare a L t X' y) W' c Xs| ≤
          ((1 + σA) * D) * Real.exp (-δ * m) := by
      intro y hy
      cases t with
      | zero =>
        have hm4 := hcz ⟨0, hk1⟩
        have e := mixedDeriv_levelShare_zero_congr a L (X := X) (X' := X') (W := W) (W' := W') y c Xs
          (fun u hu => hXX u (by
            have := supDist_triangle u y z
            omega))
          (fun u i hu hu' => hWW u i (by
            have := supDist_triangle u y z
            omega) (by
            have := supDist_triangle (u + unitStep n i) y z
            omega))
        rw [e, sub_self, abs_zero]
        positivity
      | succ t =>
        refine (abs_mixedDeriv_levelShare_succ_sub_le hL hc0 t hn hreg hcold hreg' hcold' hm hXX hWW k c Xs
          hk1 hk2 hX hcz y hy).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hDdef]
        linarith
    have hres := abs_mixedDeriv_sub_le (sh := fun y => levelShare a L t X y) (sh' := fun y => levelShare a L t X' y)
      hδ hD (by positivity : 0 ≤ (1 + σA) * D) hk1 (by omega) c Xs hF.1 hF'.1 hF.2.1 hF'.2.1
      (fun y l => hF.2.2.2.1 k c Xs l y hk1 (by omega) hX)
      (fun y l => hF'.2.2.2.1 k c Xs l y hk1 (by omega) hX) hcz hnear
    refine hres.trans ?_
    have hle : (1 + σA) * D + 2 * D * tailSumConstant δ ≤ C := by
      have : 0 ≤ D * siteSumConstant δ := by positivity
      rw [hCdef]
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (by positivity)) (Real.exp_pos _).le
end YangMills.Construction.LevelAction
end
