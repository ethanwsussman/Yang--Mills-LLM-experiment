import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlat
import YangMills.Construction.ColdChainAtEveryLevel.EveryFormSplitsAlongTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceFormAtAFlatTopProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondOrderOfAShareAtItsResponse
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.BlockAverages
namespace ResponseSecondOrder
variable {F : BlockFrame}
theorem eq_zero_of_le_mul_small {x M c : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (h : ∀ s, 0 < s → s ≤ c → x ≤ M * s) : x = 0 := by apply _root_.YangMills.Construction.BlockAverages.FlatTopHessian.eq_zero_of_le_mul_small <;> assumption
theorem isCold_flatTopField (S : Finset F.Cell) {s : ℝ} (hs : 0 < s) :
    IsCold S F.top s (flatTopField : F.GaugeField F.top) := by apply _root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.flatTopField_isCold <;> assumption
theorem plaquettesOver_self (hodd : Odd F.blockSide) (S : Finset F.Cell) :
    plaquettesOver S S 0 = innerPlaquettes S 0 := by apply _root_.YangMills.Construction.SecondDifferences.plaquettesOver_self <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (x + y) = _root_.YangMills.Construction.BlockAverages.adjointAction g x + _root_.YangMills.Construction.BlockAverages.adjointAction g y := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (t : ℝ) (x : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (t • x) = t • _root_.YangMills.Construction.BlockAverages.adjointAction g x := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem linearizedCurl_chartMove (R : F.GaugeField 0) (U A : ChainChart F) (τ : ℝ)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R (chartMove U A τ).fine p = linearizedCurl R U.fine p + τ • linearizedCurl R A.fine p := by
  simp only [linearizedCurl, chartMove, Submodule.coe_add, Submodule.coe_smul, _root_.YangMills.Construction.BlockAverages.ResponseSecondOrder.adjointAction_add,
    _root_.YangMills.Construction.BlockAverages.ResponseSecondOrder.adjointAction_smul, smul_add, smul_sub]
  abel
theorem parallelAverage_add_smul {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ]) (τ : ℝ)
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i + τ • g x i) c =
      parallelAverage R f c + τ • parallelAverage R g c := by
  simp only [parallelAverage, _root_.YangMills.Construction.BlockAverages.ResponseSecondOrder.adjointAction_add, _root_.YangMills.Construction.BlockAverages.ResponseSecondOrder.adjointAction_smul, Finset.sum_add_distrib, smul_add,
    ← Finset.smul_sum]
  rw [smul_comm τ]
theorem linearPart_chartMove (R : F.FieldChain) (U A : ChainChart F) (τ : ℝ) (j : ℕ) :
    ∀ x i, linearPart R (chartMove U A τ) j x i = linearPart R U j x i + τ • linearPart R A j x i := by
  induction j with
  | zero =>
    intro x i
    simp [linearPart, chartMove]
  | succ j ih =>
    intro y i
    simp only [linearPart]
    have h : linearPart R (chartMove U A τ) j = fun x i => linearPart R U j x i + τ • linearPart R A j x i := by
      funext x i
      exact ih x i
    rw [h, parallelAverage_add_smul]
    by_cases hj : j + 1 < F.top
    · simp only [if_pos hj, chartMove, Submodule.coe_add, Submodule.coe_smul, smul_add]
      abel
    · simp only [if_neg hj, add_zero]
theorem sum_norm_add_smul_sq {ι : Type} (s : Finset ι) (x y : ι → ℍ[ℝ]) (τ : ℝ) :
    ∑ i ∈ s, ‖x i + τ • y i‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 + 2 * τ * ∑ i ∈ s, inner ℝ (x i) (y i) +
      τ ^ 2 * ∑ i ∈ s, ‖y i‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring
theorem eq_zero_of_quadratic_nonneg {P Q : ℝ} (h : ∀ τ : ℝ, 0 ≤ 2 * τ * P + τ ^ 2 * Q) : P = 0 := by apply _root_.YangMills.SharedProofs.p10126 <;> assumption
theorem weightedQuadraticEnergy_chartMove (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (D A : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ∃ Q : ℝ, ∀ τ : ℝ,
      weightedQuadraticEnergy a S (fun _ => 1) (fun _ _ => 1) R (chartMove D A τ) v =
        weightedQuadraticEnergy a S (fun _ => 1) (fun _ _ => 1) R D v +
          2 * τ * (responseBilinear a S R D A - responseLinear a S R v A) + τ ^ 2 * Q := by
  refine ⟨∑ p ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) A.fine p‖ ^ 2 +
    a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
      ‖((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 +
    a * ∑ c ∈ innerBonds S F.top, ‖- linearPart R A F.top c.1 c.2‖ ^ 2, fun τ => ?_⟩
  have h1 : ∑ p ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) (chartMove D A τ).fine p‖ ^ 2 =
      ∑ p ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) D.fine p‖ ^ 2 +
        2 * τ * ∑ p ∈ innerPlaquettes S 0,
          inner ℝ (linearizedCurl (R 0) D.fine p) (linearizedCurl (R 0) A.fine p) +
        τ ^ 2 * ∑ p ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) A.fine p‖ ^ 2 := by
    simp only [linearizedCurl_chartMove]
    exact sum_norm_add_smul_sq _ _ _ _
  have h2 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
        ‖(((chartMove D A τ).coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          ‖((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 +
        2 * τ * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          inner ℝ ((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])
            ((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) +
        τ ^ 2 * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          ‖((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [chartMove, Submodule.coe_add, Submodule.coe_smul]
    exact sum_norm_add_smul_sq _ _ _ _
  have h3 : ∑ c ∈ innerBonds S F.top,
        ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R (chartMove D A τ) F.top c.1 c.2‖ ^ 2 =
      ∑ c ∈ innerBonds S F.top, ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2 +
        2 * τ * ∑ c ∈ innerBonds S F.top,
          inner ℝ (((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2)
            (- linearPart R A F.top c.1 c.2) +
        τ ^ 2 * ∑ c ∈ innerBonds S F.top, ‖- linearPart R A F.top c.1 c.2‖ ^ 2 := by
    rw [← sum_norm_add_smul_sq]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [linearPart_chartMove]
    congr 2
    rw [smul_neg]
    abel
  have h4 : ∑ c ∈ innerBonds S F.top,
        inner ℝ (((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2)
          (- linearPart R A F.top c.1 c.2) =
      ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart R D F.top c.1 c.2) (linearPart R A F.top c.1 c.2) -
        ∑ c ∈ innerBonds S F.top,
          inner ℝ ((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) (linearPart R A F.top c.1 c.2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_neg_right, inner_sub_left]
    ring
  simp only [weightedQuadraticEnergy, one_mul]
  rw [h1, h2, h3, h4]
  simp only [responseBilinear, responseLinear]
  have e : F.top - 1 = F.depth := rfl
  rw [e]
  ring
end ResponseSecondOrder
open ResponseSecondOrder in
theorem shareSecondDerivAtResponse_holds (hFO : criticalChainFirstOrderStatement)
    (hSp : sliceDecompositionStatement) (hDF : covariantDiffNearlyFlatStatement) :
    shareSecondDerivAtResponseStatement := by
  intro a ha
  obtain ⟨L₁, hFO⟩ := hFO a ha
  obtain ⟨c₀, L₂, hc₀, hSp⟩ := hSp
  obtain ⟨L₃, hDF⟩ := hDF
  refine ⟨max L₁ (max L₂ L₃), fun L hodd hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL3 : L₃ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨c₂, C₂, hc₂, hC₂, hDF⟩ := hDF L hodd hL3
  intro F m S hFL hamb hm hreg v
  have hoddF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hL2' : L₂ ≤ F.blockSide := by rw [hFL]; exact hL2
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hRd
  obtain ⟨D, hmin, hsh⟩ := hFO L hodd hL1 F m S hFL hamb hm hreg v
  obtain ⟨u₁, ξ, hsl, hmf, -, hu⟩ := hSp F m S hoddF hL2' hamb hm hreg c₀ flatTopField hc₀ le_rfl
    (isCold_flatTopField S hc₀) D.fine
  set g : F.Site 0 → Fin 4 → imaginaryQuaternions := fun x i => D.fine x i - u₁ x i with hg
  have hgd : ∀ x i, ((g x i : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff (R 0) ξ x i := fun x i => by
    simp only [hg, Submodule.coe_sub]
    rw [hu x i]
    abel
  have hw : ∀ (j : ℕ) (x : F.Site j), classWeight F (fun _ => 0) 0 0 j x = 1 := fun j x => by
    simp [classWeight]
  set X1 : ℝ := Real.sqrt (∑ q ∈ plaquettesOver S S 0, (classWeight F (fun _ => 0) 0 0 0 q.1 *
    ‖linearizedCurl (R 0) g q‖) ^ 2) with hX1
  set X2 : ℝ := Real.sqrt (∑ c ∈ innerBonds S F.top, (classWeight F (fun _ => 0) 0 0 F.top c.1 *
    ‖linearPart R (baseOnlyChart g) F.top c.1 c.2‖) ^ 2) with hX2
  have hX0 : X1 + X2 = 0 := by
    refine eq_zero_of_le_mul_small
      (M := C₂ * cellwiseL4Norm S (classWeight F (fun _ => 0) 0 0 0) (fun x i => g x i))
      hc₂ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) fun s hs hsc => ?_
    have := hDF F m S hFL hamb hm hreg s flatTopField hs hsc (isCold_flatTopField S hs) (fun _ => 0) 0 0 0
      (by norm_num) (by norm_num) (fun y y' => by simp) ξ g hmf hgd
    calc X1 + X2 ≤ _ := this
      _ = _ := by ring
  have hX1z : X1 = 0 := by
    have := Real.sqrt_nonneg (∑ c ∈ innerBonds S F.top, (classWeight F (fun _ => 0) 0 0 F.top c.1 *
      ‖linearPart R (baseOnlyChart g) F.top c.1 c.2‖) ^ 2)
    have h1 := Real.sqrt_nonneg (∑ q ∈ plaquettesOver S S 0, (classWeight F (fun _ => 0) 0 0 0 q.1 *
      ‖linearizedCurl (R 0) g q‖) ^ 2)
    linarith
  have hX2z : X2 = 0 := by linarith
  have hcurl : ∀ p ∈ innerPlaquettes S 0, linearizedCurl (R 0) g p = 0 := by
    intro p hp
    have h1 := (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 hX1z
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h1 p
      (by rw [plaquettesOver_self hoddF]; exact hp)
    rw [hw] at h2
    simpa using h2
  have hnu : ∀ c ∈ innerBonds S F.top, linearPart R (baseOnlyChart g) F.top c.1 c.2 = 0 := by
    intro c hc
    have h1 := (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 hX2z
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h1 c hc
    rw [hw] at h2
    simpa using h2
  set U : ChainChart F := ⟨u₁, D.coarse⟩ with hU
  have hDU : D = chartMove U (baseOnlyChart g) 1 := by
    cases D with
    | mk du dm =>
      simp only [hU, chartMove, baseOnlyChart, hg]
      congr
      · funext x i
        simp
      · funext j y i
        simp
  have hcu : ∀ p ∈ innerPlaquettes S 0, linearizedCurl (R 0) D.fine p = linearizedCurl (R 0) U.fine p := by
    intro p hp
    have h1 := linearizedCurl_chartMove (R 0) U (baseOnlyChart g) 1 p
    rw [← hDU] at h1
    rw [h1]
    have h2 : linearizedCurl (R 0) (baseOnlyChart g).fine p = 0 := hcurl p hp
    rw [h2, smul_zero, add_zero]
  have hnD : ∀ c ∈ innerBonds S F.top, linearPart R D F.top c.1 c.2 = linearPart R U F.top c.1 c.2 := by
    intro c hc
    have h1 := linearPart_chartMove R U (baseOnlyChart g) 1 F.top c.1 c.2
    rw [← hDU] at h1
    rw [h1, hnu c hc, smul_zero, add_zero]
  have heuler : ∀ A : ChainChart F, responseBilinear a S R D A = responseLinear a S R v A := by
    intro A
    obtain ⟨Q, hQ⟩ := weightedQuadraticEnergy_chartMove a S R D A v
    refine sub_eq_zero.1 (eq_zero_of_quadratic_nonneg (Q := Q) fun τ => ?_)
    have h1 := hmin (chartMove D A τ)
    unfold flatTopEnergy at h1
    rw [hQ τ] at h1
    linarith
  have hform : ∀ A : ChainChart F, responseBilinear a S R U A = responseBilinear a S R D A := by
    intro A
    unfold responseBilinear
    have e1 : ∑ p ∈ innerPlaquettes S 0, inner ℝ (linearizedCurl (R 0) U.fine p) (linearizedCurl (R 0) A.fine p) =
        ∑ p ∈ innerPlaquettes S 0, inner ℝ (linearizedCurl (R 0) D.fine p) (linearizedCurl (R 0) A.fine p) :=
      Finset.sum_congr rfl fun p hp => by rw [hcu p hp]
    have e3 : ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart R U F.top c.1 c.2) (linearPart R A F.top c.1 c.2) =
        ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart R D F.top c.1 c.2) (linearPart R A F.top c.1 c.2) :=
      Finset.sum_congr rfl fun c hc => by rw [hnD c hc]
    rw [e1, e3]
  refine ⟨U, ⟨hsl, fun A _ => by rw [hform, heuler]⟩, (hsh 0).trans ?_⟩
  unfold weightedQuadraticEnergy responseCellShare topDirectionDefect
  have e1 : ∑ p ∈ innerPlaquettes S 0, plaquetteCornerShare 0 p * ‖linearizedCurl (R 0) D.fine p‖ ^ 2 =
      ∑ p ∈ innerPlaquettes S 0, plaquetteCellShare 0 p * ‖linearizedCurl (R 0) U.fine p‖ ^ 2 :=
    Finset.sum_congr rfl fun p hp => by rw [hcu p hp]; rfl
  have e3 : ∑ c ∈ innerBonds S F.top, bondEndShare 0 F.depth c *
        ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2 =
      ∑ c ∈ innerBonds S F.top, bondCellShare 0 c *
        ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R U F.top c.1 c.2‖ ^ 2 :=
    Finset.sum_congr rfl fun c hc => by rw [hnD c hc]; rfl
  rw [e1, e3]
  rfl
end YangMills.Construction.BlockAverages
end
