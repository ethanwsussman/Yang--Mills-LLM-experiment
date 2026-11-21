import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativesOfSums
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOfHolonomies
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.GapTerms
variable {F : BlockFrame}
abbrev contourIndices (L : ℕ) : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) := centredCube L ×ˢ Finset.univ
def contourWeight (L : ℕ) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := (1 / (24 * (L : ℝ) ^ 4)) • ContinuousLinearMap.id ℝ ℍ[ℝ]
theorem contourAverage_eq_sum (c : F.Site F.top × Fin 4) (W : F.GaugeField F.depth) :
    contourAverage W c = 0 + ∑ q ∈ contourIndices F.blockSide, contourWeight F.blockSide
      ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2) : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourAverage contourWeight
  rw [zero_add, Finset.sum_product, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.smul_sum]
  rfl
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem card_contourIndices {L : ℕ} (hL : Odd L) : ((contourIndices L).card : ℝ) = 24 * (L : ℝ) ^ 4 := by
  rw [Finset.card_product, card_centredCube hL, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  push_cast
  norm_num [Nat.factorial]
  ring
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_contourAverage_mem_shell (hL : Odd F.blockSide) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4)
    (h : ∀ (o : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), o ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c o π - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖contourAverage W c‖ ∧ ‖contourAverage W c‖ ≤ 1 := by
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hN : ((contourIndices F.blockSide).card : ℝ) = 24 * (F.blockSide : ℝ) ^ 4 := card_contourIndices hL
  have hNpos : (0 : ℝ) < 24 * (F.blockSide : ℝ) ^ 4 := by positivity
  set H : (Fin 4 → ℤ) × Equiv.Perm (Fin 4) → ℍ[ℝ] := fun q =>
    ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2) : UnitQuaternion) : ℍ[ℝ]) with hH
  have hform : contourAverage W c = (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ q ∈ contourIndices F.blockSide, H q := by
    unfold contourAverage
    rw [Finset.sum_product]
  set U : ℍ[ℝ] := ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) with hU
  have hUn : ‖U‖ = 1 := norm_coe_unitQuaternion _
  have hup : ‖contourAverage W c‖ ≤ 1 := by
    rw [hform, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖∑ q ∈ contourIndices F.blockSide, H q‖ ≤ 24 * (F.blockSide : ℝ) ^ 4 := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ q ∈ contourIndices F.blockSide, ‖H q‖ ≤ 1 := fun q _ => (norm_coe_unitQuaternion _).le
      have h2 := Finset.sum_le_sum this
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, hN] at h2
      exact h2
    rw [one_div, inv_mul_le_iff₀ hNpos]
    linarith
  have hdiff : ‖contourAverage W c - U‖ ≤ 1 / 2 := by
    have e : contourAverage W c - U = (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ q ∈ contourIndices F.blockSide, (H q - U) := by
      rw [hform, Finset.sum_sub_distrib, smul_sub]
      simp only [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, hN, smul_smul]
      have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4) = 1 := by field_simp
      rw [this, one_smul]
    have hq : ∀ q ∈ contourIndices F.blockSide, ‖H q - U‖ ≤ 1 / 2 := by
      intro q hq
      have h1 := h q.1 q.2 (Finset.mem_product.1 hq).1
      unfold contourHolonomyDefect at h1
      have e1 : H q - U = (((pathHolonomy W (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2) *
          (V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) * U := by
        have : (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * U = 1 :=
          Unitary.star_mul_self_of_mem (V c.1 c.2).2
        rw [sub_mul, MulMemClass.coe_mul, mul_assoc, this, mul_one, one_mul]
      rw [e1, norm_mul, hUn, mul_one]
      exact h1
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖∑ q ∈ contourIndices F.blockSide, (H q - U)‖ ≤ (24 * (F.blockSide : ℝ) ^ 4) * (1 / 2) := by
      refine (norm_sum_le _ _).trans ?_
      have h2 := Finset.sum_le_sum hq
      rw [Finset.sum_const, nsmul_eq_mul, hN] at h2
      exact h2
    rw [one_div, inv_mul_le_iff₀ hNpos]
    linarith
  refine ⟨?_, hup⟩
  have := norm_sub_norm_le U (contourAverage W c)
  rw [hUn, norm_sub_rev] at this
  linarith
theorem length_bondContour_le (L : ℕ) (hL : Odd L) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4)
    (hh : h ∈ centredCube L) : (bondContour L h π i).length ≤ 5 * L := by
  have hleg : ∀ k : Fin 4, (h (π k)).natAbs * 2 + 1 ≤ L := by
    intro k
    have h1 := Fintype.mem_piFinset.1 hh (π k)
    rw [Finset.mem_Icc] at h1
    obtain ⟨m, hm⟩ := hL
    have h2 : (((L : ℤ) - 1) / 2) = m := by
      subst hm
      push_cast
      omega
    rw [h2] at h1
    omega
  have hfin : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hlen : (axisPath h π).length = (h (π 0)).natAbs + ((h (π 1)).natAbs +
      ((h (π 2)).natAbs + (h (π 3)).natAbs)) := by
    unfold axisPath
    rw [hfin]
    simp [List.flatMap_cons]
  have h0 := hleg 0
  have h1 := hleg 1
  have h2 := hleg 2
  have h3 := hleg 3
  simp only [bondContour, reversePath, List.length_append, List.length_replicate,
    List.length_map, List.length_reverse, hlen]
  omega
theorem siteOfCoords_add {lev : ℕ} (o o' : Fin 4 → ℤ) :
    (siteOfCoords lev (o + o') : F.Site lev) = siteOfCoords lev o + siteOfCoords lev o' := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem exists_offset_of_mem_pathPositiveBonds {lev : ℕ} (l : List PathStep) (x : F.Site lev)
    (b : F.Site lev × Fin 4) (h : b ∈ pathPositiveBonds x l) :
    ∃ o : Fin 4 → ℤ, (∀ i, (o i).natAbs ≤ l.length) ∧ b.1 = x + siteOfCoords lev o := by
  induction l generalizing x with
  | nil => simp [pathPositiveBonds] at h
  | cons st r ih =>
    simp only [pathPositiveBonds, List.mem_cons] at h
    have hst : ∃ v : Fin 4 → ℤ, (∀ i, (v i).natAbs ≤ 1) ∧
        stepDisplacement lev st = (siteOfCoords lev v : F.Site lev) := by
      obtain ⟨d, s⟩ := st
      cases s
      · refine ⟨-Pi.single d 1, fun i => ?_, ?_⟩
        · by_cases hi : i = d
          · subst hi
            simp
          · simp [Pi.single_eq_of_ne hi]
        · funext i
          simp [stepDisplacement, unitStep, siteOfCoords]
      · refine ⟨Pi.single d 1, fun i => ?_, rfl⟩
        by_cases hi : i = d
        · subst hi
          simp
        · simp [Pi.single_eq_of_ne hi]
    obtain ⟨v, hv, hsv⟩ := hst
    rcases h with h | h
    · obtain ⟨d, s⟩ := st
      cases s
      · refine ⟨-Pi.single d 1, fun i => ?_, ?_⟩
        · have h1 : ((-Pi.single d 1 : Fin 4 → ℤ) i).natAbs ≤ 1 := by
            by_cases hi : i = d
            · subst hi
              simp
            · simp [Pi.single_eq_of_ne hi]
          simp only [List.length_cons]
          omega
        · rw [h]
          funext i
          simp [unitStep, siteOfCoords, sub_eq_add_neg]
      · refine ⟨0, fun i => by simp, ?_⟩
        rw [h]
        funext i
        simp [siteOfCoords]
    · obtain ⟨o, ho, hb⟩ := ih _ h
      refine ⟨v + o, fun i => ?_, ?_⟩
      · have := Int.natAbs_add_le (v i) (o i)
        have h1 := hv i
        have h2 := ho i
        simp only [Pi.add_apply, List.length_cons]
        omega
      · rw [hb, hsv, siteOfCoords_add, add_assoc]
def OnContour (c : F.Site F.top × Fin 4) (b : F.Site F.depth × Fin 4) : Prop :=
  ∃ q ∈ contourIndices F.blockSide, b ∈ pathPositiveBonds (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2)
theorem exists_offset_of_onContour (hL : Odd F.blockSide) {c : F.Site F.top × Fin 4}
    {b : F.Site F.depth × Fin 4} (h : OnContour c b) :
    ∃ o : Fin 4 → ℤ, (∀ i, (o i).natAbs ≤ 5 * F.blockSide) ∧ b.1 = refineSite c.1 + siteOfCoords F.depth o := by
  obtain ⟨q, hq, hb⟩ := h
  obtain ⟨o, ho, hbo⟩ := exists_offset_of_mem_pathPositiveBonds _ _ _ hb
  exact ⟨o, fun i => (ho i).trans
    (length_bondContour_le F.blockSide hL q.1 q.2 c.2 (Finset.mem_product.1 hq).1), hbo⟩
open Classical in
theorem card_filter_onContour_le (hL : Odd F.blockSide) (hcell : ∀ y : F.Cell, enclosingCell (refineSite y) = y)
    (S : Finset (F.Site F.top × Fin 4)) (b : F.Site F.depth × Fin 4) :
    (S.filter fun c => OnContour c b).card ≤ (10 * F.blockSide + 1) ^ 4 * 4 := by
  set R : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset fun _ => Finset.Icc (-(5 * (F.blockSide : ℤ))) (5 * (F.blockSide : ℤ)) with hR
  set T : Finset (F.Site F.top × Fin 4) :=
    (R ×ˢ (Finset.univ : Finset (Fin 4))).image
      fun r => (enclosingCell (b.1 - siteOfCoords F.depth r.1), r.2) with hT
  have hsub : (S.filter fun c => OnContour c b) ⊆ T := by
    intro c hc
    obtain ⟨o, ho, hbo⟩ := exists_offset_of_onContour hL (Finset.mem_filter.1 hc).2
    refine Finset.mem_image.2 ⟨(o, c.2), Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · rw [hR, Fintype.mem_piFinset]
      intro i
      have := ho i
      change o i ∈ Finset.Icc (-(5 * (F.blockSide : ℤ))) (5 * (F.blockSide : ℤ))
      rw [Finset.mem_Icc]
      omega
    · simp only [hbo, add_sub_cancel_right, hcell]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_product, hR, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  have : (5 * (F.blockSide : ℤ) + 1 - -(5 * (F.blockSide : ℤ))).toNat = 10 * F.blockSide + 1 := by omega
  rw [this]
def contourDerivBound (B : ℕ → ℕ → ℝ) (k L : ℕ) : ℝ :=
  ∑ i : Fin 4, ∑ q ∈ contourIndices L, ‖contourWeight L‖ * B k (bondContour L q.1 q.2 i).length
theorem contourDerivBound_nonneg {B : ℕ → ℕ → ℝ} (hB : ∀ k n, 0 ≤ B k n) (k L : ℕ) :
    0 ≤ contourDerivBound B k L :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg (contourWeight L)) (hB _ _)
theorem sum_le_contourDerivBound {B : ℕ → ℕ → ℝ} (hB : ∀ k n, 0 ≤ B k n) (k L : ℕ) (i : Fin 4)
    (S : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4))) (hS : S ⊆ contourIndices L) :
    ∑ q ∈ S, ‖contourWeight L‖ * B k (bondContour L q.1 q.2 i).length ≤ contourDerivBound B k L := by
  have h1 : ∑ q ∈ S, ‖contourWeight L‖ * B k (bondContour L q.1 q.2 i).length ≤
      ∑ q ∈ contourIndices L, ‖contourWeight L‖ * B k (bondContour L q.1 q.2 i).length :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => mul_nonneg (norm_nonneg (contourWeight L)) (hB _ _)
  exact h1.trans (Finset.single_le_sum
    (f := fun i => ∑ q ∈ contourIndices L, ‖contourWeight L‖ * B k (bondContour L q.1 q.2 i).length)
    (fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg (contourWeight L)) (hB _ _))
    (Finset.mem_univ i))
theorem stepCoordinates_zero : stepCoordinates (0 : StepVariable (finiteCells F)) = fun _ _ => 0 := by
  classical
  funext x i
  unfold stepCoordinates
  split_ifs
  · apply Subtype.ext
    refine Quaternion.ext _ _ rfl ?_ ?_ ?_ <;> rfl
  · rfl
set_option maxHeartbeats 2000000 in
theorem gapTermsChartBounds_holds (hS : HolonomySumDerivBounds) (hC : ChartSecondDerivBound)
    (hK : HaarGapOfNormNearOne) (hSum : Calculus.FderivFinsetSum)
    (hD : SupDistCellComparison) : GapTermsChartBounds := by
  classical
  intro L hL
  obtain ⟨B, hB0, hB⟩ := hS
  obtain ⟨C, hCpos, hC⟩ := hC
  obtain ⟨K, hKpos, hK⟩ := hK
  have hT1 := contourDerivBound_nonneg hB0 1 L
  have hT2 := contourDerivBound_nonneg hB0 2 L
  set T1 : ℝ := contourDerivBound B 1 L with hT1d
  set T2 : ℝ := contourDerivBound B 2 L with hT2d
  set J : ℝ := K * (C ^ 2 * T1 ^ 2 + C ^ 2 * T2 + C * T1) with hJ
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (((10 * L + 1) ^ 4 * 4 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by positivity
  have hN0 : 0 ≤ N := by
    rw [hN]
    exact Nat.cast_nonneg _
  have hm1 : 0 ≤ K * C * T1 * N :=
    mul_nonneg (mul_nonneg (mul_nonneg hKpos.le hCpos.le) hT1) hN0
  have hm2 : 0 ≤ J * N := mul_nonneg hJ0 hN0
  have hCg : 0 < K * C * T1 * N + J * N + 1 := by linarith
  refine ⟨K * C * T1 * N + J * N + 1, hCg, ?_⟩
  intro F V w A hFL hs hA hw hcon
  subst hFL
  have hcell : ∀ y : F.Cell, enclosingCell (refineSite y) = y := fun y => (hD.2.2 F hL hs).2.2 y
  set W : F.GaugeField F.depth := chartedField w V with hWd
  set Mc : (F.Site F.top × Fin 4) → StepVariable (finiteCells F) → ℍ[ℝ] :=
    fun c => readInChart (fun W' => contourAverage W' c) w V with hMc
  have key : ∀ c : F.Site F.top × Fin 4, ContDiffAt ℝ 3 (Mc c) 0 ∧
      ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        ‖fderiv ℝ (Mc c) 0 (bondVariation b e)‖ ≤ C * (if OnContour c b.1 then T1 else 0) * ‖e‖ ∧
        ‖fderiv ℝ (fun ζ => fderiv ℝ (Mc c) ζ (bondVariation b e)) 0 (bondVariation b' e')‖ ≤
          (C ^ 2 * (if OnContour c b.1 ∧ OnContour c b'.1 then T2 else 0) +
            if b = b' then C * (if OnContour c b.1 then T1 else 0) else 0) * ‖e‖ * ‖e'‖ := by
    intro c
    have hall := hB F F.depth ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) (contourIndices F.blockSide)
      (fun _ => refineSite c.1) (fun q => bondContour F.blockSide q.1 q.2 c.2) ℍ[ℝ]
      (fun _ => contourWeight F.blockSide) 0 (fun W' => contourAverage W' c) (contourAverage_eq_sum c) W
    obtain ⟨h3, hd⟩ := hall
    have u1 : ∀ (b : ↥(chordBonds (finiteCells F))) (X : imaginaryQuaternions), ‖X‖ = 1 →
        ‖bondDeriv (fun W' => contourAverage W' c) W ![b.1] ![X]‖ ≤
          if OnContour c b.1 then T1 else 0 := by
      intro b X hX
      have h := hd 1 ![b.1] ![X] le_rfl (by intro l; fin_cases l; simpa using hX)
      refine h.trans ?_
      by_cases hon : OnContour c b.1
      · rw [if_pos hon]
        exact sum_le_contourDerivBound hB0 1 F.blockSide c.2 _ (Finset.filter_subset _ _)
      · rw [if_neg hon]
        have : (contourIndices F.blockSide).filter (fun q => ∀ i, (![b.1] : Fin 1 → _) i ∈
            pathPositiveBonds (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2)) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun q hq hall => hon ⟨q, hq, ?_⟩
          simpa using hall 0
        rw [this]
        simp
    have u2 : ∀ (b b' : ↥(chordBonds (finiteCells F))) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
        ‖bondDeriv (fun W' => contourAverage W' c) W ![b'.1, b.1] ![X', X]‖ ≤
          if OnContour c b.1 ∧ OnContour c b'.1 then T2 else 0 := by
      intro b b' X X' hX hX'
      have h := hd 2 ![b'.1, b.1] ![X', X] (by norm_num)
        (by intro l; fin_cases l <;> simpa using ‹_›)
      refine h.trans ?_
      by_cases hon : OnContour c b.1 ∧ OnContour c b'.1
      · rw [if_pos hon]
        exact sum_le_contourDerivBound hB0 2 F.blockSide c.2 _ (Finset.filter_subset _ _)
      · rw [if_neg hon]
        have : (contourIndices F.blockSide).filter (fun q => ∀ i, (![b'.1, b.1] : Fin 2 → _) i ∈
            pathPositiveBonds (refineSite c.1) (bondContour F.blockSide q.1 q.2 c.2)) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun q hq hall => hon ⟨⟨q, hq, ?_⟩, ⟨q, hq, ?_⟩⟩
          · simpa using hall 1
          · simpa using hall 0
        rw [this]
        simp
    obtain ⟨hcd, _, hbd⟩ := hC F V w ℍ[ℝ] (fun W' => contourAverage W' c) hw h3
    exact ⟨hcd, fun b b' e e' => hbd (fun b => if OnContour c b.1 then T1 else 0)
      (fun b' b => if OnContour c b.1 ∧ OnContour c b'.1 then T2 else 0) u1 u2 b b' e e'⟩
  have hM0 : ∀ c, Mc c 0 = contourAverage W c := by
    intro c
    simp only [hMc, readInChart, stepCoordinates_zero, add_zero]
    rfl
  have hshell : ∀ c, 1 / 2 ≤ ‖Mc c 0‖ ∧ ‖Mc c 0‖ ≤ 1 := by
    intro c
    rw [hM0]
    exact norm_contourAverage_mem_shell hL W V c fun h π hh => hcon c h π hh
  set Bn : Finset (F.Site F.top × Fin 4) := innerBonds (finiteCells F) F.top with hBn
  set g : (F.Site F.top × Fin 4) → StepVariable (finiteCells F) → ℝ :=
    fun c ζ => haarGap (A * ‖Mc c ζ‖) - haarGap A with hg
  have hgap : ∀ c, _ := fun c => hK (StepVariable (finiteCells F)) (Mc c) A hA (key c).1 (hshell c).1
    (hshell c).2
  have hread : readInChart (gapExcessSum A) w V = fun ζ => ∑ c ∈ Bn, g c ζ := rfl
  rw [hread]
  have hsum := hSum (StepVariable (finiteCells F)) (F.Site F.top × Fin 4) Bn g 0
    (fun c _ => (hgap c).1)
  refine ⟨hsum.1, fun b b' e e' => ?_⟩
  obtain ⟨hf1, hf2⟩ := hsum.2 (bondVariation b e) (bondVariation b' e')
  have hne := norm_nonneg e
  have hne' := norm_nonneg e'
  have hcount : ((Bn.filter fun c => OnContour c b.1).card : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast card_filter_onContour_le hL hcell Bn b.1
  constructor
  · rw [hf1]
    have hterm : ∀ c ∈ Bn, |fderiv ℝ (g c) 0 (bondVariation b e)| ≤
        if OnContour c b.1 then K * C * T1 * ‖e‖ else 0 := by
      intro c _
      have h1 := ((hgap c).2 (bondVariation b e) (bondVariation b e)).1
      have h2 := ((key c).2 b b e e).1
      by_cases hon : OnContour c b.1
      · simp only [hon, if_true] at h2 ⊢
        calc _ ≤ K * ‖fderiv ℝ (Mc c) 0 (bondVariation b e)‖ := h1
          _ ≤ K * (C * T1 * ‖e‖) := mul_le_mul_of_nonneg_left h2 hKpos.le
          _ = _ := by ring
      · simp only [hon, if_false, mul_zero, zero_mul] at h2 ⊢
        have : ‖fderiv ℝ (Mc c) 0 (bondVariation b e)‖ = 0 := le_antisymm h2 (norm_nonneg _)
        rw [this, mul_zero] at h1
        exact h1
    calc _ ≤ ∑ c ∈ Bn, |fderiv ℝ (g c) 0 (bondVariation b e)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c ∈ Bn, (if OnContour c b.1 then K * C * T1 * ‖e‖ else 0) := Finset.sum_le_sum hterm
      _ = ((Bn.filter fun c => OnContour c b.1).card : ℝ) * (K * C * T1 * ‖e‖) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (K * C * T1 * ‖e‖) := mul_le_mul_of_nonneg_right hcount (by positivity)
      _ ≤ (K * C * T1 * N + J * N + 1) * ‖e‖ := by
          have : 0 ≤ (J * N + 1) * ‖e‖ := by positivity
          nlinarith
  · rw [hf2]
    have hterm : ∀ c ∈ Bn,
        |fderiv ℝ (fun ζ => fderiv ℝ (g c) ζ (bondVariation b e)) 0 (bondVariation b' e')| ≤
          if OnContour c b.1 ∧ OnContour c b'.1 then J * ‖e‖ * ‖e'‖ else 0 := by
      intro c _
      have h1 := ((hgap c).2 (bondVariation b e) (bondVariation b' e')).2
      have a1 := ((key c).2 b b' e e').1
      have a2 := ((key c).2 b' b e' e).1
      have a3 := ((key c).2 b b' e e').2
      by_cases hon : OnContour c b.1 ∧ OnContour c b'.1
      · simp only [hon.1, hon.2, and_self, if_true] at a1 a2 a3 ⊢
        have b1 : ‖fderiv ℝ (Mc c) 0 (bondVariation b e)‖ * ‖fderiv ℝ (Mc c) 0 (bondVariation b' e')‖ ≤
            (C * T1 * ‖e‖) * (C * T1 * ‖e'‖) :=
          mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
        have b2 : ‖fderiv ℝ (fun ζ => fderiv ℝ (Mc c) ζ (bondVariation b e)) 0 (bondVariation b' e')‖ ≤
            (C ^ 2 * T2 + C * T1) * ‖e‖ * ‖e'‖ := by
          refine a3.trans ?_
          by_cases hbb : b = b'
          · simp only [hbb, if_true]
            rfl
          · simp only [hbb, if_false, add_zero]
            have : 0 ≤ C * T1 * ‖e‖ * ‖e'‖ := by positivity
            nlinarith
        calc _ ≤ K * (‖fderiv ℝ (Mc c) 0 (bondVariation b e)‖ * ‖fderiv ℝ (Mc c) 0 (bondVariation b' e')‖ +
              ‖fderiv ℝ (fun ζ => fderiv ℝ (Mc c) ζ (bondVariation b e)) 0 (bondVariation b' e')‖) := h1
          _ ≤ K * ((C * T1 * ‖e‖) * (C * T1 * ‖e'‖) + (C ^ 2 * T2 + C * T1) * ‖e‖ * ‖e'‖) :=
              mul_le_mul_of_nonneg_left (add_le_add b1 b2) hKpos.le
          _ = _ := by rw [hJ]; ring
      · rw [if_neg hon]
        have hz : ‖fderiv ℝ (Mc c) 0 (bondVariation b e)‖ * ‖fderiv ℝ (Mc c) 0 (bondVariation b' e')‖ = 0 := by
          by_cases h0 : OnContour c b.1
          · have h0' : ¬ OnContour c b'.1 := fun h => hon ⟨h0, h⟩
            simp only [h0', if_false, mul_zero, zero_mul] at a2
            rw [le_antisymm a2 (norm_nonneg _), mul_zero]
          · simp only [h0, if_false, mul_zero, zero_mul] at a1
            rw [le_antisymm a1 (norm_nonneg _), zero_mul]
        have hz2 : ‖fderiv ℝ (fun ζ => fderiv ℝ (Mc c) ζ (bondVariation b e)) 0 (bondVariation b' e')‖ = 0 := by
          refine le_antisymm (a3.trans (le_of_eq ?_)) (norm_nonneg _)
          rw [if_neg hon]
          by_cases hbb : b = b'
          · subst hbb
            have h0 : ¬ OnContour c b.1 := fun h => hon ⟨h, h⟩
            simp [h0]
          · simp [hbb]
        rw [hz, hz2] at h1
        simpa using h1
    by_cases hclose : siteSupDist b.1.1 b'.1.1 ≤ 10 * F.blockSide
    · rw [if_pos hclose]
      have hsub : ((Bn.filter fun c => OnContour c b.1 ∧ OnContour c b'.1).card : ℝ) ≤ N := by
        refine le_trans ?_ hcount
        have hsubset : (Bn.filter fun c => OnContour c b.1 ∧ OnContour c b'.1) ⊆
            Bn.filter fun c => OnContour c b.1 := by
          intro c hc
          have h := Finset.mem_filter.1 hc
          exact Finset.mem_filter.2 ⟨h.1, h.2.1⟩
        exact_mod_cast Finset.card_le_card hsubset
      calc _ ≤ ∑ c ∈ Bn, |fderiv ℝ (fun ζ => fderiv ℝ (g c) ζ (bondVariation b e)) 0 (bondVariation b' e')| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ c ∈ Bn, (if OnContour c b.1 ∧ OnContour c b'.1 then J * ‖e‖ * ‖e'‖ else 0) :=
            Finset.sum_le_sum hterm
        _ = ((Bn.filter fun c => OnContour c b.1 ∧ OnContour c b'.1).card : ℝ) * (J * ‖e‖ * ‖e'‖) := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * (J * ‖e‖ * ‖e'‖) := mul_le_mul_of_nonneg_right hsub (by positivity)
        _ ≤ (K * C * T1 * N + J * N + 1) * ‖e‖ * ‖e'‖ := by
            have : 0 ≤ (K * C * T1 * N + 1) * ‖e‖ * ‖e'‖ := by positivity
            nlinarith
    · rw [if_neg hclose, zero_mul, zero_mul]
      have hall : ∀ c ∈ Bn, ¬ (OnContour c b.1 ∧ OnContour c b'.1) := by
        intro c _ hon
        apply hclose
        obtain ⟨o, ho, hbo⟩ := exists_offset_of_onContour hL hon.1
        obtain ⟨o', ho', hbo'⟩ := exists_offset_of_onContour hL hon.2
        have e1 : b'.1.1 = b.1.1 + siteOfCoords F.depth (o' - o) := by
          rw [hbo, hbo']
          funext i
          simp [siteOfCoords]
        rw [e1]
        refine hD.2.1 F F.depth _ _ _ fun i => ?_
        have h1 := ho i
        have h2 := ho' i
        have := Int.natAbs_sub_le (o' i) (o i)
        simp only [Pi.sub_apply]
        omega
      have : ∑ c ∈ Bn, fderiv ℝ (fun ζ => fderiv ℝ (g c) ζ (bondVariation b e)) 0 (bondVariation b' e') = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        have := hterm c hc
        rw [if_neg (hall c hc)] at this
        exact abs_nonpos_iff.1 this
      rw [this]
      simp
end YangMills.Construction.ColdStepAtMirrorFrames.GapTerms
end
