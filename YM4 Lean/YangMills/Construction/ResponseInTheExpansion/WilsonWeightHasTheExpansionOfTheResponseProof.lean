import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoToriProof
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansionProof
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamilyProof
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtARadiusWithNoLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps WeightedResponses StepCosts
section Corners
abbrev CornerChoice : Type := Fin 4 × Fin 4 × Bool × Bool
def cornerChoices : Finset CornerChoice := Finset.univ.filter fun i => i.1 < i.2.1
def baseOffset (i : CornerChoice) : Fin 4 → ℤ := fun j =>
  -(if i.2.2.1 = true ∧ j = i.1 then 1 else 0) - (if i.2.2.2 = true ∧ j = i.2.1 then 1 else 0)
def coordVector (i : Fin 4) : Fin 4 → ℤ := fun j => if j = i then 1 else 0
theorem card_cornerChoices : cornerChoices.card = 24 := by decide
variable {n : ℕ}
theorem siteOfInt_coordVector (i : Fin 4) : (siteOfInt (coordVector i) : TorusSite n) = unitStep n i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [siteOfInt, coordVector, unitStep]
  · simp [siteOfInt, coordVector, unitStep, h]
def plaquetteAt (y : TorusSite n) (i : CornerChoice) : TorusPlaquette n :=
  (y + siteOfInt (baseOffset i), i.1, i.2.1)
theorem vertexMultiplicity_eq_sum (y x : TorusSite n) (μ ν : Fin 4) :
    vertexMultiplicity y (x, μ, ν) =
      ∑ ab : Bool × Bool, if x = y + siteOfInt (baseOffset (μ, ν, ab.1, ab.2)) then (1 : ℝ) else 0 := by apply _root_.YangMills.DeltaSharedProofs.p502373 <;> assumption
theorem sum_vertexMultiplicity_mul [NeZero n] (y : TorusSite n) (F : TorusPlaquette n → ℝ) :
    ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * F p =
      ∑ i ∈ cornerChoices, F (plaquetteAt y i) := by apply _root_.YangMills.DeltaSharedProofs.p501550 <;> assumption
end Corners
section Energies
variable {n : ℕ}
theorem plaquetteEnergyOf_nonneg (W : TorusField n) (p : TorusPlaquette n) : 0 ≤ plaquetteEnergyOf W p :=
  plaquetteEnergy_nonneg _ _ _ _
theorem plaquetteEnergyOf_le_two (W : TorusField n) (p : TorusPlaquette n) : plaquetteEnergyOf W p ≤ 2 := by apply _root_.YangMills.SharedProofs.p24501 <;> assumption
theorem plaquetteEnergyOf_trivialField (p : TorusPlaquette n) : plaquetteEnergyOf (trivialField n) p = 0 := by
  simp [plaquetteEnergyOf, plaquetteEnergy, holonomy_trivialField]
theorem siteResponse_eq_sum [NeZero n] (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) :
    siteResponse y W h =
      (1 / 4) * ∑ i ∈ cornerChoices, h (plaquetteAt y i) * plaquetteEnergyOf W (plaquetteAt y i) := by
  rw [← sum_vertexMultiplicity_mul y fun p => h p * plaquetteEnergyOf W p, siteResponse, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem blockMean_zero (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) :
    blockMean L 0 n y h = (1 / 24) * ∑ i ∈ cornerChoices, h (plaquetteAt y i) := by
  rw [← sum_vertexMultiplicity_mul y h]
  rfl
theorem siteResponse_trivialField [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) :
    siteResponse y (trivialField n) h = 0 := by
  simp [siteResponse, plaquetteEnergyOf_trivialField]
theorem siteResponse_linear [NeZero n] (y : TorusSite n) (W : TorusField n) (c : ℝ) (h h' : PlaquetteWeight n) :
    siteResponse y W (c • h + h') = c * siteResponse y W h + siteResponse y W h' := by
  simp only [siteResponse, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem lt_of_mem_cornerChoices {i : CornerChoice} (hi : i ∈ cornerChoices) : i.1 < i.2.1 :=
  (Finset.mem_filter.mp hi).2
theorem mem_plaquetteVertices_plaquetteAt (y : TorusSite n) (i : CornerChoice) :
    y ∈ plaquetteVertices (plaquetteAt y i).1 (plaquetteAt y i).2.1 (plaquetteAt y i).2.2 := by apply _root_.YangMills.DeltaSharedProofs.p1878 <;> assumption
theorem isPlaquetteAt_plaquetteAt (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) {i : CornerChoice}
    (hi : i ∈ cornerChoices) : IsPlaquetteAt L 0 y (plaquetteAt y i) :=
  ⟨lt_of_mem_cornerChoices hi, y, mem_plaquetteVertices_plaquetteAt y i, Finset.mem_singleton_self y⟩
theorem siteResponse_congr_weight (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (W : TorusField n)
    (h h' : PlaquetteWeight n) (hh : ∀ p, IsPlaquetteAt L 0 y p → h p = h' p) :
    siteResponse y W h = siteResponse y W h' := by
  rw [siteResponse_eq_sum, siteResponse_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun i hi =>
    congrArg (· * plaquetteEnergyOf W (plaquetteAt y i)) (hh _ (isPlaquetteAt_plaquetteAt L y hi))
end Energies
section Doubled
def barycentreOffset (i : CornerChoice) : Fin 4 → ℤ := fun j =>
  2 * baseOffset i j + (if j = i.1 then 1 else 0) + (if j = i.2.1 then 1 else 0)
set_option maxRecDepth 100000 in
theorem barycentreOffset_close : ∀ i ∈ cornerChoices, ∀ i' ∈ cornerChoices, ∀ j,
    -2 ≤ barycentreOffset i' j - barycentreOffset i j ∧ barycentreOffset i' j - barycentreOffset i j ≤ 2 := by
  decide
set_option maxRecDepth 100000 in
theorem barycentreOffset_injective : ∀ i ∈ cornerChoices, ∀ i' ∈ cornerChoices,
    (∀ j, barycentreOffset i j = barycentreOffset i' j) → i = i' := by decide
variable {n : ℕ}
theorem two_mul_val_add_cast [NeZero n] (u : ZMod n) (e : ℤ) :
    ((2 * (u + (e : ZMod n)).val : ℕ) : ZMod (2 * n)) =
      ((2 * u.val : ℕ) : ZMod (2 * n)) + ((2 * e : ℤ) : ZMod (2 * n)) := by
  have h1 : (((u + (e : ZMod n)).val : ℤ) : ZMod n) = (((u.val : ℤ) + e : ℤ) : ZMod n) := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have h2 : ((2 * (u + (e : ZMod n)).val : ℕ) : ℤ) =
      ((2 * u.val : ℕ) : ℤ) + 2 * e - ((2 * n : ℕ) : ℤ) * k := by
    push_cast
    linarith
  have h3 : ((2 * (u + (e : ZMod n)).val : ℕ) : ZMod (2 * n)) =
      (((2 * (u + (e : ZMod n)).val : ℕ) : ℤ) : ZMod (2 * n)) := by simp
  rw [h3, h2]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
def doubleSite (y : TorusSite n) : TorusSite (2 * n) := fun j => ((2 * (y j).val : ℕ) : ZMod (2 * n))
theorem doubledBarycentre_plaquetteAt [NeZero n] (y : TorusSite n) (i : CornerChoice) :
    doubledBarycentre (plaquetteAt y i) = doubleSite y + siteOfInt (barycentreOffset i) := by
  funext j
  have e : (plaquetteAt y i).1 j = y j + ((baseOffset i j : ℤ) : ZMod n) := rfl
  have e1 : (plaquetteAt y i).2.1 = i.1 := rfl
  have e2 : (plaquetteAt y i).2.2 = i.2.1 := rfl
  simp only [doubledBarycentre, doubleSite, Pi.add_apply, siteOfInt, barycentreOffset, e, e1, e2]
  rw [Nat.cast_add, Nat.cast_add, two_mul_val_add_cast]
  push_cast
  split_ifs <;> simp <;> ring
theorem eq_of_siteOfInt_eq_of_close {m : ℕ} (hm : 2 < m) {e e' : Fin 4 → ℤ}
    (h : ∀ j, -2 ≤ e' j - e j ∧ e' j - e j ≤ 2) (he : (siteOfInt e : TorusSite m) = siteOfInt e') :
    ∀ j, e j = e' j := by
  intro j
  have h1 : ((e j : ℤ) : ZMod m) = ((e' j : ℤ) : ZMod m) := congrFun he j
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have h3 : |e' j - e j| < (m : ℤ) := by
    rw [abs_lt]
    have := h j
    omega
  have := Int.eq_zero_of_abs_lt_dvd h2 h3
  omega
theorem abs_sub_le_weightLipschitz (L : ℕ) [NeZero n] (hn : 2 ≤ n) (y : TorusSite n) (h : PlaquetteWeight n)
    {i i' : CornerChoice} (hi : i ∈ cornerChoices) (hi' : i' ∈ cornerChoices) :
    |h (plaquetteAt y i) - h (plaquetteAt y i')| ≤ weightLipschitz L 0 h := by
  classical
  have : NeZero (2 * n) := ⟨by omega⟩
  have hlip : 0 ≤ weightLipschitz L 0 h := Real.iSup_nonneg fun pp => div_nonneg (abs_nonneg _) (by
    unfold barycentreDist
    positivity)
  by_cases hii : i = i'
  · subst hii
    simpa using hlip
  set p := plaquetteAt y i with hp
  set p' := plaquetteAt y i' with hp'
  have hd : doubledBarycentre p' =
      doubledBarycentre p + siteOfInt (barycentreOffset i' - barycentreOffset i) := by
    rw [hp, hp', doubledBarycentre_plaquetteAt, doubledBarycentre_plaquetteAt]
    have : (siteOfInt (barycentreOffset i') : TorusSite (2 * n)) =
        siteOfInt (barycentreOffset i) + siteOfInt (barycentreOffset i' - barycentreOffset i) := by
      rw [← siteOfInt_add]
      congr 1
      abel
    rw [this]
    abel
  have hclose := barycentreOffset_close i hi i' hi'
  have hle : supDist (doubledBarycentre p) (doubledBarycentre p') ≤ 2 := by
    rw [hd]
    refine supDist_add_siteOfInt_le _ _ 2 fun j => ?_
    have := hclose j
    simp only [Pi.sub_apply]
    omega
  have hpos : supDist (doubledBarycentre p) (doubledBarycentre p') ≠ 0 := by
    intro h0
    obtain ⟨e, he, hz⟩ := exists_offset_of_supDist (doubledBarycentre p) (doubledBarycentre p')
    have he0 : e = 0 := by
      funext j
      have := hz j
      rw [h0] at this
      simpa using this
    rw [he0] at he
    have h1 : (siteOfInt (barycentreOffset i) : TorusSite (2 * n)) = siteOfInt (barycentreOffset i') := by
      have h2 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (2 * n)) = 0 := by
        funext j
        simp [siteOfInt]
      rw [h2, add_zero, hp, hp', doubledBarycentre_plaquetteAt, doubledBarycentre_plaquetteAt] at he
      exact (add_left_cancel he).symm
    exact hii (barycentreOffset_injective i hi i' hi'
      (eq_of_siteOfInt_eq_of_close (by omega) hclose h1))
  have hbd : (0 : ℝ) < barycentreDist L 0 p p' ∧ barycentreDist L 0 p p' ≤ 1 := by
    unfold barycentreDist
    have h1 : (1 : ℝ) ≤ supDist (doubledBarycentre p) (doubledBarycentre p') := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos
    have h2 : (supDist (doubledBarycentre p) (doubledBarycentre p') : ℝ) ≤ 2 := by exact_mod_cast hle
    simp only [pow_zero, mul_one]
    constructor
    · positivity
    · linarith
  have hsup : |h p - h p'| / barycentreDist L 0 p p' ≤ weightLipschitz L 0 h := by
    have hb : BddAbove (Set.range fun pp : OrientedPlaquette n × OrientedPlaquette n =>
        |h pp.1.1 - h pp.2.1| / barycentreDist L 0 pp.1.1 pp.2.1) := (Set.finite_range _).bddAbove
    exact le_ciSup hb (⟨p, lt_of_mem_cornerChoices hi⟩, ⟨p', lt_of_mem_cornerChoices hi'⟩)
  refine le_trans ?_ hsup
  rw [le_div_iff₀ hbd.1]
  nlinarith [abs_nonneg (h p - h p'), hbd.2]
theorem abs_sub_blockMean_le (L : ℕ) [NeZero L] [NeZero n] (hn : 2 ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight n) {i : CornerChoice} (hi : i ∈ cornerChoices) :
    |h (plaquetteAt y i) - blockMean L 0 n y h| ≤ weightLipschitz L 0 h := by
  have e : h (plaquetteAt y i) - blockMean L 0 n y h =
      (1 / 24) * ∑ j ∈ cornerChoices, (h (plaquetteAt y i) - h (plaquetteAt y j)) := by
    rw [blockMean_zero, Finset.sum_sub_distrib, Finset.sum_const, card_cornerChoices]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)]
  have h1 : |∑ j ∈ cornerChoices, (h (plaquetteAt y i) - h (plaquetteAt y j))| ≤
      ∑ _j ∈ cornerChoices, weightLipschitz L 0 h :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => abs_sub_le_weightLipschitz L hn y h hi hj)
  rw [Finset.sum_const, card_cornerChoices] at h1
  simp only [nsmul_eq_mul] at h1
  push_cast at h1
  linarith
end Doubled
section Derivatives
variable {n : ℕ}
theorem mixedDeriv_sum {k : ℕ} {ι : Type} (s : Finset ι) (w : ι → ℝ) (F : ι → TorusField n → ℝ)
    (W : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions)
    (hF : ∀ i ∈ s, ContDiff ℝ ⊤ fun σ : Fin k → ℝ => F i (perturb c X σ W)) :
    mixedDeriv (fun W' => ∑ i ∈ s, w i * F i W') W c X = ∑ i ∈ s, w i * mixedDeriv (F i) W c X := by
  unfold mixedDeriv
  have e : (fun σ : Fin k → ℝ => ∑ i ∈ s, w i * F i (perturb c X σ W)) =
      ∑ i ∈ s, (w i • fun σ : Fin k → ℝ => F i (perturb c X σ W)) := by
    funext σ
    simp [Finset.sum_apply]
  have hs : ∀ i ∈ s, ContDiffAt ℝ k (w i • fun σ : Fin k → ℝ => F i (perturb c X σ W)) 0 := fun i hi =>
    (((hF i hi).const_smul (w i)).of_le le_top).contDiffAt
  rw [e, iteratedFDeriv_sum_apply hs, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iteratedFDeriv_const_smul_apply (((hF i hi).of_le le_top).contDiffAt)]
  simp [smul_eq_mul]
theorem mixedDeriv_zero_order {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : TorusField n → E)
    (W : TorusField n) (c : Fin 0 → TorusBond n) (X : Fin 0 → BlockAverages.imaginaryQuaternions) :
    mixedDeriv G W c X = G W := by
  unfold mixedDeriv
  rw [iteratedFDeriv_zero_apply, perturb_zero]
def PlaquetteEnergyBound (M : ℝ) : Prop :=
  ∀ (n k : ℕ) (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions),
    ContDiff ℝ ⊤ (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν) ∧
    (k ≤ 3 → BlockAverages.AreUnitVectors X →
      |mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X| ≤ M) ∧
    ∀ l, (∀ i, plaquetteEdges x μ ν i ≠ c l) →
      mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X = 0
def remainderCoeff (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n)
    (i : CornerChoice) : ℝ :=
  (1 / 4) * (h (plaquetteAt y i) - blockMean L 0 n y h)
theorem responseRemainder_eq (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) :
    responseRemainder (wilsonColdResponse L) n y h =
      fun W => ∑ i ∈ cornerChoices, remainderCoeff L y h i * plaquetteEnergyOf W (plaquetteAt y i) := by
  funext W
  show siteResponse y W h - blockMean L 0 n y h * siteResponse y W (constOneWeight _) = _
  simp only [siteResponse_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [remainderCoeff, constOneWeight]
  ring
theorem weightLipschitz_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightLipschitz L t h :=
  Real.iSup_nonneg fun pp => div_nonneg (abs_nonneg _) (by
    unfold barycentreDist
    positivity)
theorem abs_remainderCoeff_le (L : ℕ) [NeZero L] [NeZero n] (hn : 2 ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight n) {i : CornerChoice} (hi : i ∈ cornerChoices) :
    |remainderCoeff L y h i| ≤ weightLipschitz L 0 h / 4 := by
  have := abs_sub_blockMean_le L hn y h hi
  rw [remainderCoeff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  linarith
theorem responseRemainder_trivialField (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight n) : responseRemainder (wilsonColdResponse L) n y h (trivialField n) = 0 := by
  rw [responseRemainder_eq]
  simp [plaquetteEnergyOf_trivialField]
theorem centeredRemainder_eq (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) :
    centeredRemainder (wilsonColdResponse L) n y h = responseRemainder (wilsonColdResponse L) n y h := by
  funext W
  simp [centeredRemainder, responseRemainder_trivialField]
theorem responseRemainder_contDiffThreeAt {M : ℝ} (hE : PlaquetteEnergyBound M) (L : ℕ) [NeZero L]
    [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) (W : TorusField n) :
    ContDiffThreeAt (responseRemainder (wilsonColdResponse L) n y h) W := by
  intro k c X
  rw [responseRemainder_eq]
  exact (ContDiff.sum fun i _ => contDiff_const.mul
    (((hE n k W (plaquetteAt y i).1 i.1 i.2.1 c X).1).of_le le_top)).contDiffAt
def vertexOffset (i : CornerChoice) (s t : Bool) : Fin 4 → ℤ :=
  baseOffset i + (if s = true then coordVector i.1 else 0) + (if t = true then coordVector i.2.1 else 0)
set_option maxRecDepth 100000 in
theorem vertexOffset_close : ∀ i ∈ cornerChoices, ∀ (s t : Bool) (j : Fin 4),
    -1 ≤ vertexOffset i s t j ∧ vertexOffset i s t j ≤ 1 := by decide
theorem vertex_eq_add_siteOfInt [NeZero n] (y : TorusSite n) (i : CornerChoice) (s t : Bool) :
    (plaquetteAt y i).1 + (if s = true then unitStep n i.1 else 0) +
        (if t = true then unitStep n i.2.1 else 0) =
      y + siteOfInt (vertexOffset i s t) := by
  cases s <;> cases t <;>
    simp [vertexOffset, plaquetteAt, siteOfInt_add, siteOfInt_coordVector, add_assoc]
theorem supDist_edge_le_one [NeZero n] (y : TorusSite n) {i : CornerChoice} (hi : i ∈ cornerChoices)
    (j : Fin 4) : supDist y (plaquetteEdges (plaquetteAt y i).1 i.1 i.2.1 j).1 ≤ 1 := by
  have key : ∀ s t : Bool, supDist y ((plaquetteAt y i).1 + (if s = true then unitStep n i.1 else 0) +
      (if t = true then unitStep n i.2.1 else 0)) ≤ 1 := by
    intro s t
    rw [vertex_eq_add_siteOfInt]
    refine supDist_add_siteOfInt_le _ _ 1 fun k => ?_
    have := vertexOffset_close i hi s t k
    omega
  have h0 := key false false
  have h1 := key true false
  have h2 := key false true
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h0 h1 h2
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h0
theorem supportDiam_le_two [NeZero n] {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n)
    (h : ∀ l, supDist y (c l).1 ≤ 1) : supportDiam y c ≤ 2 := by
  unfold supportDiam
  refine max_le (Finset.sup_le fun l _ => (h l).trans (by norm_num)) (Finset.sup_le fun l _ =>
    Finset.sup_le fun l' _ => ?_)
  have h1 := supDist_triangle (c l).1 y (c l').1
  have h2 := h l
  have h3 := h l'
  rw [supDist_comm y (c l).1] at h2
  omega
theorem one_le_weight (ℓ : StepParameters) (hfit : ℓ.Admissible) (m : ℕ) : 1 ≤ ℓ.weight m := by
  unfold StepParameters.weight
  have h1 : (1 : ℝ) ≤ max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) := le_max_left _ _
  have h2 : (1 : ℝ) ≤ Real.exp (ℓ.weightRate * m) := by
    refine Real.one_le_exp (mul_nonneg ?_ (Nat.cast_nonneg m))
    have := hfit.rt_pos
    unfold StepParameters.weightRate
    positivity
  exact one_le_mul_of_one_le_of_one_le h1 h2
theorem weight_mono (ℓ : StepParameters) (hfit : ℓ.Admissible) {m m' : ℕ} (h : m ≤ m') :
    ℓ.weight m ≤ ℓ.weight m' := by apply _root_.YangMills.SharedProofs.p24433 <;> assumption
theorem weight_zero (ℓ : StepParameters) : ℓ.weight 0 = 1 := by apply _root_.YangMills.Construction.TorusLumps.StepParameters.weight_zero <;> assumption
theorem abs_mixedDeriv_responseRemainder_le {M : ℝ} (hM0 : 0 ≤ M) (hE : PlaquetteEnergyBound M)
    (ℓ : StepParameters) (hfit : ℓ.Admissible) [NeZero n] (hn : 2 ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight n) (W : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (hk : k ≤ 3) (hX : BlockAverages.AreUnitVectors X)
    {A : ℝ} (hA : 6 * M * ℓ.weight 2 ≤ A) :
    |mixedDeriv (responseRemainder (wilsonColdResponse ℓ.side) n y h) W c X| ≤
      A * weightLipschitz ℓ.side 0 h / ℓ.weight (supportDiam y c) := by
  have hlip := weightLipschitz_nonneg ℓ.side 0 h
  have hG : 0 < ℓ.weight (supportDiam y c) := lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)
  have hG2 : 1 ≤ ℓ.weight 2 := one_le_weight ℓ hfit _
  have hA0 : 0 ≤ A := le_trans (mul_nonneg (mul_nonneg (by norm_num) hM0) (le_trans zero_le_one hG2)) hA
  have hsum : mixedDeriv (responseRemainder (wilsonColdResponse ℓ.side) n y h) W c X =
      ∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i *
        mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAt y i)) W c X := by
    rw [responseRemainder_eq]
    exact mixedDeriv_sum _ _ (fun i W' => plaquetteEnergyOf W' (plaquetteAt y i)) W c X
      fun i _ => (hE n k W (plaquetteAt y i).1 i.1 i.2.1 c X).1
  rw [hsum]
  by_cases hall : ∃ i ∈ cornerChoices, ∀ l, ∃ j, plaquetteEdges (plaquetteAt y i).1 i.1 i.2.1 j = c l
  · obtain ⟨i₀, hi₀, hc⟩ := hall
    have hnear : ∀ l, supDist y (c l).1 ≤ 1 := fun l => by
      obtain ⟨j, hj⟩ := hc l
      rw [← hj]
      exact supDist_edge_le_one y hi₀ j
    have hspan := supportDiam_le_two y c hnear
    have hb : |∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i *
        mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAt y i)) W c X| ≤
          6 * M * weightLipschitz ℓ.side 0 h := by
      calc _ ≤ ∑ i ∈ cornerChoices, |remainderCoeff ℓ.side y h i *
              mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAt y i)) W c X| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ cornerChoices, weightLipschitz ℓ.side 0 h / 4 * M := Finset.sum_le_sum fun i hi => by
              rw [abs_mul]
              exact mul_le_mul (abs_remainderCoeff_le ℓ.side hn y h hi)
                ((hE n k W (plaquetteAt y i).1 i.1 i.2.1 c X).2.1 hk hX) (abs_nonneg _) (by positivity)
        _ = 6 * M * weightLipschitz ℓ.side 0 h := by
              rw [Finset.sum_const, card_cornerChoices]
              simp only [nsmul_eq_mul]
              push_cast
              ring
    refine hb.trans ?_
    rw [le_div_iff₀ hG]
    have h3 : ℓ.weight (supportDiam y c) ≤ ℓ.weight 2 := weight_mono ℓ hfit hspan
    calc 6 * M * weightLipschitz ℓ.side 0 h * ℓ.weight (supportDiam y c)
        = 6 * M * ℓ.weight (supportDiam y c) * weightLipschitz ℓ.side 0 h := by ring
      _ ≤ A * weightLipschitz ℓ.side 0 h := mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left h3 (by positivity)).trans hA) hlip
  · push Not at hall
    have h0 : ∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i *
        mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAt y i)) W c X = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨l, hl⟩ := hall i hi
      have := (hE n k W (plaquetteAt y i).1 i.1 i.2.1 c X).2.2 l hl
      have e : mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAt y i)) W c X = 0 := this
      rw [e, mul_zero]
    rw [h0, abs_zero]
    exact div_nonneg (mul_nonneg hA0 hlip) hG.le
theorem vertexOffset_add_first (i : CornerChoice) (t : Bool) :
    vertexOffset i false t + Pi.single i.1 1 = vertexOffset i true t := by
  funext j
  cases t <;> by_cases h1 : j = i.1 <;>
    simp [vertexOffset, coordVector, h1] <;> ring
theorem vertexOffset_add_second (i : CornerChoice) (s : Bool) :
    vertexOffset i s false + Pi.single i.2.1 1 = vertexOffset i s true := by
  funext j
  cases s <;> by_cases h1 : j = i.2.1 <;>
    simp [vertexOffset, coordVector, h1]
theorem plaquetteEnergyOf_eq_of_fieldsAgree [NeZero n] {n' : ℕ} [NeZero n'] {W : TorusField n}
    {W' : TorusField n'} {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} (hm : 1 ≤ m)
    (hA : FieldsAgreeNear W W' y y' m) {i : CornerChoice} (hi : i ∈ cornerChoices) :
    plaquetteEnergyOf W (plaquetteAt y i) = plaquetteEnergyOf W' (plaquetteAt y' i) := by
  have hbox : ∀ s t, OffsetInBox m (vertexOffset i s t) := by
    intro s t j
    have := vertexOffset_close i hi s t j
    rw [abs_le]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    omega
  have b1 := hA (vertexOffset i false false, i.1) ⟨hbox _ _, by
    show OffsetInBox m (vertexOffset i false false + Pi.single i.1 1)
    rw [vertexOffset_add_first]
    exact hbox _ _⟩
  have b2 := hA (vertexOffset i true false, i.2.1) ⟨hbox _ _, by
    show OffsetInBox m (vertexOffset i true false + Pi.single i.2.1 1)
    rw [vertexOffset_add_second]
    exact hbox _ _⟩
  have b3 := hA (vertexOffset i false true, i.1) ⟨hbox _ _, by
    show OffsetInBox m (vertexOffset i false true + Pi.single i.1 1)
    rw [vertexOffset_add_first]
    exact hbox _ _⟩
  have b4 := hA (vertexOffset i false false, i.2.1) ⟨hbox _ _, by
    show OffsetInBox m (vertexOffset i false false + Pi.single i.2.1 1)
    rw [vertexOffset_add_second]
    exact hbox _ _⟩
  simp only [bondFrom, ← vertex_eq_add_siteOfInt, Bool.false_eq_true, ↓reduceIte, add_zero] at b1 b2 b3 b4
  show plaquetteEnergy W (plaquetteAt y i).1 i.1 i.2.1 = plaquetteEnergy W' (plaquetteAt y' i).1 i.1 i.2.1
  unfold plaquetteEnergy holonomy
  rw [b1, b2, b3, b4]
theorem fieldsAgreeNear_perturb {k : ℕ} {W W' : TorusField n} {y : TorusSite n} {m : ℕ}
    (hA : FieldsAgreeNear W W' y y m) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) :
    FieldsAgreeNear (perturb c X σ W) (perturb c X σ W') y y m := by
  intro b hb
  show BlockAverages.expUnit _ * W _ _ = BlockAverages.expUnit _ * W' _ _
  rw [hA b hb]
theorem abs_mixedDeriv_centeredRemainder_sub_le (ℓ : StepParameters) (hfit : ℓ.Admissible) [NeZero n]
    (hn : 2 ≤ n) (y : TorusSite n) (W W' : TorusField n) (m : ℕ) (hA : FieldsAgreeNear W W' y y m)
    (h : PlaquetteWeight n) {k : ℕ} (b : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (hb : ∀ l, BondOffsetInBox m (b l)) {A : ℝ}
    (hA12 : 12 ≤ A) :
    |mixedDeriv (centeredRemainder (wilsonColdResponse ℓ.side) n y h) W (fun l => bondFrom y (b l)) X -
        mixedDeriv (centeredRemainder (wilsonColdResponse ℓ.side) n y h) W' (fun l => bondFrom y (b l)) X| ≤
      A * weightLipschitz ℓ.side 0 h / ℓ.weight m := by
  have hlip := weightLipschitz_nonneg ℓ.side 0 h
  have hG : 0 < ℓ.weight m := lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)
  rw [centeredRemainder_eq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hk : k = 0 := by
      by_contra hk
      have l : Fin k := ⟨0, by omega⟩
      obtain ⟨h1, h2⟩ := hb l
      have a1 := h1 (b l).2
      have a2 := h2 (b l).2
      simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_zero] at a1 a2
      have e1 := abs_nonpos_iff.mp a1
      have e2 := abs_nonpos_iff.mp a2
      omega
    subst hk
    rw [mixedDeriv_zero_order, mixedDeriv_zero_order, responseRemainder_eq, weight_zero, div_one]
    have e : ∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i * plaquetteEnergyOf W (plaquetteAt y i) -
        ∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i * plaquetteEnergyOf W' (plaquetteAt y i) =
        ∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i *
          (plaquetteEnergyOf W (plaquetteAt y i) - plaquetteEnergyOf W' (plaquetteAt y i)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    show |∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i * plaquetteEnergyOf W (plaquetteAt y i) -
        ∑ i ∈ cornerChoices, remainderCoeff ℓ.side y h i * plaquetteEnergyOf W' (plaquetteAt y i)| ≤ _
    rw [e]
    calc _ ≤ ∑ i ∈ cornerChoices, |remainderCoeff ℓ.side y h i *
            (plaquetteEnergyOf W (plaquetteAt y i) - plaquetteEnergyOf W' (plaquetteAt y i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ cornerChoices, weightLipschitz ℓ.side 0 h / 4 * 2 := Finset.sum_le_sum fun i hi => by
          rw [abs_mul]
          refine mul_le_mul (abs_remainderCoeff_le ℓ.side hn y h hi) ?_ (abs_nonneg _) (by positivity)
          rw [abs_le]
          have a1 := plaquetteEnergyOf_nonneg W (plaquetteAt y i)
          have a2 := plaquetteEnergyOf_le_two W (plaquetteAt y i)
          have a3 := plaquetteEnergyOf_nonneg W' (plaquetteAt y i)
          have a4 := plaquetteEnergyOf_le_two W' (plaquetteAt y i)
          constructor <;> linarith
      _ = 12 * weightLipschitz ℓ.side 0 h := by
          rw [Finset.sum_const, card_cornerChoices]
          simp only [nsmul_eq_mul]
          push_cast
          ring
      _ ≤ A * weightLipschitz ℓ.side 0 h := mul_le_mul_of_nonneg_right hA12 hlip
  · have e : mixedDeriv (responseRemainder (wilsonColdResponse ℓ.side) n y h) W (fun l => bondFrom y (b l)) X =
        mixedDeriv (responseRemainder (wilsonColdResponse ℓ.side) n y h) W' (fun l => bondFrom y (b l)) X := by
      unfold mixedDeriv
      congr 1
      congr 1
      funext σ
      rw [responseRemainder_eq]
      exact Finset.sum_congr rfl fun i hi => by
        rw [plaquetteEnergyOf_eq_of_fieldsAgree hm (fieldsAgreeNear_perturb hA _ _ σ) hi]
    rw [e, sub_self, abs_zero]
    exact div_nonneg (mul_nonneg (by linarith) hlip) hG.le
end Derivatives
section Sizes
variable {n : ℕ}
theorem weightSup_nonneg {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightSup h :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  (weightSup_nonneg h).trans (le_max_left _ _)
theorem abs_le_weightSup [NeZero n] (h : PlaquetteWeight n) (p : OrientedPlaquette n) :
    |h p.1| ≤ weightSup h := by
  have hb : BddAbove (Set.range fun p : OrientedPlaquette n => |h p.1|) := (Set.finite_range _).bddAbove
  exact le_ciSup hb p
theorem abs_siteResponse_le [NeZero n] (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) :
    |siteResponse y W h| ≤ 12 * weightSup h := by
  have hs := weightSup_nonneg h
  rw [siteResponse_eq_sum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have h1 : |∑ i ∈ cornerChoices, h (plaquetteAt y i) * plaquetteEnergyOf W (plaquetteAt y i)| ≤
      ∑ _i ∈ cornerChoices, weightSup h * 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul, abs_of_nonneg (plaquetteEnergyOf_nonneg W _)]
    exact mul_le_mul (abs_le_weightSup h ⟨plaquetteAt y i, lt_of_mem_cornerChoices hi⟩)
      (plaquetteEnergyOf_le_two W _) (plaquetteEnergyOf_nonneg W _) hs
  rw [Finset.sum_const, card_cornerChoices] at h1
  simp only [nsmul_eq_mul] at h1
  push_cast at h1
  linarith
theorem fineCentre_zero (L : ℕ) [NeZero n] (y : TorusSite n) : (fineCentre L 0 y : TorusSite n) = y := by
  funext j
  show (((L : ℤ) ^ 0 * ((y j).cast : ℤ) : ℤ) : ZMod n) = y j
  simp
theorem fineTranslate_zero (L n : ℕ) (v : Fin 4 → ℤ) : (fineTranslate L 0 n v : TorusSite n) = siteOfInt v := by
  funext j
  show (((L : ℤ) ^ 0 * v j : ℤ) : ZMod n) = ((v j : ℤ) : ZMod n)
  simp
theorem siteResponse_eq_of_agree (L : ℕ) [NeZero L] {n' : ℕ} [NeZero n] [NeZero n'] {W : TorusField n}
    {W' : TorusField n'} {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} (hm : 1 ≤ m)
    (hA : FieldsAgreeNear W W' y y' m) {h : PlaquetteWeight n} {h' : PlaquetteWeight n'}
    (hh : WeightsAgreeAt L 0 y y' h h') : siteResponse y W h = siteResponse y' W' h' := by
  rw [siteResponse_eq_sum, siteResponse_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [plaquetteEnergyOf_eq_of_fieldsAgree hm hA hi]
  have hb : ∀ j, |baseOffset i j| ≤ (L : ℤ) ^ 0 := by
    intro j
    have hne : i.1 ≠ i.2.1 := ne_of_lt (Finset.mem_filter.mp hi).2
    simp only [pow_zero, baseOffset]
    split_ifs with h1 h2 h2
    · exact absurd (h1.2.symm.trans h2.2) hne
    all_goals simp
  have h1 := hh (baseOffset i) i.1 i.2.1 hb (by
    rw [ResponseInTheExpansion.fineCentre_zero]
    exact isPlaquetteAt_plaquetteAt L y hi)
  have e1 : h (plaquetteAt y i) = h (fineCentre L 0 y + siteOfInt (baseOffset i), i.1, i.2.1) := by
    rw [ResponseInTheExpansion.fineCentre_zero]
    rfl
  have e2 : h' (plaquetteAt y' i) = h' (fineCentre L 0 y' + siteOfInt (baseOffset i), i.1, i.2.1) := by
    rw [ResponseInTheExpansion.fineCentre_zero]
    rfl
  rw [e1, e2]
  exact congrArg (· * plaquetteEnergyOf W' (plaquetteAt y' i)) h1
theorem siteResponse_translate [NeZero n] (u y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) :
    siteResponse y (TorusFields.translate u W) (translateWeight u h) = siteResponse (y + u) W h := by
  rw [siteResponse_eq_sum, siteResponse_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ((plaquetteAt y i).1 + u, (plaquetteAt y i).2) = plaquetteAt (y + u) i := by
    simp only [plaquetteAt]
    congr 1
    abel
  have e2 : plaquetteEnergyOf (TorusFields.translate u W) (plaquetteAt y i) =
      plaquetteEnergyOf W (plaquetteAt (y + u) i) := by
    rw [← e]
    exact plaquetteEnergy_translate u W (plaquetteAt y i).1 (plaquetteAt y i).2.1 (plaquetteAt y i).2.2
  rw [e2]
  show h ((plaquetteAt y i).1 + u, (plaquetteAt y i).2) * _ = _
  rw [e]
end Sizes
section Carried
variable {n : ℕ}
theorem perm_swap_pairs {α : Type} (p q r s : α) : [p, q, r, s].Perm [r, s, p, q] := by
  classical
  refine List.perm_iff_count.mpr fun z => ?_
  simp only [List.count_cons, List.count_nil]
  ring
theorem perm_swap_within {α : Type} (p q r s : α) : [p, q, r, s].Perm [q, p, s, r] := by
  classical
  refine List.perm_iff_count.mpr fun z => ?_
  simp only [List.count_cons, List.count_nil]
  ring
theorem perm_reverse_four {α : Type} (p q r s : α) : [p, q, r, s].Perm [s, r, q, p] := by
  classical
  refine List.perm_iff_count.mpr fun z => ?_
  simp only [List.count_cons, List.count_nil]
  ring
theorem perm_swap_middle {α : Type} (p q r s : α) : [p, q, r, s].Perm [p, r, q, s] := by
  classical
  refine List.perm_iff_count.mpr fun z => ?_
  simp only [List.count_cons, List.count_nil]
  ring
theorem list_four_congr {α : Type} {a b c d a' b' c' d' : α} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : [a, b, c, d] = [a', b', c', d'] := by
  rw [h1, h2, h3, h4]
theorem plaquetteVertices_perm_map (g : TorusIsometry) (x : TorusSite n) (μ ν : Fin 4) :
    (plaquetteVertices (g.imageCorner x μ ν) (g.imageAxis μ) (g.imageAxis ν)).Perm
      ((plaquetteVertices x μ ν).map g.mapSite) := by
  set A := unitStep n (g.imageAxis μ) with hA
  set B := unitStep n (g.imageAxis ν) with hB
  set z := g.mapSite x with hz
  simp only [plaquetteVertices, List.map_cons, List.map_nil]
  rcases g.axisSign_unit (g.imageAxis μ) with sa | sa <;> rcases g.axisSign_unit (g.imageAxis ν) with sb | sb
  · have hbase : g.imageCorner x μ ν = z := by simp [TorusIsometry.imageCorner, sa, sb, hz]
    rw [hbase, mapSite_add_unitStep_of_pos g (x + unitStep n μ) ν sb, mapSite_add_unitStep_of_pos g x μ sa,
      mapSite_add_unitStep_of_pos g x ν sb, ← hA, ← hB, ← hz]
  · have hbase : g.imageCorner x μ ν = z - B := by simp [TorusIsometry.imageCorner, sa, sb, hz, hB]
    rw [hbase, mapSite_add_unitStep_of_neg g (x + unitStep n μ) ν sb, mapSite_add_unitStep_of_pos g x μ sa,
      mapSite_add_unitStep_of_neg g x ν sb, ← hA, ← hB, ← hz]
    have e : [z, z + A, z - B, z + A - B] = [z - B + B, z - B + A + B, z - B, z - B + A] := by
      exact list_four_congr (by abel) (by abel) rfl (by abel)
    rw [e]
    exact perm_swap_pairs _ _ _ _
  · have hbase : g.imageCorner x μ ν = z - A := by simp [TorusIsometry.imageCorner, sa, sb, hz, hA]
    rw [hbase, mapSite_add_unitStep_of_pos g (x + unitStep n μ) ν sb, mapSite_add_unitStep_of_neg g x μ sa,
      mapSite_add_unitStep_of_pos g x ν sb, ← hA, ← hB, ← hz]
    have e : [z, z - A, z + B, z - A + B] = [z - A + A, z - A, z - A + A + B, z - A + B] := by
      exact list_four_congr (by abel) rfl (by abel) rfl
    rw [e]
    exact perm_swap_within _ _ _ _
  · have hbase : g.imageCorner x μ ν = z - A - B := by
      simp [TorusIsometry.imageCorner, sa, sb, hz, hA, hB]
    rw [hbase, mapSite_add_unitStep_of_neg g (x + unitStep n μ) ν sb, mapSite_add_unitStep_of_neg g x μ sa,
      mapSite_add_unitStep_of_neg g x ν sb, ← hA, ← hB, ← hz]
    have e : [z, z - A, z - B, z - A - B] =
        [z - A - B + A + B, z - A - B + B, z - A - B + A, z - A - B] := by
      exact list_four_congr (by abel) (by abel) (by abel) rfl
    rw [e]
    exact perm_reverse_four _ _ _ _
theorem plaquetteVertices_perm_swap (x : TorusSite n) (a b : Fin 4) :
    (plaquetteVertices x b a).Perm (plaquetteVertices x a b) := by
  have e : plaquetteVertices x a b = [x, x + unitStep n a, x + unitStep n b, x + unitStep n b + unitStep n a] := by
    exact list_four_congr rfl rfl rfl (by abel)
  rw [e]
  exact perm_swap_middle x (x + unitStep n b) (x + unitStep n a) (x + unitStep n b + unitStep n a)
theorem vertexMultiplicity_mapPlaquette (g : TorusIsometry) [NeZero n] (y : TorusSite n) (p : TorusPlaquette n) :
    vertexMultiplicity (g.mapSite y) (g.mapPlaquette p) = vertexMultiplicity y p := by
  classical
  obtain ⟨x, μ, ν⟩ := p
  have hperm : (plaquetteVertices (g.mapPlaquette (x, μ, ν)).1 (g.mapPlaquette (x, μ, ν)).2.1
      (g.mapPlaquette (x, μ, ν)).2.2).Perm ((plaquetteVertices x μ ν).map g.mapSite) := by
    unfold TorusIsometry.mapPlaquette
    simp only
    split_ifs
    · exact plaquetteVertices_perm_map g x μ ν
    · exact (plaquetteVertices_perm_swap _ _ _).trans (plaquetteVertices_perm_map g x μ ν)
  unfold vertexMultiplicity
  rw [hperm.count_eq, List.count_map_of_injective _ _ (mapSite_injective g)]
theorem plaquetteEnergyOf_mapPlaquette {g : TorusIsometry} {W W' : TorusField n} (hc : g.Transports W W')
    (p : TorusPlaquette n) : plaquetteEnergyOf W' (g.mapPlaquette p) = plaquetteEnergyOf W p := by
  obtain ⟨x, μ, ν⟩ := p
  have h1 := plaquetteEnergy_of_transports hc x μ ν
  unfold TorusIsometry.mapPlaquette plaquetteEnergyOf
  simp only
  split_ifs
  · exact h1.symm
  · exact (plaquetteEnergy_symm _ _ _ _).trans h1.symm
theorem siteResponse_constOne_of_transports {g : TorusIsometry} [NeZero n] {W W' : TorusField n}
    (hc : g.Transports W W') (y : TorusSite n) :
    siteResponse (g.mapSite y) W' (constOneWeight n) = siteResponse y W (constOneWeight n) := by
  classical
  have hne : ∀ {μ ν : Fin 4}, μ < ν → g.imageAxis μ ≠ g.imageAxis ν := by
    intro μ ν hlt he
    exact hlt.ne (g.axisPerm.symm.injective he)
  have hmem : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      g.mapPlaquette p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
    intro p hp
    have hlt := (mem_plaquettesIn_iff_forall_vertex.mp hp).1
    refine mem_plaquettesIn_iff_forall_vertex.mpr ⟨?_, fun _ _ => Finset.mem_univ _⟩
    unfold TorusIsometry.mapPlaquette
    split_ifs with hd
    · exact hd
    · exact lt_of_le_of_ne (not_lt.mp hd) (hne hlt).symm
  have hinj : Set.InjOn (g.mapPlaquette (n := n)) (plaquettesIn (Finset.univ : Finset (TorusSite n))) := by
    rintro ⟨x, μ, ν⟩ hp ⟨x', μ', ν'⟩ hp' he
    have hlt : μ < ν := (mem_plaquettesIn_iff_forall_vertex.mp hp).1
    have hlt' : μ' < ν' := (mem_plaquettesIn_iff_forall_vertex.mp hp').1
    have hplane : (μ = μ' ∧ ν = ν') := by
      have hinjd := g.axisPerm.symm.injective
      unfold TorusIsometry.mapPlaquette at he
      simp only at he
      split_ifs at he with h1 h2 h2
      · simp only [Prod.mk.injEq] at he
        exact ⟨hinjd he.2.1, hinjd he.2.2⟩
      · simp only [Prod.mk.injEq] at he
        have e1 := hinjd he.2.1
        have e2 := hinjd he.2.2
        omega
      · simp only [Prod.mk.injEq] at he
        have e1 := hinjd he.2.1
        have e2 := hinjd he.2.2
        omega
      · simp only [Prod.mk.injEq] at he
        exact ⟨hinjd he.2.2, hinjd he.2.1⟩
    obtain ⟨rfl, rfl⟩ := hplane
    have hb : g.imageCorner x μ ν = g.imageCorner x' μ ν := by
      unfold TorusIsometry.mapPlaquette at he
      simp only at he
      split_ifs at he <;> exact (Prod.mk.inj he).1
    have hx : x = x' := by
      apply mapSite_injective g
      unfold TorusIsometry.imageCorner at hb
      simpa using hb
    rw [hx]
  have himg : (plaquettesIn (Finset.univ : Finset (TorusSite n))).image (g.mapPlaquette (n := n)) =
      plaquettesIn (Finset.univ : Finset (TorusSite n)) :=
    Finset.eq_of_subset_of_card_le
      (Finset.image_subset_iff.mpr hmem) (by rw [Finset.card_image_of_injOn hinj])
  unfold siteResponse
  conv_lhs => rw [← himg]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vertexMultiplicity_mapPlaquette, plaquetteEnergyOf_mapPlaquette hc]
  rfl
end Carried
section Assembly
variable {ℓ : StepParameters} {β : ℝ} {Λ : LabelSpace} {f : LocalDensity}
  {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ} {n : ℕ} [NeZero n]
theorem wilsonWeight_eq (W : TorusField n) :
    wilsonWeight β n W = Real.exp (-β * wilsonAction Finset.univ W) := by
  simp [wilsonWeight, NeZero.ne n]
theorem hullDensity_measurable (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ)
    (hb : IsBlockTorusSide ℓ n) {W : TorusField n} {Y : Finset (TorusSite n)}
    (hY : IsHullState ℓ (clusterRange β) W Y) : Measurable fun ω : Y → Λ.Ω => Dq n W Y ω := by
  classical
  have h1 := (hull.borel n hb Y).1
  have h2 := h1.comp (measurable_prodMk_left (x := W))
  simpa [Function.comp_def, hY] using h2
theorem lintegral_hullDensity_ne_top (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ)
    (hb : IsBlockTorusSide ℓ n) {W : TorusField n} {Y : Finset (TorusSite n)}
    (hY : IsHullState ℓ (clusterRange β) W Y) :
    ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ) ≠ ⊤ := by
  classical
  have hs := hull.sum n hb W
  have hmem : Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange β) W) := by simp [hY]
  have h1 := Finset.single_le_sum (f := fun Y : Finset (TorusSite n) =>
    ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)) (fun _ _ => zero_le) hmem
  rw [hs] at h1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
theorem hullDensity_integrable (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ)
    (hb : IsBlockTorusSide ℓ n) {W : TorusField n} {Y : Finset (TorusSite n)}
    (hY : IsHullState ℓ (clusterRange β) W Y) :
    Integrable (fun ω : Y → Λ.Ω => Dq n W Y ω) (Measure.pi fun _ : Y => Λ.μ) := by
  refine ⟨(hullDensity_measurable hull hb hY).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => hull.nonneg n hb W Y ω hY)]
  exact lt_top_iff_ne_top.mpr (lintegral_hullDensity_ne_top hull hb hY)
theorem sum_integral_hullDensity (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ)
    (hb : IsBlockTorusSide ℓ n) (W : TorusField n) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange β) W),
      ∫ ω, Dq n W Y ω ∂(Measure.pi fun _ : Y => Λ.μ)) = wilsonWeight β n W := by
  classical
  have hD : 0 ≤ wilsonWeight β n W := by
    rw [ResponseInTheExpansion.wilsonWeight_eq]
    exact (Real.exp_pos _).le
  have e : ∀ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange β) W),
      ∫ ω, Dq n W Y ω ∂(Measure.pi fun _ : Y => Λ.μ) =
        (∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)).toReal := by
    intro Y hY
    have hY' := (Finset.mem_filter.mp hY).2
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => hull.nonneg n hb W Y ω hY')
      (hullDensity_measurable hull hb hY').aestronglyMeasurable
  rw [Finset.sum_congr rfl e, ← ENNReal.toReal_sum fun Y hY =>
      lintegral_hullDensity_ne_top hull hb (Finset.mem_filter.mp hY).2,
    hull.sum n hb W, ENNReal.toReal_ofReal hD]
theorem responseMass_eq (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ)
    (hb : IsBlockTorusSide ℓ n) (y : TorusSite n) (W : TorusField n) :
    responseMass ℓ 0 β Λ Dq (wilsonHullResponse ℓ.side Λ.Ω) n y W =
      siteResponse y W (constOneWeight n) * wilsonWeight β n W := by
  classical
  unfold responseMass
  rw [← sum_integral_hullDensity hull hb W, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  exact integral_const_mul _ _
theorem measurable_siteResponse (y : TorusSite n) (h : PlaquetteWeight n) :
    Measurable fun W : TorusField n => siteResponse y W h := by
  unfold siteResponse
  exact (continuous_finsetSum _ fun p _ => continuous_const.mul
    (continuous_const.mul (continuous_plaquetteEnergy p.1 p.2.1 p.2.2))).measurable
theorem measurableSet_isCold (s : ℝ) : MeasurableSet {W : TorusField n | IsCold s W} := by
  have e : {W : TorusField n | IsCold s W} =
      ⋂ (x : TorusSite n) (μ : Fin 4) (ν : Fin 4) (_ : μ < ν), {W : TorusField n | curvature W x μ ν < s} := by
    ext W
    simp [IsCold]
  rw [e]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun μ => MeasurableSet.iInter fun ν =>
    MeasurableSet.iInter fun _ => measurableSet_lt (continuous_curvature x μ ν).measurable measurable_const
theorem siteResponse_gaugeTransform (y : TorusSite n) (g : TorusSite n → BlockAverages.UnitQuaternion)
    (W : TorusField n) (h : PlaquetteWeight n) :
    siteResponse y (_root_.YangMills.Construction.TorusFields.gaugeTransform g W) h = siteResponse y W h := by
  simp [siteResponse, plaquetteEnergyOf, _root_.YangMills.Construction.TorusFields.plaquetteEnergy_gaugeTransform]
theorem siteResponse_translate_siteOfInt (L : ℕ) (v : Fin 4 → ℤ) (y : TorusSite n) (W : TorusField n)
    (h : PlaquetteWeight n) :
    siteResponse y (TorusFields.translate (siteOfInt v) W) (translateWeight (fineTranslate L 0 n v) h) =
      siteResponse (y + siteOfInt v) W h := by
  have e : (fineTranslate L 0 n v : TorusSite n) = siteOfInt v := ResponseInTheExpansion.fineTranslate_zero L n v
  have e2 : (translateWeight (fineTranslate L 0 n v) h : PlaquetteWeight n) = translateWeight (siteOfInt v) h := by
    funext p
    have e3 : ∀ u : TorusSite n, u = siteOfInt v → h (p.1 + u, p.2) = h (p.1 + siteOfInt v, p.2) :=
      fun u hu => by rw [hu]
    exact e3 _ e
  rw [e2]
  exact siteResponse_translate _ y W h
theorem sum_vertexMultiplicity (p : TorusPlaquette n) : ∑ y : TorusSite n, vertexMultiplicity y p = 4 := by
  classical
  simp only [vertexMultiplicity, plaquetteVertices, List.count_cons, List.count_nil, beq_iff_eq]
  push_cast
  simp only [zero_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  norm_num
theorem sum_siteResponse_constOne (W : TorusField n) :
    ∑ y : TorusSite n, siteResponse y W (constOneWeight n) = wilsonAction Finset.univ W := by
  unfold siteResponse wilsonAction
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [constOneWeight, one_mul, plaquetteEnergyOf]
  rw [← Finset.sum_mul, ← Finset.sum_div, sum_vertexMultiplicity]
  norm_num
theorem centered_zero (m : ℕ) [NeZero m] (y : TorusSite m) (W : TorusField m) :
    centered (fun _ _ _ => 0) m y W = 0 := by
  simp [centered]
theorem mixedDeriv_zero_fun {m k : ℕ} (W : TorusField m) (c : Fin k → TorusBond m)
    (X : Fin k → BlockAverages.imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField m => (0 : ℝ)) W c X = 0 := by apply _root_.YangMills.Construction.WilsonExpansion.mixedDeriv_zero <;> assumption
theorem coldDensityBounds_zero (hfit : ℓ.Admissible) {E E₃ : ℝ} (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) :
    ColdDensityBounds ℓ E E₃ (fun _ _ _ => 0) where
  smooth := fun n _ _ y W _ k c X => contDiffAt_const
  gauge := fun _ _ _ _ _ _ _ => rfl
  translation := fun _ _ _ _ _ _ _ => rfl
  decay := fun n _ _ y W _ k c X _ _ _ => by
    rw [ResponseInTheExpansion.mixedDeriv_zero_fun, abs_zero]
    have h1 : 0 < ℓ.weight (supportDiam y c) := lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)
    split_ifs
    · exact div_nonneg hE₃ h1.le
    · exact div_nonneg hE h1.le
  local_density := fun n n' _ _ _ _ y y' W W' m _ _ _ _ _ k h X _ _ _ => by
    have e : centered (fun _ _ _ => (0 : ℝ)) = fun _ _ _ => 0 := by
      funext a b c
      simp [centered]
    rw [e]
    simp only [ResponseInTheExpansion.mixedDeriv_zero_fun, sub_zero, abs_zero]
    exact div_nonneg hE (lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)).le
  no_curvature_term := fun A A' _ _ => by
    have h0 : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : BlockAverages.imaginaryQuaternions),
        secondDerivLimit (fun _ _ _ => 0) c c' X X' = 0 := by
      intro c c' X X'
      unfold secondDerivLimit
      simp only [ResponseInTheExpansion.mixedDeriv_zero_fun]
      exact (tendsto_const_nhds).limUnder_eq
    simp [h0]
omit [NeZero n] in
theorem siteScore_zero {Ω : Type} (Y : Finset (TorusSite n)) (ω : Y → Ω) (y : TorusSite n) :
    siteScore (fun _ : Ω => (0 : ℝ)) Y ω y = 0 := by
  unfold siteScore
  split_ifs <;> rfl
theorem abs_centered_siteResponse_sub_le (L : ℕ) [NeZero L] {n' : ℕ} [NeZero n'] {W : TorusField n}
    {W' : TorusField n'} {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} (hm : 1 ≤ m)
    (hA : FieldsAgreeNear W W' y y' m) {h : PlaquetteWeight n} {h' : PlaquetteWeight n'}
    (hh : WeightsAgreeAt L 0 y y' h h') (R : ℝ) (hR : 0 ≤ R) :
    |(siteResponse y W h - siteResponse y (trivialField n) h) -
      (siteResponse y' W' h' - siteResponse y' (trivialField n') h')| ≤ R := by
  rw [siteResponse_trivialField, siteResponse_trivialField, siteResponse_eq_of_agree L hm hA hh, sub_self,
    abs_zero]
  exact hR
theorem abs_siteResponse_sub_trivial_le (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) (R : ℝ)
    (hR : |siteResponse y W h| ≤ R) : |siteResponse y W h - siteResponse y (trivialField n) h| ≤ R := by
  rw [siteResponse_trivialField, sub_zero]
  exact hR
theorem wilsonWeight_priceBoundsScore (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ) :
    PriceBoundsScore ℓ β Λ Φ φ (fun _ => 0) where
  nonneg := fun _ => le_rfl
  borel := measurable_const
  gauge := fun _ _ _ _ _ _ => rfl
  price := fun n _ hb W Y ω P hY hP hoff => by
    have := hull.price n hb W Y ω P hY hP hoff
    simpa only [Finset.sum_const_zero, Real.exp_zero, mul_one] using this
theorem wilsonWeight_responseBounds {M : ℝ} (hM0 : 0 ≤ M) (hE : PlaquetteEnergyBound M)
    {K : ResponseParameters} (hfit : ℓ.Admissible) (hK : K.Admissible ℓ)
    (hKc : (6 * M + 12) * ℓ.weight 2 ≤ K.Kc) (hβ : ℓ.y₁ ≤ β)
    (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ) :
    ResponseBounds ℓ K 0 β 1 Λ Dq (fun _ => 0) (wilsonColdResponse ℓ.side) (wilsonHullResponse ℓ.side Λ.Ω)
      (fun _ _ _ => 0) (fun _ _ _ => 0) := by
  classical
  have hy := hfit.y₁_ge
  have hβ0 : 0 < β := by linarith
  have hr : 2 ^ 16 ≤ clusterRange β :=
    hfit.range_ge.trans (Nat.ceil_mono (Real.rpow_le_rpow (by linarith) hβ (by norm_num)))
  have hG2 : 1 ≤ ℓ.weight 2 := one_le_weight ℓ hfit _
  have hKc12 : 12 ≤ K.Kc := by nlinarith
  have hKc6 : 6 * M * ℓ.weight 2 ≤ K.Kc := by nlinarith
  have hKη : K.Kc ≤ K.Kc / K.η₃ := by
    rw [le_div_iff₀ hK.η₃_pos]
    nlinarith [hK.η₃_le, hK.η₃_pos]
  have hC0 : 12 ≤ K.C₀ := by
    rw [hK.C₀_eq]
    linarith [hfit.a_ge, hK.N₀_nonneg, hK.Kc_ge]
  have hn2 : ∀ m : ℕ, ℓ.n₀ ≤ m → 2 ≤ m := fun m hm => by
    have := hfit.n₀_ge
    omega
  have hm1 : ∀ m : ℕ, (clusterRange β : ℝ) / 64 ≤ m → 1 ≤ m := fun m hm => by
    have h1 : ((2 ^ 16 : ℕ) : ℝ) ≤ clusterRange β := by exact_mod_cast hr
    have h2 : (1 : ℝ) ≤ m := by
      push_cast at h1
      linarith
    exact_mod_cast h2
  have hsz : ∀ {m : ℕ} [NeZero m] (y : TorusSite m) (W : TorusField m) (h : PlaquetteWeight m),
      |siteResponse y W h| ≤ K.C₀ * weightNorm ℓ.side 0 h := by
    intro m _ y W h
    refine (abs_siteResponse_le y W h).trans ?_
    have h1 : weightSup h ≤ weightNorm ℓ.side 0 h := le_max_left _ _
    have h2 := weightNorm_nonneg ℓ.side 0 h
    have h3 := weightSup_nonneg h
    nlinarith
  have hrpow : 0 ≤ K.Ka * β ^ (-(1 / 2) : ℝ) := mul_nonneg hK.Ka_nonneg (Real.rpow_nonneg hβ0.le _)
  have hinv : 0 ≤ K.Kb * β⁻¹ := mul_nonneg hK.Kb_nonneg (inv_nonneg.mpr hβ0.le)
  exact
    { cold_linear := fun n _ _ y W _ c h h' => siteResponse_linear y W c h h'
      hull_linear := fun n _ _ y W Y ω _ c h h' => siteResponse_linear y W c h h'
      cold_reads := fun n _ _ y W _ h h' hh => siteResponse_congr_weight ℓ.side y W h h' hh
      hull_reads := fun n _ _ y W Y ω _ h h' hh => siteResponse_congr_weight ℓ.side y W h h' hh
      cold_borel := fun n _ _ y h => Measurable.ite (measurableSet_isCold ℓ.threshold)
        (measurable_siteResponse y h) measurable_const
      hull_borel := fun n _ hb y Y h => by
        have hset : MeasurableSet {p : TorusField n × (Y → Λ.Ω) | IsLiveState ℓ β Dq p.1 Y p.2} := by
          have h1 := (hull.borel n hb Y).1
          have e : {p : TorusField n × (Y → Λ.Ω) | IsLiveState ℓ β Dq p.1 Y p.2} =
              (fun p : TorusField n × (Y → Λ.Ω) =>
                if IsHullState ℓ (clusterRange β) p.1 Y then Dq n p.1 Y p.2 else 0) ⁻¹' Set.Ioi 0 := by
            ext p
            simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
            split_ifs with hh
            · simp [hh]
            · simp [hh]
          rw [e]
          exact h1 measurableSet_Ioi
        exact Measurable.ite hset ((measurable_siteResponse y h).comp measurable_fst) measurable_const
      cold_gauge := fun n _ _ y g W _ h => _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_gaugeTransform y g W h
      hull_gauge := fun n _ _ y g W Y ω _ h => _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_gaugeTransform y g W h
      cold_translation := fun n _ _ y v W _ h => siteResponse_translate_siteOfInt ℓ.side _ y W h
      hull_translation := fun n _ _ y v W Y ω _ h => siteResponse_translate_siteOfInt ℓ.side _ y W h
      empty := fun n _ _ y W ω _ h => rfl
      mass_integrable := fun n _ hb y W Y hY => (hullDensity_integrable hull hb hY).const_mul _
      mass_carried := fun n _ hb g y W W' hc => by
        rw [responseMass_eq hull hb, responseMass_eq hull hb, siteResponse_constOne_of_transports hc,
          ResponseInTheExpansion.wilsonWeight_eq, ResponseInTheExpansion.wilsonWeight_eq, wilsonAction_of_transports hc]
      cold_carried := fun n _ _ g y W W' _ hc => siteResponse_constOne_of_transports hc y
      share_site := fun n _ _ y W _ => by
        show siteResponse y W (constOneWeight n) - siteResponse y (trivialField n) (constOneWeight n) =
          1 * levelShare ℓ.coupling ℓ.side 0 Finset.univ y W + centered (fun _ _ _ => 0) n y W
        rw [siteResponse_trivialField, ResponseInTheExpansion.centered_zero, sub_zero, add_zero, one_mul]
        simp [siteResponse, levelShare, constOneWeight, vertexMultiplicity, plaquetteEnergyOf]
      share_total := fun n _ _ W _ => by
        show ∑ y : TorusSite n,
            (siteResponse y W (constOneWeight n) - siteResponse y (trivialField n) (constOneWeight n)) =
          1 * actionAtLevel ℓ.coupling ℓ.side 0 Finset.univ W +
            ∑ y : TorusSite n, centered (fun _ _ _ => 0) n y W
        simp only [siteResponse_trivialField, ResponseInTheExpansion.centered_zero, sub_zero, Finset.sum_const_zero,
          add_zero, one_mul]
        rw [sum_siteResponse_constOne]
        rfl
      site_family := coldDensityBounds_zero hfit hrpow (div_nonneg hrpow hK.η₃_pos.le)
      total_family := coldDensityBounds_zero hfit hinv (div_nonneg hinv hK.η₃_pos.le)
      remainder_smooth := fun n _ _ y W _ h => responseRemainder_contDiffThreeAt hE ℓ.side y h W
      remainder_decay := fun n _ hn y W _ h k c X _ hk hX =>
        abs_mixedDeriv_responseRemainder_le hM0 hE ℓ hfit (hn2 n hn) y h W c X hk hX (by
          split_ifs
          · exact hKc6.trans hKη
          · exact hKc6)
      remainder_local := fun n _ hn y W W' m _ _ _ hA h k b X _ hb _ =>
        abs_mixedDeriv_centeredRemainder_sub_le ℓ hfit (hn2 n hn) y W W' m hA h b X hb hKc12
      forget := fun n n' _ _ _ _ W W' Y Y' ω ω' y y' m h h' _ _ hm hS hh =>
        abs_centered_siteResponse_sub_le ℓ.side (hm1 m hm) hS.2.2.1 hh _ (by
          rw [siteScore_zero]
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (weightNorm_nonneg _ _ _))
      forget_cold := fun n n' _ _ _ _ W W' Y ω ω' y y' m h h' _ _ hm hS hh =>
        abs_centered_siteResponse_sub_le ℓ.side (hm1 m hm) hS.2.2.1 hh _ (by
          rw [siteScore_zero]
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (weightNorm_nonneg _ _ _))
      forget_both_cold := fun n n' _ _ _ _ W W' y y' m h h' _ _ hm _ _ hA hh =>
        abs_centered_siteResponse_sub_le ℓ.side (hm1 m hm) hA hh _
          (mul_nonneg (Real.exp_pos _).le (weightNorm_nonneg _ _ _))
      size_cold := fun n _ _ y W _ h => abs_siteResponse_sub_trivial_le y W h _ (hsz y W h)
      size_hull := fun n _ _ y W Y ω _ h => abs_siteResponse_sub_trivial_le y W h _ (by
        rw [siteScore_zero, add_zero]
        exact hsz y W h) }
end Assembly
theorem wilsonWeightHasResponseBounds (hW : WilsonWeightHasExpansion) (hE : PlaquetteEnergySmoothBound) :
    WilsonWeightHasResponseBoundsStatement := by
  obtain ⟨C, hC⟩ := hW
  obtain ⟨M, hM0, hEn⟩ := hE
  refine ⟨C, 6 * M + 12, fun ℓ K hfit hK hCd hKc β hβ => ?_⟩
  have hrow := hC ℓ hfit hCd β hβ
  obtain ⟨_, f, hcold, Λ, Dq, Φ, φ, hull⟩ := id hrow
  exact ⟨Λ, hrow, f, hcold, Dq, Φ, φ, hull, wilsonWeight_priceBoundsScore hull,
    wilsonWeight_responseBounds hM0 hEn hfit hK hKc hβ hull⟩
end YangMills.Construction.ResponseInTheExpansion
end
