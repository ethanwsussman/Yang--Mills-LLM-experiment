import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoToriProof
import YangMills.Construction.FreeEnergiesOfTheFlow.WilsonResponseOnEverySplitting
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace WilsonResponseSplitting
open TorusFields TorusLumps StepCosts WeightedResponses ResponseInTheExpansion
section Corners
abbrev PlaquetteCorner : Type := Fin 4 × Fin 4 × Bool × Bool
def orderedCorners : Finset PlaquetteCorner := Finset.univ.filter fun i => i.1 < i.2.1
def baseOffset (i : PlaquetteCorner) : Fin 4 → ℤ := fun j =>
  -(if i.2.2.1 = true ∧ j = i.1 then 1 else 0) - (if i.2.2.2 = true ∧ j = i.2.1 then 1 else 0)
def axisVector (i : Fin 4) : Fin 4 → ℤ := fun j => if j = i then 1 else 0
theorem card_orderedCorners : orderedCorners.card = 24 := by decide
variable {n : ℕ}
def plaquetteAtCorner (y : TorusSite n) (i : PlaquetteCorner) : TorusPlaquette n :=
  (y + siteOfInt (baseOffset i), i.1, i.2.1)
theorem vertexMultiplicity_eq_sum (y x : TorusSite n) (μ ν : Fin 4) :
    vertexMultiplicity y (x, μ, ν) =
      ∑ ab : Bool × Bool, if x = y + siteOfInt (baseOffset (μ, ν, ab.1, ab.2)) then (1 : ℝ) else 0 := by apply _root_.YangMills.DeltaSharedProofs.p502373 <;> assumption
theorem sum_vertexMultiplicity_mul [NeZero n] (y : TorusSite n) (F : TorusPlaquette n → ℝ) :
    ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * F p =
      ∑ i ∈ orderedCorners, F (plaquetteAtCorner y i) := by apply _root_.YangMills.DeltaSharedProofs.p501550 <;> assumption
end Corners
section Energies
variable {n : ℕ}
theorem plaquetteEnergyOf_trivialField (p : TorusPlaquette n) : plaquetteEnergyOf (trivialField n) p = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.plaquetteEnergyOf_trivialField <;> assumption
theorem siteResponse_eq_sum_corners [NeZero n] (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) :
    siteResponse y W h =
      (1 / 4) * ∑ i ∈ orderedCorners, h (plaquetteAtCorner y i) * plaquetteEnergyOf W (plaquetteAtCorner y i) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_eq_sum <;> assumption
theorem siteResponse_trivialField [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) :
    siteResponse y (trivialField n) h = 0 := by
  simp [siteResponse, plaquetteEnergyOf_trivialField]
theorem siteResponse_add_smul [NeZero n] (y : TorusSite n) (W : TorusField n) (c : ℝ) (h h' : PlaquetteWeight n) :
    siteResponse y W (c • h + h') = c * siteResponse y W h + siteResponse y W h' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_linear <;> assumption
theorem siteResponse_congr_weight (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (W : TorusField n)
    (h h' : PlaquetteWeight n) (hh : ∀ p, IsPlaquetteAt L 0 y p → h p = h' p) :
    siteResponse y W h = siteResponse y W h' := by exact _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_congr_weight L y W h h' hh
end Energies
section Doubled
def barycentreOffset (i : PlaquetteCorner) : Fin 4 → ℤ := fun j =>
  2 * baseOffset i j + (if j = i.1 then 1 else 0) + (if j = i.2.1 then 1 else 0)
set_option maxRecDepth 100000 in
theorem barycentreOffset_sub_bounded : ∀ i ∈ orderedCorners, ∀ i' ∈ orderedCorners, ∀ j,
    -2 ≤ barycentreOffset i' j - barycentreOffset i j ∧ barycentreOffset i' j - barycentreOffset i j ≤ 2 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.barycentreOffset_close <;> assumption
set_option maxRecDepth 100000 in
theorem barycentreOffset_injective : ∀ i ∈ orderedCorners, ∀ i' ∈ orderedCorners,
    (∀ j, barycentreOffset i j = barycentreOffset i' j) → i = i' := by decide
variable {n : ℕ}
theorem two_mul_val_add_cast [NeZero n] (u : ZMod n) (e : ℤ) :
    ((2 * (u + (e : ZMod n)).val : ℕ) : ZMod (2 * n)) =
      ((2 * u.val : ℕ) : ZMod (2 * n)) + ((2 * e : ℤ) : ZMod (2 * n)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.two_mul_val_add_cast <;> assumption
def doubleSite (y : TorusSite n) : TorusSite (2 * n) := fun j => ((2 * (y j).val : ℕ) : ZMod (2 * n))
theorem abs_sub_blockMean_le (L : ℕ) [NeZero L] [NeZero n] (hn : 2 ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight n) {i : PlaquetteCorner} (hi : i ∈ orderedCorners) :
    |h (plaquetteAtCorner y i) - blockMean L 0 n y h| ≤ weightLipschitz L 0 h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.abs_sub_blockMean_le <;> assumption
end Doubled
section Derivatives
variable {n : ℕ}
theorem mixedDeriv_finset_sum {k : ℕ} {ι : Type} (s : Finset ι) (w : ι → ℝ) (F : ι → TorusField n → ℝ)
    (W : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions)
    (hF : ∀ i ∈ s, ContDiff ℝ ⊤ fun σ : Fin k → ℝ => F i (perturb c X σ W)) :
    mixedDeriv (fun W' => ∑ i ∈ s, w i * F i W') W c X = ∑ i ∈ s, w i * mixedDeriv (F i) W c X := by apply _root_.YangMills.Construction.ResponseInTheExpansion.mixedDeriv_sum <;> assumption
def PlaquetteEnergyDerivBound (M : ℝ) : Prop :=
  ∀ (n k : ℕ) (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions),
    ContDiff ℝ ⊤ (fun σ : Fin k → ℝ => plaquetteEnergy (perturb c X σ W) x μ ν) ∧
    (k ≤ 3 → BlockAverages.AreUnitVectors X →
      |mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X| ≤ M) ∧
    ∀ l, (∀ i, plaquetteEdges x μ ν i ≠ c l) →
      mixedDeriv (fun W' : TorusField n => plaquetteEnergy W' x μ ν) W c X = 0
def remainderCoeff (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n)
    (i : PlaquetteCorner) : ℝ :=
  (1 / 4) * (h (plaquetteAtCorner y i) - blockMean L 0 n y h)
theorem responseRemainder_eq_sum (L : ℕ) [NeZero L] [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) :
    responseRemainder (wilsonColdResponse L) n y h =
      fun W => ∑ i ∈ orderedCorners, remainderCoeff L y h i * plaquetteEnergyOf W (plaquetteAtCorner y i) := by
  funext W
  show siteResponse y W h - blockMean L 0 n y h * siteResponse y W (constOneWeight _) = _
  simp only [siteResponse_eq_sum_corners, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [remainderCoeff, constOneWeight]
  ring
theorem weightLipschitz_nonneg' (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.weightLipschitz_nonneg <;> assumption
theorem abs_remainderCoeff_le (L : ℕ) [NeZero L] [NeZero n] (hn : 2 ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight n) {i : PlaquetteCorner} (hi : i ∈ orderedCorners) :
    |remainderCoeff L y h i| ≤ weightLipschitz L 0 h / 4 := by
  have := abs_sub_blockMean_le L hn y h hi
  rw [remainderCoeff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  linarith
theorem responseRemainder_contDiffThreeAt {M : ℝ} (hE : PlaquetteEnergyDerivBound M) (L : ℕ) [NeZero L]
    [NeZero n] (y : TorusSite n) (h : PlaquetteWeight n) (W : TorusField n) :
    ContDiffThreeAt (responseRemainder (wilsonColdResponse L) n y h) W := by
  intro k c X
  rw [responseRemainder_eq_sum]
  exact (ContDiff.sum fun i _ => contDiff_const.mul
    (((hE n k W (plaquetteAtCorner y i).1 i.1 i.2.1 c X).1).of_le le_top)).contDiffAt
def vertexOffset (i : PlaquetteCorner) (s t : Bool) : Fin 4 → ℤ :=
  baseOffset i + (if s = true then axisVector i.1 else 0) + (if t = true then axisVector i.2.1 else 0)
set_option maxRecDepth 100000 in
theorem vertexOffset_bounded : ∀ i ∈ orderedCorners, ∀ (s t : Bool) (j : Fin 4),
    -1 ≤ vertexOffset i s t j ∧ vertexOffset i s t j ≤ 1 := by decide
theorem vertex_eq_add_siteOfInt [NeZero n] (y : TorusSite n) (i : PlaquetteCorner) (s t : Bool) :
    (plaquetteAtCorner y i).1 + (if s = true then unitStep n i.1 else 0) +
        (if t = true then unitStep n i.2.1 else 0) =
      y + siteOfInt (vertexOffset i s t) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.vertex_eq_add_siteOfInt <;> assumption
theorem supDist_plaquetteEdge_le_one [NeZero n] (y : TorusSite n) {i : PlaquetteCorner}
    (hi : i ∈ orderedCorners) (j : Fin 4) :
    supDist y (plaquetteEdges (plaquetteAtCorner y i).1 i.1 i.2.1 j).1 ≤ 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.supDist_edge_le_one <;> assumption
theorem supportDiam_le_two [NeZero n] {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n)
    (h : ∀ l, supDist y (c l).1 ≤ 1) : supportDiam y c ≤ 2 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.supportDiam_le_two <;> assumption
theorem one_le_weight (ℓ : StepParameters) (hfit : ℓ.Admissible) (m : ℕ) : 1 ≤ ℓ.weight m := by apply _root_.YangMills.Construction.ResponseInTheExpansion.one_le_weight <;> assumption
theorem weight_monotone (ℓ : StepParameters) (hfit : ℓ.Admissible) {m m' : ℕ} (h : m ≤ m') :
    ℓ.weight m ≤ ℓ.weight m' := by apply _root_.YangMills.SharedProofs.p24433 <;> assumption
theorem abs_mixedDeriv_responseRemainder_le {M : ℝ} (hM0 : 0 ≤ M) (hE : PlaquetteEnergyDerivBound M)
    (ℓ : StepParameters) (hfit : ℓ.Admissible) [NeZero n] (hn : 2 ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight n) (W : TorusField n) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (hk : k ≤ 3) (hX : BlockAverages.AreUnitVectors X)
    {A : ℝ} (hA : 6 * M * ℓ.weight 2 ≤ A) :
    |mixedDeriv (responseRemainder (wilsonColdResponse ℓ.side) n y h) W c X| ≤
      A * weightLipschitz ℓ.side 0 h / ℓ.weight (supportDiam y c) := by
  have hlip := weightLipschitz_nonneg' ℓ.side 0 h
  have hG : 0 < ℓ.weight (supportDiam y c) := lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)
  have hG2 : 1 ≤ ℓ.weight 2 := one_le_weight ℓ hfit _
  have hA0 : 0 ≤ A := le_trans (mul_nonneg (mul_nonneg (by norm_num) hM0) (le_trans zero_le_one hG2)) hA
  have hsum : mixedDeriv (responseRemainder (wilsonColdResponse ℓ.side) n y h) W c X =
      ∑ i ∈ orderedCorners, remainderCoeff ℓ.side y h i *
        mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAtCorner y i)) W c X := by
    rw [responseRemainder_eq_sum]
    exact mixedDeriv_finset_sum _ _ (fun i W' => plaquetteEnergyOf W' (plaquetteAtCorner y i)) W c X
      fun i _ => (hE n k W (plaquetteAtCorner y i).1 i.1 i.2.1 c X).1
  rw [hsum]
  by_cases hall : ∃ i ∈ orderedCorners, ∀ l, ∃ j, plaquetteEdges (plaquetteAtCorner y i).1 i.1 i.2.1 j = c l
  · obtain ⟨i₀, hi₀, hc⟩ := hall
    have hnear : ∀ l, supDist y (c l).1 ≤ 1 := fun l => by
      obtain ⟨j, hj⟩ := hc l
      rw [← hj]
      exact supDist_plaquetteEdge_le_one y hi₀ j
    have hspan := supportDiam_le_two y c hnear
    have hb : |∑ i ∈ orderedCorners, remainderCoeff ℓ.side y h i *
        mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAtCorner y i)) W c X| ≤
          6 * M * weightLipschitz ℓ.side 0 h := by
      calc _ ≤ ∑ i ∈ orderedCorners, |remainderCoeff ℓ.side y h i *
              mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAtCorner y i)) W c X| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ orderedCorners, weightLipschitz ℓ.side 0 h / 4 * M := Finset.sum_le_sum fun i hi => by
              rw [abs_mul]
              exact mul_le_mul (abs_remainderCoeff_le ℓ.side hn y h hi)
                ((hE n k W (plaquetteAtCorner y i).1 i.1 i.2.1 c X).2.1 hk hX) (abs_nonneg _) (by positivity)
        _ = 6 * M * weightLipschitz ℓ.side 0 h := by
              rw [Finset.sum_const, card_orderedCorners]
              simp only [nsmul_eq_mul]
              push_cast
              ring
    refine hb.trans ?_
    rw [le_div_iff₀ hG]
    have h3 : ℓ.weight (supportDiam y c) ≤ ℓ.weight 2 := weight_monotone ℓ hfit hspan
    calc 6 * M * weightLipschitz ℓ.side 0 h * ℓ.weight (supportDiam y c)
        = 6 * M * ℓ.weight (supportDiam y c) * weightLipschitz ℓ.side 0 h := by ring
      _ ≤ A * weightLipschitz ℓ.side 0 h := mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left h3 (by positivity)).trans hA) hlip
  · push Not at hall
    have h0 : ∑ i ∈ orderedCorners, remainderCoeff ℓ.side y h i *
        mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAtCorner y i)) W c X = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨l, hl⟩ := hall i hi
      have := (hE n k W (plaquetteAtCorner y i).1 i.1 i.2.1 c X).2.2 l hl
      have e : mixedDeriv (fun W' : TorusField n => plaquetteEnergyOf W' (plaquetteAtCorner y i)) W c X = 0 :=
        this
      rw [e, mul_zero]
    rw [h0, abs_zero]
    exact div_nonneg (mul_nonneg hA0 hlip) hG.le
theorem abs_mixedDeriv_centeredRemainder_sub_le (ℓ : StepParameters) (hfit : ℓ.Admissible) [NeZero n]
    (hn : 2 ≤ n) (y : TorusSite n) (W W' : TorusField n) (m : ℕ) (hA : FieldsAgreeNear W W' y y m)
    (h : PlaquetteWeight n) {k : ℕ} (b : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (hb : ∀ l, BondOffsetInBox m (b l)) {A : ℝ}
    (hA12 : 12 ≤ A) :
    |mixedDeriv (centeredRemainder (wilsonColdResponse ℓ.side) n y h) W (fun l => bondFrom y (b l)) X -
        mixedDeriv (centeredRemainder (wilsonColdResponse ℓ.side) n y h) W' (fun l => bondFrom y (b l)) X| ≤
      A * weightLipschitz ℓ.side 0 h / ℓ.weight m := by apply _root_.YangMills.Construction.ResponseInTheExpansion.abs_mixedDeriv_centeredRemainder_sub_le <;> assumption
end Derivatives
section Sizes
variable {n : ℕ}
theorem weightSup_nonneg' {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightSup h :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem weightNorm_nonneg' (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  (weightSup_nonneg' h).trans (le_max_left _ _)
theorem abs_siteResponse_le [NeZero n] (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) :
    |siteResponse y W h| ≤ 12 * weightSup h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.abs_siteResponse_le <;> assumption
end Sizes
section Carried
variable {n : ℕ}
theorem siteResponse_of_transports {g : TorusIsometry} [NeZero n] {W W' : TorusField n}
    (hc : g.Transports W W') (y : TorusSite n) :
    siteResponse (g.mapSite y) W' (constOneWeight n) = siteResponse y W (constOneWeight n) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_constOne_of_transports <;> assumption
end Carried
section Assembly
variable {ℓ : StepParameters} {β : ℝ} {Λ : LabelSpace} {f : LocalDensity}
  {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ} {n : ℕ} [NeZero n]
theorem wilsonWeight_eq_exp (W : TorusField n) :
    wilsonWeight β n W = Real.exp (-β * wilsonAction Finset.univ W) := by
  simp [wilsonWeight, NeZero.ne n]
theorem hullDensity_integrable (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ)
    (hb : IsBlockTorusSide ℓ n) {W : TorusField n} {Y : Finset (TorusSite n)}
    (hY : IsHullState ℓ (clusterRange β) W Y) :
    Integrable (fun ω : Y → Λ.Ω => Dq n W Y ω) (Measure.pi fun _ : Y => Λ.μ) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.hullDensity_integrable <;> assumption
theorem responseMass_eq (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ) (hb : IsBlockTorusSide ℓ n)
    (y : TorusSite n) (W : TorusField n) :
    responseMass ℓ 0 β Λ Dq (wilsonHullResponse ℓ.side Λ.Ω) n y W =
      siteResponse y W (constOneWeight n) * wilsonWeight β n W := by apply _root_.YangMills.Construction.ResponseInTheExpansion.responseMass_eq <;> assumption
theorem measurable_siteResponse (y : TorusSite n) (h : PlaquetteWeight n) :
    Measurable fun W : TorusField n => siteResponse y W h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.measurable_siteResponse <;> assumption
theorem measurableSet_isCold (s : ℝ) : MeasurableSet {W : TorusField n | IsCold s W} := by apply _root_.YangMills.Construction.ResponseInTheExpansion.measurableSet_isCold <;> assumption
theorem siteResponse_gaugeTransform (y : TorusSite n) (g : TorusSite n → BlockAverages.UnitQuaternion)
    (W : TorusField n) (h : PlaquetteWeight n) : siteResponse y (gaugeTransform g W) h = siteResponse y W h := by
  simp [siteResponse, plaquetteEnergyOf, _root_.YangMills.Construction.TorusFields.plaquetteEnergy_gaugeTransform]
theorem siteResponse_translate_siteOfInt (L : ℕ) (v : Fin 4 → ℤ) (y : TorusSite n) (W : TorusField n)
    (h : PlaquetteWeight n) :
    siteResponse y (TorusFields.translate (siteOfInt v) W) (translateWeight (fineTranslate L 0 n v) h) =
      siteResponse (y + siteOfInt v) W h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.siteResponse_translate_siteOfInt <;> assumption
theorem sum_siteResponse_constOneWeight (W : TorusField n) :
    ∑ y : TorusSite n, siteResponse y W (constOneWeight n) = wilsonAction Finset.univ W := by apply _root_.YangMills.Construction.ResponseInTheExpansion.sum_siteResponse_constOne <;> assumption
theorem centered_zero_density (m : ℕ) [NeZero m] (y : TorusSite m) (W : TorusField m) :
    centered (fun _ _ _ => 0) m y W = 0 := by
  simp [centered]
theorem mixedDeriv_zero_function {m k : ℕ} (W : TorusField m) (c : Fin k → TorusBond m)
    (X : Fin k → BlockAverages.imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField m => (0 : ℝ)) W c X = 0 := by apply _root_.YangMills.Construction.WilsonExpansion.mixedDeriv_zero <;> assumption
theorem zeroColdDensityBounds (hfit : ℓ.Admissible) {E E₃ : ℝ} (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) :
    ColdDensityBounds ℓ E E₃ (fun _ _ _ => 0) where
  smooth := fun n _ _ y W _ k c X => contDiffAt_const
  gauge := fun _ _ _ _ _ _ _ => rfl
  translation := fun _ _ _ _ _ _ _ => rfl
  decay := fun n _ _ y W _ k c X _ _ _ => by
    rw [mixedDeriv_zero_function, abs_zero]
    have h1 : 0 < ℓ.weight (supportDiam y c) := lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)
    split_ifs
    · exact div_nonneg hE₃ h1.le
    · exact div_nonneg hE h1.le
  local_density := fun n n' _ _ _ _ y y' W W' m _ _ _ _ _ k h X _ _ _ => by
    have e : centered (fun _ _ _ => (0 : ℝ)) = fun _ _ _ => 0 := by
      funext a b c
      simp [centered]
    rw [e]
    simp only [mixedDeriv_zero_function, sub_zero, abs_zero]
    exact div_nonneg hE (lt_of_lt_of_le one_pos (one_le_weight ℓ hfit _)).le
  no_curvature_term := fun A A' _ _ => by
    have h0 : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : BlockAverages.imaginaryQuaternions),
        secondDerivLimit (fun _ _ _ => 0) c c' X X' = 0 := by
      intro c c' X X'
      unfold secondDerivLimit
      simp only [mixedDeriv_zero_function]
      exact (tendsto_const_nhds).limUnder_eq
    simp [h0]
omit [NeZero n] in
theorem siteScore_zero_price {Ω : Type} (Y : Finset (TorusSite n)) (ω : Y → Ω) (y : TorusSite n) :
    siteScore (fun _ : Ω => (0 : ℝ)) Y ω y = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.siteScore_zero <;> assumption
theorem abs_sub_siteResponse_sub_le (L : ℕ) [NeZero L] {n' : ℕ} [NeZero n'] {W : TorusField n}
    {W' : TorusField n'} {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} (hm : 1 ≤ m)
    (hA : FieldsAgreeNear W W' y y' m) {h : PlaquetteWeight n} {h' : PlaquetteWeight n'}
    (hh : WeightsAgreeAt L 0 y y' h h') (R : ℝ) (hR : 0 ≤ R) :
    |(siteResponse y W h - siteResponse y (trivialField n) h) -
      (siteResponse y' W' h' - siteResponse y' (trivialField n') h')| ≤ R := by exact _root_.YangMills.Construction.ResponseInTheExpansion.abs_centered_siteResponse_sub_le L hm hA hh R hR
theorem abs_siteResponse_sub_trivial_le (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n) (R : ℝ)
    (hR : |siteResponse y W h| ≤ R) : |siteResponse y W h - siteResponse y (trivialField n) h| ≤ R := by apply _root_.YangMills.Construction.ResponseInTheExpansion.abs_siteResponse_sub_trivial_le <;> assumption
theorem wilsonPriceBoundsScore (hull : HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ) :
    PriceBoundsScore ℓ β Λ Φ φ (fun _ => 0) where
  nonneg := fun _ => le_rfl
  borel := measurable_const
  gauge := fun _ _ _ _ _ _ => rfl
  price := fun n _ hb W Y ω P hY hP hoff => by
    have := hull.price n hb W Y ω P hY hP hoff
    simpa only [Finset.sum_const_zero, Real.exp_zero, mul_one] using this
theorem wilsonResponseBounds {M : ℝ} (hM0 : 0 ≤ M) (hE : PlaquetteEnergyDerivBound M) {K : ResponseParameters}
    (hfit : ℓ.Admissible) (hK : K.Admissible ℓ) (hKc : (6 * M + 12) * ℓ.weight 2 ≤ K.Kc) (hβ : ℓ.y₁ ≤ β)
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
    have h2 := weightNorm_nonneg' ℓ.side 0 h
    have h3 := weightSup_nonneg' h
    nlinarith
  have hrpow : 0 ≤ K.Ka * β ^ (-(1 / 2) : ℝ) := mul_nonneg hK.Ka_nonneg (Real.rpow_nonneg hβ0.le _)
  have hinv : 0 ≤ K.Kb * β⁻¹ := mul_nonneg hK.Kb_nonneg (inv_nonneg.mpr hβ0.le)
  exact
    { cold_linear := fun n _ _ y W _ c h h' => siteResponse_add_smul y W c h h'
      hull_linear := fun n _ _ y W Y ω _ c h h' => siteResponse_add_smul y W c h h'
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
      cold_gauge := fun n _ _ y g W _ h => _root_.YangMills.Construction.WilsonResponseSplitting.siteResponse_gaugeTransform y g W h
      hull_gauge := fun n _ _ y g W Y ω _ h => _root_.YangMills.Construction.WilsonResponseSplitting.siteResponse_gaugeTransform y g W h
      cold_translation := fun n _ _ y v W _ h => siteResponse_translate_siteOfInt ℓ.side _ y W h
      hull_translation := fun n _ _ y v W Y ω _ h => siteResponse_translate_siteOfInt ℓ.side _ y W h
      empty := fun n _ _ y W ω _ h => rfl
      mass_integrable := fun n _ hb y W Y hY => (hullDensity_integrable hull hb hY).const_mul _
      mass_carried := fun n _ hb g y W W' hc => by
        rw [responseMass_eq hull hb, responseMass_eq hull hb, siteResponse_of_transports hc,
          wilsonWeight_eq_exp, wilsonWeight_eq_exp, wilsonAction_of_transports hc]
      cold_carried := fun n _ _ g y W W' _ hc => siteResponse_of_transports hc y
      share_site := fun n _ _ y W _ => by
        show siteResponse y W (constOneWeight n) - siteResponse y (trivialField n) (constOneWeight n) =
          1 * levelShare ℓ.coupling ℓ.side 0 Finset.univ y W + centered (fun _ _ _ => 0) n y W
        rw [siteResponse_trivialField, centered_zero_density, sub_zero, add_zero, one_mul]
        simp [siteResponse, levelShare, constOneWeight, vertexMultiplicity, plaquetteEnergyOf]
      share_total := fun n _ _ W _ => by
        show ∑ y : TorusSite n,
            (siteResponse y W (constOneWeight n) - siteResponse y (trivialField n) (constOneWeight n)) =
          1 * actionAtLevel ℓ.coupling ℓ.side 0 Finset.univ W +
            ∑ y : TorusSite n, centered (fun _ _ _ => 0) n y W
        simp only [siteResponse_trivialField, centered_zero_density, sub_zero, Finset.sum_const_zero, add_zero,
          one_mul]
        rw [sum_siteResponse_constOneWeight]
        rfl
      site_family := zeroColdDensityBounds hfit hrpow (div_nonneg hrpow hK.η₃_pos.le)
      total_family := zeroColdDensityBounds hfit hinv (div_nonneg hinv hK.η₃_pos.le)
      remainder_smooth := fun n _ _ y W _ h => responseRemainder_contDiffThreeAt hE ℓ.side y h W
      remainder_decay := fun n _ hn y W _ h k c X _ hk hX =>
        abs_mixedDeriv_responseRemainder_le hM0 hE ℓ hfit (hn2 n hn) y h W c X hk hX (by
          split_ifs
          · exact hKc6.trans hKη
          · exact hKc6)
      remainder_local := fun n _ hn y W W' m _ _ _ hA h k b X _ hb _ =>
        abs_mixedDeriv_centeredRemainder_sub_le ℓ hfit (hn2 n hn) y W W' m hA h b X hb hKc12
      forget := fun n n' _ _ _ _ W W' Y Y' ω ω' y y' m h h' _ _ hm hS hh =>
        abs_sub_siteResponse_sub_le ℓ.side (hm1 m hm) hS.2.2.1 hh _ (by
          rw [siteScore_zero_price]
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (weightNorm_nonneg' _ _ _))
      forget_cold := fun n n' _ _ _ _ W W' Y ω ω' y y' m h h' _ _ hm hS hh =>
        abs_sub_siteResponse_sub_le ℓ.side (hm1 m hm) hS.2.2.1 hh _ (by
          rw [siteScore_zero_price]
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (weightNorm_nonneg' _ _ _))
      forget_both_cold := fun n n' _ _ _ _ W W' y y' m h h' _ _ hm _ _ hA hh =>
        abs_sub_siteResponse_sub_le ℓ.side (hm1 m hm) hA hh _
          (mul_nonneg (Real.exp_pos _).le (weightNorm_nonneg' _ _ _))
      size_cold := fun n _ _ y W _ h => abs_siteResponse_sub_trivial_le y W h _ (hsz y W h)
      size_hull := fun n _ _ y W Y ω _ h => abs_siteResponse_sub_trivial_le y W h _ (by
        rw [siteScore_zero_price, add_zero]
        exact hsz y W h) }
end Assembly
end WilsonResponseSplitting
namespace FreeEnergiesOfTheFlow
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion WilsonResponseSplitting
theorem wilsonResponseEverySplitting_holds (hE : PlaquetteEnergySmoothBound) :
    WilsonResponseEverySplitting := by
  obtain ⟨M, hM0, hEn⟩ := hE
  exact ⟨6 * M + 12, fun ℓ K hfit hK hKc β hβ f Λ Dq Φ φ hull =>
    ⟨wilsonPriceBoundsScore hull, wilsonResponseBounds hM0 hEn hfit hK hKc hβ hull⟩⟩
end FreeEnergiesOfTheFlow
end YangMills.Construction
end
