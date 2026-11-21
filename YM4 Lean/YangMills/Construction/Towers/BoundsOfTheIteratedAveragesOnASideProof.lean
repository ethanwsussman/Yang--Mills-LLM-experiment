import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.Towers.BoundsOfTheIteratedAveragesOnASide
import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverageProof
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.OneStepRemainderOfTheIteratedAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IteratedMeanBounds
open YangMills.Construction.IdentityExpChart (expForm)
open YangMills.Construction.Tower.TwoLevelMaps (linearSmoothingBetween)
open YangMills.Construction.Tower.StepRemainder (logMeanDefect)
theorem maxOperatorNorm_le_ofReal {ι : Type*} {f : ι → Matrices.ComplexMatrix2} {M : ℝ}
    (h : ∀ i, Matrices.ComplexMatrix2.operatorNorm (f i) ≤ M) :
    maxOperatorNorm f ≤ ENNReal.ofReal M := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.maxOperatorNorm_le_ofReal <;> assumption
theorem operatorNorm_le_toReal_maxOperatorNorm {ι : Type*} {f : ι → Matrices.ComplexMatrix2}
    (h : maxOperatorNorm f ≠ ∞) (i : ι) :
    Matrices.ComplexMatrix2.operatorNorm (f i) ≤ (maxOperatorNorm f).toReal := by
  have h₁ : ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (f i)) ≤ maxOperatorNorm f :=
    le_iSup (fun i => ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (f i))) i
  exact (ENNReal.ofReal_le_iff_le_toReal h).mp h₁
section Numbers
variable {L k : ℕ}
theorem meshAt_pos (hL : 0 < L) (j : ℕ) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_add (hL : 0 < L) (i d : ℕ) :
    meshAt L k (i + d) = (L : ℝ) ^ d * meshAt L k i := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold meshAt
  rw [← zpow_natCast, ← zpow_add₀ hL']
  congr 1
  push_cast
  ring
theorem meshAt_le_one (hL : 1 ≤ L) {j : ℕ} (hj : j ≤ k) : meshAt L k j ≤ 1 := by
  unfold meshAt
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hL) (by omega)
theorem sum_meshAt_succ_le (hL : 3 ≤ L) (j : ℕ) :
    ∑ i ∈ Finset.range j, meshAt L k (i + 1) ≤ 3 / 2 * meshAt L k j := by
  induction j with
  | zero =>
    simpa using (meshAt_pos (k := k) (by omega) 0).le
  | succ j ih =>
    have h₁ : meshAt L k (j + 1) = (L : ℝ) * meshAt L k j := by
      simpa using meshAt_add (k := k) (by omega : 0 < L) j 1
    have h₂ : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have h₃ := meshAt_pos (k := k) (by omega : 0 < L) j
    rw [Finset.sum_range_succ]
    nlinarith
theorem geometric_recursion_le (hL : 3 ≤ L) {j : ℕ} (hj : j ≤ k) {α C : ℝ} (hα : 0 ≤ α)
    (hC : 0 ≤ C) (h : 150 * C * α ≤ (L : ℝ) ^ 2) :
    5 * (L : ℝ) ^ j * (meshAt L k 0 * α) +
        ∑ i ∈ Finset.range j,
          5 * (L : ℝ) ^ (j - (i + 1)) * (C * (10 * meshAt L k i * α) ^ 2) ≤
      10 * meshAt L k j * α := by
  have hL0 : 0 < L := by omega
  have h₀ : (L : ℝ) ^ j * meshAt L k 0 = meshAt L k j := by
    simpa using (meshAt_add (k := k) hL0 0 j).symm
  have hterm : ∀ i ∈ Finset.range j,
      5 * (L : ℝ) ^ (j - (i + 1)) * (C * (10 * meshAt L k i * α) ^ 2) =
        500 * C * α ^ 2 / (L : ℝ) ^ 2 * meshAt L k j * meshAt L k (i + 1) := by
    intro i hi
    have hi' : i + 1 + (j - (i + 1)) = j := by
      have := Finset.mem_range.mp hi
      omega
    have e₁ : meshAt L k j = (L : ℝ) ^ (j - (i + 1)) * meshAt L k (i + 1) := by
      conv_lhs => rw [← hi']
      exact meshAt_add hL0 _ _
    have e₂ : meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by
      simpa using meshAt_add (k := k) hL0 i 1
    rw [e₁, e₂]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hs := sum_meshAt_succ_le (k := k) hL j
  have hl := meshAt_pos (k := k) hL0 j
  have hl1 := meshAt_le_one (k := k) (by omega : 1 ≤ L) hj
  have hc : 0 ≤ 500 * C * α ^ 2 / (L : ℝ) ^ 2 * meshAt L k j := by positivity
  have hb : 500 * C * α ^ 2 / (L : ℝ) ^ 2 * meshAt L k j *
      ∑ i ∈ Finset.range j, meshAt L k (i + 1) ≤ 5 * meshAt L k j * α := by
    have h₁ : 500 * C * α ^ 2 / (L : ℝ) ^ 2 * meshAt L k j *
        ∑ i ∈ Finset.range j, meshAt L k (i + 1) ≤
        500 * C * α ^ 2 / (L : ℝ) ^ 2 * meshAt L k j * (3 / 2 * 1) :=
      mul_le_mul_of_nonneg_left (hs.trans (by nlinarith)) hc
    have h₂ : 500 * C * α ^ 2 / (L : ℝ) ^ 2 * (3 / 2 * 1) ≤ 5 * α := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have h₃ : 5 * (L : ℝ) ^ j * (meshAt L k 0 * α) = 5 * meshAt L k j * α := by
    rw [← h₀]
    ring
  rw [h₃]
  linarith
end Numbers
section Linear
variable {L n k : ℕ}
theorem bondFormSumAlong_add {i : ℤ} (A A' : PeriodicLattice.Bond L n i → Matrices.ComplexMatrix2)
    (Γ : List (PeriodicLattice.Bond L n i)) :
    PeriodicLattice.bondFormSumAlong (A + A') Γ =
      PeriodicLattice.bondFormSumAlong A Γ + PeriodicLattice.bondFormSumAlong A' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ClosedFormsSmoothing.bondFormSumAlong_add <;> assumption
theorem contourFormAverage_add {i i' : ℤ}
    (A A' : PeriodicLattice.Bond L n i' → Matrices.ComplexMatrix2)
    (y : PeriodicLattice.Site L n i) (x : PeriodicLattice.Site L n i') :
    PeriodicLattice.contourFormAverage (A + A') y x =
      PeriodicLattice.contourFormAverage A y x + PeriodicLattice.contourFormAverage A' y x := by apply _root_.YangMills.Construction.PeriodicLattice.ClosedFormsSmoothing.contourFormAverage_add <;> assumption
theorem linearSmoothing_add (hL : 0 < L) (j : ℕ) (A A' : Edge L n k j → Matrices.ComplexMatrix2) :
    linearSmoothing L n k j (A + A') = linearSmoothing L n k j A + linearSmoothing L n k j A' := by
  have := SeparatedSequences.BaseParameters.site_finite hL n (PeriodicLattice.levelDepth k j)
  funext c
  simp only [linearSmoothing, PeriodicLattice.scaledLinearBlockStep,
    PeriodicLattice.scaledLinearBlockAverage, PeriodicLattice.linearBlockSum, Pi.add_apply]
  rw [← smul_add, ← finsum_mem_add_distrib (Set.toFinite _)]
  congr 1
  refine finsum_mem_congr rfl fun x _ => ?_
  rw [contourFormAverage_add, bondFormSumAlong_add, contourFormAverage_add]
  abel
def linearSmoothingAddHom (hL : 0 < L) (j : ℕ) :
    (Edge L n k j → Matrices.ComplexMatrix2) →+ (Edge L n k (j + 1) → Matrices.ComplexMatrix2) :=
  AddMonoidHom.mk' (linearSmoothing L n k j) (linearSmoothing_add hL j)
def composedSmoothing (L n k i l : ℕ) :
    (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k l → Matrices.ComplexMatrix2 :=
  open Classical in
  if h : i ≤ l then linearSmoothingBetween L n k h else 0
theorem composedSmoothing_self (i : ℕ) (B : Edge L n k i → Matrices.ComplexMatrix2) :
    composedSmoothing L n k i i B = B := by
  simp [composedSmoothing, linearSmoothingBetween, levelwiseComposition_self]
theorem composedSmoothing_succ {i l : ℕ} (h : i ≤ l) (B : Edge L n k i → Matrices.ComplexMatrix2) :
    composedSmoothing L n k i (l + 1) B = linearSmoothing L n k l (composedSmoothing L n k i l B) := by
  simp only [composedSmoothing, dif_pos h, dif_pos (Nat.le_succ_of_le h), linearSmoothingBetween]
  rw [levelwiseComposition_succ _ h]
  rfl
theorem composedSmoothing_mem_and_norm_le (hLin : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {i l d : ℕ}
    (hd : i + d = l) (hl : l ≤ k) {B : Edge L n k i → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) :
    composedSmoothing L n k i l B ∈ complexEdgeForms L n k l ∧
      maxOperatorNorm (composedSmoothing L n k i l B) ≤ 5 * (L : ℝ≥0∞) ^ d * maxOperatorNorm B := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · obtain rfl : i = l := by omega
    rw [composedSmoothing_self]
    refine ⟨hB, ?_⟩
    calc maxOperatorNorm B = 1 * maxOperatorNorm B := (one_mul _).symm
      _ ≤ 5 * (L : ℝ≥0∞) ^ 0 * maxOperatorNorm B := by
        gcongr
        norm_num
  · obtain rfl : i = l - d := by omega
    have h := (((hLin L hL k hk).1 n hn).2.1) d l (by omega) (by omega) hl
    have e : composedSmoothing L n k (l - d) l B =
        linearSmoothingBetween L n k (Nat.sub_le l d) B := by
      simp only [composedSmoothing, dif_pos (Nat.sub_le l d)]
    rw [e]
    exact ⟨h.linearSmoothing_mapsTo_surjOn.1 hB, h.linearSmoothing_norm_le B hB⟩
theorem composedSmoothing_apply_norm_le (hLin : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {i l d : ℕ}
    (hd : i + d = l) (hl : l ≤ k) {B : Edge L n k i → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ b, Matrices.ComplexMatrix2.operatorNorm (B b) ≤ M) (c : Edge L n k l) :
    Matrices.ComplexMatrix2.operatorNorm (composedSmoothing L n k i l B c) ≤ 5 * (L : ℝ) ^ d * M := by
  have h₁ : ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (composedSmoothing L n k i l B c)) ≤
      maxOperatorNorm (composedSmoothing L n k i l B) :=
    le_iSup (fun c => ENNReal.ofReal
      (Matrices.ComplexMatrix2.operatorNorm (composedSmoothing L n k i l B c))) c
  have h₂ : maxOperatorNorm (composedSmoothing L n k i l B) ≤
      ENNReal.ofReal (5 * (L : ℝ) ^ d * M) := by
    refine (composedSmoothing_mem_and_norm_le hLin hL hn hk hd hl hB).2.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    have h₃ : (5 : ℝ≥0∞) = ENNReal.ofReal 5 := by simp
    rw [← h₃]
    gcongr
    exact maxOperatorNorm_le_ofReal hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h₁.trans h₂)
end Linear
section Forms
variable {L n k j : ℕ}
theorem expForm_apply {A : Edge L n k j → Matrices.ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (b : Edge L n k j) : expForm A b = Matrices.ComplexMatrix2.matExp (Complex.I • A b) := by
  have hA' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra A := hA
  by_cases hb : b.IsPositivelyOriented
  · simp [expForm, PeriodicLattice.expTwist, hb]
  · simp only [expForm, PeriodicLattice.expTwist, if_neg hb, mul_one, Pi.one_apply]
    rw [hA'.2 b, smul_neg, ← Matrix.exp_neg, neg_neg]
theorem fullTrace_eq_zero_of_mem {A : Edge L n k j → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n k j) (b : Edge L n k j) :
    Matrices.ComplexMatrix2.fullTrace (A b) = 0 := by
  have hA' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra A := hA
  rcases b.positive_or_opposite_positive with hb | hb
  · exact hA'.1 b hb
  · have h : Matrices.ComplexMatrix2.fullTrace (A b.opposite) = 0 := hA'.1 _ hb
    rw [hA'.2 b] at h
    simpa [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_neg] using h
theorem expForm_mem_fieldsIn (hE : Matrices.ComplexMatrix2.ExpLogEstimates)
    {A : Edge L n k j → Matrices.ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j) :
    expForm A ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hA' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra A := hA
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rw [expForm_apply hA]
    change (Matrices.ComplexMatrix2.matExp (Complex.I • A b)).det = 1
    rw [hE.2.2.2.2.2.1]
    have h : Matrices.ComplexMatrix2.fullTrace (Complex.I • A b) = 0 := by
      simp only [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_smul]
      rw [show Matrix.trace (A b) = 0 from fullTrace_eq_zero_of_mem hA b, smul_zero]
    rw [h, Complex.exp_zero]
  · rw [expForm_apply hA, expForm_apply hA, hA'.2 b, smul_neg]
    exact Matrix.exp_neg _
def logEdgeForm (V : Edge L n k j → Matrices.ComplexMatrix2) : Edge L n k j → Matrices.ComplexMatrix2 :=
  extendOddly fun b => Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (V b)
theorem logEdgeForm_of_positive (V : Edge L n k j → Matrices.ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    logEdgeForm V b = Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (V b) := by
  simp [logEdgeForm, extendOddly, hb]
theorem logEdgeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (hj : j ≤ k)
    {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Matrices.ComplexMatrix2.logSeries (V b) ∈ Matrices.ComplexMatrix2.traceless) :
    logEdgeForm V ∈ complexEdgeForms L n k j := by
  have hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [logEdgeForm_of_positive V hb]
    exact Matrices.ComplexMatrix2.traceless.smul_mem _ (hV b hb)
  · rcases hx b with ⟨hb, hb'⟩ | ⟨hb', hb⟩
    · simp only [logEdgeForm, extendOddly, if_neg hb', if_pos hb,
        PeriodicLattice.Bond.opposite_opposite]
    · simp only [logEdgeForm, extendOddly, if_neg hb, if_pos hb', neg_neg]
end Forms
section Iterates
variable {L n k : ℕ}
def iteratedForm (a : Edge L n k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → Edge L n k j → Matrices.ComplexMatrix2
  | 0 => scaledRemainderForm a
  | j + 1 => logEdgeForm (PeriodicLattice.complexBlockFieldAtLevel (j + 1) (remainderGaugeField a))
def stepDefect (a : Edge L n k 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    Edge L n k (j + 1) → Matrices.ComplexMatrix2 :=
  iteratedForm a (j + 1) - linearSmoothing L n k j (iteratedForm a j)
theorem iteratedForm_eq_sum (hL : 0 < L) (a : Edge L n k 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    iteratedForm a j = composedSmoothing L n k 0 j (iteratedForm a 0) +
      ∑ i ∈ Finset.range j, composedSmoothing L n k (i + 1) j (stepDefect a i) := by
  induction j with
  | zero => simp [composedSmoothing_self]
  | succ j ih =>
    have h₁ : iteratedForm a (j + 1) =
        linearSmoothing L n k j (iteratedForm a j) + stepDefect a j := by
      simp [stepDefect]
    have h₂ : linearSmoothing L n k j (iteratedForm a j) =
        composedSmoothing L n k 0 (j + 1) (iteratedForm a 0) +
          ∑ i ∈ Finset.range j, composedSmoothing L n k (i + 1) (j + 1) (stepDefect a i) := by
      calc linearSmoothing L n k j (iteratedForm a j)
          = linearSmoothing L n k j (composedSmoothing L n k 0 j (iteratedForm a 0) +
              ∑ i ∈ Finset.range j, composedSmoothing L n k (i + 1) j (stepDefect a i)) :=
            congrArg _ ih
        _ = linearSmoothing L n k j (composedSmoothing L n k 0 j (iteratedForm a 0)) +
              ∑ i ∈ Finset.range j,
                linearSmoothing L n k j (composedSmoothing L n k (i + 1) j (stepDefect a i)) := by
            rw [linearSmoothing_add hL]
            congr 1
            exact map_sum (linearSmoothingAddHom hL j) _ _
        _ = _ := by
            rw [composedSmoothing_succ (Nat.zero_le j)]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [composedSmoothing_succ (by have := Finset.mem_range.mp hi; omega)]
    rw [h₁, h₂, Finset.sum_range_succ, composedSmoothing_self, add_assoc]
structure StepProperties (a : Edge L n k 0 → Matrices.ComplexMatrix2) (j : ℕ) : Prop where
  mem_polydisc : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
      nearIdentityPolydisc (polydiscRadius L) c
  form_mem : iteratedForm a (j + 1) ∈ complexEdgeForms L n k (j + 1)
  expForm_eq : expForm (iteratedForm a (j + 1)) =
    PeriodicLattice.complexBlockFieldAtLevel (j + 1) (remainderGaugeField a)
  defect_mem : stepDefect a j ∈ complexEdgeForms L n k (j + 1)
  defect_norm_le : ∀ c : Edge L n k (j + 1),
    Matrices.ComplexMatrix2.operatorNorm (stepDefect a j c) ≤
      stepRemainderConstant L * (maxOperatorNorm (iteratedForm a j)).toReal ^ 2
theorem stepProperties_of (hR : StepRemainder.QuadraticBound)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hE : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hLin : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : Edge L n k 0 → Matrices.ComplexMatrix2} {j : ℕ} (hj : j < k)
    (hform : iteratedForm a j ∈ complexEdgeForms L n k j)
    (hexp : expForm (iteratedForm a j) =
      PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a))
    (hsmall : maxOperatorNorm (iteratedForm a j) ≤ ENNReal.ofReal (stepRemainderRadius L / 2)) :
    StepProperties a j := by
  have hL13 : 13 ≤ L := hL.2
  have hone := fun (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) =>
    hR L hL n k j hn hj c hc (iteratedForm a j) hform hsmall
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  set V := PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) with hVdef
  have hpoly : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      V ∈ nearIdentityPolydisc (polydiscRadius L) c := fun c hc => by
    rw [← hexp]
    exact (hone c hc).1
  have hserve := fun (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) =>
    hρ.periodic n k j hn hj c hc
  have hsm : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.complexBlockAverage V c - 1) < 1 / 2 :=
    fun c hc => (hserve c hc).smoothing_near_one V (hpoly c hc)
  have hgrp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup := fun c hc =>
    (((hG.2 L k (j + 1) hL (by omega) (by omega)).1 n hn c V hc
      ((hserve c hc).subset_complexDomain (hpoly c hc))).2)
  have hW : ∀ c : Edge L n k (j + 1),
      PeriodicLattice.complexBlockFieldAtLevel (j + 1) (remainderGaugeField a) c =
        PeriodicLattice.complexBlockAverage V c := fun _ => rfl
  have hlog : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Matrices.ComplexMatrix2.logSeries
        (PeriodicLattice.complexBlockFieldAtLevel (j + 1) (remainderGaugeField a) c) ∈
          Matrices.ComplexMatrix2.traceless :=
    fun c hc => by
      rw [hW]
      exact (hG.1 _ (hgrp c hc) ((hsm c hc).trans (by norm_num))).2
  have hform' : iteratedForm a (j + 1) ∈ complexEdgeForms L n k (j + 1) :=
    logEdgeForm_mem (by omega) hn (by omega) hlog
  have hexplog : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Matrices.ComplexMatrix2.matExp (Complex.I • iteratedForm a (j + 1) c) =
        PeriodicLattice.complexBlockAverage V c :=
    fun c hc => by
      have h₁ : iteratedForm a (j + 1) c = Complex.I⁻¹ •
          Matrices.ComplexMatrix2.logSeries (PeriodicLattice.complexBlockAverage V c) :=
        logEdgeForm_of_positive _ hc
      have h₂ := (hE.2.2.2.1 (PeriodicLattice.complexBlockAverage V c - 1)
        ((hsm c hc).trans (by norm_num))).2.2.2.2
      rw [add_sub_cancel] at h₂
      rw [h₁, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, h₂]
  have hexp' : expForm (iteratedForm a (j + 1)) =
      PeriodicLattice.complexBlockFieldAtLevel (j + 1) (remainderGaugeField a) := by
    funext c
    by_cases hc : c.IsPositivelyOriented
    · rw [expForm_apply hform', hexplog c hc, hW]
    · have hc' : c.opposite.IsPositivelyOriented :=
        c.positive_or_opposite_positive.resolve_left hc
      have e₁ : expForm (iteratedForm a (j + 1)) c =
          (Matrices.ComplexMatrix2.matExp (Complex.I • iteratedForm a (j + 1) c.opposite) * 1)⁻¹ := by
        simp [expForm, PeriodicLattice.expTwist, hc]
      rw [e₁, hexplog _ hc', mul_one, hW]
      simp [PeriodicLattice.complexBlockAverage, hc, hc']
  have hQ : linearSmoothing L n k j (iteratedForm a j) ∈ complexEdgeForms L n k (j + 1) := by
    have h := (composedSmoothing_mem_and_norm_le (k := k) hLin hL hn (by omega) (i := j)
      (l := j + 1) (d := 1) rfl (by omega) hform).1
    rwa [composedSmoothing_succ le_rfl, composedSmoothing_self] at h
  have hrest : stepDefect a j ∈ complexEdgeForms L n k (j + 1) :=
    (complexEdgeForms L n k (j + 1)).sub_mem hform' hQ
  have hrest' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra (stepDefect a j) :=
    hrest
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      stepDefect a j c = logMeanDefect (iteratedForm a j) c :=
    fun c hc => by
      have h₁ : iteratedForm a (j + 1) c = Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
          (PeriodicLattice.complexBlockFieldAtLevel (j + 1) (remainderGaugeField a) c) :=
        logEdgeForm_of_positive _ hc
      simp only [stepDefect, Pi.sub_apply, logMeanDefect, h₁, hexp]
      rfl
  refine ⟨hpoly, hform', hexp', hrest, fun c => ?_⟩
  rcases c.positive_or_opposite_positive with hc | hc
  · rw [hpos c hc]
    exact (hone c hc).2
  · have h₁ : stepDefect a j c = -stepDefect a j c.opposite := by
      rw [hrest'.2 c, neg_neg]
    rw [h₁, Matrices.ComplexMatrix2.operatorNorm, norm_neg, hpos _ hc]
    exact (hone _ hc).2
end Iterates
section Induction
variable {L n k : ℕ}
structure LevelControl (a : Edge L n k 0 → Matrices.ComplexMatrix2) (α : ℝ) (j : ℕ) : Prop where
  form_mem : iteratedForm a j ∈ complexEdgeForms L n k j
  expForm_eq : expForm (iteratedForm a j) =
    PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a)
  norm_le : ∀ b : Edge L n k j,
    Matrices.ComplexMatrix2.operatorNorm (iteratedForm a j b) ≤ 10 * meshAt L k j * α
theorem operatorNorm_real_smul (r : ℝ) (X : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.operatorNorm (r • X) = |r| * Matrices.ComplexMatrix2.operatorNorm X := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.norm_real_smul_complexMatrix2 <;> assumption
theorem levelControl_zero {a : Edge L n k 0 → Matrices.ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0) (hfin : maxOperatorNorm a ≠ ∞) (hL : 0 < L) :
    LevelControl a (maxOperatorNorm a).toReal 0 := by
  have ha' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra a := ha
  have hη : 0 < meshAt L k 0 := meshAt_pos hL 0
  refine ⟨⟨fun b hb => ?_, fun b => ?_⟩, rfl, fun b => ?_⟩
  · change finestMesh L k • a b ∈ Matrices.ComplexMatrix2.traceless
    exact Matrices.ComplexMatrix2.traceless.smul_of_tower_mem (finestMesh L k) (ha'.1 b hb)
  · change finestMesh L k • a b.opposite = -(finestMesh L k • a b)
    rw [ha'.2 b, smul_neg]
  · change Matrices.ComplexMatrix2.operatorNorm (finestMesh L k • a b) ≤ _
    rw [operatorNorm_real_smul, finestMesh, abs_of_pos hη]
    have h₁ := operatorNorm_le_toReal_maxOperatorNorm hfin b
    have h₂ : 0 ≤ (maxOperatorNorm a).toReal := ENNReal.toReal_nonneg
    nlinarith
def admissibleRadius (L : ℕ) : ℝ :=
  min (polydiscRadius L / 41) ((L : ℝ) ^ 2 / (150 * stepRemainderConstant L))
theorem stepRemainderConstant_pos (hρ : 0 < polydiscRadius L) :
    0 < stepRemainderConstant L := by
  have hυ : 0 < stepRemainderRadius L := by
    unfold stepRemainderRadius
    positivity
  unfold stepRemainderConstant
  positivity
theorem formBounds_of_le (hR : StepRemainder.QuadraticBound)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hE : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hLin : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {a : Edge L n k 0 → Matrices.ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0)
    (hsup : maxOperatorNorm a ≤ ENNReal.ofReal (admissibleRadius L)) :
    FormConditions L n k a := by
  have hL13 : 13 ≤ L := hL.2
  have hL0 : 0 < L := by omega
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  have hρ0 := hρ.pos
  have hC := stepRemainderConstant_pos (L := L) hρ0
  have hs0 : 0 < admissibleRadius L := lt_min (by positivity) (by positivity)
  have hs1 : admissibleRadius L ≤ polydiscRadius L / 41 := min_le_left _ _
  have hs2 : admissibleRadius L ≤ (L : ℝ) ^ 2 / (150 * stepRemainderConstant L) :=
    min_le_right _ _
  have hfin : maxOperatorNorm a ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup
  set α := (maxOperatorNorm a).toReal with hαdef
  have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
  have hαρ : α ≤ admissibleRadius L := ENNReal.toReal_le_of_le_ofReal hs0.le hsup
  have hαC : 150 * stepRemainderConstant L * α ≤ (L : ℝ) ^ 2 := by
    have := hαρ.trans hs2
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have hsize : ∀ j ≤ k, 10 * meshAt L k j * α ≤ stepRemainderRadius L / 2 := by
    intro j hj
    have h₁ := meshAt_le_one (k := k) (by omega : 1 ≤ L) hj
    have h₂ := meshAt_pos (k := k) hL0 j
    have h₃ : meshAt L k j * α ≤ polydiscRadius L / 41 := by
      have : meshAt L k j * α ≤ 1 * α := by gcongr
      linarith
    unfold stepRemainderRadius
    linarith
  have hstep : ∀ j < k, LevelControl a α j → StepProperties a j := fun j hj g =>
    stepProperties_of hR hA hG hE hLin hL hn hj g.form_mem g.expForm_eq
      ((maxOperatorNorm_le_ofReal g.norm_le).trans (ENNReal.ofReal_le_ofReal (hsize j hj.le)))
  have key : ∀ j, j ≤ k → LevelControl a α j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      cases j with
      | zero => exact levelControl_zero ha hfin hL0
      | succ j =>
        have hs : ∀ i ≤ j, StepProperties a i := fun i hi =>
          hstep i (by omega) (ih i (by omega) (by omega))
        refine ⟨(hs j le_rfl).form_mem, (hs j le_rfl).expForm_eq, fun c => ?_⟩
        have hA0 := levelControl_zero (k := k) ha hfin hL0
        have h₀ : Matrices.ComplexMatrix2.operatorNorm
            (composedSmoothing L n k 0 (j + 1) (iteratedForm a 0) c) ≤
            5 * (L : ℝ) ^ (j + 1) * (meshAt L k 0 * α) := by
          refine composedSmoothing_apply_norm_le hLin hL hn hk (d := j + 1) (by omega) hj
            hA0.form_mem (by have := meshAt_pos (k := k) hL0 0; positivity) (fun b => ?_) c
          have h₁ : Matrices.ComplexMatrix2.operatorNorm (iteratedForm a 0 b) =
              meshAt L k 0 * Matrices.ComplexMatrix2.operatorNorm (a b) := by
            change Matrices.ComplexMatrix2.operatorNorm (finestMesh L k • a b) = _
            rw [operatorNorm_real_smul, finestMesh, abs_of_pos (meshAt_pos hL0 0)]
          rw [h₁]
          exact mul_le_mul_of_nonneg_left (operatorNorm_le_toReal_maxOperatorNorm hfin b)
            (meshAt_pos hL0 0).le
        have hterm : ∀ i ∈ Finset.range (j + 1),
            Matrices.ComplexMatrix2.operatorNorm
                (composedSmoothing L n k (i + 1) (j + 1) (stepDefect a i) c) ≤
              5 * (L : ℝ) ^ (j + 1 - (i + 1)) *
                (stepRemainderConstant L * (10 * meshAt L k i * α) ^ 2) := by
          intro i hi
          have hi' : i ≤ j := by have := Finset.mem_range.mp hi; omega
          have hgi := ih i (by omega) (by omega)
          have hM : 0 ≤ 10 * meshAt L k i * α := by
            have := meshAt_pos (k := k) hL0 i
            positivity
          refine composedSmoothing_apply_norm_le hLin hL hn hk (d := j + 1 - (i + 1)) (by omega) hj
            (hs i hi').defect_mem (by positivity) (fun b => ?_) c
          refine ((hs i hi').defect_norm_le b).trans ?_
          have h₁ : (maxOperatorNorm (iteratedForm a i)).toReal ≤ 10 * meshAt L k i * α :=
            ENNReal.toReal_le_of_le_ofReal hM (maxOperatorNorm_le_ofReal hgi.norm_le)
          have h₂ : (maxOperatorNorm (iteratedForm a i)).toReal ^ 2 ≤
              (10 * meshAt L k i * α) ^ 2 :=
            pow_le_pow_left₀ ENNReal.toReal_nonneg h₁ 2
          exact mul_le_mul_of_nonneg_left h₂ hC.le
        rw [congrFun (iteratedForm_eq_sum hL0 a (j + 1)) c, Pi.add_apply, Finset.sum_apply]
        calc Matrices.ComplexMatrix2.operatorNorm
              (composedSmoothing L n k 0 (j + 1) (iteratedForm a 0) c +
                ∑ i ∈ Finset.range (j + 1),
                  composedSmoothing L n k (i + 1) (j + 1) (stepDefect a i) c)
            ≤ Matrices.ComplexMatrix2.operatorNorm
                  (composedSmoothing L n k 0 (j + 1) (iteratedForm a 0) c) +
                ∑ i ∈ Finset.range (j + 1), Matrices.ComplexMatrix2.operatorNorm
                  (composedSmoothing L n k (i + 1) (j + 1) (stepDefect a i) c) :=
              (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
          _ ≤ 5 * (L : ℝ) ^ (j + 1) * (meshAt L k 0 * α) +
                ∑ i ∈ Finset.range (j + 1), 5 * (L : ℝ) ^ (j + 1 - (i + 1)) *
                  (stepRemainderConstant L * (10 * meshAt L k i * α) ^ 2) :=
              add_le_add h₀ (Finset.sum_le_sum hterm)
          _ ≤ 10 * meshAt L k (j + 1) * α :=
              geometric_recursion_le (by omega) hj hα0 hC.le hαC
  have hV : ∀ j ≤ k, ∀ b : Edge L n k j,
      Matrices.ComplexMatrix2.operatorNorm
          (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) b - 1) ≤
        20 * meshAt L k j * α := by
    intro j hj b
    have g := key j hj
    have hb := g.norm_le b
    have h₁ := meshAt_le_one (k := k) (by omega : 1 ≤ L) hj
    have h₂ := meshAt_pos (k := k) hL0 j
    have hρ1 := hρ.le_one
    have hsmall : Matrices.ComplexMatrix2.operatorNorm (iteratedForm a j b) ≤ 1 := by
      have h₃ : meshAt L k j * α ≤ 1 * α := by gcongr
      have := hsize j hj
      unfold stepRemainderRadius at this
      linarith
    have hn0 : 0 ≤ Matrices.ComplexMatrix2.operatorNorm (iteratedForm a j b) := norm_nonneg _
    have hI : Matrices.ComplexMatrix2.operatorNorm (Complex.I • iteratedForm a j b) =
        Matrices.ComplexMatrix2.operatorNorm (iteratedForm a j b) := by
      rw [Matrices.ComplexMatrix2.operatorNorm, norm_smul, Complex.norm_I, one_mul]
    rw [← g.expForm_eq, expForm_apply g.form_mem]
    have h₄ := (hE.1 (Complex.I • iteratedForm a j b)).2
    rw [hI] at h₄
    have h₅ := Real.abs_exp_sub_one_le
      (x := Matrices.ComplexMatrix2.operatorNorm (iteratedForm a j b))
      (by rwa [abs_of_nonneg hn0])
    rw [abs_of_nonneg hn0] at h₅
    have h₆ := (le_abs_self _).trans h₅
    linarith
  refine ⟨fun j hj => ?_, fun j hj c hc => ?_, hV, fun j hj b => ?_⟩
  · rw [← (key j hj).expForm_eq]
    exact expForm_mem_fieldsIn hE (key j hj).form_mem
  · exact (hstep j hj (key j hj.le)).mem_polydisc c hc
  · refine (hV j hj b).trans_lt ?_
    have h₁ := meshAt_le_one (k := k) (by omega : 1 ≤ L) hj
    have h₂ := meshAt_pos (k := k) hL0 j
    have h₃ : meshAt L k j * α ≤ 1 * α := by gcongr
    linarith
end Induction
theorem smallRadiusAdmissible_holds (hR : StepRemainder.QuadraticBound)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hE : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hLin : TwoLevelMaps.Statement) : SmallRadiusAdmissible := by
  intro L hL
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  have hρ0 := hρ.pos
  have hρ1 := hρ.le_one
  have hL0 : (0 : ℝ) < L := by
    have : 13 ≤ L := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hC := stepRemainderConstant_pos (L := L) hρ0
  have hs : RadiusIsAdmissible L (admissibleRadius L) := by
    refine ⟨lt_min (by positivity) (by positivity), ?_, fun n hn k hk a ha hsup =>
      formBounds_of_le hR hA hG hE hLin hL hn hk ha hsup⟩
    have : admissibleRadius L ≤ polydiscRadius L / 41 := min_le_left _ _
    linarith
  exact Classical.epsilon_spec ⟨admissibleRadius L, hs⟩
end YangMills.Construction.Tower.IteratedMeanBounds
end
