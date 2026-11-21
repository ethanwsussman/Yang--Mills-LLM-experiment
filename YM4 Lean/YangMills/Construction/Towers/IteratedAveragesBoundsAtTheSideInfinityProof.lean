import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.BoundsOfTheIteratedAveragesOnASideProof
import YangMills.Construction.Towers.IteratedAveragesBoundsAtTheSideInfinity
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.OneStepRemainderOfTheIteratedAveragesAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterBounds
open Matrices Matrices.ComplexMatrix2
open YangMills.Construction.Tower.FullSpace.TwoLevelMaps (linearSmoothingBetween)
theorem maxOperatorNorm_le_ofReal {ι : Type*} {f : ι → ComplexMatrix2} {M : ℝ}
    (h : ∀ i, operatorNorm (f i) ≤ M) :
    maxOperatorNorm f ≤ ENNReal.ofReal M := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.maxOperatorNorm_le_ofReal <;> assumption
theorem operatorNorm_le_toReal {ι : Type*} {f : ι → ComplexMatrix2} (h : maxOperatorNorm f ≠ ∞)
    (i : ι) : operatorNorm (f i) ≤ (maxOperatorNorm f).toReal := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.operatorNorm_le_toReal_maxOperatorNorm <;> assumption
section Numbers
variable {L k : ℕ}
theorem meshAt_pos (hL : 0 < L) (j : ℕ) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_le_one (hL : 1 ≤ L) {j : ℕ} (hj : j ≤ k) : meshAt L k j ≤ 1 := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.meshAt_le_one <;> assumption
theorem geometric_recursion_le (hL : 3 ≤ L) {j : ℕ} (hj : j ≤ k) {α C : ℝ} (hα : 0 ≤ α)
    (hC : 0 ≤ C) (h : 150 * C * α ≤ (L : ℝ) ^ 2) :
    5 * (L : ℝ) ^ j * (meshAt L k 0 * α) +
        ∑ i ∈ Finset.range j,
          5 * (L : ℝ) ^ (j - (i + 1)) * (C * (10 * meshAt L k i * α) ^ 2) ≤
      10 * meshAt L k j * α := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.geometric_recursion_le <;> assumption
end Numbers
section Links
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
end Links
section Linear
variable {L k : ℕ}
theorem cubeVertices_finite (L : ℕ) {a a' : ℝ} (y : InfiniteLattice.LatticePoint a) :
    (cubeVertices L a' y).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.cubeVertices_finite <;> assumption
theorem sumAlong_add {a : ℝ} (A A' : InfiniteLattice.Link a → ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    sumAlong (A + A') Γ = sumAlong A Γ + sumAlong A' Γ := by
  induction Γ with
  | nil => simp [sumAlong]
  | cons b Γ ih =>
    simp only [sumAlong, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
    rw [ih]
    abel
theorem contourAverage_add (L : ℕ) {a a' : ℝ} (A A' : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (A + A') y x = _root_.YangMills.Construction.Tower.FullSpace.contourAverage L A y x + _root_.YangMills.Construction.Tower.FullSpace.contourAverage L A' y x := by
  simp only [_root_.YangMills.Construction.Tower.FullSpace.contourAverage, sumAlong_add, Finset.sum_add_distrib, smul_add]
abbrev stepSmoothing (L k j : ℕ) : (Edge L k j → ComplexMatrix2) → Edge L k (j + 1) → ComplexMatrix2 :=
  linearSmoothing L
theorem stepSmoothing_add (j : ℕ) (A A' : Edge L k j → ComplexMatrix2) :
    stepSmoothing L k j (A + A') = stepSmoothing L k j A + stepSmoothing L k j A' := by
  funext c
  simp only [stepSmoothing, linearSmoothing, Pi.add_apply]
  rw [← smul_add, ← finsum_mem_add_distrib (cubeVertices_finite L _)]
  congr 1
  refine finsum_mem_congr rfl fun x _ => ?_
  rw [contourAverage_add, sumAlong_add, contourAverage_add]
  abel
def stepSmoothingHom (L k j : ℕ) :
    (Edge L k j → ComplexMatrix2) →+ (Edge L k (j + 1) → ComplexMatrix2) :=
  AddMonoidHom.mk' (stepSmoothing L k j) (stepSmoothing_add j)
def smoothingFromTo (L k i l : ℕ) : (Edge L k i → ComplexMatrix2) → Edge L k l → ComplexMatrix2 :=
  open Classical in
  if h : i ≤ l then linearSmoothingBetween L k h else 0
theorem smoothingFromTo_self (i : ℕ) (B : Edge L k i → ComplexMatrix2) :
    smoothingFromTo L k i i B = B := by
  simp [smoothingFromTo, linearSmoothingBetween, levelwiseComposition_self]
theorem smoothingFromTo_succ {i l : ℕ} (h : i ≤ l) (B : Edge L k i → ComplexMatrix2) :
    smoothingFromTo L k i (l + 1) B = stepSmoothing L k l (smoothingFromTo L k i l B) := by
  simp only [smoothingFromTo, dif_pos h, dif_pos (Nat.le_succ_of_le h), linearSmoothingBetween]
  rw [levelwiseComposition_succ _ h]
  rfl
theorem smoothingFromTo_mem_and_le (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {i l d : ℕ} (hd : i + d = l)
    (hl : l ≤ k) {B : Edge L k i → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k i)) :
    smoothingFromTo L k i l B ∈ complexEdgeForms (meshAt L k l) ∧
      maxOperatorNorm (smoothingFromTo L k i l B) ≤ 5 * (L : ℝ≥0∞) ^ d * maxOperatorNorm B := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · obtain rfl : i = l := by omega
    rw [smoothingFromTo_self]
    refine ⟨hB, ?_⟩
    calc maxOperatorNorm B = 1 * maxOperatorNorm B := (one_mul _).symm
      _ ≤ 5 * (L : ℝ≥0∞) ^ 0 * maxOperatorNorm B := by
        gcongr
        norm_num
  · obtain rfl : i = l - d := by omega
    have h := ((hLin L hL k hk).2.2.1) d l (by omega) (by omega) hl
    have e : smoothingFromTo L k (l - d) l B = linearSmoothingBetween L k (Nat.sub_le l d) B := by
      simp only [smoothingFromTo, dif_pos (Nat.sub_le l d)]
    rw [e]
    exact ⟨h.linearSmoothing_mapsTo_surjOn.1 hB, h.linearSmoothing_norm_le B hB⟩
theorem smoothingFromTo_apply_le (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {i l d : ℕ} (hd : i + d = l)
    (hl : l ≤ k) {B : Edge L k i → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k i))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ b, operatorNorm (B b) ≤ M) (c : Edge L k l) :
    operatorNorm (smoothingFromTo L k i l B c) ≤ 5 * (L : ℝ) ^ d * M := by
  have h₁ : ENNReal.ofReal (operatorNorm (smoothingFromTo L k i l B c)) ≤
      maxOperatorNorm (smoothingFromTo L k i l B) :=
    le_iSup (fun c => ENNReal.ofReal (operatorNorm (smoothingFromTo L k i l B c))) c
  have h₂ : maxOperatorNorm (smoothingFromTo L k i l B) ≤ ENNReal.ofReal (5 * (L : ℝ) ^ d * M) := by
    refine (smoothingFromTo_mem_and_le hLin hL hk hd hl hB).2.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    have h₃ : (5 : ℝ≥0∞) = ENNReal.ofReal 5 := by simp
    rw [← h₃]
    gcongr
    exact maxOperatorNorm_le_ofReal hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h₁.trans h₂)
end Linear
section Forms
variable {L k j : ℕ}
theorem expForm_apply {A : Edge L k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) :
    expForm A b = matExp (Complex.I • A b) := by
  have hA' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra A := hA
  by_cases hb : b.IsPositivelyOriented
  · simp [expForm, expTwist, hb]
  · simp only [expForm, expTwist, if_neg hb, mul_one, Pi.one_apply]
    rw [hA'.2 b, smul_neg, ← Matrix.exp_neg, neg_neg]
theorem fullTrace_of_mem {A : Edge L k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) : fullTrace (A b) = 0 := by
  have hA' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra A := hA
  rcases isPositivelyOriented_or_opposite b with hb | hb
  · exact hA'.1 b hb
  · have h : fullTrace (A b.opposite) = 0 := hA'.1 _ hb
    rw [hA'.2 b] at h
    simpa [fullTrace, Matrix.trace_neg] using h
theorem expForm_mem_fieldsValuedIn (hE : ExpLogEstimates)
    {A : Edge L k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms (meshAt L k j)) :
    expForm A ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
  have hA' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra A := hA
  refine ⟨fun b => ?_, fun b => ?_⟩
  · rw [expForm_apply hA]
    change (matExp (Complex.I • A b)).det = 1
    rw [hE.2.2.2.2.2.1]
    have h : fullTrace (Complex.I • A b) = 0 := by
      simp only [fullTrace, Matrix.trace_smul]
      rw [show Matrix.trace (A b) = 0 from fullTrace_of_mem hA b, smul_zero]
    rw [h, Complex.exp_zero]
  · rw [expForm_apply hA, expForm_apply hA, hA'.2 b, smul_neg]
    exact Matrix.exp_neg _
def logOddForm (V : Edge L k j → ComplexMatrix2) : Edge L k j → ComplexMatrix2 :=
  extendOddly fun b => Complex.I⁻¹ • logSeries (V b)
theorem logOddForm_of_pos (V : Edge L k j → ComplexMatrix2) {b : Edge L k j}
    (hb : b.IsPositivelyOriented) : logOddForm V b = Complex.I⁻¹ • logSeries (V b) := by
  simp [logOddForm, extendOddly, hb]
theorem logOddForm_mem (hL : 0 < L) {V : Edge L k j → ComplexMatrix2}
    (hV : ∀ b : Edge L k j, b.IsPositivelyOriented → logSeries (V b) ∈ traceless) :
    logOddForm V ∈ complexEdgeForms (meshAt L k j) := by
  have ha : 0 < meshAt L k j := meshAt_pos hL j
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [logOddForm_of_pos V hb]
    exact traceless.smul_mem _ (hV b hb)
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := not_isPositivelyOriented_opposite ha hb
      simp only [logOddForm, extendOddly, if_neg hb', if_pos hb]
      rfl
    · have hb' : b.opposite.IsPositivelyOriented := (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [logOddForm, extendOddly, if_neg hb, if_pos hb', neg_neg]
end Forms
section Iterates
variable {L k : ℕ}
def levelForm (a : Edge L k 0 → ComplexMatrix2) : (j : ℕ) → Edge L k j → ComplexMatrix2
  | 0 => scaledRemainderForm a
  | j + 1 => logOddForm (complexIter L k (j + 1) (remainderGaugeField a))
def stepDefect (a : Edge L k 0 → ComplexMatrix2) (j : ℕ) : Edge L k (j + 1) → ComplexMatrix2 :=
  levelForm a (j + 1) - stepSmoothing L k j (levelForm a j)
theorem levelForm_eq_sum (hL : 0 < L) (a : Edge L k 0 → ComplexMatrix2) (j : ℕ) :
    levelForm a j = smoothingFromTo L k 0 j (levelForm a 0) +
      ∑ i ∈ Finset.range j, smoothingFromTo L k (i + 1) j (stepDefect a i) := by
  induction j with
  | zero => simp [smoothingFromTo_self]
  | succ j ih =>
    have h₁ : levelForm a (j + 1) = stepSmoothing L k j (levelForm a j) + stepDefect a j := by
      simp [stepDefect]
    have h₂ : stepSmoothing L k j (levelForm a j) =
        smoothingFromTo L k 0 (j + 1) (levelForm a 0) +
          ∑ i ∈ Finset.range j, smoothingFromTo L k (i + 1) (j + 1) (stepDefect a i) := by
      calc stepSmoothing L k j (levelForm a j)
          = stepSmoothing L k j (smoothingFromTo L k 0 j (levelForm a 0) +
              ∑ i ∈ Finset.range j, smoothingFromTo L k (i + 1) j (stepDefect a i)) := congrArg _ ih
        _ = stepSmoothing L k j (smoothingFromTo L k 0 j (levelForm a 0)) +
              ∑ i ∈ Finset.range j,
                stepSmoothing L k j (smoothingFromTo L k (i + 1) j (stepDefect a i)) := by
            rw [stepSmoothing_add]
            congr 1
            exact map_sum (stepSmoothingHom L k j) _ _
        _ = _ := by
            rw [smoothingFromTo_succ (Nat.zero_le j)]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [smoothingFromTo_succ (by have := Finset.mem_range.mp hi; omega)]
    rw [h₁, h₂, Finset.sum_range_succ, smoothingFromTo_self, add_assoc]
structure StepConsequences (a : Edge L k 0 → ComplexMatrix2) (j : ℕ) : Prop where
  inPolydisc : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    complexIter L k j (remainderGaugeField a) ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c
  isForm : levelForm a (j + 1) ∈ complexEdgeForms (meshAt L k (j + 1))
  exp_eq : expForm (levelForm a (j + 1)) =
    complexIter L k (j + 1) (remainderGaugeField a)
  defect_mem : stepDefect a j ∈ complexEdgeForms (meshAt L k (j + 1))
  defect_le : ∀ c : Edge L k (j + 1), operatorNorm (stepDefect a j c) ≤
    stepRemainderConstant L * (maxOperatorNorm (levelForm a j)).toReal ^ 2
theorem stepConsequences (hR : StepRemainderAtInfiniteSide)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hE : ExpLogEstimates)
    (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {a : Edge L k 0 → ComplexMatrix2} {j : ℕ}
    (hj : j < k)
    (hform : levelForm a j ∈ complexEdgeForms (meshAt L k j))
    (hexp : expForm (levelForm a j) =
      complexIter L k j (remainderGaugeField a))
    (hsmall : maxOperatorNorm (levelForm a j) ≤ ENNReal.ofReal (stepRemainderRadius L / 2)) :
    StepConsequences a j := by
  have hL13 : 13 ≤ L := hL.2
  have hone := fun (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    hR L hL k j hj c hc (levelForm a j) hform hsmall
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  set V := complexIter L k j (remainderGaugeField a) with hVdef
  have hpoly : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := fun c hc => by
    rw [← hexp]
    exact (hone c hc).1
  have hserve := fun (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    hρ.fullSpace k j hj c hc
  have hsm : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      operatorNorm (complexSmoothing L V c - 1) < 1 / 2 := fun c hc =>
    (hserve c hc).smoothing_near_one V (hpoly c hc)
  have hgrp : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      complexSmoothing L V c ∈ PeriodicLattice.complexGaugeGroup := fun c hc =>
    (((hG.2 L k (j + 1) hL (by omega) (by omega)).2 c V hc
      ((hserve c hc).subset_complexDomain (hpoly c hc))).2)
  have hW : ∀ c : Edge L k (j + 1),
      complexIter L k (j + 1) (remainderGaugeField a) c =
        complexSmoothing L V c := fun _ => rfl
  have hlog : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      logSeries (complexIter L k (j + 1) (remainderGaugeField a) c) ∈ traceless :=
    fun c hc => by
      rw [hW]
      exact (hG.1 _ (hgrp c hc) ((hsm c hc).trans (by norm_num))).2
  have hform' : levelForm a (j + 1) ∈ complexEdgeForms (meshAt L k (j + 1)) :=
    logOddForm_mem (by omega) hlog
  have hexplog : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      matExp (Complex.I • levelForm a (j + 1) c) = complexSmoothing L V c :=
    fun c hc => by
      have h₁ : levelForm a (j + 1) c = Complex.I⁻¹ •
          logSeries (complexSmoothing L V c) := logOddForm_of_pos _ hc
      have h₂ := (hE.2.2.2.1 (complexSmoothing L V c - 1)
        ((hsm c hc).trans (by norm_num))).2.2.2.2
      rw [add_sub_cancel] at h₂
      rw [h₁, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, h₂]
  have hexp' : expForm (levelForm a (j + 1)) =
      complexIter L k (j + 1) (remainderGaugeField a) := by
    funext c
    by_cases hc : c.IsPositivelyOriented
    · rw [expForm_apply hform', hexplog c hc, hW]
    · have hc' : c.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite c).resolve_left hc
      have e₁ : expForm (levelForm a (j + 1)) c =
          (matExp (Complex.I • levelForm a (j + 1) c.opposite) * 1)⁻¹ := by
        simp [expForm, expTwist, hc]
      rw [e₁, hexplog _ hc', mul_one, hW]
      simp [complexSmoothing, hc, hc']
  have hQ : stepSmoothing L k j (levelForm a j) ∈ complexEdgeForms (meshAt L k (j + 1)) := by
    have h := (smoothingFromTo_mem_and_le (k := k) hLin hL (by omega) (i := j) (l := j + 1)
      (d := 1) rfl (by omega) hform).1
    rwa [smoothingFromTo_succ le_rfl, smoothingFromTo_self] at h
  have hrest : stepDefect a j ∈ complexEdgeForms (meshAt L k (j + 1)) :=
    (complexEdgeForms (meshAt L k (j + 1))).sub_mem hform' hQ
  have hrest' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra (stepDefect a j) := hrest
  have hpos : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → stepDefect a j c =
      Complex.I⁻¹ • logSeries (smoothingMap L k j (expForm (levelForm a j)) c) -
        linearSmoothing L (levelForm a j) c :=
    fun c hc => by
      have h₁ : levelForm a (j + 1) c = Complex.I⁻¹ • logSeries
          (complexIter L k (j + 1) (remainderGaugeField a) c) :=
        logOddForm_of_pos _ hc
      simp only [stepDefect, Pi.sub_apply, h₁, hexp]
      rfl
  refine ⟨hpoly, hform', hexp', hrest, fun c => ?_⟩
  rcases (isPositivelyOriented_or_opposite c) with hc | hc
  · rw [hpos c hc]
    exact (hone c hc).2
  · have h₁ : stepDefect a j c = -stepDefect a j c.opposite := by
      rw [hrest'.2 c, neg_neg]
    rw [h₁, operatorNorm, norm_neg, hpos _ hc]
    exact (hone _ hc).2
end Iterates
section Induction
variable {L k : ℕ}
structure LevelControl (a : Edge L k 0 → ComplexMatrix2) (α : ℝ) (j : ℕ) : Prop where
  isForm : levelForm a j ∈ complexEdgeForms (meshAt L k j)
  exp_eq : expForm (levelForm a j) = complexIter L k j (remainderGaugeField a)
  norm_le : ∀ b : Edge L k j, operatorNorm (levelForm a j b) ≤ 10 * meshAt L k j * α
theorem operatorNorm_real_smul (r : ℝ) (X : ComplexMatrix2) :
    operatorNorm (r • X) = |r| * operatorNorm X := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.operatorNorm_real_smul <;> assumption
theorem levelControl_zero {a : Edge L k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms (meshAt L k 0))
    (hfin : maxOperatorNorm a ≠ ∞) (hL : 0 < L) : LevelControl a (maxOperatorNorm a).toReal 0 := by
  have ha' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra a := ha
  have hη : 0 < meshAt L k 0 := meshAt_pos hL 0
  refine ⟨⟨fun b hb => ?_, fun b => ?_⟩, rfl, fun b => ?_⟩
  · change finestMesh L k • a b ∈ traceless
    exact traceless.smul_of_tower_mem (finestMesh L k) (ha'.1 b hb)
  · change finestMesh L k • a b.opposite = -(finestMesh L k • a b)
    rw [ha'.2 b, smul_neg]
  · change operatorNorm (finestMesh L k • a b) ≤ _
    rw [operatorNorm_real_smul, finestMesh, abs_of_pos hη]
    have h₁ := operatorNorm_le_toReal hfin b
    have h₂ : 0 ≤ (maxOperatorNorm a).toReal := ENNReal.toReal_nonneg
    nlinarith
def admissibleRadius (L : ℕ) : ℝ :=
  min (polydiscRadius L / 41) ((L : ℝ) ^ 2 / (150 * stepRemainderConstant L))
theorem stepRemainderConstant_pos (hρ : 0 < polydiscRadius L) :
    0 < stepRemainderConstant L := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.stepRemainderConstant_pos <;> assumption
theorem boundsAtForm_of_small (hR : StepRemainderAtInfiniteSide)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hE : ExpLogEstimates)
    (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {a : Edge L k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms (meshAt L k 0))
    (hsup : maxOperatorNorm a ≤ ENNReal.ofReal (admissibleRadius L)) :
    BoundsAtForm L k a := by
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
  have hstep : ∀ j < k, LevelControl a α j → StepConsequences a j := fun j hj g =>
    stepConsequences hR hA hG hE hLin hL hj g.isForm g.exp_eq
      ((maxOperatorNorm_le_ofReal g.norm_le).trans (ENNReal.ofReal_le_ofReal (hsize j hj.le)))
  have key : ∀ j, j ≤ k → LevelControl a α j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      cases j with
      | zero => exact levelControl_zero ha hfin hL0
      | succ j =>
        have hs : ∀ i ≤ j, StepConsequences a i := fun i hi =>
          hstep i (by omega) (ih i (by omega) (by omega))
        refine ⟨(hs j le_rfl).isForm, (hs j le_rfl).exp_eq, fun c => ?_⟩
        have hA0 := levelControl_zero (k := k) ha hfin hL0
        have h₀ : operatorNorm (smoothingFromTo L k 0 (j + 1) (levelForm a 0) c) ≤
            5 * (L : ℝ) ^ (j + 1) * (meshAt L k 0 * α) := by
          refine smoothingFromTo_apply_le hLin hL hk (d := j + 1) (by omega) hj hA0.isForm
            (by have := meshAt_pos (k := k) hL0 0; positivity) (fun b => ?_) c
          have h₁ : operatorNorm (levelForm a 0 b) = meshAt L k 0 * operatorNorm (a b) := by
            change operatorNorm (finestMesh L k • a b) = _
            rw [operatorNorm_real_smul, finestMesh, abs_of_pos (meshAt_pos hL0 0)]
          rw [h₁]
          exact mul_le_mul_of_nonneg_left (operatorNorm_le_toReal hfin b)
            (meshAt_pos hL0 0).le
        have hterm : ∀ i ∈ Finset.range (j + 1),
            operatorNorm (smoothingFromTo L k (i + 1) (j + 1) (stepDefect a i) c) ≤
              5 * (L : ℝ) ^ (j + 1 - (i + 1)) *
                (stepRemainderConstant L * (10 * meshAt L k i * α) ^ 2) := by
          intro i hi
          have hi' : i ≤ j := by have := Finset.mem_range.mp hi; omega
          have hgi := ih i (by omega) (by omega)
          have hM : 0 ≤ 10 * meshAt L k i * α := by
            have := meshAt_pos (k := k) hL0 i
            positivity
          refine smoothingFromTo_apply_le hLin hL hk (d := j + 1 - (i + 1)) (by omega) hj
            (hs i hi').defect_mem (by positivity) (fun b => ?_) c
          refine ((hs i hi').defect_le b).trans ?_
          have h₁ : (maxOperatorNorm (levelForm a i)).toReal ≤ 10 * meshAt L k i * α :=
            ENNReal.toReal_le_of_le_ofReal hM (maxOperatorNorm_le_ofReal hgi.norm_le)
          have h₂ : (maxOperatorNorm (levelForm a i)).toReal ^ 2 ≤ (10 * meshAt L k i * α) ^ 2 :=
            pow_le_pow_left₀ ENNReal.toReal_nonneg h₁ 2
          exact mul_le_mul_of_nonneg_left h₂ hC.le
        rw [congrFun (levelForm_eq_sum hL0 a (j + 1)) c, Pi.add_apply, Finset.sum_apply]
        calc operatorNorm (smoothingFromTo L k 0 (j + 1) (levelForm a 0) c +
                ∑ i ∈ Finset.range (j + 1), smoothingFromTo L k (i + 1) (j + 1) (stepDefect a i) c)
            ≤ operatorNorm (smoothingFromTo L k 0 (j + 1) (levelForm a 0) c) +
                ∑ i ∈ Finset.range (j + 1),
                  operatorNorm (smoothingFromTo L k (i + 1) (j + 1) (stepDefect a i) c) :=
              (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
          _ ≤ 5 * (L : ℝ) ^ (j + 1) * (meshAt L k 0 * α) +
                ∑ i ∈ Finset.range (j + 1), 5 * (L : ℝ) ^ (j + 1 - (i + 1)) *
                  (stepRemainderConstant L * (10 * meshAt L k i * α) ^ 2) :=
              add_le_add h₀ (Finset.sum_le_sum hterm)
          _ ≤ 10 * meshAt L k (j + 1) * α :=
              geometric_recursion_le (by omega) hj hα0 hC.le hαC
  have hV : ∀ j ≤ k, ∀ b : Edge L k j,
      operatorNorm (complexIter L k j (remainderGaugeField a) b - 1) ≤
        20 * meshAt L k j * α := by
    intro j hj b
    have g := key j hj
    have hb := g.norm_le b
    have h₁ := meshAt_le_one (k := k) (by omega : 1 ≤ L) hj
    have h₂ := meshAt_pos (k := k) hL0 j
    have hρ1 := hρ.le_one
    have hsmall : operatorNorm (levelForm a j b) ≤ 1 := by
      have h₃ : meshAt L k j * α ≤ 1 * α := by gcongr
      have := hsize j hj
      unfold stepRemainderRadius at this
      linarith
    have hn0 : 0 ≤ operatorNorm (levelForm a j b) := norm_nonneg _
    have hI : operatorNorm (Complex.I • levelForm a j b) = operatorNorm (levelForm a j b) := by
      rw [operatorNorm, norm_smul, Complex.norm_I, one_mul]
    rw [← g.exp_eq, expForm_apply g.isForm]
    have h₄ := (hE.1 (Complex.I • levelForm a j b)).2
    rw [hI] at h₄
    have h₅ := Real.abs_exp_sub_one_le (x := operatorNorm (levelForm a j b))
      (by rwa [abs_of_nonneg hn0])
    rw [abs_of_nonneg hn0] at h₅
    have h₆ := (le_abs_self _).trans h₅
    linarith
  refine ⟨fun j hj => ?_, fun j hj c hc => ?_, hV, fun j hj b => ?_⟩
  · rw [← (key j hj).exp_eq]
    exact expForm_mem_fieldsValuedIn hE (key j hj).isForm
  · exact (hstep j hj (key j hj.le)).inPolydisc c hc
  · refine (hV j hj b).trans_lt ?_
    have h₁ := meshAt_le_one (k := k) (by omega : 1 ≤ L) hj
    have h₂ := meshAt_pos (k := k) hL0 j
    have h₃ : meshAt L k j * α ≤ 1 * α := by gcongr
    linarith
end Induction
theorem uniformIterBounds_holds (hR : StepRemainderAtInfiniteSide)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hE : ExpLogEstimates)
    (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement) : UniformIterBounds := by
  intro L hL
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  have hρ0 := hρ.pos
  have hρ1 := hρ.le_one
  have hL0 : (0 : ℝ) < L := by
    have : 13 ≤ L := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hC := stepRemainderConstant_pos (L := L) hρ0
  refine ⟨admissibleRadius L, lt_min (by positivity) (by positivity), ?_, fun k hk a ha hsup =>
    boundsAtForm_of_small hR hA hG hE hLin hL hk ha hsup⟩
  have : admissibleRadius L ≤ polydiscRadius L / 41 := min_le_left _ _
  linarith
end YangMills.Construction.Tower.FullSpace.IterBounds
end
