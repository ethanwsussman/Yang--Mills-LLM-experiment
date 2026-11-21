import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctions
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.MotionsTensorProductsTranslationsAndTheReflection
import YangMills.Construction.Continuum.PassageFromTuplesToSchwartzFunctions
import YangMills.Construction.Continuum.TermsBoundValuesOnTuplesAndApproximationForTheFormOnAdmissibleSequences
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
namespace YangMills.Construction
namespace AdmissibleClustering
open ConfigSpace
open ConfigSpace.UpperCombination (linComb lengthPart)
open AdmissibleForm (HasGrowthBound ListMatchesFamily reflectedPairValue)
open ReflectionPositivityFromValues (AgreesOnTensors)
open SchwartzAxioms (seminormAt)
open TupleLists (toList ofList)
open SeparatedTuples (SepTuple push pushList)
section Degrees
variable {S : FlatSequence}
theorem evalAt_cast (S : FlatSequence) {a b : ℕ} (e : a = b) (f : FnOrScalar a) :
    S.evalAt (e ▸ f : FnOrScalar b) = S.evalAt f := by
  subst e
  rfl
theorem evalAt_zeroOfDegree (hS : IsLinearFunctionalSeq S) (n : ℕ) :
    S.evalAt (zeroOfDegree n) = 0 := by
  cases n with
  | zero =>
    have h0 : zeroOfDegree 0 ∈ flatOffDiagonalAt 0 := Set.mem_univ _
    rw [FlatSequence.evalAt_of_mem S h0]
    exact hS.1 ⟨_, h0⟩
  | succ p =>
    by_cases h : zeroOfDegree (p + 1) ∈ flatOffDiagonalAt (p + 1)
    · rw [FlatSequence.evalAt_of_mem S h]
      have e := hS.2 p 0 0 ⟨_, h⟩ ⟨_, h⟩ ⟨_, h⟩ (by
        funext x
        show (0 : ℂ) = (0 : ℂ) • (0 : ℂ) + (0 : ℂ) • (0 : ℂ)
        simp)
      have e' : S (p + 1) ⟨_, h⟩ = _ := e
      simpa using e'
    · rw [FlatSequence.evalAt, dif_neg h]
theorem smulAt_one {n : ℕ} (g : FnOrScalar n) : smulAt 1 g = g := by
  cases n with
  | zero => exact (fun a : ℂ => one_mul a) g
  | succ n =>
    funext y
    show (1 : ℂ) * g y = g y
    simp
theorem flipConjAt_zero (n : ℕ) : flipConjAt (zeroOfDegree n) = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.flipConjAt_zeroOfDegree <;> assumption
theorem tensorAt_zero_left {a b : ℕ} (g : FnOrScalar b) :
    tensorAt (zeroOfDegree a) g = zeroOfDegree (a + b) := by apply _root_.YangMills.Construction.ConditionDomains.tensorAt_zero_left <;> assumption
theorem tensorAt_zero_right {a b : ℕ} (f : FnOrScalar a) :
    tensorAt f (zeroOfDegree b) = zeroOfDegree (a + b) := by apply _root_.YangMills.Construction.ConditionDomains.tensorAt_zero_right <;> assumption
theorem reflectionPairing_eq_finite_sum (φ ψ : (a : ℕ) → FnOrScalar a) (N : ℕ)
    (hz : ∀ a b, N < a ∨ N < b →
      S.evalAt (tensorAt (flipConjAt (φ a)) (ψ b)) = 0) :
    S.reflectionPairing φ ψ =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        S.evalAt (tensorAt (flipConjAt (φ a)) (ψ b)) := by
  have hs : (Function.support fun p : ℕ × ℕ =>
      S.evalAt (tensorAt (flipConjAt (φ p.1)) (ψ p.2))) ⊆
      ↑(Finset.range (N + 1) ×ˢ Finset.range (N + 1)) := by
    rintro ⟨a, b⟩ hp
    by_contra hn
    refine hp (hz a b ?_)
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, not_and_or] at hn
    omega
  rw [FlatSequence.reflectionPairing, finsum_eq_sum_of_support_subset _ hs,
    Finset.sum_product]
end Degrees
section Cutoff
variable {S : FlatSequence}
def truncate (S : FlatSequence) (N : ℕ) : FlatSequence :=
  fun n φ => if n ≤ N then S n φ else 0
theorem evalAt_truncate (S : FlatSequence) (N : ℕ) {n : ℕ} (f : FnOrScalar n)
    (h : n ≤ N) : (truncate S N).evalAt f = S.evalAt f := by
  by_cases hf : f ∈ flatOffDiagonalAt n
  · rw [FlatSequence.evalAt_of_mem _ hf, FlatSequence.evalAt_of_mem _ hf]
    exact if_pos h
  · rw [FlatSequence.evalAt, FlatSequence.evalAt, dif_neg hf, dif_neg hf]
theorem evalAt_truncate_of_gt (S : FlatSequence) (N : ℕ) {n : ℕ}
    (f : FnOrScalar n) (h : ¬n ≤ N) : (truncate S N).evalAt f = 0 := by
  by_cases hf : f ∈ flatOffDiagonalAt n
  · rw [FlatSequence.evalAt_of_mem _ hf]
    exact if_neg h
  · rw [FlatSequence.evalAt, dif_neg hf]
theorem reflectionPairing_truncate (S : FlatSequence) (N : ℕ) (φ ψ : (a : ℕ) → FnOrScalar a)
    (hz : ∀ a b, N < a + b →
      S.evalAt (tensorAt (flipConjAt (φ a)) (ψ b)) = 0) :
    (truncate S N).reflectionPairing φ ψ = S.reflectionPairing φ ψ := by
  unfold FlatSequence.reflectionPairing
  refine finsum_congr fun p => ?_
  by_cases h : p.1 + p.2 ≤ N
  · exact evalAt_truncate S N _ h
  · rw [hz _ _ (not_le.1 h)]
    exact evalAt_truncate_of_gt S N _ h
theorem isCLMSequence_truncate (hS : IsCLMSequence S) (N : ℕ) :
    IsCLMSequence (truncate S N) := by
  refine ⟨fun c => ?_, fun p => ?_⟩
  · show (if 0 ≤ N then S 0 c else 0) = c.1
    rw [if_pos (Nat.zero_le N)]
    exact hS.1 c
  · by_cases h : p + 1 ≤ N
    · have e : (truncate S N).atSucc p = S.atSucc p := by
        funext φ
        exact if_pos h
      rw [e]
      exact hS.2 p
    · have e : (truncate S N).atSucc p = fun _ => 0 := by
        funext φ
        exact if_neg h
      rw [e]
      exact ⟨fun c c' φ ψ χ _ => by simp, 1, 0, le_rfl, le_rfl, fun φ => by simp⟩
theorem exists_growthBound_truncate (hF : TestSpaces.Elementary.BasicProperties)
    (hS : IsCLMSequence S) (N : ℕ) :
    ∃ (a : ℕ → ℝ) (kE : ℕ), HasGrowthBound (truncate S N) a kE := by
  classical
  choose k C hk hC hb using fun p => (hS.2 p).2
  refine ⟨fun n => if n = 0 then 1 else C (n - 1), 1 + ∑ p ∈ Finset.range N, k p,
    ⟨isCLMSequence_truncate hS N, by omega, by simp, fun n => ?_, fun p φ => ?_⟩⟩
  · show 0 ≤ (if n = 0 then (1 : ℝ) else C (n - 1))
    split_ifs
    · norm_num
    · exact hC _
  · set kE := 1 + ∑ p ∈ Finset.range N, k p with hkE
    have ha : (if p + 1 = 0 then (1 : ℝ) else C (p + 1 - 1)) = C p := by simp
    show ‖(truncate S N).atSucc p φ‖ ≤
      (if p + 1 = 0 then (1 : ℝ) else C (p + 1 - 1)) *
        bracketNorm (kE * (p + 1)) (toSchwartzFn φ)
    rw [ha]
    by_cases h : p + 1 ≤ N
    · have e : (truncate S N).atSucc p φ = S.atSucc p φ := if_pos h
      rw [e]
      refine (hb p φ).trans (mul_le_mul_of_nonneg_left ?_ (hC p))
      have hmem : p ∈ Finset.range N := Finset.mem_range.2 (by omega)
      have h₁ : k p ≤ ∑ p ∈ Finset.range N, k p :=
        Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) hmem
      have h₂ : k p ≤ kE * (p + 1) := by
        have : kE ≤ kE * (p + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos p)
        omega
      have ht : φ.1 ∈ TestSpaces.flatSchwartzSet (p + 1) :=
        (SchwartzAxioms.flatSchwartzSet_eq (n := p + 1)).superset φ.2
      have hpos : 0 < k p := hk p
      have hpos' : 0 < kE * (p + 1) := lt_of_lt_of_le hpos h₂
      have hmono : TestSpaces.weightedSeminorm (k p) φ.1 ≤
          TestSpaces.weightedSeminorm (kE * (p + 1)) φ.1 :=
        ((hF (p + 1) (Nat.succ_pos p)).1.1 φ.1 ht.1 φ.1 ht.1 0 0).2.1 _ _ hpos h₂ |>.1
      exact ENNReal.toReal_mono (ht.1.2 _ hpos').ne hmono
    · have e : (truncate S N).atSucc p φ = 0 := if_neg h
      rw [e, norm_zero]
      exact mul_nonneg (hC p) ENNReal.toReal_nonneg
end Cutoff
structure Hypotheses (σ : TestSpaces.SepTuple → ℝ) (S : FlatSequence) : Prop where
  basic : TestSpaces.Elementary.BasicProperties
  formFacts : AdmissibleForm.Statement
  combSeq : CombinationSequenceAdmissibleLinear
  translatePlus : MotionsTranslations.TranslatePreservesPlus
  linClosure : LinCombClosure
  nil_eq_one : σ TestSpaces.sepTupleNil = 1
  isCLM : IsCLMSequence S
  agrees : AgreesOnTensors σ S
  sesq : S.IsSesquilinear
  posSemidef : S.IsPosSemidef
  shiftInvariant : ∀ (p : ℕ) (w : Fin 4 → ℝ) (φ : schwartzFlatOffDiagonal (p + 1)),
    ∃ h : shiftAct w φ.1 ∈ schwartzFlatOffDiagonal (p + 1),
      S.atSucc p ⟨_, h⟩ = S.atSucc p φ
section Hyp
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
theorem Hypotheses.isLinearFunctionalSeq (H : Hypotheses σ S) : IsLinearFunctionalSeq S :=
  ⟨H.isCLM.1, fun p => (H.isCLM.2 p).1⟩
def cutoffFunctional (σ : TestSpaces.SepTuple → ℝ) (h : σ TestSpaces.sepTupleNil = 1) (N : ℕ) :
    SeparatedTuples.TupleFunctional where
  toFun Z := if Z.1.length ≤ N then σ (ofList Z) else 0
  map_nil := by
    have e : ofList SepTuple.nil = TestSpaces.sepTupleNil := by
      rw [← TupleLists.toList_sepTupleNil, TupleLists.ofList_toList]
    rw [if_pos (by simp [SepTuple.nil]), e, h]
theorem agreesOnTensors_truncate (H : Hypotheses σ S) (N : ℕ) :
    AgreesOnTensors (fun X => cutoffFunctional σ H.nil_eq_one N (toList X)) (truncate S N) := by
  intro p X hs h
  have hl : (toList ⟨p + 1, X⟩).1.length = p + 1 := by simp [toList]
  show (if p + 1 ≤ N then S (p + 1) ⟨_, h⟩ else 0) =
    (((if (toList ⟨p + 1, X⟩).1.length ≤ N then σ (ofList (toList ⟨p + 1, X⟩)) else 0 : ℝ)) : ℂ)
  rw [hl, TupleLists.ofList_toList]
  by_cases hN : p + 1 ≤ N
  · rw [if_pos hN, if_pos hN]
    exact H.agrees p X hs h
  · rw [if_neg hN, if_neg hN]
    simp
theorem length_push_le (r : (Fin 4 → ℝ) → Fin 4 → ℝ) (Y : SepTuple) :
    (push r Y).1.length ≤ Y.1.length := by
  unfold push
  split_ifs with h
  · simp [pushList]
  · simp [SepTuple.nil]
theorem length_juxt_le (A B : SepTuple) :
    (SepTuple.juxt A B).1.length ≤ A.1.length + B.1.length := by
  by_cases h : SepTuple.Composable A B
  · rw [SepTuple.juxt_val h]
    simp
  · simp [SepTuple.juxt, h, SepTuple.nil]
theorem reflectedPairValue_eq (τ : SeparatedTuples.TupleFunctional) (Y Y' : SepTuple) :
    reflectedPairValue τ Y Y' = (τ (SepTuple.juxt (push TimeAxis.timeReflection Y) Y') : ℂ) := by
  rw [reflectedPairValue, SeparatedTuples.pushSpan, SeparatedTuples.linearExtend_basisVec,
    SeparatedTuples.formalMul_basisVec, SeparatedTuples.TupleFunctional.spanExtension,
    SeparatedTuples.linearExtend_basisVec]
theorem combinationSequence_eq_lengthPart (H : Hypotheses σ S) {ι : Type} [Fintype ι] (c : ι → ℂ)
    (X : ι → UpperFamily) (hX : ∀ i, AllSmoothCompact (X i).2.1) (a : ℕ) :
    combinationSequence (linComb c X) a = lengthPart c X a :=
  (H.combSeq.2.1 _ (H.combSeq.1 ι c X hX)).1 ι c X hX rfl a
theorem ofConfigFn_zero (a : ℕ) :
    ofConfigFn (fun _ : TestSpaces.PointTuple a => (0 : ℂ)) = zeroOfDegree a := by
  cases a <;> rfl
theorem combinationSequence_eq_zero (H : Hypotheses σ S) {ι : Type} [Fintype ι] (c : ι → ℂ)
    (X : ι → UpperFamily) (hX : ∀ i, AllSmoothCompact (X i).2.1) {a : ℕ} (ha : ∀ i, (X i).1 ≠ a) :
    combinationSequence (linComb c X) a = zeroOfDegree a := by
  rw [combinationSequence_eq_lengthPart H c X hX, ← ofConfigFn_zero a]
  have : IsEmpty {i // familyLength (X i).toSeparatedFamily = a} := ⟨fun i => ha i.1 i.2⟩
  refine congrArg ofConfigFn (funext fun x => ?_)
  exact Fintype.sum_empty _
theorem reflectionForm_eq_sum (H : Hypotheses σ S) {ι κ : Type} [Fintype ι] [Fintype κ] (c : ι → ℂ)
    (c' : κ → ℂ) (X : ι → UpperFamily) (X' : κ → UpperFamily) (Y : ι → SepTuple) (Y' : κ → SepTuple)
    (hX : ∀ i, AllSmoothCompact (X i).2.1)
    (hX' : ∀ j, AllSmoothCompact (X' j).2.1)
    (hY : ∀ i, ListMatchesFamily (Y i) (X i)) (hY' : ∀ j, ListMatchesFamily (Y' j) (X' j))
    (Φ Ψ : AdmissibleSeq)
    (hΦ : ∀ a, (Φ.1 a).1 = combinationSequence (linComb c X) a)
    (hΨ : ∀ a, (Ψ.1 a).1 = combinationSequence (linComb c' X') a) :
    S.reflectionForm Φ Ψ =
      ∑ i, ∑ j, conj (c i) * c' j *
        (σ (ofList (SepTuple.juxt (push TimeAxis.timeReflection (Y i)) (Y' j))) : ℂ) := by
  set B := ∑ i, (X i).1 + ∑ j, (X' j).1 with hB
  have hBi : ∀ i, (X i).1 ≤ B := fun i =>
    (Finset.single_le_sum (f := fun i => (X i).1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_right _ _)
  have hBj : ∀ j, (X' j).1 ≤ B := fun j =>
    (Finset.single_le_sum (f := fun j => (X' j).1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans (Nat.le_add_left _ _)
  obtain ⟨a, kE, hg⟩ := exists_growthBound_truncate H.basic H.isCLM (2 * B)
  have hC := (H.formFacts.1 (truncate S (2 * B)) a kE hg).2.2 (cutoffFunctional σ H.nil_eq_one (2 * B))
    (agreesOnTensors_truncate H (2 * B))
  have h₁ := (hC ι κ c c' X X' Y Y' hX hX' hY hY' Φ Ψ hΦ hΨ).1
  have hz : ∀ p p', 2 * B < p + p' → S.evalAt (tensorAt
      (flipConjAt ((fun p => (Φ.1 p).1) p)) ((fun p => (Ψ.1 p).1) p')) = 0 := by
    intro p p' hp
    rcases (by omega : B < p ∨ B < p') with h | h
    · have e : (Φ.1 p).1 = zeroOfDegree p :=
        (hΦ p).trans (combinationSequence_eq_zero H c X hX fun i => by have := hBi i; omega)
      show S.evalAt (tensorAt (flipConjAt (Φ.1 p).1) (Ψ.1 p').1) = 0
      rw [e, flipConjAt_zero, tensorAt_zero_left, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
    · have e : (Ψ.1 p').1 = zeroOfDegree p' :=
        (hΨ p').trans (combinationSequence_eq_zero H c' X' hX' fun j => by have := hBj j; omega)
      show S.evalAt (tensorAt (flipConjAt (Φ.1 p).1) (Ψ.1 p').1) = 0
      rw [e, tensorAt_zero_right, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
  have e := reflectionPairing_truncate S (2 * B) (fun p => (Φ.1 p).1) (fun p => (Ψ.1 p).1) hz
  rw [FlatSequence.reflectionForm, ← e]
  refine h₁.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  rw [reflectedPairValue_eq]
  have hli : (Y i).1.length = (X i).1 := by rw [hY i]; simp
  have hlj : (Y' j).1.length = (X' j).1 := by rw [hY' j]; simp
  have hlen : (SepTuple.juxt (push TimeAxis.timeReflection (Y i)) (Y' j)).1.length ≤ 2 * B := by
    have h₂ := length_juxt_le (push TimeAxis.timeReflection (Y i)) (Y' j)
    have h₃ := length_push_le TimeAxis.timeReflection (Y i)
    have h₄ := hBi i
    have h₅ := hBj j
    omega
  have e₂ : cutoffFunctional σ H.nil_eq_one (2 * B)
      (SepTuple.juxt (push TimeAxis.timeReflection (Y i)) (Y' j)) =
      σ (ofList (SepTuple.juxt (push TimeAxis.timeReflection (Y i)) (Y' j))) := if_pos hlen
  rw [e₂]
end Hyp
theorem exists_linComb_eq (F : UpperCombination) (hF : F.HasSmoothFamilies) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (X : ι → UpperFamily)
      (_ : ∀ i, AllSmoothCompact (X i).2.1), F = linComb c X := by
  classical
  refine ⟨F.support, inferInstance, fun i => F i.1, fun i => i.1, fun i => ?_, ?_⟩
  · exact hF (F i.1, i.1)
      ((UpperCombination.mem_reducedForm_iff F _ _).2 ⟨Finsupp.mem_support_iff.1 i.2, rfl⟩)
  · rw [linComb, Finset.sum_coe_sort F.support
      (fun X => F X • UpperCombination.ofFamily X)]
    conv_lhs => rw [← Finsupp.sum_single F]
    simp [Finsupp.sum, UpperCombination.ofFamily, Finsupp.smul_single]
section Shifts
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
theorem shiftActAt_zero (w : Fin 4 → ℝ) (a : ℕ) :
    shiftActAt w (zeroOfDegree a) = zeroOfDegree a := by apply _root_.YangMills.Construction.ConditionDomains.shiftActAt_zeroOfDegree <;> assumption
theorem shiftActAt_cast (w : Fin 4 → ℝ) {a b : ℕ} (e : a = b) (f : FnOrScalar a) :
    shiftActAt w (e ▸ f : FnOrScalar b) = e ▸ shiftActAt w f := by
  subst e
  rfl
theorem smulAt_shiftActAt (w : Fin 4 → ℝ) (c : ℂ) {n : ℕ} (f : FnOrScalar n) :
    smulAt c (shiftActAt w f) = shiftActAt w (smulAt c f) := by
  cases n with
  | zero => rfl
  | succ p =>
    have key : ∀ g : TestSpaces.PointTuple (p + 1) → ℂ, (fun y => c * shiftAct w g y) =
        shiftAct w (fun y => c * g y) := fun g => funext fun x => by
      simp only [shiftAct_apply]
    exact key f
theorem timeFlip_sub {u w : Fin 4 → ℝ} (hw : w 3 = 0) :
    timeFlip (u - w) = timeFlip u - w := by
  funext i
  fin_cases i <;> simp [timeFlip, hw]
theorem flipConjAt_shiftActAt {w : Fin 4 → ℝ} (hw : w 3 = 0) {n : ℕ} (f : FnOrScalar n) :
    flipConjAt (shiftActAt w f) = shiftActAt w (flipConjAt f) := by
  cases n with
  | zero => rfl
  | succ p =>
    have key : ∀ g : TestSpaces.PointTuple (p + 1) → ℂ, flipConj (shiftAct w g) =
        shiftAct w (flipConj g) := fun g => funext fun x => by
      simp only [flipConj, shiftAct_apply, timeFlip_sub hw]
    exact key f
theorem tensorAt_shiftActAt (w : Fin 4 → ℝ) {a b : ℕ} (f : FnOrScalar a)
    (g : FnOrScalar b) :
    tensorAt (shiftActAt w f) (shiftActAt w g) = shiftActAt w (tensorAt f g) := by
  cases a with
  | zero =>
    show (Nat.zero_add b).symm ▸ smulAt (show ℂ from f) (shiftActAt w g) =
      shiftActAt w ((Nat.zero_add b).symm ▸ smulAt (show ℂ from f) g)
    rw [shiftActAt_cast, smulAt_shiftActAt]
  | succ p =>
    cases b with
    | zero =>
      show smulAt (show ℂ from g) (shiftActAt w f) = shiftActAt w (smulAt (show ℂ from g) f)
      exact smulAt_shiftActAt w _ f
    | succ r =>
      have key : ∀ (u : TestSpaces.PointTuple (p + 1) → ℂ) (v : TestSpaces.PointTuple (r + 1) → ℂ),
          tensorFn (shiftAct w u) (shiftAct w v) = shiftAct w (tensorFn u v) := fun u v =>
        funext fun z => by
          simp only [tensorFn, shiftAct_apply]
          rfl
      exact key f g
theorem shiftActAt_linCombAt (w : Fin 4 → ℝ) (c c' : ℂ) {n : ℕ} (f g : FnOrScalar n) :
    shiftActAt w (linCombAt c c' f g) = linCombAt c c' (shiftActAt w f) (shiftActAt w g) := by
  cases n with
  | zero => rfl
  | succ p =>
    have key : ∀ u v : TestSpaces.PointTuple (p + 1) → ℂ,
        shiftAct w (fun y => c * u y + c' * v y) =
          fun y => c * shiftAct w u y + c' * shiftAct w v y :=
      fun u v => funext fun x => by simp only [shiftAct_apply]
    exact key f g
theorem shiftActAt_mem (hK : MotionsTranslations.TranslatePreservesPlus)
    {w : Fin 4 → ℝ} (hw : w 3 = 0) {n : ℕ} {f : FnOrScalar n}
    (hf : f ∈ flatOffPosTimeAt n) : shiftActAt w f ∈ flatOffPosTimeAt n := by
  cases n with
  | zero => exact Set.mem_univ _
  | succ p =>
    have key : ∀ φ : TestSpaces.PointTuple (p + 1) → ℂ, φ ∈ schwartzFlatOffPosTime (p + 1) →
        shiftAct w φ ∈ schwartzFlatOffPosTime (p + 1) := by
      intro φ hφ
      rw [← SchwartzAxioms.positiveTimeSchwartz_eq] at hφ ⊢
      have h := hK (p + 1) (Nat.succ_pos p) φ hφ w hw.ge
      have e : shiftAct w φ = Motions.actOnFun (UpperHalfTensors.translateMotion w) φ :=
        funext fun x => by
          rw [shiftAct_apply, WightmanReconstruction.actOnFun_translateMotion]
      rw [e]
      exact h
    exact key f hf
def shiftSeq (H : Hypotheses σ S) (w : Fin 4 → ℝ) (hw : w 3 = 0) (Φ : AdmissibleSeq) :
    AdmissibleSeq :=
  ⟨fun a => ⟨shiftActAt w (Φ.1 a).1, shiftActAt_mem H.translatePlus hw (Φ.1 a).2⟩, by
    refine Set.Finite.subset Φ.2 fun a ha h0 => ha ?_
    show shiftActAt _ (Φ.1 a).1 = zeroOfDegree a
    rw [h0, shiftActAt_zero]⟩
theorem evalAt_shiftActAt (H : Hypotheses σ S) (w : Fin 4 → ℝ) {n : ℕ} {f : FnOrScalar n}
    (hf : f ∈ flatOffDiagonalAt n) : S.evalAt (shiftActAt w f) = S.evalAt f := by
  cases n with
  | zero => rfl
  | succ p =>
    obtain ⟨h, e⟩ := H.shiftInvariant p w ⟨f, hf⟩
    rw [FlatSequence.evalAt_of_mem S hf,
      FlatSequence.evalAt_of_mem S (f := shiftActAt w f) h]
    exact e
theorem reflectionForm_shiftSeq_self (H : Hypotheses σ S) (w : Fin 4 → ℝ) (hw : w 3 = 0)
    (x : AdmissibleSeq) :
    S.reflectionForm (shiftSeq H w hw x) (shiftSeq H w hw x) = S.reflectionForm x x := by
  unfold FlatSequence.reflectionForm FlatSequence.reflectionPairing
  refine finsum_congr fun p => ?_
  show S.evalAt (tensorAt (flipConjAt (shiftActAt w (x.1 p.1).1))
      (shiftActAt w (x.1 p.2).1)) =
    S.evalAt (tensorAt (flipConjAt (x.1 p.1).1) (x.1 p.2).1)
  rw [flipConjAt_shiftActAt hw, tensorAt_shiftActAt]
  exact evalAt_shiftActAt H w (H.sesq.1 x x p.1 p.2)
theorem isLinComb_shiftSeq (H : Hypotheses σ S) (w : Fin 4 → ℝ) (hw : w 3 = 0) {c c' : ℂ}
    {x y z : AdmissibleSeq} (h : IsLinComb c c' x.1 y.1 z.1) :
    IsLinComb c c' (shiftSeq H w hw x).1 (shiftSeq H w hw y).1 (shiftSeq H w hw z).1 := fun a => by
  show shiftActAt w (z.1 a).1 = _
  rw [h a, shiftActAt_linCombAt]
  rfl
end Shifts
section Families
def familyList (X : UpperFamily) : SepTuple :=
  ⟨List.ofFn X.2.1, by
    refine ⟨fun f hf => ?_, List.pairwise_ofFn.2 fun i j hij => X.2.2.2 hij.ne⟩
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    obtain ⟨-, h₁, h₂, -⟩ := mem_realC1CompactIn_iff.1 (X.2.2.1 i)
    exact ⟨h₁, h₂⟩⟩
theorem familyList_nil : familyList UpperFamily.nil = SepTuple.nil :=
  Subtype.ext (by simp [familyList, UpperFamily.nil, SepTuple.nil])
theorem familyList_mem_smoothSupportedIn (X : UpperFamily) (hX : AllSmoothCompact X.2.1) :
    familyList X ∈ WightmanReconstruction.smoothSupportedIn TestSpaces.upperHalfSpace := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact (mem_realC1CompactIn_iff.1 (X.2.2.1 i)).2.2.2
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    obtain ⟨-, a, b, -⟩ := mem_realSmoothCompactIn_iff.1 (hX i)
    exact ⟨a, b, (mem_realC1CompactIn_iff.1 (X.2.2.1 i)).2.2.2⟩
def shiftComponents {a : ℕ} (w : Fin 4 → ℝ) (f : Fin a → (Fin 4 → ℝ) → ℝ) :
    Fin a → (Fin 4 → ℝ) → ℝ :=
  fun i u => f i (u - w)
theorem tsupport_comp_sub (w : Fin 4 → ℝ) (g : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun u => g (u - w)) = (Homeomorph.subRight w) ⁻¹' tsupport g :=
  tsupport_comp_eq_preimage g (Homeomorph.subRight w)
def shiftFamily (w : Fin 4 → ℝ) (hw : w 3 = 0) (X : UpperFamily) : UpperFamily :=
  ⟨X.1, shiftComponents w X.2.1, by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · obtain ⟨ho, h₁, h₂, h₃⟩ := mem_realC1CompactIn_iff.1 (X.2.2.1 i)
      refine mem_realC1CompactIn_iff.2 ⟨ho, h₁.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
      · show IsCompact (tsupport fun u => X.2.1 i (u - w))
        rw [tsupport_comp_sub]
        exact (Homeomorph.subRight w).isCompact_preimage.mpr h₂
      · show tsupport (fun u => X.2.1 i (u - w)) ⊆ _
        rw [tsupport_comp_sub]
        intro y hy
        have h₄ : (y - w) ∈ upperHalfSpace := h₃ hy
        have h₅ : 0 < (y - w) 3 := h₄
        exact show 0 < y 3 from by simpa [hw] using h₅
    · show Disjoint (tsupport fun u => X.2.1 i (u - w)) (tsupport fun u => X.2.1 j (u - w))
      rw [tsupport_comp_sub, tsupport_comp_sub]
      exact (X.2.2.2 hij).preimage _⟩
theorem allSmoothCompact_shiftFamily (w : Fin 4 → ℝ) (hw : w 3 = 0) {X : UpperFamily}
    (hX : AllSmoothCompact X.2.1) : AllSmoothCompact (shiftFamily w hw X).2.1 := fun i => by
  obtain ⟨ho, h₁, h₂, -⟩ := mem_realSmoothCompactIn_iff.1 (hX i)
  refine mem_realSmoothCompactIn_iff.2
    ⟨ho, h₁.comp (contDiff_id.sub contDiff_const), ?_, Set.subset_univ _⟩
  show IsCompact (tsupport fun u => X.2.1 i (u - w))
  rw [tsupport_comp_sub]
  exact (Homeomorph.subRight w).isCompact_preimage.mpr h₂
theorem push_translate_familyList (w : Fin 4 → ℝ) (hw : w 3 = 0) (X : UpperFamily) :
    push (SeparatedTuples.translate w) (familyList X) = familyList (shiftFamily w hw X) := by
  have hl : pushList (SeparatedTuples.translate w) (familyList X).1 =
      (familyList (shiftFamily w hw X)).1 := by
    rw [SeparatedTuples.pushList_translate]
    show (List.ofFn X.2.1).map _ = List.ofFn _
    rw [List.map_ofFn]
    rfl
  have hs : SeparatedTuples.IsDisjointlySupported
      (pushList (SeparatedTuples.translate w) (familyList X).1) := by
    rw [hl]
    exact (familyList (shiftFamily w hw X)).2
  unfold push
  rw [dif_pos hs]
  exact Subtype.ext hl
theorem toConfigFn_tupleTensor_shift {n : ℕ} (w : Fin 4 → ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ)
    (x : TestSpaces.PointTuple n) :
    toConfigFn (entryTensor (shiftComponents w f)) x =
      toConfigFn (entryTensor f) fun i => x i - w := by
  cases n <;> rfl
theorem shiftActAt_ofConfigFn (w : Fin 4 → ℝ) {a : ℕ} (G : TestSpaces.PointTuple a → ℂ) :
    shiftActAt w (ofConfigFn G) = ofConfigFn fun x => G fun j => x j - w := by
  cases a with
  | zero =>
    show G _ = G _
    exact congrArg G (Subsingleton.elim _ _)
  | succ p =>
    funext x
    show shiftAct w G x = G _
    rw [shiftAct_apply]
theorem lengthPart_shiftFamily {ι : Type} [Fintype ι] (c : ι → ℂ) (X : ι → UpperFamily)
    (w : Fin 4 → ℝ) (hw : w 3 = 0) (a : ℕ) :
    lengthPart c (fun i => shiftFamily w hw (X i)) a = shiftActAt w (lengthPart c X a) := by
  rw [lengthPart, lengthPart, shiftActAt_ofConfigFn]
  refine congrArg ofConfigFn (funext fun x => ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (c i.1 * ·) (toConfigFn_tupleTensor_shift w (X i.1).2.1 _)
end Families
section Vacuum
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
def admissibleOfLinComb (H : Hypotheses σ S) {ι : Type} [Fintype ι] (c : ι → ℂ) (X : ι → UpperFamily)
    (hX : ∀ i, AllSmoothCompact (X i).2.1) : AdmissibleSeq :=
  ⟨fun a => ⟨combinationSequence (linComb c X) a,
      (H.combSeq.2.1 _ (H.combSeq.1 ι c X hX)).2.choose a⟩,
    (H.combSeq.2.1 _ (H.combSeq.1 ι c X hX)).2.choose_spec⟩
def vacuumSeq (H : Hypotheses σ S) : AdmissibleSeq :=
  admissibleOfLinComb H (fun _ : Unit => (1 : ℂ)) (fun _ => UpperFamily.nil)
    fun _ => allSmoothCompact_nilFamily
theorem linComb_nil :
    linComb (fun _ : Unit => (1 : ℂ)) (fun _ => UpperFamily.nil) =
      UpperCombination.ofFamily UpperFamily.nil := by
  simp [linComb]
theorem vacuumSeq_zero (H : Hypotheses σ S) : ((vacuumSeq H).1 0).1 = (1 : ℂ) := by
  show combinationSequence (linComb _ _) 0 = _
  rw [linComb_nil]
  exact H.combSeq.2.2.2.2.2.1
theorem vacuumSeq_of_pos (H : Hypotheses σ S) {a : ℕ} (ha : 1 ≤ a) :
    ((vacuumSeq H).1 a).1 = zeroOfDegree a := by
  show combinationSequence (linComb _ _) a = _
  rw [linComb_nil]
  exact H.combSeq.2.2.2.2.2.2 a ha
theorem exists_common_bound (Φ Ψ : AdmissibleSeq) :
    ∃ N : ℕ, 1 ≤ N ∧ (∀ a, N < a → (Φ.1 a).1 = zeroOfDegree a) ∧
      ∀ a, N < a → (Ψ.1 a).1 = zeroOfDegree a := by
  obtain ⟨b₁, h₁⟩ := Φ.2.bddAbove
  obtain ⟨b₂, h₂⟩ := Ψ.2.bddAbove
  refine ⟨b₁ + b₂ + 1, by omega, fun a ha => ?_, fun a ha => ?_⟩
  · by_contra hn
    have := h₁ hn
    omega
  · by_contra hn
    have := h₂ hn
    omega
theorem reflectionForm_vacuum_right (H : Hypotheses σ S) (Φ : AdmissibleSeq) :
    S.reflectionForm Φ (vacuumSeq H) = ∑ᶠ a : ℕ, S.evalAt (flipConjAt (Φ.1 a).1) := by
  obtain ⟨N, -, hΦ, -⟩ := exists_common_bound Φ Φ
  have hz : ∀ a, N < a → S.evalAt (flipConjAt (Φ.1 a).1) = 0 := fun a ha => by
    rw [hΦ a ha, flipConjAt_zero, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
  have hs : (Function.support fun a : ℕ => S.evalAt (flipConjAt (Φ.1 a).1)) ⊆
      ↑(Finset.range (N + 1)) := by
    intro a ha
    by_contra hn
    refine ha (hz a ?_)
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    omega
  rw [finsum_eq_sum_of_support_subset _ hs, FlatSequence.reflectionForm,
    reflectionPairing_eq_finite_sum _ _ N]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single 0]
    · rw [vacuumSeq_zero, tensorAt_scalar_right, smulAt_one]
    · intro b _ hb
      rw [vacuumSeq_of_pos H (Nat.one_le_iff_ne_zero.2 hb), tensorAt_zero_right,
        evalAt_zeroOfDegree H.isLinearFunctionalSeq]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h
  · rintro a b (ha | hb)
    · rw [hΦ a ha, flipConjAt_zero, tensorAt_zero_left, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
    · rw [vacuumSeq_of_pos H (by omega), tensorAt_zero_right,
        evalAt_zeroOfDegree H.isLinearFunctionalSeq]
theorem reflectionForm_vacuum_left (H : Hypotheses σ S) (Ψ : AdmissibleSeq) :
    S.reflectionForm (vacuumSeq H) Ψ = ∑ᶠ a : ℕ, S.evalAt (Ψ.1 a).1 := by
  obtain ⟨N, -, hΨ, -⟩ := exists_common_bound Ψ Ψ
  have hz : ∀ a, N < a → S.evalAt (Ψ.1 a).1 = 0 := fun a ha => by
    rw [hΨ a ha, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
  have hs : (Function.support fun a : ℕ => S.evalAt (Ψ.1 a).1) ⊆ ↑(Finset.range (N + 1)) := by
    intro a ha
    by_contra hn
    refine ha (hz a ?_)
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    omega
  rw [finsum_eq_sum_of_support_subset _ hs, FlatSequence.reflectionForm,
    reflectionPairing_eq_finite_sum _ _ N]
  · rw [Finset.sum_eq_single 0]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [vacuumSeq_zero]
      have e : flipConjAt (show FnOrScalar 0 from (1 : ℂ)) = (1 : ℂ) := map_one (starRingEnd ℂ)
      rw [e, tensorAt_scalar_left, evalAt_cast, smulAt_one]
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [vacuumSeq_of_pos H (Nat.one_le_iff_ne_zero.2 ha), flipConjAt_zero, tensorAt_zero_left,
        evalAt_zeroOfDegree H.isLinearFunctionalSeq]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h
  · rintro a b (ha | hb)
    · rw [vacuumSeq_of_pos H (by omega), flipConjAt_zero, tensorAt_zero_left,
        evalAt_zeroOfDegree H.isLinearFunctionalSeq]
    · rw [hΨ b hb, tensorAt_zero_right, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
theorem juxt_nil_right (A : SepTuple) : SepTuple.juxt A SepTuple.nil = A := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.juxt_nil <;> assumption
theorem juxt_nil_left (A : SepTuple) : SepTuple.juxt SepTuple.nil A = A := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.nil_juxt <;> assumption
theorem reflectionForm_linComb_vacuum (H : Hypotheses σ S) {ι : Type} [Fintype ι] (c : ι → ℂ)
    (X : ι → UpperFamily) (hX : ∀ i, AllSmoothCompact (X i).2.1)
    (Φ : AdmissibleSeq) (hΦ : ∀ a, (Φ.1 a).1 = combinationSequence (linComb c X) a) :
    S.reflectionForm Φ (vacuumSeq H) =
      ∑ i, conj (c i) * (σ (ofList (push TimeAxis.timeReflection (familyList (X i)))) : ℂ) := by
  rw [reflectionForm_eq_sum H c (fun _ : Unit => (1 : ℂ)) X (fun _ => UpperFamily.nil)
    (fun i => familyList (X i)) (fun _ => familyList UpperFamily.nil) hX
    (fun _ => allSmoothCompact_nilFamily) (fun _ => rfl) (fun _ => rfl) Φ
    (vacuumSeq H) hΦ fun _ => rfl]
  simp [familyList_nil, juxt_nil_right]
theorem reflectionForm_vacuum_linComb (H : Hypotheses σ S) {κ : Type} [Fintype κ] (c : κ → ℂ)
    (X : κ → UpperFamily) (hX : ∀ j, AllSmoothCompact (X j).2.1)
    (Ψ : AdmissibleSeq) (hΨ : ∀ a, (Ψ.1 a).1 = combinationSequence (linComb c X) a) :
    S.reflectionForm (vacuumSeq H) Ψ = ∑ j, c j * (σ (ofList (familyList (X j))) : ℂ) := by
  rw [reflectionForm_eq_sum H (fun _ : Unit => (1 : ℂ)) c (fun _ => UpperFamily.nil) X
    (fun _ => familyList UpperFamily.nil) (fun j => familyList (X j))
    (fun _ => allSmoothCompact_nilFamily) hX (fun _ => rfl) (fun _ => rfl)
    (vacuumSeq H) Ψ (fun _ => rfl) hΨ]
  simp [familyList_nil, juxt_nil_left, SeparatedTuples.push_nil]
theorem reflectionForm_vacuum_self (H : Hypotheses σ S) :
    S.reflectionForm (vacuumSeq H) (vacuumSeq H) = 1 := by
  rw [reflectionForm_vacuum_linComb H (fun _ : Unit => (1 : ℂ)) (fun _ => UpperFamily.nil)
    (fun _ => allSmoothCompact_nilFamily) (vacuumSeq H) fun _ => rfl]
  have e : ofList SepTuple.nil = TestSpaces.sepTupleNil := by
    rw [← TupleLists.toList_sepTupleNil, TupleLists.ofList_toList]
  simp [familyList_nil, e, H.nil_eq_one]
end Vacuum
section FormNorm
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
def formNorm (S : FlatSequence) (x : AdmissibleSeq) : ℝ :=
  Real.sqrt (S.reflectionForm x x).re
theorem formNorm_nonneg (x : AdmissibleSeq) : 0 ≤ formNorm S x := Real.sqrt_nonneg _
theorem formNorm_sq (H : Hypotheses σ S) (x : AdmissibleSeq) :
    formNorm S x ^ 2 = (S.reflectionForm x x).re :=
  Real.sq_sqrt (H.posSemidef.1 x).2
theorem norm_reflectionForm_le (H : Hypotheses σ S) (x y : AdmissibleSeq) :
    ‖S.reflectionForm x y‖ ≤ formNorm S x * formNorm S y := by
  have h := H.posSemidef.2.2.1 x y
  rw [← formNorm_sq H, ← formNorm_sq H, ← mul_pow] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (formNorm_nonneg x) (formNorm_nonneg y))).1 h
theorem reflectionForm_sub_left (H : Hypotheses σ S) {x x' d : AdmissibleSeq}
    (h : IsLinComb 1 (-1) x.1 x'.1 d.1) (y : AdmissibleSeq) :
    S.reflectionForm d y = S.reflectionForm x y - S.reflectionForm x' y := by
  rw [H.sesq.2.2.1 1 (-1) x x' d y h]
  simp
  ring
theorem reflectionForm_sub_right (H : Hypotheses σ S) {x x' d : AdmissibleSeq}
    (h : IsLinComb 1 (-1) x.1 x'.1 d.1) (y : AdmissibleSeq) :
    S.reflectionForm y d = S.reflectionForm y x - S.reflectionForm y x' := by
  rw [H.sesq.2.2.2 1 (-1) y x x' d h]
  ring
theorem formNorm_le_add (H : Hypotheses σ S) {x x' d : AdmissibleSeq}
    (h : IsLinComb 1 (-1) x.1 x'.1 d.1) :
    formNorm S x' ≤ formNorm S x + formNorm S d := by
  rcases (formNorm_nonneg (S := S) x').eq_or_lt with h0 | h0
  · rw [← h0]
    exact add_nonneg (formNorm_nonneg x) (formNorm_nonneg d)
  · have e : S.reflectionForm x' x' = S.reflectionForm x' x - S.reflectionForm x' d := by
      rw [reflectionForm_sub_right H h x']
      ring
    have h₁ : formNorm S x' ^ 2 ≤ formNorm S x' * (formNorm S x + formNorm S d) := by
      rw [formNorm_sq H]
      refine (Complex.re_le_norm _).trans ?_
      rw [e, mul_add]
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_reflectionForm_le H _ _) (norm_reflectionForm_le H _ _))
    rw [sq] at h₁
    exact le_of_mul_le_mul_left h₁ h0
theorem formNorm_shiftSeq (H : Hypotheses σ S) (w : Fin 4 → ℝ) (hw : w 3 = 0)
    (x : AdmissibleSeq) : formNorm S (shiftSeq H w hw x) = formNorm S x := by
  rw [formNorm, formNorm, reflectionForm_shiftSeq_self]
theorem formNorm_vacuum (H : Hypotheses σ S) : formNorm S (vacuumSeq H) = 1 := by
  rw [formNorm, reflectionForm_vacuum_self]
  simp
theorem exists_formNorm_sq_le (H : Hypotheses σ S) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (k : ℕ) (A : ℝ), 1 ≤ k ∧ 0 ≤ A ∧ ∀ (D : AdmissibleSeq) (δ : ℝ), 0 ≤ δ →
      (∀ a, N < a → (D.1 a).1 = zeroOfDegree a) → (D.1 0).1 = zeroOfDegree 0 →
      (∀ a, 1 ≤ a → a ≤ N → seminormAt k (D.1 a).1 ≤ ENNReal.ofReal δ) →
      formNorm S D ^ 2 ≤ A * δ ^ 2 := by
  obtain ⟨a, kE, hg⟩ := exists_growthBound_truncate H.basic H.isCLM (2 * N)
  have hk : 1 ≤ 2 * kE * N := by
    have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) hg.one_le) hN
    omega
  set R := Finset.range (N + 1) with hR
  refine ⟨2 * kE * N, ∑ p ∈ R, ∑ p' ∈ R, a (p + p'), hk,
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun p' _ => hg.coeff_nonneg _,
    fun D δ hδ hend hzero hnorm => ?_⟩
  have hB := (H.formFacts.1 (truncate S (2 * N)) a kE hg).2.1.2 D D N hN hend hend
  have hn : ∀ p ∈ R, seminormAt (2 * kE * N) (D.1 p).1 ≤ ENNReal.ofReal δ := fun p hp => by
    rcases Nat.eq_zero_or_pos p with rfl | h0
    · rw [hzero]
      simp [seminormAt, zeroOfDegree]
    · exact hnorm p h0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp))
  have hC : ∑ p ∈ R, ∑ p' ∈ R, ENNReal.ofReal (a (p + p')) * seminormAt (2 * kE * N) (D.1 p).1 *
        seminormAt (2 * kE * N) (D.1 p').1 ≤
      ENNReal.ofReal ((∑ p ∈ R, ∑ p' ∈ R, a (p + p')) * δ ^ 2) := by
    have e : (∑ p ∈ R, ∑ p' ∈ R, a (p + p')) * δ ^ 2 = ∑ p ∈ R, ∑ p' ∈ R, a (p + p') * δ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_mul _ _ _
    rw [e, ENNReal.ofReal_sum_of_nonneg fun p _ =>
      Finset.sum_nonneg fun p' _ => mul_nonneg (hg.coeff_nonneg _) (sq_nonneg δ)]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun p' _ => mul_nonneg (hg.coeff_nonneg _) (sq_nonneg δ)]
    refine Finset.sum_le_sum fun p' hp' => ?_
    rw [ENNReal.ofReal_mul (hg.coeff_nonneg _), sq, ENNReal.ofReal_mul hδ, ← mul_assoc]
    exact mul_le_mul' (mul_le_mul' le_rfl (hn p hp)) (hn p' hp')
  have hz : ∀ p p', 2 * N < p + p' → S.evalAt (tensorAt
      (flipConjAt ((fun p => (D.1 p).1) p)) ((fun p => (D.1 p).1) p')) = 0 := by
    intro p p' hp
    rcases (by omega : N < p ∨ N < p') with h | h
    · show S.evalAt (tensorAt (flipConjAt (D.1 p).1) (D.1 p').1) = 0
      rw [hend p h, flipConjAt_zero, tensorAt_zero_left, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
    · show S.evalAt (tensorAt (flipConjAt (D.1 p).1) (D.1 p').1) = 0
      rw [hend p' h, tensorAt_zero_right, evalAt_zeroOfDegree H.isLinearFunctionalSeq]
  have e := reflectionPairing_truncate S (2 * N) (fun p => (D.1 p).1) (fun p => (D.1 p).1) hz
  have e' : (truncate S (2 * N)).reflectionForm D D = S.reflectionForm D D := e
  rw [e'] at hB
  have hle := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun p' _ => hg.coeff_nonneg _) (sq_nonneg δ))).1 (hB.trans hC)
  rw [formNorm_sq H]
  exact (Complex.re_le_norm _).trans hle
theorem exists_close_linComb (H : Hypotheses σ S) (Φ : AdmissibleSeq) {N k : ℕ} {A : ℝ} (hN : 1 ≤ N)
    (hk : 1 ≤ k) (hΦ : ∀ a, N < a → (Φ.1 a).1 = zeroOfDegree a)
    (hsmall : ∀ (D : AdmissibleSeq) (δ : ℝ), 0 ≤ δ →
      (∀ a, N < a → (D.1 a).1 = zeroOfDegree a) → (D.1 0).1 = zeroOfDegree 0 →
      (∀ a, 1 ≤ a → a ≤ N → seminormAt k (D.1 a).1 ≤ ENNReal.ofReal δ) →
      formNorm S D ^ 2 ≤ A * δ ^ 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (X : ι → UpperFamily)
      (hX : ∀ i, AllSmoothCompact (X i).2.1) (D : AdmissibleSeq),
      IsLinComb 1 (-1) Φ.1 (admissibleOfLinComb H c X hX).1 D.1 ∧
        formNorm S D ^ 2 ≤ A * δ ^ 2 := by
  classical
  obtain ⟨F, hF, hend, h0, hn⟩ := H.formFacts.2 Φ N hN hΦ k δ hk hδ
  obtain ⟨ι, inst, c, X, hX, rfl⟩ := exists_linComb_eq F hF
  obtain ⟨D₀, hD₀, hlin⟩ := H.linClosure.2 1 (-1) Φ.1 (admissibleOfLinComb H c X hX).1 Φ.2
    (admissibleOfLinComb H c X hX).2
  have hsub : ∀ a, (D₀ a).1 = (Φ.1 a).1 - combinationSequence (linComb c X) a := fun a => by
    rw [hlin a, ← smul_add_smul_eq_linCombAt, one_smul, neg_smul, one_smul, sub_eq_add_neg]
    rfl
  refine ⟨ι, inst, c, X, hX, ⟨D₀, hD₀⟩, hlin, hsmall ⟨D₀, hD₀⟩ δ hδ.le (fun a ha => ?_) ?_ ?_⟩
  · show (D₀ a).1 = _
    rw [hsub, hΦ a ha, hend a ha, sub_self, zero_eq_zeroOfDegree]
  · show (D₀ 0).1 = _
    rw [hsub, h0, sub_self, zero_eq_zeroOfDegree]
  · intro a h₁ h₂
    show seminormAt k (D₀ a).1 ≤ _
    rw [hsub]
    exact hn a h₁ h₂
end FormNorm
section Limit
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
theorem smul_apply_three_eq_zero {v : Fin 4 → ℝ} (hv : v 3 = 0) (t : ℝ) : (t • v) 3 = 0 := by
  simp [hv]
theorem tendsto_of_uniform_approx {f : ℝ → ℂ} {L : ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (g : ℝ → ℂ) (L' : ℂ),
      Tendsto g atTop (𝓝 L') ∧ (∀ t, ‖f t - g t‖ ≤ ε) ∧ ‖L - L'‖ ≤ ε) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, L', hg, h₁, h₂⟩ := h (ε / 3) (by positivity)
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hg) (ε / 3) (by positivity)
  refine ⟨T, fun t ht => ?_⟩
  have h₃ := hT t ht
  rw [dist_eq_norm] at h₃ ⊢
  have e : f t - L = (f t - g t) + (g t - L') + (L' - L) := by ring
  have h₄ : ‖L' - L‖ ≤ ε / 3 := by
    rw [norm_sub_rev]
    exact h₂
  rw [e]
  have h₅ := norm_add₃_le (a := f t - g t) (b := g t - L') (c := L' - L)
  linarith [h₁ t]
theorem tendsto_reflectionForm_linComb (H : Hypotheses σ S) {v : Fin 4 → ℝ} (hv : v 3 = 0)
    (hclu : WightmanReconstruction.TupleClusteringAlong σ v) {ι κ : Type} [Fintype ι]
    [Fintype κ] (c : ι → ℂ) (c' : κ → ℂ) (X : ι → UpperFamily) (X' : κ → UpperFamily)
    (hX : ∀ i, AllSmoothCompact (X i).2.1)
    (hX' : ∀ j, AllSmoothCompact (X' j).2.1) :
    Tendsto (fun t : ℝ => S.reflectionForm (admissibleOfLinComb H c X hX)
        (shiftSeq H (t • v) (smul_apply_three_eq_zero hv t) (admissibleOfLinComb H c' X' hX'))) atTop
      (𝓝 (S.reflectionForm (admissibleOfLinComb H c X hX) (vacuumSeq H) *
        S.reflectionForm (vacuumSeq H) (admissibleOfLinComb H c' X' hX'))) := by
  have e₁ : ∀ t : ℝ, S.reflectionForm (admissibleOfLinComb H c X hX)
      (shiftSeq H (t • v) (smul_apply_three_eq_zero hv t) (admissibleOfLinComb H c' X' hX')) =
      ∑ i, ∑ j, conj (c i) * c' j * (σ (ofList (SepTuple.juxt
        (push TimeAxis.timeReflection (familyList (X i)))
        (push (SeparatedTuples.translate (t • v)) (familyList (X' j))))) : ℂ) := fun t => by
    have hw := smul_apply_three_eq_zero hv t
    rw [reflectionForm_eq_sum H c c' X (fun j => shiftFamily (t • v) hw (X' j))
      (fun i => familyList (X i)) (fun j => familyList (shiftFamily (t • v) hw (X' j))) hX
      (fun j => allSmoothCompact_shiftFamily _ hw (hX' j))
      (fun _ => rfl) (fun _ => rfl) _ _ (fun _ => rfl) fun a => ?_]
    · simp only [push_translate_familyList (t • v) hw]
    · show shiftActAt (t • v) (combinationSequence (linComb c' X') a) = _
      rw [combinationSequence_eq_lengthPart H c' X' hX',
        combinationSequence_eq_lengthPart H c' _ fun j => allSmoothCompact_shiftFamily _ hw (hX' j),
        lengthPart_shiftFamily]
  have e₂ : S.reflectionForm (admissibleOfLinComb H c X hX) (vacuumSeq H) *
      S.reflectionForm (vacuumSeq H) (admissibleOfLinComb H c' X' hX') =
      ∑ i, ∑ j, conj (c i) * c' j *
        ((σ (ofList (push TimeAxis.timeReflection (familyList (X i)))) *
          σ (ofList (familyList (X' j))) : ℝ) : ℂ) := by
    rw [reflectionForm_linComb_vacuum H c X hX _ fun _ => rfl,
      reflectionForm_vacuum_linComb H c' X' hX' _ fun _ => rfl, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  simp only [e₁]
  rw [e₂]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  refine Tendsto.const_mul _ ?_
  exact (Complex.continuous_ofReal.tendsto _).comp
    (hclu _ (familyList_mem_smoothSupportedIn _ (hX i)) _
      (familyList_mem_smoothSupportedIn _ (hX' j)))
theorem tendsto_reflectionForm_shift (H : Hypotheses σ S) {v : Fin 4 → ℝ} (hv : v 3 = 0)
    (hclu : WightmanReconstruction.TupleClusteringAlong σ v) (Φ Ψ : AdmissibleSeq) :
    Tendsto (fun t : ℝ => S.reflectionForm Φ (shiftSeq H (t • v) (smul_apply_three_eq_zero hv t) Ψ))
      atTop (𝓝 (S.reflectionForm Φ (vacuumSeq H) * S.reflectionForm (vacuumSeq H) Ψ)) := by
  obtain ⟨N, hN, hΦ₀, hΨ₀⟩ := exists_common_bound Φ Ψ
  obtain ⟨k, A, hk, hA, hsmall⟩ := exists_formNorm_sq_le H N hN
  refine tendsto_of_uniform_approx fun ε hε => ?_
  set M := formNorm S Φ + formNorm S Ψ + 1 with hM
  have hMpos : 0 < M := by
    have h₁ := formNorm_nonneg (S := S) Φ
    have h₂ := formNorm_nonneg (S := S) Ψ
    linarith
  set d := min 1 (ε / (2 * M)) with hd
  have hd₀ : 0 < d := lt_min one_pos (by positivity)
  have hd₁ : d ≤ 1 := min_le_left _ _
  have hdM : d * (2 * M) ≤ ε := by
    have : d ≤ ε / (2 * M) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  set δ := d / Real.sqrt (A + 1) with hδdef
  have hsq : 0 < Real.sqrt (A + 1) := Real.sqrt_pos.2 (by linarith)
  have hδ : 0 < δ := div_pos hd₀ hsq
  have hAδ : A * δ ^ 2 ≤ d ^ 2 := by
    rw [hδdef, div_pow, Real.sq_sqrt (by linarith), mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg d]
  obtain ⟨ι, instι, c, X, hX, D, hD, hDs⟩ := exists_close_linComb H Φ hN hk hΦ₀ hsmall hδ
  obtain ⟨κ, instκ, c', X', hX', E, hE, hEs⟩ := exists_close_linComb H Ψ hN hk hΨ₀ hsmall hδ
  set Φ' := admissibleOfLinComb H c X hX with hΦ'
  set Ψ' := admissibleOfLinComb H c' X' hX' with hΨ'
  have hnD : formNorm S D ≤ d :=
    (sq_le_sq₀ (formNorm_nonneg D) hd₀.le).1 (hDs.trans hAδ)
  have hnE : formNorm S E ≤ d :=
    (sq_le_sq₀ (formNorm_nonneg E) hd₀.le).1 (hEs.trans hAδ)
  have hnΦ' : formNorm S Φ' ≤ formNorm S Φ + d := (formNorm_le_add H hD).trans (by linarith)
  have hbound : formNorm S D * formNorm S Ψ + formNorm S Φ' * formNorm S E ≤ ε := by
    have h₁ := formNorm_nonneg (S := S) Φ
    have h₂ := formNorm_nonneg (S := S) Ψ
    have h₄ : formNorm S D * formNorm S Ψ ≤ d * formNorm S Ψ :=
      mul_le_mul_of_nonneg_right hnD h₂
    have h₅ : formNorm S Φ' * formNorm S E ≤ (formNorm S Φ + d) * d :=
      mul_le_mul hnΦ' hnE (formNorm_nonneg E) (by linarith)
    have h₆ : (formNorm S Φ + d) * d ≤ (formNorm S Φ + 1) * d :=
      mul_le_mul_of_nonneg_right (by linarith) hd₀.le
    linarith
  refine ⟨fun t => S.reflectionForm Φ' (shiftSeq H (t • v) (smul_apply_three_eq_zero hv t) Ψ'),
    S.reflectionForm Φ' (vacuumSeq H) * S.reflectionForm (vacuumSeq H) Ψ',
    tendsto_reflectionForm_linComb H hv hclu c c' X X' hX hX', fun t => ?_, ?_⟩
  · have hw := smul_apply_three_eq_zero hv t
    have e : S.reflectionForm Φ (shiftSeq H (t • v) hw Ψ) -
        S.reflectionForm Φ' (shiftSeq H (t • v) hw Ψ') =
        S.reflectionForm D (shiftSeq H (t • v) hw Ψ) +
          S.reflectionForm Φ' (shiftSeq H (t • v) hw E) := by
      rw [reflectionForm_sub_left H hD, reflectionForm_sub_right H (isLinComb_shiftSeq H _ hw hE)]
      ring
    show ‖S.reflectionForm Φ (shiftSeq H (t • v) hw Ψ) -
      S.reflectionForm Φ' (shiftSeq H (t • v) hw Ψ')‖ ≤ ε
    rw [e]
    refine (norm_add_le _ _).trans (le_trans (add_le_add (norm_reflectionForm_le H _ _)
      (norm_reflectionForm_le H _ _)) ?_)
    rw [formNorm_shiftSeq, formNorm_shiftSeq]
    exact hbound
  · have e : S.reflectionForm Φ (vacuumSeq H) * S.reflectionForm (vacuumSeq H) Ψ -
        S.reflectionForm Φ' (vacuumSeq H) * S.reflectionForm (vacuumSeq H) Ψ' =
        S.reflectionForm D (vacuumSeq H) * S.reflectionForm (vacuumSeq H) Ψ +
          S.reflectionForm Φ' (vacuumSeq H) * S.reflectionForm (vacuumSeq H) E := by
      rw [reflectionForm_sub_left H hD, reflectionForm_sub_right H hE]
      ring
    rw [e]
    refine (norm_add_le _ _).trans (le_trans (add_le_add ?_ ?_) hbound)
    · rw [norm_mul]
      refine (mul_le_mul (norm_reflectionForm_le H _ _) (norm_reflectionForm_le H _ _) (norm_nonneg _)
        (mul_nonneg (formNorm_nonneg _) (formNorm_nonneg _))).trans (le_of_eq ?_)
      rw [formNorm_vacuum]
      ring
    · rw [norm_mul]
      refine (mul_le_mul (norm_reflectionForm_le H _ _) (norm_reflectionForm_le H _ _) (norm_nonneg _)
        (mul_nonneg (formNorm_nonneg _) (formNorm_nonneg _))).trans (le_of_eq ?_)
      rw [formNorm_vacuum]
      ring
end Limit
section Schwinger
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
theorem isCLMSequence_of_schwinger (hS0 : ∀ c : flatOffDiagonalAt 0, S 0 c = c.1)
    (hSch : TestSpaces.IsSchwingerFamily σ (WightmanReconstruction.flatSequenceAsMaps S)) :
    IsCLMSequence S := by
  refine ⟨hS0, fun p => ?_⟩
  obtain ⟨hl, hb, -⟩ := hSch.1 (p + 1) (Nat.succ_pos p)
  exact (SchwartzAxioms.isContinuousOnFlat_iff _).1 ⟨hl, hb⟩
theorem agreesOnTensors_of_schwinger
    (hSch : TestSpaces.IsSchwingerFamily σ (WightmanReconstruction.flatSequenceAsMaps S)) :
    AgreesOnTensors σ S := by
  intro p X hs h
  exact (hSch.1 (p + 1) (Nat.succ_pos p)).2.2 X hs
    ((SchwartzAxioms.flatSchwartzSet_eq (n := p + 1)).superset h)
theorem shift_invariant_of_schwinger (hC : TestSpaces.SchwingerPropertiesTransfer)
    (hσ : TestSpaces.IsSepFunctional σ)
    (hinv : WightmanReconstruction.IsTranslationInvariant σ)
    (hSch : TestSpaces.IsSchwingerFamily σ (WightmanReconstruction.flatSequenceAsMaps S))
    (p : ℕ) (w : Fin 4 → ℝ) (φ : schwartzFlatOffDiagonal (p + 1)) :
    ∃ h : shiftAct w φ.1 ∈ schwartzFlatOffDiagonal (p + 1),
      S.atSucc p ⟨_, h⟩ = S.atSucc p φ := by
  classical
  set T := WightmanReconstruction.flatSequenceAsMaps S with hT
  have hb : ∀ n, ∃ (k : ℕ) (c : ℝ), 1 ≤ n → 0 < k ∧ 0 ≤ c ∧
      ∀ φ : TestSpaces.flatSchwartzSet n,
        ENNReal.ofReal ‖T n φ‖ ≤ ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1 := fun n => by
    by_cases hn : 1 ≤ n
    · obtain ⟨k, c, h⟩ := (hSch.1 n hn).2.1
      exact ⟨k, c, fun _ => h⟩
    · exact ⟨1, 0, fun h => absurd h hn⟩
  choose k c hkc using hb
  have hB : TestSpaces.IsBoundedExtensionFamily σ T k c := ⟨hSch.2, fun n hn => by
    obtain ⟨h₁, h₂, h₃⟩ := hkc n hn
    exact ⟨(hSch.1 n hn).1, h₁, h₂, h₃, (hSch.1 n hn).2.2⟩⟩
  obtain ⟨-, h₁, -⟩ := hC σ T k c hσ hB
  set r := UpperHalfTensors.translateMotion w with hr
  have hI : TestSpaces.SepTupleInvariant σ (p + 1) r := fun X Y _ hY =>
    (congrArg (fun Z : TestSpaces.SepTupleOfCard (p + 1) => σ ⟨p + 1, Z⟩)
      (Subtype.ext hY : Y = ⟨Motions.actOnTuple r X.1, _⟩)).trans (hinv w ⟨p + 1, X⟩)
  obtain ⟨hm, e⟩ := (h₁ (p + 1) (Nat.succ_pos p)
    ⟨φ.1, (SchwartzAxioms.flatSchwartzSet_eq (n := p + 1)).superset φ.2⟩).1 r hI
  have ef : shiftAct w φ.1 = Motions.actOnFun r φ.1 :=
    funext fun x => by
      rw [shiftAct_apply, hr, WightmanReconstruction.actOnFun_translateMotion]
  have h' : Motions.actOnFun r φ.1 ∈ schwartzFlatOffDiagonal (p + 1) :=
    (SchwartzAxioms.flatSchwartzSet_eq (n := p + 1)).subset hm
  refine ⟨ef.symm ▸ h', ?_⟩
  have e₂ : S (p + 1) ⟨Motions.actOnFun r φ.1, h'⟩ = S (p + 1) φ := e
  exact (congrArg (S (p + 1)) (Subtype.ext ef)).trans e₂
end Schwinger
end AdmissibleClustering
namespace WightmanReconstruction
open AdmissibleClustering ConfigSpace
theorem ClusteringTransfer.proof (hF : TestSpaces.Elementary.BasicProperties)
    (hT : AdmissibleForm.Statement)
    (hP : ConfigSpace.SesquilinearPosSemidefStatement)
    (hR : ReflectionPositivityFromValues.Statement)
    (hC : TestSpaces.SchwingerPropertiesTransfer)
    (hA : ConfigSpace.CombinationSequenceAdmissibleLinear)
    (hM : MotionsTranslations.Statement)
    (hL : ConfigSpace.LinCombClosure) :
    ClusteringTransfer.Statement := by
  intro σ S v hσ hinv hpos hS0 hSch hv hclu Φ Ψ hΦ hΨ
  have hseq := isCLMSequence_of_schwinger hS0 hSch
  have hval := agreesOnTensors_of_schwinger hSch
  have hE2 : ConfigSpace.IsOSPositive S :=
    hR σ S hσ ⟨hseq.1, fun p => (hseq.2 p).1⟩ hseq.2 hval fun F => hpos F.1 F.2
  have hform := hP S hseq
  have H : Hypotheses σ S :=
    { basic := hF, formFacts := hT, combSeq := hA, translatePlus := hM.2.1, linClosure := hL,
      nil_eq_one := hσ.1, isCLM := hseq, agrees := hval, sesq := hform.1,
      posSemidef := hform.2 hE2, shiftInvariant := shift_invariant_of_schwinger hC hσ hinv hSch }
  have h := tendsto_reflectionForm_shift H (v := v) hv hclu ⟨Φ, hΦ⟩ ⟨Ψ, hΨ⟩
  rw [reflectionForm_vacuum_right, reflectionForm_vacuum_left] at h
  exact h
end WightmanReconstruction
end YangMills.Construction
end
