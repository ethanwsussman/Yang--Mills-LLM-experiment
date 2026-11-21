import YangMills.Construction.Continuum.OperationsKeepTheSpaces
import YangMills.Construction.Continuum.OperationsOnTestFunctions
import YangMills.Construction.Continuum.TensorProductsAcrossTheTimeZeroPlane
import YangMills.Construction.Continuum.ArgumentsOfTheConditionsLieInTheirDomainsAndTheirSumsAreFinite
import YangMills.Construction.Continuum.TheThreeOpenSetsAndTheThreeSpaces
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConditionDomains
open ConfigSpace
theorem flipConjAt_zeroOfDegree {n : ℕ} :
    flipConjAt (zeroOfDegree n) = zeroOfDegree n := by
  cases n with
  | zero =>
    show conj (0 : ℂ) = 0
    simp
  | succ n =>
    funext x
    show conj (0 : ℂ) = 0
    simp
theorem shiftActAt_zeroOfDegree (w : Fin 4 → ℝ) {n : ℕ} :
    shiftActAt w (zeroOfDegree n) = zeroOfDegree n := by
  cases n with
  | zero => rfl
  | succ n => rfl
theorem smulAt_zero_left {n : ℕ} (ψ : FnOrScalar n) : smulAt 0 ψ = zeroOfDegree n := by
  cases n with
  | zero => exact (fun a : ℂ => by simp : ∀ a : ℂ, (0 : ℂ) * a = 0) ψ
  | succ n =>
    funext y
    show (0 : ℂ) * ψ y = 0
    simp
theorem smulAt_zero_right (c : ℂ) {n : ℕ} : smulAt c (zeroOfDegree n) = zeroOfDegree n := by
  cases n with
  | zero =>
    show c * (0 : ℂ) = 0
    simp
  | succ n =>
    funext y
    show c * (0 : ℂ) = 0
    simp
theorem cast_zeroOfDegree {a b : ℕ} (h : a = b) : (h ▸ zeroOfDegree a : FnOrScalar b) = zeroOfDegree b := by
  subst h
  rfl
theorem tensorAt_zero_left {q q' : ℕ} (ψ : FnOrScalar q') :
    tensorAt (zeroOfDegree q) ψ = zeroOfDegree (q + q') := by
  cases q with
  | zero =>
    show (Nat.zero_add q').symm ▸ smulAt (0 : ℂ) ψ = _
    rw [smulAt_zero_left, cast_zeroOfDegree]
  | succ m =>
    cases q' with
    | zero => exact smulAt_zero_right (n := m + 1) (show ℂ from ψ)
    | succ k =>
      funext z
      show (0 : ℂ) * ψ _ = 0
      simp
theorem tensorAt_zero_right {q q' : ℕ} (χ : FnOrScalar q) :
    tensorAt χ (zeroOfDegree q') = zeroOfDegree (q + q') := by
  cases q with
  | zero =>
    show (Nat.zero_add q').symm ▸ smulAt (show ℂ from χ) (zeroOfDegree q') = _
    rw [smulAt_zero_right, cast_zeroOfDegree]
  | succ m =>
    cases q' with
    | zero => exact smulAt_zero_left (n := m + 1) χ
    | succ k =>
      funext z
      show χ _ * (0 : ℂ) = 0
      simp
end YangMills.Construction.ConditionDomains

namespace YangMills.Construction.ConfigSpace.DomainsAndFiniteSums
theorem flat_subspace_facts (h : OpenLociAndFlatSubspaces) {n : ℕ} (hn : 1 ≤ n) :
    schwartzFlatOffPosTime n ⊆ schwartzFlatOffDiagonal n ∧
      schwartzFlatOffNegTime n ⊆ schwartzFlatOffDiagonal n ∧
      (0 : Config n → ℂ) ∈ schwartzFlatOffDiagonal n ∧
      ∀ (c : ℂ) (φ : Config n → ℂ), φ ∈ schwartzFlatOffDiagonal n →
        c • φ ∈ schwartzFlatOffDiagonal n := by
  obtain ⟨-, -, S, W, Wp, Wm, -, hW, hWp, hWm, -, -, -, hpW, hmW⟩ := h n hn
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, fun c φ hφ => ?_⟩
  · rw [← hWp] at hφ
    rw [← hW]
    exact hpW hφ
  · rw [← hWm] at hφ
    rw [← hW]
    exact hmW hφ
  · rw [← hW]
    exact W.zero_mem
  · rw [← hW] at hφ ⊢
    exact W.smul_mem c hφ
theorem mem_flatOffDiagonalAt_cast {a b : ℕ} (h : a = b) {f : FnOrScalar a}
    (hf : f ∈ flatOffDiagonalAt a) :
    (h ▸ f : FnOrScalar b) ∈ flatOffDiagonalAt b := by
  subst h
  exact hf
theorem smulAt_mem (h : OpenLociAndFlatSubspaces) (c : ℂ) {n : ℕ}
    {ψ : FnOrScalar n} (hψ : ψ ∈ flatOffDiagonalAt n) :
    smulAt c ψ ∈ flatOffDiagonalAt n := by
  cases n with
  | zero => exact Set.mem_univ _
  | succ n => exact (flat_subspace_facts h (Nat.succ_pos n)).2.2.2 c ψ hψ
theorem mem_offDiagonal_of_offPosTime (h : OpenLociAndFlatSubspaces) {n : ℕ}
    {ψ : FnOrScalar n} (hψ : ψ ∈ flatOffPosTimeAt n) :
    ψ ∈ flatOffDiagonalAt n := by
  cases n with
  | zero => exact Set.mem_univ _
  | succ n => exact (flat_subspace_facts h (Nat.succ_pos n)).1 hψ
theorem flatSchwartzSet_eq_schwartzFlatOffDiagonal (n : ℕ) :
    TestSpaces.flatSchwartzSet n = schwartzFlatOffDiagonal n := by
  ext φ
  constructor
  · rintro ⟨hs, hf⟩
    exact ⟨hs, hs.1, isOpen_distinctArgs, fun x hx => ⟨hs.1, fun α => hf α x hx⟩⟩
  · rintro ⟨hs, -, -, hf⟩
    exact ⟨hs, fun α x hx => (hf x hx).2 α⟩
theorem flipConj_mem (hA : TestFunctionOps.OperationsStatement) {m : ℕ}
    {φ : Config (m + 1) → ℂ} (hφ : φ ∈ schwartzFlatOffDiagonal (m + 1)) :
    flipConj φ ∈ schwartzFlatOffDiagonal (m + 1) := by
  have hf : φ ∈ TestSpaces.flatSchwartzSet (m + 1) := by
    rw [flatSchwartzSet_eq_schwartzFlatOffDiagonal]
    exact hφ
  have h := (((hA.1 (m + 1) 1 (Nat.succ_pos m) one_pos 1
    Motions.RigidMotion.timeReflection).2.1 φ hf.1).1.2.2.2.1 hf).2.2
  rw [flatSchwartzSet_eq_schwartzFlatOffDiagonal] at h
  exact h
theorem flipConjAt_mem (hA : TestFunctionOps.OperationsStatement)
    (hS : OpenLociAndFlatSubspaces) {q : ℕ} {φ : FnOrScalar q}
    (hφ : φ ∈ flatOffPosTimeAt q) :
    flipConjAt φ ∈ flatOffDiagonalAt q := by
  cases q with
  | zero => exact Set.mem_univ _
  | succ m => exact flipConj_mem hA (mem_offDiagonal_of_offPosTime hS hφ)
theorem tensorAt_flipConjAt_mem (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    {q q' : ℕ} {φ : FnOrScalar q} {ψ : FnOrScalar q'}
    (hφ : φ ∈ flatOffPosTimeAt q) (hψ : ψ ∈ flatOffPosTimeAt q') :
    tensorAt (flipConjAt φ) ψ ∈ flatOffDiagonalAt (q + q') := by
  cases q with
  | zero => exact mem_flatOffDiagonalAt_cast _ (smulAt_mem hS _ (mem_offDiagonal_of_offPosTime hS hψ))
  | succ m =>
    have hφ' : φ ∈ schwartzFlatOffPosTime (m + 1) := hφ
    cases q' with
    | zero =>
      have hneg : flipConj (n := m + 1) φ ∈ schwartzFlatOffNegTime (m + 1) := by
        obtain ⟨-, -, -, -, himg⟩ := hO (m + 1) (Nat.succ_pos m)
        rw [← himg]
        exact ⟨φ, hφ', rfl⟩
      exact smulAt_mem hS _ ((flat_subspace_facts hS (Nat.succ_pos m)).2.1 hneg)
    | succ k =>
      have hψ' : ψ ∈ schwartzFlatOffPosTime (k + 1) := hψ
      exact (hT (m + 1) (k + 1) (Nat.succ_pos m) (Nat.succ_pos k) 0 ⟨φ, hφ'.1⟩ ⟨ψ, hψ'.1⟩).2.2
        hφ' hψ'
theorem smul_mem_zeroTimeHyperplane {v : Fin 4 → ℝ} (hv : v ∈ zeroTimeHyperplane) (t : ℝ) :
    t • v ∈ zeroTimeHyperplane := by
  have hv' : v 3 = 0 := hv
  show (t • v) 3 = 0
  simp [hv']
theorem shiftActAt_mem (hO : OperationsPreserveSchwartzSpaces) {w : Fin 4 → ℝ}
    (hw : w ∈ zeroTimeHyperplane) {n : ℕ} {ψ : FnOrScalar n}
    (hψ : ψ ∈ flatOffPosTimeAt n) :
    shiftActAt w ψ ∈ flatOffPosTimeAt n := by
  cases n with
  | zero => exact Set.mem_univ _
  | succ n => exact ((hO (n + 1) (Nat.succ_pos n)).2.1 w hw).1 hψ
theorem flipConjAt_zero {n : ℕ} :
    flipConjAt (zeroOfDegree n) = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.flipConjAt_zeroOfDegree <;> assumption
theorem shiftActAt_zero (w : Fin 4 → ℝ) {n : ℕ} :
    shiftActAt w (zeroOfDegree n) = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.shiftActAt_zeroOfDegree <;> assumption
theorem tensorAt_zero_left {q q' : ℕ} (ψ : FnOrScalar q') :
    tensorAt (zeroOfDegree q) ψ = zeroOfDegree (q + q') := by apply _root_.YangMills.Construction.ConditionDomains.tensorAt_zero_left <;> assumption
theorem tensorAt_zero_right {q q' : ℕ} (χ : FnOrScalar q) :
    tensorAt χ (zeroOfDegree q') = zeroOfDegree (q + q') := by apply _root_.YangMills.Construction.ConditionDomains.tensorAt_zero_right <;> assumption
theorem evalAt_zero (hS : OpenLociAndFlatSubspaces) {S : FlatSequence}
    (hseq : IsLinearFunctionalSeq S) (n : ℕ) : S.evalAt (zeroOfDegree n) = 0 := by
  cases n with
  | zero =>
    rw [FlatSequence.evalAt_of_mem S (Set.mem_univ _)]
    exact hseq.1 ⟨zeroOfDegree 0, Set.mem_univ _⟩
  | succ m =>
    have h0 : zeroOfDegree (m + 1) ∈ flatOffDiagonalAt (m + 1) :=
      (flat_subspace_facts hS (Nat.succ_pos m)).2.2.1
    rw [FlatSequence.evalAt_of_mem S h0]
    have h := hseq.2 m 0 0 ⟨zeroOfDegree (m + 1), h0⟩ ⟨zeroOfDegree (m + 1), h0⟩
      ⟨zeroOfDegree (m + 1), h0⟩ (by
        funext y
        show (0 : ℂ) = 0 * 0 + 0 * 0
        simp)
    exact show S.atSucc m ⟨zeroOfDegree (m + 1), h0⟩ = 0 from by simpa using h
theorem domainsAndFiniteSums_holds (hS : OpenLociAndFlatSubspaces)
    (hO : OperationsPreserveSchwartzSpaces)
    (hT : TensorAcrossZeroTime)
    (hA : TestFunctionOps.OperationsStatement) :
    domainsAndFiniteSumsStatement := by
  intro S hseq
  refine ⟨fun m φ => ⟨fun r => ?_, fun ς => ?_, flipConj_mem hA φ.2⟩, fun Φ Ψ hΦ hΨ => ?_⟩
  · exact ((hO (m + 1) (Nat.succ_pos m)).1 φ.1 φ.2 r 1).1
  · exact ((hO (m + 1) (Nat.succ_pos m)).1 φ.1 φ.2 timeFlipMotion ς).2
  · refine ⟨fun q => flipConjAt_mem hA hS (Φ q).2,
      fun q' => mem_offDiagonal_of_offPosTime hS (Ψ q').2,
      fun q q' => tensorAt_flipConjAt_mem hT hO hS (Φ q).2 (Ψ q').2,
      fun v hv t q q' => tensorAt_flipConjAt_mem hT hO hS (Φ q).2
        (shiftActAt_mem hO (smul_mem_zeroTimeHyperplane hv t) (Ψ q').2), ?_, fun v _ t => ?_, ?_, ?_⟩
    · refine (hΦ.prod hΨ).subset fun p hp => ⟨fun e => hp ?_, fun e => hp ?_⟩
      · rw [e, flipConjAt_zero, tensorAt_zero_left]
        exact evalAt_zero hS hseq _
      · rw [e, tensorAt_zero_right]
        exact evalAt_zero hS hseq _
    · refine (hΦ.prod hΨ).subset fun p hp => ⟨fun e => hp ?_, fun e => hp ?_⟩
      · rw [e, flipConjAt_zero, tensorAt_zero_left]
        exact evalAt_zero hS hseq _
      · rw [e, shiftActAt_zero, tensorAt_zero_right]
        exact evalAt_zero hS hseq _
    · refine hΦ.subset fun q hq e => hq ?_
      rw [e, flipConjAt_zero]
      exact evalAt_zero hS hseq _
    · refine hΨ.subset fun q hq e => hq ?_
      rw [e]
      exact evalAt_zero hS hseq _
end YangMills.Construction.ConfigSpace.DomainsAndFiniteSums
end
