import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Lattice.PivotBondsOfTheCoarseBondsLieApart
import YangMills.Construction.Towers.LinearMapsAreOnto
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBonds
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import Mathlib
open Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SurjectivityProof
open Matrices TrivialLinearization
variable {L n k j : ℕ}
private def liftAlongPivots (C : Edge L n k (j + 1) → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in
  PeriodicLattice.bondFormOfPositive fun b =>
    if h : ∃ c : Edge L n k (j + 1), c.IsPositivelyOriented ∧ b = PeriodicLattice.pivot c then
      ((L : ℝ) ^ 3) • C h.choose
    else 0
private theorem neg_lt_levelDepth (hn : 0 < n) (hj : j ≤ k) :
    -(n : ℤ) < PeriodicLattice.levelDepth k j := by
  simp only [PeriodicLattice.levelDepth]
  omega
private theorem opposite_opposite {i : ℤ} (b : PeriodicLattice.Bond L n i) :
    b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
private theorem liftAlongPivots_of_pos (C : Edge L n k (j + 1) → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    open Classical in
    liftAlongPivots C b =
      if h : ∃ c : Edge L n k (j + 1), c.IsPositivelyOriented ∧ b = PeriodicLattice.pivot c then
        ((L : ℝ) ^ 3) • C h.choose
      else 0 := by
  simp only [liftAlongPivots, PeriodicLattice.bondFormOfPositive, if_pos hb]
private theorem liftAlongPivots_mem (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) {C : Edge L n k (j + 1) → ComplexMatrix2} (hC : C ∈ edgeFormSpace L n k (j + 1)) :
    liftAlongPivots C ∈ edgeFormSpace L n k j := by
  classical
  have hL2 : 2 ≤ L := by have := hL.2; omega
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [liftAlongPivots_of_pos C hb]
    split_ifs with h
    · exact ComplexMatrix2.hermitianTraceless.smul_mem _ (hC.1 _ h.choose_spec.1)
    · exact ComplexMatrix2.hermitianTraceless.zero_mem
  · have hoo : b.opposite.opposite = b := opposite_opposite b
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
        (neg_lt_levelDepth hn hj.le) b with ⟨hb, hr⟩ | ⟨hr, hb⟩
    · simp only [liftAlongPivots, PeriodicLattice.bondFormOfPositive, if_pos hb, if_neg hr, hoo]
    · simp only [liftAlongPivots, PeriodicLattice.bondFormOfPositive, if_pos hr, if_neg hb, neg_neg]
private theorem pivotScale_smul_cube (hL : Conventions.IsAdmissibleBlockingFactor L) (X : ComplexMatrix2) :
    pivotScale L • (((L : ℝ) ^ 3) • X) = X := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  rw [← Complex.coe_smul ((L : ℝ) ^ 3), smul_smul, pivotScale, ← Complex.ofReal_mul]
  have : (L : ℝ) ^ (-3 : ℤ) * (L : ℝ) ^ 3 = 1 := by
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ hL0)
  rw [this]
  simp
private theorem exists_preimage_step (hP : LinearizationFacts.pivotFormsStatement)
    (hR : AxisPathReversal.MainStatement)
    (hV : PeriodicLattice.PivotBondsLieApart)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {C : Edge L n k (j + 1) → ComplexMatrix2} (hC : C ∈ edgeFormSpace L n k (j + 1)) :
    ∃ B ∈ edgeFormSpace L n k j, linearSmoothing L n k j B = C ∧ crossingSmoothing L n k j B = C := by
  classical
  have hB := liftAlongPivots_mem hL hn hj hC
  have facts : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      (PeriodicLattice.pivot c : Edge L n k j).IsPositivelyOriented ∧
        ∀ c' : Edge L n k (j + 1), c'.IsPositivelyOriented →
          (PeriodicLattice.pivot c' : Edge L n k j) = PeriodicLattice.pivot c → c' = c := by
    intro c hc
    obtain ⟨μ, hμ⟩ := id hc
    have p := hV L n k j hL hn hj ⟨c, hc⟩ μ hμ
    exact ⟨p.positive c hc, fun c' hc' h => p.injective c' c hc' hc h⟩
  have hvalue : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      liftAlongPivots C (PeriodicLattice.pivot c : Edge L n k j) = ((L : ℝ) ^ 3) • C c := by
    intro c hc
    obtain ⟨hpos, hinj⟩ := facts c hc
    have hex : ∃ c' : Edge L n k (j + 1), c'.IsPositivelyOriented ∧
        (PeriodicLattice.pivot c : Edge L n k j) = PeriodicLattice.pivot c' := ⟨c, hc, rfl⟩
    rw [liftAlongPivots_of_pos C hpos, dif_pos hex]
    have := hinj hex.choose hex.choose_spec.1 hex.choose_spec.2.symm
    rw [this]
  have hsupp : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → b ≠ PeriodicLattice.pivot c) →
        liftAlongPivots C b = 0 := by
    intro b hb hno
    rw [liftAlongPivots_of_pos C hb, dif_neg]
    rintro ⟨c, hc, h⟩
    exact hno c hc h
  obtain ⟨-, -, hstep⟩ := hP L hL n k j hn hj _ hB hsupp
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      linearSmoothing L n k j (liftAlongPivots C) c = C c ∧
        crossingSmoothing L n k j (liftAlongPivots C) c = C c := by
    intro c hc
    obtain ⟨h₁, h₂⟩ := hstep c hc
    have h₃ : crossingSmoothing L n k j (liftAlongPivots C) c = C c := by
      rw [h₂, hvalue c hc, pivotScale_smul_cube hL]
    exact ⟨h₁.trans h₃, h₃⟩
  have hside := (hR L hL k).1 n hn
  have orient : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented :=
    fun c =>
      (PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
        (neg_lt_levelDepth hn hj) c).elim (fun h => Or.inl h.1) fun h => Or.inr h.1
  have hform := ((hside.1 j hj.le).1) _ hB
  refine ⟨liftAlongPivots C, hB, funext fun c => ?_, funext fun c => ?_⟩
  · rcases orient c with hc | hc
    · exact (hpos c hc).1
    · have h := (hside.2 j hj c.opposite _ hform).2
      rw [opposite_opposite, (hpos _ hc).1, hC.2 c, neg_neg] at h
      exact h
  · rcases orient c with hc | hc
    · exact (hpos c hc).2
    · have h := (hside.2 j hj c.opposite _ hform).1
      rw [opposite_opposite] at h
      have h' : crossingSmoothing L n k j (liftAlongPivots C) c =
          -crossingSmoothing L n k j (liftAlongPivots C) c.opposite := by
        simp only [crossingSmoothing, h, smul_neg]
      rw [h', (hpos _ hc).2, hC.2 c, neg_neg]
private theorem iterate_surjective
    (f : ∀ i, (Edge L n k i → ComplexMatrix2) → Edge L n k (i + 1) → ComplexMatrix2)
    (hf : ∀ i, i < k → ∀ C ∈ edgeFormSpace L n k (i + 1), ∃ B ∈ edgeFormSpace L n k i, f i B = C)
    (m : ℕ) :
    m ≤ k → ∀ C ∈ edgeFormSpace L n k m, ∃ B ∈ edgeFormSpace L n k 0,
      PeriodicLattice.iterateFromBare f m B = C := by
  induction m with
  | zero => exact fun _ C hC => ⟨C, hC, rfl⟩
  | succ m ih =>
    intro hm C hC
    obtain ⟨B', hB', rfl⟩ := hf m (by omega) C hC
    obtain ⟨B, hB, rfl⟩ := ih (by omega) B' hB'
    exact ⟨B, hB, rfl⟩
theorem surjectivityStatement_holds (hP : LinearizationFacts.pivotFormsStatement)
    (hR : AxisPathReversal.MainStatement)
    (hV : PeriodicLattice.PivotBondsLieApart) : LinearizationFacts.surjectivityStatement := by
  intro L hL n k j m hn hj hm
  have hstep : ∀ i, i < k → ∀ C ∈ edgeFormSpace L n k (i + 1), ∃ B ∈ edgeFormSpace L n k i,
      linearSmoothing L n k i B = C ∧ crossingSmoothing L n k i B = C :=
    fun i hi C hC => exists_preimage_step hP hR hV hL hn hi hC
  refine ⟨fun C hC => ?_, fun C hC => ?_, ?_, ?_⟩
  · obtain ⟨B, hB, h, -⟩ := hstep j hj C hC
    exact ⟨B, hB, h⟩
  · obtain ⟨B, hB, -, h⟩ := hstep j hj C hC
    exact ⟨B, hB, h⟩
  · exact iterate_surjective (linearSmoothing L n k) (fun i hi C hC => by
      obtain ⟨B, hB, h, -⟩ := hstep i hi C hC
      exact ⟨B, hB, h⟩) m hm
  · exact iterate_surjective (crossingSmoothing L n k) (fun i hi C hC => by
      obtain ⟨B, hB, -, h⟩ := hstep i hi C hC
      exact ⟨B, hB, h⟩) m hm
end YangMills.Construction.Tower.SurjectivityProof
end
