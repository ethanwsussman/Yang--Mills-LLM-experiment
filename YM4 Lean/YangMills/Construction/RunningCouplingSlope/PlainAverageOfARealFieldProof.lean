import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOneOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.TheLengthsOfTheWholeChainAreALocalFamilyProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace CompactFieldMean
open Tower Matrices Matrix
private def IsQuaternionic (A : ComplexMatrix2) : Prop := Matrix.adjugate A = Aᴴ
private theorem isQuaternionic_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    IsQuaternionic g := by apply _root_.YangMills.DeltaSharedProofs.p2612 <;> assumption
private theorem IsQuaternionic.add {A B : ComplexMatrix2} (hA : IsQuaternionic A)
    (hB : IsQuaternionic B) : IsQuaternionic (A + B) := by apply _root_.YangMills.DeltaSharedProofs.p501936 <;> assumption
private theorem IsQuaternionic.real_smul (r : ℝ) {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    IsQuaternionic ((r : ℂ) • A) := by apply _root_.YangMills.DeltaSharedProofs.p500416 <;> assumption
private theorem isQuaternionic_zero : IsQuaternionic 0 := by apply _root_.YangMills.DeltaSharedProofs.p502226 <;> assumption
private theorem isQuaternionic_sum {ι : Type*} (s : Finset ι) (f : ι → ComplexMatrix2)
    (h : ∀ i ∈ s, IsQuaternionic (f i)) : IsQuaternionic (∑ i ∈ s, f i) := by apply _root_.YangMills.DeltaSharedProofs.p502446 <;> assumption
private theorem IsQuaternionic.det_nonneg_real {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    ∃ d : ℝ, 0 ≤ d ∧ Matrix.det A = (d : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p501399 <;> assumption
private theorem inv_mem_specialUnitary {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
variable {L n k j : ℕ}
private theorem pathHolonomy_mem_specialUnitary (U : Edge L n k j → ComplexMatrix2)
    (hU : ∀ e, U e ∈ ComplexMatrix2.specialUnitary) (p : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy U p ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.SharedProofs.p132511 <;> assumption
end CompactFieldMean
open CompactFieldMean Tower Matrices in
theorem normalizedMean_of_compactField (hnear : NormalizedMeanNearOne)
    (hblocks : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    NormalizedMeanOfCompactField := by
  intro L hL
  obtain ⟨ρ, hρ, H⟩ := hnear L hL
  refine ⟨ρ, hρ, ?_⟩
  intro n k j hn hj U hU hUρ c hc
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hUs : ∀ e, U e ∈ ComplexMatrix2.specialUnitary := fun e => hU.1 e (Set.mem_univ e)
  have hUc : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun e _ => (Matrix.mem_specialUnitaryGroup_iff.1 (hUs e)).2, hU.2⟩
  obtain ⟨hrad0, -, -, hdetOne, -⟩ := H n k j hn hj U hUc hUρ c hc
  have hcard := ((hblocks L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have hne : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero hne
    exact Set.toFinite _
  have hcontour : ∀ x σ, contourHolonomy U c x σ ∈ ComplexMatrix2.specialUnitary := fun x σ =>
    ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (pathHolonomy_mem_specialUnitary U hUs _)
        (pathHolonomy_mem_specialUnitary U hUs _))
      (inv_mem_specialUnitary (pathHolonomy_mem_specialUnitary U hUs _))
  have hweight : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
      ((1 / (24 * (L : ℝ) ^ 4) : ℝ) : ℂ) := by
    rw [PeriodicLattice.inverseFourthPowerWeight]
    push_cast
    rw [zpow_neg]
    field_simp
  have hquat : IsQuaternionic (contourMean U c) := by
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, hweight]
    refine IsQuaternionic.real_smul _ (isQuaternionic_sum _ _ fun x _ =>
      isQuaternionic_sum _ _ fun σ _ => isQuaternionic_of_mem (hcontour x σ))
  obtain ⟨d, hd0, hd⟩ := hquat.det_nonneg_real
  have hradius : meanRadius U c = (d : ℂ) ^ (1 / 2 : ℂ) := by
    rw [meanRadius, hd]
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hrad0
      rw [hradius, ← h]
      simp
  have hreal : meanRadius U c = ((d ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hradius, Complex.ofReal_cpow hd0]
    norm_num
  have hre : (meanRadius U c).re = d ^ (1 / 2 : ℝ) := by
    rw [hreal, Complex.ofReal_re]
  refine ⟨by rw [hre]; exact hreal, by rw [hre]; exact Real.rpow_pos_of_pos hdpos _, ?_⟩
  have hquatMean : IsQuaternionic (normalizedMean U c) := by
    rw [normalizedMean, hreal, ← Complex.ofReal_inv]
    exact IsQuaternionic.real_smul _ hquat
  have hdet : Matrix.det (normalizedMean U c) = 1 := hdetOne
  change normalizedMean U c ∈ ComplexMatrix2.specialUnitary
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨(Matrix.mem_unitaryGroup_iff').2 ?_, hdet⟩
  have hadj : Matrix.adjugate (normalizedMean U c) * normalizedMean U c = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  rw [← hadj]
  congr 1
  exact hquatMean.symm
end YangMills.Construction.RunningCouplingSlope
end
