import YangMills.Construction.RunningCouplingSlope.CovarianceOfTheFunctionOfTheWholeChainProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesNearOne
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace MeanIterates
open Tower Matrices
variable {L n k j : ℕ}
private theorem meanIterate_succ_of_positive (U : Edge L n k 0 → ComplexMatrix2) (h : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    meanIterate U (j + 1) c = normalizedMean (meanIterate U j) c := by
  simp only [meanIterate, levelField, dif_pos h, fieldOfPositiveValues, dif_pos hc]
  exact one_mul _
private theorem meanIterate_succ_of_negative (U : Edge L n k 0 → ComplexMatrix2) (h : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬ c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    meanIterate U (j + 1) c = (normalizedMean (meanIterate U j) c.opposite)⁻¹ := by
  simp only [meanIterate, levelField, dif_pos h, fieldOfPositiveValues, dif_neg hc, dif_pos hc']
  congr 1
  exact one_mul _
private theorem continuousAt_inv_at_one : ContinuousAt (fun A : ComplexMatrix2 => A⁻¹) 1 := by apply _root_.YangMills.SharedProofs.p45833 <;> assumption
end MeanIterates
open MeanIterates Tower Matrices in
theorem meanIteratesTendToOne_holds (hS : MeanDerivOnForms.Claim)
    (hA : NormalizedMeanAnalytic) (hD : NormalizedMeanAtOne) :
    MeanIteratesTendToOne := by
  intro L hL k n hn j
  induction j with
  | zero =>
    intro _
    exact tendsto_id
  | succ j ih =>
    intro hj
    have hlt : j < k := by omega
    have IH := ih (by omega)
    have hL2 : 2 ≤ L := by
      have := hL.2
      omega
    haveI : NeZero L := ⟨by omega⟩
    have hX : ∀ b : Edge L n k (j + 1),
        Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
      PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
        (by simp only [PeriodicLattice.levelDepth]; omega) b
    have hfin : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
    let _ : Fintype (Edge L n k j) := Fintype.ofFinite _
    obtain ⟨ρ, hρ, HA⟩ := hA L hL
    have hflat : (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
      ⟨fun _ _ => by simp [PeriodicLattice.complexGaugeGroup, ComplexMatrix2.unitDeterminant],
        fun _ _ => (Matrix.inv_eq_right_inv (mul_one 1)).symm⟩
    have hcont : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → Tendsto
        (fun U : Edge L n k 0 → ComplexMatrix2 => normalizedMean (meanIterate U j) c)
        (𝓝[fieldSpace L n k 0] fun _ => (1 : ComplexMatrix2)) (𝓝 1) := by
      intro c hc
      have h1 := (HA n k j hn hlt _ hflat (fun b => by simpa using hρ) c hc).2.continuousAt
      have h2 := (hD L hL n k j hn hlt 0 (edgeFormSpace L n k j).zero_mem c hc).2.2.1
      have h3 := h1.tendsto
      rw [h2] at h3
      exact h3.comp (IH.mono_right nhdsWithin_le_nhds)
    have hev := IH.eventually (hS L hL n k j hn hlt)
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, ?_⟩
    · rcases hX b with ⟨hp, hn'⟩ | ⟨hp, hn'⟩
      · have e : (fun U : Edge L n k 0 → ComplexMatrix2 => meanIterate U (j + 1) b) =
            fun U => normalizedMean (meanIterate U j) b := by
          funext U
          exact meanIterate_succ_of_positive U hlt b hp
        rw [e]
        exact hcont b hp
      · have e : (fun U : Edge L n k 0 → ComplexMatrix2 => meanIterate U (j + 1) b) =
            fun U => (normalizedMean (meanIterate U j) b.opposite)⁻¹ := by
          funext U
          exact meanIterate_succ_of_negative U hlt b hn' hp
        rw [e]
        have h4 := continuousAt_inv_at_one.tendsto.comp (hcont _ hp)
        have h5 : (1 : ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
        rw [h5] at h4
        exact h4
    · filter_upwards [hev] with U hU
      obtain ⟨-, hreal, -⟩ := hU
      have hval : ∀ b : Edge L n k (j + 1), b.IsPositivelyOriented →
          meanIterate U (j + 1) b ∈ ComplexMatrix2.specialUnitary :=
        fun b hb => by
          rw [meanIterate_succ_of_positive U hlt b hb]
          exact (hreal b hb).2.2
      have hinvmem : ∀ {g : ComplexMatrix2}, g ∈ ComplexMatrix2.specialUnitary →
          g⁻¹ ∈ ComplexMatrix2.specialUnitary := by
        intro g hg
        rw [Matrix.mem_specialUnitaryGroup_iff] at hg ⊢
        obtain ⟨hu, hd⟩ := hg
        have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
        have h2 : g⁻¹ = star g := Matrix.inv_eq_left_inv h1
        rw [h2]
        refine ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
        · rw [star_star]
          exact h1
        · rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd, star_one]
      refine ⟨fun b _ => ?_, fun b _ => ?_⟩
      · rcases hX b with ⟨hp, hn'⟩ | ⟨hp, hn'⟩
        · exact hval b hp
        · rw [meanIterate_succ_of_negative U hlt b hn' hp]
          exact hinvmem (hreal _ hp).2.2
      · rcases hX b with ⟨hp, hn'⟩ | ⟨hp, hn'⟩
        · rw [meanIterate_succ_of_negative U hlt b.opposite hn'
              (show b.opposite.opposite.IsPositivelyOriented from hp),
            meanIterate_succ_of_positive U hlt b hp]
          rfl
        · rw [meanIterate_succ_of_positive U hlt b.opposite hp,
            meanIterate_succ_of_negative U hlt b hn' hp]
          have hdet : Matrix.det (normalizedMean (meanIterate U j) b.opposite) = 1 :=
            (Matrix.mem_specialUnitaryGroup_iff.1 (hreal _ hp).2.2).2
          exact (Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)).symm
end YangMills.Construction.RunningCouplingSlope
end
