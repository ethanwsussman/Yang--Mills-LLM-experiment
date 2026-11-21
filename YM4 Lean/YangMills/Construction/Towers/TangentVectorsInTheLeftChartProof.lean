import YangMills.Construction.Lattice.CombSchemeGaugeLawAndConjugationProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.TangentVectorsInTheLeftChart
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartTangentProof
open YangMills.Construction YangMills.Construction.Matrices YangMills.Construction.Tower
open YangMills.Construction.Tower.LeftChartFacts YangMills.Construction.Tower.LeftChartFields
theorem mul_inv_eq_one_of_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g * g⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem inv_mul_eq_one_of_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem biInvariantMetric_def (g v w : ComplexMatrix2) :
    biInvariantMetric g v w = ComplexMatrix2.halfTrace ((Complex.I⁻¹ • (v * g⁻¹)) * (Complex.I⁻¹ • (w * g⁻¹))) :=
  rfl
theorem biInvariantMetric_one {X Y : ComplexMatrix2} :
    biInvariantMetric 1 (Complex.I • X) (Complex.I • Y) = ComplexMatrix2.halfTrace (X * Y) := by
  rw [biInvariantMetric_def, inv_one, mul_one, mul_one, smul_smul, smul_smul,
    inv_mul_cancel₀ Complex.I_ne_zero, one_smul, one_smul]
theorem biInvariantMetric_mul_left {g h : ComplexMatrix2} (hh : h ∈ PeriodicLattice.compactGaugeGroup)
    (v w : ComplexMatrix2) :
    biInvariantMetric (h * g) (h * v) (h * w) = biInvariantMetric g v w := by
  have key : ∀ x : ComplexMatrix2, h * x * (h * g)⁻¹ = h * (x * g⁻¹) * h⁻¹ := fun x => by
    rw [Matrix.mul_inv_rev]
    simp only [mul_assoc]
  rw [biInvariantMetric_def, biInvariantMetric_def, key, key]
  have conj : (Complex.I⁻¹ • (h * (v * g⁻¹) * h⁻¹)) * (Complex.I⁻¹ • (h * (w * g⁻¹) * h⁻¹)) =
      h * ((Complex.I⁻¹ • (v * g⁻¹)) * (Complex.I⁻¹ • (w * g⁻¹))) * h⁻¹ := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
    rw [← mul_assoc h⁻¹ h, inv_mul_eq_one_of_mem hh, one_mul]
  rw [conj]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, inv_mul_eq_one_of_mem hh, one_mul]
theorem biInvariantMetric_mul_right {g h : ComplexMatrix2} (hh : h ∈ PeriodicLattice.compactGaugeGroup)
    (v w : ComplexMatrix2) :
    biInvariantMetric (g * h) (v * h) (w * h) = biInvariantMetric g v w := by
  have key : ∀ x : ComplexMatrix2, x * h * (g * h)⁻¹ = x * g⁻¹ := fun x => by
    rw [Matrix.mul_inv_rev, mul_assoc, ← mul_assoc h, mul_inv_eq_one_of_mem hh, one_mul]
  rw [biInvariantMetric_def, biInvariantMetric_def, key, key]
theorem isBiInvariantMetric : IsBiInvariantMetric :=
  ⟨fun _ _ _ _ => biInvariantMetric_one, fun _ _ _ hh v w =>
    ⟨biInvariantMetric_mul_left hh v w, biInvariantMetric_mul_right hh v w⟩⟩
variable {L n k j : ℕ}
theorem leftChartTangent_apply (h : (finiteData L n k j).LeftExpMulMemGroup)
    {U B : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j) (hB : B ∈ edgeFormSpace L n k j)
    (b : PositiveEdge L n k j) : leftChartTangent U B b = Complex.I • B b * U b := by
  have hfun : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U b) =
      fun t : ℝ => leftExpMul ((t : ℂ) • B b) (U b) := by
    funext t
    simp only [PeriodicLattice.expTwist, if_pos b.2]
    rfl
  change deriv (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U b) 0 = _
  rw [hfun]
  exact (h.1 U hU B hB b).2.deriv
theorem biInvariantMetric_smul_mul {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (X Y : ComplexMatrix2) :
    biInvariantMetric g (Complex.I • X * g) (Complex.I • Y * g) = ComplexMatrix2.halfTrace (X * Y) := by
  rw [biInvariantMetric_def, mul_assoc, mul_assoc, mul_inv_eq_one_of_mem hg, mul_one, mul_one, smul_smul,
    smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul, one_smul]
theorem tangentSpaceIsoForms (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) (hn : 0 < n) :
    TangentSpaceIsoForms L n k j := by
  intro inst U hU
  have h := (hA.2.2 L k j hL hj).1 n hn
  have hleft : (finiteData L n k j).LeftExpMulMemGroup := h.1.1
  obtain ⟨T, hT, hTB⟩ := (h.2.1.2.2 inst U hU).2
  refine ⟨⟨LinearEquiv.ofBijective T hT, fun B => hTB B⟩, fun B hB B' hB' => ?_⟩
  have hterm : ∀ b : PositiveEdge L n k j,
      biInvariantMetric (U b) (leftChartTangent U B b) (leftChartTangent U B' b) =
        ComplexMatrix2.halfTrace (B b * B' b) := fun b => by
    rw [leftChartTangent_apply hleft hU hB, leftChartTangent_apply hleft hU hB']
    exact biInvariantMetric_smul_mul (hU.1 b.1 (Set.mem_univ _)) _ _
  rw [Finset.sum_congr rfl fun b _ => hterm b]
  simp only [edgeFormPairing, traceFinsumPairing, finsum_eq_sum_of_fintype]
  rfl
theorem leftChartTangentSpaces (hA : LeftChartFields.Claim) :
    LeftChartTangentSpaces :=
  ⟨isBiInvariantMetric, fun _ _ _ hL hj _ hn => tangentSpaceIsoForms hA hL hj hn⟩
end YangMills.Construction.Tower.LeftChartTangentProof
end
