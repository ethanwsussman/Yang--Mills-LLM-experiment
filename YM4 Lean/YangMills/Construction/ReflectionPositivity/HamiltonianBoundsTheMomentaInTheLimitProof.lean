import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBounded
import YangMills.Construction.ReflectionPositivity.FivePointInequalityPassesToTheLimit
import YangMills.Construction.ReflectionPositivity.HamiltonianBoundsTheMomentaInTheLimit
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitMomentumBound
theorem inv_pow_mem_posAdicGridPoints {L : ℕ} (hL : 1 < L) (k : ℕ) :
    ((((L : ℝ≥0)⁻¹ ^ k : ℝ≥0)) : ℝ) ∈ SeparatedTuples.posAdicGridPoints L := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  refine ⟨(PeriodicLattice.mem_adicGridPoints_iff L _).2 ⟨k, 1, ?_⟩, ?_⟩
  · simp [PeriodicLattice.meshSize, zpow_neg, inv_pow]
  · have : (0 : ℝ) < ((L : ℝ))⁻¹ ^ k := pow_pos (inv_pos.2 hLpos) k
    simpa using this
theorem momentumBoundAssertions_of_bounded
    (hlim : FivePointLimit.FivePointInequalityInLimit)
    (hrec : LimitReconstruction.LimitReconstructionTheorem)
    (hcn : SmallTimeCone.SmallTimeConeTheorem)
    (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L)
    (σ : SeparatedTuples.TupleFunctional)
    (hbd : ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T)
    (hrp : LimitConventions.ApproxTriple.IsReflPos T)
    (hconv : LimitConventions.ApproxTriple.ConvergesTo T σ) : MomentumBoundAssertions D.L σ := by
  obtain ⟨hH, hC, h, hV, hS, hT, hM⟩ := hrec D T σ hbd hrp hconv
  obtain ⟨h', hcone⟩ := hcn σ hH
  refine ⟨hH, hC, h', hV, hS, hT, hM, fun i => ?_⟩
  obtain ⟨hseq, hone⟩ := hcone i
  have hL : 1 < D.L := by
    have h2 := D.isAdmissible.2
    omega
  have hinv : ((D.L : ℝ≥0))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hL)
  have hpos : (0 : ℝ≥0) < (D.L : ℝ≥0) := by exact_mod_cast (by omega : 0 < D.L)
  have hfive : ∀ k : ℕ, SmallTimeCone.FivePointNonnegAt σ i (((D.L : ℝ≥0))⁻¹ ^ k) := fun k =>
    hlim D T σ hbd hrp hconv i _ (inv_pow_mem_posAdicGridPoints hL k)
  obtain ⟨-, hB, hD, hFo, hK⟩ := hseq (fun k => ((D.L : ℝ≥0))⁻¹ ^ k)
    (fun k => pow_pos (inv_pos.2 hpos) k)
    (antitone_nat_of_succ_le fun k => by
      rw [pow_succ]
      exact mul_le_of_le_one_right zero_le hinv.le)
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hinv) hfive
  refine ⟨fun t ht => hone t ?_ (hlim D T σ hbd hrp hconv i t ht), hB, hD, hFo, hK⟩
  exact_mod_cast ht.2
theorem momentumBoundTheorem_holds
    (hbdd : ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hlim : FivePointLimit.FivePointInequalityInLimit)
    (hrec : LimitReconstruction.LimitReconstructionTheorem)
    (hcn : SmallTimeCone.SmallTimeConeTheorem) : MomentumBoundTheorem := by
  refine ⟨fun D T σ hbd hrp hconv => momentumBoundAssertions_of_bounded hlim hrec hcn D T σ hbd hrp hconv,
    fun D T σ hrp hconv => ?_⟩
  exact momentumBoundAssertions_of_bounded hlim hrec hcn D T σ
    (hbdd.1 D T fun X => ⟨σ X, hconv X⟩).2 hrp hconv
end YangMills.Construction.ReflectionPositivity.LimitMomentumBound
