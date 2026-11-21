import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevelProof
import YangMills.Construction.Towers.DifferentialsOfTheIteratesUnderTheDilation
import YangMills.Construction.Towers.DifferentialsUnderTheDilation
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfiguration
import YangMills.Construction.Towers.IteratesOfTheAveragesUnderTheDilation
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ScaledIterateDerivs
variable {L n k : ℕ}
theorem leftDifferential_smoothingIter_zero (hExp : Matrices.ComplexMatrix2.ExpLogEstimates)
    {W B : Edge L n k 0 → Matrices.ComplexMatrix2} (hW : W ∈ fieldSpace L n k 0)
    (hB : B ∈ edgeFormSpace L n k 0) :
    leftDifferential (smoothingIter L n k 0) W B = B := by apply _root_.YangMills.Construction.Tower.BottomLevel.leftDifferential_smoothingIter_zero <;> assumption
theorem leftDifferentialLinear_smoothingIter_zero (hExp : Matrices.ComplexMatrix2.ExpLogEstimates)
    {W : Edge L n k 0 → Matrices.ComplexMatrix2} (hW : W ∈ fieldSpace L n k 0)
    (B : edgeFormSpace L n k 0) :
    (leftDifferentialLinear (smoothingIter L n k 0) W B : Edge L n k 0 → Matrices.ComplexMatrix2) =
      B := by
  have h : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0, ∀ B : edgeFormSpace L n k 0,
      (T B : Edge L n k 0 → Matrices.ComplexMatrix2) = leftDifferential (smoothingIter L n k 0) W B :=
    ⟨LinearMap.id, fun B => (leftDifferential_smoothingIter_zero hExp hW B.2).symm⟩
  have hs : ∀ B : edgeFormSpace L n k 0,
      (leftDifferentialLinear (smoothingIter L n k 0) W B : Edge L n k 0 → Matrices.ComplexMatrix2) =
        leftDifferential (smoothingIter L n k 0) W B :=
    Classical.epsilon_spec (p := fun T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 =>
      ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k 0 → Matrices.ComplexMatrix2) =
          leftDifferential (smoothingIter L n k 0) W B) h
  exact (hs B).trans (leftDifferential_smoothingIter_zero hExp hW B.2)
theorem isOpenFieldSet_inter_level_zero (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {𝒰₁ 𝒰₂ : Set (Edge L n k 0 → Matrices.ComplexMatrix2)}
    (h₁ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₁)
    (h₂ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₂) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰₁ ∩ 𝒰₂) := by
  have A := ((hE L hL k 0 (Nat.zero_le k)).1 n hn).2.2.2.2.2.2.2.2.1
  obtain ⟨O₁, hO₁, e₁⟩ := (A 𝒰₁ h₁.1).2 h₁.2
  obtain ⟨O₂, hO₂, e₂⟩ := (A 𝒰₂ h₂.1).2 h₂.2
  have hsub : 𝒰₁ ∩ 𝒰₂ ⊆ fieldSpace L n k 0 := fun V hV => h₁.1 hV.1
  refine ⟨hsub, (A _ hsub).1 ⟨O₁ ∩ O₂, hO₁.inter hO₂, ?_⟩⟩
  rw [e₁, e₂]
  ext V
  simp only [mem_inter_iff]
  tauto
end YangMills.Construction.Tower.ScaledIterateDerivs
namespace YangMills.Construction.Tower
open ScaledIterateDerivs in
theorem scaledIterateDifferentials_holds
    (hExp : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hE : BondSetFields.ProductStructureHolds)
    (hNear : ScalingNearTrivialField)
    (hDiff : ScalingTransportsDerivatives)
    (hIter : ScalingCommutesWithSmoothingIter)
    (hAn : SmoothingIterAnalyticNearOne)
    (hPaths : AnalyticMapsAlongCurves) :
    ScaledIterateDifferentials := by
  intro L n k j hL hj hs hn hj1 l hl
  have hn' : 0 < scaledExponent n k j := Nat.add_pos_left hn _
  have hN := hNear L n k j 0 0 hL hj hs hn (Nat.zero_le j) (Nat.zero_le j)
  have hd := hN.1
  have ho := hN.2.1
  rcases l with _ | i
  · obtain ⟨𝒰, h𝒰, -, -⟩ := hAn L n k 0 hs hn (by omega)
    refine ⟨𝒰, h𝒰, fun U hU B B' hB => ?_⟩
    have hUc : U ∈ fieldSpace L n k 0 := h𝒰.1.1 hU
    have hCU := hd.1.mapsTo hUc
    rw [leftDifferentialLinear_smoothingIter_zero hExp hCU,
      leftDifferentialLinear_smoothingIter_zero hExp hUc]
    exact hB
  · obtain ⟨𝒰₁, h₁, a₁, -⟩ := hAn L n k i hs hn (by omega)
    obtain ⟨𝒰₂, h₂, a₂, -⟩ := hAn L (scaledExponent n k j) j i hs hn' (by omega)
    have himage : transportTotal (scaleEdge (n := n) hL hj 0) ''
        {V | V ∈ fieldSpace L n k 0 ∧ transportTotal (scaleEdge hL hj 0) V ∈ 𝒰₂} = 𝒰₂ := by
      ext W
      constructor
      · rintro ⟨V, hV, rfl⟩
        exact hV.2
      · intro hW
        obtain ⟨V, hV, rfl⟩ := hd.1.surjOn (h₂.1.1 hW)
        exact ⟨V, ⟨hV, hW⟩, rfl⟩
    have hpre : IsOpenFieldSet PeriodicLattice.compactGaugeGroup
        {V | V ∈ fieldSpace L n k 0 ∧ transportTotal (scaleEdge hL hj 0) V ∈ 𝒰₂} := by
      refine (ho.2.1 _ fun V hV => hV.1).2 ?_
      rw [himage]
      exact h₂.1
    refine ⟨_, ⟨isOpenFieldSet_inter_level_zero hE hs hn h₁.1 hpre, h₁.2, h₁.1.1 h₁.2, ?_⟩, ?_⟩
    · show transportTotal (scaleEdge hL hj 0) (trivialField L n k 0) ∈ 𝒰₂
      rw [hd.2.1]
      exact h₂.2
    · rintro U ⟨hU₁, hUc, hU₂⟩ B B' hB
      have p₁ := (((hPaths L n k 0 (i + 1) hs hn (Nat.zero_le k) (by omega)).1 𝒰₁ _ a₁).2 U hU₁).1 B
      have p₂ := (((hPaths L (scaledExponent n k j) j 0 (i + 1) hs hn' (Nat.zero_le j)
        (by omega)).1 𝒰₂ _ a₂).2 _ hU₂).1 B'
      have hrel := (hDiff L n k j hL hj hs hn 0 (Nat.zero_le j) (i + 1) (by omega)).1
        (smoothingIter L n k (i + 1)) (smoothingIter L (scaledExponent n k j) j (i + 1))
        (fun V hV => (hIter L n k j hL hj hs hn hj1 (i + 1) hl V hV).symm) U hUc B B.2
      rw [p₁, p₂, hB]
      exact hrel
end YangMills.Construction.Tower
end
