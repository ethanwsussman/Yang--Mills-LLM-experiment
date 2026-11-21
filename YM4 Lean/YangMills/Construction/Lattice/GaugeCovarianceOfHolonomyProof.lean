import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import Mathlib
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
private theorem mul_inv_of_mem_complexGaugeGroup {M : ComplexMatrix2} (hM : M ∈ complexGaugeGroup) :
    M * M⁻¹ = 1 := by
  have h : M.det = 1 := hM
  exact Matrix.mul_nonsing_inv M (by rw [h]; exact isUnit_one)
abbrev _root_.YangMills.DeltaSharedProofs.p2618 := @mul_inv_of_mem_complexGaugeGroup
abbrev _root_.YangMills.SharedProofs.p13806 := @mul_inv_of_mem_complexGaugeGroup
private theorem inv_mul_of_mem_complexGaugeGroup {M : ComplexMatrix2} (hM : M ∈ complexGaugeGroup) :
    M⁻¹ * M = 1 := by
  have h : M.det = 1 := hM
  exact Matrix.nonsing_inv_mul M (by rw [h]; exact isUnit_one)
abbrev _root_.YangMills.DeltaSharedProofs.p40097 := @inv_mul_of_mem_complexGaugeGroup
private theorem inv_mem_complexGaugeGroup {M : ComplexMatrix2} (hM : M ∈ complexGaugeGroup) :
    M⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
private theorem mul_mem_complexGaugeGroup {M N : ComplexMatrix2} (hM : M ∈ complexGaugeGroup)
    (hN : N ∈ complexGaugeGroup) : M * N ∈ complexGaugeGroup := by apply _root_.YangMills.DeltaSharedProofs.p585 <;> assumption
abbrev _root_.YangMills.SharedProofs.p592 := @mul_mem_complexGaugeGroup
private theorem inv_mem_compactGaugeGroup {M : ComplexMatrix2} (hM : M ∈ compactGaugeGroup) :
    M⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem isBondPathFromTo_of_cons {b : Bond L m j} {Γ : List (Bond L m j)}
    {x x' : Site L m j} (h : IsBondPathFromTo (b :: Γ) x x') :
    b.source = x ∧ IsBondPathFromTo Γ b.target x' := by
  obtain ⟨hp, -, ht, hh⟩ := h
  refine ⟨ht b (by simp), ?_⟩
  cases Γ with
  | nil => exact ⟨List.isChain_nil, fun _ => hh b (by simp), by simp, by simp⟩
  | cons c Γ' =>
    have hp' := List.isChain_cons_cons.1 hp
    refine ⟨hp'.2, by simp, ?_, ?_⟩
    · intro c' hc
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
      subst hc
      exact hp'.1.symm
    · intro d hd
      exact hh d (by simpa [List.getLast?_cons_cons] using hd)
abbrev _root_.YangMills.SharedProofs.p46261 := @isBondPathFromTo_of_cons
private theorem pathHolonomy_gaugeTransform (U : Bond L m j → ComplexMatrix2)
    (u : Site L m j → ComplexMatrix2) (hu : IsGaugeMap complexGaugeGroup u)
    (Γ : List (Bond L m j)) :
    ∀ x x' : Site L m j, IsBondPathFromTo Γ x x' →
      pathHolonomy (gaugeTransform u U) Γ = u x * pathHolonomy U Γ * (u x')⁻¹ := by
  induction Γ with
  | nil =>
    intro x x' h
    rw [← h.2.1 rfl]
    simp [pathHolonomy, mul_inv_of_mem_complexGaugeGroup (hu x)]
  | cons b Γ ih =>
    intro x x' h
    obtain ⟨rfl, hΓ⟩ := isBondPathFromTo_of_cons h
    have hs : pathHolonomy (gaugeTransform u U) (b :: Γ) =
        gaugeTransform u U b * pathHolonomy (gaugeTransform u U) Γ := by simp [pathHolonomy]
    have hs' : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by simp [pathHolonomy]
    rw [hs, ih _ _ hΓ, hs']
    simp only [gaugeTransform, mul_assoc]
    rw [← mul_assoc (u b.target)⁻¹ (u b.target), inv_mul_of_mem_complexGaugeGroup (hu b.target),
      one_mul]
private theorem boundaryBonds_isBondPathFromTo (p : Plaquette L m j) :
    IsBondPathFromTo p.boundaryBonds p.origin p.origin := by
  refine ⟨?_, by simp [Plaquette.boundaryBonds], ?_, ?_⟩
  · simp [IsBondPath, Plaquette.boundaryBonds, Bond.forwardFrom, Bond.opposite, add_right_comm]
  · simp [Plaquette.boundaryBonds, Bond.forwardFrom]
  · simp [Plaquette.boundaryBonds, Bond.forwardFrom, Bond.opposite]
abbrev _root_.YangMills.SharedProofs.p81322 := @boundaryBonds_isBondPathFromTo
theorem gaugeCovarianceOfHolonomy_holds : GaugeCovarianceOfHolonomy := by
  intro L m _ _ _ j _ ℬ U u u' _ hU hu hu'
  have hconf : IsGaugeField complexGaugeGroup ℬ (gaugeTransform u U) := by
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · exact mul_mem_complexGaugeGroup (mul_mem_complexGaugeGroup (hu _) (hU.1 b hb))
        (inv_mem_complexGaugeGroup (hu _))
    · have hopp : gaugeTransform u U b.opposite = u b.target * U b.opposite * (u b.source)⁻¹ := rfl
      have hdet : (u b.target).det = 1 := hu _
      rw [hopp, hU.2 b hb]
      simp only [gaugeTransform, Matrix.mul_inv_rev]
      rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)]
      simp only [mul_assoc]
  refine ⟨⟨hconf, fun hUr hur => ⟨fun b hb => ?_, hconf.2⟩, fun b _ => ?_⟩, ?_, ?_⟩
  · exact ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (hur _) (hUr.1 b hb)) (inv_mem_compactGaugeGroup (hur _))
  · simp only [gaugeTransform, Matrix.mul_inv_rev, mul_assoc]
  · intro Γ x x' hΓ _
    exact pathHolonomy_gaugeTransform U u hu Γ x x' hΓ
  · intro p _
    exact pathHolonomy_gaugeTransform U u hu p.boundaryBonds p.origin p.origin
      (boundaryBonds_isBondPathFromTo p)
end YangMills.Construction.PeriodicLattice
