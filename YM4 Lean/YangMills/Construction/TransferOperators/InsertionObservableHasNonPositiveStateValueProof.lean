import YangMills.Construction.TransferOperators.ConfigurationsOfACubicTorusByLayersProof
import YangMills.Construction.TransferOperators.InsertionObservableHasNonPositiveStateValue
import YangMills.Construction.TransferOperators.InsertionObservableIsRealLocalAndGaugeInvariant
import YangMills.Construction.TransferOperators.IntegralOfAnInsertionIsAtMostTheNormaliser
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice SpinHarmonics
namespace TransferOperators.LogKernelRatio
theorem level_add (ρ : Fin 4) (x y : LatticePoint 1) :
    level ρ (x + y) = level ρ x + level ρ y := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.level_add <;> assumption
def coordHom (ρ : Fin 4) : LatticePoint 1 →+ ℤ :=
  AddMonoidHom.mk' (level ρ) (level_add ρ)
theorem eq_zero_of_coordHom (x : LatticePoint 1) (h : ∀ ρ, coordHom ρ x = 0) : x = 0 := by
  refine Subtype.ext (funext fun ρ => ?_)
  have h₁ : ((level ρ x : ℤ) : ℝ) = (x : AmbientSpace) ρ := level_cast ρ x
  have h₂ : level ρ x = 0 := h ρ
  rw [h₂] at h₁
  simpa using h₁.symm
def coordMod (n : ℕ) : LatticePoint 1 →+ (Fin 4 → ZMod n) :=
  AddMonoidHom.mk' (fun x ρ => ((coordHom ρ x : ℤ) : ZMod n)) fun x y => by
    funext ρ
    simp
theorem exists_finiteIndex_le_pairwiseDisjointShifts {μ : Fin 4} (B : Block μ) (i : ℤ)
    (Q : AddSubgroup (LatticePoint 1)) (hQ : Q.FiniteIndex) :
    ∃ Q' : AddSubgroup (LatticePoint 1), Q' ≤ Q ∧ Q'.FiniteIndex ∧ B.PairwiseDisjointShifts i Q' := by
  classical
  let M : ℕ := ∑ b ∈ B.links, ∑ ρ, (coordHom ρ (b.source : LatticePoint 1)).natAbs
  have hM : ∀ b ∈ B.links, ∀ ρ, (coordHom ρ (b.source : LatticePoint 1)).natAbs ≤ M := fun b hb ρ =>
    (Finset.single_le_sum (f := fun ρ => (coordHom ρ (b.source : LatticePoint 1)).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)).trans
      (Finset.single_le_sum
        (f := fun b : SliceLink μ => ∑ ρ, (coordHom ρ (b.source : LatticePoint 1)).natAbs)
        (fun _ _ => Nat.zero_le _) hb)
  have : NeZero (2 * M + 1) := ⟨by omega⟩
  refine ⟨Q ⊓ (coordMod (2 * M + 1)).ker, inf_le_left, inferInstance, ?_⟩
  intro v v' hne
  refine Set.disjoint_left.mpr ?_
  rintro c ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩ ⟨_, ⟨_, ⟨b', hb', rfl⟩, rfl⟩, h⟩
  have ht : pointAtLevel μ i b'.source + (v' : LatticePoint 1) =
      pointAtLevel μ i b.source + (v : LatticePoint 1) :=
    congrArg InfiniteLattice.Link.initial h
  have hd : (v : LatticePoint 1) - v' = (b'.source : LatticePoint 1) - b.source := by
    rw [← pointAtLevel_sub_pointAtLevel μ i b.source b'.source]
    refine sub_eq_sub_iff_add_eq_add.mpr ?_
    rw [add_comm (v : LatticePoint 1)]
    exact ht.symm
  have hker : (v : LatticePoint 1) - v' ∈ (coordMod (2 * M + 1)).ker :=
    sub_mem v.2.2 v'.2.2
  apply hne
  refine Subtype.ext (sub_eq_zero.mp (eq_zero_of_coordHom _ fun ρ => ?_))
  have h₀ : (((coordHom ρ ((v : LatticePoint 1) - v') : ℤ)) : ZMod (2 * M + 1)) = 0 :=
    congrFun (AddMonoidHom.mem_ker.mp hker) ρ
  have hdvd : ((2 * M + 1 : ℕ) : ℤ) ∣ coordHom ρ ((v : LatticePoint 1) - v') :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₀
  have h₁ := hM b hb ρ
  have h₂ := hM b' hb' ρ
  refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
  rw [hd, map_sub, abs_lt]
  push_cast
  omega
theorem nonposStateStatement_holds (hReal : RealLocalInvariantStatement)
    (hInt : ExpShiftIntegral.BoundStatement)
    (hPass : PeriodicBoundsPassToInvariantGibbs)
    (hStates : GibbsHaarKernels.Statement) :
    NonposStateStatement := by
  intro β hβ μ B Ξ hn hr hg hk i ν hν
  have hprob : IsProbabilityMeasure ν := hν.1.1
  have hcl := hStates.1 β hβ ν hprob
  obtain ⟨Q, hQ, hνQ⟩ := hcl.2.2.mp (hcl.2.1.mp hν)
  obtain ⟨Q', hle, hfin, hdis⟩ := exists_finiteIndex_le_pairwiseDisjointShifts B i Q hQ
  have hφ := hReal β hβ μ B Ξ hn hr hg hk i
  have hνQ' : ν ∈ subgroupInvariantGibbsClass one_pos β Q' :=
    ⟨hνQ.1, fun v hv => hνQ.2 v (hle hv)⟩
  exact hPass β hβ _ hφ.1 hφ.2.1 Q' hfin
    ⟨3, le_rfl, fun s hs hsQ Γ hΓ =>
      (hInt β hβ μ B Ξ hn hr hg hk i Q' hfin hdis ⟨s, by omega, Γ, hΓ⟩ (hΓ.le.trans hsQ)).1⟩
    ν hνQ'
end TransferOperators.LogKernelRatio
end YangMills.Construction
end
