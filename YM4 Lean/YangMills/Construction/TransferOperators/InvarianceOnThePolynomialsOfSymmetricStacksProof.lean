import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOneProof
import YangMills.Construction.TransferOperators.ClassesOfSymmetricStacksAreGaugeInvariantPolynomials
import YangMills.Construction.TransferOperators.InvarianceOnThePolynomialsOfSymmetricStacks
import YangMills.Construction.TransferOperators.ReflectionInTransportedVariables
import YangMills.Construction.TransferOperators.ReversalInvarianceOnTheSymmetricStackOfTwoLayers
import YangMills.Construction.TransferOperators.ReversalInvariancePassesToTheNextSymmetricStack
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators.CenteredStackInvariance
theorem latticeSymmetry_ext_toFun {s t : LatticeSymmetry 1} (h : s.toFun = t.toFun) : s = t := by apply _root_.YangMills.Construction.InfiniteLattice.UnitMeshReflectionPositivity.latticeSymmetry_ext_toFun <;> assumption
theorem reversalInvariant_centeredStack
    (hTwo : ReversalInvariantTwoLevelStatement)
    (hSucc : ReversalInvariantSuccStatement)
    {μ : Fin 4} {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField 1)}
    (hν : IsPeriodicGibbs β ν) (i k : ℤ) (hk : 1 ≤ k) :
    IsReversalInvariantOnCenteredStack μ ν i k hk := by
  induction k, hk using Int.le_induction with
  | base => exact hTwo μ β hβ ν hν i
  | succ k hk ih => exact hSucc μ β hβ ν hν i k hk ih
theorem centeredStackReflectionInvariance_holds (hClasses : CenteredStackClassStatement)
    (hRefl : ReflectionOnTransportedVariables)
    (hTwo : ReversalInvariantTwoLevelStatement)
    (hSucc : ReversalInvariantSuccStatement) : CenteredStackReflectionInvarianceStatement := by
  intro μ β hβ ν hν i
  refine ⟨fun k hk => Set.ext fun F => hClasses μ i k hk F, fun P hv hp k hk X hX => ?_⟩
  obtain ⟨θ, hθ, -, hex⟩ := hRefl μ i k hk
  have hθP : θ = P.reflectSymmetry := by
    apply latticeSymmetry_ext_toFun
    rw [hθ]
    change NormalFamilies.reflectAcross _ _ = NormalFamilies.reflectAcross P.normal P.level
    rw [hv, hp]
  obtain ⟨v, hfin, Ψ, hne, hΨ, hinv, hXΨ⟩ := hX
  have hc : Continuous Ψ := hΨ.1.continuous
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hexv := hex v Ψ X hne hc.measurable ⟨C, fun u => hC u (Set.mem_univ u)⟩ hinv hXΨ
  have h₁ : X = fun U => Ψ fun p =>
      (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2 := funext hXΨ
  have h₂ : P.reflectObservable X = fun U => levelReversal i k v Ψ fun p =>
      (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2 := by
    funext U
    change P.reflectSymmetry.actOn X U = _
    rw [← hθP, (hexv U).1, (hexv U).2]
  rw [h₂, stateEval, stateEval]
  rw [h₁]
  exact reversalInvariant_centeredStack hTwo hSucc hβ hν i k hk v Ψ hne hΨ hinv
end YangMills.Construction.TransferOperators.CenteredStackInvariance
end
