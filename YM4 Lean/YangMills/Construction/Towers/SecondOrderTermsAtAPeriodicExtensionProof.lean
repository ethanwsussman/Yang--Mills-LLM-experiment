import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.SecondOrderTermAtTheSideInfinityIsLocalProof
import YangMills.Construction.Towers.SecondOrderTermsAtAPeriodicExtension
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.QuadraticTermsAtLift
section Support
open YangMills.Construction.Tower (HasFiniteSupp meshAt mixedDirectionalDeriv)
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule quadraticTermAt
  HasUniqueQuadraticTerm)
open YangMills.Construction.Tower.SupportOfMeans (DefinedAlike DependsOnlyOn)
open YangMills.Construction.Tower.SupportOfMeans.Unbounded (baseFields supportEdges
  HasEndpointsIn SideRequirements meanAt)
open YangMills.Construction.Tower.FullSpace (Edge complexEdgeForms expTwist restrictToPositiveEdges)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm iterRatio
  iterLogRatio iterMean topDeriv topLogRatio)
variable {L k : ℕ}
theorem getD_eq_of_definedAlike {p q : Option Matrices.ComplexMatrix2} (h : DefinedAlike p q) :
    p.getD 1 = q.getD 1 := by apply _root_.YangMills.Construction.LocalKernels.QuadraticLocality.getD_eq_of_definedAlike <;> assumption
theorem iterLogRatio_congr {F : Finset (Edge L k 0)} {c : Edge L k k}
    (hR : DependsOnlyOn (baseFields L k) F (fun e => e.IsPositivelyOriented) expTwist
      (meanAt c))
    {W : Edge L k 0 → Matrices.ComplexMatrix2} (hW : W ∈ baseFields L k)
    {C C' : Edge L k 0 → Matrices.ComplexMatrix2} (hC : C ∈ complexEdgeForms (meshAt L k 0))
    (hC' : C' ∈ complexEdgeForms (meshAt L k 0)) (h : ∀ e ∈ F, C e = C' e) :
    iterLogRatio W k c C = iterLogRatio W k c C' := by
  have hC₁ : Tower.FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra C := hC
  have hC₂ : Tower.FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra C' := hC'
  have hval := getD_eq_of_definedAlike
    (hR.definedAlike_twist W hW W hW C C' hC₁.1 hC₂.1 fun e he => ⟨rfl, h e he⟩)
  have hval' : iterMean (expTwist C W) k c = iterMean (expTwist C' W) k c := hval
  simp only [iterLogRatio, iterRatio, hval']
theorem complexQuadraticTerm_hasFiniteSupp (hR : SideRequirements L k)
    (hE : ∀ e : Edge L k 0,
      {c : Edge L k k | c.IsPositivelyOriented ∧ HasEndpointsIn c e}.Finite)
    {W : Edge L k 0 → Matrices.ComplexMatrix2} (hW : W ∈ baseFields L k)
    (hq : HasUniqueQuadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k W)
      (topDeriv L k W))
    {A A' : Edge L k 0 → Matrices.ComplexMatrix2} (hA : A ∈ complexEdgeForms (meshAt L k 0))
    (hAf : HasFiniteSupp (restrictToPositiveEdges A))
    (hA' : A' ∈ complexEdgeForms (meshAt L k 0)) :
    HasFiniteSupp (complexQuadraticTerm L k W A A') := by
  classical
  by_cases hbd : A ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) ∧
      A' ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0))
  swap
  · have hzero' : complexQuadraticTerm L k W A A' = 0 := by
      simp only [complexQuadraticTerm, quadraticTermAt, dif_neg hbd]
    rw [hzero']
    simp [HasFiniteSupp]
  have hfin : (⋃ e ∈ Function.support (restrictToPositiveEdges A),
      {c : Tower.FullSpace.PositiveEdge (meshAt L k k) |
        HasEndpointsIn c.1 (e : Edge L k 0)}).Finite := by
    refine Set.Finite.biUnion hAf fun e _ => ?_
    refine ((hE e.1).preimage Subtype.val_injective.injOn).subset fun c hc => ?_
    exact ⟨c.2, hc⟩
  refine hfin.subset fun c hc => ?_
  by_contra hnot
  apply hc
  have hzero : ∀ e ∈ supportEdges c.1, A e = 0 := by
    intro e he
    by_contra hne
    exact hnot (mem_iUnion₂.2 ⟨⟨e, he.1⟩, hne, he.2⟩)
  obtain ⟨hfinS, -⟩ := hR.finite_nonempty k le_rfl c.1
  have hDep := hR.dependsOnlyOn k le_rfl c.1 hfinS.toFinset (by simp)
  have hmixed := (hq.2.2 ⟨A, hbd.1⟩ ⟨A', hbd.2⟩ c).1
  have hconst : (fun s : ℂ => deriv (fun t : ℂ => topLogRatio L k W c
        (algebraMap ℂ ℂ s • A + algebraMap ℂ ℂ t • A')) 0) =
      fun _ => deriv (fun t : ℂ => topLogRatio L k W c (algebraMap ℂ ℂ t • A')) 0 := by
    funext s
    have hfun : (fun t : ℂ => topLogRatio L k W c
          (algebraMap ℂ ℂ s • A + algebraMap ℂ ℂ t • A')) =
        fun t : ℂ => topLogRatio L k W c (algebraMap ℂ ℂ t • A') := by
      funext t
      refine iterLogRatio_congr hDep hW ?_ ?_ fun e he => ?_
      · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hA) (Submodule.smul_mem _ _ hA')
      · exact Submodule.smul_mem _ _ hA'
      · have hAe := hzero e (hfinS.mem_toFinset.1 he)
        simp [hAe]
    rw [hfun]
  simp only [complexQuadraticTerm, quadraticTermAt, dif_pos hbd]
  rw [← hmixed]
  simp only [mixedDirectionalDeriv]
  rw [hconst]
  simp
end Support
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Tower
theorem quadraticTermsFormedAtLift_holds (h₁ : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (h₂ : LocalKernels.IterMeansOfLift.Claim)
    (h₃ : Tower.SupportOfMeans.SupportOfMeansHolds)
    (h₄ : Tower.BlockPathContourPivotStatement) :
    LocalKernels.QuadraticTermsFormedAtLift := by
  intro L hL k m hm hk U hU hS
  have hD := h₁ L hL k hk
  have hW : LocalKernels.liftGaugeField L m k 0 U ∈ Tower.FullSpace.smallIterateFields L k :=
    (h₂ L hL k m hm hk U hU).1.1 hS
  have hq := (hD.1 m hm).2.1 U hS
  have hq' := hD.2.2 _ hW
  have hE : ∀ e : Tower.FullSpace.Edge L k 0, {c : Tower.FullSpace.Edge L k k |
      c.IsPositivelyOriented ∧ Tower.SupportOfMeans.Unbounded.HasEndpointsIn c e}.Finite := by
    have H := (h₄ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1.encard_le_eight
    rw [Nat.sub_self] at H
    intro e
    have h₈ : {c : Tower.FullSpace.Edge L k k | c.IsPositivelyOriented ∧
        Tower.SupportOfMeans.Unbounded.HasEndpointsIn c e}.encard ≤ 8 := H e
    exact Set.finite_of_encard_le_coe (k := 8) (by simpa using h₈)
  refine ⟨fun A hA A' hA' c => ?_, fun A hA A' hA' c => ?_, fun A hA hAf A' hA' _ => ?_⟩
  · simp only [Tower.AsDifferentials.complexQuadraticTerm,
      Tower.AsDifferentials.quadraticTermAt, dif_pos (And.intro hA hA')]
    exact (hq.2.2 ⟨A, hA⟩ ⟨A', hA'⟩ c).2
  · simp only [Tower.FullSpace.AsDifferentials.complexQuadraticTerm,
      Tower.AsDifferentials.quadraticTermAt, dif_pos (And.intro hA hA')]
    exact (hq'.2.2 ⟨A, hA⟩ ⟨A', hA'⟩ c).2
  · exact complexQuadraticTerm_hasFiniteSupp (h₃ L hL k hk).2 hE hW.1 hq' hA hAf hA'
end YangMills.Construction.LocalKernels.QuadraticTermsAtLift
end
