import YangMills.Construction.RunningCouplingSlope.AdjointBlockAverageAtASmallConfiguration
import YangMills.Construction.Towers.AdjointBlockAverageIsLocalWithACounterpartProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.CubeAverageLocality
theorem traceless_fun_iff {ι : Type} {f : ι → Matrices.ComplexMatrix2} :
    f ∈ Matrices.GroupLieProduct.tracelessFunctions ι ↔ ∀ x, f x ∈ Matrices.ComplexMatrix2.traceless :=
  ⟨fun h x => h x (mem_univ x), fun h x _ => h x⟩
theorem additive_homogeneous_of_affine_combination {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] {P : M → Prop} (hP0 : P 0) {φ : M → N}
    (hφ : ∀ u v, P u → P v → ∀ c : ℂ, φ (c • u + v) = c • φ u + φ v) :
    (∀ u v, P u → P v → φ (u + v) = φ u + φ v) ∧ ∀ (z : ℂ) u, P u → φ (z • u) = z • φ u := by apply _root_.YangMills.Construction.LocalKernels.AdjointCubeAverageLocality.additive_and_homogeneous_of_combination <;> assumption
section OneStep
variable {L n k : ℕ}
theorem supNorm_sub_le_of_mem_cube (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ}
    {y : Tower.FullSpace.Vertex L k (j + 1)} {x : Tower.FullSpace.Vertex L k j}
    (hx : x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y) :
    TorusMetric.supNormVec ((x : InfiniteLattice.AmbientSpace) - (y : InfiniteLattice.AmbientSpace)) ≤
      Tower.meshAt L k (j + 1) / 2 := by apply _root_.YangMills.Construction.LocalKernels.AdjointCubeAverageLocality.supNormVec_sub_le_of_mem_cubeVertices <;> assumption
theorem lift_mem_smallComplexFields (hLift : LocalKernels.LiftIsGaugeField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ Tower.smallComplexFields L n k j) :
    LocalKernels.liftGaugeField L n k j V ∈ Tower.FullSpace.smallComplexFields L k j :=
  ⟨(hLift L n k j hL hn hj V).2 hV.1, fun _ => hV.2 _⟩
theorem cube_bijOn_and_contour_eq (hEdge : Tower.EdgeProjectionProperties)
    (hFields : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (hSets : Tower.ProjectionCarriesSetsStatement)
    (hNear : Tower.SmoothingNearIdentity)
    (hLift : LocalKernels.LiftIsGaugeField)
    (hPair : Tower.PairContourIndependence.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2} (hV : V ∈ Tower.smallComplexFields L n k j)
    (y : Tower.FullSpace.Vertex L k (j + 1)) :
    BijOn (Tower.FullSpace.projVertex L n k j) (Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y)
        (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
          (Tower.FullSpace.projVertex L n k (j + 1) y)) ∧
      ∀ x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y,
        Tower.FullSpace.complexContourMean L (LocalKernels.liftGaugeField L n k j V) y x =
          PeriodicLattice.complexMeanContourHolonomy V (Tower.FullSpace.projVertex L n k (j + 1) y)
            (Tower.FullSpace.projVertex L n k j x) := by apply _root_.YangMills.Construction.LocalKernels.AdjointCubeAverageLocality.bijOn_cubeVertices_and_contourMean_eq <;> assumption
end OneStep
theorem adjointCubeAverageIsLocal_holds (hEdge : Tower.EdgeProjectionProperties)
    (hFields : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (hSets : Tower.ProjectionCarriesSetsStatement)
    (hNear : Tower.SmoothingNearIdentity)
    (hLift : LocalKernels.LiftIsGaugeField)
    (hPair : Tower.PairContourIndependence.Statement)
    (hFull : Tower.FullSpace.CovariantStepComplexLinear)
    (hStep : Tower.StepMapsComplexLinear.Claim) : LocalKernels.AdjointCubeAverageIsLocal := by
  intro L hL k n hn j h V hV
  have hVe := lift_mem_smallComplexFields hLift hL hn (Nat.le_of_succ_le h) hV
  have hW := hFull L hL k j h _ hVe
  have hS := hStep L hL n k j hn h _ hV
  obtain ⟨hWadd, hWsmul⟩ := additive_homogeneous_of_affine_combination
    (P := fun u : Tower.FullSpace.Vertex L k j → Matrices.ComplexMatrix2 =>
      ∀ x, u x ∈ Matrices.ComplexMatrix2.traceless) (fun _ => Submodule.zero_mem _)
    (fun u v hu hv c => (hW.2.2.2 u v hu hv c).2)
  obtain ⟨hSadd, hSsmul⟩ := additive_homogeneous_of_affine_combination
    (P := fun u : Tower.Vertex L n k j → Matrices.ComplexMatrix2 =>
      ∀ x, u x ∈ Matrices.ComplexMatrix2.traceless) (fun _ => Submodule.zero_mem _)
    (fun u v hu hv c => (hS.2.2.2 u v hu hv c).2)
  refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg y hc => ?_⟩,
    ⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf y => ?_⟩
  · exact traceless_fun_iff.2 (hW.2.2.1 f (traceless_fun_iff.1 hf)).2
  · exact hWadd f g (traceless_fun_iff.1 hf) (traceless_fun_iff.1 hg)
  · exact hWsmul z f (traceless_fun_iff.1 hf)
  · show Tower.FullSpace.adjointCubeAverage
        (LocalKernels.liftGaugeField L n k j V) f y =
      Tower.FullSpace.adjointCubeAverage
        (LocalKernels.liftGaugeField L n k j V) g y
    unfold Tower.FullSpace.adjointCubeAverage
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    have e : f x = g x := hc x (supNorm_sub_le_of_mem_cube hL hx)
    rw [e]
  · exact traceless_fun_iff.2 (hS.2.2.1 f (traceless_fun_iff.1 hf)).2
  · exact hSadd f g (traceless_fun_iff.1 hf) (traceless_fun_iff.1 hg)
  · exact hSsmul z f (traceless_fun_iff.1 hf)
  · obtain ⟨hbij, hcont⟩ := cube_bijOn_and_contour_eq hEdge hFields hSets hNear hLift hPair hL hn h hV y
    show Tower.FullSpace.adjointCubeAverage
        (LocalKernels.liftGaugeField L n k j V)
        (fun x => f (Tower.FullSpace.projVertex L n k j x)) y =
      Tower.adjointCubeAverage V f
        (Tower.FullSpace.projVertex L n k (j + 1) y)
    unfold Tower.FullSpace.adjointCubeAverage Tower.adjointCubeAverage
    congr 1
    refine finsum_mem_eq_of_bijOn (Tower.FullSpace.projVertex L n k j) hbij fun x hx => ?_
    rw [hcont x hx]
end YangMills.Construction.LocalKernels.CubeAverageLocality
end
