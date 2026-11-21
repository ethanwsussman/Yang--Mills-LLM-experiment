import YangMills.Construction.Towers.AdjointBlockAverageIsLocalWithACounterpart
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBond
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.LinearityOfTheCovariantMapsOfAStepOnTheSides
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.PeriodicExtensionOfAConfigurationIsAConfiguration
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurations
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.AdjointCubeAverageLocality
theorem mem_tracelessFunctions_iff {ι : Type} {f : ι → Matrices.ComplexMatrix2} :
    f ∈ Matrices.GroupLieProduct.tracelessFunctions ι ↔ ∀ x, f x ∈ Matrices.ComplexMatrix2.traceless :=
  ⟨fun h x => h x (mem_univ x), fun h x _ => h x⟩
theorem additive_and_homogeneous_of_combination {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] {P : M → Prop} (hP0 : P 0) {φ : M → N}
    (hφ : ∀ u v, P u → P v → ∀ c : ℂ, φ (c • u + v) = c • φ u + φ v) :
    (∀ u v, P u → P v → φ (u + v) = φ u + φ v) ∧ ∀ (z : ℂ) u, P u → φ (z • u) = z • φ u := by
  have hadd : ∀ u v, P u → P v → φ (u + v) = φ u + φ v := fun u v hu hv => by
    simpa using hφ u v hu hv 1
  have hzero : φ 0 = 0 := by simpa using hadd 0 0 hP0 hP0
  refine ⟨hadd, fun z u hu => ?_⟩
  simpa [hzero] using hφ u 0 hu hP0 z
section Step
variable {L n k : ℕ}
theorem meshAt_succ (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) :
    Tower.meshAt L k (j + 1) = L * Tower.meshAt L k j := by
  have : (L : ℝ) ≠ 0 := by exact_mod_cast (by have := hL.2; omega : L ≠ 0)
  unfold Tower.meshAt
  push_cast
  rw [show (j : ℤ) + 1 - (k : ℤ) = (j : ℤ) - (k : ℤ) + 1 by ring, zpow_add_one₀ this]
  ring
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) :
    0 < Tower.meshAt L k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem supNormVec_sub_le_of_mem_cubeVertices (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} {y : Tower.FullSpace.Vertex L k (j + 1)} {x : Tower.FullSpace.Vertex L k j}
    (hx : x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y) :
    TorusMetric.supNormVec ((x : InfiniteLattice.AmbientSpace) - (y : InfiniteLattice.AmbientSpace)) ≤
      Tower.meshAt L k (j + 1) / 2 := by
  obtain ⟨ν, hν, he⟩ := hx
  refine Finset.sup'_le _ _ fun μ _ => ?_
  have hv : ((x : InfiniteLattice.AmbientSpace) - (y : InfiniteLattice.AmbientSpace)) μ =
      (ν μ : ℝ) * Tower.meshAt L k j := by
    rw [Pi.sub_apply, he]
    simp [Finset.sum_apply, Pi.single_apply]
  have hb : 2 * |(ν μ : ℝ)| ≤ (L : ℝ) - 1 := by
    have := hν μ
    have h' : ((2 * |ν μ| : ℤ) : ℝ) ≤ (((L : ℤ) ^ 1 - 1 : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hp := meshAt_pos (k := k) hL j
  rw [hv, abs_mul, abs_of_pos hp, meshAt_succ hL]
  nlinarith
theorem mem_latticeSubgroup_of_mem_cube (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ}
    {y : Tower.FullSpace.Vertex L k (j + 1)} {p : InfiniteLattice.AmbientSpace}
    (hp : p ∈ Tower.FullSpace.cube L (Tower.meshAt L k j) y) :
    p ∈ (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) : Set InfiniteLattice.AmbientSpace) := by
  obtain ⟨ν, -, rfl⟩ := hp
  obtain ⟨m, hm⟩ := y.2
  refine ⟨fun μ => m μ * (L : ℤ) + ν μ, fun μ => ?_⟩
  simp only [Pi.add_apply, Finset.sum_apply, Pi.single_apply]
  rw [hm μ, meshAt_succ hL]
  simp
  ring
theorem liftGaugeField_mem_smallComplexFields (hlift : LiftIsGaugeField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hV : V ∈ Tower.smallComplexFields L n k j) :
    liftGaugeField L n k j V ∈ Tower.FullSpace.smallComplexFields L k j :=
  ⟨(hlift L n k j hL hn hj V).2 hV.1, fun _ => hV.2 _⟩
theorem bijOn_cubeVertices_and_contourMean_eq (hproj : Tower.EdgeProjectionProperties)
    (hfields : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (hsetsAll : Tower.ProjectionCarriesSetsStatement)
    (hnear : Tower.SmoothingNearIdentity)
    (hlift : LiftIsGaugeField)
    (hpair : Tower.PairContourIndependence.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2} (hV : V ∈ Tower.smallComplexFields L n k j)
    (y : Tower.FullSpace.Vertex L k (j + 1)) :
    BijOn (Tower.FullSpace.projVertex L n k j) (Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y)
        (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
          (Tower.FullSpace.projVertex L n k (j + 1) y)) ∧
      ∀ x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y,
        Tower.FullSpace.complexContourMean L (liftGaugeField L n k j V) y x =
          PeriodicLattice.complexMeanContourHolonomy V (Tower.FullSpace.projVertex L n k (j + 1) y)
            (Tower.FullSpace.projVertex L n k j x) := by
  obtain ⟨c, rfl, hc⟩ : ∃ c : Tower.FullSpace.Edge L k (j + 1), c.initial = y ∧ c.IsPositivelyOriented :=
    ⟨InfiniteLattice.Link.forwardFrom y 0, rfl, ⟨0, add_sub_cancel_left _ _⟩⟩
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have hρ := (hnear.1 L hL).2.2
  have hVe := liftGaugeField_mem_smallComplexFields hlift hL hn hj.le hV
  have hcfg := hfields L hL0 hL k hk n hn j hj c hc
  have hsets := (hsetsAll L hL0 hL k hk n hn).2 j hj c hc
  have hOn : Tower.FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup
      (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c)
      (liftGaugeField L n k j V) :=
    ⟨fun b _ => hVe.1.1 b, fun b _ => hVe.1.2 b⟩
  have hdom := (hρ.fullSpace k j hj c hc).subset_complexDomain
    (show liftGaugeField L n k j V ∈
        Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c from
      ⟨hOn, fun b _ => hVe.2 b⟩)
  have hq := (hproj L n k (j + 1) hL hn hj).1 c
  have hcpos : (Tower.FullSpace.projEdge L n k (j + 1) c).IsPositivelyOriented := hq.2.2.1 hc
  have hagree : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (Tower.FullSpace.projEdge L n k (j + 1) c) :
      Set (Tower.Edge L n k j)),
      Tower.FullSpace.projField L n k j (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c)
        (liftGaugeField L n k j V) b = V b := by
    intro b hb
    rw [← hsets.doubleCubeLinks_image] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact (hcfg.projField_spec _ hOn).1 b' hb'
  rw [← hq.1]
  have hbij : BijOn (Tower.FullSpace.projVertex L n k j)
      (Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (Tower.FullSpace.projEdge L n k (j + 1) c).source) := by
    refine ⟨fun x hx => ?_, fun x hx x' hx' h => ?_, fun x' hx' => ?_⟩
    · show ((Tower.FullSpace.projVertex L n k j x : Tower.Vertex L n k j) :
        PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock (Tower.FullSpace.projEdge L n k (j + 1) c).source
      rw [← hsets.cube_initial]
      exact ⟨_, hx, rfl⟩
    · exact Subtype.ext (hsets.injOn_doubleCube (Or.inl hx) (Or.inl hx') (congrArg Subtype.val h))
    · have hx'' : (x' : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock (Tower.FullSpace.projEdge L n k (j + 1) c).source := hx'
      rw [← hsets.cube_initial] at hx''
      obtain ⟨p, hp, he⟩ := hx''
      exact ⟨⟨p, mem_latticeSubgroup_of_mem_cube hL hp⟩, hp, Subtype.ext he⟩
  refine ⟨hbij, fun x hx => ?_⟩
  rw [hcfg.complexContourMean_eq _ hdom c.initial (Or.inl rfl) x hx, hq.1]
  have hxb := hbij.mapsTo hx
  rw [hq.1] at hxb
  have hmem : Tower.FullSpace.projVertex L n k (j + 1) c.initial ∈
      ({(Tower.FullSpace.projEdge L n k (j + 1) c).source,
        (Tower.FullSpace.projEdge L n k (j + 1) c).target} :
        Set (Tower.Vertex L n k (j + 1))) := Or.inl hq.1.symm
  exact ((hpair L hL k j hj).1 n hn _ _ hxb _ _ hcpos hcpos hmem hmem V hV.1
    (fun b _ => hV.2 b) (fun b _ => hV.2 b) _ V hagree fun _ _ => rfl).2.2
end Step
theorem adjointCubeAverage_isLocalPeriodic (hproj : Tower.EdgeProjectionProperties)
    (hfields : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (hsetsAll : Tower.ProjectionCarriesSetsStatement)
    (hnear : Tower.SmoothingNearIdentity)
    (hlift : LiftIsGaugeField)
    (hpair : Tower.PairContourIndependence.Statement)
    (hfull : Tower.FullSpace.CovariantStepComplexLinear)
    (hstep : Tower.StepMapsComplexLinear.Claim) : AdjointCubeAverageIsLocalPeriodic := by
  intro L hL k n hn U hU j h
  have hV : PeriodicLattice.complexBlockFieldAtLevel j U ∈ Tower.smallComplexFields L n k j :=
    hU.2 j h
  have hVe := liftGaugeField_mem_smallComplexFields hlift hL hn (Nat.le_of_succ_le h) hV
  have hW := hfull L hL k j h _ hVe
  have hS := hstep L hL n k j hn h _ hV
  obtain ⟨hWadd, hWsmul⟩ := additive_and_homogeneous_of_combination
    (P := fun u : Tower.FullSpace.Vertex L k j → Matrices.ComplexMatrix2 =>
      ∀ x, u x ∈ Matrices.ComplexMatrix2.traceless) (fun _ => Submodule.zero_mem _)
    (fun u v hu hv c => (hW.2.2.2 u v hu hv c).2)
  obtain ⟨hSadd, hSsmul⟩ := additive_and_homogeneous_of_combination
    (P := fun u : Tower.Vertex L n k j → Matrices.ComplexMatrix2 =>
      ∀ x, u x ∈ Matrices.ComplexMatrix2.traceless) (fun _ => Submodule.zero_mem _)
    (fun u v hu hv c => (hS.2.2.2 u v hu hv c).2)
  refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg y hc => ?_⟩,
    ⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf y => ?_⟩
  · exact mem_tracelessFunctions_iff.2 (hW.2.2.1 f (mem_tracelessFunctions_iff.1 hf)).2
  · exact hWadd f g (mem_tracelessFunctions_iff.1 hf) (mem_tracelessFunctions_iff.1 hg)
  · exact hWsmul z f (mem_tracelessFunctions_iff.1 hf)
  · show Tower.FullSpace.adjointCubeAverage
        (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)) f y =
      Tower.FullSpace.adjointCubeAverage
        (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)) g y
    unfold Tower.FullSpace.adjointCubeAverage
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    have e : f x = g x := hc x (supNormVec_sub_le_of_mem_cubeVertices hL hx)
    rw [e]
  · exact mem_tracelessFunctions_iff.2 (hS.2.2.1 f (mem_tracelessFunctions_iff.1 hf)).2
  · exact hSadd f g (mem_tracelessFunctions_iff.1 hf) (mem_tracelessFunctions_iff.1 hg)
  · exact hSsmul z f (mem_tracelessFunctions_iff.1 hf)
  · obtain ⟨hbij, hcont⟩ :=
      bijOn_cubeVertices_and_contourMean_eq hproj hfields hsetsAll hnear hlift hpair hL hn h hV y
    show Tower.FullSpace.adjointCubeAverage
        (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U))
        (fun x => f (Tower.FullSpace.projVertex L n k j x)) y =
      Tower.adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U) f
        (Tower.FullSpace.projVertex L n k (j + 1) y)
    unfold Tower.FullSpace.adjointCubeAverage Tower.adjointCubeAverage
    congr 1
    refine finsum_mem_eq_of_bijOn (Tower.FullSpace.projVertex L n k j) hbij fun x hx => ?_
    rw [hcont x hx]
end YangMills.Construction.LocalKernels.AdjointCubeAverageLocality
end
