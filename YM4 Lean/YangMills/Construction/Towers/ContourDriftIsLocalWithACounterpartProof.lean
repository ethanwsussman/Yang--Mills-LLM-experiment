import YangMills.Construction.Lattice.ContourFamiliesAndCombsInABlock
import YangMills.Construction.Towers.ContourDriftIsLocalWithACounterpart
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.PeriodicExtensionOfAConfigurationIsAConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.ContourDriftLocality
open Periodisation Tower
open Conventions (IsAdmissibleBlockingFactor)
open InfiniteLattice (AmbientSpace)
open Matrices (ComplexMatrix2)
variable {L n k j : ℕ}
theorem eventually_of_smul_form {a : ℝ} {IsFormed : (InfiniteLattice.Link a → ComplexMatrix2) → Prop}
    {p v : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : Tower.AsDifferentials.IsLocallyHolomorphicLog
      (fun b : InfiniteLattice.Link a => b.IsPositivelyOriented) (FullSpace.complexEdgeForms a)
        IsFormed p v)
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms a) :
    ∀ᶠ t : ℂ in 𝓝 0, IsFormed (t • B) := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.eventually_defined_smul <;> assumption
theorem pathHolonomy_congr {m : ℕ} {i : ℤ} {W W' : PeriodicLattice.Bond L m i → ComplexMatrix2}
    {Γ : List (PeriodicLattice.Bond L m i)} (h : ∀ b ∈ Γ, W b = W' b) :
    PeriodicLattice.pathHolonomy W Γ = PeriodicLattice.pathHolonomy W' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
theorem complexMeanContourHolonomy_congr (hC : PeriodicLattice.BlockContoursAndCombs)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) {c : Edge L n k (j + 1)}
    {y : Vertex L n k (j + 1)} (hy : y = c.source ∨ y = c.target) {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {W W' : Edge L n k j → ComplexMatrix2}
    (he : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), W b = W' b) :
    PeriodicLattice.complexMeanContourHolonomy W y x =
      PeriodicLattice.complexMeanContourHolonomy W' y x := by
  unfold PeriodicLattice.complexMeanContourHolonomy
  congr 1
  funext σ
  refine pathHolonomy_congr fun b hb => he b ?_
  have hin := ((hC L n k hL hn j hj y x hx).2.1 _ ⟨σ, rfl⟩).2.2.1 b hb
  rcases hy with rfl | rfl
  · exact ⟨Or.inl hin.1, Or.inl hin.2⟩
  · exact ⟨Or.inr hin.1, Or.inr hin.2⟩
theorem complexContourMean_liftGaugeField
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : SmoothingNearIdentity)
    (hQ : EdgeProjectionProperties)
    (hC : PeriodicLattice.BlockContoursAndCombs)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {W : Edge L n k j → ComplexMatrix2}
    (hW : liftGaugeField L n k j W ∈
      FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c)
    {y : FullSpace.Vertex L k (j + 1)} (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y)
    (hx' : FullSpace.projVertex L n k j x ∈
      PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (FullSpace.projVertex L n k (j + 1) y)) :
    FullSpace.complexContourMean L (liftGaugeField L n k j W) y x =
      PeriodicLattice.complexMeanContourHolonomy W (FullSpace.projVertex L n k (j + 1) y)
        (FullSpace.projVertex L n k j x) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have Q : FullSpace.ProjPreservesStructures L n k j c :=
    ((hF L hL0 hL k).2.2.2.2.2.2 hk n hn).2 j hj c hc
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  rw [Q.complexContourMean_eq _ (hserve.subset_complexDomain hW) y hy x hx]
  have hends := (hQ L n k (j + 1) hL hn hj).1 c
  refine complexMeanContourHolonomy_congr hC hL hn hj
    (c := FullSpace.projEdge L n k (j + 1) c) ?_ hx' ?_
  · rcases hy with rfl | rfl
    · exact Or.inl hends.1.symm
    · exact Or.inr hends.2.1.symm
  · intro b hb
    rw [← Q.doubleCubeLinks_image] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact (Q.projField_spec _ hW.1).1 b' hb'
theorem complexContourMean_congr
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : SmoothingNearIdentity)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal) {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y)
    {W W' : FullSpace.Edge L k j → ComplexMatrix2}
    (hW : W ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hW' : W' ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, W b = W' b) :
    FullSpace.complexContourMean L W y x = FullSpace.complexContourMean L W' y x := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have Q : FullSpace.ProjPreservesStructures L n k j c :=
    ((hF L hL0 hL k).2.2.2.2.2.2 hk n hn).2 j hj c hc
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  rw [Q.complexContourMean_eq W (hserve.subset_complexDomain hW) y hy x hx,
    Q.complexContourMean_eq W' (hserve.subset_complexDomain hW') y hy x hx]
  congr 1
  funext z
  unfold FullSpace.projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem isPositivelyOriented_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem supNormVec_initial_sub_le (hZ : BlockPathContourPivotStatement)
    (hL : IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {b : FullSpace.Edge L k j}
    (hb : b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c) :
    TorusMetric.supNormVec ((b.initial : AmbientSpace) - (c.initial : AmbientSpace)) ≤
      3 * meshAt L k (j + 1) / 2 := by
  have Z : FullSpace.AdjacentCubesBounds L k 1 (j + 1) :=
    (hZ L hL k 1 (j + 1) (by omega) (by omega) hj).2.2.2.2.2.1
  obtain ⟨ν, hν, hlt⟩ := Z.sites_near c hc _ hb.1
  refine Finset.sup'_le _ _ fun μ _ => ?_
  have e : ((b.initial : AmbientSpace) - (c.initial : AmbientSpace)) μ =
      (ν μ : ℝ) * meshAt L k (j + 1 - 1) := by
    rw [hν]
    simp [FullSpace.offsetPoint, Finset.sum_apply, Pi.single_apply]
  rw [e]
  have := hlt μ
  linarith
theorem comp_projEdge_mem_complexEdgeForms (hQ : EdgeProjectionProperties)
    (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {f : Edge L n k j → ComplexMatrix2} (hf : f ∈ complexEdgeForms L n k j) :
    (fun b => f (FullSpace.projEdge L n k j b)) ∈ FullSpace.complexEdgeForms (meshAt L k j) := by
  have hq := (hQ L n k j hL hn hj).1
  refine ⟨fun b hb => hf.1 _ ((hq b).2.2.1 hb), fun b => ?_⟩
  show f _ = -f _
  rw [← (hq b).2.2.2]
  exact hf.2 _
theorem expTwist_liftGaugeField (hQ : EdgeProjectionProperties)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (W f : Edge L n k j → ComplexMatrix2) :
    FullSpace.expTwist (fun b => f (FullSpace.projEdge L n k j b))
        (liftGaugeField L n k j W) =
      liftGaugeField L n k j (PeriodicLattice.expTwist f W) := by
  classical
  funext b
  have hq := (hQ L n k j hL hn hj.le).1
  show _ = PeriodicLattice.expTwist f W (FullSpace.projEdge L n k j b)
  by_cases hb : b.IsPositivelyOriented
  · have hp := (hq b).2.2.1 hb
    simp only [FullSpace.expTwist, PeriodicLattice.expTwist, if_pos hb, if_pos hp]
    rfl
  · have hr : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hb
    have hrq : (FullSpace.projEdge L n k j b).opposite.IsPositivelyOriented := by
      rw [(hq b).2.2.2]
      exact (hq b.opposite).2.2.1 hr
    have hnq : ¬(FullSpace.projEdge L n k j b).IsPositivelyOriented := by
      rcases hP L n k hL hn (by omega) j hj.le (FullSpace.projEdge L n k j b) with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hrq h
      · exact h
    simp only [FullSpace.expTwist, PeriodicLattice.expTwist, if_neg hb, if_neg hnq, (hq b).2.2.2]
    rfl
theorem forwardFrom_isPositivelyOriented (y : FullSpace.Vertex L k (j + 1)) :
    (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.forwardFrom_positive <;> assumption
theorem contourLogDrift_congr (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : SmoothingNearIdentity)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2} {U' : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hw : FullSpace.AsDifferentials.StepConditions j V U')
    {f g : FullSpace.Edge L k j → ComplexMatrix2} (hf : f ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hg : g ∈ FullSpace.complexEdgeForms (meshAt L k j)) (y : FullSpace.Vertex L k (j + 1))
    (hfg : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) (InfiniteLattice.Link.forwardFrom y 0),
      b.IsPositivelyOriented → f b = g b) :
    FullSpace.contourLogDrift V f y = FullSpace.contourLogDrift V g y := by
  have hc := forwardFrom_isPositivelyOriented (L := L) (k := k) (j := j) y
  have hexp : ∀ t : ℂ,
      ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) (InfiniteLattice.Link.forwardFrom y 0),
      FullSpace.expTwist (t • f) V b = FullSpace.expTwist (t • g) V b := by
    classical
    intro t b hb
    by_cases hp : b.IsPositivelyOriented
    · simp only [FullSpace.expTwist, if_pos hp, Pi.smul_apply, hfg b hb hp]
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hp
      simp only [FullSpace.expTwist, if_neg hp, Pi.smul_apply, hfg b.opposite ⟨hb.2, hb.1⟩ hr]
  have nf := eventually_of_smul_form (hw.local_mean _ hc) hf
  have ng := eventually_of_smul_form (hw.local_mean _ hc) hg
  unfold FullSpace.contourLogDrift
  refine congrArg (fun w => PeriodicLattice.inverseFourthPowerWeight L • w)
    (finsum_mem_congr rfl fun x hx => ?_)
  unfold logDirectionalDeriv
  refine congrArg (fun w => Complex.I⁻¹ • w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [nf, ng] with t hft hgt
  show ComplexMatrix2.logSeries
      (FullSpace.complexContourMean L (FullSpace.expTwist (t • f) V) y x * _) =
    ComplexMatrix2.logSeries
      (FullSpace.complexContourMean L (FullSpace.expTwist (t • g) V) y x * _)
  rw [complexContourMean_congr (n := n) (y := y) hF hS hL hn hj hc (Or.inl rfl) hx hft hgt
    (hexp t)]
theorem contourLogDrift_liftGaugeField
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : SmoothingNearIdentity)
    (hQ : EdgeProjectionProperties)
    (hC : PeriodicLattice.BlockContoursAndCombs)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {V : Edge L n k j → ComplexMatrix2}
    {U' : FullSpace.Edge L k 0 → ComplexMatrix2} (hw : FullSpace.AsDifferentials.StepConditions j
      (liftGaugeField L n k j V) U')
    (hVw : liftGaugeField L n k j V ∈ FullSpace.smallComplexFields L k j)
    {f : Edge L n k j → ComplexMatrix2} (hf : f ∈ complexEdgeForms L n k j)
    (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.contourLogDrift (liftGaugeField L n k j V)
        (fun b => f (FullSpace.projEdge L n k j b)) y =
      contourLogDrift V f (FullSpace.projVertex L n k (j + 1) y) := by
  have hk : 1 ≤ k := by omega
  have hL0 : 0 < L := by have := hL.2; omega
  have hc := forwardFrom_isPositivelyOriented (L := L) (k := k) (j := j) y
  have hpoly : liftGaugeField L n k j V ∈
      FullSpace.nearIdentityPolydisc L k j (polydiscRadius L)
        (InfiniteLattice.Link.forwardFrom y 0) :=
    ⟨⟨fun b _ => hVw.1.1 b, fun b _ => hVw.1.2 b⟩, fun b _ => hVw.2 b⟩
  have Q : FullSpace.ProjPreservesStructures L n k j (InfiniteLattice.Link.forwardFrom y 0) :=
    ((hF L hL0 hL k).2.2.2.2.2.2 hk n hn).2 j hj _ hc
  have hdt : (FullSpace.projEdge L n k (j + 1) (InfiniteLattice.Link.forwardFrom y 0)).source =
      FullSpace.projVertex L n k (j + 1) y := ((hQ L n k (j + 1) hL hn hj).1 _).1
  have hpart : FullSpace.CubesOfOrderPartition L k (j + 1) 1 :=
    (hB L hL k (j + 1) 1 hk (by omega) hj le_rfl (by omega)).1
  have hbij : BijOn (FullSpace.projVertex L n k j) (FullSpace.cubeVertices L (meshAt L k j) y)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (FullSpace.projVertex L n k (j + 1) y)) := by
    rw [← hdt]
    refine ⟨fun x hx => ?_, fun x hx x' hx' h => ?_, fun x' hx' => ?_⟩
    · show ((FullSpace.projVertex L n k j x : Tower.Vertex L n k j) :
          PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.unitBlock (FullSpace.projEdge L n k (j + 1)
          (InfiniteLattice.Link.forwardFrom y 0)).source
      rw [← Q.cube_initial]
      exact ⟨_, hx, rfl⟩
    · exact Subtype.ext (Q.injOn_doubleCube (Or.inl hx) (Or.inl hx') (congrArg Subtype.val h))
    · have hx'' : (x' : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock (FullSpace.projEdge L n k (j + 1)
            (InfiniteLattice.Link.forwardFrom y 0)).source := hx'
      rw [← Q.cube_initial] at hx''
      obtain ⟨p, hp, he⟩ := hx''
      have hps : p ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := by
        have hu := hpart.iUnion_cube
        have : p ∈ ⋃ y : FullSpace.Vertex L k (j + 1),
            FullSpace.cubeOfOrder L (meshAt L k j) 1 y :=
          mem_iUnion.2 ⟨y, hp⟩
        exact hu ▸ this
      exact ⟨⟨p, hps⟩, hp, Subtype.ext he⟩
  have hf' := comp_projEdge_mem_complexEdgeForms hQ hL hn hj.le hf
  have near := eventually_of_smul_form (hw.local_mean _ hc) hf'
  unfold FullSpace.contourLogDrift contourLogDrift
  congr 1
  refine finsum_mem_eq_of_bijOn _ hbij fun x hx => ?_
  have hx' := hbij.mapsTo hx
  have h0 := complexContourMean_liftGaugeField hF hS hQ hC hL hn hj hc hpoly (y := y)
    (Or.inl rfl) hx hx'
  unfold logDirectionalDeriv
  rw [h0]
  refine congrArg (fun w => Complex.I⁻¹ • w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [near] with t ht
  have e : FullSpace.expTwist (t • fun b => f (FullSpace.projEdge L n k j b))
      (liftGaugeField L n k j V) =
      liftGaugeField L n k j (PeriodicLattice.expTwist (t • f) V) :=
    expTwist_liftGaugeField hQ hP hL hn hj V (t • f)
  have ht' : liftGaugeField L n k j (PeriodicLattice.expTwist (t • f) V) ∈
      FullSpace.nearIdentityPolydisc L k j (polydiscRadius L)
        (InfiniteLattice.Link.forwardFrom y 0) := e ▸ ht
  have h1 := complexContourMean_liftGaugeField hF hS hQ hC hL hn hj hc ht' (y := y)
    (Or.inl rfl) hx hx'
  show ComplexMatrix2.logSeries (FullSpace.complexContourMean L (FullSpace.expTwist
      (t • fun b => f (FullSpace.projEdge L n k j b))
      (liftGaugeField L n k j V)) y x * _) =
    ComplexMatrix2.logSeries
      (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • f) V)
        (FullSpace.projVertex L n k (j + 1) y) (FullSpace.projVertex L n k j x) * _)
  rw [e, h1]
theorem isLocalWithPeriodicCounterpart_of_stepProperties
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : SmoothingNearIdentity)
    (hQ : EdgeProjectionProperties)
    (hC : PeriodicLattice.BlockContoursAndCombs)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hZ : BlockPathContourPivotStatement)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {V : Edge L n k j → ComplexMatrix2} {U : Edge L n k 0 → ComplexMatrix2}
    (hs : Tower.AsDifferentials.StepConditions j V U)
    {U' : FullSpace.Edge L k 0 → ComplexMatrix2} (hw : FullSpace.AsDifferentials.StepConditions j
      (liftGaugeField L n k j V) U')
    (hVw : liftGaugeField L n k j V ∈ FullSpace.smallComplexFields L k j) :
    IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j hj.le)
      (CellClass.vertexClass k (j + 1) hj)
      (3 * meshAt L k (j + 1) / 2)
      (FullSpace.contourLogDrift (liftGaugeField L n k j V)) (contourLogDrift V) := by
  refine ⟨⟨fun f hf y _ => hw.mem_contour y f hf,
      fun f hf g hg => (hw.linear_contour f hf g hg 0).1,
      fun z f hf => (hw.linear_contour f hf f hf z).2, ?_⟩,
    ⟨fun f hf y _ => hs.mem_contour y f hf,
      fun f hf g hg => (hs.linear_contour f hf g hg 0).1,
      fun z f hf => (hs.linear_contour f hf f hf z).2⟩, ?_⟩
  · intro f hf g hg y hagree
    exact contourLogDrift_congr (n := n) hF hS hL hn hj hw hf hg y fun b hb hp =>
      hagree (⟨b, hp⟩ : PeriodicOperators.PosEdge L k j)
        (supNormVec_initial_sub_le hZ hL hj (forwardFrom_isPositivelyOriented y) hb)
  · intro f hf y
    exact contourLogDrift_liftGaugeField hF hS hQ hC hP hB hL hn hj hw hVw hf y
theorem contourLogDriftIsLocal_holds (hD : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hI : IterMeansOfLift.Claim)
    (hE : LiftIsGaugeField)
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : SmoothingNearIdentity)
    (hQ : EdgeProjectionProperties)
    (hC : PeriodicLattice.BlockContoursAndCombs)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hZ : BlockPathContourPivotStatement)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths) : ContourLogDriftIsLocal := by
  intro L hL k n hn U hU j h
  have hk : 1 ≤ k := by omega
  have hj : j < k := h
  have hV := hU.2 j hj
  have hVw : liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U) ∈
      FullSpace.smallComplexFields L k j :=
    ⟨(hE L n k j hL hn hj.le _).2 hV.1, fun _ => hV.2 _⟩
  have hUw := (hI L hL k n hn hk U hU.1).1.1 hU
  exact isLocalWithPeriodicCounterpart_of_stepProperties hF hS hQ hC hP hZ hB hL hn hj
    (((hD L hL k hk).1 n hn).1 j hj _ hV U hU) ((hD L hL k hk).2.1 j hj _ hVw _ hUw) hVw
end YangMills.Construction.LocalKernels.ContourDriftLocality
end
