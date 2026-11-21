import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.TwoSequencesOfOneClass
import YangMills.Construction.Torus.GreenOperatorBoundsOnTheTori
import YangMills.Construction.Torus.OperatorsOfTheSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses
namespace SingleSequence
section Correspondence
variable {X X' Y Y' : Type}
def PairsUniquely (R : X → X' → Prop) : Prop := (∀ x, ∃! x', R x x') ∧ ∀ x', ∃! x, R x x'
def AgreeAlong (R : X → X' → Prop) (f : X → ℝ) (f' : X' → ℝ) : Prop := ∀ x x', R x x' → f x = f' x'
def SpacesCorrespond (R : X → X' → Prop) (E : Set (X → ℝ)) (E' : Set (X' → ℝ)) : Prop :=
  (∀ f ∈ E, ∃ f' ∈ E', AgreeAlong R f f') ∧ ∀ f' ∈ E', ∃ f ∈ E, AgreeAlong R f f'
def PairingsCorrespond (R : X → X' → Prop) (E : Set (X → ℝ)) (E' : Set (X' → ℝ))
    (p : (X → ℝ) → (X → ℝ) → ℝ) (p' : (X' → ℝ) → (X' → ℝ) → ℝ) : Prop :=
  ∀ f ∈ E, ∀ g ∈ E, ∀ f' ∈ E', ∀ g' ∈ E', AgreeAlong R f f' → AgreeAlong R g g' → p f g = p' f' g'
def OperatorsCorrespond (R : X → X' → Prop) (R' : Y → Y' → Prop) (E : Set (X → ℝ)) (E' : Set (X' → ℝ))
    (T : (X → ℝ) → Y → ℝ) (T' : (X' → ℝ) → Y' → ℝ) : Prop :=
  ∀ f ∈ E, ∀ f' ∈ E', AgreeAlong R f f' → AgreeAlong R' (T f) (T' f')
open Classical in
def extendByZero (E : Submodule ℝ (X → ℝ)) (T : ↥E → Y → ℝ) (f : X → ℝ) : Y → ℝ :=
  if h : f ∈ E then T ⟨f, h⟩ else 0
end Correspondence
structure ScalarData (T : Type) where
  Site : Type
  pos : Site → T
  space : Set (Site → ℝ)
  inner : (Site → ℝ) → (Site → ℝ) → ℝ
  Coarse : Type
  coarsePos : Coarse → T
  coarseInner : (Coarse → ℝ) → (Coarse → ℝ) → ℝ
  avg : (Site → ℝ) → Coarse → ℝ
  op : (Site → ℝ) → Site → ℝ
  inv : (Site → ℝ) → Site → ℝ
namespace ScalarData
variable {T T' : Type} (A : ScalarData T) (A' : ScalarData T') (r : T → T')
def SiteRel (x : A.Site) (x' : A'.Site) : Prop := r (A.pos x) = A'.pos x'
def CoarseRel (y : A.Coarse) (y' : A'.Coarse) : Prop := r (A.coarsePos y) = A'.coarsePos y'
structure Corresponds : Prop where
  sites : PairsUniquely (SiteRel A A' r)
  coarse : PairsUniquely (CoarseRel A A' r)
  space : SpacesCorrespond (SiteRel A A' r) A.space A'.space
  inner : PairingsCorrespond (SiteRel A A' r) A.space A'.space A.inner A'.inner
  coarseInner : PairingsCorrespond (CoarseRel A A' r) univ univ A.coarseInner A'.coarseInner
  avg : OperatorsCorrespond (SiteRel A A' r) (CoarseRel A A' r) A.space A'.space A.avg A'.avg
  op : OperatorsCorrespond (SiteRel A A' r) (SiteRel A A' r) A.space A'.space A.op A'.op
  inv : OperatorsCorrespond (SiteRel A A' r) (SiteRel A A' r) A.space A'.space A.inv A'.inv
end ScalarData
structure OneFormData (T : Type) where
  Bond : Type
  endpoints : Bond → T × T
  space : Set (Bond → ℝ)
  inner : (Bond → ℝ) → (Bond → ℝ) → ℝ
namespace OneFormData
variable {T T' : Type} (A : OneFormData T) (A' : OneFormData T') (r : T → T')
def BondRel (b : A.Bond) (b' : A'.Bond) : Prop :=
  (r (A.endpoints b).1, r (A.endpoints b).2) = A'.endpoints b'
structure Corresponds : Prop where
  bonds : PairsUniquely (BondRel A A' r)
  space : SpacesCorrespond (BondRel A A' r) A.space A'.space
  inner : PairingsCorrespond (BondRel A A' r) A.space A'.space A.inner A'.inner
end OneFormData
structure CoarseOneFormData (T : Type) extends OneFormData T where
  WilsonWeightSeriesExpansion : Type
  expansionPos : WilsonWeightSeriesExpansion → ℕ × T × T
  avg : (Bond → ℝ) → WilsonWeightSeriesExpansion → ℝ
  op : (Bond → ℝ) → Bond → ℝ
  inv : (Bond → ℝ) → Bond → ℝ
namespace CoarseOneFormData
variable {T T' : Type} (A : CoarseOneFormData T) (A' : CoarseOneFormData T') (r : T → T')
def RowRel (c : A.WilsonWeightSeriesExpansion) (c' : A'.WilsonWeightSeriesExpansion) : Prop :=
  ((A.expansionPos c).1, r (A.expansionPos c).2.1, r (A.expansionPos c).2.2) = A'.expansionPos c'
abbrev BondRel : A.Bond → A'.Bond → Prop := OneFormData.BondRel A.toOneFormData A'.toOneFormData r
structure Corresponds : Prop where
  forms : OneFormData.Corresponds A.toOneFormData A'.toOneFormData r
  standingConstraints : PairsUniquely (RowRel A A' r)
  avg : OperatorsCorrespond (BondRel A A' r) (RowRel A A' r) A.space A'.space A.avg A'.avg
  op : OperatorsCorrespond (BondRel A A' r) (BondRel A A' r) A.space A'.space A.op A'.op
  inv : OperatorsCorrespond (BondRel A A' r) (BondRel A A' r) A.space A'.space A.inv A'.inv
end CoarseOneFormData
structure SequenceData where
  data : ClassData
  Ω : ℕ → Set data.Point
  Ω_mem : Ω ∈ data.separatedClass
  frame : BondFrame
namespace SequenceData
variable (s : SequenceData)
abbrev params : SeparatedSequences.BaseParameters := s.data.baseParamsAt 1 one_pos
abbrev Lreal : ℝ := (s.data.L : ℝ)
def mesh : ℝ := Torus.unitSpacing s.data.L s.data.t
def unitTorusSide : ℝ := Torus.unitSide s.data.L s.data.m s.data.cutoff s.data.t
abbrev lastIdx : ℕ := s.data.lastNonempty s.Ω
def L_le_blockSize : Prop := s.data.L ≤ s.data.blockSize
theorem torusSide_ne_zero : PeriodicLattice.torusSide s.data.L s.data.m ≠ 0 := by
  have h := s.data.isAdmissible.2
  have hL : (s.data.L : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.data.L ≠ 0)
  exact mul_ne_zero two_ne_zero (pow_ne_zero _ hL)
open Classical in
def toTorus (S : ℝ) (x : s.data.Point) : Torus4 S :=
  if h : S ≠ 0 then fun μ => AddCircle.equivAddCircle _ S s.torusSide_ne_zero h (x μ) else 0
def regionOn (S : ℝ) (n : ℕ) : Set (Torus4 S) := s.toTorus S '' s.Ω n
def unitScale : ℝ := s.Lreal ^ (s.data.cutoff - s.data.t)
def scaleSegment (g : LiftedSegment) : LiftedSegment := ⟨s.unitScale • g.tail, s.unitScale • g.head⟩
def scaleSegmentDir (g : LiftedSegment) : Torus.TorusSegment 4 :=
  ⟨s.unitScale • g.tail, s.unitScale • g.displacement⟩
def bondEnds {j : ℤ} (c : PeriodicLattice.PositivelyOrientedBond s.data.L s.data.m j) :
    s.data.Point × s.data.Point :=
  ((c.1.source : s.data.Point), (c.1.target : s.data.Point))
def bondSetChoice : BondFrame → GeneralTorus.BondSetChoice
  | BondFrame.star => .meeting
  | BondFrame.interior => .interior
theorem blockingFactor : Blocking.DimFourOddBlockingFactorGeThirteen 4 s.data.L :=
  ⟨rfl, s.data.isAdmissible.1, s.data.isAdmissible.2⟩
abbrev levelUnitData : GeneralTorus.ScaleData :=
  GeneralTorus.physicalInLevelUnits s.data.L s.blockingFactor s.data.m s.data.cutoff s.data.t
    s.data.t_le_cutoff s.data.blockExp s.data.gapExp
abbrev BlockSettingType : Type :=
  Dirichlet.BlockSetting 4 s.data.L (1 - s.Lreal ^ (-2 : ℤ)) 1 s.unitTorusSide
structure IsBlockSetting (𝒮 : s.BlockSettingType) : Prop where
  ξ_eq : 𝒮.ξ = s.mesh
  M_eq : 𝒮.M = s.data.blockSize
  R₁_eq : 𝒮.R₁ = s.data.gapSize
  t_eq : 𝒮.t = s.data.t
  Ω_eq : ∀ n, 𝒮.Ω n = s.regionOn s.unitTorusSide n
  a_eq : ∀ n ≤ s.data.t, 𝒮.a n = s.params.levelWeight n
structure IsWeightedTorus (D : Weighted.TorusData) (B : Weighted.SeparatedChain D) : Prop where
  L_eq : D.L = s.data.L
  blockNumber_eq : D.blockNumber = s.data.blockSize
  gapNumber_eq : D.gapNumber = s.data.gapSize
  bareSpacing_eq : D.bareSpacing = s.mesh
  top_eq : D.top = s.lastIdx
  side_eq : D.side = s.unitTorusSide
  stage_eq : ∀ n, B.stage n = s.regionOn D.side n
def InFrame {S : ℝ} {X : Type} (ends : X → Torus4 S × Torus4 S) (b : X) : Prop :=
  ∃ c ∈ s.data.frameSet s.Ω s.frame,
    (s.toTorus S (s.bondEnds c).1, s.toTorus S (s.bondEnds c).2) = ends b
structure IsNestedRegions (𝒮 : RegionSequence.NestedRegions) : Prop where
  L_eq : 𝒮.L = s.data.L
  ξ_eq : 𝒮.ξ = s.mesh
  side_eq : 𝒮.side = s.unitTorusSide
  s_eq : 𝒮.s = s.data.t
  Ω_eq : ∀ n, 𝒮.Ω n = s.regionOn 𝒮.side n
  bonds_iff : ∀ b : 𝒮.FineBond, b ∈ 𝒮.bonds ↔
    s.InFrame (fun b : 𝒮.FineBond => ((b.source : 𝒮.Point), (b.target : 𝒮.Point))) b
structure IsGaugeSetting (W : GeneralTorus.GaugeSetting) : Prop where
  data_eq : W.data = s.levelUnitData
  set_eq : ∀ n, W.chain.set n = s.regionOn W.data.torusSide n
  choice_eq : W.choice = bondSetChoice s.frame
  mass_eq : W.mass = 1
def scalarData : ScalarData s.data.Point where
  Site := s.data.BareSite
  pos x := (x : s.data.Point)
  space := (zeroFormsOn s.data.cutoff (s.Ω 0) : Submodule ℝ s.data.SiteFn)
  inner := latticeInner s.data.L s.data.t
  Coarse := ↥(s.params.allLayerPoints s.Ω)
  coarsePos y := y.1
  coarseInner := s.params.coarseZeroInner s.Ω
  avg := extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f => s.params.averageZero s.Ω f
  op := extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f => (s.params.massiveZeroOperator s.Ω f).1
  inv := extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f => (s.params.zeroGreen s.Ω f).1
def scalarDataOfBlockSetting {aMinus aPlus S : ℝ} {L : ℕ} (𝒮 : Dirichlet.BlockSetting 4 L aMinus aPlus S) :
    ScalarData (Torus4 S) where
  Site := Dirichlet.LatticeSite 4 S 𝒮.ξ
  pos x := (x : Torus4 S)
  space := {f | Dirichlet.VanishesOff (𝒮.Ω 0) f}
  inner := Dirichlet.innerSum
  Coarse := ↥𝒮.centres
  coarsePos y := y.1
  coarseInner ω ω' := ∑ᶠ y : ↥𝒮.centres, 𝒮.centreSpacing y.1 ^ 4 * ω y * ω' y
  avg f y := 𝒮.cellAverage f y.1
  op := 𝒮.fullOperator
  inv := 𝒮.fullGreen
def scalarDataOfWeighted {D : Weighted.TorusData} (B : Weighted.SeparatedChain D) :
    ScalarData D.Space where
  Site := D.BareSite
  pos x := (x : D.Space)
  space := B.bareSpace
  inner := B.bareInner
  Coarse := ↥B.allSites
  coarsePos y := y.1
  coarseInner := B.layerInner
  avg := extendByZero B.bareSpace fun f => B.avgOp f
  op := extendByZero B.bareSpace fun f => (B.weightedLap f).1
  inv := extendByZero B.bareSpace fun f => (B.greenOp f).1
def scalarDataOfNested (𝒮 : RegionSequence.NestedRegions) : ScalarData 𝒮.Point where
  Site := 𝒮.FineSite
  pos x := (x : 𝒮.Point)
  space := 𝒮.siteFns
  inner := Dirichlet.innerSum
  Coarse := ↥𝒮.allCentres
  coarsePos y := y.1
  coarseInner := RegionSequence.NestedRegions.coarseInner
  avg := RegionSequence.NestedRegions.blockAvg
  op := RegionSequence.NestedRegions.gaugeLap
  inv := RegionSequence.NestedRegions.gaugeGreenOp
def oneFormData : CoarseOneFormData s.data.Point where
  Bond := s.data.BareBond
  endpoints := s.bondEnds
  space := (oneFormsOn s.data.cutoff (s.Ω 0) s.frame : Submodule ℝ s.data.BondFn)
  inner := latticeInner s.data.L s.data.t
  WilsonWeightSeriesExpansion := ↥(s.params.principalBonds s.Ω s.frame)
  expansionPos c := (c.1.1, s.bondEnds c.1.2)
  avg := extendByZero (oneFormsOn s.data.cutoff (s.Ω 0) s.frame) fun A =>
    s.params.averageOne s.Ω s.frame A
  op := extendByZero (oneFormsOn s.data.cutoff (s.Ω 0) s.frame) fun A =>
    (s.params.massiveOneOperator s.Ω s.frame A).1
  inv := extendByZero (oneFormsOn s.data.cutoff (s.Ω 0) s.frame) fun A =>
    (s.params.oneGreen s.Ω s.frame A).1
abbrev NestedBond (𝒮 : RegionSequence.NestedRegions) : Type :=
  {c : Σ n : ℕ, 𝒮.BondAt n // c.1 ≤ 𝒮.s ∧ c.2 ∈ 𝒮.coarseBonds c.1}
def oneFormDataOfNested (𝒮 : RegionSequence.NestedRegions) : CoarseOneFormData 𝒮.Point where
  Bond := 𝒮.FineBond
  endpoints b := ((b.source : 𝒮.Point), (b.target : 𝒮.Point))
  space := 𝒮.oneForms
  inner := RegionSequence.NestedRegions.bondInner
  WilsonWeightSeriesExpansion := NestedBond 𝒮
  expansionPos c := (c.1.1, (c.1.2.source : 𝒮.Point), (c.1.2.target : 𝒮.Point))
  avg A c := RegionSequence.NestedRegions.bondAvg c.1.1 A c.1.2
  op := RegionSequence.NestedRegions.baseOp
  inv := RegionSequence.NestedRegions.baseGreen
def oneFormDataOfGauge (W : GeneralTorus.GaugeSetting) : CoarseOneFormData W.data.Space where
  Bond := W.data.BaseBond
  endpoints b := ((b.1.src : W.data.Space), (b.1.tgt : W.data.Space))
  space := W.formSubspace
  inner := W.data.bondInner
  WilsonWeightSeriesExpansion := W.CoarseBond
  expansionPos c := (GeneralTorus.GaugeSetting.coarseLevel c, GeneralTorus.GaugeSetting.coarseSrc c,
    GeneralTorus.GaugeSetting.coarseTgt c)
  avg := extendByZero W.formSubspace fun A => W.meanOp A
  op := extendByZero W.formSubspace fun A => (W.gaugeLap A).1
  inv := extendByZero W.formSubspace fun A => (W.greenOp A).1
section Geometry
variable {S : ℝ}
def SublatticesMatch (N : ℕ) (lat : ℕ → Set (Torus4 S)) : Prop :=
  ∀ n ≤ N, s.toTorus S '' (PeriodicLattice.sublattice s.data.L s.data.m
    (PeriodicLattice.levelDepth s.data.cutoff n) : Set s.data.Point) = lat n
def PartitionsMatch (N : ℕ) (par : ℕ → Set (Set (Torus4 S))) : Prop :=
  ∀ n ≤ N, (fun Q => s.toTorus S '' Q) ''
    PeriodicLattice.standardCubePartition s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) = par n
def BlockPartitionsMatch (N : ℕ) (par : ℕ → Set (Set (Torus4 S))) : Prop :=
  ∀ n ≤ N, (fun Q => s.toTorus S '' Q) ''
    PeriodicLattice.standardCubePartition s.data.L s.data.m (s.data.scales.blockPartitionIndex n) = par n
def LayersMatch (lay : ℕ → Set (Torus4 S)) : Prop :=
  ∀ n, s.toTorus S '' s.data.layerAt s.Ω n = lay n
def LayerSitesMatch (sites : ℕ → Set (Torus4 S)) : Prop :=
  ∀ n ≤ s.data.t,
    (fun y : s.data.LatticeSite n => s.toTorus S (y : s.data.Point)) '' s.data.layerSitesAt s.Ω n = sites n
def AllLayerSitesMatch (sites : Set (Torus4 S)) : Prop :=
  s.toTorus S '' s.data.layerPts s.Ω = sites
def MeshesMatch (ξ' : Torus4 S → ℝ) : Prop :=
  ∀ y : s.data.Apex s.Ω, ξ' (s.toTorus S y.point) = y.mesh
def BlocksMatch (cube : Torus4 S → Set (Torus4 S)) : Prop :=
  ∀ y : s.data.Apex s.Ω, cube (s.toTorus S y.point) = s.toTorus S '' y.block
def DoubledBlocksMatch (cube : Torus4 S → Set (Torus4 S)) : Prop :=
  ∀ y : s.data.Apex s.Ω, cube (s.toTorus S y.point) = s.toTorus S '' y.doubledBlock
def LengthsMatch {G : Type} (g : LiftedSegment → G) (w : List G → ℝ) : Prop :=
  ∀ Γ : List LiftedSegment, w (Γ.map g) = s.data.chainLength s.Ω Γ
def DistancesMatch (d : Torus4 S → Torus4 S → ℝ) : Prop :=
  ∀ y y' : s.data.Point,
    ENNReal.ofReal (d (s.toTorus S y) (s.toTorus S y')) = s.data.chainDist s.Ω y y'
end Geometry
structure BlockSettingGeometry (𝒮 : s.BlockSettingType) : Prop where
  sublattices : s.SublatticesMatch s.lastIdx fun n =>
    (Torus.spacingLattice 4 s.unitTorusSide (𝒮.scaleAt n) : Set (Torus.PeriodicTorus 4 s.unitTorusSide))
  partitions : s.PartitionsMatch s.lastIdx fun n =>
    Torus.cubePartition 4 s.unitTorusSide (𝒮.scaleAt n)
  blockPartitions : s.BlockPartitionsMatch s.lastIdx fun n =>
    Torus.cubePartition 4 s.unitTorusSide ((𝒮.M : ℝ) * 𝒮.scaleAt n)
  layers : s.LayersMatch fun n => Torus.shell 𝒮.Ω n
  layerSites : s.LayerSitesMatch fun n => Torus.shellSites s.data.L 𝒮.ξ 𝒮.Ω n
  allLayerSites : s.AllLayerSitesMatch 𝒮.centres
  meshes : s.MeshesMatch 𝒮.centreSpacing
  blocks : s.BlocksMatch 𝒮.cell
  doubledBlocks : s.DoubledBlocksMatch (Torus.doubledSiteCube s.data.L 𝒮.ξ 𝒮.Ω)
  lengths : s.LengthsMatch s.scaleSegmentDir
    (Torus.chainWeightedLength s.data.L 𝒮.ξ 𝒮.t 𝒮.Ω)
  distances : s.DistancesMatch 𝒮.blockDist
structure WeightedGeometry {D : Weighted.TorusData} (B : Weighted.SeparatedChain D) : Prop where
  sublattices : s.SublatticesMatch s.lastIdx fun n => D.latticeAt (D.scale n)
  partitions : s.PartitionsMatch s.lastIdx fun n => D.partitionAt (D.scale n)
  blockPartitions : s.BlockPartitionsMatch s.lastIdx fun n =>
    D.partitionAt ((D.blockNumber : ℝ) * D.scale n)
  layers : s.LayersMatch B.layer
  layerSites : s.LayerSitesMatch B.layerSites
  allLayerSites : s.AllLayerSitesMatch B.allSites
  meshes : s.MeshesMatch B.siteScale
  blocks : s.BlocksMatch B.siteCube
  lengths : s.LengthsMatch s.scaleSegment B.weightedLength
  distances : s.DistancesMatch B.weightedDistance
structure NestedGeometry (𝒮 : RegionSequence.NestedRegions) : Prop where
  sublattices : s.SublatticesMatch s.data.t fun n =>
    (Torus.spacingLattice 4 𝒮.side (𝒮.scale n) : Set (Torus.PeriodicTorus 4 𝒮.side))
  partitions : s.PartitionsMatch s.data.t fun n =>
    Torus.cubePartition 4 𝒮.side (𝒮.scale n)
  layers : s.LayersMatch 𝒮.shellOf
  layerSites : s.LayerSitesMatch 𝒮.centresAt
  allLayerSites : s.AllLayerSitesMatch 𝒮.allCentres
  meshes : s.MeshesMatch 𝒮.levelScale
  blocks : s.BlocksMatch 𝒮.cellOf
structure GaugeGeometry (W : GeneralTorus.GaugeSetting) : Prop where
  sublattices : s.SublatticesMatch s.data.t fun n => (W.data.levelSublattice n : Set W.data.Space)
  partitions : s.PartitionsMatch s.data.t fun n => W.data.cubePartition (W.data.levelSpacing n)
  blockPartitions : s.BlockPartitionsMatch s.lastIdx W.data.blockPartition
  layers : s.LayersMatch W.chain.shell
  layerSites : s.LayerSitesMatch W.chain.shellSites
  allLayerSites : s.AllLayerSitesMatch W.chain.shellSitesUnion
  meshes : s.MeshesMatch W.chain.localSpacing
  blocks : s.BlocksMatch W.chain.localCube
  doubledBlocks : s.DoubledBlocksMatch W.chain.localDoubleCube
  lengths : s.LengthsMatch s.scaleSegment W.chain.scaledLength
  distances : s.DistancesMatch W.chain.scaledDist
structure WeightsAtUnitMass : Prop where
  zero : s.params.levelWeight 0 = 1
  formula : ∀ n : ℕ, 1 ≤ n →
    s.params.levelWeight n = (1 - s.Lreal ^ (-2 : ℤ)) / (1 - s.Lreal ^ (-(2 * (n : ℤ))))
  one : s.params.levelWeight 1 = 1
  succ : ∀ n : ℕ, 1 ≤ n →
    s.params.levelWeight (n + 1) = s.params.levelWeight n / (s.Lreal ^ (-2 : ℤ) + s.params.levelWeight n)
  bounds : ∀ n, 1 - s.Lreal ^ (-2 : ℤ) ≤ s.params.levelWeight n ∧ s.params.levelWeight n ≤ 1
def greenSquare : (↥(s.params.allLayerPoints s.Ω) → ℝ) → ↥(s.params.allLayerPoints s.Ω) → ℝ :=
  s.params.averagedZeroGreenSq s.Ω
def greenSquareInv :
    (↥(s.params.allLayerPoints s.Ω) → ℝ) → ↥(s.params.allLayerPoints s.Ω) → ℝ :=
  ⇑(Ring.inverse (s.params.averagedZeroGreenSq s.Ω) : Module.End ℝ (s.params.CoarseZeroForms s.Ω))
def rangeProj : s.data.SiteFn → s.data.SiteFn :=
  extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f => (s.params.gaugeRangeProjection s.Ω f).1
def complProj : s.data.SiteFn → s.data.SiteFn :=
  extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0)) fun f => (s.params.gaugeComplementProjection s.Ω f).1
def greenSquareOfNested (𝒮 : RegionSequence.NestedRegions) (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  RegionSequence.NestedRegions.blockAvg (RegionSequence.NestedRegions.gaugeGreenOp
    (RegionSequence.NestedRegions.gaugeGreenOp (RegionSequence.NestedRegions.blockAvgAdj ω)))
structure WeightedProjections {D : Weighted.TorusData} (B : Weighted.SeparatedChain D) : Prop where
  square : OperatorsCorrespond (s.scalarData.CoarseRel (scalarDataOfWeighted B) (s.toTorus D.side))
    (s.scalarData.CoarseRel (scalarDataOfWeighted B) (s.toTorus D.side)) univ univ
    s.greenSquare B.avgGreenSq
  squareInv : OperatorsCorrespond (s.scalarData.CoarseRel (scalarDataOfWeighted B) (s.toTorus D.side))
    (s.scalarData.CoarseRel (scalarDataOfWeighted B) (s.toTorus D.side)) univ univ
    s.greenSquareInv ⇑(Ring.inverse B.avgGreenSq : Module.End ℝ B.LayerFn)
  range : OperatorsCorrespond (s.scalarData.SiteRel (scalarDataOfWeighted B) (s.toTorus D.side))
    (s.scalarData.SiteRel (scalarDataOfWeighted B) (s.toTorus D.side))
    s.scalarData.space (scalarDataOfWeighted B).space s.rangeProj
    (extendByZero B.bareSpace fun f => (B.complProj f).1)
  compl : OperatorsCorrespond (s.scalarData.SiteRel (scalarDataOfWeighted B) (s.toTorus D.side))
    (s.scalarData.SiteRel (scalarDataOfWeighted B) (s.toTorus D.side))
    s.scalarData.space (scalarDataOfWeighted B).space s.complProj
    (extendByZero B.bareSpace fun f => (B.avgProj f).1)
structure NestedProjections (𝒮 : RegionSequence.NestedRegions) : Prop where
  square : OperatorsCorrespond (s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side))
    (s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)) univ univ
    s.greenSquare (greenSquareOfNested 𝒮)
  squareInv : OperatorsCorrespond (s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side))
    (s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)) univ univ
    s.greenSquareInv
    (RegionSequence.inverseValue univ (greenSquareOfNested 𝒮))
  range : OperatorsCorrespond (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side))
    (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side))
    s.scalarData.space (scalarDataOfNested 𝒮).space s.rangeProj
    RegionSequence.NestedRegions.rangeProj
  compl : OperatorsCorrespond (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side))
    (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side))
    s.scalarData.space (scalarDataOfNested 𝒮).space s.complProj
    RegionSequence.NestedRegions.complProj
def GaugeSiteRel (W : GeneralTorus.GaugeSetting) (x : s.data.BareSite) (x' : W.data.BaseSite) : Prop :=
  s.toTorus W.data.torusSide (x : s.data.Point) = (x' : W.data.Space)
structure GaugeProjection (W : GeneralTorus.GaugeSetting) : Prop where
  sites : PairsUniquely (s.GaugeSiteRel W)
  space : SpacesCorrespond (s.GaugeSiteRel W) s.scalarData.space W.chain.dirichletSites
  range : OperatorsCorrespond (s.GaugeSiteRel W) (s.GaugeSiteRel W) s.scalarData.space
    W.chain.dirichletSites s.rangeProj
    (extendByZero W.chain.dirichletSites fun f => (W.chain.lapImageProj f).1)
def classOneForms : OneFormData s.data.Point where
  Bond := s.data.BareBond
  endpoints := s.bondEnds
  space := s.data.forms s.Ω s.frame
  inner := s.data.bondInner
abbrev coarseAvg := s.oneFormData.avg
def NestedMassForm (𝒮 : RegionSequence.NestedRegions) : Prop :=
  ∀ A ∈ s.oneFormData.space, ∀ A' ∈ s.oneFormData.space,
    ∀ B ∈ (oneFormDataOfNested 𝒮).space, ∀ B' ∈ (oneFormDataOfNested 𝒮).space,
    AgreeAlong (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)) A B →
    AgreeAlong (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)) A' B' →
    RegionSequence.NestedRegions.avgForm B B' =
      s.params.coarseOneInner s.Ω s.frame (s.coarseAvg A)
        (s.params.weightMulOne s.Ω s.frame (s.coarseAvg A'))
structure GaugeCoarseOperators (W : GeneralTorus.GaugeSetting) : Prop where
  inner : PairingsCorrespond (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)) univ univ
    (s.params.coarseOneInner s.Ω s.frame) W.coarseInner
  mass : OperatorsCorrespond (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide))
    (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)) univ univ
    (s.params.weightMulOne s.Ω s.frame) W.massMul
  green : OperatorsCorrespond (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide))
    (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)) univ univ
    (s.params.averagedOneGreen s.Ω s.frame) W.coarseGreen
  greenInv : OperatorsCorrespond (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide))
    (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)) univ univ
    ⇑(Ring.inverse (s.params.averagedOneGreen s.Ω s.frame) :
      Module.End ℝ (s.params.CoarseOneForms s.Ω s.frame))
    ⇑(Ring.inverse W.coarseGreen : Module.End ℝ W.CoarseField)
  ext : OperatorsCorrespond (s.oneFormData.RowRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide))
    (s.oneFormData.BondRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)) univ univ
    (fun B => (s.params.oneExtension s.Ω s.frame B).1) (fun B => (W.harmonicExt B).1)
structure NestedAnchors (𝒮 : RegionSequence.NestedRegions) : Prop where
  anchor : ∀ b b', s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side) b b' →
    s.toTorus 𝒮.side (ClassData.anchorSite s.Ω b : s.data.Point) = (𝒮.anchor b' : 𝒮.Point)
  bondIn : ∀ (X : Set s.data.Point) b b',
    s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side) b b' →
    (ClassData.BondAnchoredIn s.Ω X b ↔ RegionSequence.NestedRegions.AnchoredIn (s.toTorus 𝒮.side '' X) b')
  supportedIn : ∀ (X : Set s.data.Point), ∀ A ∈ s.oneFormData.space, ∀ A' ∈ 𝒮.oneForms,
    AgreeAlong (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)) A A' →
    (ClassData.AnchorSupportedIn s.Ω X A ↔
      RegionSequence.NestedRegions.AnchorSupported (s.toTorus 𝒮.side '' X) A')
structure GaugeAnchors (W : GeneralTorus.GaugeSetting) : Prop where
  anchor : ∀ b ∈ s.data.frameSet s.Ω s.frame, ∀ b',
    s.oneFormData.BondRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide) b b' →
    s.toTorus W.data.torusSide (ClassData.anchorSite s.Ω b : s.data.Point) =
      (W.chain.anchor b' : W.data.Space)
  bondIn : ∀ y : s.data.Apex s.Ω, ∀ b ∈ s.data.frameSet s.Ω s.frame, ∀ b',
    s.oneFormData.BondRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide) b b' →
    (ClassData.BondAnchoredIn s.Ω y.block b ↔ W.chain.LiesInCell b' (s.toTorus W.data.torusSide y.point))
  supportedIn : ∀ y : s.data.Apex s.Ω, ∀ A ∈ s.oneFormData.space, ∀ A' ∈ W.formSubspace,
    AgreeAlong (s.oneFormData.BondRel (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)) A A' →
    (ClassData.AnchorSupportedIn s.Ω y.block A ↔ W.SupportedInCell A' (s.toTorus W.data.torusSide y.point))
end SequenceData
def torusGreenConstants (c : Propagator.PropagatorConstants) : GeneralTorus.GreenBounds.GreenConstants :=
  ⟨c.δ, c.B, c.blockLower, c.gapLower, c.Bα⟩
end SingleSequence
end SeparatedClasses
end YangMills.Construction
