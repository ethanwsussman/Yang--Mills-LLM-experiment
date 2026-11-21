import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.PivotBondOfABondOfEitherOrientationAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
structure TransportsFunctionsOn {X Y : Type} (e : X ≃ Y) (S : Set X) : Prop where
  injOn : InjOn e S
  existsUnique : ∀ (V : Type) (f : S → V), ∃! g : e '' S → V, ∀ σ : S, g (e.image S σ) = f σ
  bijective : ∀ V : Type, Function.Bijective (transportFun e S : (S → V) → (e '' S → V))
def IsCongruentMod (s : ℝ) (x y : Fin 4 → ℝ) : Prop :=
  ∃ a : Fin 4 → ℤ, ∀ μ, x μ - y μ = s * (a μ : ℝ)
structure SpaceScalingProperties (L k j : ℕ) : Prop where
  bijective : Function.Bijective fun x : Fin 4 → ℝ => (L : ℝ) ^ (k - j) • x
  map_add : ∀ x y : Fin 4 → ℝ,
    (L : ℝ) ^ (k - j) • (x + y) = (L : ℝ) ^ (k - j) • x + (L : ℝ) ^ (k - j) • y
structure ScaledTowerMesh (L k j i : ℕ) : Prop where
  meshAt_eq : meshAt L j i = (L : ℝ) ^ ((i : ℤ) - (j : ℤ))
  eq_mul : (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) = (L : ℝ) ^ (k - j) * meshAt L k i
section Periodic
variable {L k j : ℕ}
def cornerList {m : ℕ} {d : ℤ} (p : PeriodicLattice.Plaquette L m d) :
    List (PeriodicLattice.Site L m d) :=
  [p.origin, p.origin + PeriodicLattice.unitStep L m d p.firstAxis,
    p.origin + PeriodicLattice.unitStep L m d p.firstAxis +
      PeriodicLattice.unitStep L m d p.secondAxis,
    p.origin + PeriodicLattice.unitStep L m d p.secondAxis]
structure ScalingAtLevel (hL : 0 < L) (hj : j ≤ k) (n i : ℕ) : Prop where
  image_sublattice : scaling hL n k j ''
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)) =
    (PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j i) :
      Set (PeriodicLattice.FourTorus L (scaledExponent n k j)))
  injOn_sublattice : InjOn (scaling hL n k j)
    (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
      Set (PeriodicLattice.FourTorus L n))
  sub_eq_step_iff : ∀ (x y : Vertex L n k i) (μ : Fin 4) (c : ℤ),
    y - x = c • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ ↔
      scaleVertex hL hj i y - scaleVertex hL hj i x =
        c • PeriodicLattice.unitStep L (scaledExponent n k j) (PeriodicLattice.levelDepth j i) μ
  edge_source : ∀ b : Edge L n k i,
    (scaleEdge hL hj i b).source = scaleVertex hL hj i b.source
  edge_target : ∀ b : Edge L n k i,
    (scaleEdge hL hj i b).target = scaleVertex hL hj i b.target
  edge_bijective : Function.Bijective (scaleEdge (n := n) hL hj i)
  edge_axis : ∀ b : Edge L n k i, (scaleEdge hL hj i b).axis = b.axis
  image_positive : scaleEdge (n := n) hL hj i '' {b | b.IsPositivelyOriented} =
    {b | b.IsPositivelyOriented}
  edge_opposite : ∀ b : Edge L n k i,
    scaleEdge hL hj i b.opposite = (scaleEdge hL hj i b).opposite
  image_paths : scalePath (n := n) hL hj i '' {γ | PeriodicLattice.IsBondPath γ} =
    {γ | PeriodicLattice.IsBondPath γ}
  injOn_paths : InjOn (scalePath (n := n) hL hj i) {γ | PeriodicLattice.IsBondPath γ}
  axial_condition : ∀ c : ℤ,
    ((|c| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n / 2 ↔
      ((|c| : ℤ) : ℝ) * (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) <
        (L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n / 2
  axialPath : ∀ (x y : Vertex L n k i) (μ : Fin 4) (c : ℤ),
    y = x + c • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ →
      ((|c| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n / 2 →
      scalePath hL hj i (PeriodicLattice.axialPath x y) =
        PeriodicLattice.axialPath (scaleVertex hL hj i x) (scaleVertex hL hj i y)
  face_origin : ∀ p : Face L n k i,
    (scaleFace hL hj i p).origin = scaleVertex hL hj i p.origin ∧
      (scaleFace hL hj i p).firstAxis = p.firstAxis ∧
      (scaleFace hL hj i p).secondAxis = p.secondAxis
  corners : ∀ p : Face L n k i,
    (cornerList p).map (scaleVertex hL hj i) = cornerList (scaleFace hL hj i p)
  image_face : ∀ p : Face L n k i,
    scaling hL n k j '' p.face = (scaleFace hL hj i p).face
  face_determined : ∀ p q : Face L n k i, p.face = q.face →
    (scaleFace hL hj i p).face = (scaleFace hL hj i q).face
  face_bijective : Function.Bijective (scaleFace (n := n) hL hj i)
structure ScalingTransportsFunctions (hL : 0 < L) (hj : j ≤ k) (n : ℕ) : Prop where
  points : ∀ S : Set (PeriodicLattice.FourTorus L n),
    (∀ x ∈ S, ∃ i ≤ j, x ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)) →
      TransportsFunctionsOn (scaling hL n k j).toEquiv S
  pointPairs : ∀ S : Set (PeriodicLattice.FourTorus L n × PeriodicLattice.FourTorus L n),
    (∀ c ∈ S, (∃ i ≤ j, c.1 ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)) ∧
      ∃ i ≤ j, c.2 ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)) →
      TransportsFunctionsOn
        ((scaling hL n k j).toEquiv.prodCongr (scaling hL n k j).toEquiv) S
  vertices : ∀ i ≤ j, ∀ S : Set (Vertex L n k i),
    TransportsFunctionsOn (scaleVertex hL hj i).toEquiv S
  vertexPairs : ∀ i ≤ j, ∀ i' ≤ j, ∀ S : Set (Vertex L n k i × Vertex L n k i'),
    TransportsFunctionsOn (scaleVertexPair hL hj i i') S
  edges : ∀ i ≤ j, ∀ S : Set (Edge L n k i),
    TransportsFunctionsOn (scaleEdge hL hj i) S
  faces : ∀ i ≤ j, ∀ S : Set (Face L n k i),
    TransportsFunctionsOn (scaleFace hL hj i) S
  edgesAllLevels : ∀ S : Set (Σ i : Fin (j + 1), Edge L n k i),
    TransportsFunctionsOn (scaleEdges hL hj) S
  facesAllLevels : ∀ S : Set (Σ i : Fin (j + 1), Face L n k i),
    TransportsFunctionsOn (scaleFaces hL hj) S
structure ScalingOnTorus (hL : 0 < L) (hj : j ≤ k) (n : ℕ) : Prop where
  side_mem : (L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n ∈ sideSet L
  side_eq : (L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n =
    PeriodicLattice.torusSide L (scaledExponent n k j)
  sublattice_eq : ∀ i ≤ j,
    (PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j i) :
        Set (PeriodicLattice.FourTorus L (scaledExponent n k j))) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) ''
        {v | ∃ a : Fin 4 → ℤ, ∀ μ, v μ = (a μ : ℝ) * (L : ℝ) ^ ((i : ℤ) - (j : ℤ))}
  mesh : ∀ i ≤ j, PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i) = meshAt L j i ∧
    ScaledTowerMesh L k j i
  spaceScaling : SpaceScalingProperties L k j
  congruent_iff : ∀ x y : Fin 4 → ℝ, IsCongruentMod (PeriodicLattice.torusSide L n) x y ↔
    IsCongruentMod ((L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n)
      ((L : ℝ) ^ (k - j) • x) ((L : ℝ) ^ (k - j) • y)
  eq_scaling_iff : ∀ φ : PeriodicLattice.FourTorus L n →
      PeriodicLattice.FourTorus L (scaledExponent n k j),
    (∀ x : Fin 4 → ℝ, φ (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j))
        ((L : ℝ) ^ (k - j) • x)) ↔
      φ = scaling hL n k j
  bijective : Function.Bijective (scaling hL n k j)
  map_add : ∀ a b : PeriodicLattice.FourTorus L n,
    scaling hL n k j (a + b) = scaling hL n k j a + scaling hL n k j b
  map_add_proj : ∀ i ≤ j, ∀ (x : PeriodicLattice.FourTorus L n) (w : Fin 4 → ℝ),
    scaling hL n k j (x + TorusMetric.torusProj (PeriodicLattice.torusSide L n) (meshAt L k i • w)) =
      scaling hL n k j x +
        TorusMetric.torusProj (PeriodicLattice.torusSide L (scaledExponent n k j))
          ((L : ℝ) ^ ((i : ℤ) - (j : ℤ)) • w)
  dist_eq : ∀ a b : PeriodicLattice.FourTorus L n,
    TorusMetric.torusEuclidNorm (scaling hL n k j a - scaling hL n k j b) =
      (L : ℝ) ^ (k - j) * TorusMetric.torusEuclidNorm (a - b)
  atLevel : ∀ i ≤ j, ScalingAtLevel hL hj n i
  distancePreserving_iff : ∀ s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
    IsDistancePreserving (conjMap (scaling hL n k j).toEquiv s) ↔ IsDistancePreserving s
  mapsSublatticeOnto_iff : ∀ i ≤ j,
    ∀ s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv s) ↔ MapsSublatticeOnto k i s
  existsUnique_map : ∀ t : PeriodicLattice.FourTorus L (scaledExponent n k j) →
      PeriodicLattice.FourTorus L (scaledExponent n k j),
    ∃! s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      t = conjMap (scaling hL n k j).toEquiv s
  transports : ScalingTransportsFunctions hL hj n
end Periodic
namespace FullSpace
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable {L k j : ℕ}
def cornerList {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) :
    List (InfiniteLattice.LatticePoint a) :=
  [p.corner, p.corner + InfiniteLattice.axisStep a p.lowAxis,
    p.corner + InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis,
    p.corner + InfiniteLattice.axisStep a p.highAxis]
def closedFace {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) : Set AmbientSpace :=
  {q | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
    q = (p.corner : AmbientSpace) + Pi.single p.lowAxis (s * a) + Pi.single p.highAxis (t * a)}
structure ScalingAtLevel (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop where
  image_sublattice : scaling hL k j ''
      (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) =
    (InfiniteLattice.latticeSubgroup (meshAt L j i) : Set AmbientSpace)
  injOn_sublattice : InjOn (scaling hL k j)
    (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace)
  sub_eq_step_iff : ∀ (x y : Vertex L k i) (μ : Fin 4) (c : ℤ),
    y - x = c • InfiniteLattice.axisStep (meshAt L k i) μ ↔
      scaleVertex hL hj i y - scaleVertex hL hj i x =
        c • InfiniteLattice.axisStep (meshAt L j i) μ
  edge_initial : ∀ b : Edge L k i,
    (scaleEdge hL hj i b).initial = scaleVertex hL hj i b.initial
  edge_terminal : ∀ b : Edge L k i,
    (scaleEdge hL hj i b).terminal = scaleVertex hL hj i b.terminal
  edge_bijective : Function.Bijective (scaleEdge hL hj i)
  edge_axis : ∀ (b : Edge L k i) (μ : Fin 4),
    LinkHasAxis (scaleEdge hL hj i b) μ ↔ LinkHasAxis b μ
  image_positive : scaleEdge hL hj i '' {b | b.IsPositivelyOriented} =
    {b | b.IsPositivelyOriented}
  edge_opposite : ∀ b : Edge L k i,
    scaleEdge hL hj i b.opposite = (scaleEdge hL hj i b).opposite
  image_paths : scalePath hL hj i '' {γ | IsLinkPath γ} = {γ | IsLinkPath γ}
  injOn_paths : InjOn (scalePath hL hj i) {γ | IsLinkPath γ}
  axisPath : ∀ (x y : Vertex L k i) (μ : Fin 4) (c : ℤ),
    y = x + c • InfiniteLattice.axisStep (meshAt L k i) μ →
      scalePath hL hj i (FullSpace.axisPath x y) =
        FullSpace.axisPath (scaleVertex hL hj i x) (scaleVertex hL hj i y)
  face_corner : ∀ p : Face L k i,
    (scaleFace hL hj i p).corner = scaleVertex hL hj i p.corner ∧
      (scaleFace hL hj i p).lowAxis = p.lowAxis ∧
      (scaleFace hL hj i p).highAxis = p.highAxis
  corners : ∀ p : Face L k i,
    (cornerList p).map (scaleVertex hL hj i) = cornerList (scaleFace hL hj i p)
  image_closedFace : ∀ p : Face L k i,
    scaling hL k j '' closedFace p = closedFace (scaleFace hL hj i p)
  closedFace_determined : ∀ p q : Face L k i, closedFace p = closedFace q →
    closedFace (scaleFace hL hj i p) = closedFace (scaleFace hL hj i q)
  face_bijective : Function.Bijective (scaleFace hL hj i)
structure ScalingTransportsFunctions (hL : 0 < L) (hj : j ≤ k) : Prop where
  points : ∀ S : Set AmbientSpace,
    (∀ x ∈ S, ∃ i ≤ j, x ∈ InfiniteLattice.latticeSubgroup (meshAt L k i)) →
      TransportsFunctionsOn (scaling hL k j).toEquiv S
  pointPairs : ∀ S : Set (AmbientSpace × AmbientSpace),
    (∀ c ∈ S, (∃ i ≤ j, c.1 ∈ InfiniteLattice.latticeSubgroup (meshAt L k i)) ∧
      ∃ i ≤ j, c.2 ∈ InfiniteLattice.latticeSubgroup (meshAt L k i)) →
      TransportsFunctionsOn ((scaling hL k j).toEquiv.prodCongr (scaling hL k j).toEquiv) S
  vertices : ∀ i ≤ j, ∀ S : Set (Vertex L k i),
    TransportsFunctionsOn (scaleVertex hL hj i).toEquiv S
  vertexPairs : ∀ i ≤ j, ∀ i' ≤ j, ∀ S : Set (Vertex L k i × Vertex L k i'),
    TransportsFunctionsOn (scaleVertexPair hL hj i i') S
  edges : ∀ i ≤ j, ∀ S : Set (Edge L k i),
    TransportsFunctionsOn (scaleEdge hL hj i) S
  faces : ∀ i ≤ j, ∀ S : Set (Face L k i),
    TransportsFunctionsOn (scaleFace hL hj i) S
  edgesAllLevels : ∀ S : Set (Σ i : Fin (j + 1), Edge L k i),
    TransportsFunctionsOn (scaleEdges hL hj) S
  facesAllLevels : ∀ S : Set (Σ i : Fin (j + 1), Face L k i),
    TransportsFunctionsOn (scaleFaces hL hj) S
structure ScalingOnSpace (hL : 0 < L) (hj : j ≤ k) : Prop where
  sublattice_eq : ∀ i ≤ j,
    (InfiniteLattice.latticeSubgroup (meshAt L j i) : Set AmbientSpace) =
      {v | ∃ a : Fin 4 → ℤ, ∀ μ, v μ = (a μ : ℝ) * (L : ℝ) ^ ((i : ℤ) - (j : ℤ))}
  mesh : ∀ i ≤ j, ScaledTowerMesh L k j i
  spaceScaling : SpaceScalingProperties L k j
  scaling_apply : ∀ x : AmbientSpace, scaling hL k j x = (L : ℝ) ^ (k - j) • x
  bijective : Function.Bijective (scaling hL k j)
  map_add : ∀ a b : AmbientSpace,
    scaling hL k j (a + b) = scaling hL k j a + scaling hL k j b
  map_add_smul : ∀ i ≤ j, ∀ x w : AmbientSpace,
    scaling hL k j (x + meshAt L k i • w) =
      scaling hL k j x + (L : ℝ) ^ ((i : ℤ) - (j : ℤ)) • w
  dist_eq : ∀ a b : AmbientSpace,
    TorusMetric.euclidNormVec (scaling hL k j a - scaling hL k j b) =
      (L : ℝ) ^ (k - j) * TorusMetric.euclidNormVec (a - b)
  atLevel : ∀ i ≤ j, ScalingAtLevel hL hj i
  distancePreserving_iff : ∀ s : AmbientSpace → AmbientSpace,
    IsDistancePreserving (conjMap (scaling hL k j).toEquiv s) ↔ IsDistancePreserving s
  mapsSublatticeOnto_iff : ∀ i ≤ j, ∀ s : AmbientSpace → AmbientSpace,
    MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv s) ↔
      MapsSublatticeOnto (meshAt L k i) s
  existsUnique_map : ∀ t : AmbientSpace → AmbientSpace,
    ∃! s : AmbientSpace → AmbientSpace, t = conjMap (scaling hL k j).toEquiv s
  transports : ScalingTransportsFunctions hL hj
end FullSpace
def ScalingPropertiesStatement : Prop :=
  ∀ (L k j : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k),
    (∀ n : ℕ, 0 < n →
      ScalingOnTorus (Nat.lt_of_lt_of_le (by norm_num) hL.2) hj n) ∧
    FullSpace.ScalingOnSpace (Nat.lt_of_lt_of_le (by norm_num) hL.2) hj
end Tower
end YangMills.Construction
end
