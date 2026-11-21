import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open InfiniteLattice (AmbientSpace)
def coordPlane (μ : Fin 4) (c : ℝ) : Set AmbientSpace := {x | x μ = c}
def coordPlaneReflection (μ : Fin 4) (c : ℝ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - c)) • stdBasis μ
def GluingSetup.halfIntegerMeshPoints (S : GluingSetup) : Set ℝ :=
  {c | ∃ i : ℤ, c = S.mesh * ((i : ℝ) + 1 / 2)}
def GluingSetup.MirrorWallsAndLinks (S : GluingSetup) : Prop :=
  (∀ G : CubicGrid S, G.IsMirrorGrid → ∀ W ∈ G.walls,
    ∃ μ : Fin 4, ∃ c ∈ S.halfIntegerMeshPoints, W = coordPlane μ c) ∧
  (∀ (μ : Fin 4), ∀ c ∈ S.halfIntegerMeshPoints, ∀ e : InfiniteLattice.Link S.mesh,
    (segment ℝ (e.initial : AmbientSpace) (e.terminal : AmbientSpace) ∩ coordPlane μ c).Nonempty →
      ((e.terminal : AmbientSpace) - (e.initial : AmbientSpace) = S.mesh • stdBasis μ ∨
        (e.terminal : AmbientSpace) - (e.initial : AmbientSpace) = -(S.mesh • stdBasis μ)) ∧
      segment ℝ (e.initial : AmbientSpace) (e.terminal : AmbientSpace) ∩ coordPlane μ c =
        {midpoint ℝ (e.initial : AmbientSpace) (e.terminal : AmbientSpace)}) ∧
  ∀ (μ : Fin 4) (c : ℝ),
    (Disjoint (coordPlane μ c) (S.gridPoints : Set AmbientSpace) ∧
      coordPlaneReflection μ c '' (S.gridPoints : Set AmbientSpace) =
        (S.gridPoints : Set AmbientSpace)) ↔
      c ∈ S.halfIntegerMeshPoints
namespace CubicGrid
variable {S : GluingSetup} (G : CubicGrid S)
def cubesPerSide : ℕ := ⌊S.cellCount G.edge⌋₊
def cubeCenter (k : Fin 4 → ℤ) : AmbientSpace :=
  fun μ => G.origin μ + G.edge * ((k μ : ℝ) + 1 / 2)
def affineReflection (σ : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (x : AmbientSpace) : AmbientSpace :=
  fun μ => (((σ μ : ℤˣ) : ℤ) : ℝ) * (x μ - G.mirrorOrigin μ) + G.mirrorOrigin μ +
    2 * (n μ : ℝ) * G.edge
def descendedReflection (σ : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) : S.Torus → S.Torus :=
  TorusLifts.descendedMap (PeriodicLattice.torusSide S.L S.m) (PeriodicLattice.torusSide S.L S.m)
    (G.affineReflection σ n)
def mirrorTorusCubes : Set (Set S.Torus) := range G.toMirror.torusCube
def CubesAndPeriods (j : ℤ) : Prop :=
  G.edge / S.mesh = (S.L : ℝ) ^ (((S.K : ℕ) : ℤ) + j) ∧
  (∃ N : ℕ, 0 < N ∧ G.edge / S.mesh = N) ∧
  S.cellCount G.edge = 2 * (S.L : ℝ) ^ (((S.m : ℕ) : ℤ) - j) ∧
  (G.cubesPerSide : ℝ) = S.cellCount G.edge ∧
  0 < G.cubesPerSide ∧
  Even G.cubesPerSide ∧
  (∀ W ∈ G.walls, Disjoint W (S.gridPoints : Set AmbientSpace)) ∧
  (∀ t k : Fin 4 → ℤ,
    (fun x => x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide S.L S.m) t) '' G.cube k =
      G.cube (k + (G.cubesPerSide : ℤ) • t)) ∧
  (∀ t : Fin 4 → ℤ,
    image (image fun x => x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide S.L S.m) t)
      G.walls = G.walls) ∧
  (∀ k k' : Fin 4 → ℤ,
    G.torusCube k = G.torusCube k' ↔ ∃ t : Fin 4 → ℤ, k - k' = (G.cubesPerSide : ℤ) • t) ∧
  (∃ e : (Fin 4 → ZMod G.cubesPerSide) ≃ range G.torusCube,
    ∀ k : Fin 4 → ℤ, (e fun μ => (k μ : ZMod G.cubesPerSide) : Set S.Torus) = G.torusCube k) ∧
  (range G.torusCube).ncard = G.cubesPerSide ^ 4
def MirrorWallsAndCubes : Prop :=
  (∀ (μ : Fin 4) (n : ℤ), ∃ i : ℤ,
    S.mesh * (i : ℝ) < G.origin μ + (n : ℝ) * G.edge ∧
    G.origin μ + (n : ℝ) * G.edge < S.mesh * ((i : ℝ) + 1) ∧
    G.mirrorOrigin μ + (n : ℝ) * G.edge = S.mesh * ((i : ℝ) + 1 / 2)) ∧
  (∀ k : Fin 4 → ℤ, ∀ x ∈ (S.gridPoints : Set AmbientSpace),
    x ∈ G.openCube k ↔ x ∈ G.toMirror.openCube k) ∧
  (∀ k : Fin 4 → ℤ, euclidNorm (G.cubeCenter k - G.toMirror.cubeCenter k) < S.mesh) ∧
  ∀ k : Fin 4 → ℤ, G.cubeAlgebra k = G.toMirror.cubeAlgebra k
def ProjOnLatticeAndOpenCubes : Prop :=
  S.proj '' (S.gridPoints : Set AmbientSpace) = (S.periodicLattice : Set S.Torus) ∧
  Function.Surjective (InfiniteLattice.projectLink S.L (S.m : ℕ) ((S.K : ℕ) : ℤ)) ∧
  Function.Surjective (TorusLifts.projectPlaquette S.L (S.m : ℕ) ((S.K : ℕ) : ℤ)) ∧
  (∀ p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize S.L ((S.K : ℕ) : ℤ)),
    (TorusLifts.projectPlaquette S.L (S.m : ℕ) ((S.K : ℕ) : ℤ) p).barycenter =
      S.proj p.center) ∧
  ∀ k : Fin 4 → ℤ, InjOn S.proj (G.openCube k)
def ReflectionGroupAction : Prop :=
  (∀ (σ : Fin 4 → ℤˣ) (n : Fin 4 → ℤ),
    TorusLifts.Descends (PeriodicLattice.torusSide S.L S.m) (PeriodicLattice.torusSide S.L S.m)
      (G.affineReflection σ n) (G.descendedReflection σ n)) ∧
  (fun r : Equiv.Perm S.Torus => (r : S.Torus → S.Torus)) ''
      (G.reflectionGroup : Set (Equiv.Perm S.Torus)) =
    range (fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) => G.descendedReflection p.1 p.2) ∧
  (∀ (σ σ' : Fin 4 → ℤˣ) (n n' : Fin 4 → ℤ),
    G.descendedReflection σ n = G.descendedReflection σ' n' ↔
      σ = σ' ∧ ∃ t : Fin 4 → ℤ, n - n' = ((G.cubesPerSide / 2 : ℕ) : ℤ) • t) ∧
  (∀ r ∈ G.reflectionGroup, ∃ ρ : S.TorusLatticeIsometry, ρ.toEquiv = r) ∧
  (∀ (σ : Fin 4 → ℤˣ) (n : Fin 4 → ℤ), orientationSign (G.descendedReflection σ n) = ∏ μ, σ μ) ∧
  (∀ r ∈ G.reflectionGroup, ∀ C ∈ G.mirrorTorusCubes, r '' C ∈ G.mirrorTorusCubes) ∧
  (∀ C ∈ G.mirrorTorusCubes, ∀ C' ∈ G.mirrorTorusCubes,
    ∃! r : G.reflectionGroup, (r : Equiv.Perm S.Torus) '' C = C') ∧
  G.mirrorTorusCubes.ncard = G.cubesPerSide ^ 4 ∧
  Nat.card G.reflectionGroup = G.cubesPerSide ^ 4 ∧
  ∀ s : ℤˣ,
    Nat.card {r : G.reflectionGroup //
        orientationSign ((r : Equiv.Perm S.Torus) : S.Torus → S.Torus) = s} =
      G.cubesPerSide ^ 4 / 2
def CubeObservablesOnTorus : Prop :=
  (∀ k : Fin 4 → ℤ, ∀ F ∈ G.cubeAlgebra k,
    InfiniteLattice.IsPeriodicObservable (S.pullToTorus F) ∧
    (∀ r ∈ G.reflectionGroup,
      InfiniteLattice.IsPeriodicObservable
        (PeriodicLattice.transportObservable r (S.pullToTorus F))) ∧
    InfiniteLattice.IsPeriodicObservable (G.reflectionProduct F) ∧
    G.chessboardNorm F ≤ InfiniteLattice.observableSupNorm F) ∧
  G.chessboardNorm (fun _ => 1) = 1
end CubicGrid
def CubicGridsAndReflectionGroups.Statement : Prop :=
  ∀ (S : GluingSetup) (G : CubicGrid S) (j : ℤ), G.edge = (S.L : ℝ) ^ j →
    G.CubesAndPeriods j ∧
    S.MirrorWallsAndLinks ∧
    G.MirrorWallsAndCubes ∧
    G.ProjOnLatticeAndOpenCubes ∧
    G.ReflectionGroupAction ∧
    G.CubeObservablesOnTorus
end YangMills.Construction.SourcesAndGluing
end
