import YangMills.Construction.ChessboardTori.StandingConventions
import Mathlib
import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1AndSupports
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.GrowthInTheNumberOfPoints
open InfiniteLattice (AmbientSpace)
inductive AmbientKind
  | euclidean
  | torus
abbrev ambientSpace (S : ChessboardTori.ChessboardSetup) : AmbientKind → Type
  | .euclidean => AmbientSpace
  | .torus => S.Torus
def ambientProj (S : ChessboardTori.ChessboardSetup) :
    (E : AmbientKind) → AmbientSpace → ambientSpace S E
  | .euclidean => id
  | .torus => S.proj
end YangMills.Construction.GrowthInTheNumberOfPoints
end

open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
def cubeEdge (L k : ℕ) : ℕ := L ^ k
theorem one_le_cubeEdge {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    1 ≤ cubeEdge L k :=
  Nat.one_le_pow _ _ (by have := hL.2; omega)
structure TorusSide where
  L : ℕ
  admissible : Conventions.IsAdmissibleBlockingFactor L
  m : ℕ+
namespace TorusSide
variable (s : TorusSide)
def length : ℝ := PeriodicLattice.torusSide s.L s.m
def ofStandingParameters (P : Conventions.StandingParameters) : TorusSide :=
  ⟨P.L, P.isAdmissible, P.m⟩
def asMirrorData : ReflectionPositivity.AxisMirror.MirrorData :=
  ⟨⟨s.L, s.admissible, 1, s.m⟩, 1, one_pos⟩
def asChessboardSetup : ChessboardTori.ChessboardSetup :=
  ⟨⟨s.L, s.admissible, 1, s.m⟩, 1, one_pos⟩
abbrev Point (E : ReflectionPositivity.AxisMirror.Ambient) : Type := E.Point s.asMirrorData
abbrev proj : (Fin 4 → ℝ) → s.asMirrorData.Torus := s.asMirrorData.projection
def ambientProj : (E : ReflectionPositivity.AxisMirror.Ambient) → (Fin 4 → ℝ) → s.Point E
  | .torus => GrowthInTheNumberOfPoints.ambientProj s.asChessboardSetup .torus
  | .euclidean => GrowthInTheNumberOfPoints.ambientProj s.asChessboardSetup .euclidean
def pullback {E : ReflectionPositivity.AxisMirror.Ambient} {Y : Type*} (f : s.Point E → Y) :
    (Fin 4 → ℝ) → Y :=
  f ∘ s.ambientProj E
abbrev pointDist (E : ReflectionPositivity.AxisMirror.Ambient) : s.Point E → s.Point E → ℝ :=
  ReflectionPositivity.AxisMirror.Ambient.metric s.asMirrorData E
def setDist : (E : ReflectionPositivity.AxisMirror.Ambient) →
    Set (s.Point E) → Set (s.Point E) → ℝ≥0∞
  | .torus => TorusMetric.setEuclidDist
  | .euclidean => TestFunctions.setDistR4
def PositivelySeparated (E : ReflectionPositivity.AxisMirror.Ambient) (A B : Set (s.Point E)) :
    Prop :=
  0 < s.setDist E A B
abbrev IsOpenWrt (E : ReflectionPositivity.AxisMirror.Ambient) (Z : Set (s.Point E)) : Prop :=
  MetricNotions.IsOpenWrt (s.pointDist E) Z
abbrev IsClosedWrt (E : ReflectionPositivity.AxisMirror.Ambient) (Z : Set (s.Point E)) : Prop :=
  MetricNotions.IsClosedWrt (s.pointDist E) Z
abbrev IsCompactWrt (E : ReflectionPositivity.AxisMirror.Ambient) (Z : Set (s.Point E)) : Prop :=
  MetricNotions.IsCompactWrt (s.pointDist E) Z
abbrev IsContinuousWrt (E : ReflectionPositivity.AxisMirror.Ambient) {𝕜 : Type*} [RCLike 𝕜]
    (f : s.Point E → 𝕜) : Prop :=
  MetricNotions.IsContinuousWrt (s.pointDist E) (fun a b : 𝕜 => ‖a - b‖) f
abbrev closedSupport (E : ReflectionPositivity.AxisMirror.Ambient) {𝕜 : Type*} [RCLike 𝕜]
    (f : s.Point E → 𝕜) : Set (s.Point E) :=
  ReflectionPositivity.AxisMirror.Ambient.closedSupport s.asMirrorData E f
def ball : (E : ReflectionPositivity.AxisMirror.Ambient) → s.Point E → ℝ → Set (s.Point E)
  | .torus, x, R => TestFunctions.closedBallTorus x R
  | .euclidean, x, R => TestFunctions.closedBallR4 x R
def IsBallRadius : ReflectionPositivity.AxisMirror.Ambient → ℝ → Prop
  | .torus, R => 0 < R ∧ R < s.length / 2
  | .euclidean, R => 0 < R
def IsBallWithRadius (E : ReflectionPositivity.AxisMirror.Ambient) (B : Set (s.Point E)) (R : ℝ) :
    Prop :=
  s.IsBallRadius E R ∧ ∃ x, B = s.ball E x R
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
