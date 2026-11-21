import YangMills.Construction.ReflectionPositivity.CheckerboardData
import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import YangMills.Construction.SourcesAndGluing.SimilaritiesOfTheLattices
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace LatticeRescaling
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
def inverseOnSpace : AmbientSpace → AmbientSpace := Function.invFun Ψ.toSpace
def inverseOnTorus : Ψ.scaleExponent.target.Torus → D.Torus := Function.invFun Ψ.toTorus
theorem target_mesh_eq : Ψ.scaleExponent.target.mesh = (D.L : ℝ) ^ Ψ.exp * D.mesh :=
  (ScaledLatticeMotion.target_mesh (e := Ψ.scaleExponent)).trans
    (meshSize_shift_eq_zpow_mul ScaleExponent.L_pos rfl)
theorem target_side_eq : Ψ.scaleExponent.target.side = (D.L : ℝ) ^ Ψ.exp * D.side :=
  Ψ.scaleExponent.torusSide_target
theorem zpow_L_pos : 0 < (D.L : ℝ) ^ Ψ.exp :=
  zpow_pos (by exact_mod_cast ScaleExponent.L_pos (D := D)) _
theorem isGridScale_scaled {c : ℝ} (hc : D.IsGridScale c) :
    Ψ.scaleExponent.target.IsGridScale ((D.L : ℝ) ^ Ψ.exp * c) := by
  obtain ⟨⟨j, rfl⟩, hlow, hhigh⟩ := hc
  have hp := Ψ.zpow_L_pos
  have hL : (D.L : ℝ) ≠ 0 := by
    exact_mod_cast (ScaleExponent.L_pos (D := D)).ne'
  refine ⟨⟨Ψ.exp + j, (zpow_add₀ hL _ _).symm⟩, ?_, ?_⟩
  · rw [Ψ.target_mesh_eq]
    exact mul_le_mul_of_nonneg_left hlow hp.le
  · rw [Ψ.target_side_eq, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hhigh hp.le
def mappedGrid (g : CubicGrid D) (hg : g.IsMirrorGrid) : CubicGrid Ψ.scaleExponent.target where
  edge := (D.L : ℝ) ^ Ψ.exp * g.edge
  isGridScale := Ψ.isGridScale_scaled g.isGridScale
  origin := Ψ.toSpace g.origin
  origin_ne μ i h := by
    obtain ⟨i₀, hi₀⟩ := hg μ
    obtain ⟨n, hn⟩ := Ψ.base_mem
    have hpos : (D.L : ℝ) ^ Ψ.exp * D.mesh ≠ 0 :=
      (mul_pos Ψ.zpow_L_pos D.mesh_pos).ne'
    rw [Ψ.target_mesh_eq] at h
    simp only [toSpace, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hi₀, hn μ] at h
    have hreal : (i₀ : ℝ) + n μ + 1 / 2 = i := mul_left_cancel₀ hpos (by linear_combination h)
    have hint : (2 * (i₀ + n μ) + 1 : ℤ) = 2 * i := by
      have hcast : ((2 * (i₀ + n μ) + 1 : ℤ) : ℝ) = ((2 * i : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    omega
def MapsInfiniteLattice : Prop :=
  Ψ.toSpace '' (D.gridPoints : Set AmbientSpace) =
      (Ψ.scaleExponent.target.gridPoints : Set AmbientSpace) ∧
  Function.Surjective Ψ.toMotion.onLink ∧
  Ψ.toMotion.onLink '' {c | c.IsPositivelyOriented} = {c | c.IsPositivelyOriented} ∧
  (∀ p : InfiniteLattice.ElementaryPlaquette D.mesh, Ψ.toMotion.onPlaquette p =
    ⟨Ψ.toMotion.onPoint p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩) ∧
  (∀ p : InfiniteLattice.ElementaryPlaquette D.mesh,
    Ψ.toSpace p.center = (Ψ.toMotion.onPlaquette p).center) ∧
  Ψ.toSpace '' range (InfiniteLattice.ElementaryPlaquette.center (a := D.mesh)) =
    range (InfiniteLattice.ElementaryPlaquette.center (a := Ψ.scaleExponent.target.mesh))
def MapsPeriodicLattice : Prop :=
  (D.L : ℝ) ^ Ψ.exp * D.side ∈ D.sideSet ∧
  Function.Bijective Ψ.toTorus ∧
  Ψ.toTorus '' (D.periodicLattice : Set D.Torus) =
    (Ψ.scaleExponent.target.periodicLattice : Set Ψ.scaleExponent.target.Torus) ∧
  Function.Surjective Ψ.toMotion.onTorusLink ∧
  Ψ.toMotion.onTorusLink '' {c | c.IsPositivelyOriented} =
    {c | c.IsPositivelyOriented} ∧
  (∀ p : PeriodicLattice.Plaquette D.L (D.m : ℕ) ((D.K : ℕ) : ℤ),
    Ψ.toMotion.onTorusPlaquette p =
      ⟨Ψ.toMotion.onTorusSite p.origin, p.firstAxis, p.secondAxis,
        p.firstAxis_lt_secondAxis⟩) ∧
  (∀ p : PeriodicLattice.Plaquette D.L (D.m : ℕ) ((D.K : ℕ) : ℤ),
    Ψ.toTorus p.barycenter = (Ψ.toMotion.onTorusPlaquette p).barycenter) ∧
  Ψ.toTorus '' range (PeriodicLattice.Plaquette.barycenter
      (L := D.L) (m := (D.m : ℕ)) (j := ((D.K : ℕ) : ℤ))) =
    range (PeriodicLattice.Plaquette.barycenter (L := Ψ.scaleExponent.target.L)
      (m := (Ψ.scaleExponent.target.m : ℕ)) (j := ((Ψ.scaleExponent.target.K : ℕ) : ℤ)))
def PreservesExpectation : Prop :=
  ∀ A : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, InfiniteLattice.IsPeriodicObservable A →
    D.expectation A = Ψ.scaleExponent.target.expectation (Ψ.precomposeTorus A)
def MapsPeriodicObservables : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (f : D.Torus → 𝕜),
    EqOn (Ψ.precomposeTorus (D.smeared f))
      (Ψ.scaleExponent.target.smeared (f ∘ Ψ.inverseOnTorus))
      Ψ.scaleExponent.target.gaugeFields
def MapsLipschitzOnTorus : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (f : D.Torus → 𝕜),
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f →
      TestFunctions.uniformNorm (f ∘ Ψ.inverseOnTorus) = TestFunctions.uniformNorm f ∧
      TestFunctions.lipConstTorus (f ∘ Ψ.inverseOnTorus) =
        (D.L : ℝ) ^ (-Ψ.exp) * TestFunctions.lipConstTorus f ∧
      Ψ.scaleExponent.target.sharpNormTorus (f ∘ Ψ.inverseOnTorus) ≤ D.sharpNormTorus f
def MapsSmearedEnergies : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (f : AmbientSpace → 𝕜),
    InfiniteLattice.IsBoundedBorelCompactlySupported f →
      Ψ.precompose (InfiniteLattice.smearedEnergy f) =
        InfiniteLattice.smearedEnergy (f ∘ Ψ.inverseOnSpace)
def MapsLipschitzOnSpace : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (f : AmbientSpace → 𝕜), TestFunctions.IsBoundedFun f →
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f →
      Ψ.scaleExponent.target.sharpNormR4 (f ∘ Ψ.inverseOnSpace) ≤ D.sharpNormR4 f
def MapsPeriodicGibbs : Prop :=
  ∀ ν : Measure D.GridField, IsProbabilityMeasure ν →
    (ν ∈ InfiniteLattice.periodicGibbsSet D.L (D.K : ℕ) D.β ↔
      Ψ.pushMeasure ν ∈ InfiniteLattice.periodicGibbsSet Ψ.scaleExponent.target.L
        (Ψ.scaleExponent.target.K : ℕ) Ψ.scaleExponent.target.β)
def MapsGridScales : Prop :=
  ∀ c : ℝ, D.IsGridScale c →
    Ψ.scaleExponent.target.IsGridScale ((D.L : ℝ) ^ Ψ.exp * c) ∧
    Ψ.scaleExponent.target.cellCount ((D.L : ℝ) ^ Ψ.exp * c) = D.cellCount c ∧
    (Ψ.scaleExponent.target.IsCellScale ((D.L : ℝ) ^ Ψ.exp * c) ↔ D.IsCellScale c)
def MapsCubes (g : CubicGrid D) (hg : g.IsMirrorGrid) : Prop :=
  (Ψ.mappedGrid g hg).IsMirrorGrid ∧
  (∀ k, Ψ.toSpace '' g.cube k = (Ψ.mappedGrid g hg).cube k) ∧
  (∀ k, Ψ.toSpace '' g.openCube k = (Ψ.mappedGrid g hg).openCube k) ∧
  ∀ μ n, Ψ.toSpace '' g.wall μ n = (Ψ.mappedGrid g hg).wall μ n
def MapsCubeAlgebras (g : CubicGrid D) (hg : g.IsMirrorGrid) : Prop :=
  ∀ k,
    Ψ.precompose '' g.cubeAlgebra k = (Ψ.mappedGrid g hg).cubeAlgebra k ∧
    ∀ F ∈ g.cubeAlgebra k,
      EqOn (Ψ.scaleExponent.target.pullToTorus (Ψ.precompose F))
        (Ψ.precomposeTorus (D.pullToTorus F)) Ψ.scaleExponent.target.gaugeFields
def ConjugatesReflectionGroup (g : CubicGrid D) (hg : g.IsMirrorGrid) : Prop :=
  ∃ φ : g.reflectionGroup ≃* (Ψ.mappedGrid g hg).reflectionGroup,
    (∀ (r : g.reflectionGroup) (x : D.Torus),
      (φ r : Equiv.Perm Ψ.scaleExponent.target.Torus) (Ψ.toTorus x) =
        Ψ.toTorus ((r : Equiv.Perm D.Torus) x)) ∧
    (∀ r : g.reflectionGroup,
      orientationSign (φ r : Equiv.Perm Ψ.scaleExponent.target.Torus) =
        orientationSign (r : Equiv.Perm D.Torus)) ∧
    ∀ (r : g.reflectionGroup) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ),
      EqOn (Ψ.precomposeTorus
          (PeriodicLattice.transportObservable (r : Equiv.Perm D.Torus) F))
        (PeriodicLattice.transportObservable (φ r : Equiv.Perm Ψ.scaleExponent.target.Torus)
          (Ψ.precomposeTorus F))
        Ψ.scaleExponent.target.gaugeFields
def MapsReflectionProducts (g : CubicGrid D) (hg : g.IsMirrorGrid) : Prop :=
  ∀ k, ∀ F ∈ g.cubeAlgebra k,
    EqOn (Ψ.precomposeTorus (g.reflectionProduct F))
      ((Ψ.mappedGrid g hg).reflectionProduct (Ψ.precompose F))
      Ψ.scaleExponent.target.gaugeFields ∧
    g.chessboardNorm F = (Ψ.mappedGrid g hg).chessboardNorm (Ψ.precompose F)
end LatticeRescaling
def CubicGrid.centeringPoint {D : GluingSetup} (g : CubicGrid D) : AmbientSpace :=
  -g.origin - ((1 / 2) * D.mesh) • Conventions.onesVector
def MovesToNormalizedOrigin {D : GluingSetup} (g : CubicGrid D) (hg : g.IsMirrorGrid) : Prop :=
  g.centeringPoint ∈ D.gridPoints ∧
  ∀ Ψ : LatticeRescaling D, Ψ.base = g.centeringPoint →
    (Ψ.mappedGrid g hg).mirrorOrigin =
        (-(1 / 2) * Ψ.scaleExponent.target.mesh) • Conventions.onesVector ∧
    (1 ≤ (D.L : ℝ) ^ Ψ.exp * g.edge → ∀ j : ℤ, g.edge = (D.L : ℝ) ^ j →
      ∃ q : ReflectionPositivity.CheckerboardDatum D.L,
        (q.depth : ℤ) = ((D.K : ℕ) : ℤ) - Ψ.exp ∧
        (q.sizeExp : ℤ) = ((D.m : ℕ) : ℤ) + Ψ.exp ∧ q.cellExp = j + Ψ.exp ∧
        q.basePoint = (-(1 / 2) * Ψ.scaleExponent.target.mesh) • Conventions.onesVector ∧
        q.IsNormalized)
end YangMills.Construction.SourcesAndGluing
end
