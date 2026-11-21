import YangMills.Construction.ChessboardTori.QuotientsOfTheLattice
import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
structure PeriodSubgroup (D : ChessboardSetup) where
  mult : Fin 4 → ℤ
  four_le_mult : ∀ μ, 4 ≤ mult μ
namespace PeriodSubgroup
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def sideLengths : Fin 4 → ℝ := D.periodLengths P.mult
def subgroup : AddSubgroup AmbientSpace := D.periodGroup P.mult
abbrev TorusSpace : Type := BoxTorus.Space P.sideLengths
def proj : AmbientSpace →+ P.TorusSpace := BoxTorus.projection P.sideLengths
def torusDist (u v : P.TorusSpace) : ℝ := BoxTorus.torusDist u v
theorem torusDist_proj (y y' : AmbientSpace) :
    P.torusDist (P.proj y) (P.proj y') = D.periodicDistance P.mult y y' := by
  have key : ∀ z : AmbientSpace, BoxTorus.IsLiftOf z (P.proj y - P.proj y') ↔
      z - (y - y') ∈ P.subgroup := by
    intro z
    rw [BoxTorus.IsLiftOf, ← map_sub, ← sub_eq_zero]
    change BoxTorus.projection P.sideLengths z -
      BoxTorus.projection P.sideLengths (y - y') = 0 ↔ _
    rw [← map_sub, ← AddMonoidHom.mem_ker, BoxTorus.projection_ker]
    rfl
  rw [torusDist, BoxTorus.torusDist, ChessboardSetup.periodicDistance]
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - (y - y'), (key z).mp hz, ?_⟩
    simp [TorusMetric.euclidNormVec]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨y - y' + w, (key _).mpr ?_, ?_⟩
    · rw [add_sub_cancel_left]
      exact hw
    · simp [TorusMetric.euclidNormVec]
def translate (u : P.TorusSpace) (z : AmbientSpace) : P.TorusSpace := BoxTorus.translate u z
def descend (F : AmbientSpace → ℂ) : P.TorusSpace → ℂ :=
  fun u => F (Function.surjInv (BoxTorus.projection_surjective P.sideLengths) u)
theorem descend_proj {F : AmbientSpace → ℂ}
    (hF : ∀ x, ∀ w ∈ P.subgroup, F (x + w) = F x) (x : AmbientSpace) :
    P.descend F (P.proj x) = F x := by
  have hinv := Function.surjInv_eq (BoxTorus.projection_surjective P.sideLengths)
    (BoxTorus.projection P.sideLengths x)
  set z := Function.surjInv (BoxTorus.projection_surjective P.sideLengths)
    (BoxTorus.projection P.sideLengths x) with hz
  have hmem : z - x ∈ P.subgroup := by
    have hker : z - x ∈ (BoxTorus.projection P.sideLengths).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hinv, sub_self]
    rwa [BoxTorus.projection_ker] at hker
  change F z = F x
  have := hF x _ hmem
  rwa [add_sub_cancel] at this
abbrev gridSubgroup : AddSubgroup P.TorusSpace :=
  BoxTorus.gridSubgroup D.L ((D.K : ℕ) : ℤ) P.sideLengths
abbrev GridPoint : Type := BoxTorus.GridPoint D.L ((D.K : ℕ) : ℤ) P.sideLengths
abbrev DirectedEdge : Type := BoxTorus.DirectedEdge D.L ((D.K : ℕ) : ℤ) P.sideLengths
abbrev ForwardEdge : Type := BoxTorus.ForwardEdge D.L ((D.K : ℕ) : ℤ) P.sideLengths
abbrev Face : Type := BoxTorus.Face D.L ((D.K : ℕ) : ℤ) P.sideLengths
abbrev GaugeConfig : Type := BoxTorus.GaugeConfig D.L ((D.K : ℕ) : ℤ) P.sideLengths
def haarMeasure : Measure P.GaugeConfig :=
  BoxTorus.haarConfigMeasure D.L ((D.K : ℕ) : ℤ) P.sideLengths
def faceCenter (p : P.Face) : P.TorusSpace :=
  P.translate (p.corner : P.TorusSpace)
    ((D.mesh / 2) • (BoxTorus.basisVector p.dir₁ + BoxTorus.basisVector p.dir₂))
def faceEnergy (U : P.GaugeConfig) (p : P.Face) : ℝ :=
  BoxTorus.faceEnergy U p
def wilsonAction (U : P.GaugeConfig) : ℝ := BoxTorus.wilsonAction U
def projPoint (x : InfiniteLattice.LatticePoint D.mesh) : P.GridPoint :=
  ⟨P.proj x, by
    obtain ⟨n, hn⟩ := x.2
    exact ⟨n, congrArg (BoxTorus.projection P.sideLengths) (funext hn)⟩⟩
def projEdge (b : D.Link) : P.DirectedEdge where
  source := P.projPoint b.initial
  target := P.projPoint b.terminal
  isNeighbour := by
    have hstep : ∀ (μ : Fin 4) (σ : ℝ), (b.terminal : AmbientSpace) - b.initial =
        (σ * D.mesh) • BoxTorus.basisVector μ → (σ = 1 ∨ σ = -1) →
        BoxTorus.IsNeighbourStep (P.projPoint b.initial)
          (P.projPoint b.terminal) μ σ := by
      intro μ σ hdiff hσ
      refine ⟨hσ, ?_⟩
      have heq : (b.terminal : AmbientSpace) = b.initial + (σ * D.mesh) • BoxTorus.basisVector μ := by
        rw [← hdiff]
        abel
      change P.proj b.terminal = P.proj b.initial + P.proj _
      rw [heq, map_add]
      rfl
    obtain ⟨μ, hadj | hadj⟩ := b.isAdjacent
    · refine ⟨μ, 1, hstep μ 1 ?_ (Or.inl rfl)⟩
      have hc := congrArg (fun d : InfiniteLattice.LatticePoint D.mesh => (d : AmbientSpace)) hadj
      refine hc.trans (funext fun ν => ?_)
      by_cases hν : ν = μ
      · subst hν
        simp [InfiniteLattice.axisStep, BoxTorus.basisVector]
      · simp [InfiniteLattice.axisStep, BoxTorus.basisVector, Pi.single_eq_of_ne hν]
    · refine ⟨μ, -1, hstep μ (-1) ?_ (Or.inr rfl)⟩
      have hc := congrArg (fun d : InfiniteLattice.LatticePoint D.mesh => (d : AmbientSpace)) hadj
      refine hc.trans (funext fun ν => ?_)
      by_cases hν : ν = μ
      · subst hν
        simp [InfiniteLattice.axisStep, BoxTorus.basisVector]
      · simp [InfiniteLattice.axisStep, BoxTorus.basisVector, Pi.single_eq_of_ne hν]
def projFace (p : D.Plaquette) : P.Face :=
  ⟨P.projPoint p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def liftField (U : P.GaugeConfig) (b : D.Link) : Conventions.StandingParameters.gaugeGroup :=
  BoxTorus.edgeVariable U (P.projEdge b)
end PeriodSubgroup
namespace ChessboardSetup
variable (D : ChessboardSetup)
def shiftLink (b : D.Link) (v : InfiniteLattice.LatticePoint D.mesh) : D.Link :=
  ⟨b.initial + v, b.terminal + v, by simpa only [add_sub_add_right_eq_sub] using b.isAdjacent⟩
def shiftPlaquette (p : D.Plaquette) (v : InfiniteLattice.LatticePoint D.mesh) : D.Plaquette :=
  ⟨p.corner + v, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def cubicPeriod : PeriodSubgroup D where
  mult _ := 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ))
  four_le_mult _ := by
    have hL : (2 : ℤ) ≤ D.L := by
      have := D.isAdmissible.2
      exact_mod_cast (by omega : 2 ≤ D.L)
    have hn : (D.m : ℕ) + (D.K : ℕ) ≠ 0 := by
      have := D.m.pos
      omega
    have hle : (D.L : ℤ) ≤ (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) :=
      le_self_pow₀ (by omega) hn
    linarith
theorem sideLengths_cubicPeriod (μ : Fin 4) :
    D.cubicPeriod.sideLengths μ = PeriodicLattice.torusSide D.L D.m := by
  have hL : 0 < D.L := by
    have := D.isAdmissible.2
    omega
  rw [SourcesAndGluing.torusSide_eq_intCast_mul_meshSize hL D.m D.K]
  rfl
end ChessboardSetup
end ChessboardTori
end YangMills.Construction
end
