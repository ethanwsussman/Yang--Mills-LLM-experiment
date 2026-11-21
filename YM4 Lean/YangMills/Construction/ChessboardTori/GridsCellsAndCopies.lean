import YangMills.Construction.ChessboardTori.PeriodGroupsAndTheirLattices
import YangMills.Construction.Conventions.SignedConjugate
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
def coordVec (μ : Fin 4) : AmbientSpace := Pi.single μ 1
def HasLinearComponent (r : AmbientSpace → AmbientSpace) (R : AmbientSpace →ₗ[ℝ] AmbientSpace) : Prop :=
  ∃ v : AmbientSpace, ∀ x, r x = R x + v
def linearComponent (r : AmbientSpace → AmbientSpace) : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  Classical.epsilon (HasLinearComponent r)
def orientationSign (r : AmbientSpace → AmbientSpace) : ℤˣ :=
  open Classical in if LinearMap.det (linearComponent r) = 1 then 1 else -1
def translate (v : AmbientSpace) (x : AmbientSpace) : AmbientSpace := x + v
def PreservesDist (r : AmbientSpace → AmbientSpace) : Prop :=
  ∀ x y, TorusMetric.euclidNormVec (r x - r y) = TorusMetric.euclidNormVec (x - y)
namespace ChessboardSetup
variable (D : ChessboardSetup)
abbrev LatticeSym : Type := InfiniteLattice.LatticeSymmetry D.mesh
def faceCorners (p : D.Plaquette) : Set (InfiniteLattice.LatticePoint D.mesh) :=
  {p.corner, p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis,
    p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis + InfiniteLattice.axisStep D.mesh p.highAxis,
    p.corner + InfiniteLattice.axisStep D.mesh p.highAxis}
instance : Nonempty D.Plaquette := ⟨⟨0, 0, 1, by decide⟩⟩
def imageFace (r : D.LatticeSym) (p : D.Plaquette) : D.Plaquette :=
  Classical.epsilon fun p' => D.faceCorners p' = r.pointMap '' D.faceCorners p
def IsEdgeOf (b : D.Link) (p : D.Plaquette) : Prop :=
  b.initial ∈ D.faceCorners p ∧ b.terminal ∈ D.faceCorners p
theorem one_lt_factor : (1 : ℝ) < D.L := by
  have h := D.isAdmissible.2
  exact_mod_cast (by omega : 1 < D.L)
theorem mesh_pos : 0 < D.mesh := zpow_pos (by linarith [D.one_lt_factor]) _
end ChessboardSetup
structure ReflectionGrid (D : ChessboardSetup) where
  q : ℤ
  one_sub_K_le_q : 1 - ((D.K : ℕ) : ℤ) ≤ q
  origin : AmbientSpace
  origin_mem : ∀ μ, ∃ i : ℤ, origin μ = D.mesh * ((i : ℝ) + 1 / 2)
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def cellSide : ℝ := (D.L : ℝ) ^ g.q
def IsCoarse : Prop := 0 ≤ g.q
@[reducible] def withExponent (m' : ℕ+) : ReflectionGrid (D.withExponent m') :=
  ⟨g.q, g.one_sub_K_le_q, g.origin, g.origin_mem⟩
def cellRatio : ℤ := (D.L : ℤ) ^ (g.q + ((D.K : ℕ) : ℤ)).toNat
theorem cellSide_eq : g.cellSide = (g.cellRatio : ℝ) * D.mesh := by
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  have hq : 0 ≤ g.q + ((D.K : ℕ) : ℤ) := by linarith [g.one_sub_K_le_q]
  have h1 : ((D.L : ℝ) ^ (g.q + ((D.K : ℕ) : ℤ)).toNat) =
      (D.L : ℝ) ^ (g.q + ((D.K : ℕ) : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hq]
  simp only [cellSide, cellRatio, ChessboardSetup.mesh, PeriodicLattice.meshSize]
  push_cast
  rw [h1, ← zpow_add₀ hL]
  simp
theorem two_le_cellRatio : 2 ≤ g.cellRatio := by
  have hL : (2 : ℤ) ≤ D.L := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 2 ≤ D.L)
  have hn : (g.q + ((D.K : ℕ) : ℤ)).toNat ≠ 0 := by
    have := g.one_sub_K_le_q
    omega
  have h : (D.L : ℤ) ≤ (D.L : ℤ) ^ (g.q + ((D.K : ℕ) : ℤ)).toNat := le_self_pow₀ (by omega) hn
  exact hL.trans h
def wall (μ : Fin 4) (k : ℤ) : Set AmbientSpace := {x | x μ = g.origin μ + k * g.cellSide}
def walls : Set AmbientSpace := ⋃ (μ : Fin 4) (k : ℤ), g.wall μ k
def reflect (μ : Fin 4) (k : ℤ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - g.origin μ - k * g.cellSide)) • coordVec μ
theorem reflect_involutive (μ : Fin 4) (k : ℤ) : Function.Involutive (g.reflect μ k) := by
  intro x
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [reflect, coordVec]
    ring
  · simp [reflect, coordVec, Pi.single_eq_of_ne h]
def reflectPerm (μ : Fin 4) (k : ℤ) : Equiv.Perm AmbientSpace :=
  Function.Involutive.toPerm (g.reflect μ k) (g.reflect_involutive μ k)
def reflectionGroup : Subgroup (Equiv.Perm AmbientSpace) :=
  Subgroup.closure (range fun p : Fin 4 × ℤ => g.reflectPerm p.1 p.2)
def cell (k : Fin 4 → ℤ) : Set AmbientSpace :=
  {x | ∀ μ, x μ - (g.origin μ + g.cellSide * k μ) ∈ Icc 0 g.cellSide}
def cellSet : Set (Set AmbientSpace) := range g.cell
theorem preservesDist_reflect (μ : Fin 4) (k : ℤ) : PreservesDist (g.reflect μ k) := by
  intro x y
  simp only [TorusMetric.euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    simp [reflect, coordVec]
    ring
  · simp [reflect, coordVec, Pi.single_eq_of_ne h]
theorem reflect_mem_gridPoints {x : AmbientSpace} (hx : x ∈ D.gridPoints) (μ : Fin 4) (k : ℤ) :
    g.reflect μ k x ∈ D.gridPoints := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨i, hi⟩ := g.origin_mem μ
  refine ⟨Function.update n μ (2 * i + 1 + 2 * k * g.cellRatio - n μ), fun ν => ?_⟩
  by_cases h : ν = μ
  · subst h
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, coordVec, Pi.single_eq_same,
      smul_eq_mul, mul_one, Function.update_self, hn ν, hi, g.cellSide_eq]
    push_cast
    ring
  · simp [reflect, coordVec, Pi.single_eq_of_ne h, Function.update_of_ne h, hn ν]
def latticeSymGroup (D : ChessboardSetup) : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {r | PreservesDist r ∧ r '' (D.gridPoints : Set AmbientSpace) = D.gridPoints}
  mul_mem' := by
    rintro r s ⟨hr, hr'⟩ ⟨hs, hs'⟩
    refine ⟨fun x y => (hr _ _).trans (hs _ _), ?_⟩
    rw [Equiv.Perm.coe_mul, image_comp, hs', hr']
  one_mem' := ⟨fun _ _ => rfl, by simp⟩
  inv_mem' := by
    rintro r ⟨hr, hr'⟩
    refine ⟨fun x y => ?_, ?_⟩
    · have h := hr (r⁻¹ x) (r⁻¹ y)
      simpa using h.symm
    · conv_lhs => rw [← hr']
      rw [← image_comp]
      simp
theorem reflectionGroup_le_latticeSymGroup : g.reflectionGroup ≤ latticeSymGroup D := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨⟨μ, k⟩, rfl⟩
  refine ⟨g.preservesDist_reflect μ k, Subset.antisymm ?_ fun x hx => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact g.reflect_mem_gridPoints hx μ k
  · exact ⟨g.reflect μ k x, g.reflect_mem_gridPoints hx μ k, g.reflect_involutive μ k x⟩
def toLatticeSym (r : g.reflectionGroup) : D.LatticeSym :=
  ⟨r.1, (g.reflectionGroup_le_latticeSymGroup r.2).1, (g.reflectionGroup_le_latticeSymGroup r.2).2⟩
def interiorLinks (S : Set AmbientSpace) : Set D.Link := InfiniteLattice.linksWithin (interior S)
def restrictField (S : Set AmbientSpace) (U : D.GaugeField) :
    interiorLinks (D := D) S → Conventions.StandingParameters.gaugeGroup :=
  fun b => U b.1
def cellObservables (S : Set AmbientSpace) : Set (D.GaugeField → ℂ) :=
  {F | ∃ f : (interiorLinks (D := D) S → Conventions.StandingParameters.gaugeGroup) → ℂ,
    Measurable f ∧ (∃ C : ℝ, ∀ u, ‖f u‖ ≤ C) ∧ F = f ∘ restrictField S}
def transport (r : g.reflectionGroup) (F : D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  Conventions.signedConjFun (orientationSign r.1) ((g.toLatticeSym r).actOn F)
def mover (S S' : Set AmbientSpace) : g.reflectionGroup :=
  Classical.epsilon fun r : g.reflectionGroup => r.1 '' S = S'
def transportTo (S S' : Set AmbientSpace) (F : D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  g.transport (g.mover S S') F
def Straddles (b : D.Link) (μ : Fin 4) (k : ℤ) : Prop :=
  ((b.initial : AmbientSpace) μ < g.origin μ + k * g.cellSide ∧
      g.origin μ + k * g.cellSide < (b.terminal : AmbientSpace) μ) ∨
    ((b.terminal : AmbientSpace) μ < g.origin μ + k * g.cellSide ∧
      g.origin μ + k * g.cellSide < (b.initial : AmbientSpace) μ)
def IsReflectionPeriodic (W : AmbientSpace → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) ∧
    (∀ (μ : Fin 4) (k : ℤ), W ∘ g.reflect μ k = fun x => starRingEnd ℂ (W x)) ∧
    ∀ p : D.Plaquette, (∃ b : D.Link, D.IsEdgeOf b p ∧ ∃ (μ : Fin 4) (k : ℤ), g.Straddles b μ k) →
      W p.center = 0
def boxPeriods (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) : PeriodSubgroup D where
  mult μ := n μ * g.cellRatio
  four_le_mult μ := by nlinarith [hn μ, g.two_le_cellRatio]
end ReflectionGrid
def PeriodSubgroup.weightedPartition {D : ChessboardSetup} (P : PeriodSubgroup D)
    (W : AmbientSpace → ℂ) : ℂ :=
  ∫ U, Complex.exp (∑ᶠ p : P.Face,
    (P.descend W (P.faceCenter p) - (D.β : ℂ)) * (P.faceEnergy U p : ℂ)) ∂P.haarMeasure
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def cellsAcross : ℝ := PeriodicLattice.torusSide D.L D.m / g.cellSide
def block (k : Fin 4 → ℤ) : Set AmbientSpace :=
  {x | ∀ μ, x μ - (g.origin μ + g.cellSide * k μ) ∈ Icc 0 (PeriodicLattice.torusSide D.L D.m)}
def blocks : Set (Set AmbientSpace) := range g.block
def cellsWithin (B : Set AmbientSpace) : Set (Set AmbientSpace) := {S | S ∈ g.cellSet ∧ S ⊆ B}
def torusCellSet : Set (Set D.Torus) := (fun S => D.proj '' S) '' g.cellSet
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
