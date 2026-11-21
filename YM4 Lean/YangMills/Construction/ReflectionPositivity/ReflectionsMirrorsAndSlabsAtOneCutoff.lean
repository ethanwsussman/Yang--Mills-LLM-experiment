import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
structure MirrorData extends Conventions.StandingParameters where
  coupling : ℝ
  coupling_pos : 0 < coupling
  dir : Fin 4
inductive SlabSide where
  | pos
  | neg
def SlabSide.toReal : SlabSide → ℝ
  | .pos => 1
  | .neg => -1
namespace MirrorData
variable (D : MirrorData)
def spacing : ℝ := PeriodicLattice.meshSize D.L (D.K : ℕ)
abbrev latticeSubgroup : AddSubgroup D.Torus := PeriodicLattice.sublattice D.L D.m (D.K : ℕ)
def sitesPerSide : ℕ := D.L ^ ((D.m : ℕ) + (D.K : ℕ))
def proj (y : Fin 4 → ℝ) : D.Torus := TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) y
def IsLiftOf (y : D.Torus) (y' : Fin 4 → ℝ) : Prop := D.proj y' = y
abbrev CircleCoord : Type := AddCircle (PeriodicLattice.torusSide D.L D.m)
def IsRep (t : D.CircleCoord) (r : ℝ) : Prop := (r : D.CircleCoord) = t
theorem isRep_iff (y : D.Torus) (ν : Fin 4) (r : ℝ) :
    D.IsRep (y ν) r ↔ ∃ y', D.IsLiftOf y y' ∧ y' ν = r := by
  constructor
  · intro h
    have hs : ∀ κ, ∃ t : ℝ, (t : D.CircleCoord) = y κ := fun κ =>
      QuotientAddGroup.mk_surjective (y κ)
    choose t ht using hs
    refine ⟨Function.update t ν r, ?_, by simp⟩
    funext κ
    by_cases hκ : κ = ν
    · subst hκ
      simpa [proj, TorusMetric.torusProj, IsRep] using h
    · simpa [proj, TorusMetric.torusProj, Function.update_of_ne hκ] using ht κ
  · rintro ⟨y', hy, rfl⟩
    exact congrFun hy ν
def addVec (x : D.Torus) (v : Fin 4 → ℝ) : D.Torus := x + D.proj v
def DiffEq (x' x : D.Torus) (v : Fin 4 → ℝ) : Prop := x' = D.addVec x v
def torusDist (x y : D.Torus) : ℝ := PeriodicLattice.torusEuclidDist D.L D.m x y
def closureSet (Z : Set D.Torus) : Set D.Torus := MetricNotions.closureWrt D.torusDist Z
def IsCompactSubset (Z : Set D.Torus) : Prop := MetricNotions.IsCompactWrt D.torusDist Z
def IsContinuousFn {Y : Type*} (d : Y → Y → ℝ) (f : D.Torus → Y) : Prop :=
  MetricNotions.IsContinuousWrt D.torusDist d f
def IsHomeo (f : D.Torus → D.Torus) : Prop :=
  ∃ g : D.Torus → D.Torus, Function.LeftInverse g f ∧ Function.RightInverse g f ∧
    D.IsContinuousFn D.torusDist f ∧ D.IsContinuousFn D.torusDist g
def IsBorel (Z : Set D.Torus) : Prop :=
  MeasurableSet[MeasurableSpace.generateFrom {U | MetricNotions.IsOpenWrt D.torusDist U}] Z
def supp {E : Type*} [Zero E] (f : D.Torus → E) : Set D.Torus := D.closureSet {x | f x ≠ 0}
end MirrorData
def euclidSupp {E : Type*} [Zero E] (f : (Fin 4 → ℝ) → E) : Set (Fin 4 → ℝ) :=
  MetricNotions.closureWrt (fun x y => TorusMetric.euclidNormVec (x - y)) {x | f x ≠ 0}
namespace MirrorData
variable (D : MirrorData)
def flipMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun ν => if ν = D.dir then -1 else 1
def reflectVec (c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  D.flipMatrix.mulVec x + (2 * c) • PeriodicLattice.coordVec D.dir
theorem reflectVec_eq_sub (c : ℝ) (x : Fin 4 → ℝ) :
    D.reflectVec c x = x - (2 * (x D.dir - c)) • PeriodicLattice.coordVec D.dir := by
  funext ν
  by_cases h : ν = D.dir
  · subst h
    simp [reflectVec, flipMatrix, Matrix.mulVec_diagonal, PeriodicLattice.coordVec]
    ring
  · simp [reflectVec, flipMatrix, Matrix.mulVec_diagonal, PeriodicLattice.coordVec, h]
def Induces (c : ℝ) (t : D.Torus → D.Torus) : Prop :=
  t ∘ D.proj = D.proj ∘ D.reflectVec c
theorem existsUnique_induces (c : ℝ) : ∃! t, D.Induces c t := by
  have hsurj : Function.Surjective D.proj := by
    intro x
    have hs : ∀ κ, ∃ t : ℝ, (t : D.CircleCoord) = x κ := fun κ =>
      QuotientAddGroup.mk_surjective (x κ)
    choose t ht using hs
    exact ⟨t, funext ht⟩
  refine ⟨fun x => Function.update x D.dir (((2 * c : ℝ) : D.CircleCoord) - x D.dir), ?_, ?_⟩
  · funext y
    funext ν
    simp only [Function.comp_apply, reflectVec_eq_sub]
    by_cases h : ν = D.dir
    · subst h
      simp only [Function.update_self, proj, TorusMetric.torusProj, Pi.sub_apply, Pi.smul_apply,
        PeriodicLattice.coordVec, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [← AddCircle.coe_sub]
      congr 1
      ring
    · simp [Function.update_of_ne h, proj, TorusMetric.torusProj,
        PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
  · intro t ht
    funext x
    obtain ⟨y, rfl⟩ := hsurj x
    have h₁ := congrFun ht y
    simp only [Function.comp_apply] at h₁
    rw [h₁]
    funext ν
    simp only [reflectVec_eq_sub]
    by_cases h : ν = D.dir
    · subst h
      simp only [Function.update_self, proj, TorusMetric.torusProj, Pi.sub_apply, Pi.smul_apply,
        PeriodicLattice.coordVec, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [← AddCircle.coe_sub]
      congr 1
      ring
    · simp [Function.update_of_ne h, proj, TorusMetric.torusProj,
        PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
def reflect (c : ℝ) : D.Torus → D.Torus :=
  Classical.epsilon (D.Induces c)
theorem induces_reflect (c : ℝ) : D.Induces c (D.reflect c) :=
  Classical.epsilon_spec (D.existsUnique_induces c).exists
def mirrorSet (c : ℝ) : Set D.Torus :=
  D.proj '' ({y | y D.dir = c} ∪ {y | y D.dir = c + D.side / 2})
def nearPlane (c : ℝ) : Set D.Torus := D.proj '' {y | y D.dir = c}
def farPlane (c : ℝ) : Set D.Torus := D.proj '' {y | y D.dir = c + D.side / 2}
def openSlab (c : ℝ) (σ : SlabSide) : Set D.Torus :=
  D.proj '' {y | 0 < σ.toReal * (y D.dir - c) ∧ σ.toReal * (y D.dir - c) < D.side / 2}
def IsLinkLevel (c : ℝ) : Prop := ∃ n : ℤ, c = D.spacing * ((n : ℝ) + 1 / 2)
end MirrorData
structure LinkLevel (D : MirrorData) where
  pos : ℝ
  isLinkLevel : D.IsLinkLevel pos
namespace LinkLevel
variable {D : MirrorData} (C : LinkLevel D)
def refl : D.Torus → D.Torus := D.reflect C.pos
def reflVec : (Fin 4 → ℝ) → Fin 4 → ℝ := D.reflectVec C.pos
def mirrorSet : Set D.Torus := D.mirrorSet C.pos
def openSlab (σ : SlabSide) : Set D.Torus := D.openSlab C.pos σ
def reflectFn {E : Type*} (f : D.Torus → E) : D.Torus → E := f ∘ C.refl
end LinkLevel
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
