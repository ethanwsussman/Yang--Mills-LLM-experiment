import YangMills.Construction.SourcesAndGluing.LatticeSimilarities
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusLifts TorusMetric
noncomputable section
namespace SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace GluingSetup
variable (D : GluingSetup)
def IsGridScale (c : ℝ) : Prop :=
  (∃ j : ℤ, c = (D.L : ℝ) ^ j) ∧ D.mesh ≤ c ∧ c ≤ D.side / 2
def IsCellScale (c : ℝ) : Prop := D.IsGridScale c ∧ (D.L : ℝ) ^ 2 * D.mesh ≤ c
def cellCount (c : ℝ) : ℝ := D.side / c
theorem one_lt_L : (1 : ℝ) < D.L := by
  have h := D.isAdmissible.2
  exact_mod_cast (by omega : 1 < D.L)
theorem mesh_pos : 0 < D.mesh := meshSize_pos (by have h := D.isAdmissible.2; omega) _
theorem isGridScale_zpow_iff (j : ℤ) :
    D.IsGridScale ((D.L : ℝ) ^ j) ↔ -((D.K : ℕ) : ℤ) ≤ j ∧ j ≤ ((D.m : ℕ) : ℤ) := by
  have hL := D.one_lt_L
  have hmesh : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
  have hhalf : D.side / 2 = (D.L : ℝ) ^ ((D.m : ℕ) : ℤ) := by
    simp [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  constructor
  · rintro ⟨-, hlo, hhi⟩
    rw [hmesh] at hlo
    rw [hhalf] at hhi
    exact ⟨(zpow_le_zpow_iff_right₀ hL).1 hlo, (zpow_le_zpow_iff_right₀ hL).1 hhi⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨j, rfl⟩, ?_, ?_⟩
    · rw [hmesh]
      exact (zpow_le_zpow_iff_right₀ hL).2 hlo
    · rw [hhalf]
      exact (zpow_le_zpow_iff_right₀ hL).2 hhi
def trivialExponent : ScaleExponent D where
  shift := 0
  one_le_cutoff_sub := by have := D.K.pos; omega
  one_le_side_add := by have := D.m.pos; omega
def pullToTorus (F : D.GridField → ℂ) : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  fun U => F (InfiniteLattice.liftField D.L D.m ((D.K : ℕ) : ℤ) U)
end GluingSetup
section Orientation
variable {D : GluingSetup}
def HasRotationPart (r : D.Torus → D.Torus) (S : Equiv.Perm AmbientSpace) : Prop :=
  ∃ Φ : ScaledLatticeMotion D.trivialExponent, Φ.rotation = S ∧
    Descends (PeriodicLattice.torusSide D.L D.m) (PeriodicLattice.torusSide D.L D.m) Φ.onSpace r
def rotationPart (r : D.Torus → D.Torus) : Equiv.Perm AmbientSpace :=
  Classical.epsilon (HasRotationPart r)
def rotationDet (S : Equiv.Perm AmbientSpace) : ℝ :=
  Matrix.det (Matrix.of fun ν μ => S (stdBasis μ) ν)
theorem rotationDet_eq_one_or_neg_one (S : Equiv.Perm AmbientSpace)
    (hS : S ∈ hyperoctahedralGroupEuclidean) :
    rotationDet S = 1 ∨ rotationDet S = -1 := by
  obtain ⟨σ, ε, rfl⟩ := hS
  have hmat : (Matrix.of fun ν μ => signedCoordinateEquiv σ ε (stdBasis μ) ν : Matrix _ _ ℝ) =
      Matrix.diagonal (fun ν => (((ε ν : ℤˣ) : ℤ) : ℝ)) *
        (1 : Matrix (Fin 4) (Fin 4) ℝ).submatrix σ id := by
    ext ν μ
    simp [signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean, stdBasis,
      Matrix.diagonal_mul, Matrix.one_apply, Pi.single_apply]
  have hdet : rotationDet (signedCoordinateEquiv σ ε) =
      (((∏ ν, ε ν) * Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [rotationDet, hmat, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute,
      Matrix.det_one]
    push_cast
    simp
  rcases Int.units_eq_one_or ((∏ ν, ε ν) * Equiv.Perm.sign σ) with h | h
  · exact Or.inl (by rw [hdet, h]; simp)
  · exact Or.inr (by rw [hdet, h]; simp)
def orientationSign (r : D.Torus → D.Torus) : ℤˣ :=
  open Classical in if rotationDet (rotationPart r) = 1 then 1 else -1
theorem orientationSign_eq_rotationDet {r : D.Torus → D.Torus} {S : Equiv.Perm AmbientSpace}
    (h : HasRotationPart r S) :
    (((orientationSign r : ℤˣ) : ℤ) : ℝ) = rotationDet (rotationPart r) := by
  have hr : HasRotationPart r (rotationPart r) := Classical.epsilon_spec ⟨S, h⟩
  obtain ⟨Φ, hΦ, -⟩ := hr
  rcases rotationDet_eq_one_or_neg_one _ (hΦ ▸ Φ.rotation_mem) with h1 | h1
  · simp [orientationSign, h1]
  · have h2 : (-1 : ℝ) ≠ 1 := by norm_num
    simp [orientationSign, h1, h2]
def signedCopy (r : Equiv.Perm D.Torus) (F : D.GridField → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  Conventions.signedConjFun (orientationSign r)
    (PeriodicLattice.transportObservable r (D.pullToTorus F))
theorem signedCopy_eq_actOn (r : D.TorusLatticeIsometry) (F : D.GridField → ℂ) :
    signedCopy r.toEquiv F =
      Conventions.signedConjFun (orientationSign r.toEquiv) (r.actOn (D.pullToTorus F)) := by
  rw [signedCopy, r.actOn_eq]
end Orientation
structure CubicGrid (D : GluingSetup) where
  edge : ℝ
  isGridScale : D.IsGridScale edge
  origin : AmbientSpace
  origin_ne : ∀ (μ : Fin 4) (i : ℤ), origin μ ≠ D.mesh * i
namespace CubicGrid
variable {D : GluingSetup} (g : CubicGrid D)
def cube (k : Fin 4 → ℤ) : Set AmbientSpace :=
  {x | ∀ μ, x μ - (g.origin μ + g.edge * k μ) ∈ Icc 0 g.edge}
def openCube (k : Fin 4 → ℤ) : Set AmbientSpace :=
  {x | ∀ μ, x μ - (g.origin μ + g.edge * k μ) ∈ Ioo 0 g.edge}
def wall (μ : Fin 4) (n : ℤ) : Set AmbientSpace := {x | x μ = g.origin μ + n * g.edge}
def walls : Set (Set AmbientSpace) := range fun p : Fin 4 × ℤ => g.wall p.1 p.2
def torusCube (k : Fin 4 → ℤ) : Set D.Torus := D.proj '' g.cube k
def IsMirrorGrid : Prop := ∀ μ, ∃ i : ℤ, g.origin μ = D.mesh * (i + 1 / 2)
def mirrorOrigin : AmbientSpace := fun μ => D.mesh * ((⌊g.origin μ / D.mesh⌋ : ℝ) + 1 / 2)
def toMirror : CubicGrid D where
  edge := g.edge
  isGridScale := g.isGridScale
  origin := g.mirrorOrigin
  origin_ne μ i h := by
    have h1 : ((⌊g.origin μ / D.mesh⌋ : ℤ) : ℝ) + 1 / 2 = i := mul_left_cancel₀ D.mesh_pos.ne' h
    have h2 : (2 * ⌊g.origin μ / D.mesh⌋ + 1 : ℤ) = 2 * i := by
      have h3 : ((2 * ⌊g.origin μ / D.mesh⌋ + 1 : ℤ) : ℝ) = ((2 * i : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h3
    omega
theorem toMirror_isMirrorGrid : g.toMirror.IsMirrorGrid := fun μ => ⟨⌊g.origin μ / D.mesh⌋, rfl⟩
theorem mirrorOrigin_of_isMirrorGrid (h : g.IsMirrorGrid) : g.mirrorOrigin = g.origin := by
  funext μ
  obtain ⟨i, hi⟩ := h μ
  have hf : ⌊g.origin μ / D.mesh⌋ = i := by
    rw [hi, mul_div_cancel_left₀ _ D.mesh_pos.ne', Int.floor_eq_iff]
    constructor <;> linarith
  change D.mesh * ((⌊g.origin μ / D.mesh⌋ : ℝ) + 1 / 2) = g.origin μ
  rw [hf, hi]
theorem toMirror_of_isMirrorGrid (h : g.IsMirrorGrid) : g.toMirror = g := by
  have h1 : g.toMirror.origin = g.origin := g.mirrorOrigin_of_isMirrorGrid h
  cases g
  simpa [toMirror] using h1
def cubeAlgebra (k : Fin 4 → ℤ) : Set (D.GridField → ℂ) :=
  {F | InfiniteLattice.IsBoundedObservable F ∧ ∀ U V : D.GridField,
    (∀ b ∈ InfiniteLattice.linksWithin (g.openCube k), U b = V b) → F U = F V}
def wallReflection (μ : Fin 4) (n : ℤ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - g.mirrorOrigin μ - n * g.edge)) • stdBasis μ
theorem wallReflection_involutive (μ : Fin 4) (n : ℤ) :
    Function.Involutive (g.wallReflection μ n) := by
  intro x
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [wallReflection, stdBasis]
    ring
  · simp [wallReflection, stdBasis, Pi.single_eq_of_ne h]
theorem wallReflection_add_latticeTranslate (μ : Fin 4) (n : ℤ) (ℓ : ℝ) (x : AmbientSpace)
    (k : Fin 4 → ℤ) :
    g.wallReflection μ n (x + TestFunctions.latticeTranslate ℓ k) =
      g.wallReflection μ n x + TestFunctions.latticeTranslate ℓ (Function.update k μ (-k μ)) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [wallReflection, stdBasis, TestFunctions.latticeTranslate]
    ring
  · simp [wallReflection, stdBasis, TestFunctions.latticeTranslate, Pi.single_eq_of_ne h,
      Function.update_of_ne h]
theorem descendedMap_wallReflection_torusProj (μ : Fin 4) (n : ℤ) (ℓ : ℝ) (x : AmbientSpace) :
    descendedMap ℓ ℓ (g.wallReflection μ n) (torusProj ℓ x) =
      torusProj ℓ (g.wallReflection μ n x) := by
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (TestFunctions.torusProj_liftPoint (torusProj ℓ x))
  rw [descendedMap, hk, wallReflection_add_latticeTranslate,
    TestFunctions.torusProj_add_latticeTranslate]
def torusWallReflection (μ : Fin 4) (n : ℤ) : Equiv.Perm D.Torus :=
  Function.Involutive.toPerm
    (descendedMap (PeriodicLattice.torusSide D.L D.m) (PeriodicLattice.torusSide D.L D.m)
      (g.wallReflection μ n))
    (fun u => by
      obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
      rw [descendedMap_wallReflection_torusProj, descendedMap_wallReflection_torusProj,
        g.wallReflection_involutive μ n x])
theorem descends_torusWallReflection (μ : Fin 4) (n : ℤ) :
    Descends (PeriodicLattice.torusSide D.L D.m) (PeriodicLattice.torusSide D.L D.m)
      (g.wallReflection μ n) (g.torusWallReflection μ n) :=
  funext fun x => g.descendedMap_wallReflection_torusProj μ n _ x
def reflectionGroup : Subgroup (Equiv.Perm D.Torus) :=
  Subgroup.closure (range fun p : Fin 4 × ℤ => g.torusWallReflection p.1 p.2)
def reflectionProduct (F : D.GridField → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  fun U => ∏ᶠ r : g.reflectionGroup, signedCopy (r : Equiv.Perm D.Torus) F U
def chessboardNorm (F : D.GridField → ℂ) : ℝ :=
  ‖D.expectation (g.reflectionProduct F)‖ ^ (1 / D.cellCount g.edge ^ 4)
end CubicGrid
end SourcesAndGluing
end
end YangMills.Construction
