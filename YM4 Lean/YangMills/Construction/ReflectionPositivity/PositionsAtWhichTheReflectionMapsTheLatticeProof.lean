import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import YangMills.Construction.ReflectionPositivity.PositionsAtWhichTheReflectionMapsTheLattice
import YangMills.Construction.ReflectionPositivity.ReflectionAtACoordinateMirror
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.ReflectionLevels
private theorem intCombination_apply (α : ℝ) (k : Fin 4 → ℤ) (i : Fin 4) :
    intCombination α k i = α * k i := by
  simp [intCombination, PeriodicLattice.coordVec, Finset.sum_apply, Pi.single_apply]
private theorem mesh_pos (M : MirrorData) : 0 < M.mesh := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.mesh_pos <;> assumption
private theorem euclidReflect_apply_same (i : Fin 4) (t : ℝ) (x : Fin 4 → ℝ) :
    euclidReflect i t x i = 2 * t - x i := by
  simp [euclidReflect, PeriodicLattice.coordVec]
  ring
private theorem euclidReflect_apply_of_ne {i j : Fin 4} (hji : j ≠ i) (t : ℝ) (x : Fin 4 → ℝ) :
    euclidReflect i t x j = x j := by
  simp [euclidReflect, PeriodicLattice.coordVec, hji]
private theorem mem_flatLattice_iff (M : MirrorData) (x : Fin 4 → ℝ) :
    x ∈ M.flatLattice ↔ x ∈ intLattice M.mesh := by
  change (∃ k : Fin 4 → ℤ, ∀ i, x i = (k i : ℝ) * M.mesh) ↔ _
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, funext fun i => by rw [intCombination_apply, hk i, mul_comm]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, fun i => by rw [intCombination_apply, mul_comm]⟩
private theorem mem_flatLattice_iff_coords (M : MirrorData) (x : Fin 4 → ℝ) :
    x ∈ M.flatLattice ↔ ∃ k : Fin 4 → ℤ, ∀ i, x i = (k i : ℝ) * M.mesh :=
  Iff.rfl
private theorem projection_facts (hproj : ProjectionFacts) (M : MirrorData) (i : Fin 4)
    (t : ℝ) :
    (∀ x, M.projection x ∈ M.torusSublattice ↔ x ∈ M.flatLattice) ∧
      ((M.torusSublattice : Set M.Torus) =
        M.projection '' (M.flatLattice : Set (Fin 4 → ℝ))) ∧
      M.Induces (euclidReflect i t) (M.descended (euclidReflect i t)) ∧
      ∀ Z : Set (Fin 4 → ℝ), M.descended (euclidReflect i t) '' (M.projection '' Z) =
        M.projection '' (euclidReflect i t '' Z) := by
  obtain ⟨-, -, -, hSite, hCutoff, hMap⟩ := hproj M
  have hle : -(M.m : ℤ) ≤ ((M.K : ℕ) : ℤ) := by
    have h1 : (0 : ℤ) ≤ (M.m : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ ((M.K : ℕ) : ℤ) := Int.natCast_nonneg _
    omega
  obtain ⟨-, -, hLat, hMem, -⟩ := hSite _ hle
  obtain ⟨-, -, -, -, -, hDesc, -, -, hImg, -⟩ :=
    hMap (axisSignFlip i) ((2 * t) • PeriodicLattice.coordVec i)
  rw [← euclidReflect_eq_frameAffine] at hDesc hImg
  rw [hCutoff.1] at hLat hMem
  have hset : (M.flatLattice : Set (Fin 4 → ℝ)) = intLattice M.mesh :=
    Set.ext fun x => mem_flatLattice_iff M x
  refine ⟨fun x => ?_, ?_, hDesc, hImg⟩
  · rw [mem_flatLattice_iff]
    exact hMem x
  · rw [hset]
    exact hLat
private theorem euclidReflect_involutive (hprops : ReflectionProperties) (M : MirrorData)
    (i : Fin 4) (t : ℝ) (x : Fin 4 → ℝ) : euclidReflect i t (euclidReflect i t x) = x :=
  congrFun (hprops M i t).1.2.1 x
private theorem preservesFlat_of_mem (hprops : ReflectionProperties) (M : MirrorData)
    (i : Fin 4) (t : ℝ) (h : 2 * t ∈ siteLevels M.mesh) : PreservesFlatLattice M i t := by
  obtain ⟨q, hq⟩ := h
  have hsub : ∀ x ∈ M.flatLattice, euclidReflect i t x ∈ M.flatLattice := by
    intro x hx
    obtain ⟨k, hk⟩ := (mem_flatLattice_iff_coords M x).1 hx
    refine (mem_flatLattice_iff_coords M _).2 ⟨Function.update k i (q - k i), fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      rw [euclidReflect_apply_same, hq, hk j, Function.update_self]
      push_cast
      ring
    · rw [euclidReflect_apply_of_ne hj, hk j, Function.update_of_ne hj]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hsub x hx
  · intro x hx
    exact ⟨euclidReflect i t x, hsub x hx, euclidReflect_involutive hprops M i t x⟩
private theorem preservesTorus_of_preservesFlat (hproj : ProjectionFacts) (M : MirrorData)
    (i : Fin 4) (t : ℝ) (h : PreservesFlatLattice M i t) : PreservesTorusLattice M i t := by
  obtain ⟨-, hLat, -, hImg⟩ := projection_facts hproj M i t
  change M.descended (euclidReflect i t) '' (M.torusSublattice : Set M.Torus) = _
  rw [hLat, hImg, h]
private theorem mem_of_preservesTorus (hproj : ProjectionFacts) (M : MirrorData) (i : Fin 4)
    (t : ℝ) (h : PreservesTorusLattice M i t) : 2 * t ∈ siteLevels M.mesh := by
  obtain ⟨hMem, -, hDesc, -⟩ := projection_facts hproj M i t
  have h0 : M.projection 0 ∈ (M.torusSublattice : Set M.Torus) :=
    (hMem 0).2 M.flatLattice.zero_mem
  have h1 : M.descended (euclidReflect i t) (M.projection 0) ∈
      (M.torusSublattice : Set M.Torus) := by
    have hin : M.descended (euclidReflect i t) (M.projection 0) ∈
        (M.descended (euclidReflect i t)) '' (M.torusSublattice : Set M.Torus) :=
      ⟨_, h0, rfl⟩
    have hEq : (M.descended (euclidReflect i t)) '' (M.torusSublattice : Set M.Torus) =
        (M.torusSublattice : Set M.Torus) := h
    rwa [hEq] at hin
  have h2 : M.descended (euclidReflect i t) (M.projection 0) =
      M.projection (euclidReflect i t 0) := congrFun hDesc 0
  rw [h2] at h1
  obtain ⟨k, hk⟩ := (mem_flatLattice_iff_coords M _).1 ((hMem _).1 h1)
  refine ⟨k i, ?_⟩
  have := hk i
  rw [euclidReflect_apply_same] at this
  simpa using this
private theorem mem_of_preservesFlat (M : MirrorData) (i : Fin 4) (t : ℝ)
    (h : PreservesFlatLattice M i t) : 2 * t ∈ siteLevels M.mesh := by
  have hin : euclidReflect i t 0 ∈ euclidReflect i t '' (M.flatLattice : Set (Fin 4 → ℝ)) :=
    ⟨0, M.flatLattice.zero_mem, rfl⟩
  have hEq : euclidReflect i t '' (M.flatLattice : Set (Fin 4 → ℝ)) =
      (M.flatLattice : Set (Fin 4 → ℝ)) := h
  rw [hEq] at hin
  obtain ⟨k, hk⟩ := (mem_flatLattice_iff_coords M _).1 hin
  refine ⟨k i, ?_⟩
  have := hk i
  rw [euclidReflect_apply_same] at this
  simpa using this
private theorem mem_halfLevels_iff (s t : ℝ) :
    t ∈ halfLevels s ↔ 2 * t ∈ siteLevels s := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, by ring⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by linarith⟩
private theorem disjoint_siteLevels_linkLevels (M : MirrorData) :
    Disjoint (siteLevels M.mesh) (linkLevels M.mesh) := by
  have hs : M.mesh ≠ 0 := (mesh_pos M).ne'
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨q, rfl⟩ ⟨r, hr⟩
  have h1 : (q : ℝ) = (r : ℝ) + 1 / 2 := mul_right_cancel₀ hs hr
  have h2 : (2 * q : ℝ) = 2 * r + 1 := by linarith
  have h3 : 2 * q = 2 * r + 1 := by exact_mod_cast h2
  omega
theorem characterization_holds (hproj : ProjectionFacts)
    (hprops : ReflectionProperties) : Characterization := by
  refine ⟨fun M i t => ?_, fun M => ⟨halfLevels_eq_union M.mesh, disjoint_siteLevels_linkLevels M⟩⟩
  have hT : PreservesTorusLattice M i t ↔ 2 * t ∈ siteLevels M.mesh :=
    ⟨mem_of_preservesTorus hproj M i t, fun h =>
      preservesTorus_of_preservesFlat hproj M i t (preservesFlat_of_mem hprops M i t h)⟩
  have hF : PreservesFlatLattice M i t ↔ 2 * t ∈ siteLevels M.mesh :=
    ⟨mem_of_preservesFlat M i t, preservesFlat_of_mem hprops M i t⟩
  obtain ⟨hSymF, -, -, hSymT, -⟩ := (hprops M i t).1
  refine ⟨hT, hF, ?_, ?_⟩
  · rw [mem_halfLevels_iff, ← hT]
    constructor
    · rintro ⟨g, hg⟩
      have h := g.image_eq
      rw [hg] at h
      exact h
    · intro h
      exact ⟨⟨_, hSymT, h⟩, rfl⟩
  · rw [mem_halfLevels_iff, ← hF]
    constructor
    · rintro ⟨g, hg⟩
      have h := g.image_eq
      rw [hg] at h
      exact h
    · intro h
      exact ⟨⟨_, hSymF, h⟩, rfl⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.ReflectionLevels
