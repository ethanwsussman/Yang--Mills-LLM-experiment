import YangMills.Construction.MirrorGridsOfEverySide.FacePlanesAreLinkMirrorsAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.InfiniteLattice (AmbientSpace ReflectionClass)
open YangMills.Construction.ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
namespace WallsBisectLinks
theorem wallLevel_mem {D : GridSetup} (g : ReflectionGrid D) (μ : Fin 4) (k : ℤ) :
    ∃ m : ℤ, wallLevel g μ k = D.mesh * ((m : ℝ) + 1 / 2) := by
  obtain ⟨i, hi⟩ := g.origin_mem μ
  refine ⟨i + k * g.cellRatio, ?_⟩
  simp only [wallLevel, hi, g.cellSide_eq]
  push_cast
  ring
theorem intMul_ne_halfInt {a : ℝ} (ha : 0 < a) (p m : ℤ) : (p : ℝ) * a ≠ a * ((m : ℝ) + 1 / 2) := by
  intro h
  have h1 : (p : ℝ) = (m : ℝ) + 1 / 2 := by
    apply mul_right_cancel₀ ha.ne'
    linarith
  have h2 : ((2 * p : ℤ) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3 : 2 * p = 2 * m + 1 := by exact_mod_cast h2
  omega
theorem axis_eq_and_half {a c : ℝ} (ha : 0 < a) {m : ℤ} (hc : c = a * ((m : ℝ) + 1 / 2))
    {μ lam : Fin 4} {x y : AmbientSpace} {p : ℤ} (hx : x μ = (p : ℝ) * a) {s : ℝ} (hs : s = a ∨ s = -a)
    (hd : y - x = s • (Pi.single lam 1 : AmbientSpace)) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hz : (x + t • (y - x)) μ = c) : lam = μ ∧ t = 1 / 2 := by
  by_cases hl : lam = μ
  · refine ⟨hl, ?_⟩
    subst hl
    rw [hd] at hz
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hx, hc] at hz
    rcases hs with rfl | rfl
    · have e : t = ((m - p : ℤ) : ℝ) + 1 / 2 := by
        apply mul_left_cancel₀ ha.ne'
        push_cast
        linarith
      have l1 : (-1 : ℝ) < ((m - p : ℤ) : ℝ) := by linarith
      have l2 : ((m - p : ℤ) : ℝ) < 1 := by linarith
      have l3 : (-1 : ℤ) < m - p := by exact_mod_cast l1
      have l4 : m - p < 1 := by exact_mod_cast l2
      have l5 : m - p = 0 := by omega
      rw [e, l5]
      norm_num
    · have e : t = ((p - m : ℤ) : ℝ) - 1 / 2 := by
        apply mul_left_cancel₀ ha.ne'
        push_cast
        linarith
      have l1 : (0 : ℝ) < ((p - m : ℤ) : ℝ) := by linarith
      have l2 : ((p - m : ℤ) : ℝ) < 2 := by linarith
      have l3 : (0 : ℤ) < p - m := by exact_mod_cast l1
      have l4 : p - m < 2 := by exact_mod_cast l2
      have l5 : p - m = 1 := by omega
      rw [e, l5]
      norm_num
  · exfalso
    rw [hd] at hz
    have hne : μ ≠ lam := fun e => hl e.symm
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_eq_mul, mul_zero,
      add_zero, hx] at hz
    exact intMul_ne_halfInt ha p m (hz.trans hc)
theorem link_sub_eq {D : GridSetup} (b : D.Link) :
    ∃ (lam : Fin 4) (s : ℝ), (s = D.mesh ∨ s = -D.mesh) ∧
      (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = s • (Pi.single lam 1 : AmbientSpace) := by
  obtain ⟨lam, hl⟩ := b.isAdjacent
  have hsingle : (Pi.single lam D.mesh : AmbientSpace) = D.mesh • (Pi.single lam 1 : AmbientSpace) := by
    funext ν
    by_cases h : ν = lam
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  rcases hl with hl | hl
  · refine ⟨lam, D.mesh, Or.inl rfl, ?_⟩
    have h := congrArg (fun y : InfiniteLattice.LatticePoint D.mesh => (y : AmbientSpace)) hl
    simpa [InfiniteLattice.axisStep, hsingle] using h
  · refine ⟨lam, -D.mesh, Or.inr rfl, ?_⟩
    have h := congrArg (fun y : InfiniteLattice.LatticePoint D.mesh => (y : AmbientSpace)) hl
    simpa [InfiniteLattice.axisStep, hsingle] using h
theorem realNormal_dotProduct (μ : Fin 4) (x : AmbientSpace) :
    (ReflectionClass.axial μ).realNormal ⬝ᵥ x = x μ := by
  fin_cases μ <;>
    simp [ReflectionClass.realNormal, ReflectionClass.intNormal, dotProduct, Fin.sum_univ_four]
end WallsBisectLinks
open WallsBisectLinks in
theorem allGridsWallsBisectLinks : AllGridsWallsBisectLinks := by
  intro D g _ μ k
  obtain ⟨m, hm⟩ := wallLevel_mem g μ k
  have ha : 0 < D.mesh := D.mesh_pos
  have hplane : g.wall μ k = {x : AmbientSpace | x μ = wallLevel g μ k} := rfl
  refine ⟨hplane, ⟨m, hm⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨.axial μ, wallLevel g μ k, ⟨2 * m + 1, ?_⟩⟩, rfl, ?_, ⟨m, ?_⟩⟩
    · rw [hm]
      push_cast
      ring
    · ext x
      simp [InfiniteLattice.LatticeMirror.plane, realNormal_dotProduct, hplane]
    · show wallLevel g μ k = _
      rw [hm]
      ring
  · rintro x ⟨p, hp⟩ hx
    have h1 : x μ = wallLevel g μ k := hx
    rw [hp μ, hm] at h1
    exact intMul_ne_halfInt ha _ _ h1
  · rintro b ⟨y, hy, hyP⟩
    obtain ⟨lam, s, hs, hd⟩ := link_sub_eq b
    obtain ⟨p, hp⟩ := b.initial.2
    have key : ∀ z ∈ segment ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace), z ∈ g.wall μ k →
        lam = μ ∧ z = midpoint ℝ (b.initial : AmbientSpace) (b.terminal : AmbientSpace) := by
      intro z hz hzP
      rw [segment_eq_image'] at hz
      obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hz
      obtain ⟨hl, ht⟩ := axis_eq_and_half ha hm (hp μ) hs hd h0 h1 hzP
      refine ⟨hl, ?_⟩
      subst ht
      funext ν
      simp [midpoint_eq_smul_add]
      ring
    obtain ⟨hl, hym⟩ := key y hy hyP
    subst hl
    refine ⟨?_, ?_⟩
    · rcases hs with rfl | rfl
      · exact Or.inl hd
      · exact Or.inr hd
    · refine eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨y, hy, hyP⟩, ?_⟩
      rintro z ⟨hz, hzP⟩
      exact (key z hz hzP).2
  · refine ⟨g.toLatticeSym ⟨g.reflectPerm μ k, Subgroup.subset_closure ⟨(μ, k), rfl⟩⟩, ?_⟩
    funext x
    show g.reflect μ k x = _
    rw [ReflectionPositivity.CutoffMirrors.MirrorData.reflectVec_eq_sub]
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [ReflectionGrid.reflect, ChessboardTori.coordVec, PeriodicLattice.coordVec,
        wallLevel]
      ring
    · simp [ReflectionGrid.reflect, ChessboardTori.coordVec, PeriodicLattice.coordVec,
        Pi.single_eq_of_ne h]
end MirrorGridsAllSides
end YangMills.Construction
end
