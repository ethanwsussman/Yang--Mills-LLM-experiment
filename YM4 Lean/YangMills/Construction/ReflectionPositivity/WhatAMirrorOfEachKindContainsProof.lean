import YangMills.Construction.ReflectionPositivity.PositionsAtWhichTheReflectionMapsTheLattice
import YangMills.Construction.ReflectionPositivity.WhatAMirrorOfEachKindContains
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.LevelContentsProof
open Ambient
variable (D : MirrorData)
private theorem mesh_ne_zero : D.mesh ≠ 0 := by
  have hL : (0 : ℝ) < D.L := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  simp only [MirrorData.mesh, PeriodicLattice.meshSize]
  exact (zpow_pos hL _).ne'
private def proj : (E : Ambient) → (Fin 4 → ℝ) → E.Point D
  | .torus => D.projection
  | .euclidean => id
private def periods : Ambient → ℝ → Prop
  | .torus, z => ∃ n : ℤ, z = D.side * n
  | .euclidean, z => z = 0
private theorem periods_zero : ∀ E : Ambient, periods D E 0
  | .torus => ⟨0, by simp⟩
  | .euclidean => rfl
private theorem intCombination_apply (α : ℝ) (w : Fin 4 → ℤ) (ν : Fin 4) :
    intCombination α w ν = (w ν : ℝ) * α := by
  simp [intCombination, PeriodicLattice.coordVec, Finset.sum_apply, Pi.single_apply, mul_comm]
private theorem projection_add (y v : Fin 4 → ℝ) :
    D.projection (y + v) = D.projection y + D.projection v :=
  funext fun _ => rfl
private theorem projection_single (μ : Fin 4) :
    D.projection (Pi.single μ D.mesh) =
      (PeriodicLattice.unitStep D.L D.m (D.K : ℕ) μ : D.Torus) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [MirrorData.projection, TorusMetric.torusProj, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, MirrorData.mesh]
  · simp [MirrorData.projection, TorusMetric.torusProj, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
variable {D}
private theorem proj_surjective (hl : ProjectionFacts) :
    ∀ (E : Ambient) (x : E.Point D), ∃ y, proj D E y = x
  | .torus, x => (hl D).1.1 x
  | .euclidean, x => ⟨x, rfl⟩
private theorem proj_mem_levelSet (hl : ProjectionFacts) (μ : Fin 4) (c : ℝ)
    (y : Fin 4 → ℝ) :
    ∀ E : Ambient, proj D E y ∈ levelSet D μ c E ↔ ∃ z, periods D E z ∧ y μ = c + z
  | .torus => by
    have h := ((hl D).2.2.1 μ {c} {c}).1 y
    constructor
    · intro hy
      obtain ⟨α, hα, n, hn⟩ := h.1 hy
      exact ⟨D.side * n, ⟨n, rfl⟩, by rw [hn, mem_singleton_iff.1 hα]⟩
    · rintro ⟨z, ⟨n, rfl⟩, hz⟩
      exact h.2 ⟨c, rfl, n, hz⟩
  | .euclidean => by
    constructor
    · intro hy
      exact ⟨0, rfl, by rw [add_zero]; exact hy⟩
    · rintro ⟨z, rfl, hz⟩
      rw [add_zero] at hz
      exact hz
private theorem proj_isSite (hl : ProjectionFacts) (y : Fin 4 → ℝ) :
    ∀ E : Ambient, (∃ s : E.Site D, siteToPoint s = proj D E y) ↔ ∀ ν, ∃ n : ℤ, y ν = n * D.mesh
  | .torus => by
    have hj : -(D.m : ℤ) ≤ (((D.K : ℕ) : ℤ)) := by
      have h1 : (0 : ℤ) ≤ (D.m : ℕ) := Int.natCast_nonneg _
      have h2 : (0 : ℤ) ≤ (D.K : ℕ) := Int.natCast_nonneg _
      omega
    have h := ((hl D).2.2.2.1 _ hj).2.2.2.1 y
    constructor
    · rintro ⟨s, hs⟩
      have hm : D.projection y ∈ PeriodicLattice.sublattice D.L D.m (((D.K : ℕ) : ℤ)) := by
        have hs' : (s : PeriodicLattice.Site D.L D.m (D.K : ℕ)).1 = D.projection y := hs
        rw [← hs']
        exact (s : PeriodicLattice.Site D.L D.m (D.K : ℕ)).2
      obtain ⟨w, hw⟩ := h.1 hm
      exact fun ν => ⟨w ν, by rw [← hw]; exact intCombination_apply _ _ _⟩
    · intro hy
      choose n hn using hy
      refine ⟨(⟨D.projection y, h.2 ⟨n, funext fun ν => ?_⟩⟩ :
        PeriodicLattice.Site D.L D.m (D.K : ℕ)), rfl⟩
      rw [hn ν]
      exact intCombination_apply _ _ _
  | .euclidean => by
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨n, hn⟩ := (s : InfiniteLattice.LatticePoint D.mesh).2
      have hs' : (s : InfiniteLattice.LatticePoint D.mesh).1 = y := hs
      exact fun ν => ⟨n ν, by rw [← hs']; exact hn ν⟩
    · intro hy
      choose n hn using hy
      exact ⟨(⟨y, n, hn⟩ : InfiniteLattice.LatticePoint D.mesh), rfl⟩
private theorem addVec_proj (hl : ProjectionFacts) (y v : Fin 4 → ℝ) :
    ∀ E : Ambient, addVec (proj D E y) v = proj D E (y + v)
  | .torus => (hl D).1.2.2.2.1 y v
  | .euclidean => rfl
private theorem periods_mem (hl : ProjectionFacts) {z : ℝ} :
    ∀ E : Ambient, periods D E z → ∃ n : ℤ, z = n * D.mesh
  | .torus, ⟨n, hn⟩ => by
    have hj : -(D.m : ℤ) ≤ (((D.K : ℕ) : ℤ)) := by
      have h1 : (0 : ℤ) ≤ (D.m : ℕ) := Int.natCast_nonneg _
      have h2 : (0 : ℤ) ≤ (D.K : ℕ) := Int.natCast_nonneg _
      omega
    obtain ⟨n', h'⟩ := ((hl D).2.2.2.1 _ hj).2.1 n
    exact ⟨n', by rw [hn, h', mul_comm]; rfl⟩
  | .euclidean, h => ⟨0, by rw [show z = 0 from h]; simp⟩
private theorem linkStart_isSite :
    ∀ {E : Ambient} (b : E.Bond D), ∃ s : E.Site D, siteToPoint s = linkStart b
  | .torus, b => ⟨(b : PeriodicLattice.Bond D.L D.m (D.K : ℕ)).source, rfl⟩
  | .euclidean, b => ⟨(b : InfiniteLattice.Link D.mesh).initial, rfl⟩
private theorem vertices_lift (hl : ProjectionFacts) :
    ∀ {E : Ambient} (p : E.Plaquette D), ∃ y, ∀ w ∈ plaquetteVertices p,
      ∃ u : Fin 4 → ℝ, w = proj D E (y + u) ∧
        ∀ μ, μ ≠ plaquetteLowAxis p → μ ≠ plaquetteHighAxis p → u μ = 0
  | .torus, p => by
    let q : PeriodicLattice.Plaquette D.L D.m (D.K : ℕ) := p
    obtain ⟨y, hy⟩ := proj_surjective (D := D) hl .torus (q.origin.1)
    have hy' : D.projection y = q.origin.1 := hy
    refine ⟨y, ?_⟩
    rintro w ⟨s, hs, rfl⟩
    have hf : plaquetteLowAxis (D := D) (E := .torus) p = q.firstAxis := rfl
    have hg : plaquetteHighAxis (D := D) (E := .torus) p = q.secondAxis := rfl
    rw [hf, hg]
    have hs' : s ∈ q.vertices := hs
    rcases hs' with rfl | rfl | rfl | rfl
    · refine ⟨0, ?_, fun _ _ _ => rfl⟩
      rw [add_zero]
      exact hy'.symm
    · refine ⟨Pi.single q.firstAxis D.mesh, ?_, fun μ h _ => Pi.single_eq_of_ne h _⟩
      change _ = D.projection _
      rw [projection_add, hy', projection_single]
      rfl
    · refine ⟨Pi.single q.firstAxis D.mesh + Pi.single q.secondAxis D.mesh, ?_, fun μ h h' => ?_⟩
      · change _ = D.projection _
        rw [projection_add, projection_add, hy', projection_single, projection_single,
          ← add_assoc]
        rfl
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    · refine ⟨Pi.single q.secondAxis D.mesh, ?_, fun μ _ h => Pi.single_eq_of_ne h _⟩
      change _ = D.projection _
      rw [projection_add, hy', projection_single]
      rfl
  | .euclidean, p => by
    let q : InfiniteLattice.ElementaryPlaquette D.mesh := p
    refine ⟨q.corner.1, ?_⟩
    rintro w ⟨s, hs, rfl⟩
    have hf : plaquetteLowAxis (D := D) (E := .euclidean) p = q.lowAxis := rfl
    have hg : plaquetteHighAxis (D := D) (E := .euclidean) p = q.highAxis := rfl
    rw [hf, hg]
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨0, (add_zero (q.corner.1 : Fin 4 → ℝ)).symm, fun _ _ _ => rfl⟩
    · exact ⟨Pi.single q.lowAxis D.mesh, rfl, fun μ h _ => Pi.single_eq_of_ne h _⟩
    · refine ⟨(Pi.single q.lowAxis D.mesh + Pi.single q.highAxis D.mesh : Fin 4 → ℝ), ?_,
        fun μ h h' => ?_⟩
      · exact add_assoc (q.corner.1 : Fin 4 → ℝ) (Pi.single q.lowAxis D.mesh)
          (Pi.single q.highAxis D.mesh)
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    · exact ⟨Pi.single q.highAxis D.mesh, rfl, fun μ _ h => Pi.single_eq_of_ne h _⟩
private theorem proj_add_mem_iff (hl : ProjectionFacts) {μ : Fin 4} {c : ℝ}
    {E : Ambient} (y : Fin 4 → ℝ) {v : Fin 4 → ℝ} (hv : v μ = 0) :
    proj D E (y + v) ∈ levelSet D μ c E ↔ proj D E y ∈ levelSet D μ c E := by
  rw [proj_mem_levelSet hl, proj_mem_levelSet hl, Pi.add_apply, hv, add_zero]
private theorem smul_coordVec_apply_of_ne {μ ν : Fin 4} (h : μ ≠ ν) (t : ℝ) :
    (t • PeriodicLattice.coordVec ν) μ = 0 := by
  simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
private theorem site_level_case (hl : ProjectionFacts) (E : Ambient) (μ : Fin 4) (c : ℝ)
    (hc : c ∈ siteLevels D.mesh) : SiteLevelContents D E μ c := by
  refine ⟨?_, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨q, hq⟩ := hc
    obtain ⟨s, hs⟩ := (proj_isSite (D := D) hl (Pi.single μ c) E).2 fun ν => by
      by_cases h : ν = μ
      · subst h
        exact ⟨q, by simpa using hq⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
    refine ⟨s, ?_⟩
    rw [hs, proj_mem_levelSet hl]
    exact ⟨0, periods_zero D E, by simp⟩
  · rintro b ⟨ν, ⟨ε, -, hstep⟩, hne⟩ hend
    obtain ⟨y, hy⟩ := proj_surjective (D := D) hl E (linkStart b)
    have hhead : linkEnd b = proj D E (y + (ε * D.mesh) • PeriodicLattice.coordVec ν) := by
      rw [hstep, ← hy, addVec_proj hl]
    have hiff : linkEnd b ∈ levelSet D μ c E ↔ linkStart b ∈ levelSet D μ c E := by
      rw [hhead, ← hy]
      exact proj_add_mem_iff hl y (smul_coordVec_apply_of_ne hne _)
    rcases hend with h | h
    · have ht : linkStart b ∈ levelSet D μ c E := h ▸ hx
      exact ⟨ht, hiff.2 ht⟩
    · have ht : linkEnd b ∈ levelSet D μ c E := h ▸ hx
      exact ⟨hiff.1 ht, ht⟩
  · intro p hp hxp w hw
    have h1 : μ ≠ plaquetteLowAxis p := fun h => hp (Or.inl h)
    have h2 : μ ≠ plaquetteHighAxis p := fun h => hp (Or.inr h)
    obtain ⟨y, hy⟩ := vertices_lift hl p
    obtain ⟨u, hu, hu0⟩ := hy _ hxp
    obtain ⟨u', hu', hu0'⟩ := hy w hw
    rw [hu']
    rw [hu] at hx
    exact (proj_add_mem_iff hl y (hu0' μ h1 h2)).2
      ((proj_add_mem_iff hl y (hu0 μ h1 h2)).1 hx)
private theorem param_eq_half (hl : ProjectionFacts) {E : Ambient} {μ : Fin 4} {c : ℝ}
    (hc : c ∈ linkLevels D.mesh) {y : Fin 4 → ℝ} (hy : ∃ i : ℤ, y μ = i * D.mesh) {ε τ : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hin : proj D E (y + (τ * ε * D.mesh) • PeriodicLattice.coordVec μ) ∈
      levelSet D μ c E) : τ = 1 / 2 := by
  obtain ⟨q, rfl⟩ := hc
  obtain ⟨i, hi⟩ := hy
  obtain ⟨z, hz, he⟩ := (proj_mem_levelSet hl μ _ _ E).1 hin
  obtain ⟨n, rfl⟩ := periods_mem hl E hz
  have hco : (y + (τ * ε * D.mesh) • PeriodicLattice.coordVec μ) μ = y μ + τ * ε * D.mesh := by
    simp [PeriodicLattice.coordVec]
  rw [hco, hi] at he
  have ha := mesh_ne_zero D
  have hcancel : (i : ℝ) + τ * ε = (q : ℝ) + 1 / 2 + n := by
    apply mul_right_cancel₀ ha
    linarith
  obtain ⟨h0, h1⟩ := hτ
  rcases hε with rfl | rfl
  · have hk : τ = ((q + n - i : ℤ) : ℝ) + 1 / 2 := by
      push_cast
      linarith
    have hk1 : ((q + n - i : ℤ) : ℝ) < 1 := by linarith
    have hk2 : (-1 : ℝ) < ((q + n - i : ℤ) : ℝ) := by linarith
    have hk1' : q + n - i < 1 := by exact_mod_cast hk1
    have hk2' : -1 < q + n - i := by exact_mod_cast hk2
    have hk0 : q + n - i = 0 := by omega
    rw [hk, hk0]
    simp
  · have hk : τ = ((i - q - n : ℤ) : ℝ) - 1 / 2 := by
      push_cast
      linarith
    have hk1 : ((i - q - n : ℤ) : ℝ) < 2 := by linarith
    have hk2 : (0 : ℝ) < ((i - q - n : ℤ) : ℝ) := by linarith
    have hk1' : i - q - n < 2 := by exact_mod_cast hk1
    have hk2' : 0 < i - q - n := by exact_mod_cast hk2
    have hk0 : i - q - n = 1 := by omega
    rw [hk, hk0]
    norm_num
private theorem link_level_case (hl : ProjectionFacts)
    (hp : ReflectionLevels.Characterization) (E : Ambient) (μ : Fin 4) (c : ℝ)
    (hc : c ∈ linkLevels D.mesh) : LinkLevelContents D E μ c := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := proj_surjective (D := D) hl E (siteToPoint x)
    obtain ⟨n, hn⟩ := (proj_isSite hl y E).1 ⟨x, hy.symm⟩ μ
    rw [← hy] at hx
    obtain ⟨z, hz, he⟩ := (proj_mem_levelSet hl μ c y E).1 hx
    obtain ⟨n', rfl⟩ := periods_mem hl E hz
    have hs : c ∈ siteLevels D.mesh := ⟨n - n', by push_cast; linarith⟩
    exact Set.disjoint_left.1 (hp.2 D).2 hs hc
  · rintro b ⟨ε₀, hε₀⟩ ⟨⟨p₀, ⟨τ₀, hτ₀, rfl⟩, hp₀⟩, htail, -⟩
    have hspec : IsSignedStep b (axisAndSign b).1 (axisAndSign b).2 :=
      Classical.epsilon_spec (p := fun q : Fin 4 × ℝ => IsSignedStep b q.1 q.2) ⟨(μ, ε₀), hε₀⟩
    obtain ⟨s, hs⟩ := linkStart_isSite b
    obtain ⟨y, hy⟩ := proj_surjective (D := D) hl E (linkStart b)
    have hsite := (proj_isSite hl y E).1 ⟨s, hs.trans hy.symm⟩
    have hpoint : ∀ τ, pointAlong b τ = proj D E
        (y + (τ * (axisAndSign b).2 * D.mesh) • PeriodicLattice.coordVec (axisAndSign b).1) := by
      intro τ
      unfold pointAlong
      rw [← hy, addVec_proj hl]
    have hdir : (axisAndSign b).1 = μ := by
      by_contra h
      apply htail
      rw [hpoint] at hp₀
      rw [← hy]
      exact (proj_add_mem_iff hl y (smul_coordVec_apply_of_ne (Ne.symm h) _)).1 hp₀
    have hkey : ∀ τ ∈ Icc (0 : ℝ) 1, pointAlong b τ ∈ levelSet D μ c E → τ = 1 / 2 := by
      intro τ hτ hin
      rw [hpoint, hdir] at hin
      exact param_eq_half hl hc (hsite μ) hspec.1 hτ hin
    have hhalf := hkey τ₀ hτ₀ hp₀
    refine ⟨?_, ?_⟩
    · change pointAlong b (1 / 2) ∈ _
      rw [← hhalf]
      exact hp₀
    · rintro _ ⟨τ, hτ, rfl⟩ hin
      change pointAlong b τ = pointAlong b (1 / 2)
      rw [hkey τ hτ hin]
theorem levelContents_holds (h₁ : ProjectionFacts)
    (h₂ : ReflectionLevels.Characterization) : LevelContents :=
  fun _ E μ c => ⟨site_level_case h₁ E μ c, link_level_case h₁ h₂ E μ c⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.LevelContentsProof
