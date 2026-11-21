import YangMills.Construction.InfiniteLattice.ElementaryFactsOfAGridOfMultipleReflections
import YangMills.Construction.InfiniteLattice.InducedGroupOfAMirrorGridOnTheTorus
import YangMills.Construction.SourcesAndGluing.GridsAndTheirGroups
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections
open InfiniteLattice (AmbientSpace)
namespace TorusGroupInduced
variable {D : Setup} (G : D.Grid) (i : ℕ) (h : 2 * G.edge ≤ D.side)
theorem mirrorOrigin_toCubicGrid : (G.toCubicGrid i h).mirrorOrigin = G.shift :=
  SourcesAndGluing.CubicGrid.mirrorOrigin_of_isMirrorGrid (G.toCubicGrid i h) fun μ => G.shift_mem μ
theorem actsCoordinatewise_affineReflection (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) :
    G.ActsCoordinatewise ((G.toCubicGrid i h).affineReflection ε n) := by
  refine ⟨fun μ y => (((ε μ : ℤˣ) : ℤ) : ℝ) * (y - G.shift μ) + G.shift μ +
    2 * (n μ : ℝ) * G.edge, fun μ => ?_, fun x μ => ?_⟩
  · rcases Int.units_eq_one_or (ε μ) with hε | hε
    · exact Or.inl ⟨n μ, fun y => by simp only [hε]; push_cast; ring⟩
    · exact Or.inr ⟨n μ, fun y => by simp only [hε]; push_cast; ring⟩
  · simp only [SourcesAndGluing.CubicGrid.affineReflection, mirrorOrigin_toCubicGrid]
    rfl
theorem exists_affineReflection_of_actsCoordinatewise {f : AmbientSpace → AmbientSpace}
    (hf : G.ActsCoordinatewise f) :
    ∃ (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ), f = (G.toCubicGrid i h).affineReflection ε n := by
  obtain ⟨δ, hδ, hfδ⟩ := hf
  have key : ∀ α, ∃ (e : ℤˣ) (m : ℤ), ∀ y, δ α y =
      (((e : ℤˣ) : ℤ) : ℝ) * (y - G.shift α) + G.shift α + 2 * (m : ℝ) * G.edge := by
    intro α
    rcases hδ α with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨1, m, fun y => by rw [hm]; push_cast; ring⟩
    · exact ⟨-1, m, fun y => by rw [hm]; push_cast; ring⟩
  choose ε n hn using key
  refine ⟨ε, n, ?_⟩
  funext x α
  rw [hfδ, hn]
  simp only [SourcesAndGluing.CubicGrid.affineReflection, mirrorOrigin_toCubicGrid]
  rfl
theorem det_linear_of_eq_affineReflection (r : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) (ε : Fin 4 → ℤˣ)
    (n : Fin 4 → ℤ) (hr : (r : AmbientSpace → AmbientSpace) = (G.toCubicGrid i h).affineReflection ε n) :
    LinearMap.det (r.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) = (((∏ μ, ε μ : ℤˣ) : ℤ) : ℝ) := by
  have hl : (r.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) =
      Matrix.toLin' (Matrix.diagonal fun μ => (((ε μ : ℤˣ) : ℤ) : ℝ)) := by
    ext v μ
    have hv : r.linear (Pi.single v 1) = r (Pi.single v 1) - r 0 := by
      have := r.toAffineMap.linearMap_vsub (Pi.single v 1 : AmbientSpace) (0 : AmbientSpace)
      simpa using this
    simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_single, hv, hr, SourcesAndGluing.CubicGrid.affineReflection, Pi.sub_apply,
      Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.zero_apply]
    ring
  rw [hl, LinearMap.det_toLin', Matrix.det_diagonal]
  simp
end TorusGroupInduced
open TorusGroupInduced in
theorem torusGroupInducedHolds_of
    (hGrids : SourcesAndGluing.CubicGridsAndReflectionGroups.Statement)
    (hFacts : GridElementaryFacts) :
    TorusGroupInducedHolds := by
  intro D G h i
  obtain ⟨-, -, -, -, ⟨hInd, hImg, -, hIso, hPar, -⟩, -⟩ :=
    hGrids (D.toGluingSetup i) (G.toCubicGrid i h) G.edgeExp G.edge_eq_zpow_edgeExp
  obtain ⟨hActs, hMaps⟩ :=
    (hFacts D G G.edgeExp G.edge_eq_zpow_edgeExp).2.2.2.2
  have hUnique : ∀ (r' : D.Torus → D.Torus) (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ),
      D.coveringMap ∘ (G.toCubicGrid i h).affineReflection ε n = r' ∘ D.coveringMap →
        r' = (G.toCubicGrid i h).descendedReflection ε n := by
    intro r' ε n hr
    funext u
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    have h1 := congrFun hr x
    have h2 := congrFun (hInd ε n) x
    exact h1.symm.trans h2.symm
  refine ⟨?_, ?_⟩
  · ext r'
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨ρ, hρ⟩ := hIso r hr
      have hmem : ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) ∈
          Set.range (fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) =>
            (G.toCubicGrid i h).descendedReflection p.1 p.2) := by
        rw [← hImg]
        exact ⟨r, hr, rfl⟩
      obtain ⟨⟨ε, n⟩, hεn⟩ := hmem
      obtain ⟨g, hg⟩ := hMaps _ (actsCoordinatewise_affineReflection G i h ε n)
      refine ⟨?_, g.1, g.2, ?_⟩
      · have := ρ.isIsometry.2
        rw [← hρ]
        exact this
      · rw [hg]
        have h3 := hInd ε n
        change (G.toCubicGrid i h).descendedReflection ε n ∘ D.coveringMap =
          D.coveringMap ∘ (G.toCubicGrid i h).affineReflection ε n at h3
        rw [← h3]
        exact congrArg (fun φ : D.Torus → D.Torus => φ ∘ D.coveringMap) hεn
    · rintro ⟨-, r, hr, hcomm⟩
      obtain ⟨ε, n, hεn⟩ := exists_affineReflection_of_actsCoordinatewise G i h (hActs ⟨r, hr⟩)
      have hεn' : (r : AmbientSpace → AmbientSpace) = (G.toCubicGrid i h).affineReflection ε n := hεn
      rw [hεn'] at hcomm
      rw [hUnique r' ε n hcomm, hImg]
      exact ⟨(ε, n), rfl⟩
  · intro r' hr' r hcomm
    obtain ⟨ε, n, hεn⟩ := exists_affineReflection_of_actsCoordinatewise G i h (hActs r)
    have hεn' : ((r.1 : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) =
        (G.toCubicGrid i h).affineReflection ε n := hεn
    rw [hεn'] at hcomm
    rw [hUnique _ ε n hcomm, hPar ε n]
    exact (det_linear_of_eq_affineReflection G i h r.1 ε n hεn').symm
end YangMills.Construction.MultipleReflections
end
