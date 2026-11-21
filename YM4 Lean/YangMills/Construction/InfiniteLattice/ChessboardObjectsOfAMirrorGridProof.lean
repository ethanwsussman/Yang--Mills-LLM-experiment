import YangMills.Construction.InfiniteLattice.CellsOfTheTorusOfAMirrorGridProof
import YangMills.Construction.InfiniteLattice.ChessboardObjectsOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfAGridOfMultipleReflections
import YangMills.Construction.Measurability.FactorThroughMapStatement
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.MultipleReflections
namespace ChessboardObjects
open InfiniteLattice (AmbientSpace)
open Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem reflect_eq_wallReflect (μ : Fin 4) (n : ℤ) :
    G.toChessboardGrid.reflect μ n = G.wallReflect μ n := by
  funext x
  simp only [ChessboardTori.ReflectionGrid.reflect, InfiniteLattice.ReflectionGrid.wallReflect,
    cellSide_toChessboardGrid]
  rfl
theorem exists_affine_of_mem_chessboardGroup {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ G.toChessboardGrid.reflectionGroup) :
    ∃ e ∈ InfiniteLattice.ReflectionGrid.reflectionGroup G, (e : AmbientSpace → AmbientSpace) = r := by
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨⟨μ, n⟩, rfl⟩ := hr
    exact ⟨G.wallReflectEquiv μ n, Subgroup.subset_closure ⟨(μ, n), rfl⟩,
      (reflect_eq_wallReflect G μ n).symm⟩
  | one => exact ⟨1, one_mem _, rfl⟩
  | mul r s _ _ hr hs =>
    obtain ⟨e, he, her⟩ := hr
    obtain ⟨f, hf, hfs⟩ := hs
    refine ⟨e * f, mul_mem he hf, ?_⟩
    rw [AffineEquiv.coe_mul, Equiv.Perm.coe_mul, her, hfs]
  | inv r _ hr =>
    obtain ⟨e, he, her⟩ := hr
    refine ⟨e⁻¹, inv_mem he, funext fun x => ?_⟩
    apply r.injective
    have hr₁ : r (r⁻¹ x) = x := by simp
    have he₁ : e (e⁻¹ x) = x := e.apply_symm_apply x
    rw [hr₁, ← congrFun her, he₁]
theorem exists_perm_of_mem_reflectionGroup {e : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (he : e ∈ InfiniteLattice.ReflectionGrid.reflectionGroup G) :
    ∃ r ∈ G.toChessboardGrid.reflectionGroup, (r : AmbientSpace → AmbientSpace) = e := by
  induction he using Subgroup.closure_induction with
  | mem e he =>
    obtain ⟨⟨μ, n⟩, rfl⟩ := he
    exact ⟨G.toChessboardGrid.reflectPerm μ n, Subgroup.subset_closure ⟨(μ, n), rfl⟩,
      reflect_eq_wallReflect G μ n⟩
  | one => exact ⟨1, one_mem _, rfl⟩
  | mul e f _ _ he hf =>
    obtain ⟨r, hr, hre⟩ := he
    obtain ⟨s, hs, hsf⟩ := hf
    refine ⟨r * s, mul_mem hr hs, ?_⟩
    rw [AffineEquiv.coe_mul, Equiv.Perm.coe_mul, hre, hsf]
  | inv e _ he =>
    obtain ⟨r, hr, hre⟩ := he
    refine ⟨r⁻¹, inv_mem hr, funext fun x => ?_⟩
    apply e.injective
    have hr₁ : r (r⁻¹ x) = x := by simp
    have he₁ : e (e⁻¹ x) = x := e.apply_symm_apply x
    rw [he₁, ← congrFun hre, hr₁]
theorem linearComponent_eq_linear {r : AmbientSpace → AmbientSpace}
    (e : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) (h : (e : AmbientSpace → AmbientSpace) = r) :
    ChessboardTori.linearComponent r = (e.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) := by
  have hlin : ChessboardTori.HasLinearComponent r (e.linear : AmbientSpace →ₗ[ℝ] AmbientSpace) := by
    refine ⟨e 0, fun x => ?_⟩
    rw [← h]
    have := e.map_vadd 0 x
    simpa using this
  obtain ⟨v, hv⟩ : ChessboardTori.HasLinearComponent r (ChessboardTori.linearComponent r) :=
    Classical.epsilon_spec (p := ChessboardTori.HasLinearComponent r) ⟨_, hlin⟩
  obtain ⟨w, hw⟩ := hlin
  have hvw : v = w := by
    have h0 := (hv 0).symm.trans (hw 0)
    simpa using h0
  refine LinearMap.ext fun x => ?_
  have hx := (hv x).symm.trans (hw x)
  rw [hvw] at hx
  exact add_right_cancel hx
theorem orientationSign_eq_orientation {r : Equiv.Perm AmbientSpace}
    (e : InfiniteLattice.ReflectionGrid.reflectionGroup G)
    (h : ((e.1 : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) = r) :
    (((ChessboardTori.orientationSign r : ℤˣ) : ℤ) : ℝ) =
      InfiniteLattice.ReflectionGrid.orientation G e := by
  have hl := linearComponent_eq_linear e.1 h
  have hs : InfiniteLattice.ReflectionGrid.orientation G e =
      LinearMap.det (ChessboardTori.linearComponent r) := by
    rw [hl]
    rfl
  unfold ChessboardTori.orientationSign
  rw [← hs]
  rcases InfiniteLattice.ReflectionGrid.orientation_eq_one_or_neg_one G e with h1 | h1
  · rw [if_pos h1, h1]
    simp
  · rw [if_neg (by rw [h1]; norm_num), h1]
    simp
theorem cell_eq_tile (k : Fin 4 → ℤ) : G.toChessboardGrid.cell k = G.tile k := by apply _root_.YangMills.Construction.MultipleReflections.TorusCells.tile_toChessboardGrid <;> assumption
theorem interior_tile (k : Fin 4 → ℤ) : interior (G.tile k) = G.tileInterior k := by
  have h : G.tile k = Set.pi univ fun μ => Icc (G.cornerAt k μ) (G.cornerAt k μ + G.edge) := by
    ext x
    exact ⟨fun hx μ _ => hx μ, fun hx μ => hx μ (mem_univ μ)⟩
  rw [h, interior_pi_set finite_univ]
  ext x
  simp [InfiniteLattice.ReflectionGrid.tileInterior, Set.mem_pi]
theorem cellObservables_eq (hDoob : Measurability.FactorThroughMap.Claim) (S : Set AmbientSpace) :
    ChessboardTori.ReflectionGrid.cellObservables (D := D.toChessboardSetup) S =
      {A | InfiniteLattice.IsBoundedObservable A ∧
        InfiniteLattice.IsRegionMeasurable (interior S) A} := by
  ext F
  constructor
  · rintro ⟨f, hf, ⟨C, hC⟩, rfl⟩
    have hs : Measurable[InfiniteLattice.regionSigma (interior S)]
        (ChessboardTori.ReflectionGrid.restrictField (D := D.toChessboardSetup) S) := by
      refine @measurable_pi_lambda _ _ _ (InfiniteLattice.regionSigma (interior S)) _ _ fun b => ?_
      have hle : MeasurableSpace.comap
          (fun U : D.toChessboardSetup.GaugeField => U b.1) inferInstance ≤
          InfiniteLattice.regionSigma (interior S) :=
        le_iSup₂_of_le b.1 b.2 le_rfl
      exact (comap_measurable _).mono hle le_rfl
    have hb : Measurable (ChessboardTori.ReflectionGrid.restrictField (D := D.toChessboardSetup) S) := by
      refine measurable_pi_lambda _ fun b => ?_
      have hc : Continuous fun U : D.toChessboardSetup.GaugeField => U b.1 :=
        (continuous_apply b.1).comp continuous_subtype_val
      exact hc.measurable
    exact ⟨⟨hf.comp hb, C, fun U => hC _⟩, hf.comp hs⟩
  · rintro ⟨⟨-, C, hC⟩, hmeas⟩
    have hle : InfiniteLattice.regionSigma (interior S) ≤
        MeasurableSpace.comap (ChessboardTori.ReflectionGrid.restrictField (D := D.toChessboardSetup) S)
          inferInstance := by
      refine iSup₂_le fun b hb => ?_
      have h1 : (fun U : D.toChessboardSetup.GaugeField => U b) =
          (fun V : ChessboardTori.ReflectionGrid.interiorLinks (D := D.toChessboardSetup) S →
            Conventions.StandingParameters.gaugeGroup => V ⟨b, hb⟩) ∘
          ChessboardTori.ReflectionGrid.restrictField (D := D.toChessboardSetup) S := rfl
      rw [h1, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
    obtain ⟨-, hbound⟩ := hDoob D.toChessboardSetup.GaugeField
      (ChessboardTori.ReflectionGrid.interiorLinks (D := D.toChessboardSetup) S →
        Conventions.StandingParameters.gaugeGroup)
      inferInstance (ChessboardTori.ReflectionGrid.restrictField (D := D.toChessboardSetup) S) F
      (hmeas.mono hle le_rfl)
    obtain ⟨h, hh, hF, hb⟩ := hbound (max C 0) (le_max_right _ _)
      fun U => (hC U).trans (le_max_left _ _)
    exact ⟨h, hh, ⟨_, hb⟩, hF⟩
theorem latticeSymmetry_ext {a : ℝ} {s t : InfiniteLattice.LatticeSymmetry a}
    (h : s.toFun = t.toFun) : s = t := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
end ChessboardObjects
open ChessboardObjects Setup.Grid InfiniteLattice in
theorem chessboardObjectsHold_of_facts (hFacts : GridElementaryFacts)
    (hDoob : Measurability.FactorThroughMap.Claim) : ChessboardObjectsHold := by
  intro D G
  have hone := (hFacts D G G.edgeExp G.edge_eq_zpow_edgeExp).2.2.2.1
  refine ⟨G.cellSide_toChessboardGrid, rfl, ?_, ?_, ?_, cell_eq_tile G, ?_, ?_, ?_⟩
  · intro μ n
    ext x
    simp only [ChessboardTori.ReflectionGrid.wall, InfiniteLattice.ReflectionGrid.wall,
      cellSide_toChessboardGrid]
    rfl
  · ext f
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨e, he, h⟩ := exists_affine_of_mem_chessboardGroup G hr
      exact ⟨e, he, h⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨r, hr, h⟩ := exists_perm_of_mem_reflectionGroup G he
      exact ⟨r, hr, h⟩
  · intro r r' h
    exact orientationSign_eq_orientation G r' h.symm
  · intro k
    rw [cell_eq_tile, interior_tile]
  · intro k
    rw [cellObservables_eq hDoob, cell_eq_tile, interior_tile]
    rfl
  · intro k k' F _
    obtain ⟨e, huniq, hmap, hsign⟩ := hone k k'
    obtain ⟨r₀, hr₀, hr₀e⟩ := exists_perm_of_mem_reflectionGroup G e.2
    have hex : ∃ c : G.toChessboardGrid.reflectionGroup,
        (c.1 : AmbientSpace → AmbientSpace) '' G.toChessboardGrid.cell k =
          G.toChessboardGrid.cell k' := by
      refine ⟨⟨r₀, hr₀⟩, ?_⟩
      change (r₀ : AmbientSpace → AmbientSpace) '' _ = _
      rw [hr₀e, cell_eq_tile, cell_eq_tile]
      exact (huniq e).2 rfl
    have hc : ((G.toChessboardGrid.mover (G.toChessboardGrid.cell k)
        (G.toChessboardGrid.cell k')).1 : AmbientSpace → AmbientSpace) ''
          G.toChessboardGrid.cell k = G.toChessboardGrid.cell k' := Classical.epsilon_spec hex
    obtain ⟨e', he', he'c⟩ := exists_affine_of_mem_chessboardGroup G (G.toChessboardGrid.mover
      (G.toChessboardGrid.cell k) (G.toChessboardGrid.cell k')).2
    have hee : (⟨e', he'⟩ : G.reflectionGroup) = e := by
      refine (huniq _).1 ?_
      change (e' : AmbientSpace → AmbientSpace) '' _ = _
      rw [he'c, ← cell_eq_tile, ← cell_eq_tile]
      exact hc
    have hcm : ((G.toChessboardGrid.mover (G.toChessboardGrid.cell k)
        (G.toChessboardGrid.cell k')).1 : AmbientSpace → AmbientSpace) = G.tileReflection k k' := by
      rw [← he'c, ← hmap, ← hee]
    have hs : ChessboardTori.orientationSign (G.toChessboardGrid.mover (G.toChessboardGrid.cell k)
        (G.toChessboardGrid.cell k')).1 = tileSign k k' := by
      have h := orientationSign_eq_orientation G ⟨e', he'⟩ he'c
      rw [hee, hsign] at h
      exact Units.ext (Int.cast_injective h)
    have hiso : G.toChessboardGrid.toLatticeSym (G.toChessboardGrid.mover
        (G.toChessboardGrid.cell k) (G.toChessboardGrid.cell k')) = G.tileSymmetry k k' :=
      latticeSymmetry_ext hcm
    change Conventions.signedConjFun _ (InfiniteLattice.LatticeSymmetry.actOn
        (G.toChessboardGrid.toLatticeSym _) F) = Conventions.signedConjFun _ _
    rw [hs, hiso]
    rfl
end YangMills.Construction.MultipleReflections
end
