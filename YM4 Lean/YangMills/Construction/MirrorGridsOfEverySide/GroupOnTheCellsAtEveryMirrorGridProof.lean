import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign translate)
namespace MirrorGridsAllSides
namespace CellAction
theorem exists_diagonal_linearComponent {D : GridSetup} (g : ReflectionGrid D)
    {r : AmbientSpace → AmbientSpace} (hr : g.IsProductOfCoordMaps r) :
    ∃ ε : Fin 4 → ℝ, (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
      ChessboardTori.HasLinearComponent r (Matrix.toLin' (Matrix.diagonal ε)) := by
  have h : ∀ μ, ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ x : AmbientSpace, r x μ = e * x μ + r 0 μ := by
    intro μ
    rcases hr μ with ⟨t, ht⟩ | ⟨k, hk⟩
    · refine ⟨1, Or.inl rfl, fun x => ?_⟩
      have h1 := ht x
      have h2 := ht 0
      simp only [ReflectionGrid.coordShift, Pi.zero_apply] at h1 h2
      linarith
    · refine ⟨-1, Or.inr rfl, fun x => ?_⟩
      have h1 := hk x
      have h2 := hk 0
      simp only [ReflectionGrid.coordReflect, Pi.zero_apply] at h1 h2
      linarith
  choose ε hε hx using h
  refine ⟨ε, hε, r 0, fun x => ?_⟩
  funext μ
  simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, hx μ x]
theorem bijOn_cellSet {D : GridSetup} (g : ReflectionGrid D) (hf : g.ReflectionGroupCoordForm)
    {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    BijOn (fun S => r '' S) g.cellSet g.cellSet := by
  have hmaps := hf.2.2.2.2.2.1
  refine ⟨fun S hS => hmaps r hr S hS, fun S _ S' _ h => ?_, fun S' hS' => ?_⟩
  · exact image_injective.mpr r.injective h
  · refine ⟨⇑(r⁻¹ : Equiv.Perm AmbientSpace) '' S',
      hmaps r⁻¹ (g.reflectionGroup.inv_mem hr) S' hS', ?_⟩
    show r '' (⇑(r⁻¹ : Equiv.Perm AmbientSpace) '' S') = S'
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨(r⁻¹ : Equiv.Perm AmbientSpace) x, ⟨x, hx, rfl⟩, by simp⟩
end CellAction
theorem allGridsReflectionGroupActsOnCells_holds
    (h₁ : ChessboardTori.ReflectionGroupCoordinates.Statement)
    (h₂ : ChessboardTori.CellsBlocksAndSigns.Statement) :
    AllGridsReflectionGroupActsOnCells := by
  intro D g _
  have hf := h₁ D g
  have hc := (h₂ D g).1
  refine ⟨fun r hr => ⟨⟨g.toLatticeSym ⟨r, hr⟩, rfl⟩,
      CellAction.exists_diagonal_linearComponent g (hf.1 r hr),
      CellAction.bijOn_cellSet g hf hr⟩,
    fun k k' => hf.2.2.2.2.2.2.1 _ ⟨k, rfl⟩ _ ⟨k', rfl⟩,
    fun k k' r h => (hc k k' r.1 r.2 h).2,
    fun r s => hf.2.2.2.1 r.1 r.2 s.1 s.2,
    fun t => ?_⟩
  obtain ⟨r, hr, ht, hs⟩ := hf.2.2.2.2.2.2.2 t
  exact ⟨⟨r, hr⟩, ht, hs⟩
end MirrorGridsAllSides
end YangMills.Construction
end
