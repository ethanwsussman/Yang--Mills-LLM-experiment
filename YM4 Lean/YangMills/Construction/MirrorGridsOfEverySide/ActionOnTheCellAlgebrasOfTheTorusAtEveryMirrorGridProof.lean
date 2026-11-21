import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.ChessboardTori.ThreeEvaluationRules
import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
namespace TorusCellObservableAction
variable {D : GridSetup} {g : ReflectionGrid D}
theorem periodicLink_eq_of_endpoints {b b' : D.PeriodicLink}
    (hs : (b.source : D.Torus) = b'.source)
    (ht : (b.target : D.Torus) = b'.target) : b = b' := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.link_eq_of_ends <;> assumption
def MapsLinksToLinks (D : GridSetup) (φ : D.Torus → D.Torus) : Prop :=
  ∀ b : D.PeriodicLink, ∃ b' : D.PeriodicLink,
    (b'.source : D.Torus) = φ b.source ∧ (b'.target : D.Torus) = φ b.target
theorem imageLink_endpoints {φ : D.Torus → D.Torus} (h : MapsLinksToLinks D φ)
    (b : D.PeriodicLink) :
    ((D.imageLink φ b).source : D.Torus) = φ b.source ∧
      ((D.imageLink φ b).target : D.Torus) = φ b.target :=
  Classical.epsilon_spec (h b)
theorem const_one_mem_torusFields (D : GridSetup) :
    (fun _ => 1 : D.PeriodicLink → Matrices.ComplexMatrix2) ∈ D.torusFields :=
  ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
theorem mapsLinksToLinks_of_mem (hL : ChessboardTori.LiftingRules.Statement)
    {φ : D.Torus → D.Torus} (hφ : φ ∈ g.inducedTorusMaps) : MapsLinksToLinks D φ := by
  obtain ⟨r, hr, hc⟩ := hφ
  intro b
  obtain ⟨b', h1, h2, -⟩ :=
    (((hL D).2.2.2 (g.toLatticeSym ⟨r, hr⟩) φ hc).2 _ (const_one_mem_torusFields D)).2 b
  exact ⟨b', h1, h2⟩
theorem pullbackField_mem {φ : D.Torus → D.Torus} (h : MapsLinksToLinks D φ)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.torusFields) :
    D.pullbackField φ U ∈ D.torusFields := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U (D.imageLink φ b.opposite) = (U (D.imageLink φ b))⁻¹
  have h1 : D.imageLink φ b.opposite = (D.imageLink φ b).opposite :=
    periodicLink_eq_of_endpoints
      ((imageLink_endpoints h _).1.trans (imageLink_endpoints h b).2.symm)
      ((imageLink_endpoints h _).2.trans (imageLink_endpoints h b).1.symm)
  rw [h1]
  exact hU.2 _ (mem_univ _)
theorem pullbackField_pullbackField {φ ψ : D.Torus → D.Torus} (hφ : MapsLinksToLinks D φ)
    (hψ : MapsLinksToLinks D ψ) (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    D.pullbackField ψ (D.pullbackField φ U) = D.pullbackField (φ ∘ ψ) U := by
  have hφψ : MapsLinksToLinks D (φ ∘ ψ) := fun b =>
    ⟨D.imageLink φ (D.imageLink ψ b),
      by rw [(imageLink_endpoints hφ _).1, (imageLink_endpoints hψ _).1]; rfl,
      by rw [(imageLink_endpoints hφ _).2, (imageLink_endpoints hψ _).2]; rfl⟩
  funext b
  change U (D.imageLink φ (D.imageLink ψ b)) = U (D.imageLink (φ ∘ ψ) b)
  congr 1
  refine periodicLink_eq_of_endpoints ?_ ?_
  · rw [(imageLink_endpoints hφ _).1, (imageLink_endpoints hψ _).1,
      (imageLink_endpoints hφψ _).1]
    rfl
  · rw [(imageLink_endpoints hφ _).2, (imageLink_endpoints hψ _).2,
      (imageLink_endpoints hφψ _).2]
    rfl
theorem pullbackField_leftInverse {φ ψ : D.Torus → D.Torus} (hφ : MapsLinksToLinks D φ)
    (hψ : MapsLinksToLinks D ψ) (h : ∀ u, φ (ψ u) = u)
    (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    D.pullbackField ψ (D.pullbackField φ U) = U := by
  funext b
  change U (D.imageLink φ (D.imageLink ψ b)) = U b
  congr 1
  refine periodicLink_eq_of_endpoints ?_ ?_
  · rw [(imageLink_endpoints hφ _).1, (imageLink_endpoints hψ _).1, h]
  · rw [(imageLink_endpoints hφ _).2, (imageLink_endpoints hψ _).2, h]
theorem exists_inverse_mem_inducedTorusMaps (hT : TorusGroupActsOnCells g)
    {φ : D.Torus → D.Torus} (hφ : φ ∈ g.inducedTorusMaps) :
    ∃ ψ ∈ g.inducedTorusMaps, (∀ u, φ (ψ u) = u) ∧ ∀ u, ψ (φ u) = u := by
  obtain ⟨r, hr, hc⟩ := hφ
  obtain ⟨s, hs⟩ := hT.1 r⁻¹ (g.reflectionGroup.inv_mem hr)
  have h1 : ∀ y, s.toFun (D.proj y) = D.proj (r⁻¹ y) := fun y => congrFun hs y
  have h2 : ∀ y, φ (D.proj y) = D.proj (r y) := fun y => (congrFun hc y).symm
  have hsurj : ∀ u : D.Torus, ∃ x, D.proj x = u := fun u =>
    ⟨TestFunctions.liftPoint u, TestFunctions.torusProj_liftPoint u⟩
  refine ⟨s.toFun, ⟨r⁻¹, g.reflectionGroup.inv_mem hr, hs.symm⟩, fun u => ?_, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := hsurj u
    rw [h1, h2]
    simp
  · obtain ⟨x, rfl⟩ := hsurj u
    rw [h2, h1]
    simp
theorem continuous_of_mem_reflectionGroup (hG : ReflectionGroupActsOnCells g)
    {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    Continuous (r : AmbientSpace → AmbientSpace) := by
  obtain ⟨-, ⟨ε, -, v, hv⟩, -⟩ := hG.1 r hr
  have h : (r : AmbientSpace → AmbientSpace) =
      fun x => Matrix.toLin' (Matrix.diagonal ε) x + v := funext hv
  rw [h]
  exact (LinearMap.continuous_of_finiteDimensional _).add continuous_const
theorem image_interior_eq (hG : ReflectionGroupActsOnCells g) {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ g.reflectionGroup) (S : Set AmbientSpace) : r '' interior S = interior (r '' S) :=
  (Homeomorph.mk r (continuous_of_mem_reflectionGroup hG hr)
    (continuous_of_mem_reflectionGroup hG (g.reflectionGroup.inv_mem hr))).image_interior S
theorem exists_image_cell_eq (hG : ReflectionGroupActsOnCells g) {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ g.reflectionGroup) (k : Fin 4 → ℤ) : ∃ k', r '' g.cell k = g.cell k' := by
  obtain ⟨-, -, hb⟩ := hG.1 r hr
  obtain ⟨k', hk'⟩ := hb.mapsTo (⟨k, rfl⟩ : g.cell k ∈ g.cellSet)
  exact ⟨k', hk'.symm⟩
theorem image_proj_image {r : Equiv.Perm AmbientSpace} {φ : D.Torus → D.Torus}
    (hc : D.proj ∘ r = φ ∘ D.proj) (A : Set AmbientSpace) :
    φ '' (D.proj '' A) = D.proj '' (r '' A) := by
  rw [← image_comp, ← hc, image_comp]
theorem image_mem_torusCellSet_and_observables (hL : ChessboardTori.LiftingRules.Statement)
    (hG : ReflectionGroupActsOnCells g) (hC : TorusCellStructure g) {φ : D.Torus → D.Torus}
    (hφ : φ ∈ g.inducedTorusMaps) {C : Set D.Torus} (hCm : C ∈ g.torusCellSet) :
    φ '' C ∈ g.torusCellSet ∧
      ∀ F ∈ g.torusCellObservables C,
        D.pullbackObservable φ F ∈ g.torusCellObservables (φ '' C) := by
  have hl := mapsLinksToLinks_of_mem hL hφ
  obtain ⟨r, hr, hc⟩ := hφ
  obtain ⟨S, ⟨k, rfl⟩, rfl⟩ := hCm
  obtain ⟨k', hk'⟩ := exists_image_cell_eq hG hr k
  have hint : ∀ j, g.torusCellInterior (D.proj '' g.cell j) =
      D.proj '' interior (g.cell j) := fun j => (hC.2.2.2.2 j j rfl).2.1
  have hImg : φ '' (D.proj '' g.cell k) = D.proj '' g.cell k' := by
    rw [image_proj_image hc, hk']
  have hInt : ∀ u ∈ g.torusCellInterior (D.proj '' g.cell k),
      φ u ∈ g.torusCellInterior (φ '' (D.proj '' g.cell k)) := by
    intro u hu
    rw [hint] at hu
    rw [hImg, hint, ← hk', ← image_interior_eq hG hr, ← image_proj_image hc]
    exact mem_image_of_mem φ hu
  have hlinks : ∀ b ∈ g.torusCellLinks (D.proj '' g.cell k),
      D.imageLink φ b ∈ g.torusCellLinks (φ '' (D.proj '' g.cell k)) := by
    intro b hb
    refine ⟨?_, ?_⟩
    · rw [(imageLink_endpoints hl b).1]
      exact hInt _ hb.1
    · rw [(imageLink_endpoints hl b).2]
      exact hInt _ hb.2
  refine ⟨by rw [hImg]; exact ⟨_, ⟨k', rfl⟩, rfl⟩, fun F hF => ?_⟩
  obtain ⟨f, hm, ⟨c, hcb⟩, hrep⟩ := hF
  refine ⟨fun w => f fun b => w ⟨D.imageLink φ b.1, hlinks b.1 b.2⟩,
    hm.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨c, fun _ => hcb _⟩,
    fun U => ?_⟩
  exact hrep ⟨_, pullbackField_mem hl U.2⟩
end TorusCellObservableAction
theorem allGridsTorusActOnCellObservables_holds
    (h₁ : ChessboardTori.LiftingRules.Statement)
    (h₂ : AllGridsReflectionGroupActsOnCells)
    (h₃ : AllGridsTorusCellStructure)
    (h₄ : AllGridsTorusGroupActsOnCells) :
    AllGridsTorusActOnCellObservables := by
  open TorusCellObservableAction in
  intro D g hg hs
  have hG := h₂ D g hg
  have hC := h₃ D g hg hs
  have hT := h₄ D g hg hs
  refine ⟨fun φ hφ ψ hψ F U _ => ?_, fun φ hφ C hCm => ⟨?_, fun F _ F' _ c =>
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩⟩
  · change F (D.pullbackField (φ ∘ ψ) U) = F (D.pullbackField ψ (D.pullbackField φ U))
    rw [pullbackField_pullbackField (mapsLinksToLinks_of_mem h₁ hφ)
      (mapsLinksToLinks_of_mem h₁ hψ)]
  · obtain ⟨hCφ, hin⟩ := image_mem_torusCellSet_and_observables h₁ hG hC hφ hCm
    obtain ⟨ψ, hψ, hφψ, hψφ⟩ := exists_inverse_mem_inducedTorusMaps hT hφ
    refine Subset.antisymm ?_ fun F' hF' => ?_
    · rintro _ ⟨F, hF, rfl⟩
      exact hin F hF
    · have hback : ψ '' (φ '' C) = C := by
        have hid : ψ ∘ φ = id := funext hψφ
        rw [← image_comp, hid, image_id]
      have hF := (image_mem_torusCellSet_and_observables h₁ hG hC hψ hCφ).2 F' hF'
      rw [hback] at hF
      refine ⟨_, hF, funext fun U => ?_⟩
      change F' (D.pullbackField ψ (D.pullbackField φ U)) = F' U
      rw [pullbackField_leftInverse (mapsLinksToLinks_of_mem h₁ hφ)
        (mapsLinksToLinks_of_mem h₁ hψ) hφψ]
end MirrorGridsAllSides
end YangMills.Construction
end
