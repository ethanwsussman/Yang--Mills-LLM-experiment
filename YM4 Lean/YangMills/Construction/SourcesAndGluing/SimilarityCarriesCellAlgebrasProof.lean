import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.PeriodicExtensionsUnderLatticeSimilaritiesForm
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesCellAlgebras
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesGridSidesAndCells
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
namespace CubeAlgebrasUnderRescaling
open InfiniteLattice (AmbientSpace Link GaugeField)
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
theorem toSpace_injective : Function.Injective Ψ.toSpace := by
  intro x y h
  funext μ
  have h1 : (D.L : ℝ) ^ Ψ.exp * (x μ + Ψ.base μ) = (D.L : ℝ) ^ Ψ.exp * (y μ + Ψ.base μ) :=
    congrFun h μ
  have h2 := mul_left_cancel₀ Ψ.zpow_L_pos.ne' h1
  linarith
theorem toSpace_mem_openCube_iff (g : CubicGrid D) (hg : g.IsMirrorGrid)
    (hc : Ψ.MapsCubes g hg) (k : Fin 4 → ℤ) (x : AmbientSpace) :
    Ψ.toSpace x ∈ (Ψ.mappedGrid g hg).openCube k ↔ x ∈ g.openCube k := by
  rw [← hc.2.2.1 k]
  exact (toSpace_injective Ψ).mem_set_image
theorem onLink_mem_linksWithin_iff (g : CubicGrid D) (hg : g.IsMirrorGrid)
    (hc : Ψ.MapsCubes g hg) (k : Fin 4 → ℤ) (c : Link D.mesh) :
    Ψ.toMotion.onLink c ∈ InfiniteLattice.linksWithin ((Ψ.mappedGrid g hg).openCube k) ↔
      c ∈ InfiniteLattice.linksWithin (g.openCube k) := by
  change (((Ψ.toMotion.onLink c).initial : AmbientSpace) ∈ _ ∧
      ((Ψ.toMotion.onLink c).terminal : AmbientSpace) ∈ _) ↔ _
  rw [Ψ.onLink_initial, Ψ.onLink_terminal, toSpace_mem_openCube_iff Ψ g hg hc,
    toSpace_mem_openCube_iff Ψ g hg hc]
  rfl
theorem continuous_pull : Continuous Ψ.pull := by
  have h : Continuous fun U' : Ψ.scaleExponent.target.GridField =>
      (fun c => U'.1 (Ψ.toMotion.onLink c) :
        Link D.mesh → Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_pi fun c => (continuous_apply _).comp continuous_subtype_val
  exact h.subtype_mk fun U' => (Ψ.pull U').2
def linkEquivOfBijective (hb : Function.Bijective Ψ.toMotion.onLink) :
    Link D.mesh ≃ Link Ψ.scaleExponent.target.mesh :=
  Equiv.ofBijective _ hb
theorem onLink_linkEquivOfBijective_symm (hb : Function.Bijective Ψ.toMotion.onLink)
    (c : Link Ψ.scaleExponent.target.mesh) :
    Ψ.toMotion.onLink ((linkEquivOfBijective Ψ hb).symm c) = c :=
  (linkEquivOfBijective Ψ hb).apply_symm_apply c
theorem linkEquivOfBijective_symm_opposite (hb : Function.Bijective Ψ.toMotion.onLink)
    (c : Link Ψ.scaleExponent.target.mesh) :
    (linkEquivOfBijective Ψ hb).symm c.opposite =
      ((linkEquivOfBijective Ψ hb).symm c).opposite := by
  apply hb.1
  have h : Ψ.toMotion.onLink ((linkEquivOfBijective Ψ hb).symm c).opposite =
      (Ψ.toMotion.onLink ((linkEquivOfBijective Ψ hb).symm c)).opposite := rfl
  rw [h, onLink_linkEquivOfBijective_symm, onLink_linkEquivOfBijective_symm]
def push (hb : Function.Bijective Ψ.toMotion.onLink)
    (U : D.GridField) : Ψ.scaleExponent.target.GridField :=
  ⟨fun c => U.1 ((linkEquivOfBijective Ψ hb).symm c), fun c =>
    (congrArg U.1 (linkEquivOfBijective_symm_opposite Ψ hb c)).trans (U.2 _)⟩
theorem continuous_push (hb : Function.Bijective Ψ.toMotion.onLink) :
    Continuous (push Ψ hb) := by
  have h : Continuous fun U : D.GridField =>
      (fun c => U.1 ((linkEquivOfBijective Ψ hb).symm c) :
        Link Ψ.scaleExponent.target.mesh → Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_pi fun c => (continuous_apply _).comp continuous_subtype_val
  exact h.subtype_mk fun U => (push Ψ hb U).2
theorem push_pull (hb : Function.Bijective Ψ.toMotion.onLink)
    (U' : Ψ.scaleExponent.target.GridField) : push Ψ hb (Ψ.pull U') = U' :=
  Subtype.ext (funext fun c => congrArg U'.1 (onLink_linkEquivOfBijective_symm Ψ hb c))
theorem precompose_mem_cubeAlgebra (g : CubicGrid D) (hg : g.IsMirrorGrid)
    (hc : Ψ.MapsCubes g hg)
    (k : Fin 4 → ℤ) {F : D.GridField → ℂ} (hF : F ∈ g.cubeAlgebra k) :
    Ψ.precompose F ∈ (Ψ.mappedGrid g hg).cubeAlgebra k := by
  obtain ⟨⟨hm, C, hC⟩, hdep⟩ := hF
  refine ⟨⟨hm.comp (continuous_pull Ψ).measurable, C, fun U' => hC _⟩, fun U' V' h => ?_⟩
  refine hdep _ _ fun b hb => ?_
  exact h _ ((onLink_mem_linksWithin_iff Ψ g hg hc k b).2 hb)
theorem exists_precompose_eq (g : CubicGrid D) (hg : g.IsMirrorGrid)
    (hc : Ψ.MapsCubes g hg)
    (hb : Function.Bijective Ψ.toMotion.onLink)
    (k : Fin 4 → ℤ) {F' : Ψ.scaleExponent.target.GridField → ℂ}
    (hF' : F' ∈ (Ψ.mappedGrid g hg).cubeAlgebra k) :
    ∃ F ∈ g.cubeAlgebra k, Ψ.precompose F = F' := by
  obtain ⟨⟨hm, C, hC⟩, hdep⟩ := hF'
  refine ⟨F' ∘ push Ψ hb,
    ⟨⟨hm.comp (continuous_push Ψ hb).measurable, C, fun U => hC _⟩, fun U V h => ?_⟩,
    funext fun U' => congrArg F' (push_pull Ψ hb U')⟩
  refine hdep _ _ fun c hc' => h _ ?_
  rw [← onLink_mem_linksWithin_iff Ψ g hg hc k, onLink_linkEquivOfBijective_symm]
  exact hc'
end CubeAlgebrasUnderRescaling
theorem CubeAlgebrasUnderRescaling.cubeAlgebrasClaim_proof
    (hCubes : RescalingKeepsGridScalesAndCubes.Statement)
    (hLinks : ScaledMotionLinksOfSpaceClaim)
    (hLifts : ScaledMotionLiftClaim) :
    LatticeRescalingCubeAlgebrasClaim := by
  intro D Ψ g hg k
  have hc := (hCubes D Ψ).2 g hg
  have hb : Function.Bijective Ψ.toMotion.onLink :=
    (hLinks D Ψ.scaleExponent Ψ.toMotion).1
  refine ⟨Subset.antisymm ?_ fun F' hF' => ?_, fun F _ U' hU' => ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact CubeAlgebrasUnderRescaling.precompose_mem_cubeAlgebra Ψ g hg hc k hF
  · obtain ⟨F, hF, rfl⟩ :=
      CubeAlgebrasUnderRescaling.exists_precompose_eq Ψ g hg hc hb k hF'
    exact ⟨F, hF, rfl⟩
  · exact congrArg F (hLifts D Ψ.scaleExponent Ψ.toMotion U' hU')
end YangMills.Construction.SourcesAndGluing
end
