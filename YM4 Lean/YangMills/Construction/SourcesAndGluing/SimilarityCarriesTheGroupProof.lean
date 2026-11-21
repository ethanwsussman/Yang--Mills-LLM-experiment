import YangMills.Construction.SourcesAndGluing.GridsAndTheirGroups
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesGridSidesAndCellsProof
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheGroup
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheTorusLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLifts TorusMetric
namespace SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace RescalingConjugatesGroup
theorem bondPreimage_eq_of_endpoints {L m : ℕ} {j : ℤ}
    {σ : PeriodicLattice.FourTorus L m ≃ PeriodicLattice.FourTorus L m}
    {b b' : PeriodicLattice.Bond L m j}
    (ht : (b'.source : PeriodicLattice.FourTorus L m) = σ.symm b.source)
    (hh : (b'.target : PeriodicLattice.FourTorus L m) = σ.symm b.target) :
    PeriodicLattice.bondPreimage σ b = b' := by
  have h : ∃ b'' : PeriodicLattice.Bond L m j,
      (b''.source : PeriodicLattice.FourTorus L m) = σ.symm b.source ∧
      (b''.target : PeriodicLattice.FourTorus L m) = σ.symm b.target := ⟨b', ht, hh⟩
  rw [PeriodicLattice.bondPreimage, dif_pos h]
  exact PeriodicLattice.Bond.ext (Subtype.ext (h.choose_spec.1.trans ht.symm))
    (Subtype.ext (h.choose_spec.2.trans hh.symm))
variable {D : GluingSetup} (Ψ : LatticeRescaling D) (g : CubicGrid D) (hg : g.IsMirrorGrid)
theorem mappedGrid_isMirrorGrid : (Ψ.mappedGrid g hg).IsMirrorGrid := by apply _root_.YangMills.Construction.SourcesAndGluing.RescalingKeepsGridScalesAndCubes.mappedGrid_isMirrorGrid <;> assumption
theorem mirrorOrigin_mappedGrid : (Ψ.mappedGrid g hg).mirrorOrigin = Ψ.toSpace g.mirrorOrigin := by
  rw [CubicGrid.mirrorOrigin_of_isMirrorGrid _ (mappedGrid_isMirrorGrid Ψ g hg),
    g.mirrorOrigin_of_isMirrorGrid hg]
  rfl
theorem toSpace_wallReflection (μ : Fin 4) (n : ℤ) (x : AmbientSpace) :
    Ψ.toSpace (g.wallReflection μ n x) =
      (Ψ.mappedGrid g hg).wallReflection μ n (Ψ.toSpace x) := by
  have hedge : (Ψ.mappedGrid g hg).edge = (D.L : ℝ) ^ Ψ.exp * g.edge := rfl
  funext ν
  simp only [CubicGrid.wallReflection, mirrorOrigin_mappedGrid Ψ g hg, hedge,
    LatticeRescaling.toSpace, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring
theorem toSpace_affineReflection (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (x : AmbientSpace) :
    Ψ.toSpace (g.affineReflection ε n x) =
      (Ψ.mappedGrid g hg).affineReflection ε n (Ψ.toSpace x) := by
  have hedge : (Ψ.mappedGrid g hg).edge = (D.L : ℝ) ^ Ψ.exp * g.edge := rfl
  funext ν
  simp only [CubicGrid.affineReflection, mirrorOrigin_mappedGrid Ψ g hg, hedge,
    LatticeRescaling.toSpace, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring
theorem toTorus_torusProj (x : AmbientSpace) :
    Ψ.toTorus (torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) x) =
      torusProj (PeriodicLattice.torusSide D.L (Ψ.scaleExponent.target.m : ℕ)) (Ψ.toSpace x) := by
  rw [← Ψ.toMotion_onSpace]
  exact Ψ.toMotion.onTorus_torusProj x
theorem toTorus_torusWallReflection (μ : Fin 4) (n : ℤ) (y : D.Torus) :
    Ψ.toTorus (g.torusWallReflection μ n y) =
      (Ψ.mappedGrid g hg).torusWallReflection μ n (Ψ.toTorus y) := by
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ y
  have h1 := congrFun (g.descends_torusWallReflection μ n) x
  have h2 := congrFun ((Ψ.mappedGrid g hg).descends_torusWallReflection μ n) (Ψ.toSpace x)
  simp only [Function.comp_apply] at h1 h2
  rw [h1, toTorus_torusProj, toTorus_torusProj, toSpace_wallReflection Ψ g hg]
  exact h2.symm
theorem toTorus_descendedReflection (hj : ∀ (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ),
      Descends (PeriodicLattice.torusSide D.L D.m) (PeriodicLattice.torusSide D.L D.m)
        (g.affineReflection ε n) (g.descendedReflection ε n))
    (hj' : ∀ (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ),
      Descends (PeriodicLattice.torusSide Ψ.scaleExponent.target.L Ψ.scaleExponent.target.m)
        (PeriodicLattice.torusSide Ψ.scaleExponent.target.L Ψ.scaleExponent.target.m)
        ((Ψ.mappedGrid g hg).affineReflection ε n) ((Ψ.mappedGrid g hg).descendedReflection ε n))
    (ε : Fin 4 → ℤˣ) (n : Fin 4 → ℤ) (y : D.Torus) :
    Ψ.toTorus (g.descendedReflection ε n y) =
      (Ψ.mappedGrid g hg).descendedReflection ε n (Ψ.toTorus y) := by
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ y
  have h1 := congrFun (hj ε n) x
  have h2 := congrFun (hj' ε n) (Ψ.toSpace x)
  simp only [Function.comp_apply] at h1 h2
  rw [h1, toTorus_torusProj, toTorus_torusProj, toSpace_affineReflection Ψ g hg]
  exact h2.symm
theorem mappedGrid_edge {j : ℤ} (hj : g.edge = (D.L : ℝ) ^ j) :
    (Ψ.mappedGrid g hg).edge = (D.L : ℝ) ^ (Ψ.exp + j) := by
  have hL : (D.L : ℝ) ≠ 0 := (by linarith [D.one_lt_L] : (0 : ℝ) < D.L).ne'
  change (D.L : ℝ) ^ Ψ.exp * g.edge = _
  rw [hj, zpow_add₀ hL]
theorem rescalingConjugatesGroup (hgrid : CubicGridsAndReflectionGroups.Statement)
    (htorus : RescalingMapsPeriodicLatticeClaim) :
    RescalingConjugatesGroupClaim := by
  intro D Ψ g hg
  have hbij : Function.Bijective Ψ.toTorus := (htorus D Ψ).2.1
  obtain ⟨⟨j, hj⟩, -⟩ := g.isGridScale
  have hG := (hgrid D g j hj).2.2.2.2.1
  have hG' := (hgrid Ψ.scaleExponent.target (Ψ.mappedGrid g hg) (Ψ.exp + j)
    (mappedGrid_edge Ψ g hg hj)).2.2.2.2.1
  let e : D.Torus ≃ Ψ.scaleExponent.target.Torus := Equiv.ofBijective _ hbij
  let c : Equiv.Perm D.Torus ≃* Equiv.Perm Ψ.scaleExponent.target.Torus := e.permCongrHom
  have hc : ∀ (r : Equiv.Perm D.Torus) (x : D.Torus), c r (Ψ.toTorus x) = Ψ.toTorus (r x) := by
    intro r x
    change e (r (e.symm (e x))) = e (r x)
    rw [e.symm_apply_apply]
  have hgen : ∀ (μ : Fin 4) (n : ℤ),
      c (g.torusWallReflection μ n) = (Ψ.mappedGrid g hg).torusWallReflection μ n := by
    intro μ n
    refine Equiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hbij.2 y
    rw [hc, toTorus_torusWallReflection Ψ g hg]
  have hmap : g.reflectionGroup.map c.toMonoidHom = (Ψ.mappedGrid g hg).reflectionGroup := by
    rw [CubicGrid.reflectionGroup, CubicGrid.reflectionGroup, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext p
    exact hgen p.1 p.2
  let φ : g.reflectionGroup ≃* (Ψ.mappedGrid g hg).reflectionGroup :=
    (c.subgroupMap g.reflectionGroup).trans (MulEquiv.subgroupCongr hmap)
  have hφ : ∀ r : g.reflectionGroup,
      (φ r : Equiv.Perm Ψ.scaleExponent.target.Torus) = c (r : Equiv.Perm D.Torus) := fun _ => rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro r x
    rw [hφ]
    exact hc _ x
  · intro r
    obtain ⟨p, hp⟩ : ((r : Equiv.Perm D.Torus) : D.Torus → D.Torus) ∈
        Set.range (fun p : (Fin 4 → ℤˣ) × (Fin 4 → ℤ) => g.descendedReflection p.1 p.2) := by
      rw [← hG.2.1]
      exact ⟨r, r.2, rfl⟩
    have hp' : g.descendedReflection p.1 p.2 = (r : Equiv.Perm D.Torus) := hp
    have hr : ((c (r : Equiv.Perm D.Torus) : Equiv.Perm Ψ.scaleExponent.target.Torus) :
        Ψ.scaleExponent.target.Torus → Ψ.scaleExponent.target.Torus) =
        (Ψ.mappedGrid g hg).descendedReflection p.1 p.2 := by
      funext y
      obtain ⟨x, rfl⟩ := hbij.2 y
      rw [hc, ← hp', toTorus_descendedReflection Ψ g hg hG.1 hG'.1]
    rw [hφ, hr, ← hp', hG.2.2.2.2.1, hG'.2.2.2.2.1]
  · intro r F U' _
    obtain ⟨ρ, hρ⟩ := hG.2.2.2.1 r r.2
    have hrρ : ∀ x, (r : Equiv.Perm D.Torus) x = ρ.toFun x := fun x => by
      rw [← hρ]
      rfl
    have h1 : ∀ b : D.PeriodicLink,
        PeriodicLattice.bondPreimage (r : Equiv.Perm D.Torus).symm b = ρ.linkMap b := fun b =>
      bondPreimage_eq_of_endpoints ((ρ.linkMap_source b).trans (hrρ _).symm)
        ((ρ.linkMap_target b).trans (hrρ _).symm)
    have h2 : ∀ b : D.PeriodicLink,
        PeriodicLattice.bondPreimage (c (r : Equiv.Perm D.Torus)).symm
            (Ψ.toMotion.onTorusLink b) =
          Ψ.toMotion.onTorusLink (ρ.linkMap b) := fun b =>
      bondPreimage_eq_of_endpoints
        (by
          change Ψ.toTorus (ρ.toFun b.source) = c (r : Equiv.Perm D.Torus) (Ψ.toTorus b.source)
          rw [hc, hrρ])
        (by
          change Ψ.toTorus (ρ.toFun b.target) = c (r : Equiv.Perm D.Torus) (Ψ.toTorus b.target)
          rw [hc, hrρ])
    rw [hφ]
    change F (PeriodicLattice.transportGaugeField (r : Equiv.Perm D.Torus).symm
        (Ψ.pullTorus U')) =
      F (Ψ.pullTorus (PeriodicLattice.transportGaugeField
        (c (r : Equiv.Perm D.Torus)).symm U'))
    congr 1
    funext b
    change U' (Ψ.toMotion.onTorusLink
        (PeriodicLattice.bondPreimage (r : Equiv.Perm D.Torus).symm b)) =
      U' (PeriodicLattice.bondPreimage (c (r : Equiv.Perm D.Torus)).symm
        (Ψ.toMotion.onTorusLink b))
    rw [h1, h2]
end RescalingConjugatesGroup
end SourcesAndGluing
end YangMills.Construction
end
