import YangMills.Construction.Dirichlet.RegionSequenceOperators
import YangMills.Construction.Lattice.GreenOperatorsOfCubesInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.BareDilation
variable {L j N : ℕ}
structure DilationData (𝒯 : RegionSequence.NestedRegions) (S : PeriodicLattice.Scales 4 L j N) (r : ℝ) :
    Prop where
  blockFactor_eq : 𝒯.L = L
  scale_pos : 0 < r
  side_eq : 𝒯.side = r * N
  mesh_eq : 𝒯.ξ = r * PeriodicLattice.fineScale L j
structure TwoLayered (𝒯 : RegionSequence.NestedRegions) (j : ℕ) : Prop where
  top_eq : 𝒯.s = j + 1
  lower_eq_univ : ∀ i ≤ j, 𝒯.Ω i = univ
  bonds_eq_univ : 𝒯.bonds = univ
namespace DilationData
variable {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
theorem period_ne_zero (_D : DilationData 𝒯 S r) : (N : ℝ) ≠ 0 := by
  exact_mod_cast S.period_pos.ne'
theorem side_ne_zero (_D : DilationData 𝒯 S r) : 𝒯.side ≠ 0 := 𝒯.side_pos.ne'
variable (D : DilationData 𝒯 S r)
def dilateEquiv : PeriodicLattice.Torus 4 N ≃+ 𝒯.Point :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle (N : ℝ) 𝒯.side D.period_ne_zero D.side_ne_zero
theorem circle_mesh_eq :
    AddCircle.equivAddCircle (N : ℝ) 𝒯.side D.period_ne_zero D.side_ne_zero
        ((S.fineMesh.h : ℝ) : AddCircle (N : ℝ)) = ((𝒯.ξ : ℝ) : AddCircle 𝒯.side) := by
  rw [AddCircle.equivAddCircle_apply_mk]
  congr 1
  have hN := D.period_ne_zero
  change PeriodicLattice.fineScale L j * ((N : ℝ)⁻¹ * 𝒯.side) = 𝒯.ξ
  rw [D.side_eq, D.mesh_eq]
  field_simp
theorem mem_sublattice_iff (u : PeriodicLattice.Torus 4 N) :
    u ∈ PeriodicLattice.gridSubgroup 4 S.fineMesh ↔
      D.dilateEquiv u ∈ Torus.spacingLattice 4 𝒯.side 𝒯.ξ := by
  have hmap (k : ℤ) : AddCircle.equivAddCircle (N : ℝ) 𝒯.side D.period_ne_zero D.side_ne_zero
      (k • ((S.fineMesh.h : ℝ) : AddCircle (N : ℝ))) = (((k : ℝ) * 𝒯.ξ : ℝ) : AddCircle 𝒯.side) := by
    rw [map_zsmul, D.circle_mesh_eq, ← zsmul_eq_mul, AddCircle.coe_zsmul]
  constructor
  · intro hu
    have h (μ : Fin 4) : ∃ k : ℤ, k • ((S.fineMesh.h : ℝ) : AddCircle (N : ℝ)) = u μ :=
      AddSubgroup.mem_zmultiples_iff.mp (hu μ (mem_univ μ))
    choose k hk using h
    refine ⟨k, funext fun μ => ?_⟩
    change AddCircle.equivAddCircle (N : ℝ) 𝒯.side D.period_ne_zero D.side_ne_zero (u μ) = _
    rw [← hk μ, hmap]
    rfl
  · rintro ⟨k, hk⟩ μ _
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k μ, ?_⟩
    apply (AddCircle.equivAddCircle (N : ℝ) 𝒯.side D.period_ne_zero D.side_ne_zero).injective
    rw [hmap]
    exact (congrFun hk μ).symm
def fineSiteEquiv : PeriodicLattice.DilatedSite 4 S.fineMesh r ≃ 𝒯.FineSite :=
  (PeriodicLattice.DilatedSite.equivSite S.fineMesh r).trans
    (D.dilateEquiv.toEquiv.subtypeEquiv D.mem_sublattice_iff)
def pullSite (f : 𝒯.FineSite → ℝ) : PeriodicLattice.DilatedFun 4 S.fineMesh r :=
  fun x => f (D.fineSiteEquiv x)
def pullBond (A : 𝒯.FineBond → ℝ) : PeriodicLattice.DilatedOneForm 4 S.fineMesh r :=
  fun q => A ⟨D.fineSiteEquiv q.2, q.1⟩
def pushBond (B : PeriodicLattice.DilatedOneForm 4 S.fineMesh r) : 𝒯.FineBond → ℝ :=
  fun b => B (b.dir, D.fineSiteEquiv.symm b.source)
def pullTensorOne (J : 𝒯.Tensor 1) :
    PeriodicLattice.DilatedField 4 S.fineMesh r (Fin 4 × Fin 4) :=
  fun q => J (RegionSequence.NestedRegions.constIdx q.1.1) ⟨D.fineSiteEquiv q.2, q.1.2⟩
def pullTensorTwo (J : 𝒯.Tensor 2) :
    PeriodicLattice.DilatedField 4 S.fineMesh r (Fin 4 × Fin 4 × Fin 4) :=
  fun q => J ![q.1.1, q.1.2.1] ⟨D.fineSiteEquiv q.2, q.1.2.2⟩
def coarseTrace : Set (PeriodicLattice.GridPoint 4 S.coarseMesh) :=
  {y | D.dilateEquiv (y : PeriodicLattice.Torus 4 N) ∈ 𝒯.Ω (j + 1)}
end DilationData
open Classical in
def centeredAvgPart (S : PeriodicLattice.Scales 4 L j N)
    (Λ' : Set (PeriodicLattice.GridPoint 4 S.coarseMesh)) (r r' a : ℝ)
    (A : PeriodicLattice.DilatedOneForm 4 S.fineMesh r) : ℝ :=
  a * r ^ (4 - 2) * ∑ b with b ∈ PeriodicLattice.linksAvoiding (S.centeredRegion Λ'),
      |S.centeredFineFormAvg (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) A) b| ^ 2 +
    a * r' ^ (4 - 2) * ∑ c with c ∈ PeriodicLattice.linksMeeting Λ',
      |S.centeredCoarseFormAvg
        (S.centeredFineFormAvg (PeriodicLattice.dilateFieldEquiv S.fineMesh r (Fin 4) A)) c| ^ 2
end YangMills.Construction.BareDilation
