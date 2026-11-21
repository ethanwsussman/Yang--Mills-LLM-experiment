import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionsAndExponentialsUnderALatticeIsometry
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace FaceCovariance
variable {a : ℝ}
theorem smearedEnergy_eq_finset_sum (f : AmbientSpace → ℂ) (U : GaugeField a)
    (s : Finset (ElementaryPlaquette a))
    (hs : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ s) :
    smearedEnergy f U = ∑ p ∈ s, faceEnergy U p • f p.center := by
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  refine hs p fun h0 => ?_
  exact hp (by simp [h0])
theorem smearedEnergy_pullbackField (r : LatticeSymmetry a)
    (hbij : Function.Bijective r.plaquetteMap)
    (hact : ∀ p : ElementaryPlaquette a, r.actOn (fun U : GaugeField a => faceEnergy U p) =
      fun U : GaugeField a => faceEnergy U (r.plaquetteMap p))
    (hcen : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center)
    (f : AmbientSpace → ℂ) (U : GaugeField a) :
    smearedEnergy f (r.pullbackField U) = smearedEnergy (r.pushforwardFun f) U := by
  change (∑ᶠ p : ElementaryPlaquette a, faceEnergy (r.pullbackField U) p • f p.center) =
    ∑ᶠ p : ElementaryPlaquette a, faceEnergy U p • r.pushforwardFun f p.center
  refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective _ hbij)
    (f := fun p : ElementaryPlaquette a => faceEnergy U p • r.pushforwardFun f p.center))
  refine finsum_congr fun p => ?_
  have h := congrFun (hact p) U
  change faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p) at h
  rw [h, Equiv.ofBijective_apply, hcen p, LatticeSymmetry.pushforwardFun_apply_toFun]
end FaceCovariance
open FaceCovariance in
theorem faceEnergyAndExponentialCovariance_holds
    (hMoves : GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes)
    (hSmear : SmearedEnergyAndSymmetryAction.Main) :
    FaceEnergyAndExponentialCovariance := by
  intro a ha r _
  obtain ⟨-, -, hP⟩ := hMoves a ha
  obtain ⟨-, hbij, -, hact, hcen, -⟩ := hP r
  have hfin := (hSmear a ha).1.1
  refine ⟨fun p => ⟨hcen p, hact p, fun U => congrFun (hact p) U⟩, fun v v' hv hv' => ?_⟩
  obtain ⟨h, -⟩ := hfin v hv
  obtain ⟨h', -⟩ := hfin v' hv'
  refine ⟨?_, ?_, ?_⟩
  · funext U
    change Complex.exp (smearedEnergy v (r.pullbackField U)) = _
    rw [smearedEnergy_pullbackField r hbij hact hcen]
  · funext U
    rw [← Complex.exp_conj]
    congr 1
    rw [smearedEnergy_eq_finset_sum v U h.toFinset (fun p hp => h.mem_toFinset.mpr hp),
      smearedEnergy_eq_finset_sum (fun x => conj (v x)) U h.toFinset (fun p hp => h.mem_toFinset.mpr
        fun h0 => hp (by simp [h0])), map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Complex.real_smul]
  · classical
    funext U
    rw [← Complex.exp_add]
    congr 1
    have hs : ∀ p : ElementaryPlaquette a, v p.center ≠ 0 → p ∈ h.toFinset ∪ h'.toFinset :=
      fun p hp => Finset.mem_union_left _ (h.mem_toFinset.mpr hp)
    have hs' : ∀ p : ElementaryPlaquette a, v' p.center ≠ 0 → p ∈ h.toFinset ∪ h'.toFinset :=
      fun p hp => Finset.mem_union_right _ (h'.mem_toFinset.mpr hp)
    have hs'' : ∀ p : ElementaryPlaquette a, (v + v') p.center ≠ 0 →
        p ∈ h.toFinset ∪ h'.toFinset := by
      intro p hp
      by_cases h0 : v p.center = 0
      · refine hs' p fun h1 => hp ?_
        simp [h0, h1]
      · exact hs p h0
    rw [smearedEnergy_eq_finset_sum v U _ hs, smearedEnergy_eq_finset_sum v' U _ hs',
      smearedEnergy_eq_finset_sum (v + v') U _ hs'', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [smul_add]
end YangMills.Construction.InfiniteLattice
