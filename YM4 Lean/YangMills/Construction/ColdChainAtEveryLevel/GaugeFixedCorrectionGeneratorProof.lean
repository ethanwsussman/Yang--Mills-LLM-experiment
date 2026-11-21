import YangMills.Construction.ColdChainAtEveryLevel.GaugeFixedCorrectionGenerator
import YangMills.Construction.ColdChainAtEveryLevel.GeneratorsOfAFramingOnACell
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.PinnedCorrection
variable {F : BlockFrame}
def adjointImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨adjointAction g (w : ℍ[ℝ]), re_adjointAction g w.2⟩
theorem smul_adjointImaginary (t : ℝ) (g : UnitQuaternion) (w : imaginaryQuaternions) :
    t • adjointImaginary g w = adjointImaginary g (t • w) := by
  apply Subtype.ext
  show t • adjointAction g (w : ℍ[ℝ]) = adjointAction g (t • (w : ℍ[ℝ]))
  rw [PatchForms.adjointAction_apply_smul]
theorem expUnit_adjointImaginary (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (adjointImaginary g w) = g * expUnit w * g⁻¹ := by
  apply Subtype.ext
  let u : (ℍ[ℝ])ˣ := ⟨(g : ℍ[ℝ]), ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), by
    rw [← Submonoid.coe_mul, mul_inv_cancel]
    rfl, by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl⟩
  show NormedSpace.exp ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
    (g : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  letI : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
  have h := NormedSpace.exp_units_conj u (w : ℍ[ℝ])
  convert h
  all_goals rfl
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem siteGauge_rotateAlong (ξ : LatticeFractionalIntegration.Lattice4 → imaginaryQuaternions) (t : ℝ)
    (γ : LatticeFractionalIntegration.Lattice4 → UnitQuaternion) :
    PatchLatticeChart.siteGaugeOfLatticeGauge S V z (PinnedGauge.PinnedGaugeData.rotateAlong ξ t γ) =
      rotatedBaseGauge (fun s => adjointImaginary (GaugeMap.frameChange S V z s) (ξ (GaugeMap.patchChart S z s))) t
        (PatchLatticeChart.siteGaugeOfLatticeGauge S V z γ) := by
  funext s
  unfold PatchLatticeChart.siteGaugeOfLatticeGauge rotatedBaseGauge PinnedGauge.PinnedGaugeData.rotateAlong
  rw [smul_adjointImaginary, expUnit_adjointImaginary]
  group
set_option maxHeartbeats 2000000 in
theorem pinnedCorrectionGenerator_holds (hVar : pinnedGaugeVariationStatement)
    (hGen : cellGeneratorNearBlockMeanStatement) :
    pinnedCorrectionGeneratorStatement := by
  classical
  intro F m S V W kW X k γ ξ z y q r E hodd h5 hamb hm hreg hz hy hq hr he8 hE0 hEs hk hleg hgap hne
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  set Γ0 := PatchLatticeChart.siteGaugeOfLatticeGauge S V z γ with hΓ0
  let ξs : F.Site 0 → imaginaryQuaternions :=
    fun s => adjointImaginary (GaugeMap.frameChange S V z s) (ξ (GaugeMap.patchChart S z s))
  have hyn : y ∈ sitesOfCells (patchCells S z) F.top := mem_sitesOfCells_top.2 hy
  obtain ⟨hre, hder⟩ := (hVar F W kW X k Γ0 ξs (patchCells S z) hodd hne).2 y hyn
  have hb := hGen F m S V W kW X k Γ0 ξs z y q r E hodd h5 hamb hm hreg hy hq hr he8 hE0 hEs hk hleg hgap hne
  set G := pinnedGaugeGenerator W kW X k Γ0 (fun x => (ξs x : ℍ[ℝ])) F.top y with hG
  set fr := patchFrame S V z y with hfr
  refine ⟨adjointAction fr⁻¹ G, re_adjointAction _ hre, ?_, ?_⟩
  · have e1 : (fun t : ℝ => ((pinnedTopCorrection S V z W kW X k
          (PinnedGauge.PinnedGaugeData.rotateAlong ξ t γ) y : UnitQuaternion) : ℍ[ℝ])) = fun t : ℝ =>
        ((fr⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((topCorrection W kW X k
          (pinnedGaugeOfBase W kW X k (rotatedBaseGauge ξs t Γ0)) y : UnitQuaternion) : ℍ[ℝ]) *
          (fr : ℍ[ℝ]) := by
      funext t
      unfold pinnedTopCorrection
      rw [siteGauge_rotateAlong]
      rfl
    rw [e1]
    refine ((hder.const_mul ((fr⁻¹ : UnitQuaternion) : ℍ[ℝ])).mul_const (fr : ℍ[ℝ])).congr_deriv ?_
    have h1 : ((((fr⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])) * ((fr⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel]
      rfl
    show _ = (((fr⁻¹ : UnitQuaternion) : ℍ[ℝ]) * G * (((fr⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
      (((fr⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        ((topCorrection W kW X k (pinnedGaugeOfBase W kW X k Γ0) y : UnitQuaternion) : ℍ[ℝ]) * (fr : ℍ[ℝ]))
    calc _ = ((fr⁻¹ : UnitQuaternion) : ℍ[ℝ]) * G *
          ((((fr⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((fr⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
          ((topCorrection W kW X k (pinnedGaugeOfBase W kW X k Γ0) y : UnitQuaternion) : ℍ[ℝ]) *
            (fr : ℍ[ℝ]) := by
          rw [h1, mul_one]
          simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  · have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    have hinj : Set.InjOn (fun h : LatticeFractionalIntegration.Lattice4 =>
        GaugeMap.patchChart S z (cellCentre 0 y + siteOfCoords 0 h))
        (centredCube (F.blockSide ^ F.top) : Set LatticeFractionalIntegration.Lattice4) := by
      intro h hh h' hh' e
      have e1 : cellCentre 0 y + siteOfCoords 0 h = cellCentre 0 y + siteOfCoords 0 h' := by
        have := congrArg (GaugeMap.patchSite S z) e
        simpa only [PatchPoints.patchSite_patchChart hs] using this
      exact PatchPotentials.siteOfCoords_injOn_centredCube hamb hodd hh hh' (add_left_cancel e1)
    have hmean : (pinnedGaugeDataOfPatch S V z W kW X k).cellMean y (fun x => (ξ x : ℍ[ℝ])) =
        (1 / ((F.blockSide : ℝ) ^ F.top) ^ 4) •
        ∑ h ∈ centredCube (F.blockSide ^ F.top),
          adjointAction (GaugeMap.frameChange S V z (cellCentre 0 y + siteOfCoords 0 h))⁻¹
          (ξs (cellCentre 0 y + siteOfCoords 0 h) : ℍ[ℝ]) := by
      show (1 / ((F.blockSide ^ F.top : ℕ) : ℝ) ^ 4) • ∑ x ∈ (centredCube (F.blockSide ^ F.top)).image
        (fun h => GaugeMap.patchChart S z (cellCentre 0 y + siteOfCoords 0 h)), (ξ x : ℍ[ℝ]) = _
      rw [Finset.sum_image hinj]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      show _ = adjointAction (GaugeMap.frameChange S V z (cellCentre 0 y + siteOfCoords 0 h))⁻¹
        (adjointAction (GaugeMap.frameChange S V z (cellCentre 0 y + siteOfCoords 0 h)) _)
      rw [PatchForms.adjointAction_inv_apply_apply]
    rw [hmean]
    refine hb.trans (le_of_eq ?_)
    have hsum : ∑ x ∈ sitesOfCells ({y} : Finset F.Cell) 0, ‖(ξs x : ℍ[ℝ])‖ ^ 4 =
        ∑ x ∈ (pinnedGaugeDataOfPatch S V z W kW X k).cellSites y, ‖(ξ x : ℍ[ℝ])‖ ^ 4 := by
      show _ = ∑ x ∈ (centredCube (F.blockSide ^ F.top)).image
        (fun h => GaugeMap.patchChart S z (cellCentre 0 y + siteOfCoords 0 h)), ‖(ξ x : ℍ[ℝ])‖ ^ 4
      rw [Finset.sum_image hinj]
      have e2 : sitesOfCells ({y} : Finset F.Cell) 0 = (centredCube (F.blockSide ^ F.top)).image
          fun h => cellCentre (F := F) 0 y + siteOfCoords 0 h := by
        simp [sitesOfCells]
      rw [e2, Finset.sum_image (fun h hh h' hh' e =>
        PatchPotentials.siteOfCoords_injOn_centredCube hamb hodd hh hh' (add_left_cancel e))]
      refine Finset.sum_congr rfl fun h _ => ?_
      show ‖adjointAction _ _‖ ^ 4 = _
      rw [norm_adjointAction]
    rw [hsum]
    show _ = _ / ((F.blockSide ^ F.top : ℕ) : ℝ) ^ 4
    push_cast
    rfl
end YangMills.Construction.BlockAverages.PinnedCorrection
end
