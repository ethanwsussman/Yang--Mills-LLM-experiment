import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheSharesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ChartedEnergyCoordinates
theorem sum_imaginaryCoord_smul_imaginaryUnit (w : imaginaryQuaternions) :
    ∑ α, imaginaryCoord α w • imaginaryUnit α = w := by
  apply Subtype.ext
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [Fin.sum_univ_three, imaginaryCoord, imaginaryUnit, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_add, Submodule.coe_smul]
  ext
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    rw [hre]
    ring
  · change (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    ring
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    ring
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    ring
theorem mem_finiteCells (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
theorem mem_sitesOfCells_top (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) :
    z ∈ sitesOfCells (finiteCells F) F.top := by
  classical
  unfold sitesOfCells
  rw [Finset.mem_biUnion]
  refine ⟨z, mem_finiteCells hext z, ?_⟩
  rw [Finset.mem_image]
  refine ⟨0, ?_, ?_⟩
  · unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    simp
  · funext i
    simp only [cellCentre, siteOfCoords, Nat.sub_self, pow_zero, one_mul, Pi.add_apply, Pi.zero_apply,
      Int.cast_zero, add_zero]
    exact ZMod.intCast_zmod_cast (z i)
theorem mem_innerBonds_top (hext : ∀ i, 2 ≤ F.extent i) (b : F.Site F.top × Fin 4) :
    b ∈ innerBonds (finiteCells F) F.top := by
  classical
  unfold innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨mem_sitesOfCells_top hext _, mem_sitesOfCells_top hext _⟩
theorem sum_comp_chartCoordinateEquiv_symm {M : Type} [AddCommMonoid M]
    (f : ChartCoordinateIndex F → M) :
    ∑ n, f ((chartCoordinateEquiv F).symm n) = ∑ ι, f ι :=
  (chartCoordinateEquiv F).symm.sum_comp f
theorem sum_directionMove_chartCoordinates (hext : ∀ i, 2 ≤ F.extent i)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    (fun y i => ∑ l, chartCoordinates dw dv l • directionMove (chartDirections F l) y i) = dv := by
  classical
  funext y i
  have hsum : ∑ l, chartCoordinates dw dv l • directionMove (chartDirections F l) y i =
      ∑ ι : ChartCoordinateIndex F, coordinateOfIndex dw dv ι • directionMove (directionOfIndex ι) y i :=
    sum_comp_chartCoordinateEquiv_symm
      (fun ι => coordinateOfIndex dw dv ι • directionMove (directionOfIndex ι) y i)
  rw [hsum, Fintype.sum_sum_type]
  simp only [coordinateOfIndex, directionOfIndex, directionMove, smul_zero, Finset.sum_const_zero,
    zero_add]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single
    (⟨(y, i), mem_innerBonds_top hext _⟩ : ↥(innerBonds (finiteCells F) F.top))]
  · simp only [and_self, if_true]
    exact sum_imaginaryCoord_smul_imaginaryUnit _
  · intro b _ hb
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [if_neg, smul_zero]
    rintro ⟨h₁, h₂⟩
    exact hb (Subtype.ext (Prod.ext h₁ h₂))
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem sum_directionCoordinate_chartCoordinates
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4)
    (hb : (x, i) ∈ chordBonds (finiteCells F)) :
    ∑ l, chartCoordinates dw dv l • directionCoordinate (chartDirections F l) x i = dw x i := by
  classical
  have hsum : ∑ l, chartCoordinates dw dv l • directionCoordinate (chartDirections F l) x i =
      ∑ ι : ChartCoordinateIndex F,
        coordinateOfIndex dw dv ι • directionCoordinate (directionOfIndex ι) x i :=
    sum_comp_chartCoordinateEquiv_symm
      (fun ι => coordinateOfIndex dw dv ι • directionCoordinate (directionOfIndex ι) x i)
  rw [hsum, Fintype.sum_sum_type]
  simp only [coordinateOfIndex, directionOfIndex, directionCoordinate, smul_zero,
    Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨(x, i), hb⟩ : ↥(chordBonds (finiteCells F)))]
  · simp only [and_self, if_true]
    exact sum_imaginaryCoord_smul_imaginaryUnit _
  · intro b _ hne
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [if_neg, smul_zero]
    rintro ⟨h₁, h₂⟩
    exact hne (Subtype.ext (Prod.ext h₁ h₂))
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem chartedField_congr (hcover : BlocksCoverLowerLevel) (hodd : Odd F.blockSide)
    (hext : ∀ i, 2 ≤ F.extent i)
    (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (h : ∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w' b.1 b.2) :
    chartedField w V = chartedField w' V := by
  classical
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hext i; omega
  funext x i
  unfold chartedField
  have hmem : ¬ IsAxialTreeBond (x, i) → (x, i) ∈ chordBonds (finiteCells F) := by
    intro ht
    unfold chordBonds innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hcover F hodd hpos _, hcover F hodd hpos _⟩, ht⟩
  by_cases hcr : IsCrossingBond (x, i)
  · simp only [if_pos hcr]
    rw [h (x, i) (hmem fun ht => ht.1 hcr)]
  · simp only [if_neg hcr]
    by_cases ht : IsAxialTreeBond (x, i)
    · simp only [if_pos ht]
    · simp only [if_neg ht]
      rw [h (x, i) (hmem ht)]
end ChartedEnergyCoordinates
open ChartedEnergyCoordinates in
theorem chartedEnergyInCoordinates_of_blocksCover (hcover : BlocksCoverLowerLevel) :
    ChartedEnergyInCoordinates := by
  classical
  intro F a w dw V dv hodd hext
  refine ⟨?_, fun σ => ?_⟩
  · unfold chartRestriction chartedEnergy
    rw [sum_directionMove_chartCoordinates hext,
      chartedField_congr hcover hodd hext _ (fun x i => w x i + dw x i) _ fun b hb => by
        rw [sum_directionCoordinate_chartCoordinates dw dv b.1 b.2 hb]]
  · unfold chartRestriction chartedEnergy
    have hmove : (fun y i => ∑ l, (chartCoordinates dw (fun _ _ => 0) + σ) l •
          directionMove (chartDirections F l) y i) =
        fun y i => ∑ l, σ l • directionMove (chartDirections F l) y i := by
      funext y i
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      have := congrFun (congrFun (sum_directionMove_chartCoordinates hext dw (fun _ _ => 0)) y) i
      rw [this, zero_add]
    rw [hmove, chartedField_congr hcover hodd hext _
      (fun x i => (w x i + dw x i) + ∑ l, σ l • directionCoordinate (chartDirections F l) x i) _
      fun b hb => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        rw [sum_directionCoordinate_chartCoordinates dw (fun _ _ => 0) b.1 b.2 hb, add_assoc]]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
