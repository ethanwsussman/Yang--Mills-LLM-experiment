import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.GaugeCovarianceOfAContour
import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAGauge
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace ShareGaugeInvariance
open ChartCoordinates
variable {F : BlockFrame} {S : Finset F.Cell}
theorem re_conj_eq (g : UnitQuaternion) (q : UnitQuaternion) :
    ((g * q * g⁻¹ : UnitQuaternion) : ℍ[ℝ]).re = (q : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.TorusFields.re_unitQuaternion_conj <;> assumption
def cellGaugeChain (γ : F.Cell → UnitQuaternion) (X : F.FieldChain) : F.FieldChain :=
  fun j => gaugeTransform (fun x => γ (enclosingCell x)) (X j)
theorem zero_mem_centredCube {L : ℕ} (hodd : Odd L) : (0 : Fin 4 → ℤ) ∈ centredCube L := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.zero_mem_centredCube <;> assumption
theorem enclosingCell_top (y : F.Cell) : enclosingCell y = y := by apply _root_.YangMills.Construction.PotentialMeans.enclosingCell_self <;> assumption
theorem enclosingCell_refineSite (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1)) : enclosingCell (refineSite y) = enclosingCell y := by
  obtain ⟨z, hz, h, hh, rfl⟩ := mem_sitesOfCells.1 hy
  have e : F.top - j = (F.top - (j + 1)) + 1 := by omega
  have hs : (fun i => (F.blockSide : ℤ) * h i) ∈ centredCube (F.blockSide ^ (F.top - j)) := by
    rw [e]
    have := scale_add_mem_centredCube hodd hh (zero_mem_centredCube hodd)
    simpa using this
  rw [refineSite_add j hj, refineSite_cellCentre j hj, LocalPartition.enclosingCell_cellCentre_add hodd z _ hs,
    LocalPartition.enclosingCell_cellCentre_add hodd z _ hh]
theorem cellGaugeChain_top (γ : F.Cell → UnitQuaternion) (X : F.FieldChain) :
    cellGaugeChain γ X F.top = gaugeTransform γ (X F.top) := by
  funext y i
  simp only [cellGaugeChain, gaugeTransform, enclosingCell_top]
variable (hG : gaugeCovarianceStatement) (hodd : Odd F.blockSide)
include hG hodd
theorem plaquetteHolonomy_re_cellGaugeChain (γ : F.Cell → UnitQuaternion) (X : F.FieldChain)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    ((plaquetteHolonomy (cellGaugeChain γ X 0) p : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re := by
  have h0 : 0 < F.top := Nat.succ_pos _
  rw [show cellGaugeChain γ X 0 = gaugeTransform (fun x => γ (enclosingCell x)) (X 0) from rfl,
    (hG F 0 h0 hodd.pos).2.2.1]
  exact re_conj_eq _ _
theorem blockFit_cellGaugeChain (γ : F.Cell → UnitQuaternion) (X : F.FieldChain) {j : ℕ} (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    blockFit (cellGaugeChain γ X j) (cellGaugeChain γ X (j + 1)) c = blockFit (X j) (X (j + 1)) c := by
  have h := innerBonds_ends hc
  exact (hG F j hj hodd.pos).2.2.2 _ _ _ _ c (by rw [enclosingCell_refineSite hodd hj h.1])
    (by rw [enclosingCell_refineSite hodd hj h.2])
theorem chainAction_cellGaugeChain (a : ℝ) (γ : F.Cell → UnitQuaternion) (X : F.FieldChain) :
    chainAction a S (cellGaugeChain γ X) = chainAction a S X := by
  have e0 : wilsonAction S (cellGaugeChain γ X 0) = wilsonAction S (X 0) :=
    Finset.sum_congr rfl fun p _ => by rw [plaquetteHolonomy_re_cellGaugeChain hG hodd]
  have e1 : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
        blockFit (cellGaugeChain γ X j) (cellGaugeChain γ X (j + 1)) c =
      ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), blockFit (X j) (X (j + 1)) c :=
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc =>
      blockFit_cellGaugeChain hG hodd γ X (Finset.mem_range.1 hj) hc
  unfold chainAction
  rw [e0, e1]
theorem cellShare_cellGaugeChain (a : ℝ) (Y : F.Cell) (γ : F.Cell → UnitQuaternion) (X : F.FieldChain) :
    cellShare a S Y (cellGaugeChain γ X) = cellShare a S Y X := by
  classical
  have e0 : ∑ p ∈ innerPlaquettes S 0,
        (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (cellGaugeChain γ X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes S 0,
        (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) :=
    Finset.sum_congr rfl fun p _ => by rw [plaquetteHolonomy_re_cellGaugeChain hG hodd]
  have e1 : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
        ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
        blockFit (cellGaugeChain γ X j) (cellGaugeChain γ X (j + 1)) c =
      ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
        ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
        blockFit (X j) (X (j + 1)) c :=
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => by
      rw [blockFit_cellGaugeChain hG hodd γ X (Finset.mem_range.1 hj) hc]
  unfold cellShare
  rw [e0, e1]
end ShareGaugeInvariance
theorem gaugeInvarianceOfShare (hG : gaugeCovarianceStatement) (hV : minimalChainExistenceStatement) :
    gaugeInvarianceOfShareStatement := by
  intro F a S V γ ha hodd hone Y
  have hback : ∀ V₁ : F.GaugeField F.top, gaugeTransform (fun y => (γ y)⁻¹) (gaugeTransform γ V₁) = V₁ := by
    intro V₁
    funext y i
    simp only [gaugeTransform]
    group
  refine minimalCellShare_eq_of_chainMap (V := V) (V' := gaugeTransform γ V)
    (ShareGaugeInvariance.cellGaugeChain γ)
    (ShareGaugeInvariance.cellGaugeChain fun y => (γ y)⁻¹) (fun X hX => ?_) (fun X hX => ?_)
    (fun X _ => ShareGaugeInvariance.chainAction_cellGaugeChain hG hodd a γ X)
    (fun X _ => ShareGaugeInvariance.chainAction_cellGaugeChain hG hodd a _ X)
    (fun X _ => ShareGaugeInvariance.cellShare_cellGaugeChain hG hodd a Y _ X) ?_ (fun X hX => hone X hX Y)
  · rw [ShareGaugeInvariance.cellGaugeChain_top, hX]
  · rw [ShareGaugeInvariance.cellGaugeChain_top, hX, hback]
  · obtain ⟨X, hX, -⟩ := (hV F a S ha).2.2.2 (gaugeTransform γ V)
    exact ⟨X, hX⟩
end YangMills.Construction.BlockAverages
end
