import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Lattice.BlocksBoxesAndPaths
import YangMills.Construction.Lattice.ContourFamiliesAndCombsInABlock
import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomy
import YangMills.Construction.RunningCouplingSlope.CovarianceOfThePlainAverage
import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
theorem det_eq_one_of_mem_complexGaugeGroup {g : Matrices.ComplexMatrix2}
    (h : g ∈ PeriodicLattice.complexGaugeGroup) : Matrix.det g = 1 := h
theorem inv_mul_cancel_of_mem_complexGaugeGroup {g : Matrices.ComplexMatrix2}
    (h : g ∈ PeriodicLattice.complexGaugeGroup) : g⁻¹ * g = 1 := by apply _root_.YangMills.DeltaSharedProofs.p40097 <;> assumption
theorem contourMeanGaugeCovariant_holds (hlegs : AxisOrderLegsAreContours)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    ContourMeanGaugeCovariant := by
  intro L hL n k j hn hj V hV v hv c hc
  have hLpos : 0 < L := by have := hL.2; omega
  have hK : 0 < k := by omega
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  have hcross := (hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj |>.2.1 c hc
  have hjm : -(n : ℤ) ≤ PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]; omega
  have hgauge := fun (Γ : List (Edge L n k j)) (x x' : Vertex L n k j)
      (h : PeriodicLattice.IsBondPathFromTo Γ x x') =>
    (hg L n hL.1 hL.2 hn (PeriodicLattice.levelDepth k j) hjm Set.univ V v v
      (fun b _ => trivial) hV hv hv).2.1 Γ x x' h (fun _ _ => trivial)
  have hleg : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j), (x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock y → ∀ π, PeriodicLattice.IsBondPathFromTo (contourLeg y x π)
        (y.toSublattice (PeriodicLattice.levelDepth k j)) x := by
    intro y x hx π
    obtain ⟨σ, hσ⟩ := hlegs L n _ _ y x π
    have := ((hcf L n k hL hn j hj y x hx).2.1 _ ⟨σ, rfl⟩).1
    rw [← hσ] at this
    exact this
  have hcv : ∀ x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)), ∀ π, contourHolonomy (PeriodicLattice.gaugeTransform v V) c x π =
      v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * contourHolonomy V c x π *
        (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ := by
    intro x hx π
    have hx' : PeriodicLattice.shiftAcross c x ∈ (PeriodicLattice.sitesInBlock
        (PeriodicLattice.levelDepth k j) c.target : Set (Vertex L n k j)) := hcross.1.mapsTo hx
    rw [contourHolonomy, contourHolonomy, hgauge _ _ _ (hleg _ _ hx π),
      hgauge _ _ _ (hcross.2 x hx).1, hgauge _ _ _ (hleg _ _ hx' π)]
    have a1 : ∀ M : Matrices.ComplexMatrix2, (v x)⁻¹ * (v x * M) = M := fun M => by
      rw [← mul_assoc, inv_mul_cancel_of_mem_complexGaugeGroup (hv x), one_mul]
    have a2 : ∀ M : Matrices.ComplexMatrix2, (v (PeriodicLattice.shiftAcross c x))⁻¹ *
        (v (PeriodicLattice.shiftAcross c x) * M) = M := fun M => by
      rw [← mul_assoc, inv_mul_cancel_of_mem_complexGaugeGroup (hv _), one_mul]
    have hu : IsUnit (Matrix.det (v (PeriodicLattice.shiftAcross c x))) := by
      rw [det_eq_one_of_mem_complexGaugeGroup (hv _)]; exact isUnit_one
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu]
    simp only [mul_assoc, a1, a2]
  have h1 : contourMean (PeriodicLattice.gaugeTransform v V) c =
      v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * contourMean V c *
        (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ := by
    rw [contourMean, contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    exact hcv x (by simpa using hx) π
  have h2 : meanRadius (PeriodicLattice.gaugeTransform v V) c = meanRadius V c := by
    rw [meanRadius, meanRadius, h1, Matrix.det_mul, Matrix.det_mul,
      det_eq_one_of_mem_complexGaugeGroup (hv _),
      Matrix.det_nonsing_inv, det_eq_one_of_mem_complexGaugeGroup (hv _)]
    simp
  refine ⟨h1, h2, ?_⟩
  rw [normalizedMean, normalizedMean, h2, h1, Matrix.mul_smul, Matrix.smul_mul]
end YangMills.Construction.RunningCouplingSlope
end
