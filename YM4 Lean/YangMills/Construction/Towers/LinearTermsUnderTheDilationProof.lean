import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASide
import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import YangMills.Construction.Towers.DilationCarriesTheLatticesOfATower
import YangMills.Construction.Towers.GaugeFixingFunctionAsASumOfCosinesProof
import YangMills.Construction.Towers.LinearTermsUnderTheDilation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.CoboundaryScalingProof
variable {L n k j : ℕ}
theorem scaleEdge_forwardFrom (hL : 0 < L) (hj : j ≤ k) (l : ℕ) (x : Vertex L n k l) (μ : Fin 4) :
    scaleEdge hL hj l (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (scaleVertex hL hj l x) μ := by
  apply PeriodicLattice.Bond.ext
  · rfl
  · simp [scaleEdge, edgeEquivOfVertexEquiv, PeriodicLattice.Bond.forwardFrom, scaleVertex_unitStep]
theorem edgeCoboundary_transport (hL : 0 < L) (hj : j ≤ k) (l : ℕ)
    (B : Edge L n k l → Matrices.ComplexMatrix2) :
    edgeCoboundary (transportTotal (scaleEdge hL hj l) B) =
      transportTotal (scaleFace hL hj l) (edgeCoboundary B) := by
  funext p'
  obtain ⟨p, rfl⟩ := (scaleFace (n := n) hL hj l).surjective p'
  rw [transportTotal_apply]
  have hb : (scaleFace hL hj l p).origin = scaleVertex hL hj l p.origin := rfl
  have hf : (scaleFace hL hj l p).firstAxis = p.firstAxis := rfl
  have hs : (scaleFace hL hj l p).secondAxis = p.secondAxis := rfl
  simp only [edgeCoboundary, hb, hf, hs]
  rw [← scaleVertex_unitStep hL hj l p.firstAxis, ← scaleVertex_unitStep hL hj l p.secondAxis,
    ← map_add, ← map_add, ← scaleEdge_forwardFrom, ← scaleEdge_forwardFrom,
    ← scaleEdge_forwardFrom, ← scaleEdge_forwardFrom]
  simp only [transportTotal_apply]
theorem cubeCentre_spec {i : ℕ} (hS : BlocksPartitionFiner L n k (i + 1))
    (x : FineOnlyVertex L n k i) :
    x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) (cubeCentre x) ∧
      (x.1 : PeriodicLattice.FourTorus L n) ≠ cubeCentre x := by apply _root_.YangMills.SharedProofs.p27590 <;> assumption
theorem cubeCentre_eq_of_mem {i : ℕ} (hS : BlocksPartitionFiner L n k (i + 1))
    (x : FineOnlyVertex L n k i) (y : Vertex L n k (i + 1))
    (h₁ : x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y)
    (h₂ : (x.1 : PeriodicLattice.FourTorus L n) ≠ y) : cubeCentre x = y := by
  have hc := cubeCentre_spec hS x
  exact (hS.2.2 x.1 x.2).unique ⟨hc.1, hc.2⟩ ⟨h₁, h₂⟩
def fineOnlyScaling (hL : 0 < L) (hj : j ≤ k) (i : ℕ)
    (hlat : scaling hL n k j ''
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) =
      PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j (i + 1))) :
    FineOnlyVertex L n k i ≃ FineOnlyVertex L (scaledExponent n k j) j i :=
  (scaleVertex hL hj i).toEquiv.subtypeEquiv fun x => not_congr (by
    change _ ↔ scaling hL n k j x.1 ∈
      (PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j (i + 1)) :
        Set (PeriodicLattice.FourTorus L (scaledExponent n k j)))
    rw [← hlat]
    exact (Function.Injective.mem_set_image (scaling hL n k j).injective).symm)
theorem cubeCentre_fineOnlyScaling (hL : 0 < L) (hj : j ≤ k) {i : ℕ}
    (hlat : scaling hL n k j ''
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) =
      PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j (i + 1)))
    (hS : BlocksPartitionFiner L n k (i + 1))
    (hS' : BlocksPartitionFiner L (scaledExponent n k j) j (i + 1))
    (hI : ScalingPreservesAtLevel hL hj n (i + 1)) (x : FineOnlyVertex L n k i) :
    cubeCentre (fineOnlyScaling hL hj i hlat x) =
      scaleVertex hL hj (i + 1) (cubeCentre x) := by
  have hc := cubeCentre_spec hS x
  refine cubeCentre_eq_of_mem hS' _ _ ?_ ?_
  · change scaling hL n k j x.1 ∈ PeriodicLattice.refinedBlock 1 (scaleVertex hL hj (i + 1) _)
    rw [← hI.refinedBlock_image 1 (by omega)]
    exact ⟨_, hc.1, rfl⟩
  · intro h
    exact hc.2 ((scaling hL n k j).injective h)
theorem fineOnlyContourAverage_transport (hL : 0 < L) (hj : j ≤ k) {i : ℕ}
    (hlat : scaling hL n k j ''
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) =
      PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j (i + 1)))
    (hS : BlocksPartitionFiner L n k (i + 1))
    (hS' : BlocksPartitionFiner L (scaledExponent n k j) j (i + 1))
    (hI : ScalingPreservesAtLevel hL hj n (i + 1)) (hA : ScalingPreservesAtStep hL hj n i)
    (B : Edge L n k i → Matrices.ComplexMatrix2) (x : FineOnlyVertex L n k i) :
    fineOnlyContourAverage L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) B)
        (fineOnlyScaling hL hj i hlat x) =
      fineOnlyContourAverage L n k i B x := by
  simp only [fineOnlyContourAverage]
  rw [cubeCentre_fineOnlyScaling hL hj hlat hS hS' hI x]
  exact hA.contourFormAverage_eq _ _ B (cubeCentre_spec hS x).1
theorem traceFinsumNorm_eq_of_equiv {ι ι' : Type*} (e : ι ≃ ι') (f : ι → Matrices.ComplexMatrix2)
    (f' : ι' → Matrices.ComplexMatrix2) (h : ∀ x, f' (e x) = f x) :
    traceFinsumNorm f' = traceFinsumNorm f := by
  have hp : traceFinsumPairing f' f' = traceFinsumPairing f f := by
    simp only [traceFinsumPairing]
    rw [← finsum_comp_equiv e]
    simp only [h]
  simp only [traceFinsumNorm, hp]
theorem coboundaryScaling (h₁ : ScalingPreservesSublatticesAllSides)
    (h₂ : ScalingPreservesObjectsAtLevel.Statement)
    (h₃ : ScalingPreservesStepsAtSide.Statement)
    (h₄ : BlockStructure) : CoboundaryScaling.Statement := by
  intro L n k j hL hj hs hn hj1
  refine ⟨fun l _ B => edgeCoboundary_transport hL hj l B, fun i hi B => ?_⟩
  have hi' : i + 1 ≤ j := hi
  have hlat := ((h₁ L hL hs k j hj).1 n hn).image_sublattice (i + 1) hi'
  have hS : BlocksPartitionFiner L n k (i + 1) :=
    ((h₄ L k (i + 1) hs (by omega) (by omega) (by omega)).1 n hn).2.1
  have hS' : BlocksPartitionFiner L (scaledExponent n k j) j (i + 1) :=
    ((h₄ L j (i + 1) hs hj1 (by omega) hi').1 (scaledExponent n k j)
      (by simp only [scaledExponent]; omega)).2.1
  exact traceFinsumNorm_eq_of_equiv (fineOnlyScaling hL hj i hlat) _ _
    (fineOnlyContourAverage_transport hL hj hlat hS hS'
      ((h₂ L hL hs k j hj hj1 (i + 1) hi').1 n hn) (h₃ L hL hs k j hj hj1 i hi n hn) B)
end YangMills.Construction.Tower.CoboundaryScalingProof
end
