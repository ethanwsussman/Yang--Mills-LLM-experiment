import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
abbrev UnitQuaternion : Type := unitary ℍ[ℝ]
def imaginaryQuaternions : Submodule ℝ ℍ[ℝ] where
  carrier := {q | q.re = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    simp [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    simp [ha]
theorem exp_imaginary_mem_unitary (w : imaginaryQuaternions) :
    NormedSpace.exp (w : ℍ[ℝ]) ∈ unitary ℍ[ℝ] := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  have hn : ‖NormedSpace.exp (w : ℍ[ℝ])‖ = 1 := by
    rw [Quaternion.norm_exp, hw]
    simp
  have hs : Quaternion.normSq (NormedSpace.exp (w : ℍ[ℝ])) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hn]
    norm_num
  rw [Unitary.mem_iff]
  constructor
  · rw [Quaternion.star_mul_self, hs]
    simp
  · rw [Quaternion.self_mul_star, hs]
    simp
def expUnit (w : imaginaryQuaternions) : UnitQuaternion :=
  ⟨NormedSpace.exp (w : ℍ[ℝ]), exp_imaginary_mem_unitary w⟩
structure BlockFrame where
  blockSide : ℕ
  depth : ℕ
  extent : Fin 4 → ℕ
variable (F : BlockFrame)
abbrev BlockFrame.top : ℕ := F.depth + 1
def BlockFrame.period (j : ℕ) (i : Fin 4) : ℕ := F.extent i * F.blockSide ^ (F.top - j)
abbrev BlockFrame.Site (j : ℕ) : Type := (i : Fin 4) → ZMod (F.period j i)
abbrev BlockFrame.Cell : Type := F.Site F.top
abbrev BlockFrame.GaugeField (j : ℕ) : Type := F.Site j → Fin 4 → UnitQuaternion
variable {F}
def siteOfCoords (j : ℕ) (z : Fin 4 → ℤ) : F.Site j := fun i => (z i : ZMod (F.period j i))
def siteCoords {j : ℕ} (x : F.Site j) : Fin 4 → ℤ := fun i => ZMod.cast (x i)
def unitStep (j : ℕ) (i : Fin 4) : F.Site j := siteOfCoords j (Pi.single i 1)
abbrev PathStep : Type := Fin 4 × Bool
def stepDisplacement (j : ℕ) (st : PathStep) : F.Site j :=
  if st.2 then unitStep j st.1 else - unitStep j st.1
def linkValue {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) : UnitQuaternion :=
  if st.2 then X x st.1 else (X (x - unitStep j st.1) st.1)⁻¹
def pathHolonomy {j : ℕ} (X : F.GaugeField j) : F.Site j → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r => linkValue X x st * pathHolonomy X (x + stepDisplacement j st) r
def plaquetteHolonomy {j : ℕ} (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    UnitQuaternion :=
  pathHolonomy X p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
def centredCube (M : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(((M : ℤ) - 1) / 2)) (((M : ℤ) - 1) / 2)
def cellCentre (j : ℕ) (z : F.Cell) : F.Site j :=
  siteOfCoords j fun i => (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i
def refineSite {j : ℕ} (y : F.Site (j + 1)) : F.Site j :=
  siteOfCoords j fun i => (F.blockSide : ℤ) * siteCoords y i
def enclosingCell {j : ℕ} (x : F.Site j) : F.Cell :=
  siteOfCoords F.top fun i =>
    (siteCoords x i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j)
def cellSupDist (y z : F.Cell) : ℕ :=
  Finset.univ.sup fun i => ((y i - z i).valMinAbs).natAbs
def sitesOfCells (S : Finset F.Cell) (j : ℕ) : Finset (F.Site j) :=
  S.biUnion fun z =>
    (centredCube (F.blockSide ^ (F.top - j))).image fun h => cellCentre j z + siteOfCoords j h
def innerBonds (S : Finset F.Cell) (j : ℕ) : Finset (F.Site j × Fin 4) :=
  (sitesOfCells S j ×ˢ Finset.univ).filter fun b => b.1 + unitStep j b.2 ∈ sitesOfCells S j
def plaquetteCorners {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : Finset (F.Site j) :=
  {p.1, p.1 + unitStep j p.2.1, p.1 + unitStep j p.2.2,
    p.1 + unitStep j p.2.1 + unitStep j p.2.2}
def innerPlaquettes (S : Finset F.Cell) (j : ℕ) : Finset (F.Site j × Fin 4 × Fin 4) :=
  (sitesOfCells S j ×ˢ Finset.univ ×ˢ Finset.univ).filter fun p =>
    p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ sitesOfCells S j
def axisPath (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : List PathStep :=
  (List.finRange 4).flatMap fun k =>
    List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
def reversePath (l : List PathStep) : List PathStep := (l.reverse).map fun st => (st.1, !st.2)
def bondContour (L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) : List PathStep :=
  axisPath h π ++ List.replicate L (i, true) ++ reversePath (axisPath h π)
def contourAverage {j : ℕ} (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])
def blockFit {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : ℝ :=
  ‖contourAverage X c‖ - (contourAverage X c * ((X' c.1 c.2)⁻¹ : UnitQuaternion)).re
def wilsonAction (S : Finset F.Cell) (U : F.GaugeField 0) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, (1 - ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]).re)
def minimalAction (a : ℝ) (S : Finset F.Cell) : (j : ℕ) → F.GaugeField j → ℝ
  | 0, U => wilsonAction S U
  | j + 1, V => ⨅ W : F.GaugeField j,
      (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c)
def blockEnergy (a : ℝ) (S : Finset F.Cell) (t : ℕ) (W : F.GaugeField t)
    (V : F.GaugeField (t + 1)) : ℝ :=
  minimalAction a S t W + a * ∑ c ∈ innerBonds S (t + 1), blockFit W V c
end BlockAverages
end YangMills.Construction
end
