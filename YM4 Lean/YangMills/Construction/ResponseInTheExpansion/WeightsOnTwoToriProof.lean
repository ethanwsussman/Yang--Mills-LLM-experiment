import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoTori
import YangMills.Construction.ResponseInTheExpansion.WeightsThatAgreeAtABlockProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields StepSettings BlockOffsets TorusLumps BlockAverages
section PlaquetteVertices
private abbrev VertexSlot : Type := Fin 4 × Fin 4 × Bool × Bool
private def vertexSlots : Finset VertexSlot := Finset.univ.filter fun i => i.1 < i.2.1
private def slotOffset (i : VertexSlot) : Fin 4 → ℤ := fun j =>
  -(if i.2.2.1 = true ∧ j = i.1 then 1 else 0) - (if i.2.2.2 = true ∧ j = i.2.1 then 1 else 0)
variable {n : ℕ}
private theorem siteOfInt_slotOffset (μ ν : Fin 4) (a b : Bool) :
    (siteOfInt (slotOffset (μ, ν, a, b)) : TorusSite n) =
      -(if a = true then TorusFields.unitStep n μ else 0) -
        (if b = true then TorusFields.unitStep n ν else 0) := by
  funext j
  cases a <;> cases b <;> by_cases h1 : j = μ <;> by_cases h2 : j = ν <;>
    simp [siteOfInt, slotOffset, TorusFields.unitStep, Pi.single_apply, h1, h2]
abbrev _root_.YangMills.DeltaSharedProofs.p500697 := @siteOfInt_slotOffset
private def plaquetteAtVertex (y : TorusSite n) (i : VertexSlot) : TorusPlaquette n :=
  (y + siteOfInt (slotOffset i), i.1, i.2.1)
private theorem vertexMultiplicity_eq_sum (y x : TorusSite n) (μ ν : Fin 4) :
    vertexMultiplicity y (x, μ, ν) =
      ∑ ab : Bool × Bool, if x = y + siteOfInt (slotOffset (μ, ν, ab.1, ab.2)) then (1 : ℝ) else 0 := by
  have e0 : (x = y + siteOfInt (slotOffset (μ, ν, false, false))) ↔ x = y := by
    rw [siteOfInt_slotOffset]
    simp
  have e1 : (x = y + siteOfInt (slotOffset (μ, ν, true, false))) ↔
      x + TorusFields.unitStep n μ = y := by
    rw [siteOfInt_slotOffset]
    simp only [if_true, Bool.false_eq_true, if_false, sub_zero]
    exact ⟨fun h => by rw [h]; abel, fun h => by rw [← h]; abel⟩
  have e2 : (x = y + siteOfInt (slotOffset (μ, ν, false, true))) ↔
      x + TorusFields.unitStep n ν = y := by
    rw [siteOfInt_slotOffset]
    simp only [if_true, Bool.false_eq_true, if_false]
    exact ⟨fun h => by rw [h]; abel, fun h => by rw [← h]; abel⟩
  have e3 : (x = y + siteOfInt (slotOffset (μ, ν, true, true))) ↔
      x + TorusFields.unitStep n μ + TorusFields.unitStep n ν = y := by
    rw [siteOfInt_slotOffset]
    simp only [if_true]
    exact ⟨fun h => by rw [h]; abel, fun h => by rw [← h]; abel⟩
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [e0, e1, e2, e3, vertexMultiplicity, plaquetteVertices, List.count_cons, List.count_nil]
  simp only [beq_iff_eq]
  push_cast
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p502373 := @vertexMultiplicity_eq_sum
private theorem sum_vertexMultiplicity_mul [NeZero n] (y : TorusSite n) (F : TorusPlaquette n → ℝ) :
    ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * F p =
      ∑ i ∈ vertexSlots, F (plaquetteAtVertex y i) := by
  classical
  have h1 : plaquettesIn (Finset.univ : Finset (TorusSite n)) =
      Finset.univ.filter fun p : TorusPlaquette n => p.2.1 < p.2.2 := by
    ext p
    simp [plaquettesIn]
  rw [h1, Finset.sum_filter, vertexSlots, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hμν : μ < ν
  · simp only [hμν, if_true, vertexMultiplicity_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, add_mul,
      ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      plaquetteAtVertex]
  · simp [hμν]
abbrev _root_.YangMills.DeltaSharedProofs.p501550 := @sum_vertexMultiplicity_mul
private theorem mem_plaquetteVertices_plaquetteAtVertex (y : TorusSite n) (i : VertexSlot) :
    y ∈ plaquetteVertices (plaquetteAtVertex y i).1 (plaquetteAtVertex y i).2.1 (plaquetteAtVertex y i).2.2 := by
  rcases i with ⟨μ, ν, a, b⟩
  show y ∈ plaquetteVertices (y + siteOfInt (slotOffset (μ, ν, a, b))) μ ν
  rw [siteOfInt_slotOffset]
  unfold plaquetteVertices
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
  · left; abel
  · right; right; left; abel
  · right; left; abel
  · right; right; right; left; abel
abbrev _root_.YangMills.DeltaSharedProofs.p1878 := @mem_plaquetteVertices_plaquetteAtVertex
private theorem abs_slotOffset_le_one {i : VertexSlot} (hi : i ∈ vertexSlots) (j : Fin 4) :
    |slotOffset i j| ≤ 1 := by
  have hne : i.1 ≠ i.2.1 := ne_of_lt (Finset.mem_filter.mp hi).2
  unfold slotOffset
  by_cases e1 : j = i.1
  · have e2 : j ≠ i.2.1 := fun e => hne (e1.symm.trans e)
    by_cases a : i.2.2.1 = true <;> simp [e1, a, hne]
  · by_cases b : i.2.2.2 = true <;> by_cases e2 : j = i.2.1 <;> simp [e1, e2, b, hne.symm]
end PlaquetteVertices
section BlockScales
variable {L : ℕ}
variable [NeZero L]
private theorem weightsAgreeAt_fineSite (hodd : Odd L) (t n n' : ℕ) [NeZero n] [NeZero n']
    (y : TorusSite n) (y' : TorusSite n')
    (h : PlaquetteWeight (fineSide L (t + 1) n)) (h' : PlaquetteWeight (fineSide L (t + 1) n'))
    (hA : WeightsAgreeAt L (t + 1) y y' h h') (o : Fin 4 → ℤ) (ho : o ∈ centredCube L) :
    WeightsAgreeAt L t (fineSite L y 0 o) (fineSite L y' 0 o) h h' := by apply _root_.YangMills.SharedProofs.p19862 <;> assumption
omit [NeZero L] in
private theorem fineCentre_zero {n : ℕ} [NeZero n] (y : TorusSite n) :
    (fineCentre L 0 y : TorusSite n) = y := by
  funext j
  show (((L : ℤ) ^ 0 * ((y j).cast : ℤ) : ℤ) : ZMod n) = y j
  simp
private theorem blockMean_eq_of_weightsAgreeAt (hodd : Odd L) : (t n n' : ℕ) → [NeZero n] → [NeZero n'] →
    (y : TorusSite n) → (y' : TorusSite n') →
    (h : PlaquetteWeight (fineSide L t n)) → (h' : PlaquetteWeight (fineSide L t n')) →
    WeightsAgreeAt L t y y' h h' → blockMean L t n y h = blockMean L t n' y' h'
  | 0, n, n', _, _, y, y', h, h', hA => by
    show (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * h p =
      (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n') Finset.univ, vertexMultiplicity y' p * h' p
    rw [sum_vertexMultiplicity_mul y h, sum_vertexMultiplicity_mul y' h']
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hz : ∀ j, |slotOffset i j| ≤ (L : ℤ) ^ 0 := fun j => by
      rw [pow_zero]
      exact abs_slotOffset_le_one hi j
    have h1 := hA (slotOffset i) i.1 i.2.1 hz (by
      rw [fineCentre_zero]
      exact ⟨(Finset.mem_filter.mp hi).2, y, mem_plaquetteVertices_plaquetteAtVertex y i,
        Finset.mem_singleton_self y⟩)
    have e1 : h (plaquetteAtVertex y i) = h (fineCentre L 0 y + siteOfInt (slotOffset i), i.1, i.2.1) := by
      rw [fineCentre_zero]
      rfl
    have e2 : h' (plaquetteAtVertex y' i) =
        h' (fineCentre L 0 y' + siteOfInt (slotOffset i), i.1, i.2.1) := by
      rw [fineCentre_zero]
      rfl
    exact e1.trans (h1.trans e2.symm)
  | t + 1, n, n', _, _, y, y', h, h', hA => by
    show ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {y}, blockMean L t (n * L) z h =
      ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {y'}, blockMean L t (n' * L) z h'
    rw [sum_sitesInBlocks hodd y fun z => blockMean L t (n * L) z h,
      sum_sitesInBlocks hodd y' fun z => blockMean L t (n' * L) z h']
    congr 1
    exact Finset.sum_congr rfl fun o ho =>
      blockMean_eq_of_weightsAgreeAt hodd t (n * L) (n' * L) _ _ h h'
        (weightsAgreeAt_fineSite hodd t n n' y y' h h' hA o ho)
private theorem weightNorm_le_succ (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h := by
  refine max_le_max le_rfl ?_
  have hb : BddAbove (Set.range fun pp : OrientedPlaquette m × OrientedPlaquette m =>
      |h pp.1.1 - h pp.2.1| / barycentreDist L (t + 1) pp.1.1 pp.2.1) := (Set.finite_range _).bddAbove
  have hnn : 0 ≤ weightLipschitz L (t + 1) h := Real.iSup_nonneg fun pp => div_nonneg (abs_nonneg _) (by
    unfold barycentreDist
    positivity)
  refine Real.iSup_le (fun pp => le_trans ?_ (le_ciSup hb pp)) hnn
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hP : (0 : ℝ) < (L : ℝ) ^ t := by positivity
  unfold barycentreDist
  set d : ℝ := (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  rcases hd0.eq_or_lt with h0 | hpos
  · simp [← h0]
  · refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    rw [pow_succ]
    refine div_le_div_of_nonneg_left hd0 (by positivity) ?_
    nlinarith
end BlockScales
theorem weightsCompatibleAcrossTori : WeightsCompatibleAcrossTori := fun _ _ hodd t n n' _ _ =>
  ⟨fun y y' h h' hA o ho => weightsAgreeAt_fineSite hodd t n n' y y' h h' hA o ho,
    fun y y' h h' hA => blockMean_eq_of_weightsAgreeAt hodd t n n' y y' h h' hA,
    fun h => weightNorm_le_succ t h⟩
end YangMills.Construction.WeightedResponses
end
