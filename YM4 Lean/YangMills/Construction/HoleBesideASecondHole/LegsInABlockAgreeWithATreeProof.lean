import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvatureProof
import YangMills.Construction.HoleBesideASecondHole.MeansAtABondProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockTrees
open BlockAverages LumpContours
namespace LegAlongTree
variable {F : BlockFrame}
theorem unitQuaternion_coe_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem unitQuaternion_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_unitQuaternion_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, one_mul]
theorem norm_mul_unitQuaternion (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, mul_one]
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem linkValue_reverse {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def unitSquareHolonomy {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (st : PathStep) (i : Fin 4) :
    UnitQuaternion :=
  pathHolonomy X z [st, (i, true), (st.1, !st.2), (i, false)]
def sweepDefect {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (P : List PathStep) (i : Fin 4) (M : ℕ) : ℝ :=
  ‖((pathHolonomy X x (P ++ List.replicate M (i, true) ++ reversePath P) : UnitQuaternion) : ℍ[ℝ]) -
    (pathHolonomy X x (List.replicate M (i, true)) : UnitQuaternion)‖
theorem reversePath_append (P Q : List PathStep) :
    reversePath (P ++ Q) = reversePath Q ++ reversePath P := by
  simp [reversePath]
theorem sweepDefect_append {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (P Q : List PathStep) (i : Fin 4)
    (M : ℕ) :
    sweepDefect X x (P ++ Q) i M ≤ sweepDefect X x P i M + sweepDefect X (x + pathDisplacement j P) Q i M := by
  unfold sweepDefect
  set R := List.replicate M (i, true)
  set x1 := x + pathDisplacement j P
  set a := pathHolonomy X x P
  set b := pathHolonomy X (x1 + pathDisplacement j R) (reversePath P)
  have e1 : pathHolonomy X x ((P ++ Q) ++ R ++ reversePath (P ++ Q)) =
      a * pathHolonomy X x1 (Q ++ R ++ reversePath Q) * b := by
    have e : (P ++ Q) ++ R ++ reversePath (P ++ Q) = P ++ ((Q ++ R ++ reversePath Q) ++ reversePath P) := by
      rw [reversePath_append]
      simp [List.append_assoc]
    rw [e, pathHolonomy_append, pathHolonomy_append, mul_assoc]
    have e2 : x + pathDisplacement j P + pathDisplacement j (Q ++ R ++ reversePath Q) =
        x1 + pathDisplacement j R := by
      rw [pathDisplacement_append, pathDisplacement_append, pathDisplacement_reversePath]
      simp only [x1]
      abel
    rw [e2]
  have e3 : pathHolonomy X x (P ++ R ++ reversePath P) = a * pathHolonomy X x1 R * b := by
    rw [pathHolonomy_append, pathHolonomy_append, pathDisplacement_append, ← add_assoc]
  rw [e1]
  have e4 : ((a * pathHolonomy X x1 (Q ++ R ++ reversePath Q) * b : UnitQuaternion) : ℍ[ℝ]) -
      (pathHolonomy X x R : UnitQuaternion) =
      (a : ℍ[ℝ]) * ((((pathHolonomy X x1 (Q ++ R ++ reversePath Q) : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy X x1 R : UnitQuaternion)) * (b : ℍ[ℝ])) +
      (((pathHolonomy X x (P ++ R ++ reversePath P) : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy X x R : UnitQuaternion)) := by
    rw [e3, unitQuaternion_coe_mul, unitQuaternion_coe_mul, unitQuaternion_coe_mul, unitQuaternion_coe_mul]
    noncomm_ring
  rw [e4]
  refine (norm_add_le _ _).trans ?_
  rw [norm_unitQuaternion_mul, norm_mul_unitQuaternion]
  linarith
theorem sweepDefect_nil {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (i : Fin 4) (M : ℕ) :
    sweepDefect X x [] i M = 0 := by
  simp [sweepDefect, reversePath]
theorem sweepDefect_single {j : ℕ} (X : F.GaugeField j) (st : PathStep) (i : Fin 4) (M : ℕ) :
    ∀ x : F.Site j, sweepDefect X x [st] i M ≤
      ∑ r ∈ Finset.range M, ‖((unitSquareHolonomy X (x + r • unitStep j i) st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  induction M with
  | zero =>
    intro x
    have e : pathHolonomy X x ([st] ++ List.replicate 0 (i, true) ++ reversePath [st]) = 1 := by
      have h := pathHolonomy_reversePath X [st] x
      have e2 : [st] ++ List.replicate 0 (i, true) ++ reversePath [st] = [st] ++ reversePath [st] := by simp
      rw [e2, pathHolonomy_append, h, mul_inv_cancel]
    unfold sweepDefect
    rw [e]
    simp [pathHolonomy]
  | succ M ih =>
    intro x
    set e := unitStep j i with he
    have hsum : ∑ r ∈ Finset.range (M + 1), ‖((unitSquareHolonomy X (x + r • e) st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
        ∑ r ∈ Finset.range M, ‖((unitSquareHolonomy X (x + e + r • e) st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
          ‖((unitSquareHolonomy X x st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      rw [Finset.sum_range_succ']
      simp only [zero_smul, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 3
      rw [add_smul, one_smul]
      abel
    rw [hsum]
    have h1 := ih (x + e)
    refine le_trans ?_ (add_le_add h1 le_rfl)
    unfold sweepDefect
    set a := linkValue X x st
    set a' := linkValue X (x + e) st
    set b := linkValue X (x + stepDisplacement j st) (i, true)
    set c := linkValue X x (i, true)
    set R := List.replicate M (i, true)
    set A' := pathHolonomy X (x + stepDisplacement j st + e) R
    set B := pathHolonomy X (x + e) R
    set a2 := pathHolonomy X (x + stepDisplacement j st + e + pathDisplacement j R) [(st.1, !st.2)]
    have hR1 : List.replicate (M + 1) (i, true) = (i, true) :: R := rfl
    have hstep : stepDisplacement j (i, true) = (e : F.Site j) := by simp [stepDisplacement, he]
    have e1 : pathHolonomy X x ([st] ++ (i, true) :: R ++ reversePath [st]) = a * b * A' * a2 := by
      have er : reversePath [st] = [(st.1, !st.2)] := by simp [reversePath]
      rw [er]
      have : [st] ++ (i, true) :: R ++ [(st.1, !st.2)] = st :: (i, true) :: (R ++ [(st.1, !st.2)]) := by simp
      rw [this]
      simp only [pathHolonomy]
      rw [pathHolonomy_append, hstep]
      simp only [mul_assoc]
      rfl
    have e2 : pathHolonomy X (x + e) ([st] ++ R ++ reversePath [st]) = a' * A' * a2 := by
      have er : reversePath [st] = [(st.1, !st.2)] := by simp [reversePath]
      rw [er]
      have : [st] ++ R ++ [(st.1, !st.2)] = st :: (R ++ [(st.1, !st.2)]) := by simp
      rw [this]
      simp only [pathHolonomy]
      rw [pathHolonomy_append]
      have e5 : x + e + stepDisplacement j st = x + stepDisplacement j st + e := by abel
      rw [e5, mul_assoc]
    have e3 : pathHolonomy X x ((i, true) :: R) = c * B := by
      simp only [pathHolonomy]
      rw [hstep]
    have eS : unitSquareHolonomy X x st i = a * b * a'⁻¹ * c⁻¹ := by
      unfold unitSquareHolonomy
      simp only [pathHolonomy, mul_one]
      have e6 : linkValue X (x + e + stepDisplacement j st) (st.1, !st.2) = (linkValue X (x + e) st)⁻¹ :=
        linkValue_reverse X (x + e) st
      have e7 : linkValue X (x + stepDisplacement j (i, true)) (i, false) = (linkValue X x (i, true))⁻¹ :=
        linkValue_reverse X x (i, true)
      have e8 : x + stepDisplacement j st + stepDisplacement j (i, true) = x + e + stepDisplacement j st := by
        rw [hstep]
        abel
      have e9 : x + stepDisplacement j st + stepDisplacement j (i, true) + stepDisplacement j (st.1, !st.2) =
          x + stepDisplacement j (i, true) := by
        obtain ⟨d, s⟩ := st
        cases s <;> simp [stepDisplacement] <;> abel
      rw [e9, e8, e6, e7]
      simp only [a, b, a', c, mul_assoc]
    rw [hR1, e1, e3, e2]
    have e4 : ((a * b * A' * a2 : UnitQuaternion) : ℍ[ℝ]) - ((c * B : UnitQuaternion) : ℍ[ℝ]) =
        (((unitSquareHolonomy X x st i : UnitQuaternion) : ℍ[ℝ]) - 1) *
            (((c * (a' * A' * a2) : UnitQuaternion)) : ℍ[ℝ]) +
          (c : ℍ[ℝ]) * (((a' * A' * a2 : UnitQuaternion) : ℍ[ℝ]) - (B : ℍ[ℝ])) := by
      have h : a * b * A' * a2 = unitSquareHolonomy X x st i * (c * (a' * A' * a2)) := by
        rw [eS]
        group
      rw [h, unitQuaternion_coe_mul (unitSquareHolonomy X x st i), unitQuaternion_coe_mul c B, sub_mul, one_mul,
        mul_sub, ← unitQuaternion_coe_mul c (a' * A' * a2)]
      abel
    rw [e4]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul_unitQuaternion, norm_unitQuaternion_mul]
    linarith
theorem sweepDefect_replicate {j : ℕ} (X : F.GaugeField j) (st : PathStep) (i : Fin 4) (M m : ℕ) :
    ∀ x : F.Site j, sweepDefect X x (List.replicate m st) i M ≤
      ∑ r ∈ Finset.range m, sweepDefect X (x + r • stepDisplacement j st) [st] i M := by
  induction m with
  | zero =>
    intro x
    simp [sweepDefect_nil]
  | succ m ih =>
    intro x
    have e : List.replicate (m + 1) st = [st] ++ List.replicate m st := rfl
    rw [e, Finset.sum_range_succ']
    refine (sweepDefect_append X x [st] _ i M).trans ?_
    have e1 : x + pathDisplacement j [st] = x + stepDisplacement j st := by simp [pathDisplacement]
    rw [e1, add_comm]
    simp only [zero_smul, add_zero]
    refine add_le_add ((ih _).trans (le_of_eq ?_)) le_rfl
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [add_smul, one_smul, add_assoc, add_comm (stepDisplacement j st)]
def squareBase {j : ℕ} (z : F.Site j) (st : PathStep) : F.Site j :=
  if st.2 then z else z - unitStep j st.1
def squarePlaquette {j : ℕ} (z : F.Site j) (st : PathStep) (i : Fin 4) : F.Site j × Fin 4 × Fin 4 :=
  (squareBase z st, min st.1 i, max st.1 i)
theorem plaquetteHolonomy_swap_defect {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    ‖((plaquetteHolonomy X (x, ν, μ) : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      ‖((plaquetteHolonomy X (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BondContours.plaquetteHolonomy_swap_defect <;> assumption
theorem plaquetteDefect_ordered {j : ℕ} (X : F.GaugeField j) (b : F.Site j) (d i : Fin 4) :
    plaquetteDefect X (b, min d i, max d i) = ‖((plaquetteHolonomy X (b, d, i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BondContours.plaquetteDefect_ordered <;> assumption
theorem unitSquare_defect {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (st : PathStep) (i : Fin 4) :
    ‖((unitSquareHolonomy X z st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ = plaquetteDefect X (squarePlaquette z st i) := by apply _root_.YangMills.Construction.BondContours.elementarySquare_defect <;> assumption
theorem unitSquare_degenerate {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (b : Bool) (i : Fin 4) :
    unitSquareHolonomy X z (i, b) i = 1 := by apply _root_.YangMills.Construction.BondContours.elementarySquare_degenerate <;> assumption
theorem unitStep_apply_ne (j : ℕ) (i k : Fin 4) (hk : i ≠ k) : (unitStep j i : F.Site j) k = 0 := by
  simp [unitStep, siteOfCoords, Pi.single_apply, hk.symm]
theorem unitStep_apply_self (j : ℕ) (i : Fin 4) : (unitStep j i : F.Site j) i = 1 := by
  simp [unitStep, siteOfCoords]
theorem natCast_injective_of_lt {p r r' : ℕ} (h : (r : ZMod p) = r') (hp : p = 0 ∨ (r < p ∧ r' < p)) :
    r = r' := by apply _root_.YangMills.Construction.BondContours.natCast_zmod_injective_of_lt <;> assumption
theorem squarePlaquette_injOn {j : ℕ} (x : F.Site j) (st : PathStep) (i : Fin 4) (m M : ℕ) (hne : st.1 ≠ i)
    (hp : ∀ k, F.period j k = 0 ∨ (m ≤ F.period j k ∧ M ≤ F.period j k)) :
    Set.InjOn (fun q : ℕ × ℕ => squarePlaquette (x + q.1 • stepDisplacement j st + q.2 • unitStep j i) st i)
      (Finset.range m ×ˢ Finset.range M : Finset (ℕ × ℕ)) := by apply _root_.YangMills.Construction.BondContours.squarePlaquette_injOn <;> assumption
theorem sweepDefect_sq_le {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) (i : Fin 4) (m M : ℕ)
    (B : Finset (F.Site j × Fin 4 × Fin 4))
    (hmem : st.1 ≠ i → ∀ r1 < m, ∀ r2 < M,
      squarePlaquette (x + r1 • stepDisplacement j st + r2 • unitStep j i) st i ∈ B)
    (hp : ∀ k, F.period j k = 0 ∨ (m ≤ F.period j k ∧ M ≤ F.period j k)) :
    sweepDefect X x (List.replicate m st) i M ^ 2 ≤ (m : ℝ) * M * ∑ p ∈ B, plaquetteDefect X p ^ 2 := by
  classical
  have hG : 0 ≤ ∑ p ∈ B, plaquetteDefect X p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have h0 : 0 ≤ sweepDefect X x (List.replicate m st) i M := norm_nonneg _
  by_cases hne : st.1 = i
  · have hz : sweepDefect X x (List.replicate m st) i M ≤ 0 := by
      refine (sweepDefect_replicate X st i M m x).trans ?_
      refine Finset.sum_nonpos fun r _ => ?_
      refine (sweepDefect_single X st i M _).trans (le_of_eq ?_)
      refine Finset.sum_eq_zero fun r' _ => ?_
      obtain ⟨d, b⟩ := st
      simp only at hne
      subst hne
      rw [unitSquare_degenerate]
      simp
    have : sweepDefect X x (List.replicate m st) i M = 0 := le_antisymm hz h0
    rw [this]
    have h00 : (0 : ℝ) ≤ (m : ℝ) * M := by positivity
    have := mul_nonneg h00 hG
    simpa using this
  · have h1 : sweepDefect X x (List.replicate m st) i M ≤
        ∑ q ∈ Finset.range m ×ˢ Finset.range M,
          plaquetteDefect X (squarePlaquette (x + q.1 • stepDisplacement j st + q.2 • unitStep j i) st i) := by
      refine (sweepDefect_replicate X st i M m x).trans ?_
      rw [Finset.sum_product]
      refine Finset.sum_le_sum fun r _ => ?_
      refine (sweepDefect_single X st i M _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [unitSquare_defect]
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range m ×ˢ Finset.range M)
      (f := fun q : ℕ × ℕ =>
        plaquetteDefect X (squarePlaquette (x + q.1 • stepDisplacement j st + q.2 • unitStep j i) st i))
    have hinj := squarePlaquette_injOn x st i m M hne hp
    have h3 : ∑ q ∈ Finset.range m ×ˢ Finset.range M,
        plaquetteDefect X (squarePlaquette (x + q.1 • stepDisplacement j st + q.2 • unitStep j i) st i) ^ 2 ≤
        ∑ p ∈ B, plaquetteDefect X p ^ 2 := by
      rw [← Finset.sum_image (f := fun p => plaquetteDefect X p ^ 2) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => sq_nonneg _
      intro p hp'
      obtain ⟨⟨r1, r2⟩, hq, rfl⟩ := Finset.mem_image.1 hp'
      have hq' := Finset.mem_product.1 hq
      exact hmem hne r1 (Finset.mem_range.1 hq'.1) r2 (Finset.mem_range.1 hq'.2)
    have hcard : ((Finset.range m ×ˢ Finset.range M).card : ℝ) = (m : ℝ) * M := by
      simp
    rw [hcard] at h2
    have h5 : (0 : ℝ) ≤ (m : ℝ) * M := by positivity
    exact (pow_le_pow_left₀ h0 h1 2).trans (h2.trans (mul_le_mul_of_nonneg_left h3 h5))
def WithinBlock (L : ℕ) (o : Fin 4 → ℤ) : Prop := ∀ m, |o m| ≤ ((L : ℤ) - 1) / 2
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem mem_centredCube_of_withinBlock {L : ℕ} {o : Fin 4 → ℤ} (ho : WithinBlock L o) : o ∈ centredCube L := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_of_withinBlock <;> assumption
theorem withinBlock_of_mem_centredCube {L : ℕ} {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) : WithinBlock L o := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.withinBlock_of_mem_centredCube <;> assumption
theorem refineSite_add_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o : Fin 4 → ℤ}
    (ho : WithinBlock F.blockSide o) :
    refineSite y + siteOfCoords j o ∈ sitesBelow j y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_mem_sitesBelow <;> assumption
def prefixOffset (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem prefixOffset_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : prefixOffset h π 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_zero <;> assumption
theorem prefixOffset_succ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    prefixOffset h π ((k : ℕ) + 1) = prefixOffset h π k + h (π k) • Pi.single (π k) 1 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_succ <;> assumption
theorem axisPath_eq_segments (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_eq_append <;> assumption
def axisSegment (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) : List PathStep :=
  List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
theorem site_after_segment (j : ℕ) (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    x + siteOfCoords j (prefixOffset h π k) + pathDisplacement j (axisSegment h π k) =
      x + siteOfCoords j (prefixOffset h π ((k : ℕ) + 1)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.add_axisPathFlow <;> assumption
theorem sweepDefect_axisPath {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (h : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) (M : ℕ) :
    sweepDefect X x (axisPath h π) i M ≤ ∑ k : Fin 4,
      sweepDefect X (x + siteOfCoords j (prefixOffset h π k)) (axisSegment h π k) i M := by
  rw [axisPath_eq_segments, Fin.sum_univ_four]
  have z0 : x + siteOfCoords j (prefixOffset h π ((0 : Fin 4) : ℕ)) = x := by
    simp [prefixOffset_zero, siteOfCoords_zero]
  have s0 := site_after_segment j x h π 0
  have s1 := site_after_segment j x h π 1
  have s2 := site_after_segment j x h π 2
  have b0 := sweepDefect_append X x (axisSegment h π 0)
    (axisSegment h π 1 ++ (axisSegment h π 2 ++ (axisSegment h π 3 ++ []))) i M
  have b1 := sweepDefect_append X (x + siteOfCoords j (prefixOffset h π ((1 : Fin 4) : ℕ))) (axisSegment h π 1)
    (axisSegment h π 2 ++ (axisSegment h π 3 ++ [])) i M
  have b2 := sweepDefect_append X (x + siteOfCoords j (prefixOffset h π ((2 : Fin 4) : ℕ))) (axisSegment h π 2)
    (axisSegment h π 3 ++ []) i M
  have b3 := sweepDefect_append X (x + siteOfCoords j (prefixOffset h π ((3 : Fin 4) : ℕ)))
    (axisSegment h π 3) [] i M
  rw [sweepDefect_nil] at b3
  rw [z0] at s0 ⊢
  have e01 : x + pathDisplacement j (axisSegment h π 0) =
      x + siteOfCoords j (prefixOffset h π ((1 : Fin 4) : ℕ)) := by
    have : (((0 : Fin 4) : ℕ) + 1) = ((1 : Fin 4) : ℕ) := rfl
    rw [← this, ← s0]
  have e12 : x + siteOfCoords j (prefixOffset h π ((1 : Fin 4) : ℕ)) + pathDisplacement j (axisSegment h π 1) =
      x + siteOfCoords j (prefixOffset h π ((2 : Fin 4) : ℕ)) := s1
  have e23 : x + siteOfCoords j (prefixOffset h π ((2 : Fin 4) : ℕ)) + pathDisplacement j (axisSegment h π 2) =
      x + siteOfCoords j (prefixOffset h π ((3 : Fin 4) : ℕ)) := s2
  rw [e01] at b0
  rw [e12] at b1
  rw [e23] at b2
  simp only [axisSegment] at b0 b1 b2 b3 ⊢
  linarith
theorem period_eq_zero_or_ge (j : ℕ) (hj : j < F.top) (hA : IsAdmissibleAmbient F) (hL : 0 < F.blockSide)
    (k : Fin 4) :
    F.period j k = 0 ∨ F.blockSide ≤ F.period j k := by apply _root_.YangMills.Construction.BondContours.period_eq_zero_or_le <;> assumption
theorem plaquette_mem_cutPlaquettes (j : ℕ) (hL : Odd F.blockSide) (y : F.Site (j + 1)) (d i : Fin 4)
    (hne : d ≠ i) {lo : Fin 4 → ℤ} (h00 : WithinBlock F.blockSide lo)
    (h10 : WithinBlock F.blockSide (lo + (1 : ℤ) • Pi.single d 1))
    (h01 : WithinBlock F.blockSide (lo + (1 : ℤ) • Pi.single i 1))
    (h11 : WithinBlock F.blockSide (lo + (1 : ℤ) • Pi.single d 1 + (1 : ℤ) • Pi.single i 1)) :
    (refineSite y + siteOfCoords j lo, min d i, max d i) ∈ cutPlaquettes (sitesBelow j y) := by
  have a1 := refineSite_add_mem_sitesBelow j y h00
  have a2 := refineSite_add_mem_sitesBelow j y h10
  have a3 := refineSite_add_mem_sitesBelow j y h01
  have a4 := refineSite_add_mem_sitesBelow j y h11
  have hu : ∀ e, siteOfCoords (F := F) j (Pi.single e (1 : ℤ)) = unitStep j e := fun _ => rfl
  simp only [siteOfCoords_add, one_smul, hu] at a2 a3 a4
  simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  refine ⟨a1, min_lt_max.2 hne, ?_⟩
  intro w hw
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact a1
    · convert a2 using 1
      abel
    · convert a3 using 1
      abel
    · convert a4 using 1
      abel
  · rw [min_eq_right h.le, max_eq_left h.le] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact a1
    · convert a3 using 1
      abel
    · convert a2 using 1
      abel
    · convert a4 using 1
      abel
theorem squarePlaquette_mem_cutPlaquettes (j : ℕ) (hL : Odd F.blockSide) (y : F.Site (j + 1)) (i : Fin 4)
    (o : Fin 4 → ℤ) (st : PathStep) (m M : ℕ) (hne : st.1 ≠ i)
    (hC : ∀ r ≤ m, ∀ r' ≤ M,
      WithinBlock F.blockSide
        (o + (if st.2 then (r : ℤ) else -(r : ℤ)) • Pi.single st.1 1 + (r' : ℤ) • Pi.single i 1)) :
    ∀ r1 < m, ∀ r2 < M,
      squarePlaquette (refineSite y + siteOfCoords j o + r1 • stepDisplacement j st + r2 • unitStep j i) st i ∈
        cutPlaquettes (sitesBelow j y) := by
  intro r1 h1 r2 h2
  obtain ⟨d, b⟩ := st
  simp only at hne hC
  cases b
  · simp only [Bool.false_eq_true, if_false] at hC
    set lo : Fin 4 → ℤ := o + (-((r1 + 1 : ℕ) : ℤ)) • Pi.single d 1 + (r2 : ℤ) • Pi.single i 1 with hlo
    have e1 : lo + (1 : ℤ) • Pi.single d 1 = o + (-(r1 : ℤ)) • Pi.single d 1 + (r2 : ℤ) • Pi.single i 1 := by
      funext m
      simp only [hlo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have e2 : lo + (1 : ℤ) • Pi.single i 1 =
        o + (-((r1 + 1 : ℕ) : ℤ)) • Pi.single d 1 + ((r2 + 1 : ℕ) : ℤ) • Pi.single i 1 := by
      funext m
      simp only [hlo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have e3 : lo + (1 : ℤ) • Pi.single d 1 + (1 : ℤ) • Pi.single i 1 =
        o + (-(r1 : ℤ)) • Pi.single d 1 + ((r2 + 1 : ℕ) : ℤ) • Pi.single i 1 := by
      funext m
      simp only [hlo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have := plaquette_mem_cutPlaquettes j hL y d i hne (lo := lo) (hC (r1 + 1) h1 r2 h2.le)
      (by rw [e1]; exact hC r1 h1.le r2 h2.le) (by rw [e2]; exact hC (r1 + 1) h1 (r2 + 1) h2)
      (by rw [e3]; exact hC r1 h1.le (r2 + 1) h2)
    convert this using 1
    simp only [squarePlaquette, squareBase, Bool.false_eq_true, if_false, stepDisplacement]
    congr 1
    rw [hlo, siteOfCoords_add, siteOfCoords_add, siteOfCoords_single, siteOfCoords_single, neg_smul,
      natCast_zsmul, natCast_zsmul, add_smul, one_smul, smul_neg]
    abel
  · simp only [if_true] at hC
    set lo : Fin 4 → ℤ := o + ((r1 : ℤ)) • Pi.single d 1 + (r2 : ℤ) • Pi.single i 1 with hlo
    have e1 : lo + (1 : ℤ) • Pi.single d 1 = o + ((r1 + 1 : ℕ) : ℤ) • Pi.single d 1 + (r2 : ℤ) • Pi.single i 1 := by
      funext m
      simp only [hlo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have e2 : lo + (1 : ℤ) • Pi.single i 1 =
        o + ((r1 : ℤ)) • Pi.single d 1 + ((r2 + 1 : ℕ) : ℤ) • Pi.single i 1 := by
      funext m
      simp only [hlo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have e3 : lo + (1 : ℤ) • Pi.single d 1 + (1 : ℤ) • Pi.single i 1 =
        o + ((r1 + 1 : ℕ) : ℤ) • Pi.single d 1 + ((r2 + 1 : ℕ) : ℤ) • Pi.single i 1 := by
      funext m
      simp only [hlo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have := plaquette_mem_cutPlaquettes j hL y d i hne (lo := lo) (hC r1 h1.le r2 h2.le)
      (by rw [e1]; exact hC (r1 + 1) h1 r2 h2.le) (by rw [e2]; exact hC r1 h1.le (r2 + 1) h2)
      (by rw [e3]; exact hC (r1 + 1) h1 (r2 + 1) h2)
    convert this using 1
    simp only [squarePlaquette, squareBase, if_true, stepDisplacement]
    congr 1
    rw [hlo, siteOfCoords_add, siteOfCoords_add, siteOfCoords_single, siteOfCoords_single, natCast_zsmul,
      natCast_zsmul]
    abel
def straightPath (k : ℤ) (d : Fin 4) : List PathStep := List.replicate k.natAbs (d, decide (0 ≤ k))
theorem pathDisplacement_straightPath (j : ℕ) (k : ℤ) (d : Fin 4) :
    pathDisplacement (F := F) j (straightPath k d) = k • unitStep j d := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate_axis <;> assumption
theorem sweepDefect_straightPath (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (hA : IsAdmissibleAmbient F)
    (X : F.GaugeField j) (y : F.Site (j + 1))
    (o : Fin 4 → ℤ) (ho : WithinBlock F.blockSide o) (k : ℤ) (d i : Fin 4) (M : ℕ)
    (hk : |o d + k| ≤ ((F.blockSide : ℤ) - 1) / 2) (hM : |o i + M| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    sweepDefect X (refineSite y + siteOfCoords j o) (straightPath k d) i M ≤
      (F.blockSide : ℝ) * blockCurvatureNorm X y := by
  have hkL : k.natAbs ≤ F.blockSide := by
    have a1 := abs_le.1 (ho d)
    have a2 := abs_le.1 hk
    omega
  have hML : M ≤ F.blockSide := by
    have a1 := abs_le.1 (ho i)
    have a2 := abs_le.1 hM
    omega
  have h1 := sweepDefect_sq_le X (refineSite y + siteOfCoords j o) (d, decide (0 ≤ k)) i k.natAbs M
    (cutPlaquettes (sitesBelow j y))
    (fun hn => squarePlaquette_mem_cutPlaquettes j hL y i o _ _ _ hn (by
      intro r hr r' hr' m
      have a1 := abs_le.1 (ho m)
      have a2 := abs_le.1 hk
      have a3 := abs_le.1 hM
      have a4 := abs_le.1 (ho d)
      have a5 := abs_le.1 (ho i)
      simp only at hn
      rw [abs_le]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hmd : m = d
      · subst hmd
        have hmi : m ≠ i := hn
        by_cases hk0 : 0 ≤ k
        · simp only [hk0, decide_true, if_true, hmi, if_false]
          omega
        · simp only [hk0, decide_false, Bool.false_eq_true, if_false, hmi, if_true]
          omega
      · by_cases hmi : m = i
        · subst hmi
          simp only [hmd, if_false, if_true]
          omega
        · simp only [hmd, hmi, if_false]
          omega))
    (fun k' => by
      rcases period_eq_zero_or_ge j hj hA hL.pos k' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨hkL.trans h', hML.trans h'⟩)
  have hG : 0 ≤ ∑ p ∈ cutPlaquettes (sitesBelow j y), plaquetteDefect X p ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have h0 : 0 ≤ sweepDefect X (refineSite y + siteOfCoords j o) (straightPath k d) i M := norm_nonneg _
  have hL0 : (0 : ℝ) ≤ F.blockSide := by positivity
  have h2 : sweepDefect X (refineSite y + siteOfCoords j o) (straightPath k d) i M ^ 2 ≤
      ((F.blockSide : ℝ) * blockCurvatureNorm X y) ^ 2 := by
    rw [mul_pow, blockCurvatureNorm, Real.sq_sqrt hG]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hG)
    have b1 : ((k.natAbs : ℕ) : ℝ) ≤ F.blockSide := by exact_mod_cast hkL
    have b2 : (M : ℝ) ≤ F.blockSide := by exact_mod_cast hML
    nlinarith [Nat.cast_nonneg (α := ℝ) k.natAbs, Nat.cast_nonneg (α := ℝ) M]
  have hnn : 0 ≤ (F.blockSide : ℝ) * blockCurvatureNorm X y := mul_nonneg hL0 (Real.sqrt_nonneg _)
  exact (pow_le_pow_iff_left₀ h0 hnn (by norm_num)).1 h2
theorem pathHolonomy_straightPath_succ {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (k : ℤ) (d : Fin 4) :
    pathHolonomy X z (straightPath (k + 1) d) = pathHolonomy X z (straightPath k d) * X (z + k • unitStep j d) d := by
  by_cases hk : 0 ≤ k
  · have h1 : (k + 1).natAbs = k.natAbs + 1 := by omega
    have h2 : decide (0 ≤ k + 1) = decide (0 ≤ k) := by
      simp only [decide_eq_decide]
      omega
    have e : straightPath (k + 1) d = straightPath k d ++ [(d, true)] := by
      simp only [straightPath, h1, h2, hk, decide_true]
      rw [List.replicate_succ']
    rw [e, pathHolonomy_append, pathDisplacement_straightPath]
    simp [pathHolonomy, linkValue]
  · have h1 : k.natAbs = (k + 1).natAbs + 1 := by omega
    have e : straightPath k d = straightPath (k + 1) d ++ [(d, false)] := by
      by_cases h0 : k = -1
      · subst h0
        simp [straightPath]
      · have h2 : ¬ (0 ≤ k + 1) := by omega
        simp only [straightPath, h1, hk, h2, decide_false]
        rw [List.replicate_succ']
    rw [e, pathHolonomy_append, pathDisplacement_straightPath]
    simp only [pathHolonomy, linkValue, Bool.false_eq_true, if_false, mul_one]
    have e2 : z + (k + 1) • unitStep j d - unitStep j d = z + k • unitStep j d := by
      rw [add_smul, one_smul]
      abel
    rw [e2]
    group
theorem pathHolonomy_straightPath_add {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (a : ℤ) (d : Fin 4) (M : ℕ) :
    pathHolonomy X z (straightPath a d) * pathHolonomy X (z + a • unitStep j d) (List.replicate M (d, true)) =
      pathHolonomy X z (straightPath (a + M) d) := by
  induction M with
  | zero => simp [pathHolonomy]
  | succ M ih =>
    rw [List.replicate_succ', pathHolonomy_append, ← mul_assoc, ih]
    have e : ((a + ((M + 1 : ℕ) : ℤ))) = (a + M) + 1 := by
      push_cast
      ring
    rw [e, pathHolonomy_straightPath_succ, pathDisplacement_replicate]
    simp only [pathHolonomy, linkValue, stepDisplacement, if_true, mul_one]
    congr 2
    rw [add_smul, natCast_zsmul, add_assoc]
def coordsBelow (o : Fin 4 → ℤ) (d : Fin 4) : Fin 4 → ℤ := fun m => if m < d then o m else 0
def coordsAbove (o : Fin 4 → ℤ) (d : Fin 4) : Fin 4 → ℤ := fun m => if d < m then o m else 0
theorem axisPath_split (o : Fin 4 → ℤ) (d : Fin 4) :
    axisPath o 1 = axisPath (coordsBelow o d) 1 ++ (straightPath (o d) d ++ axisPath (coordsAbove o d) 1) := by
  rw [axisPath_eq_segments, axisPath_eq_segments, axisPath_eq_segments]
  fin_cases d <;> simp [coordsBelow, coordsAbove, straightPath] <;> rfl
theorem coords_split (o : Fin 4 → ℤ) (d : Fin 4) :
    o = coordsBelow o d + o d • Pi.single d 1 + coordsAbove o d := by
  funext m
  simp only [coordsBelow, coordsAbove, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rcases lt_trichotomy m d with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · subst h
    simp
  · simp [h, h.ne', not_lt.2 h.le]
theorem norm_sandwich_sub (u v v' w : UnitQuaternion) :
    ‖((u * v * w : UnitQuaternion) : ℍ[ℝ]) - ((u * v' * w : UnitQuaternion) : ℍ[ℝ])‖ = ‖(v : ℍ[ℝ]) - v'‖ := by apply _root_.YangMills.Construction.BondMeans.norm_mul_mul_sub_mul_mul <;> assumption
theorem forwardLine_near_tree (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (hA : IsAdmissibleAmbient F)
    (X : F.GaugeField j) (y : F.Site (j + 1))
    (o : Fin 4 → ℤ) (ho : WithinBlock F.blockSide o) (d : Fin 4) (M : ℕ)
    (hM : |o d + M| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    ‖((blockTreeTransport X y o * pathHolonomy X (refineSite y + siteOfCoords j o) (List.replicate M (d, true)) *
        (blockTreeTransport X y (o + (M : ℤ) • Pi.single d 1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      4 * ((F.blockSide : ℝ) * blockCurvatureNorm X y) := by
  set o' := o + (M : ℤ) • (Pi.single d 1 : Fin 4 → ℤ) with ho'
  have hlow : coordsBelow o' d = coordsBelow o d := by
    funext m
    simp only [coordsBelow, ho', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases h : m < d
    · simp [h, h.ne]
    · simp [h]
  have hhigh : coordsAbove o' d = coordsAbove o d := by
    funext m
    simp only [coordsAbove, ho', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases h : d < m
    · simp [h, h.ne']
    · simp [h]
  have hod : o' d = o d + M := by simp [ho']
  set A := axisPath (coordsBelow o d) 1 with hAdef
  set T := axisPath (coordsAbove o d) 1 with hT
  set c := refineSite y with hc
  set z := c + pathDisplacement j A with hz
  set a := o d with ha
  set R := List.replicate M (d, true) with hR
  set z1 := z + a • unitStep j d with hz1
  have hpR : pathDisplacement (F := F) j R = (M : ℤ) • unitStep j d := by
    rw [hR, pathDisplacement_replicate]
    simp [stepDisplacement, natCast_zsmul]
  have hsite : c + siteOfCoords j o = z1 + pathDisplacement j T := by
    conv_lhs => rw [coords_split o d]
    rw [siteOfCoords_add, siteOfCoords_add, siteOfCoords_single, hT, pathDisplacement_axisPath, hz1, hz, hAdef,
      pathDisplacement_axisPath]
    abel
  have t1 : blockTreeTransport X y o =
      pathHolonomy X c A * (pathHolonomy X z (straightPath a d) * pathHolonomy X z1 T) := by
    unfold blockTreeTransport
    rw [axisPath_split o d, pathHolonomy_append, pathHolonomy_append, pathDisplacement_straightPath]
  have t2 : blockTreeTransport X y o' =
      pathHolonomy X c A *
        (pathHolonomy X z (straightPath (a + M) d) * pathHolonomy X (z1 + pathDisplacement j R) T) := by
    have e : c + pathDisplacement j A + (a + M) • unitStep j d = z1 + pathDisplacement j R := by
      rw [hpR, hz1, hz, add_smul, add_assoc (c + pathDisplacement j A)]
    show pathHolonomy X c (axisPath o' 1) = _
    rw [axisPath_split o' d, hlow, hhigh, hod, pathHolonomy_append, pathHolonomy_append,
      pathDisplacement_straightPath, e]
  have hsw : pathHolonomy X z1 (T ++ R ++ reversePath T) =
      pathHolonomy X z1 T * pathHolonomy X (c + siteOfCoords j o) R *
        (pathHolonomy X (z1 + pathDisplacement j R) T)⁻¹ := by
    rw [pathHolonomy_append, pathHolonomy_append, pathDisplacement_append, hsite]
    have h1 := pathHolonomy_reversePath X T (z1 + pathDisplacement j R)
    have e : z1 + (pathDisplacement j T + pathDisplacement j R) =
        z1 + pathDisplacement j R + pathDisplacement j T := by abel
    rw [e, h1]
  have hone : (1 : UnitQuaternion) = (pathHolonomy X c A * pathHolonomy X z (straightPath a d)) *
      pathHolonomy X z1 R *
      (pathHolonomy X c A * pathHolonomy X z (straightPath (a + M) d))⁻¹ := by
    have hla : pathHolonomy X z (straightPath a d) * pathHolonomy X z1 R =
        pathHolonomy X z (straightPath (a + M) d) := pathHolonomy_straightPath_add X z a d M
    rw [← hla]
    generalize pathHolonomy X c A = p1
    generalize pathHolonomy X z (straightPath a d) = p2
    generalize pathHolonomy X z1 R = p3
    group
  have hE : blockTreeTransport X y o * pathHolonomy X (c + siteOfCoords j o) R * (blockTreeTransport X y o')⁻¹ =
      (pathHolonomy X c A * pathHolonomy X z (straightPath a d)) * pathHolonomy X z1 (T ++ R ++ reversePath T) *
        (pathHolonomy X c A * pathHolonomy X z (straightPath (a + M) d))⁻¹ := by
    rw [t1, t2, hsw]
    group
  have hnorm : ‖((blockTreeTransport X y o * pathHolonomy X (c + siteOfCoords j o) R *
        (blockTreeTransport X y o')⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      sweepDefect X z1 T d M := by
    rw [hE]
    conv_lhs => rw [show ((1 : ℍ[ℝ])) = ((1 : UnitQuaternion) : ℍ[ℝ]) from rfl, hone]
    rw [norm_sandwich_sub]
    rfl
  rw [hnorm]
  have hs := sweepDefect_axisPath X z1 (coordsAbove o d) 1 d M
  refine hs.trans ?_
  have hhalf : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by
    have := hL.pos
    omega
  have hterm : ∀ k : Fin 4, sweepDefect X (z1 + siteOfCoords j (prefixOffset (coordsAbove o d) 1 k))
      (axisSegment (coordsAbove o d) 1 k) d M ≤ (F.blockSide : ℝ) * blockCurvatureNorm X y := by
    intro k
    set q : Fin 4 → ℤ := coordsBelow o d + a • Pi.single d 1 + prefixOffset (coordsAbove o d) 1 k with hq
    have hqs : z1 + siteOfCoords j (prefixOffset (coordsAbove o d) 1 k) = c + siteOfCoords j q := by
      rw [hq, siteOfCoords_add, siteOfCoords_add, siteOfCoords_single, hz1, hz, hAdef, pathDisplacement_axisPath]
      abel
    have hqv : ∀ m, q m = o m ∨ q m = 0 := by
      intro m
      simp only [hq, coordsBelow, coordsAbove, prefixOffset, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply]
      rcases lt_trichotomy m d with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h
        simp [ha]
      · simp only [not_lt.2 h.le, h.ne', h, if_false, if_true]
        by_cases h2 : (((1 : Equiv.Perm (Fin 4)).symm m : Fin 4) : ℕ) < k
        · simp [h2]
        · simp [h2]
    have hqo : WithinBlock F.blockSide q := by
      intro m
      rcases hqv m with h | h
      · rw [h]
        exact ho m
      · rw [h]
        simpa using hhalf
    have hqd : q d = a := by
      simp [hq, coordsBelow, coordsAbove, prefixOffset]
    rw [hqs]
    have hpiece : axisSegment (coordsAbove o d) 1 k =
        straightPath (coordsAbove o d ((1 : Equiv.Perm (Fin 4)) k)) k := rfl
    rw [hpiece]
    refine sweepDefect_straightPath j hj hL hA X y q hqo _ k d M ?_ (by rw [hqd]; exact hM)
    have hk1 : ((1 : Equiv.Perm (Fin 4)) k) = k := rfl
    rw [hk1]
    have hqk : q k + coordsAbove o d k = o k ∨ q k + coordsAbove o d k = q k := by
      simp only [hq, coordsBelow, coordsAbove, prefixOffset, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply]
      rcases lt_trichotomy k d with h | h | h
      · right
        simp [h, h.ne, not_lt.2 h.le]
      · right
        subst h
        simp
      · left
        simp [h, h.ne', not_lt.2 h.le]
        intro h2
        exact absurd (show k < k from h2) (lt_irrefl _)
    rcases hqk with h | h
    · rw [h]
      exact ho k
    · rw [h]
      exact hqo k
  rw [Fin.sum_univ_four]
  have := hterm 0
  have := hterm 1
  have := hterm 2
  have := hterm 3
  linarith
theorem defect_inv (g : UnitQuaternion) : ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem straightPath_near_tree (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (hA : IsAdmissibleAmbient F)
    (X : F.GaugeField j) (y : F.Site (j + 1))
    (q : Fin 4 → ℤ) (hq : WithinBlock F.blockSide q) (d : Fin 4) (k : ℤ)
    (hk : |q d + k| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    ‖((blockTreeTransport X y q * pathHolonomy X (refineSite y + siteOfCoords j q) (straightPath k d) *
        (blockTreeTransport X y (q + k • Pi.single d 1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      4 * ((F.blockSide : ℝ) * blockCurvatureNorm X y) := by
  by_cases hk0 : 0 ≤ k
  · have e : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hk0
    have h := forwardLine_near_tree j hj hL hA X y q hq d k.natAbs (by rw [e]; exact hk)
    rw [e] at h
    have e2 : straightPath k d = List.replicate k.natAbs (d, true) := by
      simp [straightPath, hk0]
    rw [e2]
    exact h
  · have hk1 : k < 0 := by omega
    set M := k.natAbs with hMdef
    have eM : (M : ℤ) = -k := by omega
    set q' := q + k • (Pi.single d 1 : Fin 4 → ℤ) with hq'
    have hq'o : WithinBlock F.blockSide q' := by
      intro m
      by_cases hm : m = d
      · subst hm
        simpa [hq'] using hk
      · simpa [hq', hm] using hq m
    have hback : q' + (M : ℤ) • (Pi.single d 1 : Fin 4 → ℤ) = q := by
      rw [eM, hq', add_assoc, ← add_smul]
      simp
    have h := forwardLine_near_tree j hj hL hA X y q' hq'o d M (by
      have : q' d + M = q d := by
        simp [hq', eM]
      rw [this]
      exact hq d)
    rw [hback] at h
    have e2 : straightPath k d = reversePath (List.replicate M (d, true)) := by
      simp [straightPath, hk0, reversePath, List.map_replicate, hMdef]
    have hpR : pathDisplacement (F := F) j (List.replicate M (d, true)) = (M : ℤ) • unitStep j d := by
      rw [pathDisplacement_replicate]
      simp [stepDisplacement, natCast_zsmul]
    have hs : refineSite y + siteOfCoords j q =
        refineSite y + siteOfCoords j q' + pathDisplacement j (List.replicate M (d, true)) := by
      rw [hpR, eM, hq', siteOfCoords_add, siteOfCoords_single]
      simp only [neg_smul]
      abel
    have h1 := pathHolonomy_reversePath X (List.replicate M (d, true)) (refineSite y + siteOfCoords j q')
    rw [e2, hs, h1, ← defect_inv]
    convert h using 3
    group
def NearTransport (a g g' : UnitQuaternion) (K : ℝ) : Prop :=
  ‖(a : ℍ[ℝ]) - ((g⁻¹ * g' : UnitQuaternion) : ℍ[ℝ])‖ ≤ K
theorem nearTransport_of_defect (a g g' : UnitQuaternion) (K : ℝ)
    (h : ‖((g * a * g'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ K) : NearTransport a g g' K := by
  unfold NearTransport
  have e : (1 : ℍ[ℝ]) = ((g * (g⁻¹ * g') * g'⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have : g * (g⁻¹ * g') * g'⁻¹ = 1 := by group
    rw [this]
    rfl
  rw [e, norm_sandwich_sub] at h
  exact h
theorem nearTransport_mul (a b g g' g'' : UnitQuaternion) (K K' : ℝ) (h : NearTransport a g g' K)
    (h' : NearTransport b g' g'' K') :
    NearTransport (a * b) g g'' (K + K') := by
  unfold NearTransport at *
  have e : ((a * b : UnitQuaternion) : ℍ[ℝ]) - ((g⁻¹ * g'' : UnitQuaternion) : ℍ[ℝ]) =
      ((a : ℍ[ℝ]) - ((g⁻¹ * g' : UnitQuaternion) : ℍ[ℝ])) * (b : ℍ[ℝ]) +
        ((g⁻¹ * g' : UnitQuaternion) : ℍ[ℝ]) * ((b : ℍ[ℝ]) - ((g'⁻¹ * g'' : UnitQuaternion) : ℍ[ℝ])) := by
    have e1 : ((g⁻¹ * g'' : UnitQuaternion) : ℍ[ℝ]) =
        ((g⁻¹ * g' : UnitQuaternion) : ℍ[ℝ]) * ((g'⁻¹ * g'' : UnitQuaternion) : ℍ[ℝ]) := by
      rw [← unitQuaternion_coe_mul]
      congr 1
      group
    rw [e1, unitQuaternion_coe_mul a b]
    noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul_unitQuaternion, norm_unitQuaternion_mul]
  linarith
end LegAlongTree
theorem legNearBlockTree_holds : LegNearBlockTree := by
  intro F j hj hL hA X y o o' π ho ho'
  have hb := LegAlongTree.withinBlock_of_mem_centredCube ho
  have hb' := LegAlongTree.withinBlock_of_mem_centredCube ho'
  set h := o' - o with hh
  set K := 4 * ((F.blockSide : ℝ) * blockCurvatureNorm X y) with hK
  let q : ℕ → Fin 4 → ℤ := fun k => o + LegAlongTree.prefixOffset h π k
  have hq0 : q 0 = o := by
    simp [q, LegAlongTree.prefixOffset_zero]
  have hq4 : q 4 = o' := by
    funext m
    have : (((π.symm m : Fin 4) : ℕ)) < 4 := (π.symm m).2
    simp [q, LegAlongTree.prefixOffset, this, hh]
  have hqb : ∀ k m, q k m = o m ∨ q k m = o' m := by
    intro k m
    simp only [q, LegAlongTree.prefixOffset, Pi.add_apply, hh, Pi.sub_apply]
    by_cases h2 : (((π.symm m : Fin 4) : ℕ)) < k
    · right
      simp [h2]
    · left
      simp [h2]
  have hqi : ∀ k, LegAlongTree.WithinBlock F.blockSide (q k) := by
    intro k m
    rcases hqb k m with h' | h'
    · rw [h']
      exact hb m
    · rw [h']
      exact hb' m
  have step : ∀ k : Fin 4, LegAlongTree.NearTransport
      (pathHolonomy X (refineSite y + siteOfCoords j (q k)) (LegAlongTree.axisSegment h π k))
      (blockTreeTransport X y (q k)) (blockTreeTransport X y (q ((k : ℕ) + 1))) K := by
    intro k
    refine LegAlongTree.nearTransport_of_defect _ _ _ _ ?_
    have hnext : q ((k : ℕ) + 1) = q k + h (π k) • Pi.single (π k) 1 := by
      simp only [q]
      rw [LegAlongTree.prefixOffset_succ, add_assoc]
    have hval : q k (π k) + h (π k) = o' (π k) := by
      simp [q, LegAlongTree.prefixOffset, hh]
    rw [hnext]
    exact LegAlongTree.straightPath_near_tree j hj hL hA X y (q k) (hqi k) (π k) (h (π k))
      (by rw [hval]; exact hb' _)
  have hsite : ∀ k : Fin 4, refineSite y + siteOfCoords j (q k) +
      LegAlongTree.pathDisplacement j (LegAlongTree.axisSegment h π k) =
      refineSite y + siteOfCoords j (q ((k : ℕ) + 1)) := by
    intro k
    have := LegAlongTree.site_after_segment j (refineSite y + siteOfCoords j o) h π k
    simp only [q, LegAlongTree.siteOfCoords_add, add_assoc] at this ⊢
    exact this
  have e0 : axisPath h π = LegAlongTree.axisSegment h π 0 ++
      (LegAlongTree.axisSegment h π 1 ++ (LegAlongTree.axisSegment h π 2 ++
        (LegAlongTree.axisSegment h π 3 ++ []))) :=
    LegAlongTree.axisPath_eq_segments h π
  have n01 := LegAlongTree.nearTransport_mul _ _ _ _ _ _ _ (step 0) (step 1)
  have n02 := LegAlongTree.nearTransport_mul _ _ _ _ _ _ _ n01 (step 2)
  have n03 := LegAlongTree.nearTransport_mul _ _ _ _ _ _ _ n02 (step 3)
  have hhol : pathHolonomy X (refineSite y + siteOfCoords j o) (axisPath h π) =
      pathHolonomy X (refineSite y + siteOfCoords j (q ((0 : Fin 4) : ℕ))) (LegAlongTree.axisSegment h π 0) *
      pathHolonomy X (refineSite y + siteOfCoords j (q ((1 : Fin 4) : ℕ))) (LegAlongTree.axisSegment h π 1) *
      pathHolonomy X (refineSite y + siteOfCoords j (q ((2 : Fin 4) : ℕ))) (LegAlongTree.axisSegment h π 2) *
      pathHolonomy X (refineSite y + siteOfCoords j (q ((3 : Fin 4) : ℕ))) (LegAlongTree.axisSegment h π 3) := by
    have s0 := hsite 0
    have s1 := hsite 1
    have s2 := hsite 2
    have z0 : q ((0 : Fin 4) : ℕ) = o := hq0
    rw [e0, LegAlongTree.pathHolonomy_append, LegAlongTree.pathHolonomy_append,
      LegAlongTree.pathHolonomy_append, LegAlongTree.pathHolonomy_append]
    rw [z0] at s0 ⊢
    rw [s0]
    have e1 : (((0 : Fin 4) : ℕ) + 1) = ((1 : Fin 4) : ℕ) := rfl
    have e2 : (((1 : Fin 4) : ℕ) + 1) = ((2 : Fin 4) : ℕ) := rfl
    have e3 : (((2 : Fin 4) : ℕ) + 1) = ((3 : Fin 4) : ℕ) := rfl
    rw [e1] at *
    rw [s1]
    rw [e2] at *
    rw [s2]
    rw [e3] at *
    simp [pathHolonomy, mul_assoc]
  have hfin : ((3 : Fin 4) : ℕ) + 1 = 4 := rfl
  have hz : q ((0 : Fin 4) : ℕ) = o := hq0
  rw [hhol]
  unfold LegAlongTree.NearTransport at n03
  rw [hfin, hq4, hz] at n03
  have : K + K + K + K = 16 * (F.blockSide : ℝ) * blockCurvatureNorm X y := by
    rw [hK]
    ring
  rw [← this]
  convert n03 using 3
  rw [hz]
end YangMills.Construction.BlockTrees
end
