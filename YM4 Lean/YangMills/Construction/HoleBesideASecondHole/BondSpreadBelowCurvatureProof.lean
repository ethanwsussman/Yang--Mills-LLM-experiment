import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours SquareDescent GroupMeans
namespace BondContours
variable {F : BlockFrame}
theorem unitQuaternion_coe_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem unitQuaternion_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem unitQuaternion_coe_mul_inv (g : UnitQuaternion) :
    (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
theorem norm_unitQuaternion_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, one_mul]
theorem norm_mul_unitQuaternion (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, mul_one]
theorem norm_sub_inv_unitQuaternion (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - g'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem linkValue_reverseStep {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
theorem refineSite_add_stepDisplacement (j : ℕ) (hj : j < F.top) (y : F.Site (j + 1)) (st : PathStep) :
    refineSite (y + stepDisplacement (j + 1) st) = refineSite y + F.blockSide • stepDisplacement j st := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_step <;> assumption
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem pathDisplacement_straightFlow (j : ℕ) (c : ℤ) (i : Fin 4) :
    pathDisplacement (F := F) j (List.replicate c.natAbs (i, decide (0 ≤ c))) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate_axis <;> assumption
def elementarySquare {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (st : PathStep) (i : Fin 4) :
    UnitQuaternion :=
  pathHolonomy X z [st, (i, true), (st.1, !st.2), (i, false)]
def transportDeviation {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (P : List PathStep) (i : Fin 4)
    (M : ℕ) : ℝ :=
  ‖((pathHolonomy X x (P ++ List.replicate M (i, true) ++ reversePath P) : UnitQuaternion) : ℍ[ℝ]) -
    (pathHolonomy X x (List.replicate M (i, true)) : UnitQuaternion)‖
theorem reversePath_append (P Q : List PathStep) :
    reversePath (P ++ Q) = reversePath Q ++ reversePath P := by
  simp [reversePath]
theorem transportDeviation_append {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (P Q : List PathStep)
    (i : Fin 4) (M : ℕ) :
    transportDeviation X x (P ++ Q) i M ≤
      transportDeviation X x P i M + transportDeviation X (x + pathDisplacement j P) Q i M := by
  unfold transportDeviation
  set R := List.replicate M (i, true)
  set x1 := x + pathDisplacement j P
  set a := pathHolonomy X x P
  set b := pathHolonomy X (x1 + pathDisplacement j R) (reversePath P)
  have e1 : pathHolonomy X x ((P ++ Q) ++ R ++ reversePath (P ++ Q)) =
      a * pathHolonomy X x1 (Q ++ R ++ reversePath Q) * b := by
    have e : (P ++ Q) ++ R ++ reversePath (P ++ Q) =
        P ++ ((Q ++ R ++ reversePath Q) ++ reversePath P) := by
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
    rw [e3, unitQuaternion_coe_mul, unitQuaternion_coe_mul, unitQuaternion_coe_mul,
      unitQuaternion_coe_mul]
    noncomm_ring
  rw [e4]
  refine (norm_add_le _ _).trans ?_
  rw [norm_unitQuaternion_mul, norm_mul_unitQuaternion]
  linarith
theorem transportDeviation_nil {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (i : Fin 4) (M : ℕ) :
    transportDeviation X x [] i M = 0 := by
  simp [transportDeviation, reversePath]
theorem transportDeviation_single_le {j : ℕ} (X : F.GaugeField j) (st : PathStep) (i : Fin 4) (M : ℕ) :
    ∀ x : F.Site j, transportDeviation X x [st] i M ≤
      ∑ r ∈ Finset.range M,
        ‖((elementarySquare X (x + r • unitStep j i) st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  induction M with
  | zero =>
    intro x
    have e : pathHolonomy X x ([st] ++ List.replicate 0 (i, true) ++ reversePath [st]) = 1 := by
      have h := pathHolonomy_reversePath X [st] x
      have e2 : [st] ++ List.replicate 0 (i, true) ++ reversePath [st] = [st] ++ reversePath [st] := by
        simp
      rw [e2, pathHolonomy_append, h, mul_inv_cancel]
    unfold transportDeviation
    rw [e]
    simp [pathHolonomy]
  | succ M ih =>
    intro x
    set e := unitStep j i with he
    have hsum : ∑ r ∈ Finset.range (M + 1),
          ‖((elementarySquare X (x + r • e) st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
        ∑ r ∈ Finset.range M,
          ‖((elementarySquare X (x + e + r • e) st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
          ‖((elementarySquare X x st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
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
    unfold transportDeviation
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
      have : [st] ++ (i, true) :: R ++ [(st.1, !st.2)] = st :: (i, true) :: (R ++ [(st.1, !st.2)]) := by
        simp
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
    have eS : elementarySquare X x st i = a * b * a'⁻¹ * c⁻¹ := by
      unfold elementarySquare
      simp only [pathHolonomy, mul_one]
      have e6 : linkValue X (x + e + stepDisplacement j st) (st.1, !st.2) = (linkValue X (x + e) st)⁻¹ :=
        linkValue_reverseStep X (x + e) st
      have e7 : linkValue X (x + stepDisplacement j (i, true)) (i, false) = (linkValue X x (i, true))⁻¹ :=
        linkValue_reverseStep X x (i, true)
      have e8 : x + stepDisplacement j st + stepDisplacement j (i, true) =
          x + e + stepDisplacement j st := by
        rw [hstep]
        abel
      have e9 : x + stepDisplacement j st + stepDisplacement j (i, true) +
          stepDisplacement j (st.1, !st.2) = x + stepDisplacement j (i, true) := by
        obtain ⟨d, s⟩ := st
        cases s <;> simp [stepDisplacement] <;> abel
      rw [e9, e8, e6, e7]
      simp only [a, b, a', c, mul_assoc]
    rw [hR1, e1, e3, e2]
    have e4 : ((a * b * A' * a2 : UnitQuaternion) : ℍ[ℝ]) - ((c * B : UnitQuaternion) : ℍ[ℝ]) =
        (((elementarySquare X x st i : UnitQuaternion) : ℍ[ℝ]) - 1) *
            (((c * (a' * A' * a2) : UnitQuaternion)) : ℍ[ℝ]) +
          (c : ℍ[ℝ]) * (((a' * A' * a2 : UnitQuaternion) : ℍ[ℝ]) - (B : ℍ[ℝ])) := by
      have h : a * b * A' * a2 = elementarySquare X x st i * (c * (a' * A' * a2)) := by
        rw [eS]
        group
      rw [h, unitQuaternion_coe_mul (elementarySquare X x st i), unitQuaternion_coe_mul c B, sub_mul,
        one_mul, mul_sub, ← unitQuaternion_coe_mul c (a' * A' * a2)]
      abel
    rw [e4]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul_unitQuaternion, norm_unitQuaternion_mul]
    linarith
theorem transportDeviation_replicate_le {j : ℕ} (X : F.GaugeField j) (st : PathStep) (i : Fin 4)
    (M m : ℕ) :
    ∀ x : F.Site j, transportDeviation X x (List.replicate m st) i M ≤
      ∑ r ∈ Finset.range m, transportDeviation X (x + r • stepDisplacement j st) [st] i M := by
  induction m with
  | zero =>
    intro x
    simp [transportDeviation_nil]
  | succ m ih =>
    intro x
    have e : List.replicate (m + 1) st = [st] ++ List.replicate m st := rfl
    rw [e, Finset.sum_range_succ']
    refine (transportDeviation_append X x [st] _ i M).trans ?_
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
      ‖((plaquetteHolonomy X (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  have h := pathHolonomy_reversePath X [(μ, true), (ν, true), (μ, false), (ν, false)] x
  have e0 : pathDisplacement (F := F) j [(μ, true), (ν, true), (μ, false), (ν, false)] = 0 := by
    simp only [pathDisplacement, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      stepDisplacement, if_true, Bool.false_eq_true, if_false]
    abel
  have e1 : reversePath [(μ, true), (ν, true), (μ, false), (ν, false)] =
      [(ν, true), (μ, true), (ν, false), (μ, false)] := by
    simp [reversePath]
  rw [e0, e1, add_zero] at h
  have e2 : plaquetteHolonomy X (x, ν, μ) = (plaquetteHolonomy X (x, μ, ν))⁻¹ := h
  rw [e2]
  have := norm_sub_inv_unitQuaternion (plaquetteHolonomy X (x, μ, ν)) 1
  simpa using this
theorem unitQuaternion_conj_defect (a b : UnitQuaternion) :
    ‖((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem plaquetteDefect_ordered {j : ℕ} (X : F.GaugeField j) (b : F.Site j) (d i : Fin 4) :
    plaquetteDefect X (b, min d i, max d i) =
      ‖((plaquetteHolonomy X (b, d, i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  unfold plaquetteDefect
  rcases le_total d i with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact plaquetteHolonomy_swap_defect X b d i |>.symm ▸ rfl
theorem elementarySquare_forward {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (d i : Fin 4) :
    ‖((elementarySquare X z (d, true) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      plaquetteDefect X (squarePlaquette z (d, true) i) := by
  simp only [squarePlaquette, squareBase, if_true]
  rw [plaquetteDefect_ordered]
  rfl
theorem elementarySquare_backward {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (d i : Fin 4) :
    ‖((elementarySquare X z (d, false) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      plaquetteDefect X (squarePlaquette z (d, false) i) := by
  simp only [squarePlaquette, squareBase, Bool.false_eq_true, if_false]
  rw [plaquetteDefect_ordered, ← plaquetteHolonomy_swap_defect]
  set z' := z - unitStep j d with hz'
  have e0 : z + stepDisplacement j (d, false) = z' := by
    simp [stepDisplacement, hz', sub_eq_add_neg]
  have e1 : z' + stepDisplacement j (i, true) + stepDisplacement j (d, true) +
      stepDisplacement j (i, false) = z := by
    simp only [stepDisplacement, if_true, Bool.false_eq_true, if_false, hz']
    abel
  have e2 : elementarySquare X z (d, false) i =
      linkValue X z (d, false) * plaquetteHolonomy X (z', i, d) * (linkValue X z (d, false))⁻¹ := by
    simp only [elementarySquare, plaquetteHolonomy, pathHolonomy, mul_one, Bool.not_false]
    rw [e0, e1]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [e2, unitQuaternion_conj_defect]
theorem elementarySquare_defect {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (st : PathStep) (i : Fin 4) :
    ‖((elementarySquare X z st i : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      plaquetteDefect X (squarePlaquette z st i) := by
  obtain ⟨d, b⟩ := st
  cases b
  · exact elementarySquare_backward X z d i
  · exact elementarySquare_forward X z d i
theorem elementarySquare_degenerate {j : ℕ} (X : F.GaugeField j) (z : F.Site j) (b : Bool) (i : Fin 4) :
    elementarySquare X z (i, b) i = 1 := by
  cases b
  · simp only [elementarySquare, pathHolonomy, mul_one, Bool.not_false]
    have e0 : linkValue X (z + stepDisplacement j (i, false)) (i, true) =
        (linkValue X z (i, false))⁻¹ :=
      linkValue_reverseStep X z (i, false)
    have e1 : linkValue X (z + stepDisplacement j (i, false) + stepDisplacement j (i, true) +
          stepDisplacement j (i, true)) (i, false) =
        (linkValue X (z + stepDisplacement j (i, false) + stepDisplacement j (i, true)) (i, true))⁻¹ :=
      linkValue_reverseStep X (z + stepDisplacement j (i, false) + stepDisplacement j (i, true)) (i, true)
    rw [e1, e0]
    simp
  · simp only [elementarySquare, pathHolonomy, mul_one, Bool.not_true]
    have e0 : linkValue X (z + stepDisplacement j (i, true) + stepDisplacement j (i, true)) (i, false) =
        (linkValue X (z + stepDisplacement j (i, true)) (i, true))⁻¹ :=
      linkValue_reverseStep X (z + stepDisplacement j (i, true)) (i, true)
    have e1 : linkValue X (z + stepDisplacement j (i, true) + stepDisplacement j (i, true) +
          stepDisplacement j (i, false)) (i, false) =
        (linkValue X z (i, true))⁻¹ := by
      have e2 : z + stepDisplacement j (i, true) + stepDisplacement j (i, true) +
          stepDisplacement j (i, false) = z + stepDisplacement j (i, true) := by
        simp [stepDisplacement]
      rw [e2]
      exact linkValue_reverseStep X z (i, true)
    rw [e1, e0]
    simp
theorem unitStep_apply_ne (j : ℕ) (i k : Fin 4) (hk : i ≠ k) : (unitStep j i : F.Site j) k = 0 := by
  simp [unitStep, siteOfCoords, Pi.single_apply, hk.symm]
theorem unitStep_apply_self (j : ℕ) (i : Fin 4) : (unitStep j i : F.Site j) i = 1 := by
  simp [unitStep, siteOfCoords]
theorem natCast_zmod_injective_of_lt {p r r' : ℕ} (h : (r : ZMod p) = r')
    (hp : p = 0 ∨ (r < p ∧ r' < p)) : r = r' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rcases hp with rfl | ⟨h1, h2⟩
  · simpa using h
  · rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
theorem squarePlaquette_injOn {j : ℕ} (x : F.Site j) (st : PathStep) (i : Fin 4) (m M : ℕ)
    (hne : st.1 ≠ i)
    (hp : ∀ k, F.period j k = 0 ∨ (m ≤ F.period j k ∧ M ≤ F.period j k)) :
    Set.InjOn
      (fun q : ℕ × ℕ => squarePlaquette (x + q.1 • stepDisplacement j st + q.2 • unitStep j i) st i)
      (Finset.range m ×ˢ Finset.range M : Finset (ℕ × ℕ)) := by
  rintro ⟨r1, r2⟩ h1 ⟨r1', r2'⟩ h2 he
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at h1 h2
  have hb := congrArg Prod.fst he
  simp only [squarePlaquette, squareBase] at hb
  have hz : x + r1 • stepDisplacement j st + r2 • unitStep j i =
      x + r1' • stepDisplacement j st + r2' • unitStep j i := by
    split_ifs at hb
    · exact hb
    · exact sub_left_injective hb
  have hz' : r1 • (stepDisplacement j st : F.Site j) + r2 • (unitStep j i : F.Site j) =
      r1' • (stepDisplacement j st : F.Site j) + r2' • (unitStep j i : F.Site j) := by
    have h := hz
    rw [add_assoc, add_assoc] at h
    exact add_left_cancel h
  obtain ⟨d, b⟩ := st
  simp only at hne
  have c1 := congrFun hz' d
  have c2 := congrFun hz' i
  have e1 : (r1 : ZMod (F.period j d)) = r1' := by
    cases b
    · simp only [stepDisplacement, Bool.false_eq_true, if_false, Pi.add_apply, Pi.smul_apply,
        Pi.neg_apply, unitStep_apply_ne j i d hne.symm, unitStep_apply_self] at c1
      simp only [nsmul_eq_mul, mul_zero, add_zero, mul_neg, mul_one] at c1
      exact neg_injective c1
    · simp only [stepDisplacement, if_true, Pi.add_apply, Pi.smul_apply,
        unitStep_apply_ne j i d hne.symm, unitStep_apply_self] at c1
      simp only [nsmul_eq_mul, mul_zero, add_zero, mul_one] at c1
      exact c1
  have e2 : (r2 : ZMod (F.period j i)) = r2' := by
    cases b
    · simp only [stepDisplacement, Bool.false_eq_true, if_false, Pi.add_apply, Pi.smul_apply,
        Pi.neg_apply, unitStep_apply_ne j d i hne, unitStep_apply_self] at c2
      simp only [nsmul_eq_mul, mul_zero, add_zero, mul_one, neg_zero, zero_add] at c2
      exact c2
    · simp only [stepDisplacement, if_true, Pi.add_apply, Pi.smul_apply,
        unitStep_apply_ne j d i hne, unitStep_apply_self] at c2
      simp only [nsmul_eq_mul, mul_zero, add_zero, mul_one, zero_add] at c2
      exact c2
  have f1 : r1 = r1' := natCast_zmod_injective_of_lt e1 (by
    rcases hp d with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩)
  have f2 : r2 = r2' := natCast_zmod_injective_of_lt e2 (by
    rcases hp i with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩)
  rw [f1, f2]
theorem transportDeviation_straightFlow_sq_le {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep)
    (i : Fin 4) (m M : ℕ) (B : Finset (F.Site j × Fin 4 × Fin 4))
    (hmem : st.1 ≠ i → ∀ r1 < m, ∀ r2 < M,
      squarePlaquette (x + r1 • stepDisplacement j st + r2 • unitStep j i) st i ∈ B)
    (hp : ∀ k, F.period j k = 0 ∨ (m ≤ F.period j k ∧ M ≤ F.period j k)) :
    transportDeviation X x (List.replicate m st) i M ^ 2 ≤
      (m : ℝ) * M * ∑ p ∈ B, plaquetteDefect X p ^ 2 := by
  classical
  have hG : 0 ≤ ∑ p ∈ B, plaquetteDefect X p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have h0 : 0 ≤ transportDeviation X x (List.replicate m st) i M := norm_nonneg _
  by_cases hne : st.1 = i
  · have hz : transportDeviation X x (List.replicate m st) i M ≤ 0 := by
      refine (transportDeviation_replicate_le X st i M m x).trans ?_
      refine Finset.sum_nonpos fun r _ => ?_
      refine (transportDeviation_single_le X st i M _).trans (le_of_eq ?_)
      refine Finset.sum_eq_zero fun r' _ => ?_
      obtain ⟨d, b⟩ := st
      simp only at hne
      subst hne
      rw [elementarySquare_degenerate]
      simp
    have : transportDeviation X x (List.replicate m st) i M = 0 := le_antisymm hz h0
    rw [this]
    have h00 : (0 : ℝ) ≤ (m : ℝ) * M := by positivity
    have := mul_nonneg h00 hG
    simpa using this
  · have h1 : transportDeviation X x (List.replicate m st) i M ≤
        ∑ q ∈ Finset.range m ×ˢ Finset.range M,
          plaquetteDefect X (squarePlaquette (x + q.1 • stepDisplacement j st + q.2 • unitStep j i) st i) := by
      refine (transportDeviation_replicate_le X st i M m x).trans ?_
      rw [Finset.sum_product]
      refine Finset.sum_le_sum fun r _ => ?_
      refine (transportDeviation_single_le X st i M _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [elementarySquare_defect]
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
def InCentredBlock (L : ℕ) (o : Fin 4 → ℤ) : Prop := ∀ m, |o m| ≤ ((L : ℤ) - 1) / 2
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem mem_centredCube_of_inCentredBlock {L : ℕ} {o : Fin 4 → ℤ} (ho : InCentredBlock L o) :
    o ∈ centredCube L := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_of_withinBlock <;> assumption
theorem inCentredBlock_of_mem_centredCube {L : ℕ} {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) :
    InCentredBlock L o := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.withinBlock_of_mem_centredCube <;> assumption
theorem refineSite_add_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o : Fin 4 → ℤ}
    (ho : InCentredBlock F.blockSide o) :
    refineSite y + siteOfCoords j o ∈ sitesBelow j y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_mem_sitesBelow <;> assumption
theorem add_smul_single_apply (o : Fin 4 → ℤ) (c : ℤ) (i m : Fin 4) :
    (o + c • (Pi.single i 1 : Fin 4 → ℤ)) m = o m + if m = i then c else 0 := by apply _root_.YangMills.Construction.GaugeFixing.add_smul_single_apply <;> assumption
theorem mem_sitesBelow_union (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (y : F.Site (j + 1))
    (i : Fin 4) {o : Fin 4 → ℤ} (ho : InCentredBlock F.blockSide o) (r : ℕ) (hr : r ≤ F.blockSide) :
    refineSite y + siteOfCoords j o + r • unitStep j i ∈
      sitesBelow j y ∪ sitesBelow j (y + unitStep (j + 1) i) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_adjacent_blocks <;> assumption
theorem plaquette_mem_blockPairPlaquettes (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (y : F.Site (j + 1)) (d i : Fin 4) (hne : d ≠ i)
    {lo : Fin 4 → ℤ} (h1 : InCentredBlock F.blockSide lo)
    (h2 : InCentredBlock F.blockSide (lo + (1 : ℤ) • Pi.single d 1))
    (r : ℕ) (hr : r < F.blockSide) :
    (refineSite y + siteOfCoords j lo + r • unitStep j i, min d i, max d i) ∈
      blockPairPlaquettes (y, i) := by
  have a1 := mem_sitesBelow_union j hj hL y i h1 r hr.le
  have a2 := mem_sitesBelow_union j hj hL y i h2 r hr.le
  have a3 := mem_sitesBelow_union j hj hL y i h1 (r + 1) hr
  have a4 := mem_sitesBelow_union j hj hL y i h2 (r + 1) hr
  rw [siteOfCoords_add, siteOfCoords_single, one_smul] at a2 a4
  rw [add_smul, one_smul] at a3 a4
  simp only [blockPairPlaquettes, cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    and_true]
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
theorem squarePlaquette_mem_blockPairPlaquettes (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (y : F.Site (j + 1)) (i : Fin 4) (o : Fin 4 → ℤ) (st : PathStep) (m : ℕ) (hne : st.1 ≠ i)
    (hC : ∀ r ≤ m, InCentredBlock F.blockSide
      (o + (if st.2 then (r : ℤ) else -(r : ℤ)) • Pi.single st.1 1)) :
    ∀ r1 < m, ∀ r2 < F.blockSide,
      squarePlaquette (refineSite y + siteOfCoords j o + r1 • stepDisplacement j st + r2 • unitStep j i)
        st i ∈ blockPairPlaquettes (y, i) := by
  intro r1 h1 r2 h2
  obtain ⟨d, b⟩ := st
  simp only at hne hC
  cases b
  · simp only [Bool.false_eq_true, if_false] at hC
    have hlo := hC (r1 + 1) h1
    have hhi := hC r1 h1.le
    have e1 : o + (-((r1 + 1 : ℕ) : ℤ)) • Pi.single d 1 + (1 : ℤ) • Pi.single d 1 =
        o + (-(r1 : ℤ)) • Pi.single d 1 := by
      rw [add_assoc, ← add_smul]
      congr 2
      push_cast
      ring
    have := plaquette_mem_blockPairPlaquettes j hj hL y d i hne hlo (by rw [e1]; exact hhi) r2 h2
    convert this using 1
    simp only [squarePlaquette, squareBase, Bool.false_eq_true, if_false, stepDisplacement]
    congr 1
    rw [siteOfCoords_add, siteOfCoords_single, neg_smul, natCast_zsmul, add_smul, one_smul, smul_neg]
    abel
  · simp only [if_true] at hC
    have hlo := hC r1 h1.le
    have hhi := hC (r1 + 1) h1
    have e1 : o + ((r1 : ℤ)) • Pi.single d 1 + (1 : ℤ) • Pi.single d 1 =
        o + ((r1 + 1 : ℕ) : ℤ) • Pi.single d 1 := by
      rw [add_assoc, ← add_smul]
      congr 2
    have := plaquette_mem_blockPairPlaquettes j hj hL y d i hne hlo (by rw [e1]; exact hhi) r2 h2
    convert this using 1
    simp only [squarePlaquette, squareBase, if_true, stepDisplacement]
    congr 1
    rw [siteOfCoords_add, siteOfCoords_single, natCast_zsmul]
    abel
def partialDisplacement (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem partialDisplacement_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    partialDisplacement h π 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_zero <;> assumption
theorem inCentredBlock_partialDisplacement (L : ℕ) (h : Fin 4 → ℤ) (hh : InCentredBlock L h)
    (π : Equiv.Perm (Fin 4)) (k : Fin 4) (r : ℕ) (hr : r ≤ (h (π k)).natAbs) :
    InCentredBlock L (partialDisplacement h π k +
      (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.axisPathOffset_flow_withinBlock <;> assumption
theorem axisPath_eq_flows (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_eq_append <;> assumption
def axisBondPath (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) : List PathStep :=
  List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
theorem partialDisplacement_next (j : ℕ) (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4))
    (k : Fin 4) :
    x + siteOfCoords j (partialDisplacement h π k) + pathDisplacement j (axisBondPath h π k) =
      x + siteOfCoords j (partialDisplacement h π ((k : ℕ) + 1)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.add_axisPathFlow <;> assumption
theorem transportDeviation_axisPath_le {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (h : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) (M : ℕ) :
    transportDeviation X x (axisPath h π) i M ≤ ∑ k : Fin 4,
      transportDeviation X (x + siteOfCoords j (partialDisplacement h π k)) (axisBondPath h π k) i M := by
  rw [axisPath_eq_flows, Fin.sum_univ_four]
  have z0 : x + siteOfCoords j (partialDisplacement h π ((0 : Fin 4) : ℕ)) = x := by
    simp [partialDisplacement_zero, siteOfCoords_zero]
  have s0 := partialDisplacement_next j x h π 0
  have s1 := partialDisplacement_next j x h π 1
  have s2 := partialDisplacement_next j x h π 2
  have b0 := transportDeviation_append X x (axisBondPath h π 0)
    (axisBondPath h π 1 ++ (axisBondPath h π 2 ++ (axisBondPath h π 3 ++ []))) i M
  have b1 := transportDeviation_append X (x + siteOfCoords j (partialDisplacement h π ((1 : Fin 4) : ℕ)))
    (axisBondPath h π 1) (axisBondPath h π 2 ++ (axisBondPath h π 3 ++ [])) i M
  have b2 := transportDeviation_append X (x + siteOfCoords j (partialDisplacement h π ((2 : Fin 4) : ℕ)))
    (axisBondPath h π 2) (axisBondPath h π 3 ++ []) i M
  have b3 := transportDeviation_append X (x + siteOfCoords j (partialDisplacement h π ((3 : Fin 4) : ℕ)))
    (axisBondPath h π 3) [] i M
  rw [transportDeviation_nil] at b3
  rw [z0] at s0 ⊢
  have e01 : x + pathDisplacement j (axisBondPath h π 0) =
      x + siteOfCoords j (partialDisplacement h π ((1 : Fin 4) : ℕ)) := by
    have : (((0 : Fin 4) : ℕ) + 1) = ((1 : Fin 4) : ℕ) := rfl
    rw [← this, ← s0]
  have e12 : x + siteOfCoords j (partialDisplacement h π ((1 : Fin 4) : ℕ)) +
      pathDisplacement j (axisBondPath h π 1) =
      x + siteOfCoords j (partialDisplacement h π ((2 : Fin 4) : ℕ)) := s1
  have e23 : x + siteOfCoords j (partialDisplacement h π ((2 : Fin 4) : ℕ)) +
      pathDisplacement j (axisBondPath h π 2) =
      x + siteOfCoords j (partialDisplacement h π ((3 : Fin 4) : ℕ)) := s2
  rw [e01] at b0
  rw [e12] at b1
  rw [e23] at b2
  simp only [axisBondPath] at b0 b1 b2 b3 ⊢
  linarith
theorem period_eq_zero_or_le (j : ℕ) (hj : j < F.top) (hA : IsAdmissibleAmbient F)
    (hL : 0 < F.blockSide) (k : Fin 4) :
    F.period j k = 0 ∨ F.blockSide ≤ F.period j k := by
  have hs : F.extent k = 0 ∨ 64 ≤ F.extent k := by
    rcases hA with h | h
    · exact Or.inl (h k)
    · exact Or.inr (h k)
  rcases hs with h | h
  · left
    simp [BlockFrame.period, h]
  · right
    have h1 : F.blockSide ≤ F.blockSide ^ (F.top - j) := Nat.le_self_pow (by omega) _
    have h2 : F.blockSide ^ (F.top - j) ≤ F.extent k * F.blockSide ^ (F.top - j) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact h1.trans h2
theorem natAbs_le_blockSide (hL : Odd F.blockSide) {h : Fin 4 → ℤ} (hh : InCentredBlock F.blockSide h)
    (m : Fin 4) : (h m).natAbs ≤ F.blockSide := by
  have h1 := hh m
  obtain ⟨k, hk⟩ := hL
  have hhalf : ((F.blockSide : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  rw [hhalf] at h1
  have h2 : ((h m).natAbs : ℤ) ≤ k := by
    rw [Int.natCast_natAbs]
    exact h1
  omega
theorem transportDeviation_axisFlow_sq_le (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (hA : IsAdmissibleAmbient F) (W : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ)
    (hh : InCentredBlock F.blockSide h) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    transportDeviation W (refineSite c.1 + siteOfCoords j (partialDisplacement h π k)) (axisBondPath h π k)
        c.2 F.blockSide ^ 2 ≤
      (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 := by
  have hG : 0 ≤ ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hm := natAbs_le_blockSide hL hh (π k)
  have h1 := transportDeviation_straightFlow_sq_le W
    (refineSite c.1 + siteOfCoords j (partialDisplacement h π k)) (π k, decide (0 ≤ h (π k))) c.2
    (h (π k)).natAbs F.blockSide (blockPairPlaquettes c)
    (fun hne => squarePlaquette_mem_blockPairPlaquettes j hj hL c.1 c.2 (partialDisplacement h π k) _ _ hne
      (fun r hr => inCentredBlock_partialDisplacement F.blockSide h hh π k r hr))
    (fun k' => by
      rcases period_eq_zero_or_le j hj hA hL.pos k' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨hm.trans h', h'⟩)
  refine h1.trans ?_
  have hm' : ((h (π k)).natAbs : ℝ) ≤ F.blockSide := by exact_mod_cast hm
  have : ((h (π k)).natAbs : ℝ) * F.blockSide ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right this hG
theorem contourHolonomy_deviation_sq_le (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (hA : IsAdmissibleAmbient F) (W : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) (he : e ∈ allContours F) :
    ‖((contourHolonomy W c e : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy W (refineSite c.1) (List.replicate F.blockSide (c.2, true)) : UnitQuaternion)‖ ^ 2 ≤
      16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 := by
  have hh : InCentredBlock F.blockSide e.1 :=
    inCentredBlock_of_mem_centredCube (Finset.mem_product.1 he).1
  have e0 : ‖((contourHolonomy W c e : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy W (refineSite c.1) (List.replicate F.blockSide (c.2, true)) : UnitQuaternion)‖ =
      transportDeviation W (refineSite c.1) (axisPath e.1 e.2) c.2 F.blockSide := rfl
  rw [e0]
  have h1 := transportDeviation_axisPath_le W (refineSite c.1) e.1 e.2 c.2 F.blockSide
  rw [Fin.sum_univ_four] at h1
  have q0 := transportDeviation_axisFlow_sq_le j hj hL hA W c e.1 hh e.2 0
  have q1 := transportDeviation_axisFlow_sq_le j hj hL hA W c e.1 hh e.2 1
  have q2 := transportDeviation_axisFlow_sq_le j hj hL hA W c e.1 hh e.2 2
  have q3 := transportDeviation_axisFlow_sq_le j hj hL hA W c e.1 hh e.2 3
  have h0 : 0 ≤ transportDeviation W (refineSite c.1) (axisPath e.1 e.2) c.2 F.blockSide := norm_nonneg _
  set A := transportDeviation W (refineSite c.1 + siteOfCoords j (partialDisplacement e.1 e.2 ((0 : Fin 4) : ℕ)))
    (axisBondPath e.1 e.2 0) c.2 F.blockSide
  set B := transportDeviation W (refineSite c.1 + siteOfCoords j (partialDisplacement e.1 e.2 ((1 : Fin 4) : ℕ)))
    (axisBondPath e.1 e.2 1) c.2 F.blockSide
  set C := transportDeviation W (refineSite c.1 + siteOfCoords j (partialDisplacement e.1 e.2 ((2 : Fin 4) : ℕ)))
    (axisBondPath e.1 e.2 2) c.2 F.blockSide
  set D := transportDeviation W (refineSite c.1 + siteOfCoords j (partialDisplacement e.1 e.2 ((3 : Fin 4) : ℕ)))
    (axisBondPath e.1 e.2 3) c.2 F.blockSide
  set G := (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 with hGdef
  have h2 : (A + B + C + D) ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (B - C),
      sq_nonneg (B - D), sq_nonneg (C - D)]
  have h3 : transportDeviation W (refineSite c.1) (axisPath e.1 e.2) c.2 F.blockSide ^ 2 ≤
      (A + B + C + D) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have e1 : 16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 = 16 * G := by
    rw [hGdef]
    ring
  rw [e1]
  linarith
theorem squareHolonomyDefect_le_sum {j : ℕ} (W : F.GaugeField j) (x : F.Site j) (N : ℕ) (μ ν : Fin 4)
    (h : μ < ν) :
    squareHolonomyDefect W x N μ ν ≤ ∑ r ∈ Finset.range N, ∑ r' ∈ Finset.range N,
      plaquetteDefect W (x + r • unitStep j μ + r' • unitStep j ν, μ, ν) := by
  have e1 : squareHolonomyDefect W x N μ ν = transportDeviation W x (List.replicate N (μ, true)) ν N := by
    unfold squareHolonomyDefect transportDeviation squarePath
    have hr : reversePath (List.replicate N (μ, true)) = List.replicate N (μ, false) := by
      simp [reversePath, List.map_replicate]
    rw [hr, pathHolonomy_append]
    set P := List.replicate N (μ, true) ++ List.replicate N (ν, true) ++ List.replicate N (μ, false)
    set a := pathHolonomy W x P
    have h1 := pathHolonomy_reversePath W (List.replicate N (ν, true)) x
    have hr2 : reversePath (List.replicate N (ν, true)) = List.replicate N (ν, false) := by
      simp [reversePath, List.map_replicate]
    have e2 : x + pathDisplacement j P = x + pathDisplacement j (List.replicate N (ν, true)) := by
      simp only [P, pathDisplacement_append, pathDisplacement_replicate, stepDisplacement, if_true,
        Bool.false_eq_true, if_false]
      simp only [smul_neg]
      abel
    rw [hr2] at h1
    rw [e2, h1]
    set b := pathHolonomy W x (List.replicate N (ν, true))
    have e3 : ((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
        ((a : ℍ[ℝ]) - b) * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [unitQuaternion_coe_mul, sub_mul, unitQuaternion_coe_mul_inv]
    rw [e3, norm_mul_unitQuaternion]
  rw [e1]
  refine (transportDeviation_replicate_le W (μ, true) ν N N x).trans ?_
  refine Finset.sum_le_sum fun r _ => ?_
  refine (transportDeviation_single_le W (μ, true) ν N _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [elementarySquare_defect]
  simp only [squarePlaquette, squareBase, if_true, min_eq_left h.le, max_eq_right h.le, stepDisplacement]
theorem contourVarianceCurvatureBound_of_meanProductEstimate (hm : MeanProductEstimate) :
    ContourVarianceCurvatureBound := by
  refine ⟨?_, fun F j W x N μ ν h => squareHolonomyDefect_le_sum W x N μ ν h⟩
  intro F j hj hL hA W c
  have hne : (allContours F).Nonempty := by
    refine Finset.Nonempty.product ?_ Finset.univ_nonempty
    exact ⟨fun _ => 0, mem_centredCube_of_inCentredBlock (fun m => by
      obtain ⟨k, hk⟩ := hL
      rw [hk]
      push_cast
      simp only [Pi.zero_apply, abs_zero]
      omega)⟩
  obtain ⟨-, hs, -, -⟩ := hm _ (allContours F) hne
  have h1 := hs (contourHolonomy W c)
    (pathHolonomy W (refineSite c.1) (List.replicate F.blockSide (c.2, true)))
  refine h1.trans ?_
  unfold average
  calc (1 / ((allContours F).card : ℝ)) * ∑ e ∈ allContours F,
        ‖((contourHolonomy W c e : UnitQuaternion) : ℍ[ℝ]) -
          (pathHolonomy W (refineSite c.1) (List.replicate F.blockSide (c.2, true)) : UnitQuaternion)‖ ^ 2
      ≤ (1 / ((allContours F).card : ℝ)) * ∑ _e ∈ allContours F,
        16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun e he => contourHolonomy_deviation_sq_le j hj hL hA W c e he)
          (by positivity)
    _ = 16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
end BondContours
end YangMills.Construction
end
