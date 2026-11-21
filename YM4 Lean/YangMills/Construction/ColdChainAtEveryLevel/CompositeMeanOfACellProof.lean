import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfACellForm
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CompositeMean
open BlockAverages PotentialMeans LatticeFractionalIntegration
variable {F : BlockFrame}
def cellAverage {E : Type} [AddCommMonoid E] [Module ℝ E] {j : ℕ} (g : F.Site j → E) (y : F.Site (j + 1)) : E :=
  (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h)
def nestedAverage {E : Type} [AddCommMonoid E] [Module ℝ E] (g : F.Site 0 → E) : (j : ℕ) → F.Site j → E
  | 0 => g
  | j + 1 => cellAverage (nestedAverage g j)
theorem baseSite_refineSite_add (j : ℕ) (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (h h' : Lattice4) :
    baseSite (refineSite y + siteOfCoords j h) + siteOfCoords 0 h' =
      baseSite y + siteOfCoords 0 (fun k => ((F.blockSide ^ j : ℕ) : ℤ) * h k + h' k) := by
  rw [baseSite_add j (by omega), baseSite_refineSite j hj, add_assoc, ← siteOfCoords_add]
  congr 2
theorem baseSite_eq_self (x : F.Site 0) : baseSite x = x := PatchForms.baseSite_depth_zero x
theorem nestedAverage_eq_flat {E : Type} [AddCommMonoid E] [Module ℝ E] (hodd : Odd F.blockSide) (g : F.Site 0 → E)
    (j : ℕ) (hj : j ≤ F.top) (y : F.Site j) :
    nestedAverage g j y = (1 / ((F.blockSide : ℝ) ^ j) ^ 4) •
      ∑ h ∈ centredCube (F.blockSide ^ j), g (baseSite y + siteOfCoords 0 h) := by
  induction j with
  | zero =>
    simp only [pow_zero, centredCube_one, Finset.sum_singleton]
    simp [nestedAverage, baseSite_eq_self, siteOfCoords_zero]
  | succ j ih =>
    have hj' : j ≤ F.top := by omega
    have hM : Odd (F.blockSide ^ j) := hodd.pow
    have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    show cellAverage (nestedAverage g j) y = _
    simp only [cellAverage]
    have h1 : ∀ h : Lattice4, nestedAverage g j (refineSite y + siteOfCoords j h) =
        (1 / ((F.blockSide : ℝ) ^ j) ^ 4) • ∑ h' ∈ centredCube (F.blockSide ^ j),
          g (baseSite y + siteOfCoords 0 (fun k => ((F.blockSide ^ j : ℕ) : ℤ) * h k + h' k)) := by
      intro h
      rw [ih hj']
      simp only [baseSite_refineSite_add j hj y h]
    simp only [h1]
    have e2 : ((F.blockSide : ℝ) ^ (j + 1)) ^ 4 = (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) ^ j) ^ 4 := by ring
    have e3 : F.blockSide ^ (j + 1) = F.blockSide * F.blockSide ^ j := by ring
    rw [e2, e3, ← sum_centredCube_mul hodd hM (fun H => g (baseSite y + siteOfCoords 0 H))]
    simp only [← Finset.smul_sum]
    rw [smul_smul]
    congr 1
    field_simp
theorem cellAverage_nonneg {j : ℕ} {g : F.Site j → ℝ} (hg : ∀ x, 0 ≤ g x) (y : F.Site (j + 1)) :
    0 ≤ cellAverage g y := by
  unfold cellAverage
  rw [smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun h _ => hg _)
theorem card_centredCube_blockSide (hodd : Odd F.blockSide) :
    ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
  rw [card_centredCube_odd hodd]
  push_cast
  rfl
theorem cellAverage_sq_le (hodd : Odd F.blockSide) {j : ℕ} (g : F.Site j → ℝ) (y : F.Site (j + 1)) :
    cellAverage g y ^ 2 ≤
      (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h) ^ 2 := by
  have hL0 : (0 : ℝ) < (F.blockSide : ℝ) ^ 4 := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  have h := sq_sum_le_card_mul_sum_sq (s := centredCube F.blockSide) (f := fun h => g (refineSite y + siteOfCoords j h))
  rw [card_centredCube_blockSide hodd] at h
  unfold cellAverage
  rw [smul_eq_mul, mul_pow]
  calc (1 / (F.blockSide : ℝ) ^ 4) ^ 2 * (∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h)) ^ 2
      ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ 2 *
          ((F.blockSide : ℝ) ^ 4 * ∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h) ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp
theorem cellAverage_pow_four_le (hodd : Odd F.blockSide) {j : ℕ} (g : F.Site j → ℝ) (y : F.Site (j + 1)) :
    cellAverage g y ^ 4 ≤
      (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h) ^ 4 := by
  have hL0 : (0 : ℝ) < (F.blockSide : ℝ) ^ 4 := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  have h1 := cellAverage_sq_le hodd g y
  have h2 := sq_sum_le_card_mul_sum_sq (s := centredCube F.blockSide)
    (f := fun h => g (refineSite y + siteOfCoords j h) ^ 2)
  rw [card_centredCube_blockSide hodd] at h2
  have e : ∀ h, (g (refineSite y + siteOfCoords j h) ^ 2) ^ 2 = g (refineSite y + siteOfCoords j h) ^ 4 :=
    fun h => by ring
  simp only [e] at h2
  calc cellAverage g y ^ 4 = (cellAverage g y ^ 2) ^ 2 := by ring
    _ ≤ ((1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (1 / (F.blockSide : ℝ) ^ 4) ^ 2 *
          (∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h) ^ 2) ^ 2 := by ring
    _ ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ 2 *
          ((F.blockSide : ℝ) ^ 4 * ∑ h ∈ centredCube F.blockSide, g (refineSite y + siteOfCoords j h) ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp
theorem norm_cellAverage_le {j : ℕ} (hL : 0 < F.blockSide) (g : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) :
    ‖cellAverage g y‖ ≤ cellAverage (fun x => ‖g x‖) y := by
  unfold cellAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
theorem cellAverage_mono {j : ℕ} {g g' : F.Site j → ℝ} (h : ∀ x, g x ≤ g' x) (y : F.Site (j + 1)) :
    cellAverage g y ≤ cellAverage g' y := by
  unfold cellAverage
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => h _) (by positivity)
theorem cellAverage_add {j : ℕ} (g g' : F.Site j → ℝ) (y : F.Site (j + 1)) :
    cellAverage (fun x => g x + g' x) y = cellAverage g y + cellAverage g' y := by
  unfold cellAverage
  simp only [smul_eq_mul, Finset.sum_add_distrib, mul_add]
theorem cellAverage_sub {j : ℕ} (g g' : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) :
    cellAverage (fun x => g x - g' x) y = cellAverage g y - cellAverage g' y := by
  unfold cellAverage
  rw [Finset.sum_sub_distrib, smul_sub]
theorem norm_nestedAverage_le (hL : 0 < F.blockSide) (g : F.Site 0 → ℍ[ℝ]) (j : ℕ) (x : F.Site j) :
    ‖nestedAverage g j x‖ ≤ nestedAverage (fun t => ‖g t‖) j x := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    show ‖cellAverage (nestedAverage g j) x‖ ≤ cellAverage (nestedAverage (fun t => ‖g t‖) j) x
    exact (norm_cellAverage_le hL _ x).trans (cellAverage_mono ih x)
theorem nestedAverage_nonneg {g : F.Site 0 → ℝ} (hg : ∀ t, 0 ≤ g t) (j : ℕ) (x : F.Site j) :
    0 ≤ nestedAverage g j x := by
  induction j with
  | zero => exact hg x
  | succ j ih => exact cellAverage_nonneg ih x
set_option maxHeartbeats 2000000 in
theorem compositeMeanBound : compositeMeanBoundStatement := by
  classical
  intro F y₀ f β e hodd h5 he0 he hβ0 hβ hrec
  set S : Finset F.Cell := {y₀} with hS
  set g0 := f 0 with hg0
  set p := nestedAverage (fun t => ‖g0 t‖) with hp
  set m := nestedAverage g0 with hm
  set Lr : ℝ := (F.blockSide : ℝ) with hLr
  have hL5 : (5 : ℝ) ≤ Lr := by
    rw [hLr]
    exact_mod_cast h5
  have hLp : 0 < F.blockSide := hodd.pos
  let E : (j : ℕ) → F.Site j → ℝ := fun j x => ‖f j x - m j x‖
  have hE0 : ∀ j x, 0 ≤ E j x := fun j x => norm_nonneg _
  have hp0 : ∀ j x, 0 ≤ p j x := fun j x => nestedAverage_nonneg (fun t => norm_nonneg _) j x
  let Q : ℕ → ℝ := fun j => ∑ x ∈ sitesOfCells S j, p j x ^ 4
  let u : ℕ → ℝ := fun j => ∑ x ∈ sitesOfCells S j, E j x ^ 2
  have hQ0 : ∀ j, 0 ≤ Q j := fun j => Finset.sum_nonneg fun _ _ => by positivity
  have hQstep : ∀ j, j + 1 ≤ F.top → Q (j + 1) ≤ Q j / Lr ^ 4 := by
    intro j hj
    calc Q (j + 1) = ∑ y ∈ sitesOfCells S (j + 1), cellAverage (p j) y ^ 4 := rfl
      _ ≤ ∑ y ∈ sitesOfCells S (j + 1),
            (1 / Lr ^ 4) * ∑ h ∈ centredCube F.blockSide, p j (refineSite y + siteOfCoords j h) ^ 4 :=
          Finset.sum_le_sum fun y _ => cellAverage_pow_four_le hodd (p j) y
      _ = (1 / Lr ^ 4) * ∑ y ∈ sitesOfCells S (j + 1),
            ∑ h ∈ centredCube F.blockSide, p j (refineSite y + siteOfCoords j h) ^ 4 := by
          rw [Finset.mul_sum]
      _ ≤ (1 / Lr ^ 4) * Q j := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_sum_refineSite_le hodd hj (G := fun x => p j x ^ 4) fun x => by positivity
      _ = Q j / Lr ^ 4 := by ring
  have hQall : ∀ j, j ≤ F.top → Q j * (Lr ^ j) ^ 4 ≤ Q 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hQstep j hj
      have h3 : Q (j + 1) * Lr ^ 4 ≤ Q j := by rwa [le_div_iff₀ (by positivity)] at h2
      calc Q (j + 1) * (Lr ^ (j + 1)) ^ 4 = (Q (j + 1) * Lr ^ 4) * (Lr ^ j) ^ 4 := by ring
        _ ≤ Q j * (Lr ^ j) ^ 4 := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ ≤ Q 0 := h1
  have hstep : ∀ j, j < F.top →
      u (j + 1) ≤ 81 / 32 * (u j / Lr ^ 4) + 2 * (e ^ 2 * Real.sqrt (Q (j + 1))) := by
    intro j hj
    have hj1 : j + 1 ≤ F.top := hj
    have hpt : ∀ y ∈ sitesOfCells S (j + 1), E (j + 1) y ^ 2 ≤
        81 / 32 * cellAverage (E j) y ^ 2 + 2 * (β j y ^ 2 * p (j + 1) y ^ 2) := by
      intro y hy
      have hβe : β j y ≤ e := by
        have h1 : β j y ^ 4 ≤ e ^ 4 := le_trans (Finset.single_le_sum (f := fun y => β j y ^ 4)
          (fun _ _ => by positivity) hy) (hβ j hj)
        exact (pow_le_pow_iff_left₀ (hβ0 j y) he0 (by norm_num)).1 h1
      have hr := hrec j hj y hy
      have hmean : (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, f j (refineSite y + siteOfCoords j h) =
          cellAverage (f j) y := rfl
      have hmean2 : (1 / (F.blockSide : ℝ) ^ 4) *
          ∑ h ∈ centredCube F.blockSide, ‖f j (refineSite y + siteOfCoords j h)‖ =
          cellAverage (fun x => ‖f j x‖) y := rfl
      rw [hmean, hmean2] at hr
      have hbe : 0 ≤ cellAverage (E j) y := cellAverage_nonneg (hE0 j) y
      have h1 : cellAverage (fun x => ‖f j x‖) y ≤ p (j + 1) y + cellAverage (E j) y := by
        have : ∀ x, ‖f j x‖ ≤ p j x + E j x := fun x => by
          have a := norm_add_le (m j x) (f j x - m j x)
          rw [add_sub_cancel] at a
          have b := norm_nestedAverage_le hLp g0 j x
          show ‖f j x‖ ≤ p j x + ‖f j x - m j x‖
          linarith
        refine le_trans (cellAverage_mono this y) (le_of_eq ?_)
        rw [cellAverage_add]
        rfl
      have h2 : E (j + 1) y ≤ β j y * (p (j + 1) y + cellAverage (E j) y) + cellAverage (E j) y := by
        have e1 : f (j + 1) y - m (j + 1) y = (f (j + 1) y - cellAverage (f j) y) +
            cellAverage (fun x => f j x - m j x) y := by
          rw [cellAverage_sub]
          have : m (j + 1) y = cellAverage (m j) y := rfl
          rw [this]
          abel
        show ‖f (j + 1) y - m (j + 1) y‖ ≤ _
        rw [e1]
        refine le_trans (norm_add_le _ _) (add_le_add (le_trans hr ?_) (norm_cellAverage_le hLp _ y))
        exact mul_le_mul_of_nonneg_left h1 (hβ0 j y)
      have h3 : E (j + 1) y ≤ 9 / 8 * cellAverage (E j) y + β j y * p (j + 1) y := by
        have : β j y * cellAverage (E j) y ≤ 1 / 8 * cellAverage (E j) y :=
          mul_le_mul_of_nonneg_right (le_trans hβe he) hbe
        nlinarith
      have h4 : E (j + 1) y ^ 2 ≤ (9 / 8 * cellAverage (E j) y + β j y * p (j + 1) y) ^ 2 :=
        pow_le_pow_left₀ (hE0 _ y) h3 2
      nlinarith [sq_nonneg (9 / 8 * cellAverage (E j) y - β j y * p (j + 1) y)]
    have hb1 : ∑ y ∈ sitesOfCells S (j + 1), cellAverage (E j) y ^ 2 ≤ u j / Lr ^ 4 := by
      calc ∑ y ∈ sitesOfCells S (j + 1), cellAverage (E j) y ^ 2
          ≤ ∑ y ∈ sitesOfCells S (j + 1),
              (1 / Lr ^ 4) * ∑ h ∈ centredCube F.blockSide, E j (refineSite y + siteOfCoords j h) ^ 2 :=
            Finset.sum_le_sum fun y _ => cellAverage_sq_le hodd (E j) y
        _ = (1 / Lr ^ 4) * ∑ y ∈ sitesOfCells S (j + 1),
              ∑ h ∈ centredCube F.blockSide, E j (refineSite y + siteOfCoords j h) ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ (1 / Lr ^ 4) * u j := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_sum_refineSite_le hodd hj1 (G := fun x => E j x ^ 2) fun x => by positivity
        _ = _ := by ring
    have hb2 : ∑ y ∈ sitesOfCells S (j + 1), β j y ^ 2 * p (j + 1) y ^ 2 ≤ e ^ 2 * Real.sqrt (Q (j + 1)) := by
      have hc := Finset.sum_mul_sq_le_sq_mul_sq (sitesOfCells S (j + 1)) (fun y => β j y ^ 2)
        (fun y => p (j + 1) y ^ 2)
      have e1 : ∀ y, (β j y ^ 2) ^ 2 = β j y ^ 4 := fun y => by ring
      have e2 : ∀ y, (p (j + 1) y ^ 2) ^ 2 = p (j + 1) y ^ 4 := fun y => by ring
      simp only [e1, e2] at hc
      have hx : 0 ≤ ∑ y ∈ sitesOfCells S (j + 1), β j y ^ 2 * p (j + 1) y ^ 2 :=
        Finset.sum_nonneg fun _ _ => by positivity
      have hy : 0 ≤ e ^ 2 * Real.sqrt (Q (j + 1)) := by positivity
      refine (sq_le_sq₀ hx hy).1 ?_
      rw [mul_pow, Real.sq_sqrt (hQ0 _)]
      refine le_trans hc ?_
      calc (∑ y ∈ sitesOfCells S (j + 1), β j y ^ 4) * (∑ y ∈ sitesOfCells S (j + 1), p (j + 1) y ^ 4)
          ≤ e ^ 4 * Q (j + 1) := mul_le_mul_of_nonneg_right (hβ j hj) (hQ0 _)
        _ = _ := by ring
    calc u (j + 1) ≤ ∑ y ∈ sitesOfCells S (j + 1), (81 / 32 * cellAverage (E j) y ^ 2 +
          2 * (β j y ^ 2 * p (j + 1) y ^ 2)) := Finset.sum_le_sum hpt
      _ = 81 / 32 * ∑ y ∈ sitesOfCells S (j + 1), cellAverage (E j) y ^ 2 +
          2 * ∑ y ∈ sitesOfCells S (j + 1), β j y ^ 2 * p (j + 1) y ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by linarith
  set A := Real.sqrt (Q 0) with hA
  have hAsq : A ^ 2 = Q 0 := Real.sq_sqrt (hQ0 0)
  have hall : ∀ j, j ≤ F.top → u j ≤ 3 * (e ^ 2 * A) / (Lr ^ j) ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      have : u 0 = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        show ‖f 0 x - m 0 x‖ ^ 2 = 0
        have : m 0 x = f 0 x := rfl
        rw [this, sub_self, norm_zero]
        norm_num
      rw [this]
      positivity
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j hj
      set T := Lr ^ j with hT
      have hT0 : 0 < T := by positivity
      have e1 : Lr ^ (j + 1) = T * Lr := by rw [hT, pow_succ]
      have hq : Real.sqrt (Q (j + 1)) ≤ A / (Lr ^ (j + 1)) ^ 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        have h3 := hQall (j + 1) hj
        rw [div_pow, hAsq, le_div_iff₀ (by positivity)]
        calc Q (j + 1) * ((Lr ^ (j + 1)) ^ 2) ^ 2 = Q (j + 1) * (Lr ^ (j + 1)) ^ 4 := by ring
          _ ≤ Q 0 := h3
      rw [e1] at hq ⊢
      set B := e ^ 2 * A / (T * Lr) ^ 2 with hB
      have hB0 : 0 ≤ B := by positivity
      have h4 : e ^ 2 * Real.sqrt (Q (j + 1)) ≤ B := by
        calc e ^ 2 * Real.sqrt (Q (j + 1)) ≤ e ^ 2 * (A / (T * Lr) ^ 2) :=
              mul_le_mul_of_nonneg_left hq (by positivity)
          _ = B := by rw [hB]; ring
      have h5' : u j / Lr ^ 4 ≤ 3 * B / Lr ^ 2 := by
        rw [hB]
        calc u j / Lr ^ 4 ≤ (3 * (e ^ 2 * A) / T ^ 2) / Lr ^ 4 := by gcongr
          _ = _ := by field_simp
      have h6 : 3 * B / Lr ^ 2 ≤ 3 * B / 25 := by
        have : (25 : ℝ) ≤ Lr ^ 2 := by nlinarith
        gcongr
      have e2 : 3 * (e ^ 2 * A) / (T * Lr) ^ 2 = 3 * B := by rw [hB]; ring
      rw [e2]
      linarith
  have hyn : y₀ ∈ sitesOfCells S F.top := mem_sitesOfCells_top.2 (Finset.mem_singleton_self y₀)
  have h1 : E F.top y₀ ^ 2 ≤ u F.top := Finset.single_le_sum (f := fun x => E F.top x ^ 2)
    (fun _ _ => by positivity) hyn
  have h2 := hall F.top le_rfl
  have hflat : m F.top y₀ = (1 / ((F.blockSide : ℝ) ^ F.top) ^ 4) •
      ∑ h ∈ centredCube (F.blockSide ^ F.top), f 0 (cellCentre 0 y₀ + siteOfCoords 0 h) := by
    rw [hm, nestedAverage_eq_flat hodd g0 F.top le_rfl y₀]
    have e : baseSite y₀ = cellCentre (F := F) 0 y₀ := by
      have h := baseSite_cellCentre (F := F) F.top le_rfl y₀
      rwa [cellCentre_top] at h
    rw [e]
  rw [← hflat]
  show E F.top y₀ ^ 4 ≤ _
  have e3 : ∑ x ∈ sitesOfCells S 0, ‖f 0 x‖ ^ 4 = Q 0 := rfl
  rw [e3, ← hAsq]
  have h3 : E F.top y₀ ^ 2 ≤ 3 * (e ^ 2 * A) / (Lr ^ F.top) ^ 2 := le_trans h1 h2
  calc E F.top y₀ ^ 4 = (E F.top y₀ ^ 2) ^ 2 := by ring
    _ ≤ (3 * (e ^ 2 * A) / (Lr ^ F.top) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    _ = _ := by field_simp; ring
end YangMills.Construction.CompositeMean
end
