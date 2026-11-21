import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAtSomeSlots
import YangMills.Construction.ColdStepAtMirrorFrames.MoveOfAChartFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.MoveOfTheStepField
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace FieldAboveFrameMove
variable {F : BlockFrame}
theorem norm_stepCoordinates_le (η : StepVariable (finiteCells F)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ b, ‖η b‖ ≤ ρ) (x : F.Site F.depth) (i : Fin 4) : ‖stepCoordinates η x i‖ ≤ ρ := by apply _root_.YangMills.Construction.SecondOrderMoves.norm_stepCoordinates_le <;> assumption
theorem slotDecayWeight_le_one {k : ℕ} (r : ℝ) (hr : 0 ≤ r) (b : F.Site F.depth × Fin 4)
    (c : Fin k → F.Site F.top × Fin 4) (i : Fin k) : slotDecayWeight r b c i ≤ 1 := by
  unfold slotDecayWeight
  rw [Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1) (c i).1 := by positivity
  nlinarith
theorem slotDecayWeight_pos {k : ℕ} (r : ℝ) (b : F.Site F.depth × Fin 4)
    (c : Fin k → F.Site F.top × Fin 4) (i : Fin k) : 0 < slotDecayWeight r b c i := Real.exp_pos _
theorem exp_bondListDistance_le {k : ℕ} (r : ℝ) (hr : 0 ≤ r) (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (i : Fin k) :
    Real.exp (-(r * bondListDistance Y c)) ≤ Real.exp (-(r * cellSupDist Y (c i).1)) := by
  apply Real.exp_le_exp.2
  have h : cellSupDist Y (c i).1 ≤ bondListDistance Y c :=
    Finset.le_sup (f := fun l : Fin k => cellSupDist Y (c l).1) (Finset.mem_univ i)
  have h' : (cellSupDist Y (c i).1 : ℝ) ≤ bondListDistance Y c := by exact_mod_cast h
  nlinarith
theorem cellSupDist_self (Y : F.Cell) : cellSupDist Y Y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem iteratedFDeriv_add_const_eq {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : P → E) (e : E) (n : ℕ) (hn : n ≠ 0)
    (hg : ContDiffAt ℝ n g 0) :
    iteratedFDeriv ℝ n (fun τ => g τ + e) 0 = iteratedFDeriv ℝ n g 0 := by
  have : (fun τ => g τ + e) = g + fun _ => e := rfl
  rw [this, iteratedFDeriv_add_apply hg contDiffAt_const]
  rw [iteratedFDeriv_const_of_ne hn]
  simp
theorem movedField_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) : movedField c X V 0 = V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldMoveLemmas.movedField_zero' <;> assumption
theorem norm_crossingMoveMap_basis_le {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (b : F.Site F.depth × Fin 4) (i : Fin k)
    (r : ℝ) (hr : 0 ≤ r) :
    ‖crossingMoveMap c X b (slotBasisVector i)‖ ≤ slotDecayWeight r b c i := by
  classical
  unfold crossingMoveMap
  by_cases h : IsCrossingBond b
  · rw [if_pos h, ContinuousLinearMap.sum_apply, Finset.sum_eq_single i]
    · by_cases e : c i = (enclosingCell b.1, b.2)
      · rw [if_pos e]
        have hd : slotDecayWeight r b c i = 1 := by
          unfold slotDecayWeight
          rw [e]
          simp [cellSupDist_self]
        rw [hd]
        simp [hX i]
      · rw [if_neg e]
        simpa using (slotDecayWeight_pos r b c i).le
    · intro l _ hl
      split_ifs
      · simp [Pi.single_eq_of_ne hl]
      · simp
    · simp
  · rw [if_neg h]
    simpa using (slotDecayWeight_pos r b c i).le
theorem injective_vecOne {k : ℕ} (i : Fin k) : Function.Injective ![i] := by
  intro a b _
  exact Subsingleton.elim _ _
theorem injective_vecTwo {k : ℕ} (i j : Fin k) (h : i ≠ j) : Function.Injective ![i, j] := by
  intro a b e
  fin_cases a <;> fin_cases b <;> simp_all
theorem injective_vecThree {k : ℕ} (i j l : Fin k) (h₁ : i ≠ j) (h₂ : i ≠ l) (h₃ : j ≠ l) :
    Function.Injective ![i, j, l] := by
  intro a b e
  fin_cases a <;> fin_cases b <;> simp_all
theorem mul_le_sq_mul_of_le {a b u α : ℝ} (ha : a ≤ (α + 1) * u) (hb : b ≤ α + 1) (na : 0 ≤ a)
    (nb : 0 ≤ b) (hu : 0 ≤ u) (hα : 0 ≤ α) : a * b ≤ (α + 1) ^ 2 * u := by
  have := mul_le_mul ha hb nb (by positivity)
  calc _ ≤ _ := this
    _ = _ := by ring
theorem areUnitVectors_comp {k m : ℕ} (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (ι : Fin m → Fin k) : AreUnitVectors (X ∘ ι) :=
  fun l => hX (ι l)
end FieldAboveFrameMove
open FieldAboveFrameMove
theorem fieldAboveFrameMoveStatement_holds (hmove : ChartedFieldUnderMove)
    (hslots : IteratedDerivSubsetSlots) : fieldAboveFrameMoveStatement := by
  classical
  obtain ⟨C₀, hC₀, hmv⟩ := hmove
  refine ⟨C₀, hC₀, ?_⟩
  intro F star a ρA δ₂ Cw σ ρ m V η k c X B hB hCh hX hCw hδ hρ hFS hsz hη
  set w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun V' => coordsAboveFrame star a ρA m V' η with hwdef
  have hfr : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b →
      ContDiffAt ℝ 3 (fun τ => stepFrame star a ρA m b (leftTranslate (bondSpread c X τ) V)) 0 :=
    fun b hb => (hFS.analytic b (hCh b hb) k c X).contDiffAt
  have hw : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b →
      ContDiffAt ℝ 3 (fun τ => w (movedField c X V τ) b.1 b.2) 0 := fun b hb =>
    (hfr b hb).add contDiffAt_const
  have hs : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → ‖w V b.1 b.2‖ ≤ 1 := fun b hb => by
    have h1 := hFS.norm_le b (hCh b hb)
    have h2 := norm_stepCoordinates_le η ρ hρ hη b.1 b.2
    have h3 := norm_add_le (stepFrame star a ρA m (b.1, b.2) V) (stepCoordinates η b.1 b.2)
    simp only [hwdef, coordsAboveFrame]
    linarith
  obtain ⟨A, hA1, hA0, hAe, hAb⟩ := hmv F k c X w V B hB hw hs
  have hr : 0 ≤ δ₂ / 4 := by positivity
  have d1 : ∀ (i : Fin k) (b : F.Site F.depth × Fin 4), ¬ IsAxialTreeBond b →
      iteratedFDeriv ℝ 1 (fun τ => w (movedField c X V τ) b.1 b.2) 0 ![slotBasisVector i] =
        bondDeriv (stepFrame star a ρA m b) V ![c i] ![X i] := fun i b hb => by
    have h := iteratedFDeriv_add_const_eq
      (fun τ => stepFrame star a ρA m b (leftTranslate (bondSpread c X τ) V))
      (stepCoordinates η b.1 b.2) 1 (by norm_num) ((hfr b hb).of_le (by norm_num))
    have h' := hslots imaginaryQuaternions F F.top k 1 (stepFrame star a ρA m b) V c X ![i]
      (injective_vecOne i) ((hfr b hb).of_le (by norm_num))
    have e1 : (fun l => Pi.single (![i] l) (1 : ℝ)) = ![slotBasisVector i] := by
      funext l; fin_cases l; rfl
    have e2 : c ∘ ![i] = ![c i] := by funext l; fin_cases l; rfl
    have e3 : X ∘ ![i] = ![X i] := by funext l; fin_cases l; rfl
    rw [e1, e2, e3] at h'
    rw [← h', ← h]
    rfl
  have d2 : ∀ (i j x : Fin k) (b : F.Site F.depth × Fin 4), ¬ IsAxialTreeBond b → i ≠ j →
      (x = i ∨ x = j) →
      ‖iteratedFDeriv ℝ 2 (fun τ => w (movedField c X V τ) b.1 b.2) 0
          ![slotBasisVector i, slotBasisVector j]‖ ≤
        Cw * slotDecayWeight (δ₂ / 4) b c x := fun i j x b hb hij hx => by
    have h := iteratedFDeriv_add_const_eq
      (fun τ => stepFrame star a ρA m b (leftTranslate (bondSpread c X τ) V))
      (stepCoordinates η b.1 b.2) 2 (by norm_num) ((hfr b hb).of_le (by norm_num))
    have h' := hslots imaginaryQuaternions F F.top k 2 (stepFrame star a ρA m b) V c X ![i, j]
      (injective_vecTwo i j hij) ((hfr b hb).of_le (by norm_num))
    have e1 : (fun l => Pi.single (![i, j] l) (1 : ℝ)) = ![slotBasisVector i, slotBasisVector j] := by
      funext l; fin_cases l <;> rfl
    rw [e1] at h'
    have hb' := hFS.decay b (hCh b hb) 2 (c ∘ ![i, j]) (X ∘ ![i, j]) (by norm_num) (by norm_num)
      (areUnitVectors_comp X hX _)
    have h'' : iteratedFDeriv ℝ 2 (fun τ => w (movedField c X V τ) b.1 b.2) 0
        ![slotBasisVector i, slotBasisVector j] =
        bondDeriv (stepFrame star a ρA m b) V (c ∘ ![i, j]) (X ∘ ![i, j]) := by
      rw [← h', ← h]
      rfl
    rw [h'']
    refine hb'.trans (mul_le_mul_of_nonneg_left ?_ hCw)
    rcases hx with rfl | rfl
    · exact exp_bondListDistance_le (δ₂ / 4) hr _ (c ∘ ![_, j]) 0
    · exact exp_bondListDistance_le (δ₂ / 4) hr _ (c ∘ ![i, _]) 1
  have d3 : ∀ (i j l x : Fin k) (b : F.Site F.depth × Fin 4), ¬ IsAxialTreeBond b → i ≠ j → i ≠ l →
      j ≠ l → (x = i ∨ x = j ∨ x = l) →
      ‖iteratedFDeriv ℝ 3 (fun τ => w (movedField c X V τ) b.1 b.2) 0
          ![slotBasisVector i, slotBasisVector j, slotBasisVector l]‖ ≤
        Cw * slotDecayWeight (δ₂ / 4) b c x := fun i j l x b hb hij hil hjl hx => by
    have h := iteratedFDeriv_add_const_eq
      (fun τ => stepFrame star a ρA m b (leftTranslate (bondSpread c X τ) V))
      (stepCoordinates η b.1 b.2) 3 (by norm_num) (hfr b hb)
    have h' := hslots imaginaryQuaternions F F.top k 3 (stepFrame star a ρA m b) V c X ![i, j, l]
      (injective_vecThree i j l hij hil hjl) (hfr b hb)
    have e1 : (fun l' => Pi.single (![i, j, l] l') (1 : ℝ)) =
        ![slotBasisVector i, slotBasisVector j, slotBasisVector l] := by
      funext l'; fin_cases l' <;> rfl
    rw [e1] at h'
    have hb' := hFS.decay b (hCh b hb) 3 (c ∘ ![i, j, l]) (X ∘ ![i, j, l]) (by norm_num)
      (by norm_num) (areUnitVectors_comp X hX _)
    have h'' : iteratedFDeriv ℝ 3 (fun τ => w (movedField c X V τ) b.1 b.2) 0
        ![slotBasisVector i, slotBasisVector j, slotBasisVector l] =
        bondDeriv (stepFrame star a ρA m b) V (c ∘ ![i, j, l]) (X ∘ ![i, j, l]) := by
      rw [← h', ← h]
      rfl
    rw [h'']
    refine hb'.trans (mul_le_mul_of_nonneg_left ?_ hCw)
    rcases hx with rfl | rfl | rfl
    · exact exp_bondListDistance_le (δ₂ / 4) hr _ (c ∘ ![_, j, l]) 0
    · exact exp_bondListDistance_le (δ₂ / 4) hr _ (c ∘ ![i, _, l]) 1
    · exact exp_bondListDistance_le (δ₂ / 4) hr _ (c ∘ ![i, j, _]) 2
  have ps : ∀ (i : Fin k) (b : F.Site F.depth × Fin 4), ¬ IsAxialTreeBond b →
      firstOrderSize (fun τ => w (movedField c X V τ) b.1 b.2) (crossingMoveMap c X b)
          (slotBasisVector i) ≤
        (Cw + 1) * slotDecayWeight (δ₂ / 4) b c i := fun i b hb => by
    unfold firstOrderSize
    rw [d1 i b hb]
    have hq := norm_crossingMoveMap_basis_le c X hX b i (δ₂ / 4) hr
    have hd := hFS.decay b (hCh b hb) 1 ![c i] ![X i] le_rfl (by norm_num)
      (fun l => by fin_cases l; exact hX i)
    have he := exp_bondListDistance_le (δ₂ / 4) hr (enclosingCell b.1) ![c i] 0
    have : ‖bondDeriv (stepFrame star a ρA m b) V ![c i] ![X i]‖ ≤
        Cw * slotDecayWeight (δ₂ / 4) b c i :=
      hd.trans (mul_le_mul_of_nonneg_left he hCw)
    linarith
  set K : ℝ := C₀ * (Cw + 2) ^ 3 with hK
  have f1 : Cw + 1 ≤ (Cw + 2) ^ 3 := by nlinarith [sq_nonneg Cw, mul_nonneg hCw (sq_nonneg Cw)]
  have f2 : (Cw + 1) ^ 2 + Cw ≤ (Cw + 2) ^ 3 := by
    nlinarith [sq_nonneg Cw, mul_nonneg hCw (sq_nonneg Cw)]
  have f3 : (Cw + 1) ^ 3 + 3 * Cw * (Cw + 1) + Cw ≤ (Cw + 2) ^ 3 := by
    nlinarith [sq_nonneg Cw, mul_nonneg hCw (sq_nonneg Cw)]
  have hu1 : ∀ (b : F.Site F.depth × Fin 4) (i : Fin k), slotDecayWeight (δ₂ / 4) b c i ≤ 1 :=
    fun b i => slotDecayWeight_le_one _ hr b c i
  have hu0 : ∀ (b : F.Site F.depth × Fin 4) (i : Fin k), 0 ≤ slotDecayWeight (δ₂ / 4) b c i :=
    fun b i => (slotDecayWeight_pos _ b c i).le
  have hK0 : 0 ≤ K := by positivity
  have ps0 : ∀ (u : Fin k → ℝ) (b : F.Site F.depth × Fin 4),
      0 ≤ firstOrderSize (fun τ => w (movedField c X V τ) b.1 b.2) (crossingMoveMap c X b) u :=
    fun u b => by
      unfold firstOrderSize; positivity
  have ps1 : ∀ (i : Fin k) (b : F.Site F.depth × Fin 4), ¬ IsAxialTreeBond b →
      firstOrderSize (fun τ => w (movedField c X V τ) b.1 b.2) (crossingMoveMap c X b)
        (slotBasisVector i) ≤ Cw + 1 :=
    fun i b hb => (ps i b hb).trans (by nlinarith [hu1 b i])
  have d2' : ∀ (i j : Fin k) (b : F.Site F.depth × Fin 4), ¬ IsAxialTreeBond b → i ≠ j →
      ‖iteratedFDeriv ℝ 2 (fun τ => w (movedField c X V τ) b.1 b.2) 0
          ![slotBasisVector i, slotBasisVector j]‖ ≤ Cw :=
    fun i j b hb hij => (d2 i j i b hb hij (Or.inl rfl)).trans (by nlinarith [hu1 b i])
  refine ⟨A, ⟨hA1, hA0, hAe, fun b τ h => (hAb b).1 h τ, ⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro i b
    by_cases ht : IsAxialTreeBond b.1
    · have e : (fun τ => A τ b) = fun _ => 0 := funext fun τ => (hAb b).1 ht τ
      simp only [firstDerivNorm, e]
      rw [iteratedFDeriv_const_of_ne (by norm_num)]
      simpa using mul_nonneg hK0 (hu0 b.1 i)
    · obtain ⟨-, -, -, -, h1, -, -⟩ := (hAb b).2 ht
      refine (h1 (slotBasisVector i)).trans ?_
      calc C₀ * firstOrderSize _ _ (slotBasisVector i) ≤
            C₀ * ((Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c i) :=
            mul_le_mul_of_nonneg_left (ps i b.1 ht) hC₀
        _ ≤ K * slotDecayWeight (δ₂ / 4) b.1 c i := by
            rw [← mul_assoc, hK, mul_assoc C₀, mul_assoc C₀]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right f1 (hu0 b.1 i)) hC₀
  · intro i j x b hij hx
    by_cases ht : IsAxialTreeBond b.1
    · have e : (fun τ => A τ b) = fun _ => 0 := funext fun τ => (hAb b).1 ht τ
      simp only [secondDerivNorm, e]
      rw [iteratedFDeriv_const_of_ne (by norm_num)]
      simpa using mul_nonneg hK0 (hu0 b.1 x)
    · obtain ⟨-, -, -, -, -, h2, -⟩ := (hAb b).2 ht
      refine (h2 (slotBasisVector i) (slotBasisVector j)).trans ?_
      have hu := hu0 b.1 x
      have e3 := d2 i j x b.1 ht hij hx
      have e4 : firstOrderSize (fun τ => w (movedField c X V τ) b.1.1 b.1.2) (crossingMoveMap c X b.1)
            (slotBasisVector i) *
          firstOrderSize (fun τ => w (movedField c X V τ) b.1.1 b.1.2) (crossingMoveMap c X b.1)
            (slotBasisVector j) ≤
          (Cw + 1) ^ 2 * slotDecayWeight (δ₂ / 4) b.1 c x := by
        rcases hx with rfl | rfl
        · exact mul_le_sq_mul_of_le (ps _ b.1 ht) (ps1 j b.1 ht) (ps0 _ _) (ps0 _ _) hu hCw
        · rw [mul_comm]
          exact mul_le_sq_mul_of_le (ps _ b.1 ht) (ps1 i b.1 ht) (ps0 _ _) (ps0 _ _) hu hCw
      calc _ ≤ C₀ * ((Cw + 1) ^ 2 * slotDecayWeight (δ₂ / 4) b.1 c x +
              Cw * slotDecayWeight (δ₂ / 4) b.1 c x) :=
            mul_le_mul_of_nonneg_left (add_le_add e4 e3) hC₀
        _ = C₀ * (((Cw + 1) ^ 2 + Cw) * slotDecayWeight (δ₂ / 4) b.1 c x) := by ring
        _ ≤ K * slotDecayWeight (δ₂ / 4) b.1 c x := by
            rw [hK, mul_assoc C₀]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right f2 hu) hC₀
  · intro i j l x b hij hil hjl hx
    by_cases ht : IsAxialTreeBond b.1
    · have e : (fun τ => A τ b) = fun _ => 0 := funext fun τ => (hAb b).1 ht τ
      simp only [thirdDerivNorm, e]
      rw [iteratedFDeriv_const_of_ne (by norm_num)]
      simpa using mul_nonneg hK0 (hu0 b.1 x)
    · obtain ⟨-, -, -, -, -, -, h3⟩ := (hAb b).2 ht
      refine (h3 (slotBasisVector i) (slotBasisVector j) (slotBasisVector l)).trans ?_
      have hu := hu0 b.1 x
      set Pi' := firstOrderSize (fun τ => w (movedField c X V τ) b.1.1 b.1.2)
        (crossingMoveMap c X b.1) (slotBasisVector i)
      set Pj := firstOrderSize (fun τ => w (movedField c X V τ) b.1.1 b.1.2)
        (crossingMoveMap c X b.1) (slotBasisVector j)
      set Pl := firstOrderSize (fun τ => w (movedField c X V τ) b.1.1 b.1.2)
        (crossingMoveMap c X b.1) (slotBasisVector l)
      have ni : 0 ≤ Pi' := ps0 _ _
      have nj : 0 ≤ Pj := ps0 _ _
      have nl : 0 ≤ Pl := ps0 _ _
      have bi : Pi' ≤ Cw + 1 := ps1 i b.1 ht
      have bj : Pj ≤ Cw + 1 := ps1 j b.1 ht
      have bl : Pl ≤ Cw + 1 := ps1 l b.1 ht
      have ui : Pi' ≤ (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c i := ps i b.1 ht
      have uj : Pj ≤ (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c j := ps j b.1 ht
      have ul : Pl ≤ (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c l := ps l b.1 ht
      have q4 := d3 i j l x b.1 ht hij hil hjl hx
      have t1 : Pi' * Pj * Pl ≤ (Cw + 1) ^ 3 * slotDecayWeight (δ₂ / 4) b.1 c x := by
        rcases hx with rfl | rfl | rfl
        · have := mul_le_sq_mul_of_le ui bj ni nj hu hCw
          have h := mul_le_mul this bl nl (by positivity)
          calc _ ≤ _ := h
            _ = _ := by ring
        · have := mul_le_sq_mul_of_le uj bi nj ni hu hCw
          have h := mul_le_mul this bl nl (by positivity)
          calc Pi' * Pj * Pl = Pj * Pi' * Pl := by ring
            _ ≤ _ := h
            _ = _ := by ring
        · have := mul_le_sq_mul_of_le ul bi nl ni hu hCw
          have h := mul_le_mul this bj nj (by positivity)
          calc Pi' * Pj * Pl = Pl * Pi' * Pj := by ring
            _ ≤ _ := h
            _ = _ := by ring
      have t2 : ‖iteratedFDeriv ℝ 2 (fun τ => w (movedField c X V τ) b.1.1 b.1.2) 0
            ![slotBasisVector i, slotBasisVector j]‖ * Pl ≤
          Cw * (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c x := by
        by_cases hxl : x = l
        · subst hxl
          have h := mul_le_mul (d2' i j b.1 ht hij) ul nl hCw
          calc _ ≤ _ := h
            _ = _ := by ring
        · have hx' : x = i ∨ x = j := by
            rcases hx with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hxl
          have h := mul_le_mul (d2 i j x b.1 ht hij hx') bl nl (by positivity)
          calc _ ≤ _ := h
            _ = _ := by ring
      have t3 : ‖iteratedFDeriv ℝ 2 (fun τ => w (movedField c X V τ) b.1.1 b.1.2) 0
            ![slotBasisVector i, slotBasisVector l]‖ * Pj ≤
          Cw * (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c x := by
        by_cases hxj : x = j
        · subst hxj
          have h := mul_le_mul (d2' i l b.1 ht hil) uj nj hCw
          calc _ ≤ _ := h
            _ = _ := by ring
        · have hx' : x = i ∨ x = l := by
            rcases hx with h | h | h
            · exact Or.inl h
            · exact absurd h hxj
            · exact Or.inr h
          have h := mul_le_mul (d2 i l x b.1 ht hil hx') bj nj (by positivity)
          calc _ ≤ _ := h
            _ = _ := by ring
      have t4 : ‖iteratedFDeriv ℝ 2 (fun τ => w (movedField c X V τ) b.1.1 b.1.2) 0
            ![slotBasisVector j, slotBasisVector l]‖ * Pi' ≤
          Cw * (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c x := by
        by_cases hxi : x = i
        · subst hxi
          have h := mul_le_mul (d2' j l b.1 ht hjl) ui ni hCw
          calc _ ≤ _ := h
            _ = _ := by ring
        · have hx' : x = j ∨ x = l := by
            rcases hx with h | h | h
            · exact absurd h hxi
            · exact Or.inl h
            · exact Or.inr h
          have h := mul_le_mul (d2 j l x b.1 ht hjl hx') bi ni (by positivity)
          calc _ ≤ _ := h
            _ = _ := by ring
      have tot := add_le_add (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) q4
      refine (mul_le_mul_of_nonneg_left tot hC₀).trans ?_
      have : (Cw + 1) ^ 3 * slotDecayWeight (δ₂ / 4) b.1 c x +
          Cw * (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c x +
          Cw * (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c x +
          Cw * (Cw + 1) * slotDecayWeight (δ₂ / 4) b.1 c x +
          Cw * slotDecayWeight (δ₂ / 4) b.1 c x =
          ((Cw + 1) ^ 3 + 3 * Cw * (Cw + 1) + Cw) * slotDecayWeight (δ₂ / 4) b.1 c x := by ring
      rw [this, hK, mul_assoc C₀]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right f3 hu) hC₀
  · intro i b ht
    obtain ⟨-, -, -, h0, -, -, -⟩ := (hAb b).2 ht
    have h := h0 (slotBasisVector i)
    rw [d1 i b.1 ht] at h
    simp only [movedField_zero] at h
    refine h.trans ?_
    have hn := norm_nonneg (w V b.1.1 b.1.2)
    have e := ps1 i b.1 ht
    calc _ ≤ C₀ * ‖w V b.1.1 b.1.2‖ * (Cw + 1) := mul_le_mul_of_nonneg_left e (by positivity)
      _ ≤ K * ‖w V b.1.1 b.1.2‖ := by
        rw [hK]
        nlinarith [mul_le_mul_of_nonneg_left f1 (mul_nonneg hC₀ hn)]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
