import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ResponseInTheExpansion.EntriesMoveByTheirKernels
import YangMills.Construction.ResponseInTheExpansion.MixedDerivativesAlongSlots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.DirectionalDerivatives
namespace ChartResponse
variable {F : BlockFrame}
private theorem expUnit_zero_aux : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem max_cellSupDist_le_directionDiameter_aux (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions)
    (r : ChartDirection F) :
    max (cellSupDist (enclosingCell p.1) (enclosingCell q.1)) (cellSupDist (enclosingCell p.1) (directionCell r)) ≤
      directionDiameter (![Sum.inl p, Sum.inl q, r] : Fin 3 → ChartDirection F) := by
  set l : Fin 3 → ChartDirection F := ![Sum.inl p, Sum.inl q, r] with hl
  have key : ∀ i j : Fin 3, cellSupDist (directionCell (l i)) (directionCell (l j)) ≤ directionDiameter l := by
    intro i j
    have h5 := Finset.le_sup (f := fun l' : Fin 3 => cellSupDist (directionCell (l i)) (directionCell (l l')))
      (Finset.mem_univ j)
    have h6 := Finset.le_sup (f := fun k : Fin 3 => Finset.univ.sup fun l' : Fin 3 =>
      cellSupDist (directionCell (l k)) (directionCell (l l'))) (Finset.mem_univ i)
    exact h5.trans h6
  refine max_le ?_ ?_
  · simpa [hl, directionCell] using key 0 1
  · simpa [hl, directionCell] using key 0 2
theorem hessianEntryLipschitz_of_kernelBound (hK : ChartEnergyKernelBound)
    (hM : MixedDerivLipschitzAndSecondDifference) : HessianEntryLipschitz := by
  intro a L c ha hL hL0 hc
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hL hL0 hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  refine ⟨Ck 3, hCk 3, fun F w u V v Bt Bn p q hF hp hq hu hv hpts => ?_⟩
  classical
  have one : ∀ (w₁ : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V₁ : F.GaugeField F.top)
      (r : ChartDirection F) (t : ℝ), 0 ≤ t →
      ‖directionVector r‖ = 1 →
      (∀ θ, 0 ≤ θ → θ ≤ t → IsAdmissibleChartPoint L c.σA (shiftCoordinates r θ w₁) (shiftField r θ V₁)) →
      |chartMixedDeriv a (shiftCoordinates r t w₁) (shiftField r t V₁) ![Sum.inl p, Sum.inl q] -
        chartMixedDeriv a w₁ V₁ ![Sum.inl p, Sum.inl q]| ≤
        Ck 3 * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
          (cellSupDist (enclosingCell p.1) (directionCell r)) : ℕ))) * t := by
    intro w₁ V₁ r t ht hr hs
    refine hM.1 F (chartedEnergy a) w₁ V₁ p q r _ t ht fun θ h0 h1 => ?_
    obtain ⟨h2, h3⟩ := hker F _ _ hF (hs θ h0 h1) 3 ![r, Sum.inl p, Sum.inl q]
    refine ⟨h2, ?_⟩
    have hu' : ∀ l, ‖directionVector ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) l)‖ = 1 := by
      intro l
      fin_cases l
      · simpa using hr
      · simpa [directionVector] using hp
      · simpa [directionVector] using hq
    refine (h3 (by norm_num) hu').trans ?_
    have hd := max_cellSupDist_le_directionDiameter_aux p q r
    have hperm : directionDiameter (![Sum.inl p, Sum.inl q, r] : Fin 3 → ChartDirection F) ≤
        directionDiameter (![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) := by
      unfold directionDiameter
      refine Finset.sup_le fun i _ => Finset.sup_le fun j _ => ?_
      have key : ∀ i j : Fin 3,
          cellSupDist (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) i))
            (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) j)) ≤
          Finset.univ.sup fun l : Fin 3 => Finset.univ.sup fun l' : Fin 3 =>
            cellSupDist (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) l))
              (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) l')) := by
        intro i j
        have h5 := Finset.le_sup (f := fun l' : Fin 3 =>
          cellSupDist (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) i))
            (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) l'))) (Finset.mem_univ j)
        have h6 := Finset.le_sup (f := fun k : Fin 3 => Finset.univ.sup fun l' : Fin 3 =>
          cellSupDist (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) k))
            (directionCell ((![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) l'))) (Finset.mem_univ i)
        exact h5.trans h6
      fin_cases i <;> fin_cases j
      · simpa using key 1 1
      · simpa using key 1 2
      · simpa using key 1 0
      · simpa using key 2 1
      · simpa using key 2 2
      · simpa using key 2 0
      · simpa using key 0 1
      · simpa using key 0 2
      · simpa using key 0 0
    have hd' : ((max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
        (cellSupDist (enclosingCell p.1) (directionCell r)) : ℕ) : ℝ) ≤
        (directionDiameter (![r, Sum.inl p, Sum.inl q] : Fin 3 → ChartDirection F) : ℝ) := by
      exact_mod_cast hd.trans hperm
    have h4 := (hCk 3).le
    unfold chartMixedDeriv at *
    gcongr
  set P : (F.Site F.depth → Fin 4 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun θ z i => w z i + θ z i • u z i with hP
  set Q : (F.Site F.top → Fin 4 → ℝ) → F.GaugeField F.top :=
    fun ϑ => leftTranslate (fun y i => ϑ y i • v y i) V with hQ
  set K : (F.Site F.depth → Fin 4 → ℝ) → (F.Site F.top → Fin 4 → ℝ) → ℝ :=
    fun θ ϑ => chartMixedDeriv a (P θ) (Q ϑ) ![Sum.inl p, Sum.inl q] with hKd
  have hI : ∀ (A : Finset (F.Site F.depth × Fin 4)) z i, 0 ≤ (if (z, i) ∈ A then (1 : ℝ) else 0) ∧
      (if (z, i) ∈ A then (1 : ℝ) else 0) ≤ 1 := by
    intro A z i
    split_ifs <;> norm_num
  have hJ : ∀ (A : Finset (F.Site F.top × Fin 4)) z i, 0 ≤ (if (z, i) ∈ A then (1 : ℝ) else 0) ∧
      (if (z, i) ∈ A then (1 : ℝ) else 0) ≤ 1 := by
    intro A z i
    split_ifs <;> norm_num
  have stepT : ∀ (A : Finset (F.Site F.depth × Fin 4)) (ϑ : F.Site F.top → Fin 4 → ℝ) (b₀ : F.Site F.depth × Fin 4),
      b₀ ∉ A → (∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) →
      |K (fun z i => if (z, i) ∈ insert b₀ A then 1 else 0) ϑ - K (fun z i => if (z, i) ∈ A then 1 else 0) ϑ| ≤
        Ck 3 * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
          (cellSupDist (enclosingCell p.1) (enclosingCell b₀.1)) : ℕ))) * ‖u b₀.1 b₀.2‖ := by
    intro A ϑ b₀ hb₀ hϑ
    set t := ‖u b₀.1 b₀.2‖ with ht
    by_cases ht0 : t = 0
    · have h0 : u b₀.1 b₀.2 = 0 := norm_eq_zero.1 (ht ▸ ht0)
      have e1 : P (fun z i => if (z, i) ∈ insert b₀ A then 1 else 0) = P (fun z i => if (z, i) ∈ A then 1 else 0) := by
        funext z i
        by_cases hz : (z, i) = b₀
        · subst hz
          simp [hP, hb₀, h0]
        · simp [hP, Finset.mem_insert, hz]
      simp only [hKd]
      rw [e1, ht0]
      simp
    · have htp : 0 < t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0)
      set X : imaginaryQuaternions := t⁻¹ • u b₀.1 b₀.2 with hX
      have hX1 : ‖X‖ = 1 := by
        rw [hX, norm_smul, norm_inv, Real.norm_of_nonneg htp.le, ← ht]
        field_simp
      have htX : t • X = u b₀.1 b₀.2 := by
        rw [hX, smul_smul, mul_inv_cancel₀ ht0, one_smul]
      set r : ChartDirection F := Sum.inl (b₀.1, b₀.2, X) with hr
      have hturn : ∀ θ : ℝ, shiftField r θ (Q ϑ) = Q ϑ := by
        intro θ
        funext y i
        simp [shiftField, leftTranslate, hr, directionMove, expUnit_zero_aux]
      have hmove : ∀ θ : ℝ, shiftCoordinates r θ (P fun z i => if (z, i) ∈ A then 1 else 0) =
          P (fun z i => (if (z, i) ∈ A then 1 else 0) + if (z, i) = b₀ then θ / t else 0) := by
        intro θ
        funext z i
        by_cases hz : (z, i) = b₀
        · subst hz
          have e : θ • X = (θ / t) • u (z, i).1 (z, i).2 := by
            rw [hX, smul_smul, div_eq_mul_inv]
          simp only [shiftCoordinates, hP, hr, directionCoordinate, and_self, if_true, add_smul, add_assoc, e]
        · have hne : ¬ (b₀.1 = z ∧ b₀.2 = i) := fun h => hz (by rw [← h.1, ← h.2])
          simp [shiftCoordinates, hP, hr, directionCoordinate, hz, hne]
      have hsm : ∀ θ, 0 ≤ θ → θ ≤ t → IsAdmissibleChartPoint L c.σA
          (shiftCoordinates r θ (P fun z i => if (z, i) ∈ A then 1 else 0)) (shiftField r θ (Q ϑ)) := by
        intro θ h0 h1
        rw [hmove, hturn]
        refine hpts _ ϑ (fun z i => ?_) hϑ
        by_cases hz : (z, i) = b₀
        · subst hz
          simp only [hb₀, if_false, if_true, zero_add]
          exact ⟨by positivity, (div_le_one htp).2 h1⟩
        · simp only [hz, if_false, add_zero]
          exact hI A z i
      have := one _ (Q ϑ) r t htp.le (by simpa [hr, directionVector] using hX1) hsm
      have e1 : shiftCoordinates r t (P fun z i => if (z, i) ∈ A then 1 else 0) =
          P fun z i => if (z, i) ∈ insert b₀ A then 1 else 0 := by
        rw [hmove]
        funext z i
        by_cases hz : (z, i) = b₀
        · subst hz
          simp [hP, hb₀, div_self ht0]
        · simp [hP, Finset.mem_insert, hz]
      rw [hturn, e1] at this
      simpa [hr, directionCell, hKd] using this
  have stepN : ∀ (θf : F.Site F.depth → Fin 4 → ℝ) (A : Finset (F.Site F.top × Fin 4)) (c₀ : F.Site F.top × Fin 4),
      c₀ ∉ A → (∀ z i, 0 ≤ θf z i ∧ θf z i ≤ 1) →
      |K θf (fun y i => if (y, i) ∈ insert c₀ A then 1 else 0) - K θf (fun y i => if (y, i) ∈ A then 1 else 0)| ≤
        Ck 3 * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
          (cellSupDist (enclosingCell p.1) c₀.1) : ℕ))) * ‖v c₀.1 c₀.2‖ := by
    intro θf A c₀ hc₀ hθ
    set t := ‖v c₀.1 c₀.2‖ with ht
    by_cases ht0 : t = 0
    · have h0 : v c₀.1 c₀.2 = 0 := norm_eq_zero.1 (ht ▸ ht0)
      have e1 : Q (fun y i => if (y, i) ∈ insert c₀ A then 1 else 0) = Q (fun y i => if (y, i) ∈ A then 1 else 0) := by
        simp only [hQ]
        congr 1
        funext z i
        by_cases hz : (z, i) = c₀
        · subst hz
          simp [hc₀, h0]
        · simp [Finset.mem_insert, hz]
      simp only [hKd]
      rw [e1, ht0]
      simp
    · have htp : 0 < t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0)
      set X : imaginaryQuaternions := t⁻¹ • v c₀.1 c₀.2 with hX
      have hX1 : ‖X‖ = 1 := by
        rw [hX, norm_smul, norm_inv, Real.norm_of_nonneg htp.le, ← ht]
        field_simp
      set r : ChartDirection F := Sum.inr (c₀.1, c₀.2, X) with hr
      have hmove : ∀ θ : ℝ, shiftCoordinates r θ (P θf) = P θf := by
        intro θ
        funext z i
        simp [shiftCoordinates, hr, directionCoordinate]
      have hturn : ∀ θ : ℝ, shiftField r θ (Q fun y i => if (y, i) ∈ A then 1 else 0) =
          Q (fun y i => (if (y, i) ∈ A then 1 else 0) + if (y, i) = c₀ then θ / t else 0) := by
        intro θ
        funext y i
        by_cases hz : (y, i) = c₀
        · subst hz
          have e : θ • X = (θ / t) • v (y, i).1 (y, i).2 := by
            rw [hX, smul_smul, div_eq_mul_inv]
          simp only [shiftField, hQ, leftTranslate, hr, directionMove, and_self, if_true, hc₀, if_false, zero_smul,
            expUnit_zero_aux, zero_add, e, one_mul]
        · have hne : ¬ (c₀.1 = y ∧ c₀.2 = i) := fun h => hz (by rw [← h.1, ← h.2])
          simp [shiftField, hQ, leftTranslate, hr, directionMove, hz, hne, expUnit_zero_aux]
      have hsm : ∀ θ, 0 ≤ θ → θ ≤ t → IsAdmissibleChartPoint L c.σA
          (shiftCoordinates r θ (P θf)) (shiftField r θ (Q fun y i => if (y, i) ∈ A then 1 else 0)) := by
        intro θ h0 h1
        rw [hmove, hturn]
        refine hpts θf _ hθ (fun y i => ?_)
        by_cases hz : (y, i) = c₀
        · subst hz
          simp only [hc₀, if_false, if_true, zero_add]
          exact ⟨by positivity, (div_le_one htp).2 h1⟩
        · simp only [hz, if_false, add_zero]
          exact hJ A y i
      have := one (P θf) _ r t htp.le (by simpa [hr, directionVector] using hX1) hsm
      have e1 : shiftField r t (Q fun y i => if (y, i) ∈ A then 1 else 0) =
          Q fun y i => if (y, i) ∈ insert c₀ A then 1 else 0 := by
        rw [hturn]
        simp only [hQ]
        congr 1
        funext y i
        by_cases hz : (y, i) = c₀
        · subst hz
          simp [hc₀, div_self ht0]
        · simp [Finset.mem_insert, hz]
      rw [hmove, e1] at this
      simpa [hr, directionCell, hKd] using this
  have sumT : ∀ (A : Finset (F.Site F.depth × Fin 4)),
      |K (fun z i => if (z, i) ∈ A then 1 else 0) (fun _ _ => 0) - K (fun _ _ => 0) (fun _ _ => 0)| ≤
      ∑ b ∈ A, Ck 3 * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
        (cellSupDist (enclosingCell p.1) (enclosingCell b.1)) : ℕ))) * ‖u b.1 b.2‖ := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | insert b₀ A hb₀ ih =>
      rw [Finset.sum_insert hb₀]
      have := stepT A (fun _ _ => 0) b₀ hb₀ (fun _ _ => ⟨le_rfl, zero_le_one⟩)
      exact (abs_sub_le _ _ _).trans (add_le_add this ih)
  have sumN : ∀ (A : Finset (F.Site F.top × Fin 4)),
      |K (fun z i => if (z, i) ∈ Bt then 1 else 0) (fun y i => if (y, i) ∈ A then 1 else 0) -
        K (fun z i => if (z, i) ∈ Bt then 1 else 0) (fun _ _ => 0)| ≤
      ∑ b ∈ A, Ck 3 * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
        (cellSupDist (enclosingCell p.1) b.1) : ℕ))) * ‖v b.1 b.2‖ := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | insert b₀ A hb₀ ih =>
      rw [Finset.sum_insert hb₀]
      have := stepN (fun z i => if (z, i) ∈ Bt then 1 else 0) A b₀ hb₀ (hI Bt)
      exact (abs_sub_le _ _ _).trans (add_le_add this ih)
  have e1 : P (fun z i => if (z, i) ∈ Bt then 1 else 0) = fun z i => w z i + u z i := by
    funext z i
    by_cases hz : (z, i) ∈ Bt
    · simp [hP, hz]
    · simp [hP, hz, hu (z, i) hz]
  have e2 : Q (fun y i => if (y, i) ∈ Bn then 1 else 0) = leftTranslate v V := by
    simp only [hQ]
    congr 1
    funext y i
    by_cases hz : (y, i) ∈ Bn
    · simp [hz]
    · simpa [hz] using (hv (y, i) hz).symm
  have e3 : P (fun _ _ => 0) = w := by
    funext z i
    simp [hP]
  have e4 : Q (fun _ _ => 0) = V := by
    funext y i
    simp [hQ, leftTranslate, expUnit_zero_aux]
  have h1 := sumT Bt
  have h2 := sumN Bn
  simp only [hKd] at h1 h2
  rw [e1, e3, e4] at h1
  rw [e1, e2, e4] at h2
  refine (abs_sub_le _ (chartMixedDeriv a (fun z i => w z i + u z i) V ![Sum.inl p, Sum.inl q]) _).trans ?_
  linarith
end ChartResponse
end YangMills.Construction
end
