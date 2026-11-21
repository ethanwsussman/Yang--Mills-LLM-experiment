import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsSummedOverPlaces
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ConvexObservables YangMills.Construction.CellCounting
namespace YangMills.Construction.Cumulants
namespace Multilinear
variable {ι : Type} [Fintype ι] {M : ℕ}
theorem ballExpectation_finsetSum {w : ℝ → ℝ} {Ψ : BondField ι → ℝ} {Q : Type} (s : Finset Q)
    (f : Q → BondField ι → ℝ)
    (hi : ∀ q ∈ s, Integrable fun η => f q η * ballDensity w Ψ η) :
    ballExpectation w Ψ (fun η => ∑ q ∈ s, f q η) = ∑ q ∈ s, ballExpectation w Ψ (f q) := by
  classical
  unfold ballExpectation
  rw [← Finset.sum_div]
  congr 1
  rw [← integral_finsetSum s hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [Finset.sum_mul]
theorem cumulantFromMoments_update_finsetSum (w : ℝ → ℝ) (Ψ : BondField ι → ℝ)
    (H : Fin M → BondField ι → ℝ)
    (i : Fin M) {Q : Type} (s : Finset Q) (f : Q → BondField ι → ℝ)
    (hint : ∀ q ∈ s, ∀ J : Finset (Fin M), Integrable fun η =>
      (∏ l ∈ J, Function.update H i (f q) l η) * ballDensity w Ψ η) :
    cumulantFromMoments w Ψ (Function.update H i fun η => ∑ q ∈ s, f q η) =
      ∑ q ∈ s, cumulantFromMoments w Ψ (Function.update H i (f q)) := by
  classical
  unfold cumulantFromMoments
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  obtain ⟨J₀, hJ₀, hi₀⟩ := π.exists_mem (Finset.mem_univ i)
  have hdis : ∀ J ∈ π.parts, J ≠ J₀ → i ∉ J := by
    intro J hJ hne hiJ
    exact hne (π.eq_of_mem_parts hJ hJ₀ hiJ hi₀)
  have hsame : ∀ (g : BondField ι → ℝ), ∀ J ∈ π.parts, J ≠ J₀ →
      ballExpectation w Ψ (fun η => ∏ l ∈ J, Function.update H i g l η) =
        ballExpectation w Ψ (fun η => ∏ l ∈ J, H l η) := by
    intro g J hJ hne
    congr 1
    funext η
    refine Finset.prod_congr rfl fun l hl => ?_
    have : l ≠ i := fun e => hdis J hJ hne (e ▸ hl)
    simp [Function.update_of_ne this]
  have hsplit : ∀ g : BondField ι → ℝ,
      ∏ J ∈ π.parts, ballExpectation w Ψ (fun η => ∏ l ∈ J, Function.update H i g l η) =
        ballExpectation w Ψ (fun η => ∏ l ∈ J₀, Function.update H i g l η) *
          ∏ J ∈ π.parts.erase J₀, ballExpectation w Ψ (fun η => ∏ l ∈ J, H l η) := by
    intro g
    rw [← Finset.mul_prod_erase π.parts _ hJ₀]
    congr 1
    refine Finset.prod_congr rfl fun J hJ => ?_
    exact hsame g J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ)
  simp only [hsplit]
  rw [← Finset.sum_mul]
  congr 1
  have hprod : ∀ η, (∏ l ∈ J₀, Function.update H i (fun η => ∑ q ∈ s, f q η) l η) =
      ∑ q ∈ s, ∏ l ∈ J₀, Function.update H i (f q) l η := by
    intro η
    simp only [← Finset.mul_prod_erase J₀ _ hi₀, Function.update_self]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    have : l ≠ i := Finset.ne_of_mem_erase hl
    simp [Function.update_of_ne this]
  simp only [hprod]
  exact ballExpectation_finsetSum s _ fun q hq => hint q hq J₀
open Classical in
def slotSumsAt {Q : Fin M → Type} [∀ i, Fintype (Q i)] (T : Finset (Fin M))
    (O : ∀ i, Q i → BondField ι → ℝ) (p : ∀ i, Q i) : Fin M → BondField ι → ℝ :=
  fun i η => if i ∈ T then ∑ q, O i q η else O i (p i) η
open Classical in
theorem slotSumsAt_update {Q : Fin M → Type} [∀ i, Fintype (Q i)] {T : Finset (Fin M)} {a : Fin M}
    (hT : a ∉ T) (O : ∀ i, Q i → BondField ι → ℝ) (p : ∀ i, Q i) (q : Q a) :
    Function.update (slotSumsAt T O p) a (O a q) = slotSumsAt T O (Function.update p a q) := by
  funext i η
  by_cases h : i = a
  · subst h
    simp [slotSumsAt, hT]
  · simp only [Function.update_of_ne h, slotSumsAt]
open Classical in
theorem slotSumsAt_insert {Q : Fin M → Type} [∀ i, Fintype (Q i)] {T : Finset (Fin M)} {a : Fin M}
    (hT : a ∉ T) (O : ∀ i, Q i → BondField ι → ℝ) (p : ∀ i, Q i) :
    slotSumsAt (insert a T) O p = Function.update (slotSumsAt T O p) a fun η => ∑ q, O a q η := by
  funext i η
  by_cases h : i = a
  · subst h
    simp [slotSumsAt]
  · simp [slotSumsAt, Function.update_of_ne h, Finset.mem_insert, h]
open Classical in
theorem integrable_slotSumsAt {Q : Fin M → Type} [∀ i, Fintype (Q i)] {w : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {O : ∀ i, Q i → BondField ι → ℝ}
    (hint : ∀ (p : ∀ i, Q i) (J : Finset (Fin M)),
      Integrable fun η => (∏ l ∈ J, O l (p l) η) * ballDensity w Ψ η) (T : Finset (Fin M)) :
    ∀ (p : ∀ i, Q i) (J : Finset (Fin M)), Integrable fun η =>
      (∏ l ∈ J, slotSumsAt T O p l η) * ballDensity w Ψ η := by
  induction T using Finset.induction_on with
  | empty =>
    intro p J
    simpa [slotSumsAt] using hint p J
  | insert a T hT ih =>
    intro p J
    by_cases ha : a ∈ J
    · have e : (fun η => (∏ l ∈ J, slotSumsAt (insert a T) O p l η) * ballDensity w Ψ η) =
          fun η => ∑ q, (∏ l ∈ J, slotSumsAt T O (Function.update p a q) l η) *
            ballDensity w Ψ η := by
        funext η
        rw [← Finset.sum_mul]
        congr 1
        rw [slotSumsAt_insert hT O p]
        simp only [← Finset.mul_prod_erase J _ ha, Function.update_self]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 1
        · simp [slotSumsAt, hT]
        · refine Finset.prod_congr rfl fun l hl => ?_
          have hne : l ≠ a := Finset.ne_of_mem_erase hl
          simp [Function.update_of_ne hne, slotSumsAt]
      rw [e]
      exact integrable_finsetSum _ fun q _ => ih (Function.update p a q) J
    · have e : (fun η => (∏ l ∈ J, slotSumsAt (insert a T) O p l η) * ballDensity w Ψ η) =
          fun η => (∏ l ∈ J, slotSumsAt T O p l η) * ballDensity w Ψ η := by
        funext η
        congr 1
        rw [slotSumsAt_insert hT O p]
        refine Finset.prod_congr rfl fun l hl => ?_
        have hne : l ≠ a := fun h => ha (h ▸ hl)
        simp [Function.update_of_ne hne]
      rw [e]
      exact ih p J
open Classical in
theorem cumulantFromMoments_slotSumsAt {Q : Fin M → Type} [∀ i, Fintype (Q i)] {w : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {O : ∀ i, Q i → BondField ι → ℝ}
    (hint : ∀ (p : ∀ i, Q i) (J : Finset (Fin M)),
      Integrable fun η => (∏ l ∈ J, O l (p l) η) * ballDensity w Ψ η) (T : Finset (Fin M)) :
    ∀ p : ∀ i, Q i, cumulantFromMoments w Ψ (slotSumsAt T O p) =
      ∑ p' : ∀ i, Q i, if (∀ i, i ∉ T → p' i = p i) then
        cumulantFromMoments w Ψ (fun i => O i (p' i)) else 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro p
    have e : slotSumsAt ∅ O p = fun i => O i (p i) := by
      funext i η
      simp [slotSumsAt]
    rw [e]
    have : ∀ p' : ∀ i, Q i, (∀ i, i ∉ (∅ : Finset (Fin M)) → p' i = p i) ↔ p' = p := by
      intro p'
      constructor
      · intro h
        funext i
        exact h i (by simp)
      · rintro rfl i _
        rfl
    simp only [this]
    simp
  | insert a T hT ih =>
    intro p
    rw [slotSumsAt_insert hT O p, cumulantFromMoments_update_finsetSum w Ψ _ a Finset.univ (O a)
      (fun q _ J => by
        rw [slotSumsAt_update hT O p q]
        exact integrable_slotSumsAt hint T _ J)]
    simp only [slotSumsAt_update hT O p, ih]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => ?_
    have hiff : ∀ q : Q a, (∀ i, i ∉ T → p' i = Function.update p a q i) ↔
        (q = p' a ∧ ∀ i, i ∉ insert a T → p' i = p i) := by
      intro q
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · have := h a hT
          simpa using this.symm
        · intro i hi
          have hne : i ≠ a := fun e => hi (e ▸ Finset.mem_insert_self _ _)
          have hiT : i ∉ T := fun h' => hi (Finset.mem_insert_of_mem h')
          have := h i hiT
          simpa [Function.update_of_ne hne] using this
      · rintro ⟨rfl, h⟩ i hi
        by_cases hne : i = a
        · subst hne
          simp
        · rw [Function.update_of_ne hne]
          exact h i (by simp [Finset.mem_insert, hne, hi])
    simp only [hiff]
    by_cases hR : ∀ i, i ∉ insert a T → p' i = p i
    · rw [if_pos hR]
      have h1 : ∀ q : Q a, (q = p' a ∧ ∀ i, i ∉ insert a T → p' i = p i) ↔ q = p' a :=
        fun q => ⟨fun h => h.1, fun h => ⟨h, hR⟩⟩
      simp only [h1]
      simp
    · rw [if_neg hR]
      exact Finset.sum_eq_zero fun q _ => if_neg fun h => hR h.2
end Multilinear
open Multilinear in
theorem placeSummedCumulantBound_of_expDecaySum (hW : ExpDecaySumBounded) :
    placeSummedCumulantBound := by
  classical
  intro N κ M hκ hM
  have hc : 0 < κ / (16 * M) := by positivity
  obtain ⟨W₀, hW₀, hb⟩ := hW N (κ / (16 * M)) hc
  refine ⟨W₀ ^ M, by positivity, ?_⟩
  intro F ι _ w Ψ Q _ z O e A T₀ r n Y₀ hr hT₀ hA he hne hmult hint hcum hdiam htri
  obtain ⟨p₀⟩ : Nonempty (∀ i, Q i) := ⟨fun i => (hne i).some⟩
  have hsum := cumulantFromMoments_slotSumsAt hint Finset.univ p₀
  have e1 : slotSumsAt Finset.univ O p₀ = fun i η => ∑ q, O i q η := by
    funext i η
    simp [slotSumsAt]
  rw [e1] at hsum
  simp only [Finset.mem_univ, not_true_eq_false, false_imp_iff, implies_true, if_true] at hsum
  rw [hsum]
  set g : ∀ i, Q i → ℝ := fun i q => Real.exp (-(κ / (16 * M) * (cellSupDist (z i q) Y₀ : ℝ)))
    with hg
  have hterm : ∀ p : ∀ i, Q i, |cumulantFromMoments w Ψ fun i => O i (p i)| ≤
      T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n)) * ∏ i, g i (p i) := by
    intro p
    refine (hcum p).trans ?_
    have hprod : ∏ i, (A i * Real.exp (-(r * e i (p i)))) =
        (∏ i, A i) * Real.exp (-(r * ∑ i, e i (p i))) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    have hgp : ∏ i, g i (p i) =
        Real.exp (-(κ / (16 * M) * ∑ i, (cellSupDist (z i (p i)) Y₀ : ℝ))) := by
      simp only [hg]
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hprod, hgp]
    have hD : ∑ i, (cellSupDist (z i (p i)) Y₀ : ℝ) ≤
        M * (cellsDiameter fun i => z i (p i) : ℝ) := by
      calc ∑ i, (cellSupDist (z i (p i)) Y₀ : ℝ) ≤ ∑ _i : Fin M,
            (cellsDiameter fun i => z i (p i) : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact_mod_cast hdiam p i
        _ = M * (cellsDiameter fun i => z i (p i) : ℝ) := by simp
    have hexp : -(r * ∑ i, e i (p i)) + -(κ / 8 * (cellsDiameter fun i => z i (p i) : ℝ)) ≤
        -(κ / 16 * n) + -(κ / (16 * M) * ∑ i, (cellSupDist (z i (p i)) Y₀ : ℝ)) := by
      have h1 := htri p
      have he0 : 0 ≤ ∑ i, e i (p i) := Finset.sum_nonneg fun i _ => he i _
      have h2 : κ / 16 * ∑ i, e i (p i) ≤ r * ∑ i, e i (p i) :=
        mul_le_mul_of_nonneg_right hr he0
      have h3 : κ / 16 * n ≤
          κ / 16 * ((cellsDiameter fun i => z i (p i) : ℝ) + ∑ i, e i (p i)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : κ / (16 * M) * ∑ i, (cellSupDist (z i (p i)) Y₀ : ℝ) ≤
          κ / (16 * M) * (M * (cellsDiameter fun i => z i (p i) : ℝ)) :=
        mul_le_mul_of_nonneg_left hD hc.le
      have h5 : κ / (16 * M) * (M * (cellsDiameter fun i => z i (p i) : ℝ)) =
          κ / 16 * (cellsDiameter fun i => z i (p i) : ℝ) := by
        field_simp
      nlinarith
    have hA0 : 0 ≤ ∏ i, A i := Finset.prod_nonneg fun i _ => hA i
    calc T₀ * ((∏ i, A i) * Real.exp (-(r * ∑ i, e i (p i)))) *
          Real.exp (-(κ / 8 * (cellsDiameter fun i => z i (p i) : ℝ)))
        = T₀ * (∏ i, A i) * Real.exp (-(r * ∑ i, e i (p i)) +
            -(κ / 8 * (cellsDiameter fun i => z i (p i) : ℝ))) := by
          rw [Real.exp_add]
          ring
      _ ≤ T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n) +
            -(κ / (16 * M) * ∑ i, (cellSupDist (z i (p i)) Y₀ : ℝ))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (mul_nonneg hT₀ hA0)
      _ = _ := by
          rw [Real.exp_add]
          ring
  have hfin : ∑ p : ∀ i, Q i, ∏ i, g i (p i) ≤ W₀ ^ M := by
    have h1 : ∑ p : ∀ i, Q i, ∏ i, g i (p i) = ∏ i, ∑ q, g i q := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [h1]
    calc ∏ i, ∑ q, g i q ≤ ∏ _i : Fin M, W₀ := by
          refine Finset.prod_le_prod
            (fun i _ => Finset.sum_nonneg fun q _ => (Real.exp_pos _).le) ?_
          intro i _
          exact hb F (Q i) (z i) (hmult i) Y₀
      _ = W₀ ^ M := by simp
  have hA0 : 0 ≤ ∏ i, A i := Finset.prod_nonneg fun i _ => hA i
  calc |∑ p : ∀ i, Q i, cumulantFromMoments w Ψ fun i => O i (p i)|
      ≤ ∑ p : ∀ i, Q i, |cumulantFromMoments w Ψ fun i => O i (p i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : ∀ i, Q i, T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n)) * ∏ i, g i (p i) :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n)) * ∑ p : ∀ i, Q i, ∏ i, g i (p i) := by
        rw [Finset.mul_sum]
    _ ≤ T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n)) * W₀ ^ M :=
        mul_le_mul_of_nonneg_left hfin
          (mul_nonneg (mul_nonneg hT₀ hA0) (Real.exp_pos _).le)
    _ = W₀ ^ M * T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n)) := by ring
end YangMills.Construction.Cumulants
end
