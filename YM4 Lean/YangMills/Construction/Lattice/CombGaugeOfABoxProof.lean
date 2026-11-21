import YangMills.Construction.Lattice.CombGaugeOfABox
import YangMills.Construction.Lattice.PathRearrangement
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequalityProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace CombGaugeOnBox
section Geometry
variable {L m : ℕ} {j : ℤ}
def shiftBy (z : Site L m j) (t : Fin 4 → ℤ) : Site L m j := z + ∑ μ, t μ • unitStep L m j μ
theorem meshSize_pos (hL : 0 < L) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p16883 <;> assumption
theorem torusSide_pos (hL : 0 < L) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p16249 <;> assumption
theorem coe_sum_zsmul_unitStep (t : Fin 4 → ℤ) (μ : Fin 4) :
    ((∑ ν, t ν • unitStep L m j ν : Site L m j) : FourTorus L m) μ =
      (((t μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  have h : ((∑ ν, t ν • unitStep L m j ν : Site L m j) : FourTorus L m) =
      ∑ ν, t ν • ((unitStep L m j ν : Site L m j) : FourTorus L m) := by
    simp
  rw [h, Finset.sum_apply, Finset.sum_eq_single μ]
  · simp only [unitStep, pointOnAxis, Pi.smul_apply, Pi.single_eq_same]
    rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
  · intro ν _ hν
    simp [unitStep, pointOnAxis, Pi.single_eq_of_ne hν.symm]
  · simp
theorem int_eq_zero_of_coe_eq_zero (hL : 0 < L) {t : ℤ}
    (h : (((t : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0)
    (hb : ((|t| : ℤ) : ℝ) * meshSize L j < torusSide L m) : t = 0 := by
  obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff _).mp h
  rw [zsmul_eq_mul] at hq
  have hξ : 0 < meshSize L j := meshSize_pos hL
  have hS : 0 < torusSide L m := torusSide_pos hL
  have h1 : |(q : ℝ)| * torusSide L m = ((|t| : ℤ) : ℝ) * meshSize L j := by
    have := congrArg abs hq
    rw [abs_mul, abs_mul, abs_of_pos hS, abs_of_pos hξ] at this
    simpa using this
  have h2 : |(q : ℝ)| < 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have h3 : q = 0 := by
    have : |q| < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.mp this
  subst h3
  simp only [Int.cast_zero, zero_mul] at hq
  rcases mul_eq_zero.mp hq.symm with h4 | h4
  · exact_mod_cast h4
  · exact absurd h4 hξ.ne'
theorem chartOffset_unique (hL : 0 < L) {y x : Site L m j} {d d' : Fin 4 → ℤ}
    (h : IsChartOffset y x d) (h' : IsChartOffset y x d') : d = d' := by
  funext μ
  have e : ∑ ν, d ν • unitStep L m j ν = ∑ ν, d' ν • unitStep L m j ν := h.1.symm.trans h'.1
  have c := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) e
  simp only [coe_sum_zsmul_unitStep] at c
  have z : ((((d μ - d' μ : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    push_cast
    rw [sub_mul, AddCircle.coe_sub, c, sub_self]
  have hb : ((|d μ - d' μ| : ℤ) : ℝ) * meshSize L j < torusSide L m := by
    have b1 := h.2 μ
    have b2 := h'.2 μ
    have b3 : ((|d μ - d' μ| : ℤ) : ℝ) ≤ ((|d μ| : ℤ) : ℝ) + ((|d' μ| : ℤ) : ℝ) := by
      exact_mod_cast abs_sub _ _
    nlinarith [meshSize_pos (j := j) hL]
  have := int_eq_zero_of_coe_eq_zero hL z hb
  omega
theorem chartOffset_eq (hL : 0 < L) {y x : Site L m j} {d : Fin 4 → ℤ}
    (h : IsChartOffset y x d) : chartOffset y x = d :=
  chartOffset_unique hL
    (Classical.epsilon_spec (p := IsChartOffset y x) ⟨d, h⟩) h
theorem torusSide_eq_int_mul (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    ∃ N : ℤ, 2 ≤ N ∧ torusSide L m = (N : ℝ) * meshSize L j := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + j)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨2 * (L : ℤ) ^ k, ?_, ?_⟩
  · have : 1 ≤ (L : ℤ) ^ k := one_le_pow₀ (by exact_mod_cast hL)
    omega
  · have h1 : (L : ℝ) ^ m = (L : ℝ) ^ k * (L : ℝ) ^ (-j) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL']
      congr 1
      omega
    simp only [torusSide, meshSize]
    push_cast
    rw [h1]
    ring
theorem exists_intervals (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {Y : Set (Site L m j)}
    (hY : IsSiteBox j Y) {y : Site L m j} (hy : y ∈ Y) :
    ∃ I : Fin 4 → Set ℤ, (∀ μ, (I μ).OrdConnected) ∧ (∀ μ, (0 : ℤ) ∈ I μ) ∧
      (∀ μ, ∀ a ∈ I μ, ∀ b ∈ I μ, ((|a - b| : ℤ) : ℝ) * meshSize L j < torusSide L m / 2) ∧
      (∀ t : Fin 4 → ℤ, (∀ μ, t μ ∈ I μ) → shiftBy y t ∈ Y) ∧
      (∀ x ∈ Y, IsChartOffset y x (chartOffset y x) ∧
        ∀ μ, chartOffset y x μ ∈ I μ) := by
  obtain ⟨i, X, _, _, _, ⟨c, hc⟩, rfl⟩ := hY
  have hξ : 0 < meshSize L j := meshSize_pos hL
  obtain ⟨vy, hvy, hcy⟩ := c.exists_lift ⟨(y : FourTorus L m), hy⟩
  have hvy' : ∀ μ, vy μ ∈ Set.Icc (c.lower μ) (c.upper μ) := fun μ => hvy μ (Set.mem_univ μ)
  have hwidth : ∀ (μ : Fin 4) (u v : ℝ), u ∈ Set.Icc (c.lower μ) (c.upper μ) →
      v ∈ Set.Icc (c.lower μ) (c.upper μ) → |u - v| < torusSide L m / 2 := by
    intro μ u v hu hv
    have := hc μ
    rw [abs_lt]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  refine ⟨fun μ => {n : ℤ | vy μ + (n : ℝ) * meshSize L j ∈ Set.Icc (c.lower μ) (c.upper μ)},
    ?_, ?_, ?_, ?_, ?_⟩
  · intro μ
    refine ⟨fun a ha b hb n hn => ?_⟩
    have h1 : (a : ℝ) ≤ n := by exact_mod_cast hn.1
    have h2 : (n : ℝ) ≤ b := by exact_mod_cast hn.2
    have h3 := mul_le_mul_of_nonneg_right h1 hξ.le
    have h4 := mul_le_mul_of_nonneg_right h2 hξ.le
    exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · intro μ
    simpa using hvy' μ
  · intro μ a ha b hb
    have h1 := hwidth μ _ _ ha hb
    have h2 : vy μ + (a : ℝ) * meshSize L j - (vy μ + (b : ℝ) * meshSize L j) =
        ((a - b : ℤ) : ℝ) * meshSize L j := by push_cast; ring
    rw [h2, abs_mul, abs_of_pos hξ] at h1
    simpa using h1
  · intro t ht
    show ((shiftBy y t : Site L m j) : FourTorus L m) ∈ X
    have h1 : TorusMetric.torusProj (torusSide L m) (fun μ => vy μ + (t μ : ℝ) * meshSize L j) =
        ((shiftBy y t : Site L m j) : FourTorus L m) := by
      funext μ
      have h2 := congrFun hcy μ
      simp only [TorusMetric.torusProj] at h2 ⊢
      simp only [shiftBy, AddSubgroup.coe_add, Pi.add_apply, coe_sum_zsmul_unitStep]
      rw [AddCircle.coe_add, h2]
    rw [← c.image_proj]
    exact ⟨_, fun μ _ => ht μ, h1⟩
  · intro x hx
    obtain ⟨vx, hvx, hcx⟩ := c.exists_lift ⟨(x : FourTorus L m), hx⟩
    have hvx' : ∀ μ, vx μ ∈ Set.Icc (c.lower μ) (c.upper μ) :=
      fun μ => hvx μ (Set.mem_univ μ)
    obtain ⟨n, hn⟩ := (x - y).2
    obtain ⟨N, -, hN⟩ := torusSide_eq_int_mul (m := m) hL hj
    have hz : ∀ μ, ((vx μ - vy μ - (n μ : ℝ) * meshSize L j : ℝ) :
        AddCircle (torusSide L m)) = 0 := by
      intro μ
      have h1 := hn μ
      have h2 := congrFun hcx μ
      have h3 := congrFun hcy μ
      simp only [TorusMetric.torusProj] at h2 h3
      rw [AddCircle.coe_sub, AddCircle.coe_sub, h2, h3, ← h1]
      simp
    choose q hq using fun μ => (AddCircle.coe_eq_zero_iff _).mp (hz μ)
    set d : Fin 4 → ℤ := fun μ => n μ + q μ * N with hd
    have hvd : ∀ μ, vx μ = vy μ + (d μ : ℝ) * meshSize L j := by
      intro μ
      have h1 := hq μ
      rw [zsmul_eq_mul, hN] at h1
      simp only [hd]
      push_cast
      linarith
    have off : IsChartOffset y x d := by
      refine ⟨Subtype.ext (funext fun μ => ?_), fun μ => ?_⟩
      · rw [coe_sum_zsmul_unitStep]
        have h2 := congrFun hcx μ
        have h3 := congrFun hcy μ
        simp only [TorusMetric.torusProj] at h2 h3
        have h4 : (d μ : ℝ) * meshSize L j = vx μ - vy μ := by rw [hvd μ]; ring
        rw [h4, AddCircle.coe_sub, h2, h3]
        rfl
      · have h1 := hwidth μ _ _ (hvx' μ) (hvy' μ)
        rw [hvd μ, add_sub_cancel_left, abs_mul, abs_of_pos hξ] at h1
        simpa using h1
    rw [chartOffset_eq hL off]
    refine ⟨off, fun μ => ?_⟩
    show vy μ + (d μ : ℝ) * meshSize L j ∈ Set.Icc (c.lower μ) (c.upper μ)
    rw [← hvd μ]
    exact hvx' μ
theorem shiftBy_add_single (y : Site L m j) (t : Fin 4 → ℤ) (μ : Fin 4) (a : ℤ) :
    shiftBy y (t + Pi.single μ a) = shiftBy y t + a • unitStep L m j μ := by
  simp only [shiftBy, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
  congr 2
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ h
    simp [Pi.single_eq_of_ne h]
  · simp
theorem shiftBy_zero (y : Site L m j) : shiftBy y 0 = y := by simp [shiftBy]
theorem shiftBy_of_isChartOffset {y x : Site L m j} {d : Fin 4 → ℤ}
    (h : IsChartOffset y x d) : shiftBy y d = x := by
  rw [shiftBy, ← h.1]
  abel
structure BoxWindow (Y : Set (Site L m j)) (y : Site L m j) (I : Fin 4 → Set ℤ) : Prop where
  ordConnected : ∀ μ, (I μ).OrdConnected
  zero_mem : ∀ μ, (0 : ℤ) ∈ I μ
  short : ∀ μ, ∀ a ∈ I μ, ∀ b ∈ I μ, ((|a - b| : ℤ) : ℝ) * meshSize L j < torusSide L m / 2
  shiftBy_mem : ∀ t : Fin 4 → ℤ, (∀ μ, t μ ∈ I μ) → shiftBy y t ∈ Y
theorem abs_le_of_coordCount_le (hL : 0 < L) {Y : Set (Site L m j)} {y : Site L m j}
    {I : Fin 4 → Set ℤ} (w : BoxWindow Y y I) {s : ℕ} {μ : Fin 4} (hc : coordCount μ Y ≤ s + 1)
    {a : ℤ} (ha : a ∈ I μ) : |a| ≤ s := by
  have hS : 0 < torusSide L m := torusSide_pos hL
  set f : ℤ → AddCircle (torusSide L m) :=
    fun n => ((shiftBy y (Pi.single μ n) : Site L m j) : FourTorus L m) μ with hf
  have hfv : ∀ n, f n = (y : FourTorus L m) μ +
      (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
    intro n
    simp only [hf, shiftBy, AddSubgroup.coe_add, Pi.add_apply, coe_sum_zsmul_unitStep,
      Pi.single_eq_same]
  have hT : Set.uIcc 0 a ⊆ I μ := (w.ordConnected μ).uIcc_subset (w.zero_mem μ) ha
  have inj : Set.InjOn f (Set.uIcc 0 a) := by
    intro p hp q hq hpq
    rw [hfv, hfv] at hpq
    have h1 := add_left_cancel hpq
    have h2 : ((((p - q : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      push_cast
      rw [sub_mul, AddCircle.coe_sub, h1, sub_self]
    have h3 := w.short μ p (hT hp) q (hT hq)
    have := int_eq_zero_of_coe_eq_zero hL h2 (by linarith)
    omega
  have himg : f '' Set.uIcc 0 a ⊆ (fun x : Site L m j => (x : FourTorus L m) μ) '' Y := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨_, w.shiftBy_mem (Pi.single μ n) fun ν => ?_, rfl⟩
    by_cases h : ν = μ
    · subst h
      simpa using hT hn
    · simpa [Pi.single_eq_of_ne h] using w.zero_mem ν
  have h1 : (Set.uIcc 0 a).encard ≤ (s : ℕ∞) + 1 :=
    calc (Set.uIcc 0 a).encard = (f '' Set.uIcc 0 a).encard := inj.encard_image.symm
      _ ≤ _ := Set.encard_le_encard himg
      _ ≤ _ := hc
  have h2 : (Set.uIcc 0 a) = ((Finset.Icc (0 ⊓ a) (0 ⊔ a) : Finset ℤ) : Set ℤ) := by
    rw [Finset.coe_Icc]
    rfl
  rw [h2, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc] at h1
  have h3 : ((0 ⊔ a) + 1 - (0 ⊓ a)).toNat ≤ s + 1 := by exact_mod_cast h1
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]
    simp only [h, sup_of_le_right, inf_of_le_left] at h3
    omega
  · rw [abs_of_nonpos h]
    simp only [h, sup_of_le_left, inf_of_le_right] at h3
    omega
theorem chartOffset_add_unitStep (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {Y : Set (Site L m j)}
    {y x : Site L m j} {I : Fin 4 → Set ℤ} (w : BoxWindow Y y I) (ν : Fin 4) {D E : Fin 4 → ℤ}
    (hx : IsChartOffset y x D) (hDI : ∀ μ, D μ ∈ I μ)
    (hx' : IsChartOffset y (x + unitStep L m j ν) E) (hEI : ∀ μ, E μ ∈ I μ) :
    E = D + Pi.single ν 1 := by
  have hξ : 0 < meshSize L j := meshSize_pos hL
  obtain ⟨N, hN2, hN⟩ := torusSide_eq_int_mul (m := m) hL hj
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  obtain ⟨D', hD'⟩ : ∃ D' : Fin 4 → ℤ, D' = D + Pi.single ν 1 := ⟨_, rfl⟩
  have e1 : shiftBy y E = shiftBy y D' := by
    rw [hD', shiftBy_of_isChartOffset hx', shiftBy_add_single,
      shiftBy_of_isChartOffset hx, one_smul]
  have e2 : ∑ μ, E μ • unitStep L m j μ = ∑ μ, D' μ • unitStep L m j μ :=
    add_left_cancel e1
  rw [← hD']
  funext μ
  have c := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) e2
  simp only [coe_sum_zsmul_unitStep] at c
  have z : ((((E μ - D' μ : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [Int.cast_sub, sub_mul, AddCircle.coe_sub, c, sub_self]
  have hb : ((|E μ - D' μ| : ℤ) : ℝ) * meshSize L j < torusSide L m := by
    have b1 := w.short μ _ (hEI μ) _ (hDI μ)
    have b2 : |E μ - D' μ| ≤ |E μ - D μ| + 1 := by
      have h1 : D' μ = D μ ∨ D' μ = D μ + 1 := by
        rw [hD']
        by_cases h : μ = ν
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h]
      rcases h1 with h1 | h1 <;> rw [h1]
      · linarith
      · have : E μ - (D μ + 1) = (E μ - D μ) - 1 := by ring
        rw [this]
        exact (abs_sub _ _).trans (by simp)
    have b3 : ((|E μ - D' μ| : ℤ) : ℝ) ≤ ((|E μ - D μ| : ℤ) : ℝ) + 1 := by
      exact_mod_cast b2
    have b4 : meshSize L j ≤ torusSide L m / 2 := by rw [hN]; nlinarith
    have b5 := mul_le_mul_of_nonneg_right b3 hξ.le
    linarith
  have := int_eq_zero_of_coe_eq_zero hL z hb
  omega
end Geometry
section Paths
variable {L m : ℕ} {j : ℤ}
def wordSum (𝔰 : StepWord L m j) : Site L m j :=
  (𝔰.map fun s : UnitStepVec L m j => (s : Site L m j)).sum
@[simp] theorem wordSum_nil : wordSum ([] : StepWord L m j) = 0 := rfl
theorem wordSum_cons (s : UnitStepVec L m j) (𝔰 : StepWord L m j) :
    wordSum (s :: 𝔰) = s + wordSum 𝔰 := by simp [wordSum]
theorem wordSum_append (u v : StepWord L m j) : wordSum (u ++ v) = wordSum u + wordSum v := by
  simp [wordSum]
def StaysWithin (Y : Set (Site L m j)) : Site L m j → StepWord L m j → Prop
  | z, [] => z ∈ Y
  | z, s :: 𝔰 => z ∈ Y ∧ StaysWithin Y (z + s) 𝔰
variable {Y : Set (Site L m j)}
theorem StaysWithin.start_mem {z : Site L m j} {𝔰 : StepWord L m j} (h : StaysWithin Y z 𝔰) :
    z ∈ Y := by
  cases 𝔰 with
  | nil => exact h
  | cons s 𝔰 => exact h.1
theorem staysWithin_append {z : Site L m j} {u v : StepWord L m j} :
    StaysWithin Y z (u ++ v) ↔ StaysWithin Y z u ∧ StaysWithin Y (z + wordSum u) v := by
  induction u generalizing z with
  | nil =>
    simp only [List.nil_append, wordSum_nil, add_zero]
    exact ⟨fun h => ⟨h.start_mem, h⟩, fun h => h.2⟩
  | cons s u ih =>
    simp only [List.cons_append, StaysWithin, ih, wordSum_cons, add_assoc, and_assoc]
theorem pathOfWord_append (z : Site L m j) (u v : StepWord L m j) :
    pathOfWord z (u ++ v) = pathOfWord z u ++ pathOfWord (z + wordSum u) v := by
  induction u generalizing z with
  | nil => simp [pathOfWord]
  | cons s u ih => simp [pathOfWord, ih, wordSum_cons, add_assoc]
theorem pathHolonomy_append (U : Bond L m j → ComplexMatrix2) (Γ Γ' : List (Bond L m j)) :
    pathHolonomy U (Γ ++ Γ') = pathHolonomy U Γ * pathHolonomy U Γ' := by
  simp [pathHolonomy]
theorem liesIn_of_staysWithin {z : Site L m j} {𝔰 : StepWord L m j} (h : StaysWithin Y z 𝔰) :
    ∀ b ∈ pathOfWord z 𝔰, b.LiesIn Y := by
  induction 𝔰 generalizing z with
  | nil => simp [pathOfWord]
  | cons s 𝔰 ih =>
    intro b hb
    simp only [pathOfWord, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨h.1, h.2.start_mem⟩
    · exact ih h.2 b hb
def posUnit (μ : Fin 4) : UnitStepVec L m j := ⟨unitStep L m j μ, μ, Or.inl rfl⟩
def negUnit (μ : Fin 4) : UnitStepVec L m j := ⟨-unitStep L m j μ, μ, Or.inr rfl⟩
def wordAlong (μ : Fin 4) (n : ℤ) : StepWord L m j :=
  if 0 ≤ n then List.replicate n.toNat (posUnit μ)
  else List.replicate (-n).toNat (negUnit μ)
theorem forwardFlow_eq (x : Site L m j) (μ : Fin 4) (k : ℕ) :
    forwardAxisPath x μ k = pathOfWord x (List.replicate k (posUnit μ)) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [forwardAxisPath, List.replicate_succ, pathOfWord]
    rw [ih]
    rfl
theorem backwardFlow_eq (x : Site L m j) (μ : Fin 4) (k : ℕ) :
    backwardAxisPath x μ k = pathOfWord x (List.replicate k (negUnit μ)) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [backwardAxisPath, List.replicate_succ, pathOfWord]
    have h : x - unitStep L m j μ = x + ((negUnit μ : UnitStepVec L m j) : Site L m j) :=
      sub_eq_add_neg _ _
    rw [ih, h]
    congr 1
    exact Bond.ext rfl h
theorem flowAlong_eq (x : Site L m j) (μ : Fin 4) (n : ℤ) :
    flowAlong x μ n = pathOfWord x (wordAlong μ n) := by
  simp only [flowAlong, wordAlong]
  split_ifs
  · exact forwardFlow_eq _ _ _
  · exact backwardFlow_eq _ _ _
theorem wordSum_replicate (k : ℕ) (u : UnitStepVec L m j) :
    wordSum (List.replicate k u) = k • (u : Site L m j) := by
  unfold wordSum
  rw [List.map_replicate, List.sum_replicate]
theorem wordSum_wordAlong (μ : Fin 4) (n : ℤ) :
    wordSum (wordAlong μ n : StepWord L m j) = n • unitStep L m j μ := by
  unfold wordAlong
  split_ifs with h
  · rw [wordSum_replicate]
    change n.toNat • unitStep L m j μ = _
    conv_rhs => rw [← Int.toNat_of_nonneg h]
    rw [natCast_zsmul]
  · rw [wordSum_replicate]
    change (-n).toNat • (-unitStep L m j μ) = _
    have h1 : n = -(((-n).toNat : ℕ) : ℤ) := by omega
    conv_rhs => rw [h1, neg_zsmul, natCast_zsmul]
    rw [smul_neg]
def wordThrough (n : Fin 4 → ℤ) : List (Fin 4) → StepWord L m j
  | [] => []
  | μ :: l => wordAlong μ (n μ) ++ wordThrough n l
theorem wordThrough_append (n : Fin 4 → ℤ) (l l' : List (Fin 4)) :
    (wordThrough n (l ++ l') : StepWord L m j) = wordThrough n l ++ wordThrough n l' := by
  induction l with
  | nil => rfl
  | cons μ l ih => simp [wordThrough, ih]
theorem wordThrough_congr {n n' : Fin 4 → ℤ} {l : List (Fin 4)} (h : ∀ μ ∈ l, n μ = n' μ) :
    (wordThrough n l : StepWord L m j) = wordThrough n' l := by
  induction l with
  | nil => rfl
  | cons μ l ih =>
    simp only [wordThrough]
    rw [h μ (List.mem_cons_self ..), ih fun ν hν => h ν (List.mem_cons_of_mem _ hν)]
theorem stepsThroughAxes_eq (n : Fin 4 → ℤ) (x : Site L m j) (l : List (Fin 4)) :
    stepsThroughAxes n x l = pathOfWord x (wordThrough n l) := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [stepsThroughAxes, wordThrough, pathOfWord_append, flowAlong_eq, wordSum_wordAlong,
      ih]
theorem length_wordAlong (μ : Fin 4) (n : ℤ) :
    (wordAlong μ n : StepWord L m j).length = n.natAbs := by
  unfold wordAlong
  split_ifs <;> simp <;> omega
theorem length_wordThrough (n : Fin 4 → ℤ) (l : List (Fin 4)) :
    ((wordThrough n l : StepWord L m j).length : ℝ) =
      (l.map fun μ => ((|n μ| : ℤ) : ℝ)).sum := by
  induction l with
  | nil => simp [wordThrough]
  | cons μ l ih =>
    simp only [wordThrough, List.length_append, length_wordAlong, Nat.cast_add, ih, List.map_cons,
      List.sum_cons, Nat.cast_natAbs]
def coordsAfter (n : Fin 4 → ℤ) : List (Fin 4) → (Fin 4 → ℤ) → Fin 4 → ℤ
  | [], t => t
  | μ :: l, t => coordsAfter n l (t + Pi.single μ (n μ))
theorem shiftBy_coordsAfter (y : Site L m j) (n : Fin 4 → ℤ) (l : List (Fin 4))
    (t : Fin 4 → ℤ) : shiftBy y (coordsAfter n l t) = shiftBy y t + wordSum (wordThrough n l) := by
  induction l generalizing t with
  | nil => simp [coordsAfter, wordThrough]
  | cons μ l ih =>
    simp only [coordsAfter, wordThrough, ih, shiftBy_add_single, wordSum_append,
      wordSum_wordAlong, add_assoc]
theorem coordsAfter_apply (n : Fin 4 → ℤ) {l : List (Fin 4)} (h : l.Nodup) (t : Fin 4 → ℤ)
    (ν : Fin 4) : coordsAfter n l t ν = t ν + if ν ∈ l then n ν else 0 := by
  classical
  induction l generalizing t with
  | nil => simp [coordsAfter]
  | cons μ l ih =>
    have h' := List.nodup_cons.mp h
    rw [coordsAfter, ih h'.2]
    by_cases hν : ν = μ
    · subst hν
      simp [h'.1]
    · simp [hν]
variable {y : Site L m j} {I : Fin 4 → Set ℤ}
theorem staysWithin_replicate (w : BoxWindow Y y I) (u : UnitStepVec L m j) (μ : Fin 4) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hu : (u : Site L m j) = ε • unitStep L m j μ) :
    ∀ (k : ℕ) (t : Fin 4 → ℤ), (∀ ν, t ν ∈ I ν) → t μ + k * ε ∈ I μ →
      StaysWithin Y (shiftBy y t) (List.replicate k u) := by
  intro k
  induction k with
  | zero => exact fun t ht _ => w.shiftBy_mem t ht
  | succ k ih =>
    intro t ht hk
    refine ⟨w.shiftBy_mem t ht, ?_⟩
    have e : shiftBy y t + u = shiftBy y (t + Pi.single μ ε) := by
      rw [shiftBy_add_single, hu]
    rw [e]
    have hm : t μ + ε ∈ I μ := by
      refine (w.ordConnected μ).uIcc_subset (ht μ) hk ?_
      rw [Set.mem_uIcc]
      push_cast
      rcases hε with rfl | rfl <;> omega
    refine ih _ (fun ν => ?_) ?_
    · by_cases h : ν = μ
      · subst h
        simpa using hm
      · simpa [Pi.single_eq_of_ne h] using ht ν
    · have : (t + Pi.single μ ε : Fin 4 → ℤ) μ + (k : ℤ) * ε = t μ + ((k + 1 : ℕ) : ℤ) * ε := by
        simp only [Pi.add_apply, Pi.single_eq_same]
        push_cast
        ring
      rw [this]
      exact hk
theorem staysWithin_wordAlong (w : BoxWindow Y y I) {t : Fin 4 → ℤ} (ht : ∀ ν, t ν ∈ I ν)
    (μ : Fin 4) {n : ℤ} (h : t μ + n ∈ I μ) : StaysWithin Y (shiftBy y t) (wordAlong μ n) := by
  unfold wordAlong
  split_ifs with hn
  · refine staysWithin_replicate w _ μ 1 (Or.inl rfl) (by simp [posUnit]) _ t ht ?_
    rw [Int.toNat_of_nonneg hn, mul_one]
    exact h
  · refine staysWithin_replicate w _ μ (-1) (Or.inr rfl) (by simp [negUnit]) _ t ht ?_
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -n)]
    have : t μ + -n * -1 = t μ + n := by ring
    rw [this]
    exact h
theorem staysWithin_wordThrough (w : BoxWindow Y y I) (n : Fin 4 → ℤ) :
    ∀ (l : List (Fin 4)) (t : Fin 4 → ℤ), l.Nodup → (∀ ν, t ν ∈ I ν) →
      (∀ ν ∈ l, t ν + n ν ∈ I ν) → StaysWithin Y (shiftBy y t) (wordThrough n l) := by
  intro l
  induction l with
  | nil => exact fun t _ ht _ => w.shiftBy_mem t ht
  | cons μ l ih =>
    intro t hl ht hn
    have hl' := List.nodup_cons.mp hl
    simp only [wordThrough]
    rw [staysWithin_append]
    refine ⟨staysWithin_wordAlong w ht μ (hn μ (List.mem_cons_self ..)), ?_⟩
    rw [wordSum_wordAlong, ← shiftBy_add_single]
    refine ih _ hl'.2 (fun ν => ?_) (fun ν hν => ?_)
    · by_cases h : ν = μ
      · subst h
        simpa using hn ν (List.mem_cons_self ..)
      · simpa [Pi.single_eq_of_ne h] using ht ν
    · have h : ν ≠ μ := fun e => hl'.1 (e ▸ hν)
      simpa [Pi.single_eq_of_ne h] using hn ν (List.mem_cons_of_mem _ hν)
end Paths
section Level
variable {L m K n : ℕ} {Y : Set (SiteAtLevel L m K n)} {W : BondAtLevel L m K n → ComplexMatrix2}
theorem pathHolonomy_mem (hW : IsGaugeFieldWithin Y W) {Γ : List (BondAtLevel L m K n)}
    (h : ∀ b ∈ Γ, b.LiesIn Y) : pathHolonomy W Γ ∈ ComplexMatrix2.specialUnitary := by
  induction Γ with
  | nil => exact one_mem _
  | cons b Γ ih =>
    have h1 : W b ∈ ComplexMatrix2.specialUnitary := hW.1 b (h b (List.mem_cons_self ..))
    have h2 := ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact mul_mem h1 h2
theorem mem_unitaryGroup_of_mem_specialUnitary {T : ComplexMatrix2}
    (h : T ∈ ComplexMatrix2.specialUnitary) : T ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.specialUnitaryGroup_le_unitaryGroup h
theorem mul_inv_of_mem_specialUnitary {T : ComplexMatrix2}
    (h : T ∈ ComplexMatrix2.specialUnitary) : T * T⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p21267 <;> assumption
theorem inv_mem_unitaryGroup_of_mem_specialUnitary {T : ComplexMatrix2}
    (h : T ∈ ComplexMatrix2.specialUnitary) : T⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hu := mem_unitaryGroup_of_mem_specialUnitary h
  have h1 : T⁻¹ = star T := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  rw [h1, Matrix.mem_unitaryGroup_iff, star_star]
  exact Matrix.mem_unitaryGroup_iff'.mp hu
theorem cornerSite_eq (e : AdjacentSwap L m (levelDepth K n)) (z : SiteAtLevel L m K n) :
    e.cornerSite z = z + wordSum e.pre := by
  unfold AdjacentSwap.cornerSite wordSum
  congr 1
  generalize e.pre = l
  induction l with
  | nil => rfl
  | cons s l ih => simpa using ih
theorem swap_holonomy_bound (hR : PathRearrangementBound)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) (hodd : Odd L) (h13 : 13 ≤ L)
    (hm : 0 < m) (hj : -(m : ℤ) ≤ levelDepth K n) (hW : IsGaugeFieldWithin Y W) {ϖ : ℝ}
    (hϖ : 0 ≤ ϖ)
    (hP : ∀ p : PlaquetteAtLevel L m K n, p.LiesIn Y →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) ≤ ϖ)
    (z : SiteAtLevel L m K n) (e : AdjacentSwap L m (levelDepth K n))
    (h1 : StaysWithin Y z e.original) (h2 : StaysWithin Y z e.swapped) :
    ComplexMatrix2.operatorNorm (wordHolonomy W z e.original - wordHolonomy W z e.swapped) ≤ ϖ := by
  have hc := (hR L m hodd h13 hm (levelDepth K n) hj (bondsWithin Y).bonds W
    (bondsWithin Y).opposite_mem hW z).1 e (fun b hb => liesIn_of_staysWithin h1 b hb)
    (fun b hb => liesIn_of_staysWithin h2 b hb)
  by_cases hpar : e.IsCollinear
  · rw [hc.1 hpar, sub_self]
    simpa using hϖ
  · obtain ⟨⟨p, hp⟩, hall⟩ := hc.2 hpar
    have s1 := (staysWithin_append.mp h1).2
    have s2 := (staysWithin_append.mp h2).2
    rw [← cornerSite_eq] at s1 s2
    have hin : p.LiesIn Y := by
      intro q hq
      rw [hp] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact s1.1
      · exact s1.2.1
      · exact s2.2.1
      · exact s1.2.2.start_mem
    obtain ⟨T, hT, ε, hε, hEq⟩ := hall p hp (fun b hb => hin.boundaryBonds_liesIn b hb)
    have hs := pathHolonomy_mem hW (liesIn_of_staysWithin h1)
    have ht := pathHolonomy_mem hW (liesIn_of_staysWithin h2)
    have hPu : plaquetteHolonomy W p ∈ ComplexMatrix2.specialUnitary :=
      pathHolonomy_mem hW (hin.boundaryBonds_liesIn)
    calc ComplexMatrix2.operatorNorm (wordHolonomy W z e.original - wordHolonomy W z e.swapped)
        = ComplexMatrix2.operatorNorm
            (wordHolonomy W z e.original * (wordHolonomy W z e.swapped)⁻¹ - 1) :=
          (hN.2.2.2.1 _ _ (mem_unitaryGroup_of_mem_specialUnitary hs)
            (mem_unitaryGroup_of_mem_specialUnitary ht)).symm
      _ = ComplexMatrix2.operatorNorm (T * (plaquetteHolonomy W p ^ ε - 1) * T⁻¹) := by
          rw [hEq, mul_sub, sub_mul, mul_one, mul_inv_of_mem_specialUnitary hT]
      _ = ComplexMatrix2.operatorNorm (plaquetteHolonomy W p ^ ε - 1) :=
          hN.2.1 _ _ (mem_unitaryGroup_of_mem_specialUnitary hT)
      _ ≤ ϖ := by
          rcases hε with rfl | rfl
          · rw [zpow_one]
            exact hP p hin
          · rw [zpow_neg_one, hN.2.2.1 _ (mem_unitaryGroup_of_mem_specialUnitary hPu)]
            exact hP p hin
theorem move_step_back_bound {z : SiteAtLevel L m K n} {ϖ : ℝ}
    (hex : ∀ e : AdjacentSwap L m (levelDepth K n), StaysWithin Y z e.original →
      StaysWithin Y z e.swapped →
      ComplexMatrix2.operatorNorm (wordHolonomy W z e.original - wordHolonomy W z e.swapped) ≤ ϖ)
    (s : UnitStepVec L m (levelDepth K n)) (B : StepWord L m (levelDepth K n)) :
    ∀ u v : StepWord L m (levelDepth K n), StaysWithin Y z (u ++ (B ++ s :: v)) →
      StaysWithin Y z (u ++ s :: (B ++ v)) →
      ComplexMatrix2.operatorNorm (wordHolonomy W z (u ++ (B ++ s :: v)) -
        wordHolonomy W z (u ++ s :: (B ++ v))) ≤ B.length * ϖ := by
  induction B with
  | nil =>
    intro u v _ _
    simp
  | cons r B ih =>
    intro u v h1 h2
    have e1 : u ++ (r :: B ++ s :: v) = (u ++ [r]) ++ (B ++ s :: v) := by simp
    have e2 : u ++ r :: s :: (B ++ v) = (u ++ [r]) ++ s :: (B ++ v) := by simp
    have hM : StaysWithin Y z (u ++ r :: s :: (B ++ v)) := by
      obtain ⟨hu, a1, a2⟩ := staysWithin_append.mp h1
      obtain ⟨-, b1, b2, b3⟩ := staysWithin_append.mp h2
      refine staysWithin_append.mpr ⟨hu, a1, a2.start_mem, ?_⟩
      rwa [add_right_comm]
    have k1 := ih (u ++ [r]) v (by rw [← e1]; exact h1) (by rw [← e2]; exact hM)
    have k2 := hex ⟨u, r, s, B ++ v⟩ hM h2
    have k3 : ComplexMatrix2.operatorNorm (wordHolonomy W z (u ++ r :: s :: (B ++ v)) -
        wordHolonomy W z (u ++ s :: r :: (B ++ v))) ≤ ϖ := k2
    rw [← e1, ← e2] at k1
    have k4 := norm_sub_le_norm_sub_add_norm_sub
      (wordHolonomy W z (u ++ (r :: B ++ s :: v)))
      (wordHolonomy W z (u ++ r :: s :: (B ++ v)))
      (wordHolonomy W z (u ++ s :: r :: (B ++ v)))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    simp only [List.cons_append] at k1 k4 ⊢
    linarith
theorem wordHolonomy_cancel (hW : IsGaugeFieldWithin Y W) (ν : Fin 4)
    (u B : StepWord L m (levelDepth K n)) (z : SiteAtLevel L m K n)
    (h : StaysWithin Y z (u ++ negUnit ν :: posUnit ν :: B)) :
    wordHolonomy W z (u ++ negUnit ν :: posUnit ν :: B) = wordHolonomy W z (u ++ B) := by
  obtain ⟨-, h1, h2, -⟩ := staysWithin_append.mp h
  obtain ⟨c, hc⟩ : ∃ c, c = z + wordSum u := ⟨_, rfl⟩
  rw [← hc] at h1 h2
  have hb : (bondOfStep c (negUnit ν)).LiesIn Y := ⟨h1, h2⟩
  have e1 : c + ((negUnit ν : UnitStepVec L m (levelDepth K n)) : SiteAtLevel L m K n) +
      ((posUnit ν : UnitStepVec L m (levelDepth K n)) : SiteAtLevel L m K n) = c := by
    simp [negUnit, posUnit]
  have e2 : bondOfStep (c + ((negUnit ν : UnitStepVec L m (levelDepth K n)) :
      SiteAtLevel L m K n)) (posUnit ν) = (bondOfStep c (negUnit ν)).opposite := Bond.ext rfl e1
  have e3 : W (bondOfStep c (negUnit ν)) * W (bondOfStep c (negUnit ν)).opposite = 1 := by
    rw [hW.2 _ hb]
    exact mul_inv_of_mem_specialUnitary (hW.1 _ hb)
  simp only [wordHolonomy, pathOfWord_append, pathHolonomy_append, pathOfWord, ← hc, e1, e2]
  simp only [pathHolonomy, List.map_cons, List.prod_cons]
  rw [← mul_assoc (W _), e3, one_mul]
theorem wordHolonomy_wordAlong_succ (hW : IsGaugeFieldWithin Y W) (ν : Fin 4)
    (u B : StepWord L m (levelDepth K n)) (z : SiteAtLevel L m K n) (a : ℤ)
    (h : StaysWithin Y z (u ++ (wordAlong ν a ++ posUnit ν :: B))) :
    wordHolonomy W z (u ++ (wordAlong ν a ++ posUnit ν :: B)) =
      wordHolonomy W z (u ++ (wordAlong ν (a + 1) ++ B)) := by
  by_cases ha : 0 ≤ a
  · have e : (wordAlong ν a ++ posUnit ν :: B : StepWord L m (levelDepth K n)) =
        wordAlong ν (a + 1) ++ B := by
      simp only [wordAlong, if_pos ha, if_pos (by omega : 0 ≤ a + 1)]
      have h1 : (a + 1).toNat = a.toNat + 1 := by omega
      rw [h1, List.replicate_succ']
      simp
    rw [e]
  · have e1 : (wordAlong ν a : StepWord L m (levelDepth K n)) =
        wordAlong ν (a + 1) ++ [negUnit ν] := by
      have h2 : (wordAlong ν (a + 1) : StepWord L m (levelDepth K n)) =
          List.replicate (-a - 1).toNat (negUnit ν) := by
        by_cases h3 : a = -1
        · subst h3
          rfl
        · simp only [wordAlong, if_neg (by omega : ¬ 0 ≤ a + 1)]
          congr 1
          omega
      rw [h2, ← List.replicate_succ']
      simp only [wordAlong, if_neg ha]
      congr 1
      omega
    rw [e1] at h ⊢
    have e2 : u ++ ((wordAlong ν (a + 1) ++ [negUnit ν]) ++ posUnit ν :: B) =
        (u ++ wordAlong ν (a + 1)) ++ negUnit ν :: posUnit ν :: B := by simp
    have e3 : u ++ (wordAlong ν (a + 1) ++ B) = (u ++ wordAlong ν (a + 1)) ++ B := by simp
    rw [e2] at h ⊢
    rw [e3]
    exact wordHolonomy_cancel hW ν _ B z h
theorem split_axes (ν : Fin 4) :
    ∃ l₁ l₂ : List (Fin 4), [3, 2, 1, 0] = l₁ ++ ν :: l₂ ∧ l₂.toFinset = Finset.Iio ν := by
  fin_cases ν
  · exact ⟨[3, 2, 1], [], rfl, by decide⟩
  · exact ⟨[3, 2], [0], rfl, by decide⟩
  · exact ⟨[3], [1, 0], rfl, by decide⟩
  · exact ⟨[], [2, 1, 0], rfl, by decide⟩
theorem coordinateComb_eq (y x : SiteAtLevel L m K n) :
    coordinateComb y x = pathOfWord y (wordThrough (chartOffset y x) [3, 2, 1, 0]) :=
  stepsThroughAxes_eq _ _ _
theorem add_wordSum_comb {y x : SiteAtLevel L m K n} {D : Fin 4 → ℤ} (h : IsChartOffset y x D) :
    y + wordSum (wordThrough D [3, 2, 1, 0] : StepWord L m (levelDepth K n)) = x := by
  have h1 := shiftBy_coordsAfter y D [3, 2, 1, 0] 0
  rw [shiftBy_zero] at h1
  rw [← h1]
  have h2 : coordsAfter D [3, 2, 1, 0] 0 = D := by
    funext ν
    rw [coordsAfter_apply _ (by decide)]
    have h3 : ν ∈ ([3, 2, 1, 0] : List (Fin 4)) := by fin_cases ν <;> decide
    simp [h3]
  rw [h2]
  exact shiftBy_of_isChartOffset h
variable {y : SiteAtLevel L m K n} {I : Fin 4 → Set ℤ}
theorem staysWithin_comb (w : BoxWindow Y y I)
    (hcd : ∀ x ∈ Y, IsChartOffset y x (chartOffset y x) ∧
      ∀ μ, chartOffset y x μ ∈ I μ) {x : SiteAtLevel L m K n} (hx : x ∈ Y) :
    StaysWithin Y y (wordThrough (chartOffset y x) [3, 2, 1, 0]) := by
  have h := staysWithin_wordThrough w (chartOffset y x) [3, 2, 1, 0] 0 (by decide) w.zero_mem
    (fun ν _ => by simpa using (hcd x hx).2 ν)
  rwa [shiftBy_zero] at h
theorem combTransport_bond_bound (hR : PathRearrangementBound)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) (hodd : Odd L) (h13 : 13 ≤ L)
    (hm : 0 < m) (hj : -(m : ℤ) ≤ levelDepth K n) (w : BoxWindow Y y I)
    (hcd : ∀ x ∈ Y, IsChartOffset y x (chartOffset y x) ∧
      ∀ μ, chartOffset y x μ ∈ I μ)
    (hW : IsGaugeFieldWithin Y W) {ϖ : ℝ} (hϖ : 0 ≤ ϖ)
    (hP : ∀ p : PlaquetteAtLevel L m K n, p.LiesIn Y →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) ≤ ϖ)
    {x : SiteAtLevel L m K n} (ν : Fin 4) (hx : x ∈ Y)
    (hx' : x + unitStep L m (levelDepth K n) ν ∈ Y) :
    ComplexMatrix2.operatorNorm
        (gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) - 1) ≤
      ϖ * offsetNormBefore y x ν := by
  have hL : 0 < L := by omega
  obtain ⟨l₁, l₂, hl, hset⟩ := split_axes ν
  obtain ⟨D, hD⟩ : ∃ D, D = chartOffset y x := ⟨_, rfl⟩
  obtain ⟨hDc, hDI⟩ := hcd x hx
  rw [← hD] at hDc hDI
  obtain ⟨hEc, hEI⟩ := hcd _ hx'
  have hDE : chartOffset y (x + unitStep L m (levelDepth K n) ν) = D + Pi.single ν 1 :=
    chartOffset_add_unitStep hL hj w ν hDc hDI hEc hEI
  rw [hDE] at hEI
  have nd : (l₁ ++ ν :: l₂).Nodup := by
    rw [← hl]
    decide
  have nd₂' := List.nodup_cons.mp nd.of_append_right
  have nd₂ := nd₂'.2
  have disj := List.disjoint_of_nodup_append nd
  have hν₁ : ν ∉ l₁ := fun h => disj h (List.mem_cons_self ..)
  have hs : (D + Pi.single ν 1 : Fin 4 → ℤ) ν = D ν + 1 := by simp
  have hoff : ∀ μ, μ ≠ ν → (D + Pi.single ν 1 : Fin 4 → ℤ) μ = D μ := by
    intro μ h
    simp [Pi.single_eq_of_ne h]
  obtain ⟨A, hA⟩ : ∃ A : StepWord L m (levelDepth K n),
      A = wordThrough D l₁ ++ wordAlong ν (D ν) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : StepWord L m (levelDepth K n), B = wordThrough D l₂ := ⟨_, rfl⟩
  have hC : (wordThrough D [3, 2, 1, 0] : StepWord L m (levelDepth K n)) = A ++ B := by
    rw [hl, wordThrough_append, hA, hB]
    simp [wordThrough]
  have hC' : (wordThrough (D + Pi.single ν 1) [3, 2, 1, 0] : StepWord L m (levelDepth K n)) =
      wordThrough D l₁ ++ (wordAlong ν (D ν + 1) ++ B) := by
    rw [hl, wordThrough_append,
      wordThrough_congr (n' := D) (l := l₁) fun μ hμ => hoff μ fun e => hν₁ (e ▸ hμ)]
    simp only [wordThrough]
    rw [wordThrough_congr (n' := D) (l := l₂) fun μ hμ => hoff μ fun e => nd₂'.1 (e ▸ hμ), hs,
      hB]
  have hA' : A = wordThrough D (l₁ ++ [ν]) := by
    rw [hA, wordThrough_append]
    simp [wordThrough]
  have W0 : StaysWithin Y y (A ++ B) := by
    rw [← hC, hD]
    exact staysWithin_comb w hcd hx
  have hsum : y + wordSum (A ++ B) = x := by
    rw [← hC]
    exact add_wordSum_comb hDc
  have W1 : StaysWithin Y y (A ++ (B ++ posUnit ν :: [])) := by
    rw [← List.append_assoc]
    refine staysWithin_append.mpr ⟨W0, ?_⟩
    rw [hsum]
    exact ⟨hx, hx'⟩
  have nd' : (l₁ ++ [ν]).Nodup :=
    List.Nodup.sublist (List.Sublist.append_left (List.singleton_sublist.mpr
      (List.mem_cons_self ..)) l₁) nd
  obtain ⟨tA, htA⟩ : ∃ tA, tA = coordsAfter D (l₁ ++ [ν]) 0 := ⟨_, rfl⟩
  have htv : ∀ μ, tA μ = if μ ∈ l₁ ++ [ν] then D μ else 0 := by
    intro μ
    rw [htA, coordsAfter_apply _ nd']
    simp
  have hcA : y + wordSum A = shiftBy y tA := by
    have h := shiftBy_coordsAfter y D (l₁ ++ [ν]) 0
    rw [shiftBy_zero, ← hA', ← htA] at h
    exact h.symm
  have htI : ∀ μ, tA μ ∈ I μ := by
    intro μ
    rw [htv]
    split_ifs
    · exact hDI μ
    · exact w.zero_mem μ
  have WA : StaysWithin Y y A := by
    have h := staysWithin_wordThrough w D (l₁ ++ [ν]) 0 nd' w.zero_mem
      (fun μ _ => by simpa using hDI μ)
    rwa [shiftBy_zero, ← hA'] at h
  have hν : tA ν = D ν := by
    rw [htv, if_pos (by simp)]
  have ht₂ : ∀ μ, (tA + Pi.single ν 1 : Fin 4 → ℤ) μ ∈ I μ := by
    intro μ
    by_cases h : μ = ν
    · subst h
      have := hEI μ
      rw [hs] at this
      simpa [hν] using this
    · simpa [Pi.single_eq_of_ne h] using htI μ
  have WB : StaysWithin Y (shiftBy y (tA + Pi.single ν 1)) B := by
    rw [hB]
    refine staysWithin_wordThrough w D l₂ _ nd₂ ht₂ fun μ hμ => ?_
    have h1 : μ ≠ ν := fun e => nd₂'.1 (e ▸ hμ)
    have h2 : μ ∉ l₁ ++ [ν] := by
      intro h3
      rcases List.mem_append.mp h3 with h3 | h3
      · exact disj h3 (List.mem_cons_of_mem _ hμ)
      · exact h1 (by simpa using h3)
    have h3 : (tA + Pi.single ν 1 : Fin 4 → ℤ) μ = 0 := by
      simp only [Pi.add_apply, Pi.single_eq_of_ne h1, add_zero]
      rw [htv, if_neg h2]
    rw [h3, zero_add]
    exact hDI μ
  have W2 : StaysWithin Y y (A ++ posUnit ν :: B) := by
    refine staysWithin_append.mpr ⟨WA, ?_⟩
    rw [hcA]
    refine ⟨w.shiftBy_mem _ htI, ?_⟩
    have h : shiftBy y tA + ((posUnit ν : UnitStepVec L m (levelDepth K n)) :
        SiteAtLevel L m K n) = shiftBy y (tA + Pi.single ν 1) := by
      rw [shiftBy_add_single, one_smul]
      rfl
    rw [h]
    exact WB
  have hcar := move_step_back_bound
    (swap_holonomy_bound hR hN hodd h13 hm hj hW hϖ hP y) (posUnit ν) B A [] W1
    (by simpa using W2)
  rw [List.append_nil] at hcar
  have H1 : wordHolonomy W y (A ++ (B ++ posUnit ν :: [])) =
      pathHolonomy W (coordinateComb y x ++ [Bond.forwardFrom x ν]) := by
    rw [coordinateComb_eq, ← hD, hC, ← List.append_assoc, wordHolonomy,
      pathOfWord_append y (A ++ B), hsum]
    rfl
  have e3 : A ++ posUnit ν :: B =
      wordThrough D l₁ ++ (wordAlong ν (D ν) ++ posUnit ν :: B) := by
    rw [hA]
    simp
  have H2 : wordHolonomy W y (A ++ posUnit ν :: B) =
      pathHolonomy W (coordinateComb y (x + unitStep L m (levelDepth K n) ν)) := by
    rw [coordinateComb_eq, hDE, hC', e3]
    exact wordHolonomy_wordAlong_succ hW ν _ B y (D ν) (e3 ▸ W2)
  have hu1 : pathHolonomy W (coordinateComb y x ++ [Bond.forwardFrom x ν]) ∈
      ComplexMatrix2.specialUnitary := by
    rw [← H1]
    exact pathHolonomy_mem hW (liesIn_of_staysWithin W1)
  have hu2 : pathHolonomy W (coordinateComb y (x + unitStep L m (levelDepth K n) ν)) ∈
      ComplexMatrix2.specialUnitary := by
    rw [← H2]
    exact pathHolonomy_mem hW (liesIn_of_staysWithin W2)
  have e : gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) =
      pathHolonomy W (coordinateComb y x ++ [Bond.forwardFrom x ν]) *
        (pathHolonomy W (coordinateComb y (x + unitStep L m (levelDepth K n) ν)))⁻¹ := by
    show pathHolonomy W (coordinateComb y x) * W (Bond.forwardFrom x ν) *
      (pathHolonomy W (coordinateComb y (x + unitStep L m (levelDepth K n) ν)))⁻¹ = _
    rw [pathHolonomy_append]
    simp [pathHolonomy]
  rw [e, hN.2.2.2.1 _ _ (mem_unitaryGroup_of_mem_specialUnitary hu1)
    (mem_unitaryGroup_of_mem_specialUnitary hu2), ← H1, ← H2]
  refine hcar.trans (le_of_eq ?_)
  have hlen : (B.length : ℝ) = offsetNormBefore y x ν := by
    rw [hB, length_wordThrough, offsetNormBefore, ← hD, ← hset, List.sum_toFinset _ nd₂]
  rw [hlen, mul_comm]
end Level
end CombGaugeOnBox
open CombGaugeOnBox in
theorem CombGaugeOnBox.holds (hR : PathRearrangementBound)
    (hA : ComplexMatrix2.SpecialUnitaryAngleBounds)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hG : GaugeCovarianceOfHolonomy)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) : CombTransportOnBox.Statement := by
  classical
  intro L hLs m K n hm hn Y s y W ϖ hY hcount hy hW hϖ hP
  obtain ⟨hodd, h13⟩ := hLs
  have hL : 0 < L := by omega
  have hj : -(m : ℤ) ≤ levelDepth K n := by
    simp only [levelDepth]
    omega
  obtain ⟨I, hord, hzero, hshort, hgood, hcd⟩ := exists_intervals hL hj hY hy
  have w : BoxWindow Y y I := ⟨hord, hzero, hshort, hgood⟩
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have habs : ∀ x ∈ Y, ∀ μ, ((|chartOffset y x μ| : ℤ) : ℝ) ≤ s := by
    intro x hx μ
    have := abs_le_of_coordCount_le hL w (hcount μ) ((hcd x hx).2 μ)
    exact_mod_cast this
  have hcombSU : ∀ x ∈ Y, combTransport W y x ∈ ComplexMatrix2.specialUnitary := by
    intro x hx
    unfold combTransport
    rw [coordinateComb_eq]
    exact pathHolonomy_mem hW (liesIn_of_staysWithin (staysWithin_comb w hcd hx))
  have hF : ∀ (x : SiteAtLevel L m K n) (ν : Fin 4), (Bond.forwardFrom x ν).LiesIn Y →
      ComplexMatrix2.operatorNorm
          (gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) - 1) ≤
        ϖ * offsetNormBefore y x ν :=
    fun x ν hb => combTransport_bond_bound hR hN hodd h13 hm hj w hcd hW hϖ hP ν hb.1 hb.2
  have hnn : ∀ (x : SiteAtLevel L m K n) (μ : Fin 4),
      (0 : ℝ) ≤ ((|chartOffset y x μ| : ℤ) : ℝ) := fun x μ => by
    exact_mod_cast abs_nonneg _
  have hS : ∀ x ∈ Y, ∀ ν : Fin 4,
      offsetNormBefore y x ν ≤ min (3 * (s : ℝ)) (offsetL1Norm y x) := by
    intro x hx ν
    refine le_min ?_ ?_
    · have h1 := Finset.sum_le_card_nsmul (Finset.Iio ν)
        (fun μ => ((|chartOffset y x μ| : ℤ) : ℝ)) (s : ℝ) fun μ _ => habs x hx μ
      have h2 : (((Finset.Iio ν).card : ℕ) : ℝ) ≤ 3 := by
        rw [Fin.card_Iio]
        have := ν.isLt
        exact_mod_cast (by omega : (ν : ℕ) ≤ 3)
      rw [nsmul_eq_mul] at h1
      calc offsetNormBefore y x ν ≤ ((Finset.Iio ν).card : ℝ) * s := h1
        _ ≤ 3 * s := mul_le_mul_of_nonneg_right h2 hs0
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun μ _ _ => hnn x μ
  have hF3 : ∀ (x : SiteAtLevel L m K n) (ν : Fin 4), (Bond.forwardFrom x ν).LiesIn Y →
      ComplexMatrix2.operatorNorm
          (gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) - 1) ≤
        3 * (s : ℝ) * ϖ := by
    intro x ν hb
    refine (hF x ν hb).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ((hS x hb.1 ν).trans (min_le_left _ _)) hϖ
  obtain ⟨u, hudef⟩ : ∃ u : SiteAtLevel L m K n → ComplexMatrix2,
      u = fun x => if x ∈ Y then combTransport W y x else 1 := ⟨_, rfl⟩
  have hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary := by
    intro x
    rw [hudef]
    by_cases hx : x ∈ Y
    · simpa [hx] using hcombSU x hx
    · simp [hx]
  have huC : IsGaugeMap complexGaugeGroup u :=
    fun x => (Matrix.mem_specialUnitaryGroup_iff.mp (hu x)).2
  have hWC : IsGaugeField complexGaugeGroup (bondsWithin Y).bonds W :=
    ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.mp (hW.1 b hb)).2, hW.2⟩
  obtain ⟨⟨-, hRe, -⟩, hHol, -⟩ := hG L m hodd h13 hm _ hj (bondsWithin Y).bonds W u u
    (bondsWithin Y).opposite_mem hWC huC huC
  have hWu : IsGaugeField compactGaugeGroup (bondsWithin Y).bonds (gaugeTransform u W) :=
    hRe hW hu
  have hagree : ∀ b ∈ (bondsWithin Y).bonds,
      gaugeTransform (combTransport W y) W b = gaugeTransform u W b := by
    intro b hb
    have h1 : b.source ∈ Y := hb.1
    have h2 : b.target ∈ Y := hb.2
    simp only [gaugeTransform, hudef, if_pos h1, if_pos h2]
  have hpos : ∀ b ∈ (bondsWithin Y).bonds, b.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (gaugeTransform u W b - 1) ≤ 3 * (s : ℝ) * ϖ := by
    intro b hb hp
    obtain ⟨μ, hμ⟩ := hp
    obtain ⟨x, rfl⟩ : ∃ x, b = Bond.forwardFrom x μ :=
      ⟨b.source, Bond.ext rfl (by
        show b.target = b.source + unitStep L m (levelDepth K n) μ
        rw [← hμ]
        abel)⟩
    rw [← hagree _ hb]
    exact hF3 _ _ hb
  have hrev : ∀ b ∈ (bondsWithin Y).bonds,
      gaugeTransform u W b = (gaugeTransform u W b.opposite)⁻¹ :=
    fun b hb => hWu.2 b.opposite ((bondsWithin Y).opposite_mem b hb)
  have hB3 : ∀ b ∈ (bondsWithin Y).bonds,
      ComplexMatrix2.operatorNorm (gaugeTransform u W b - 1) ≤ 3 * (s : ℝ) * ϖ := by
    intro b hb
    by_cases hp : b.IsPositivelyOriented
    · exact hpos b hb hp
    · have hb' := (bondsWithin Y).opposite_mem b hb
      rw [hrev b hb, hN.2.2.1 _ (mem_unitaryGroup_of_mem_specialUnitary (hWu.1 _ hb'))]
      exact hpos _ hb' (Bond.opposite_isPositivelyOriented hp)
  refine ⟨?_, fun x ν hb => ⟨hF x ν hb, ?_⟩, fun h2 => ?_, ?_⟩
  · have hy0 : chartOffset y y = 0 := by
      refine chartOffset_eq hL ⟨by simp, fun μ => ?_⟩
      have := torusSide_pos (m := m) hL
      simp only [Pi.zero_apply, abs_zero, Int.cast_zero, zero_mul]
      linarith
    simp only [combTransport, coordinateComb, hy0]
    simp [stepsThroughAxes, flowAlong, forwardAxisPath, pathHolonomy]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hS x hb.1 ν) hϖ
  · have hdom : ∀ b ∈ (bondsWithin Y).bonds,
        gaugeTransform u W b ∈ ComplexMatrix2.unitaryLogDomain := by
      intro b hb
      refine ⟨hWu.1 b hb, fun hneg => ?_⟩
      have h3 := hB3 b hb
      rw [Set.mem_singleton_iff.mp hneg] at h3
      have h4 : ComplexMatrix2.operatorNorm ((-1 : ComplexMatrix2) - 1) = 2 := by
        have h5 : ((-1 : ComplexMatrix2) - 1) = (-2 : ℂ) • (1 : ComplexMatrix2) := by
          rw [neg_smul, two_smul]
          abel
        rw [h5, ComplexMatrix2.operatorNorm, norm_smul, norm_one]
        simp
      linarith
    have hlog := hI.2.2.2.2.1
    let a : LieBondFieldWithin Y := fun b =>
      ⟨ComplexMatrix2.unitaryLieLog (gaugeTransform u W b.1), (hlog _ (hdom b.1 b.2.1)).1.2⟩
    have hval : ∀ b (h : b ∈ (bondsWithin Y).bonds ∧ b.IsPositivelyOriented),
        (a.eval b : ComplexMatrix2) = ComplexMatrix2.unitaryLieLog (gaugeTransform u W b) := by
      intro b h
      have := LieBondField.eval_of_positive a ⟨b, h⟩
      exact congrArg Subtype.val this
    refine ⟨a, fun b => (hlog _ (hdom b.1 b.2.1)).1, fun b hb => ?_, ?_⟩
    · rw [hagree b hb]
      by_cases hp : b.IsPositivelyOriented
      · rw [hval b ⟨hb, hp⟩]
        exact (hlog _ (hdom b hb)).2.2.1.symm
      · have h' := Bond.opposite_isPositivelyOriented hp
        have hb' := (bondsWithin Y).opposite_mem b hb
        have hv : a.eval b = -a ⟨b.opposite, hb', h'⟩ := by
          simp only [LieBondField.eval]
          rw [dif_neg (fun x => hp x.2),
            dif_pos (⟨hb', h'⟩ : b.opposite ∈ (bondsWithin Y).bonds ∧ _)]
        have hv' : (a.eval b : ComplexMatrix2) =
            -ComplexMatrix2.unitaryLieLog (gaugeTransform u W b.opposite) :=
          congrArg Subtype.val hv
        have hE := (hlog _ (hdom _ hb')).2.2.1
        have h6 : ComplexMatrix2.matExp
              (-(Complex.I • ComplexMatrix2.unitaryLieLog (gaugeTransform u W b.opposite))) =
            (ComplexMatrix2.matExp
              (Complex.I • ComplexMatrix2.unitaryLieLog (gaugeTransform u W b.opposite)))⁻¹ :=
          Matrix.exp_neg _
        rw [hv', smul_neg, hrev b hb, h6, hE]
    · refine Real.iSup_le (fun b => ?_) (by positivity)
      have hb := b.2.1
      have h1 := (hA.2.2.2.1 _ (hdom b.1 hb)).1
      have h3 := (hA.2.1 _ (hWu.1 b.1 hb)).2.2.2.2.1
      have h4 := hB3 b.1 hb
      show ComplexMatrix2.operatorNorm (ComplexMatrix2.unitaryLieLog (gaugeTransform u W b.1)) ≤ _
      rw [h1]
      have hπ := Real.pi_pos
      have h5 : ComplexMatrix2.rotationAngle (gaugeTransform u W b.1) =
          Real.pi / 2 * (2 / Real.pi * ComplexMatrix2.rotationAngle (gaugeTransform u W b.1)) := by
        field_simp
      rw [h5]
      calc Real.pi / 2 * (2 / Real.pi * ComplexMatrix2.rotationAngle (gaugeTransform u W b.1))
          ≤ Real.pi / 2 * (3 * (s : ℝ) * ϖ) :=
            mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
        _ = _ := by ring
  · intro Γ₁ Γ₂ z z' h1 h2 hb1 hb2
    have hb : ∀ Γ : List (BondAtLevel L m K n), (∀ b ∈ Γ, b.LiesIn Y) →
        ComplexMatrix2.operatorNorm (pathHolonomy (gaugeTransform u W) Γ - 1) ≤
          3 * (s : ℝ) * ϖ * (Γ.length : ℝ) := by
      intro Γ
      induction Γ with
      | nil =>
        intro _
        simp [pathHolonomy]
      | cons b Γ ih =>
        intro h
        have hbm := h b (List.mem_cons_self ..)
        have k1 := ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
        have k2 := hB3 b hbm
        have k3 : pathHolonomy (gaugeTransform u W) (b :: Γ) - 1 =
            gaugeTransform u W b * (pathHolonomy (gaugeTransform u W) Γ - 1) * 1 +
              (gaugeTransform u W b - 1) := by
          simp only [pathHolonomy, List.map_cons, List.prod_cons]
          rw [mul_one, mul_sub, mul_one]
          abel
        have k4 : ComplexMatrix2.operatorNorm
              (gaugeTransform u W b * (pathHolonomy (gaugeTransform u W) Γ - 1) * 1) =
            ComplexMatrix2.operatorNorm (pathHolonomy (gaugeTransform u W) Γ - 1) :=
          hN.1 _ _ _ (mem_unitaryGroup_of_mem_specialUnitary (hWu.1 b hbm)) (one_mem _)
        rw [k3]
        refine (norm_add_le _ _).trans ?_
        have k5 : ‖gaugeTransform u W b * (pathHolonomy (gaugeTransform u W) Γ - 1) * 1‖ =
            ‖pathHolonomy (gaugeTransform u W) Γ - 1‖ := k4
        rw [k5]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        have k6 : ‖pathHolonomy (gaugeTransform u W) Γ - 1‖ ≤
            3 * (s : ℝ) * ϖ * (Γ.length : ℝ) := k1
        have k7 : ‖gaugeTransform u W b - 1‖ ≤ 3 * (s : ℝ) * ϖ := k2
        linarith
    have e1 := hHol Γ₁ z z' h1 hb1
    have e2 := hHol Γ₂ z z' h2 hb2
    have k1 := hb Γ₁ hb1
    have k2 := hb Γ₂ hb2
    have k3 : ComplexMatrix2.operatorNorm (pathHolonomy W Γ₁ - pathHolonomy W Γ₂) =
        ComplexMatrix2.operatorNorm
          (pathHolonomy (gaugeTransform u W) Γ₁ - pathHolonomy (gaugeTransform u W) Γ₂) := by
      rw [e1, e2, ← sub_mul, ← mul_sub]
      exact (hN.1 _ _ _ (mem_unitaryGroup_of_mem_specialUnitary (hu z))
        (inv_mem_unitaryGroup_of_mem_specialUnitary (hu z'))).symm
    rw [k3]
    have k4 := norm_sub_le_norm_sub_add_norm_sub (pathHolonomy (gaugeTransform u W) Γ₁) 1
      (pathHolonomy (gaugeTransform u W) Γ₂)
    rw [norm_sub_rev 1] at k4
    have k5 : ‖pathHolonomy (gaugeTransform u W) Γ₁ - 1‖ ≤
        3 * (s : ℝ) * ϖ * (Γ₁.length : ℝ) := k1
    have k6 : ‖pathHolonomy (gaugeTransform u W) Γ₂ - 1‖ ≤
        3 * (s : ℝ) * ϖ * (Γ₂.length : ℝ) := k2
    exact show ‖pathHolonomy (gaugeTransform u W) Γ₁ - pathHolonomy (gaugeTransform u W) Γ₂‖ ≤
        3 * (s : ℝ) * ϖ * ((Γ₁.length : ℝ) + Γ₂.length) from by
      rw [mul_add]
      linarith
end PeriodicLattice
end YangMills.Construction
