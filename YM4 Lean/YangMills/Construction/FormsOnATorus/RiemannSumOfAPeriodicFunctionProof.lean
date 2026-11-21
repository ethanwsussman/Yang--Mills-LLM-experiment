import YangMills.Construction.FormsOnATorus.RiemannSumOfAPeriodicFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace YangMills.Construction.RiemannSums
section Periodicity
variable {F : (Fin 4 → ℝ) → ℂ}
private theorem periodic_int_mul_single (hper : ∀ (i : Fin 4) (p : Fin 4 → ℝ), F (p + Pi.single i (2 * Real.pi)) = F p)
    (i : Fin 4) (w : ℤ) (p : Fin 4 → ℝ) : F (p + Pi.single i (2 * Real.pi * (w : ℝ))) = F p := by
  have hp : Function.Periodic (fun t : ℝ => F (p + Pi.single i t)) (2 * Real.pi) := by
    intro t
    have e : p + Pi.single i (t + 2 * Real.pi) = (p + Pi.single i t) + Pi.single i (2 * Real.pi) := by
      rw [Pi.single_add, add_assoc]
    show F (p + Pi.single i (t + 2 * Real.pi)) = F (p + Pi.single i t)
    rw [e, hper]
  have h := hp.int_mul w 0
  simp only [zero_add] at h
  have e2 : (w : ℝ) * (2 * Real.pi) = 2 * Real.pi * (w : ℝ) := by ring
  simpa [e2] using h
private theorem periodic_int_vector (hper : ∀ (i : Fin 4) (p : Fin 4 → ℝ), F (p + Pi.single i (2 * Real.pi)) = F p)
    (w : Fin 4 → ℤ) (p : Fin 4 → ℝ) : F (p + fun i => 2 * Real.pi * (w i : ℝ)) = F p := by
  classical
  have key : ∀ s : Finset (Fin 4), F (p + fun i => if i ∈ s then 2 * Real.pi * (w i : ℝ) else 0) = F p := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (p + fun i : Fin 4 => if i ∈ (∅ : Finset (Fin 4)) then 2 * Real.pi * (w i : ℝ) else 0) = p := by
        funext i; simp
      rw [e]
    | insert a s ha ih =>
      have e : (p + fun i => if i ∈ insert a s then 2 * Real.pi * (w i : ℝ) else 0) =
          (p + fun i => if i ∈ s then 2 * Real.pi * (w i : ℝ) else 0) + Pi.single a (2 * Real.pi * (w a : ℝ)) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [ha]
        · simp [hi, Finset.mem_insert]
      rw [e, periodic_int_mul_single hper, ih]
  simpa using key Finset.univ
end Periodicity
private def floorCell (N : ℕ) (t : ℝ) : ℤ := ⌊(t + Real.pi) * (N : ℝ) / (2 * Real.pi)⌋
private def cellLeft (N : ℕ) (k : ℤ) : ℝ := -Real.pi + 2 * Real.pi * (k : ℝ) / (N : ℝ)
private theorem floorCell_eq_iff {N : ℕ} (hN : 0 < N) (t : ℝ) (k : ℤ) :
    floorCell N t = k ↔ t ∈ Ico (cellLeft N k) (cellLeft N (k + 1)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold floorCell cellLeft
  rw [Int.floor_eq_iff, mem_Ico]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_lt_iff₀ (by positivity)] at h2
    constructor
    · have : 2 * Real.pi * (k : ℝ) / (N : ℝ) ≤ t + Real.pi := by
        rw [div_le_iff₀ hN']; nlinarith
      linarith
    · have : t + Real.pi < 2 * Real.pi * ((k : ℝ) + 1) / (N : ℝ) := by
        rw [lt_div_iff₀ hN']; nlinarith
      linarith
  · rintro ⟨h1, h2⟩
    have h1' : 2 * Real.pi * (k : ℝ) / (N : ℝ) ≤ t + Real.pi := by linarith
    have h2' : t + Real.pi < 2 * Real.pi * ((k : ℝ) + 1) / (N : ℝ) := by linarith
    rw [div_le_iff₀ hN'] at h1'
    rw [lt_div_iff₀ hN'] at h2'
    constructor
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
private theorem abs_cellLeft_sub_le {N : ℕ} (hN : 0 < N) (t : ℝ) :
    |cellLeft N (floorCell N t) - t| ≤ 2 * Real.pi / (N : ℝ) := by
  have h := (floorCell_eq_iff hN t (floorCell N t)).1 rfl
  have e : cellLeft N (floorCell N t + 1) = cellLeft N (floorCell N t) + 2 * Real.pi / (N : ℝ) := by
    unfold cellLeft; push_cast; field_simp; ring
  rw [e] at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]
private theorem floorCell_bounds {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Ico (-Real.pi) Real.pi) :
    0 ≤ floorCell N t ∧ floorCell N t < N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold floorCell
  constructor
  · apply Int.floor_nonneg.2
    have : 0 ≤ t + Real.pi := by linarith [ht.1]
    positivity
  · rw [Int.floor_lt]
    push_cast
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [ht.2]
private theorem mem_Ico_of_floorCell {N : ℕ} (hN : 0 < N) {t : ℝ} (h0 : 0 ≤ floorCell N t) (h1 : floorCell N t < N) :
    t ∈ Ico (-Real.pi) Real.pi := by
  have hpi := Real.pi_pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (floorCell_eq_iff hN t (floorCell N t)).1 rfl
  have h1' : (floorCell N t : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1
  constructor
  · have : 0 ≤ 2 * Real.pi * (floorCell N t : ℝ) / (N : ℝ) := by positivity
    have := h.1
    unfold cellLeft at this
    linarith
  · have h2 := h.2
    unfold cellLeft at h2
    push_cast at h2
    have : 2 * Real.pi * ((floorCell N t : ℝ) + 1) / (N : ℝ) ≤ 2 * Real.pi := by
      rw [div_le_iff₀ hN']; nlinarith
    linarith
private def siteCell (n : ℕ) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) : Fin 4 → ℤ :=
  fun i => (((j i + (n : ZMod (2 * n))).val : ℕ) : ℤ)
private theorem siteCell_bounds (n : ℕ) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) (i : Fin 4) :
    0 ≤ siteCell n j i ∧ siteCell n j i < ((2 * n : ℕ) : ℤ) := by
  unfold siteCell
  exact ⟨by positivity, by exact_mod_cast ZMod.val_lt _⟩
private theorem intCast_siteCell (n : ℕ) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) (i : Fin 4) :
    ((siteCell n j i : ℤ) : ZMod (2 * n)) = j i + (n : ZMod (2 * n)) := by
  unfold siteCell
  simp
private theorem siteCell_injective (n : ℕ) [NeZero (2 * n)] : Function.Injective (siteCell n) := by
  intro j j' h
  funext i
  have := congrArg (fun k : Fin 4 → ℤ => ((k i : ℤ) : ZMod (2 * n))) h
  simpa [intCast_siteCell] using this
private theorem exists_siteCell_eq (n : ℕ) [NeZero (2 * n)] (K : Fin 4 → ℤ)
    (hK : ∀ i, 0 ≤ K i ∧ K i < ((2 * n : ℕ) : ℤ)) : ∃ j, siteCell n j = K := by
  refine ⟨fun i => ((K i : ℤ) : ZMod (2 * n)) - (n : ZMod (2 * n)), ?_⟩
  funext i
  unfold siteCell
  simp only [sub_add_cancel]
  obtain ⟨h0, h1⟩ := hK i
  lift K i to ℕ using h0 with m hm
  have hm' : m < 2 * n := by exact_mod_cast h1
  simp [ZMod.val_natCast_of_lt hm']
private theorem exists_cellLeft_siteCell_eq (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) :
    ∃ w : Fin 4 → ℤ, (fun i => cellLeft (2 * n) (siteCell n j i)) =
      dualTorusMomentum j + fun i => 2 * Real.pi * (w i : ℝ) := by
  have hdvd : ∀ i, ((2 * n : ℕ) : ℤ) ∣ (siteCell n j i - n) - (j i).valMinAbs := by
    intro i
    have : (((siteCell n j i - n : ℤ)) : ZMod (2 * n)) = (((j i).valMinAbs : ℤ) : ZMod (2 * n)) := by
      rw [ZMod.coe_valMinAbs]
      push_cast
      rw [intCast_siteCell]
      ring
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this.symm
  choose w hw using hdvd
  refine ⟨w, ?_⟩
  funext i
  have h := hw i
  have hr : (siteCell n j i : ℝ) - n - ((j i).valMinAbs : ℝ) = (2 * (n : ℝ)) * (w i : ℝ) := by
    exact_mod_cast h
  simp only [Pi.add_apply, dualTorusMomentum, cellLeft]
  push_cast
  have hc : (siteCell n j i : ℝ) = ((j i).valMinAbs : ℝ) + n + 2 * (n : ℝ) * (w i : ℝ) := by linarith
  rw [hc]
  field_simp
  ring
private def siteBox (n : ℕ) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) : Set (Fin 4 → ℝ) :=
  {p | (fun i => floorCell (2 * n) (p i)) = siteCell n j}
private theorem siteBox_eq_pi (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) :
    siteBox n j = Set.pi univ fun i =>
      Ico (cellLeft (2 * n) (siteCell n j i)) (cellLeft (2 * n) (siteCell n j i + 1)) := by
  ext p
  simp only [siteBox, Set.mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies, funext_iff]
  exact forall_congr' fun i => floorCell_eq_iff (by omega) (p i) _
private theorem measurableSet_siteBox (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) :
    MeasurableSet (siteBox n j) := by
  rw [siteBox_eq_pi n hn]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico
private theorem volume_real_siteBox (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] (j : Fin 4 → ZMod (2 * n)) :
    (volume : Measure (Fin 4 → ℝ)).real (siteBox n j) = (2 * Real.pi / ((2 * n : ℕ) : ℝ)) ^ 4 := by
  have e : ∀ k : ℤ, cellLeft (2 * n) (k + 1) - cellLeft (2 * n) k = 2 * Real.pi / ((2 * n : ℕ) : ℝ) := by
    intro k
    unfold cellLeft
    push_cast
    field_simp
    ring
  rw [siteBox_eq_pi n hn, Measure.real, Real.volume_pi_Ico]
  simp only [e]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]
private def stepApprox (F : (Fin 4 → ℝ) → ℂ) (n : ℕ) [NeZero (2 * n)] (p : Fin 4 → ℝ) : ℂ :=
  ∑ j : Fin 4 → ZMod (2 * n), (siteBox n j).indicator (fun _ => F (dualTorusMomentum j)) p
private theorem integral_stepApprox (F : (Fin 4 → ℝ) → ℂ) (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] :
    ∫ p, stepApprox F n p = ((2 * Real.pi / ((2 * n : ℕ) : ℝ)) ^ 4 : ℝ) • ∑ j : Fin 4 → ZMod (2 * n), F (dualTorusMomentum j) := by
  unfold stepApprox
  rw [integral_finsetSum]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_const _ (measurableSet_siteBox n hn j), volume_real_siteBox n hn]
  · intro j _
    refine (integrable_indicator_iff (measurableSet_siteBox n hn j)).2 (integrableOn_const ?_ )
    rw [siteBox_eq_pi n hn, Real.volume_pi_Ico]
    exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne
private theorem measurable_stepApprox (F : (Fin 4 → ℝ) → ℂ) (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] :
    Measurable (stepApprox F n) := by
  unfold stepApprox
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.indicator (measurableSet_siteBox n hn j)
private theorem stepApprox_of_not_mem (F : (Fin 4 → ℝ) → ℂ) (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] {p : Fin 4 → ℝ}
    (hp : p ∉ Set.pi univ fun _ : Fin 4 => Ico (-Real.pi) Real.pi) : stepApprox F n p = 0 := by
  unfold stepApprox
  refine Finset.sum_eq_zero fun j _ => ?_
  refine indicator_of_notMem (fun hj => hp ?_) _
  intro i _
  have h := congrFun hj i
  have hr := siteCell_bounds n j i
  rw [← h] at hr
  exact mem_Ico_of_floorCell (by omega) hr.1 hr.2
private theorem stepApprox_of_mem {F : (Fin 4 → ℝ) → ℂ}
    (hper : ∀ (i : Fin 4) (p : Fin 4 → ℝ), F (p + Pi.single i (2 * Real.pi)) = F p)
    (n : ℕ) (hn : 0 < n) [NeZero (2 * n)] {p : Fin 4 → ℝ}
    (hp : p ∈ Set.pi univ fun _ : Fin 4 => Ico (-Real.pi) Real.pi) :
    stepApprox F n p = F (fun i => cellLeft (2 * n) (floorCell (2 * n) (p i))) ∧
      ∃ j : Fin 4 → ZMod (2 * n), stepApprox F n p = F (dualTorusMomentum j) := by
  have hr : ∀ i, 0 ≤ floorCell (2 * n) (p i) ∧ floorCell (2 * n) (p i) < ((2 * n : ℕ) : ℤ) := fun i =>
    floorCell_bounds (by omega) (hp i (mem_univ i))
  obtain ⟨j, hj⟩ := exists_siteCell_eq n (fun i => floorCell (2 * n) (p i)) hr
  have hs : stepApprox F n p = F (dualTorusMomentum j) := by
    unfold stepApprox
    rw [Finset.sum_eq_single j]
    · exact indicator_of_mem (show p ∈ siteBox n j from hj.symm) _
    · intro j' _ hne
      refine indicator_of_notMem (fun h => hne ?_) _
      have h' : (fun i => floorCell (2 * n) (p i)) = siteCell n j' := h
      exact siteCell_injective n (h'.symm.trans hj.symm)
    · intro h; exact absurd (Finset.mem_univ j) h
  refine ⟨?_, j, hs⟩
  obtain ⟨w, hw⟩ := exists_cellLeft_siteCell_eq n hn j
  have e : (fun i => cellLeft (2 * n) (floorCell (2 * n) (p i))) = fun i => cellLeft (2 * n) (siteCell n j i) := by
    funext i
    have h1 := congrFun hj i
    rw [h1]
  rw [e, hw, periodic_int_vector hper, hs]
private theorem tendsto_cellLeft_floorCell (p : Fin 4 → ℝ) :
    Tendsto (fun n : ℕ => fun i => cellLeft (2 * (n + 1)) (floorCell (2 * (n + 1)) (p i))) atTop (𝓝 p) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  have hlim : Tendsto (fun n : ℕ => 2 * Real.pi / ((2 * (n + 1) : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((2 * (n + 1) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => (by show n ≤ 2 * (n + 1); omega)) tendsto_id)
    exact h1.const_div_atTop _
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim)
  rw [Real.norm_eq_abs]
  exact abs_cellLeft_sub_le (by omega) (p i)
theorem tendstoRiemannSumOfPeriodic_holds : TendstoRiemannSumOfPeriodic := by
  intro F B hF hB hper hcont
  set E : Set (Fin 4 → ℝ) := Set.pi univ (fun _ => Ico (-Real.pi) Real.pi) with hE
  have hEm : MeasurableSet E := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hEfin : (volume : Measure (Fin 4 → ℝ)) E ≠ ⊤ := by
    rw [hE, Real.volume_pi_Ico]
    exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne
  have hlim : Tendsto (fun n : ℕ => ∫ p, stepApprox F (n + 1) p) atTop (𝓝 (∫ p, E.indicator F p)) := by
    refine tendsto_integral_of_dominated_convergence (E.indicator fun _ => B) ?_ ?_ ?_ ?_
    · exact fun n => (measurable_stepApprox F (n + 1) (by omega)).aestronglyMeasurable
    · exact (integrable_indicator_iff hEm).2 (integrableOn_const hEfin)
    · intro n
      refine Eventually.of_forall fun p => ?_
      by_cases hp : p ∈ E
      · rw [indicator_of_mem hp]
        obtain ⟨j, hj⟩ := (stepApprox_of_mem hper (n + 1) (by omega) hp).2
        rw [hj]
        exact hB _
      · rw [indicator_of_notMem hp, stepApprox_of_not_mem F (n + 1) (by omega) hp]
        simp
    · have h0 : ∀ᵐ p : Fin 4 → ℝ, p ≠ 0 := by
        have := measure_singleton (μ := (volume : Measure (Fin 4 → ℝ))) (0 : Fin 4 → ℝ)
        exact compl_mem_ae_iff.2 this
      filter_upwards [h0] with p hp0
      by_cases hp : p ∈ E
      · rw [indicator_of_mem hp]
        have hc := hcont p hp0 (fun i => ⟨(hp i (mem_univ i)).1, (hp i (mem_univ i)).2.le⟩)
        have ht := hc.tendsto.comp (tendsto_cellLeft_floorCell p)
        refine ht.congr fun n => ?_
        exact (stepApprox_of_mem hper (n + 1) (by omega) hp).1.symm
      · rw [indicator_of_notMem hp]
        refine tendsto_const_nhds.congr fun n => ?_
        exact (stepApprox_of_not_mem F (n + 1) (by omega) hp).symm
  have hint : ∫ p, E.indicator F p = ∫ p in Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), F p := by
    rw [integral_indicator hEm]
    refine setIntegral_congr_set ?_
    have h1 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 4 => (volume : Measure ℝ))
      (f := fun _ => -Real.pi) (g := fun _ => Real.pi)
    rw [volume_pi]
    exact h1
  rw [← hint]
  have hmul := hlim.const_mul (((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4)
  refine hmul.congr fun n => ?_
  rw [integral_stepApprox F (n + 1) (by omega)]
  have hN : (((2 * (n + 1) : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : 2 * (n + 1) ≠ 0)
  have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * Real.pi ≠ 0)
  rw [Complex.real_smul]
  push_cast
  push_cast at hN h2
  field_simp
end YangMills.Construction.RiemannSums
end
