import YangMills.Construction.Continuum.DistributionsOffTheDiagonalsAndTranslationsInSpaceProof
import YangMills.Construction.Continuum.TensorsOfBumpsInTheNorm
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.TensorApprox
open BumpApprox Elementary
variable {n : ℕ}
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg (v i)) (Finset.mem_univ μ))
theorem dist_le_of_forall_euclidNormVec_le {x z : PointTuple n} {r : ℝ} (hr : 0 ≤ r)
    (hxz : ∀ i, TorusMetric.euclidNormVec (x i - z i) ≤ r) : dist x z ≤ r := by
  refine (dist_pi_le_iff hr).2 fun i => (dist_pi_le_iff hr).2 fun μ => ?_
  rw [Real.dist_eq]
  exact (abs_apply_le_euclidNormVec (x i - z i) μ).trans (hxz i)
theorem exists_isStandardBumpR4 (hB : BumpApprox.BumpLemma) :
    ∃ ψ : (Fin 4 → ℝ) → ℝ, IsStandardBumpR4 ψ := by apply _root_.YangMills.Construction.TestSpaces.OffDiagonal.exists_standardBumpR4 <;> assumption
theorem zero_mem_disjointSupportTuples (O : Set (Fin 4 → ℝ)) :
    (fun _ _ => 0 : Fin n → (Fin 4 → ℝ) → ℝ) ∈ disjointSupportTuples O n ∧
      HasSmoothComponents O (fun _ _ => 0 : Fin n → (Fin 4 → ℝ) → ℝ) := by
  have hsupp : tsupport (fun _ => 0 : (Fin 4 → ℝ) → ℝ) = ∅ := by
    simp [tsupport, Function.support]
  have hcs : HasCompactSupport (fun _ => 0 : (Fin 4 → ℝ) → ℝ) := HasCompactSupport.zero
  refine ⟨⟨fun _ => ⟨contDiff_const, hcs, by rw [hsupp]; exact Set.empty_subset _⟩, ?_⟩,
    fun _ => ⟨contDiff_const, hcs, by rw [hsupp]; exact Set.empty_subset _⟩⟩
  intro i i' _
  rw [hsupp]
  exact Set.disjoint_empty _
theorem rescaledBump_mem_disjointSupportTuples {V : Set (PointTuple n)} {O : Set (Fin 4 → ℝ)}
    (hV : ∀ x ∈ V, (∀ i, x i ∈ O) ∧ Function.Injective x)
    {ψ : (Fin 4 → ℝ) → ℝ} {r : ℝ} {z : PointTuple n} (hr : 0 ≤ r)
    (hz : ∀ x : PointTuple n, (∀ i, TorusMetric.euclidNormVec (x i - z i) ≤ r) → x ∈ V)
    (hs : ∀ v, rescaledBump ψ r v ∈ (smoothCompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)) ∧
      tsupport (rescaledBump ψ r v) ⊆ {u | TorusMetric.euclidNormVec (u - v) ≤ r}) :
    (fun i => rescaledBump ψ r (z i)) ∈ disjointSupportTuples O n ∧
      HasSmoothComponents O fun i => rescaledBump ψ r (z i) := by
  have hself : ∀ i, TorusMetric.euclidNormVec (z i - z i) ≤ r := by
    intro i
    simpa [TorusMetric.euclidNormVec] using hr
  have hO : ∀ i, tsupport (rescaledBump ψ r (z i)) ⊆ O := by
    intro i u hu
    have hu' : TorusMetric.euclidNormVec (u - z i) ≤ r := (hs (z i)).2 hu
    have hx : Function.update z i u ∈ V := by
      apply hz
      intro l
      by_cases hl : l = i
      · subst hl
        simpa using hu'
      · simpa [Function.update_of_ne hl] using hself l
    simpa using (hV _ hx).1 i
  have hsm : ∀ i, rescaledBump ψ r (z i) ∈
      (smoothCompactSupp O : Set ((Fin 4 → ℝ) → ℝ)) :=
    fun i => ⟨(hs (z i)).1.1, (hs (z i)).1.2.1, hO i⟩
  refine ⟨⟨fun i => ⟨(hsm i).1.of_le ?_, (hsm i).2.1, hO i⟩, ?_⟩, hsm⟩
  · exact_mod_cast le_top
  · intro i i' hne
    rw [Set.disjoint_left]
    intro u hu hu'
    have hu1 : TorusMetric.euclidNormVec (u - z i) ≤ r := (hs (z i)).2 hu
    have hu2 : TorusMetric.euclidNormVec (u - z i') ≤ r := (hs (z i')).2 hu'
    have hx : Function.update (Function.update z i u) i' u ∈ V := by
      apply hz
      intro l
      by_cases hl' : l = i'
      · subst hl'
        simpa using hu2
      · by_cases hl : l = i
        · subst hl
          simpa [Function.update_of_ne hl'] using hu1
        · simpa [Function.update_of_ne hl', Function.update_of_ne hl] using hself l
    exact hne ((hV _ hx).2 (by simp [Function.update_of_ne hne]))
theorem approxByTensorSums_of_injective (hF : Elementary.BasicProperties)
    (hB : BumpApprox.BumpLemma) {k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {V : Set (PointTuple n)} {O : Set (Fin 4 → ℝ)} (hVo : IsOpen V) (hOo : IsOpen O)
    (hV : ∀ x ∈ V, (∀ i, x i ∈ O) ∧ Function.Injective x) : ApproxByTensorSums V O k := by
  intro φ hφ ε hε
  obtain ⟨hφs, hφc, hφV⟩ := hφ
  obtain ⟨-, -, hCS, hST, -⟩ := hF n hn
  obtain ⟨-, -, hbump, happ⟩ := hB n hn
  obtain ⟨ψ, hψ⟩ := exists_isStandardBumpR4 hB
  have hKc : IsCompact (tsupport φ) := hφc
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_thickening_subset_open hVo hφV
  have hK' : IsCompact (Metric.cthickening 1 (tsupport φ)) := hKc.cthickening
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧
      ∀ x ∈ Metric.cthickening 1 (tsupport φ), tupleNorm x ≤ ρ := by
    have hc : Continuous (tupleNorm : PointTuple n → ℝ) := by
      unfold tupleNorm
      fun_prop
    obtain ⟨b, hb⟩ := (hK'.image hc).bddAbove
    exact ⟨max b 0, le_max_right _ _,
      fun x hx => (hb ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  have hW : 0 < (1 + ρ ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨ε₁, hε₁, hap⟩ := happ φ ⟨hφs, hφc, Set.subset_univ _⟩ k
    (ε / (1 + ρ ^ 2) ^ ((k : ℝ) / 2)) (div_pos hε hW)
  obtain ⟨r, hr, hr₁, hrδ, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ε₁ ∧ r < δ ∧ r ≤ 1 :=
    ⟨min ε₁ (min (δ / 2) 1), lt_min hε₁ (lt_min (half_pos hδ) one_pos), min_le_left _ _,
      ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hδ),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨h, -, hfin, hnear⟩ := hap ψ hψ r hr hr₁
  have hs := fun v => hbump ψ hψ r v hr
  have hsum : ∀ x, gridApprox ψ φ r h x = ∑ z ∈ hfin.toFinset, gridSummand ψ φ r h z x := by
    intro x
    have h0 : gridApprox ψ φ r h = ∑ z ∈ hfin.toFinset, gridSummand ψ φ r h z :=
      finsum_mem_eq_sum _ hfin
    rw [h0, Finset.sum_apply]
  have hTK : ∀ z ∈ hfin.toFinset, z ∈ tsupport φ := by
    intro z hz
    have hz' : z ∈ latticeGrid n h ∧ gridSummand ψ φ r h z ≠ 0 := hfin.mem_toFinset.1 hz
    refine subset_tsupport _ ?_
    intro h0
    apply hz'.2
    funext x
    simp [gridSummand, h0]
  have hsep : ∀ z ∈ hfin.toFinset, (fun i => rescaledBump ψ r (z i)) ∈ disjointSupportTuples O n ∧
      HasSmoothComponents O fun i => rescaledBump ψ r (z i) := by
    intro z hz
    refine rescaledBump_mem_disjointSupportTuples hV hr.le (fun x hx => hδV ?_) hs
    exact Metric.mem_thickening_iff.2
      ⟨z, hTK z hz, (dist_le_of_forall_euclidNormVec_le hr.le hx).trans_lt hrδ⟩
  have hterm : ∀ z ∈ hfin.toFinset, ContDiff ℝ ∞ (gridSummand ψ φ r h z) := by
    intro z hz
    have hc : ContDiff ℝ ∞ (tensorProdComplex fun i => rescaledBump ψ r (z i)) :=
      (((hST O hOo _ (hsep z hz).1).2 (hsep z hz).2).2.1).1.1
    exact contDiff_const.mul hc
  have hsmooth : ContDiff ℝ ∞ (gridApprox ψ φ r h) := by
    have : gridApprox ψ φ r h = fun x => ∑ z ∈ hfin.toFinset, gridSummand ψ φ r h z x :=
      funext hsum
    rw [this]
    exact ContDiff.sum hterm
  have hvan : ∀ x, x ∉ Metric.cthickening 1 (tsupport φ) → (φ - gridApprox ψ φ r h) x = 0 := by
    intro x hx
    have hφx : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hm => hx (Metric.self_subset_cthickening _ hm)
    have hRx : gridApprox ψ φ r h x = 0 := by
      rw [hsum]
      refine Finset.sum_eq_zero fun z hz => ?_
      have hex : ∃ i, ¬ TorusMetric.euclidNormVec (x i - z i) ≤ r := by
        by_contra hall
        exact hx (Metric.mem_cthickening_of_dist_le x z 1 _ (hTK z hz)
          ((dist_le_of_forall_euclidNormVec_le hr.le
            fun i => by_contra fun hi => hall ⟨i, hi⟩).trans hr1))
      obtain ⟨i, hi⟩ := hex
      have hzero : rescaledBump ψ r (z i) (x i) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hm => hi ((hs (z i)).2 hm)
      have ht : tensorProd (fun i => rescaledBump ψ r (z i)) x = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      simp [gridSummand, ht]
    simp [hφx, hRx]
  have hD : φ - gridApprox ψ φ r h ∈
      (smoothCompactSupp Set.univ : Set (PointTuple n → ℂ)) :=
    ⟨hφs.sub hsmooth, HasCompactSupport.intro hK' hvan, Set.subset_univ _⟩
  have hnorm : weightedSeminorm k (φ - gridApprox ψ φ r h) ≤ ENNReal.ofReal ε := by
    have hb := (hCS Set.univ isOpen_univ _ hD).2.2.2 ρ hρ0
      (fun x hx => hvan x fun hm => hx (hρ x hm)) k hk
    calc weightedSeminorm k (φ - gridApprox ψ φ r h)
        ≤ ENNReal.ofReal ((1 + ρ ^ 2) ^ ((k : ℝ) / 2)) *
            derivSupNorm k (φ - gridApprox ψ φ r h) := hb
      _ ≤ ENNReal.ofReal ((1 + ρ ^ 2) ^ ((k : ℝ) / 2)) *
            ENNReal.ofReal (ε / (1 + ρ ^ 2) ^ ((k : ℝ) / 2)) := by gcongr
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hW.le, mul_div_cancel₀ _ hW.ne']
  let pt : Fin hfin.toFinset.card → PointTuple n := fun i => (hfin.toFinset.equivFin.symm i).1
  have hpt : ∀ i, pt i ∈ hfin.toFinset := fun i => (hfin.toFinset.equivFin.symm i).2
  let c : Fin (hfin.toFinset.card + 1) → ℂ :=
    Fin.cons 0 fun i => ((h ^ (4 * n) : ℝ) : ℂ) * φ (pt i)
  let f : Fin (hfin.toFinset.card + 1) → Fin n → (Fin 4 → ℝ) → ℝ :=
    Fin.cons (fun _ _ => 0) fun i l => rescaledBump ψ r (pt i l)
  have hR : (fun x => ∑ ι, c ι * ((tensorProd (f ι) x : ℝ) : ℂ)) = gridApprox ψ φ r h := by
    funext x
    rw [hsum, Fin.sum_univ_succ]
    simp only [c, f, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
    rw [← Finset.sum_coe_sort hfin.toFinset fun z => gridSummand ψ φ r h z x,
      ← Equiv.sum_comp hfin.toFinset.equivFin.symm]
    rfl
  refine ⟨hfin.toFinset.card + 1, c, f, Nat.succ_pos _, ?_, ?_, ?_⟩
  · intro ι
    refine Fin.cases ?_ (fun i => ?_) ι
    · exact zero_mem_disjointSupportTuples O
    · exact hsep _ (hpt i)
  · rw [hR]
    exact hnorm
  · intro hre ι
    refine Fin.cases ?_ (fun i => ?_) ι
    · simp [c]
    · simp only [c, Fin.cons_succ]
      rw [Complex.mul_im, Complex.ofReal_im, hre]
      simp
theorem tensorSumsApproxBumps_holds (hF : Elementary.BasicProperties)
    (hB : BumpApprox.BumpLemma) : TensorSumsApproxBumps := by
  intro n k hn hk
  obtain ⟨-, hopen, -⟩ := hF n hn
  refine ⟨approxByTensorSums_of_injective hF hB hn hk hopen.1 isOpen_univ
      fun x hx => ⟨fun _ => trivial, hx⟩,
    approxByTensorSums_of_injective hF hB hn hk hopen.2.1 ?_ fun x hx => ⟨hx.2, hx.1⟩⟩
  exact isOpen_lt continuous_const (continuous_apply 3)
end YangMills.Construction.TestSpaces.TensorApprox
end
