import YangMills.Construction.EuclideanSpectral.ProjMeasureBasicFacts
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanSpectral
namespace SpectralFacts
open ProjMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem eq_zero_of_inner_self_apply_eq_zero (A : H →ₗ[ℂ] H) (hA : ∀ ψ : H, inner ℂ ψ (A ψ) = 0) :
    A = 0 := by
  refine (inner_map_self_eq_zero A).1 fun x => ?_
  rw [← inner_conj_symm, hA x, map_zero]
theorem inner_map_map_of_isUnitaryMap {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U) (φ ψ : H) :
    inner ℂ (U φ) (U ψ) = inner ℂ φ ψ :=
  (LinearIsometry.mk U hU.norm_map).inner_map_map φ ψ
theorem apply_inv_apply {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U) (φ : H) : U (hU.inv φ) = φ :=
  (LinearEquiv.ofBijective U hU.bijective).apply_symm_apply φ
theorem inv_inner {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U) (φ ψ : H) :
    inner ℂ (hU.inv φ) ψ = inner ℂ φ (U ψ) := by
  rw [← inner_map_map_of_isUnitaryMap hU, apply_inv_apply]
theorem inner_inv {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U) (φ ψ : H) :
    inner ℂ φ (hU.inv ψ) = inner ℂ (U φ) ψ := by
  rw [← inner_map_map_of_isUnitaryMap hU, apply_inv_apply]
theorem orthProj_idem {p : H →ₗ[ℂ] H} (hp : IsOrthProj p) (ψ : H) : p (p ψ) = p ψ :=
  LinearMap.congr_fun hp.idem ψ
theorem orthProj_norm_sq {p : H →ₗ[ℂ] H} (hp : IsOrthProj p) (ψ : H) :
    ((‖p ψ‖ ^ 2 : ℝ) : ℂ) = inner ℂ ψ (p ψ) := by
  have h1 : inner ℂ (p ψ) (p ψ) = inner ℂ ψ (p ψ) := by
    rw [hp.symm, orthProj_idem hp]
  rw [← h1, inner_self_eq_norm_sq_to_K]
  simp
theorem orthProj_norm_sq_eq_re {p : H →ₗ[ℂ] H} (hp : IsOrthProj p) (ψ : H) :
    ‖p ψ‖ ^ 2 = (inner ℂ ψ (p ψ)).re := by
  rw [← orthProj_norm_sq hp, Complex.ofReal_re]
theorem orthProj_norm_le {p : H →ₗ[ℂ] H} (hp : IsOrthProj p) (ψ : H) : ‖p ψ‖ ≤ ‖ψ‖ := by
  rcases (norm_nonneg (p ψ)).eq_or_lt with h | hpos
  · rw [← h]; exact norm_nonneg _
  · have h2 : ‖p ψ‖ * ‖p ψ‖ ≤ ‖ψ‖ * ‖p ψ‖ := by
      rw [← sq, orthProj_norm_sq_eq_re hp]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    exact le_of_mul_le_mul_right h2 hpos
theorem isOrthProj_conj {p : H →ₗ[ℂ] H} (hp : IsOrthProj p) {U : H →ₗ[ℂ] H}
    (hU : IsUnitaryMap U) : IsOrthProj (hU.inv ∘ₗ p ∘ₗ U) where
  idem := by
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, apply_inv_apply, orthProj_idem hp]
  symm φ ψ := by
    simp only [LinearMap.comp_apply]
    rw [inv_inner hU, hp.symm, inner_inv hU]
variable {n : ℕ} [NeZero n]
theorem diag_eq_norm_sq (E : ProjMeasure H n) (ψ : H) (B : BorelSubset n) :
    E.diag ψ B = ((‖E B ψ‖ ^ 2 : ℝ) : ℂ) :=
  (orthProj_norm_sq (E.isOrthProj B) ψ).symm
theorem hasSum_norm_sq (E : ProjMeasure H n) (ψ : H) (B : ℕ → BorelSubset n)
    (hB : Pairwise fun k l => Disjoint (B k).1 (B l).1) :
    HasSum (fun k => ‖E (B k) ψ‖ ^ 2) (‖E (BorelSubset.unionSeq B) ψ‖ ^ 2) := by
  have h := E.hasSum_diag ψ B hB
  have h' : HasSum (fun k => ((‖E (B k) ψ‖ ^ 2 : ℝ) : ℂ))
      ((‖E (BorelSubset.unionSeq B) ψ‖ ^ 2 : ℝ) : ℂ) := by
    convert h using 1
    · exact funext fun k => (diag_eq_norm_sq E ψ (B k)).symm
    · exact (diag_eq_norm_sq E ψ _).symm
  exact Complex.hasSum_ofReal.1 h'
theorem norm_sq_empty (E : ProjMeasure H n) (ψ : H) :
    ‖E ⟨∅, MeasurableSet.empty⟩ ψ‖ ^ 2 = 0 := by
  have h := hasSum_norm_sq E ψ (fun _ => ⟨∅, MeasurableSet.empty⟩) (fun _ _ _ => by simp)
  have he : BorelSubset.unionSeq (fun _ : ℕ => (⟨∅, MeasurableSet.empty⟩ : BorelSubset n)) =
      ⟨∅, MeasurableSet.empty⟩ := Subtype.ext (by simp [BorelSubset.unionSeq])
  rw [he] at h
  exact (summable_const_iff _).1 h.summable
theorem exists_diag_measure (E : ProjMeasure H n) (ψ : H) :
    ∃ μ, IsFiniteMeasureRep (E.diag ψ) μ := by
  let w : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → ℝ≥0∞ :=
    fun s hs => ENNReal.ofReal (‖E ⟨s, hs⟩ ψ‖ ^ 2)
  have w0 : w ∅ MeasurableSet.empty = 0 := by
    simp only [w]
    rw [norm_sq_empty E ψ, ENNReal.ofReal_zero]
  have wU : ∀ ⦃f : ℕ → Set (EuclideanSpace ℝ (Fin n))⦄ (h : ∀ i, MeasurableSet (f i)),
      Pairwise (Function.onFun Disjoint f) →
        w (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, w (f i) (h i) := by
    intro f h hd
    have hs := hasSum_norm_sq E ψ (fun i => ⟨f i, h i⟩) hd
    simp only [w]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable, hs.tsum_eq]
    rfl
  let μ := Measure.ofMeasurable w w0 wU
  have hμ : ∀ B : BorelSubset n, μ B.1 = ENNReal.ofReal (‖E B ψ‖ ^ 2) := fun B =>
    Measure.ofMeasurable_apply B.1 B.2
  refine ⟨μ, ⟨?_⟩, fun B => ?_⟩
  · have := hμ (BorelSubset.univ n)
    simp only [BorelSubset.univ] at this
    rw [this]
    exact ENNReal.ofReal_lt_top
  · rw [diag_eq_norm_sq, Measure.real, hμ B, ENNReal.toReal_ofReal (by positivity)]
theorem diagMeasure_spec (E : ProjMeasure H n) (ψ : H) :
    IsFiniteMeasureRep (E.diag ψ) (E.diagMeasure ψ) :=
  Classical.epsilon_spec (exists_diag_measure E ψ)
instance diagMeasure_isFinite (E : ProjMeasure H n) (ψ : H) :
    IsFiniteMeasure (E.diagMeasure ψ) :=
  (diagMeasure_spec E ψ).1
theorem inner_apply_eq_measureReal (E : ProjMeasure H n) (ψ : H) (B : BorelSubset n) :
    inner ℂ ψ (E B ψ) = (((E.diagMeasure ψ).real B.1 : ℝ) : ℂ) :=
  (diagMeasure_spec E ψ).2 B
theorem measureReal_eq_norm_sq (E : ProjMeasure H n) (ψ : H) (B : BorelSubset n) :
    (E.diagMeasure ψ).real B.1 = ‖E B ψ‖ ^ 2 := by
  have h := (inner_apply_eq_measureReal E ψ B).symm.trans
    (orthProj_norm_sq (E.isOrthProj B) ψ).symm
  exact_mod_cast h
theorem measureReal_univ (E : ProjMeasure H n) (ψ : H) :
    (E.diagMeasure ψ).real univ = ‖ψ‖ ^ 2 := by
  have h := measureReal_eq_norm_sq E ψ (BorelSubset.univ n)
  rw [show E (BorelSubset.univ n) = LinearMap.id from E.univ_eq_id] at h
  simpa [BorelSubset.univ] using h
theorem apply_apply (E : ProjMeasure H n) (B : BorelSubset n) (ψ : H) :
    E B (E B ψ) = E B ψ :=
  orthProj_idem (E.isOrthProj B) ψ
theorem apply_union (E : ProjMeasure H n) (B B' : BorelSubset n)
    (h : Disjoint B.1 B'.1) : E ⟨B.1 ∪ B'.1, B.2.union B'.2⟩ = E B + E B' := by
  have h0 : E ⟨B.1 ∪ B'.1, B.2.union B'.2⟩ - E B - E B' = 0 := by
    refine eq_zero_of_inner_self_apply_eq_zero _ fun ψ => ?_
    simp only [LinearMap.sub_apply, inner_sub_right, inner_apply_eq_measureReal]
    rw [measureReal_union h B'.2]
    push_cast
    ring
  rw [sub_sub, sub_eq_zero] at h0
  exact h0
theorem comp_of_disjoint_eq_zero (E : ProjMeasure H n) (B B' : BorelSubset n)
    (h : Disjoint B.1 B'.1) : E B ∘ₗ E B' = 0 := by
  refine LinearMap.ext fun φ => ?_
  have hsum : (E.diagMeasure (E B' φ)).real (B.1 ∪ B'.1) =
      ‖E B (E B' φ)‖ ^ 2 + ‖E B' φ‖ ^ 2 := by
    rw [measureReal_union h B'.2, measureReal_eq_norm_sq, measureReal_eq_norm_sq, apply_apply]
  have hle := orthProj_norm_le (E.isOrthProj ⟨B.1 ∪ B'.1, B.2.union B'.2⟩) (E B' φ)
  have hu := measureReal_eq_norm_sq E (E B' φ) ⟨B.1 ∪ B'.1, B.2.union B'.2⟩
  have hz : ‖E B (E B' φ)‖ ^ 2 ≤ 0 := by
    have h3 : ‖E ⟨B.1 ∪ B'.1, B.2.union B'.2⟩ (E B' φ)‖ ^ 2 ≤ ‖E B' φ‖ ^ 2 := by gcongr
    simp only at hu
    linarith
  have hz' : ‖E B (E B' φ)‖ = 0 := by
    have := sq_nonneg ‖E B (E B' φ)‖
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hz this)
  simpa using hz'
theorem comp_eq_apply_inter (E : ProjMeasure H n) (B B' : BorelSubset n) :
    E B ∘ₗ E B' = E ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩ := by
  let B₀ : BorelSubset n := ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩
  let B₁ : BorelSubset n := ⟨B.1 \ B'.1, B.2.diff B'.2⟩
  let B₂ : BorelSubset n := ⟨B'.1 \ B.1, B'.2.diff B.2⟩
  have d10 : Disjoint B₁.1 B₀.1 :=
    Set.disjoint_left.2 fun x hx hy => hx.2 hy.2
  have d20 : Disjoint B₂.1 B₀.1 :=
    Set.disjoint_left.2 fun x hx hy => hx.2 hy.1
  have d12 : Disjoint B₁.1 B₂.1 :=
    Set.disjoint_left.2 fun x hx hy => hx.2 hy.1
  have e1 : E B = E B₁ + E B₀ := by
    rw [← apply_union E B₁ B₀ d10]
    exact congrArg E (Subtype.ext (Set.sdiff_union_inter B.1 B'.1).symm)
  have e2 : E B' = E B₂ + E B₀ := by
    rw [← apply_union E B₂ B₀ d20]
    refine congrArg E (Subtype.ext ?_)
    simp only [B₂, B₀]
    rw [Set.inter_comm, Set.sdiff_union_inter]
  have z12 := comp_of_disjoint_eq_zero E B₁ B₂ d12
  have z10 := comp_of_disjoint_eq_zero E B₁ B₀ d10
  have z02 := comp_of_disjoint_eq_zero E B₀ B₂ d20.symm
  refine LinearMap.ext fun ψ => ?_
  have a12 := LinearMap.congr_fun z12 ψ
  have a10 := LinearMap.congr_fun z10 ψ
  have a02 := LinearMap.congr_fun z02 ψ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at a12 a10 a02
  rw [LinearMap.comp_apply, e1, e2]
  simp only [LinearMap.add_apply, map_add, a12, a10, a02, apply_apply, zero_add]
  rfl
theorem isNull_iff_diag (E : ProjMeasure H n) (B : BorelSubset n) :
    E.IsNull B ↔ ∀ ψ : H, E.diag ψ B = 0 := by
  constructor
  · intro h ψ
    have h' : E B = 0 := h
    rw [diag_eq_norm_sq, h']
    simp
  · intro h
    refine LinearMap.ext fun ψ => ?_
    have h1 := h ψ
    rw [diag_eq_norm_sq] at h1
    have h2 : ‖E B ψ‖ ^ 2 = 0 := by exact_mod_cast h1
    simpa using h2
theorem isNull_iff_diagMeasure (E : ProjMeasure H n) (B : BorelSubset n) :
    E.IsNull B ↔ ∀ ψ : H, E.diagMeasure ψ B.1 = 0 := by
  rw [isNull_iff_diag]
  refine forall_congr' fun ψ => ?_
  have h : E.diag ψ B = (((E.diagMeasure ψ).real B.1 : ℝ) : ℂ) :=
    inner_apply_eq_measureReal E ψ B
  rw [h, Complex.ofReal_eq_zero, measureReal_eq_zero_iff]
def simpleOp (E : ProjMeasure H n)
    (g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) : H →ₗ[ℂ] H :=
  ∑ y ∈ g.range, y • E ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩
theorem simpleOp_apply (E : ProjMeasure H n)
    (g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) (ψ : H) :
    simpleOp E g ψ = ∑ y ∈ g.range, y • E ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ ψ := by
  simp [simpleOp, LinearMap.sum_apply]
theorem inner_simpleOp (E : ProjMeasure H n)
    (g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) (ψ : H) :
    inner ℂ ψ (simpleOp E g ψ) = ∫ x, g x ∂(E.diagMeasure ψ) := by
  rw [← SimpleFunc.integral_eq_integral g (g.integrable_of_isFiniteMeasure),
    SimpleFunc.integral_eq, simpleOp_apply, inner_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [inner_smul_right, inner_apply_eq_measureReal, Complex.real_smul, mul_comm]
theorem inner_fiber_fiber (E : ProjMeasure H n)
    (g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) (ψ : H) {y y' : ℂ} (h : y ≠ y') :
    inner ℂ (E ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ ψ)
      (E ⟨g ⁻¹' {y'}, g.measurableSet_fiber y'⟩ ψ) = 0 := by
  have hd : Disjoint (g ⁻¹' {y}) (g ⁻¹' {y'}) :=
    Disjoint.preimage _ (by simpa using h)
  have hz := LinearMap.congr_fun
    (comp_of_disjoint_eq_zero E ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩
      ⟨g ⁻¹' {y'}, g.measurableSet_fiber y'⟩ hd) ψ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [(E.isOrthProj _).symm, hz, inner_zero_right]
theorem norm_sq_simpleOp (E : ProjMeasure H n)
    (g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) (ψ : H) :
    ‖simpleOp E g ψ‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂(E.diagMeasure ψ) := by
  have hmap := SimpleFunc.map_integral (μ := E.diagMeasure ψ) g (fun z : ℂ => ‖z‖ ^ 2)
    (g.integrable_of_isFiniteMeasure) (by simp)
  have hint := SimpleFunc.integral_eq_integral (g.map fun z : ℂ => ‖z‖ ^ 2)
    ((g.map fun z : ℂ => ‖z‖ ^ 2).integrable_of_isFiniteMeasure (μ := E.diagMeasure ψ))
  have hI : ∫ x, ‖g x‖ ^ 2 ∂(E.diagMeasure ψ) =
      ∑ y ∈ g.range, (E.diagMeasure ψ).real (g ⁻¹' {y}) • ‖y‖ ^ 2 := by
    rw [← hmap, hint]
    rfl
  rw [hI]
  have hC : ((‖simpleOp E g ψ‖ ^ 2 : ℝ) : ℂ) =
      ((∑ y ∈ g.range, (E.diagMeasure ψ).real (g ⁻¹' {y}) • ‖y‖ ^ 2 : ℝ) : ℂ) := by
    have h0 : ((‖simpleOp E g ψ‖ ^ 2 : ℝ) : ℂ) =
        inner ℂ (simpleOp E g ψ) (simpleOp E g ψ) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [h0, simpleOp_apply, sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [inner_sum, Finset.sum_eq_single y]
    · rw [inner_smul_left, inner_smul_right]
      have h1 : inner ℂ (E ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ ψ)
          (E ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ ψ) =
          (((E.diagMeasure ψ).real (g ⁻¹' {y}) : ℝ) : ℂ) := by
        rw [(E.isOrthProj _).symm, apply_apply, inner_apply_eq_measureReal]
      rw [h1, smul_eq_mul]
      have h2 : (starRingEnd ℂ) y * y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast at h2 ⊢
      linear_combination (((E.diagMeasure ψ).real (g ⁻¹' {y}) : ℝ) : ℂ) * h2
    · intro y' _ hne
      rw [inner_smul_right, inner_smul_left, inner_fiber_fiber E g ψ hne.symm]
      simp
    · intro h
      exact absurd hy h
  exact_mod_cast hC
theorem simpleOp_sub (E : ProjMeasure H n)
    (g g' : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) :
    simpleOp E g - simpleOp E g' = simpleOp E (g - g') := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_self_apply_eq_zero _ fun ψ => ?_
  simp only [LinearMap.sub_apply, inner_sub_right, inner_simpleOp, SimpleFunc.coe_sub,
    Pi.sub_apply]
  rw [integral_sub (g.integrable_of_isFiniteMeasure) (g'.integrable_of_isFiniteMeasure), sub_self]
theorem norm_simpleOp_le (E : ProjMeasure H n)
    (g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ) (ψ : H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ x, ‖g x‖ ≤ δ) : ‖simpleOp E g ψ‖ ≤ δ * ‖ψ‖ := by
  have h1 : ‖simpleOp E g ψ‖ ^ 2 ≤ (δ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_simpleOp]
    have hb : ‖∫ x, ‖g x‖ ^ 2 ∂(E.diagMeasure ψ)‖ ≤ δ ^ 2 * (E.diagMeasure ψ).real univ := by
      refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg x) 2
    rw [measureReal_univ] at hb
    calc _ ≤ ‖∫ x, ‖g x‖ ^ 2 ∂(E.diagMeasure ψ)‖ := le_abs_self _
      _ ≤ δ ^ 2 * ‖ψ‖ ^ 2 := hb
      _ = (δ * ‖ψ‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
omit [NeZero n] in
theorem exists_simpleFunc_approx (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (k : ℕ) :
    ∃ g : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, ‖f x - g x‖ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  let c : ℝ := (k : ℝ) + 1
  let h : EuclideanSpace ℝ (Fin n) → ℤ × ℤ :=
    fun x => (⌊c * (f x).re⌋, ⌊c * (f x).im⌋)
  have hm : Measurable h :=
    ((measurable_const.mul (Complex.measurable_re.comp hf)).floor).prodMk
      ((measurable_const.mul (Complex.measurable_im.comp hf)).floor)
  have hbox : ∀ t : ℝ, |t| ≤ C → ⌊c * t⌋ ∈ Icc ⌊c * (-C)⌋ ⌊c * C⌋ := by
    intro t ht
    have := abs_le.1 ht
    exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left this.1 hk.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left this.2 hk.le)⟩
  have hfin : (range h).Finite := by
    refine ((finite_Icc ⌊c * (-C)⌋ ⌊c * C⌋).prod (finite_Icc ⌊c * (-C)⌋ ⌊c * C⌋)).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨hbox _ ((Complex.abs_re_le_norm _).trans (hC x)),
      hbox _ ((Complex.abs_im_le_norm _).trans (hC x))⟩
  let S : SimpleFunc (EuclideanSpace ℝ (Fin n)) (ℤ × ℤ) :=
    { toFun := h
      measurableSet_fiber' := fun p => hm (measurableSet_singleton p)
      finite_range' := hfin }
  refine ⟨S.map fun p => ⟨(p.1 : ℝ) / c, (p.2 : ℝ) / c⟩, fun x => ?_⟩
  have hround : ∀ t : ℝ, |t - (⌊c * t⌋ : ℝ) / c| ≤ 1 / c := by
    intro t
    have h1 := Int.floor_le (c * t)
    have h2 := Int.lt_floor_add_one (c * t)
    have hc : t - (⌊c * t⌋ : ℝ) / c = (c * t - ⌊c * t⌋) / c := by
      rw [sub_div, mul_div_cancel_left₀ _ hk.ne']
    rw [hc, abs_div, abs_of_pos hk]
    refine div_le_div_of_nonneg_right ?_ hk.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hre := hround (f x).re
  have him := hround (f x).im
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hrw : (f x - (S.map fun p => (⟨(p.1 : ℝ) / c, (p.2 : ℝ) / c⟩ : ℂ)) x).re =
      (f x).re - (⌊c * (f x).re⌋ : ℝ) / c := rfl
  have hiw : (f x - (S.map fun p => (⟨(p.1 : ℝ) / c, (p.2 : ℝ) / c⟩ : ℂ)) x).im =
      (f x).im - (⌊c * (f x).im⌋ : ℝ) / c := rfl
  rw [hrw, hiw]
  have : 2 * (1 / ((k : ℝ) + 1)) = 1 / c + 1 / c := by
    simp only [c]; ring
  rw [this]
  exact add_le_add hre him
theorem weakIntegral_unique (E : ProjMeasure H n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    {A A' : H →ₗ[ℂ] H} (hA : E.IsWeakIntegralOp f A) (hA' : E.IsWeakIntegralOp f A') : A = A' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_self_apply_eq_zero _ fun ψ => ?_
  rw [LinearMap.sub_apply, inner_sub_right, hA ψ, hA' ψ, sub_self]
theorem exists_weakIntegral (E : ProjMeasure H n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ∃ A : H →ₗ[ℂ] H, E.IsWeakIntegralOp f A ∧
      ∀ ψ : H, ‖A ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ) := by
  choose g hg using fun k : ℕ => exists_simpleFunc_approx f hf hC k
  have hε : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have hε1 : ∀ k : ℕ, 2 * (1 / ((k : ℝ) + 1)) ≤ 2 := by
    intro k
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  have hanti : ∀ k l : ℕ, k ≤ l → 2 * (1 / ((l : ℝ) + 1)) ≤ 2 * (1 / ((k : ℝ) + 1)) := by
    intro k l hkl
    have : ((k : ℝ) + 1) ≤ (l : ℝ) + 1 := by
      have : (k : ℝ) ≤ l := by exact_mod_cast hkl
      linarith
    gcongr
  have hcauchy : ∀ ψ : H, CauchySeq fun k => simpleOp E (g k) ψ := by
    intro ψ
    refine cauchySeq_of_le_tendsto_0' (fun k : ℕ => 2 * (2 * (1 / ((k : ℝ) + 1))) * ‖ψ‖)
      (fun k l hkl => ?_) ?_
    · rw [dist_eq_norm, ← LinearMap.sub_apply, simpleOp_sub]
      refine norm_simpleOp_le E _ ψ (by positivity) fun x => ?_
      have h1 := hg k x
      have h2 := hg l x
      have h3 := hanti k l hkl
      have h4 : (g k - g l) x = (f x - g l x) - (f x - g k x) := by
        simp [SimpleFunc.coe_sub]
      rw [h4]
      refine (norm_sub_le _ _).trans ?_
      linarith
    · simpa using (hε.const_mul 2).mul_const ‖ψ‖
  choose L hL using fun ψ : H => cauchySeq_tendsto_of_complete (hcauchy ψ)
  let A : H →ₗ[ℂ] H :=
    { toFun := L
      map_add' := fun φ ψ => by
        refine tendsto_nhds_unique (hL (φ + ψ)) ?_
        simpa only [map_add] using (hL φ).add (hL ψ)
      map_smul' := fun z ψ => by
        refine tendsto_nhds_unique (hL (z • ψ)) ?_
        simpa only [map_smul, RingHom.id_apply] using (hL ψ).const_smul z }
  have hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hε
    rw [norm_sub_rev]
    exact hg k x
  have hbound : ∀ k x, ‖g k x‖ ≤ C + 2 := by
    intro k x
    have h1 : g k x = f x - (f x - g k x) := by ring
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    linarith [hC x, hg k x, hε1 k]
  refine ⟨A, fun ψ => ?_, fun ψ => ?_⟩
  · have h1 : Tendsto (fun k => inner ℂ ψ (simpleOp E (g k) ψ)) atTop
        (𝓝 (inner ℂ ψ (A ψ))) := tendsto_const_nhds.inner (hL ψ)
    have h2 : Tendsto (fun k => ∫ x, g k x ∂(E.diagMeasure ψ)) atTop
        (𝓝 (∫ x, f x ∂(E.diagMeasure ψ))) :=
      tendsto_integral_of_dominated_convergence (fun _ => C + 2)
        (fun k => (g k).aestronglyMeasurable) (integrable_const _)
        (fun k => Eventually.of_forall (hbound k)) (Eventually.of_forall hlim)
    simp only [inner_simpleOp] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 : Tendsto (fun k => ‖simpleOp E (g k) ψ‖ ^ 2) atTop (𝓝 (‖A ψ‖ ^ 2)) :=
      ((hL ψ).norm).pow 2
    have h2 : Tendsto (fun k => ∫ x, ‖g k x‖ ^ 2 ∂(E.diagMeasure ψ)) atTop
        (𝓝 (∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ))) :=
      tendsto_integral_of_dominated_convergence (fun _ => (C + 2) ^ 2)
        (fun k => ((g k).measurable.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
        (fun k => Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hbound k x) 2)
        (Eventually.of_forall fun x => ((hlim x).norm).pow 2)
    simp only [norm_sq_simpleOp] at h1
    exact tendsto_nhds_unique h1 h2
end SpectralFacts
open SpectralFacts ProjMeasure
theorem ProjMeasureBasicFacts.holds : ProjMeasureBasicFacts := by
  intro H _ _ _ n _ E
  refine ⟨⟨eq_zero_of_inner_self_apply_eq_zero,
      fun U hU φ ψ => ⟨inner_map_map_of_isUnitaryMap hU φ ψ, inv_inner hU φ ψ⟩⟩,
    fun p hp => ⟨fun ψ => ⟨orthProj_norm_sq hp ψ, ?_⟩, fun U hU => isOrthProj_conj hp hU⟩,
    fun ψ => ⟨diagMeasure_spec E ψ, diag_eq_norm_sq E ψ, ?_⟩,
    fun φ ψ z B => ⟨?_, ?_⟩,
    ⟨?_, fun B B' h => apply_union E B B' h, comp_eq_apply_inter E⟩,
    ⟨isNull_iff_diag E, ?_, ?_⟩, fun f hf hb => ?_⟩
  · rw [← orthProj_norm_sq_eq_re hp]
    exact pow_le_pow_left₀ (norm_nonneg _) (orthProj_norm_le hp ψ) 2
  · rw [diag_eq_norm_sq, show E (BorelSubset.univ n) = LinearMap.id from E.univ_eq_id]
    rfl
  · rw [diag_eq_norm_sq, diag_eq_norm_sq, map_smul, norm_smul]
    push_cast
    ring
  · rw [measureReal_eq_norm_sq, measureReal_eq_norm_sq, measureReal_eq_norm_sq, map_add]
    have h := norm_add_le (E B φ) (E B ψ)
    have h2 : ‖E B φ + E B ψ‖ ^ 2 ≤ (‖E B φ‖ + ‖E B ψ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖E B φ‖ - ‖E B ψ‖)]
  · refine LinearMap.ext fun ψ => ?_
    have h := norm_sq_empty E ψ
    simpa using h
  · intro B B' hs hB
    rw [isNull_iff_diagMeasure] at hB ⊢
    exact fun ψ => measure_mono_null hs (hB ψ)
  · intro ι _ B hB
    rw [isNull_iff_diagMeasure]
    exact fun ψ => measure_iUnion_null fun i => (isNull_iff_diagMeasure E (B i)).1 (hB i) ψ
  · obtain ⟨C, hC⟩ := hb
    obtain ⟨A, hA, hn⟩ := exists_weakIntegral E f hf hC
    refine ⟨⟨A, hA, fun A' hA' => weakIntegral_unique E f hA' hA⟩, fun A' hA' ψ => ?_⟩
    rw [weakIntegral_unique E f hA' hA]
    exact hn ψ
end YangMills.Construction.EuclideanSpectral
