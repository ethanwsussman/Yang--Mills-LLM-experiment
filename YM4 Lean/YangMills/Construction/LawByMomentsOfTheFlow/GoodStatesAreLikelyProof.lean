import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesAreLikely
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCurvatureNearThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.NoHullNearThePoint
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages
section Parameters
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ∀ Λ, Q₁ Λ → Q₂ Λ)
    (h₁ : ForAllHullParameters Q₁) : ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p16214 <;> assumption
private theorem forAllHullParameters_of_forAllParameters {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllParameters_admissible_floorMin_le :
    ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
end Parameters
section RealBounds
private theorem one_add_sqrt_mul_pow_le {x v T Z : ℝ} {k κ Q : ℕ} (hx : 1 ≤ x) (hv : 0 ≤ v) (hT : 1 ≤ T)
    (hk : k ≤ κ) (hκ : κ ≤ 2 * Q) (hZ : v ^ (2 * Q) ≤ Z) :
    (1 + x ^ ((1 : ℝ) / 2) * v) ^ k ≤ (2 * T) ^ κ + 2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q * Z := by apply _root_.YangMills.SharedProofs.p20252 <;> assumption
private theorem clusterRange_bounds {x : ℝ} (hx : (8 : ℝ) ^ 100 ≤ x) :
    (8 : ℝ) ≤ (clusterRange x : ℝ) ∧ (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by apply _root_.YangMills.SharedProofs.p89177 <;> assumption
private theorem clusterRange_pow_eight_le {x : ℝ} (hx : (8 : ℝ) ^ 100 ≤ x) :
    (clusterRange x : ℝ) ^ 8 ≤ 256 * x ^ ((2 : ℝ) / 25) := by apply _root_.YangMills.SharedProofs.p28510 <;> assumption
private theorem plaquetteCount_le {x : ℝ} (hx : (8 : ℝ) ^ 100 ≤ x) :
    ((16 * (2 * (2 * (clusterRange x) ^ 2) + 1) ^ 4 : ℕ) : ℝ) ≤ 2560000 * x ^ ((2 : ℝ) / 25) := by apply _root_.YangMills.SharedProofs.p40573 <;> assumption
private theorem tail_bound_le {x c CH Cq Pc : ℝ} (N : ℕ) (hx : 1 ≤ x) (hc : 0 < c) (hCH : 0 ≤ CH) (hCq : 0 ≤ Cq)
    (hP : Pc ≤ 2560000 * x ^ ((2 : ℝ) / 25)) :
    2 * (CH * Real.exp (-(c * x))) + Pc * (Cq * x ^ (-((2 * N + 2 : ℕ) : ℝ)) / (x ^ (-(1 / 4) : ℝ)) ^ (2 * (2 * N + 2))) ≤
      (2 * CH * ((N.factorial : ℝ) / c ^ N) + 2560000 * Cq) * x ^ (-(N : ℝ)) := by apply _root_.YangMills.SharedProofs.p108377 <;> assumption
private theorem moment_bound_le {x c CH Cq Pc : ℝ} (k : ℕ) (hx : 1 ≤ x) (hc : 0 < c) (hCH : 0 ≤ CH) (hCq : 0 ≤ Cq)
    (hP : Pc ≤ 2560000 * x ^ ((2 : ℝ) / 25)) :
    1 ≤ x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ))) ∧
    (2 * x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ)))) ^ (k + 1) +
        2 ^ (k + 1) * (x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ)))) ^ (k + 1) /
          (x ^ ((1 : ℝ) / (4000 * ((k + 1 : ℕ) : ℝ)))) ^ (2 * (201 * (k + 1))) * x ^ (201 * (k + 1)) *
          (Pc * (Cq * x ^ (-((201 * (k + 1) : ℕ) : ℝ)))) +
        (1 + x ^ ((1 : ℝ) / 4)) ^ (k + 1) * (CH * Real.exp (-(c * x))) ≤
      2 ^ (k + 1) * (1 + 2560000 * Cq + CH * (((k + 1).factorial : ℝ) / c ^ (k + 1))) * x ^ ((1 : ℝ) / 4000) := by apply _root_.YangMills.SharedProofs.p80063 <;> assumption
end RealBounds
section MeasureBounds
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measure_inter_lt_le {G : Set Ω} (hG : MeasurableSet G) {X : Ω → ℝ} (hX : Measurable X)
    {a b : ℝ} (ha : 0 < a) (q : ℕ)
    (h : ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal (X ω ^ (2 * q))) ω ∂μ ≤ ENNReal.ofReal b) :
    μ (G ∩ {ω | a < X ω}) ≤ ENNReal.ofReal (b / a ^ (2 * q)) := by
  have hf : Measurable (G.indicator fun ω => ENNReal.ofReal (X ω ^ (2 * q))) :=
    ((hX.pow_const _).ennreal_ofReal).indicator hG
  have haq : 0 < a ^ (2 * q) := by positivity
  have hm := mul_meas_ge_le_lintegral (μ := μ) hf (ENNReal.ofReal (a ^ (2 * q)))
  have hsub : G ∩ {ω | a < X ω} ⊆
      {ω | ENNReal.ofReal (a ^ (2 * q)) ≤ G.indicator (fun ω => ENNReal.ofReal (X ω ^ (2 * q))) ω} := by
    rintro ω ⟨hω, hlt⟩
    show ENNReal.ofReal (a ^ (2 * q)) ≤ G.indicator (fun ω => ENNReal.ofReal (X ω ^ (2 * q))) ω
    rw [Set.indicator_of_mem hω]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha.le (le_of_lt hlt) _)
  have h1 : ENNReal.ofReal (a ^ (2 * q)) * μ (G ∩ {ω | a < X ω}) ≤ ENNReal.ofReal b :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hm.trans h)
  rw [ENNReal.ofReal_div_of_pos haq]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using haq)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h1
private theorem measure_iUnion_lt_le {Ω' ι : Type} [MeasurableSpace Ω'] {ν : Measure Ω'} {db : Ω → Ω'}
    (hdb : Measurable db) (hmap : Measure.map db μ = ν) (P : Finset ι) {X : ι → Ω' → ℝ} (hX : ∀ p, Measurable (X p))
    {G : Set Ω} (hG : MeasurableSet G) {a b ε : ℝ} (ha : 0 < a) (q : ℕ) (hGc : μ Gᶜ ≤ ENNReal.ofReal ε)
    (hM : ∀ p ∈ P, ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal (X p (db ω) ^ (2 * q))) ω ∂μ ≤ ENNReal.ofReal b) :
    ν (⋃ p ∈ P, {w | a < X p w}) ≤ ENNReal.ofReal ε + ∑ _p ∈ P, ENNReal.ofReal (b / a ^ (2 * q)) := by
  have hB : MeasurableSet (⋃ p ∈ P, {w | a < X p w}) :=
    Finset.measurableSet_biUnion _ fun p _ => measurableSet_lt measurable_const (hX p)
  rw [← hmap, Measure.map_apply hdb hB]
  have hsub : db ⁻¹' (⋃ p ∈ P, {w | a < X p w}) ⊆ Gᶜ ∪ ⋃ p ∈ P, (G ∩ {ω | a < X p (db ω)}) := by
    intro ω hω
    by_cases hg : ω ∈ G
    · right
      simp only [Set.mem_preimage, Set.mem_iUnion] at hω ⊢
      obtain ⟨p, hp, h⟩ := hω
      exact ⟨p, hp, hg, h⟩
    · left
      exact hg
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine add_le_add hGc ((measure_biUnion_finset_le _ _).trans ?_)
  exact Finset.sum_le_sum fun p hp => measure_inter_lt_le hG ((hX p).comp hdb) ha q (hM p hp)
private theorem lintegral_indicator_one_add_pow_le [IsProbabilityMeasure μ] {Ω' ι : Type} [MeasurableSpace Ω']
    {ν : Measure Ω'} {db : Ω → Ω'}
    (hmap : Measure.map db μ = ν) (hdb : Measurable db) (P : Finset ι) {X : ι → Ω' → ℝ} (hX : ∀ p, Measurable (X p))
    (hX0 : ∀ p w, 0 ≤ X p w)
    {G : Set Ω} (hG : MeasurableSet G) {E : Set Ω'} {v : Ω' → ℝ} {x T b ε : ℝ} {k κ Q : ℕ} (hx : 1 ≤ x) (hT : 1 ≤ T)
    (hk : k ≤ κ) (hκ : κ ≤ 2 * Q) (hv0 : ∀ w, 0 ≤ v w) (hvE : ∀ w ∈ E, v w ≤ x ^ (-(1 / 4) : ℝ))
    (hvZ : ∀ w, v w ^ (2 * Q) ≤ ∑ p ∈ P, X p w ^ (2 * Q)) (hGc : μ Gᶜ ≤ ENNReal.ofReal ε)
    (hM : ∀ p ∈ P, ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal (X p (db ω) ^ (2 * Q))) ω ∂μ ≤ ENNReal.ofReal b) :
    ∫⁻ w, E.indicator (fun w => ENNReal.ofReal ((1 + x ^ ((1 : ℝ) / 2) * v w) ^ k)) w ∂ν ≤
      ENNReal.ofReal ((2 * T) ^ κ) + (ENNReal.ofReal (2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q) *
          ∑ _p ∈ P, ENNReal.ofReal b + ENNReal.ofReal ((1 + x ^ ((1 : ℝ) / 4)) ^ κ) * ENNReal.ofReal ε) := by
  have hx0 : 0 < x := by linarith
  rw [← hmap]
  refine (lintegral_map_le _ _).trans ?_
  have hind : ∀ p, Measurable (G.indicator fun ω => ENNReal.ofReal (X p (db ω) ^ (2 * Q))) := fun p =>
    ((((hX p).comp hdb).pow_const _).ennreal_ofReal).indicator hG
  have hpt : ∀ ω, E.indicator (fun w => ENNReal.ofReal ((1 + x ^ ((1 : ℝ) / 2) * v w) ^ k)) (db ω) ≤
      ENNReal.ofReal ((2 * T) ^ κ) + (ENNReal.ofReal (2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q) *
        (∑ p ∈ P, G.indicator (fun ω => ENNReal.ofReal (X p (db ω) ^ (2 * Q))) ω) +
        ENNReal.ofReal ((1 + x ^ ((1 : ℝ) / 4)) ^ κ) * Gᶜ.indicator 1 ω) := by
    intro ω
    by_cases hE : db ω ∈ E
    · rw [Set.indicator_of_mem hE]
      by_cases hg : ω ∈ G
      · have hZ := hvZ (db ω)
        have hr := one_add_sqrt_mul_pow_le hx (hv0 (db ω)) hT hk hκ hZ
        have hB0 : 0 ≤ 2 ^ κ * T ^ κ / T ^ (2 * Q) * x ^ Q := by positivity
        have hS0 : 0 ≤ ∑ p ∈ P, X p (db ω) ^ (2 * Q) := Finset.sum_nonneg fun p _ => pow_nonneg (hX0 p _) _
        have e1 : ∑ p ∈ P, G.indicator (fun ω => ENNReal.ofReal (X p (db ω) ^ (2 * Q))) ω =
            ENNReal.ofReal (∑ p ∈ P, X p (db ω) ^ (2 * Q)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ => pow_nonneg (hX0 p _) _]
          exact Finset.sum_congr rfl fun p _ => Set.indicator_of_mem hg _
        rw [e1]
        refine (ENNReal.ofReal_le_ofReal hr).trans ?_
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hB0 hS0), ENNReal.ofReal_mul hB0]
        gcongr
        exact le_self_add
      · have hs : x ^ ((1 : ℝ) / 2) * v (db ω) ≤ x ^ ((1 : ℝ) / 4) := by
          have h1 := mul_le_mul_of_nonneg_left (hvE _ hE) (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2))
          refine h1.trans (le_of_eq ?_)
          rw [← Real.rpow_add hx0]
          norm_num
        have hs0 : 0 ≤ x ^ ((1 : ℝ) / 2) * v (db ω) := mul_nonneg (by positivity) (hv0 _)
        have h2 : (1 + x ^ ((1 : ℝ) / 2) * v (db ω)) ^ k ≤ (1 + x ^ ((1 : ℝ) / 4)) ^ κ :=
          (pow_le_pow_right₀ (by linarith) hk).trans (pow_le_pow_left₀ (by linarith) (by linarith) κ)
        have e2 : Gᶜ.indicator (1 : Ω → ENNReal) ω = 1 := Set.indicator_of_mem (show ω ∈ Gᶜ from hg) _
        rw [e2, mul_one]
        refine (ENNReal.ofReal_le_ofReal h2).trans ?_
        exact le_add_self.trans le_add_self
    · rw [Set.indicator_of_notMem hE]
      exact zero_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_add_left ((Finset.measurable_sum _ fun p _ => hind p).const_mul _),
    lintegral_const_mul _ (Finset.measurable_sum _ fun p _ => hind p),
    lintegral_finsetSum _ fun p _ => hind p,
    lintegral_const_mul _ (measurable_one.indicator hG.compl), lintegral_indicator_one hG.compl]
  gcongr with p hp
  exact hM p hp
private theorem lintegral_indicator_le_of_sq_le {E : Set Ω} (hE : MeasurableSet E) {f h : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) {ε M p : ℝ}
    (hε : 0 < ε) (hM0 : 0 ≤ M) (hp0 : 0 ≤ p) (hfh : ∀ᵐ ω ∂μ, f ω ^ 2 ≤ h ω)
    (hh : ∫⁻ ω, ENNReal.ofReal (h ω) ∂μ ≤ ENNReal.ofReal M) (hEp : μ E ≤ ENNReal.ofReal p) :
    ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal (f ω)) ω ∂μ ≤ ENNReal.ofReal (ε / 2 * M + 1 / (2 * ε) * p) := by
  have hpt : ∀ᵐ ω ∂μ, E.indicator (fun ω => ENNReal.ofReal (f ω)) ω ≤
      ENNReal.ofReal (ε / 2) * ENNReal.ofReal (h ω) + ENNReal.ofReal (1 / (2 * ε)) * E.indicator 1 ω := by
    filter_upwards [hfh] with ω hω
    have hh0 : 0 ≤ h ω := (sq_nonneg _).trans hω
    by_cases hg : ω ∈ E
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, mul_one, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have key : f ω ≤ ε / 2 * f ω ^ 2 + 1 / (2 * ε) := by
        have h2 : 0 ≤ (ε * f ω - 1) ^ 2 / (2 * ε) := by positivity
        have e : ε / 2 * f ω ^ 2 + 1 / (2 * ε) - f ω = (ε * f ω - 1) ^ 2 / (2 * ε) := by field_simp; ring
        linarith
      have h3 : ε / 2 * f ω ^ 2 ≤ ε / 2 * h ω := by gcongr
      linarith
    · rw [Set.indicator_of_notMem hg]
      exact zero_le
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_add_right _ (measurable_one.indicator hE |>.const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ (measurable_one.indicator hE),
    lintegral_indicator_one hE, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  gcongr
private theorem sum_ofReal_const_le {ι : Type} (P : Finset ι) {c Pc : ℝ} (hc : 0 ≤ c) (hP : (P.card : ℝ) ≤ Pc) :
    ∑ _p ∈ P, ENNReal.ofReal c ≤ ENNReal.ofReal (Pc * c) := by
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by gcongr)
end MeasureBounds
section NearPlaquettes
variable {m : ℕ} [NeZero m]
open Classical in
private def plaquettesNear (o : TorusSite m) (R : ℝ) : Finset (OrientedPlaquette m) :=
  Finset.univ.filter fun p => (TorusFields.supDist p.1.1 o : ℝ) ≤ R
private theorem supBall_card_le (o : TorusSite m) (R : ℕ) : (supBall o (R : ℝ)).card ≤ (2 * R + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p9908 <;> assumption
private theorem plaquettesNear_card_le (o : TorusSite m) (R : ℕ) :
    (plaquettesNear o (R : ℝ)).card ≤ 16 * (2 * R + 1) ^ 4 := by
  classical
  have hinj : Set.InjOn (fun p : OrientedPlaquette m => ((p.1.1, p.1.2) : TorusSite m × Fin 4 × Fin 4))
      (plaquettesNear o (R : ℝ) : Set (OrientedPlaquette m)) := by
    intro p _ p' _ h
    exact Subtype.ext h
  have hmaps : ∀ p ∈ plaquettesNear o (R : ℝ), ((p.1.1, p.1.2) : TorusSite m × Fin 4 × Fin 4) ∈
      supBall o (R : ℝ) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4)) := by
    intro p hp
    have := (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩, Finset.mem_univ _⟩
  have h := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  have := supBall_card_le o R
  nlinarith
private theorem boxCurvature_eq_zero_or (o : TorusSite m) (R : ℝ) (W : TorusField m) :
    boxCurvature o R W = 0 ∨
      ∃ p ∈ plaquettesNear o R, boxCurvature o R W = curvature W p.1.1 p.1.2.1 p.1.2.2 := by
  classical
  unfold boxCurvature
  by_cases hE : IsEmpty {p : TorusPlaquette m // PlaquetteInBox o R p}
  · left
    exact Real.iSup_of_isEmpty _
  · rw [not_isEmpty_iff] at hE
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
      (f := fun p : {p : TorusPlaquette m // PlaquetteInBox o R p} => curvature W p.1.1 p.1.2.1 p.1.2.2)
    right
    refine ⟨⟨i.1, i.2.1⟩, ?_, hi.symm⟩
    have h0 := i.2.2 i.1.1 (by simp [plaquetteVertices])
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.mp h0).2⟩
omit [NeZero m] in
private theorem curvature_nonneg' (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) : 0 ≤ curvature W x μ ν :=
  norm_nonneg _
private theorem boxCurvature_nonneg (o : TorusSite m) (R : ℝ) (W : TorusField m) : 0 ≤ boxCurvature o R W :=
  Real.iSup_nonneg fun _ => curvature_nonneg' _ _ _ _
private theorem boxCurvature_pow_le (o : TorusSite m) (R : ℝ) (W : TorusField m) {j : ℕ} (hj : j ≠ 0) :
    boxCurvature o R W ^ j ≤ ∑ p ∈ plaquettesNear o R, curvature W p.1.1 p.1.2.1 p.1.2.2 ^ j := by
  have hnn : ∀ p ∈ plaquettesNear o R, 0 ≤ curvature W p.1.1 p.1.2.1 p.1.2.2 ^ j :=
    fun p _ => pow_nonneg (curvature_nonneg' _ _ _ _) _
  rcases boxCurvature_eq_zero_or o R W with h | ⟨p, hp, h⟩
  · rw [h, zero_pow hj]
    exact Finset.sum_nonneg hnn
  · rw [h]
    exact Finset.single_le_sum hnn hp
omit [NeZero m] in
private theorem measurable_curvature_comp {Ω₀ : Type} [MeasurableSpace Ω₀] {V : Ω₀ → TorusField m}
    (hV : Measurable V) (x : TorusSite m) (μ ν : Fin 4) : Measurable fun a => curvature (V a) x μ ν := by apply _root_.YangMills.SharedProofs.p85954 <;> assumption
end NearPlaquettes
section AtPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem state_fst_eq_topField (u n : ℕ) [NeZero n] (w : MarkedSample Λ.stepParams u n) :
    (S.state u n w).1 = topField Λ.stepParams u n w := by
  cases u <;> rfl
variable (hq : ∀ (s n : ℕ) [NeZero n], Measurable (stageState S.tower s n))
include hq in
private theorem measurable_topField (u n : ℕ) [NeZero n] : Measurable (topField Λ.stepParams u n) := by
  have h : topField Λ.stepParams u n = fun w => (stageState S.tower u n w).1 :=
    funext fun w => (state_fst_eq_topField S u n w).symm
  rw [h]
  exact measurable_fst.comp (hq u n)
include hq in
private theorem measurableSet_disjoint_lumps (s n : ℕ) [NeZero n] (B : Finset (TorusSite n)) :
    MeasurableSet {w : MarkedSample Λ.stepParams s n | Disjoint (stageState S.tower s n w).2.1 B} := by
  have e : {w : MarkedSample Λ.stepParams s n | Disjoint (stageState S.tower s n w).2.1 B} =
      ⋃ a ∈ {a : Finset (TorusSite n) | Disjoint a B},
        {w : MarkedSample Λ.stepParams s n | (stageState S.tower s n w).2.1 = a} := by
    ext w
    simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (measurable_snd.comp (hq s n)) (measurableSet_sigma_fst_eq a)
include hq in
private theorem measurableSet_noLumpNear (v : ℕ) (ρ : ℝ) : ∀ (d n : ℕ) [NeZero n],
    MeasurableSet {w : MarkedSample Λ.stepParams (v + d) n | S.NoLumpNear v ρ d n w}
  | 0, n, _ => measurableSet_disjoint_lumps S hq v n _
  | d + 1, n, _ => by
    have h1 := measurableSet_disjoint_lumps S hq (v + d + 1) n (supBall (S.originSite (v + d + 1) n) ρ)
    have h2 := measurableSet_noLumpNear v ρ d (n * Λ.stepParams.side)
    exact h1.inter (measurable_fst h2)
include hq in
private theorem measurableSet_isGoodConfig (u n : ℕ) [NeZero n] :
    MeasurableSet {w : MarkedSample Λ.stepParams u n | S.IsGoodConfig u n (S.state u n w).1 (S.state u n w).2.1} := by
  have hv : Measurable fun w : MarkedSample Λ.stepParams u n => S.localCurvature u n (S.state u n w).1 := by
    have hV : Measurable fun w : MarkedSample Λ.stepParams u n => (S.state u n w).1 := measurable_fst.comp (hq u n)
    exact Measurable.iSup fun p => measurable_curvature_comp hV _ _ _
  have e : {w : MarkedSample Λ.stepParams u n | S.IsGoodConfig u n (S.state u n w).1 (S.state u n w).2.1} =
      {w | Disjoint (stageState S.tower u n w).2.1 (supBall (S.originSite u n) (8 * S.rangeSq))} ∩
        {w | S.localCurvature u n (S.state u n w).1 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)} := by
    ext w
    exact ⟨fun h => ⟨h.disjoint_lumps, h.curvature_le⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [e]
  exact (measurableSet_disjoint_lumps S hq u n _).inter (measurableSet_le hv measurable_const)
include hq in
private theorem good_bounds_at_level (u d n : ℕ) [NeZero n] [IsProbabilityMeasure (S.law (u + d) n)]
    (hdb : Measurable (sampleBelow Λ.stepParams u d n))
    (hmap : Measure.map (sampleBelow Λ.stepParams u d n) (S.law (u + d) n) =
      S.law u (fineSide Λ.stepParams.side d n))
    (hx : 1 ≤ S.scaleCoupling) (h8 : 8 * (S.rangeSq : ℝ) ≤ (S.range : ℝ) ^ 3) {ε : ℝ} {Cq : ℕ → ℝ}
    (hCq : ∀ q, 0 ≤ Cq q) (hε : 0 ≤ ε)
    (hH₂ : S.law (u + d) n {w | ¬ S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w} ≤ ENNReal.ofReal ε)
    (hM : ∀ p : OrientedPlaquette (fineSide Λ.stepParams.side d n),
      (TorusFields.supDist p.1.1 (S.originSite u (fineSide Λ.stepParams.side d n)) : ℝ) ≤ 4 * (S.range : ℝ) ^ 2 →
      ∀ q : ℕ, 1 ≤ q →
        ∫⁻ w, Set.indicator {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w}
            (fun w => ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n)
              (sampleBelow Λ.stepParams u d n w)) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))) w ∂(S.law (u + d) n) ≤
          ENNReal.ofReal (Cq q * S.scaleCoupling ^ (-(q : ℝ))))
    (m : ℕ) [NeZero m] (hm : fineSide Λ.stepParams.side d n = m)
    (hH₁ : S.law u m {w | ¬ Disjoint (S.state u m w).2.1 (supBall (S.originSite u m) ((S.range : ℝ) ^ 3))} ≤
      ENNReal.ofReal ε) :
    (∀ q : ℕ, 1 ≤ q → S.law u m {w | ¬ S.IsGoodConfig u m (S.state u m w).1 (S.state u m w).2.1} ≤
        ENNReal.ofReal (2 * ε + ((16 * (2 * (2 * S.rangeSq) + 1) ^ 4 : ℕ) : ℝ) *
          (Cq q * S.scaleCoupling ^ (-(q : ℝ)) / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * q)))) ∧
    (∀ (k κ Q : ℕ) (T : ℝ), 1 ≤ Q → 1 ≤ T → k ≤ κ → κ ≤ 2 * Q →
      ∫⁻ w, Set.indicator {w | S.IsGoodConfig u m (S.state u m w).1 (S.state u m w).2.1}
          (fun w => ENNReal.ofReal ((1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
            S.localCurvature u m (S.state u m w).1) ^ k)) w ∂(S.law u m) ≤
        ENNReal.ofReal ((2 * T) ^ κ + 2 ^ κ * T ^ κ / T ^ (2 * Q) * S.scaleCoupling ^ Q *
            (((16 * (2 * (2 * S.rangeSq) + 1) ^ 4 : ℕ) : ℝ) * (Cq Q * S.scaleCoupling ^ (-(Q : ℝ)))) +
          (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ κ * ε)) := by
  subst hm
  have hx0 : 0 < S.scaleCoupling := by linarith
  have ha : 0 < S.scaleCoupling ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hcard : ((plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))).card : ℝ) ≤
      ((16 * (2 * (2 * S.rangeSq) + 1) ^ 4 : ℕ) : ℝ) := by
    have h := plaquettesNear_card_le (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * S.rangeSq)
    rw [Nat.cast_mul, Nat.cast_ofNat] at h
    exact_mod_cast h
  have hG : MeasurableSet {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w} := measurableSet_noLumpNear S hq u _ d n
  have hGc : S.law (u + d) n {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w}ᶜ ≤ ENNReal.ofReal ε := hH₂
  have hX : ∀ p : OrientedPlaquette (fineSide Λ.stepParams.side d n),
      Measurable fun w => curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n) w)
        p.1.1 p.1.2.1 p.1.2.2 :=
    fun p => measurable_curvature_comp (measurable_topField S hq u _) _ _ _
  have hMP : ∀ p ∈ plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ)),
      ∀ q : ℕ, 1 ≤ q →
      ∫⁻ w, Set.indicator {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w}
            (fun w => ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n)
              (sampleBelow Λ.stepParams u d n w)) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))) w ∂(S.law (u + d) n) ≤
          ENNReal.ofReal (Cq q * S.scaleCoupling ^ (-(q : ℝ))) := by
    intro p hp q hq1
    refine hM p ?_ q hq1
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 : (S.rangeSq : ℝ) = (S.range : ℝ) ^ 2 := by simp [MomentPoint.rangeSq]
    have h3 : 0 ≤ (S.range : ℝ) ^ 2 := by positivity
    rw [h2] at h1
    linarith
  refine ⟨fun q hq1 => ?_, fun k κ Q T hQ hT hk hκ => ?_⟩
  · have hb0 : 0 ≤ Cq q * S.scaleCoupling ^ (-(q : ℝ)) / (S.scaleCoupling ^ (-(1 / 4) : ℝ)) ^ (2 * q) :=
      div_nonneg (mul_nonneg (hCq q) (by positivity)) (by positivity)
    have hhit := measure_iUnion_lt_le hdb hmap
      (plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))) hX hG ha q hGc
      (fun p hp => hMP p hp q hq1)
    have hsub : {w | ¬ S.IsGoodConfig u (fineSide Λ.stepParams.side d n) (S.state u _ w).1 (S.state u _ w).2.1} ⊆
        {w | ¬ Disjoint (S.state u (fineSide Λ.stepParams.side d n) w).2.1
            (supBall (S.originSite u (fineSide Λ.stepParams.side d n)) ((S.range : ℝ) ^ 3))} ∪
          ⋃ p ∈ plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ)),
            {w | S.scaleCoupling ^ (-(1 / 4) : ℝ) <
              curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n) w) p.1.1 p.1.2.1 p.1.2.2} := by
      intro w hw
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      apply hw
      refine ⟨?_, ?_⟩
      · have h3 : Disjoint (S.state u (fineSide Λ.stepParams.side d n) w).2.1
            (supBall (S.originSite u (fineSide Λ.stepParams.side d n)) ((S.range : ℝ) ^ 3)) := not_not.mp h1
        refine h3.mono_right fun z hz => ?_
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.trans h8⟩
      · by_contra hs
        rw [not_le] at hs
        rcases boxCurvature_eq_zero_or (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))
            (S.state u _ w).1 with h0 | ⟨p, hp, h0⟩
        · have : S.localCurvature u (fineSide Λ.stepParams.side d n) (S.state u _ w).1 = 0 := h0
          rw [this] at hs
          linarith
        · apply h2
          simp only [Set.mem_iUnion]
          refine ⟨p, hp, ?_⟩
          have e : S.localCurvature u (fineSide Λ.stepParams.side d n) (S.state u _ w).1 =
              curvature (S.state u (fineSide Λ.stepParams.side d n) w).1 p.1.1 p.1.2.1 p.1.2.2 := h0
          rw [e, state_fst_eq_topField] at hs
          exact hs
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add hH₁ hhit).trans ?_
    have hs := sum_ofReal_const_le
      (plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))) hb0 hcard
    rw [show 2 * ε = ε + ε by ring, ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) hb0),
      ENNReal.ofReal_add hε hε, add_assoc]
    gcongr
  · have hb0 : 0 ≤ Cq Q * S.scaleCoupling ^ (-(Q : ℝ)) := mul_nonneg (hCq Q) (by positivity)
    have hmom := lintegral_indicator_one_add_pow_le
      (E := {w | S.IsGoodConfig u (fineSide Λ.stepParams.side d n) (S.state u _ w).1 (S.state u _ w).2.1})
      (v := fun w => S.localCurvature u (fineSide Λ.stepParams.side d n) (S.state u _ w).1) hmap hdb
      (plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))) hX
      (fun _ _ => curvature_nonneg' _ _ _ _) hG hx hT hk hκ
      (fun w => boxCurvature_nonneg _ _ _) (fun w hw => hw.curvature_le)
      (fun w => by
        have h := boxCurvature_pow_le (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))
          (S.state u _ w).1 (j := 2 * Q) (by omega)
        rw [state_fst_eq_topField] at h
        simpa only [MomentPoint.localCurvature, state_fst_eq_topField] using h)
      hGc (fun p hp => hMP p hp Q hQ)
    refine hmom.trans ?_
    have hB0 : 0 ≤ 2 ^ κ * T ^ κ / T ^ (2 * Q) * S.scaleCoupling ^ Q := by positivity
    have hs := sum_ofReal_const_le
      (plaquettesNear (S.originSite u (fineSide Λ.stepParams.side d n)) (2 * (S.rangeSq : ℝ))) hb0 hcard
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hB0, ENNReal.ofReal_mul (by positivity), add_assoc]
    gcongr
    rw [ENNReal.ofReal_mul (by positivity)]
private def badMassConstant (CM : ℕ → ℝ) (CH c : ℝ) (N : ℕ) : ℝ :=
  2 * CH * ((N.factorial : ℝ) / c ^ N) + 2560000 * |CM (2 * N + 2)|
private def goodMomentConstant (CM : ℕ → ℝ) (CH c : ℝ) (k : ℕ) : ℝ :=
  2 ^ (k + 1) * (1 + 2560000 * |CM (201 * (k + 1))| + CH * (((k + 1).factorial : ℝ) / c ^ (k + 1)))
include hq in
private theorem good_bounds_in_window (hprob : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (S.law s n))
    (hbelow : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
      Measure.map (sampleBelow Λ.stepParams s d n) (S.law (s + d) n) = S.law s (fineSide Λ.stepParams.side d n))
    (hx : (8 : ℝ) ^ 100 ≤ S.scaleCoupling) (hK : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel)
    {CM : ℕ → ℝ} {CH c : ℝ} (hc : 0 < c)
    (hM : ∀ (u d n : ℕ) [NeZero n], S.lastSeparated ≤ u → u ≤ S.lastSeparated + S.logIndex + 2 →
      u + d = S.lastSeparated + 2 * S.logIndex + 3 → n = S.levelSide (u + d) →
      ∀ p : OrientedPlaquette (fineSide Λ.stepParams.side d n),
      (TorusFields.supDist p.1.1 (S.originSite u (fineSide Λ.stepParams.side d n)) : ℝ) ≤ 4 * (S.range : ℝ) ^ 2 →
      ∀ q : ℕ, 1 ≤ q →
        ∫⁻ w, Set.indicator {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w}
            (fun w => ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n)
              (sampleBelow Λ.stepParams u d n w)) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))) w ∂(S.law (u + d) n) ≤
          ENNReal.ofReal (CM q * S.scaleCoupling ^ (-(q : ℝ))))
    (hH₁ : ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 →
      S.law u (S.levelSide u) {w | ¬ Disjoint (S.state u (S.levelSide u) w).2.1
        (supBall (S.originSite u (S.levelSide u)) ((S.range : ℝ) ^ 3))} ≤
        ENNReal.ofReal (CH * Real.exp (-(c * S.scaleCoupling))))
    (hH₂ : ∀ (u d n : ℕ) [NeZero n], S.lastSeparated ≤ u → u + d = S.lastSeparated + 2 * S.logIndex + 3 →
      n = S.levelSide (u + d) →
      S.law (u + d) n {w | ¬ S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w} ≤
        ENNReal.ofReal (CH * Real.exp (-(c * S.scaleCoupling))))
    (u : ℕ) (hu₁ : S.lastSeparated ≤ u) (hu₂ : u ≤ S.lastSeparated + S.logIndex + 1) :
    (∀ N : ℕ, S.law u (S.levelSide u)
        {w | ¬ S.IsGoodConfig u (S.levelSide u) (S.state u (S.levelSide u) w).1 (S.state u (S.levelSide u) w).2.1} ≤
      ENNReal.ofReal (badMassConstant CM |CH| c N * S.scaleCoupling ^ (-(N : ℝ)))) ∧
    ∀ k : ℕ, ∫⁻ w, Set.indicator
        {w | S.IsGoodConfig u (S.levelSide u) (S.state u (S.levelSide u) w).1 (S.state u (S.levelSide u) w).2.1}
        (fun w => ENNReal.ofReal ((1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
          S.localCurvature u (S.levelSide u) (S.state u (S.levelSide u) w).1) ^ k)) w
        ∂(S.law u (S.levelSide u)) ≤
        ENNReal.ofReal (goodMomentConstant CM |CH| c k * S.scaleCoupling ^ ((1 : ℝ) / 4000)) := by
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (one_le_pow₀ (by norm_num)) hx
  have hr := clusterRange_bounds hx
  have hr8 : (8 : ℝ) ≤ (S.range : ℝ) := hr.1
  have h8 : 8 * (S.rangeSq : ℝ) ≤ (S.range : ℝ) ^ 3 := by
    have h2 : (S.rangeSq : ℝ) = (S.range : ℝ) ^ 2 := by simp [MomentPoint.rangeSq]
    rw [h2]
    have : 0 ≤ (S.range : ℝ) ^ 2 := by positivity
    nlinarith
  have hP := plaquetteCount_le hx
  obtain ⟨d, hud⟩ : ∃ d, u + d = S.lastSeparated + 2 * S.logIndex + 3 :=
    ⟨S.lastSeparated + 2 * S.logIndex + 3 - u, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, n = S.levelSide (u + d) := ⟨_, rfl⟩
  have : NeZero n := by
    rw [hn]
    infer_instance
  have hm : fineSide Λ.stepParams.side d n = S.levelSide u := by
    rw [fineSide_eq, hn]
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + d)) *
        Λ.stepParams.side ^ d = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u)
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have := hprob (u + d) n
  obtain ⟨hdb, hmap⟩ := hbelow u d n
  have hε0 : 0 ≤ |CH| * Real.exp (-(c * S.scaleCoupling)) := by positivity
  have hle : ENNReal.ofReal (CH * Real.exp (-(c * S.scaleCoupling))) ≤
      ENNReal.ofReal (|CH| * Real.exp (-(c * S.scaleCoupling))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have hx0 : 0 < S.scaleCoupling := by linarith
  have W := good_bounds_at_level S hq u d n hdb hmap hx1 h8 (Cq := fun q => |CM q|) (fun _ => abs_nonneg _) hε0
    ((hH₂ u d n hu₁ hud hn).trans hle)
    (fun p hp q hq1 => (hM u d n hu₁ (by omega) hud hn p hp q hq1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))))
    (S.levelSide u) hm ((hH₁ u hu₁ (by omega)).trans hle)
  refine ⟨fun N => ?_, fun k => ?_⟩
  · refine (W.1 (2 * N + 2) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact tail_bound_le N hx1 hc (abs_nonneg _) (abs_nonneg _) hP
  · obtain ⟨hT, hb⟩ := moment_bound_le (x := S.scaleCoupling) (c := c) (CH := |CH|)
      (Cq := |CM (201 * (k + 1))|) k hx1 hc (abs_nonneg _) (abs_nonneg _) hP
    refine (W.2 k (k + 1) (201 * (k + 1)) _ (by omega) hT (by omega) (by omega)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact hb
end AtPoint
private def productMomentConstant (c₀ CS CN : ℝ) (k : ℕ) : ℝ :=
  (1 + |c₀| * |CS|) ^ (2 * k) * 256 ^ k * (1 + (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6)
private theorem lintegral_indicator_prod_le {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {k : ℕ} {E : Set Ω}
    (hE : MeasurableSet E) {F Nn : Fin k → Ω → ℝ} {c₀ CS CN r x C₁ : ℝ} (A : Fin k → ℝ) (hA0 : ∀ i, 0 ≤ A i)
    (hA : ∀ i, A i ≤ CS * r ^ 4) (hr0 : 0 ≤ r) (hr8 : r ^ 8 ≤ 256 * x) (hx : 1 ≤ x)
    (hae : ∀ᵐ ω ∂ν, ∀ i, |F i ω| ≤ c₀ * A i * Nn i ω)
    (hmom : ∀ p : ℕ, 1 ≤ p → ∀ J : List (Fin k), J.length = p →
      ∫⁻ ω, ENNReal.ofReal (J.map fun i => Nn i ω).prod ∂ν ≤ ENNReal.ofReal (CN ^ p * (p.factorial : ℝ) ^ 6))
    (N : ℕ) (hC₁ : 0 ≤ C₁) (hE₁ : ν E ≤ ENNReal.ofReal (C₁ * x ^ (-((2 * N + k : ℕ) : ℝ))))
    (B : Finset (Fin k)) :
    ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal (∏ i ∈ B, |F i ω|)) ω ∂ν ≤
      ENNReal.ofReal ((productMomentConstant c₀ CS CN k + C₁) * x ^ (-(N : ℝ))) := by
  classical
  have hx0 : 0 < x := by linarith
  have hb : B.card ≤ k := by simpa using Finset.card_le_univ B
  set Dn : ℝ := 1 + |c₀| * |CS| with hDn
  have hDn1 : 1 ≤ Dn := by
    have : 0 ≤ |c₀| * |CS| := by positivity
    linarith
  set Mk : ℝ := 1 + (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6 with hMk
  have hMk1 : 1 ≤ Mk := by
    have : 0 ≤ (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6 := by positivity
    linarith
  set G : ℝ := Dn ^ (2 * k) * 256 ^ k with hG
  have hJ : ∀ ω, ((B.toList ++ B.toList).map fun i => Nn i ω).prod = (∏ i ∈ B, Nn i ω) ^ 2 := by
    intro ω
    rw [List.map_append, List.prod_append, Finset.prod_map_toList, sq]
  have hfh : ∀ᵐ ω ∂ν, (∏ i ∈ B, |F i ω|) ^ 2 ≤
      G * x ^ k * ((B.toList ++ B.toList).map fun i => Nn i ω).prod := by
    filter_upwards [hae] with ω hω
    rw [hJ ω, ← Finset.prod_pow]
    have h1 : ∀ i ∈ B, |F i ω| ^ 2 ≤ (Dn * r ^ 4) ^ 2 * Nn i ω ^ 2 := by
      intro i _
      have h2 : |F i ω| ^ 2 ≤ (c₀ * A i * Nn i ω) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hω i) 2
      have h3 : |c₀ * A i| ≤ Dn * r ^ 4 := by
        rw [abs_mul, abs_of_nonneg (hA0 i)]
        have h4 : A i ≤ |CS| * r ^ 4 :=
          (hA i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        calc |c₀| * A i ≤ |c₀| * (|CS| * r ^ 4) := by gcongr
          _ = (|c₀| * |CS|) * r ^ 4 := by ring
          _ ≤ Dn * r ^ 4 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith
      have h5 : (c₀ * A i) ^ 2 ≤ (Dn * r ^ 4) ^ 2 := by
        rw [← sq_abs (c₀ * A i)]
        exact pow_le_pow_left₀ (abs_nonneg _) h3 2
      calc |F i ω| ^ 2 ≤ (c₀ * A i * Nn i ω) ^ 2 := h2
        _ = (c₀ * A i) ^ 2 * Nn i ω ^ 2 := by ring
        _ ≤ (Dn * r ^ 4) ^ 2 * Nn i ω ^ 2 := by gcongr
    have h6 := Finset.prod_le_prod (fun i _ => sq_nonneg |F i ω|) h1
    refine h6.trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
    have h7 : ((Dn * r ^ 4) ^ 2) ^ B.card ≤ G * x ^ k := by
      have e : ((Dn * r ^ 4) ^ 2) ^ B.card = Dn ^ (2 * B.card) * (r ^ 8) ^ B.card := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
        ring_nf
      rw [e, hG, mul_assoc, ← mul_pow]
      have h8 : (r ^ 8) ^ B.card ≤ (256 * x) ^ k :=
        (pow_le_pow_left₀ (by positivity) hr8 _).trans (pow_le_pow_right₀ (by linarith) hb)
      have h9 : Dn ^ (2 * B.card) ≤ Dn ^ (2 * k) := pow_le_pow_right₀ hDn1 (by omega)
      gcongr
    gcongr
  have hint : ∫⁻ ω, ENNReal.ofReal (((B.toList ++ B.toList).map fun i => Nn i ω).prod) ∂ν ≤
      ENNReal.ofReal Mk := by
    by_cases hB : B.card = 0
    · have hB' : B = ∅ := Finset.card_eq_zero.mp hB
      subst hB'
      simp only [Finset.toList_empty, List.append_nil, List.map_nil, List.prod_nil, ENNReal.ofReal_one,
        lintegral_const, measure_univ, mul_one]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hMk1
    · have hl : (B.toList ++ B.toList).length = 2 * B.card := by
        rw [List.length_append, Finset.length_toList]
        ring
      refine (hmom (2 * B.card) (by omega) _ hl).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : CN ^ (2 * B.card) ≤ (1 + |CN|) ^ (2 * k) := by
        have h2 : CN ^ (2 * B.card) ≤ |CN| ^ (2 * B.card) := by
          rw [← abs_pow]
          exact le_abs_self _
        refine h2.trans ((pow_le_pow_left₀ (abs_nonneg _) (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg CN]) (by omega)))
      have h3 : ((2 * B.card).factorial : ℝ) ≤ ((2 * k).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have h4 : ((2 * B.card).factorial : ℝ) ^ 6 ≤ ((2 * k).factorial : ℝ) ^ 6 :=
        pow_le_pow_left₀ (by positivity) h3 6
      have h5 : CN ^ (2 * B.card) * ((2 * B.card).factorial : ℝ) ^ 6 ≤
          (1 + |CN|) ^ (2 * k) * ((2 * k).factorial : ℝ) ^ 6 :=
        mul_le_mul h1 h4 (by positivity) (by positivity)
      linarith
  have hGx : 0 ≤ G * x ^ k := by positivity
  have hh : ∫⁻ ω, ENNReal.ofReal (G * x ^ k * ((B.toList ++ B.toList).map fun i => Nn i ω).prod) ∂ν ≤
      ENNReal.ofReal (G * x ^ k * Mk) := by
    simp_rw [ENNReal.ofReal_mul hGx]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
  have hε : 0 < x ^ (-((N + k : ℕ) : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hc := lintegral_indicator_le_of_sq_le hE (f := fun ω => ∏ i ∈ B, |F i ω|)
    (fun ω => Finset.prod_nonneg fun i _ => abs_nonneg _) hε
    (M := G * x ^ k * Mk) (p := C₁ * x ^ (-((2 * N + k : ℕ) : ℝ))) (by positivity) (by positivity) hfh hh hE₁
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  have a₁ : x ^ (-((N + k : ℕ) : ℝ)) = (x ^ N * x ^ k)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, pow_add]
  have a₂ : x ^ (-((2 * N + k : ℕ) : ℝ)) = (x ^ N * x ^ N * x ^ k)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
  have a₃ : x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
  rw [a₁, a₂, a₃]
  have hmain : ((x ^ N * x ^ k)⁻¹ / 2 * (G * x ^ k * Mk) +
      1 / (2 * (x ^ N * x ^ k)⁻¹) * (C₁ * (x ^ N * x ^ N * x ^ k)⁻¹)) = (G * Mk + C₁) / 2 * (x ^ N)⁻¹ := by
    field_simp
  rw [hmain]
  have hpos : 0 ≤ G * Mk + C₁ := by positivity
  have : productMomentConstant c₀ CS CN k = G * Mk := rfl
  rw [this]
  have hXi : 0 ≤ (x ^ N)⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_right _ hXi
  linarith
theorem goodConfigsLikely_of_moments (h₁ : curvatureMomentsNearPointStatement) (h₂ : noLumpNearPointStatement)
    (h₃ : farLevelSupportSitesStatement) (h₄ : meanScoreMomentBoundStatement) (h₅ : scaleWindowStatement)
    (h₆ : supportTotalBoundedByScoresStatement) (h₇ : StageStatesMeasurableStatement)
    (h₈ : sampleBelowLawStatement) (h₉ : forgetLastStepStatement) : goodConfigsLikelyStatement := by
  unfold curvatureMomentsNearPointStatement at h₁
  unfold noLumpNearPointStatement at h₂
  unfold farLevelSupportSitesStatement at h₃
  unfold meanScoreMomentBoundStatement at h₄
  unfold scaleWindowStatement at h₅
  unfold supportTotalBoundedByScoresStatement at h₆
  unfold goodConfigsLikelyStatement
  unfold ForAllPoints at h₁ h₂ h₃ h₅ h₆
  unfold ForAllHullPoints at h₄ ⊢
  refine forAllHullParameters_mono ?_ (forAllHullParameters_and (forAllHullParameters_of_forAllParameters h₁)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters h₂)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters h₃) (forAllHullParameters_and h₄
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters h₅)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters h₆)
      (forAllHullParameters_of_forAllParameters forAllParameters_admissible_floorMin_le)))))))
  rintro Λ ⟨⟨CM, _, XM, _, _, HM⟩, ⟨CH, c, XH, hc, _, HH⟩, ⟨CS, _, _, _, _, HS⟩, ⟨CN, _, _, _, _, HN⟩,
    ⟨_, _, XW, _, _, HW⟩, ⟨_, _, XF, _, _, HF⟩, hD, hy⟩
  have hfit : Λ.stepParams.Admissible := hD.fits Λ.floor hy
  have hL : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side := hD.L_gt
  set C₃ : ℝ := productMomentConstant Λ.response.C₀ (CS 0) (CN 0) Λ.k with hC₃
  have hC₃0 : 0 ≤ C₃ := by
    rw [hC₃]
    unfold productMomentConstant
    positivity
  have hf0 : ∀ N, 0 ≤ badMassConstant CM |CH 0| c N := fun N => by
    unfold badMassConstant
    positivity
  have hs0 : ∀ N, 0 ≤ goodMomentConstant CM |CH 0| c N := fun N => by
    unfold goodMomentConstant
    positivity
  refine ⟨fun N => badMassConstant CM |CH 0| c N + goodMomentConstant CM |CH 0| c N +
      (C₃ + badMassConstant CM |CH 0| c (2 * N + Λ.k)), 1,
    max (max (max XM XH) (max XW XF)) (max Λ.floor ((8 : ℝ) ^ 100)), one_pos,
    le_max_of_le_right (le_max_left _ _), ?_⟩
  intro S hX
  have hxM : XM ≤ S.scaleCoupling :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hX
  have hxH : XH ≤ S.scaleCoupling :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hX
  have hxW : XW ≤ S.scaleCoupling :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hX
  have hxF : XF ≤ S.scaleCoupling :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hX
  have hx8 : (8 : ℝ) ^ 100 ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (one_le_pow₀ (by norm_num)) hx8
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hq : ∀ (s n : ℕ) [NeZero n], Measurable (stageState S.tower s n) :=
    fun s n _ => h₇ Λ.stepParams hfit S.tower s n
  have hprob : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (S.law s n) :=
    fun s n _ => (h₉ Λ.stepParams hfit hL S.tower S.isCutoff S.marksMeasurable S.β s n).1
  have hbelow : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
      Measure.map (sampleBelow Λ.stepParams s d n) (S.law (s + d) n) = S.law s (fineSide Λ.stepParams.side d n) :=
    fun s d n _ => (h₈ Λ.stepParams hfit hL S.tower S.isCutoff S.marksMeasurable S.β (fun _ => 0)).1 s d n
  have hK : S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel := (HW S hxW).2.2.2.2.2.1
  have hH := HH S hxH
  have hpc := good_bounds_in_window S hq hprob hbelow hx8 hK hc (HM S hxM) hH.1 hH.2
  have hN : ∀ N, badMassConstant CM |CH 0| c N ≤ badMassConstant CM |CH 0| c N +
      goodMomentConstant CM |CH 0| c N + (C₃ + badMassConstant CM |CH 0| c (2 * N + Λ.k)) := fun N => by
    have := hs0 N
    have := hf0 (2 * N + Λ.k)
    linarith
  have hS : ∀ N, goodMomentConstant CM |CH 0| c N ≤ badMassConstant CM |CH 0| c N +
      goodMomentConstant CM |CH 0| c N + (C₃ + badMassConstant CM |CH 0| c (2 * N + Λ.k)) := fun N => by
    have := hf0 N
    have := hf0 (2 * N + Λ.k)
    linarith
  have hT : ∀ N, C₃ + badMassConstant CM |CH 0| c (2 * N + Λ.k) ≤ badMassConstant CM |CH 0| c N +
      goodMomentConstant CM |CH 0| c N + (C₃ + badMassConstant CM |CH 0| c (2 * N + Λ.k)) := fun N => by
    have := hf0 N
    have := hs0 N
    linarith
  refine ⟨fun u hu₁ hu₂ => ⟨fun N => ?_, fun k => ?_⟩, fun B N => ?_⟩
  · exact ((hpc u hu₁ hu₂).1 N).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hN N) (by positivity)))
  · exact ((hpc u hu₁ hu₂).2 k).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hS k) (by positivity)))
  · have hE : MeasurableSet {w | ¬ S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated)
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).2.1} :=
      (measurableSet_isGoodConfig S hq S.lastSeparated (S.levelSide S.lastSeparated)).compl
    have hr8 : (S.range : ℝ) ^ 8 ≤ 256 * S.scaleCoupling := by
      refine (clusterRange_pow_eight_le hx8).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      have := Real.rpow_le_rpow_of_exponent_le hx1 (show (2 : ℝ) / 25 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have := hprob S.lastSeparated (S.levelSide S.lastSeparated)
    have hb := lintegral_indicator_prod_le (ν := S.law S.lastSeparated (S.levelSide S.lastSeparated)) hE
      (F := fun i w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
      (Nn := fun i w => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
      (c₀ := Λ.response.C₀) (CS := CS 0) (CN := CN 0)
      (r := (S.range : ℝ)) (x := S.scaleCoupling) (C₁ := badMassConstant CM |CH 0| c (2 * N + Λ.k))
      (fun i => ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ)) (fun i => by positivity)
      (HS S).1 (by positivity) hr8 hx1
      (HF S hxF) (fun p hp J hJ => (HN S p hp J hJ).2) N (hf0 _)
      ((hpc S.lastSeparated le_rfl (by omega)).1 (2 * N + Λ.k)) B
    exact hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hT N) (by positivity)))
end YangMills.Construction.MomentLaw
end
