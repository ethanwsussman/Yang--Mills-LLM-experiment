import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlockProof
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemes
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.UnimodularArgumentHolomorphy
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.AveragingDomains
open YangMills.Construction.Matrices YangMills.Construction.Coordinates YangMills.Construction.Averaging YangMills.Construction.Conventions
private def logSeriesCoeff (n : ℕ) : ℂ := if n = 0 then 0 else (n : ℂ)⁻¹
private theorem norm_logSeriesCoeff_le (n : ℕ) : ‖logSeriesCoeff n‖ ≤ 1 := by
  unfold logSeriesCoeff
  split_ifs with h
  · simp
  · rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 h)
private theorem summable_logSeriesTerms {Y : ComplexMatrix2} (hY : ‖Y‖ < 1) :
    Summable fun n : ℕ => logSeriesCoeff n • Y ^ n := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg Y) hY) fun n => ?_
  calc ‖logSeriesCoeff n • Y ^ n‖ ≤ ‖logSeriesCoeff n‖ * ‖Y ^ n‖ := norm_smul_le _ _
    _ ≤ 1 * ‖Y‖ ^ n := by
      gcongr
      · exact norm_logSeriesCoeff_le n
      · exact norm_pow_le _ _
    _ = ‖Y‖ ^ n := one_mul _
private theorem logSeries_eq_neg_tsum {X : ComplexMatrix2} (hX : ‖1 - X‖ < 1) :
    ComplexMatrix2.logSeries X = -∑' n : ℕ, logSeriesCoeff n • (1 - X) ^ n := by
  rw [(summable_logSeriesTerms hX).tsum_eq_zero_add]
  unfold ComplexMatrix2.logSeries
  congr 1
  simp only [logSeriesCoeff, if_true, zero_smul, zero_add]
  refine tsum_congr fun n => ?_
  simp
private theorem analyticAt_logSeries {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.logBall) :
    AnalyticAt ℂ ComplexMatrix2.logSeries X := by
  have hX' : ‖1 - X‖ < 1 := by
    have : ‖X - 1‖ < 1 := hX
    rwa [norm_sub_rev]
  set q := FormalMultilinearSeries.ofScalars ComplexMatrix2 logSeriesCoeff with hq
  have hrad : (1 : ENNReal) ≤ q.radius := by
    have := q.le_radius_of_bound (C := 1) (r := 1) fun n => by
      simpa [hq, FormalMultilinearSeries.ofScalars_norm] using norm_logSeriesCoeff_le n
    simpa using this
  have hball := q.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)
  have hmem : (1 - X) ∈ Metric.eball (0 : ComplexMatrix2) q.radius := by
    refine Metric.eball_subset_eball hrad ?_
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact ENNReal.ofReal_lt_one.2 hX'
  have h₁ : AnalyticAt ℂ q.sum (1 - X) := hball.analyticAt_of_mem hmem
  have h₂ : AnalyticAt ℂ (fun Z : ComplexMatrix2 => 1 - Z) X := analyticAt_const.sub analyticAt_id
  have h₃ : AnalyticAt ℂ (fun Z : ComplexMatrix2 => -q.sum (1 - Z)) X :=
    (AnalyticAt.comp (g := q.sum) (f := fun Z : ComplexMatrix2 => 1 - Z) h₁ h₂).neg
  refine h₃.congr ?_
  have hopen : ∀ᶠ Z in 𝓝 X, ‖1 - Z‖ < 1 :=
    (continuous_const.sub continuous_id).norm.continuousAt.eventually (gt_mem_nhds hX')
  filter_upwards [hopen] with Z hZ
  rw [logSeries_eq_neg_tsum hZ, hq]
  exact congrArg Neg.neg (FormalMultilinearSeries.ofScalars_sum_eq logSeriesCoeff (1 - Z))
private def traceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
private theorem trace_pow_eq_eigen_sum (Y : ComplexMatrix2) (a b : ℂ) (hs : a + b = Matrix.trace Y)
    (hp : a * b = Y.det) (n : ℕ) :
    Matrix.trace (Y ^ n) = a ^ n + b ^ n ∧ Matrix.trace (Y ^ (n + 1)) = a ^ (n + 1) + b ^ (n + 1) := by
  have hch : Y * Y = Matrix.trace Y • Y - Y.det • (1 : ComplexMatrix2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
  induction n with
  | zero => simp [Matrix.trace_fin_two, hs]; norm_num
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : Y ^ (n + 1 + 1) = Matrix.trace Y • Y ^ (n + 1) - Y.det • Y ^ n := by
      rw [pow_succ, pow_succ, mul_assoc, hch, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
        ← pow_succ]
    rw [e, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2, ← hs, ← hp]
    simp only [smul_eq_mul]
    ring
abbrev _root_.YangMills.DeltaSharedProofs.p501865 := @trace_pow_eq_eigen_sum
private theorem norm_root_lt_one {Y : ComplexMatrix2} (hY : ‖Y‖ < 1) {a : ℂ}
    (ha : a ^ 2 - Matrix.trace Y * a + Y.det = 0) : ‖a‖ < 1 := by
  refine lt_of_le_of_lt (spectrum.norm_le_norm_of_mem (𝕜 := ℂ) (a := Y) ?_) hY
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  rw [Matrix.det_fin_two]
  simp only [Matrix.algebraMap_matrix_apply, Matrix.sub_apply]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two] at ha
  simp
  linear_combination ha
private theorem trace_logSeries_eq_zero {X : ComplexMatrix2} (hdet : X.det = 1)
    (hX : X ∈ ComplexMatrix2.logBall) : Matrix.trace (ComplexMatrix2.logSeries X) = 0 := by
  set Y : ComplexMatrix2 := 1 - X with hYdef
  have hY : ‖Y‖ < 1 := by
    have : ‖X - 1‖ < 1 := hX
    rwa [norm_sub_rev]
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (Matrix.trace Y ^ 2 - 4 * Y.det)
    (n := 2) (by norm_num)
  set a : ℂ := (Matrix.trace Y + r) / 2 with ha
  set b : ℂ := (Matrix.trace Y - r) / 2 with hb
  have hs : a + b = Matrix.trace Y := by rw [ha, hb]; ring
  have hp : a * b = Y.det := by
    rw [ha, hb]
    linear_combination (-1 / 4 : ℂ) * hr
  have hra : a ^ 2 - Matrix.trace Y * a + Y.det = 0 := by
    rw [← hs, ← hp]; ring
  have hrb : b ^ 2 - Matrix.trace Y * b + Y.det = 0 := by
    rw [← hs, ← hp]; ring
  have hna := norm_root_lt_one hY hra
  have hnb := norm_root_lt_one hY hrb
  have hone : (1 - a) * (1 - b) = 1 := by
    have h1 : X = 1 - Y := by rw [hYdef]; abel
    have h3 : (1 - Y).det = 1 - Matrix.trace Y + Y.det := by
      simp [Matrix.trace_fin_two, Matrix.det_fin_two]
      ring
    have h2 : 1 - Matrix.trace Y + Y.det = 1 := by
      rw [← h3, ← h1]
      exact hdet
    rw [← hs, ← hp] at h2
    linear_combination h2
  have hsum : HasSum (fun n : ℕ => logSeriesCoeff n • Y ^ n)
      (∑' n : ℕ, logSeriesCoeff n • Y ^ n) :=
    (summable_logSeriesTerms hY).hasSum
  have htr := traceCLM.hasSum hsum
  have hlogs : ∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun n : ℕ => logSeriesCoeff n * z ^ n) (-Complex.log (1 - z)) := by
    intro z hz
    have e : (fun n : ℕ => logSeriesCoeff n * z ^ n) = fun n : ℕ => z ^ n / n := by
      funext n
      by_cases h : n = 0
      · simp [logSeriesCoeff, h]
      · simp [logSeriesCoeff, h, div_eq_inv_mul]
    rw [e]
    exact Complex.hasSum_taylorSeries_neg_log hz
  have hterm : ∀ n : ℕ, traceCLM (logSeriesCoeff n • Y ^ n) =
      logSeriesCoeff n * a ^ n + logSeriesCoeff n * b ^ n := by
    intro n
    have : traceCLM (logSeriesCoeff n • Y ^ n) = logSeriesCoeff n * Matrix.trace (Y ^ n) := by
      rw [map_smul]
      rfl
    rw [this, (trace_pow_eq_eigen_sum Y a b hs hp n).1]
    ring
  have hval : traceCLM (∑' n : ℕ, logSeriesCoeff n • Y ^ n) =
      -Complex.log (1 - a) + -Complex.log (1 - b) := by
    refine HasSum.unique (htr) ?_
    simp only [hterm]
    exact (hlogs a hna).add (hlogs b hnb)
  have hre : ∀ z : ℂ, ‖z‖ < 1 → 0 < (1 - z).re := by
    intro z hz
    have := (abs_le.1 (Complex.abs_re_le_norm z)).2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have harg : ∀ z : ℂ, ‖z‖ < 1 → |Complex.arg (1 - z)| < Real.pi / 2 := fun z hz =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre z hz))
  have hne : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := fun z hz h => by
    have := hre z hz
    simp [h] at this
  have hlog : Complex.log (1 - a) + Complex.log (1 - b) = 0 := by
    have h := (Complex.log_mul_eq_add_log_iff (hne a hna) (hne b hnb)).2 (by
      have h1 := abs_lt.1 (harg a hna)
      have h2 := abs_lt.1 (harg b hnb)
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
    rw [← h, hone, Complex.log_one]
  have hfin : ComplexMatrix2.logSeries X = -∑' n : ℕ, logSeriesCoeff n • Y ^ n :=
    logSeries_eq_neg_tsum hY
  have htrace : Matrix.trace (∑' n : ℕ, logSeriesCoeff n • Y ^ n) =
      -Complex.log (1 - a) + -Complex.log (1 - b) := hval
  rw [hfin, Matrix.trace_neg, htrace]
  linear_combination hlog
section LocalForms
variable {σ : Type} [Fintype σ]
private def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        simp only [Matrix.adjugate_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> ring
      map_smul' := fun t X => by
        simp only [Matrix.adjugate_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
private theorem inv_eq_adjugateCLM {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ = adjugateCLM X := by
  have h' : X.det = 1 := h
  change X⁻¹ = Matrix.adjugate X
  simp [Matrix.inv_def, h']
private theorem inv_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
abbrev _root_.YangMills.SharedProofs.p413 := @inv_mem_unitDeterminant
private theorem mul_mem_unitDeterminant {X Y : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) (h' : Y ∈ ComplexMatrix2.unitDeterminant) :
    X * Y ∈ ComplexMatrix2.unitDeterminant := by
  have e : X.det = 1 := h
  have e' : Y.det = 1 := h'
  change (X * Y).det = 1
  rw [Matrix.det_mul, e, e', one_mul]
abbrev _root_.YangMills.DeltaSharedProofs.p585 := @mul_mem_unitDeterminant
abbrev _root_.YangMills.SharedProofs.p36859 := @mul_mem_unitDeterminant
private def LocalForm (p : σ → ComplexMatrix2) (f : (σ → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∃ F : (σ → ComplexMatrix2) → ComplexMatrix2, AnalyticAt ℂ F p ∧
    ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi σ] p,
      f v = F v ∧ f v ∈ ComplexMatrix2.unitDeterminant
private theorem LocalForm.mul {p : σ → ComplexMatrix2} {f g : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hf : LocalForm p f) (hg : LocalForm p g) : LocalForm p fun v => f v * g v := by
  obtain ⟨F, hF, hFe⟩ := hf
  obtain ⟨G, hG, hGe⟩ := hg
  refine ⟨fun v => F v * G v, hF.mul hG, ?_⟩
  filter_upwards [hFe, hGe] with v h₁ h₂
  exact ⟨by rw [h₁.1, h₂.1], mul_mem_unitDeterminant h₁.2 h₂.2⟩
private theorem LocalForm.inv {p : σ → ComplexMatrix2} {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hf : LocalForm p f) : LocalForm p fun v => (f v)⁻¹ := by
  obtain ⟨F, hF, hFe⟩ := hf
  refine ⟨fun v => adjugateCLM (F v),
    AnalyticAt.comp (g := adjugateCLM) (adjugateCLM.analyticAt _) hF, ?_⟩
  filter_upwards [hFe] with v h
  exact ⟨by rw [inv_eq_adjugateCLM h.2, h.1], inv_mem_unitDeterminant h.2⟩
private theorem localForm_one (p : σ → ComplexMatrix2) : LocalForm p fun _ => 1 :=
  ⟨fun _ => 1, analyticAt_const, Eventually.of_forall fun _ => ⟨rfl, by
    change Matrix.det (1 : ComplexMatrix2) = 1
    simp⟩⟩
private theorem complexLogMean_comp_equiv {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    (V : ι → ComplexMatrix2) : complexLogMean (V ∘ e) = complexLogMean V := by
  unfold complexLogMean
  congr 1
  funext W
  apply propext
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, i, hi⟩
    refine ⟨⟨h1, fun i => ?_, ?_⟩, e i, hi⟩
    · simpa using h2 (e.symm i)
    · rw [← Equiv.sum_comp e]
      exact h3
  · rintro ⟨⟨h1, h2, h3⟩, i, hi⟩
    refine ⟨⟨h1, fun i => h2 (e i), ?_⟩, e.symm i, by simpa using hi⟩
    change ∑ i, ComplexMatrix2.logSeries (V (e i) * W⁻¹) = 0
    rw [Equiv.sum_comp e (fun i => ComplexMatrix2.logSeries (V i * W⁻¹))]
    exact h3
abbrev _root_.YangMills.SharedProofs.p1929 := @complexLogMean_comp_equiv
private theorem familyDiameter_comp_equiv {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    (V : ι → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  exact (e.prodCongr e).iSup_congr fun _ => rfl
private theorem complexLogMean_mem {n : ℕ} (hM : ComplexLogMeanProperties n)
    {V : Fin n → ComplexMatrix2} (hV : V ∈ smallComplexFamilies n) :
    complexLogMean V ∈ ComplexMatrix2.unitDeterminant := by
  obtain ⟨W, hW, -⟩ := hM.existsUnique V hV
  have h := Classical.epsilon_spec (⟨W, hW⟩ : ∃ W, IsNearComplexLogMean V W)
  exact h.1.1
private theorem localForm_complexLogMean (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    {ι : Type} [Fintype ι] [Nonempty ι] {p : σ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct.unimodularPi σ) {f : (σ → ComplexMatrix2) → ι → ComplexMatrix2}
    (hf : ∀ i, LocalForm p fun v => f v i)
    (hsmall : ComplexMatrix2.familyDiameter (f p) < centreOfMassDiameter) :
    LocalForm p (fun v => complexLogMean (f v)) ∧
      ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi σ] p,
        ComplexMatrix2.familyDiameter (f v) < centreOfMassDiameter := by
  classical
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hMn := hM _ hn
  choose F hFa hFe using hf
  let G : (σ → ComplexMatrix2) → Fin (Fintype.card ι) → ComplexMatrix2 := fun v k => F (e k) v
  have hGa : AnalyticAt ℂ G p := analyticAt_pi_iff.2 fun k => hFa (e k)
  have hev : ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi σ] p, ∀ k,
      f v (e k) = G v k ∧ f v (e k) ∈ ComplexMatrix2.unitDeterminant :=
    eventually_all.2 fun k => hFe (e k)
  have hself : f p ∘ e = G p := funext fun k => (hev.self_of_nhdsWithin hp k).1
  have hV0 : G p ∈ smallComplexFamilies (Fintype.card ι) := by
    refine ⟨fun k => ?_, ?_⟩
    · have := (hev.self_of_nhdsWithin hp k)
      rw [← this.1]
      exact this.2
    · rw [← hself, familyDiameter_comp_equiv]
      exact hsmall
  obtain ⟨O, hO, hOeq⟩ := hMn.isOpen
  obtain ⟨H, hHa, hHe⟩ := hMn.holomorphicInEntries.2.2 _ hV0
  have hV0O : G p ∈ O := by
    rw [hOeq] at hV0
    exact hV0.1
  have hmem : ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi σ] p,
      G v ∈ smallComplexFamilies (Fintype.card ι) := by
    have h1 : ∀ᶠ v in 𝓝 p, G v ∈ O := hGa.continuousAt.eventually (hO.mem_nhds hV0O)
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds, hev] with v a b
    rw [hOeq]
    refine ⟨a, fun k => ?_⟩
    have := b k
    change G v k ∈ ComplexMatrix2.unitDeterminant
    rw [← this.1]
    exact this.2
  have htend : Tendsto G (𝓝[GroupLieProduct.unimodularPi σ] p)
      (𝓝[smallComplexFamilies (Fintype.card ι)] (G p)) :=
    tendsto_nhdsWithin_iff.2 ⟨hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, hmem⟩
  have hfam : ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi σ] p, f v ∘ e = G v :=
    hev.mono fun v h => funext fun k => (h k).1
  refine ⟨⟨fun v => H (G v) (), ?_, ?_⟩, ?_⟩
  · exact analyticAt_pi_iff.1 (AnalyticAt.comp (g := H) (f := G) hHa hGa) ()
  · filter_upwards [htend.eventually hHe, hfam, hmem] with v h₁ h₂ h₃
    have e₁ : complexLogMean (f v) = complexLogMean (G v) := by
      rw [← h₂, complexLogMean_comp_equiv]
    refine ⟨?_, ?_⟩
    · rw [e₁]
      exact congrFun h₁ ()
    · rw [e₁]
      exact complexLogMean_mem hMn h₃
  · filter_upwards [hfam, hmem] with v h₂ h₃
    rw [← familyDiameter_comp_equiv e, h₂]
    exact h₃.2
private theorem isHolomorphicVia_of_analyticAt {k : ℕ} (ν : σ ≃ Fin k)
    {N : Set (σ → ComplexMatrix2)} (hN : IsOpen N)
    {F : (σ → ComplexMatrix2) → ComplexMatrix2} (hF : ∀ y ∈ N, AnalyticAt ℂ F y) :
    ComplexCoordinates.IsHolomorphicVia (GroupLieProduct.matrixPiEquiv ν)
      ComplexCoordinates.matrixEquiv N F := by
  let e := GroupLieProduct.matrixPiEquiv ν
  let pos : Fin (ComplexCoordinates.productDim
      fun _ : Fin k => ComplexCoordinates.Component.matrix) → (i : Fin k) × Fin 4 := fun q =>
    (finSigmaFinEquiv
      (n := fun i => ((fun _ : Fin k => ComplexCoordinates.Component.matrix) i).dim)).symm q
  have key : ∀ (z : σ → ComplexMatrix2) (q), e z q =
      ComplexCoordinates.matrixEquiv (z (ν.symm (pos q).1)) (pos q).2 := fun _ _ => rfl
  let eL : (σ → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates (ComplexCoordinates.productDim
      fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
    { e with
      map_add' := fun x y => by
        funext q
        exact key (x + y) q
      map_smul' := fun t x => by
        funext q
        exact key (t • x) q }
  let eC := eL.toContinuousLinearEquiv
  let mL : ComplexMatrix2 ≃ₗ[ℂ] ComplexCoordinates 4 :=
    { ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let mC := mL.toContinuousLinearEquiv
  have hopen : IsOpen (e '' N) := eC.toHomeomorph.isOpenMap N hN
  have han : ∀ w ∈ e '' N,
      AnalyticAt ℂ (ComplexCoordinates.matrixEquiv ∘ F ∘ e.symm) w := by
    rintro _ ⟨y, hy, rfl⟩
    have h₁ : AnalyticAt ℂ eC.symm (e y) := eC.symm.toContinuousLinearMap.analyticAt _
    have e₁ : eC.symm (e y) = y := e.symm_apply_apply y
    have h₂ : AnalyticAt ℂ F (eC.symm (e y)) := by
      rw [e₁]
      exact hF y hy
    have h₃ : AnalyticAt ℂ (F ∘ eC.symm) (e y) := AnalyticAt.comp h₂ h₁
    exact AnalyticAt.comp (g := mC) (mC.toContinuousLinearMap.analyticAt _) h₃
  refine ⟨hopen, fun w hw => (han w hw).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • (ComplexCoordinates.stdBasisVector j) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • (ComplexCoordinates.stdBasisVector j) ∈ e '' N :=
    hline.continuousAt.eventually (by
      simp only [zero_smul, add_zero]
      exact hopen.mem_nhds ha)
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • (ComplexCoordinates.stdBasisVector j)) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := ComplexCoordinates.matrixEquiv ∘ F ∘ e.symm) ζ
    (han _ hζ).differentiableAt hd
abbrev _root_.YangMills.SharedProofs.p13839 := @isHolomorphicVia_of_analyticAt
private theorem isHolomorphicIn_congr {M M' : ℕ} {W : Set (ComplexCoordinates M)}
    {g g' : ComplexCoordinates M → ComplexCoordinates M'}
    (h : ComplexCoordinates.IsHolomorphicIn W g)
    (e : ∀ w ∈ W, g' w = g w) : ComplexCoordinates.IsHolomorphicIn W g' := by
  refine ⟨h.1, h.2.1.congr e, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • (ComplexCoordinates.stdBasisVector j) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • (ComplexCoordinates.stdBasisVector j) ∈ W :=
    hline.continuousAt.eventually (by simpa using h.1.mem_nhds ha)
  filter_upwards [h.2.2 a ha j, eventually_eventually_nhds.2 hnear] with ζ hd hz
  exact hd.congr_of_eventuallyEq (hz.mono fun ζ' h' => e _ h')
abbrev _root_.YangMills.SharedProofs.p63802 := @isHolomorphicIn_congr
private theorem exists_open_analytic_extension {D : Set (σ → ComplexMatrix2)}
    (hDo : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct.unimodularPi σ) D)
    {p : σ → ComplexMatrix2} (hp : p ∈ D) {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hf : LocalForm p f) :
    ∃ (N : Set (σ → ComplexMatrix2)) (F : (σ → ComplexMatrix2) → ComplexMatrix2),
      IsOpen N ∧ p ∈ N ∧ (∀ y ∈ N, AnalyticAt ℂ F y) ∧
      ∀ v ∈ N ∩ GroupLieProduct.unimodularPi σ,
        v ∈ D ∧ f v = F v ∧ F v ∈ ComplexMatrix2.unitDeterminant := by
  obtain ⟨O, hO, rfl⟩ := hDo
  obtain ⟨F, hFa, hFe⟩ := hf
  have h1 := hFa.eventually_analyticAt
  have h2 := eventually_nhdsWithin_iff.1 hFe
  have h3 : ∀ᶠ v in 𝓝 p, v ∈ O := hO.mem_nhds hp.1
  obtain ⟨N, hsub, hNo, hpN⟩ := eventually_nhds_iff.1 (h1.and (h2.and h3))
  refine ⟨N, F, hNo, hpN, fun y hy => (hsub y hy).1, fun v hv => ?_⟩
  obtain ⟨-, h₂, h₃⟩ := hsub v hv.1
  obtain ⟨e₁, e₂⟩ := h₂ hv.2
  exact ⟨⟨h₃, hv.2⟩, e₁, e₁ ▸ e₂⟩
private theorem holomorphic_of_localForms (hS : UnimodularArguments.HolomorphicAtUnimodular)
    [Nonempty σ] {D : Set (σ → ComplexMatrix2)} (hDs : D ⊆ GroupLieProduct.unimodularPi σ)
    (hDo : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct.unimodularPi σ) D)
    {f : (σ → ComplexMatrix2) → ComplexMatrix2} (hf : ∀ p ∈ D, LocalForm p f) :
    ComplexMatrix2.IsHolomorphicBetween (fun _ : σ => ComplexMatrix2.FactorKind.group)
        (fun _ : Unit => ComplexMatrix2.FactorKind.group) D (fun v _ => f v) ∧
      ∀ (N : ℕ) (ν : σ ≃ Fin N) (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
        ComplexCoordinates.IsHolomorphicOnSL2Power β ((fun v => v ∘ ν.symm) '' D)
          fun X => f (X ∘ ν) := by
  have hstep : ∀ {N : Set (σ → ComplexMatrix2)} {F : (σ → ComplexMatrix2) → ComplexMatrix2},
      IsOpen N → (∀ y ∈ N, AnalyticAt ℂ F y) →
      (∀ v ∈ N ∩ GroupLieProduct.unimodularPi σ,
        v ∈ D ∧ f v = F v ∧ F v ∈ ComplexMatrix2.unitDeterminant) →
      _ := fun {N F} hNo hNa hNe =>
    hS σ _ (Fintype.equivFin σ) N F hNo (isHolomorphicVia_of_analyticAt _ hNo hNa)
      fun U hU => (hNe U hU).2.2
  refine ⟨⟨hDo, fun v hv _ => ?_, fun x hx => ?_⟩, fun N' ν β => ?_⟩
  · obtain ⟨F, -, hFe⟩ := hf v hv
    exact (hFe.self_of_nhdsWithin (hDs hv)).2
  · obtain ⟨N, F, hNo, hxN, hNa, hNe⟩ := exists_open_analytic_extension hDo hx (hf x hx)
    obtain ⟨-, hb, -, -⟩ := hstep hNo hNa hNe
    obtain ⟨G, hGa, hGe⟩ := hb.2.2 x ⟨hxN, hDs hx⟩
    refine ⟨G, hGa, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_nhdsWithin_iff.1 hGe, hNo.mem_nhds hxN] with y hy hyN hyD
    have hcp : y ∈ UnimodularArguments.unimodularPart N := ⟨hyN, hDs hyD⟩
    rw [← hy hcp]
    funext _
    exact (hNe y hcp).2.1
  · have hmem : ∀ X, X ∈ (fun v => v ∘ ν.symm) '' D ↔ X ∘ ν ∈ D := by
      intro X
      constructor
      · rintro ⟨v, hv, rfl⟩
        simpa [Function.comp_def] using hv
      · intro h
        exact ⟨X ∘ ν, h, by funext i; simp⟩
    have hcomp : Continuous fun X : Fin N' → ComplexMatrix2 => X ∘ ν :=
      continuous_pi fun i => continuous_apply _
    have hone : 1 ≤ N' := (ν (Classical.arbitrary σ)).pos
    refine ⟨hone, ?_, ?_, fun X hX => ?_, fun X hX => ?_⟩
    · obtain ⟨O, hO, hOe⟩ := hDo
      refine ⟨(fun X => X ∘ ν) ⁻¹' O, hO.preimage hcomp, ?_⟩
      ext X
      rw [hmem, hOe]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, fun i => by simpa using h₂ (ν.symm i)⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, fun i => h₂ (ν i)⟩
    · intro X hX
      obtain ⟨F, -, hFe⟩ := hf _ ((hmem X).1 hX)
      exact (hFe.self_of_nhdsWithin (hDs ((hmem X).1 hX))).2
    · have hp := (hmem X).1 hX
      obtain ⟨N, F, hNo, hxN, hNa, hNe⟩ := exists_open_analytic_extension hDo hp (hf _ hp)
      have hc : ContinuousAt (fun Y : Fin N' → ComplexMatrix2 => F (Y ∘ ν)) X :=
        ContinuousAt.comp (g := F) (f := fun Y : Fin N' → ComplexMatrix2 => Y ∘ ν)
          (hNa _ hxN).continuousAt hcomp.continuousAt
      refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hNe _ ⟨hxN, hDs hp⟩).2.1
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards [hcomp.continuousAt.eventually (hNo.mem_nhds hxN)] with Y hY hYU
      exact (hNe _ ⟨hY, hDs ((hmem Y).1 hYU)⟩).2.1
    · have hp := (hmem X).1 hX
      obtain ⟨N, F, hNo, hxN, hNa, hNe⟩ := exists_open_analytic_extension hDo hp (hf _ hp)
      obtain ⟨-, -, hc, -⟩ := hstep hNo hNa hNe
      have hX' : X ∈ (fun U => U ∘ ν.symm) '' UnimodularArguments.unimodularPart N :=
        ⟨X ∘ ν, ⟨hxN, hDs hp⟩, by funext i; simp⟩
      obtain ⟨-, -, -, -, hch⟩ := hc N' ν β hone
      obtain ⟨Wc, h0, hW, hhol⟩ := hch X hX'
      have hpart : ∀ Y ∈ (fun U => U ∘ ν.symm) '' UnimodularArguments.unimodularPart N,
          Y ∘ ν ∈ UnimodularArguments.unimodularPart N := by
        rintro _ ⟨v, hv, rfl⟩
        simpa [Function.comp_def] using hv
      have hq : ∀ w ∈ Wc, ComplexCoordinates.expChartQuotient (fun Y => f (Y ∘ ν)) X
          (ComplexCoordinates.tracelessTuple β w) =
          ComplexCoordinates.expChartQuotient (fun Y => F (Y ∘ ν)) X
            (ComplexCoordinates.tracelessTuple β w) := by
        intro w hw
        change f (ComplexCoordinates.expChart X (ComplexCoordinates.tracelessTuple β w) ∘ ν) *
            (f (X ∘ ν))⁻¹ =
          F (ComplexCoordinates.expChart X (ComplexCoordinates.tracelessTuple β w) ∘ ν) *
            (F (X ∘ ν))⁻¹
        rw [(hNe _ (hpart _ (hW w hw).1)).2.1, (hNe _ ⟨hxN, hDs hp⟩).2.1]
      refine ⟨Wc, h0, fun w hw => ⟨?_, ?_⟩, ?_⟩
      · exact (hmem _).2 (hNe _ (hpart _ (hW w hw).1)).1
      · rw [hq w hw]
        exact (hW w hw).2
      · refine isHolomorphicIn_congr hhol fun w hw => ?_
        simp only [hq w hw]
end LocalForms
section PositiveCoordinates
variable {L m : ℕ} {j : ℤ}
private theorem pathHolonomy_congr {U U' : Bond L m j → ComplexMatrix2} {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, U b = U' b) : pathHolonomy U Γ = pathHolonomy U' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem opposite_isPositivelyOriented {b : Bond L m j} (h : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
private theorem localForm_extend (ℬ : Set (Bond L m j)) [Fintype (PositiveBondOf ℬ)]
    (p : PositiveBondOf ℬ → ComplexMatrix2) (b : Bond L m j) :
    LocalForm p fun v => extendFromPositive ℬ v b := by
  by_cases h : b ∈ ℬ ∧ b.IsPositivelyOriented
  · refine ⟨fun v => v ⟨b, h⟩, analyticAt_pi_iff.1 analyticAt_id _, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    have e : extendFromPositive ℬ v b = v ⟨b, h⟩ := by
      unfold extendFromPositive
      rw [dif_pos h]
    exact ⟨e, e ▸ hv _⟩
  · by_cases h' : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented
    · refine ⟨fun v => adjugateCLM (v ⟨b.opposite, h'⟩),
        AnalyticAt.comp (g := adjugateCLM) (adjugateCLM.analyticAt _)
          (analyticAt_pi_iff.1 analyticAt_id _), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      have e : extendFromPositive ℬ v b = (v ⟨b.opposite, h'⟩)⁻¹ := by
        unfold extendFromPositive
        rw [dif_neg h, dif_pos h']
      have hm : v ⟨b.opposite, h'⟩ ∈ ComplexMatrix2.unitDeterminant := hv _
      exact ⟨e.trans (inv_eq_adjugateCLM hm), e ▸ inv_mem_unitDeterminant hm⟩
    · refine ⟨fun _ => 1, analyticAt_const, Eventually.of_forall fun v => ?_⟩
      have e : extendFromPositive ℬ v b = 1 := by
        unfold extendFromPositive
        rw [dif_neg h, dif_neg h']
      refine ⟨e, ?_⟩
      change Matrix.det (extendFromPositive ℬ v b) = 1
      rw [e]
      simp
private theorem localForm_pathHolonomy (ℬ : Set (Bond L m j)) [Fintype (PositiveBondOf ℬ)]
    (p : PositiveBondOf ℬ → ComplexMatrix2) (Γ : List (Bond L m j)) :
    LocalForm p fun v => pathHolonomy (extendFromPositive ℬ v) Γ := by
  induction Γ with
  | nil => exact localForm_one p
  | cons b Γ ih =>
    have e : ∀ U : Bond L m j → ComplexMatrix2,
        pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := fun U => by
      simp [pathHolonomy]
    simp only [e]
    exact (localForm_extend ℬ p b).mul ih
private theorem isGaugeField_extendFromPositive {ℬ : Set (Bond L m j)}
    (hrev : ∀ b ∈ ℬ, b.opposite ∈ ℬ)
    (hno : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented)
    {v : PositiveBondOf ℬ → ComplexMatrix2}
    (hv : v ∈ GroupLieProduct.unimodularPi (PositiveBondOf ℬ)) :
    IsGaugeField complexGaugeGroup ℬ (extendFromPositive ℬ v) := by
  have hvm : ∀ i, v i ∈ ComplexMatrix2.unitDeterminant := hv
  have hpos : ∀ b (h : b ∈ ℬ ∧ b.IsPositivelyOriented), extendFromPositive ℬ v b = v ⟨b, h⟩ := by
    intro b h
    unfold extendFromPositive
    rw [dif_pos h]
  have hneg : ∀ b (h : b ∈ ℬ ∧ ¬b.IsPositivelyOriented),
      ∀ h' : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented,
      extendFromPositive ℬ v b = (v ⟨b.opposite, h'⟩)⁻¹ := by
    intro b h h'
    unfold extendFromPositive
    rw [dif_neg (fun k => h.2 k.2), dif_pos h']
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [hpos b ⟨hb, h⟩]
      exact hvm _
    · rw [hneg b ⟨hb, h⟩ ⟨hrev b hb, opposite_isPositivelyOriented h⟩]
      exact inv_mem_unitDeterminant (hvm _)
  · by_cases h : b.IsPositivelyOriented
    · rw [hpos b ⟨hb, h⟩, hneg b.opposite ⟨hrev b hb, hno b h⟩ ⟨hb, h⟩]
      rfl
    · have h₂ : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented :=
        ⟨hrev b hb, opposite_isPositivelyOriented h⟩
      have hu : IsUnit (v ⟨b.opposite, h₂⟩).det := by
        have : (v ⟨b.opposite, h₂⟩).det = 1 := hvm _
        rw [this]
        exact isUnit_one
      rw [hpos _ h₂, hneg b ⟨hb, h⟩ h₂, Matrix.nonsing_inv_nonsing_inv _ hu]
private theorem extendFromPositive_restrict {ℬ : Set (Bond L m j)}
    (hrev : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Bond L m j → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup ℬ W) {b : Bond L m j} (hb : b ∈ ℬ) :
    extendFromPositive ℬ (restrictToPositive ℬ W) b = W b := by
  by_cases h : b.IsPositivelyOriented
  · unfold extendFromPositive
    rw [dif_pos ⟨hb, h⟩]
    rfl
  · have h₂ : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented :=
      ⟨hrev b hb, opposite_isPositivelyOriented h⟩
    unfold extendFromPositive
    rw [dif_neg (fun k => h k.2), dif_pos h₂]
    change (W b.opposite)⁻¹ = W b
    have hu : IsUnit (W b).det := by
      have : (W b).det = 1 := hW.1 b hb
      rw [this]
      exact isUnit_one
    rw [hW.2 b hb, Matrix.nonsing_inv_nonsing_inv _ hu]
private theorem restrict_extendFromPositive (ℬ : Set (Bond L m j))
    (v : PositiveBondOf ℬ → ComplexMatrix2) :
    restrictToPositive ℬ (extendFromPositive ℬ v) = v := by
  funext b
  unfold restrictToPositive extendFromPositive
  rw [dif_pos b.2]
end PositiveCoordinates
section DoubleBlock
variable {L m K n : ℕ}
private abbrev doubleBlockSet (c : BondAtLevel L m K (n + 1)) : Set (BondAtLevel L m K n) :=
  bondsInDoubleBlock c
private structure DoubleBlockData (c : BondAtLevel L m K (n + 1)) : Prop where
  finite_source : (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)).Finite
  finite_target : (sitesInBlock (levelDepth K n) c.target : Set (SiteAtLevel L m K n)).Finite
  finite_bonds : (doubleBlockSet c).Finite
  contour : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
    ∀ x ∈ (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)), ∀ τ : AxisOrdering y x,
      ∀ b ∈ orderedContour y x τ, b ∈ doubleBlockSet c
  cornered : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
    ∀ x ∈ (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)),
      ∀ b ∈ coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x, b ∈ doubleBlockSet c
  crossing : ∀ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
    ∀ b ∈ crossingPath c x, b ∈ doubleBlockSet c
  transport : ∀ s : AveragingScheme, ∀ b ∈ axialPath (schemeBaseSite s (levelDepth K n) c.source)
    (schemeBaseSite s (levelDepth K n) c.target), b ∈ doubleBlockSet c
  shift_mem : ∀ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
    shiftAcross c x ∈ (sitesInBlock (levelDepth K n) c.target : Set (SiteAtLevel L m K n))
  exists_positive : ∃ b : BondAtLevel L m K n, b ∈ doubleBlockSet c ∧ b.IsPositivelyOriented
  not_both_oriented : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
    ¬b.opposite.IsPositivelyOriented
private theorem zero_mem_blockIndexBox (hL : 1 ≤ L) : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
  intro ν
  have : 0 ≤ centreToFaceSteps L := by
    unfold centreToFaceSteps
    omega
  simp only [Pi.zero_apply]
  omega
abbrev _root_.YangMills.SharedProofs.p113877 := @zero_mem_blockIndexBox
private theorem single_mem_blockIndexBox (hL : 3 ≤ L) (ν : Fin 4) :
    (Pi.single ν 1 : Fin 4 → ℤ) ∈ blockIndexBox L ∧
      (-Pi.single ν 1 : Fin 4 → ℤ) ∈ blockIndexBox L := by
  have h1 : 1 ≤ centreToFaceSteps L := by
    unfold centreToFaceSteps
    omega
  constructor
  · intro μ
    by_cases e : μ = ν
    · subst e; simp only [Pi.single_eq_same]; omega
    · rw [Pi.single_eq_of_ne e]; omega
  · intro μ
    by_cases e : μ = ν
    · subst e; simp only [Pi.neg_apply, Pi.single_eq_same]; omega
    · simp only [Pi.neg_apply, Pi.single_eq_of_ne e]; omega
abbrev _root_.YangMills.SharedProofs.p64624 := @single_mem_blockIndexBox
private theorem offsetSite_single {j' : ℤ} (w : Site L m j') (ν : Fin 4) :
    offsetSite w (Pi.single ν 1) = w + unitStep L m j' ν := by
  unfold offsetSite
  congr 1
  rw [Finset.sum_eq_single ν]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp
abbrev _root_.YangMills.SharedProofs.p21430 := @offsetSite_single
private theorem offsetSite_neg_single {j' : ℤ} (w : Site L m j') (ν : Fin 4) :
    offsetSite w (-Pi.single ν 1) = w - unitStep L m j' ν := by
  unfold offsetSite
  rw [sub_eq_add_neg]
  congr 1
  rw [Finset.sum_eq_single ν]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp
abbrev _root_.YangMills.SharedProofs.p79766 := @offsetSite_neg_single
private theorem forwardFrom_mem_forwardFlow {j' : ℤ} (x : Site L m j') (μ : Fin 4) {k : ℕ}
    (hk : 0 < k) : Bond.forwardFrom x μ ∈ forwardAxisPath x μ k := by
  cases k with
  | zero => omega
  | succ k => simp [forwardAxisPath]
private theorem doubleBlockData (hP : BlockPaths.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented) : DoubleBlockData c := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨hy, hcs⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨hD, -, -, hS, hI⟩ := hcs c μ hμ
  have hL13 := hL.2
  have hblock : ∀ y : SiteAtLevel L m K (n + 1), (unitBlock y).Finite := fun y =>
    Set.finite_of_ncard_ne_zero (by
      rw [(hy y).1.2.1]
      exact pow_ne_zero _ (by omega))
  have hsites : ∀ X : Set (FourTorus L m), X.Finite →
      {x : SiteAtLevel L m K n | (x : FourTorus L m) ∈ X}.Finite :=
    fun X hX => hX.preimage Subtype.val_injective.injOn
  have hdouble : (bondDoubleBlock c).Finite := (hblock _).union (hblock _)
  have hbase : c.source.toSublattice (levelDepth K n) ∈
      (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)) := by
    have h := (hy c.source).1.1.2
    change ((c.source.toSublattice (levelDepth K n) : Site L m (levelDepth K n)) : FourTorus L m) ∈
      unitBlock c.source
    rw [← h]
    exact ⟨0, zero_mem_blockIndexBox (by omega), by simp [offsetSite]⟩
  refine
    { finite_source := hsites _ (hblock _)
      finite_target := hsites _ (hblock _)
      finite_bonds := ?_
      contour := fun y hy' x hx τ b hb => (hI.1 y hy' x hx).1 _ ⟨τ, rfl⟩ b hb
      cornered := fun y hy' x hx b hb => (hI.1 y hy' x hx).2 b hb
      crossing := fun x hx b hb => hI.2 x hx b hb
      transport := fun s b hb => ?_
      shift_mem := fun x hx => ?_
      exists_positive := ?_
      not_both_oriented := ?_ }
  · refine Set.Finite.subset (((hsites _ hdouble).prod (hsites _ hdouble)).preimage
      (f := fun b : BondAtLevel L m K n => (b.source, b.target)) ?_) ?_
    · intro b _ b' _ e
      exact Bond.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
    · intro b hb
      exact ⟨hb.1, hb.2⟩
  · have hbase' : schemeBaseSite s (levelDepth K n) c.source ∈
        (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)) := by
      cases s with
      | centred => exact hbase
      | cornered => exact (hy c.source).1.2.2
    have hstraight : axialPath (schemeBaseSite s (levelDepth K n) c.source)
        (schemeBaseSite s (levelDepth K n) c.target) =
        crossingPath c (schemeBaseSite s (levelDepth K n) c.source) := by
      cases s with
      | centred => exact hS.2.1
      | cornered => exact hS.2.2
    rw [hstraight] at hb
    exact hI.2 _ hbase' b hb
  · rw [hD.2.2.2.2.1 x hx, ← hD.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  · refine ⟨Bond.forwardFrom (c.source.toSublattice (levelDepth K n)) μ, hI.2 _ hbase _ ?_, μ, ?_⟩
    · rw [(hS.1 _ hbase).2.1]
      exact forwardFrom_mem_forwardFlow _ _ (by omega)
    · simp [Bond.forwardFrom]
  · rintro b ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
    have h₂' : b.source - b.target = unitStep L m (levelDepth K n) μ₂ := h₂
    have e : offsetSite (c.source.toSublattice (levelDepth K n)) (Pi.single μ₁ 1) =
        offsetSite (c.source.toSublattice (levelDepth K n)) (-Pi.single μ₂ 1) := by
      rw [offsetSite_single, offsetSite_neg_single, ← h₁, ← h₂']
      abel
    have h3 : 3 ≤ L := by omega
    have := (hy c.source).1.1.1 (single_mem_blockIndexBox h3 μ₁).1
      (single_mem_blockIndexBox h3 μ₂).2 e
    have h := congrFun this μ₁
    by_cases q : μ₁ = μ₂
    · subst q
      simp at h
    · simp [Pi.single_eq_of_ne q] at h
private theorem opposite_mem_doubleBlockSet (c : BondAtLevel L m K (n + 1)) :
    ∀ b ∈ doubleBlockSet c, b.opposite ∈ doubleBlockSet c := fun _ hb => ⟨hb.2, hb.1⟩
variable {c : BondAtLevel L m K (n + 1)}
private theorem contourHolonomies_congr (hF : DoubleBlockData c)
    {W W' : BondAtLevel L m K n → ComplexMatrix2}
    (h : ∀ b ∈ doubleBlockSet c, W b = W' b) {y : SiteAtLevel L m K (n + 1)}
    (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hx : x ∈ (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n))) :
    contourHolonomies W y x = contourHolonomies W' y x :=
  funext fun τ => pathHolonomy_congr fun b hb => h b (hF.contour y hy x hx τ b hb)
private theorem contourHolonomy_congr (hF : DoubleBlockData c)
    {W W' : BondAtLevel L m K n → ComplexMatrix2}
    (h : ∀ b ∈ doubleBlockSet c, W b = W' b) {y : SiteAtLevel L m K (n + 1)}
    (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hx : x ∈ (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)))
    (s : AveragingScheme) :
    contourHolonomy s W y x = contourHolonomy s W' y x := by
  cases s with
  | centred =>
    change complexLogMean (contourHolonomies W y x) = complexLogMean (contourHolonomies W' y x)
    rw [contourHolonomies_congr hF h hy hx]
  | cornered => exact pathHolonomy_congr fun b hb => h b (hF.cornered y hy x hx b hb)
private theorem localDefect_congr (hF : DoubleBlockData c)
    {W W' : BondAtLevel L m K n → ComplexMatrix2}
    (h : ∀ b ∈ doubleBlockSet c, W b = W' b) (s : AveragingScheme) {x : SiteAtLevel L m K n}
    (hx : x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n))) :
    localDefect s W c x = localDefect s W' c x := by
  unfold localDefect baseTransport
  rw [contourHolonomy_congr hF h (Or.inl rfl) hx s,
    contourHolonomy_congr hF h (Or.inr rfl) (hF.shift_mem x hx) s,
    pathHolonomy_congr (fun b hb => h b (hF.crossing x hx b hb)),
    pathHolonomy_congr (fun b hb => h b (hF.transport s b hb))]
private theorem isGaugeField_bondsInside {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (doubleBlockSet c) W) {y : SiteAtLevel L m K (n + 1)}
    (hy : y = c.source ∨ y = c.target) :
    IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W := by
  have hsub : (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)) ⊆ doubleBlockSet c := by
    intro b hb
    rcases hy with rfl | rfl
    · exact ⟨Or.inl hb.1, Or.inl hb.2⟩
    · exact ⟨Or.inr hb.1, Or.inr hb.2⟩
  exact ⟨fun b hb => hW.1 b (hsub hb), fun b hb => hW.2 b (hsub hb)⟩
private theorem isContourHolonomyDefined_congr (hF : DoubleBlockData c)
    {W W' : BondAtLevel L m K n → ComplexMatrix2}
    (hW' : IsGaugeField complexGaugeGroup (doubleBlockSet c) W')
    (h : ∀ b ∈ doubleBlockSet c, W b = W' b)
    {s : AveragingScheme} {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target)
    {x : SiteAtLevel L m K n} (hd : IsContourHolonomyDefined s W y x) :
    IsContourHolonomyDefined s W' y x := by
  obtain ⟨h1, -, h3⟩ := hd
  refine ⟨h1, isGaugeField_bondsInside hW' hy, ?_⟩
  cases s with
  | centred =>
    change ComplexMatrix2.familyDiameter (contourHolonomies W' y x) < centreOfMassDiameter
    rw [← contourHolonomies_congr hF h hy h1]
    exact h3
  | cornered => trivial
private theorem isSchemeAverageDefined_congr (hF : DoubleBlockData c)
    {W W' : BondAtLevel L m K n → ComplexMatrix2}
    (hW' : IsGaugeField complexGaugeGroup (doubleBlockSet c) W')
    (h : ∀ b ∈ doubleBlockSet c, W b = W' b)
    {s : AveragingScheme} (hd : IsSchemeAverageDefined s W c) : IsSchemeAverageDefined s W' c := by
  obtain ⟨-, ⟨ha, hb⟩, hc⟩ := hd
  exact ⟨hW', ⟨fun x hx => isContourHolonomyDefined_congr hF hW' h (Or.inl rfl) (ha x hx),
    fun x hx => isContourHolonomyDefined_congr hF hW' h (Or.inr rfl) (hb x hx)⟩,
    fun x hx => by
      rw [← localDefect_congr hF h s hx]
      exact hc x hx⟩
private theorem mem_restrictedDomain_iff (hF : DoubleBlockData c) (s : AveragingScheme)
    (v : PositiveBondOf (doubleBlockSet c) → ComplexMatrix2) :
    v ∈ restrictToPositive (doubleBlockSet c) '' {W | IsSchemeAverageDefined s W c} ↔
      v ∈ GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)) ∧
        IsSchemeAverageDefined s (extendFromPositive (doubleBlockSet c) v) c := by
  constructor
  · rintro ⟨W, hW, rfl⟩
    have hv : restrictToPositive (doubleBlockSet c) W ∈
        GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)) :=
      fun i => hW.1.1 i.1 i.2.1
    exact ⟨hv, isSchemeAverageDefined_congr hF
      (isGaugeField_extendFromPositive (opposite_mem_doubleBlockSet c) hF.not_both_oriented hv)
      (fun b hb =>
        (extendFromPositive_restrict (opposite_mem_doubleBlockSet c) hW.1 hb).symm) hW⟩
  · rintro ⟨-, h⟩
    exact ⟨_, h, restrict_extendFromPositive _ v⟩
section Analytic
variable [Fintype (PositiveBondOf (doubleBlockSet c))]
private theorem localForm_contourHolonomy (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    (hF : DoubleBlockData c) (s : AveragingScheme)
    {p : PositiveBondOf (doubleBlockSet c) → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)))
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hd : IsContourHolonomyDefined s (extendFromPositive (doubleBlockSet c) p) y x) :
    LocalForm p (fun v => contourHolonomy s (extendFromPositive (doubleBlockSet c) v) y x) ∧
      ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))] p,
        IsContourHolonomyDefined s (extendFromPositive (doubleBlockSet c) v) y x := by
  have hconf : ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))] p,
      IsGaugeField complexGaugeGroup (bondsInside (unitBlock y))
        (extendFromPositive (doubleBlockSet c) v) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact isGaugeField_bondsInside
      (isGaugeField_extendFromPositive (opposite_mem_doubleBlockSet c) hF.not_both_oriented hv) hy
  cases s with
  | centred =>
    have : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
    obtain ⟨h₁, h₂⟩ := localForm_complexLogMean hM hp
      (f := fun v => contourHolonomies (extendFromPositive (doubleBlockSet c) v) y x)
      (fun τ => localForm_pathHolonomy _ p _) hd.2.2
    refine ⟨h₁, ?_⟩
    filter_upwards [hconf, h₂] with v a b
    exact ⟨hd.1, a, b⟩
  | cornered =>
    refine ⟨localForm_pathHolonomy _ p _, ?_⟩
    filter_upwards [hconf] with v a
    exact ⟨hd.1, a, trivial⟩
private theorem localForm_localDefect (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    (hF : DoubleBlockData c) (s : AveragingScheme)
    {p : PositiveBondOf (doubleBlockSet c) → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)))
    (hd : AreContourHolonomiesDefined s (extendFromPositive (doubleBlockSet c) p) c)
    {x : SiteAtLevel L m K n}
    (hx : x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n))) :
    LocalForm p fun v => localDefect s (extendFromPositive (doubleBlockSet c) v) c x :=
  (((localForm_contourHolonomy hM hF s hp (Or.inl rfl) (hd.1 x hx)).1.mul
    (localForm_pathHolonomy _ p _)).mul
    (localForm_contourHolonomy hM hF s hp (Or.inr rfl) (hd.2 _ (hF.shift_mem x hx))).1.inv).mul
    (localForm_pathHolonomy _ p _).inv
private theorem eventually_isSchemeAverageDefined
    (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    (hF : DoubleBlockData c) (htarget : (sitesInBlock (levelDepth K n) c.target :
      Set (SiteAtLevel L m K n)).Finite) (s : AveragingScheme)
    {p : PositiveBondOf (doubleBlockSet c) → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)))
    (hd : IsSchemeAverageDefined s (extendFromPositive (doubleBlockSet c) p) c) :
    ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))] p,
      IsSchemeAverageDefined s (extendFromPositive (doubleBlockSet c) v) c := by
  obtain ⟨-, hcv, hnear⟩ := hd
  have h₁ := (Filter.eventually_all_finite hF.finite_source).2 fun x hx =>
    (localForm_contourHolonomy hM hF s hp (Or.inl rfl) (hcv.1 x hx)).2
  have h₂ := (Filter.eventually_all_finite htarget).2 fun x hx =>
    (localForm_contourHolonomy hM hF s hp (Or.inr rfl) (hcv.2 x hx)).2
  have h₃ := (Filter.eventually_all_finite hF.finite_source).2 fun x hx => by
    obtain ⟨F, hFa, hFe⟩ := localForm_localDefect hM hF s hp hcv hx
    have hpF := (hFe.self_of_nhdsWithin hp).1
    have hlt : ∀ᶠ v in 𝓝 p, ‖F v - 1‖ < 1 :=
      (hFa.continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const (by
        change ‖F p - 1‖ < 1
        rw [← hpF]
        exact hnear x hx)
    have : ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))] p,
        ComplexMatrix2.operatorNorm
          (localDefect s (extendFromPositive (doubleBlockSet c) v) c x - 1) < 1 := by
      filter_upwards [hlt.filter_mono nhdsWithin_le_nhds, hFe] with v a b
      rw [b.1]
      exact a
    exact this
  filter_upwards [self_mem_nhdsWithin, h₁, h₂, h₃] with v hv a b d
  exact ⟨isGaugeField_extendFromPositive (opposite_mem_doubleBlockSet c) hF.not_both_oriented hv,
    ⟨a, b⟩, d⟩
private theorem localForm_schemeBlockAverage
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    (hF : DoubleBlockData c) (htarget : (sitesInBlock (levelDepth K n) c.target :
      Set (SiteAtLevel L m K n)).Finite) (hc : c.IsPositivelyOriented) (s : AveragingScheme)
    {p : PositiveBondOf (doubleBlockSet c) → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)))
    (hd : IsSchemeAverageDefined s (extendFromPositive (doubleBlockSet c) p) c) :
    LocalForm p fun v => schemeBlockAverage s (extendFromPositive (doubleBlockSet c) v) c := by
  have hev := eventually_isSchemeAverageDefined hM hF htarget s hp hd
  obtain ⟨-, hcv, hnear⟩ := hd
  have hgerm : ∀ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
      ∃ F : (PositiveBondOf (doubleBlockSet c) → ComplexMatrix2) → ComplexMatrix2,
        AnalyticAt ℂ F p ∧
        ∀ᶠ v in 𝓝[GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))] p,
          localDefect s (extendFromPositive (doubleBlockSet c) v) c x = F v ∧
            localDefect s (extendFromPositive (doubleBlockSet c) v) c x ∈
              ComplexMatrix2.unitDeterminant :=
    fun x hx => localForm_localDefect hM hF s hp hcv hx
  choose! F hFa hFe using hgerm
  obtain ⟨T, hTa, hTe⟩ := localForm_pathHolonomy (doubleBlockSet c) p
    (axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target))
  have hlog : ∀ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
      AnalyticAt ℂ (fun v => ComplexMatrix2.logSeries (F x v)) p := fun x hx => by
    have h := (hFe x hx).self_of_nhdsWithin hp
    have hm : F x p ∈ ComplexMatrix2.logBall := by
      rw [← h.1]
      exact hnear x hx
    exact AnalyticAt.comp (g := ComplexMatrix2.logSeries) (analyticAt_logSeries hm) (hFa x hx)
  let Z : (PositiveBondOf (doubleBlockSet c) → ComplexMatrix2) → ComplexMatrix2 := fun v =>
    inverseFourthPowerWeight L • ∑ x ∈ hF.finite_source.toFinset, ComplexMatrix2.logSeries (F x v)
  have hZ : AnalyticAt ℂ Z p :=
    AnalyticAt.fun_smul analyticAt_const (Finset.analyticAt_fun_sum _ fun x hx =>
      hlog x (hF.finite_source.mem_toFinset.1 hx))
  refine ⟨fun v => ComplexMatrix2.matExp (Z v) * T v,
    (AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic _) hZ).mul hTa, ?_⟩
  have hall := (Filter.eventually_all_finite hF.finite_source).2 hFe
  filter_upwards [hall, hev, hTe] with v h₁ h₂ h₃
  have hsum : ∑ᶠ x ∈ (sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)),
      ComplexMatrix2.logSeries (localDefect s (extendFromPositive (doubleBlockSet c) v) c x) =
      ∑ x ∈ hF.finite_source.toFinset, ComplexMatrix2.logSeries (F x v) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hF.finite_source]
    exact Finset.sum_congr rfl fun x hx => by
      rw [(h₁ x (hF.finite_source.mem_toFinset.1 hx)).1]
  have hval : schemeBlockAverage s (extendFromPositive (doubleBlockSet c) v) c =
      ComplexMatrix2.matExp (Z v) * T v := by
    have e : schemeBlockAverage s (extendFromPositive (doubleBlockSet c) v) c =
        positiveBondAverage s (extendFromPositive (doubleBlockSet c) v) c := if_pos hc
    rw [e]
    unfold positiveBondAverage baseTransport
    rw [hsum, h₃.1]
  refine ⟨hval, ?_⟩
  rw [hval]
  have htr : ComplexMatrix2.fullTrace (Z v) = 0 := by
    change Matrix.trace (inverseFourthPowerWeight L •
      ∑ x ∈ hF.finite_source.toFinset, ComplexMatrix2.logSeries (F x v)) = 0
    rw [Matrix.trace_smul, Matrix.trace_sum, Finset.sum_eq_zero, smul_zero]
    intro x hx
    have hx' := hF.finite_source.mem_toFinset.1 hx
    have h := h₁ x hx'
    rw [← h.1]
    exact trace_logSeries_eq_zero h.2 (h₂.2.2 x hx')
  refine mul_mem_unitDeterminant ?_ ?_
  · change (ComplexMatrix2.matExp (Z v)).det = 1
    rw [hdet, htr, Complex.exp_zero]
  · rw [← h₃.1]
    exact h₃.2
end Analytic
end DoubleBlock
theorem openAndHolomorphic (hP : BlockPaths.Statement)
    (hMean : ComplexLogMeanOfSmallFamilies)
    (hS : UnimodularArguments.HolomorphicAtUnimodular)
    (hE : ComplexMatrix2.ExpLogEstimates) :
    AveragingDomainsOpenAndHolomorphic := by
  intro L hL m K n hm hn s c hc
  have hF : DoubleBlockData c := doubleBlockData hP hL hm hn hc
  have hM : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n := hMean.2.2.2.1
  have hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z) :=
    hE.2.2.2.2.2.1
  have htarget := hF.finite_target
  have hfinite : Finite (PositiveBondOf (doubleBlockSet c)) :=
    (hF.finite_bonds.subset fun b hb => hb.1).to_subtype
  let inst : Fintype (PositiveBondOf (doubleBlockSet c)) := Fintype.ofFinite _
  have : Nonempty (PositiveBondOf (doubleBlockSet c)) := by
    obtain ⟨b, h⟩ := hF.exists_positive
    exact ⟨⟨b, h⟩⟩
  set D := restrictToPositive (doubleBlockSet c) '' {W | IsSchemeAverageDefined s W c} with hDdef
  have hDs : D ⊆ GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c)) :=
    fun v hv => ((mem_restrictedDomain_iff hF s v).1 hv).1
  have hloc : ∀ p ∈ D,
      D ∈ 𝓝[GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))] p := by
    intro p hp
    obtain ⟨hpg, hpd⟩ := (mem_restrictedDomain_iff hF s p).1 hp
    filter_upwards [self_mem_nhdsWithin,
      eventually_isSchemeAverageDefined hM hF htarget s hpg hpd] with v a b
    exact (mem_restrictedDomain_iff hF s v).2 ⟨a, b⟩
  have hDo : ComplexMatrix2.IsRelativelyOpen
      (GroupLieProduct.unimodularPi (PositiveBondOf (doubleBlockSet c))) D := by
    choose! U hUo hUp hUs using fun p (hp : p ∈ D) => mem_nhdsWithin.1 (hloc p hp)
    refine ⟨⋃ p ∈ D, U p, isOpen_biUnion hUo, ?_⟩
    ext v
    constructor
    · intro hv
      exact ⟨mem_biUnion hv (hUp v hv), hDs hv⟩
    · rintro ⟨hv, hg⟩
      obtain ⟨p, hp, hvp⟩ := mem_iUnion₂.1 hv
      exact hUs p hp ⟨hvp, hg⟩
  refine ⟨hDo, fun y hy x hx => ?_, ?_⟩
  · have hy' : y = c.source ∨ y = c.target := by simpa using hy
    have h := holomorphic_of_localForms hS hDs hDo
      (f := fun v => contourHolonomy s (extendFromPositive (doubleBlockSet c) v) y x)
      fun p hp => by
        obtain ⟨hpg, hpd⟩ := (mem_restrictedDomain_iff hF s p).1 hp
        have hcd : IsContourHolonomyDefined s (extendFromPositive (doubleBlockSet c) p) y x := by
          rcases hy' with rfl | rfl
          · exact hpd.2.1.1 x hx
          · exact hpd.2.1.2 x hx
        exact (localForm_contourHolonomy hM hF s hpg hy' hcd).1
    exact ⟨⟨inst, h.1⟩, h.2⟩
  · have h := holomorphic_of_localForms hS hDs hDo
      (f := fun v => schemeBlockAverage s (extendFromPositive (doubleBlockSet c) v) c)
      fun p hp => by
        obtain ⟨hpg, hpd⟩ := (mem_restrictedDomain_iff hF s p).1 hp
        exact localForm_schemeBlockAverage hdet hM hF htarget hc s hpg hpd
    exact ⟨⟨inst, h.1⟩, h.2⟩
end YangMills.Construction.PeriodicLattice.AveragingDomains
