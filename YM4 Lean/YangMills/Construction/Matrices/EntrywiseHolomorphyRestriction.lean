import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.EntrywiseHolomorphicMaps
import YangMills.Construction.Matrices.ExpLogEstimates
import Mathlib
open Filter Set
open scoped Matrix.Norms.L2Operator Topology NNReal ENNReal
noncomputable section
namespace YangMills.Construction.Matrices.EntrywiseHolomorphy
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
section MultiIndexedSeries
variable {N : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
private def multiDegree (m : Fin N → ℕ) : ℕ := ∑ j, m j
private theorem exists_word_prod_eq (k : ℕ) (m : Fin N → ℕ) (hm : ∑ j, m j = k) :
    ∃ σ : Fin k → Fin N, ∀ g : Fin N → ℂ, ∏ i, g (σ i) = ∏ j, g j ^ m j := by
  subst hm
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun g => ?_⟩
  refine (Fintype.prod_equiv finSigmaFinEquiv.symm (fun i => g (finSigmaFinEquiv.symm i).1)
    (fun x : (j : Fin N) × Fin (m j) => g x.1) (fun _ => rfl)).trans ?_
  rw [Fintype.prod_sigma]
  simp
abbrev _root_.YangMills.SharedProofs.p39221 := @exists_word_prod_eq
private theorem exists_monomial_multilinear (k : ℕ) (m : Fin N → ℕ) (hm : multiDegree m = k)
    (v : V) :
    ∃ T : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin N → ℂ) V,
      (∀ y : Fin N → ℂ, T (fun _ => y) = (∏ j, y j ^ m j) • v) ∧ ‖T‖ ≤ ‖v‖ := by
  obtain ⟨σ, hσ⟩ := exists_word_prod_eq k m hm
  let M : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin N → ℂ) ℂ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compContinuousLinearMap
      fun i => ContinuousLinearMap.proj (σ i)
  have hM : ∀ w : Fin k → Fin N → ℂ, M w = ∏ i, w i (σ i) := fun w => by simp [M]
  refine ⟨M.smulRight v, fun y => ?_, ?_⟩
  · rw [ContinuousMultilinearMap.smulRight_apply, hM, hσ fun j => y j]
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg v) fun w => ?_
    rw [ContinuousMultilinearMap.smulRight_apply, hM, norm_smul, norm_prod, mul_comm]
    gcongr with i
    exact norm_le_pi_norm (w i) (σ i)
private theorem analyticAt_of_hasSum_multiIndexed [CompleteSpace V] (a : Fin N → ℂ)
    (c : (Fin N → ℕ) → V) (f : (Fin N → ℂ) → V) (r : ℝ≥0) (hr : 0 < r)
    (hsum : ∀ y : Fin N → ℂ, ‖y‖ < r → HasSum (fun m => (∏ j, y j ^ m j) • c m) (f (a + y)))
    (hbound : Summable fun m : Fin N → ℕ => (r : ℝ) ^ multiDegree m * ‖c m‖) :
    AnalyticAt ℂ f a := by
  classical
  let S : ℕ → Finset (Fin N → ℕ) := fun k => Finset.piAntidiag Finset.univ k
  have hS : ∀ k m, m ∈ S k ↔ multiDegree m = k := by
    intro k m
    simp [S, multiDegree, Finset.mem_piAntidiag]
  have hT : ∀ k (m : S k), ∃ T : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin N → ℂ) V,
      (∀ y : Fin N → ℂ, T (fun _ => y) = (∏ j, y j ^ m.1 j) • c m.1) ∧ ‖T‖ ≤ ‖c m.1‖ :=
    fun k m => exists_monomial_multilinear k m.1 ((hS k m.1).1 m.2) (c m.1)
  choose T hTv hTn using hT
  let p : FormalMultilinearSeries ℂ (Fin N → ℂ) V := fun k => ∑ m : S k, T k m
  have hp : ∀ k (y : Fin N → ℂ),
      p k (fun _ => y) = ∑ m ∈ S k, (∏ j, y j ^ m j) • c m := by
    intro k y
    simp only [p, _root_.sum_apply, hTv]
    exact Finset.sum_coe_sort (S k) fun m => (∏ j, y j ^ m j) • c m
  have hnorm : ∀ k, ‖p k‖ * (r : ℝ) ^ k ≤ ∑' m, (r : ℝ) ^ multiDegree m * ‖c m‖ := by
    intro k
    calc ‖p k‖ * (r : ℝ) ^ k ≤ (∑ m : S k, ‖c m.1‖) * (r : ℝ) ^ k := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hTn k m)
      _ = ∑ m ∈ S k, (r : ℝ) ^ multiDegree m * ‖c m‖ := by
          rw [Finset.sum_mul,
            ← Finset.sum_coe_sort (S k) fun m => (r : ℝ) ^ multiDegree m * ‖c m‖]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [(hS k m.1).1 m.2, mul_comm]
      _ ≤ _ := hbound.sum_le_tsum _ fun _ _ => by positivity
  refine ⟨p, (r : ℝ≥0∞), p.le_radius_of_bound _ hnorm, ENNReal.coe_pos.2 hr, ?_⟩
  intro y hy
  have hy₀ : ‖y‖₊ < r := by
    simpa [Metric.eball, edist_zero_right, enorm_eq_nnnorm] using hy
  have hy' : ‖y‖ < r := NNReal.coe_lt_coe.2 hy₀
  have hfib := (hsum y hy').tsum_fiberwise multiDegree
  convert hfib using 2 with k
  rw [hp]
  have hset : multiDegree ⁻¹' {k} = (↑(S k) : Set (Fin N → ℕ)) := by
    ext m
    simp [hS]
  rw [hset]
  exact (Finset.tsum_subtype' (S k) fun m => (∏ j, y j ^ m j) • c m).symm
end MultiIndexedSeries
private theorem analyticAt_of_hasPowerSeriesSumOn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {f : ComplexCoordinates N → ComplexCoordinates N'} {a : ComplexCoordinates N}
    (ha : a ∈ O) (h : ∀ ρ > 0, closedPolydisk a ρ ⊆ O → HasPowerSeriesSumOn f a ρ) :
    AnalyticAt ℂ f a := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO a ha
  have hρ : 0 < ε / 2 := by positivity
  have hsub : closedPolydisk a (ε / 2) ⊆ O := by
    intro z hz
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hρ.le).2 fun j => ?_) (by linarith)
    exact hz j
  obtain ⟨c, hc, hs⟩ := h _ hρ hsub
  have hr : 0 < ε / 4 := by positivity
  have hlt : ε / 4 < ε / 2 := by linarith
  refine analyticAt_of_hasSum_multiIndexed a c f ⟨ε / 4, hr.le⟩ (by exact_mod_cast hr)
    (fun y hy => ?_) ?_
  · have hmem : a + y ∈ openPolydisk a (ε / 2) := by
      intro j
      have h₁ : ‖y j‖ ≤ ‖y‖ := norm_le_pi_norm y j
      have h₂ : ‖y‖ < ε / 4 := hy
      simpa using lt_of_le_of_lt h₁ (h₂.trans hlt)
    have hterm : monomialTerm c a (a + y) = fun m => (∏ j, y j ^ m j) • c m := by
      funext m
      simp [monomialTerm]
    rw [← hterm]
    exact hc _ hmem
  · have hmem : a + (fun _ => ((ε / 4 : ℝ) : ℂ)) ∈ closedPolydisk a (ε / 4) := by
      intro j
      simp only [Pi.add_apply, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, le_refl]
    refine ((hs _ hlt).1 _ hmem).congr fun m => ?_
    simp only [monomialTerm, Pi.add_apply, add_sub_cancel_left, norm_smul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Finset.prod_pow_eq_pow_sum, multiDegree]
    rfl
private def IsLinearCoords {E : Type} [AddCommGroup E] [Module ℂ E] {M : ℕ}
    (e : E ≃ ComplexCoordinates M) : Prop :=
  (∀ x y, e (x + y) = e x + e y) ∧ ∀ (t : ℂ) x, e (t • x) = t • e x
private def linearCoordsEquiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {M : ℕ} (e : E ≃ ComplexCoordinates M) (h : IsLinearCoords e) :
    E ≃L[ℂ] ComplexCoordinates M :=
  LinearEquiv.toContinuousLinearEquiv
    { e with map_add' := h.1, map_smul' := h.2 }
private theorem analyticAt_of_analyticAt_coords {E E' : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [FiniteDimensional ℂ E'] {M M' : ℕ} (e : E ≃ ComplexCoordinates M)
    (e' : E' ≃ ComplexCoordinates M') (he : IsLinearCoords e) (he' : IsLinearCoords e')
    {f : E → E'} {x : E} (h : AnalyticAt ℂ (e' ∘ f ∘ e.symm) (e x)) : AnalyticAt ℂ f x := by
  let L := linearCoordsEquiv e he
  let L' := linearCoordsEquiv e' he'
  have hL : AnalyticAt ℂ L x := L.toContinuousLinearMap.analyticAt x
  have h₁ : AnalyticAt ℂ ((e' ∘ f ∘ e.symm) ∘ L) x :=
    AnalyticAt.comp (f := L) (g := e' ∘ f ∘ e.symm) h hL
  have h₂ : AnalyticAt ℂ (L'.symm ∘ ((e' ∘ f ∘ e.symm) ∘ L)) x :=
    AnalyticAt.comp (L'.symm.toContinuousLinearMap.analyticAt _) h₁
  convert h₂ using 1
  funext y
  change f y = e'.symm (e' (f (e.symm (e y))))
  simp
private theorem matrixEquiv_isLinearCoords : IsLinearCoords matrixEquiv :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
private theorem productEquiv_isLinearCoords (n : ℕ) :
    IsLinearCoords (E := Fin n → ComplexMatrix2) (productEquiv (matrixKinds n)) := by
  let pos : Fin (productDim (matrixKinds n)) → (i : Fin n) × Fin 4 := fun k =>
    (finSigmaFinEquiv (n := fun i => (matrixKinds n i).dim)).symm k
  have key : ∀ (z : Fin n → ComplexMatrix2) (k : Fin (productDim (matrixKinds n))),
      productEquiv (matrixKinds n) z k = matrixEquiv (z (pos k).1) (pos k).2 :=
    fun _ _ => rfl
  refine ⟨fun x y => ?_, fun t x => ?_⟩
  · funext k
    exact (key (x + y) k).trans ((congrFun (matrixEquiv_isLinearCoords.1 _ _) _).trans
      (congrArg₂ (· + ·) (key x k).symm (key y k).symm))
  · funext k
    exact (key (t • x) k).trans ((congrFun (matrixEquiv_isLinearCoords.2 _ _) _).trans
      (congrArg (t • ·) (key x k).symm))
private theorem isHolomorphicIn_of_analyticAt {N N' : ℕ} {W : Set (ComplexCoordinates N)}
    (hW : IsOpen W) {g : ComplexCoordinates N → ComplexCoordinates N'}
    (h : ∀ w ∈ W, AnalyticAt ℂ g w) : IsHolomorphicIn W g := by
  refine ⟨hW, fun w hw => (h w hw).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • (stdBasisVector j : ComplexCoordinates N) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • (stdBasisVector j : ComplexCoordinates N) ∈ W :=
    hline.continuousAt.eventually (by simpa using hW.mem_nhds ha)
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • (stdBasisVector j : ComplexCoordinates N)) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := g) ζ (h _ hζ).differentiableAt hd
private theorem analyticAt_expChart_tracelessTuple {n : ℕ}
    (hexp : ∀ Z : ComplexMatrix2, AnalyticAt ℂ ComplexMatrix2.matExp Z)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (X : Fin n → ComplexMatrix2)
    (w : ComplexCoordinates (n * 3)) :
    AnalyticAt ℂ (fun w => expChart X (tracelessTuple b w)) w := by
  refine analyticAt_pi_iff.2 fun i => ?_
  have hl : AnalyticAt ℂ (fun w : ComplexCoordinates (n * 3) => tracelessTuple b w i) w :=
    Finset.analyticAt_fun_sum _ fun c _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * 3) => ℂ)
        (finProdFinEquiv (i, c))).analyticAt w).smul analyticAt_const
  have he : AnalyticAt ℂ
      (fun w : ComplexCoordinates (n * 3) => ComplexMatrix2.matExp (tracelessTuple b w i)) w :=
    AnalyticAt.comp (g := ComplexMatrix2.matExp) (hexp _) hl
  exact he.mul analyticAt_const
private theorem expChart_mem_unimodularPow {n : ℕ}
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {X : Fin n → ComplexMatrix2}
    (hX : X ∈ unimodularPow n) (w : ComplexCoordinates (n * 3)) :
    expChart X (tracelessTuple b w) ∈ unimodularPow n := by
  intro i
  have hmem : tracelessTuple b w i ∈ ComplexMatrix2.traceless :=
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2
  have htr : ComplexMatrix2.fullTrace (tracelessTuple b w i) = 0 := hmem
  have hXi : (X i).det = 1 := hX i
  change (ComplexMatrix2.matExp (tracelessTuple b w i) * X i).det = 1
  rw [Matrix.det_mul, hdet, htr, hXi, Complex.exp_zero, one_mul]
private theorem expChart_tracelessTuple_zero {n : ℕ}
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (X : Fin n → ComplexMatrix2) :
    expChart X (tracelessTuple b 0) = X := by
  funext i
  simp [expChart, tracelessTuple, ComplexMatrix2.matExp]
private theorem exists_nhds_logSeries_expChartQuotient {n : ℕ}
    {O : Set (Fin n → ComplexMatrix2)} (hO : IsOpen O)
    {F : (Fin n → ComplexMatrix2) → ComplexMatrix2} (hanF : ∀ X ∈ O, AnalyticAt ℂ F X)
    (hexp : ∀ Z : ComplexMatrix2, AnalyticAt ℂ ComplexMatrix2.matExp Z)
    (hlog : ∀ Z ∈ ComplexMatrix2.logBall, AnalyticAt ℂ ComplexMatrix2.logSeries Z)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {X : Fin n → ComplexMatrix2}
    (hX : X ∈ O) (hdet : (F X).det = 1) :
    ∃ W : Set (ComplexCoordinates (n * 3)), 0 ∈ W ∧
      (∀ w ∈ W, expChart X (tracelessTuple b w) ∈ O ∧
        expChartQuotient F X (tracelessTuple b w) ∈ ComplexMatrix2.logBall) ∧
      IsHolomorphicIn W fun w =>
        matrixEquiv (ComplexMatrix2.logSeries (expChartQuotient F X (tracelessTuple b w))) := by
  let chart : ComplexCoordinates (n * 3) → Fin n → ComplexMatrix2 :=
    fun w => expChart X (tracelessTuple b w)
  let Q : ComplexCoordinates (n * 3) → ComplexMatrix2 :=
    fun w => expChartQuotient F X (tracelessTuple b w)
  have hchartAn : ∀ w, AnalyticAt ℂ chart w := analyticAt_expChart_tracelessTuple hexp b X
  have hQan : ∀ w, chart w ∈ O → AnalyticAt ℂ Q w := fun w hw =>
    (AnalyticAt.comp (g := F) (hanF _ hw) (hchartAn w)).mul analyticAt_const
  have hlogOpen : IsOpen ComplexMatrix2.logBall :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  let W : Set (ComplexCoordinates (n * 3)) := {w | chart w ∈ O ∧ Q w ∈ ComplexMatrix2.logBall}
  have hWopen : IsOpen W := by
    refine isOpen_iff_mem_nhds.2 fun w hw => ?_
    exact ((hchartAn w).continuousAt.eventually (hO.mem_nhds hw.1)).and
      ((hQan w hw.1).continuousAt.eventually (hlogOpen.mem_nhds hw.2))
  have hW0 : (0 : ComplexCoordinates (n * 3)) ∈ W := by
    have hchart0 : chart 0 = X := expChart_tracelessTuple_zero b X
    have hX0 : chart 0 ∈ O := by rw [hchart0]; exact hX
    refine ⟨hX0, ?_⟩
    have hone : Q 0 = 1 := by
      change F (chart 0) * (F X)⁻¹ = 1
      rw [hchart0]
      exact Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
    change ComplexMatrix2.operatorNorm (Q 0 - 1) < 1
    rw [hone, sub_self]
    simp [ComplexMatrix2.operatorNorm]
  refine ⟨W, hW0, fun w hw => hw, isHolomorphicIn_of_analyticAt hWopen fun w hw => ?_⟩
  have hl : AnalyticAt ℂ (fun w => ComplexMatrix2.logSeries (Q w)) w :=
    AnalyticAt.comp (g := ComplexMatrix2.logSeries) (hlog _ hw.2) (hQan w hw.1)
  exact AnalyticAt.comp
    ((linearCoordsEquiv matrixEquiv matrixEquiv_isLinearCoords).toContinuousLinearMap.analyticAt
      _) hl
private theorem analyticAt_of_isHolomorphicVia {E E' : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [FiniteDimensional ℂ E'] {M M' : ℕ} (e : E ≃ ComplexCoordinates M)
    (e' : E' ≃ ComplexCoordinates M') (he : IsLinearCoords e) (he' : IsLinearCoords e')
    {O : Set E} {f : E → E'} (hf : IsHolomorphicVia e e' O f)
    (hs : ∀ a ∈ e '' O, ∀ ρ > 0, closedPolydisk a ρ ⊆ e '' O →
      HasPowerSeriesSumOn (e' ∘ f ∘ e.symm) a ρ) {x : E} (hx : x ∈ O) : AnalyticAt ℂ f x :=
  analyticAt_of_analyticAt_coords e e' he he'
    (analyticAt_of_hasPowerSeriesSumOn hf.1 (mem_image_of_mem _ hx)
      (hs _ (mem_image_of_mem _ hx)))
private def HolomorphicHasPowerSeries : Prop :=
  ∀ (N : ℕ) (O : Set (ComplexCoordinates N)), IsOpen O → ∀ (N' : ℕ)
    (f : ComplexCoordinates N → ComplexCoordinates N'), IsHolomorphicIn O f →
    ∀ a ∈ O, ∀ ρ > 0, closedPolydisk a ρ ⊆ O → HasPowerSeriesSumOn f a ρ
private theorem analyticAt_of_matrixMap (hser : HolomorphicHasPowerSeries)
    {O : Set ComplexMatrix2} {f : ComplexMatrix2 → ComplexMatrix2}
    (hf : IsHolomorphicVia matrixEquiv matrixEquiv O f) {x : ComplexMatrix2} (hx : x ∈ O) :
    AnalyticAt ℂ f x :=
  analyticAt_of_isHolomorphicVia matrixEquiv matrixEquiv matrixEquiv_isLinearCoords
    matrixEquiv_isLinearCoords hf (hser _ _ hf.1 _ _ hf) hx
private theorem analyticAt_of_isEntrywiseHolomorphic (hser : HolomorphicHasPowerSeries) {n : ℕ}
    {O : Set (Fin n → ComplexMatrix2)} {F : (Fin n → ComplexMatrix2) → ComplexMatrix2}
    (hF : IsEntrywiseHolomorphic O F) {X : Fin n → ComplexMatrix2} (hX : X ∈ O) :
    AnalyticAt ℂ F X :=
  analyticAt_of_isHolomorphicVia (E := Fin n → ComplexMatrix2) (E' := ComplexMatrix2)
    (productEquiv (matrixKinds n)) matrixEquiv
    (productEquiv_isLinearCoords n) matrixEquiv_isLinearCoords hF (hser _ _ hF.1 _ _ hF) hX
private theorem restriction_of_analyticAt
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (hanExp : ∀ Z : ComplexMatrix2, AnalyticAt ℂ ComplexMatrix2.matExp Z)
    (hanLog : ∀ Z ∈ ComplexMatrix2.logBall, AnalyticAt ℂ ComplexMatrix2.logSeries Z) {n : ℕ}
    (hn : 1 ≤ n) {O : Set (Fin n → ComplexMatrix2)} (hO : IsOpen O)
    {F : (Fin n → ComplexMatrix2) → ComplexMatrix2} (hanF : ∀ X ∈ O, AnalyticAt ℂ F X)
    (hG : ∀ X ∈ O ∩ unimodularPow n, F X ∈ ComplexMatrix2.unitDeterminant) :
    (ComplexMatrix2.IsRelativelyOpen (unimodularPow n) (O ∩ unimodularPow n) ∧
      (∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
        ComplexCoordinates.IsHolomorphicOnSL2Power b (O ∩ unimodularPow n) F) ∧
      ComplexMatrix2.IsHolomorphicBetween (groupKinds n) targetKind (O ∩ unimodularPow n)
        fun X _ => F X) ∧
    ∀ S : Set (Fin n → ComplexMatrix2), S ⊆ O ∩ unitaryPow n →
      ComplexMatrix2.IsRelativelyOpen (unitaryPow n) S →
      (∀ X ∈ S, F X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) →
      ComplexMatrix2.IsRealAnalyticBetween (groupKinds n) targetKind S fun X _ => F X := by
  have hcont : ContinuousOn F O := fun X hX => (hanF X hX).continuousAt.continuousWithinAt
  have hopen : ComplexMatrix2.IsRelativelyOpen (unimodularPow n) (O ∩ unimodularPow n) :=
    ⟨O, hO, rfl⟩
  have hhol : ComplexMatrix2.IsHolomorphicBetween (groupKinds n) targetKind
      (O ∩ unimodularPow n) fun X _ => F X := by
    refine ⟨hopen, fun X hX _ => hG X hX, fun X hX => ⟨fun Y _ => F Y, ?_,
      Eventually.of_forall fun _ => rfl⟩⟩
    exact analyticAt_pi_iff.2 fun _ => hanF X hX.1
  refine ⟨⟨hopen, fun b => ?_, hhol⟩, fun S hS hSo hSG => ⟨hSo, fun X hX =>
    ⟨O ∩ unimodularPow n, fun Y _ => F Y, ⟨(hS hX).1, fun i => ?_⟩, hhol,
      Eventually.of_forall fun _ => rfl⟩⟩⟩
  · refine ⟨hn, hopen, hG, hcont.mono inter_subset_left, fun X hX => ?_⟩
    obtain ⟨W, h0, hW, hholW⟩ :=
      exists_nhds_logSeries_expChartQuotient hO hanF hanExp hanLog b hX.1 (hG X hX)
    exact ⟨W, h0, fun w hw =>
      ⟨⟨(hW w hw).1, expChart_mem_unimodularPow hdet b hX.2 w⟩, (hW w hw).2⟩, hholW⟩
  · exact (Matrix.mem_specialUnitaryGroup_iff.1 ((hS hX).2 i)).2
theorem restrictionStatement_of_expLogEstimates (hlog : ComplexMatrix2.ExpLogEstimates)
    (hholo : ComplexCoordinates.PowerSeriesHolomorphy.Properties) : RestrictionStatement := by
  have hser : HolomorphicHasPowerSeries := fun N O hO N' f hf => ((hholo.1 N O hO).1 N' f hf).1
  intro n hn O hO F hF hG
  exact restriction_of_analyticAt hlog.2.2.2.2.2.1
    (fun Z => analyticAt_of_matrixMap hser hholo.2.2.2.2.1 (mem_univ Z))
    (fun Z hZ => analyticAt_of_matrixMap hser hholo.2.2.2.2.2 hZ) hn hO
    (fun X hX => analyticAt_of_isEntrywiseHolomorphic hser hF hX) hG
end YangMills.Construction.Matrices.EntrywiseHolomorphy
