import YangMills.Construction.ClusterExpansionOfAStep.PartsOfTheCostAlongMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields StepSettings StepSettings.ChartSetting CostDerivatives FreeBondMoves FreeBonds WideCharts
  WideChartFloor LevelAction QuaternionLogarithm ColdStepAtMirrorFrames
theorem areUnitVectors_single {p : ImaginaryCoord} (hp : ‖p‖ = 1) : AreUnitVectors ![toImaginary p] := by
  intro l
  fin_cases l
  simpa [norm_toImaginary] using hp
theorem areUnitVectors_pair {p q : ImaginaryCoord} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    AreUnitVectors ![toImaginary p, toImaginary q] := by
  intro l
  fin_cases l
  · simpa [norm_toImaginary] using hp
  · simpa [norm_toImaginary] using hq
theorem supDist_le_bondListSpread_pair {m : ℕ} (b b' : TorusBond m) : _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 ≤ bondListSpread ![b, b'] := by
  unfold bondListSpread
  refine le_trans ?_ (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
    _root_.YangMills.Construction.TorusFields.supDist ((![b, b'] : Fin 2 → TorusBond m) l).1 ((![b, b'] : Fin 2 → TorusBond m) l').1) (Finset.mem_univ 0))
  exact Finset.le_sup (f := fun l' : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist ((![b, b'] : Fin 2 → TorusBond m) 0).1
    ((![b, b'] : Fin 2 → TorusBond m) l').1) (Finset.mem_univ 1)
theorem bondListSpread_single {m : ℕ} [NeZero m] (b : TorusBond m) : bondListSpread ![b] = 0 := by
  unfold bondListSpread
  refine Nat.le_zero.mp (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  rw [Subsingleton.elim l l', _root_.YangMills.Construction.TorusFields.supDist_self]
theorem mul_exp_le_of_near {δ C ε : ℝ} {r k : ℕ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hε : 3 * C * Real.exp 1 * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) ≤ ε) (hk : 4 * k + 4 ≤ r) :
    C * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 8) ≤ ε * Real.exp (-(δ / 4) * k) := by
  have hk' : (4 : ℝ) * k + 4 ≤ r := by exact_mod_cast hk
  have h1 : Real.exp (-δ * r / 8) ≤ Real.exp (-δ * r / 16) * Real.exp (-(δ / 4) * k) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hs := Real.exp_pos (-(δ / 4) * k)
  have h2 : C * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) ≤ ε := by
    refine le_trans ?_ hε
    have : 0 ≤ C * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) := by positivity
    have h3 : 3 * C * Real.exp 1 * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) =
        (3 * Real.exp 1) * (C * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16)) := by ring
    rw [h3]
    nlinarith
  calc C * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 8)
      ≤ C * ((r : ℝ) + 1) ^ 4 * (Real.exp (-δ * r / 16) * Real.exp (-(δ / 4) * k)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (C * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16)) * Real.exp (-(δ / 4) * k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hs.le
theorem mul_exp_le_of_far {δ C ε : ℝ} {r k : ℕ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hC : 0 ≤ C)
    (hε : 3 * C * Real.exp 1 * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) ≤ ε) (hk : r < 4 * k + 4) :
    2 * C * Real.exp (-δ * k) ≤ ε * Real.exp (-(δ / 4) * k) := by
  have hk' : (r : ℝ) ≤ 4 * k + 4 := by exact_mod_cast hk.le
  have h1 : Real.exp (-δ * k) ≤ Real.exp 1 * Real.exp (-δ * r / 16) * Real.exp (-(δ / 4) * k) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hP : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hs := Real.exp_pos (-(δ / 4) * k)
  have h2 : 2 * C * Real.exp 1 * Real.exp (-δ * r / 16) ≤ ε := by
    refine le_trans ?_ hε
    have hb : 0 ≤ C * Real.exp 1 * Real.exp (-δ * r / 16) := by positivity
    have h3 : 3 * C * Real.exp 1 * ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) =
        3 * (C * Real.exp 1 * Real.exp (-δ * r / 16)) * ((r : ℝ) + 1) ^ 4 := by ring
    rw [h3]
    nlinarith
  calc 2 * C * Real.exp (-δ * k)
      ≤ 2 * C * (Real.exp 1 * Real.exp (-δ * r / 16) * Real.exp (-(δ / 4) * k)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 * C * Real.exp 1 * Real.exp (-δ * r / 16)) * Real.exp (-(δ / 4) * k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hs.le
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
theorem mem_coolRegion_and_sitesUnderRegion (c : s.ChainContext δ lam σA cg N) {b₀ : TorusBond (n * R.params.side)}
    (hb : b₀ ∈ s.free) {y : TorusSite (n * R.params.side)} (hy : _root_.YangMills.Construction.TorusFields.supDist y b₀.1 ≤ 3 * R.range) :
    y ∈ s.coolRegion ∧ y ∈ s.sitesUnderRegion := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hy
  exact ⟨mem_coolRegion_of_near_free c.admissible c.large_range hb hy,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, parentBlock_mem_region_of_near_free c.admissible c.large_range hb hy⟩⟩
theorem isNearFree_of_supDist_le {b₀ : TorusBond (n * R.params.side)} (hb : b₀ ∈ s.free)
    {y : TorusSite (n * R.params.side)} {i : Fin 4} (hy : _root_.YangMills.Construction.TorusFields.supDist y b₀.1 ≤ 2 * R.range) : s.IsNearFree (y, i) :=
  ⟨b₀, hb, by
    show _root_.YangMills.Construction.TorusFields.supDist b₀.1 y ≤ 2 * R.range + 2
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    omega⟩
theorem supDist_le_half_card {m : ℕ} [NeZero m] (x y : TorusSite m) : _root_.YangMills.Construction.TorusFields.supDist x y ≤ m / 2 := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  exact fun i => ZMod.natAbs_valMinAbs_le _
theorem coolRegion_eq_and_field_eq_of_small (c : s.ChainContext δ lam σA cg N)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (η₀ : FreeCoords s.free) {b₀ : TorusBond (n * R.params.side)} (hb : b₀ ∈ s.free)
    (hsmall : ¬ 2 * R.range + 2 < n * R.params.side) :
    s.coolRegion = s.sitesUnderRegion ∧ s.chartedFieldAt η₀ = s.wideChartAt w η₀ := by
  have hbig := c.large_range.range_large
  have hall : ∀ y : TorusSite (n * R.params.side), _root_.YangMills.Construction.TorusFields.supDist y b₀.1 ≤ 2 * R.range := by
    intro y
    have := _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card y b₀.1
    omega
  refine ⟨?_, ?_⟩
  · ext y
    have h := mem_coolRegion_and_sitesUnderRegion c hb (y := y) ((hall y).trans (by omega))
    exact iff_of_true h.1 h.2
  · funext y i
    exact (torusChart_wideCoords c w η₀ (isNearFree_of_supDist_le hb (hall y))).symm
variable {C : ℝ} {σ' : ℝ} {w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions}
theorem abs_fderiv_regionAction_le (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA C R.params.side) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) (b : s.free) (u : ImaginaryCoord) (hu : ‖u‖ = 1) :
    |fderiv ℝ (s.regionActionMoves η₀) 0 (Pi.single b u)| ≤ C := by
  rw [fderiv_alongMoves (contDiffThreeAt_action_coolRegion c hF hη₀)]
  have h := (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.coolRegion _
    (isRegularRegion_coolRegion c.complement_regular c.params_admissible s)
    (isColdOn_chartedFieldAt c hη₀)).2.1 1 ![(b : TorusBond (n * R.params.side))] ![toImaginary u] le_rfl
    (by norm_num) (areUnitVectors_single hu)
  rw [bondListSpread_single] at h
  simpa using h
theorem abs_second_fderiv_regionAction_le (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA C R.params.side) (hC : 0 ≤ C)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) (b b' : s.free) (u u' : ImaginaryCoord) (hu : ‖u‖ = 1)
    (hu' : ‖u'‖ = 1) :
    |fderiv ℝ (fderiv ℝ (s.regionActionMoves η₀)) 0 (Pi.single b u) (Pi.single b' u')| ≤
      C * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by
  rw [second_fderiv_alongMoves (contDiffThreeAt_action_coolRegion c hF hη₀)]
  have hδ : 0 < δ := c.chain.1
  have h := (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.coolRegion _
    (isRegularRegion_coolRegion c.complement_regular c.params_admissible s)
    (isColdOn_chartedFieldAt c hη₀)).2.1 2
    ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))] ![toImaginary u, toImaginary u']
    (by norm_num) (by norm_num) (areUnitVectors_pair hu hu')
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
  have h1 : (_root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1 : ℝ) ≤
      bondListSpread ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))] := by
    exact_mod_cast _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_bondListSpread_pair _ _
  nlinarith
theorem abs_fderiv_nearFit_le (c : s.ChainContext δ lam σA cg N) {K : ℝ}
    (hK : AlignmentDerivativeBounds R.params.side K) (hK0 : 0 ≤ K)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) (b : s.free) (u : ImaginaryCoord) (hu : ‖u‖ = 1) :
    |fderiv ℝ (s.nearFitMoves η₀) 0 (Pi.single b u)| ≤ R.params.coupling * (4 * 13 ^ 4 * K) := by
  rw [fderiv_alongMoves (contDiffThreeAt_nearFitSum c hη₀)]
  exact abs_mixedDeriv_one_nearFitSum_le c hK hK0 hη₀ _ _ (areUnitVectors_single hu)
theorem abs_second_fderiv_nearFit_le (c : s.ChainContext δ lam σA cg N) {K : ℝ}
    (hK : AlignmentDerivativeBounds R.params.side K) (hK0 : 0 ≤ K)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) (b b' : s.free) (u u' : ImaginaryCoord) (hu : ‖u‖ = 1)
    (hu' : ‖u'‖ = 1) :
    |fderiv ℝ (fderiv ℝ (s.nearFitMoves η₀)) 0 (Pi.single b u) (Pi.single b' u')| ≤
      alignmentExpansionBound R.params.side R.params.coupling K (b : TorusBond (n * R.params.side)) b' := by
  rw [second_fderiv_alongMoves (contDiffThreeAt_nearFitSum c hη₀)]
  exact abs_mixedDeriv_two_nearFitSum_le c hK hK0 hη₀ _ _ _ (areUnitVectors_pair hu hu')
theorem abs_fderiv_sub_le (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA C R.params.side) (hC : 0 ≤ C)
    (hm : s.MinimizerData lam σA (N 0) σ' w) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) {ε : ℝ}
    (hε : 3 * C * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-δ * R.range / 16) ≤ ε) (b : s.free)
    (u : ImaginaryCoord) (hu : ‖u‖ = 1) :
    |fderiv ℝ (s.regionActionMoves η₀) 0 (Pi.single b u) - fderiv ℝ (s.coreActionMoves w η₀) 0 (Pi.single b u)| ≤
      ε := by
  have hδ : 0 < δ := c.chain.1
  have hbig := c.large_range.range_large
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  by_cases hsm : 2 * R.range + 2 < n * R.params.side
  · rw [fderiv_alongMoves (contDiffThreeAt_action_coolRegion c hF hη₀),
      fderiv_alongMoves (contDiffThreeAt_action_sitesUnderRegion c hF hm hη₀)]
    have hcmp := (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.coolRegion _
      (isRegularRegion_coolRegion c.complement_regular c.params_admissible s)
      (isColdOn_chartedFieldAt c hη₀)).2.2 s.sitesUnderRegion (s.wideChartAt w η₀) b.1.1 R.range
      (isRegularRegion_sitesUnderRegion c.params_admissible s (topFrame_extent R n) hm.regular)
      (isColdOn_wideChartAt c hm hη₀) hsm
      (fun y hy => by
        have h := mem_coolRegion_and_sitesUnderRegion c b.2 (y := y) (by omega)
        exact iff_of_true h.1 h.2)
      (fun y i hy _ => (torusChart_wideCoords c w η₀ (isNearFree_of_supDist_le b.2 hy)).symm)
      1 ![(b : TorusBond (n * R.params.side))] ![toImaginary u] le_rfl (by norm_num) (areUnitVectors_single hu)
      (fun l => by
        fin_cases l
        simp only [Fin.zero_eta, Matrix.cons_val_zero, _root_.YangMills.Construction.TorusFields.supDist_self]
        omega)
    refine hcmp.trans ?_
    have h1 := mul_exp_le_of_near (k := 0) hδ hC hε (by omega)
    simpa using h1
  · obtain ⟨e1, e2⟩ := coolRegion_eq_and_field_eq_of_small c w η₀ b.2 hsm
    have : s.regionActionMoves η₀ = s.coreActionMoves w η₀ := by
      show alongMoves s.free (actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion) (s.chartedFieldAt η₀) =
        alongMoves s.free (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) (s.wideChartAt w η₀)
      rw [e1, e2]
    rw [this, sub_self, abs_zero]
    exact hε0
theorem abs_second_fderiv_sub_le (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA C R.params.side) (hC : 0 ≤ C)
    (hm : s.MinimizerData lam σA (N 0) σ' w) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) {ε : ℝ}
    (hε : 3 * C * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-δ * R.range / 16) ≤ ε) (b b' : s.free)
    (u u' : ImaginaryCoord) (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    |fderiv ℝ (fderiv ℝ (s.regionActionMoves η₀)) 0 (Pi.single b u) (Pi.single b' u') -
      fderiv ℝ (fderiv ℝ (s.coreActionMoves w η₀)) 0 (Pi.single b u) (Pi.single b' u')| ≤
      ε * Real.exp (-(δ / 4) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by
  have hδ : 0 < δ := c.chain.1
  have hδ8 : δ ≤ 1 / 8 := c.chain.2.1
  have hbig := c.large_range.range_large
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  by_cases hsm : 2 * R.range + 2 < n * R.params.side
  · have hfacts := hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.coolRegion _
      (isRegularRegion_coolRegion c.complement_regular c.params_admissible s) (isColdOn_chartedFieldAt c hη₀)
    have hfacts2 := hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.sitesUnderRegion _
      (isRegularRegion_sitesUnderRegion c.params_admissible s (topFrame_extent R n) hm.regular)
      (isColdOn_wideChartAt c hm hη₀)
    rw [second_fderiv_alongMoves (contDiffThreeAt_action_coolRegion c hF hη₀),
      second_fderiv_alongMoves (contDiffThreeAt_action_sitesUnderRegion c hF hm hη₀)]
    by_cases hcl : 4 * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1 + 4 ≤ R.range
    · have hcmp := hfacts.2.2 s.sitesUnderRegion (s.wideChartAt w η₀) b.1.1 R.range
        (isRegularRegion_sitesUnderRegion c.params_admissible s (topFrame_extent R n) hm.regular)
        (isColdOn_wideChartAt c hm hη₀) hsm
        (fun y hy => by
          have h := mem_coolRegion_and_sitesUnderRegion c b.2 (y := y) (by omega)
          exact iff_of_true h.1 h.2)
        (fun y i hy _ => (torusChart_wideCoords c w η₀ (isNearFree_of_supDist_le b.2 hy)).symm)
        2 ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))]
        ![toImaginary u, toImaginary u'] (by norm_num) le_rfl
        (areUnitVectors_pair hu hu') (fun l => by
          fin_cases l
          · simp only [Fin.zero_eta, Matrix.cons_val_zero, _root_.YangMills.Construction.TorusFields.supDist_self]
            omega
          · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
            rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
            exact hcl)
      exact hcmp.trans (mul_exp_le_of_near hδ hC hε hcl)
    · have h1 := hfacts.2.1 2 ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))]
        ![toImaginary u, toImaginary u'] (by norm_num) (by norm_num) (areUnitVectors_pair hu hu')
      have h2 := hfacts2.2.1 2 ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))]
        ![toImaginary u, toImaginary u'] (by norm_num) (by norm_num) (areUnitVectors_pair hu hu')
      have h3 : Real.exp (-δ *
            bondListSpread ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))]) ≤
          Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by
        apply Real.exp_le_exp.mpr
        have h4 : (_root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1 : ℝ) ≤
            bondListSpread ![(b : TorusBond (n * R.params.side)), (b' : TorusBond (n * R.params.side))] := by
          exact_mod_cast _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_bondListSpread_pair _ _
        nlinarith
      have h5 := mul_exp_le_of_far hδ hδ8 hC hε (not_le.mp hcl)
      have h6 := mul_le_mul_of_nonneg_left h3 hC
      calc _ ≤ _ := abs_sub _ _
        _ ≤ C * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) + C * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) :=
          add_le_add (h1.trans h6) (h2.trans h6)
        _ = 2 * C * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by ring
        _ ≤ _ := h5
  · obtain ⟨e1, e2⟩ := coolRegion_eq_and_field_eq_of_small c w η₀ b.2 hsm
    have : s.regionActionMoves η₀ = s.coreActionMoves w η₀ := by
      show alongMoves s.free (actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion) (s.chartedFieldAt η₀) =
        alongMoves s.free (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) (s.wideChartAt w η₀)
      rw [e1, e2]
    rw [this, sub_self, abs_zero]
    positivity
end YangMills.Construction.ClusterExpansionOfAStep
end
