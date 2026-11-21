import YangMills.Construction.ClusterExpansionOfAStep.TwoActionsAlongMovesForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages FiniteDifferences LumpContours HoleSavings StepSettings RenormalizationStepParameters StepCosts QuaternionLogarithm
  FreeBondCharts FreeBondMoves CostDerivatives WideCharts WideChartFloor TorusFields TorusLumps LineCalculus
def ChartTranslateBounds (Cm : ℝ) : Prop :=
  ∀ w : imaginaryQuaternions, ‖(w : ℍ[ℝ])‖ ≤ 1 → (∀ v, ‖fderiv ℝ (chartTranslate w) 0 v‖ ≤ Cm * ‖v‖) ∧
    ∀ v v', ‖fderiv ℝ (fderiv ℝ (chartTranslate w)) 0 v v'‖ ≤ Cm * ‖v‖ * ‖v'‖
theorem abs_add_add_add_le {A B C D a b c d : ℝ} (ha : |A| ≤ a) (hb : |B| ≤ b) (hc : |C| ≤ c) (hd : |D| ≤ d) :
    |A + B + (C + D)| ≤ a + b + (c + d) :=
  (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ha hb)) ((abs_add_le _ _).trans (add_le_add hc hd)))
theorem abs_add_le_add {A B a b : ℝ} (ha : |A| ≤ a) (hb : |B| ≤ b) : |A + B| ≤ a + b :=
  (abs_add_le _ _).trans (add_le_add ha hb)
theorem add_add_sub_add_add_eq (a1 a2 a3 b1 b2 b3 : ℝ) : a1 + a3 + (b1 + b3) - (a2 + a3 + (b2 + b3)) = (a1 - a2) + (b1 - b2) := by ring
theorem half_mul_le_of_abs_sub_le {X Y l t : ℝ} (h : |X - Y| ≤ l / 2 * t) (h2 : l * t ≤ Y) : l / 2 * t ≤ X := by
  have := (abs_le.mp h).1
  linarith
theorem half_hessian_floor_of_eventuallyEq {ι : Type} [Fintype ι] [DecidableEq ι] {u₁ u₂ G₁ G₂ G₃ : (ι → ImaginaryCoord) → ℝ}
    {Λ : (ι → ImaginaryCoord) → (ι → ImaginaryCoord)} {p : ι → ImaginaryCoord} {K₁ K₂ ε E Cm lam : ℝ} {e : ι → ι → ℝ}
    (hu₁ : u₁ =ᶠ[𝓝 p] (fun a => K₁ + (G₁ a + G₃ a)) ∘ Λ) (hu₂ : u₂ =ᶠ[𝓝 p] (fun a => K₂ + (G₂ a + G₃ a)) ∘ Λ)
    (hΛ0 : Λ p = 0) (s1 : ContDiffAt ℝ 2 G₁ 0) (s2 : ContDiffAt ℝ 2 G₂ 0) (s3 : ContDiffAt ℝ 2 G₃ 0)
    (hl : ContDiffAt ℝ 2 Λ p)
    (hD : ∀ (b b' : ι) (x y : ImaginaryCoord), ‖x‖ = 1 → ‖y‖ = 1 →
      |fderiv ℝ (fderiv ℝ G₁) 0 (Pi.single b x) (Pi.single b' y) - fderiv ℝ (fderiv ℝ G₂) 0 (Pi.single b x) (Pi.single b' y)| ≤
        ε * e b b')
    (hT : ∀ (b : ι) (x : ImaginaryCoord), ‖x‖ = 1 →
      |fderiv ℝ G₁ 0 (Pi.single b x) - fderiv ℝ G₂ 0 (Pi.single b x)| ≤ ε)
    (he : ∀ b b', 0 ≤ e b b') (hsym : ∀ b b', e b b' = e b' b) (hrow : ∀ b, ∑ b', e b b' ≤ E) (hε0 : 0 ≤ ε) (hE : 0 ≤ E)
    (hP : ∀ (v : ι → ImaginaryCoord) (b : ι), ‖fderiv ℝ Λ p v b‖ ≤ Cm * ‖v b‖)
    (hQ : ∀ (v : ι → ImaginaryCoord) (b : ι), ‖fderiv ℝ (fderiv ℝ Λ) p v v b‖ ≤ Cm * ‖v b‖ * ‖v b‖)
    (hfl : ε * (E * Cm ^ 2 + Cm) ≤ lam / 2)
    (hlow : ∀ v : ι → ImaginaryCoord, lam * ∑ b, ‖v b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ u₂) p v v) (v : ι → ImaginaryCoord) :
    lam / 2 * ∑ b, ‖v b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ u₁) p v v := by
  have e1 := second_fderiv_apply_of_eventuallyEq_sum hu₁ hΛ0 s1 s3 hl v v
  have e2 := second_fderiv_apply_of_eventuallyEq_sum hu₂ hΛ0 s2 s3 hl v v
  have hS0 : 0 ≤ ∑ b, ‖v b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  refine half_mul_le_of_abs_sub_le ?_ (hlow v)
  rw [e1, e2, add_add_sub_add_add_eq]
  have hPb := hP v
  have hQb := hQ v
  generalize fderiv ℝ Λ p v = P at hPb ⊢
  generalize fderiv ℝ (fderiv ℝ Λ) p v v = Q at hQb ⊢
  have hform : |(fderiv ℝ (fderiv ℝ G₁) 0 - fderiv ℝ (fderiv ℝ G₂) 0) P P| ≤ ε * E * ∑ b, ‖P b‖ ^ 2 := by
    rw [bilinear_eq_sum_single]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hs := sum_sum_mul_le_rowBound_mul_sum_sq (fun b b' => ε * e b b') (fun b b' => mul_nonneg hε0 (he b b'))
      (fun b b' => by simp only [hsym b b']) (fun b => by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hrow b) hε0) (fun b => ‖P b‖)
    refine le_trans ?_ hs
    refine Finset.sum_le_sum fun b _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
    exact abs_bilinear_single_le _ b b' (fun x y hx hy => hD b b' x y hx hy) _ _
  have hlin : |(fderiv ℝ G₁ 0 - fderiv ℝ G₂ 0) Q| ≤ ε * ∑ b, ‖Q b‖ := by
    rw [linear_eq_sum_single, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    exact abs_linear_single_le _ b (fun x hx => hT b x hx) _
  have hP2 : ∑ b, ‖P b‖ ^ 2 ≤ Cm ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have := pow_le_pow_left₀ (norm_nonneg _) (hPb b) 2
    calc _ ≤ _ := this
      _ = _ := by ring
  have hQ2 : ∑ b, ‖Q b‖ ≤ Cm * ∑ b, ‖v b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => (hQb b).trans (le_of_eq ?_)
    ring
  have t1 : ε * E * ∑ b, ‖P b‖ ^ 2 ≤ ε * E * (Cm ^ 2 * ∑ b, ‖v b‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hP2 (mul_nonneg hε0 hE)
  have t2 : ε * ∑ b, ‖Q b‖ ≤ ε * (Cm * ∑ b, ‖v b‖ ^ 2) := mul_le_mul_of_nonneg_left hQ2 hε0
  calc |fderiv ℝ (fderiv ℝ G₁) 0 P P - fderiv ℝ (fderiv ℝ G₂) 0 P P + (fderiv ℝ G₁ 0 Q - fderiv ℝ G₂ 0 Q)|
      ≤ ε * E * (Cm ^ 2 * ∑ b, ‖v b‖ ^ 2) + ε * (Cm * ∑ b, ‖v b‖ ^ 2) :=
        abs_add_le_add (hform.trans t1) (hlin.trans t2)
    _ = (ε * (E * Cm ^ 2 + Cm)) * ∑ b, ‖v b‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfl hS0
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
variable {CA Cm Kf σ' : ℝ} {w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions}
theorem norm_coordinates_le_one (c : s.ChainContext δ lam σA cg N) (d : s.MinimizerData lam σA (N 0) σ' w)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) (b : s.free) :
    ‖((s.coordinates η₀ b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 1 := by
  have hρ1 : R.anchorRadius ≤ 1 := c.chain.2.2.2.2.1
  have h1 := wideCoords_close c d hη₀ b.1
  rw [wideCoords_eq_coordinates_of_mem_free c w η₀ b.2] at h1
  have hc := (mem_chordBonds_of_isNearFree c (isNearFree_of_mem_free b.2) (not_isBlockTreeBond_of_mem_free c _ b.2)).2
  have h2 : ‖((minimizerOnTorus R n w b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ min R.anchorRadius (N 0 * σ') :=
    d.isMinimizing.2.1 _ hc
  have h3 : ‖((s.coordinates η₀ b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ‖((s.coordinates η₀ b.1 : imaginaryQuaternions) : ℍ[ℝ]) -
      ((minimizerOnTorus R n w b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ +
        ‖((minimizerOnTorus R n w b.1 : imaginaryQuaternions) : ℍ[ℝ])‖ := by
    have := norm_add_le (((s.coordinates η₀ b.1 : imaginaryQuaternions) : ℍ[ℝ]) -
      ((minimizerOnTorus R n w b.1 : imaginaryQuaternions) : ℍ[ℝ]))
      ((minimizerOnTorus R n w b.1 : imaginaryQuaternions) : ℍ[ℝ])
    rwa [sub_add_cancel] at this
  have h4 : N 0 * σ' ≤ 2 * N 0 * R.params.threshold := by
    have hN0 := c.chain.2.2.2.2.2.2.2.1 0
    have := d.le_two_mul
    nlinarith
  have h5 := c.anchor_ge
  have h6 := min_le_right R.anchorRadius (N 0 * σ')
  linarith
theorem norm_fderiv_leftMoveCoords_le (c : s.ChainContext δ lam σA cg N) (d : s.MinimizerData lam σA (N 0) σ' w)
    (hM : ChartTranslateBounds Cm) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) (v : FreeCoords s.free) (b : s.free) :
    ‖fderiv ℝ (leftMoveCoords s.free (s.coordinates η₀) η₀) η₀ v b‖ ≤ Cm * ‖v b‖ := by
  rw [fderiv_leftMoveCoords_apply]
  exact (hM _ (norm_coordinates_le_one c d hη₀ b)).1 _
theorem norm_second_fderiv_leftMoveCoords_le (c : s.ChainContext δ lam σA cg N) (d : s.MinimizerData lam σA (N 0) σ' w)
    (hM : ChartTranslateBounds Cm) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) (v v' : FreeCoords s.free) (b : s.free) :
    ‖fderiv ℝ (fderiv ℝ (leftMoveCoords s.free (s.coordinates η₀) η₀)) η₀ v v' b‖ ≤ Cm * ‖v b‖ * ‖v' b‖ := by
  rw [second_fderiv_leftMoveCoords_apply]
  exact (hM _ (norm_coordinates_le_one c d hη₀ b)).2 _ _
omit [NeZero n] in
theorem fderiv_leftMoveCoords_single (η₀ : FreeCoords s.free) (b : s.free) (X : ImaginaryCoord) :
    fderiv ℝ (leftMoveCoords s.free (s.coordinates η₀) η₀) η₀ (Pi.single b X) =
      Pi.single b (fderiv ℝ (chartTranslate (s.coordinates η₀ b.1)) 0 X) := by
  funext b''
  rw [fderiv_leftMoveCoords_apply]
  by_cases h : b'' = b
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
omit [NeZero n] in
theorem second_fderiv_leftMoveCoords_single (η₀ : FreeCoords s.free) (b b' : s.free) (X X' : ImaginaryCoord) :
    fderiv ℝ (fderiv ℝ (leftMoveCoords s.free (s.coordinates η₀) η₀)) η₀ (Pi.single b X) (Pi.single b' X') =
      open Classical in if b = b' then Pi.single b (fderiv ℝ (fderiv ℝ (chartTranslate (s.coordinates η₀ b.1))) 0 X X') else 0 := by
  classical
  funext b''
  rw [second_fderiv_leftMoveCoords_apply]
  by_cases h : b'' = b
  · subst h
    by_cases h' : b'' = b'
    · subst h'
      simp
    · simp [h']
  · by_cases h' : b = b'
    · simp [h', Pi.single_eq_of_ne (h' ▸ h)]
    · simp [Pi.single_eq_of_ne h, h']
theorem contDiffAt_regionActionMoves (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) : ContDiffAt ℝ 3 (s.regionActionMoves η₀) 0 :=
  contDiffAt_alongMoves _ (contDiffThreeAt_action_coolRegion c hF hη₀)
theorem contDiffAt_coreActionMoves (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side)
    (d : s.MinimizerData lam σA (N 0) σ' w) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ContDiffAt ℝ 3 (s.coreActionMoves w η₀) 0 :=
  contDiffAt_alongMoves _ (contDiffThreeAt_action_sitesUnderRegion c hF d hη₀)
theorem contDiffAt_nearFitMoves (c : s.ChainContext δ lam σA cg N) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ContDiffAt ℝ 3 (s.nearFitMoves η₀) 0 := contDiffAt_alongMoves _ (contDiffThreeAt_nearFitSum c hη₀)
omit [NeZero n] in
theorem contDiffAt_of_eventuallyEq_moves {u : FreeCoords s.free → ℝ} {f g : FreeCoords s.free → ℝ} {K : ℝ}
    {η₀ : FreeCoords s.free}
    (hu : u =ᶠ[𝓝 η₀] (fun a => K + (f a + g a)) ∘ leftMoveCoords s.free (s.coordinates η₀) η₀) (hf : ContDiffAt ℝ 3 f 0)
    (hg : ContDiffAt ℝ 3 g 0) : ContDiffAt ℝ 3 u η₀ := by
  have hs : ContDiffAt ℝ 3 (fun a => K + (f a + g a)) (leftMoveCoords s.free (s.coordinates η₀) η₀ η₀) := by
    rw [leftMoveCoords_self]
    exact contDiffAt_const.add (hf.add hg)
  exact (hs.comp η₀ (contDiffAt_leftMoveCoords _ _ η₀)).congr_of_eventuallyEq hu
theorem contDiffAt_costSum (hS : SharesSumToAction) (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ContDiffAt ℝ 3 s.costSum η₀ := by
  obtain ⟨K, hK⟩ := costSum_eventuallyEq_moves hS c hη₀
  exact contDiffAt_of_eventuallyEq_moves hK (contDiffAt_regionActionMoves c hF hη₀) (contDiffAt_nearFitMoves c hη₀)
def costEntryBound (s : ChartSetting R n) (δ CA Cm Kf : ℝ) (b b' : s.free) : ℝ :=
  open Classical in
  Cm ^ 2 * (CA * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) +
      alignmentExpansionBound R.params.side R.params.coupling Kf (b : TorusBond (n * R.params.side)) b') +
    if b = b' then Cm * (CA + R.params.coupling * (4 * 13 ^ 4 * Kf)) else 0
theorem abs_second_fderiv_costSum_single_le (hS : SharesSumToAction) (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) (hCA : 0 ≤ CA)
    (hK : AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf)
    (d : s.MinimizerData lam σA (N 0) σ' w) (hM : ChartTranslateBounds Cm) (hCm : 0 ≤ Cm) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) (b b' : s.free) (X X' : ImaginaryCoord) (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |fderiv ℝ (fderiv ℝ s.costSum) η₀ (Pi.single b X) (Pi.single b' X')| ≤ costEntryBound s δ CA Cm Kf b b' := by
  classical
  obtain ⟨K, hu⟩ := costSum_eventuallyEq_moves hS c hη₀
  have h1 := (contDiffAt_regionActionMoves c hF hη₀).of_le (m := 2) (by norm_num)
  have h3 := (contDiffAt_nearFitMoves c hη₀).of_le (m := 2) (by norm_num)
  have hl : ContDiffAt ℝ 2 (leftMoveCoords s.free (s.coordinates η₀) η₀) η₀ :=
    (contDiffAt_leftMoveCoords _ _ η₀).of_le (by norm_num)
  rw [second_fderiv_apply_of_eventuallyEq_sum hu (leftMoveCoords_self _ _ η₀) h1 h3 hl, fderiv_leftMoveCoords_single,
    fderiv_leftMoveCoords_single, second_fderiv_leftMoveCoords_single]
  set x := fderiv ℝ (chartTranslate (s.coordinates η₀ b.1)) 0 X with hx
  set y := fderiv ℝ (chartTranslate (s.coordinates η₀ b'.1)) 0 X' with hy
  have hx1 : ‖x‖ ≤ Cm := by
    have := (hM _ (norm_coordinates_le_one c d hη₀ b)).1 X
    rwa [hX, mul_one] at this
  have hy1 : ‖y‖ ≤ Cm := by
    have := (hM _ (norm_coordinates_le_one c d hη₀ b')).1 X'
    rwa [hX', mul_one] at this
  have ha : 0 ≤ R.params.coupling := by linarith [c.params_admissible.a_ge]
  have hfit0 : 0 ≤ alignmentExpansionBound R.params.side R.params.coupling Kf (b : TorusBond (n * R.params.side)) b' := by
    unfold alignmentExpansionBound
    split_ifs
    · positivity
    · exact le_rfl
  have hE : 0 ≤ CA * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by positivity
  have hxy : ‖x‖ * ‖y‖ ≤ Cm ^ 2 := by
    have := mul_le_mul hx1 hy1 (norm_nonneg _) hCm
    nlinarith
  have t1 := abs_bilinear_single_le (fderiv ℝ (fderiv ℝ (s.regionActionMoves η₀)) 0) b b'
    (fun u u' hu hu' => abs_second_fderiv_regionAction_le c hF hCA hη₀ b b' u u' hu hu') x y
  have t2 := abs_bilinear_single_le (fderiv ℝ (fderiv ℝ (s.nearFitMoves η₀)) 0) b b'
    (fun u u' hu hu' => abs_second_fderiv_nearFit_le c hK hKf hη₀ b b' u u' hu hu') x y
  have t1' : |fderiv ℝ (fderiv ℝ (s.regionActionMoves η₀)) 0 (Pi.single b x) (Pi.single b' y)| ≤
      CA * Real.exp (-δ * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) * Cm ^ 2 := by
    refine t1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hxy hE
  have t2' : |fderiv ℝ (fderiv ℝ (s.nearFitMoves η₀)) 0 (Pi.single b x) (Pi.single b' y)| ≤
      alignmentExpansionBound R.params.side R.params.coupling Kf (b : TorusBond (n * R.params.side)) b' * Cm ^ 2 := by
    refine t2.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hxy hfit0
  unfold costEntryBound
  by_cases hbb : b = b'
  · subst hbb
    rw [if_pos rfl, if_pos rfl]
    set q := fderiv ℝ (fderiv ℝ (chartTranslate (s.coordinates η₀ b.1))) 0 X X' with hq
    have hq1 : ‖q‖ ≤ Cm := by
      have := (hM _ (norm_coordinates_le_one c d hη₀ b)).2 X X'
      rwa [hX, hX', mul_one, mul_one] at this
    have t3 := abs_linear_single_le (fderiv ℝ (s.regionActionMoves η₀) 0) b
      (fun u hu => abs_fderiv_regionAction_le c hF hη₀ b u hu) q
    have t4 := abs_linear_single_le (fderiv ℝ (s.nearFitMoves η₀) 0) b
      (fun u hu => abs_fderiv_nearFit_le c hK hKf hη₀ b u hu) q
    have t3' : |fderiv ℝ (s.regionActionMoves η₀) 0 (Pi.single b q)| ≤ CA * Cm :=
      t3.trans (mul_le_mul_of_nonneg_left hq1 hCA)
    have t4' : |fderiv ℝ (s.nearFitMoves η₀) 0 (Pi.single b q)| ≤ R.params.coupling * (4 * 13 ^ 4 * Kf) * Cm :=
      t4.trans (mul_le_mul_of_nonneg_left hq1 (by positivity))
    refine (abs_add_add_add_le t1' t2' t3' t4').trans (le_of_eq ?_)
    ring
  · rw [if_neg hbb, if_neg hbb]
    simp only [map_zero, add_zero]
    refine (abs_add_le_add t1' t2').trans (le_of_eq ?_)
    ring
theorem abs_fderiv_costSum_single_le (hS : SharesSumToAction) (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) (hCA : 0 ≤ CA)
    (hK : AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf)
    (d : s.MinimizerData lam σA (N 0) σ' w) (hM : ChartTranslateBounds Cm) (hCm : 0 ≤ Cm) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) (b : s.free) (X : ImaginaryCoord) (hX : ‖X‖ = 1) :
    |fderiv ℝ s.costSum η₀ (Pi.single b X)| ≤ Cm * (CA + R.params.coupling * (4 * 13 ^ 4 * Kf)) := by
  obtain ⟨K, hu⟩ := costSum_eventuallyEq_moves hS c hη₀
  have h1 := (contDiffAt_regionActionMoves c hF hη₀).differentiableAt (by norm_num)
  have h3 := (contDiffAt_nearFitMoves c hη₀).differentiableAt (by norm_num)
  have hl := (contDiffAt_leftMoveCoords s.free (s.coordinates η₀) η₀).differentiableAt (by norm_num)
  rw [fderiv_apply_of_eventuallyEq_sum hu (leftMoveCoords_self _ _ η₀) h1 h3 hl, fderiv_leftMoveCoords_single]
  set x := fderiv ℝ (chartTranslate (s.coordinates η₀ b.1)) 0 X with hx
  have hx1 : ‖x‖ ≤ Cm := by
    have := (hM _ (norm_coordinates_le_one c d hη₀ b)).1 X
    rwa [hX, mul_one] at this
  have t3 := abs_linear_single_le (fderiv ℝ (s.regionActionMoves η₀) 0) b
    (fun u hu => abs_fderiv_regionAction_le c hF hη₀ b u hu) x
  have t4 := abs_linear_single_le (fderiv ℝ (s.nearFitMoves η₀) 0) b
    (fun u hu => abs_fderiv_nearFit_le c hK hKf hη₀ b u hu) x
  have ha : 0 ≤ R.params.coupling := by linarith [c.params_admissible.a_ge]
  have t3' := t3.trans (mul_le_mul_of_nonneg_left hx1 hCA)
  have t4' := t4.trans (mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ R.params.coupling * (4 * 13 ^ 4 * Kf)))
  refine (abs_add_le_add t3' t4').trans (le_of_eq ?_)
  ring
theorem sum_exp_neg_mul_supDist_subtype_le {m : ℕ} [NeZero m] {β : ℝ} (hβ : 0 < β) (z : TorusSite m)
    (I : Finset (TorusBond m)) :
    ∑ b : I, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1.1) ≤ 4 * (2 / (1 - Real.exp (-β / 4))) ^ 4 := by
  classical
  have h1 : ∑ b : I, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1.1) = ∑ b ∈ I, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1) :=
    Finset.sum_coe_sort I fun b => Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1)
  have h2 : ∑ b ∈ I, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1) ≤ ∑ b : TorusBond m, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
  have h3 : ∑ b : TorusBond m, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z b.1) = 4 * ∑ y : TorusSite m, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist y z) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    show ∑ _i : Fin 4, Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist z y) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, _root_.YangMills.Construction.TorusFields.supDist_comm]
    norm_num
  rw [h1]
  refine h2.trans ?_
  rw [h3]
  have := sum_exp_neg_mul_supDist_le hβ z
  linarith
theorem hessian_costSum_ge (hS : SharesSumToAction) (hC : WholeCellCostEqualsMinimalAction)
    (hA : ActionAtLevelIsCutAction) (c : s.ChainContext δ lam σA cg N)
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) (hCA : 0 ≤ CA)
    (d : s.MinimizerData lam σA (N 0) σ' w) (hM : ChartTranslateBounds Cm)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) {ε : ℝ}
    (hε : 3 * CA * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-δ * R.range / 16) ≤ ε)
    (hfl : ε * (4 * (2 / (1 - Real.exp (-(δ / 4) / 4))) ^ 4 * Cm ^ 2 + Cm) ≤ lam / 2) (v : FreeCoords s.free) :
    lam / 2 * ∑ b, ‖v b‖ ^ 2 ≤ deriv (deriv fun τ : ℝ => s.costSum (η₀ + τ • v)) 0 := by
  have hδ : 0 < δ := c.chain.1
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  obtain ⟨K₁, hu₁⟩ := costSum_eventuallyEq_moves hS c hη₀
  obtain ⟨K₂, hu₂⟩ := wideChartEnergy_eventuallyEq_moves hC hA c w η₀
  have s1 := contDiffAt_regionActionMoves c hF hη₀
  have s2 := contDiffAt_coreActionMoves c hF d hη₀
  have s3 := contDiffAt_nearFitMoves c hη₀
  have c1 : ContDiffAt ℝ 2 s.costSum η₀ := (contDiffAt_of_eventuallyEq_moves hu₁ s1 s3).of_le (by norm_num)
  have c2 : ContDiffAt ℝ 2 (s.wideChartEnergy w η₀) η₀ := (contDiffAt_of_eventuallyEq_moves hu₂ s2 s3).of_le (by norm_num)
  have hl : ContDiffAt ℝ 2 (leftMoveCoords s.free (s.coordinates η₀) η₀) η₀ :=
    (contDiffAt_leftMoveCoords _ _ η₀).of_le (by norm_num)
  have d2 : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  have hK40 : 0 ≤ 4 * (2 / (1 - Real.exp (-(δ / 4) / 4))) ^ 4 := by
    have h : Real.exp (-(δ / 4) / 4) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have : 0 < 1 - Real.exp (-(δ / 4) / 4) := by linarith
    positivity
  rw [second_deriv_along_line c1]
  exact half_hessian_floor_of_eventuallyEq (ι := s.free) (e := fun b b' => Real.exp (-(δ / 4) * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1))
    hu₁ hu₂ (leftMoveCoords_self _ _ η₀) (s1.of_le d2) (s2.of_le d2) (s3.of_le d2) hl
    (fun b b' x y hx hy => abs_second_fderiv_sub_le c hF hCA d hη₀ hε b b' x y hx hy)
    (fun b x hx => abs_fderiv_sub_le c hF hCA d hη₀ hε b x hx)
    (fun b b' => (Real.exp_pos _).le) (fun b b' => by simp only [_root_.YangMills.Construction.TorusFields.supDist_comm])
    (fun b => sum_exp_neg_mul_supDist_subtype_le (by positivity) b.1.1 s.free) hε0 hK40
    (fun v b => norm_fderiv_leftMoveCoords_le c d hM hη₀ v b)
    (fun v b => norm_second_fderiv_leftMoveCoords_le c d hM hη₀ v v b) hfl
    (fun v => by
      have h := hessian_wideChartEnergy_ge c d hη₀ v
      rwa [second_deriv_along_line c2] at h) v
end YangMills.Construction.ClusterExpansionOfAStep
end
