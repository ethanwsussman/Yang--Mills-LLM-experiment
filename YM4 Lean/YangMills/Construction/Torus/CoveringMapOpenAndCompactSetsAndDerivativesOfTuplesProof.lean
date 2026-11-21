import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.DistancesAndLiftsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.TupleTopology
section Partials
variable {D : ℕ}
theorem iterate_partialDeriv_induction (P : ((Fin D → ℝ) → ℂ) → Prop)
    (hP : ∀ j G, P G → P (partialDeriv j G)) (j : Fin D) (n : ℕ) {G : (Fin D → ℝ) → ℂ}
    (hG : P G) : P ((partialDeriv j)^[n] G) := by
  induction n with
  | zero => exact hG
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hP j _ ih
theorem iteratedPartial_induction (P : ((Fin D → ℝ) → ℂ) → Prop)
    (hP : ∀ j G, P G → P (partialDeriv j G)) (α : PowerSeries.MultiIndex D) {G : (Fin D → ℝ) → ℂ}
    (hG : P G) : P (iteratedPartial α G) := by
  have h : ∀ l : List (Fin D), P (l.foldr (fun j H => (partialDeriv j)^[α j] H) G) := by
    intro l
    induction l with
    | nil => exact hG
    | cons j l ih => exact iterate_partialDeriv_induction P hP j _ ih
  exact h _
theorem partialDeriv_periodic (j : Fin D) {G : (Fin D → ℝ) → ℂ} {w : Fin D → ℝ}
    (h : ∀ x, G (x + w) = G x) (x : Fin D → ℝ) :
    partialDeriv j G (x + w) = partialDeriv j G x := by
  simp only [partialDeriv, lineDeriv]
  congr 1
  funext t
  rw [add_right_comm, h]
theorem partialDeriv_eq_zero_of_eqOn_open (j : Fin D) {W : Set (Fin D → ℝ)} (hW : IsOpen W)
    {G : (Fin D → ℝ) → ℂ} (h : ∀ x ∈ W, G x = 0) : ∀ x ∈ W, partialDeriv j G x = 0 := by
  intro x hx
  have hc : Continuous fun t : ℝ => x + t • (Pi.single j 1 : Fin D → ℝ) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • (Pi.single j 1 : Fin D → ℝ) ∈ W :=
    hc.continuousAt.eventually_mem (by simpa using hW.mem_nhds hx)
  have hz : (fun t : ℝ => G (x + t • (Pi.single j 1 : Fin D → ℝ))) =ᶠ[𝓝 0] fun _ => 0 :=
    hev.mono fun t ht => h _ ht
  simp only [partialDeriv, lineDeriv]
  rw [hz.deriv_eq]
  simp
theorem iterate_partialDeriv_continuousPartials {U : Set (Fin D → ℝ)} (j : Fin D) (k : ℕ) :
    ∀ (n : ℕ) {G : (Fin D → ℝ) → ℂ}, ContinuousPartialsUpTo U (n + k) G →
      ContinuousPartialsUpTo U n ((partialDeriv j)^[k] G) := by
  induction k with
  | zero => exact fun n G h => h
  | succ k ih =>
    intro n G h
    have h' : ContinuousPartialsUpTo U ((n + k) + 1) G := h
    rw [Function.iterate_succ_apply]
    exact ih n (h'.2 j).2
theorem foldr_partialDeriv_continuousPartials {U : Set (Fin D → ℝ)} (α : PowerSeries.MultiIndex D)
    (l : List (Fin D)) : ∀ (n : ℕ) {G : (Fin D → ℝ) → ℂ},
      ContinuousPartialsUpTo U (n + (l.map α).sum) G →
      ContinuousPartialsUpTo U n (l.foldr (fun j H => (partialDeriv j)^[α j] H) G) := by
  induction l with
  | nil => exact fun n G h => h
  | cons j l ih =>
    intro n G h
    refine iterate_partialDeriv_continuousPartials j (α j) n (ih (n + α j) ?_)
    have he : n + α j + (l.map α).sum = n + ((j :: l).map α).sum := by
      simp [add_assoc]
    rw [he]
    exact h
theorem iteratedPartial_continuousPartials {U : Set (Fin D → ℝ)} (α : PowerSeries.MultiIndex D)
    (n : ℕ) {G : (Fin D → ℝ) → ℂ} (h : ContinuousPartialsUpTo U (n + α.order) G) :
    ContinuousPartialsUpTo U n (iteratedPartial α G) := by
  refine foldr_partialDeriv_continuousPartials α _ n ?_
  have he : ((List.finRange D).map α).sum = α.order := by
    rw [PowerSeries.MultiIndex.order, Fin.sum_univ_def]
  rw [he]
  exact h
def gradientCLM (G : (Fin D → ℝ) → ℂ) (x : Fin D → ℝ) : (Fin D → ℝ) →L[ℝ] ℂ :=
  ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D => ℝ) j).smulRight
    (partialDeriv j G x)
theorem gradientCLM_apply (G : (Fin D → ℝ) → ℂ) (x h : Fin D → ℝ) :
    gradientCLM G x h = ∑ j, h j • partialDeriv j G x := by
  simp [gradientCLM]
def partialStep (x h : Fin D → ℝ) (k : ℕ) : Fin D → ℝ :=
  fun i => if (i : ℕ) < k then x i + h i else x i
theorem partialStep_zero (x h : Fin D → ℝ) : partialStep x h 0 = x := by
  funext i
  simp [partialStep]
theorem partialStep_last (x h : Fin D → ℝ) : partialStep x h D = x + h := by
  funext i
  simp [partialStep]
theorem partialStep_succ (x h : Fin D → ℝ) (k : Fin D) :
    partialStep x h (k + 1) = partialStep x h k + h k • (Pi.single k 1 : Fin D → ℝ) := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp [partialStep]
  · have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
    have hiff : (i : ℕ) < k + 1 ↔ (i : ℕ) < k := by omega
    simp [partialStep, hiff, hik]
theorem norm_coordIncrement_sub_le {G : (Fin D → ℝ) → ℂ} {j : Fin D} {z : Fin D → ℝ} {c : ℂ}
    {ε a : ℝ} (hd : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hb : ∀ t : ℝ, |t| ≤ |a| →
      ‖partialDeriv j G (z + t • (Pi.single j 1 : Fin D → ℝ)) - c‖ ≤ ε) :
    ‖G (z + a • (Pi.single j 1 : Fin D → ℝ)) - G z - a • c‖ ≤ ε * |a| := by
  set e : Fin D → ℝ := Pi.single j 1 with he
  have hder : ∀ t : ℝ, HasDerivAt (fun u : ℝ => G (z + u • e) - u • c)
      (partialDeriv j G (z + t • e) - c) t := by
    intro t
    have h0 : HasDerivAt (fun u : ℝ => G ((z + t • e) + u • e))
        (partialDeriv j G (z + t • e)) 0 := (hd (z + t • e)).hasLineDerivAt
    have h1 : HasDerivAt (fun u : ℝ => G ((z + t • e) + (u - t) • e))
        (partialDeriv j G (z + t • e)) t :=
      HasDerivAt.comp_sub_const t t (by simpa using h0)
    have hfun : (fun u : ℝ => G ((z + t • e) + (u - t) • e)) = fun u : ℝ => G (z + u • e) := by
      funext u
      congr 1
      rw [sub_smul]
      abel
    rw [hfun] at h1
    have h2 : HasDerivAt (fun u : ℝ => u • c) c t := by
      simpa using (hasDerivAt_id t).smul_const c
    exact h1.sub h2
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun u : ℝ => G (z + u • e) - u • c)
    (f' := fun t => partialDeriv j G (z + t • e) - c) (C := ε)
    (s := Icc (-|a|) |a|) (x := 0) (y := a)
    (fun t _ => (hder t).hasDerivWithinAt)
    (fun t ht => hb t (abs_le.2 ht)) (convex_Icc _ _)
    (by simp) ⟨neg_abs_le a, le_abs_self a⟩
  have hE : (G (z + a • e) - a • c) - (G (z + (0 : ℝ) • e) - (0 : ℝ) • c) =
      G (z + a • e) - G z - a • c := by
    simp only [zero_smul, add_zero, sub_zero]
    abel
  rw [hE] at hmain
  simpa [Real.norm_eq_abs] using hmain
theorem hasFDerivAt_gradientCLM {G : (Fin D → ℝ) → ℂ}
    (hd : ∀ j x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hc : ∀ j, Continuous (partialDeriv j G)) (x : Fin D → ℝ) :
    HasFDerivAt G (gradientCLM G x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  set ε' : ℝ := ε / ((D : ℝ) + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε hD
  have ev : ∀ᶠ z in 𝓝 x, ∀ j, ‖partialDeriv j G z - partialDeriv j G x‖ ≤ ε' := by
    refine eventually_all.2 fun j => ?_
    have ht := (hc j).tendsto x
    have := (Metric.tendsto_nhds.1 ht) ε' hε'pos
    exact this.mono fun z hz => by
      rw [dist_eq_norm] at hz
      exact hz.le
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ev
  filter_upwards [Metric.ball_mem_nhds (0 : Fin D → ℝ) hδ] with h hh
  have hnorm : ‖h‖ < δ := by simpa using hh
  have hterm : ∀ k : Fin D,
      ‖G (partialStep x h (k + 1)) - G (partialStep x h k) - h k • partialDeriv k G x‖ ≤
        ε' * |h k| := by
    intro k
    rw [partialStep_succ]
    refine norm_coordIncrement_sub_le (hd k) fun t ht => hball ?_ k
    rw [dist_pi_lt_iff hδ]
    intro i
    have hik : |h i| ≤ ‖h‖ := by simpa using norm_le_pi_norm h i
    have hkk : |h k| ≤ ‖h‖ := by simpa using norm_le_pi_norm h k
    have hn : 0 ≤ ‖h‖ := norm_nonneg h
    rw [Real.dist_eq]
    by_cases hi : i = k
    · subst hi
      simp only [partialStep, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one, lt_irrefl, if_false]
      rw [add_sub_cancel_left]
      linarith
    · simp only [partialStep, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul,
        mul_zero, add_zero]
      split_ifs
      · rw [add_sub_cancel_left]
        linarith
      · simp only [sub_self, abs_zero]
        exact hδ
  have hsum : G (x + h) - G x - gradientCLM G x h =
      ∑ k : Fin D, (G (partialStep x h (k + 1)) - G (partialStep x h k) -
        h k • partialDeriv k G x) := by
    rw [Finset.sum_sub_distrib, gradientCLM_apply]
    congr 1
    have htel := Finset.sum_range_sub (fun n => G (partialStep x h n)) D
    rw [Fin.sum_univ_eq_sum_range (fun n => G (partialStep x h (n + 1)) - G (partialStep x h n)) D,
      htel, partialStep_last, partialStep_zero]
  rw [hsum]
  calc ‖∑ k : Fin D, (G (partialStep x h (k + 1)) - G (partialStep x h k) -
        h k • partialDeriv k G x)‖
      ≤ ∑ k : Fin D, ε' * |h k| := norm_sum_le_of_le _ fun k _ => hterm k
    _ ≤ ∑ _k : Fin D, ε' * ‖h‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hkk : |h k| ≤ ‖h‖ := by simpa using norm_le_pi_norm h k
        exact mul_le_mul_of_nonneg_left hkk hε'pos.le
    _ = (D : ℝ) * (ε' * ‖h‖) := by simp
    _ ≤ ε * ‖h‖ := by
        have hle : (D : ℝ) * ε' ≤ ε := by
          rw [hε', ← mul_div_assoc, div_le_iff₀ hD]
          nlinarith
        have := mul_le_mul_of_nonneg_right hle (norm_nonneg h)
        linarith
theorem contDiff_of_continuousPartials (n : ℕ) :
    ∀ {G : (Fin D → ℝ) → ℂ}, ContinuousPartialsUpTo univ n G → ContDiff ℝ n G := by
  induction n with
  | zero =>
    intro G h
    have hc : Continuous G := continuousOn_univ.1 h
    have h0 : ContDiff ℝ 0 G := contDiff_zero.2 hc
    simpa using h0
  | succ n ih =>
    intro G h
    have hcd : ∀ j, ContDiff ℝ n (partialDeriv j G) := fun j => ih (h.2 j).2
    have hf : ∀ x, HasFDerivAt G (gradientCLM G x) x :=
      hasFDerivAt_gradientCLM (fun j x => (h.2 j).1 x (mem_univ x)) fun j => (hcd j).continuous
    have hfd : fderiv ℝ G = gradientCLM G := funext fun x => (hf x).fderiv
    have hg : ContDiff ℝ n (gradientCLM G) := by
      unfold gradientCLM
      exact ContDiff.sum fun j _ => contDiff_const.smulRight (hcd j)
    push_cast
    rw [contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact hg
def AllContinuousPartials (G : (Fin D → ℝ) → ℂ) : Prop :=
  ∀ n : ℕ, ContinuousPartialsUpTo univ n G
theorem AllContinuousPartials.partialDeriv {G : (Fin D → ℝ) → ℂ} (h : AllContinuousPartials G)
    (j : Fin D) : AllContinuousPartials (AmbientPoints.partialDeriv j G) :=
  fun n => ((h (n + 1)).2 j).2
theorem partialDeriv_eq_fderiv_apply (j : Fin D) {G : (Fin D → ℝ) → ℂ}
    (h : Differentiable ℝ G) :
    partialDeriv j G = fun x => fderiv ℝ G x (Pi.single j 1) :=
  funext fun x => (h x).lineDeriv_eq_fderiv
theorem partialDeriv_comm {G : (Fin D → ℝ) → ℂ} (h : AllContinuousPartials G) (i j : Fin D) :
    partialDeriv i (partialDeriv j G) = partialDeriv j (partialDeriv i G) := by
  have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) G := contDiff_of_continuousPartials 2 (h 2)
  have hdiff : Differentiable ℝ G := h2.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ G) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hmix : ∀ a b : Fin D, ∀ x, partialDeriv a (partialDeriv b G) x =
      fderiv ℝ (fderiv ℝ G) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b x
    have hb : DifferentiableAt ℝ (fun y => fderiv ℝ G y (Pi.single b 1)) x :=
      (hfd x).clm_apply (differentiableAt_const _)
    rw [partialDeriv_eq_fderiv_apply b hdiff]
    change lineDeriv ℝ (fun y => fderiv ℝ G y (Pi.single b 1)) x (Pi.single a 1) = _
    rw [hb.lineDeriv_eq_fderiv, fderiv_clm_apply (hfd x) (differentiableAt_const _)]
    simp
  funext x
  rw [hmix, hmix]
  have hs : IsSymmSndFDerivAt ℝ G x :=
    (h2.contDiffAt).isSymmSndFDerivAt (by simp)
  exact hs _ _
theorem allContinuousPartials_iterate {G : (Fin D → ℝ) → ℂ} (h : AllContinuousPartials G)
    (j : Fin D) (n : ℕ) : AllContinuousPartials ((partialDeriv j)^[n] G) :=
  iterate_partialDeriv_induction AllContinuousPartials (fun j _ h => h.partialDeriv j) j n h
theorem allContinuousPartials_foldr {G : (Fin D → ℝ) → ℂ} (h : AllContinuousPartials G)
    (α : PowerSeries.MultiIndex D) (l : List (Fin D)) :
    AllContinuousPartials (l.foldr (fun j H => (partialDeriv j)^[α j] H) G) := by
  induction l with
  | nil => exact h
  | cons j l ih => exact allContinuousPartials_iterate ih j _
theorem partialDeriv_iterate_comm (i j : Fin D) (b : ℕ) :
    ∀ {G : (Fin D → ℝ) → ℂ}, AllContinuousPartials G →
      partialDeriv i ((partialDeriv j)^[b] G) =
        (partialDeriv j)^[b] (partialDeriv i G) := by
  induction b with
  | zero => exact fun _ => rfl
  | succ b ih =>
    intro G h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (h.partialDeriv j),
      partialDeriv_comm h i j]
theorem iterate_partialDeriv_comm (i j : Fin D) (a b : ℕ) :
    ∀ {G : (Fin D → ℝ) → ℂ}, AllContinuousPartials G →
      (partialDeriv i)^[a] ((partialDeriv j)^[b] G) =
        (partialDeriv j)^[b] ((partialDeriv i)^[a] G) := by
  induction a with
  | zero => exact fun _ => rfl
  | succ a ih =>
    intro G h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, partialDeriv_iterate_comm i j b h,
      ih (h.partialDeriv i)]
theorem foldr_partialDeriv_iterate_comm (β : PowerSeries.MultiIndex D) (j : Fin D) (a : ℕ)
    (l : List (Fin D)) :
    ∀ {H : (Fin D → ℝ) → ℂ}, AllContinuousPartials H →
      l.foldr (fun i X => (partialDeriv i)^[β i] X) ((partialDeriv j)^[a] H) =
        (partialDeriv j)^[a] (l.foldr (fun i X => (partialDeriv i)^[β i] X) H) := by
  induction l with
  | nil => exact fun _ => rfl
  | cons i l ih =>
    intro H h
    simp only [List.foldr_cons]
    rw [ih h, iterate_partialDeriv_comm i j _ _ (allContinuousPartials_foldr h β l)]
theorem iteratedPartial_iteratedPartial (α β : PowerSeries.MultiIndex D) {G : (Fin D → ℝ) → ℂ}
    (h : AllContinuousPartials G) :
    iteratedPartial β (iteratedPartial α G) = iteratedPartial (α + β) G := by
  have key : ∀ l : List (Fin D),
      l.foldr (fun i X => (partialDeriv i)^[β i] X)
          (l.foldr (fun i X => (partialDeriv i)^[α i] X) G) =
        l.foldr (fun i X => (partialDeriv i)^[(α + β) i] X) G := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldr_cons]
      rw [foldr_partialDeriv_iterate_comm β j _ l (allContinuousPartials_foldr h α l), ih,
        ← Function.iterate_add_apply, Pi.add_apply, add_comm]
  exact key _
end Partials
section Coordinates
variable {p : ℕ}
def blockCoordEquiv (p : ℕ) : Fin p × Fin 4 ≃ Fin (4 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 4))
theorem flattenCoords_symm_apply (x : Fin (4 * p) → ℝ) (i : Fin p) (μ : Fin 4) :
    (flattenCoords p).symm x i μ = x (blockCoordEquiv p (i, μ)) := rfl
theorem flattenCoords_symm_sub (x x' : Fin (4 * p) → ℝ) (i : Fin p) :
    (flattenCoords p).symm (x - x') i =
      (flattenCoords p).symm x i - (flattenCoords p).symm x' i := rfl
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_supNorm (u : Fin p → Fin 4 → ℝ) (i : Fin p) :
    TorusMetric.euclidNormVec (u i) ≤ supNorm u :=
  le_ciSup (f := fun i => TorusMetric.euclidNormVec (u i)) (Set.finite_range _).bddAbove i
theorem supNorm_nonneg (u : Fin p → Fin 4 → ℝ) : 0 ≤ supNorm u :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
theorem liftSupDist_nonneg (x x' : Fin (4 * p) → ℝ) : 0 ≤ liftSupDist x x' :=
  supNorm_nonneg _
theorem dist_le_liftSupDist (x x' : Fin (4 * p) → ℝ) : dist x x' ≤ liftSupDist x x' := by
  refine (dist_pi_le_iff (liftSupDist_nonneg x x')).2 fun j => ?_
  obtain ⟨⟨i, μ⟩, rfl⟩ := (blockCoordEquiv p).surjective j
  rw [Real.dist_eq]
  exact (abs_apply_le_euclidNormVec ((flattenCoords p).symm (x - x') i) μ).trans
    (euclidNormVec_le_supNorm _ i)
theorem liftSupDist_le_liftEuclidDist (x x' : Fin (4 * p) → ℝ) :
    liftSupDist x x' ≤ liftEuclidDist x x' := by
  refine Real.iSup_le (fun i => ?_) (Real.sqrt_nonneg _)
  refine Real.sqrt_le_sqrt ?_
  have hsum : ∑ j, (x j - x' j) ^ 2 =
      ∑ q : Fin p × Fin 4, (x (blockCoordEquiv p q) - x' (blockCoordEquiv p q)) ^ 2 :=
    ((blockCoordEquiv p).sum_comp fun j => (x j - x' j) ^ 2).symm
  rw [hsum, Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun i : Fin p => ∑ μ : Fin 4,
      (x (blockCoordEquiv p (i, μ)) - x' (blockCoordEquiv p (i, μ))) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
theorem liftEuclidDist_le_dist (x x' : Fin (4 * p) → ℝ) :
    liftEuclidDist x x' ≤ (4 * p + 1 : ℝ) * dist x x' := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hterm : ∀ j, (x j - x' j) ^ 2 ≤ dist x x' ^ 2 := by
    intro j
    rw [← sq_abs]
    have h := dist_le_pi_dist x x' j
    rw [Real.dist_eq] at h
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc ∑ j, (x j - x' j) ^ 2 ≤ ∑ _j : Fin (4 * p), dist x x' ^ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (4 * p : ℝ) * dist x x' ^ 2 := by simp
    _ ≤ ((4 * p + 1 : ℝ) * dist x x') ^ 2 := by
        have : (4 * p : ℝ) ≤ (4 * p + 1) ^ 2 := by nlinarith
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
theorem dist_le_liftEuclidDist (x x' : Fin (4 * p) → ℝ) : dist x x' ≤ liftEuclidDist x x' :=
  (dist_le_liftSupDist x x').trans (liftSupDist_le_liftEuclidDist x x')
theorem liftSupDist_le_dist (x x' : Fin (4 * p) → ℝ) :
    liftSupDist x x' ≤ (4 * p + 1 : ℝ) * dist x x' :=
  (liftSupDist_le_liftEuclidDist x x').trans (liftEuclidDist_le_dist x x')
theorem liftEuclidDist_le_liftSupDist (x x' : Fin (4 * p) → ℝ) :
    liftEuclidDist x x' ≤ (4 * p + 1 : ℝ) * liftSupDist x x' :=
  (liftEuclidDist_le_dist x x').trans
    (mul_le_mul_of_nonneg_left (dist_le_liftSupDist x x') (by positivity))
theorem isOpenWrt_of_le {X : Type} {d d' : X → X → ℝ} {C : ℝ} (hC : 0 < C)
    (h : ∀ x x', d x x' ≤ C * d' x x') {U : Set X} (hU : IsOpenWrt d U) :
    IsOpenWrt d' U := by
  intro x hx
  obtain ⟨r, hr, hb⟩ := hU x hx
  refine ⟨r / C, div_pos hr hC, fun x' hx' => hb x' ?_⟩
  calc d x x' ≤ C * d' x x' := h x x'
    _ < C * (r / C) := mul_lt_mul_of_pos_left hx' hC
    _ = r := by field_simp
theorem isBoundedWrt_of_le {X : Type} {d d' : X → X → ℝ} {C : ℝ} (hC : 0 < C)
    (h : ∀ x x', d x x' ≤ C * d' x x') {U : Set X} (hU : IsBoundedWrt d' U) :
    IsBoundedWrt d U := by
  obtain ⟨B, hB⟩ := hU
  exact ⟨C * B, fun x hx x' hx' =>
    (h x x').trans (mul_le_mul_of_nonneg_left (hB x hx x' hx') hC.le)⟩
theorem isOpen_iff_isOpenWrt_dist (U : Set (Fin (4 * p) → ℝ)) :
    IsOpen U ↔ IsOpenWrt (fun x x' => dist x x') U := by
  rw [Metric.isOpen_iff]
  refine forall₂_congr fun x _ => ?_
  refine exists_congr fun r => and_congr_right fun _ => ?_
  constructor
  · exact fun h x' hx' => h (by simpa [Metric.mem_ball, dist_comm] using hx')
  · exact fun h x' hx' => h x' (by simpa [Metric.mem_ball, dist_comm] using hx')
theorem isBounded_iff_isBoundedWrt_dist (U : Set (Fin (4 * p) → ℝ)) :
    Bornology.IsBounded U ↔ IsBoundedWrt (fun x x' => dist x x') U := by
  rw [Metric.isBounded_iff]
  exact ⟨fun ⟨C, h⟩ => ⟨C, fun x hx x' hx' => h hx hx'⟩,
    fun ⟨C, h⟩ => ⟨C, fun x hx x' hx' => h x hx x' hx'⟩⟩
end Coordinates
section Tuples
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem tupleProj_eq_iff (E : Ambient) (p : ℕ) (x x' : Fin (4 * p) → ℝ) :
    tupleProj s E p x = tupleProj s E p x' ↔ IsTuplePeriod s E p (x - x') := by
  cases E with
  | torus =>
    constructor
    · intro h
      have hi : ∀ i, ∃ k, (flattenCoords p).symm x i = (flattenCoords p).symm x' i +
          TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m) k :=
        fun i => TestFunctions.exists_latticeTranslate_of_torusProj_eq (congrFun h i)
      choose k hk using hi
      refine ⟨fun j => k ((blockCoordEquiv p).symm j).1 ((blockCoordEquiv p).symm j).2,
        fun j => ?_⟩
      obtain ⟨⟨i, μ⟩, rfl⟩ := (blockCoordEquiv p).surjective j
      have h1 := congrFun (hk i) μ
      simp only [flattenCoords_symm_apply, Pi.add_apply, TestFunctions.latticeTranslate] at h1
      simp only [Equiv.symm_apply_apply, Pi.sub_apply, Conventions.StandingParameters.side]
      rw [h1]
      ring
    · rintro ⟨k, hk⟩
      funext i
      have hv : (flattenCoords p).symm x i = (flattenCoords p).symm x' i +
          TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m)
            (fun μ => k (blockCoordEquiv p (i, μ))) := by
        funext μ
        have h1 := hk (blockCoordEquiv p (i, μ))
        simp only [Pi.sub_apply, Conventions.StandingParameters.side] at h1
        simp only [flattenCoords_symm_apply, Pi.add_apply, TestFunctions.latticeTranslate]
        linarith
      change TorusMetric.torusProj _ _ = TorusMetric.torusProj _ _
      rw [hv]
      exact TestFunctions.torusProj_add_latticeTranslate _ _ _
  | euclidean =>
    change (fun i => (flattenCoords p).symm x i) = (fun i => (flattenCoords p).symm x' i) ↔
      x - x' = 0
    rw [sub_eq_zero]
    exact (flattenCoords p).symm.injective.eq_iff
theorem tupleCoveringProps_of_metricFacts (hF : DistanceFacts.MetricFacts s E) (p : ℕ)
    (hp : 1 ≤ p) : TupleCoveringProps s E p := by
  have hne : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  refine ⟨tupleProj_surjective s E p, tupleProj_eq_iff E p, fun x x' => ?_, fun x y => ?_⟩
  · refine ciSup_le fun i => ?_
    refine (hF.pointDist_proj_le _ _).trans ?_
    rw [← flattenCoords_symm_sub]
    exact euclidNormVec_le_supNorm _ i
  · choose b hb hb' using fun i => hF.exists_lift_pointDist ((flattenCoords p).symm x i) (y i)
    refine ⟨flattenCoords p b, ?_, ?_⟩
    · funext i
      rw [tupleProj_flattenCoords]
      exact hb i
    · have hi : ∀ i, TorusMetric.euclidNormVec
          ((flattenCoords p).symm (x - flattenCoords p b) i) =
          pointDist s E (tupleProj s E p x i) (y i) := by
        intro i
        rw [flattenCoords_symm_sub, Equiv.symm_apply_apply]
        exact hb' i
      exact iSup_congr hi
variable {p : ℕ}
theorem continuous_tupleProj (hc : TupleCoveringProps s E p) :
    Continuous (tupleProj s E p) := by
  have hC : (0 : ℝ) < 4 * p + 1 := by positivity
  refine Metric.continuous_iff.2 fun b ε hε => ⟨ε / (4 * p + 1), div_pos hε hC, fun a ha => ?_⟩
  rw [dist_eq_supDist]
  calc supDist (tupleProj s E p a) (tupleProj s E p b)
      ≤ liftSupDist a b := hc.2.2.1 a b
    _ ≤ (4 * p + 1 : ℝ) * dist a b := liftSupDist_le_dist a b
    _ < (4 * p + 1 : ℝ) * (ε / (4 * p + 1)) := mul_lt_mul_of_pos_left ha hC
    _ = ε := by field_simp
theorem isOpenMap_tupleProj (hc : TupleCoveringProps s E p) :
    IsOpenMap (tupleProj s E p) := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨r, hr, fun y hy => ?_⟩
  obtain ⟨x', hx', hd⟩ := hc.2.2.2 x y
  refine ⟨x', hb ?_, hx'⟩
  rw [Metric.mem_ball, dist_comm]
  refine (dist_le_liftSupDist x x').trans_lt ?_
  rw [hd, ← dist_eq_supDist, dist_comm]
  exact hy
theorem isQuotientMap_tupleProj (hc : TupleCoveringProps s E p) :
    Topology.IsQuotientMap (tupleProj s E p) :=
  (isOpenMap_tupleProj hc).isQuotientMap (continuous_tupleProj hc) hc.1
theorem tupleOpenSetProps_of_covering (hc : TupleCoveringProps s E p) :
    TupleOpenSetProps s E p := by
  have hC : (0 : ℝ) < 4 * p + 1 := by positivity
  have h1 : ∀ x x' : Fin (4 * p) → ℝ,
      liftSupDist x x' ≤ 1 * liftEuclidDist x x' := fun x x' => by
    simpa using liftSupDist_le_liftEuclidDist x x'
  have h3 : ∀ x x' : Fin (4 * p) → ℝ, dist x x' ≤ 1 * liftEuclidDist x x' :=
    fun x x' => by simpa using dist_le_liftEuclidDist x x'
  refine ⟨fun U => ⟨isOpenWrt_of_le one_pos h1,
      isOpenWrt_of_le hC liftEuclidDist_le_liftSupDist⟩,
    fun U => ⟨isBoundedWrt_of_le hC liftEuclidDist_le_liftSupDist,
      isBoundedWrt_of_le one_pos h1⟩,
    fun U => ?_, fun U => ?_, fun A => ?_, fun X _ h => ?_⟩
  · rw [isOpen_iff_isOpenWrt_dist]
    exact ⟨isOpenWrt_of_le one_pos h3, isOpenWrt_of_le hC liftEuclidDist_le_dist⟩
  · rw [isBounded_iff_isBoundedWrt_dist]
    exact ⟨isBoundedWrt_of_le hC liftEuclidDist_le_dist, isBoundedWrt_of_le one_pos h3⟩
  · exact (isQuotientMap_tupleProj hc).isOpen_preimage.symm
  · exact (isQuotientMap_tupleProj hc).continuous_iff
theorem tupleFactorProps_holds (s : Conventions.StandingParameters) (E : Ambient) (p : ℕ) :
    TupleFactorProps s E p := by
  refine ⟨fun A => ⟨fun h => isOpen_set_pi finite_univ fun i _ => h i,
    fun h => isClosed_set_pi fun i _ => h i,
    fun h => isCompact_univ_pi h⟩, fun i => ⟨continuous_apply i,
    fun K hK => hK.image (continuous_apply i)⟩, ?_⟩
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun i' =>
    isOpen_iInter_of_finite fun _ => isOpen_ne_fun (continuous_apply i) (continuous_apply i')
def blockHomeomorph {q : ℕ} (P : Fin q → ℕ) :
    Tuple s E (∑ a, P a) ≃ₜ ((a : Fin q) → Tuple s E (P a)) where
  toFun y a := blockOf P y a
  invFun z j := z (finSigmaFinEquiv.symm j).1 (finSigmaFinEquiv.symm j).2
  left_inv y := by
    funext j
    simp [blockOf]
  right_inv z := by
    funext a i
    have h : ∀ w : (a : Fin q) × Fin (P a), w = ⟨a, i⟩ → z w.1 w.2 = z a i := by
      rintro _ rfl
      rfl
    exact h _ (finSigmaFinEquiv.symm_apply_apply _)
  continuous_toFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact continuous_apply _
  continuous_invFun := by
    refine continuous_pi fun j => ?_
    exact (continuous_apply _).comp (continuous_apply _)
theorem blockProductProps_holds (s : Conventions.StandingParameters) (E : Ambient) :
    BlockProductProps s E := by
  intro q P _ _ A
  have hset : blockProduct P A = (blockHomeomorph (s := s) (E := E) P) ⁻¹' (univ.pi A) := by
    ext y
    simp [blockProduct, blockHomeomorph]
  rw [hset]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact (isOpen_set_pi finite_univ fun a _ => h a).preimage (blockHomeomorph P).continuous
  · exact (isClosed_set_pi fun a _ => h a).preimage (blockHomeomorph P).continuous
  · exact (blockHomeomorph P).isCompact_preimage.2 (isCompact_univ_pi h)
theorem tupleBallProps_of_covering (hc : TupleCoveringProps s E p) : TupleBallProps s E p := by
  have hcomp : ∀ A : Set (Tuple s E p), IsClosed A → Bornology.IsBounded A → IsCompact A := by
    intro A hA hB
    obtain ⟨r, hr⟩ := hB.subset_closedBall (tupleProj s E p 0)
    have hK : IsCompact (tupleProj s E p '' Metric.closedBall 0 r) :=
      (isCompact_closedBall 0 r).image (continuous_tupleProj hc)
    refine hK.of_isClosed_subset hA fun y hy => ?_
    obtain ⟨x', hx', hd⟩ := hc.2.2.2 0 y
    refine ⟨x', ?_, hx'⟩
    rw [Metric.mem_closedBall, dist_comm]
    refine (dist_le_liftSupDist 0 x').trans ?_
    rw [hd, ← dist_eq_supDist, dist_comm]
    exact hr hy
  refine ⟨hcomp, fun y r hr => ?_⟩
  have hcl : {y' : Tuple s E p | supDist y' y ≤ r} = Metric.closedBall y r := by
    ext y'
    simp [Metric.mem_closedBall, dist_eq_supDist]
  have hop : {y' : Tuple s E p | supDist y' y < r} = Metric.ball y r := by
    ext y'
    simp [Metric.mem_ball, dist_eq_supDist]
  rw [hcl, hop]
  refine ⟨?_, hcomp _ Metric.isClosed_closedBall Metric.isBounded_closedBall, ?_,
    Metric.isOpen_ball⟩
  · ext y'
    rw [Metric.mem_closedBall, dist_pi_le_iff hr.le]
    simp only [Set.mem_pi, mem_univ, true_implies]
    rfl
  · ext y'
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    simp only [Set.mem_pi, mem_univ, true_implies]
    rfl
theorem setDist_pos_of_disjoint {K K' : Set (Pt s E)} (hK : IsCompact K) (hK' : IsCompact K')
    (hd : Disjoint K K') : 0 < setDist s E K K' := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [setDist_empty_left]
  rcases K'.eq_empty_or_nonempty with rfl | hne'
  · simp [setDist_empty_right]
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmin⟩ := (hK.prod hK').exists_isMinOn (hne.prod hne')
    (continuous_dist (α := Pt s E)).continuousOn
  have hab : a ≠ b := fun h => (Set.disjoint_left.1 hd ha) (h ▸ hb)
  have hpos : 0 < dist a b := dist_pos.2 hab
  refine (ENNReal.ofReal_pos.2 hpos).trans_le ?_
  refine le_iInf₂ fun c hc => le_iInf₂ fun c' hc' => ?_
  exact ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hmin (c, c') (mem_prod.2 ⟨hc, hc'⟩))
theorem exists_factor_iteratedPartial (hc : TupleCoveringProps s E p)
    (α : PowerSeries.MultiIndex (4 * p)) (F : Tuple s E p → ℂ) :
    ∃ H : Tuple s E p → ℂ,
      H ∘ tupleProj s E p = iteratedPartial α (F ∘ tupleProj s E p) := by
  have hper : ∀ w : Fin (4 * p) → ℝ, IsTuplePeriod s E p w → ∀ x,
      iteratedPartial α (F ∘ tupleProj s E p) (x + w) =
        iteratedPartial α (F ∘ tupleProj s E p) x := by
    intro w hw
    refine iteratedPartial_induction (fun G => ∀ x, G (x + w) = G x)
      (fun j G h x => partialDeriv_periodic j h x) α fun x => ?_
    have he : tupleProj s E p (x + w) = tupleProj s E p x :=
      (hc.2.1 _ _).2 (by simpa using hw)
    simp [he]
  refine ⟨fun y => iteratedPartial α (F ∘ tupleProj s E p) (Function.surjInv hc.1 y), ?_⟩
  funext x
  have hx : tupleProj s E p (Function.surjInv hc.1 (tupleProj s E p x)) =
      tupleProj s E p x := Function.surjInv_eq hc.1 _
  have hw := (hc.2.1 _ _).1 hx
  have := hper _ hw x
  rw [add_sub_cancel] at this
  exact this
theorem multiDeriv_comp_eq (hc : TupleCoveringProps s E p) (α : PowerSeries.MultiIndex (4 * p))
    (F : Tuple s E p → ℂ) :
    multiDeriv α F ∘ tupleProj s E p = iteratedPartial α (F ∘ tupleProj s E p) :=
  multiDeriv_comp_tupleProj (exists_factor_iteratedPartial hc α F)
theorem multiDeriv_eq_zero_of_not_mem (hc : TupleCoveringProps s E p)
    (ho : TupleOpenSetProps s E p) (α : PowerSeries.MultiIndex (4 * p)) (F : Tuple s E p → ℂ)
    {y : Tuple s E p} (hy : y ∉ closedSupport F) : multiDeriv α F y = 0 := by
  have hW : IsOpen (tupleProj s E p ⁻¹' (closedSupport F)ᶜ) :=
    (ho.2.2.2.2.1 _).1 isClosed_closure.isOpen_compl
  have hz := iteratedPartial_induction
    (fun G => ∀ x ∈ tupleProj s E p ⁻¹' (closedSupport F)ᶜ, G x = 0)
    (fun j G h => partialDeriv_eq_zero_of_eqOn_open j hW h) α (G := F ∘ tupleProj s E p)
    (fun x hx => by
      by_contra hne
      exact hx (subset_closure hne))
  obtain ⟨x, rfl⟩ := hc.1 y
  have h1 := congrFun (multiDeriv_comp_eq hc α F) x
  simp only [Function.comp_apply] at h1
  rw [h1]
  exact hz x hy
theorem closedSupport_multiDeriv_subset (hc : TupleCoveringProps s E p)
    (ho : TupleOpenSetProps s E p) (α : PowerSeries.MultiIndex (4 * p)) (F : Tuple s E p → ℂ) :
    closedSupport (multiDeriv α F) ⊆ closedSupport F := by
  refine closure_minimal (fun y hy => ?_) isClosed_closure
  by_contra hn
  exact hy (multiDeriv_eq_zero_of_not_mem hc ho α F hn)
theorem continuous_multiDeriv (hc : TupleCoveringProps s E p) (ho : TupleOpenSetProps s E p)
    {F : Tuple s E p → ℂ} (α : PowerSeries.MultiIndex (4 * p))
    (h : ContinuousPartialsUpTo univ α.order (F ∘ tupleProj s E p)) :
    Continuous (multiDeriv α F) := by
  rw [ho.2.2.2.2.2 ℂ, multiDeriv_comp_eq hc]
  have h0 : ContinuousPartialsUpTo univ 0 (iteratedPartial α (F ∘ tupleProj s E p)) :=
    iteratedPartial_continuousPartials α 0 (by simpa using h)
  exact continuousOn_univ.1 h0
theorem cnNorm_lt_top (hc : TupleCoveringProps s E p) (ho : TupleOpenSetProps s E p)
    {F : Tuple s E p → ℂ} (n : ℕ)
    (hF : ContinuousPartialsUpTo univ n (F ∘ tupleProj s E p))
    (hK : IsCompact (closedSupport F)) : cnNorm n F < ⊤ := by
  have hb : ∀ α : PowerSeries.MultiIndex (4 * p), ∃ C : ℝ, 0 ≤ C ∧
      (α.order ≤ n → ∀ y, ‖multiDeriv α F y‖ ≤ C) := by
    intro α
    by_cases hα : α.order ≤ n
    · have hcont := continuous_multiDeriv hc ho α (hF.mono hα)
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun _ y => ?_⟩
      by_cases hy : y ∈ closedSupport F
      · exact (hC y hy).trans (le_max_left _ _)
      · rw [multiDeriv_eq_zero_of_not_mem hc ho α F hy]
        simp
    · exact ⟨0, le_rfl, fun h => absurd h hα⟩
  choose C hC0 hC using hb
  set S : Finset (PowerSeries.MultiIndex (4 * p)) :=
    Fintype.piFinset fun _ => Finset.range (n + 1) with hS
  have hmem : ∀ α : PowerSeries.MultiIndex (4 * p), α.order ≤ n → α ∈ S := by
    intro α hα
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    exact (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hα
  have hle : cnNorm n F ≤ ENNReal.ofReal (∑ α ∈ S, C α) := by
    refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
    refine ENNReal.ofReal_le_ofReal ((hC α hα y).trans ?_)
    exact Finset.single_le_sum (f := C) (fun a _ => hC0 a) (hmem α hα)
  exact hle.trans_lt ENNReal.ofReal_lt_top
theorem tupleDerivProps_of_covering (hc : TupleCoveringProps s E p)
    (ho : TupleOpenSetProps s E p) : TupleDerivProps s E p := by
  intro ν F hF
  have hclass : ∀ n : ℕ, (n : ℕ∞) ≤ ν →
      ContinuousPartialsUpTo univ n (F ∘ tupleProj s E p) := hF.2
  refine ⟨fun α hα => ⟨?_, continuous_multiDeriv hc ho α (hclass _ hα),
    closedSupport_multiDeriv_subset hc ho α F, fun hν => ?_⟩, fun n hn hK => ?_⟩
  · obtain ⟨H, hH⟩ := exists_factor_iteratedPartial hc α F
    exact ⟨H, hH, fun H' hH' => hc.1.injective_comp_right (hH'.trans hH.symm)⟩
  · subst hν
    have hsm : AllContinuousPartials (F ∘ tupleProj s E p) := fun n => hclass n le_top
    refine ⟨⟨isOpen_univ, fun n _ => ?_⟩, fun β => ?_⟩
    · rw [multiDeriv_comp_eq hc]
      exact iteratedPartial_continuousPartials α n (hsm _)
    · apply hc.1.injective_comp_right
      change multiDeriv β (multiDeriv α F) ∘ tupleProj s E p =
        multiDeriv (α + β) F ∘ tupleProj s E p
      rw [multiDeriv_comp_eq hc, multiDeriv_comp_eq hc, multiDeriv_comp_eq hc,
        iteratedPartial_iteratedPartial α β hsm]
  · subst hn
    exact cnNorm_lt_top hc ho n (hclass n le_rfl) hK
end Tuples
theorem holds_of_metricFactsClaim (h : DistanceFacts.MetricFactsClaim) : Holds := by
  intro s E
  refine ⟨fun p hp => ?_, blockProductProps_holds s E,
    fun K K' hK hK' hd => setDist_pos_of_disjoint hK hK' hd⟩
  have hc := tupleCoveringProps_of_metricFacts (h s E) p hp
  have ho := tupleOpenSetProps_of_covering hc
  exact ⟨hc, ho, tupleFactorProps_holds s E p, tupleBallProps_of_covering hc,
    tupleDerivProps_of_covering hc ho⟩
end YangMills.Construction.AmbientPoints.TupleTopology
