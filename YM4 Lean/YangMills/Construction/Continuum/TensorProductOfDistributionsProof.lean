import YangMills.Construction.Continuum.TensorProductOfDistributions
import Mathlib
set_option autoImplicit false
open TopologicalSpace YangMills.Construction.ReflectionSpaces.Euclidean Filter Topology MeasureTheory Set
open scoped ContDiff BoundedContinuousFunction
noncomputable section
namespace YangMills.Construction.Continuum.TensorProduct.Construct
section PartialDerivatives
variable {n ν : ℕ}
def IsTestFn (F : Coord n → ℂ) : Prop := ContDiff ℝ ∞ F ∧ HasCompactSupport F
theorem top_add_natCast_le (k : ℕ) : (∞ : WithTop ℕ∞) + (k : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : (⊤ : ℕ∞) + k ≤ ⊤)
instance derivIndex_nonempty : Nonempty (DerivIndex n ν) := ⟨⟨⟨0, by omega⟩, Fin.elim0⟩⟩
theorem contDiff_partialDeriv {k : ℕ} (c : Fin k → Fin n) {F : Coord n → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialDeriv c F) := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k F) := hF.iteratedFDeriv_right (top_add_natCast_le k)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Coord n) ℂ
    (fun j => Pi.single (c j) 1)).contDiff.comp h
theorem IsTestFn.partialDeriv {F : Coord n → ℂ} (hF : IsTestFn F) {k : ℕ} (c : Fin k → Fin n) :
    IsTestFn (partialDeriv c F) := by
  refine ⟨contDiff_partialDeriv c hF.1, ?_⟩
  have h := (hF.2.iteratedFDeriv (𝕜 := ℝ) k).comp_left
    (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Coord n) ℂ =>
      A fun j => Pi.single (c j) 1) (by simp)
  exact h
theorem partialDeriv_zero (c : Fin 0 → Fin n) (F : Coord n → ℂ) : partialDeriv c F = F := by
  funext x
  simp [partialDeriv]
theorem partialDeriv_add {k : ℕ} (c : Fin k → Fin n) {F G : Coord n → ℂ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) :
    partialDeriv c (F + G) = partialDeriv c F + partialDeriv c G := by
  funext x
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (x := x) (f := F) (g := G)
    (hF.contDiffAt.of_le (by exact_mod_cast le_top)) (hG.contDiffAt.of_le (by exact_mod_cast le_top))
  simp [partialDeriv, this]
theorem partialDeriv_smul {k : ℕ} (c : Fin k → Fin n) (r : ℂ) {F : Coord n → ℂ} (hF : ContDiff ℝ ∞ F) :
    partialDeriv c (r • F) = r • partialDeriv c F := by
  funext x
  have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (x := x) (f := F) (a := r)
    (hF.contDiffAt.of_le (by exact_mod_cast le_top))
  simp [partialDeriv, this]
theorem partialDeriv_cons {k : ℕ} (i : Fin n) (c : Fin k → Fin n) {F : Coord n → ℂ}
    (hF : ContDiff ℝ ∞ F) (x : Coord n) :
    partialDeriv (Fin.cons i c : Fin (k + 1) → Fin n) F x =
      fderiv ℝ (partialDeriv c F) x (Pi.single i 1) := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k F) := hF.iteratedFDeriv_right (top_add_natCast_le k)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) x :=
    (h.differentiable (by simp)).differentiableAt
  have h2 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Coord n) ℂ
    (fun j => Pi.single (c j) 1)).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have h3 : partialDeriv c F = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Coord n) ℂ
    (fun j => Pi.single (c j) 1)) ∘ iteratedFDeriv ℝ k F := rfl
  rw [h3, h2]
  simp only [partialDeriv, iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_def, Fin.cons_succ]
theorem partialDeriv_partialDeriv {F : Coord n → ℂ} (hF : ContDiff ℝ ∞ F) {l : ℕ} (d : Fin l → Fin n) :
    ∀ (k : ℕ) (c : Fin k → Fin n), ∃ m, m = k + l ∧ ∃ e : Fin m → Fin n,
      partialDeriv c (partialDeriv d F) = partialDeriv e F := by
  intro k
  induction k with
  | zero =>
    intro c
    exact ⟨l, by simp, d, partialDeriv_zero c _⟩
  | succ k ih =>
    intro c
    obtain ⟨m, hm, e, he⟩ := ih (Fin.tail c)
    refine ⟨m + 1, by omega, Fin.cons (c 0) e, ?_⟩
    funext x
    rw [partialDeriv_cons _ _ hF, ← he, ← partialDeriv_cons _ _ (contDiff_partialDeriv d hF),
      Fin.cons_self_tail]
theorem partialDeriv_comp_affine {a N : ℕ} (l : Coord a →L[ℝ] Coord N) (f : Fin a → Fin N)
    (hl : ∀ i, l (Pi.single i 1) = Pi.single (f i) 1) (t : Coord N) {H : Coord N → ℂ}
    (hH : ContDiff ℝ ∞ H) {k : ℕ} (c : Fin k → Fin a) (x : Coord a) :
    partialDeriv c (fun x => H (l x + t)) x = partialDeriv (f ∘ c) H (l x + t) := by
  have hs : ContDiff ℝ ∞ (fun w => H (w + t)) := hH.comp (by fun_prop)
  have h1 : (fun x => H (l x + t)) = (fun w => H (w + t)) ∘ l := rfl
  have h2 := l.iteratedFDeriv_comp_right hs x (i := k) (by exact_mod_cast le_top)
  simp only [partialDeriv]
  rw [h1, h2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right' k t]
  simp [hl, Function.comp]
theorem norm_le_uniformNorm {f : Coord n → ℂ} (hc : Continuous f) (hs : HasCompactSupport f)
    (x : Coord n) : ‖f x‖ ≤ YangMills.Construction.TestFunctions.uniformNorm f := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
theorem bddAbove_range_uniformNorm (ν : ℕ) (F : Coord n → ℂ) :
    BddAbove (Set.range fun p : DerivIndex n ν =>
      YangMills.Construction.TestFunctions.uniformNorm (partialDeriv p.2 F)) :=
  (Set.finite_range _).bddAbove
theorem norm_partialDeriv_le_cNorm {F : Coord n → ℂ} (hF : IsTestFn F) {k : ℕ} (hk : k ≤ ν)
    (c : Fin k → Fin n) (x : Coord n) : ‖partialDeriv c F x‖ ≤ cNorm ν F := by
  have h := norm_le_uniformNorm (hF.partialDeriv c).1.continuous (hF.partialDeriv c).2 x
  refine h.trans ?_
  exact le_ciSup (bddAbove_range_uniformNorm ν F) (⟨⟨k, by omega⟩, c⟩ : DerivIndex n ν)
theorem cNorm_mono {F : Coord n → ℂ} {ν' : ℕ} (h : ν ≤ ν') (hF : IsTestFn F) :
    cNorm ν F ≤ cNorm ν' F := by
  refine ciSup_le fun p => ?_
  refine ciSup_le fun x => ?_
  exact norm_partialDeriv_le_cNorm hF (by omega) p.2 x
end PartialDerivatives
section JetSpaces
variable {n : ℕ}
def toBCF {X : Type*} [TopologicalSpace X] (f : X → ℂ) (hc : Continuous f)
    (hs : HasCompactSupport f) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hc
    (Classical.choose (hc.bounded_above_of_compact_support hs))
    (Classical.choose_spec (hc.bounded_above_of_compact_support hs))
abbrev JetSpace (n ν : ℕ) : Type := DerivIndex n ν → (Coord n →ᵇ ℂ)
def jetOf (ν : ℕ) (F : Coord n → ℂ) (hF : IsTestFn F) : JetSpace n ν :=
  fun p => toBCF (partialDeriv p.2 F) (hF.partialDeriv p.2).1.continuous (hF.partialDeriv p.2).2
@[simp] theorem jetOf_apply (ν : ℕ) (F : Coord n → ℂ) (hF : IsTestFn F) (p : DerivIndex n ν)
    (x : Coord n) : jetOf ν F hF p x = partialDeriv p.2 F x := rfl
theorem cNorm_le_norm_jetOf (ν : ℕ) {F : Coord n → ℂ} (hF : IsTestFn F) :
    cNorm ν F ≤ ‖jetOf ν F hF‖ := by
  refine ciSup_le fun p => ?_
  refine ciSup_le fun x => ?_
  exact ((jetOf ν F hF p).norm_coe_le_norm x).trans (norm_le_pi_norm (jetOf ν F hF) p)
theorem isTestFn_of_mem {W : Opens (Coord n)} (F : testFunctionSpace W) :
    IsTestFn (F : Coord n → ℂ) := ⟨F.2.1, F.2.2.1⟩
theorem exists_jet_extension {W : Opens (Coord n)} {T : Module.Dual ℂ (testFunctionSpace W)}
    {K : Set (Coord n)} {ν : ℕ} (hb : HasOrderBound T K ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L : JetSpace n ν →L[ℂ] ℂ, ‖L‖ ≤ C ∧
      ∀ F : testFunctionSpace W, tsupport (F : Coord n → ℂ) ⊆ K →
        L (jetOf ν F (isTestFn_of_mem F)) = T F := by
  obtain ⟨C, hC, hb⟩ := hb
  let D : Submodule ℂ (testFunctionSpace W) :=
    { carrier := {F | tsupport (F : Coord n → ℂ) ⊆ K}
      add_mem' := by
        intro F G hF hG
        exact (tsupport_add (F : Coord n → ℂ) G).trans (Set.union_subset hF hG)
      zero_mem' := by
        show tsupport (0 : Coord n → ℂ) ⊆ K
        simp [tsupport]
      smul_mem' := by
        intro r F hF
        have hs : Function.support (r • (F : Coord n → ℂ)) ⊆ Function.support (F : Coord n → ℂ) :=
          Function.support_const_smul_subset r (F : Coord n → ℂ)
        exact (closure_mono hs).trans hF }
  let j : D →ₗ[ℂ] JetSpace n ν :=
    { toFun := fun F => jetOf ν F.1 (isTestFn_of_mem F.1)
      map_add' := by
        intro F G
        funext p
        ext x
        have := congrFun (partialDeriv_add p.2 (isTestFn_of_mem F.1).1 (isTestFn_of_mem G.1).1) x
        simpa using this
      map_smul' := by
        intro r F
        funext p
        ext x
        have := congrFun (partialDeriv_smul p.2 r (isTestFn_of_mem F.1).1) x
        simpa using this }
  have hinj : Function.Injective j := by
    intro F G hFG
    have h0 : ∀ x, (F.1 : Coord n → ℂ) x = (G.1 : Coord n → ℂ) x := by
      intro x
      have := congrArg (fun J : JetSpace n ν => J ⟨⟨0, by omega⟩, Fin.elim0⟩ x) hFG
      simpa [j, partialDeriv_zero] using this
    exact Subtype.ext (Subtype.ext (funext h0))
  let e := LinearEquiv.ofInjective j hinj
  let f : LinearMap.range j →ₗ[ℂ] ℂ := (T ∘ₗ D.subtype) ∘ₗ e.symm.toLinearMap
  have hf : ∀ v, ‖f v‖ ≤ C * ‖v‖ := by
    intro v
    obtain ⟨F, rfl⟩ := e.surjective v
    have h1 : f (e F) = T F.1 := by simp [f]
    rw [h1]
    refine (hb F.1 F.2).trans ?_
    have h2 : ((e F : LinearMap.range j) : JetSpace n ν) = jetOf ν F.1 (isTestFn_of_mem F.1) :=
      LinearEquiv.ofInjective_apply j F
    show _ ≤ C * ‖((e F : LinearMap.range j) : JetSpace n ν)‖
    rw [h2]
    exact mul_le_mul_of_nonneg_left (cNorm_le_norm_jetOf ν _) hC
  let g := f.mkContinuous C hf
  obtain ⟨L, hL, hn⟩ := exists_extension_norm_eq (LinearMap.range j) g
  refine ⟨C, hC, L, hn.le.trans (LinearMap.mkContinuous_norm_le _ hC _), ?_⟩
  intro F hFK
  have h3 := hL (e ⟨F, hFK⟩)
  have h4 : g (e ⟨F, hFK⟩) = T F := by simp [g, f]
  rw [h4] at h3
  exact h3
end JetSpaces
section Currying
variable {a b : ℕ}
def IsTestFn₂ (G : Coord a × Coord b → ℂ) : Prop := ContDiff ℝ ∞ G ∧ HasCompactSupport G
theorem IsTestFn₂.hasCompactSupport_slice {G : Coord a × Coord b → ℂ} (hG : IsTestFn₂ G)
    (x : Coord a) : HasCompactSupport fun y => G (x, y) := by
  refine HasCompactSupport.intro (hG.2.image continuous_snd) fun y hy => ?_
  refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨(x, y), h, rfl⟩
def curry (G : Coord a × Coord b → ℂ) (hG : IsTestFn₂ G) (x : Coord a) : Coord b →ᵇ ℂ :=
  toBCF (fun y => G (x, y)) (hG.1.continuous.comp (by fun_prop)) (hG.hasCompactSupport_slice x)
@[simp] theorem curry_apply (G : Coord a × Coord b → ℂ) (hG : IsTestFn₂ G) (x : Coord a)
    (y : Coord b) : curry G hG x y = G (x, y) := rfl
theorem continuous_curry {G : Coord a × Coord b → ℂ} (hG : IsTestFn₂ G) :
    Continuous (curry G hG) := by
  have hu : UniformContinuous G := hG.2.uniformContinuous_of_continuous hG.1.continuous
  refine (Metric.uniformContinuous_iff.2 fun ε hε => ?_).continuous
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 hu (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun {x x'} hx => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).2 fun y => ?_)
    (half_lt_self hε)
  refine (h ?_).le
  simpa [Prod.dist_eq] using hx
def partialFst (G : Coord a × Coord b → ℂ) (i : Fin a) : Coord a × Coord b → ℂ :=
  fun z => fderiv ℝ G z (Pi.single i 1, 0)
theorem IsTestFn₂.partialFst {G : Coord a × Coord b → ℂ} (hG : IsTestFn₂ G) (i : Fin a) :
    IsTestFn₂ (partialFst G i) := by
  refine ⟨(hG.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, ?_⟩
  exact hG.2.fderiv_apply (𝕜 := ℝ) _
theorem hasFDerivAt_curry {G : Coord a × Coord b → ℂ} (hG : IsTestFn₂ G) (x : Coord a) :
    HasFDerivAt (curry G hG)
      (∑ i, (ContinuousLinearMap.proj i : Coord a →L[ℝ] ℝ).smulRight
        (curry (partialFst G i) (hG.partialFst i) x)) x := by
  have hdiff : Differentiable ℝ G := hG.1.differentiable (by simp)
  have hc : Continuous (fderiv ℝ G) := hG.1.continuous_fderiv (by simp)
  have hu : UniformContinuous (fderiv ℝ G) :=
    (hG.2.fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous hc
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun ε hε => ?_)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 hu ε hε
  filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun y => ?_
  set B : Coord a →L[ℝ] ℂ := (fderiv ℝ G (x, y)).comp (ContinuousLinearMap.inl ℝ _ _) with hB
  have hsum : ∀ v : Coord a, B v = ∑ i, v i • partialFst G i (x, y) := by
    intro v
    have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Coord a) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    simp [B, partialFst]
  let g : Coord a → ℂ := fun w => G (w, y) - B w
  let g' : Coord a → Coord a →L[ℝ] ℂ :=
    fun w => (fderiv ℝ G (w, y)).comp (ContinuousLinearMap.inl ℝ _ _) - B
  have hg : ∀ w ∈ Metric.ball x δ, HasFDerivWithinAt g (g' w) (Metric.ball x δ) w := by
    intro w _
    have h1 : HasFDerivAt (fun w => G (w, y))
        ((fderiv ℝ G (w, y)).comp (ContinuousLinearMap.inl ℝ _ _)) w :=
      (hdiff (w, y)).hasFDerivAt.comp w (hasFDerivAt_prodMk_left w y)
    exact (h1.sub B.hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ w ∈ Metric.ball x δ, ‖g' w‖ ≤ ε := by
    intro w hw
    have hd : dist (fderiv ℝ G (w, y)) (fderiv ℝ G (x, y)) < ε := by
      refine h ?_
      simpa [Prod.dist_eq] using hw
    rw [dist_eq_norm] at hd
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun v => ?_
    have h3 : g' w v = (fderiv ℝ G (w, y) - fderiv ℝ G (x, y)) (v, 0) := by
      simp [g', B]
    rw [h3]
    refine ((fderiv ℝ G (w, y) - fderiv ℝ G (x, y)).le_opNorm _).trans ?_
    have h4 : ‖((v, 0) : Coord a × Coord b)‖ = ‖v‖ := by simp [Prod.norm_def]
    rw [h4]
    exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
  have hmv := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hb
    (Metric.mem_ball_self hδ) hz
  have hval : (curry G hG z - curry G hG x -
      (∑ i, (ContinuousLinearMap.proj i : Coord a →L[ℝ] ℝ).smulRight
        (curry (partialFst G i) (hG.partialFst i) x)) (z - x)) y = g z - g x := by
    have hs : ((∑ i, (ContinuousLinearMap.proj i : Coord a →L[ℝ] ℝ).smulRight
        (curry (partialFst G i) (hG.partialFst i) x)) (z - x)) y = B (z - x) := by
      rw [hsum, _root_.sum_apply]
      have : ∀ (s : Finset (Fin a)) (f : Fin a → Coord b →ᵇ ℂ), (∑ i ∈ s, f i) y = ∑ i ∈ s, f i y := by
        intro s f
        exact map_sum (BoundedContinuousFunction.evalCLM ℝ y) f s
      rw [this]
      rfl
    rw [BoundedContinuousFunction.sub_apply, hs, BoundedContinuousFunction.sub_apply,
      curry_apply, curry_apply]
    simp only [g, map_sub]
    ring
  rw [hval]
  exact hmv
theorem contDiff_curry_nat (m : ℕ) :
    ∀ (G : Coord a × Coord b → ℂ) (hG : IsTestFn₂ G), ContDiff ℝ m (curry G hG) := by
  induction m with
  | zero =>
    intro G hG
    exact contDiff_zero.2 (continuous_curry hG)
  | succ m ih =>
    intro G hG
    have : ContDiff ℝ ((m : WithTop ℕ∞) + 1) (curry G hG) := by
      refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ?_, hasFDerivAt_curry hG⟩
      refine ContDiff.sum fun i _ => ?_
      exact (ContinuousLinearMap.smulRightL ℝ (Coord a) (Coord b →ᵇ ℂ)
        (ContinuousLinearMap.proj i)).contDiff.comp (ih _ (hG.partialFst i))
    exact_mod_cast this
theorem contDiff_curry {G : Coord a × Coord b → ℂ} (hG : IsTestFn₂ G) :
    ContDiff ℝ ∞ (curry G hG) :=
  contDiff_infty.2 fun m => contDiff_curry_nat m G hG
theorem iteratedFDeriv_curry_apply {G : Coord a × Coord b → ℂ} (hG : IsTestFn₂ G) (k : ℕ)
    (x : Coord a) (v : Fin k → Coord a) (y : Coord b) :
    iteratedFDeriv ℝ k (curry G hG) x v y = iteratedFDeriv ℝ k (fun x => G (x, y)) x v := by
  have h1 : (fun x => G (x, y)) = (BoundedContinuousFunction.evalCLM ℝ y) ∘ curry G hG := rfl
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_left _
    (contDiff_curry hG).contDiffAt (by exact_mod_cast le_top)]
  rfl
end Currying
section CoordinateBlocks
variable {a b N : ℕ} (e : Fin a ⊕ Fin b ≃ Fin N)
def embedFst : Coord a →L[ℝ] Coord N :=
  ContinuousLinearMap.pi fun c =>
    (e.symm c).elim (fun i => ContinuousLinearMap.proj i) (fun _ => 0)
def embedSnd : Coord b →L[ℝ] Coord N :=
  ContinuousLinearMap.pi fun c =>
    (e.symm c).elim (fun _ => 0) (fun i => ContinuousLinearMap.proj i)
def projFst (z : Coord N) : Coord a := fun i => z (e (Sum.inl i))
def projSnd (z : Coord N) : Coord b := fun i => z (e (Sum.inr i))
theorem continuous_projFst : Continuous (projFst e) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_projSnd : Continuous (projSnd e) :=
  continuous_pi fun _ => continuous_apply _
@[simp] theorem embedFst_inl (x : Coord a) (i : Fin a) : embedFst e x (e (Sum.inl i)) = x i := by
  simp [embedFst]
@[simp] theorem embedFst_inr (x : Coord a) (i : Fin b) : embedFst e x (e (Sum.inr i)) = 0 := by
  simp [embedFst]
@[simp] theorem embedSnd_inl (y : Coord b) (i : Fin a) : embedSnd e y (e (Sum.inl i)) = 0 := by
  simp [embedSnd]
@[simp] theorem embedSnd_inr (y : Coord b) (i : Fin b) : embedSnd e y (e (Sum.inr i)) = y i := by
  simp [embedSnd]
@[simp] theorem projFst_embed_add (x : Coord a) (y : Coord b) :
    projFst e (embedFst e x + embedSnd e y) = x := by
  funext i
  simp [projFst]
@[simp] theorem projSnd_embed_add (x : Coord a) (y : Coord b) :
    projSnd e (embedFst e x + embedSnd e y) = y := by
  funext i
  simp [projSnd]
theorem embedFst_single (i : Fin a) :
    embedFst e (Pi.single i 1) = Pi.single (e (Sum.inl i)) 1 := by
  funext c
  obtain ⟨s, rfl⟩ := e.surjective c
  rcases s with j | j
  · simp [Pi.single_apply, e.injective.eq_iff]
  · simp [Pi.single_apply, e.injective.eq_iff]
theorem embedSnd_single (i : Fin b) :
    embedSnd e (Pi.single i 1) = Pi.single (e (Sum.inr i)) 1 := by
  funext c
  obtain ⟨s, rfl⟩ := e.surjective c
  rcases s with j | j
  · simp [Pi.single_apply, e.injective.eq_iff]
  · simp [Pi.single_apply, e.injective.eq_iff]
end CoordinateBlocks
section TwoBlocks
variable {a b N : ℕ} (e : Fin a ⊕ Fin b ≃ Fin N)
variable {A : Opens (Coord a)} {B : Opens (Coord b)} {W : Opens (Coord N)}
theorem tsupport_section_subset (φ : testFunctionSpace W) (x : Coord a) :
    tsupport (fun y => (φ : Coord N → ℂ) (embedSnd e y + embedFst e x)) ⊆
      projSnd e '' tsupport (φ : Coord N → ℂ) := by
  have hK : IsCompact (tsupport (φ : Coord N → ℂ)) := φ.2.2.1
  refine closure_minimal ?_ (hK.image (continuous_projSnd e)).isClosed
  intro y hy
  refine ⟨embedSnd e y + embedFst e x, subset_tsupport _ hy, ?_⟩
  rw [add_comm, projSnd_embed_add]
theorem image_projSnd_subset (hW : ∀ z, z ∈ W ↔ projFst e z ∈ A ∧ projSnd e z ∈ B)
    {K : Set (Coord N)} (hK : K ⊆ W) : projSnd e '' K ⊆ B := by
  rintro _ ⟨z, hz, rfl⟩
  exact ((hW z).1 (hK hz)).2
theorem image_projFst_subset (hW : ∀ z, z ∈ W ↔ projFst e z ∈ A ∧ projSnd e z ∈ B)
    {K : Set (Coord N)} (hK : K ⊆ W) : projFst e '' K ⊆ A := by
  rintro _ ⟨z, hz, rfl⟩
  exact ((hW z).1 (hK hz)).1
def sectionAt (hW : ∀ z, z ∈ W ↔ projFst e z ∈ A ∧ projSnd e z ∈ B) (φ : testFunctionSpace W)
    (x : Coord a) : testFunctionSpace B :=
  ⟨fun y => (φ : Coord N → ℂ) (embedSnd e y + embedFst e x),
    φ.2.1.comp (by fun_prop),
    ((φ.2.2.1.image (continuous_projSnd e))).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_section_subset e φ x),
    (tsupport_section_subset e φ x).trans (image_projSnd_subset e hW φ.2.2.2)⟩
def uncurryBlocks (H : Coord N → ℂ) : Coord a × Coord b → ℂ :=
  fun z => H (embedFst e z.1 + embedSnd e z.2)
theorem isTestFn₂_uncurryBlocks {H : Coord N → ℂ} (hH : IsTestFn H) :
    IsTestFn₂ (uncurryBlocks (a := a) (b := b) e H) := by
  refine ⟨hH.1.comp (by fun_prop), ?_⟩
  have hK : IsCompact (tsupport H) := hH.2
  refine HasCompactSupport.intro
    ((hK.image (continuous_projFst e)).prod (hK.image (continuous_projSnd e))) fun z hz => ?_
  show H _ = 0
  refine image_eq_zero_of_notMem_tsupport fun h => hz ⟨?_, ?_⟩
  · exact ⟨_, h, projFst_embed_add e z.1 z.2⟩
  · exact ⟨_, h, projSnd_embed_add e z.1 z.2⟩
def sndIndices {k : ℕ} (c : Fin k → Fin b) : Fin k → Fin N := fun j => e (Sum.inr (c j))
def jetPath (ν : ℕ) {F : Coord N → ℂ} (hF : IsTestFn F) (x : Coord a) : JetSpace b ν :=
  fun p => curry (uncurryBlocks e (partialDeriv (sndIndices e p.2) F))
    (isTestFn₂_uncurryBlocks e (hF.partialDeriv _)) x
theorem contDiff_jetPath (ν : ℕ) {F : Coord N → ℂ} (hF : IsTestFn F) :
    ContDiff ℝ ∞ (jetPath (a := a) e ν hF) :=
  contDiff_pi.2 fun _ => contDiff_curry _
theorem isTestFn_section {F : Coord N → ℂ} (hF : IsTestFn F) (x : Coord a) :
    IsTestFn (fun y : Coord b => F (embedSnd e y + embedFst e x)) := by
  refine ⟨hF.1.comp (by fun_prop), ?_⟩
  have h := (isTestFn₂_uncurryBlocks (a := a) (b := b) e hF).hasCompactSupport_slice x
  have h2 : (fun y : Coord b => F (embedSnd e y + embedFst e x)) =
      fun y => uncurryBlocks e F (x, y) := by
    funext y
    simp [uncurryBlocks, add_comm]
  rw [h2]
  exact h
theorem jetOf_section (ν : ℕ) {F : Coord N → ℂ} (hF : IsTestFn F) (x : Coord a) :
    jetOf ν _ (isTestFn_section e hF x) = jetPath e ν hF x := by
  funext p
  ext y
  rw [jetOf_apply]
  rw [partialDeriv_comp_affine (embedSnd e) (fun i => e (Sum.inr i)) (embedSnd_single e) _ hF.1]
  simp only [jetPath, curry_apply, uncurryBlocks]
  rw [add_comm (embedSnd e y)]
  rfl
theorem norm_iteratedFDeriv_jetPath_le (ν ν₁ : ℕ) {F : Coord N → ℂ} (hF : IsTestFn F) {k : ℕ}
    (hk : k ≤ ν₁) (c : Fin k → Fin a) (x : Coord a) :
    ‖iteratedFDeriv ℝ k (jetPath e ν hF) x fun j => Pi.single (c j) 1‖ ≤
      cNorm (ν₁ + ν) F := by
  have h0 : 0 ≤ cNorm (ν₁ + ν) F :=
    (norm_nonneg _).trans (norm_partialDeriv_le_cNorm hF (Nat.zero_le _) (Fin.elim0) 0)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun p => ?_
  refine (BoundedContinuousFunction.norm_le h0).2 fun y => ?_
  set H := partialDeriv (sndIndices e p.2) F with hHdef
  have hH : IsTestFn H := hF.partialDeriv _
  have h2 : iteratedFDeriv ℝ k (jetPath e ν hF) x (fun j => Pi.single (c j) 1) p =
      iteratedFDeriv ℝ k (curry (uncurryBlocks e H) (isTestFn₂_uncurryBlocks e hH)) x
        (fun j => Pi.single (c j) 1) := by
    have h3 := (ContinuousLinearMap.proj p : JetSpace b ν →L[ℝ] (Coord b →ᵇ ℂ)).iteratedFDeriv_comp_left
      (contDiff_jetPath (a := a) e ν hF).contDiffAt (x := x) (i := k)
      (by exact_mod_cast le_top)
    have h4 : (ContinuousLinearMap.proj p : JetSpace b ν →L[ℝ] (Coord b →ᵇ ℂ)) ∘ jetPath e ν hF =
        curry (uncurryBlocks e H) (isTestFn₂_uncurryBlocks e hH) := rfl
    rw [h4] at h3
    rw [h3]
    rfl
  rw [h2, iteratedFDeriv_curry_apply]
  have h5 : iteratedFDeriv ℝ k (fun x => uncurryBlocks e H (x, y)) x (fun j => Pi.single (c j) 1) =
      partialDeriv c (fun x => H (embedFst e x + embedSnd e y)) x := rfl
  rw [h5, partialDeriv_comp_affine (embedFst e) (fun i => e (Sum.inl i)) (embedFst_single e) _ hH.1]
  obtain ⟨m, hm, d, hd⟩ := partialDeriv_partialDeriv hF.1 (sndIndices e p.2) k
    ((fun i => e (Sum.inl i)) ∘ c)
  rw [hHdef, hd]
  refine norm_partialDeriv_le_cNorm hF ?_ d _
  have := p.1.2
  omega
variable (hW : ∀ z, z ∈ W ↔ projFst e z ∈ A ∧ projSnd e z ∈ B)
def pairSnd (w : Distribution B) (φ : testFunctionSpace W) : Coord a → ℂ :=
  fun x => w.form (sectionAt e hW φ x)
theorem pairSnd_eq_comp (w : Distribution B) (φ : testFunctionSpace W) {ν : ℕ}
    {K : Set (Coord N)} {L : JetSpace b ν →L[ℂ] ℂ}
    (hL : ∀ F : testFunctionSpace B, tsupport (F : Coord b → ℂ) ⊆ projSnd e '' K →
      L (jetOf ν F (isTestFn_of_mem F)) = w.form F)
    (hK : tsupport (φ : Coord N → ℂ) ⊆ K) :
    pairSnd e hW w φ =
      (L.restrictScalars ℝ) ∘ jetPath e ν (isTestFn_of_mem φ) := by
  funext x
  have h1 := hL (sectionAt e hW φ x)
    ((tsupport_section_subset e φ x).trans (Set.image_mono hK))
  simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
  rw [← jetOf_section e ν (isTestFn_of_mem φ) x]
  exact h1.symm
theorem isCompact_tsupport_test (φ : testFunctionSpace W) : IsCompact (tsupport (φ : Coord N → ℂ)) :=
  φ.2.2.1
theorem contDiff_pairSnd (w : Distribution B) (φ : testFunctionSpace W) :
    ContDiff ℝ ∞ (pairSnd e hW w φ) := by
  have hc := (isCompact_tsupport_test φ).image (continuous_projSnd e)
  obtain ⟨ν, hb⟩ := w.bound _ hc (image_projSnd_subset e hW φ.2.2.2)
  obtain ⟨C, _, L, _, hL⟩ := exists_jet_extension hb
  rw [pairSnd_eq_comp e hW w φ hL subset_rfl]
  exact (L.restrictScalars ℝ).contDiff.comp (contDiff_jetPath e ν _)
theorem tsupport_pairSnd_subset (w : Distribution B) (φ : testFunctionSpace W) :
    tsupport (pairSnd e hW w φ) ⊆ projFst e '' tsupport (φ : Coord N → ℂ) := by
  refine closure_minimal ?_ ((isCompact_tsupport_test φ).image (continuous_projFst e)).isClosed
  intro x hx
  by_contra hn
  refine hx ?_
  have h0 : sectionAt e hW φ x = 0 := by
    refine Subtype.ext (funext fun y => ?_)
    show (φ : Coord N → ℂ) _ = 0
    refine image_eq_zero_of_notMem_tsupport fun h => hn ⟨_, h, ?_⟩
    rw [add_comm, projFst_embed_add]
  simp [pairSnd, h0]
def pairSndTest (w : Distribution B) (φ : testFunctionSpace W) : testFunctionSpace A :=
  ⟨pairSnd e hW w φ, contDiff_pairSnd e hW w φ,
    ((isCompact_tsupport_test φ).image (continuous_projFst e)).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_pairSnd_subset e hW w φ),
    (tsupport_pairSnd_subset e hW w φ).trans (image_projFst_subset e hW φ.2.2.2)⟩
def pairSndLinear (w : Distribution B) : testFunctionSpace W →ₗ[ℂ] testFunctionSpace A where
  toFun := pairSndTest e hW w
  map_add' φ φ' := by
    refine Subtype.ext (funext fun x => ?_)
    have h : sectionAt e hW (φ + φ') x = sectionAt e hW φ x + sectionAt e hW φ' x := rfl
    show w.form _ = w.form _ + w.form _
    rw [← map_add]
    rfl
  map_smul' r φ := by
    refine Subtype.ext (funext fun x => ?_)
    show w.form _ = r • w.form _
    rw [← map_smul]
    rfl
theorem cNorm_pairSnd_le (w : Distribution B) (ν₁ : ℕ) {ν : ℕ}
    {K : Set (Coord N)} {L : JetSpace b ν →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hLC : ‖L‖ ≤ C)
    (hL : ∀ F : testFunctionSpace B, tsupport (F : Coord b → ℂ) ⊆ projSnd e '' K →
      L (jetOf ν F (isTestFn_of_mem F)) = w.form F)
    (φ : testFunctionSpace W) (hK : tsupport (φ : Coord N → ℂ) ⊆ K) :
    cNorm ν₁ (pairSnd e hW w φ) ≤ C * cNorm (ν₁ + ν) (φ : Coord N → ℂ) := by
  refine ciSup_le fun p => ?_
  refine ciSup_le fun x => ?_
  have hcd := contDiff_jetPath (a := a) e ν (isTestFn_of_mem φ)
  have h1 : partialDeriv p.2 (pairSnd e hW w φ) x =
      L (iteratedFDeriv ℝ p.1 (jetPath e ν (isTestFn_of_mem φ)) x
        fun j => Pi.single (p.2 j) 1) := by
    simp only [partialDeriv]
    rw [pairSnd_eq_comp e hW w φ hL hK,
      ContinuousLinearMap.iteratedFDeriv_comp_left _ hcd.contDiffAt
        (by exact_mod_cast le_top)]
    rfl
  rw [h1]
  refine (L.le_opNorm _).trans ?_
  refine mul_le_mul hLC ?_ (norm_nonneg _) hC
  exact norm_iteratedFDeriv_jetPath_le e ν ν₁ _ (by have := p.1.2; omega) p.2 x
def iteratedPairing (v : Distribution A) (w : Distribution B) : Distribution W where
  form := v.form ∘ₗ pairSndLinear e hW w
  bound K hK hKW := by
    obtain ⟨ν₁, C₁, hC₁, h₁⟩ := v.bound _ (hK.image (continuous_projFst e))
      (image_projFst_subset e hW hKW)
    obtain ⟨ν₂, hb₂⟩ := w.bound _ (hK.image (continuous_projSnd e))
      (image_projSnd_subset e hW hKW)
    obtain ⟨C₂, hC₂, L, hLC, hL⟩ := exists_jet_extension hb₂
    refine ⟨ν₁ + ν₂, C₁ * C₂, mul_nonneg hC₁ hC₂, fun φ hφ => ?_⟩
    have hs : tsupport (pairSndTest e hW w φ : Coord a → ℂ) ⊆ projFst e '' K :=
      (tsupport_pairSnd_subset e hW w φ).trans (Set.image_mono hφ)
    refine (h₁ (pairSndTest e hW w φ) hs).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (cNorm_pairSnd_le e hW w ν₁ hC₂ hLC hL φ hφ) hC₁
theorem iteratedPairing_apply_of_product (v : Distribution A) (w : Distribution B)
    (f : testFunctionSpace A) (g : testFunctionSpace B) (φ : testFunctionSpace W)
    (hφ : ∀ z, (φ : Coord N → ℂ) z = (f : Coord a → ℂ) (projFst e z) *
      (g : Coord b → ℂ) (projSnd e z)) :
    (iteratedPairing e hW v w).form φ = v.form f * w.form g := by
  have h1 : ∀ x, sectionAt e hW φ x = (f : Coord a → ℂ) x • g := by
    intro x
    refine Subtype.ext (funext fun y => ?_)
    show (φ : Coord N → ℂ) _ = _
    rw [hφ, add_comm, projFst_embed_add, projSnd_embed_add]
    rfl
  have h2 : pairSndLinear e hW w φ = w.form g • f := by
    refine Subtype.ext (funext fun x => ?_)
    show w.form (sectionAt e hW φ x) = _
    rw [h1, map_smul]
    simp [mul_comm]
  show v.form (pairSndLinear e hW w φ) = _
  rw [h2, map_smul]
  simp [mul_comm]
end TwoBlocks
section Convolution
variable {N : ℕ}
def smoothConv (f g : Coord N → ℂ) : Coord N → ℂ :=
  convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume
theorem smoothConv_apply (f g : Coord N → ℂ) (x : Coord N) :
    smoothConv f g x = ∫ t, f t * g (x - t) := rfl
theorem smoothConv_comm (f g : Coord N → ℂ) : smoothConv f g = smoothConv g f := by
  funext x
  rw [smoothConv, convolution_eq_swap, smoothConv_apply]
  simp only [ContinuousLinearMap.mul_apply']
  simp_rw [mul_comm]
theorem contDiff_smoothConv {f g : Coord N → ℂ} (hf : Continuous f) (hg : IsTestFn g) :
    ContDiff ℝ ∞ (smoothConv f g) :=
  hg.2.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable hg.1
theorem fderiv_smoothConv {f g : Coord N → ℂ} (hf : Continuous f) (hg : IsTestFn g) (x v : Coord N) :
    fderiv ℝ (smoothConv f g) x v = smoothConv f (fun y => fderiv ℝ g y v) x := by
  have h1 := (hg.2.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
    hf.locallyIntegrable (hg.1.of_le (by exact_mod_cast le_top)) x).fderiv
  have hc : Continuous (fderiv ℝ g) := hg.1.continuous_fderiv (by simp)
  have hint := ((hg.2.fderiv (𝕜 := ℝ)).convolutionExists_right (μ := volume)
    ((ContinuousLinearMap.mul ℝ ℂ).precompR (Coord N)) hf.locallyIntegrable hc) x
  have h2 : fderiv ℝ (smoothConv f g) x = _ := h1
  rw [h2, convolution_def, ContinuousLinearMap.integral_apply hint, smoothConv_apply]
  simp
theorem partialDeriv_smoothConv {f g : Coord N → ℂ} (hf : Continuous f) (hg : IsTestFn g) :
    ∀ (k : ℕ) (c : Fin k → Fin N),
      partialDeriv c (smoothConv f g) = smoothConv f (partialDeriv c g) := by
  intro k
  induction k with
  | zero =>
    intro c
    rw [partialDeriv_zero, partialDeriv_zero]
  | succ k ih =>
    intro c
    funext x
    rw [← Fin.cons_self_tail c, partialDeriv_cons _ _ (contDiff_smoothConv hf hg), ih,
      fderiv_smoothConv hf (hg.partialDeriv _)]
    congr 1
    funext y
    rw [partialDeriv_cons _ _ hg.1]
end Convolution
section Annihilation
variable {N : ℕ}
theorem partialDeriv_sub {k : ℕ} (c : Fin k → Fin N) {F G : Coord N → ℂ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) :
    partialDeriv c (F - G) = partialDeriv c F - partialDeriv c G := by
  have h : F - G = F + (-1 : ℂ) • G := by
    funext x
    simp [sub_eq_add_neg]
  have hs : ContDiff ℝ ∞ ((-1 : ℂ) • G) := hG.const_smul (-1 : ℂ)
  rw [h, partialDeriv_add c hF hs, partialDeriv_smul c _ hG]
  funext x
  simp [sub_eq_add_neg]
theorem exists_uniform_modulus {F : Coord N → ℂ} (hF : IsTestFn F) (ν : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ (p : DerivIndex N ν) (x x' : Coord N), dist x x' < δ →
      dist (partialDeriv p.2 F x) (partialDeriv p.2 F x') < η := by
  have hu : UniformContinuous fun x (p : DerivIndex N ν) => partialDeriv p.2 F x :=
    uniformContinuous_pi.2 fun p =>
      (hF.partialDeriv p.2).2.uniformContinuous_of_continuous (hF.partialDeriv p.2).1.continuous
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 hu η hη
  refine ⟨δ, hδ, fun p x x' hx => ?_⟩
  exact (dist_pi_lt_iff hη).1 (h hx) p
theorem dist_smoothConv_le {h : Coord N → ℂ} (hc : Continuous h) {ρ : Coord N → ℝ} {ε η : ℝ}
    (hη : 0 ≤ η) (hs : Function.support ρ ⊆ Metric.ball 0 ε) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x = 1)
    (hm : ∀ x x', dist x x' < ε → dist (h x) (h x') ≤ η) (x : Coord N) :
    dist (smoothConv (fun x => (ρ x : ℂ)) h x) (h x) ≤ η := by
  have h2 := dist_convolution_le (μ := volume) (f := ρ) (g := h) (x₀ := x) (z₀ := h x) hη hs h0 h1
    hc.aestronglyMeasurable (fun x' hx' => hm x' x hx')
  have h3 : smoothConv (fun x => (ρ x : ℂ)) h x =
      convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    rw [smoothConv_apply, convolution_def]
    simp [Complex.real_smul]
  rw [h3]
  exact h2
structure IsAnnihilatingMollifier {W : Opens (Coord N)} (T : Module.Dual ℂ (testFunctionSpace W))
    (ε : ℝ) (ρ : Coord N → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ρ
  hasCompactSupport : HasCompactSupport ρ
  nonneg : ∀ x, 0 ≤ ρ x
  integral_eq_one : ∫ x, ρ x = 1
  support_subset : Function.support ρ ⊆ Metric.ball 0 ε
  annihilates : ∀ y : Coord N, Metric.closedBall y ε ⊆ W → ∀ F : testFunctionSpace W,
    (∀ x, (F : Coord N → ℂ) x = (ρ (x - y) : ℂ)) → T F = 0
theorem IsAnnihilatingMollifier.isTestFn {W : Opens (Coord N)}
    {T : Module.Dual ℂ (testFunctionSpace W)} {ε : ℝ}
    {ρ : Coord N → ℝ} (h : IsAnnihilatingMollifier T ε ρ) : IsTestFn fun x => (ρ x : ℂ) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp h.contDiff, ?_⟩
  exact h.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
theorem isTestFn₂_mul_translate {φ ρ : Coord N → ℂ} (hφ : IsTestFn φ) (hρ : IsTestFn ρ) :
    IsTestFn₂ (fun z : Coord N × Coord N => φ z.1 * ρ (z.2 - z.1)) := by
  refine ⟨(hφ.1.comp contDiff_fst).mul (hρ.1.comp (contDiff_snd.sub contDiff_fst)), ?_⟩
  have hK : IsCompact (tsupport φ) := hφ.2
  have hS : IsCompact (tsupport ρ) := hρ.2
  refine HasCompactSupport.intro (hK.prod (hK.add hS)) fun z hz => ?_
  by_cases h1 : z.1 ∈ tsupport φ
  · have h2 : z.2 - z.1 ∉ tsupport ρ := fun h3 =>
      hz ⟨h1, Set.mem_add.2 ⟨z.1, h1, z.2 - z.1, h3, by simp⟩⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]
theorem apply_smoothConv_eq_zero {W : Opens (Coord N)} {T : Module.Dual ℂ (testFunctionSpace W)}
    {ε : ℝ} {ρ : Coord N → ℝ} (hρ : IsAnnihilatingMollifier T ε ρ) (φ : testFunctionSpace W)
    {K' : Set (Coord N)}
    (hK' : ∀ y ∈ tsupport (φ : Coord N → ℂ), Metric.closedBall y ε ⊆ K') (hKW : K' ⊆ W)
    {ν : ℕ} (hb : HasOrderBound T K' ν) (ψ : testFunctionSpace W)
    (hψ : (ψ : Coord N → ℂ) = smoothConv φ (fun x => (ρ x : ℂ)))
    (hψK : tsupport (ψ : Coord N → ℂ) ⊆ K') : T ψ = 0 := by
  obtain ⟨C, _, L, _, hL⟩ := exists_jet_extension hb
  have hφ := isTestFn_of_mem φ
  have hr := hρ.isTestFn
  set r : Coord N → ℂ := fun x => (ρ x : ℂ) with hrdef
  let G : DerivIndex N ν → Coord N × Coord N → ℂ :=
    fun p z => (φ : Coord N → ℂ) z.1 * partialDeriv p.2 r (z.2 - z.1)
  have hG : ∀ p, IsTestFn₂ (G p) := fun p => isTestFn₂_mul_translate hφ (hr.partialDeriv p.2)
  let J : Coord N → JetSpace N ν := fun y p => curry (G p) (hG p) y
  have hJc : Continuous J := continuous_pi fun p => continuous_curry (hG p)
  have hJs : HasCompactSupport J := by
    refine HasCompactSupport.intro (isCompact_tsupport_test φ) fun y hy => ?_
    funext p
    ext x
    simp [J, G, image_eq_zero_of_notMem_tsupport hy]
  have hint : Integrable J := hJc.integrable_of_hasCompactSupport hJs
  have hzero : ∀ y, L (J y) = 0 := by
    intro y
    by_cases hy : (φ : Coord N → ℂ) y = 0
    · have : J y = 0 := by
        funext p
        ext x
        simp [J, G, hy]
      rw [this, map_zero]
    · have hyK : y ∈ tsupport (φ : Coord N → ℂ) := subset_tsupport _ hy
      have hτc : ContDiff ℝ ∞ (fun x => r (x - y)) := hr.1.comp (by fun_prop)
      have hτs : tsupport (fun x => r (x - y)) ⊆ Metric.closedBall y ε := by
        refine closure_minimal ?_ Metric.isClosed_closedBall
        intro x hx
        have hx' : ρ (x - y) ≠ 0 := fun h0 => hx (by simp [hrdef, h0])
        have := hρ.support_subset hx'
        rw [Metric.mem_ball, dist_zero_right] at this
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact this.le
      have hτK : tsupport (fun x => r (x - y)) ⊆ K' := hτs.trans (hK' y hyK)
      have hcompact : IsCompact (tsupport (fun x => r (x - y))) :=
        (isCompact_closedBall y ε).of_isClosed_subset (isClosed_tsupport _) hτs
      let τ : testFunctionSpace W := ⟨fun x => r (x - y), hτc, hcompact, hτK.trans hKW⟩
      have h1 : T τ = 0 := hρ.annihilates y ((hK' y hyK).trans hKW) τ fun x => rfl
      have h2 : J y = (φ : Coord N → ℂ) y • jetOf ν τ (isTestFn_of_mem τ) := by
        funext p
        ext x
        have h3 := partialDeriv_comp_affine (ContinuousLinearMap.id ℝ (Coord N)) id (fun _ => rfl)
          (-y) hr.1 p.2 x
        have h4 : (fun x => r (x - y)) =
            fun x => r ((ContinuousLinearMap.id ℝ (Coord N)) x + -y) := by
          funext x
          simp [sub_eq_add_neg]
        simp only [J, G, curry_apply, Pi.smul_apply, BoundedContinuousFunction.coe_smul,
          jetOf_apply, smul_eq_mul]
        congr 1
        show _ = partialDeriv p.snd (fun x => r (x - y)) x
        rw [h4, h3]
        simp [sub_eq_add_neg]
      rw [h2, map_smul, hL τ hτK, h1, smul_zero]
  have hI : L (∫ y, J y) = 0 := by
    rw [← ContinuousLinearMap.integral_comp_comm L hint]
    simp [hzero]
  have hjet : ∫ y, J y = jetOf ν ψ (isTestFn_of_mem ψ) := by
    funext p
    ext x
    let Λ : JetSpace N ν →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ x).comp
      (ContinuousLinearMap.proj p)
    have h1 : (∫ y, J y) p x = Λ (∫ y, J y) := rfl
    rw [h1, ← ContinuousLinearMap.integral_comp_comm Λ hint, jetOf_apply, hψ,
      partialDeriv_smoothConv (isTestFn_of_mem φ).1.continuous hr p.1 p.2, smoothConv_apply]
    rfl
  rw [← hL ψ hψK, ← hjet, hI]
theorem eq_zero_of_mollifiers {W : Opens (Coord N)} {T : Module.Dual ℂ (testFunctionSpace W)}
    (hT : ∀ K : Set (Coord N), IsCompact K → K ⊆ W → ∃ ν : ℕ, HasOrderBound T K ν)
    (hk : ∀ ε : ℝ, 0 < ε → ∃ ρ, IsAnnihilatingMollifier T ε ρ) (φ : testFunctionSpace W) :
    T φ = 0 := by
  have hφ := isTestFn_of_mem φ
  have hKφ : IsCompact (tsupport (φ : Coord N → ℂ)) := isCompact_tsupport_test φ
  obtain ⟨δ, hδ, hδW⟩ := hKφ.exists_cthickening_subset_open W.isOpen φ.2.2.2
  set K' := Metric.cthickening δ (tsupport (φ : Coord N → ℂ)) with hK'def
  have hK'c : IsCompact K' := hKφ.cthickening
  obtain ⟨ν, hb⟩ := hT K' hK'c hδW
  obtain ⟨C, hC, hbd⟩ := id hb
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun η hη => ?_)
  have hC1 : 0 < C + 1 := by linarith
  have hη' : 0 < η / (C + 1) := by positivity
  obtain ⟨δ', hδ', hm⟩ := exists_uniform_modulus hφ ν hη'
  have hε : 0 < min δ δ' := lt_min hδ hδ'
  obtain ⟨ρ, hρ⟩ := hk _ hε
  have hr := hρ.isTestFn
  set ε := min δ δ' with hεdef
  set r : Coord N → ℂ := fun x => (ρ x : ℂ) with hrdef
  have hsup : ∀ x, x ∈ Function.support (smoothConv (φ : Coord N → ℂ) r) → x ∈ K' := by
    intro x hx
    obtain ⟨a, ha, b, hb', rfl⟩ := Set.mem_add.1
      (support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ) hx)
    have hb0 : ρ b ≠ 0 := fun h0 => hb' (by simp [hrdef, h0])
    have hbs := hρ.support_subset hb0
    rw [Metric.mem_ball, dist_zero_right] at hbs
    refine Metric.closedBall_subset_cthickening (subset_tsupport _ ha) δ ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using (hbs.trans_le (min_le_left _ _)).le
  have hψK : tsupport (smoothConv (φ : Coord N → ℂ) r) ⊆ K' :=
    closure_minimal hsup hK'c.isClosed
  let ψ : testFunctionSpace W := ⟨smoothConv (φ : Coord N → ℂ) r,
    contDiff_smoothConv hφ.1.continuous hr,
    hK'c.of_isClosed_subset (isClosed_tsupport _) hψK, hψK.trans hδW⟩
  have hK' : ∀ y ∈ tsupport (φ : Coord N → ℂ), Metric.closedBall y ε ⊆ K' := fun y hy =>
    (Metric.closedBall_subset_cthickening hy ε).trans
      (Metric.cthickening_mono (min_le_left _ _) _)
  have hz : T ψ = 0 := apply_smoothConv_eq_zero hρ φ hK' hδW hb ψ rfl hψK
  have hφK : tsupport (φ : Coord N → ℂ) ⊆ K' := Metric.self_subset_cthickening _
  have hDs : tsupport ((φ - ψ : testFunctionSpace W) : Coord N → ℂ) ⊆ K' := by
    refine closure_minimal ?_ hK'c.isClosed
    intro x hx
    by_contra hn
    refine hx ?_
    have h1 : (φ : Coord N → ℂ) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hn (hφK h)
    have h2 : (ψ : Coord N → ℂ) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hn (hψK h)
    show (φ : Coord N → ℂ) x - (ψ : Coord N → ℂ) x = 0
    rw [h1, h2, sub_zero]
  have hnorm : cNorm ν ((φ - ψ : testFunctionSpace W) : Coord N → ℂ) ≤ η / (C + 1) := by
    refine ciSup_le fun p => ?_
    refine ciSup_le fun x => ?_
    have h1 : ((φ - ψ : testFunctionSpace W) : Coord N → ℂ) = (φ : Coord N → ℂ) - smoothConv φ r :=
      rfl
    have h2 : partialDeriv p.2 (smoothConv (φ : Coord N → ℂ) r) =
        smoothConv r (partialDeriv p.2 (φ : Coord N → ℂ)) := by
      rw [smoothConv_comm, partialDeriv_smoothConv hr.1.continuous hφ]
    rw [h1, partialDeriv_sub _ hφ.1 (contDiff_smoothConv hφ.1.continuous hr), h2, Pi.sub_apply,
      ← dist_eq_norm, dist_comm]
    refine dist_smoothConv_le (hφ.partialDeriv p.2).1.continuous hη'.le hρ.support_subset
      hρ.nonneg hρ.integral_eq_one
      (fun x x' hx => (hm p x x' (hx.trans_le (min_le_right _ _))).le) x
  have hT1 : T φ = T (φ - ψ) := by rw [map_sub, hz, sub_zero]
  rw [hT1]
  refine (hbd _ hDs).trans ?_
  calc C * cNorm ν ((φ - ψ : testFunctionSpace W) : Coord N → ℂ) ≤ C * (η / (C + 1)) :=
        mul_le_mul_of_nonneg_left hnorm hC
    _ ≤ 0 + η := by
        rw [zero_add, mul_div_assoc', div_le_iff₀ hC1]
        nlinarith
end Annihilation
section Blocks
variable {r : ℕ} {n : Fin r → ℕ}
def assemble (g : ∀ i, Coord (n i)) : Coord (∑ i, n i) :=
  fun c => g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
theorem assemble_apply (g : ∀ i, Coord (n i)) (i : Fin r) (a : Fin (n i)) :
    assemble g (finSigmaFinEquiv ⟨i, a⟩) = g i a := by
  show (fun s : Σ i, Fin (n i) => g s.1 s.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, a⟩)) = _
  rw [Equiv.symm_apply_apply]
@[simp] theorem blockComponent_assemble (g : ∀ i, Coord (n i)) (i : Fin r) :
    blockComponent n (assemble g) i = g i := by
  funext a
  exact assemble_apply g i a
theorem assemble_blockComponent (x : Coord (∑ i, n i)) :
    assemble (fun i => blockComponent n x i) = x := by
  funext c
  simp [blockComponent, assemble]
theorem continuous_assemble : Continuous (assemble (n := n)) := by
  refine continuous_pi fun c => ?_
  exact (continuous_apply _).comp (continuous_apply _)
theorem contDiff_blockComponent (i : Fin r) : ContDiff ℝ ∞ fun x => blockComponent n x i :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
theorem norm_apply_le_norm_blockComponent (x : Coord (∑ i, n i)) (i : Fin r) (a : Fin (n i)) :
    ‖x (finSigmaFinEquiv ⟨i, a⟩)‖ ≤ ‖blockComponent n x i‖ :=
  norm_le_pi_norm (blockComponent n x i) a
theorem tensorFn_mem {U : ∀ i, Opens (Coord (n i))} (φ : ∀ i, testFunctionSpace (U i)) :
    tensorFn n (fun i => (φ i : Coord (n i) → ℂ)) ∈
      testFunctionSpace (prodOpens n U) := by
  set S : Set (Coord (∑ i, n i)) :=
    assemble '' Set.pi Set.univ fun i => tsupport (φ i : Coord (n i) → ℂ) with hS
  have hSc : IsCompact S :=
    (isCompact_univ_pi fun i => (φ i).2.2.1).image continuous_assemble
  have hsub : tsupport (tensorFn n fun i => (φ i : Coord (n i) → ℂ)) ⊆ S := by
    refine closure_minimal ?_ hSc.isClosed
    intro x hx
    have h1 : ∀ i, (φ i : Coord (n i) → ℂ) (blockComponent n x i) ≠ 0 := by
      intro i
      have h2 : ∏ i, (φ i : Coord (n i) → ℂ) (blockComponent n x i) ≠ 0 := hx
      exact Finset.prod_ne_zero_iff.1 h2 i (Finset.mem_univ i)
    exact ⟨fun i => blockComponent n x i, fun i _ => subset_tsupport _ (h1 i),
      assemble_blockComponent x⟩
  refine ⟨?_, hSc.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans ?_⟩
  · exact contDiff_prod fun i _ => (φ i).2.1.comp (contDiff_blockComponent i)
  · rintro _ ⟨g, hg, rfl⟩
    show ∀ i, blockComponent n (assemble g) i ∈ U i
    intro i
    rw [blockComponent_assemble]
    exact (φ i).2.2.2 (hg i (Set.mem_univ i))
end Blocks
section ProductMollifiers
variable {r : ℕ} {n : Fin r → ℕ}
def ballBump (m : ℕ) {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : Coord m) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩
def blockBump (n : Fin r → ℕ) {ε : ℝ} (hε : 0 < ε) : Coord (∑ i, n i) → ℝ :=
  fun x => ∏ i, ballBump (n i) hε (blockComponent n x i)
theorem norm_blockComponent_lt_of_blockBump_ne_zero {ε : ℝ} (hε : 0 < ε) {x : Coord (∑ i, n i)}
    (hx : blockBump n hε x ≠ 0) (i : Fin r) :
    ‖blockComponent n x i‖ < ε := by
  have h1 := Finset.prod_ne_zero_iff.1 hx i (Finset.mem_univ i)
  have h2 : blockComponent n x i ∈ Function.support (ballBump (n i) hε) := h1
  rw [ContDiffBump.support_eq] at h2
  simpa [ballBump] using h2
theorem support_blockBump_subset {ε : ℝ} (hε : 0 < ε) :
    Function.support (blockBump n hε) ⊆ Metric.ball 0 ε := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε]
  intro c
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective c
  exact (norm_apply_le_norm_blockComponent x i a).trans_lt
    (norm_blockComponent_lt_of_blockBump_ne_zero hε hx i)
theorem contDiff_blockBump {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (blockBump n hε) :=
  contDiff_prod fun i _ => (ballBump (n i) hε).contDiff.comp (contDiff_blockComponent i)
theorem hasCompactSupport_blockBump {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (blockBump n hε) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Coord (∑ i, n i)) ε) ?_
  exact (support_blockBump_subset hε).trans Metric.ball_subset_closedBall
theorem blockBump_nonneg {ε : ℝ} (hε : 0 < ε) (x : Coord (∑ i, n i)) :
    0 ≤ blockBump n hε x :=
  Finset.prod_nonneg fun i _ => (ballBump (n i) hε).nonneg
theorem blockBump_zero {ε : ℝ} (hε : 0 < ε) : blockBump n hε 0 = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have h0 : blockComponent n 0 i = 0 := rfl
  rw [h0]
  exact (ballBump (n i) hε).one_of_mem_closedBall (by simp [ballBump]; positivity)
theorem integral_blockBump_pos {ε : ℝ} (hε : 0 < ε) : 0 < ∫ x, blockBump n hε x :=
  (contDiff_blockBump hε).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_blockBump hε) (blockBump_nonneg hε)
    (by rw [blockBump_zero hε]; exact one_ne_zero)
theorem closedBall_blockComponent_subset {U : ∀ i, Opens (Coord (n i))} {y : Coord (∑ i, n i)}
    {ε : ℝ} (hε : 0 < ε) (hy : Metric.closedBall y ε ⊆ prodOpens n U) (i : Fin r) :
    Metric.closedBall (blockComponent n y i) ε ⊆ U i := by
  intro w hw
  set z := assemble (Function.update (fun i => blockComponent n y i) i w) with hz
  have hzy : z ∈ Metric.closedBall y ε := by
    rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hε.le]
    intro c
    obtain ⟨⟨j, a⟩, rfl⟩ := finSigmaFinEquiv.surjective c
    by_cases hji : j = i
    · subst hji
      have h1 : z (finSigmaFinEquiv ⟨j, a⟩) = w a := by
        rw [hz, assemble_apply]
        simp
      have h2 : y (finSigmaFinEquiv ⟨j, a⟩) = blockComponent n y j a := rfl
      rw [Pi.sub_apply, h1, h2, ← Pi.sub_apply]
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      exact (norm_le_pi_norm _ a).trans hw
    · have h1 : z (finSigmaFinEquiv ⟨j, a⟩) = y (finSigmaFinEquiv ⟨j, a⟩) := by
        rw [hz, assemble_apply, Function.update_of_ne hji]
        rfl
      simp [h1, hε.le]
  have h3 : ∀ j, blockComponent n z j ∈ U j := hy hzy
  have h4 := h3 i
  rw [hz, blockComponent_assemble] at h4
  simpa using h4
theorem form_eq_of_isTensorProduct_pair {U : ∀ i, Opens (Coord (n i))}
    {u : ∀ i, Distribution (U i)} {T₁ T₂ : Distribution (prodOpens n U)}
    (h₁ : IsTensorProduct u T₁) (h₂ : IsTensorProduct u T₂)
    (φ : testFunctionSpace (prodOpens n U)) : T₁.form φ = T₂.form φ := by
  have hbound : ∀ K : Set (Coord (∑ i, n i)), IsCompact K → K ⊆ prodOpens n U →
      ∃ ν : ℕ, HasOrderBound (T₁.form - T₂.form) K ν := by
    intro K hK hKW
    obtain ⟨ν₁, C₁, hC₁, b₁⟩ := T₁.bound K hK hKW
    obtain ⟨ν₂, C₂, hC₂, b₂⟩ := T₂.bound K hK hKW
    refine ⟨max ν₁ ν₂, C₁ + C₂, add_nonneg hC₁ hC₂, fun F hF => ?_⟩
    have hF' := isTestFn_of_mem F
    have m₁ := cNorm_mono (le_max_left ν₁ ν₂) hF'
    have m₂ := cNorm_mono (le_max_right ν₁ ν₂) hF'
    have e₁ := (b₁ F hF).trans (mul_le_mul_of_nonneg_left m₁ hC₁)
    have e₂ := (b₂ F hF).trans (mul_le_mul_of_nonneg_left m₂ hC₂)
    calc ‖(T₁.form - T₂.form) F‖ ≤ ‖T₁.form F‖ + ‖T₂.form F‖ := norm_sub_le _ _
      _ ≤ (C₁ + C₂) * cNorm (max ν₁ ν₂) (F : Coord (∑ i, n i) → ℂ) := by
        rw [add_mul]
        exact add_le_add e₁ e₂
  have hkernel : ∀ ε : ℝ, 0 < ε → ∃ ρ, IsAnnihilatingMollifier (T₁.form - T₂.form) ε ρ := by
    intro ε hε
    have hI := integral_blockBump_pos (n := n) hε
    set I := ∫ x, blockBump n hε x with hIdef
    refine ⟨fun x => I⁻¹ * blockBump n hε x, ?_⟩
    refine ⟨contDiff_const.mul (contDiff_blockBump hε), ?_, ?_, ?_, ?_, ?_⟩
    · exact (hasCompactSupport_blockBump hε).mul_left
    · exact fun x => mul_nonneg (inv_nonneg.2 hI.le) (blockBump_nonneg hε x)
    · rw [integral_const_mul, ← hIdef, inv_mul_cancel₀ hI.ne']
    · refine Set.Subset.trans ?_ (support_blockBump_subset hε)
      intro x hx hx0
      exact hx (by simp [hx0])
    · intro y hy F hF
      let f : ∀ i, Coord (n i) → ℂ :=
        fun i w => (ballBump (n i) hε (w - blockComponent n y i) : ℂ)
      have hfc : ∀ i, ContDiff ℝ ∞ (f i) := fun i =>
        Complex.ofRealCLM.contDiff.comp ((ballBump (n i) hε).contDiff.comp (by fun_prop))
      have hfs : ∀ i, tsupport (f i) ⊆ Metric.closedBall (blockComponent n y i) ε := by
        intro i
        refine closure_minimal ?_ Metric.isClosed_closedBall
        intro w hw
        have h1 : w - blockComponent n y i ∈ Function.support (ballBump (n i) hε) := by
          intro h0
          exact hw (by simp [f, h0])
        rw [ContDiffBump.support_eq] at h1
        have h2 : ‖w - blockComponent n y i‖ < ε := by simpa [ballBump] using h1
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact h2.le
      let g : ∀ i, testFunctionSpace (U i) := fun i =>
        ⟨f i, hfc i, (isCompact_closedBall _ ε).of_isClosed_subset (isClosed_tsupport _) (hfs i),
          (hfs i).trans (closedBall_blockComponent_subset hε hy i)⟩
      obtain ⟨m₁, v₁⟩ := h₁ g
      obtain ⟨m₂, v₂⟩ := h₂ g
      have hFe : F = ((I⁻¹ : ℝ) : ℂ) • (⟨_, m₁⟩ : testFunctionSpace (prodOpens n U)) := by
        refine Subtype.ext (funext fun x => ?_)
        rw [hF x]
        show _ = ((I⁻¹ : ℝ) : ℂ) * ∏ i, f i (blockComponent n x i)
        have h3 : ∀ i, blockComponent n (x - y) i = blockComponent n x i - blockComponent n y i :=
          fun i => rfl
        simp [blockBump, f, h3]
      have hm : (⟨_, m₁⟩ : testFunctionSpace (prodOpens n U)) = ⟨_, m₂⟩ := rfl
      rw [hFe, map_smul, LinearMap.sub_apply, v₁, hm, v₂, sub_self, smul_zero]
  have h := eq_zero_of_mollifiers hbound hkernel φ
  rwa [LinearMap.sub_apply, sub_eq_zero] at h
theorem eq_of_isTensorProduct_pair {U : ∀ i, Opens (Coord (n i))}
    {u : ∀ i, Distribution (U i)} {T₁ T₂ : Distribution (prodOpens n U)}
    (h₁ : IsTensorProduct u T₁) (h₂ : IsTensorProduct u T₂) : T₁ = T₂ := by
  have h : T₁.form = T₂.form := LinearMap.ext (form_eq_of_isTensorProduct_pair h₁ h₂)
  cases T₁
  cases T₂
  simp only [Distribution.mk.injEq]
  exact h
end ProductMollifiers
section Induction
def sigmaSplitLast {r : ℕ} (n : Fin (r + 1) → ℕ) :
    (Σ i : Fin r, Fin (n i.castSucc)) ⊕ Fin (n (Fin.last r)) ≃ Σ i, Fin (n i) :=
  Equiv.ofBijective
    (Sum.elim (fun s => ⟨s.1.castSucc, s.2⟩) (fun c => ⟨Fin.last r, c⟩)) (by
      constructor
      · rintro (⟨i, a⟩ | c) (⟨j, b⟩ | d) h
        · simp only [Sum.elim_inl, Sigma.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          have h3 : i = j := Fin.castSucc_injective _ h1
          subst h3
          simpa using h2
        · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.injEq] at h
          exact absurd h.1 (Fin.castSucc_lt_last i).ne
        · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.injEq] at h
          exact absurd h.1.symm (Fin.castSucc_lt_last j).ne
        · simp only [Sum.elim_inr, Sigma.mk.injEq, heq_eq_eq, true_and] at h
          rw [h]
      · rintro ⟨i, a⟩
        induction i using Fin.lastCases with
        | last => exact ⟨Sum.inr a, rfl⟩
        | cast i => exact ⟨Sum.inl ⟨i, a⟩, rfl⟩)
def finSplitLast {r : ℕ} (n : Fin (r + 1) → ℕ) :
    Fin (∑ i : Fin r, n i.castSucc) ⊕ Fin (n (Fin.last r)) ≃ Fin (∑ i, n i) :=
  (Equiv.sumCongr finSigmaFinEquiv.symm (Equiv.refl _)).trans
    ((sigmaSplitLast n).trans finSigmaFinEquiv)
theorem blockComponent_projFst {r : ℕ} (n : Fin (r + 1) → ℕ) (z : Coord (∑ i, n i)) (i : Fin r) :
    blockComponent (fun i : Fin r => n i.castSucc) (projFst (finSplitLast n) z) i =
      blockComponent n z i.castSucc := by
  funext a
  simp [blockComponent, projFst, finSplitLast, sigmaSplitLast]
  rfl
theorem projSnd_eq_blockComponent_last {r : ℕ} (n : Fin (r + 1) → ℕ) (z : Coord (∑ i, n i)) :
    projSnd (finSplitLast n) z = blockComponent n z (Fin.last r) := by
  funext a
  simp [blockComponent, projSnd, finSplitLast, sigmaSplitLast]
  rfl
theorem mem_prodOpens_iff_split {r : ℕ} (n : Fin (r + 1) → ℕ) (U : ∀ i, Opens (Coord (n i)))
    (z : Coord (∑ i, n i)) :
    z ∈ prodOpens n U ↔
      projFst (finSplitLast n) z ∈
          prodOpens (fun i : Fin r => n i.castSucc) (fun i => U i.castSucc) ∧
        projSnd (finSplitLast n) z ∈ U (Fin.last r) := by
  show (∀ i, blockComponent n z i ∈ U i) ↔
    (∀ i : Fin r, blockComponent _ (projFst (finSplitLast n) z) i ∈ U i.castSucc) ∧ _
  rw [Fin.forall_iff_castSucc, projSnd_eq_blockComponent_last]
  simp only [blockComponent_projFst]
  tauto
def evalAtZero {n : Fin 0 → ℕ} (U : ∀ i, Opens (Coord (n i))) :
    Distribution (prodOpens n U) where
  form :=
    { toFun := fun F => (F : Coord (∑ i, n i) → ℂ) 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  bound K _ _ := by
    refine ⟨0, 1, zero_le_one, fun F _ => ?_⟩
    have h := norm_partialDeriv_le_cNorm (isTestFn_of_mem F) (le_refl 0) Fin.elim0 0
    rw [partialDeriv_zero] at h
    simpa using h
theorem exists_isTensorProduct_of_factors : ∀ (r : ℕ) (n : Fin r → ℕ) (U : ∀ i, Opens (Coord (n i)))
    (u : ∀ i, Distribution (U i)), ∃ T, IsTensorProduct u T := by
  intro r
  induction r with
  | zero =>
    intro n U u
    refine ⟨evalAtZero U, fun φ => ⟨tensorFn_mem φ, ?_⟩⟩
    simp [evalAtZero, tensorFn]
  | succ r ih =>
    intro n U u
    obtain ⟨T', hT'⟩ := ih (fun i => n i.castSucc) (fun i => U i.castSucc)
      (fun i => u i.castSucc)
    refine ⟨iteratedPairing (finSplitLast n) (mem_prodOpens_iff_split n U) T' (u (Fin.last r)),
      fun φ => ⟨tensorFn_mem φ, ?_⟩⟩
    obtain ⟨m, hm⟩ := hT' (fun i => φ i.castSucc)
    rw [iteratedPairing_apply_of_product (finSplitLast n) (mem_prodOpens_iff_split n U) T'
      (u (Fin.last r)) ⟨_, m⟩ (φ (Fin.last r)) ⟨_, tensorFn_mem φ⟩, hm, Fin.prod_univ_castSucc]
    intro z
    show ∏ i, (φ i : Coord (n i) → ℂ) (blockComponent n z i) =
      (∏ i : Fin r, (φ i.castSucc : Coord (n i.castSucc) → ℂ)
        (blockComponent _ (projFst (finSplitLast n) z) i)) * _
    rw [Fin.prod_univ_castSucc, projSnd_eq_blockComponent_last]
    simp only [blockComponent_projFst]
end Induction
theorem tensorProductExistsUnique_holds : TensorProductExistsUnique := by
  intro r _ n _ U u
  have hex := exists_isTensorProduct_of_factors r n U u
  have hspec : IsTensorProduct u (tensorDist u) := by
    have := distribution_nonempty (prodOpens n U)
    exact Classical.epsilon_spec hex
  exact ⟨hspec, fun T hT => eq_of_isTensorProduct_pair hT hspec⟩
end YangMills.Construction.Continuum.TensorProduct.Construct
