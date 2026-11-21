import YangMills.Construction.ClusterExpansionOfAStep.CutOnTheQuaternions
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSumsWithMomentsProofForm
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongParametersOfAFamilyProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaleDerivatives
open Set Filter Topology MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.DensityMeans YangMills.Construction.Cumulants
section
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem iteratedFDeriv_succ_cons_apply {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x)
    (a : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons a u) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n f y u) x a := by apply _root_.YangMills.Construction.ParameterListDerivatives.iteratedFDeriv_succ_cons_eq_fderiv <;> assumption
theorem contDiffAt_iteratedFDeriv_apply {n m i : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ n f x)
    (hmn : m + i ≤ n) (u : Fin i → E) :
    ContDiffAt ℝ m (fun y => iteratedFDeriv ℝ i f y u) x := by apply _root_.YangMills.Construction.ParameterListDerivatives.contDiffAt_iteratedFDeriv_eval <;> assumption
theorem iteratedFDeriv_comp_add_const_apply {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (a : E) {x : G}
    (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) (v : Fin i → G) :
    iteratedFDeriv ℝ i (fun z => f (L z + a)) x v = iteratedFDeriv ℝ i f (L x + a) fun j => L (v j) := by apply _root_.YangMills.SharedProofs.p13665 <;> assumption
end
section
variable {E₁ E₂ H : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup H] [NormedSpace ℝ H]
def partialJetSnd (f : E₁ × E₂ → H) (y : E₂) {k : ℕ} (w : Fin k → E₂) (x : E₁) : H :=
  iteratedFDeriv ℝ k (fun y' => f (x, y')) y w
theorem partialJetSnd_eq {n k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y))
    (hk : k ≤ n) (w : Fin k → E₂) :
    partialJetSnd f y w x = iteratedFDeriv ℝ k f (x, y) fun j => (0, w j) := by
  have h := iteratedFDeriv_comp_add_const_apply (ContinuousLinearMap.inr ℝ E₁ E₂) (x, 0) (x := y) (f := f)
    (by simpa using hf) hk w
  have e1 : (fun z => f ((ContinuousLinearMap.inr ℝ E₁ E₂) z + (x, 0))) = fun y' => f (x, y') := by
    funext z; simp
  rw [e1] at h
  simp only [partialJetSnd]
  rw [h]
  simp
theorem eventually_contDiffAt_fst {n : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y)) :
    ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ n f (x', y) := by apply _root_.YangMills.Construction.ParameterListDerivatives.eventually_contDiffAt_left <;> assumption
theorem contDiffAt_partialJetSnd {n m k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + k ≤ n) (w : Fin k → E₂) :
    ContDiffAt ℝ m (partialJetSnd f y w) x := by
  have h1 : ContDiffAt ℝ m (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) (x, y) :=
    contDiffAt_iteratedFDeriv_apply hf hmn _
  have h2 : ContDiffAt ℝ m (fun x' : E₁ => (x', y)) x := by fun_prop
  have h3 : ContDiffAt ℝ m (fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j)) x :=
    ContDiffAt.comp x (g := fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) h1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [eventually_contDiffAt_fst hf] with x' hx'
  exact partialJetSnd_eq hx' (by omega) w
def IsSplitTuple {m p k : ℕ} (v : Fin p → E₁) (w : Fin k → E₂) (u : Fin m → E₁ × E₂) : Prop :=
  m = p + k ∧ (∀ (i : Fin m) (hi : i.val < p), u i = (v ⟨i.val, hi⟩, 0)) ∧
    ∀ (i : Fin m) (hi : p ≤ i.val) (hk : i.val - p < k), u i = (0, w ⟨i.val - p, hk⟩)
theorem iteratedFDeriv_partialJetSnd {k : ℕ} (w : Fin k → E₂) {n : ℕ} {f : E₁ × E₂ → H} {y : E₂} :
    ∀ (p m : ℕ) (v : Fin p → E₁) (u : Fin m → E₁ × E₂) (x : E₁), IsSplitTuple v w u →
      ContDiffAt ℝ n f (x, y) → m ≤ n →
      iteratedFDeriv ℝ p (partialJetSnd f y w) x v = iteratedFDeriv ℝ m f (x, y) u := by
  intro p
  induction p with
  | zero =>
    intro m v u x hu hf hm
    obtain ⟨h0, -, h2⟩ := hu
    have : m = k := by omega
    subst this
    have hu' : u = fun j => (0, w j) := by
      funext j
      have := h2 j (Nat.zero_le _) (by simpa using j.2)
      simpa using this
    rw [hu', ← partialJetSnd_eq hf hm w]
    simp
  | succ p ih =>
    intro m v u x hu hf hm
    obtain ⟨h0, h1, h2⟩ := hu
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hR : ContDiffAt ℝ (p + 1 : ℕ) (partialJetSnd f y w) x :=
      contDiffAt_partialJetSnd hf (by omega) w
    have hf' : ContDiffAt ℝ (m' + 1 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hm)
    have hu0 : u 0 = (v 0, 0) := h1 0 (by simp)
    have ht : IsSplitTuple (Fin.tail v) w (Fin.tail u) := by
      refine ⟨by omega, fun i hi => ?_, fun i hi hk => ?_⟩
      · have := h1 i.succ (by simpa using hi)
        simpa [Fin.tail_def] using this
      · have := h2 i.succ (by simp; omega) (by simp; omega)
        simp only [Fin.tail_def]
        rw [this]
        congr 2
        apply Fin.ext
        simp
    have e1 := iteratedFDeriv_succ_cons_apply hR (v 0) (Fin.tail v)
    have e2 := iteratedFDeriv_succ_cons_apply hf' (u 0) (Fin.tail u)
    rw [Fin.cons_self_tail] at e1 e2
    rw [e1, e2]
    have hev : (fun x' => iteratedFDeriv ℝ p (partialJetSnd f y w) x' (Fin.tail v)) =ᶠ[𝓝 x]
        fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u) := by
      filter_upwards [eventually_contDiffAt_fst hf] with x' hx'
      exact ih m' _ _ x' ht hx' (by omega)
    rw [hev.fderiv_eq, hu0]
    have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) (x, y) :=
      (contDiffAt_iteratedFDeriv_apply (m := 1) hf (by omega) _).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun x' : E₁ => (x', y)) (ContinuousLinearMap.inl ℝ E₁ E₂) x :=
      hasFDerivAt_prodMk_left x y
    have := (hd.hasFDerivAt.comp x hc).fderiv
    have e3 : (fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u)) =
      (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) ∘ fun x' : E₁ => (x', y) := rfl
    rw [e3, this]
    simp
end
theorem exists_uniform_jet_bound {n : ℕ} {k : ℕ} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (G : (Fin k → ℝ) × Q → ℝ) (K : Set Q) (hK : IsCompact K) (hG : ∀ η ∈ K, ContDiffAt ℝ n G (0, η)) :
    ∃ r M : ℝ, 0 < r ∧
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ContinuousOn (fun η => G (τ, η)) K) ∧
      ∀ η ∈ K, ContDiffOn ℝ n (fun τ => G (τ, η)) (Metric.ball 0 r) ∧
        ∀ j, j ≤ n → ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
          ‖iteratedFDeriv ℝ j (fun τ => G (τ, η)) τ‖ ≤ M := by
  set U : Set ((Fin k → ℝ) × Q) := {z | ContDiffAt ℝ n G z} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (show ContDiffAt ℝ n G z from hz).eventually (by simp)
  have hGU : ContDiffOn ℝ n G U := fun z hz => (show ContDiffAt ℝ n G z from hz).contDiffWithinAt
  have hsub : ({0} : Set (Fin k → ℝ)) ×ˢ K ⊆ U := by
    rintro ⟨t, η⟩ ⟨ht, hη⟩
    obtain rfl : t = 0 := ht
    exact hG η hη
  obtain ⟨u, v, hu, hv, h0u, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hUo hsub
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hu 0 (h0u rfl)
  set r : ℝ := r₀ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hcb : Metric.closedBall (0 : Fin k → ℝ) r ⊆ u := fun z hz =>
    hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by rw [hr]; linarith))
  have hC : IsCompact (Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K) :=
    (isCompact_closedBall _ _).prod hK
  have hCU : Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K ⊆ U := fun z hz =>
    huv ⟨hcb hz.1, hKv hz.2⟩
  have hbd : ∀ j, j ≤ n → ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K,
      ‖iteratedFDeriv ℝ j G z‖ ≤ M := fun j hj => by
    have hc : ContinuousOn (iteratedFDeriv ℝ j G) U :=
      (hGU.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
        hUo.uniqueDiffOn).congr (fun z hz => (iteratedFDerivWithin_of_isOpen j hUo hz).symm)
    exact hC.exists_bound_of_continuousOn (hc.mono hCU)
  choose! Mj hMj using hbd
  refine ⟨r, ∑ j ∈ Finset.range (n + 1), |Mj j|, hrpos, fun τ hτ η hη => ?_, fun η hη => ?_⟩
  · have hz : (τ, η) ∈ U := hCU ⟨Metric.ball_subset_closedBall hτ, hη⟩
    have hc : ContinuousAt G (τ, η) := (show ContDiffAt ℝ n G (τ, η) from hz).continuousAt
    have h2 : ContinuousAt (fun η' : Q => (τ, η')) η := by fun_prop
    exact (ContinuousAt.comp (f := fun η' : Q => (τ, η')) hc h2).continuousWithinAt
  set ι : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) × Q := ContinuousLinearMap.inl ℝ _ _ with hι
  set f : (Fin k → ℝ) × Q → ℝ := fun z => G (z + (0, η)) with hf
  set s : Set ((Fin k → ℝ) × Q) := (fun z => z + ((0 : Fin k → ℝ), η)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_add_const _)
  have hfs : ContDiffOn ℝ n f s :=
    hGU.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  have hslice : (fun τ => G (τ, η)) = f ∘ ι := by
    funext τ
    simp [hf, hι]
  have hiota : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ι τ ∈ s := fun τ hτ => by
    have : (τ, η) ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K :=
      ⟨Metric.ball_subset_closedBall hτ, hη⟩
    have h2 := hCU this
    simpa [hs, hι] using h2
  constructor
  · rw [hslice]
    exact hfs.comp ι.contDiff.contDiffOn hiota
  · intro j hj τ hτ
    have hcomp := ι.iteratedFDerivWithin_comp_right hfs hso.uniqueDiffOn
      (hso.preimage ι.continuous).uniqueDiffOn (hiota τ hτ) (i := j) (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen j (hso.preimage ι.continuous) (hiota τ hτ),
      iteratedFDerivWithin_of_isOpen j hso (hiota τ hτ)] at hcomp
    rw [hslice, hcomp]
    have hadd : iteratedFDeriv ℝ j f (ι τ) = iteratedFDeriv ℝ j G (ι τ + (0, η)) := by
      rw [hf]
      exact iteratedFDeriv_comp_add_right j (0, η) (ι τ)
    have hmem : ι τ + ((0 : Fin k → ℝ), η) ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K := by
      simpa [hι] using (⟨Metric.ball_subset_closedBall hτ, hη⟩ :
        (τ, η) ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K)
    have hnorm : ‖ι‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ _ _
    have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j f (ι τ)) (fun _ => ι)
    have hprod : ∏ _i : Fin j, ‖ι‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hnorm)
    calc ‖(iteratedFDeriv ℝ j f (ι τ)).compContinuousLinearMap fun _ => ι‖
        ≤ ‖iteratedFDeriv ℝ j f (ι τ)‖ * ∏ _i : Fin j, ‖ι‖ := h3
      _ ≤ ‖iteratedFDeriv ℝ j f (ι τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ j G (ι τ + (0, η))‖ := by rw [mul_one, hadd]
      _ ≤ Mj j := hMj j hj _ hmem
      _ ≤ |Mj j| := le_abs_self _
      _ ≤ ∑ j ∈ Finset.range (n + 1), |Mj j| :=
        Finset.single_le_sum (f := fun j => |Mj j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
def pureQuaternionEmbedding : BondVector →L[ℝ] Quaternion ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (⟨0, v 0, v 1, v 2⟩ : Quaternion ℝ)
      map_add' := by
        intro a b
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · show (0 : ℝ) = 0 + 0
          simp
        · show (a + b) 0 = a 0 + b 0
          simp
        · show (a + b) 1 = a 1 + b 1
          simp
        · show (a + b) 2 = a 2 + b 2
          simp
      map_smul' := by
        intro c a
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · show (0 : ℝ) = c * 0
          simp
        · show (c • a) 0 = c * a 0
          simp
        · show (c • a) 1 = c * a 1
          simp
        · show (c • a) 2 = c * a 2
          simp }
theorem pureQuaternionEmbedding_apply (v : BondVector) :
    pureQuaternionEmbedding v = (⟨0, v 0, v 1, v 2⟩ : Quaternion ℝ) := rfl
theorem norm_pureQuaternionEmbedding (v : BondVector) : ‖pureQuaternionEmbedding v‖ = ‖v‖ := by
  have h1 : ‖pureQuaternionEmbedding v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def',
      pureQuaternionEmbedding_apply]
    simp [Fin.sum_univ_three]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
theorem contDiff_cutoffFactor_norm (hQ : QuaternionCutoffSmoothBounded) {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : BondVector => cutoffFactor ρ p ‖v‖) := by
  have h1 := (hQ ρ p hρ hp).1
  have h2 : (fun v : BondVector => cutoffFactor ρ p ‖v‖) =
      (fun v : Quaternion ℝ => cutoffFactor ρ p ‖v‖) ∘ pureQuaternionEmbedding := by
    funext v
    simp [norm_pureQuaternionEmbedding]
  rw [h2]
  exact h1.comp pureQuaternionEmbedding.contDiff
theorem iteratedFDeriv_cutoffFactor_norm_eq_zero (hQ : QuaternionCutoffSmoothBounded) {ρ : ℝ} {p : ℝ → ℝ}
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) (j : ℕ) {v : BondVector} (hv : ρ ≤ ‖v‖) :
    iteratedFDeriv ℝ j (fun v : BondVector => cutoffFactor ρ p ‖v‖) v = 0 := by
  have hs := contDiff_cutoffFactor_norm hQ hρ hp
  have hc : Continuous (iteratedFDeriv ℝ j (fun v : BondVector => cutoffFactor ρ p ‖v‖)) :=
    hs.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  have hz : ∀ w : BondVector, ρ < ‖w‖ →
      iteratedFDeriv ℝ j (fun v : BondVector => cutoffFactor ρ p ‖v‖) w = 0 := by
    intro w hw
    have hev : (fun v : BondVector => cutoffFactor ρ p ‖v‖) =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      have : {v : BondVector | ρ < ‖v‖} ∈ 𝓝 w := (isOpen_lt continuous_const continuous_norm).mem_nhds hw
      filter_upwards [this] with z hz
      have h1 : ¬ ‖z‖ < ρ := not_lt.mpr (le_of_lt hz)
      simp [cutoffFactor, h1]
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
    simp
  have hcl : IsClosed {t : ℝ | iteratedFDeriv ℝ j (fun v : BondVector => cutoffFactor ρ p ‖v‖) (t • v) = 0} :=
    isClosed_eq (hc.comp (continuous_id.smul continuous_const)) continuous_const
  have hsub : Set.Ioi (1 : ℝ) ⊆
      {t : ℝ | iteratedFDeriv ℝ j (fun v : BondVector => cutoffFactor ρ p ‖v‖) (t • v) = 0} := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    apply hz
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    nlinarith
  have h1 := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioi] at h1
  have := h1 (Set.self_mem_Ici)
  simpa using this
variable {ι : Type} [Fintype ι] {k : ℕ}
def scaleTopCLM (i k : ℕ) : (Fin (i + k) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ a : Fin i, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (i + k) => ℝ) (Fin.castAdd k a))
    (ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (Fin.natAdd i b))
theorem scaleTopCLM_apply (i k : ℕ) (τ : Fin (i + k) → ℝ) : scaleTopCLM i k τ = scaleTopSplit i k τ := by
  simp [scaleTopCLM, scaleTopSplit]
theorem scaleTopCLM_single_of_lt (i k : ℕ) (a : Fin (i + k)) (h : (a : ℕ) < i) :
    scaleTopCLM i k (Pi.single a 1) = (1, 0) := by
  rw [scaleTopCLM_apply]
  have ha : a = Fin.castAdd k ⟨a, h⟩ := by ext; simp
  refine Prod.ext ?_ ?_
  · show ∑ a' : Fin i, (Pi.single a 1 : Fin (i + k) → ℝ) (Fin.castAdd k a') = 1
    rw [Finset.sum_eq_single (⟨a, h⟩ : Fin i)]
    · rw [← ha]; simp
    · intro b _ hb
      rw [Pi.single_apply, if_neg]
      intro hc
      apply hb
      rw [ha] at hc
      exact Fin.castAdd_injective _ _ hc
    · simp
  · funext b
    show (Pi.single a 1 : Fin (i + k) → ℝ) (Fin.natAdd i b) = 0
    rw [Pi.single_apply, if_neg]
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
theorem scaleTopCLM_single_of_le (i k : ℕ) (a : Fin (i + k)) (h : i ≤ (a : ℕ)) (hk : (a : ℕ) - i < k) :
    scaleTopCLM i k (Pi.single a 1) = (0, Pi.single ⟨(a : ℕ) - i, hk⟩ 1) := by
  rw [scaleTopCLM_apply]
  refine Prod.ext ?_ ?_
  · show ∑ a' : Fin i, (Pi.single a 1 : Fin (i + k) → ℝ) (Fin.castAdd k a') = 0
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Pi.single_apply, if_neg]
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  · funext b
    show (Pi.single a 1 : Fin (i + k) → ℝ) (Fin.natAdd i b) = (Pi.single ⟨(a : ℕ) - i, hk⟩ 1 : Fin k → ℝ) b
    by_cases hb : b = ⟨(a : ℕ) - i, hk⟩
    · subst hb
      have : Fin.natAdd i (⟨(a : ℕ) - i, hk⟩ : Fin k) = a := by
        ext
        simp
        omega
      simp [this]
    · rw [Pi.single_apply, if_neg, Pi.single_apply, if_neg hb]
      intro hc
      apply hb
      ext
      have := congrArg Fin.val hc
      simp at this
      simp
      omega
def polyBall (ι : Type) (R : ℝ) : Set (BondField ι) := {ζ | ∀ b, ‖ζ b‖ ≤ R}
theorem isCompact_polyBall (R : ℝ) : IsCompact (polyBall ι R) := by
  have : polyBall ι R = Set.pi Set.univ fun _ => Metric.closedBall 0 R := by
    ext η
    simp [polyBall]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
theorem exists_polyBall_subset {R₀ : ℝ} (hR : 0 < R₀) (W : Set (BondField ι))
    (hW : ∀ ζ ∈ polyBall ι R₀, W ∈ 𝓝 ζ) :
    ∃ R₁ : ℝ, R₀ < R₁ ∧ polyBall ι R₁ ⊆ W := by
  have hK : IsCompact (polyBall ι R₀) := isCompact_polyBall R₀
  have hsub : polyBall ι R₀ ⊆ interior W := fun ζ hζ => mem_interior_iff_mem_nhds.mpr (hW ζ hζ)
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open isOpen_interior hsub
  refine ⟨R₀ + δ / 2, by linarith, fun ζ hζ => interior_subset (hth ?_)⟩
  set R₁ := R₀ + δ / 2 with hR₁
  have hR₁p : 0 < R₁ := by positivity
  rw [Metric.mem_thickening_iff]
  refine ⟨(R₀ / R₁) • ζ, fun b => ?_, ?_⟩
  · show ‖((R₀ / R₁) • ζ) b‖ ≤ R₀
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc R₀ / R₁ * ‖ζ b‖ ≤ R₀ / R₁ * R₁ := by gcongr; exact hζ b
      _ = R₀ := by field_simp
  · rw [dist_eq_norm]
    have h1 : ‖ζ - (R₀ / R₁) • ζ‖ ≤ δ / 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b => ?_
      have e : (ζ - (R₀ / R₁) • ζ) b = (1 - R₀ / R₁) • ζ b := by
        simp [sub_smul]
      rw [e, norm_smul, Real.norm_of_nonneg]
      · have h0 : 0 ≤ 1 - R₀ / R₁ := by
          rw [sub_nonneg, div_le_one hR₁p]
          linarith
        calc (1 - R₀ / R₁) * ‖ζ b‖ ≤ (1 - R₀ / R₁) * R₁ := by gcongr; exact hζ b
          _ = δ / 2 := by field_simp; rw [hR₁]; ring
      · rw [sub_nonneg, div_le_one hR₁p]
        linarith
    linarith
theorem cutoffFactor_pos_of_lt {ρ : ℝ} {p : ℝ → ℝ} {u : ℝ} (h : u < ρ) : 0 < cutoffFactor ρ p u := by
  simp [cutoffFactor, h, Real.exp_pos]
theorem cutoffFactor_nonneg_all (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem cutoffFactor_eq_zero_of_le {ρ : ℝ} {p : ℝ → ℝ} {u : ℝ} (h : ρ ≤ u) : cutoffFactor ρ p u = 0 := by
  simp [cutoffFactor, not_lt.mpr h]
theorem scaledCutoff_nonneg_all (ρ : ℝ) (p : ℝ → ℝ) (l : ℝ) (ζ : BondField ι) : 0 ≤ scaledCutoff ρ p l ζ :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg_all _ _ _
theorem scaledCutoff_pos_of_lt {ρ : ℝ} {p : ℝ → ℝ} {l : ℝ} {ζ : BondField ι} (h : ∀ b, ‖l • ζ b‖ < ρ) :
    0 < scaledCutoff ρ p l ζ :=
  Finset.prod_pos fun b _ => cutoffFactor_pos_of_lt (h b)
theorem scaledCutoff_eq_zero_of_le {ρ : ℝ} {p : ℝ → ℝ} {l : ℝ} {ζ : BondField ι} {b : ι} (h : ρ ≤ ‖l • ζ b‖) :
    scaledCutoff ρ p l ζ = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ b) (cutoffFactor_eq_zero_of_le h)
theorem contDiff_scaledCutoff (hQ : QuaternionCutoffSmoothBounded) {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × BondField ι => scaledCutoff ρ p q.1 q.2) := by
  unfold scaledCutoff
  refine contDiff_prod fun b _ => ?_
  refine (contDiff_cutoffFactor_norm hQ hρ hp).comp ?_
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × BondField ι => q.2 b) :=
    (contDiff_apply ℝ BondVector b).comp contDiff_snd
  exact contDiff_fst.smul h2
def paramLift (i : ℕ) (l : ℝ) (f : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ)
    (q : (Fin (i + k) → ℝ) × BondField ι) : ℝ :=
  shiftedAlongScale i l f q.1 q.2
theorem paramLift_contDiffAt {n : ℕ} {i : ℕ} {l : ℝ} {f : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ}
    {ζ : BondField ι} (h : ContDiffAt ℝ n f ((l, ζ), 0)) : ContDiffAt ℝ n (paramLift i l f) (0, ζ) := by
  have hm : ContDiff ℝ n (fun q : (Fin (i + k) → ℝ) × BondField ι =>
      (((l + (scaleTopCLM i k q.1).1, q.2), (scaleTopCLM i k q.1).2) : (ℝ × BondField ι) × (Fin k → ℝ))) := by
    have h1 : ContDiff ℝ n (fun q : (Fin (i + k) → ℝ) × BondField ι => scaleTopCLM i k q.1) :=
      (scaleTopCLM i k).contDiff.comp contDiff_fst
    exact ((contDiff_const.add h1.fst).prodMk contDiff_snd).prodMk h1.snd
  have e : paramLift i l f = f ∘ fun q : (Fin (i + k) → ℝ) × BondField ι =>
      (((l + (scaleTopCLM i k q.1).1, q.2), (scaleTopCLM i k q.1).2) : (ℝ × BondField ι) × (Fin k → ℝ)) := by
    funext q
    simp only [paramLift, shiftedAlongScale, Function.comp, scaleTopCLM_apply]
  rw [e]
  refine ContDiffAt.comp (0, ζ) ?_ hm.contDiffAt
  simpa using h
def paramDensity (ρ : ℝ) (p : ℝ → ℝ) (i : ℕ) (l : ℝ) (A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ)
    (q : (Fin (i + k) → ℝ) × BondField ι) : ℝ :=
  scaledCutoff ρ p (l + (scaleTopCLM i k q.1).1) q.2 * Real.exp (-paramLift i l A q)
theorem paramDensity_eq (ρ : ℝ) (p : ℝ → ℝ) (i : ℕ) (l : ℝ) (A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ)
    (τ : Fin (i + k) → ℝ) (ζ : BondField ι) :
    paramDensity ρ p i l A (τ, ζ) =
      scaledDensity ρ p A (l + (scaleTopCLM i k τ).1, (scaleTopCLM i k τ).2) ζ := by
  simp only [paramDensity, scaledDensity, paramLift, shiftedAlongScale, scaleTopCLM_apply]
theorem paramDensity_contDiffAt (hQ : QuaternionCutoffSmoothBounded) {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {n i : ℕ} {l : ℝ} {A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ} {ζ : BondField ι}
    (h : ContDiffAt ℝ n (paramLift i l A) (0, ζ)) : ContDiffAt ℝ n (paramDensity ρ p i l A) (0, ζ) := by
  have h0 : ContDiff ℝ n (fun q : ℝ × BondField ι => scaledCutoff ρ p q.1 q.2) :=
    (contDiff_scaledCutoff hQ hρ hp).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have h1 : ContDiff ℝ n (fun q : (ℝ × BondField ι) × (Fin k → ℝ) => scaledCutoff ρ p q.1.1 q.1.2) :=
    h0.comp contDiff_fst
  have h2 : ContDiffAt ℝ n
      (paramLift i l fun q : (ℝ × BondField ι) × (Fin k → ℝ) => scaledCutoff ρ p q.1.1 q.1.2) (0, ζ) :=
    paramLift_contDiffAt h1.contDiffAt
  have e : paramDensity ρ p i l A = fun q => paramLift i l (fun q : (ℝ × BondField ι) × (Fin k → ℝ) =>
      scaledCutoff ρ p q.1.1 q.1.2) q * Real.exp (-paramLift i l A q) := by
    funext q
    simp only [paramDensity, paramLift, shiftedAlongScale, scaleTopCLM_apply]
  rw [e]
  exact h2.mul (Real.contDiff_exp.contDiffAt.comp _ h.neg)
def scaleCLM (i k : ℕ) : (Fin (i + k) → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin k → ℝ)).comp (scaleTopCLM i k)
theorem scaleCLM_apply (i k : ℕ) (τ : Fin (i + k) → ℝ) : scaleCLM i k τ = (scaleTopCLM i k τ).1 := rfl
theorem iteratedFDeriv_paramDensity_eq_zero (hQ : QuaternionCutoffSmoothBounded) {ρ : ℝ} {p : ℝ → ℝ}
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) {n i : ℕ} {l r : ℝ} {A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ}
    {ζ : BondField ι} (hA : ContDiffOn ℝ n (fun τ => paramLift i l A (τ, ζ)) (Metric.ball 0 r))
    {τ : Fin (i + k) → ℝ} (hτ : τ ∈ Metric.ball (0 : Fin (i + k) → ℝ) r)
    (hz : paramDensity ρ p i l A (τ, ζ) = 0) (j : ℕ) (hj : j ≤ n) :
    iteratedFDeriv ℝ j (fun τ' => paramDensity ρ p i l A (τ', ζ)) τ = 0 := by
  classical
  have hc : scaledCutoff ρ p (l + (scaleTopCLM i k τ).1) ζ = 0 := by
    have := (mul_eq_zero.mp hz)
    rcases this with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'
  obtain ⟨b, -, hb⟩ := Finset.prod_eq_zero_iff.mp hc
  have hrim : ρ ≤ ‖(l + (scaleTopCLM i k τ).1) • ζ b‖ := by
    by_contra hlt
    exact (cutoffFactor_pos_of_lt (p := p) (not_le.mp hlt)).ne' hb
  set g : BondVector → ℝ := fun v => cutoffFactor ρ p ‖v‖ with hg
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_cutoffFactor_norm hQ hρ hp
  set L₂ : (Fin (i + k) → ℝ) →L[ℝ] BondVector := (scaleCLM i k).smulRight (ζ b) with hL₂
  set u : (Fin (i + k) → ℝ) → ℝ := fun τ' => g (L₂ τ' + l • ζ b) with hu
  set R : (Fin (i + k) → ℝ) → ℝ := fun τ' =>
    (∏ c ∈ Finset.univ.erase b, cutoffFactor ρ p ‖(l + (scaleTopCLM i k τ').1) • ζ c‖) *
      Real.exp (-paramLift i l A (τ', ζ)) with hR
  have harg : ∀ τ', L₂ τ' + l • ζ b = (l + (scaleTopCLM i k τ').1) • ζ b := by
    intro τ'
    simp only [hL₂, ContinuousLinearMap.smulRight_apply, scaleCLM_apply, add_smul]
    rw [add_comm]
  have hfun : (fun τ' => paramDensity ρ p i l A (τ', ζ)) = fun τ' => u τ' * R τ' := by
    funext τ'
    simp only [paramDensity, scaledCutoff, hu, hR, hg, harg]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
    ring
  have hus : ContDiff ℝ n u := by
    have h1 : ContDiff ℝ n g := hgs.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    exact h1.comp (L₂.contDiff.add contDiff_const)
  have hRs : ContDiffOn ℝ n R (Metric.ball 0 r) := by
    refine ContDiffOn.mul ?_ ?_
    · refine ContDiff.contDiffOn ?_
      refine contDiff_prod fun c _ => ?_
      have h1 : ContDiff ℝ n g := hgs.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      have h2 : ContDiff ℝ n (fun τ' : Fin (i + k) → ℝ => (l + (scaleTopCLM i k τ').1) • ζ c) :=
        (contDiff_const.add (contDiff_fst.comp (scaleTopCLM i k).contDiff)).smul contDiff_const
      exact h1.comp h2
    · exact Real.contDiff_exp.comp_contDiffOn hA.neg
  have hzero : ∀ m : ℕ, iteratedFDeriv ℝ m u τ = 0 := by
    intro m
    ext v
    have h1 : ContDiffAt ℝ m g (L₂ τ + l • ζ b) :=
      (hgs.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).contDiffAt
    have h2 := iteratedFDeriv_comp_add_const_apply L₂ (l • ζ b) (x := τ) h1 le_rfl v
    show iteratedFDeriv ℝ m (fun z => g (L₂ z + l • ζ b)) τ v = 0
    rw [h2]
    have h3 : iteratedFDeriv ℝ m g (L₂ τ + l • ζ b) = 0 := by
      rw [harg τ]
      exact iteratedFDeriv_cutoffFactor_norm_eq_zero hQ hρ hp m hrim
    rw [h3]
    simp
  have hB : IsOpen (Metric.ball (0 : Fin (i + k) → ℝ) r) := Metric.isOpen_ball
  have hle := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := u) (g := R) (N := n) hus.contDiffOn hRs
    hB.uniqueDiffOn hτ (n := j) (by exact_mod_cast hj)
  rw [hfun, ← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hB hτ]
  refine hle.trans (le_of_eq ?_)
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [iteratedFDerivWithin_of_isOpen m hB hτ, hzero m]
  simp
theorem log_paramDensity_eventually {ρ : ℝ} {p : ℝ → ℝ} {i : ℕ} {l : ℝ}
    {A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ} {ζ : BondField ι} (hl : 0 < l) (hζ : ∀ b, l * ‖ζ b‖ < ρ) :
    ∀ᶠ τ in 𝓝 (0 : Fin (i + k) → ℝ), Real.log (paramDensity ρ p i l A (τ, ζ)) =
      -(∑ b, p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) - paramLift i l A (τ, ζ) := by
  have hc : Continuous fun τ : Fin (i + k) → ℝ => l + (scaleTopCLM i k τ).1 :=
    continuous_const.add (continuous_fst.comp (scaleTopCLM i k).continuous)
  have h0 : ∀ᶠ τ in 𝓝 (0 : Fin (i + k) → ℝ), 0 < l + (scaleTopCLM i k τ).1 := by
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    simpa using hl
  have h1 : ∀ᶠ τ in 𝓝 (0 : Fin (i + k) → ℝ), ∀ b, (l + (scaleTopCLM i k τ).1) * ‖ζ b‖ < ρ := by
    rw [eventually_all]
    intro b
    have hc2 : Continuous fun τ : Fin (i + k) → ℝ => (l + (scaleTopCLM i k τ).1) * ‖ζ b‖ :=
      hc.mul continuous_const
    refine hc2.continuousAt.eventually (gt_mem_nhds ?_)
    simpa using hζ b
  filter_upwards [h0, h1] with τ h2 h3
  have e : paramDensity ρ p i l A (τ, ζ) =
      Real.exp (-(∑ b, p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) - paramLift i l A (τ, ζ)) := by
    simp only [paramDensity, scaledCutoff]
    rw [sub_eq_add_neg, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    have e2 : ‖(l + (scaleTopCLM i k τ).1) • ζ b‖ = (l + (scaleTopCLM i k τ).1) * ‖ζ b‖ := by
      rw [norm_smul, Real.norm_of_nonneg h2.le]
    rw [e2]
    simp [cutoffFactor, h3 b]
  rw [e, Real.log_exp]
theorem contDiffAt_comp_mul_const {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {l u : ℝ} (hl : 0 < l)
    (hu : 0 ≤ u) (h : l * u < ρ) (n : ℕ) : ContDiffAt ℝ n (fun t => p (t * u)) l := by
  rcases hu.eq_or_lt with rfl | hu
  · simp only [mul_zero]
    exact contDiffAt_const
  · have h1 : ContDiffAt ℝ n p (l * u) :=
      (hp.smooth.contDiffAt (Ico_mem_nhds (by positivity) h)).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    exact ContDiffAt.comp (g := p) l h1 (by fun_prop)
theorem iteratedDeriv_comp_mul_const {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {u : ℝ} (hu : 0 < u) :
    ∀ (m : ℕ) (t : ℝ), 0 < t → t * u < ρ →
      iteratedDeriv m (fun t => p (t * u)) t = u ^ m * iteratedDeriv m p (t * u) := by
  intro m
  induction m with
  | zero =>
    intro t _ _
    simp
  | succ m ih =>
    intro t h0 h1
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (fun t => p (t * u)) =ᶠ[𝓝 t]
        fun s => u ^ m * iteratedDeriv m p (s * u) := by
      have a0 : ∀ᶠ s in 𝓝 t, 0 < s := lt_mem_nhds h0
      have a1 : ∀ᶠ s in 𝓝 t, s * u < ρ := by
        have hc : Continuous fun s : ℝ => s * u := continuous_id.mul continuous_const
        exact hc.continuousAt.eventually (gt_mem_nhds h1)
      filter_upwards [a0, a1] with s b0 b1
      exact ih s b0 b1
    rw [hev.deriv_eq]
    have hd : ContDiffAt ℝ (m + 1 : ℕ) p (t * u) :=
      (hp.smooth.contDiffAt (Ico_mem_nhds (by positivity) h1)).of_le
        (by exact_mod_cast (le_top : ((m + 1 : ℕ) : ℕ∞) ≤ ⊤))
    have hd2 : DifferentiableAt ℝ (iteratedDeriv m p) (t * u) := by
      have h3 : DifferentiableAt ℝ (iteratedFDeriv ℝ m p) (t * u) :=
        hd.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m)
      have h4 : iteratedDeriv m p = fun x => iteratedFDeriv ℝ m p x fun _ => 1 := by
        funext x
        exact iteratedDeriv_eq_iteratedFDeriv
      rw [h4]
      exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ) ℝ fun _ => 1).differentiableAt).comp
        (t * u) h3
    have h5 : HasDerivAt (fun s : ℝ => iteratedDeriv m p (s * u))
        (deriv (iteratedDeriv m p) (t * u) * u) t := by
      have h6 : HasDerivAt (fun s : ℝ => s * u) u t := by simpa using (hasDerivAt_id t).mul_const u
      exact hd2.hasDerivAt.comp t h6
    rw [(h5.const_mul (u ^ m)).deriv, iteratedDeriv_succ]
    ring
theorem iteratedFDeriv_cutoffExponent_single {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {i : ℕ} {l u : ℝ}
    (hl : 0 < l) (hu : 0 ≤ u) (h : l * u < ρ) (J : Finset (Fin (i + k))) :
    iteratedFDeriv ℝ J.card (fun τ => p ((l + (scaleTopCLM i k τ).1) * u)) 0
        (fun j => Pi.single (J.orderEmbOfFin rfl j) 1) =
      if ∀ a ∈ J, (a : ℕ) < i then u ^ J.card * iteratedDeriv J.card p (l * u) else 0 := by
  set P : ℝ → ℝ := fun t => p (t * u) with hP
  have hsm : ContDiffAt ℝ J.card P (scaleCLM i k 0 + l) := by
    simpa using contDiffAt_comp_mul_const hp hl hu h J.card
  have h1 := iteratedFDeriv_comp_add_const_apply (scaleCLM i k) l (x := (0 : Fin (i + k) → ℝ)) hsm le_rfl
    (fun j => Pi.single (J.orderEmbOfFin rfl j) 1)
  have e1 : (fun τ => p ((l + (scaleTopCLM i k τ).1) * u)) = fun z => P (scaleCLM i k z + l) := by
    funext τ
    simp only [hP, scaleCLM_apply]
    rw [add_comm]
  rw [e1, h1]
  have e2 : scaleCLM i k 0 + l = l := by simp
  rw [e2]
  have hlow : ∀ a : Fin (i + k), (a : ℕ) < i → scaleCLM i k (Pi.single a 1) = 1 := fun a ha => by
    rw [scaleCLM_apply, scaleTopCLM_single_of_lt i k a ha]
  have hhigh : ∀ a : Fin (i + k), i ≤ (a : ℕ) → scaleCLM i k (Pi.single a 1) = 0 := fun a ha => by
    rw [scaleCLM_apply, scaleTopCLM_single_of_le i k a ha (by omega)]
  by_cases hall : ∀ a ∈ J, (a : ℕ) < i
  · rw [if_pos hall]
    have e3 : (fun j => scaleCLM i k (Pi.single (J.orderEmbOfFin rfl j) 1)) = fun _ => (1 : ℝ) := by
      funext j
      exact hlow _ (hall _ (Finset.orderEmbOfFin_mem J rfl j))
    rw [e3, ← iteratedDeriv_eq_iteratedFDeriv]
    rcases hu.eq_or_lt with rfl | hu'
    · rcases Nat.eq_zero_or_pos J.card with h0 | h0
      · rw [h0]
        simp [hP]
      · have : P = fun _ => p 0 := by
          funext t
          simp [hP]
        rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_const_of_ne h0.ne', zero_pow h0.ne',
          zero_mul]
        simp
    · exact iteratedDeriv_comp_mul_const hp hu' J.card l hl h
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨a, ha, hi⟩ := hall
    have ha' : a ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨j, rfl⟩ := ha'
    exact ContinuousMultilinearMap.map_coord_zero _ j (hhigh _ hi)
theorem mixedDerivAt_log_paramDensity {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {i : ℕ} {l : ℝ}
    {A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ} {ζ : BondField ι} (hl : 0 < l) (hζ : ∀ b, l * ‖ζ b‖ < ρ)
    (J : Finset (Fin (i + k))) (hA : ContDiffAt ℝ J.card (fun τ => paramLift i l A (τ, ζ)) 0) :
    mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ =
      -mixedDerivAt (shiftedAlongScale i l A) J ζ - ∑ b, cutoffDerivAlong i k p l J b ζ := by
  have hev := log_paramDensity_eventually (i := i) (A := A) (p := p) hl hζ
  unfold mixedDerivAt
  have e0 : (fun τ => logDensity (fun τ ζ => paramDensity ρ p i l A (τ, ζ)) τ ζ) =ᶠ[𝓝 0] fun τ =>
      -(∑ b, p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) - paramLift i l A (τ, ζ) := hev
  rw [(e0.iteratedFDeriv ℝ J.card).eq_of_nhds]
  have hP : ∀ b, ContDiffAt ℝ J.card
      (fun τ : Fin (i + k) → ℝ => p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) 0 := by
    intro b
    have h1 : ContDiffAt ℝ J.card (fun t => p (t * ‖ζ b‖)) (scaleCLM i k 0 + l) := by
      simpa using contDiffAt_comp_mul_const hp hl (norm_nonneg _) (hζ b) J.card
    have h2 : ContDiffAt ℝ J.card (fun z : Fin (i + k) → ℝ => scaleCLM i k z + l) 0 :=
      ((scaleCLM i k).contDiff.add contDiff_const).contDiffAt
    have h3 := ContDiffAt.comp (g := fun t => p (t * ‖ζ b‖)) (0 : Fin (i + k) → ℝ) h1 h2
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
    simp only [Function.comp, scaleCLM_apply]
    rw [add_comm]
  have hS : ContDiffAt ℝ J.card
      (fun τ : Fin (i + k) → ℝ => ∑ b, p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) 0 :=
    ContDiffAt.sum fun b _ => hP b
  have e1 := fun_iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := J.card) hS.neg hA
  rw [e1]
  have e2 : iteratedFDeriv ℝ J.card
        (fun τ : Fin (i + k) → ℝ => -∑ b, p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) 0 =
      -iteratedFDeriv ℝ J.card
        (fun τ : Fin (i + k) → ℝ => ∑ b, p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) 0 :=
    iteratedFDeriv_neg_apply
  rw [e2, iteratedFDeriv_fun_sum_apply fun b _ => hP b]
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.neg_apply,
    ContinuousMultilinearMap.sum_apply]
  have e3 : ∀ b, iteratedFDeriv ℝ J.card
      (fun τ : Fin (i + k) → ℝ => p ((l + (scaleTopCLM i k τ).1) * ‖ζ b‖)) 0
      (fun j => Pi.single (J.orderEmbOfFin rfl j) 1) = cutoffDerivAlong i k p l J b ζ := by
    intro b
    rw [iteratedFDeriv_cutoffExponent_single hp hl (norm_nonneg _) (hζ b) J]
    rfl
  simp only [e3]
  have e4 : iteratedFDeriv ℝ J.card (fun τ => paramLift i l A (τ, ζ)) 0
        (fun j => Pi.single (J.orderEmbOfFin rfl j) 1) =
      iteratedFDeriv ℝ J.card (fun τ => shiftedAlongScale i l A τ ζ) 0
        (fun j => Pi.single (J.orderEmbOfFin rfl j) 1) := rfl
  rw [e4]
  ring
theorem densityMean_restrict_eq {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {K : Set Ω} {Z H : Ω → ℝ}
    (hz : ∀ ζ, ζ ∉ K → Z ζ = 0) :
    densityMean (μ.restrict K) Z H = densityMean μ Z H := by
  unfold densityMean
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun ω => H ω * Z ω) fun ζ h => by simp [hz ζ h],
    setIntegral_eq_integral_of_forall_compl_eq_zero hz]
theorem densityMean_congr_of_ne_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {Z H H' : Ω → ℝ}
    (h : ∀ ζ, Z ζ ≠ 0 → H ζ = H' ζ) :
    densityMean μ Z H = densityMean μ Z H' := by
  unfold densityMean
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  by_cases hz : Z ζ = 0
  · simp [hz]
  · simp [h ζ hz]
theorem jointCumulant_congr_of_blockProd {Ω α : Type} [DecidableEq α] {m m' : (Ω → ℝ) → ℝ} {S : Finset α}
    {f f' : α → Ω → ℝ} (h : ∀ J : Finset α, m (blockProd f J) = m' (blockProd f' J)) :
    jointCumulant m S f = jointCumulant m' S f' := by
  unfold jointCumulant
  simp only [h]
theorem sum_pow_le_card_pow_mul_sum {α : Type} [Fintype α] [Nonempty α] (a : α → ℝ) (ha : ∀ t, 0 ≤ a t)
    (m : ℕ) : (∑ t, a t) ^ m ≤ (Fintype.card α : ℝ) ^ m * ∑ t, a t ^ m := by
  obtain ⟨t₀, -, ht⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  have h1 : ∑ t, a t ≤ (Fintype.card α : ℝ) * a t₀ := by
    calc ∑ t, a t ≤ ∑ _t : α, a t₀ := Finset.sum_le_sum fun t _ => ht t (Finset.mem_univ t)
      _ = (Fintype.card α : ℝ) * a t₀ := by simp
  have h2 : a t₀ ^ m ≤ ∑ t, a t ^ m :=
    Finset.single_le_sum (f := fun t => a t ^ m) (fun t _ => pow_nonneg (ha t) m) (Finset.mem_univ t₀)
  calc (∑ t, a t) ^ m ≤ ((Fintype.card α : ℝ) * a t₀) ^ m :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun t _ => ha t) h1 m
    _ = (Fintype.card α : ℝ) ^ m * a t₀ ^ m := mul_pow _ _ _
    _ ≤ (Fintype.card α : ℝ) ^ m * ∑ t, a t ^ m := mul_le_mul_of_nonneg_left h2 (by positivity)
theorem abs_prod_le_one_add_sum_pow {α : Type} (P : Finset α) (a : α → ℝ) :
    |∏ t ∈ P, a t| ≤ 1 + ∑ t ∈ P, |a t| ^ P.card := by apply _root_.YangMills.Construction.Cumulants.abs_prod_le_one_add_sum_pow <;> assumption
theorem norm_piSingle_one {n : ℕ} (a : Fin n) : ‖(Pi.single a 1 : Fin n → ℝ)‖ = 1 := by
  rw [Pi.norm_single]
  simp
theorem abs_mixedDerivAt_le {Ω : Type} {n : ℕ} (G : (Fin n → ℝ) → Ω → ℝ) (J : Finset (Fin n)) (ω : Ω) :
    |mixedDerivAt G J ω| ≤ ‖iteratedFDeriv ℝ J.card (fun τ => G τ ω) 0‖ := by
  unfold mixedDerivAt
  have h := (iteratedFDeriv ℝ J.card (fun τ => G τ ω) 0).le_opNorm
    (fun j => (Pi.single (J.orderEmbOfFin rfl j) 1 : Fin n → ℝ))
  simpa [norm_piSingle_one] using h
theorem integrable_prod_mixedDerivAt_log_mul_paramDensity (hQ : QuaternionCutoffSmoothBounded) {ρ : ℝ}
    {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {i : ℕ} {l R₁ M : ℝ}
    {A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ} (hl : 0 < l) (hR : ρ / l ≤ R₁)
    (hAK : ∀ ζ ∈ polyBall ι R₁, ContDiffAt ℝ (i + k : ℕ) (paramLift i l A) (0, ζ))
    (hM : ∀ ζ ∈ polyBall ι R₁, ∀ j, j ≤ i + k →
      ‖iteratedFDeriv ℝ j (fun τ => paramLift i l A (τ, ζ)) 0‖ ≤ M)
    (hint : ∀ (j q : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
      Integrable fun ζ => |iteratedDeriv j p (l * ‖ζ b‖)| ^ q * scaledDensity ρ p A (l, 0) ζ)
    (hZ : Integrable (scaledDensity ρ p A (l, 0))) (S : Finset (Fin (i + k))) (π : Finpartition S) :
    Integrable fun ζ =>
      (∏ J ∈ π.parts, mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ) *
        paramDensity ρ p i l A (0, ζ) := by
  classical
  set Z₀ : BondField ι → ℝ := scaledDensity ρ p A (l, 0) with hZ₀
  have hz0 : ∀ ζ, paramDensity ρ p i l A (0, ζ) = Z₀ ζ := by
    intro ζ
    rw [paramDensity_eq]
    simp [hZ₀]
  set U : Set (BondField ι) := {ζ | ∀ b, l * ‖ζ b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {ζ | l * ‖ζ b‖ < ρ} := by
      ext ζ
      simp [hU]
    rw [this]
    refine isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    exact continuous_const.mul (continuous_norm.comp (continuous_apply b))
  have hUK : U ⊆ polyBall ι R₁ := fun ζ hζ b => by
    have h1 : ‖ζ b‖ < ρ / l := by
      rw [lt_div_iff₀ hl, mul_comm]
      exact hζ b
    linarith
  have hZpos : ∀ ζ ∈ U, 0 < paramDensity ρ p i l A (0, ζ) := by
    intro ζ hζ
    have h1 : 0 < scaledCutoff ρ p (l + (scaleTopCLM i k 0).1) ζ := by
      refine scaledCutoff_pos_of_lt fun b => ?_
      simp only [map_zero, Prod.fst_zero, add_zero]
      rw [norm_smul, Real.norm_of_nonneg hl.le]
      exact hζ b
    exact mul_pos h1 (Real.exp_pos _)
  have hZoff : ∀ ζ, ζ ∉ U → Z₀ ζ = 0 := by
    intro ζ hζ
    simp only [hU, mem_ofPred_eq, not_forall, not_lt] at hζ
    obtain ⟨b, hb⟩ := hζ
    have : scaledCutoff ρ p l ζ = 0 := by
      refine scaledCutoff_eq_zero_of_le (b := b) ?_
      rw [norm_smul, Real.norm_of_nonneg hl.le]
      exact hb
    simp [hZ₀, scaledDensity, this]
  have hzc : ∀ ζ ∈ U, ContDiffAt ℝ (i + k : ℕ) (paramDensity ρ p i l A) (0, ζ) := fun ζ hζ =>
    paramDensity_contDiffAt hQ hρ hp (hAK ζ (hUK hζ))
  have hE : ∀ J : Finset (Fin (i + k)), ContinuousOn
      (mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J) U := by
    intro J ζ hζ
    set f' : BondField ι × (Fin (i + k) → ℝ) → ℝ := fun q => Real.log (paramDensity ρ p i l A (q.2, q.1))
      with hf'
    have h1 : ContDiffAt ℝ (i + k : ℕ) f' (ζ, 0) := by
      have h2 : ContDiffAt ℝ (i + k : ℕ)
          (fun q : BondField ι × (Fin (i + k) → ℝ) => paramDensity ρ p i l A (q.2, q.1)) (ζ, 0) :=
        ContDiffAt.comp (g := paramDensity ρ p i l A) (ζ, 0) (hzc ζ hζ)
          (contDiff_snd.prodMk contDiff_fst).contDiffAt
      exact h2.log (hZpos ζ hζ).ne'
    have hcard : J.card ≤ i + k := by simpa using J.card_le_univ
    have h3 := contDiffAt_partialJetSnd (m := 0) h1 (by omega)
      (fun j => (Pi.single (J.orderEmbOfFin rfl j) 1 : Fin (i + k) → ℝ))
    exact h3.continuousAt.continuousWithinAt
  set F : BondField ι → ℝ := fun ζ =>
    (∏ J ∈ π.parts, mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ) *
      paramDensity ρ p i l A (0, ζ) with hF
  have hFc : ContinuousOn F U := by
    refine ContinuousOn.mul (continuousOn_finsetProd _ fun J _ => hE J) ?_
    intro ζ hζ
    have h1 : ContinuousAt (paramDensity ρ p i l A) (0, ζ) := (hzc ζ hζ).continuousAt
    have h2 : ContinuousAt (fun ζ' : BondField ι => ((0 : Fin (i + k) → ℝ), ζ')) ζ := by fun_prop
    exact (ContinuousAt.comp (f := fun ζ' : BondField ι => ((0 : Fin (i + k) → ℝ), ζ')) h1 h2).continuousWithinAt
  have hFoff : ∀ ζ, ζ ∉ U → F ζ = 0 := fun ζ hζ => by
    simp only [hF, hz0, hZoff ζ hζ, mul_zero]
  have hFm : AEStronglyMeasurable F volume := by
    have h1 : AEStronglyMeasurable F (volume.restrict U) := hFc.aestronglyMeasurable hUo.measurableSet
    have h2 : U.indicator F = F := by
      funext ζ
      by_cases h : ζ ∈ U
      · simp [h]
      · simp [h, hFoff ζ h]
    rw [← h2]
    exact (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr h1
  set m : ℕ := π.parts.card with hm
  set C : ℝ := (Fintype.card (Option ι) : ℝ) ^ m with hC
  set D : BondField ι → ℝ := fun ζ => Z₀ ζ + ∑ J ∈ π.parts, C * (|M| ^ m * Z₀ ζ +
      ∑ b, (|R₁| ^ J.card) ^ m * (|iteratedDeriv J.card p (l * ‖ζ b‖)| ^ m * Z₀ ζ)) with hD
  have hDi : Integrable D := by
    refine hZ.add (integrable_finsetSum _ fun J hJ => ?_)
    have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hJ)
    have hm1 : 1 ≤ m := Finset.card_pos.mpr ⟨J, hJ⟩
    refine Integrable.const_mul (Integrable.add (hZ.const_mul _) (integrable_finsetSum _ fun b _ => ?_)) _
    exact (hint J.card m b hJ1 hm1).const_mul _
  refine hDi.mono' hFm (Eventually.of_forall fun ζ => ?_)
  by_cases hζ : ζ ∈ U
  · have hzp := hZpos ζ hζ
    rw [hz0] at hzp
    have h1 : ‖F ζ‖ =
        |∏ J ∈ π.parts, mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ| * Z₀ ζ := by
      simp only [hF, hz0, Real.norm_eq_abs, abs_mul, abs_of_pos hzp]
    rw [h1]
    have h2 := abs_prod_le_one_add_sum_pow π.parts fun J =>
      mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ
    have hterm : ∀ J ∈ π.parts,
        |mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ| ^ m ≤
        C * (|M| ^ m + ∑ b, (|R₁| ^ J.card) ^ m * |iteratedDeriv J.card p (l * ‖ζ b‖)| ^ m) := by
      intro J _
      have hcard : J.card ≤ i + k := by simpa using J.card_le_univ
      have hA1 : ContDiffAt ℝ J.card (fun τ => paramLift i l A (τ, ζ)) 0 := by
        have h3 := hAK ζ (hUK hζ)
        have h4 : ContDiffAt ℝ (i + k : ℕ) (fun τ : Fin (i + k) → ℝ => paramLift i l A (τ, ζ)) 0 :=
          ContDiffAt.comp (g := paramLift i l A) (0 : Fin (i + k) → ℝ) h3 (by fun_prop)
        exact h4.of_le (by exact_mod_cast hcard)
      rw [mixedDerivAt_log_paramDensity hp hl hζ J hA1]
      set a : Option ι → ℝ := fun o => match o with
        | none => |M|
        | some b => |R₁| ^ J.card * |iteratedDeriv J.card p (l * ‖ζ b‖)| with ha
      have hane : ∀ o, 0 ≤ a o := by
        intro o
        cases o with
        | none => exact abs_nonneg _
        | some b => positivity
      have hs : |-mixedDerivAt (shiftedAlongScale i l A) J ζ - ∑ b, cutoffDerivAlong i k p l J b ζ| ≤
          ∑ o, a o := by
        rw [Fintype.sum_option]
        have h5 : |mixedDerivAt (shiftedAlongScale i l A) J ζ| ≤ |M| := by
          have h6 := abs_mixedDerivAt_le (shiftedAlongScale i l A) J ζ
          exact h6.trans ((hM ζ (hUK hζ) J.card hcard).trans (le_abs_self _))
        have h7 : |∑ b, cutoffDerivAlong i k p l J b ζ| ≤
            ∑ b, |R₁| ^ J.card * |iteratedDeriv J.card p (l * ‖ζ b‖)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          unfold cutoffDerivAlong
          split_ifs
          · rw [abs_mul, abs_pow, abs_of_nonneg (norm_nonneg (ζ b))]
            have h8 : ‖ζ b‖ ≤ |R₁| := (hUK hζ b).trans (le_abs_self _)
            gcongr
          · simp only [abs_zero]
            positivity
        calc _ ≤ |mixedDerivAt (shiftedAlongScale i l A) J ζ| + |∑ b, cutoffDerivAlong i k p l J b ζ| := by
              rw [sub_eq_add_neg, ← neg_add]
              rw [abs_neg]
              exact abs_add_le _ _
          _ ≤ _ := add_le_add h5 h7
      have h9 := sum_pow_le_card_pow_mul_sum a hane m
      rw [Fintype.sum_option] at h9
      calc _ ≤ (∑ o, a o) ^ m := pow_le_pow_left₀ (abs_nonneg _) hs m
        _ ≤ _ := by
          rw [Fintype.sum_option]
          refine h9.trans (le_of_eq ?_)
          rw [hC, Fintype.sum_option]
          simp only [ha, mul_pow]
    have h3 : |∏ J ∈ π.parts, mixedDerivAt (logDensity fun τ ζ => paramDensity ρ p i l A (τ, ζ)) J ζ| ≤
        1 + ∑ J ∈ π.parts, C * (|M| ^ m + ∑ b, (|R₁| ^ J.card) ^ m * |iteratedDeriv J.card p (l * ‖ζ b‖)| ^ m) :=
      h2.trans (by gcongr with J hJ; exact hterm J hJ)
    have h4 := mul_le_mul_of_nonneg_right h3 hzp.le
    refine h4.trans (le_of_eq ?_)
    simp only [hD, add_mul, Finset.sum_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_assoc, add_mul, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · rw [hFoff ζ hζ]
    simp only [norm_zero, hD, hZoff ζ hζ]
    simp
theorem iteratedDeriv_partialJetSnd_eq_iteratedFDeriv {i : ℕ} {l : ℝ} (M M' : ℝ × (Fin k → ℝ) → ℝ)
    (mt : (Fin (i + k) → ℝ) → ℝ) (hM' : ContDiffAt ℝ (i + k : ℕ) M' (l, 0))
    (hev : mt =ᶠ[𝓝 0] fun τ => M' (scaleTopCLM i k τ + (l, 0)))
    (hg : iteratedDeriv i (partialJetSnd M (0 : Fin k → ℝ) fun j => Pi.single j 1) l =
      iteratedDeriv i (partialJetSnd M' (0 : Fin k → ℝ) fun j => Pi.single j 1) l) :
    iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => M (l', τ)) 0 fun j => Pi.single j 1) l =
      iteratedFDeriv ℝ (i + k) mt 0 fun a => Pi.single a 1 := by
  have e1 : iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => M (l', τ)) 0 fun j => Pi.single j 1) l =
      iteratedDeriv i (partialJetSnd M (0 : Fin k → ℝ) fun j => Pi.single j 1) l := rfl
  rw [e1, hg, (hev.iteratedFDeriv ℝ (i + k)).eq_of_nhds]
  have h0 : ContDiffAt ℝ (i + k : ℕ) M' (scaleTopCLM i k 0 + (l, 0)) := by simpa using hM'
  rw [iteratedFDeriv_comp_add_const_apply (scaleTopCLM i k) (l, 0) (x := (0 : Fin (i + k) → ℝ)) h0 le_rfl]
  have e2 : scaleTopCLM i k 0 + (l, (0 : Fin k → ℝ)) = (l, 0) := by simp
  rw [e2, iteratedDeriv_eq_iteratedFDeriv]
  refine iteratedFDeriv_partialJetSnd (fun j => Pi.single j 1) i (i + k) (fun _ => 1) _ l ⟨rfl, ?_, ?_⟩
    hM' le_rfl
  · intro a ha
    exact scaleTopCLM_single_of_lt i k a ha
  · intro a ha hk
    exact scaleTopCLM_single_of_le i k a ha hk
theorem eventually_contDiffAt_zero_snd {n m : ℕ} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : (Fin m → ℝ) × Q → ℝ} {ζ : Q}
    (h : ContDiffAt ℝ n f (0, ζ)) : ∀ᶠ ζ' in 𝓝 ζ, ContDiffAt ℝ n f (0, ζ') := by
  have h1 : ∀ᶠ z in 𝓝 ((0 : Fin m → ℝ), ζ), ContDiffAt ℝ n f z := h.eventually (by simp)
  have h2 : Tendsto (fun ζ' : Q => ((0 : Fin m → ℝ), ζ')) (𝓝 ζ) (𝓝 (0, ζ)) :=
    (Continuous.prodMk_right _).tendsto ζ
  exact h2.eventually h1
def scaleTopSection (i k : ℕ) (v : ℝ × (Fin k → ℝ)) : Fin (i + k) → ℝ := fun a =>
  if h : (a : ℕ) < i then (if (a : ℕ) = 0 then v.1 else 0) else
    if hk : (a : ℕ) - i < k then v.2 ⟨(a : ℕ) - i, hk⟩ else 0
theorem contDiff_scaleTopSection (i k n : ℕ) : ContDiff ℝ n (scaleTopSection i k) := by
  refine contDiff_pi.mpr fun a => ?_
  by_cases h : (a : ℕ) < i
  · by_cases h0 : (a : ℕ) = 0
    · simp only [scaleTopSection, h, h0, dif_pos, if_true]
      have : (0 : ℕ) < i := by omega
      simp only [this, dite_true, if_true]
      exact contDiff_fst
    · simp only [scaleTopSection, h, h0, dite_true, if_false]
      exact contDiff_const
  · have hk : (a : ℕ) - i < k := by omega
    simp only [scaleTopSection, h, hk, dite_true, dite_false]
    exact (contDiff_apply ℝ ℝ _).comp contDiff_snd
theorem scaleTopSection_zero (i k : ℕ) : scaleTopSection i k 0 = 0 := by
  funext a
  simp only [scaleTopSection, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Pi.zero_def]
  split_ifs <;> rfl
theorem scaleTopCLM_scaleTopSection_snd (i k : ℕ) (v : ℝ × (Fin k → ℝ)) :
    (scaleTopCLM i k (scaleTopSection i k v)).2 = v.2 := by
  rw [scaleTopCLM_apply]
  funext b
  show scaleTopSection i k v (Fin.natAdd i b) = v.2 b
  have h1 : ¬ ((Fin.natAdd i b : Fin (i + k)) : ℕ) < i := by simp
  have h2 : ((Fin.natAdd i b : Fin (i + k)) : ℕ) - i < k := by simp
  have h3 : (⟨((Fin.natAdd i b : Fin (i + k)) : ℕ) - i, h2⟩ : Fin k) = b := by
    apply Fin.ext
    simp
  simp only [scaleTopSection, h1, h2, dite_true, dite_false, h3]
theorem scaleTopCLM_scaleTopSection_fst {i : ℕ} (hi : 1 ≤ i) (k : ℕ) (v : ℝ × (Fin k → ℝ)) :
    (scaleTopCLM i k (scaleTopSection i k v)).1 = v.1 := by
  rw [scaleTopCLM_apply]
  show ∑ a : Fin i, scaleTopSection i k v (Fin.castAdd k a) = v.1
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin i)]
  · have h0 : (0 : ℕ) < i := by omega
    simp [scaleTopSection, h0]
  · intro b _ hb
    have h1 : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    simp [scaleTopSection, h1]
  · simp
theorem scaleTopCLM_fst_of_zero (k : ℕ) (τ : Fin (0 + k) → ℝ) : (scaleTopCLM 0 k τ).1 = 0 := by
  rw [scaleTopCLM_apply]
  simp [scaleTopSplit]
theorem scaleTopCLM_scaleTopSection_scaleTopCLM (i k : ℕ) (τ : Fin (i + k) → ℝ) :
    scaleTopCLM i k (scaleTopSection i k (scaleTopCLM i k τ)) = scaleTopCLM i k τ := by
  refine Prod.ext ?_ (scaleTopCLM_scaleTopSection_snd i k _)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [scaleTopCLM_fst_of_zero, scaleTopCLM_fst_of_zero]
  · exact scaleTopCLM_scaleTopSection_fst hi k _
theorem scaledMeanCumulantExpansion_of_densityMean (hMean : DensityMeanCumulantExpansion)
    (hQ : QuaternionCutoffSmoothBounded) : ScaledMeanCumulantExpansion := by
  intro ι _ ρ p i k A G l hρ hp hl hA hG hint
  classical
  set R₀ : ℝ := ρ / l with hR₀
  have hR₀p : 0 < R₀ := by positivity
  have hball : ∀ ζ ∈ polyBall ι R₀, ∀ b, l * ‖ζ b‖ ≤ ρ := fun ζ hζ b => by
    have h1 := hζ b
    rw [hR₀, le_div_iff₀ hl] at h1
    linarith
  set W : Set (BondField ι) := {ζ | ContDiffAt ℝ (i + k : ℕ) (paramLift i l A) (0, ζ) ∧
    ContDiffAt ℝ (i + k : ℕ) (paramLift i l G) (0, ζ)} with hW
  obtain ⟨R₁, hR₁, hsub⟩ := exists_polyBall_subset hR₀p W fun ζ hζ => by
    have h1 := eventually_contDiffAt_zero_snd (paramLift_contDiffAt (i := i) (hA ζ (hball ζ hζ)))
    have h2 := eventually_contDiffAt_zero_snd (paramLift_contDiffAt (i := i) (hG ζ (hball ζ hζ)))
    filter_upwards [h1, h2] with z a b using ⟨a, b⟩
  set K₁ : Set (BondField ι) := polyBall ι R₁ with hK₁
  have hKc : IsCompact K₁ := isCompact_polyBall R₁
  have hKm : MeasurableSet K₁ := hKc.isClosed.measurableSet
  have hAK : ∀ ζ ∈ K₁, ContDiffAt ℝ (i + k : ℕ) (paramLift i l A) (0, ζ) := fun ζ h => (hsub h).1
  have hGK : ∀ ζ ∈ K₁, ContDiffAt ℝ (i + k : ℕ) (paramLift i l G) (0, ζ) := fun ζ h => (hsub h).2
  have hZK : ∀ ζ ∈ K₁, ContDiffAt ℝ (i + k : ℕ) (paramDensity ρ p i l A) (0, ζ) := fun ζ h =>
    paramDensity_contDiffAt hQ hρ hp (hAK ζ h)
  obtain ⟨r₁, M₁, hr₁, hc₁, hs₁⟩ := exists_uniform_jet_bound (paramLift i l G) K₁ hKc hGK
  obtain ⟨r₂, M₂, hr₂, hc₂, hs₂⟩ := exists_uniform_jet_bound (paramDensity ρ p i l A) K₁ hKc hZK
  obtain ⟨r₃, M₃, hr₃, hc₃, hs₃⟩ := exists_uniform_jet_bound (paramLift i l A) K₁ hKc hAK
  have hR₁p : 0 < R₁ := hR₀p.trans hR₁
  have hlR : ρ < l * R₁ := by
    have : ρ / l < R₁ := hR₁
    rw [div_lt_iff₀ hl] at this
    linarith
  have hopen : IsOpen {τ : Fin (i + k) → ℝ |
      ρ < (l + (scaleTopCLM i k τ).1) * R₁ ∧ 0 < l + (scaleTopCLM i k τ).1} := by
    have hc : Continuous fun τ : Fin (i + k) → ℝ => l + (scaleTopCLM i k τ).1 :=
      continuous_const.add (continuous_fst.comp (scaleTopCLM i k).continuous)
    exact (isOpen_lt continuous_const (hc.mul continuous_const)).inter (isOpen_lt continuous_const hc)
  obtain ⟨r₄, hr₄, hb₄⟩ := Metric.isOpen_iff.mp hopen 0 (by simp [hlR, hl])
  set r : ℝ := min (min r₁ r₂) (min r₃ r₄) with hr
  have hrp : 0 < r := by simp [hr, hr₁, hr₂, hr₃, hr₄]
  have hB₁ : Metric.ball (0 : Fin (i + k) → ℝ) r ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hB₂ : Metric.ball (0 : Fin (i + k) → ℝ) r ⊆ Metric.ball 0 r₂ :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hB₃ : Metric.ball (0 : Fin (i + k) → ℝ) r ⊆ Metric.ball 0 r₃ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hB₄ : Metric.ball (0 : Fin (i + k) → ℝ) r ⊆ Metric.ball 0 r₄ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  set B : Set (Fin (i + k) → ℝ) := Metric.ball 0 r with hB
  have h0B : (0 : Fin (i + k) → ℝ) ∈ B := Metric.mem_ball_self hrp
  set μ : Measure (BondField ι) := volume.restrict K₁ with hμ
  have : IsFiniteMeasure μ := ⟨by simpa [hμ] using hKc.measure_lt_top⟩
  have hae : ∀ᵐ ζ ∂μ, ζ ∈ K₁ := ae_restrict_mem hKm
  set G' : (Fin (i + k) → ℝ) → BondField ι → ℝ := shiftedAlongScale i l G with hG'
  set Z' : (Fin (i + k) → ℝ) → BondField ι → ℝ := fun τ ζ => paramDensity ρ p i l A (τ, ζ) with hZ'
  have hoff : ∀ τ ∈ B, ∀ ζ, ζ ∉ K₁ → Z' τ ζ = 0 := by
    intro τ hτ ζ hζ
    simp only [hK₁, polyBall, mem_ofPred_eq, not_forall, not_le] at hζ
    obtain ⟨b, hb⟩ := hζ
    obtain ⟨h1, h2⟩ := hb₄ (hB₄ hτ)
    have : scaledCutoff ρ p (l + (scaleTopCLM i k τ).1) ζ = 0 := by
      refine scaledCutoff_eq_zero_of_le (b := b) ?_
      rw [norm_smul, Real.norm_of_nonneg h2.le]
      have : (l + (scaleTopCLM i k τ).1) * R₁ ≤ (l + (scaleTopCLM i k τ).1) * ‖ζ b‖ :=
        mul_le_mul_of_nonneg_left hb.le h2.le
      linarith
    simp [hZ', paramDensity, this]
  have hdom : IsDominatedSmoothFamily μ (i + k) B M₁ G' := by
    refine ⟨fun τ hτ => ?_, ?_, ?_⟩
    · exact (hc₁ τ (hB₁ hτ)).aestronglyMeasurable hKm
    · filter_upwards [hae] with ζ hζ
      exact (hs₁ ζ hζ).1.mono hB₁
    · filter_upwards [hae] with ζ hζ j hj τ hτ
      exact (hs₁ ζ hζ).2 j hj τ (hB₁ hτ)
  have hZint : IntegrableOn (Z' 0) K₁ := (hc₂ 0 (Metric.mem_ball_self hr₂)).integrableOn_compact hKc
  set D₀ : BondField ι → ℝ := scaledDensity ρ p A (l, 0) with hD₀
  have hZ0 : Z' 0 = D₀ := by
    funext ζ
    simp only [hZ', hD₀]
    rw [paramDensity_eq]
    simp
  have hD₀i : Integrable D₀ := by
    rw [← hZ0]
    exact hZint.integrable_of_forall_notMem_eq_zero (hoff 0 h0B)
  set U' : Set (BondField ι) := {ζ | ∀ b, l * ‖ζ b‖ < ρ} with hU'
  have hUo' : IsOpen U' := by
    have : U' = ⋂ b, {ζ | l * ‖ζ b‖ < ρ} := by
      ext ζ
      simp [hU']
    rw [this]
    refine isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    exact continuous_const.mul (continuous_norm.comp (continuous_apply b))
  have hU'K : U' ⊆ K₁ := fun ζ hζ b => by
    have h1 : ‖ζ b‖ < ρ / l := by
      rw [lt_div_iff₀ hl, mul_comm]
      exact hζ b
    exact (h1.trans hR₁).le
  have hD₀pos : ∀ ζ ∈ U', 0 < D₀ ζ := fun ζ hζ => by
    refine mul_pos (scaledCutoff_pos_of_lt fun b => ?_) (Real.exp_pos _)
    show ‖l • ζ b‖ < ρ
    rw [norm_smul, Real.norm_of_nonneg hl.le]
    exact hζ b
  have hD₀off : ∀ ζ, D₀ ζ ≠ 0 → ζ ∈ U' := fun ζ hz b => by
    by_contra hlt
    apply hz
    have : scaledCutoff ρ p l ζ = 0 := by
      refine scaledCutoff_eq_zero_of_le (b := b) ?_
      rw [norm_smul, Real.norm_of_nonneg hl.le]
      exact not_lt.mp hlt
    simp [hD₀, scaledDensity, this]
  have hflat : IsFlatDensity μ B M₂ Z' := by
    refine ⟨⟨fun τ hτ => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact (hc₂ τ (hB₂ hτ)).aestronglyMeasurable hKm
    · filter_upwards [hae] with ζ hζ
      exact (hs₂ ζ hζ).1.mono hB₂
    · filter_upwards [hae] with ζ hζ j hj τ hτ
      exact (hs₂ ζ hζ).2 j hj τ (hB₂ hτ)
    · refine Eventually.of_forall fun ζ τ _ => ?_
      exact mul_nonneg (scaledCutoff_nonneg_all _ _ _ _) (Real.exp_pos _).le
    · filter_upwards [hae] with ζ hζ τ hτ hz j hj
      exact iteratedFDeriv_paramDensity_eq_zero hQ hρ hp ((hs₃ ζ hζ).1.mono hB₃) hτ hz j hj
    · rw [hZ0]
      have hnn : 0 ≤ᵐ[μ] D₀ := Eventually.of_forall fun ζ =>
        mul_nonneg (scaledCutoff_nonneg_all _ _ _ _) (Real.exp_pos _).le
      rw [integral_pos_iff_support_of_nonneg_ae hnn hD₀i.restrict]
      have hU'o : IsOpen U' := hUo'
      have hpos : 0 < volume U' := hU'o.measure_pos volume ⟨0, fun b => by simpa using hρ⟩
      have h2 : μ U' = volume U' := by
        rw [hμ, Measure.restrict_apply hU'o.measurableSet, Set.inter_eq_left.mpr hU'K]
      have h3 : U' ⊆ Function.support D₀ := fun ζ hζ => by
        have h4 := hD₀pos ζ hζ
        exact h4.ne'
      calc 0 < μ U' := by rw [h2]; exact hpos
        _ ≤ _ := measure_mono h3
    · intro S π
      have h1 := integrable_prod_mixedDerivAt_log_mul_paramDensity hQ hρ hp (R₁ := R₁) (M := M₃) (A := A)
        hl hR₁.le hAK (fun ζ hζ j hj => (hs₃ ζ hζ).2 j hj 0 (Metric.mem_ball_self hr₃)) hint hD₀i S π
      exact h1.restrict
  obtain ⟨hC, hF⟩ := hMean (BondField ι) μ (i + k) B M₁ M₂ G' Z' Metric.isOpen_ball h0B hdom hflat
  set M : ℝ × (Fin k → ℝ) → ℝ := scaledTopMean ρ p A G with hM
  set mt : (Fin (i + k) → ℝ) → ℝ := fun τ => densityMean μ (Z' τ) (G' τ) with hmt
  have hφ : ∀ τ ∈ B, mt τ = M (scaleTopCLM i k τ + (l, 0)) := by
    intro τ hτ
    have e : scaleTopCLM i k τ + (l, (0 : Fin k → ℝ)) =
        (l + (scaleTopCLM i k τ).1, (scaleTopCLM i k τ).2) := by
      refine Prod.ext ?_ ?_
      · simp [add_comm]
      · simp
    simp only [hmt, hμ]
    rw [densityMean_restrict_eq volume (hoff τ hτ), e]
    simp only [hM, scaledTopMean]
    have e2 : Z' τ = scaledDensity ρ p A (l + (scaleTopCLM i k τ).1, (scaleTopCLM i k τ).2) :=
      funext fun ζ => paramDensity_eq ρ p i l A τ ζ
    rw [e2]
    have e3 : G' τ = fun ζ => G ((l + (scaleTopCLM i k τ).1, ζ), (scaleTopCLM i k τ).2) := by
      funext ζ
      simp only [hG', shiftedAlongScale, scaleTopCLM_apply]
    rw [e3]
  set M'' : ℝ × (Fin k → ℝ) → ℝ := fun q => mt (scaleTopSection i k (q - (l, 0))) with hM''
  have hsc : Continuous (scaleTopSection i k) := (contDiff_scaleTopSection i k 0).continuous
  have hmap : ContDiffAt ℝ (i + k : ℕ) (fun q : ℝ × (Fin k → ℝ) => scaleTopSection i k (q - (l, 0))) (l, 0) :=
    ((contDiff_scaleTopSection i k (i + k)).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hMc : ContDiffAt ℝ (i + k : ℕ) M'' (l, 0) := by
    refine ContDiffAt.comp (g := mt) (l, 0) ?_ hmap
    have e : scaleTopSection i k (((l, 0) : ℝ × (Fin k → ℝ)) - (l, 0)) = 0 := by
      rw [sub_self, scaleTopSection_zero]
    rw [e]
    exact hC
  have hin : ∀ᶠ q in 𝓝 ((l, 0) : ℝ × (Fin k → ℝ)), scaleTopSection i k (q - (l, 0)) ∈ B := by
    have hc : ContinuousAt (fun q : ℝ × (Fin k → ℝ) => scaleTopSection i k (q - (l, 0))) (l, 0) :=
      (hsc.comp (continuous_id.sub continuous_const)).continuousAt
    refine hc.eventually (Metric.isOpen_ball.mem_nhds ?_)
    have e : scaleTopSection i k (((l, 0) : ℝ × (Fin k → ℝ)) - (l, 0)) = 0 := by
      rw [sub_self, scaleTopSection_zero]
    show scaleTopSection i k (((l, 0) : ℝ × (Fin k → ℝ)) - (l, 0)) ∈ B
    rw [e]
    exact h0B
  have hMq : ∀ᶠ q in 𝓝 ((l, 0) : ℝ × (Fin k → ℝ)),
      M'' q = M (scaleTopCLM i k (scaleTopSection i k (q - (l, 0))) + (l, 0)) := by
    filter_upwards [hin] with q hq
    exact hφ _ hq
  have hev : mt =ᶠ[𝓝 0] fun τ => M'' (scaleTopCLM i k τ + (l, 0)) := by
    have hc : ContinuousAt (fun τ : Fin (i + k) → ℝ => scaleTopSection i k (scaleTopCLM i k τ)) 0 :=
      (hsc.comp (scaleTopCLM i k).continuous).continuousAt
    have h1 : ∀ᶠ τ in 𝓝 (0 : Fin (i + k) → ℝ), scaleTopSection i k (scaleTopCLM i k τ) ∈ B := by
      refine hc.eventually (Metric.isOpen_ball.mem_nhds ?_)
      show scaleTopSection i k (scaleTopCLM i k 0) ∈ B
      rw [map_zero, scaleTopSection_zero]
      exact h0B
    have h2 : ∀ᶠ τ in 𝓝 (0 : Fin (i + k) → ℝ), τ ∈ B := Metric.isOpen_ball.mem_nhds h0B
    filter_upwards [h1, h2] with τ a b
    simp only [hM'', add_sub_cancel_right]
    rw [hφ _ b, hφ _ a, scaleTopCLM_scaleTopSection_scaleTopCLM]
  have hcur := hMq.curry_nhds
  refine ⟨fun hi => ?_, ?_⟩
  · refine hMc.congr_of_eventuallyEq ?_
    filter_upwards [hMq] with q hq
    rw [hq]
    have e : scaleTopCLM i k (scaleTopSection i k (q - (l, 0))) = q - (l, 0) :=
      Prod.ext (scaleTopCLM_scaleTopSection_fst hi k _) (scaleTopCLM_scaleTopSection_snd i k _)
    rw [e, sub_add_cancel]
  have hg : iteratedDeriv i (partialJetSnd M (0 : Fin k → ℝ) fun j => Pi.single j 1) l =
      iteratedDeriv i (partialJetSnd M'' (0 : Fin k → ℝ) fun j => Pi.single j 1) l := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [iteratedDeriv_zero, partialJetSnd]
      have h1 := hcur.self_of_nhds
      have h2 : (fun y' => M (l, y')) =ᶠ[𝓝 0] fun y' => M'' (l, y') := by
        filter_upwards [h1] with τ hτ
        rw [hτ]
        have e : scaleTopCLM 0 k (scaleTopSection 0 k (((l, τ) : ℝ × (Fin k → ℝ)) - (l, 0))) = (0, τ) := by
          refine Prod.ext (scaleTopCLM_fst_of_zero k _) ?_
          rw [scaleTopCLM_scaleTopSection_snd]
          simp
        rw [e]
        simp
      rw [(h2.iteratedFDeriv ℝ k).eq_of_nhds]
    · have h3 : (partialJetSnd M (0 : Fin k → ℝ) fun j => Pi.single j 1) =ᶠ[𝓝 l]
          partialJetSnd M'' (0 : Fin k → ℝ) fun j => Pi.single j 1 := by
        filter_upwards [hcur] with l' hl'
        simp only [partialJetSnd]
        have h2 : (fun y' => M (l', y')) =ᶠ[𝓝 0] fun y' => M'' (l', y') := by
          filter_upwards [hl'] with τ hτ
          rw [hτ]
          have e : scaleTopCLM i k (scaleTopSection i k (((l', τ) : ℝ × (Fin k → ℝ)) - (l, 0))) =
              ((l', τ) : ℝ × (Fin k → ℝ)) - (l, 0) :=
            Prod.ext (scaleTopCLM_scaleTopSection_fst hi k _) (scaleTopCLM_scaleTopSection_snd i k _)
          rw [e, sub_add_cancel]
        rw [(h2.iteratedFDeriv ℝ k).eq_of_nhds]
      exact h3.iteratedDeriv_eq i
  rw [iteratedDeriv_partialJetSnd_eq_iteratedFDeriv M M'' mt hMc hev hg, hF]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun π _ =>
    jointCumulant_congr_of_blockProd fun J => ?_
  rw [hμ, densityMean_restrict_eq volume (hoff 0 h0B), hZ0]
  refine densityMean_congr_of_ne_zero volume fun ζ hz => ?_
  refine Finset.prod_congr rfl fun o _ => ?_
  cases o with
  | none => rfl
  | some J' =>
    have hζ := hD₀off ζ hz
    have hcard : J'.card ≤ i + k := by simpa using J'.card_le_univ
    have hA1 : ContDiffAt ℝ J'.card (fun τ => paramLift i l A (τ, ζ)) 0 := by
      have h4 : ContDiffAt ℝ (i + k : ℕ) (fun τ : Fin (i + k) → ℝ => paramLift i l A (τ, ζ)) 0 :=
        ContDiffAt.comp (g := paramLift i l A) (0 : Fin (i + k) → ℝ) (hAK ζ (hU'K hζ)) (by fun_prop)
      exact h4.of_le (by exact_mod_cast hcard)
    exact mixedDerivAt_log_paramDensity hp hl hζ J' hA1
end YangMills.Construction.ScaleDerivatives
end
