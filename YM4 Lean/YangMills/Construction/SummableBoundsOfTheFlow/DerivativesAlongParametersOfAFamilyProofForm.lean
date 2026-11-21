import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAMoveNearATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongParametersOfAList
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterListDerivatives
open Set Filter Topology MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.DensityMeans YangMills.Construction.ScaleDerivatives YangMills.Construction.ScaledVariables
section
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem fderiv_multilinear_apply_eq {n : ℕ} {Φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => G) H} {x : E}
    (h : DifferentiableAt ℝ Φ x) (a : E) (u : Fin n → G) :
    (fderiv ℝ Φ x a) u = fderiv ℝ (fun y => Φ y u) x a := by
  have h1 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => G) H u).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  have h2 : (fun y => Φ y u) = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => G) H u) ∘ Φ := rfl
  rw [h2, h1]
  rfl
theorem iteratedFDeriv_succ_cons_eq_fderiv {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x)
    (a : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons a u) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n f y u) x a := by
  rw [iteratedFDeriv_succ_apply_left]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
    (hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n))
  have := fderiv_multilinear_apply_eq hd a u
  simpa [Fin.tail_def] using this
theorem contDiffAt_iteratedFDeriv_eval {n m i : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ n f x)
    (hmn : m + i ≤ n) (u : Fin i → E) :
    ContDiffAt ℝ m (fun y => iteratedFDeriv ℝ i f y u) x := by
  have h1 : ContDiffAt ℝ m (iteratedFDeriv ℝ i f) x :=
    hf.iteratedFDeriv_right (by exact_mod_cast hmn)
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) H u).contDiff.contDiffAt).comp x h1
theorem iteratedFDeriv_comp_add_const_apply {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (a : E) {x : G}
    (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) (v : Fin i → G) :
    iteratedFDeriv ℝ i (fun z => f (L z + a)) x v = iteratedFDeriv ℝ i f (L x + a) fun j => L (v j) := by apply _root_.YangMills.SharedProofs.p13665 <;> assumption
end
section
variable {E₁ E₂ H : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup H] [NormedSpace ℝ H]
def sndJet (f : E₁ × E₂ → H) (y : E₂) {k : ℕ} (w : Fin k → E₂) (x : E₁) : H :=
  iteratedFDeriv ℝ k (fun y' => f (x, y')) y w
theorem sndJet_eq_iteratedFDeriv {n k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y))
    (hk : k ≤ n) (w : Fin k → E₂) :
    sndJet f y w x = iteratedFDeriv ℝ k f (x, y) fun j => (0, w j) := by
  have h := iteratedFDeriv_comp_add_const_apply (ContinuousLinearMap.inr ℝ E₁ E₂) (x, 0) (x := y) (f := f)
    (by simpa using hf) hk w
  have e1 : (fun z => f ((ContinuousLinearMap.inr ℝ E₁ E₂) z + (x, 0))) = fun y' => f (x, y') := by
    funext z; simp
  rw [e1] at h
  simp only [sndJet]
  rw [h]
  simp
theorem eventually_contDiffAt_left {n : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y)) :
    ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ n f (x', y) := by
  have h1 : ∀ᶠ z in 𝓝 (x, y), ContDiffAt ℝ n f z := hf.eventually (by simp)
  have h2 : Tendsto (fun x' : E₁ => (x', y)) (𝓝 x) (𝓝 (x, y)) :=
    (Continuous.prodMk_left y).tendsto x
  exact h2.eventually h1
theorem contDiffAt_sndJet {n m k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + k ≤ n) (w : Fin k → E₂) :
    ContDiffAt ℝ m (sndJet f y w) x := by
  have h1 : ContDiffAt ℝ m (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) (x, y) :=
    contDiffAt_iteratedFDeriv_eval hf hmn _
  have h2 : ContDiffAt ℝ m (fun x' : E₁ => (x', y)) x := by fun_prop
  have h3 : ContDiffAt ℝ m (fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j)) x :=
    ContDiffAt.comp x (g := fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) h1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [eventually_contDiffAt_left hf] with x' hx'
  exact sndJet_eq_iteratedFDeriv hx' (by omega) w
def IsFstSndConcat {m p k : ℕ} (v : Fin p → E₁) (w : Fin k → E₂) (u : Fin m → E₁ × E₂) : Prop :=
  m = p + k ∧ (∀ (i : Fin m) (hi : i.val < p), u i = (v ⟨i.val, hi⟩, 0)) ∧
    ∀ (i : Fin m) (_ : p ≤ i.val) (hk : i.val - p < k), u i = (0, w ⟨i.val - p, hk⟩)
theorem iteratedFDeriv_sndJet {k : ℕ} (w : Fin k → E₂) {n : ℕ} {f : E₁ × E₂ → H} {y : E₂} :
    ∀ (p m : ℕ) (v : Fin p → E₁) (u : Fin m → E₁ × E₂) (x : E₁), IsFstSndConcat v w u →
      ContDiffAt ℝ n f (x, y) → m ≤ n →
      iteratedFDeriv ℝ p (sndJet f y w) x v = iteratedFDeriv ℝ m f (x, y) u := by
  intro p
  induction p with
  | zero =>
    intro m v u x hu hf hm
    obtain ⟨h0, -, h2⟩ := hu
    have : m = k := by omega
    subst this
    have hu' : u = fun j => (0, w j) := by
      funext j
      have := h2 j (Nat.zero_le _) (by simp)
      simpa using this
    rw [hu', ← sndJet_eq_iteratedFDeriv hf hm w]
    simp
  | succ p ih =>
    intro m v u x hu hf hm
    obtain ⟨h0, h1, h2⟩ := hu
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hR : ContDiffAt ℝ (p + 1 : ℕ) (sndJet f y w) x :=
      contDiffAt_sndJet hf (by omega) w
    have hf' : ContDiffAt ℝ (m' + 1 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hm)
    have hu0 : u 0 = (v 0, 0) := h1 0 (by simp)
    have ht : IsFstSndConcat (Fin.tail v) w (Fin.tail u) := by
      refine ⟨by omega, fun i hi => ?_, fun i hi hk => ?_⟩
      · have := h1 i.succ (by simpa using hi)
        simpa [Fin.tail_def] using this
      · have := h2 i.succ (by simp; omega) (by simp; omega)
        simp only [Fin.tail_def]
        rw [this]
        congr 2
        apply Fin.ext
        simp
    have e1 := iteratedFDeriv_succ_cons_eq_fderiv hR (v 0) (Fin.tail v)
    have e2 := iteratedFDeriv_succ_cons_eq_fderiv hf' (u 0) (Fin.tail u)
    rw [Fin.cons_self_tail] at e1 e2
    rw [e1, e2]
    have hev : (fun x' => iteratedFDeriv ℝ p (sndJet f y w) x' (Fin.tail v)) =ᶠ[𝓝 x]
        fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u) := by
      filter_upwards [eventually_contDiffAt_left hf] with x' hx'
      exact ih m' _ _ x' ht hx' (by omega)
    rw [hev.fderiv_eq, hu0]
    have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) (x, y) :=
      (contDiffAt_iteratedFDeriv_eval (m := 1) hf (by omega) _).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun x' : E₁ => (x', y)) (ContinuousLinearMap.inl ℝ E₁ E₂) x :=
      hasFDerivAt_prodMk_left x y
    have := (hd.hasFDerivAt.comp x hc).fderiv
    have e3 : (fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u)) =
      (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) ∘ fun x' : E₁ => (x', y) := rfl
    rw [e3, this]
    simp
end
def scaleTopMap (i k : ℕ) : (Fin (i + k) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ a : Fin i, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (i + k) => ℝ) (Fin.castAdd k a))
    (ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (Fin.natAdd i b))
theorem scaleTopMap_apply (i k : ℕ) (τ : Fin (i + k) → ℝ) : scaleTopMap i k τ = scaleTopSplit i k τ := by
  simp [scaleTopMap, scaleTopSplit]
theorem scaleTopMap_single_of_lt (i k : ℕ) (a : Fin (i + k)) (h : (a : ℕ) < i) :
    scaleTopMap i k (Pi.single a 1) = (1, 0) := by
  rw [scaleTopMap_apply]
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
theorem scaleTopMap_single_of_le (i k : ℕ) (a : Fin (i + k)) (h : i ≤ (a : ℕ)) (hk : (a : ℕ) - i < k) :
    scaleTopMap i k (Pi.single a 1) = (0, Pi.single ⟨(a : ℕ) - i, hk⟩ 1) := by
  rw [scaleTopMap_apply]
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
variable {i k : ℕ}
theorem scaleCount_le_scale (J : Finset (Fin (i + k))) : scaleCount J ≤ i := by
  have hinj : Function.Injective fun j : {j : Fin J.card // ((orderList J j : Fin (i + k)) : ℕ) < i} =>
      (⟨((orderList J j.1 : Fin (i + k)) : ℕ), j.2⟩ : Fin i) := by
    intro a b h
    have h2 := congrArg Fin.val h
    simp only at h2
    exact Subtype.ext ((orderList J).injective (Fin.ext h2))
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, Fintype.card_subtype] at this
  exact this
theorem topIndices_injective (J : Finset (Fin (i + k))) : Function.Injective (topIndices J) := by
  intro a b h
  have h2 := congrArg Fin.val h
  simp only [topIndices] at h2
  have ha := (orderList_lt_iff J ⟨scaleCount J + a, by have := scaleCount_le_card J; omega⟩).not.mpr (by simp)
  have hb := (orderList_lt_iff J ⟨scaleCount J + b, by have := scaleCount_le_card J; omega⟩).not.mpr (by simp)
  have h3 : ((orderList J ⟨scaleCount J + a, by have := scaleCount_le_card J; omega⟩ : Fin (i + k)) : ℕ) =
      ((orderList J ⟨scaleCount J + b, by have := scaleCount_le_card J; omega⟩ : Fin (i + k)) : ℕ) := by omega
  have h4 := (orderList J).injective (Fin.ext h3)
  have h5 := congrArg Fin.val h4
  simp only at h5
  exact Fin.ext (by omega)
theorem card_sub_scaleCount_le (J : Finset (Fin (i + k))) : J.card - scaleCount J ≤ k := by
  have := Fintype.card_le_of_injective _ (topIndices_injective J)
  simpa using this
def topEmbedding {r : ℕ} (t : Fin r → Fin k) : (Fin r → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ u, if t u = b then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℝ) u else 0
theorem topEmbedding_apply {r : ℕ} (t : Fin r → Fin k) (τ : Fin r → ℝ) (b : Fin k) :
    topEmbedding t τ b = ∑ u, if t u = b then τ u else 0 := by
  simp only [topEmbedding, ContinuousLinearMap.coe_pi', FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp
theorem topEmbedding_single {r : ℕ} (t : Fin r → Fin k) (u : Fin r) :
    topEmbedding t (Pi.single u 1) = Pi.single (t u) 1 := by
  funext b
  rw [topEmbedding_apply, Finset.sum_eq_single u]
  · by_cases h : t u = b
    · subst h
      simp
    · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h)]
  · intro u' _ hu
    split_ifs
    · simp [hu]
    · rfl
  · simp
theorem iteratedFDeriv_scaleTop_eq_iteratedDeriv (g : ℝ × (Fin k → ℝ) → ℝ) (l : ℝ) (J : Finset (Fin (i + k)))
    (hg : ContDiffAt ℝ J.card g (l, 0)) :
    iteratedFDeriv ℝ J.card (fun τ => g (l + (scaleTopMap i k τ).1, (scaleTopMap i k τ).2)) 0
        (fun j => Pi.single (J.orderEmbOfFin rfl j) 1) =
      iteratedDeriv (scaleCount J) (fun l' => iteratedFDeriv ℝ (J.card - scaleCount J)
        (fun τ => g (l', topEmbedding (topIndices J) τ)) 0 fun u => Pi.single u 1) l := by
  set s := scaleCount J with hs
  set r := J.card - s with hr
  have hsm : s ≤ J.card := scaleCount_le_card J
  set w : Fin r → Fin k → ℝ := fun u => Pi.single (topIndices J u) 1 with hw
  have e0 : (fun τ => g (l + (scaleTopMap i k τ).1, (scaleTopMap i k τ).2)) =
      fun τ => g (scaleTopMap i k τ + (l, 0)) := by
    funext τ
    congr 1
    refine Prod.ext ?_ ?_
    · simp [add_comm]
    · simp
  rw [e0]
  have h0 : ContDiffAt ℝ J.card g (scaleTopMap i k 0 + (l, 0)) := by simpa using hg
  rw [iteratedFDeriv_comp_add_const_apply (scaleTopMap i k) (l, 0) (x := (0 : Fin (i + k) → ℝ)) h0 le_rfl]
  have e1 : scaleTopMap i k 0 + (l, (0 : Fin k → ℝ)) = (l, 0) := by simp
  rw [e1]
  have hev : (fun l' => iteratedFDeriv ℝ r (fun τ => g (l', topEmbedding (topIndices J) τ)) 0
      fun u => Pi.single u 1) =ᶠ[𝓝 l] sndJet g (0 : Fin k → ℝ) w := by
    filter_upwards [eventually_contDiffAt_left hg] with l' hl'
    have h1 : ContDiffAt ℝ r (fun y => g (l', y)) (topEmbedding (topIndices J) 0 + 0) := by
      have h2 : ContDiffAt ℝ r g (l', 0) := hl'.of_le (by norm_cast; omega)
      have e : topEmbedding (topIndices J) 0 + 0 = (0 : Fin k → ℝ) := by simp
      rw [e]
      exact ContDiffAt.comp (g := g) (0 : Fin k → ℝ) h2
        (by fun_prop : ContDiffAt ℝ r (fun y : Fin k → ℝ => (l', y)) 0)
    have h3 := iteratedFDeriv_comp_add_const_apply (topEmbedding (topIndices J)) (0 : Fin k → ℝ)
      (x := (0 : Fin r → ℝ)) h1 le_rfl fun u => Pi.single u 1
    simp only [add_zero, map_zero] at h3
    rw [h3]
    simp only [sndJet, hw, topEmbedding_single]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_eq_iteratedFDeriv]
  symm
  refine iteratedFDeriv_sndJet w s J.card (fun _ => 1) _ l ⟨by omega, ?_, ?_⟩ hg le_rfl
  · intro j hj
    exact scaleTopMap_single_of_lt i k _ ((orderList_lt_iff J j).mpr hj)
  · intro j hj hk
    have hnot : ¬ ((orderList J j : Fin (i + k)) : ℕ) < i :=
      fun h => absurd ((orderList_lt_iff J j).mp h) (by omega)
    have hi : i ≤ ((orderList J j : Fin (i + k)) : ℕ) := not_lt.mp hnot
    have hk' : ((orderList J j : Fin (i + k)) : ℕ) - i < k := by
      have := (orderList J j : Fin (i + k)).2
      omega
    show scaleTopMap i k (Pi.single (orderList J j) 1) = _
    rw [scaleTopMap_single_of_le i k _ hi hk']
    simp only [hw]
    congr 2
    apply Fin.ext
    simp only [topIndices]
    congr 3
    apply Fin.ext
    simp only
    omega
variable {F : BlockFrame}
theorem bondSpread_topEmbedding {r : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (t : Fin r → Fin k) (τ : Fin r → ℝ) :
    ColdStepAtMirrorFrames.bondSpread c X (topEmbedding t τ) =
      ColdStepAtMirrorFrames.bondSpread (c ∘ t) (X ∘ t) τ := by
  classical
  funext y a
  simp only [ColdStepAtMirrorFrames.bondSpread, topEmbedding_apply, Function.comp]
  have h1 : ∀ l : Fin k, (if c l = (y, a) then (∑ u, if t u = l then τ u else 0) • X l else 0) =
      ∑ u, if t u = l then (if c l = (y, a) then τ u • X l else 0) else 0 := by
    intro l
    by_cases hc : c l = (y, a)
    · simp only [hc, if_true, Finset.sum_smul]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> simp
    · simp [hc]
  rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_ite_eq]
  simp
theorem mixedDerivAt_shiftedAlongScale_eq
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {l : ℝ}
    {ζ : StepVariable (finiteCells F)} {n : ℕ}
    (hreg : ContDiffAt ℝ n (observableAlongList Ob V c X) ((l, ζ), 0)) (I : Finset (Fin (i + k)))
    (hI : I.card ≤ n) :
    mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I ζ =
      scaleDeriv Ob V (c ∘ topIndices I) (X ∘ topIndices I) (scaleCount I) ζ l := by
  set g : ℝ × (Fin k → ℝ) → ℝ := fun x => observableAlongList Ob V c X ((x.1, ζ), x.2) with hg
  have hgc : ContDiffAt ℝ I.card g (l, 0) := by
    have h1 : ContDiffAt ℝ n g (l, 0) :=
      ContDiffAt.comp (g := observableAlongList Ob V c X) (l, 0) hreg (by fun_prop)
    exact h1.of_le (by exact_mod_cast hI)
  have h := iteratedFDeriv_scaleTop_eq_iteratedDeriv g l I hgc
  unfold mixedDerivAt scaleDeriv
  have e1 : (fun τ => shiftedAlongScale i l (observableAlongList Ob V c X) τ ζ) =
      fun τ => g (l + (scaleTopMap i k τ).1, (scaleTopMap i k τ).2) := by
    funext τ
    simp only [shiftedAlongScale, hg, scaleTopMap_apply]
  rw [e1, h]
  congr 1
  funext l'
  unfold bondDeriv
  have e2 : (fun τ => g (l', topEmbedding (topIndices I) τ)) =
      fun τ => Ob l' ζ
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread (c ∘ topIndices I) (X ∘ topIndices I) τ) V) := by
    funext τ
    simp only [hg, observableAlongList, bondSpread_topEmbedding]
  rw [e2]
theorem contDiffAt_mixedDerivAt_shiftedAlongScale
    {f : (ℝ × BondField ↥(chordBonds (finiteCells F))) × (Fin k → ℝ) → ℝ} {l : ℝ}
    {ζ : StepVariable (finiteCells F)} {n : ℕ} (hreg : ContDiffAt ℝ n f ((l, ζ), 0)) (I : Finset (Fin (i + k)))
    (hI : 1 + I.card ≤ n) : ContDiffAt ℝ 1 (mixedDerivAt (shiftedAlongScale i l f) I) ζ := by
  set f' : StepVariable (finiteCells F) × (Fin (i + k) → ℝ) → ℝ :=
    fun q => f ((l + (scaleTopMap i k q.2).1, q.1), (scaleTopMap i k q.2).2) with hf'
  have hm : ContDiff ℝ n (fun q : StepVariable (finiteCells F) × (Fin (i + k) → ℝ) =>
      (((l + (scaleTopMap i k q.2).1, q.1), (scaleTopMap i k q.2).2) :
        (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ))) := by
    have h1 : ContDiff ℝ n (fun q : StepVariable (finiteCells F) × (Fin (i + k) → ℝ) => scaleTopMap i k q.2) :=
      (scaleTopMap i k).contDiff.comp contDiff_snd
    exact ((contDiff_const.add h1.fst).prodMk contDiff_fst).prodMk h1.snd
  have h2 : ContDiffAt ℝ n f' (ζ, 0) := by
    refine ContDiffAt.comp (ζ, 0) ?_ hm.contDiffAt
    simpa using hreg
  have h3 := contDiffAt_sndJet (m := 1) h2 (by omega)
    (fun j => (Pi.single (I.orderEmbOfFin rfl j) 1 : Fin (i + k) → ℝ))
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun ζ' => ?_)
  simp only [mixedDerivAt, sndJet, hf', shiftedAlongScale, scaleTopMap_apply]
theorem exists_topIndices_eq (J : Finset (Fin (i + k))) (b : Fin k) (hb : Fin.natAdd i b ∈ J) :
    ∃ u, topIndices J u = b := by
  have h1 : Fin.natAdd i b ∈ Set.range (J.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hb
  obtain ⟨j, hj⟩ := h1
  have hlow : ¬ ((orderList J j : Fin (i + k)) : ℕ) < i := by
    show ¬ ((J.orderEmbOfFin rfl j : Fin (i + k)) : ℕ) < i
    rw [hj]
    simp
  have hs : scaleCount J ≤ j := not_lt.mp fun h => hlow ((orderList_lt_iff J j).mpr h)
  refine ⟨⟨(j : ℕ) - scaleCount J, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [topIndices]
  have e : (⟨scaleCount J + ((j : ℕ) - scaleCount J), by omega⟩ : Fin J.card) = j := by
    apply Fin.ext
    simp only
    omega
  simp only [e]
  show ((J.orderEmbOfFin rfl j : Fin (i + k)) : ℕ) - i = b
  rw [hj]
  simp
theorem scaleCount_eq_card {J : Finset (Fin (i + k))} (h : ∀ a ∈ J, (a : ℕ) < i) : scaleCount J = J.card := by
  unfold scaleCount
  rw [Finset.filter_true_of_mem fun j _ => h _ (Finset.orderEmbOfFin_mem J rfl j)]
  simp
theorem derivAlongParameterList_holds : derivAlongParameterListStatement :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ h I hI => mixedDerivAt_shiftedAlongScale_eq h I hI,
    fun _ _ _ _ _ _ _ h I hI => contDiffAt_mixedDerivAt_shiftedAlongScale h I hI,
    fun _ _ J => ⟨scaleCount_le_scale J, card_sub_scaleCount_le J⟩, fun _ _ _ h => scaleCount_eq_card h,
    fun _ _ J b h => exists_topIndices_eq J b h⟩
end YangMills.Construction.ParameterListDerivatives
end
