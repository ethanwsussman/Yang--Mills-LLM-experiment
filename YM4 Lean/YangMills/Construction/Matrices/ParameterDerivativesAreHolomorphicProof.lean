import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import YangMills.Construction.Matrices.ParameterDerivativeHolomorphy
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.ParameterDerivatives
open YangMills.Construction.Coordinates
section PartialDerivatives
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [CompleteSpace F]
def partialDerivSnd (G : E × ℂ → F) : ℕ → E × ℂ → F
  | 0 => G
  | k + 1 => fun x => fderiv ℂ (partialDerivSnd G k) x ((0 : E), (1 : ℂ))
theorem analyticOnNhd_partialDerivSnd {G : E × ℂ → F} {Ω : Set (E × ℂ)}
    (hG : AnalyticOnNhd ℂ G Ω) (k : ℕ) : AnalyticOnNhd ℂ (partialDerivSnd G k) Ω := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro x hx
    exact ((ContinuousLinearMap.apply ℂ F ((0 : E), (1 : ℂ))).analyticAt _).comp (ih.fderiv x hx)
theorem iteratedDeriv_eq_partialDerivSnd {G : E × ℂ → F} {Ω : Set (E × ℂ)} (hΩ : IsOpen Ω)
    (hG : AnalyticOnNhd ℂ G Ω) (k : ℕ) : ∀ (w : E) (t : ℂ), (w, t) ∈ Ω →
      iteratedDeriv k (fun s : ℂ => G (w, s)) t = partialDerivSnd G k (w, t) := by
  induction k with
  | zero => intro w t _; simp [partialDerivSnd]
  | succ k ih =>
    intro w t h
    rw [iteratedDeriv_succ]
    have hc : ContinuousAt (fun s : ℂ => (w, s)) t := by fun_prop
    have he : iteratedDeriv k (fun s : ℂ => G (w, s)) =ᶠ[𝓝 t]
        fun s => partialDerivSnd G k (w, s) := by
      filter_upwards [hc.preimage_mem_nhds (hΩ.mem_nhds h)] with s hs using ih w s hs
    rw [he.deriv_eq]
    have hd : HasFDerivAt (partialDerivSnd G k)
        (fderiv ℂ (partialDerivSnd G k) (w, t)) (w, t) :=
      (analyticOnNhd_partialDerivSnd hG k (w, t) h).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun s : ℂ => (w, s)) ((0 : E), (1 : ℂ)) t :=
      (hasDerivAt_const t w).prodMk (hasDerivAt_id t)
    exact (hd.comp_hasDerivAt t hl).deriv
end PartialDerivatives
def entriesEquiv : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem entriesEquiv_apply (X : ComplexMatrix2) :
    entriesEquiv X = ComplexCoordinates.matrixEquiv X :=
  rfl
theorem analyticOnNhd_of_isHolomorphicIn
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    {N : ℕ} {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates 4}
    (hf : ComplexCoordinates.IsHolomorphicIn O f) :
    AnalyticOnNhd ℂ (fun z => entriesEquiv.symm (f z)) O := by
  have ho : IsOpen O := hf.1
  obtain ⟨-, -, hL, -, -⟩ := (hH.1 N O ho).1 4 f hf
  have hdiff : ∀ a ∈ O, DifferentiableAt ℂ f a := fun a ha => by
    obtain ⟨L, hL⟩ := hL a ha
    exact (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt
  let P : (Fin N → ComplexMatrix2) →L[ℂ] ComplexCoordinates N :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X j => X j 0 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let Q : ComplexCoordinates N →L[ℂ] (Fin N → ComplexMatrix2) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun z j => z j • (1 : ComplexMatrix2)
        map_add' := fun x y => by funext j; simp [add_smul]
        map_smul' := fun c x => by funext j; simp [mul_smul] }
  have hPQ : ∀ z, P (Q z) = z := by
    intro z
    funext j
    change (z j • (1 : ComplexMatrix2)) 0 0 = z j
    simp
  have hopen : IsOpen (P ⁻¹' O) := ho.preimage P.continuous
  have hdf : DifferentiableOn ℂ (fun X => entriesEquiv.symm (f (P X))) (P ⁻¹' O) := by
    intro X hX
    have h1 : DifferentiableAt ℂ (fun X => f (P X)) X :=
      (hdiff _ hX).comp X P.differentiableAt
    exact (entriesEquiv.symm.differentiableAt.comp X h1).differentiableWithinAt
  have han := hA (Fin N) (P ⁻¹' O) _ hopen hdf
  intro z hz
  have hmem : Q z ∈ P ⁻¹' O := by
    show P (Q z) ∈ O
    rwa [hPQ]
  have hc := (han (Q z) hmem).comp (Q.analyticAt z)
  refine hc.congr (Eventually.of_forall fun y => ?_)
  simp [hPQ]
theorem isHolomorphicIn_of_analyticOnNhd {N : ℕ} {S : Set (ComplexCoordinates N)}
    {F F' : ComplexCoordinates N → ComplexCoordinates 4} (hS : IsOpen S)
    (hF' : AnalyticOnNhd ℂ F' S) (hEq : ∀ w ∈ S, F w = F' w) :
    ComplexCoordinates.IsHolomorphicIn S F := by
  refine ⟨hS, hF'.continuousOn.congr hEq, fun a ha j => ?_⟩
  have hc : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hU : IsOpen ((fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ⁻¹' S) :=
    hS.preimage hc
  have h0 : (0 : ℂ) ∈ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ⁻¹' S := by
    simpa using ha
  filter_upwards [hU.mem_nhds h0] with ζ hζ
  have he : (fun ζ : ℂ => F (a + ζ • ComplexCoordinates.stdBasisVector j)) =ᶠ[𝓝 ζ]
      fun ζ : ℂ => F' (a + ζ • ComplexCoordinates.stdBasisVector j) := by
    filter_upwards [hU.mem_nhds hζ] with η hη using hEq _ hη
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => F' (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ :=
    (hF' _ hζ).differentiableAt.comp ζ (by fun_prop)
  exact hd.congr_of_eventuallyEq he
theorem continuousOn_of_isHolomorphicOnTraceless {σ E : Type} [Fintype σ] {l : ℕ}
    (hT : ExpChartHolomorphy.TracelessTopologiesAgree σ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (e : E ≃ ComplexCoordinates l)
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    (h : IsHolomorphicOnTraceless b e O f) :
    ContinuousOn (e ∘ f) O := by
  have hsub : O ⊆ tracelessPi σ := h.1.1
  let ν : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have h2 := h.2 ν
  rw [continuousOn_iff']
  intro t ht
  have hS : (e ∘ f) ⁻¹' t ∩ O ⊆ tracelessPi σ := fun A hA => hsub hA.2
  have hTo : IsOpen (tupleOfCoords b ν ⁻¹' ((e ∘ f) ⁻¹' t ∩ O)) := by
    have := h2.2.1.isOpen_inter_preimage h2.1 ht
    convert this using 1
    ext w
    simp [and_comm]
  have hto : IsSupOpen ((e ∘ f) ⁻¹' t ∩ O) := (((hT _ hS).2 b ν)).2 hTo
  obtain ⟨u, hu, hue⟩ := (hT _ hS).1.1 hto
  refine ⟨u, hu, ?_⟩
  ext A
  constructor
  · intro hA
    have hA' := hA
    rw [hue] at hA'
    exact ⟨hA'.1, hA.2⟩
  · intro hA
    have : A ∈ u ∩ tracelessPi σ := ⟨hA.1, hsub hA.2⟩
    rwa [← hue] at this
section Coordinates
variable {ι κ : Type} [Fintype ι] [Fintype κ]
def paramCoord (dc : Fin 3 → ℂ) (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)))
    (x : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ) (c : Fin 3) : ι ⊕ (κ ⊕ Unit) → ℂ
  | .inl i => x.1 (finProdFinEquiv (ν (.inl i), c))
  | .inr (.inl k) => x.1 (finProdFinEquiv (ν (.inr k), c))
  | .inr (.inr _) => x.2 * dc c
theorem paramCoord_add (dc : Fin 3 → ℂ) (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)))
    (x y : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ) (c : Fin 3)
    (i : ι ⊕ (κ ⊕ Unit)) :
    paramCoord dc ν (x + y) c i = paramCoord dc ν x c i + paramCoord dc ν y c i := by
  rcases i with i | k | u <;> simp [paramCoord, add_mul]
theorem paramCoord_smul (dc : Fin 3 → ℂ) (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ))) (a : ℂ)
    (x : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ) (c : Fin 3)
    (i : ι ⊕ (κ ⊕ Unit)) :
    paramCoord dc ν (a • x) c i = a * paramCoord dc ν x c i := by
  rcases i with i | k | u <;> simp [paramCoord, mul_assoc]
def paramCoordMap (dc : Fin 3 → ℂ) (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)))
    (ν' : ι ⊕ (κ ⊕ Unit) ≃ Fin (Fintype.card (ι ⊕ (κ ⊕ Unit)))) :
    (ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ) →L[ℂ]
      ComplexCoordinates (Fintype.card (ι ⊕ (κ ⊕ Unit)) * 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x j => paramCoord dc ν x (finProdFinEquiv.symm j).2
        (ν'.symm (finProdFinEquiv.symm j).1)
      map_add' := fun x y => funext fun _ => paramCoord_add dc ν x y _ _
      map_smul' := fun a x => funext fun _ => paramCoord_smul dc ν a x _ _ }
theorem tupleOfCoords_paramCoordMap (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (dc : Fin 3 → ℂ) (hdc : ∑ c, dc c • (b c : ComplexMatrix2) = cartanDirection)
    (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)))
    (ν' : ι ⊕ (κ ⊕ Unit) ≃ Fin (Fintype.card (ι ⊕ (κ ⊕ Unit))))
    (x : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ) :
    tupleOfCoords b ν' (paramCoordMap dc ν ν' x) =
      withParameter (tupleOfCoords b ν x.1) x.2 := by
  funext i
  have hL : ∀ c, paramCoordMap dc ν ν' x (finProdFinEquiv (ν' i, c)) =
      paramCoord dc ν x c i := by
    intro c
    change paramCoord dc ν x (finProdFinEquiv.symm (finProdFinEquiv (ν' i, c))).2
      (ν'.symm (finProdFinEquiv.symm (finProdFinEquiv (ν' i, c))).1) = _
    rw [Equiv.symm_apply_apply]
    simp
  simp only [tupleOfCoords, ComplexCoordinates.tracelessTuple, hL]
  rcases i with i | k | u
  · simp [paramCoord, withParameter, tupleOfCoords, ComplexCoordinates.tracelessTuple]
  · simp [paramCoord, withParameter, tupleOfCoords, ComplexCoordinates.tracelessTuple]
  · simp only [paramCoord, withParameter]
    rw [← hdc, Finset.smul_sum]
    simp [mul_smul]
omit [Fintype ι] [Fintype κ] in
theorem expChartAt_withParameter (p A : ι ⊕ κ → ComplexMatrix2) (t : ℂ) :
    expChartAt (withParameter p 0) (withParameter A t) =
      withParameter (expChartAt p A) t := by
  funext i
  rcases i with i | k | u <;> simp [expChartAt, withParameter]
theorem cartanDirection_mem : cartanDirection ∈ ComplexMatrix2.traceless := by
  show ComplexMatrix2.fullTrace cartanDirection = 0
  simp [ComplexMatrix2.fullTrace, cartanDirection, Matrix.trace]
theorem isHolomorphicOnTraceless_iteratedDeriv_chart
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (Φ : (ι ⊕ (κ ⊕ Unit) → ComplexMatrix2) → ComplexMatrix2)
    (p : ι ⊕ κ → ComplexMatrix2) {O' : Set (ι ⊕ (κ ⊕ Unit) → ComplexMatrix2)}
    (hO' : IsHolomorphicOnTraceless b ComplexCoordinates.matrixEquiv O'
      (Φ ∘ expChartAt (withParameter p 0)))
    (n : ℕ) {O : Set (ι ⊕ κ → ComplexMatrix2)} (hO : IsSupOpen O)
    (hOO' : ∀ A ∈ O, withParameter A 0 ∈ O') :
    IsHolomorphicOnTraceless b ComplexCoordinates.matrixEquiv O
      ((fun p => iteratedDeriv n (fun t : ℂ => Φ (withParameter p t)) 0) ∘
        expChartAt p) := by
  have : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
  refine ⟨hO, fun ν => ?_⟩
  have hopenT : IsOpen (tupleOfCoords b ν ⁻¹' O) :=
    (((hE.2.1 (ι ⊕ κ)).1 O hO.1).2 b ν).1 hO
  let ν' : ι ⊕ (κ ⊕ Unit) ≃ Fin (Fintype.card (ι ⊕ (κ ⊕ Unit))) := Fintype.equivFin _
  let dc : Fin 3 → ℂ := fun c => b.repr ⟨cartanDirection, cartanDirection_mem⟩ c
  have hdc : ∑ c, dc c • (b c : ComplexMatrix2) = cartanDirection := by
    have h2 := map_sum ComplexMatrix2.traceless.subtype (fun c => dc c • b c) Finset.univ
    have h3 : ComplexMatrix2.traceless.subtype (∑ c, dc c • b c) = cartanDirection :=
      congrArg Subtype.val (b.sum_repr ⟨cartanDirection, cartanDirection_mem⟩)
    rw [← h3, h2]
    rfl
  let L := paramCoordMap dc ν ν'
  have hf := hO'.2 ν'
  have han := analyticOnNhd_of_isHolomorphicIn hH hA hf
  let G : ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ → ComplexMatrix2 := fun x =>
    entriesEquiv.symm ((ComplexCoordinates.matrixEquiv ∘
      (Φ ∘ expChartAt (withParameter p 0)) ∘ tupleOfCoords b ν') (L x))
  have hGeq : ∀ w t, G (w, t) =
      Φ (withParameter (expChartAt p (tupleOfCoords b ν w)) t) := by
    intro w t
    have h1 : entriesEquiv.symm (ComplexCoordinates.matrixEquiv
        (Φ (expChartAt (withParameter p 0)
          (tupleOfCoords b ν' (L (w, t)))))) =
        Φ (expChartAt (withParameter p 0) (tupleOfCoords b ν' (L (w, t)))) := by
      rw [← entriesEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
    show entriesEquiv.symm (ComplexCoordinates.matrixEquiv
        (Φ (expChartAt (withParameter p 0)
          (tupleOfCoords b ν' (L (w, t)))))) = _
    rw [h1, tupleOfCoords_paramCoordMap b dc hdc ν ν' (w, t),
      expChartAt_withParameter]
  let Ω : Set (ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3) × ℂ) :=
    L ⁻¹' (tupleOfCoords b ν' ⁻¹' O')
  have hΩ : IsOpen Ω := hf.1.preimage L.continuous
  have hGan : AnalyticOnNhd ℂ G Ω := fun x hx => (han _ hx).comp (L.analyticAt x)
  have hmem : ∀ w ∈ tupleOfCoords b ν ⁻¹' O, (w, (0 : ℂ)) ∈ Ω := by
    intro w hw
    show tupleOfCoords b ν' (L (w, 0)) ∈ O'
    rw [tupleOfCoords_paramCoordMap b dc hdc ν ν' (w, 0)]
    exact hOO' _ hw
  have hDan := analyticOnNhd_partialDerivSnd hGan n
  let I := ContinuousLinearMap.inl ℂ (ComplexCoordinates (Fintype.card (ι ⊕ κ) * 3)) ℂ
  have hI : ∀ w, I w = (w, (0 : ℂ)) := fun w => rfl
  refine isHolomorphicIn_of_analyticOnNhd
    (F' := (entriesEquiv : ComplexMatrix2 →L[ℂ] ComplexCoordinates 4) ∘
      partialDerivSnd G n ∘ I)
    hopenT ?_ ?_
  · intro w hw
    have h1 : AnalyticAt ℂ (partialDerivSnd G n ∘ I) w :=
      AnalyticAt.comp (hDan (I w) (by rw [hI]; exact hmem w hw)) (I.analyticAt w)
    exact AnalyticAt.comp (ContinuousLinearMap.analyticAt _ _) h1
  · intro w hw
    have h2 := iteratedDeriv_eq_partialDerivSnd hΩ hGan n w 0 (hmem w hw)
    simp only [hGeq] at h2
    simp only [Function.comp_apply]
    rw [h2, hI]
    rfl
end Coordinates
theorem parameterDerivativesHolomorphic_of (hE : ExpChartHolomorphy.ExpChartTheory)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic) :
    ParameterDerivativesHolomorphic := by
  intro ι κ _ _ b W W' Φ hW hΦ hWW' n
  obtain ⟨W₀, hW₀, hWe⟩ := id hW
  have hWP : ∀ p ∈ W, p ∈ GroupLieProduct ι κ := fun p hp => by
    rw [hWe] at hp
    exact hp.2
  have hAg := (hE.2.1 (ι ⊕ κ)).1
  have hAg' := (hE.2.1 (ι ⊕ (κ ⊕ Unit))).1
  have hpc : Continuous fun A : ι ⊕ κ → ComplexMatrix2 => withParameter A 0 := by
    refine continuous_pi fun i => ?_
    rcases i with i | k | u
    · exact continuous_apply _
    · exact continuous_apply _
    · exact continuous_const
  have hAP' : ∀ A ∈ tracelessPi (ι ⊕ κ),
      withParameter A 0 ∈ tracelessPi (ι ⊕ (κ ⊕ Unit)) := by
    intro A hA' i
    rcases i with i | k | u
    · exact hA' _
    · exact hA' _
    · show (0 : ℂ) • cartanDirection ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
      rw [zero_smul]
      exact ComplexMatrix2.traceless.zero_mem
  have hchart : ∀ p ∈ W, ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧
      (∀ A ∈ O, expChartAt p A ∈ W) ∧
      IsHolomorphicOnTraceless b ComplexCoordinates.matrixEquiv O
        ((fun p => iteratedDeriv n (fun t : ℂ => Φ (withParameter p t)) 0) ∘
          expChartAt p) := by
    intro p hp
    obtain ⟨O', h0, -, hT⟩ := hΦ.2.2 (withParameter p 0) (hWW' p hp)
    obtain ⟨-, hcont, hmaps, hzero, -⟩ := (hE.2.2.2.1 ι κ).1 p (hWP p hp)
    let O : Set (ι ⊕ κ → ComplexMatrix2) := {A | A ∈ tracelessPi (ι ⊕ κ) ∧
      expChartAt p A ∈ W ∧ withParameter A 0 ∈ O'}
    have hsub : O ⊆ tracelessPi (ι ⊕ κ) := fun A hA' => hA'.1
    obtain ⟨O₀, hO₀, hO'e⟩ := (hAg' O' hT.1.1).1.1 hT.1
    obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 hcont W₀ hW₀
    have hOe : O = (u ∩ (fun A => withParameter A 0) ⁻¹' O₀) ∩ tracelessPi (ι ⊕ κ) := by
      ext A
      constructor
      · rintro ⟨h1, h2, h3⟩
        have h2' : expChartAt p A ∈ W₀ := by
          rw [hWe] at h2
          exact h2.1
        have h4 : A ∈ expChartAt p ⁻¹' W₀ ∩ tracelessPi (ι ⊕ κ) := ⟨h2', h1⟩
        rw [hue] at h4
        rw [hO'e] at h3
        exact ⟨⟨h4.1, h3.1⟩, h1⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h4 : A ∈ u ∩ tracelessPi (ι ⊕ κ) := ⟨h1, h3⟩
        rw [← hue] at h4
        refine ⟨h3, ?_, ?_⟩
        · rw [hWe]
          exact ⟨h4.1, hmaps h3⟩
        · rw [hO'e]
          exact ⟨h2, hAP' A h3⟩
    have hOopen : IsSupOpen O :=
      (hAg O hsub).1.2 ⟨_, hu.inter (hO₀.preimage hpc), hOe⟩
    have h0AP : (0 : ι ⊕ κ → ComplexMatrix2) ∈ tracelessPi (ι ⊕ κ) :=
      fun _ => ComplexMatrix2.traceless.zero_mem
    have hpt0 : withParameter (0 : ι ⊕ κ → ComplexMatrix2) 0 = 0 := by
      funext i
      rcases i with i | k | u <;> simp [withParameter]
    refine ⟨O, ⟨h0AP, by rwa [hzero], by rwa [hpt0]⟩, fun A hA' => hA'.2.1, ?_⟩
    exact isHolomorphicOnTraceless_iteratedDeriv_chart hE hH hA b Φ p hT n hOopen
      fun A hA' => hA'.2.2
  refine ⟨hW, ?_, hchart⟩
  intro p hp
  obtain ⟨O, h0, -, hT⟩ := hchart p hp
  have hhc := continuousOn_of_isHolomorphicOnTraceless hAg b _ hT
  obtain ⟨-, -, -, hzero, hball⟩ := (hE.2.2.2.1 ι κ).1 p (hWP p hp)
  have hexp : Real.exp (1 / 2) ≤ 19 / 10 := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  obtain ⟨-, hopen, hinv, hlc⟩ := hball (1 / 2) (by norm_num) hexp
  have h0B : (0 : ι ⊕ κ → ComplexMatrix2) ∈ supBall (ι ⊕ κ) (1 / 2) := by
    refine ⟨fun _ => ComplexMatrix2.traceless.zero_mem, ?_⟩
    simp [supNorm]
  have hpI : p ∈ expChartAt p '' supBall (ι ⊕ κ) (1 / 2) := ⟨0, h0B, hzero⟩
  have hlog : ExpChartHolomorphy.logChart p p = 0 := by
    have := hinv.1 h0B
    rwa [hzero] at this
  have hlogAP : MapsTo (ExpChartHolomorphy.logChart p)
      (expChartAt p '' supBall (ι ⊕ κ) (1 / 2)) (tracelessPi (ι ⊕ κ)) := by
    rintro _ ⟨A, hA', rfl⟩
    have := hinv.1 hA'
    rw [this]
    exact hA'.1
  obtain ⟨Ou, hOu, hOe⟩ := (hAg O hT.1.1).1.1 hT.1
  have h0u : (0 : ι ⊕ κ → ComplexMatrix2) ∈ Ou := by
    rw [hOe] at h0
    exact h0.1
  have hAPw := (hhc 0 h0).mono_of_mem_nhdsWithin
    (s := tracelessPi (ι ⊕ κ))
    (mem_nhdsWithin.2 ⟨Ou, hOu, h0u, fun x hx => by rw [hOe]; exact hx⟩)
  rw [← hlog] at hAPw
  have hcomp := hAPw.comp (hlc p hpI) hlogAP
  obtain ⟨U, hU, hUe⟩ := hopen
  have hpU : p ∈ U := by
    have := hpI
    rw [hUe] at this
    exact this.1
  have hcongr : ContinuousWithinAt (ComplexCoordinates.matrixEquiv ∘
      fun p => iteratedDeriv n (fun t : ℂ => Φ (withParameter p t)) 0)
      (expChartAt p '' supBall (ι ⊕ κ) (1 / 2)) p := hcomp.congr
    (fun y hy => by
      have := hinv.2 hy
      simp only [Function.comp_apply]
      rw [this])
    (by
      have := hinv.2 hpI
      simp only [Function.comp_apply]
      rw [this])
  exact hcongr.mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨U, hU, hpU, fun x hx => by rw [hUe]; exact ⟨hx.1, hWP x hx.2⟩⟩)
end YangMills.Construction.Matrices.GroupLieProduct.ParameterDerivatives
