import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAndThePrincipalLogarithm
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ContDiff
namespace YangMills.Construction.SeveralComplexVariables.HolomorphicCalculus
variable {I : Type} [Fintype I] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
lemma differentiable_affineLine (c v : I → ℂ) : Differentiable ℂ fun ζ : ℂ => c + ζ • v :=
  (differentiable_const c).add (differentiable_id.smul_const v)
lemma eventually_affineLine_mem {Ω : Set (I → ℂ)} (hΩ : IsOpen Ω) (c v : I → ℂ) (ζ₀ : ℂ)
    (hζ₀ : c + ζ₀ • v ∈ Ω) : ∀ᶠ ζ in 𝓝 ζ₀, c + ζ • v ∈ Ω :=
  (differentiable_affineLine c v).continuous.continuousAt.eventually (hΩ.mem_nhds hζ₀)
lemma isHolomorphicOnOpen_of_differentiableOn {Ω : Set (I → ℂ)} {g : (I → ℂ) → F}
    (hΩ : IsOpen Ω) (hd : DifferentiableOn ℂ g Ω) : IsHolomorphicOnOpen Ω g := by
  refine ⟨hΩ, hd.continuousOn, fun c hc q => ?_⟩
  filter_upwards [eventually_affineLine_mem hΩ c (basisVector q) 0 (by simpa using hc)] with ζ hζ
  exact (hd.differentiableAt (hΩ.mem_nhds hζ)).comp ζ (differentiable_affineLine c _ ζ)
omit [Fintype I] in
lemma differentiableAt_coordLine {Ω : Set (I → ℂ)} {g : (I → ℂ) → F}
    (hg : IsHolomorphicOnOpen Ω g) (c : I → ℂ) (q : I) {ζ₀ : ℂ}
    (hζ₀ : c + ζ₀ • basisVector q ∈ Ω) :
    DifferentiableAt ℂ (fun ζ : ℂ => g (c + ζ • basisVector q)) ζ₀ := by
  have h0 := (hg.2.2 _ hζ₀ q).self_of_nhds
  have hs : DifferentiableAt ℂ (fun ζ : ℂ => ζ - ζ₀) ζ₀ := differentiableAt_id.sub_const ζ₀
  have hcomp := DifferentiableAt.comp
    (g := fun ζ' : ℂ => g (c + ζ₀ • basisVector q + ζ' • basisVector q)) ζ₀ (by simpa using h0) hs
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
  simp only [Function.comp]
  congr 1
  rw [add_assoc, ← add_smul]
  simp
lemma contDiffOn_and_differentiableOn
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {Ω : Set (I → ℂ)} {g : (I → ℂ) → ℂ} (hg : IsHolomorphicOnOpen Ω g) :
    ContDiffOn ℝ ∞ g Ω ∧ DifferentiableOn ℂ g Ω := by
  classical
  let e := Fintype.equivFin I
  let toI : (Fin (Fintype.card I) → ℂ) → I → ℂ := fun z i => z (e i)
  let toFin : (I → ℂ) → Fin (Fintype.card I) → ℂ := fun c j => c (e.symm j)
  have htoI : Continuous toI := continuous_pi fun i => continuous_apply _
  have hback : ∀ c, toI (toFin c) = c := fun c => by
    funext i
    simp [toI, toFin]
  let f : Coordinates.ComplexCoordinates (Fintype.card I) → Coordinates.ComplexCoordinates 1 :=
    fun z _ => g (toI z)
  let O : Set (Coordinates.ComplexCoordinates (Fintype.card I)) := toI ⁻¹' Ω
  have hO : IsOpen O := hg.1.preimage htoI
  have hline : ∀ (a : Coordinates.ComplexCoordinates (Fintype.card I)) (j : Fin (Fintype.card I))
      (ζ : ℂ), toI (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) =
        toI a + ζ • basisVector (e.symm j) := by
    intro a j ζ
    funext i
    by_cases hij : e i = j
    · have : i = e.symm j := by rw [← hij]; simp
      simp [toI, Coordinates.ComplexCoordinates.stdBasisVector, basisVector, this]
    · have : i ≠ e.symm j := fun hc => hij (by rw [hc]; simp)
      simp [toI, Coordinates.ComplexCoordinates.stdBasisVector, basisVector, hij, this]
  have hf : Coordinates.ComplexCoordinates.IsHolomorphicIn O f := by
    refine ⟨hO, continuousOn_pi.2 fun _ => hg.2.1.comp htoI.continuousOn fun z hz => hz, ?_⟩
    intro a ha j
    have hmem : toI a + (0 : ℂ) • basisVector (e.symm j) ∈ Ω := by
      simpa using (show toI a ∈ Ω from ha)
    filter_upwards [eventually_affineLine_mem hg.1 (toI a) (basisVector (e.symm j)) 0 hmem]
      with ζ hζ
    refine differentiableAt_pi.2 fun _ => ?_
    simp only [f, hline]
    exact differentiableAt_coordLine hg (toI a) (e.symm j) hζ
  obtain ⟨-, hsm, hL, -, -⟩ := (H.1 _ O hO).1 1 f hf
  have hmaps : MapsTo toFin Ω O := fun c hc => by
    show toI (toFin c) ∈ Ω
    rwa [hback]
  have hrepr : ∀ c, g c = f (toFin c) 0 := fun c => by simp [f, hback]
  constructor
  · have hfin : ContDiff ℝ ∞ toFin := contDiff_pi.2 fun j => contDiff_apply ℝ ℂ (e.symm j)
    have := ((contDiffOn_pi.1 hsm) 0).comp hfin.contDiffOn hmaps
    exact this.congr fun c _ => hrepr c
  · intro c hc
    obtain ⟨L, hLc⟩ := hL _ (hmaps hc)
    have hdc : DifferentiableAt ℂ f (toFin c) :=
      (hasFDerivAt_of_restrictScalars ℝ hLc rfl).differentiableAt
    have hfin : DifferentiableAt ℂ toFin c :=
      differentiableAt_pi.2 fun j => differentiableAt_apply (e.symm j) c
    have hcomp : DifferentiableAt ℂ (fun c' => f (toFin c') 0) c :=
      (differentiableAt_pi.1 hdc 0).comp c hfin
    exact (hcomp.congr_of_eventuallyEq (Eventually.of_forall hrepr)).differentiableWithinAt
lemma partialDeriv_eq_fderiv {g : (I → ℂ) → F} {c : I → ℂ} (q : I)
    (hd : DifferentiableAt ℂ g c) :
    partialDeriv q g c = fderiv ℂ g c (basisVector q) := by
  have hl : HasDerivAt (fun ζ : ℂ => c + ζ • basisVector q) (basisVector q) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (basisVector q)).const_add c
  have hc0 : HasFDerivAt g (fderiv ℂ g c) (c + (0 : ℂ) • basisVector q) := by
    simpa using hd.hasFDerivAt
  exact (hc0.comp_hasDerivAt 0 hl).deriv
lemma fderiv_real_eq_restrictScalars {g : (I → ℂ) → F} {c : I → ℂ}
    (hd : DifferentiableAt ℂ g c) :
    fderiv ℝ g c = (fderiv ℂ g c).restrictScalars ℝ :=
  (hd.hasFDerivAt.restrictScalars ℝ).fderiv
lemma exists_hasFDerivAt_fderiv_real_apply {Ω : Set (I → ℂ)} {g : (I → ℂ) → ℂ}
    (hΩ : IsOpen Ω) (hs : ContDiffOn ℝ ∞ g Ω) (hd : DifferentiableOn ℂ g Ω) {c : I → ℂ}
    (hc : c ∈ Ω) (v : I → ℂ) :
    ∃ L : (I → ℂ) →L[ℂ] ℂ, HasFDerivAt (fun c' => fderiv ℝ g c' v) L c ∧
      ∀ u, L u = fderiv ℝ (fderiv ℝ g) c u v := by
  have hDs : ContDiffOn ℝ ∞ (fderiv ℝ g) Ω := hs.fderiv_of_isOpen hΩ (by simp)
  have hDc : DifferentiableAt ℝ (fderiv ℝ g) c :=
    (hDs.contDiffAt (hΩ.mem_nhds hc)).differentiableAt (by simp)
  have hsym : IsSymmSndFDerivAt ℝ g c :=
    (hs.contDiffAt (hΩ.mem_nhds hc)).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
  have hCL : ∀ c' ∈ Ω, ∀ w : I → ℂ,
      fderiv ℝ g c' (Complex.I • w) = Complex.I * fderiv ℝ g c' w := by
    intro c' hc' w
    have hd' : DifferentiableAt ℂ g c' := hd.differentiableAt (hΩ.mem_nhds hc')
    rw [fderiv_real_eq_restrictScalars hd']
    simp
  have happ : ∀ w : I → ℂ, HasFDerivAt (fun c' => fderiv ℝ g c' w)
      ((ContinuousLinearMap.apply ℝ ℂ w).comp (fderiv ℝ (fderiv ℝ g) c)) c := fun w =>
    (ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt.comp c hDc.hasFDerivAt
  have hK : ∀ u w : I → ℂ, fderiv ℝ (fderiv ℝ g) c u (Complex.I • w) =
      Complex.I * fderiv ℝ (fderiv ℝ g) c u w := by
    intro u w
    have hA := happ (Complex.I • w)
    have hB := (happ w).const_mul Complex.I
    have hev : (fun c' => fderiv ℝ g c' (Complex.I • w)) =ᶠ[𝓝 c]
        fun c' => Complex.I * fderiv ℝ g c' w := by
      filter_upwards [hΩ.mem_nhds hc] with c' hc' using hCL c' hc' w
    have := congrArg (fun T => T u) ((hA.congr_of_eventuallyEq hev.symm).unique hB)
    simpa using this
  let Lr : (I → ℂ) →L[ℝ] ℂ := (ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ g) c)
  have hLr : ∀ u, Lr u = fderiv ℝ (fderiv ℝ g) c u v := fun u => rfl
  have hI : ∀ u, Lr (Complex.I • u) = Complex.I * Lr u := by
    intro u
    rw [hLr, hLr, hsym (Complex.I • u) v, hK, hsym v u]
  have hsmul : ∀ (z : ℂ) (u : I → ℂ), z • u = z.re • u + z.im • (Complex.I • u) := by
    intro z u
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im z]
    ring
  let Ll : (I → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := Lr
      map_add' := Lr.map_add
      map_smul' := by
        intro z u
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [hsmul z u, map_add, map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im z]
        ring }
  let L : (I → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Ll
  refine ⟨L, hasFDerivAt_of_restrictScalars ℝ (happ v) ?_, fun u => rfl⟩
  ext u
  rfl
lemma partialDeriv_eq_fderiv_real {g : (I → ℂ) → F} {c : I → ℂ} (q : I)
    (hd : DifferentiableAt ℂ g c) :
    partialDeriv q g c = fderiv ℝ g c (basisVector q) := by
  rw [partialDeriv_eq_fderiv q hd, fderiv_real_eq_restrictScalars hd]
  rfl
lemma exists_hasFDerivAt_partialDeriv {Ω : Set (I → ℂ)} {g : (I → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hs : ContDiffOn ℝ ∞ g Ω) (hd : DifferentiableOn ℂ g Ω) {c : I → ℂ} (hc : c ∈ Ω) (q : I) :
    ∃ L : (I → ℂ) →L[ℂ] ℂ, HasFDerivAt (partialDeriv q g) L c ∧
      ∀ u, L u = fderiv ℝ (fderiv ℝ g) c u (basisVector q) := by
  obtain ⟨L, hL, hLu⟩ := exists_hasFDerivAt_fderiv_real_apply hΩ hs hd hc (basisVector q)
  refine ⟨L, hL.congr_of_eventuallyEq ?_, hLu⟩
  filter_upwards [hΩ.mem_nhds hc] with c' hc'
  exact partialDeriv_eq_fderiv_real q (hd.differentiableAt (hΩ.mem_nhds hc'))
lemma holomorphicOfLocallyUniformLimit_holds : HolomorphicOfLocallyUniformLimit := by
  intro I _ _ Ω hΩ gs g hhol hloc
  refine ⟨hΩ, fun c hc => ?_, fun c hc q => ?_⟩
  · obtain ⟨O, hO, hcO, hOΩ, hun⟩ := hloc c hc
    have hcont : ContinuousOn g O := hun.continuousOn
      (Eventually.of_forall fun k => (hhol k).2.1.mono hOΩ).frequently
    exact (hcont.continuousAt (hO.mem_nhds hcO)).continuousWithinAt
  · let line : ℂ → I → ℂ := fun ζ => c + ζ • basisVector q
    have hline : Continuous line := (differentiable_affineLine c (basisVector q)).continuous
    let U : Set ℂ := line ⁻¹' Ω
    have hU : IsOpen U := hΩ.preimage hline
    have hlim : TendstoLocallyUniformlyOn (fun k ζ => gs k (line ζ)) (fun ζ => g (line ζ)) atTop
        U := by
      intro u hu ζ hζ
      obtain ⟨O, hO, hcO, -, hun⟩ := hloc (line ζ) hζ
      exact ⟨line ⁻¹' O, mem_nhdsWithin_of_mem_nhds ((hO.preimage hline).mem_nhds hcO),
        (hun u hu).mono fun k hk y hy => hk _ hy⟩
    have hdiff : DifferentiableOn ℂ (fun ζ => g (line ζ)) U := hlim.differentiableOn
      (Eventually.of_forall fun k ζ hζ =>
        (differentiableAt_coordLine (hhol k) c q hζ).differentiableWithinAt) hU
    have h0 : (0 : ℂ) ∈ U := by simpa [U, line] using hc
    filter_upwards [hU.mem_nhds h0] with ζ hζ
    exact hdiff.differentiableAt (hU.mem_nhds hζ)
lemma partialDerivsHolomorphicAndCommute_holds
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    PartialDerivsHolomorphicAndCommute := by
  intro I _ _ Ω hΩ g hg
  obtain ⟨hs, hd⟩ := contDiffOn_and_differentiableOn H hg
  refine ⟨fun q => isHolomorphicOnOpen_of_differentiableOn hΩ fun c hc => ?_,
    fun q q' c hc => ?_⟩
  · obtain ⟨L, hL, -⟩ := exists_hasFDerivAt_partialDeriv hΩ hs hd hc q
    exact hL.differentiableAt.differentiableWithinAt
  · obtain ⟨L, hL, hLu⟩ := exists_hasFDerivAt_partialDeriv hΩ hs hd hc q'
    obtain ⟨L', hL', hLu'⟩ := exists_hasFDerivAt_partialDeriv hΩ hs hd hc q
    have hsym : IsSymmSndFDerivAt ℝ g c :=
      (hs.contDiffAt (hΩ.mem_nhds hc)).isSymmSndFDerivAt
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
    rw [partialDeriv_eq_fderiv q hL.differentiableAt, hL.fderiv, hLu,
      partialDeriv_eq_fderiv q' hL'.differentiableAt, hL'.fderiv, hLu']
    exact hsym _ _
lemma differentiable_mvPolynomial_eval (P : MvPolynomial I ℂ) :
    Differentiable ℂ fun c : I → ℂ => MvPolynomial.eval c P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    simp only [map_add]
    exact hp.add hr
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (differentiable_apply i)
lemma mvPolynomialEvalIsEntire_holds : MvPolynomialEvalIsEntire := fun _ _ _ P =>
  isHolomorphicOnOpen_of_differentiableOn isOpen_univ
    (differentiable_mvPolynomial_eval P).differentiableOn
lemma addMulDivHolomorphic_holds
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    AddMulDivHolomorphic := by
  intro I _ _ Ω hΩ g₁ g₂ hg₁ hg₂
  have hd₁ := (contDiffOn_and_differentiableOn H hg₁).2
  have hd₂ := (contDiffOn_and_differentiableOn H hg₂).2
  refine ⟨isHolomorphicOnOpen_of_differentiableOn hΩ (hd₁.add hd₂),
    isHolomorphicOnOpen_of_differentiableOn hΩ (hd₁.mul hd₂),
    fun hz => isHolomorphicOnOpen_of_differentiableOn hΩ ?_⟩
  have hq : DifferentiableOn ℂ (fun c => g₁ c * (g₂ c)⁻¹) Ω := hd₁.mul (hd₂.inv hz)
  simpa only [div_eq_mul_inv] using hq
omit [Fintype I] in
lemma isHolomorphicOnOpen_apply {J : Type} [Fintype J] {Ω : Set (I → ℂ)}
    {Ψ : (I → ℂ) → J → ℂ} (hΨ : IsHolomorphicOnOpen Ω Ψ) (j : J) :
    IsHolomorphicOnOpen Ω fun c => Ψ c j := by
  refine ⟨hΨ.1, (continuous_apply j).comp_continuousOn hΨ.2.1, fun c hc q => ?_⟩
  filter_upwards [hΨ.2.2 c hc q] with ζ hζ
  exact differentiableAt_pi.1 hζ j
lemma clm_apply_eq_sum_basisVector {J : Type} [Fintype J] (L : (J → ℂ) →L[ℂ] ℂ) (ξ : J → ℂ) :
    L ξ = ∑ j, L (basisVector j) * ξ j := by
  classical
  have hξ : ξ = ∑ j, ξ j • basisVector j := by
    funext i
    simp [Finset.sum_apply, basisVector]
  conv_lhs => rw [hξ]
  simp [map_sum, mul_comm]
lemma compHolomorphicAndChainRule_holds
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    CompHolomorphicAndChainRule := by
  intro I _ _ Ω hΩ J _ _ Ω' hΩ' Ψ g hΨ hmaps hg
  have hdΨ : DifferentiableOn ℂ Ψ Ω := differentiableOn_pi.2 fun j =>
    (contDiffOn_and_differentiableOn H (isHolomorphicOnOpen_apply hΨ j)).2
  have hdg : DifferentiableOn ℂ g Ω' := (contDiffOn_and_differentiableOn H hg).2
  have hcomp : DifferentiableOn ℂ (fun c => g (Ψ c)) Ω := hdg.comp hdΨ hmaps
  refine ⟨isHolomorphicOnOpen_of_differentiableOn hΩ hcomp, fun c hc q => ?_⟩
  have hΨc : DifferentiableAt ℂ Ψ c := hdΨ.differentiableAt (hΩ.mem_nhds hc)
  have hgc : DifferentiableAt ℂ g (Ψ c) := hdg.differentiableAt (hΩ'.mem_nhds (hmaps hc))
  have hmember : ∀ j, partialDeriv q (fun c' => Ψ c' j) c =
      fderiv ℂ Ψ c (basisVector q) j := by
    intro j
    have hq : HasFDerivAt (fun c' => Ψ c' j)
        ((ContinuousLinearMap.proj j : (J → ℂ) →L[ℂ] ℂ).comp (fderiv ℂ Ψ c)) c :=
      (ContinuousLinearMap.proj j : (J → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp c hΨc.hasFDerivAt
    rw [partialDeriv_eq_fderiv q hq.differentiableAt, hq.fderiv]
    rfl
  have hchain : fderiv ℂ (fun c' => g (Ψ c')) c =
      (fderiv ℂ g (Ψ c)).comp (fderiv ℂ Ψ c) := (hgc.hasFDerivAt.comp c hΨc.hasFDerivAt).fderiv
  rw [partialDeriv_eq_fderiv q (hcomp.differentiableAt (hΩ.mem_nhds hc)), hchain,
    ContinuousLinearMap.comp_apply, clm_apply_eq_sum_basisVector]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDeriv_eq_fderiv j hgc, hmember]
lemma partialDerivRealOfReal_holds : PartialDerivRealOfReal := by
  intro I _ _ Ω hΩ g hg hreal q c hc
  have hc0 : c + (0 : ℂ) • basisVector q ∈ Ω := by simpa using hc.1
  have hder : HasDerivAt (fun ζ : ℂ => g (c + ζ • basisVector q)) (partialDeriv q g c) 0 :=
    (differentiableAt_coordLine hg c q hc0).hasDerivAt
  have hreal' : HasDerivAt (fun t : ℝ => g (c + (t : ℂ) • basisVector q))
      (partialDeriv q g c) 0 := by
    simpa using hder.comp_ofReal
  have him : HasDerivAt (fun t : ℝ => (g (c + (t : ℂ) • basisVector q)).im)
      (partialDeriv q g c).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hreal'
  have hev : (fun t : ℝ => (g (c + (t : ℂ) • basisVector q)).im) =ᶠ[𝓝 0] fun _ => 0 := by
    have hcont : Continuous fun t : ℝ => c + (t : ℂ) • basisVector q :=
      (differentiable_affineLine c (basisVector q)).continuous.comp Complex.continuous_ofReal
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, c + (t : ℂ) • basisVector q ∈ Ω :=
      hcont.continuousAt.eventually (hΩ.mem_nhds (by simpa using hc.1))
    filter_upwards [hmem] with t ht
    refine hreal _ ⟨ht, fun j => ?_⟩
    have hj := hc.2 j
    by_cases hjq : j = q <;> simp [basisVector, hjq, hj]
    simpa [hjq] using hc.2 q
  exact (hev.hasDerivAt_iff.1 him).unique (hasDerivAt_const 0 0)
lemma logSeries_eq_log {u : ℂ} (hu : u ∈ disc 1 1) : logSeries u = Complex.log u := by
  have hz : ‖1 - u‖ < 1 := by simpa [disc, norm_sub_rev] using hu
  have hsum := Complex.hasSum_taylorSeries_neg_log hz
  have hshift : HasSum (fun k : ℕ => ((k : ℂ) + 1)⁻¹ * (1 - u) ^ (k + 1)) (-Complex.log u) := by
    have := (hasSum_nat_add_iff' 1).2 hsum
    simpa [div_eq_inv_mul] using this
  rw [logSeries, hshift.tsum_eq, neg_neg]
lemma isOpen_disc_one_one : IsOpen (disc 1 1) := by apply _root_.YangMills.Construction.SourcesAndGluing.isOpen_unitDiscAtOne <;> assumption
lemma mem_slitPlane_of_mem_disc {u : ℂ} (hu : u ∈ disc 1 1) : u ∈ Complex.slitPlane := by
  have hn : ‖u - 1‖ < 1 := hu
  have hre : |(u - 1).re| ≤ ‖u - 1‖ := Complex.abs_re_le_norm _
  have : 0 < u.re := by
    have := abs_lt.1 (hre.trans_lt hn)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith [this.1]
  exact Or.inl this
lemma logSeriesProperties_holds : LogSeriesProperties := by
  have hd : DifferentiableOn ℂ logSeries (disc 1 1) := fun u hu =>
    ((Complex.differentiableAt_log (mem_slitPlane_of_mem_disc hu)).congr_of_eventuallyEq
      (by
        filter_upwards [isOpen_disc_one_one.mem_nhds hu] with w hw using
          logSeries_eq_log hw)).differentiableWithinAt
  have hopen : IsOpen {c : Unit → ℂ | c () ∈ disc 1 1} :=
    isOpen_disc_one_one.preimage (continuous_apply ())
  have h1 : (1 : ℂ) ∈ disc 1 1 := by simp [disc]
  refine ⟨hd, ?_, fun u hu => ?_, ?_, fun t ht₀ ht₂ => ?_⟩
  · refine isHolomorphicOnOpen_of_differentiableOn hopen ?_
    exact hd.comp (differentiable_apply ()).differentiableOn fun c hc => hc
  · rw [logSeries_eq_log hu]
    exact Complex.exp_log (mem_slitPlane_of_mem_disc hu |> Complex.slitPlane_ne_zero)
  · rw [logSeries_eq_log h1, Complex.log_one]
  · have ht : (t : ℂ) ∈ disc 1 1 := by
      have : ‖(t : ℂ) - 1‖ < 1 := by
        rw [show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      exact this
    rw [logSeries_eq_log ht, ← Complex.ofReal_log ht₀.le, Complex.ofReal_im]
theorem statement_of_powerSeriesHolomorphy
    (H : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Statement :=
  ⟨holomorphicOfLocallyUniformLimit_holds, partialDerivsHolomorphicAndCommute_holds H,
    mvPolynomialEvalIsEntire_holds, addMulDivHolomorphic_holds H,
    compHolomorphicAndChainRule_holds H, partialDerivRealOfReal_holds, logSeriesProperties_holds⟩
end YangMills.Construction.SeveralComplexVariables.HolomorphicCalculus
