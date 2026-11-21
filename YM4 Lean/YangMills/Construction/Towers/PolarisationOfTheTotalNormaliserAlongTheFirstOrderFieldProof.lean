import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.Towers.DifferentialOfTheCompositeOfTheCriticalBranchProof
import YangMills.Construction.Towers.DifferentialsOfRealAnalyticMapsProof
import YangMills.Construction.Towers.FirstDifferentialInTheExponentialChartVanishes
import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalyticProof
import YangMills.Construction.Towers.PolarisationOfTheTotalNormaliserAlongTheFirstOrderField
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.RelationsOfTheResponseOnTheTorus
import YangMills.Construction.Towers.RepresentationOfTheLogarithmOfTheTotalNormaliser
import YangMills.Construction.Towers.SecondDifferentialInTheLeftChart
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalAndItsComplexExtension
import YangMills.Construction.Towers.TheProductOfTheNormalisers
import YangMills.Construction.Towers.TheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter Asymptotics
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.NormaliserHessianAlongLinearizedField
open YangMills.Construction.Matrices
theorem isLittleO_sub_taylor_two {φ : ℝ → ℝ} (h₁ : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ φ t)
    (h₂ : DifferentiableAt ℝ (deriv φ) 0) :
    (fun t : ℝ => φ t - (φ 0 + deriv φ 0 * t + t ^ 2 / 2 * deriv (deriv φ) 0)) =o[𝓝 0]
      fun t : ℝ => t ^ 2 := by
  set a := deriv φ 0 with ha
  set c := deriv (deriv φ) 0 with hc
  have hlin : (fun h : ℝ => deriv φ h - a - h * c) =o[𝓝 0] fun h : ℝ => h := by
    have h := hasDerivAt_iff_isLittleO_nhds_zero.1 h₂.hasDerivAt
    simpa [smul_eq_mul] using h
  rw [isLittleO_iff]
  intro ε hε
  have hb := (isLittleO_iff.1 hlin) hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h₁.and hb)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
  have htδ : |t| < δ := by simpa [Real.dist_eq] using ht
  have hts : ∀ x ∈ uIcc (0 : ℝ) t, |x| ≤ |t| := by
    intro x hx
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hx
      rw [abs_of_nonneg hx.1, abs_of_nonneg h]
      exact hx.2
    · rw [uIcc_of_ge h] at hx
      rw [abs_of_nonpos hx.2, abs_of_nonpos h]
      linarith [hx.1]
  have hnear : ∀ x ∈ uIcc (0 : ℝ) t, dist x 0 < δ := fun x hx => by
    rw [Real.dist_eq, sub_zero]
    exact (hts x hx).trans_lt htδ
  let g : ℝ → ℝ := fun x => φ x - (φ 0 + a * x + x ^ 2 / 2 * c)
  have hg : ∀ x ∈ uIcc (0 : ℝ) t,
      HasDerivWithinAt g (deriv φ x - a - x * c) (uIcc (0 : ℝ) t) x := by
    intro x hx
    have hd := (hball (hnear x hx)).1
    have h3 : HasDerivAt (fun x : ℝ => φ 0 + a * x + x ^ 2 / 2 * c) (a + x * c) x := by
      have h4 : HasDerivAt (fun x : ℝ => x ^ 2 / 2 * c) (x * c) x := by
        have h5 := (((hasDerivAt_id x).pow 2).div_const 2).mul_const c
        refine h5.congr_deriv ?_
        simp
      have h6 : HasDerivAt (fun x : ℝ => φ 0 + a * x) a x := by
        have h7 := ((hasDerivAt_id x).const_mul a).const_add (φ 0)
        simpa using h7
      exact h6.add h4
    have h8 := hd.hasDerivAt.sub h3
    exact (h8.congr_deriv (by ring)).hasDerivWithinAt
  have hbound : ∀ x ∈ uIcc (0 : ℝ) t, ‖deriv φ x - a - x * c‖ ≤ ε * |t| := by
    intro x hx
    have h := (hball (hnear x hx)).2
    rw [Real.norm_eq_abs x] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hts x hx) hε.le)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound (convex_uIcc 0 t)
    left_mem_uIcc right_mem_uIcc
  have hg0 : g 0 = 0 := by simp [g]
  have hgt : g t = φ t - (φ 0 + a * t + t ^ 2 / 2 * c) := rfl
  rw [hg0, sub_zero, sub_zero, hgt, Real.norm_eq_abs t] at hm
  rw [Real.norm_eq_abs (t ^ 2), abs_pow, sq_abs]
  calc _ ≤ ε * |t| * |t| := hm
    _ = ε * t ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring
theorem eq_zero_of_linear_add_quadratic_isLittleO {α d : ℝ}
    (h : (fun t : ℝ => α * t + t ^ 2 / 2 * d) =o[𝓝 0] fun t : ℝ => t ^ 2) : d = 0 := by
  by_contra hd
  have hpos : 0 < |d| / 4 := by positivity
  have hb := (isLittleO_iff.1 h) hpos
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℝ)).tendsto 0
  have hb' := hneg.eventually hb
  have hex : ∃ t : ℝ, t ≠ 0 ∧ ‖α * t + t ^ 2 / 2 * d‖ ≤ |d| / 4 * ‖t ^ 2‖ ∧
      ‖α * -t + (-t) ^ 2 / 2 * d‖ ≤ |d| / 4 * ‖(-t) ^ 2‖ := by
    have h₁ := (hb.and hb').filter_mono (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    have h₂ : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := eventually_mem_nhdsWithin
    obtain ⟨t, ht₁, ht₂⟩ := (h₁.and h₂).exists
    exact ⟨t, ht₂, ht₁.1, ht₁.2⟩
  obtain ⟨t, ht, h₁, h₂⟩ := hex
  have ht2 : 0 < t ^ 2 := by positivity
  have hsum : t ^ 2 * d = (α * t + t ^ 2 / 2 * d) + (α * -t + t ^ 2 / 2 * d) := by ring
  have habs : |t ^ 2 * d| ≤ |d| / 2 * t ^ 2 := by
    rw [hsum]
    refine (abs_add_le _ _).trans ?_
    simp only [Real.norm_eq_abs, neg_sq, abs_pow, sq_abs] at h₁ h₂
    linarith
  rw [abs_mul, abs_of_pos ht2] at habs
  nlinarith
theorem deriv_coe_comp (φ : ℝ → ℝ) (x : ℝ) :
    deriv (fun t => (φ t : ℂ)) x = ((deriv φ x : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.ProlongDifferential.deriv_ofReal_comp_eq <;> assumption
theorem differentiableAt_of_coe_comp {φ : ℝ → ℝ} {x : ℝ}
    (h : DifferentiableAt ℝ (fun t => (φ t : ℂ)) x) : DifferentiableAt ℝ φ x := by
  have h₂ := Complex.reCLM.differentiableAt.comp x h
  simpa [Function.comp_def] using h₂
section Reindexing
variable {σ τ : Type} [Fintype σ] [Fintype τ]
def chartOfEquiv (e : σ ≃ τ) (c : EmbeddedSubmanifold.Chart (specialUnitaryPower τ)) :
    EmbeddedSubmanifold.Chart (specialUnitaryPower σ) where
  dim := c.dim
  source := c.source
  param := fun u => c.param u ∘ e
  isOpen_source := c.isOpen_source
  contDiffOn_param :=
    contDiffOn_pi.2 fun s => contDiffOn_pi.1 c.contDiffOn_param (e s)
  injective_fderiv_param := by
    intro u hu
    let R : (τ → ComplexMatrix2) →L[ℝ] (σ → ComplexMatrix2) :=
      ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (e s)
    have hd : DifferentiableAt ℝ c.param u :=
      (c.contDiffOn_param.contDiffAt (c.isOpen_source.mem_nhds hu)).differentiableAt
        (by simp)
    have hR : HasFDerivAt (fun u => c.param u ∘ e)
        (R.comp (fderiv ℝ c.param u)) u :=
      R.hasFDerivAt.comp u hd.hasFDerivAt
    rw [hR.fderiv]
    intro x y hxy
    apply c.injective_fderiv_param u hu
    funext t
    have h := congrFun hxy (e.symm t)
    simpa [R] using h
  injOn_param := by
    intro u hu v hv h
    apply c.injOn_param hu hv
    funext t
    have h' := congrFun h (e.symm t)
    simpa using h'
  isRelativelyOpen_image := by
    intro W hW hWo
    obtain ⟨O, hO, hE⟩ := c.isRelativelyOpen_image W hW hWo
    have hcont : Continuous fun w : σ → ComplexMatrix2 => w ∘ e.symm :=
      continuous_pi fun t => continuous_apply _
    refine ⟨(fun w : σ → ComplexMatrix2 => w ∘ e.symm) ⁻¹' O, hO.preimage hcont, ?_⟩
    ext w
    have hw : (∃ u ∈ W, c.param u ∘ e = w) ↔
        w ∘ e.symm ∈ c.param '' W := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by funext t; simp⟩
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu, by rw [h]; funext s; simp⟩
    have hM : w ∘ e.symm ∈ specialUnitaryPower τ ↔ w ∈ specialUnitaryPower σ := by
      constructor
      · intro h s
        have h' := h (e s)
        simpa using h'
      · intro h t
        exact h (e.symm t)
    simp only [mem_image, mem_inter_iff, mem_preimage]
    rw [hw, hE]
    simp only [mem_inter_iff, hM]
theorem hasDifferentiablePartialsOn_comp_equiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : σ ≃ τ) {O : Set (σ → ComplexMatrix2)} {g : (σ → ComplexMatrix2) → F}
    (h : EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower σ) O g) :
    EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower τ)
      {w | w ∘ e ∈ O} fun w => g (w ∘ e) := by
  obtain ⟨⟨⟨O₀, hO₀, hE⟩, hd⟩, hd₂⟩ := h
  refine ⟨⟨⟨(fun w : τ → ComplexMatrix2 => w ∘ e) ⁻¹' O₀,
    hO₀.preimage (continuous_pi fun s => continuous_apply _), ?_⟩,
    fun c => hd (chartOfEquiv e c)⟩, fun c k => ?_⟩
  · ext w
    have hM : w ∘ e ∈ specialUnitaryPower σ ↔ w ∈ specialUnitaryPower τ := by
      constructor
      · intro h t
        have h' := h (e.symm t)
        simpa using h'
      · intro h s
        exact h (e s)
    simp only [mem_ofPred_eq, hE, mem_inter_iff, mem_preimage, hM]
  · exact hd₂ (chartOfEquiv e c) k
end Reindexing
section SecondDerivative
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem fieldOfPositiveValues_restrict_expTwist (A U : Edge L n k j → ComplexMatrix2) :
    fieldOfPositiveValues (restrictToPositiveEdges (PeriodicLattice.expTwist A U)) =
      PeriodicLattice.expTwist A U := by apply _root_.YangMills.SharedProofs.p25947 <;> assumption
theorem restrictToPositiveEdges_expTwist (A U : Edge L n k j → ComplexMatrix2)
    (b : PositiveEdge L n k j) :
    restrictToPositiveEdges (PeriodicLattice.expTwist A U) b =
      ComplexMatrix2.matExp (Complex.I • A b.1) * U b.1 := by
  simp only [restrictToPositiveEdges, PeriodicLattice.expTwist, if_pos b.2]
theorem leftSecondDeriv_coe (F : (Edge L n k j → ComplexMatrix2) → ℝ)
    (U B B' : Edge L n k j → ComplexMatrix2) :
    leftSecondDeriv (fun W => (F W : ℂ)) U B B' = ((leftSecondDeriv F U B B' : ℝ) : ℂ) := by
  simp only [leftSecondDeriv, mixedDirectionalDeriv, deriv_coe_comp]
theorem leftSecondDeriv_self_eq_deriv_deriv (F : (Edge L n k j → ComplexMatrix2) → ℝ)
    (U B : Edge L n k j → ComplexMatrix2) :
    leftSecondDeriv F U B B =
      deriv (deriv fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B) U)) 0 := by
  have hline : ∀ s t : ℝ, (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) = ((s + t : ℝ) : ℂ) • B := by
    intro s t
    rw [← add_smul]
    congr 1
    simp
  simp only [leftSecondDeriv, mixedDirectionalDeriv, hline]
  congr 1
  funext s
  have h := deriv_comp_const_add (f := fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B) U)) s 0
  simpa using h
structure HessianFacts (F : (Edge L n k j → ComplexMatrix2) → ℝ) : Prop where
  symm : ∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
    leftSecondDeriv F (trivialField L n k j) B B' =
      leftSecondDeriv F (trivialField L n k j) B' B
  add_left : ∀ B₁ ∈ edgeFormSpace L n k j, ∀ B₂ ∈ edgeFormSpace L n k j,
    ∀ B' ∈ edgeFormSpace L n k j,
    leftSecondDeriv F (trivialField L n k j) (B₁ + B₂) B' =
      leftSecondDeriv F (trivialField L n k j) B₁ B' +
        leftSecondDeriv F (trivialField L n k j) B₂ B'
  differentiableAt_near : ∀ B ∈ edgeFormSpace L n k j, ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ
    (fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j))) t
  differentiableAt_deriv : ∀ B ∈ edgeFormSpace L n k j, DifferentiableAt ℝ
    (deriv fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j))) 0
theorem hessianFacts_of_analytic (hS : LeftChartSecondDerivative.MainStatement)
    (hN : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h𝒰 : IsOpenNhdOfOne 𝒰) {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) : HessianFacts F := by
  have hFc : IsAnalyticComplexFieldFunction 𝒰 (fun W => (F W : ℂ)) := hF
  obtain ⟨-, -, ⟨-, fin, htw⟩, hpt⟩ := (hN L n k j j hL hn hj hj 𝒰 h𝒰.1).1 _ hFc
  let _ := fin
  have hpos : Nonempty (PositiveEdge L n k j) := by
    let b : Edge L n k j := PeriodicLattice.Bond.forwardFrom 0 0
    rcases isPositivelyOriented_or_opposite b with h | h
    · exact ⟨⟨b, h⟩⟩
    · exact ⟨⟨b.opposite, h⟩⟩
  let e := Fintype.equivFin (PositiveEdge L n k j)
  let N := Fintype.card (PositiveEdge L n k j)
  have hN1 : 1 ≤ N := Fintype.card_pos
  let bs : Fin N → PositiveEdge L n k j := e.symm
  let f : (Fin N → ComplexMatrix2) → ℂ := fun w => ((F (fieldOfPositiveValues (w ∘ e)) : ℝ) : ℂ)
  let O : Set (Fin N → ComplexMatrix2) := {w | w ∘ e ∈ restrictToPositiveEdges '' 𝒰}
  have htw' : EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower (Fin N)) O f :=
    hasDifferentiablePartialsOn_comp_equiv e htw
  have hone : trivialField L n k j ∈ fieldSpace L n k j := h𝒰.1.1 h𝒰.2
  have hmem : (fun i => trivialField L n k j (((fun b : PositiveEdge L n k j => b.1) ∘ bs) i))
      ∈ O := ⟨trivialField L n k j, h𝒰.2, rfl⟩
  have hfacts := ((hS L k j N hL hj hN1).1 n hn bs).2.1 O f htw'.1.1 htw' _ hone hmem
  have hval : LeftChartSecondDerivative.chartValue f ((fun b : PositiveEdge L n k j => b.1) ∘ bs)
      (trivialField L n k j) = fun X =>
        ((F (PeriodicLattice.expTwist X (trivialField L n k j)) : ℝ) : ℂ) := by
    funext X
    show ((F (fieldOfPositiveValues (LeftChartSecondDerivative.chartPoint _ _ X ∘ e)) : ℝ) : ℂ) = _
    have hp : LeftChartSecondDerivative.chartPoint ((fun b : PositiveEdge L n k j => b.1) ∘ bs)
        (trivialField L n k j) X ∘ e =
        restrictToPositiveEdges (PeriodicLattice.expTwist X (trivialField L n k j)) := by
      funext p
      rw [restrictToPositiveEdges_expTwist]
      simp [LeftChartSecondDerivative.chartPoint, bs]
    rw [hp, fieldOfPositiveValues_restrict_expTwist]
  have hmix : ∀ B B', LeftChartSecondDerivative.mixedAt ℝ f
      ((fun b : PositiveEdge L n k j => b.1) ∘ bs) (trivialField L n k j) B B' =
      ((leftSecondDeriv F (trivialField L n k j) B B' : ℝ) : ℂ) := by
    intro B B'
    rw [← leftSecondDeriv_coe]
    unfold LeftChartSecondDerivative.mixedAt
    rw [hval]
    rfl
  obtain ⟨-, hadd, -, hsym, -⟩ := hfacts
  have hline : ∀ (B : Edge L n k j → ComplexMatrix2) (s t : ℝ),
      (s : ℂ) • B + (t : ℂ) • B = ((s + t : ℝ) : ℂ) • B := by
    intro B s t
    rw [← add_smul]
    congr 1
    simp
  have hsecond := fun B (hB : B ∈ edgeFormSpace L n k j) => (hpt _ h𝒰.2).2 B hB B hB
  simp only [hline] at hsecond
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB B' hB'
    apply Complex.ofReal_injective
    rw [← hmix, ← hmix]
    exact hsym B hB B' hB'
  · intro B₁ hB₁ B₂ hB₂ B' hB'
    apply Complex.ofReal_injective
    have h := hadd B₁ hB₁ B₂ hB₂ B' hB' 1
    simp only [map_one, one_smul] at h
    rw [hmix, hmix, hmix] at h
    exact_mod_cast h
  · intro B hB
    filter_upwards [(hsecond B hB).1] with s hs
    apply differentiableAt_of_coe_comp
    have h₁ := DifferentiableAt.comp (x := s) (f := fun u : ℝ => u - s)
      (g := fun t : ℝ => ((F (PeriodicLattice.expTwist (((s + t : ℝ) : ℂ) • B)
        (trivialField L n k j)) : ℝ) : ℂ)) (by simpa using hs)
      (differentiableAt_id.sub_const s)
    simpa [Function.comp_def] using h₁
  · intro B hB
    have h₂ := (hsecond B hB).2
    have hfun : (fun s : ℝ => deriv (fun t : ℝ => ((F (PeriodicLattice.expTwist
        (((s + t : ℝ) : ℂ) • B) (trivialField L n k j)) : ℝ) : ℂ)) 0) =
        fun s : ℝ => ((deriv (fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B)
          (trivialField L n k j))) s : ℝ) : ℂ) := by
      funext s
      rw [deriv_coe_comp]
      have h := deriv_comp_const_add
        (f := fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B)
          (trivialField L n k j))) s 0
      simp only [add_zero] at h
      rw [h]
    rw [hfun] at h₂
    exact differentiableAt_of_coe_comp h₂
end SecondDerivative
section Coefficients
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
theorem exists_re_pauliCoeff_clm (a : Fin 3) :
    ∃ P : ComplexMatrix2 →L[ℝ] ℝ, ∀ X ∈ ComplexMatrix2.traceless, P X = (pauliCoeff a X).re := by
  obtain ⟨g, hg⟩ :=
    (ComplexMatrix2.traceless.subtype).exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let T : ComplexMatrix2 →ₗ[ℂ] ℂ :=
    (LinearMap.proj a : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ OneLoop.pauliCoordinateEquiv.toLinearMap ∘ₗ g
  let P₀ : ComplexMatrix2 →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ T.restrictScalars ℝ
  refine ⟨LinearMap.toContinuousLinearMap P₀, fun X hX => ?_⟩
  have hgX : g X = ⟨X, hX⟩ := LinearMap.congr_fun hg ⟨X, hX⟩
  simp [P₀, T, hgX, pauliCoeff, hX]
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
variable {L n k j : ℕ}
theorem hasDerivAt_re_toPauliCoeffs {χ : ℝ → edgeFormSpace L n k j} {d : edgeFormSpace L n k j}
    (h : ∀ b : PositiveEdge L n k j, HasDerivAt (fun t => (χ t : Edge L n k j → ComplexMatrix2) b.1)
      ((d : Edge L n k j → ComplexMatrix2) b.1) 0) (ι : Fin 3 × PositiveEdge L n k j) :
    HasDerivAt
      (fun t => (toPauliCoeffs (restrictToPositiveEdges (χ t : Edge L n k j → ComplexMatrix2)) ι).re)
      (toPauliCoeffs (restrictToPositiveEdges (d : Edge L n k j → ComplexMatrix2)) ι).re 0 := by
  obtain ⟨P, hP⟩ := exists_re_pauliCoeff_clm ι.1
  have hform : ∀ x : edgeFormSpace L n k j, P ((x : Edge L n k j → ComplexMatrix2) ι.2.1) =
      (toPauliCoeffs (restrictToPositiveEdges (x : Edge L n k j → ComplexMatrix2)) ι).re :=
    fun x => hP _ (mem_traceless_of_mem_hermitianTraceless (x.2.1 _ ι.2.2))
  have h₁ := P.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h ι.2)
  rw [← hform d]
  exact h₁.congr_of_eventuallyEq (Eventually.of_forall fun t => (hform (χ t)).symm)
theorem hasDerivAt_fieldTripleCoords [Fintype (PositiveEdge L n k 0)]
    [Fintype (PositiveEdge L n k k)]
    {γ : ℝ → FieldTriple L n k} {γ₁ : FieldTriple L n k}
    (h₁ : ∀ b : PositiveEdge L n k 0, HasDerivAt
      (fun t => ((γ t).1 : Edge L n k 0 → ComplexMatrix2) b.1)
      ((γ₁.1 : Edge L n k 0 → ComplexMatrix2) b.1) 0)
    (h₂ : ∀ b : PositiveEdge L n k 0, HasDerivAt
      (fun t => ((γ t).2.1 : Edge L n k 0 → ComplexMatrix2) b.1)
      ((γ₁.2.1 : Edge L n k 0 → ComplexMatrix2) b.1) 0)
    (h₃ : ∀ b : PositiveEdge L n k k, HasDerivAt
      (fun t => ((γ t).2.2 : Edge L n k k → ComplexMatrix2) b.1)
      ((γ₁.2.2 : Edge L n k k → ComplexMatrix2) b.1) 0) :
    HasDerivAt (fun t => fieldTripleCoords (γ t)) (fieldTripleCoords γ₁) 0 := by
  refine hasDerivAt_pi.2 ?_
  rintro (ι | ι | ι)
  · exact hasDerivAt_re_toPauliCoeffs (χ := fun t => (γ t).1) h₁ ι
  · exact hasDerivAt_re_toPauliCoeffs (χ := fun t => (γ t).2.1) h₂ ι
  · exact hasDerivAt_re_toPauliCoeffs (χ := fun t => (γ t).2.2) h₃ ι
theorem edgeForm_ext {B B' : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) (h : ∀ b, b.IsPositivelyOriented → B b = B' b) :
    B = B' := by apply _root_.YangMills.SharedProofs.p88895 <;> assumption
theorem not_isPositivelyOriented_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
end Coefficients
section Logarithm
variable {L n k j : ℕ}
def logEdgeForm (U : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  edgeFormOfPositiveValues fun p => Complex.I⁻¹ • ComplexMatrix2.logSeries (U p.1)
theorem logSeries_mem_and_exp (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ PeriodicLattice.compactGaugeGroup) (h1 : ComplexMatrix2.operatorNorm (A - 1) < 1) :
    Complex.I⁻¹ • ComplexMatrix2.logSeries A ∈ ComplexMatrix2.hermitianTraceless ∧
      ComplexMatrix2.matExp (Complex.I • (Complex.I⁻¹ • ComplexMatrix2.logSeries A)) = A := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hE
  have hS : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := hA
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hS
  obtain ⟨H, -, hlog, -, hexp, -, hdet⟩ := h8 A hu h1
  obtain ⟨-, hH, -⟩ := hdet hd
  have e : Complex.I⁻¹ • ComplexMatrix2.logSeries A = H := by
    rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  rw [e]
  exact ⟨hH, hexp⟩
theorem logEdgeForm_of_pos (U : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    logEdgeForm U b = Complex.I⁻¹ • ComplexMatrix2.logSeries (U b) := by
  simp only [logEdgeForm, edgeFormOfPositiveValues, dif_pos hb]
theorem logEdgeForm_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (hr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j)
    (h1 : ∀ p : PositiveEdge L n k j, ComplexMatrix2.operatorNorm (U p.1 - 1) < 1) :
    logEdgeForm U ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [logEdgeForm_of_pos U hb]
    exact (logSeries_mem_and_exp hE (hU.1 b (mem_univ _)) (h1 ⟨b, hb⟩)).1
  · by_cases hb : b.IsPositivelyOriented
    · have hr' := hr b hb
      have hrr : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [logEdgeForm, edgeFormOfPositiveValues, dif_pos hb, dif_neg hr', dif_pos hrr]
      rfl
    · have hr' := (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [logEdgeForm, edgeFormOfPositiveValues, dif_pos hr', dif_neg hb, neg_neg]
theorem expGaugeField_logEdgeForm (hE : ComplexMatrix2.ExpLogEstimates)
    {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j)
    (h1 : ∀ p : PositiveEdge L n k j, ComplexMatrix2.operatorNorm (U p.1 - 1) < 1) :
    PeriodicLattice.expGaugeField (logEdgeForm U) = U := by
  funext b
  show ComplexMatrix2.matExp (Complex.I • logEdgeForm U b) = U b
  by_cases hb : b.IsPositivelyOriented
  · rw [logEdgeForm_of_pos U hb]
    exact (logSeries_mem_and_exp hE (hU.1 b (mem_univ _)) (h1 ⟨b, hb⟩)).2
  · have hr' := (isPositivelyOriented_or_opposite b).resolve_left hb
    have e : logEdgeForm U b = -(Complex.I⁻¹ • ComplexMatrix2.logSeries (U b.opposite)) := by
      simp only [logEdgeForm, edgeFormOfPositiveValues, dif_neg hb, dif_pos hr']
    have hexp := (logSeries_mem_and_exp hE (hU.1 _ (mem_univ _)) (h1 ⟨_, hr'⟩)).2
    have hinv : U b = (U b.opposite)⁻¹ := hU.2 b.opposite (mem_univ _)
    have hneg : ComplexMatrix2.matExp
        (-(Complex.I • (Complex.I⁻¹ • ComplexMatrix2.logSeries (U b.opposite)))) =
        (ComplexMatrix2.matExp
          (Complex.I • (Complex.I⁻¹ • ComplexMatrix2.logSeries (U b.opposite))))⁻¹ :=
      Matrix.exp_neg _
    rw [e, smul_neg, hneg]
    exact (congrArg (·⁻¹) hexp).trans hinv.symm
end Logarithm
section Curve
open CriticalBranchResponse
variable {L n k : ℕ}
theorem continuous_expLineField (B : Edge L n k k → ComplexMatrix2) (b : Edge L n k k) :
    Continuous fun t : ℝ => expLineField L n k B t b := by
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  by_cases h : b.IsPositivelyOriented
  · have e : (fun t : ℝ => expLineField L n k B t b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b)) := by
      funext t
      simp [expLineField, PeriodicLattice.expTwist, h]
    rw [e]
    exact NormedSpace.exp_continuous.comp (by fun_prop)
  · have e : (fun t : ℝ => expLineField L n k B t b) =
        fun t : ℝ => ComplexMatrix2.matExp (-(Complex.I • ((t : ℂ) • B b.opposite))) := by
      funext t
      have hneg : ComplexMatrix2.matExp (-(Complex.I • ((t : ℂ) • B b.opposite))) =
          (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b.opposite)))⁻¹ := Matrix.exp_neg _
      rw [hneg]
      simp [expLineField, PeriodicLattice.expTwist, h]
    rw [e]
    exact NormedSpace.exp_continuous.comp (by fun_prop)
theorem expLineField_zero (B : Edge L n k k → ComplexMatrix2) :
    expLineField L n k B 0 = trivialField L n k k := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp [expLineField, PeriodicLattice.expTwist, h]
  · simp [expLineField, PeriodicLattice.expTwist, h]
theorem inv_mem_specialUnitary {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem inv_inv_of_mem_specialUnitary {W : ComplexMatrix2}
    (hW : W ∈ ComplexMatrix2.specialUnitary) : (W⁻¹)⁻¹ = W := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem expLineField_mem (hC : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hr : ∀ b : Edge L n k k, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (hone : trivialField L n k k ∈ fieldSpace L n k k)
    {B : Edge L n k k → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k k) (t : ℝ) :
    expLineField L n k B t ∈ fieldSpace L n k k := by
  have hv := ((hC.2.2 L k k hL le_rfl).1 n hn).1.1.1 _ hone B hB
  have hpos : ∀ b : Edge L n k k, b.IsPositivelyOriented →
      expLineField L n k B t b ∈ ComplexMatrix2.specialUnitary := by
    intro b hb
    have h := (hv ⟨b, hb⟩).1 t
    simpa [expLineField, PeriodicLattice.expTwist, hb, LeftChartFields.leftExpMul,
      LeftChartFields.LatticeData.onPositive,
      LeftChartFields.finiteData] using h
  have hneg : ∀ b : Edge L n k k, ¬ b.IsPositivelyOriented →
      expLineField L n k B t b = (expLineField L n k B t b.opposite)⁻¹ := by
    intro b hb
    have hb' := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp [expLineField, PeriodicLattice.expTwist, hb, hb']
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · rw [hneg b hb]
      exact inv_mem_specialUnitary (hpos _ ((isPositivelyOriented_or_opposite b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · exact hneg b.opposite (hr b hb)
    · rw [hneg b hb]
      exact (inv_inv_of_mem_specialUnitary
        (hpos _ ((isPositivelyOriented_or_opposite b).resolve_left hb))).symm
theorem tendsto_expLineField {B : Edge L n k k → ComplexMatrix2}
    (hmem : ∀ t, expLineField L n k B t ∈ fieldSpace L n k k) :
    Tendsto (expLineField L n k B) (𝓝 0)
      (𝓝[fieldSpace L n k k] trivialField L n k k) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, Eventually.of_forall hmem⟩
  have h := (continuous_expLineField B b).tendsto 0
  rw [expLineField_zero] at h
  exact h
end Curve
section Remainder
open CriticalBranchResponse ResponseOperators PeriodicOperators
open BackgroundFieldResponse (responseDefect)
open LocalKernels.Periodisation (periodSide)
variable {L n k : ℕ}
theorem periodicDefect_add (hRel : TorusResponseRelations.statement)
    (hOp : ResponseOperators.Claim) (hP : PeriodicOperators.TowerIndexSets.Claim)
    (hQ : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hn : 0 < n) (B₁ B₂ : edgeFormSpace L n k k) :
    periodicDefect L n k ((B₁ + B₂ : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
      periodicDefect L n k B₁ + periodicDefect L n k B₂ := by
  have hper := (hP L hL k k le_rfl).2.1
  have hs : 0 < periodSide L n := by
    have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
    unfold periodSide
    positivity
  have hfin : Finite ((colourEdges L k k).QuotMod (periodSide L n)) :=
    (hQ _ _ hper hper _ hs).1.2.1
  let _ := Fintype.ofFinite ((colourEdges L k k).QuotMod (periodSide L n))
  obtain ⟨δ₀, -, hops⟩ := hOp
  have huniq := ((hops L hL k hk).torus_sides n hn).forms_top
  obtain ⟨g₁, hg₁, h₁⟩ := (hRel L hL k hk n hn B₁).image_defect
  obtain ⟨g₂, hg₂, h₂⟩ := (hRel L hL k hk n hn B₂).image_defect
  obtain ⟨g₃, hg₃, h₃⟩ := (hRel L hL k hk n hn (B₁ + B₂)).image_defect
  have hsl : ∀ (x : edgeFormSpace L n k k) (p : PositiveEdge L n k k),
      (x : Edge L n k k → ComplexMatrix2) p.1 ∈ ComplexMatrix2.traceless :=
    fun x p => mem_traceless_of_mem_hermitianTraceless (x.2.1 _ p.2)
  have hg : g₃ = g₁ + g₂ := by
    funext c
    obtain ⟨ι, rfl⟩ := Quot.exists_rep c
    have e₁ := hg₁ ι
    have e₂ := hg₂ ι
    have e₃ := hg₃ ι
    change g₃ ((colourEdges L k k).mkQuot (periodSide L n) ι) =
      g₁ ((colourEdges L k k).mkQuot (periodSide L n) ι) +
        g₂ ((colourEdges L k k).mkQuot (periodSide L n) ι)
    rw [e₁, e₂, e₃]
    exact pauliCoeff_add (hsl B₁ _) (hsl B₂ _) _
  set M := periodicMatrix (colourEdges L k k) (colourEdges L k k) (responseDefect L k)
    (periodSide L n) with hM
  have hact : applyKernel M g₃ = applyKernel M g₁ + applyKernel M g₂ := by
    funext c
    simp only [applyKernel, hg, Pi.add_apply, mul_add, tsum_fintype, Finset.sum_add_distrib]
  have h₁₂ : ClassFnEqForm L n k k
      (restrictToPositiveEdges
        ((periodicDefect L n k B₁ + periodicDefect L n k B₂ : edgeFormSpace L n k k) :
          Edge L n k k → ComplexMatrix2)) (applyKernel M g₃) := by
    intro ι
    rw [hact, Pi.add_apply, h₁ ι, h₂ ι]
    exact (pauliCoeff_add (hsl _ _) (hsl _ _) _).symm
  have hmem : ∀ x : edgeFormSpace L n k k,
      restrictToPositiveEdges (x : Edge L n k k → ComplexMatrix2) ∈
        GroupLieProduct.tracelessFunctions (PositiveEdge L n k k) :=
    fun x => Submodule.mem_pi.2 fun p _ => hsl x p
  have e := (huniq (applyKernel M g₃)).unique ⟨hmem _, h₃⟩ ⟨hmem _, h₁₂⟩
  refine Subtype.ext (edgeForm_ext (Subtype.property _) (Subtype.property _) fun b hb => ?_)
  exact congrFun e ⟨b, hb⟩
end Remainder
section Field
open CriticalBranchResponse TorusResponseField
open AnalyticDifferentials (HasLeftDifferentialAt)
variable {L n k : ℕ}
theorem prolongComp_trivial {b : CriticalBranchData L n k} (hb : b.IsCritical) :
    ∀ j ≤ k, b.prolongComp j (trivialField L n k j) = trivialField L n k 0 := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.prolongComp_trivial <;> assumption
theorem exists_analytic_prolongComp (hM : AnalyticNearField.CompositionAndExpTwist)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {b : CriticalBranchData L n k}
    (hb : b.IsCritical) (j : ℕ) (hj : 1 ≤ j) :
    j ≤ k → ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldMap 𝒰 (b.prolongComp j) := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.prolongComp_analytic <;> assumption
theorem leftGradient_plaquetteAction_trivial (hb : (chosenCriticalBranch L n k).IsCritical)
    (hone : trivialField L n k k ∈ fieldSpace L n k k) :
    leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
      (trivialField L n k 0) = 0 := by
  have h := (hb.prolongComp_section k le_rfl).self_of_nhdsWithin hone
  obtain ⟨g, hg, hgr⟩ := h.2.2
  have hz : g = 0 := Subtype.ext (hg.trans (hb.gradient_trivial k le_rfl))
  subst hz
  have h0 := congrArg Subtype.val (LinearMap.map_zero (PairedFunctionSpace.realTransposeMap
    (S := edgePairedSpace L n k 0) (S' := edgePairedSpace L n k k) (leftDifferentialLinear
      (smoothingIter L n k k)
      ((chosenCriticalBranch L n k).prolongComp k (trivialField L n k k)))))
  have h1 := h0.symm.trans hgr
  rw [prolongComp_trivial hb k le_rfl] at h1
  exact h1.symm
theorem linearizedField_spec {B : Edge L n k k → ComplexMatrix2} {A₁ : edgeFormSpace L n k 0}
    (hA : (A₁ : Edge L n k 0 → ComplexMatrix2) =
      leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) B) :
    ((linearizedField L n k B).1 : Edge L n k 0 → ComplexMatrix2) =
        leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) B ∧
      (linearizedField L n k B).2 = (responseField L n k B).2 :=
  Classical.epsilon_spec (p := fun r : RealPeriodicField L n k =>
    (r.1 : Edge L n k 0 → ComplexMatrix2) =
        leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) B ∧
      r.2 = (responseField L n k B).2)
    ⟨(A₁, (responseField L n k B).2), hA, rfl⟩
theorem exists_curve_of_expLineField (hE : ComplexMatrix2.ExpLogEstimates)
    (hr : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
    (hb : (chosenCriticalBranch L n k).IsCritical)
    (hone : trivialField L n k k ∈ fieldSpace L n k k)
    {𝒲 : Set (Edge L n k k → ComplexMatrix2)}
    (hmaps : MapsTo (chosenProlongComp L n k k) 𝒲 (fieldSpace L n k 0))
    (hFM : HasLeftDifferentialAt (chosenProlongComp L n k k) (trivialField L n k k))
    (B : edgeFormSpace L n k k) (hcurve : ∀ᶠ t in 𝓝 (0 : ℝ), expLineField L n k B t ∈ 𝒲)
    (hG : GradientDerivativeCondition L n k B) {ζ : RealPeriodicField L n k}
    (hζ₁ : (ζ.1 : Edge L n k 0 → ComplexMatrix2) =
      leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) B)
    (hζ₂ : ζ.2 = (responseField L n k B).2) :
    ∃ γ : ℝ → FieldTriple L n k, IsCurveFromZero γ ζ ∧ ∀ᶠ t in 𝓝 (0 : ℝ),
      PeriodicLattice.expGaugeField ((γ t).1 : Edge L n k 0 → ComplexMatrix2) =
          chosenProlongComp L n k k (expLineField L n k B t) ∧
        ((γ t).2.1 : Edge L n k 0 → ComplexMatrix2) =
          leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
            (chosenProlongComp L n k k (expLineField L n k B t)) ∧
        ((γ t).2.2 : Edge L n k k → ComplexMatrix2) =
          (chosenCriticalBranch L n k).energyGradient k (expLineField L n k B t) := by
  obtain ⟨χJ, hχJ, hdJ⟩ := hG.hasDeriv_action_gradient
  obtain ⟨χμ, hχμ, hdμ⟩ := hG.hasDeriv_energy_gradient
  have hm1 : chosenProlongComp L n k k (trivialField L n k k) =
      trivialField L n k 0 := prolongComp_trivial hb k le_rfl
  have hinv1 : ∀ c : Edge L n k 0,
      (chosenProlongComp L n k k (trivialField L n k k) c)⁻¹ = 1 := by
    intro c
    rw [hm1]
    show (1 : ComplexMatrix2)⁻¹ = 1
    simp
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p : PositiveEdge L n k 0,
      ComplexMatrix2.operatorNorm (chosenProlongComp L n k k (expLineField L n k B t) p.1 - 1) < 1 := by
    refine eventually_all.2 fun p => ?_
    filter_upwards [(hFM B B.2 p.1 p.2).1] with t ht
    rw [hinv1, mul_one] at ht
    exact ht
  let raw : ℝ → Edge L n k 0 → ComplexMatrix2 := fun t =>
    logEdgeForm (chosenProlongComp L n k k (expLineField L n k B t))
  classical
  let A : ℝ → edgeFormSpace L n k 0 := fun t =>
    if h : raw t ∈ edgeFormSpace L n k 0 then ⟨raw t, h⟩ else 0
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ), (A t : Edge L n k 0 → ComplexMatrix2) = raw t ∧
      PeriodicLattice.expGaugeField (raw t) = chosenProlongComp L n k k (expLineField L n k B t) := by
    filter_upwards [hnear, hcurve] with t h₁ h₂
    have hU := hmaps h₂
    have hmem : raw t ∈ edgeFormSpace L n k 0 := logEdgeForm_mem hE hr hU h₁
    refine ⟨?_, expGaugeField_logEdgeForm hE hU h₁⟩
    simp only [A, dif_pos hmem]
  have hm0 : chosenProlongComp L n k k (expLineField L n k B 0) = trivialField L n k 0 := by
    rw [expLineField_zero, hm1]
  have hlog1 : ComplexMatrix2.logSeries (1 : ComplexMatrix2) = 0 := by
    simp [ComplexMatrix2.logSeries]
  have hraw0 : raw 0 = 0 := by
    funext b
    by_cases hbp : b.IsPositivelyOriented
    · show logEdgeForm _ b = 0
      rw [logEdgeForm_of_pos _ hbp, hm0]
      show Complex.I⁻¹ • ComplexMatrix2.logSeries (1 : ComplexMatrix2) = 0
      rw [hlog1, smul_zero]
    · by_cases hbr : b.opposite.IsPositivelyOriented
      · show logEdgeForm _ b = 0
        simp only [logEdgeForm, edgeFormOfPositiveValues, dif_neg hbp, dif_pos hbr, hm0]
        show -(Complex.I⁻¹ • ComplexMatrix2.logSeries (1 : ComplexMatrix2)) = 0
        rw [hlog1, smul_zero, neg_zero]
      · show logEdgeForm _ b = 0
        simp only [logEdgeForm, edgeFormOfPositiveValues, dif_neg hbp, dif_neg hbr]
  refine ⟨fun t => (A t, χJ t, χμ t), ⟨?_, ?_⟩, ?_⟩
  · refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · exact hA.self_of_nhds.1.trans hraw0
    · have h : (χJ 0 : Edge L n k 0 → ComplexMatrix2) = leftGradient (fieldSpace L n k 0)
          (fun U => (plaquetteAction L n k U : ℂ))
          (chosenProlongComp L n k k (expLineField L n k B 0)) :=
        hχJ.self_of_nhds
      rw [hm0, leftGradient_plaquetteAction_trivial hb hone] at h
      exact h
    · have h : (χμ 0 : Edge L n k k → ComplexMatrix2) =
          (chosenCriticalBranch L n k).energyGradient k (expLineField L n k B 0) :=
        hχμ.self_of_nhds
      rw [expLineField_zero, hb.gradient_trivial k le_rfl] at h
      exact h
  · obtain ⟨hζJ, hζμ⟩ := Prod.ext_iff.1 hζ₂
    refine hasDerivAt_fieldTripleCoords (γ := fun t => (A t, χJ t, χμ t)) (fun p => ?_)
      (fun p => ?_) (fun p => ?_)
    · have hd := (hFM B B.2 p.1 p.2).2
      have hval : (ζ.1 : Edge L n k 0 → ComplexMatrix2) p.1 = Complex.I⁻¹ • deriv (fun t : ℝ =>
          ComplexMatrix2.logSeries (chosenProlongComp L n k k (PeriodicLattice.expTwist
            ((t : ℂ) • (B : Edge L n k k → ComplexMatrix2)) (trivialField L n k k)) p.1 *
            (chosenProlongComp L n k k (trivialField L n k k) p.1)⁻¹)) 0 := by
        rw [hζ₁]
        simp only [leftDifferential, extendOddly, if_pos p.2]
        rfl
      rw [hval]
      refine (hd.hasDerivAt.const_smul Complex.I⁻¹).congr_of_eventuallyEq ?_
      filter_upwards [hA] with t ht
      show (A t : Edge L n k 0 → ComplexMatrix2) p.1 = _
      rw [ht.1]
      show logEdgeForm _ p.1 = _
      rw [logEdgeForm_of_pos _ p.2, hinv1]
      simp only [Pi.smul_apply, mul_one]
      rfl
    · have h := hdJ p.1
      rw [hG.coboundary_square_eq] at h
      rw [hζJ]
      exact h
    · have h := hdμ p.1
      rw [hζμ]
      exact h
  · filter_upwards [hA, hχJ, hχμ] with t h₁ h₂ h₃
    refine ⟨?_, h₂, h₃⟩
    show PeriodicLattice.expGaugeField (A t : Edge L n k 0 → ComplexMatrix2) = _
    rw [h₁.1]
    exact h₁.2
theorem leftSecondDeriv_self_eq [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
    (hrep : EventuallyNearIdentity (fieldSpace L n k k) (HasBackgroundFunctionalFormula L n k))
    (hF : ExpChartFunctionalExpansion L n k)
    (hφ : ∀ x : FieldTriple L n k, expChartFirstDeriv x = 0)
    (hfacts : HessianFacts (logTotalNormaliserRatio L n k))
    {B : Edge L n k k → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k k)
    (htend : Tendsto (expLineField L n k B) (𝓝 0)
      (𝓝[fieldSpace L n k k] trivialField L n k k))
    {γ : ℝ → FieldTriple L n k} {ζ : FieldTriple L n k} (hγ : IsCurveFromZero γ ζ)
    (hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      PeriodicLattice.expGaugeField ((γ t).1 : Edge L n k 0 → ComplexMatrix2) =
          chosenProlongComp L n k k (expLineField L n k B t) ∧
        ((γ t).2.1 : Edge L n k 0 → ComplexMatrix2) =
          leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
            (chosenProlongComp L n k k (expLineField L n k B t)) ∧
        ((γ t).2.2 : Edge L n k k → ComplexMatrix2) =
          (chosenCriticalBranch L n k).energyGradient k (expLineField L n k B t)) :
    leftSecondDeriv (logTotalNormaliserRatio L n k) (trivialField L n k k) B B =
      expChartSecondDeriv ζ ζ := by
  let φ : ℝ → ℝ := fun t => logTotalNormaliserRatio L n k
    (PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k k))
  have hT := isLittleO_sub_taylor_two (φ := φ) (hfacts.differentiableAt_near B hB)
    (hfacts.differentiableAt_deriv B hB)
  have h0 : φ 0 = 0 := by
    show logTotalNormaliserRatio L n k (expLineField L n k B 0) = 0
    rw [expLineField_zero]
    simp [logTotalNormaliserRatio]
  have hX := hF.isLittleO γ ζ hγ
  have hrepE : ∀ᶠ t in 𝓝 (0 : ℝ), expChartFunctional (γ t) =
      φ t + backgroundFunctional (trivialField L n k 0) 0 0 := by
    filter_upwards [htend.eventually hrep, hev] with t ht hv
    obtain ⟨he, hJ', hμ'⟩ := hv
    obtain ⟨-, J, μ, hJ, hμ, -, hΨ⟩ := ht
    have eJ : (γ t).2.1 = J := Subtype.ext (hJ'.trans hJ.symm)
    have eμ : (γ t).2.2 = μ := Subtype.ext (hμ'.trans hμ.symm)
    show backgroundFunctional
      (PeriodicLattice.expGaugeField ((γ t).1 : Edge L n k 0 → ComplexMatrix2))
      (γ t).2.1 (γ t).2.2 = _
    rw [he, eJ, eμ]
    have e : φ t = logTotalNormaliserRatio L n k (expLineField L n k B t) := rfl
    rw [e, hΨ]
    ring
  have hX' : (fun t : ℝ => φ t - t ^ 2 / 2 * expChartSecondDeriv ζ ζ) =o[𝓝 0]
      fun t : ℝ => t ^ 2 := by
    refine hX.congr' ?_ EventuallyEq.rfl
    filter_upwards [hrepE] with t ht
    rw [ht, hφ]
    ring
  have hsub := hX'.sub hT
  have hcoef := eq_zero_of_linear_add_quadratic_isLittleO (α := deriv φ 0)
    (d := deriv (deriv φ) 0 - expChartSecondDeriv ζ ζ)
    (hsub.congr_left fun t => by rw [h0]; ring)
  rw [leftSecondDeriv_self_eq_deriv_deriv]
  exact sub_eq_zero.1 hcoef
end Field
theorem claim_holds (hFirst : ExpChartFirstDerivVanishes)
    (hExt : HessianAndComplexExtensionHolds)
    (hRep : LogNormaliserRepresentationHolds)
    (hAx : CriticalBranchResponse.ResponseConditions)
    (hGlue : NormaliserProductTheorem)
    (hpU : ExpChartFunctionalClaim)
    (hCB : CriticalBranchExists)
    (hN : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hS : LeftChartSecondDerivative.MainStatement)
    (hM : AnalyticNearField.CompositionAndExpTwist)
    (hRel : TorusResponseRelations.statement)
    (hOp : ResponseOperators.Claim)
    (hP : PeriodicOperators.TowerIndexSets.Claim)
    (hQ : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hC : LeftChartFields.Claim)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hE : ComplexMatrix2.ExpLogEstimates) :
    NormaliserHessianAlongLinearizedField.Claim := by
  open CriticalBranchResponse TorusResponseField in
  intro L hL k hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s₀, hs₀, hax⟩ := hAx L hL i
  refine ⟨s₀, hs₀, ?_⟩
  intro s hs hle n hn hside B hB B' hB'
  suffices H : ∀ C C' : edgeFormSpace L n (i + 1) (i + 1),
      leftSecondDeriv (logTotalNormaliserRatio L n (i + 1))
          (trivialField L n (i + 1) (i + 1)) (C : Edge L n (i + 1) (i + 1) → ComplexMatrix2) C' =
        fieldFunctionalSecondDeriv L n (i + 1) (linearizedField L n (i + 1) C)
          (linearizedField L n (i + 1) C') from H ⟨B, hB⟩ ⟨B', hB'⟩
  intro C C'
  have hall := hax s hs hle n hn hside
  have hrep := hRep L n (i + 1) hL hn hk
  obtain ⟨f₀, fk, -⟩ := hrep.analytic_near_identity
  let _ := f₀
  let _ := fk
  have hbr : (chosenCriticalBranch L n (i + 1)).IsCritical :=
    Classical.epsilon_spec (hCB L n (i + 1) hL hn)
  obtain ⟨𝒲, h𝒲, hm⟩ := exists_analytic_prolongComp hM hL hn hbr (i + 1) hk le_rfl
  have hNm := hN L n (i + 1) (i + 1) 0 hL hn le_rfl (Nat.zero_le _) 𝒲 h𝒲.1
  obtain ⟨hinf, -, hat⟩ := hNm.2.1 _ hm
  obtain ⟨hFM, hHL⟩ := hat _ h𝒲.2
  have hmaps := hinf.2.1
  have hHL' : AnalyticDifferentials.LeftDifferentialIsLinear
      (chosenProlongComp L n (i + 1) (i + 1)) (trivialField L n (i + 1) (i + 1)) := hHL
  have hr0 : ∀ b : Edge L n (i + 1) 0, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented :=
    fun b hb => not_isPositivelyOriented_opposite hA hL hn (Nat.zero_le _) b hb
  have hrk : ∀ b : Edge L n (i + 1) (i + 1), b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented :=
    fun b hb => not_isPositivelyOriented_opposite hA hL hn le_rfl b hb
  obtain ⟨𝒰, h𝒰, hΨ⟩ := (hGlue L n i hL hn).analytic
  have hfacts := hessianFacts_of_analytic hS hN hL hn le_rfl h𝒰 hΨ
  have hF := (hpU L n (i + 1) hL hn hk).2
  have hExtT := hExt L n (i + 1) hL hn hk
  have hone : trivialField L n (i + 1) (i + 1) ∈ fieldSpace L n (i + 1) (i + 1) :=
    h𝒲.1.1 h𝒲.2
  have hspec : ∀ D : edgeFormSpace L n (i + 1) (i + 1),
      ((linearizedField L n (i + 1) D).1 : Edge L n (i + 1) 0 → ComplexMatrix2) =
        leftDifferential (chosenProlongComp L n (i + 1) (i + 1))
          (trivialField L n (i + 1) (i + 1)) D ∧
      (linearizedField L n (i + 1) D).2 = (responseField L n (i + 1) D).2 :=
    fun D => linearizedField_spec (hHL' D)
  have hdiag : ∀ D : edgeFormSpace L n (i + 1) (i + 1),
      leftSecondDeriv (logTotalNormaliserRatio L n (i + 1))
          (trivialField L n (i + 1) (i + 1)) D D =
        fieldFunctionalSecondDeriv L n (i + 1) (linearizedField L n (i + 1) D)
          (linearizedField L n (i + 1) D) := by
    intro D
    have hG := (hall D D.2).2.1
    have hmem := expLineField_mem (B := (D : Edge L n (i + 1) (i + 1) → ComplexMatrix2))
      hC hL hn hrk hone D.2
    have hcurve := (hNm.2.2.1 _ univ (expLineField L n (i + 1) D) hm
      ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩, fun t _ => hmem t,
        by rw [expLineField_zero]; exact h𝒲.2,
        fun b _ r c => ((continuous_expLineField _ b).matrix_elem r c).continuousOn⟩).1
    obtain ⟨γ, hγ, hev⟩ :=
      exists_curve_of_expLineField hE hr0 hbr hone hmaps hFM D hcurve hG (hspec D).1 (hspec D).2
    rw [hExtT.eq_expChartSecondDeriv]
    exact leftSecondDeriv_self_eq hrep.eventually_formula hF (hFirst L n (i + 1) hL hn hk)
      hfacts D.2 (tendsto_expLineField hmem) hγ hev
  have hν := periodicDefect_add hRel hOp hP hQ hL hk hn C C'
  have hadd : linearizedField L n (i + 1) ((C + C' : edgeFormSpace L n (i + 1) (i + 1)) :
        Edge L n (i + 1) (i + 1) → ComplexMatrix2) =
      linearizedField L n (i + 1) C + linearizedField L n (i + 1) C' := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · have e₁ := (hspec (C + C')).1
      have e₂ : leftDifferential (chosenProlongComp L n (i + 1) (i + 1))
            (trivialField L n (i + 1) (i + 1))
            ((C + C' : edgeFormSpace L n (i + 1) (i + 1)) :
              Edge L n (i + 1) (i + 1) → ComplexMatrix2) =
          leftDifferential (chosenProlongComp L n (i + 1) (i + 1))
              (trivialField L n (i + 1) (i + 1)) C +
            leftDifferential (chosenProlongComp L n (i + 1) (i + 1))
              (trivialField L n (i + 1) (i + 1)) C' := by
        rw [← hHL' (C + C'), map_add, Submodule.coe_add, hHL' C, hHL' C']
      show _ = ((linearizedField L n (i + 1) C).1 : Edge L n (i + 1) 0 → ComplexMatrix2) +
        ((linearizedField L n (i + 1) C').1 : Edge L n (i + 1) 0 → ComplexMatrix2)
      rw [(hspec C).1, (hspec C').1]
      exact e₁.trans e₂
    · have e₂ := (hspec (C + C')).2
      refine e₂.trans ?_
      have e₃ : (linearizedField L n (i + 1) C + linearizedField L n (i + 1) C').2 =
          (linearizedField L n (i + 1) C).2 + (linearizedField L n (i + 1) C').2 := rfl
      rw [e₃, (hspec C).2, (hspec C').2]
      simp only [responseField, hν, map_add]
      rfl
  obtain ⟨β, hβ, hsym⟩ := hExtT.exists_symm_bilinForm
  set Q := leftSecondDeriv (logTotalNormaliserRatio L n (i + 1))
    (trivialField L n (i + 1) (i + 1)) with hQdef
  set c : Edge L n (i + 1) (i + 1) → ComplexMatrix2 :=
    (C : Edge L n (i + 1) (i + 1) → ComplexMatrix2) with hc
  set c' : Edge L n (i + 1) (i + 1) → ComplexMatrix2 :=
    (C' : Edge L n (i + 1) (i + 1) → ComplexMatrix2) with hc'
  set z := linearizedField L n (i + 1) c with hz
  set z' := linearizedField L n (i + 1) c' with hz'
  have hcm : c ∈ edgeFormSpace L n (i + 1) (i + 1) := C.2
  have hcm' : c' ∈ edgeFormSpace L n (i + 1) (i + 1) := C'.2
  have hsm : c + c' ∈ edgeFormSpace L n (i + 1) (i + 1) :=
    (edgeFormSpace L n (i + 1) (i + 1)).add_mem hcm hcm'
  have hAL : ∀ x ∈ edgeFormSpace L n (i + 1) (i + 1), ∀ y ∈ edgeFormSpace L n (i + 1) (i + 1),
      ∀ w ∈ edgeFormSpace L n (i + 1) (i + 1), Q (x + y) w = Q x w + Q y w := hfacts.add_left
  have hSY : ∀ x ∈ edgeFormSpace L n (i + 1) (i + 1), ∀ y ∈ edgeFormSpace L n (i + 1) (i + 1),
      Q x y = Q y x :=
    hfacts.symm
  have e₁ : Q (c + c') (c + c') = Q c c + Q c' c + (Q c c' + Q c' c') := by
    rw [hAL c hcm c' hcm' _ hsm, hSY c hcm _ hsm, hSY c' hcm' _ hsm, hAL c hcm c' hcm' c hcm,
      hAL c hcm c' hcm' c' hcm']
  have e₂ : Q (c + c') (c + c') = β (z + z') (z + z') := by
    rw [hβ, ← hadd]
    exact hdiag (C + C')
  have e₄ : Q c c = β z z := by
    rw [hβ]
    exact hdiag C
  have e₅ : Q c' c' = β z' z' := by
    rw [hβ]
    exact hdiag C'
  have e₆ := hSY c hcm c' hcm'
  have e₇ := hsym z z'
  have e₈ : β (z + z') (z + z') = β z z + β z' z + (β z z' + β z' z') := by
    simp only [map_add, LinearMap.add_apply]
  rw [← hβ]
  linarith
end YangMills.Construction.Tower.NormaliserHessianAlongLinearizedField
end
