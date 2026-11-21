import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import YangMills.Construction.Matrices.ProductAnalyticInMatrices
import YangMills.Construction.Matrices.TracelessHolomorphyDifferentiableHolds
import YangMills.Construction.Towers.BondsOnWhichTheAveragesDepend
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.IteratesAreHolomorphicInTheFormAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.GroupLieProduct
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterHolomorphy
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (levelwiseMean meanOfDefined)
section Tuples
variable {σ : Type} [Fintype σ]
theorem supNorm_eq_pi_norm (A : σ → Matrices.ComplexMatrix2) : supNorm A = ‖A‖ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.supNorm_eq_norm <;> assumption
theorem isHolomorphicIn_of_analyticAt {m n : ℕ} {U : Set (Coordinates.ComplexCoordinates m)}
    {φ : Coordinates.ComplexCoordinates m → Coordinates.ComplexCoordinates n} (hU : IsOpen U)
    (h : ∀ z ∈ U, AnalyticAt ℂ φ z) : Coordinates.ComplexCoordinates.IsHolomorphicIn U φ := by
  refine ⟨hU, fun z hz => (h z hz).continuousAt.continuousWithinAt, fun p hp r => ?_⟩
  have hline : Continuous fun ζ : ℂ => p + ζ • Coordinates.ComplexCoordinates.stdBasisVector r := by
    fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), p + ζ • Coordinates.ComplexCoordinates.stdBasisVector r ∈ U := by
    apply hline.continuousAt.eventually_mem
    simpa using hU.mem_nhds hp
  filter_upwards [hmem] with ζ hζ
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => p + ζ • Coordinates.ComplexCoordinates.stdBasisVector r) ζ := by
    fun_prop
  exact (h _ hζ).differentiableAt.comp ζ hd
def matrixEquivCLM : Matrices.ComplexMatrix2 →L[ℂ] Coordinates.ComplexCoordinates 4 :=
  LinearMap.toContinuousLinearMap
    { toFun := Coordinates.ComplexCoordinates.matrixEquiv
      map_add' := fun X Y => by
        funext t
        simp [Coordinates.ComplexCoordinates.matrixEquiv]
      map_smul' := fun c X => by
        funext t
        simp [Coordinates.ComplexCoordinates.matrixEquiv] }
def coordsToTupleCLM (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (e : σ ≃ Fin (Fintype.card σ)) :
    Coordinates.ComplexCoordinates (Fintype.card σ * 3) →L[ℂ] σ → Matrices.ComplexMatrix2 :=
  ContinuousLinearMap.pi fun i => ∑ c : Fin 3,
    (ContinuousLinearMap.proj (finProdFinEquiv (e i, c))).smulRight (β c : Matrices.ComplexMatrix2)
theorem coordsToTupleCLM_apply (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (e : σ ≃ Fin (Fintype.card σ)) (z : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) :
    coordsToTupleCLM β e z = tupleOfCoords β e z := by
  funext i
  simp [coordsToTupleCLM, tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple]
theorem tupleOfCoords_mem_tracelessPi (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (e : σ ≃ Fin (Fintype.card σ)) (z : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) :
    tupleOfCoords β e z ∈ tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
theorem isHolomorphicOnTraceless_of_locally_analytic
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) (ρ : ℝ)
    (f : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2)
    (h : ∀ A ∈ supBall σ ρ, ∃ g : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2,
      AnalyticAt ℂ g A ∧ ∀ᶠ B in 𝓝 A, B ∈ supBall σ ρ → f B = g B) :
    IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv (supBall σ ρ) f := by
  refine ⟨⟨fun A hA => hA.1, fun A hA => ⟨ρ - supNorm A, sub_pos.2 hA.2, fun B hB hlt =>
    ⟨hB, ?_⟩⟩⟩, fun e => ?_⟩
  · have h1 : ‖B‖ ≤ ‖B - A‖ + ‖A‖ := by simpa using norm_add_le (B - A) A
    rw [supNorm_eq_pi_norm] at hlt ⊢
    rw [supNorm_eq_pi_norm] at hlt
    linarith
  · have hT : ∀ z, tupleOfCoords β e z = coordsToTupleCLM β e z := fun z =>
      (coordsToTupleCLM_apply β e z).symm
    have hU : tupleOfCoords β e ⁻¹' supBall σ ρ =
        {z | ‖coordsToTupleCLM β e z‖ < ρ} := by
      ext z
      show tupleOfCoords β e z ∈ supBall σ ρ ↔ ‖coordsToTupleCLM β e z‖ < ρ
      rw [← hT]
      exact ⟨fun hz => by rw [← supNorm_eq_pi_norm]; exact hz.2,
        fun hz => ⟨tupleOfCoords_mem_tracelessPi β e z, by rw [supNorm_eq_pi_norm]; exact hz⟩⟩
    have hopen : IsOpen (tupleOfCoords β e ⁻¹' supBall σ ρ) := by
      rw [hU]
      exact isOpen_lt (by fun_prop) continuous_const
    refine isHolomorphicIn_of_analyticAt hopen fun z hz => ?_
    obtain ⟨g, hg, hev⟩ := h _ hz
    have hcont : ContinuousAt (tupleOfCoords β e) z := by
      have : tupleOfCoords β e = coordsToTupleCLM β e := funext hT
      rw [this]
      exact (coordsToTupleCLM β e).continuous.continuousAt
    have hana : AnalyticAt ℂ (fun z => matrixEquivCLM (g (coordsToTupleCLM β e z))) z := by
      have h1 : AnalyticAt ℂ (coordsToTupleCLM β e) z := (coordsToTupleCLM β e).analyticAt z
      have h2 : AnalyticAt ℂ g (coordsToTupleCLM β e z) := by rwa [← hT]
      exact matrixEquivCLM.analyticAt _ |>.comp (h2.comp h1)
    refine hana.congr ?_
    filter_upwards [hcont.eventually hev, hopen.mem_nhds hz] with v hv hv'
    show matrixEquivCLM (g (coordsToTupleCLM β e v)) = Coordinates.ComplexCoordinates.matrixEquiv _
    rw [← hT, ← hv hv']
    rfl
end Tuples
variable {L k : ℕ}
theorem levelwiseMean_eq_some_iter
    (hxor : ∀ (i : ℕ) (e : Edge L k i), Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (W : Edge L k 0 → Matrices.ComplexMatrix2)
    (hW : ∀ j < k, complexIter L k j W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
      ∀ e : Edge L k j, Matrices.ComplexMatrix2.operatorNorm (complexIter L k j W e - 1) <
        polydiscRadius L / 2) :
    ∀ i ≤ k, ∀ c : Edge L k i, levelwiseMean W i c = some (complexIter L k i W c) := by
  intro i
  induction i with
  | zero => intro _ c; rfl
  | succ i ih =>
    intro hi c
    have ih' : levelwiseMean W i = fun c => some (complexIter L k i W c) :=
      funext (ih (by omega))
    obtain ⟨hconf, hsmall⟩ := hW i (by omega)
    have hpos : ∀ c : Edge L k (i + 1), meanOfDefined (levelwiseMean W i) c =
        some (complexSmoothing L (complexIter L k i W) c) := by
      intro c
      have hf : valuesOrOne (levelwiseMean W i) = complexIter L k i W := by
        rw [ih']
        rfl
      unfold meanOfDefined
      rw [hf, if_pos]
      refine ⟨fun e _ => by rw [ih']; rfl, ⟨fun e _ => hconf.1 e, fun e _ => hconf.2 e⟩,
        fun e _ => ?_⟩
      have h := hsmall e
      have h0 : 0 ≤ Matrices.ComplexMatrix2.operatorNorm (complexIter L k i W e - 1) := norm_nonneg _
      linarith
    have hval : complexIter L k (i + 1) W c =
        complexSmoothing L (complexIter L k i W) c := rfl
    rw [hval, levelwiseMean]
    beta_reduce
    by_cases hc : c.IsPositivelyOriented
    · rw [if_pos hc, hpos]
    · have hr : c.opposite.IsPositivelyOriented := by
        rcases hxor (i + 1) c with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 hc
        · exact h1
      rw [if_neg hc, hpos, Option.map_some]
      unfold complexSmoothing
      rw [if_pos hr, if_neg hc]
theorem exists_form_restrict_eq
    (hxor : ∀ e : Edge L k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {ρ : ℝ} (hρ : 0 < ρ) (F : Finset (Edge L k 0)) (hF : ∀ e ∈ F, e.IsPositivelyOriented)
    {A : F → Matrices.ComplexMatrix2} (hA : A ∈ supBall F ρ) :
    ∃ ω ∈ complexEdgeForms (meshAt L k 0), maxOperatorNorm ω < ENNReal.ofReal ρ ∧
      (fun c : F => ω c) = A := by
  classical
  let ω₀ : Edge L k 0 → Matrices.ComplexMatrix2 := fun e => if h : e ∈ F then A ⟨e, h⟩ else 0
  let ω : Edge L k 0 → Matrices.ComplexMatrix2 := extendOddly ω₀
  have hωp : ∀ e : Edge L k 0, e.IsPositivelyOriented → ω e = ω₀ e := fun e he => by
    show (if e.IsPositivelyOriented then _ else _) = _
    rw [if_pos he]
  have hωn : ∀ e : Edge L k 0, ¬ e.IsPositivelyOriented → ω e = -ω₀ e.opposite := fun e he => by
    show (if e.IsPositivelyOriented then _ else _) = _
    rw [if_neg he]
  have hω₀ : ∀ e, ω₀ e ∈ Matrices.ComplexMatrix2.traceless := fun e => by
    by_cases h : e ∈ F
    · simp only [ω₀, dif_pos h]
      exact hA.1 _
    · simp only [ω₀, dif_neg h]
      exact (Matrices.ComplexMatrix2.traceless).zero_mem
  have hnorm₀ : ∀ e, Matrices.ComplexMatrix2.operatorNorm (ω₀ e) ≤ supNorm A := fun e => by
    by_cases h : e ∈ F
    · simp only [ω₀, dif_pos h]
      rw [supNorm_eq_pi_norm]
      exact norm_le_pi_norm A ⟨e, h⟩
    · simp only [ω₀, dif_neg h]
      rw [supNorm_eq_pi_norm]
      simp
  have hnorm : ∀ e, Matrices.ComplexMatrix2.operatorNorm (ω e) ≤ supNorm A := fun e => by
    by_cases h : e.IsPositivelyOriented
    · rw [hωp e h]
      exact hnorm₀ e
    · rw [hωn e h]
      simpa using hnorm₀ e.opposite
  refine ⟨ω, ⟨fun e he => ?_, fun e => ?_⟩, ?_, ?_⟩
  · rw [hωp e he]
    exact hω₀ e
  · rcases hxor e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hωn _ h2, hωp e h1]
      rfl
    · rw [hωp _ h1, hωn e h2, neg_neg]
  · refine lt_of_le_of_lt (iSup_le fun e => ENNReal.ofReal_le_ofReal (hnorm e)) ?_
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 hA.2
  · funext c
    rw [hωp _ (hF _ c.2)]
    simp [ω₀]
theorem remainderGaugeField_apply_of_pos (ω : Edge L k 0 → Matrices.ComplexMatrix2)
    {e : Edge L k 0} (he : e.IsPositivelyOriented) :
    remainderGaugeField ω e =
      Matrices.ComplexMatrix2.matExp (Complex.I • (finestMesh L k • ω e)) := by
  show expTwist (scaledRemainderForm ω) 1 e = _
  unfold expTwist
  rw [if_pos he]
  simp [scaledRemainderForm]
def expFamily (η : ℝ) {σ : Type} (A : σ → Matrices.ComplexMatrix2) :
    σ ⊕ Empty → Matrices.ComplexMatrix2 :=
  asGroupFactors fun s => Matrices.ComplexMatrix2.matExp (Complex.I • (η • A s))
theorem analyticAt_expFamily (η : ℝ) {σ : Type} [Fintype σ] (A : σ → Matrices.ComplexMatrix2) :
    AnalyticAt ℂ (expFamily η : (σ → Matrices.ComplexMatrix2) → σ ⊕ Empty → Matrices.ComplexMatrix2)
      A := by
  have : CompleteSpace Matrices.ComplexMatrix2 := FiniteDimensional.complete ℂ Matrices.ComplexMatrix2
  rw [analyticAt_pi_iff]
  rintro (s | s)
  · let l : (σ → Matrices.ComplexMatrix2) →L[ℂ] Matrices.ComplexMatrix2 :=
      (Complex.I * (η : ℂ)) •
        (ContinuousLinearMap.proj s : (σ → Matrices.ComplexMatrix2) →L[ℂ] Matrices.ComplexMatrix2)
    have hl : ∀ B : σ → Matrices.ComplexMatrix2, Complex.I • (η • B s) = l B := fun B => by
      ext i j
      simp [l]
      ring
    have hexp : AnalyticAt ℂ Matrices.ComplexMatrix2.matExp (l A) :=
      NormedSpace.exp_analytic (𝕂 := ℂ) _
    have := hexp.comp (l.analyticAt A)
    refine this.congr (Eventually.of_forall fun B => ?_)
    show Matrices.ComplexMatrix2.matExp (l B) =
      Matrices.ComplexMatrix2.matExp (Complex.I • (η • B s))
    rw [hl]
  · exact s.elim
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (e : InfiniteLattice.Link a) :
    Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem iteratesHolomorphicInForm_holds
    (H₁ : Matrices.GroupLieProduct.HolomorphicMatrixAnalyticity)
    (H₂ : SupportOfMeans.SupportOfMeansHolds) : IteratesHolomorphicInForm := by
  intro L hL ρ hρ k hk hP j hj b
  have hS := (H₂ L hL k hk).2
  have hmesh : ∀ i, 0 < meshAt L k i := fun i => by
    have : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact zpow_pos this _
  have hxor : ∀ (i : ℕ) (c : Edge L k i),
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented :=
    fun i c => xor_isPositivelyOriented_opposite (hmesh i) c
  obtain ⟨hfin, -⟩ := hS.finite_nonempty j hj b
  have hR := hS.dependsOnlyOn j hj b hfin.toFinset hfin.coe_toFinset
  obtain ⟨f₀, hw⟩ := hR.exists_representation
  have hhol := hR.representation_holomorphic f₀ hw
  have hFpos : ∀ c ∈ hfin.toFinset, c.IsPositivelyOriented := fun c hc =>
    (hfin.mem_toFinset.1 hc).1
  have hform : ∀ ω ∈ complexEdgeForms (meshAt L k 0), maxOperatorNorm ω < ENNReal.ofReal ρ →
      remainderGaugeField ω ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup ∧
        levelwiseMean (remainderGaugeField ω) j b =
          some (complexIter L k j (remainderGaugeField ω) b) := fun ω hω hs =>
    ⟨(hP ω hω hs 0 (by omega)).1, levelwiseMean_eq_some_iter hxor _ (hP ω hω hs) j hj b⟩
  have hval : ∀ ω : Edge L k 0 → Matrices.ComplexMatrix2,
      (fun c : hfin.toFinset => remainderGaugeField ω c) =
        fun c : hfin.toFinset =>
          Matrices.ComplexMatrix2.matExp (Complex.I • (finestMesh L k • ω c)) := fun ω => by
    funext c
    exact remainderGaugeField_apply_of_pos ω (hFpos _ c.2)
  have hdefined : ∀ ω ∈ complexEdgeForms (meshAt L k 0), maxOperatorNorm ω < ENNReal.ofReal ρ →
      (fun c : hfin.toFinset => remainderGaugeField ω c) ∈
        SupportOfMeans.definedLocus (SupportOfMeans.Unbounded.baseFields L k) hfin.toFinset
          (SupportOfMeans.Unbounded.meanAt b) := fun ω hω hs => by
    obtain ⟨hc, hm⟩ := hform ω hω hs
    refine (hR.isSome_iff _ hc).1 ?_
    show (levelwiseMean (remainderGaugeField ω) j b).isSome
    rw [hm]
    rfl
  refine ⟨hfin.toFinset,
    fun A => f₀ fun c => Matrices.ComplexMatrix2.matExp (Complex.I • (finestMesh L k • A c)),
    fun β => ?_, fun ω hω hs => ?_⟩
  · have hmem : ∀ B ∈ supBall hfin.toFinset ρ,
        (fun c => Matrices.ComplexMatrix2.matExp (Complex.I • (finestMesh L k • B c))) ∈
          SupportOfMeans.definedLocus (SupportOfMeans.Unbounded.baseFields L k) hfin.toFinset
            (SupportOfMeans.Unbounded.meanAt b) := by
      intro B hB
      obtain ⟨ω, hω, hs, rfl⟩ := exists_form_restrict_eq (hxor 0) hρ hfin.toFinset hFpos hB
      rw [← hval ω]
      exact hdefined ω hω hs
    refine isHolomorphicOnTraceless_of_locally_analytic β ρ _ fun A hA => ?_
    obtain ⟨G, hG, hev⟩ := H₁ hfin.toFinset Empty β _ _ (Or.inr (hhol β))
      (expFamily (finestMesh L k) A) ⟨_, hmem A hA, rfl⟩
    refine ⟨fun B => G (expFamily (finestMesh L k) B),
      hG.comp (analyticAt_expFamily _ A), ?_⟩
    have hc := (analyticAt_expFamily (finestMesh L k) A).continuousAt
    filter_upwards [hc.eventually hev] with B hB hBball
    exact hB ⟨_, hmem B hBball, rfl⟩
  · obtain ⟨hc, hm⟩ := hform ω hω hs
    have hv := hw.eq_some _ hc (hdefined ω hω hs)
    have hv' : levelwiseMean (remainderGaugeField ω) j b =
        some (f₀ fun c => remainderGaugeField ω c) := hv
    rw [hm] at hv'
    rw [Option.some.inj hv', hval ω]
end YangMills.Construction.Tower.FullSpace.IterHolomorphy
end
