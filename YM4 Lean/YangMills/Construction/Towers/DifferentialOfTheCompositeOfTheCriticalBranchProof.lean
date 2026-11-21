import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
import YangMills.Construction.Towers.MultiplierOfTheNextLevelProof
import YangMills.Construction.Towers.PairingOfTheTransposeIntoThePlaquetteFunctions
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import YangMills.Construction.Towers.RealAnalyticMapsAlongExponentialCurves
import YangMills.Construction.Towers.RealAnalyticMapsNearAConfigurationProof
import YangMills.Construction.Towers.SecondDifferentialAtACriticalPoint
import YangMills.Construction.Towers.TheCriticalBranch
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.ProlongDifferential
open CriticalBranchResponse
structure FormConditions (L m k : ℕ) (B : edgeFormSpace L m k k) (A₁ : edgeFormSpace L m k 0)
    (μ₁ : edgeFormSpace L m k k) : Prop where
  deriv_eq : (A₁ : Edge L m k 0 → Matrices.ComplexMatrix2) =
    leftDifferential (chosenProlongComp L m k k) (trivialField L m k k) B
  smoothing_eq : linearSmoothingIter L m k k A₁ = B
  energy_hasDeriv : IsFormCurveDerivAtZero
    (fun t => (chosenCriticalBranch L m k).energyGradient k (expLineField L m k B t)) μ₁
  action_hasDeriv : IsFormCurveDerivAtZero
    (fun t => leftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
      (chosenProlongComp L m k k (expLineField L m k B t)))
    (formCoboundaryTranspose L m k (formCoboundary L m k A₁))
  coboundary_eq : formCoboundaryTranspose L m k (formCoboundary L m k A₁) =
    linearSmoothingTranspose L m k μ₁
def ProlongDifferentialHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, 0 < m →
    ∀ B : edgeFormSpace L m k k, ∃ (A₁ : edgeFormSpace L m k 0) (μ₁ : edgeFormSpace L m k k),
      FormConditions L m k B A₁ μ₁
end YangMills.Construction.Tower.ProlongDifferential
end

open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ProlongDifferential
open CriticalBranchResponse AnalyticDifferentials CriticalSecondDeriv AnalyticNearField
  LeftChartFields Matrices
section RealFunctions
variable {L n k j : ℕ}
theorem deriv_ofReal_comp_eq (f : ℝ → ℝ) (t : ℝ) :
    deriv (fun s => (f s : ℂ)) t = ((deriv f t : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ f t
  · exact h.hasDerivAt.ofReal_comp.deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => (f s : ℂ)) t := fun h' => h (by
      have := Complex.reCLM.differentiableAt.comp t h'
      simpa [Function.comp_def] using this)
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h']
    simp
theorem leftSecondDeriv_ofReal (F : (Edge L n k j → ComplexMatrix2) → ℝ)
    (U B B' : Edge L n k j → ComplexMatrix2) :
    leftSecondDeriv (fun V => (F V : ℂ)) U B B' = ((leftSecondDeriv F U B B' : ℝ) : ℂ) := by
  simp only [leftSecondDeriv, mixedDirectionalDeriv]
  rw [← deriv_ofReal_comp_eq]
  congr 1
  funext s
  exact deriv_ofReal_comp_eq _ 0
theorem leftGradient_indep_domain (𝔇 𝔇' : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → ℝ) (U : Edge L n k j → ComplexMatrix2) :
    leftGradient 𝔇 (fun V => (F V : ℂ)) U = leftGradient 𝔇' (fun V => (F V : ℂ)) U := by
  have h : IsLeftGradient 𝔇 (fun V => (F V : ℂ)) U = IsLeftGradient 𝔇' (fun V => (F V : ℂ)) U := by
    funext X
    simp only [IsLeftGradient, Complex.ofReal_im, implies_true, forall_const]
  simp only [leftGradient, h]
theorem traceFinsumPairing_comm {ι : Type*} (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.traceFinsumPairing_comm <;> assumption
end RealFunctions
section Entries
def matrixEntryCLM (r c : Fin 2) : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X r c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem contDiff_matExp : ContDiff ℝ ∞ (ComplexMatrix2.matExp) := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.contDiff_matExp <;> assumption
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem contDiff_matExp_I_smul {X : E → ComplexMatrix2} (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun p => ComplexMatrix2.matExp (Complex.I • X p)) :=
  contDiff_matExp.comp (ContDiff.smul (f := fun _ => Complex.I) contDiff_const hX :
    ContDiff ℝ ∞ (fun p => Complex.I • X p))
theorem contDiff_ofReal_smul_const (M : ComplexMatrix2) {a : E → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun p => ((a p : ℝ) : ℂ) • M) :=
  (Complex.ofRealCLM.contDiff.comp ha).smul contDiff_const
end Entries
section Chart
variable {L n k j : ℕ}
structure FiniteLevelFacts (L n k j : ℕ) : Prop where
  conditions : (finiteData L n k j).Conditions
  tangentEq : FiniteTangentSpaceEq L n k j
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem expTwist_of_pos (A U : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := if_pos hb
theorem isUnit_det_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit V.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem eq_expTwist {V A U : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, b.IsPositivelyOriented → V b = ComplexMatrix2.matExp (Complex.I • A b) * U b) :
    V = PeriodicLattice.expTwist A U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_pos A U hb]
    exact h b hb
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have h1 : V b.opposite = (V b)⁻¹ := hV.2 b (mem_univ b)
    have h2 : PeriodicLattice.expTwist A U b =
        (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := if_neg hb
    rw [h2, ← h _ hr, h1,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact (hV.1 b (mem_univ b)))]
theorem expTwist_zero {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist 0 U = U := by apply _root_.YangMills.Construction.Tower.AnalyticNearField.expTwist_zero <;> assumption
theorem expTwist_mem (hl : FiniteLevelFacts L n k j) {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k j := by
  have h := hl.conditions.1.1 U hU A hA
  obtain ⟨-, hbij, -⟩ := hl.tangentEq
  have hw : (fun b : PositiveEdge L n k j => ComplexMatrix2.matExp (Complex.I • A b.1) * U b.1) ∈
      specialUnitaryPower (PositiveEdge L n k j) := fun b => by
    have h1 := (h b).1 1
    exact show ComplexMatrix2.matExp (Complex.I • A b.1) * U b.1 ∈ ComplexMatrix2.specialUnitary from by
      simpa [leftExpMul, LatticeData.onPositive, finiteData] using h1
  obtain ⟨V, hV, hVw⟩ := hbij.surjOn hw
  have h2 := eq_expTwist (A := A) (U := U) hV fun b hb => congrFun hVw ⟨b, hb⟩
  rw [← h2]
  exact hV
theorem hasDerivAt_expTwist_line (hl : FiniteLevelFacts L n k j)
    {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b)
      (Complex.I • A b * U b) 0 := by
  have h := ((hl.conditions.1.1 U hU A hA) ⟨b, hb⟩).2
  have he : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b) =
      fun t : ℝ => leftExpMul ((t : ℂ) • A b) (U b) := by
    funext t
    rw [expTwist_of_pos _ _ hb]
    rfl
  rw [he]
  exact h
theorem extendOddly_eq {f A : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j)
    (h : ∀ b, b.IsPositivelyOriented → f b = A b) : extendOddly f = A := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, if_pos hb]
    exact h b hb
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have h1 : A b.opposite = -A b := hA.2 b
    simp only [extendOddly, if_neg hb]
    rw [h _ hr, h1, neg_neg]
theorem curveTangent_expTwist_line (hl : FiniteLevelFacts L n k j)
    {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) :
    curveTangent (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U) = A := by
  have h0 : PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • A) U = U := by
    simpa using expTwist_zero hU
  refine extendOddly_eq hA fun b hb => ?_
  rw [(hasDerivAt_expTwist_line hl hA hU hb).deriv]
  beta_reduce
  rw [h0, mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compact (hU.1 b (mem_univ b))), mul_one, smul_smul,
    inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem curveTangent_congr {f g : ℝ → Edge L n k j → ComplexMatrix2} (h : f =ᶠ[𝓝 0] g) :
    curveTangent f = curveTangent g := by apply _root_.YangMills.SharedProofs.p19450 <;> assumption
theorem ofReal_smul_mem {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (s : ℝ) : (s : ℂ) • B ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.ofReal_smul_mem_edgeFormSpace <;> assumption
theorem isSmoothTwoParamFamily_expTwist (hl : FiniteLevelFacts L n k j)
    {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (hB' : B' ∈ edgeFormSpace L n k j)
    (hone : trivialField L n k j ∈ fieldSpace L n k j) :
    IsSmoothTwoParamFamily (trivialField L n k j) univ
      (fun p : ℝ × ℝ => PeriodicLattice.expTwist ((p.1 : ℂ) • B + (p.2 : ℂ) • B')
        (trivialField L n k j)) := by
  refine ⟨isOpen_univ, mem_univ _, fun p _ => ?_, ?_, fun b hb r c => ?_⟩
  · exact expTwist_mem hl
      ((edgeFormSpace L n k j).add_mem (ofReal_smul_mem hB _) (ofReal_smul_mem hB' _)) hone
  · have : (((0 : ℝ) : ℂ) • B + ((0 : ℝ) : ℂ) • B') = 0 := by simp
    simp only [this]
    exact expTwist_zero hone
  · have hX : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((p.1 : ℂ) • B b + (p.2 : ℂ) • B' b)) :=
      (contDiff_ofReal_smul_const (B b) contDiff_fst).add
        (contDiff_ofReal_smul_const (B' b) contDiff_snd)
    have h := ((matrixEntryCLM r c).contDiff.comp (contDiff_matExp_I_smul hX)).contDiffOn
      (s := univ)
    refine h.congr fun p _ => ?_
    simp only [expTwist_of_pos _ _ hb]
    simp [matrixEntryCLM]
    rfl
theorem isSmoothCurveAt_expTwist_line (hl : FiniteLevelFacts L n k j)
    {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (hone : trivialField L n k j ∈ fieldSpace L n k j)
    {I : Set ℝ} (hI : IsOpenIntervalAroundZero I) :
    IsSmoothCurveAt (trivialField L n k j) I
      (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j)) := by
  refine ⟨hI, fun t _ => expTwist_mem hl (ofReal_smul_mem hB _) hone, ?_, fun b hb r c => ?_⟩
  · have : (((0 : ℝ) : ℂ) • B) = 0 := by simp
    simp only [this]
    exact expTwist_zero hone
  · have hX : ContDiff ℝ ∞ (fun t : ℝ => ((t : ℂ) • B b)) :=
      contDiff_ofReal_smul_const (B b) contDiff_id
    have h := ((matrixEntryCLM r c).contDiff.comp (contDiff_matExp_I_smul hX)).contDiffOn (s := I)
    refine h.congr fun p _ => ?_
    simp only [expTwist_of_pos _ _ hb]
    simp [matrixEntryCLM]
    rfl
theorem tendsto_expTwist_line (hl : FiniteLevelFacts L n k j) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (hone : trivialField L n k j ∈ fieldSpace L n k j) :
    Tendsto (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j))
      (𝓝 0) (𝓝[fieldSpace L n k j] trivialField L n k j) := by
  have hV : ∀ b : Edge L n k j,
      Tendsto (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b)))
      (𝓝 0) (𝓝 1) := fun b => by
    have hX : ContDiff ℝ ∞ (fun t : ℝ => ((t : ℂ) • B b)) :=
      contDiff_ofReal_smul_const (B b) contDiff_id
    have h := (contDiff_matExp_I_smul hX).continuous.tendsto 0
    simpa [ComplexMatrix2.matExp, NormedSpace.exp_zero] using h
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_,
    Eventually.of_forall fun t => expTwist_mem hl (ofReal_smul_mem hB _) hone⟩
  by_cases hb : b.IsPositivelyOriented
  · have he : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B)
        (trivialField L n k j) b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b)) := by
      funext t
      rw [expTwist_of_pos _ _ hb]
      simp
    rw [he]
    exact hV b
  · have he : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B)
        (trivialField L n k j) b) =
        fun t : ℝ => Ring.inverse (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b.opposite))) := by
      funext t
      have h2 : PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j) b =
          (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B) b.opposite) *
            trivialField L n k j b.opposite)⁻¹ := if_neg hb
      rw [h2, Matrix.nonsing_inv_eq_ringInverse]
      simp
    rw [he]
    have hc : ContinuousAt (Ring.inverse : ComplexMatrix2 → ComplexMatrix2)
        ((1 : ComplexMatrix2ˣ) : ComplexMatrix2) :=
      NormedRing.inverse_continuousAt 1
    have h := hc.tendsto.comp (hV b.opposite)
    simp only [Units.val_one, Ring.inverse_one] at h
    exact h
end Chart
section Gradients
variable {L n k j : ℕ}
theorem entriesDifferentiableOn_of_smooth {U₀ : Edge L n k j → ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2} (hγ : IsSmoothCurveAt U₀ I γ) :
    EntriesDifferentiableOn I γ :=
  ⟨hγ.1, hγ.2.1, fun b hb r c t ht =>
    ((hγ.2.2.2 b hb r c).contDiffAt (hγ.1.1.mem_nhds ht)).differentiableAt (by simp)⟩
theorem exists_leftGradient_curve {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {f : (Edge L n k j → ComplexMatrix2) → ℝ}
    {U₀ : Edge L n k j → ComplexMatrix2}
    (hG : GradientDerivAlongCurves 𝒩 (fun V => (f V : ℂ)) U₀) {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2} (hγ : IsSmoothCurveAt U₀ I γ)
    (h0 : leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) U₀ = 0) :
    ∃ (χ : ℝ → edgeFormSpace L n k j) (D : edgeFormSpace L n k j),
      (∀ᶠ t in 𝓝 (0 : ℝ), (χ t : Edge L n k j → ComplexMatrix2) =
        leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ t)) ∧ χ 0 = 0 ∧
      HasFormDerivAtZero χ D ∧
      PairsAsHessian (fun V => (f V : ℂ)) U₀ (curveTangent γ) D := by
  classical
  obtain ⟨hev, -, D, hD, hder, hpair, -⟩ := hG I γ hγ
  have hX : ∀ t, leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ t) =
      leftGradient 𝒩 (fun V => (f V : ℂ)) (γ t) := fun t => leftGradient_indep_domain _ _ f _
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ),
      leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ t) ∈ edgeFormSpace L n k j :=
    hev.mono fun t ht => by
      rw [hX]
      exact ht.2.2.1.2.1 fun V _ => Complex.ofReal_im _
  let χ : ℝ → edgeFormSpace L n k j := fun t =>
    if h : leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ t) ∈ edgeFormSpace L n k j then
      ⟨_, h⟩ else 0
  have hχ : ∀ᶠ t in 𝓝 (0 : ℝ), (χ t : Edge L n k j → ComplexMatrix2) =
      leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ t) :=
    hmem.mono fun t ht => by simp only [χ, dif_pos ht]
  refine ⟨χ, ⟨D, hD⟩, hχ, ?_, ?_, hpair⟩
  · have h00 : leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ 0) = 0 := by
      rw [hγ.2.2.1, h0]
    have hm : leftGradient (fieldSpace L n k j) (fun V => (f V : ℂ)) (γ 0) ∈
        edgeFormSpace L n k j := by
      rw [h00]
      exact (edgeFormSpace L n k j).zero_mem
    apply Subtype.ext
    simp only [χ, dif_pos hm, h00]
    rfl
  · intro b
    refine (hder b).congr_of_eventuallyEq ?_
    filter_upwards [hχ] with t ht
    rw [ht, hX]
end Gradients
section Polarisation
theorem eq_of_symm_additive_diag {V : Type*} [AddCommGroup V] (p r : V → V → ℝ)
    (hp : ∀ x y, p x y = p y x) (hr : ∀ x y, r x y = r y x)
    (hpa : ∀ x y z, p x (y + z) = p x y + p x z) (hra : ∀ x y z, r x (y + z) = r x y + r x z)
    (hq : ∀ x, p x x = r x x) (x y : V) : p x y = r x y := by
  have h1 := hq (x + y)
  rw [hpa, hra, hp (x + y) x, hp (x + y) y, hr (x + y) x, hr (x + y) y, hpa, hpa, hra, hra,
    hq x, hq y, hp y x, hr y x] at h1
  linarith
variable {L n k : ℕ}
theorem formCoboundary_apply (x : edgeFormSpace L n k 0) :
    (formCoboundary L n k x : Face L n k 0 → ComplexMatrix2) =
      edgeCoboundary (x : Edge L n k 0 → ComplexMatrix2) := by
  have hpos : ∀ (y : Vertex L n k 0) (μ : Fin 4),
      (PeriodicLattice.Bond.forwardFrom y μ).IsPositivelyOriented :=
    fun y μ => ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  let T : edgeFormSpace L n k 0 →ₗ[ℝ] faceFunctionSpace L n k 0 :=
    { toFun := fun x => ⟨edgeCoboundary (x : Edge L n k 0 → ComplexMatrix2), fun p _ =>
        ComplexMatrix2.hermitianTraceless.sub_mem
          (ComplexMatrix2.hermitianTraceless.sub_mem
            (ComplexMatrix2.hermitianTraceless.add_mem (x.2.1 _ (hpos _ _))
              (x.2.1 _ (hpos _ _))) (x.2.1 _ (hpos _ _))) (x.2.1 _ (hpos _ _))⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext p
        simp only [edgeCoboundary, Submodule.coe_add, Pi.add_apply]
        abel
      map_smul' := fun c a => by
        apply Subtype.ext
        funext p
        simp only [edgeCoboundary, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
          smul_add, smul_sub] }
  have h := Classical.epsilon_spec
    (p := fun T : edgeFormSpace L n k 0 →ₗ[ℝ] faceFunctionSpace L n k 0 =>
      ∀ x : edgeFormSpace L n k 0, (T x : Face L n k 0 → ComplexMatrix2) =
        edgeCoboundary (x : Edge L n k 0 → ComplexMatrix2)) ⟨T, fun _ => rfl⟩
  exact h x
theorem traceFinsumPairing_self_re_nonneg (hE3 : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {f : Face L n k 0 → ComplexMatrix2}
    (hf : ∀ p, f p ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re := by
  obtain ⟨⟨-, c, hc⟩, -, hall, -⟩ := ((hE3 L hL k 0 (Nat.zero_le k)).1 n hn).2.2.2 univ
  let f' : FaceSums.finSuppLieFields (univ : Set (Face L n k 0)) :=
    ⟨fun σ => f σ.1, fun σ => hf σ.1, hall _⟩
  have h1 := hc f' f'
  have h2 : traceFinsumPairing f'.1 f'.1 = traceFinsumPairing f f := by
    simp only [traceFinsumPairing]
    exact finsum_comp_equiv (Equiv.Set.univ (Face L n k 0))
      (f := fun p => ComplexMatrix2.halfTrace (f p * f p))
  rw [← h2, ← h1, Complex.ofReal_re]
  simpa using c.re_inner_nonneg f'
theorem eq_transpose_of_pairsAsHessian (hG2 : FiniteSideFormSpaces)
    (hE3 : FaceSums.FacesAndPairings)
    (hPT : RealTransposeFaceFunctionPairing)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hsym : ∀ B ∈ edgeFormSpace L n k 0, ∀ B' ∈ edgeFormSpace L n k 0,
      leftSecondDeriv (fun V => (plaquetteAction L n k V : ℂ)) (trivialField L n k 0) B B' =
        leftSecondDeriv (fun V => (plaquetteAction L n k V : ℂ)) (trivialField L n k 0) B' B)
    (hH : ∀ B ∈ edgeFormSpace L n k 0, ∃ H ∈ edgeFormSpace L n k 0,
      PairsAsHessian (fun V => (plaquetteAction L n k V : ℂ))
        (trivialField L n k 0) B H)
    (hq : ∀ B ∈ edgeFormSpace L n k 0,
      leftSecondDeriv (plaquetteAction L n k) (trivialField L n k 0) B B =
        traceFinsumNorm (edgeCoboundary B) ^ 2)
    (A₁ D : edgeFormSpace L n k 0)
    (hD : PairsAsHessian (fun V => (plaquetteAction L n k V : ℂ))
      (trivialField L n k 0) A₁ D) :
    D = formCoboundaryTranspose L n k (formCoboundary L n k A₁) := by
  classical
  obtain ⟨-, -, -, c, hc⟩ := hG2 L n k 0 hL hn (Nat.zero_le k)
  have hsymc : ∀ a b : edgeFormSpace L n k 0, c.inner a b = c.inner b a := fun a b => by
    have := c.conj_inner_symm a b
    simpa using this.symm
  have hadd : ∀ a y z : edgeFormSpace L n k 0,
      c.inner a (y + z) = c.inner a y + c.inner a z := by
    intro a y z
    rw [hsymc, c.add_left, hsymc y, hsymc z]
  choose! H hHm hHp using hH
  let Hf : edgeFormSpace L n k 0 → edgeFormSpace L n k 0 := fun x => ⟨H x, hHm x x.2⟩
  let S : edgeFormSpace L n k 0 → edgeFormSpace L n k 0 := fun x =>
    formCoboundaryTranspose L n k (formCoboundary L n k x)
  have hTp : ∀ x y : edgeFormSpace L n k 0,
      traceFinsumPairing (formCoboundary L n k x : Face L n k 0 → ComplexMatrix2)
        (formCoboundary L n k y : Face L n k 0 → ComplexMatrix2) =
          ((c.inner (S x) y : ℝ) : ℂ) := by
    intro x y
    rw [← hc]
    exact (hPT L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k) (formCoboundary L n k)
      (formCoboundary L n k x) y).symm
  have hpP : ∀ x y : edgeFormSpace L n k 0,
      leftSecondDeriv (fun V => (plaquetteAction L n k V : ℂ)) (trivialField L n k 0) x y =
        ((c.inner (Hf x) y : ℝ) : ℂ) := by
    intro x y
    rw [← hc]
    exact (hHp x x.2 y y.2).symm
  have hp_symm : ∀ x y : edgeFormSpace L n k 0, c.inner (Hf x) y = c.inner (Hf y) x := by
    intro x y
    have h := hsym x x.2 y y.2
    rw [hpP, hpP] at h
    exact_mod_cast h
  have hr_symm : ∀ x y : edgeFormSpace L n k 0, c.inner (S x) y = c.inner (S y) x := by
    intro x y
    have h := traceFinsumPairing_comm (formCoboundary L n k x : Face L n k 0 → ComplexMatrix2)
      (formCoboundary L n k y : Face L n k 0 → ComplexMatrix2)
    rw [hTp, hTp] at h
    exact_mod_cast h
  have hdiag : ∀ x : edgeFormSpace L n k 0, c.inner (Hf x) x = c.inner (S x) x := by
    intro x
    have h1 : ((c.inner (Hf x) x : ℝ) : ℂ) =
        ((traceFinsumNorm (edgeCoboundary (x : Edge L n k 0 → ComplexMatrix2)) ^ 2 : ℝ) : ℂ) := by
      rw [← hpP, leftSecondDeriv_ofReal, hq x x.2]
    have h2 : c.inner (Hf x) x =
        traceFinsumNorm (edgeCoboundary (x : Edge L n k 0 → ComplexMatrix2)) ^ 2 := by
      exact_mod_cast h1
    have hnn := traceFinsumPairing_self_re_nonneg hE3 hL hn (k := k)
      (f := formCoboundary L n k x) fun p => (formCoboundary L n k x).2 p (mem_univ p)
    rw [h2, traceFinsumNorm, ← formCoboundary_apply, Real.sq_sqrt hnn, hTp, Complex.ofReal_re]
  have hpol : ∀ x y : edgeFormSpace L n k 0, c.inner (Hf x) y = c.inner (S x) y :=
    eq_of_symm_additive_diag (fun x y => c.inner (Hf x) y) (fun x y => c.inner (S x) y)
      hp_symm hr_symm (fun x y z => hadd _ y z) (fun x y z => hadd _ y z) hdiag
  have hfinal : ∀ y : edgeFormSpace L n k 0, c.inner D y = c.inner (S A₁) y := by
    intro y
    have h1 : ((c.inner D y : ℝ) : ℂ) =
        leftSecondDeriv (fun V => (plaquetteAction L n k V : ℂ)) (trivialField L n k 0) A₁ y := by
      rw [← hc]
      exact hD y y.2
    rw [hpP] at h1
    rw [← hpol]
    exact_mod_cast h1
  have hadd' := c.add_left (S A₁) (D - S A₁) (D - S A₁)
  have hS : S A₁ + (D - S A₁) = D := by simp
  rw [hS, hfinal] at hadd'
  have hz : D - S A₁ = 0 := c.definite _ (by linarith)
  exact sub_eq_zero.1 hz
end Polarisation
section Composite
variable {L n K : ℕ}
theorem prolongComp_analytic (hT1 : AnalyticNearField.CompositionAndExpTwist)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {b : CriticalBranchData L n K}
    (hb : b.IsCritical) (j : ℕ) (hj : 1 ≤ j) :
    j ≤ K → ∃ 𝒰 : Set (Edge L n K j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldMap 𝒰 (b.prolongComp j) ∧
      b.prolongComp j (trivialField L n K j) = trivialField L n K 0 := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro h1
    obtain ⟨𝒰, h𝒰, ha⟩ := hb.analytic_prolong 0 (by omega)
    exact ⟨𝒰, h𝒰, ha, hb.prolong_trivial 0 (by omega)⟩
  | succ m hm ih =>
    intro hm'
    obtain ⟨𝒰, h𝒰, ha, h1⟩ := ih (by omega)
    obtain ⟨𝒰', h𝒰', ha'⟩ := hb.analytic_prolong m (by omega)
    have hc := ((hT1 L n K (m + 1) m 0 hL hn hm' (by omega) (by omega)).1 𝒰' 𝒰
      (b.prolong m) ha').2 (b.prolongComp m) ha
    have hl1 := hb.prolong_trivial m (by omega)
    refine ⟨relPreimage 𝒰' (b.prolong m) 𝒰, ⟨hc.1, ?_⟩, hc.2, ?_⟩
    · exact ⟨h𝒰'.2, by rw [hl1]; exact h𝒰.2⟩
    · change b.prolongComp m (b.prolong m _) = _
      rw [hl1, h1]
theorem leftSecondDeriv_symm {j : ℕ} (hl : FiniteLevelFacts L n K j)
    {𝒩 : Set (Edge L n K j → ComplexMatrix2)}
    {F : (Edge L n K j → ComplexMatrix2) → ℂ}
    (hMix : MixedPartialsEqHessian 𝒩 F (trivialField L n K j))
    {B B' : Edge L n K j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n K j)
    (hB' : B' ∈ edgeFormSpace L n K j)
    (hone : trivialField L n K j ∈ fieldSpace L n K j) :
    leftSecondDeriv F (trivialField L n K j) B B' =
      leftSecondDeriv F (trivialField L n K j) B' B := by
  obtain ⟨-, -, h2⟩ := hMix univ _ (isSmoothTwoParamFamily_expTwist hl hB hB' hone)
  have t1 : curveTangent (fun s : ℝ =>
      PeriodicLattice.expTwist ((s : ℂ) • B + ((0 : ℝ) : ℂ) • B')
        (trivialField L n K j)) = B := by
    have e : (fun s : ℝ => PeriodicLattice.expTwist ((s : ℂ) • B + ((0 : ℝ) : ℂ) • B')
        (trivialField L n K j)) =
        fun s : ℝ => PeriodicLattice.expTwist ((s : ℂ) • B) (trivialField L n K j) := by
      funext s
      simp
    rw [e]
    exact curveTangent_expTwist_line hl hB hone
  have t2 : curveTangent (fun t : ℝ =>
      PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B + (t : ℂ) • B')
        (trivialField L n K j)) = B' := by
    have e : (fun t : ℝ => PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B + (t : ℂ) • B')
        (trivialField L n K j)) =
        fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B') (trivialField L n K j) := by
      funext t
      simp
    rw [e]
    exact curveTangent_expTwist_line hl hB' hone
  rw [t1, t2] at h2
  rw [← h2]
  simp only [leftSecondDeriv, mixedDirectionalDeriv]
  have e : ∀ u v : ℝ, ((v : ℂ) • B + (u : ℂ) • B') =
      algebraMap ℝ ℂ u • B' + algebraMap ℝ ℂ v • B := fun u v => add_comm _ _
  simp only [e]
end Composite
theorem exists_form (hCB : CriticalBranchExists)
    (hH1 : CriticalSecondDeriv.HessianAtCriticalPoint)
    (hN1 : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hT1 : AnalyticNearField.CompositionAndExpTwist)
    (hFib : SmoothingFibres)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hA2 : LeftChartFields.Claim)
    (hAct : ActionFacts.Statement)
    (hW : WilsonActionAnalytic)
    (hG2 : FiniteSideFormSpaces)
    (hE3 : FaceSums.FacesAndPairings)
    (hPT : RealTransposeFaceFunctionPairing)
    (hRE : AnalyticAlongExpCurves.Statement)
    {L n i : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (B : edgeFormSpace L n (i + 1) (i + 1)) :
    ∃ (A₁ : edgeFormSpace L n (i + 1) 0) (μ₁ : edgeFormSpace L n (i + 1) (i + 1)),
      FormConditions L n (i + 1) B A₁ μ₁ := by
  have hb : (chosenCriticalBranch L n (i + 1)).IsCritical :=
    Classical.epsilon_spec (hCB L n (i + 1) hL hn)
  obtain ⟨𝒰c, h𝒰c, hcA, hc1⟩ := prolongComp_analytic hT1 hL hn hb (i + 1) (by omega) le_rfl
  obtain ⟨hQ, -, -, -, ⟨𝒰M, h𝒰M, hMd, hMa, -⟩, -, -⟩ := hFib L n (i + 1) i hL hn (by omega)
  let c := chosenProlongComp L n (i + 1) (i + 1)
  let M := smoothingIter L n (i + 1) (i + 1)
  let O := trivialField L n (i + 1) (i + 1)
  let O₀ := trivialField L n (i + 1) 0
  let γ := expLineField L n (i + 1) (B : Edge L n (i + 1) (i + 1) → ComplexMatrix2)
  have hone : O ∈ fieldSpace L n (i + 1) (i + 1) := h𝒰c.1.1 h𝒰c.2
  have hone0 : O₀ ∈ fieldSpace L n (i + 1) 0 := h𝒰M.1.1 h𝒰M.2
  have hlK : FiniteLevelFacts L n (i + 1) (i + 1) := by
    have h := (hA2.2.2 L (i + 1) (i + 1) hL le_rfl).1 n hn
    exact ⟨h.1, h.2.1⟩
  have hl0 : FiniteLevelFacts L n (i + 1) 0 := by
    have h := (hA2.2.2 L (i + 1) 0 hL (Nat.zero_le _)).1 n hn
    exact ⟨h.1, h.2.1⟩
  obtain ⟨-, hMapsC, -, -⟩ := hN1 L n (i + 1) (i + 1) 0 hL hn le_rfl (Nat.zero_le _) 𝒰c h𝒰c.1
  obtain ⟨-, hcd, hcV⟩ := hMapsC _ hcA
  obtain ⟨-, hMapsM, -, hTransM⟩ :=
    hN1 L n (i + 1) 0 (i + 1) hL hn (Nat.zero_le _) le_rfl 𝒰M h𝒰M.1
  obtain ⟨-, -, hMV⟩ := hMapsM _ hMa
  let A₁ : edgeFormSpace L n (i + 1) 0 := leftDifferentialLinear c O B
  have hA₁ : (A₁ : Edge L n (i + 1) 0 → ComplexMatrix2) = leftDifferential c O B :=
    (hcV O h𝒰c.2).2 B
  obtain ⟨I, hI, hIc, hsm⟩ := hRE L n (i + 1) (i + 1) 0 hL hn le_rfl (Nat.zero_le _) O B 𝒰c c hone
    h𝒰c.2 B.2 hcA
  have hγs : IsSmoothCurveAt O I γ := isSmoothCurveAt_expTwist_line hlK B.2 hone hI
  have hγ0 : γ 0 = O := hγs.2.2.1
  let δ : ℝ → Edge L n (i + 1) 0 → ComplexMatrix2 := fun t => c (γ t)
  have hδ0 : δ 0 = O₀ := by
    change c (γ 0) = O₀
    rw [hγ0]
    exact hc1
  have hδ : IsSmoothCurveAt O₀ I δ :=
    ⟨hI, fun t ht => hcA.2.1 (hIc t ht), hδ0, fun b _ r s => hsm b r s⟩
  have hHK := hH1 L n (i + 1) (i + 1) (i + 1) hL hn le_rfl le_rfl
  have hH0 := hH1 L n (i + 1) 0 (i + 1) hL hn (Nat.zero_le _) le_rfl
  have hγd : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ :=
    hHK.1 I γ (entriesDifferentiableOn_of_smooth hγs)
  have hδd : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I δ :=
    hH0.1 I δ (entriesDifferentiableOn_of_smooth hδ)
  have htγ : curveTangent γ = B := curveTangent_expTwist_line hlK B.2 hone
  have hCK := hCu L (i + 1) (i + 1) 0 hL le_rfl (Nat.zero_le _) n hn
  have hC0 := hCu L (i + 1) 0 (i + 1) hL (Nat.zero_le _) le_rfl n hn
  have htδ : curveTangent δ = A₁ := by
    have h := (hCK.1 𝒰c c hcd O h𝒰c.2 I γ hγd hγ0).2
    rw [htγ] at h
    exact h.trans hA₁.symm
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), M (δ t) = γ t ∧
      (chosenCriticalBranch L n (i + 1)).SatisfiesMultiplierIdentity (i + 1) (γ t) := by
    have h := (tendsto_expTwist_line hlK B.2 hone).eventually
      (hb.prolongComp_section (i + 1) le_rfl)
    exact h.mono fun t ht => ⟨ht.1, ht.2.2⟩
  have hav : linearSmoothingIter L n (i + 1) (i + 1) A₁ = B := by
    have e1 : curveTangent (fun t => M (δ t)) = curveTangent γ :=
      curveTangent_congr (hnear.mono fun t ht => ht.1)
    have e3 := (hC0.1 𝒰M M hMd O₀ h𝒰M.2 I δ hδd hδ0).2
    have e2 := hQ A₁ A₁.2
    rw [← e2, ← htδ]
    exact e3.symm.trans (e1.trans htγ)
  obtain ⟨𝒩k, h𝒩k, haK⟩ := hb.analytic_energy (i + 1) le_rfl
  have hg1 := hb.gradient_trivial (i + 1) le_rfl
  have hcritK : IsRealCriticalPoint 𝒩k
      (fun V => ((chosenCriticalBranch L n (i + 1)).energy (i + 1) V : ℂ)) O :=
    ⟨hone, h𝒩k.2, haK, fun V _ => Complex.ofReal_im _, (leftGradient_indep_domain _ _ _ _).trans hg1⟩
  obtain ⟨-, hGK, -⟩ := hHK.2.2 𝒩k _ O hcritK
  obtain ⟨χ, μ, hχ, hχ0, hχd, -⟩ := exists_leftGradient_curve hGK hγs hg1
  obtain ⟨-, -, -, -, -, hgrad0, hsec⟩ := hAct L (i + 1) n hL hn
  have hcrit0 : IsRealCriticalPoint (fieldSpace L n (i + 1) 0)
      (fun V => (plaquetteAction L n (i + 1) V : ℂ)) O₀ :=
    ⟨hone0, hone0, hW L n (i + 1) hL hn, fun V _ => Complex.ofReal_im _, hgrad0⟩
  obtain ⟨hMix0, hG0, -⟩ := hH0.2.2 _ _ O₀ hcrit0
  obtain ⟨χ₀, D, hχ₀, -, hχ₀d, hpair⟩ := exists_leftGradient_curve hG0 hδ hgrad0
  rw [htδ] at hpair
  have huniv : IsOpenIntervalAroundZero (univ : Set ℝ) :=
    ⟨isOpen_univ, ordConnected_univ, mem_univ _⟩
  have hD : D = formCoboundaryTranspose L n (i + 1) (formCoboundary L n (i + 1) A₁) :=
    eq_transpose_of_pairsAsHessian hG2 hE3 hPT hL hn
      (fun x hx y hy => leftSecondDeriv_symm hl0 hMix0 hx hy hone0)
      (fun x hx => by
        obtain ⟨-, D', -, -, -, hp⟩ :=
          exists_leftGradient_curve hG0 (isSmoothCurveAt_expTwist_line hl0 hx hone0 huniv) hgrad0
        rw [curveTangent_expTwist_line hl0 hx hone0] at hp
        exact ⟨D', D'.2, hp⟩)
      hsec A₁ D hpair
  have hcont : IsContinuousCurveStartingIn 𝒰M I δ :=
    ⟨hI, hδ.2.1, by rw [hδ0]; exact h𝒰M.2, fun b hb r s => (hδ.2.2.2 b hb r s).continuousOn⟩
  have hTr := (hTransM M I δ χ μ hMa hcont hχ0 hχd).2
  have hdual : ∀ᶠ t in 𝓝 (0 : ℝ), (χ₀ t : Edge L n (i + 1) 0 → ComplexMatrix2) =
      (leftDifferentialTranspose M (δ t) (χ t) : Edge L n (i + 1) 0 → ComplexMatrix2) := by
    filter_upwards [hnear, hχ, hχ₀] with t h1 h2 h3
    obtain ⟨g, hg, hrel⟩ := h1.2
    have hgχ : g = χ t := Subtype.ext (hg.trans h2.symm)
    subst hgχ
    exact h3.trans hrel.symm
  have hDeq : D = leftDifferentialTranspose M O₀ μ := by
    apply Subtype.ext
    funext b
    have h := (hχ₀d b).unique
      ((hTr b).congr_of_eventuallyEq (hdual.mono fun t ht => congrFun ht b))
    rw [hδ0] at h
    exact h
  have hval : ∀ x : edgeFormSpace L n (i + 1) 0, (leftDifferentialLinear M O₀ x :
      Edge L n (i + 1) (i + 1) → ComplexMatrix2) = linearSmoothingIter L n (i + 1) (i + 1) x :=
    fun x => ((hMV O₀ h𝒰M.2).2 x).trans (hQ x x.2)
  have hsp : ∀ x : edgeFormSpace L n (i + 1) 0, (linearSmoothingToTop L n (i + 1) x :
      Edge L n (i + 1) (i + 1) → ComplexMatrix2) = linearSmoothingIter L n (i + 1) (i + 1) x :=
    Classical.epsilon_spec
      (p := fun T : edgeFormSpace L n (i + 1) 0 →ₗ[ℝ] edgeFormSpace L n (i + 1) (i + 1) =>
        ∀ x : edgeFormSpace L n (i + 1) 0, (T x : Edge L n (i + 1) (i + 1) → ComplexMatrix2) =
          linearSmoothingIter L n (i + 1) (i + 1) x) ⟨_, hval⟩
  have hEq : leftDifferentialLinear M O₀ = linearSmoothingToTop L n (i + 1) :=
    LinearMap.ext fun x => Subtype.ext ((hval x).trans (hsp x).symm)
  have hTq : leftDifferentialTranspose M O₀ = linearSmoothingTranspose L n (i + 1) := by
    simp only [leftDifferentialTranspose, linearSmoothingTranspose, hEq]
    rfl
  refine ⟨A₁, μ, hA₁, hav, ⟨χ, hχ, hχd⟩, ⟨χ₀, hχ₀, ?_⟩, ?_⟩
  · rw [← hD]
    exact hχ₀d
  · rw [← hD, hDeq, hTq]
theorem prolongDifferentialHolds_of (hCB : CriticalBranchExists)
    (hH1 : CriticalSecondDeriv.HessianAtCriticalPoint)
    (hN1 : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hT1 : AnalyticNearField.CompositionAndExpTwist)
    (hFib : SmoothingFibres)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hA2 : LeftChartFields.Claim)
    (hAct : ActionFacts.Statement)
    (hW : WilsonActionAnalytic)
    (hG2 : FiniteSideFormSpaces)
    (hE3 : FaceSums.FacesAndPairings)
    (hPT : RealTransposeFaceFunctionPairing)
    (hRE : AnalyticAlongExpCurves.Statement) : ProlongDifferentialHolds := by
  intro L hL k hk n hn B
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  exact exists_form hCB hH1 hN1 hT1 hFib hCu hA2 hAct hW hG2 hE3 hPT hRE hL hn B
end YangMills.Construction.Tower.ProlongDifferential
end
