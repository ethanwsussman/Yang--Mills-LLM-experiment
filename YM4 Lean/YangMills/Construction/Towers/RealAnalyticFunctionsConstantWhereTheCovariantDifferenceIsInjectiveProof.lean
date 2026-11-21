import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import YangMills.Construction.Towers.RealAnalyticFunctionsConstantWhereTheCovariantDifferenceIsInjective
import YangMills.Construction.Towers.RealAnalyticMapsAreReadInTheChartAtOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.IdentityPrincipleNearOne
open Set Filter
open YangMills.Construction.Tower YangMills.Construction.IdentityExpChart
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology Matrix.Norms.L2Operator
private def pauliX : ComplexMatrix2 := !![0, 1; 1, 0]
private def pauliZ : ComplexMatrix2 := !![1, 0; 0, -1]
private theorem pauliX_mem : pauliX ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
  · simp [pauliX, ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
private theorem pauliZ_mem : pauliZ ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]
  · simp [pauliZ, ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
private theorem pauliX_sq : pauliX ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
private theorem pauliZ_sq : pauliZ ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
private theorem eq_zero_of_commute_pauli {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (hx : pauliX * X = X * pauliX) (hz : pauliZ * X = X * pauliZ) :
    X = 0 := by
  have e₁₀ := congrFun (congrFun hx 0) 0
  have e₀₁ := congrFun (congrFun hz 0) 1
  have e₁₀' := congrFun (congrFun hz 1) 0
  have htr : X 0 0 + X 1 1 = 0 := by
    have := hX.2
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using this
  simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at e₁₀ e₀₁ e₁₀'
  have a : X 0 1 = 0 := by
    have : (2 : ℂ) * X 0 1 = 0 := by linear_combination e₀₁
    simpa using this
  have b : X 1 0 = 0 := by
    have : (2 : ℂ) * X 1 0 = 0 := by linear_combination -e₁₀'
    simpa using this
  have c : X 0 0 = 0 := by
    have : (2 : ℂ) * X 0 0 = 0 := by
      have e := congrFun (congrFun hx 0) 1
      simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two] at e
      linear_combination htr - e
    simpa using this
  have d : X 1 1 = 0 := by rw [c] at htr; simpa using htr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, b, c, d]
private theorem matExp_I_smul_of_sq_eq_one (hLog : ComplexMatrix2.UnitaryLogConjugationProperties)
    {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) (hsq : A ^ 2 = 1) {θ : ℝ}
    (hθ : 0 < θ) :
    ComplexMatrix2.matExp (Complex.I • (θ • A)) =
      (Real.cos θ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sin θ : ℂ)) • A := by
  obtain ⟨h₁, h₂, -⟩ := hLog.1 (θ • A) (ComplexMatrix2.hermitianTraceless.smul_mem θ hA)
  have hn : ComplexMatrix2.operatorNorm (θ • A) = θ := by
    have e : (θ • A) ^ 2 = ((θ : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
      rw [smul_pow, hsq]
      ext i j
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [e] at h₁
    have h00 := congrFun (congrFun h₁ 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    have h' : θ ^ 2 = ComplexMatrix2.operatorNorm (θ • A) ^ 2 := by exact_mod_cast h00
    have hnn : 0 ≤ ComplexMatrix2.operatorNorm (θ • A) := norm_nonneg _
    nlinarith [sq_nonneg (θ - ComplexMatrix2.operatorNorm (θ • A)),
      sq_nonneg (θ + ComplexMatrix2.operatorNorm (θ • A))]
  rw [h₂, hn]
  congr 1
  have hs : ComplexMatrix2.sincAngle θ = θ⁻¹ * Real.sin θ := by
    simp [ComplexMatrix2.sincAngle, hθ.ne']
  rw [hs]
  ext i j
  have hθ' : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp
private theorem commute_of_commute_matExp (hLog : ComplexMatrix2.UnitaryLogConjugationProperties)
    {A X : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) (hsq : A ^ 2 = 1) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (h : ComplexMatrix2.matExp (Complex.I • (θ • A)) * X =
      X * ComplexMatrix2.matExp (Complex.I • (θ • A))) :
    A * X = X * A := by
  rw [matExp_I_smul_of_sq_eq_one hLog hA hsq hθ] at h
  have hs : ((Complex.I * (Real.sin θ : ℂ))) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne'
  have h' : (Complex.I * (Real.sin θ : ℂ)) • (A * X) =
      (Complex.I * (Real.sin θ : ℂ)) • (X * A) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    exact add_left_cancel h
  exact smul_right_injective _ hs h'
private theorem pow_commute_of_shift {S : Type*} [AddCommGroup S] (s : S) (g : S → ComplexMatrix2)
    (w : ComplexMatrix2) (h : ∀ x, w * g (x + s) = g x * w) (N : ℕ) (hN : N • s = 0) (x : S) :
    w ^ N * g x = g x * w ^ N := by
  have key : ∀ (m : ℕ) (x : S), w ^ m * g (x + m • s) = g x * w ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      have e : x + (m + 1) • s = (x + m • s) + s := by rw [succ_nsmul]; abel
      rw [e, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]
  have := key N x
  rwa [hN, add_zero] at this
private theorem exists_analytic_injectivity_witness {E V F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E → V →ₗ[ℝ] F) (hT : ∀ (v : V) (y : E), AnalyticAt ℝ (fun y => T y v) y) (y₀ : E)
    (h₀ : Function.Injective (T y₀)) :
    ∃ H : E → ℝ, (∀ y, AnalyticAt ℝ H y) ∧ H y₀ ≠ 0 ∧
      ∀ y, H y ≠ 0 → Function.Injective (T y) := by
  obtain ⟨S, hS⟩ := (T y₀).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h₀)
  let b := Module.finBasis ℝ V
  refine ⟨fun y => LinearMap.det (S ∘ₗ T y), fun y => ?_, ?_, fun y hy => ?_⟩
  · have e : (fun y => LinearMap.det (S ∘ₗ T y)) =
        fun y => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ V)), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, LinearMap.toMatrix b b (S ∘ₗ T y) (σ i) i := by
      funext y
      rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
    rw [e]
    refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
    refine Finset.analyticAt_fun_prod _ fun i _ => ?_
    let φ : F →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((b.coord (σ i)) ∘ₗ S)
    refine ((φ.analyticAt _).comp (hT (b i) y)).congr (Eventually.of_forall fun z => ?_)
    simp [φ, LinearMap.toMatrix_apply]
  · show LinearMap.det (S ∘ₗ T y₀) ≠ 0
    rw [hS]
    simp
  · have hy' : LinearMap.det (S ∘ₗ T y) ≠ 0 := hy
    have hinj : Function.Injective (S ∘ₗ T y) :=
      fun u v h => (LinearMap.equivOfDetNeZero _ hy').injective h
    exact Function.Injective.of_comp (f := S) hinj
private theorem analyticOnNhd_of_realAnalyticToRealSpace
    (hRA : RealAnalyticity.CoordRealAnalyticIffAnalytic) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {D : Set V} {g : V → ℝ}
    (h : IsRealAnalyticToRealSpace D g) : AnalyticOnNhd ℝ g D := by
  let x := (Module.finBasis ℝ V).equivFun
  let xL : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := x.toContinuousLinearEquiv
  have hreal : PowerSeries.RealSeries.realEmbed '' (x '' D) ⊆
      Coordinates.ComplexCoordinates.realLocus (Module.finrank ℝ V) := by
    rintro _ ⟨u, -, rfl⟩ j
    simp [PowerSeries.RealSeries.realEmbed]
  have hpre : (fun (u : Fin (Module.finrank ℝ V) → ℝ) (j : Fin (Module.finrank ℝ V)) => (u j : ℂ)) ⁻¹'
      (PowerSeries.RealSeries.realEmbed '' (x '' D)) = x '' D := by
    ext u
    constructor
    · rintro ⟨v, hv, hvu⟩
      have : v = u := by
        funext j
        have := congrFun hvu j
        simpa [PowerSeries.RealSeries.realEmbed] using this
      exact this ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have h1 := h 1 (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  have h2 := h1.2 _ x
  have key := (hRA _ _ (fun z => ((g (x.symm fun i => (z i).re) : ℝ) : ℂ)) hreal).1
    ⟨h2.1, fun p hp => by
      obtain ⟨c, hc⟩ := h2.2 p hp
      refine ⟨c, hc.mono fun z hz => ?_⟩
      refine Pi.hasSum.2 fun i => ?_
      have hz' := (Pi.hasSum.1 hz) i
      simpa [PowerSeries.RealSeries.realEmbed] using hz'⟩
  rw [hpre] at key
  intro v hv
  have h3 := (Complex.reCLM.analyticAt _).comp (key.2 (x v) ⟨v, hv, rfl⟩)
  have h4 : AnalyticAt ℝ (fun u : Fin (Module.finrank ℝ V) → ℝ => g (x.symm u)) (x v) :=
    h3.congr (Eventually.of_forall fun u => by simp)
  let xC : V →L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := xL
  have h4' : AnalyticAt ℝ (fun u : Fin (Module.finrank ℝ V) → ℝ => g (x.symm u)) (xC v) := h4
  have h5 := AnalyticAt.comp h4' (xC.analyticAt v)
  refine h5.congr (Eventually.of_forall fun u => ?_)
  show g (x.symm (x u)) = g u
  rw [x.symm_apply_apply]
private theorem matExp_neg (Z : ComplexMatrix2) :
    ComplexMatrix2.matExp (-Z) = (ComplexMatrix2.matExp Z)⁻¹ := Matrix.exp_neg Z
private theorem matExp_pow (Z : ComplexMatrix2) (m : ℕ) :
    ComplexMatrix2.matExp Z ^ m = ComplexMatrix2.matExp (m • Z) :=
  (Matrix.exp_nsmul m Z).symm
section Edges
variable {L n k j : ℕ}
private theorem positive_or_opposite_positive (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem forwardFrom_positive (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem finite_vertex [Finite (PositiveEdge L n k j)] : Finite (Vertex L n k j) := by
  refine Finite.of_injective (fun x : Vertex L n k j =>
    (⟨PeriodicLattice.Bond.forwardFrom x 0, forwardFrom_positive x 0⟩ : PositiveEdge L n k j)) ?_
  intro x x' h
  exact congrArg (fun b : PositiveEdge L n k j => b.1.source) h
abbrev _root_.YangMills.DeltaSharedProofs.p500448 := @finite_vertex
private theorem field_of_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem identityChartPoint_of_positive
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    identityChartPoint y b = ComplexMatrix2.matExp (Complex.I • (y ⟨b, h⟩).toMatrix) := by apply _root_.YangMills.Construction.Tower.IdentityChart.identityChartPoint_of_positive <;> assumption
private theorem restrict_identityChartPoint (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    restrictToPositiveEdges (identityChartPoint y) = expFamily y := by apply _root_.YangMills.Construction.Tower.IdentityChart.restrictToPositiveEdges_identityChartPoint <;> assumption
private theorem covDiff_of_positive (y : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    (g : Vertex L n k j → ComplexMatrix2) {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    covDiff (identityChartPoint y) g b =
      ComplexMatrix2.matExp (Complex.I • (y ⟨b, h⟩).toMatrix) * g b.target *
        ComplexMatrix2.matExp (-(Complex.I • (y ⟨b, h⟩).toMatrix)) - g b.source := by
  simp only [covDiff, extendOddly, if_pos h]
  rw [identityChartPoint_of_positive y h, ComplexMatrix2.conjugateBy, matExp_neg]
private def edgeExponent (b : PositiveEdge L n k j) :
    (PositiveEdge L n k j → ComplexMatrix2.LieElement) →ₗ[ℝ] ComplexMatrix2 where
  toFun y := Complex.I • (y b).toMatrix
  map_add' y y' := smul_add _ (y b).toMatrix (y' b).toMatrix
  map_smul' _ _ := smul_comm _ _ _
private def twistedDiff (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    (Vertex L n k j → ComplexMatrix2.LieElement) →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2) where
  toFun g b := ComplexMatrix2.matExp (edgeExponent b y) * (g b.1.target).toMatrix *
    ComplexMatrix2.matExp (-edgeExponent b y) - (g b.1.source).toMatrix
  map_add' g g' := by
    funext b
    have e₁ : ((g + g') b.1.target).toMatrix = (g b.1.target).toMatrix + (g' b.1.target).toMatrix :=
      rfl
    have e₂ : ((g + g') b.1.source).toMatrix = (g b.1.source).toMatrix + (g' b.1.source).toMatrix :=
      rfl
    show ComplexMatrix2.matExp (edgeExponent b y) * ((g + g') b.1.target).toMatrix *
      ComplexMatrix2.matExp (-edgeExponent b y) - ((g + g') b.1.source).toMatrix = _
    rw [e₁, e₂, mul_add, add_mul]
    simp only [Pi.add_apply]
    abel
  map_smul' r g := by
    funext b
    have e₁ : ((r • g) b.1.target).toMatrix = r • (g b.1.target).toMatrix := rfl
    have e₂ : ((r • g) b.1.source).toMatrix = r • (g b.1.source).toMatrix := rfl
    show ComplexMatrix2.matExp (edgeExponent b y) * ((r • g) b.1.target).toMatrix *
      ComplexMatrix2.matExp (-edgeExponent b y) - ((r • g) b.1.source).toMatrix = _
    rw [e₁, e₂, mul_smul_comm, smul_mul_assoc]
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]
private theorem covDiffInjective_iff (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    CovDiffInjective (identityChartPoint y) ↔ Function.Injective (twistedDiff y) := by
  constructor
  · intro hI
    refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
    let g : Vertex L n k j → ComplexMatrix2 := fun x => (u x).toMatrix
    have hg : g ∈ vertexFunctionSpace L n k j := fun x _ => (u x).2
    have key : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        covDiff (identityChartPoint y) g b = 0 := by
      intro b h
      rw [covDiff_of_positive y g h]
      exact congrFun hu ⟨b, h⟩
    have hD : covDiff (identityChartPoint y) g = 0 := by
      funext b
      by_cases h : b.IsPositivelyOriented
      · exact key b h
      · have h' := (positive_or_opposite_positive b).resolve_left h
        have hz := key _ h'
        simp only [covDiff, extendOddly, if_pos h'] at hz
        simp only [covDiff, extendOddly, if_neg h]
        rw [hz, neg_zero]
        rfl
    have h0 := hI g hg hD
    funext x
    exact Subtype.ext (congrFun h0 x)
  · intro hI g hg hD
    let u : Vertex L n k j → ComplexMatrix2.LieElement :=
      fun x => (⟨g x, hg x (mem_univ _)⟩ : ComplexMatrix2.hermitianTraceless)
    have hu : twistedDiff y u = 0 := by
      funext b
      have e := covDiff_of_positive y g b.2
      rw [hD] at e
      exact e.symm
    have h0 := hI (hu.trans (map_zero _).symm)
    funext x
    exact congrArg ComplexMatrix2.LieElement.toMatrix (congrFun h0 x)
private theorem twistedDiff_analyticAt [Fintype (PositiveEdge L n k j)]
    (v : Vertex L n k j → ComplexMatrix2.LieElement)
    (y₀ : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    AnalyticAt ℝ (fun y => twistedDiff y v) y₀ := by
  refine AnalyticAt.pi fun b => ?_
  let Z : (PositiveEdge L n k j → ComplexMatrix2.LieElement) →L[ℝ] ComplexMatrix2 :=
    LinearMap.toContinuousLinearMap (edgeExponent b)
  have h₁ : AnalyticAt ℝ (fun y => ComplexMatrix2.matExp (Z y)) y₀ :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (Z y₀)).comp (Z.analyticAt y₀)
  have h₂ : AnalyticAt ℝ (fun y => ComplexMatrix2.matExp ((-Z) y)) y₀ :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) ((-Z) y₀)).comp ((-Z).analyticAt y₀)
  exact ((h₁.mul analyticAt_const).mul h₂).sub analyticAt_const
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : GroupLieProduct.IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    PowerExpCharts.HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem analyticOnNhd_in_chart (hOn : IdentityChartOnFields)
    (hInv : ChartAndBallImages.Statement)
    (hRead : AnalyticReadInExpChartStatement)
    (hRA : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) [inst : Fintype (PositiveEdge L n k j)] {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℝ} (hF : IsAnalyticFieldFunction 𝒰 F)
    {A : Set (PositiveEdge L n k j → ComplexMatrix2.LieElement)} (hA : IsOpen A)
    (hAs : A ⊆ lieBall (PositiveEdge L n k j) (1 / 2))
    (hAU : identityChartPoint '' A ⊆ 𝒰) :
    AnalyticOnNhd ℝ (fun y => F (identityChartPoint y)) A := by
  obtain ⟨hopen, iF, hra⟩ := hF
  obtain rfl := Subsingleton.elim iF inst
  have : Nonempty (PositiveEdge L n k j) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, forwardFrom_positive 0 0⟩⟩
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hR := hRead (PositiveEdge L n k j) (PositiveEdge L n k j) β
  have hC := (hInv (PositiveEdge L n k j)).1
  obtain ⟨-, -, -, hpts, hop, -⟩ := hOn L n k j hL hn hj
  have hfield : ∀ y ∈ A, fieldOfPositiveValues (expFamily y) = identityChartPoint y := fun y hy => by
    rw [← restrict_identityChartPoint y, field_of_restrict (hpts y (hAs hy)).1]
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  have hfield𝒰 : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => field_of_restrict (hopen.1 hU)
  have hrest : PowerExpCharts.IsLocallyHolomorphicRestriction (PowerExpCharts.HolomorphicScalar β)
      Complex.ofReal (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : GroupLieProduct.asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (GroupLieProduct.Subspaces.groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hfield𝒰 hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  let O : Set (PositiveEdge L n k j → ComplexMatrix2) :=
    restrictToPositiveEdges '' (identityChartPoint '' A)
  have hO : specialUnitaryPower.IsOpenSubset O := (hop A hA hAs).2
  have hsub : O ⊆ expImage (PositiveEdge L n k j) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hAs hy, (restrict_identityChartPoint y).symm⟩
  have hdom : pullbackDomain O = A := by
    ext y
    constructor
    · rintro ⟨hys, _, ⟨y', hy', rfl⟩, e⟩
      rw [restrict_identityChartPoint] at e
      rw [hC.1 hys (hAs hy') e.symm]
      exact hy'
    · intro hy
      exact ⟨hAs hy, _, ⟨y, hy, rfl⟩, restrict_identityChartPoint y⟩
  have hr' : PowerExpCharts.IsLocallyHolomorphicRestriction (PowerExpCharts.HolomorphicScalar β)
      Complex.ofReal O f := by
    intro p hp
    have hbig : O ⊆ restrictToPositiveEdges '' 𝒰 := image_mono hAU
    obtain ⟨W, Φ, h1, h2, h3⟩ := hrest p (hbig hp)
    exact ⟨W, Φ, h1, h2, fun x hx hxW => h3 x (hbig hx) hxW⟩
  have hreal := ((hR O hO hsub).1 f).1 hr'
  rw [hdom] at hreal
  refine (analyticOnNhd_of_realAnalyticToRealSpace hRA hreal).congr hA fun y hy => ?_
  show F (fieldOfPositiveValues (expFamily y)) = F (identityChartPoint y)
  rw [hfield y hy]
end Edges
section Twist
variable {L n k : ℕ}
private theorem meshSize_top :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem nsmul_unitStep_eq_zero (μ : Fin 4) :
    (2 * L ^ n) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ = 0 := by
  apply Subtype.ext
  have e : (((2 * L ^ n) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ :
      Vertex L n k k) : PeriodicLattice.FourTorus L n) =
      (2 * L ^ n) • (PeriodicLattice.pointOnAxis L n μ 1) := by
    rw [AddSubmonoidClass.coe_nsmul]
    show (2 * L ^ n) • PeriodicLattice.pointOnAxis L n μ
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) = _
    rw [meshSize_top]
  rw [e]
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← AddCircle.coe_nsmul]
    have e' : (2 * L ^ n) • (1 : ℝ) = PeriodicLattice.torusSide L n := by
      simp [PeriodicLattice.torusSide]
    rw [e']
    exact AddCircle.coe_period _
  · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
private theorem unitStep_one_ne_zero :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) 1 ≠
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) 0 := by
  intro h
  have h0 := congrFun (congrArg Subtype.val h) 0
  change PeriodicLattice.pointOnAxis L n 1
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) 0 =
    PeriodicLattice.pointOnAxis L n 0
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) 0 at h0
  rw [meshSize_top] at h0
  simp only [PeriodicLattice.pointOnAxis, Pi.single_eq_same] at h0
  rw [Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 1)] at h0
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).1 h0.symm
  have hm' : (m : ℝ) * (2 * (L : ℝ) ^ n) = 1 := by
    simpa [PeriodicLattice.torusSide] using hm
  have hz : m * (2 * (L : ℤ) ^ n) = 1 := by exact_mod_cast hm'
  have : 2 * (m * (L : ℤ) ^ n) = 1 := by linarith
  omega
private def pauliXVec : ComplexMatrix2.LieElement :=
  (⟨pauliX, pauliX_mem⟩ : ComplexMatrix2.hermitianTraceless)
private def pauliZVec : ComplexMatrix2.LieElement :=
  (⟨pauliZ, pauliZ_mem⟩ : ComplexMatrix2.hermitianTraceless)
private def twist (L n k : ℕ) : PositiveEdge L n k k → ComplexMatrix2.LieElement :=
  open Classical in fun b =>
    if b.1.target - b.1.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) 0 then
      pauliXVec
    else if b.1.target - b.1.source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) 1 then pauliZVec
    else 0
private theorem commute_along_axis (hLog : ComplexMatrix2.UnitaryLogConjugationProperties) {ε : ℝ}
    (hε : 0 < ε) (hπ : ((2 * L ^ n : ℕ) : ℝ) * ε < Real.pi) (hn : 0 < (L : ℝ))
    (y : PositiveEdge L n k k → ComplexMatrix2.LieElement) {g : Vertex L n k k → ComplexMatrix2}
    (hD : covDiff (identityChartPoint y) g = 0) (μ : Fin 4) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) (hsq : A ^ 2 = 1)
    (hy : ∀ x : Vertex L n k k,
      (y ⟨PeriodicLattice.Bond.forwardFrom x μ, forwardFrom_positive x μ⟩).toMatrix = ε • A)
    (x : Vertex L n k k) : A * g x = g x * A := by
  let Z : ComplexMatrix2 := Complex.I • (ε • A)
  have hinv : ComplexMatrix2.matExp (-Z) * ComplexMatrix2.matExp Z = 1 := by
    rw [matExp_neg]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  have hstep : ∀ x : Vertex L n k k, ComplexMatrix2.matExp Z *
      g (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) =
        g x * ComplexMatrix2.matExp Z := by
    intro x
    have h := congrFun hD (PeriodicLattice.Bond.forwardFrom x μ)
    rw [covDiff_of_positive y g (forwardFrom_positive x μ), hy x] at h
    have h' : ComplexMatrix2.matExp Z *
        g (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) *
        ComplexMatrix2.matExp (-Z) = g x := sub_eq_zero.1 h
    calc ComplexMatrix2.matExp Z *
          g (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ)
        = ComplexMatrix2.matExp Z *
            g (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) *
            (ComplexMatrix2.matExp (-Z) * ComplexMatrix2.matExp Z) := by rw [hinv, mul_one]
      _ = g x * ComplexMatrix2.matExp Z := by rw [← mul_assoc, h']
  have hc := pow_commute_of_shift _ g _ hstep (2 * L ^ n) (nsmul_unitStep_eq_zero μ) x
  have e : (2 * L ^ n) • Z = Complex.I • ((((2 * L ^ n : ℕ) : ℝ) * ε) • A) := by
    show (2 * L ^ n) • (Complex.I • (ε • A)) = _
    rw [mul_smul (((2 * L ^ n : ℕ) : ℝ)) ε A, smul_comm Complex.I (((2 * L ^ n : ℕ) : ℝ)),
      Nat.cast_smul_eq_nsmul ℝ]
  rw [matExp_pow, e] at hc
  have hpos : 0 < ((2 * L ^ n : ℕ) : ℝ) * ε := by
    refine mul_pos ?_ hε
    push_cast
    positivity
  exact commute_of_commute_matExp hLog hA hsq hpos hπ hc
private theorem covDiffInjective_twist (hLog : ComplexMatrix2.UnitaryLogConjugationProperties)
    {ε : ℝ} (hε : 0 < ε) (hπ : ((2 * L ^ n : ℕ) : ℝ) * ε < Real.pi) (hL : 0 < (L : ℝ)) :
    CovDiffInjective (identityChartPoint (ε • twist L n k)) := by
  intro g hg hD
  funext x
  refine eq_zero_of_commute_pauli (hg x (mem_univ _)) ?_ ?_
  · refine commute_along_axis hLog hε hπ hL _ hD 0 pauliX_mem pauliX_sq (fun x => ?_) x
    show ε • (twist L n k ⟨_, _⟩).toMatrix = _
    have : twist L n k ⟨PeriodicLattice.Bond.forwardFrom x 0, forwardFrom_positive x 0⟩ =
        pauliXVec :=
      if_pos (by simp [PeriodicLattice.Bond.forwardFrom])
    rw [this]
    rfl
  · refine commute_along_axis hLog hε hπ hL _ hD 1 pauliZ_mem pauliZ_sq (fun x => ?_) x
    show ε • (twist L n k ⟨_, _⟩).toMatrix = _
    have e : (PeriodicLattice.Bond.forwardFrom x 1).target -
        (PeriodicLattice.Bond.forwardFrom x 1).source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) 1 := by
      simp [PeriodicLattice.Bond.forwardFrom]
    have : twist L n k ⟨PeriodicLattice.Bond.forwardFrom x 1, forwardFrom_positive x 1⟩ =
        pauliZVec := by
      refine (if_neg ?_).trans (if_pos e)
      show (PeriodicLattice.Bond.forwardFrom x 1).target -
        (PeriodicLattice.Bond.forwardFrom x 1).source ≠ _
      rw [e]
      exact unitStep_one_ne_zero
    rw [this]
    rfl
end Twist
private theorem mem_nhdsWithin_of_isOpenNhdOfOne {L n k j : ℕ}
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    𝒰 ∈ 𝓝[fieldSpace L n k j] trivialField L n k j := by
  obtain ⟨⟨hsub, O₀, hO₀, e⟩, h1⟩ := h
  have hmem : restrictToPositiveEdges (trivialField L n k j) ∈ O₀ := by
    have : restrictToPositiveEdges (trivialField L n k j) ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, h1, rfl⟩
    rw [e] at this
    exact this.1
  refine mem_nhdsWithin.2 ⟨restrictToPositiveEdges ⁻¹' O₀,
    hO₀.preimage (continuous_pi fun b => continuous_apply _), hmem, ?_⟩
  rintro V ⟨hV, hVc⟩
  have h2 : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := by
    rw [e]
    exact ⟨hV, fun b => hVc.1 b (mem_univ _)⟩
  obtain ⟨U, hU, hUV⟩ := h2
  rw [← field_of_restrict hVc, ← hUV, field_of_restrict (hsub hU)]
  exact hU
theorem holds (hOn : IdentityChartOnFields)
    (hInv : ChartAndBallImages.Statement)
    (hRead : AnalyticReadInExpChartStatement)
    (hRA : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (hLog : ComplexMatrix2.UnitaryLogConjugationProperties) : IdentityPrincipleNearOneStatement := by
  intro L n k hL hn _ 𝒰 f c h𝒰 hf hnear
  obtain ⟨-, inst, -⟩ := id hf
  have hfin : Finite (Vertex L n k k) := finite_vertex
  have hL0 : 0 < (L : ℝ) := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  obtain ⟨hsO, h0s, -, hpts, -, htend, -, hball, hnhds, -⟩ := hOn L n k k hL hn le_rfl
  have hmemField : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k k → ComplexMatrix2.LieElement),
      identityChartPoint y ∈ fieldSpace L n k k := by
    filter_upwards [hsO.mem_nhds h0s] with y hy
    exact (hpts y hy).1
  have htend' : Tendsto (identityChartPoint (L := L) (n := n) (k := k) (j := k)) (𝓝 0)
      (𝓝[fieldSpace L n k k] trivialField L n k k) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, hmemField⟩
  have hB : ∀ᶠ y in 𝓝 (0 : PositiveEdge L n k k → ComplexMatrix2.LieElement),
      y ∈ lieBall (PositiveEdge L n k k) (1 / 2) ∧ identityChartPoint y ∈ 𝒰 ∧
        (CovDiffInjective (identityChartPoint y) → f (identityChartPoint y) = c) :=
    Filter.Eventually.and (hsO.mem_nhds h0s)
      (Filter.Eventually.and (htend' (mem_nhdsWithin_of_isOpenNhdOfOne h𝒰))
        (htend'.eventually hnear))
  obtain ⟨r, hr, hprop⟩ := Metric.eventually_nhds_iff_ball.1 hB
  have hF : AnalyticOnNhd ℝ (fun y => f (identityChartPoint y)) (Metric.ball 0 r) :=
    analyticOnNhd_in_chart hOn hInv hRead hRA hL hn le_rfl hf Metric.isOpen_ball
      (fun y hy => (hprop y hy).1) (by
        rintro _ ⟨y, hy, rfl⟩
        exact (hprop y hy).2.1)
  have hlim : Tendsto (fun ε : ℝ => ε • twist L n k) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun ε : ℝ => ε • twist L n k := continuous_id.smul continuous_const
    simpa using h.tendsto 0
  have hlim₂ : Tendsto (fun ε : ℝ => ((2 * L ^ n : ℕ) : ℝ) * ε) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun ε : ℝ => ((2 * L ^ n : ℕ) : ℝ) * ε :=
      continuous_const.mul continuous_id
    simpa using h.tendsto 0
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ε • twist L n k ∈ Metric.ball (0 : PositiveEdge L n k k →
      ComplexMatrix2.LieElement) r ∧ ((2 * L ^ n : ℕ) : ℝ) * ε < Real.pi :=
    Filter.Eventually.and (hlim (Metric.ball_mem_nhds _ hr)) (hlim₂ (Iio_mem_nhds Real.pi_pos))
  obtain ⟨ε, ⟨hεB, hεπ⟩, hε⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ ∧ ε ∈ Ioi (0 : ℝ)).exists
  have hinj := (covDiffInjective_iff (ε • twist L n k)).1
    (covDiffInjective_twist (k := k) hLog hε hεπ hL0)
  obtain ⟨H, hHa, hH0, hHinj⟩ := exists_analytic_injectivity_witness
    (twistedDiff (L := L) (n := n) (k := k) (j := k)) (fun v y => twistedDiff_analyticAt v y)
    (ε • twist L n k) hinj
  have hEq : ∀ y ∈ Metric.ball (0 : PositiveEdge L n k k → ComplexMatrix2.LieElement) r,
      f (identityChartPoint y) = c := by
    intro y₀ hy₀
    by_contra hne
    have hcont : ContinuousAt (fun y => f (identityChartPoint y)) y₀ := (hF y₀ hy₀).continuousAt
    have hnear₀ : ∀ᶠ y in 𝓝 y₀,
        y ∈ Metric.ball (0 : PositiveEdge L n k k → ComplexMatrix2.LieElement) r ∧
          f (identityChartPoint y) ≠ c :=
      Filter.Eventually.and (Metric.isOpen_ball.mem_nhds hy₀) (hcont.eventually_ne hne)
    have hzero : H =ᶠ[𝓝 y₀] 0 := by
      filter_upwards [hnear₀] with y hy
      by_contra hHy
      exact hy.2 ((hprop y hy.1).2.2 ((covDiffInjective_iff y).2 (hHinj y hHy)))
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun y _ => hHa y) (convex_ball _ _).isPreconnected hy₀ hzero
    exact hH0 (hall hεB)
  obtain ⟨δ, hδ, hsub⟩ := hball _ (Metric.ball_mem_nhds _ hr)
  filter_upwards [hnhds δ hδ] with W hW
  obtain ⟨y, hy, rfl⟩ := hsub hW
  exact hEq y hy
end YangMills.Construction.Tower.IdentityPrincipleNearOne
end
