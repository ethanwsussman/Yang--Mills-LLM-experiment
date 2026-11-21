import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Lattice.AverageOfAConfigurationTrivialInsideTwoBlocksProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASideProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.RealLinearMaps
open Matrices Matrices.GroupLieProduct LeftChartFields
section Chart
variable {σ : Type} [Fintype σ]
def coordsOfTuple (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    (σ → ComplexMatrix2.traceless) →ₗ[ℂ] Coordinates.ComplexCoordinates (Fintype.card σ * 3) where
  toFun s w := β.repr (s (ν.symm (finProdFinEquiv.symm w).1)) (finProdFinEquiv.symm w).2
  map_add' s s' := by
    funext w
    simp
  map_smul' c s := by
    funext w
    simp
theorem tupleOfCoords_coordsOfTuple (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (s : σ → ComplexMatrix2.traceless) :
    tupleOfCoords β ν (coordsOfTuple β ν s) = fun i => (s i : ComplexMatrix2) := by
  funext i
  have h := congrArg Subtype.val (β.sum_repr (s i))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  simp only [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, coordsOfTuple,
    LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact h
def matrixOfCoords : Coordinates.ComplexCoordinates 4 →ₗ[ℂ] ComplexMatrix2 where
  toFun := Coordinates.ComplexCoordinates.matrixEquiv.symm
  map_add' z z' := by
    ext i j
    simp [Coordinates.ComplexCoordinates.matrixEquiv]
  map_smul' c z := by
    ext i j
    simp [Coordinates.ComplexCoordinates.matrixEquiv]
theorem exists_hasDerivAt_traceless_line
    (hm : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    (h0 : (0 : σ → ComplexMatrix2) ∈ O)
    (hf : IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv O f) :
    ∃ Λ : (σ → ComplexMatrix2.traceless) →ₗ[ℂ] ComplexMatrix2, ∀ s : σ → ComplexMatrix2.traceless,
      HasDerivAt (fun t : ℂ => f (t • fun i => (s i : ComplexMatrix2))) (Λ s) 0 := by
  let ν : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let T := tupleOfCoords β ν
  let g := Coordinates.ComplexCoordinates.matrixEquiv ∘ f ∘ T
  have hh := hf.2 ν
  have hT0 : T 0 = 0 := by
    have := tupleOfCoords_coordsOfTuple β ν (0 : σ → ComplexMatrix2.traceless)
    simp at this
    exact this
  have h0' : (0 : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) ∈ T ⁻¹' O := by
    show T 0 ∈ O
    rw [hT0]
    exact h0
  obtain ⟨Lr, hL⟩ := ((hm.1 _ _ hh.1).1 4 g hh).2.2.1 0 h0'
  have hL' : HasFDerivAt g Lr 0 := hasFDerivAt_of_restrictScalars ℝ hL rfl
  refine ⟨matrixOfCoords ∘ₗ Lr.toLinearMap ∘ₗ coordsOfTuple β ν, fun s => ?_⟩
  let c := coordsOfTuple β ν s
  have hline : HasDerivAt (fun t : ℂ => t • c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const c
  have hL0 : HasFDerivAt g Lr ((0 : ℂ) • c) := by simpa using hL'
  have hg : HasDerivAt (fun t : ℂ => g (t • c)) (Lr c) 0 := hL0.comp_hasDerivAt (0 : ℂ) hline
  have hE := (matrixOfCoords.toContinuousLinearMap.hasFDerivAt (x := g ((0 : ℂ) • c)))
  have hfin := hE.comp_hasDerivAt (0 : ℂ) hg
  refine hfin.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  have e : T (t • c) = t • fun i => (s i : ComplexMatrix2) := by
    have h1 := tupleOfCoords_coordsOfTuple β ν (t • s)
    rw [map_smul] at h1
    refine h1.trans ?_
    funext i
    simp
  show f (t • fun i => (s i : ComplexMatrix2)) = matrixOfCoords (g (t • c))
  simp only [g, Function.comp]
  rw [e]
  exact (Coordinates.ComplexCoordinates.matrixEquiv.symm_apply_apply _).symm
theorem exists_hasDerivAt_log_chart {ι : Type} [Fintype ι]
    (hm : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2} (hΦ : IsHolomorphicToUnimodular β W Φ)
    {p : ι ⊕ Empty → ComplexMatrix2} (hp : p ∈ W) :
    ∃ Λ : (ι ⊕ Empty → ComplexMatrix2.traceless) →ₗ[ℂ] ComplexMatrix2,
      ∀ s : ι ⊕ Empty → ComplexMatrix2.traceless,
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
        (Φ (expChartAt p (t • fun i => (s i : ComplexMatrix2))) * (Φ p)⁻¹)) (Λ s) 0 := by
  obtain ⟨O, h0, -, hO⟩ := hΦ.2.2.2 p hp
  exact exists_hasDerivAt_traceless_line hm β h0 hO
end Chart
section Level
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem inv_inv_of_mem_complexGaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem fieldOfPositiveValues_exp_mul (V A : Edge L n k j → ComplexMatrix2) :
    fieldOfPositiveValues (fun b : PositiveEdge L n k j =>
      ComplexMatrix2.matExp (Complex.I • A b.1) * V b.1) = PeriodicLattice.expTwist A V := by
  classical
  funext b
  unfold fieldOfPositiveValues PeriodicLattice.expTwist
  by_cases hb : b.IsPositivelyOriented
  · simp [hb]
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp [hb, hr]
theorem fieldOfPositiveValues_self {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues (fun b : PositiveEdge L n k j => V b.1) = V := by apply _root_.YangMills.Construction.Tower.CovDiffStep.fieldOfPositiveValues_restrict <;> assumption
theorem expTwist_zero_smul {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (B : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  have h := fieldOfPositiveValues_exp_mul V ((0 : ℂ) • B)
  rw [← h]
  simpa [NormedSpace.exp_zero] using fieldOfPositiveValues_self hV
theorem mem_complexEdgeForms_of_mem {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem hasDerivAt_ofReal_of_complex {g : ℂ → ComplexMatrix2} {d : ComplexMatrix2}
    (h : HasDerivAt g d 0) : HasDerivAt (fun t : ℝ => g (t : ℂ)) d 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.hasDerivAt_ofReal_of_complex <;> assumption
theorem exists_linear_log_deriv
    (hm : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {𝔇 : Set (Edge L n k j → ComplexMatrix2)}
    {h : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hh : MeanStableFields.IsHolomorphicOnFields β 𝔇 h)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ 𝔇) :
    ∃ Λ : complexEdgeForms L n k j →ₗ[ℂ] ComplexMatrix2, ∀ B : complexEdgeForms L n k j,
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries (h (PeriodicLattice.expTwist
        (t • (B : Edge L n k j → ComplexMatrix2)) V) * (h V)⁻¹)) (Λ B) 0 := by
  obtain ⟨h𝔇, inst, hΦ⟩ := hh
  have hVc : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := h𝔇.1 hV
  let p : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 :=
    asGroupFactors (restrictToPositiveEdges V)
  have hp : p ∈ asGroupFactors '' (restrictToPositiveEdges '' 𝔇) := ⟨_, ⟨V, hV, rfl⟩, rfl⟩
  obtain ⟨Λ₀, hΛ₀⟩ := exists_hasDerivAt_log_chart hm β hΦ hp
  let A : complexEdgeForms L n k j →ₗ[ℂ] (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2.traceless) :=
    { toFun := fun B => Sum.elim
        (fun b => ⟨Complex.I • (B : Edge L n k j → ComplexMatrix2) b.1,
          ComplexMatrix2.traceless.smul_mem _ (B.2.1 b.1 b.2)⟩) Empty.elim
      map_add' := fun B B' => by
        funext q
        rcases q with b | e
        · apply Subtype.ext
          simp [smul_add]
        · exact e.elim
      map_smul' := fun c B => by
        funext q
        rcases q with b | e
        · apply Subtype.ext
          simp [smul_comm c Complex.I]
        · exact e.elim }
  refine ⟨Λ₀ ∘ₗ A, fun B => ?_⟩
  have key : ∀ t : ℂ, (fun b : PositiveEdge L n k j =>
      expChartAt p (t • fun i => ((A B i : ComplexMatrix2.traceless) : ComplexMatrix2)) (.inl b)) =
      fun b => ComplexMatrix2.matExp (Complex.I • (t • (B : Edge L n k j → ComplexMatrix2)) b.1) *
        V b.1 := by
    intro t
    funext b
    simp [expChartAt, p, A, asGroupFactors, restrictToPositiveEdges, smul_comm t Complex.I]
  have main0 : (fun b : PositiveEdge L n k j => p (.inl b)) = fun b => V b.1 := rfl
  have h1 := hΛ₀ (A B)
  simp only [key, main0, fieldOfPositiveValues_exp_mul, fieldOfPositiveValues_self hVc] at h1
  exact h1
theorem exists_real_linear_log_deriv (hA : LeftChartFields.Claim)
    (hm : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {𝔇 : Set (Edge L n k j → ComplexMatrix2)}
    {h : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hh : MeanStableFields.IsHolomorphicOnFields β 𝔇 h)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ 𝔇)
    (hcurve : ∀ B ∈ edgeFormSpace L n k j, ∃ W : ℝ → ComplexMatrix2, DifferentiableAt ℝ W 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, W t ∈ PeriodicLattice.compactGaugeGroup ∧
        W t = h (PeriodicLattice.expTwist ((t : ℂ) • B) V)) :
    ∃ Λ : edgeFormSpace L n k j →ₗ[ℝ] ComplexMatrix2.hermitianTraceless,
      ∀ B : edgeFormSpace L n k j, (Λ B : ComplexMatrix2) =
      logDirectionalDeriv ℂ (fun X => h (PeriodicLattice.expTwist X V)) (h V)
        (B : Edge L n k j → ComplexMatrix2) := by
  have hVc : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := hh.1.1 hV
  obtain ⟨Λc, hΛ⟩ := exists_linear_log_deriv hm β hh hV
  let inc : edgeFormSpace L n k j → complexEdgeForms L n k j :=
    fun B => ⟨B.1, mem_complexEdgeForms_of_mem B.2⟩
  have hval : ∀ B : edgeFormSpace L n k j,
      logDirectionalDeriv ℂ (fun X => h (PeriodicLattice.expTwist X V))
      (h V) (B : Edge L n k j → ComplexMatrix2) = Complex.I⁻¹ • Λc (inc B) := by
    intro B
    unfold logDirectionalDeriv
    congr 1
    exact (hΛ (inc B)).deriv
  have hmem : ∀ B : edgeFormSpace L n k j,
      Complex.I⁻¹ • Λc (inc B) ∈ ComplexMatrix2.hermitianTraceless := by
    intro B
    obtain ⟨W, hWd, hW⟩ := hcurve B.1 B.2
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hW
    have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) := by
      refine ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hε⟩
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    have hlog := (hA.1 _ hI).1 W (fun t ht => (hball t ht).1) hWd
    have hW0 : W 0 = h V := by
      have := (hball 0 (Metric.mem_ball_self hε)).2
      rw [Complex.ofReal_zero, expTwist_zero_smul hVc] at this
      exact this
    have hder := hasDerivAt_ofReal_of_complex (hΛ (inc B))
    have hder' : HasDerivAt (fun t : ℝ => ComplexMatrix2.logSeries (W t * (W 0)⁻¹))
        (Λc (inc B)) 0 := by
      refine hder.congr_of_eventuallyEq ?_
      filter_upwards [hW] with t ht
      rw [ht.2, hW0]
    rw [← hder'.deriv, hlog.2.2.1]
    exact hlog.2.2.2
  let f : edgeFormSpace L n k j →ₗ[ℝ] ComplexMatrix2 :=
    { toFun := fun B => Complex.I⁻¹ • Λc (inc B)
      map_add' := fun B B' => by
        have : inc (B + B') = inc B + inc B' := rfl
        rw [this, map_add, smul_add]
      map_smul' := fun c B => by
        have : inc (c • B) = (c : ℂ) • inc B := by
          apply Subtype.ext
          funext b
          exact (algebraMap_smul ℂ c ((B : Edge L n k j → ComplexMatrix2) b))
        rw [this, map_smul, smul_comm]
        simp only [RingHom.id_apply]
        exact algebraMap_smul ℂ c _ }
  refine ⟨f.codRestrict ComplexMatrix2.hermitianTraceless hmem, fun B => ?_⟩
  rw [hval B]
  rfl
end Level
section Restriction
variable {ι ι' : Type}
theorem eq_zero_of_halfTrace_mul_eq_zero {D : ComplexMatrix2} (hD : D ∈ ComplexMatrix2.traceless)
    (h : ∀ Y ∈ ComplexMatrix2.traceless, ComplexMatrix2.halfTrace (D * Y) = 0) : D = 0 := by
  have h0 : Matrix.trace D = 0 := hD
  rw [Matrix.trace_fin_two] at h0
  have e : ∀ Y : ComplexMatrix2, Matrix.trace Y = 0 → Matrix.trace (D * Y) = 0 := by
    intro Y hY
    have := h Y hY
    simpa [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace] using this
  have e1 := e !![0, 1; 0, 0] (by simp [Matrix.trace_fin_two])
  have e2 := e !![0, 0; 1, 0] (by simp [Matrix.trace_fin_two])
  have e3 := e !![1, 0; 0, -1] (by simp [Matrix.trace_fin_two])
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have e4 : D 0 0 = 0 := by linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * e3
  have e5 : D 1 1 = 0 := by linear_combination (1 / 2 : ℂ) * h0 - (1 / 2 : ℂ) * e3
  ext a b
  fin_cases a <;> fin_cases b <;> simp [e1, e2, e4, e5]
theorem traceFinsumPairing_extend [Finite ι] [Finite ι'] {e : ι' → ι}
    (he : Function.Injective e) (g : ι' → ComplexMatrix2) (f : ι → ComplexMatrix2) :
    traceFinsumPairing (Function.extend e g 0) f = traceFinsumPairing g (fun y => f (e y)) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite ι'
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective e he _ _ (fun x hx => ?_) (fun y => ?_)
  · rw [Function.extend_apply' _ _ _ (fun h => hx h)]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  · rw [he.extend_apply]
theorem extend_zero_add (e : ι' → ι) (g g' : ι' → ComplexMatrix2) :
    Function.extend e (g + g') 0 = Function.extend e g 0 + Function.extend e g' 0 := by
  classical
  funext x
  by_cases h : ∃ y, e y = x
  · simp only [Pi.add_apply, Function.extend_def, dif_pos h]
  · simp [Function.extend_apply' _ _ _ h]
theorem extend_zero_smul {R : Type} [SMulZeroClass R ComplexMatrix2] (e : ι' → ι) (c : R)
    (g : ι' → ComplexMatrix2) :
    Function.extend e (c • g) 0 = c • Function.extend e g 0 := by
  classical
  funext x
  by_cases h : ∃ y, e y = x
  · simp only [Pi.smul_apply, Function.extend_def, dif_pos h]
  · simp [Function.extend_apply' _ _ _ h]
theorem single_mem_tracelessFunctions [DecidableEq ι] {x : ι} {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) :
    (Pi.single x Y : ι → ComplexMatrix2) ∈ tracelessFunctions ι := by
  refine Submodule.mem_pi.2 fun z _ => ?_
  by_cases hz : z = x
  · subst hz
    simpa using hY
  · simp [Pi.single_eq_of_ne hz]
theorem traceFinsumPairing_single [DecidableEq ι] (A : ι → ComplexMatrix2) (x : ι)
    (Y : ComplexMatrix2) :
    traceFinsumPairing A (Pi.single x Y) = ComplexMatrix2.halfTrace (A x * Y) := by
  unfold traceFinsumPairing
  rw [finsum_eq_single _ x]
  · simp
  · intro z hz
    simp [Pi.single_eq_of_ne hz, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
def complexPullback (e : ι' → ι) :
    (pairedFunctions ι).complexSubmodule →ₗ[ℂ] (pairedFunctions ι').complexSubmodule where
  toFun f := ⟨fun y => f.1 (e y), Submodule.mem_pi.2 fun y _ =>
    Submodule.mem_pi.1 f.2 (e y) (mem_univ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem extend_zero_mem {S : Set ComplexMatrix2} (h0 : (0 : ComplexMatrix2) ∈ S) (e : ι' → ι)
    {g : ι' → ComplexMatrix2} (hg : ∀ y, g y ∈ S) (x : ι) : Function.extend e g 0 x ∈ S := by
  classical
  by_cases h : ∃ y, e y = x
  · rw [Function.extend_def, dif_pos h]
    exact hg _
  · rw [Function.extend_apply' _ _ _ h]
    exact h0
def complexExtendByZero (e : ι' → ι) :
    (pairedFunctions ι').complexSubmodule →ₗ[ℂ] (pairedFunctions ι).complexSubmodule where
  toFun g := ⟨Function.extend e g.1 0, Submodule.mem_pi.2 fun x _ =>
    extend_zero_mem ComplexMatrix2.traceless.zero_mem e
      (fun y => Submodule.mem_pi.1 g.2 y (mem_univ _)) x⟩
  map_add' g g' := by
    apply Subtype.ext
    exact extend_zero_add e g.1 g'.1
  map_smul' c g := by
    apply Subtype.ext
    exact extend_zero_smul e c g.1
def realExtendByZero (e : ι' → ι) :
    (pairedFunctions ι').realSubmodule →ₗ[ℝ] (pairedFunctions ι).realSubmodule where
  toFun g := ⟨Function.extend e g.1 0, Submodule.mem_pi.2 fun x _ =>
    extend_zero_mem ComplexMatrix2.hermitianTraceless.zero_mem e
      (fun y => Submodule.mem_pi.1 g.2 y (mem_univ _)) x⟩
  map_add' g g' := by
    apply Subtype.ext
    exact extend_zero_add e g.1 g'.1
  map_smul' c g := by
    apply Subtype.ext
    exact extend_zero_smul e c g.1
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
def hermPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def antiHermPart (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-(Complex.I / 2)) • (X - X.conjTranspose)
theorem fullTrace_conjTranspose_eq_zero {X : ComplexMatrix2}
    (h : ComplexMatrix2.fullTrace X = 0) : ComplexMatrix2.fullTrace X.conjTranspose = 0 := by
  have := Matrix.trace_conjTranspose X
  simp only [ComplexMatrix2.fullTrace] at h ⊢
  rw [this, h, star_zero]
theorem hermPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    hermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have hX : ComplexMatrix2.fullTrace X = 0 := h
  have hX' := fullTrace_conjTranspose_eq_zero hX
  refine ⟨?_, ?_⟩
  · simp only [hermPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]
    congr 1
    simp [Complex.ext_iff]
  · simp only [ComplexMatrix2.fullTrace] at hX hX' ⊢
    simp [hermPart, Matrix.trace_smul, Matrix.trace_add, hX, hX']
theorem antiHermPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    antiHermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have hX : ComplexMatrix2.fullTrace X = 0 := h
  have hX' := fullTrace_conjTranspose_eq_zero hX
  refine ⟨?_, ?_⟩
  · simp only [antiHermPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.ext_iff]
      norm_num
    rw [this, ← neg_sub X, smul_neg, neg_smul]
  · simp only [ComplexMatrix2.fullTrace] at hX hX' ⊢
    simp [antiHermPart, Matrix.trace_smul, Matrix.trace_sub, hX, hX']
theorem hermPart_add_I_smul_antiHermPart (X : ComplexMatrix2) :
    X = hermPart X + Complex.I • antiHermPart X := by
  simp only [hermPart, antiHermPart, smul_smul]
  have h : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  rw [h, ← smul_add]
  have : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num
theorem realTransposeMap_eq_extend [Finite ι] [Finite ι'] {e : ι' → ι}
    (he : Function.Injective e)
    (T₀ : (pairedFunctions ι).realSubmodule →ₗ[ℝ] (pairedFunctions ι').realSubmodule)
    (hT : ∀ (l : (pairedFunctions ι).realSubmodule) (y : ι'), (T₀ l).1 y = l.1 (e y))
    (g : (pairedFunctions ι').realSubmodule) :
    (PairedFunctionSpace.realTransposeMap T₀ g).1 = Function.extend e g.1 0 := by
  classical
  let Tc := complexPullback (ι := ι) (ι' := ι') e
  let Ec := complexExtendByZero (ι := ι) (ι' := ι') e
  have hCont : PairedFunctionSpace.IsComplexification T₀ Tc := by
    intro f f' h hh
    funext y
    show h.1 (e y) = _
    rw [hh]
    exact (congrArg₂ (fun a b : ComplexMatrix2 => a + Complex.I • b) (hT f y) (hT f' y)).symm
  have hsplit : ∀ h : (pairedFunctions ι).complexSubmodule,
      ∃ f f' : (pairedFunctions ι).realSubmodule,
      (h.1 : ι → ComplexMatrix2) = f.1 + Complex.I • (f'.1 : ι → ComplexMatrix2) := by
    intro h
    refine ⟨⟨fun x => hermPart (h.1 x), Submodule.mem_pi.2 fun x _ =>
        hermPart_mem (Submodule.mem_pi.1 h.2 x (mem_univ _))⟩,
      ⟨fun x => antiHermPart (h.1 x), Submodule.mem_pi.2 fun x _ =>
        antiHermPart_mem (Submodule.mem_pi.1 h.2 x (mem_univ _))⟩, ?_⟩
    funext x
    exact hermPart_add_I_smul_antiHermPart (h.1 x)
  have hc : PairedFunctionSpace.complexification T₀ = Tc := by
    have hs : PairedFunctionSpace.IsComplexification T₀ (PairedFunctionSpace.complexification T₀) :=
      Classical.epsilon_spec (p := PairedFunctionSpace.IsComplexification T₀) ⟨Tc, hCont⟩
    refine LinearMap.ext fun h => Subtype.ext ?_
    obtain ⟨f, f', hp⟩ := hsplit h
    rw [hs f f' h hp, hCont f f' h hp]
  have hTr : PairedFunctionSpace.IsTransposeMap Tc Ec := by
    intro g f _
    exact traceFinsumPairing_extend he g.1 f.1
  have hte : PairedFunctionSpace.transposeMap Tc = Ec := by
    have hs : PairedFunctionSpace.IsTransposeMap Tc (PairedFunctionSpace.transposeMap Tc) :=
      Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap Tc) ⟨Ec, hTr⟩
    refine LinearMap.ext fun g => Subtype.ext ?_
    funext x
    have hsub : (PairedFunctionSpace.transposeMap Tc g).1 x - (Ec g).1 x = 0 := by
      refine eq_zero_of_halfTrace_mul_eq_zero (ComplexMatrix2.traceless.sub_mem
        (Submodule.mem_pi.1 (PairedFunctionSpace.transposeMap Tc g).2 x (mem_univ _))
        (Submodule.mem_pi.1 (Ec g).2 x (mem_univ _))) fun Y hY => ?_
      let f : (pairedFunctions ι).complexSubmodule :=
        ⟨(Pi.single (x : ι) Y : ι → ComplexMatrix2), single_mem_tracelessFunctions hY⟩
      have hfs : (pairedFunctions ι).IsFinitelySupported f :=
        Set.toFinite (Function.support (Pi.single (x : ι) Y : ι → ComplexMatrix2))
      let A₁ : ι → ComplexMatrix2 := (PairedFunctionSpace.transposeMap Tc g).1
      let A₂ : ι → ComplexMatrix2 := (Ec g).1
      have e3 : traceFinsumPairing A₁ (Pi.single (x : ι) Y) =
          traceFinsumPairing A₂ (Pi.single (x : ι) Y) :=
        (hs g f hfs).trans (hTr g f hfs).symm
      have e4 : ComplexMatrix2.halfTrace (A₁ x * Y) = ComplexMatrix2.halfTrace (A₂ x * Y) :=
        (traceFinsumPairing_single (ι := ι) A₁ x Y).symm.trans
          (e3.trans (traceFinsumPairing_single (ι := ι) A₂ x Y))
      show ComplexMatrix2.halfTrace ((A₁ x - A₂ x) * Y) = 0
      rw [sub_mul]
      simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_sub] at e4 ⊢
      linear_combination e4
    exact sub_eq_zero.1 hsub
  have hRT : PairedFunctionSpace.IsRealTransposeMap T₀ (realExtendByZero e) := by
    intro g h hh
    rw [hc, hte]
    show Function.extend e g.1 0 = Function.extend e h.1 0
    rw [hh]
  have hs : PairedFunctionSpace.IsRealTransposeMap T₀ (PairedFunctionSpace.realTransposeMap T₀) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsRealTransposeMap T₀) ⟨_, hRT⟩
  let gc : (pairedFunctions ι').complexSubmodule := ⟨g.1, Submodule.mem_pi.2 fun y _ =>
    mem_traceless_of_mem_hermitianTraceless (Submodule.mem_pi.1 g.2 y (mem_univ _))⟩
  rw [hs g gc rfl, ← hRT g gc rfl]
  rfl
end Restriction
structure Inputs : Prop where
  cubes : Tower.BlockStructure
  prolongs : ProlongCompositesAndVertexLayers.Statement
  levelwise : LevelwiseMeans.LevelwiseMeansHold
  stable : MeanStableFields.MeanStableFieldsHold
  iterated : IteratedMeans.IteratedMeansHold
  contours : PolydiscContours.ContourHolomorphyHolds
  leftChart : LeftChartFields.Claim
  nearTrivial : Tower.SmoothingNearTrivialField
  lattices : QuotientLattices.TorusAndSpaceLatticeProperties
  powerSeries : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties
  pauli : OneLoop.PauliMatrixRelations
section Side
variable {L n k : ℕ}
theorem finite_vertex (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {j : ℕ} (hj : j ≤ k) : Finite (Vertex L n k j) :=
  (G.lattices L hL n j k hn hj).2.1.2.2.2.2.2.2.2.2.2.2.1
theorem finite_edge (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {j : ℕ} (hj : j ≤ k) : Finite (Edge L n k j) :=
  (G.lattices L hL n j k hn hj).2.1.2.2.2.2.2.2.2.2.2.2.2.1
theorem not_opposite_isPositivelyOriented (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (b : Edge L n k j) (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hN := (G.lattices L hL n j k hn hj).2.2.2.2.2.1
  have hs : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k j)
      (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
    have h := congrArg Subtype.val hμ
    simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps] using h
  have hs' : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k j)
      (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
    have h := congrArg Subtype.val hν
    simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps,
      PeriodicLattice.Bond.opposite] using h
  have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
  rcases hX with ⟨-, h⟩ | ⟨-, h⟩
  · exact h ⟨ν, hs'⟩
  · exact h ⟨μ, hs⟩
def OppositeFlipsOrientation (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented
theorem oppositeFlipsOrientation (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : OppositeFlipsOrientation L n k j :=
  fun b => ⟨fun h h' => not_opposite_isPositivelyOriented G hL hn hj b h' h,
    fun h => (isPositivelyOriented_or_opposite b).resolve_left h⟩
variable {j : ℕ}
theorem extendOddly_of_pos {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos hb
theorem extendOddly_of_not_pos {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := if_neg hb
theorem extendOddly_opposite (hr : OppositeFlipsOrientation L n k j)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_not_pos (fun h => (hr b).mp h hb), extendOddly_of_pos hb]
    rfl
  · rw [extendOddly_of_pos ((hr b).mpr hb), extendOddly_of_not_pos hb, neg_neg]
theorem extendOddly_congr {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ c : Edge L n k j, c.IsPositivelyOriented → f c = g c) :
    extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
theorem exists_linear_extendOddly {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hr : OppositeFlipsOrientation L n k j) (F : Edge L n k j → E → ComplexMatrix2)
    (hF : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      ∃ Λ : E →ₗ[ℝ] ComplexMatrix2.hermitianTraceless, ∀ e, (Λ e : ComplexMatrix2) = F c e) :
    ∃ T : E →ₗ[ℝ] edgeFormSpace L n k j, ∀ e, (T e : Edge L n k j → ComplexMatrix2) =
      extendOddly fun c => F c e := by
  classical
  choose! Λ hΛ using hF
  have hmem : ∀ e, extendOddly (fun c => F c e) ∈ edgeFormSpace L n k j := fun e =>
    ⟨fun b hb => by
      rw [extendOddly_of_pos hb, ← hΛ b hb e]
      exact (Λ b e).2, extendOddly_opposite hr _⟩
  refine ⟨{ toFun := fun e => ⟨extendOddly fun c => F c e, hmem e⟩
            map_add' := fun e e' => ?_
            map_smul' := fun a e => ?_ }, fun e => rfl⟩
  · apply Subtype.ext
    funext b
    show extendOddly (fun c => F c (e + e')) b =
      extendOddly (fun c => F c e) b + extendOddly (fun c => F c e') b
    by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly_of_pos hb, ← hΛ b hb, map_add]
      rfl
    · have hb' := (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [extendOddly_of_not_pos hb, ← hΛ _ hb', map_add]
      rw [Submodule.coe_add, neg_add]
  · apply Subtype.ext
    funext b
    show extendOddly (fun c => F c (a • e)) b = a • extendOddly (fun c => F c e) b
    by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly_of_pos hb, ← hΛ b hb, map_smul]
      rfl
    · have hb' := (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [extendOddly_of_not_pos hb, ← hΛ _ hb', map_smul]
      rw [Submodule.coe_smul, smul_neg]
theorem inverseFourthPowerWeight_smul (X : ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • X = ((L : ℝ) ^ (-4 : ℤ)) • X :=
  algebraMap_smul ℂ ((L : ℝ) ^ (-4 : ℤ)) X
theorem exists_linear_block_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {i : ℕ}
    (hfin : ∀ y : Vertex L n k (i + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y).Finite)
    (F : Vertex L n k (i + 1) → Vertex L n k i → E → ComplexMatrix2)
    (hF : ∀ y, ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      ∃ Λ : E →ₗ[ℝ] ComplexMatrix2.hermitianTraceless, ∀ e, (Λ e : ComplexMatrix2) = F y x e) :
    ∃ T : E →ₗ[ℝ] vertexFunctionSpace L n k (i + 1), ∀ e,
      (T e : Vertex L n k (i + 1) → ComplexMatrix2) =
      fun y => PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y, F y x e := by
  classical
  choose! Λ hΛ using hF
  let S : ∀ y : Vertex L n k (i + 1), E →ₗ[ℝ] ComplexMatrix2.hermitianTraceless := fun y =>
    ((L : ℝ) ^ (-4 : ℤ)) • ∑ x ∈ (hfin y).toFinset, Λ y x
  have hS : ∀ e y, (S y e : ComplexMatrix2) = PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y, F y x e := by
    intro e y
    rw [inverseFourthPowerWeight_smul, finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    simp only [S, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
      Submodule.coe_sum]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    exact hΛ y x ((hfin y).mem_toFinset.1 hx) e
  refine ⟨{ toFun := fun e => ⟨fun y => (S y e : ComplexMatrix2),
              Submodule.mem_pi.2 fun y _ => (S y e).2⟩
            map_add' := fun e e' => ?_
            map_smul' := fun a e => ?_ }, fun e => funext (hS e)⟩
  · apply Subtype.ext
    funext y
    simp
  · apply Subtype.ext
    funext y
    simp
theorem conjugateBy_add (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X + Y) =
      ComplexMatrix2.conjugateBy V X + ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_real_smul (V : ComplexMatrix2) (c : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by
  have r : ∀ Y : ComplexMatrix2, c • Y = (c : ℂ) • Y := fun Y => (algebraMap_smul ℂ c Y).symm
  rw [r, r, conjugateBy_smul]
theorem conjugateBy_mem_hermitianTraceless (G : Inputs) {V X : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.hermitianTraceless := by
  have h := G.pauli.2.2.2.2.2.2.2.2.2.2 V hV
  have m := Set.mem_image_of_mem (ComplexMatrix2.conjugateBy V)
    (show X ∈ (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) from hX)
  rw [h] at m
  exact m
def conjugateAtPoint (G : Inputs) {ι : Type} {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (x : ι) :
    hermitianTracelessFunctions ι →ₗ[ℝ] ComplexMatrix2.hermitianTraceless where
  toFun l := ⟨ComplexMatrix2.conjugateBy g (l.1 x),
    conjugateBy_mem_hermitianTraceless G hg (Submodule.mem_pi.1 l.2 x (mem_univ x))⟩
  map_add' l l' := by
    apply Subtype.ext
    exact conjugateBy_add g _ _
  map_smul' c l := by
    apply Subtype.ext
    exact conjugateBy_real_smul g c _
def evalAtPoint {ι : Type} (x : ι) :
    hermitianTracelessFunctions ι →ₗ[ℝ] ComplexMatrix2.hermitianTraceless where
  toFun l := ⟨l.1 x, Submodule.mem_pi.1 l.2 x (mem_univ x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem mem_fieldsIn_of_mem_fieldSpace {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
theorem inv_eq_adjugate_of_mem {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹ = X.adjugate := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.MeanData.inv_eq_adjugate_of_mem <;> assumption
theorem ofReal_smul_mem_edgeFormSpace {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (t : ℝ) : (t : ℂ) • B ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.ofReal_smul_mem_edgeFormSpace <;> assumption
theorem tendsto_expTwist_real (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hj : j ≤ k) {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (hB : B ∈ edgeFormSpace L n k j) :
    Tendsto (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) V) (𝓝 0)
      (𝓝[fieldSpace L n k j] V) := by
  classical
  have hconf : ∀ t : ℝ, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ fieldSpace L n k j :=
    fun t => (G.nearTrivial L n k hL hn hk).2 j hj _ (ofReal_smul_mem_edgeFormSpace hB t) V hV
  have hleft := ((G.leftChart.2.2 L k j hL hj).1 n hn).1.1.1
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Tendsto (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) V b) (𝓝 0) (𝓝 (V b)) := by
    intro b hb
    have h := (hleft V hV B hB ⟨b, hb⟩).2.continuousAt.tendsto
    have e0 : leftExpMul (((0 : ℝ) : ℂ) • LatticeData.onPositive (Λ := finiteData L n k j) B ⟨b, hb⟩)
        (LatticeData.onPositive (Λ := finiteData L n k j) V ⟨b, hb⟩) = V b := by
      simp [leftExpMul, NormedSpace.exp_zero, LatticeData.onPositive, finiteData]
    rw [e0] at h
    refine h.congr fun t => ?_
    simp [PeriodicLattice.expTwist, hb, leftExpMul, LatticeData.onPositive, finiteData]
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, Eventually.of_forall hconf⟩
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have h2 : Tendsto
        (fun t : ℝ => (PeriodicLattice.expTwist ((t : ℂ) • B) V b.opposite).adjugate)
        (𝓝 0) (𝓝 (V b.opposite).adjugate) :=
      (Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp (hpos _ hr)
    have hVc := mem_fieldsIn_of_mem_fieldSpace hV
    have e0 : (V b.opposite).adjugate = V b := by
      rw [← inv_eq_adjugate_of_mem (hVc.1 _ (mem_univ _)), hVc.2 b (mem_univ b)]
      exact inv_inv_of_mem_complexGaugeGroup (hVc.1 b (mem_univ b))
    rw [e0] at h2
    refine h2.congr fun t => ?_
    have hc := mem_fieldsIn_of_mem_fieldSpace (hconf t)
    rw [← inv_eq_adjugate_of_mem (hc.1 _ (mem_univ _)), hc.2 b (mem_univ b)]
    exact inv_inv_of_mem_complexGaugeGroup (hc.1 b (mem_univ b))
structure StepProperties (i : ℕ) (V : Edge L n k i → ComplexMatrix2) : Prop where
  near_one : V ∈ MeanStableFields.fieldsNearOne L n k i
  contour_mem_compact : ∀ y : Vertex L n k (i + 1),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
    PeriodicLattice.complexMeanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup
  contour_real_curve : ∀ y : Vertex L n k (i + 1),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
    ∀ B ∈ edgeFormSpace L n k i,
      ∃ W : ℝ → ComplexMatrix2, DifferentiableAt ℝ W 0 ∧
        ∀ᶠ t : ℝ in 𝓝 0, W t ∈ PeriodicLattice.compactGaugeGroup ∧
        W t = PeriodicLattice.complexMeanContourHolonomy
          (PeriodicLattice.expTwist ((t : ℂ) • B) V) y x
  smoothing_mem_compact : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.compactGaugeGroup
  smoothing_real_curve : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ B ∈ edgeFormSpace L n k i,
    ∃ W : ℝ → ComplexMatrix2, DifferentiableAt ℝ W 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, W t ∈ PeriodicLattice.compactGaugeGroup ∧
      W t = PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist ((t : ℂ) • B) V) c
def RealComplexAgree (i : ℕ) (c : Edge L n k (i + 1)) (y : Vertex L n k (i + 1))
    (x : Vertex L n k i) (V : Edge L n k i → ComplexMatrix2) : Prop :=
  PeriodicLattice.complexBlockAverage V c = smoothingStep L n k i V c ∧
  PeriodicLattice.complexMeanContourHolonomy V y x = PeriodicLattice.meanContourHolonomy V y x ∧
  ∀ B ∈ edgeFormSpace L n k i,
    DifferentiableAt ℝ (fun t : ℝ =>
      smoothingStep L n k i (PeriodicLattice.expTwist ((t : ℂ) • B) V) c) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ =>
      PeriodicLattice.meanContourHolonomy (PeriodicLattice.expTwist ((t : ℂ) • B) V) y x) 0
theorem forwardFrom_zero_isPositivelyOriented {i : ℕ} (y : Vertex L n k i) :
    (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
  ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
theorem eventually_stepProperties (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {i : ℕ} (hi : i < k) :
    EventuallyNearIdentity (fieldSpace L n k i) (StepProperties i) := by
  classical
  have hH := (G.levelwise L hL k hk).1 n hn
  have hO := (G.prolongs.1 L n k hL hn hk).2.1
  have := finite_edge (k := k) G hL hn (j := i + 1) hi
  have := finite_vertex (k := k) G hL hn (j := i + 1) hi
  have := finite_vertex (k := k) G hL hn (j := i) hi.le
  have hall : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)),
      ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (i + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
          RealComplexAgree i c y x V := by
    refine eventually_all.2 fun c => eventually_imp_distrib_left.2 fun hc =>
      eventually_all.2 fun y => eventually_imp_distrib_left.2 fun hy =>
      eventually_all.2 fun x => eventually_imp_distrib_left.2 fun hx => ?_
    refine Eventually.mono (hH.agree_near_identity i hi c hc y hy x hx) fun V hV => ?_
    refine ⟨hV.2.1, hV.2.2.2.1, fun B hB => ?_⟩
    obtain ⟨-, ⟨D, h, -⟩, ⟨D', h', -⟩⟩ := hV.2.2.2.2 B hB
    exact ⟨h.differentiableAt, h'.differentiableAt⟩
  have hgood : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)),
      (∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (i + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
          RealComplexAgree i c y x V) ∧
      (∀ y : Vertex L n k (i + 1),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup) ∧
      ∀ c : Edge L n k (i + 1), smoothingStep L n k i V c ∈ PeriodicLattice.compactGaugeGroup := by
    filter_upwards [hall, hO.contourMean_mem i hi, hO.smoothingStep_mem i hi] with V h₁ h₂ h₃
    exact ⟨h₁, fun y x hx => (h₂ y x hx).2, h₃⟩
  have hnear := eventually_eventually_nhdsWithin.2 hgood
  have hrad := ((G.iterated L hL k hk).1 n hn).eventually_near i hi
  filter_upwards [hnear, hgood, hrad, self_mem_nhdsWithin] with V hV hV₀ hR hVc
  have hcurve : ∀ B ∈ edgeFormSpace L n k i, ∀ᶠ t : ℝ in 𝓝 0,
      (∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (i + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
          RealComplexAgree i c y x (PeriodicLattice.expTwist ((t : ℂ) • B) V)) ∧
      (∀ y : Vertex L n k (i + 1),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy (PeriodicLattice.expTwist ((t : ℂ) • B) V) y x ∈
          PeriodicLattice.compactGaugeGroup) ∧
      ∀ c : Edge L n k (i + 1),
        smoothingStep L n k i (PeriodicLattice.expTwist ((t : ℂ) • B) V) c ∈
          PeriodicLattice.compactGaugeGroup :=
    fun B hB => (tendsto_expTwist_real G hL hn hk hi.le hVc hB).eventually hV
  have hcentre : ∀ (y : Vertex L n k (i + 1)),
      y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
        (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L n k (i + 1))) :=
    fun y => Or.inl rfl
  have hxc : ∀ y : Vertex L n k (i + 1), ∃ x : Vertex L n k i,
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
    intro y
    have hZ := (G.cubes L k (i + 1) hL hk (by omega) hi).1 n hn
    have hy : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
      have h := hZ.2.1.1 y
      have m : (y : PeriodicLattice.FourTorus L n) ∈ ({(y : PeriodicLattice.FourTorus L n)} :
        Set (PeriodicLattice.FourTorus L n)) := rfl
      rw [← h] at m
      exact m.1
    exact ⟨⟨y, (hZ.1 y).2.2.2 hy⟩, hy⟩
  refine ⟨⟨mem_fieldsIn_of_mem_fieldSpace hVc, hR⟩, fun y x hx => ?_, fun y x hx B hB => ?_,
    fun c hc => ?_, fun c hc B hB => ?_⟩
  · rw [(hV₀.1 _ (forwardFrom_zero_isPositivelyOriented y) y (hcentre y) x hx).2.1]
    exact hV₀.2.1 y x hx
  · refine ⟨fun t => PeriodicLattice.meanContourHolonomy
        (PeriodicLattice.expTwist ((t : ℂ) • B) V) y x,
      ((hV₀.1 _ (forwardFrom_zero_isPositivelyOriented y) y (hcentre y) x hx).2.2 B hB).2, ?_⟩
    filter_upwards [hcurve B hB] with t ht
    exact ⟨ht.2.1 y x hx,
      (ht.1 _ (forwardFrom_zero_isPositivelyOriented y) y (hcentre y) x hx).2.1.symm⟩
  · obtain ⟨x, hx⟩ := hxc c.source
    rw [(hV₀.1 c hc c.source (mem_insert _ _) x hx).1]
    exact hV₀.2.2 c
  · obtain ⟨x, hx⟩ := hxc c.source
    refine ⟨fun t => smoothingStep L n k i (PeriodicLattice.expTwist ((t : ℂ) • B) V) c,
      ((hV₀.1 c hc c.source (mem_insert _ _) x hx).2.2 B hB).1, ?_⟩
    filter_upwards [hcurve B hB] with t ht
    exact ⟨ht.2.2 c, (ht.1 c hc c.source (mem_insert _ _) x hx).1.symm⟩
end Side
section Maps
variable {L n k : ℕ}
theorem nonempty_traceless_basis (G : Inputs) :
    Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := by
  obtain ⟨e, -⟩ := G.pauli.2.2.2.1
  exact ⟨e⟩
structure StepLinearMaps (i : ℕ) (V : Edge L n k i → ComplexMatrix2) : Prop where
  drift_linear : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] vertexFunctionSpace L n k (i + 1),
    ∀ B : edgeFormSpace L n k i,
    (T B : Vertex L n k (i + 1) → ComplexMatrix2) =
      contourLogDrift V (B : Edge L n k i → ComplexMatrix2)
  average_linear : ∃ T : vertexFunctionSpace L n k i →ₗ[ℝ] vertexFunctionSpace L n k (i + 1),
    ∀ l : vertexFunctionSpace L n k i,
    (T l : Vertex L n k (i + 1) → ComplexMatrix2) =
      adjointCubeAverage V (l : Vertex L n k i → ComplexMatrix2)
  deriv_linear : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1),
    ∀ B : edgeFormSpace L n k i,
    (T B : Edge L n k (i + 1) → ComplexMatrix2) =
      complexSmoothingDeriv V (B : Edge L n k i → ComplexMatrix2)
  covariant_linear : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1),
    ∀ B : edgeFormSpace L n k i,
    (T B : Edge L n k (i + 1) → ComplexMatrix2) =
      covariantSmoothingDeriv V (B : Edge L n k i → ComplexMatrix2)
theorem exists_linear_covDiff (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) {V' : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b : Edge L n k j, b.IsPositivelyOriented → V' b ∈ PeriodicLattice.compactGaugeGroup) :
    ∃ T : vertexFunctionSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j,
      ∀ l : vertexFunctionSpace L n k j,
      (T l : Edge L n k j → ComplexMatrix2) = covDiff V' (l : Vertex L n k j → ComplexMatrix2) :=
  exists_linear_extendOddly (E := vertexFunctionSpace L n k j) (oppositeFlipsOrientation G hL hn hj)
    (fun b l => ComplexMatrix2.conjugateBy (V' b) ((l : Vertex L n k j → ComplexMatrix2) b.target) -
      (l : Vertex L n k j → ComplexMatrix2) b.source)
    (fun b hb => ⟨conjugateAtPoint G (hV b hb) b.target - evalAtPoint b.source, fun _ => rfl⟩)
theorem stepLinearMaps_of_properties (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {i : ℕ} (hi : i < k) {V : Edge L n k i → ComplexMatrix2}
    (h : StepProperties i V) : StepLinearMaps i V := by
  classical
  obtain ⟨β⟩ := nonempty_traceless_basis G
  have := finite_vertex (k := k) G hL hn (j := i) hi.le
  have hW := (G.contours L hL k i hi).1 n hn
  have hS := (G.stable L hL k hk).1 n hn
  have hdrift : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] vertexFunctionSpace L n k (i + 1),
      ∀ B : edgeFormSpace L n k i,
      (T B : Vertex L n k (i + 1) → ComplexMatrix2) =
        contourLogDrift V (B : Edge L n k i → ComplexMatrix2) :=
    exists_linear_block_sum (E := edgeFormSpace L n k i) (fun y => Set.toFinite _)
      (fun y x B => logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) (B : Edge L n k i → ComplexMatrix2))
      (fun y x hx => exists_real_linear_log_deriv G.leftChart G.powerSeries β
        (((hW _ (forwardFrom_zero_isPositivelyOriented y)).holomorphicOn_fieldsNearOne y
          (mem_insert _ _) x hx).isHolomorphicOnFields β)
        h.near_one (h.contour_real_curve y x hx))
  have hdiff : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1),
      ∀ B : edgeFormSpace L n k i,
      (T B : Edge L n k (i + 1) → ComplexMatrix2) =
        complexSmoothingDeriv V (B : Edge L n k i → ComplexMatrix2) :=
    exists_linear_extendOddly (E := edgeFormSpace L n k i) (oppositeFlipsOrientation G hL hn hi)
      (fun c B => logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.expTwist X V) c)
        (PeriodicLattice.complexBlockAverageStep i V c) (B : Edge L n k i → ComplexMatrix2))
      (fun c hc => exists_real_linear_log_deriv G.leftChart G.powerSeries β
        (hS.holomorphic_smoothing i hi c hc β) h.near_one (h.smoothing_real_curve c hc))
  refine ⟨hdrift, ?_, hdiff, ?_⟩
  · exact exists_linear_block_sum (E := vertexFunctionSpace L n k i) (fun y => Set.toFinite _)
      (fun y x l => ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x)
        ((l : Vertex L n k i → ComplexMatrix2) x))
      (fun y x hx => ⟨conjugateAtPoint G (h.contour_mem_compact y x hx) x, fun _ => rfl⟩)
  · obtain ⟨Tq, hTq⟩ := hdiff
    obtain ⟨Tn, hTn⟩ := hdrift
    obtain ⟨TD, hTD⟩ := exists_linear_covDiff G hL hn hi
      (V' := PeriodicLattice.complexBlockAverageStep i V) (fun b hb => h.smoothing_mem_compact b hb)
    refine ⟨Tq + TD ∘ₗ Tn, fun B => ?_⟩
    show (Tq B : Edge L n k (i + 1) → ComplexMatrix2) +
      (TD (Tn B) : Edge L n k (i + 1) → ComplexMatrix2) = _
    rw [hTq, hTD, hTn]
    rfl
theorem complexBlockFieldAtLevel_eq_of_meanSequence (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {W : Edge L n k 0 → ComplexMatrix2} {Vf : ∀ i : ℕ, Edge L n k i → ComplexMatrix2}
    (h : LevelwiseMeans.IsMeanSequence k Vf) (h0 : Vf 0 = W) :
    ∀ i, i ≤ k → PeriodicLattice.complexBlockFieldAtLevel i W = Vf i := by
  have hO := (G.iterated L hL k hk).1 n hn
  intro i
  induction i with
  | zero => exact fun _ => h0.symm
  | succ i ih =>
    intro hi
    have hi' : i < k := hi
    have e := ih hi'.le
    have hu := (hO.meanStep_unique i hi' (Vf i) ⟨h.mem_fields i hi'.le, h.norm_sub_one_lt i hi'⟩
      (Vf (i + 1)) (h.mem_fields (i + 1) hi)).1 (fun c hc => h.eq_mean i hi' c hc)
    show PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.complexBlockFieldAtLevel i W) =
      Vf (i + 1)
    rw [e, hu]
    rfl
theorem expTwist_mem_fieldsIn {j : ℕ} (hr : OppositeFlipsOrientation L n k j)
    {A U : Edge L n k j → ComplexMatrix2}
    (hl : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • A b) * U b ∈ PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  classical
  have hinv : ∀ X : ComplexMatrix2, X ∈ PeriodicLattice.complexGaugeGroup →
      X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by
    intro X hX
    have e : X.det = 1 := hX
    show (X⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, e]
    simp
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hl b hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      exact hinv _ (hl _ ((hr b).2 hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hn' : ¬ b.opposite.IsPositivelyOriented := fun h => (hr b).1 h hb
      simp only [PeriodicLattice.expTwist, if_neg hn', if_pos hb]
      rfl
    · have hp := (hr b).2 hb
      simp only [PeriodicLattice.expTwist, if_pos hp, if_neg hb]
      exact (inv_inv_of_mem_complexGaugeGroup (hl _ hp)).symm
structure IterateProperties (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  complex_eq_real : ∀ i ≤ k,
    PeriodicLattice.complexBlockFieldAtLevel i U = smoothingIter L n k i U
  complexIterDeriv_eq : ∀ j ≤ k, ∀ B ∈ edgeFormSpace L n k 0, complexIterDeriv L n k j U B =
    leftDifferential (smoothingIter L n k j) U B
theorem eventually_iterateProperties (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) (IterateProperties (L := L) (n := n) (k := k)) := by
  classical
  have hH := (G.levelwise L hL k hk).1 n hn
  have hS := (G.stable L hL k hk).1 n hn
  have hlev := ((G.leftChart.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).1.1
  have := finite_edge (k := k) G hL hn (j := 0) (Nat.zero_le k)
  have hr := oppositeFlipsOrientation (k := k) G hL hn (j := 0) (Nat.zero_le k)
  filter_upwards [hH.iterates_defined, self_mem_nhdsWithin] with U hU hUc₀
  have hUc := mem_fieldsIn_of_mem_fieldSpace hUc₀
  let Vf : ∀ i : ℕ, Edge L n k i → ComplexMatrix2 := fun i => smoothingIter L n k i U
  have hfam : LevelwiseMeans.IsMeanSequence k Vf := by
    refine ⟨fun i hi => mem_fieldsIn_of_mem_fieldSpace (hU i hi).1, fun i hi b => (hU i hi.le).2.1 b,
      fun i hi c hc => ?_⟩
    have e := (hU (i + 1) hi).2.2.1 c
    have e0 : LevelwiseMeans.levelwiseMean U i = fun c => some (Vf i c) :=
      funext (hU i hi.le).2.2.1
    rw [LevelwiseMeans.levelwiseMean] at e
    simp only [if_pos hc] at e
    rw [e0] at e
    unfold LevelwiseMeans.meanOfDefined at e
    split_ifs at e
    exact (Option.some.inj e).symm
  have hst : U ∈ MeanStableFields.meanStableFields L n k k := ⟨Vf, hfam, rfl⟩
  have heq : ∀ i, i ≤ k → PeriodicLattice.complexBlockFieldAtLevel i U = Vf i :=
    complexBlockFieldAtLevel_eq_of_meanSequence G hL hn hk hfam rfl
  refine ⟨heq, fun j hj B hB => ?_⟩
  have hBc := mem_complexEdgeForms_of_mem hB
  let F₀ : Finset (Edge L n k 0) :=
    (Set.toFinite {b : Edge L n k 0 | b.IsPositivelyOriented}).toFinset
  have hF₀ : ∀ b ∈ F₀, b.IsPositivelyOriented := fun b hb =>
    (Set.toFinite {b : Edge L n k 0 | b.IsPositivelyOriented}).mem_toFinset.1 hb
  have hmoves : ∀ᶠ t : ℂ in 𝓝 0, PeriodicLattice.expTwist (t • B) U ∈
      MeanStableFields.meanStableFields L n k k := by
    obtain ⟨ε, hε, hm⟩ := hS.small_perturbation U hst F₀ hF₀
    have hcl : ∀ᶠ t : ℂ in 𝓝 0, ∀ b ∈ F₀,
        ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist (t • B) U b - U b) < ε := by
      refine (Finset.eventually_all _).2 fun b hb => ?_
      have hb' := hF₀ b hb
      have hc := (hlev.2 U hUc B hBc ⟨b, hb'⟩).2.continuousAt.tendsto
      have e0 : leftExpMul ((0 : ℂ) • LatticeData.onPositive (Λ := finiteData L n k 0) B ⟨b, hb'⟩)
          (LatticeData.onPositive (Λ := finiteData L n k 0) U ⟨b, hb'⟩) = U b := by
        simp [leftExpMul, NormedSpace.exp_zero, LatticeData.onPositive, finiteData]
      rw [e0] at hc
      filter_upwards [Metric.tendsto_nhds.1 hc ε hε] with t ht
      rw [dist_eq_norm] at ht
      have e1 : PeriodicLattice.expTwist (t • B) U b =
          leftExpMul (t • LatticeData.onPositive (Λ := finiteData L n k 0) B ⟨b, hb'⟩)
            (LatticeData.onPositive (Λ := finiteData L n k 0) U ⟨b, hb'⟩) := by
        simp [PeriodicLattice.expTwist, hb', leftExpMul, LatticeData.onPositive, finiteData]
      rw [e1]
      exact ht
    filter_upwards [hcl] with t ht
    refine hm _ (expTwist_mem_fieldsIn hr fun b hb => ?_) (fun b hb hnot => ?_) ht
    · have := (hlev.2 U hUc B hBc ⟨b, hb⟩).1 t
      simpa [leftExpMul, LatticeData.onPositive, finiteData] using this
    · exact absurd ((Set.toFinite {b : Edge L n k 0 | b.IsPositivelyOriented}).mem_toFinset.2 hb)
        hnot
  have key : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexBlockFieldAtLevel j (PeriodicLattice.expTwist X U) c)
        (PeriodicLattice.complexBlockFieldAtLevel j U c) B =
      logDirectionalDeriv ℝ
        (fun X => smoothingIter L n k j (PeriodicLattice.expTwist X U) c)
        (smoothingIter L n k j U c) B := by
    intro c hc
    have hform : LevelwiseMeans.IsDefinedAt U j c := by
      unfold LevelwiseMeans.IsDefinedAt
      rw [(hU j hj).2.2.1 c]
      rfl
    obtain ⟨F, O, f, hw⟩ := hH.exists_representation j hj c U hUc hform
    have hder := ((hU j hj).2.2.2 B hB c hc).2 F O f hw
    have hfU : f (LevelwiseMeans.edgeEntries F U) =
        PeriodicLattice.complexBlockFieldAtLevel j U c := by
      have e1 := hw.eq_some U hUc hw.mem
      rw [(hU j hj).2.2.1 c] at e1
      rw [heq j hj]
      exact (Option.some.inj e1).symm
    have hal := hH.represents_along_curves j hj c U hUc F O f hw B hBc.1
    have hev : (fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexBlockFieldAtLevel j
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) c *
          (PeriodicLattice.complexBlockFieldAtLevel j U c)⁻¹)) =ᶠ[𝓝 0]
        fun t : ℂ => ComplexMatrix2.logSeries (f (LevelwiseMeans.expChartPoint F (t • B) U) *
          (f (LevelwiseMeans.edgeEntries F U))⁻¹) := by
      filter_upwards [hal, hmoves] with t h1 h2
      obtain ⟨Wf, hb⟩ := h2
      have e1 := hS.eq_levelwiseMean k le_rfl _ Wf hb j hj c
      have e2 := complexBlockFieldAtLevel_eq_of_meanSequence G hL hn hk hb.1 hb.2 j hj
      rw [h1.2] at e1
      have e3 : PeriodicLattice.complexBlockFieldAtLevel j
          (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) c =
          f (LevelwiseMeans.expChartPoint F (t • B) U) := by
        show PeriodicLattice.complexBlockFieldAtLevel j (PeriodicLattice.expTwist (t • B) U) c = _
        rw [e2]
        exact (Option.some.inj e1).symm
      rw [e3, hfU]
    have hR : logDirectionalDeriv ℝ
        (fun X => smoothingIter L n k j (PeriodicLattice.expTwist X U) c)
        (smoothingIter L n k j U c) B = leftDifferential (smoothingIter L n k j) U B c := by
      unfold leftDifferential
      exact (extendOddly_of_pos (f := fun c => logDirectionalDeriv ℝ
        (fun X => smoothingIter L n k j (PeriodicLattice.expTwist X U) c)
        (smoothingIter L n k j U c) B) hc).symm
    rw [hR]
    unfold logDirectionalDeriv
    rw [hev.deriv_eq, hder.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  exact extendOddly_congr key
theorem iterated_maps_linear {U : Edge L n k 0 → ComplexMatrix2}
    (hstep : ∀ i < k, StepLinearMaps i (PeriodicLattice.complexBlockFieldAtLevel i U))
    (hQ : ∀ j ≤ k, ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j,
      ∀ B : edgeFormSpace L n k 0,
      (T B : Edge L n k j → ComplexMatrix2) =
        complexIterDeriv L n k j U (B : Edge L n k 0 → ComplexMatrix2)) :
    ∀ j, j ≤ k →
      (∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k j,
        ∀ B : edgeFormSpace L n k 0,
        (T B : Vertex L n k j → ComplexMatrix2) =
          iterContourLogDrift L n k U j (B : Edge L n k 0 → ComplexMatrix2)) ∧
      (∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k j,
        ∀ l : vertexFunctionSpace L n k 0,
        (T l : Vertex L n k j → ComplexMatrix2) =
          iterAdjointCubeAverage L n k U j (l : Vertex L n k 0 → ComplexMatrix2)) ∧
      ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j, ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k j → ComplexMatrix2) =
          iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2) := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨⟨0, fun _ => rfl⟩, ⟨LinearMap.id, fun _ => rfl⟩,
      ⟨LinearMap.id, fun _ => rfl⟩⟩
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    obtain ⟨⟨Tn, hTn⟩, ⟨Ta, hTa⟩, ⟨Tc, hTc⟩⟩ := ih hj'.le
    obtain ⟨Tq, hTq⟩ := hQ j hj'.le
    have hs := hstep j hj'
    obtain ⟨Sn, hSn⟩ := hs.drift_linear
    obtain ⟨Sa, hSa⟩ := hs.average_linear
    obtain ⟨Sc, hSc⟩ := hs.covariant_linear
    refine ⟨⟨Sa ∘ₗ Tn + Sn ∘ₗ Tq, fun B => ?_⟩, ⟨Sa ∘ₗ Ta, fun l => ?_⟩, ⟨Sc ∘ₗ Tc, fun B => ?_⟩⟩
    · show (Sa (Tn B) : Vertex L n k (j + 1) → ComplexMatrix2) +
        (Sn (Tq B) : Vertex L n k (j + 1) → ComplexMatrix2) = _
      rw [hSa, hSn, hTn, hTq]
      rfl
    · show (Sa (Ta l) : Vertex L n k (j + 1) → ComplexMatrix2) = _
      rw [hSa, hTa]
      rfl
    · show (Sc (Tc B) : Edge L n k (j + 1) → ComplexMatrix2) = _
      rw [hSc, hTc]
      rfl
theorem eventually_iterated_maps_linear (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      (∀ j ≤ k, ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j,
        ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k j → ComplexMatrix2) =
          complexIterDeriv L n k j U (B : Edge L n k 0 → ComplexMatrix2)) ∧
      ∀ j, j ≤ k →
        (∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k j,
          ∀ B : edgeFormSpace L n k 0,
          (T B : Vertex L n k j → ComplexMatrix2) =
            iterContourLogDrift L n k U j (B : Edge L n k 0 → ComplexMatrix2)) ∧
        (∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k j,
          ∀ l : vertexFunctionSpace L n k 0,
          (T l : Vertex L n k j → ComplexMatrix2) =
            iterAdjointCubeAverage L n k U j (l : Vertex L n k 0 → ComplexMatrix2)) ∧
        ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j, ∀ B : edgeFormSpace L n k 0,
          (T B : Edge L n k j → ComplexMatrix2) =
            iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2) := by
  have hH := (G.levelwise L hL k hk).1 n hn
  have hO := (G.prolongs.1 L n k hL hn hk).2.1
  have hsteps : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
      ∀ i ∈ Set.Iio k, StepProperties i (smoothingIter L n k i U) :=
    (eventually_all_finite (Set.finite_Iio k)).2 fun i hi =>
      (hH.iterate_tendsto i (le_of_lt hi)).eventually (eventually_stepProperties G hL hn hk hi)
  have hlin : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
      ∀ j ∈ Set.Iic k, ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j,
        ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k j → ComplexMatrix2) =
          leftDifferential (smoothingIter L n k j) U (B : Edge L n k 0 → ComplexMatrix2) :=
    (eventually_all_finite (Set.finite_Iic k)).2 fun j hj => hO.iterDifferential_linear j hj
  filter_upwards [hsteps, hlin, eventually_iterateProperties G hL hn hk] with U h₁ h₂ h₃
  have hQ : ∀ j ≤ k, ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j,
      ∀ B : edgeFormSpace L n k 0,
      (T B : Edge L n k j → ComplexMatrix2) =
        complexIterDeriv L n k j U (B : Edge L n k 0 → ComplexMatrix2) := by
    intro j hj
    obtain ⟨T, hT⟩ := h₂ j hj
    exact ⟨T, fun B => (hT B).trans (h₃.complexIterDeriv_eq j hj B B.2).symm⟩
  refine ⟨hQ, iterated_maps_linear (fun i hi => ?_) hQ⟩
  rw [h₃.complex_eq_real i hi.le]
  exact stepLinearMaps_of_properties G hL hn hk hi (h₁ i hi)
theorem prolongIter_eq_prolong {j t : ℕ} (b : CriticalBranchData L n k) (h : j + 1 ≤ t)
    (W : Edge L n k t → ComplexMatrix2) :
    b.prolongIter (Nat.le_of_succ_le h) W = b.prolong j (b.prolongIter h W) := by
  induction t, h using Nat.le_induction with
  | base => simp [CriticalBranchData.prolongIter, Nat.leRec_self, Nat.leRec_succ]
  | succ t h ih =>
    have e₁ : ∀ (h' : j ≤ t + 1) (V : Edge L n k (t + 1) → ComplexMatrix2),
        b.prolongIter h' V = b.prolongIter (Nat.le_of_succ_le h) (b.prolong t V) := by
      intro h' V
      simp [CriticalBranchData.prolongIter, Nat.leRec_succ, Nat.le_of_succ_le h]
    have e₂ : ∀ (h' : j + 1 ≤ t + 1) (V : Edge L n k (t + 1) → ComplexMatrix2),
        b.prolongIter h' V = b.prolongIter h (b.prolong t V) := by
      intro h' V
      simp [CriticalBranchData.prolongIter, Nat.leRec_succ, h]
    rw [e₁, e₂, ih]
theorem descendingChain_eq_chosenProlongIter (W : Edge L n k k → ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) : descendingChain W hj = chosenProlongIter L n k hj W := by
  refine Nat.decreasingInduction (motive := fun i h =>
    descendingChain W h = (chosenCriticalBranch L n k).prolongIter h W) ?_ ?_ hj
  · intro i hi ih
    rw [descendingChain_of_lt W hi, ih]
    exact (prolongIter_eq_prolong _ hi W).symm
  · rw [descendingChain_top]
    simp [CriticalBranchData.prolongIter, Nat.leRec_self]
theorem exists_restriction_transpose (G : Inputs)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∃ r : (pairedFunctions (Vertex L n k 0)).realSubmodule →ₗ[ℝ]
        (pairedFunctions (Vertex L n k k)).realSubmodule,
      (∀ l : (pairedFunctions (Vertex L n k 0)).realSubmodule,
        (r l).1 = restrictVertexFunction (L := L) (m := n) (k := k) (j := 0) k l.1) ∧
      RestrictionTranspose L n k r := by
  classical
  have := finite_vertex (k := k) G hL hn (j := 0) (Nat.zero_le k)
  have := finite_vertex (k := k) G hL hn (j := k) le_rfl
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hsub := ((hT L hpos hL k).2.2.1 n hn).1 0 k (Nat.zero_le k) le_rfl
  let e : Vertex L n k k → Vertex L n k 0 :=
    fun y => y.toSublattice (PeriodicLattice.levelDepth k 0)
  have he : ∀ y : Vertex L n k k,
      ((e y : Vertex L n k 0) : PeriodicLattice.FourTorus L n) = y := fun y =>
    Classical.epsilon_spec (p := fun x : Vertex L n k 0 =>
      (x : PeriodicLattice.FourTorus L n) = (y : PeriodicLattice.FourTorus L n))
      ⟨⟨y, hsub y.2⟩, rfl⟩
  have hinj : Function.Injective e := by
    intro y y' h
    apply Subtype.ext
    rw [← he y, ← he y', h]
  let r : (pairedFunctions (Vertex L n k 0)).realSubmodule →ₗ[ℝ]
      (pairedFunctions (Vertex L n k k)).realSubmodule :=
    { toFun := fun l => ⟨fun y => l.1 (e y), Submodule.mem_pi.2 fun y _ =>
        Submodule.mem_pi.1 l.2 (e y) (mem_univ _)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : ∀ (l : (pairedFunctions (Vertex L n k 0)).realSubmodule) (y : Vertex L n k k),
      (r l).1 y = l.1 (e y) := fun _ _ => rfl
  have htr := realTransposeMap_eq_extend hinj r hr
  have hext : ∀ g : Vertex L n k k → ComplexMatrix2, Function.extend e g 0 =
      extendByZero (L := L) (m := n) (k := k) g := by
    intro g
    funext x
    unfold extendByZero
    by_cases h : (x : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)
    · rw [dif_pos h]
      have ex : x = e ⟨x, h⟩ := Subtype.ext (he ⟨x, h⟩).symm
      conv_lhs => rw [ex]
      rw [hinj.extend_apply]
    · rw [dif_neg h, Function.extend_apply']
      · rfl
      · rintro ⟨y, rfl⟩
        exact h (by rw [he y]; exact y.2)
  refine ⟨r, fun _ => rfl, ?_⟩
  have hright : ∀ g, r (PairedFunctionSpace.realTransposeMap r g) = g := by
    intro g
    apply Subtype.ext
    funext y
    refine (hr _ y).trans ?_
    have e1 := congrFun (htr g) (e y)
    exact e1.trans (hinj.extend_apply _ _ _)
  refine ⟨fun g f => ?_, fun g => ?_, hright, fun g => ⟨_, hright g⟩⟩
  · exact (congrArg (fun A => traceFinsumPairing A f.1) (htr g)).trans
      (traceFinsumPairing_extend hinj g.1 f.1)
  · exact (htr g).trans (hext g.1)
end Maps
theorem realLinearMaps_holds (hZ : Tower.BlockStructure)
    (hC : ProlongCompositesAndVertexLayers.Statement)
    (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hS : MeanStableFields.MeanStableFieldsHold)
    (hF : IteratedMeans.IteratedMeansHold)
    (hW : PolydiscContours.ContourHolomorphyHolds)
    (hA : LeftChartFields.Claim)
    (hV : Tower.SmoothingNearTrivialField)
    (hT : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hP : OneLoop.PauliMatrixRelations)
    (hD : SublatticesSymmetriesScalingsAndProjections.Statement) : RealLinearMapsStatement := by
  intro L n k hL hn hk
  have G : Inputs := ⟨hZ, hC, hH, hS, hF, hW, hA, hV, hT, hM, hP⟩
  have hO := (G.prolongs.1 L n k hL hn hk).2.1
  have hCt := (G.prolongs.1 L n k hL hn hk).1
  refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
  · have hmaps : EventuallyNearIdentity (fieldSpace L n k i) (StepLinearMaps i) :=
      Eventually.mono (eventually_stepProperties G hL hn hk hi) fun V h =>
        stepLinearMaps_of_properties G hL hn hk hi h
    have hit := eventually_iterated_maps_linear G hL hn hk
    obtain ⟨h₁, -, h₃⟩ := ((G.cubes L k (i + 1) hL hk (by omega) hi).1 n hn).2.1
    have hoff : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i), x ∈ cubeMinusCentre i y →
        (x : PeriodicLattice.FourTorus L n) ∉
          PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) := by
      intro y x hx hl
      have m : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∩
          (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
            Set (PeriodicLattice.FourTorus L n)) := ⟨hx.1, hl⟩
      rw [h₁ y] at m
      exact hx.2 m
    refine
      { blocks_pairwiseDisjoint := ?_
        iUnion_blocks := ?_
        contourLogDeriv_isLinear := hO.contourLogDeriv_linear i hi
        contourLogDrift_isLinear := Eventually.mono hmaps fun V h => h.drift_linear
        adjointCubeAverage_isLinear := Eventually.mono hmaps fun V h => h.average_linear
        complexSmoothingDeriv_isLinear := Eventually.mono hmaps fun V h => h.deriv_linear
        covariantSmoothingDeriv_isLinear := Eventually.mono hmaps fun V h => h.covariant_linear
        complexIterDeriv_isLinear := Eventually.mono hit fun U h => h.1 (i + 1) hi
        iterCovariantDeriv_isLinear :=
          Eventually.mono hit fun U h => (h.2 (i + 1) hi).2.2
        iterContourLogDrift_isLinear := Eventually.mono hit fun U h => (h.2 (i + 1) hi).1
        iterAdjointCubeAverage_isLinear := Eventually.mono hit fun U h => (h.2 (i + 1) hi).2.1 }
    · intro y y' hne
      refine Set.disjoint_left.2 fun x hx hx' => hne ?_
      exact (h₃ x (hoff y x hx)).unique ⟨hx.1, hx.2⟩ ⟨hx'.1, hx'.2⟩
    · ext x
      simp only [mem_iUnion, mem_setOf_eq]
      constructor
      · rintro ⟨y, hy⟩
        exact hoff y x hy
      · intro hx
        obtain ⟨y, hy, -⟩ := h₃ x hx
        exact ⟨y, hy.1, hy.2⟩
  · exact fun i hi V' hV' => exists_linear_covDiff G hL hn hi fun b _ => hV'.1 b (mem_univ b)
  · have hall : ∀ᶠ W in 𝓝[fieldSpace L n k k] (fun _ => (1 : ComplexMatrix2)), ∀ i : Fin k,
        ∃ T : edgeFormSpace L n k i →ₗ[ℝ] fineOnlyFunctions L n k i, ∀ B : edgeFormSpace L n k i,
          (T B : FineOnlyVertex L n k i → ComplexMatrix2) = contourLogDeriv L n k i
            (descendingChain W i.is_lt.le) (B : Edge L n k i → ComplexMatrix2) := by
      refine eventually_all.2 fun i => ?_
      have h := (hCt.tendsto i i.is_lt.le).eventually
        (hO.contourLogDeriv_linear i i.is_lt)
      refine Eventually.mono h fun W hW => ?_
      rw [descendingChain_eq_chosenProlongIter]
      exact hW
    refine Eventually.mono hall fun W hW => ?_
    choose Ti hTi using hW
    refine ⟨{ toFun := fun B => ⟨fun i => (Ti i (smoothingIterDifferential L n k i (chainBottom W) B) :
                FineOnlyVertex L n k i → ComplexMatrix2), Submodule.mem_pi.2 fun i _ => (Ti i _).2⟩
              map_add' := fun B B' => ?_
              map_smul' := fun a B => ?_ }, fun B => ?_⟩
    · apply Subtype.ext
      funext i
      simp
    · apply Subtype.ext
      funext i
      simp
    · funext i
      exact hTi i _
  · exact exists_restriction_transpose G hD hL hn
end YangMills.Construction.Tower.RealLinearMaps
end
