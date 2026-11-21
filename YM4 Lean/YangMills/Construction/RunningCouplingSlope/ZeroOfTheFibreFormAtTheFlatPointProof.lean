import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmooth
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeastProof
import YangMills.Construction.RunningCouplingSlope.FormAfterTheChangeOfGauge
import YangMills.Construction.RunningCouplingSlope.GradientAtTheFlatPoint
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheSoftAction
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.ZeroOfTheFibreFormAtTheFlatPoint
import YangMills.Construction.Towers.DifferentialOfTheCompositeOfTheCriticalBranchProof
import YangMills.Construction.Towers.PlaquettesAndSumsOfATowerProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.UnitHessianKernel
open Filter YangMills.Construction.Tower YangMills.Construction.Matrices
open scoped Topology
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem deriv_deriv_line_eq_fderiv_fderiv {Φ : E → ℝ} (hΦ : ContDiffAt ℝ 2 Φ 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => Φ (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ Φ) 0 u v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
end Calculus
section Fibre
variable {L n k : ℕ}
private theorem fibreHessian_eq_fibreSecondDeriv {N : ℕ} {a : ℝ} {X : ChainPoint L n k}
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelForms L n k)
    (h : ContDiffAt ℝ 2 (fun w : Fin N → ℝ => chainAction a (fibreMove X (e w))) 0)
    (η : LinearMap.ker (topDeriv X)) :
    fibreHessian a X η = fibreSecondDeriv a X η η := by
  obtain ⟨H, hH⟩ : ∃ H, H = fderiv ℝ
    (fderiv ℝ fun w : Fin N → ℝ => chainAction a (fibreMove X (e w))) 0 := ⟨_, rfl⟩
  have hsecond : ∀ u, H u u = fibreSecondDeriv a X (e u) (e u) := by
    intro u
    rw [hH, ← deriv_deriv_line_eq_fderiv_fderiv h u u]
    simp only [fibreSecondDeriv, map_add, map_smul]
  have hex : ∃ T : QuadraticForm ℝ (LinearMap.ker (topDeriv X)), IsFibreHessian a X T := by
    obtain ⟨c, hc⟩ : ∃ c : LinearMap.ker (topDeriv X) →ₗ[ℝ] Fin N → ℝ,
      c = (e.symm : LevelForms L n k →ₗ[ℝ] Fin N → ℝ) ∘ₗ
        (LinearMap.ker (topDeriv X)).subtype := ⟨_, rfl⟩
    refine ⟨LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ (fun u v => H (c u) (c v))
      ?_ ?_ ?_ ?_), fun ξ => ?_⟩
    · intro u u' v
      simp [map_add]
    · intro r u v
      simp [map_smul]
    · intro u v v'
      simp [map_add]
    · intro r u v
      simp [map_smul]
    · have h1 : c ξ = e.symm (ξ : LevelForms L n k) := by rw [hc]; rfl
      change H (c ξ) (c ξ) = _
      rw [h1, hsecond, e.apply_symm_apply]
  have hs : IsFibreHessian a X (fibreHessian a X) := Classical.epsilon_spec hex
  exact hs η
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
end Fibre
section Squares
private theorem halfTrace_mul_self_re_nonneg {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (ComplexMatrix2.halfTrace (X * X)).re := by apply _root_.YangMills.SharedProofs.p2980 <;> assumption
private theorem eq_zero_of_halfTrace_mul_self_re {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (h : (ComplexMatrix2.halfTrace (X * X)).re = 0) : X = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.eq_zero_of_halfTrace_mul_self_re <;> assumption
private theorem eq_zero_of_finsum_halfTrace_sq {ι : Type*} [Finite ι] {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (h : ∑ᶠ i, (ComplexMatrix2.halfTrace (f i * f i)).re = 0) : f = 0 := by
  have := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype] at h
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => halfTrace_mul_self_re_nonneg (hf i)).1 h
  funext i
  exact eq_zero_of_halfTrace_mul_self_re (hf i) (h2 i (Finset.mem_univ i))
private theorem eq_zero_of_traceFinsumNorm_eq_zero {ι : Type*} [Finite ι] {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) (h : traceFinsumNorm f = 0) : f = 0 := by apply _root_.YangMills.Construction.Tower.StepQuadraticFormProof.eq_zero_of_traceFinsumNorm_eq_zero <;> assumption
end Squares
section Forms
variable {L n k j : ℕ}
private theorem formValues_injective {ξ ξ' : LevelForms L n k} (h : formValues ξ = formValues ξ') :
    ξ = ξ' :=
  Prod.ext (Subtype.ext (congrArg Prod.fst h))
    (funext fun i => Subtype.ext (congrFun (congrArg Prod.snd h) i))
private theorem formValues_add (ξ ξ' : LevelForms L n k) :
    formValues (ξ + ξ') = formValues ξ + formValues ξ' := rfl
private theorem forwardFrom_isPositivelyOriented (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem eq_forwardFrom_of_sub {b : Edge L n k j} {μ : Fin 4}
    (h : b.target - b.source = PeriodicLattice.unitStep L n _ μ) :
    b = PeriodicLattice.Bond.forwardFrom b.source μ := by apply _root_.YangMills.Construction.Tower.ClosedEdgeForms.eq_forwardFrom_of_sub <;> assumption
private theorem extendOddly_eq {f C : Edge L n k j → ComplexMatrix2} (hC : C ∈ edgeFormSpace L n k j)
    (h : ∀ c : Edge L n k j, c.IsPositivelyOriented → f c = C c) : extendOddly f = C := by apply _root_.YangMills.Construction.Tower.ProlongDifferential.extendOddly_eq <;> assumption
private theorem conjugateBy_one (A : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 A = A := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
private theorem covDiff_one (l : Vertex L n k j → ComplexMatrix2) :
    covDiff (fun _ => (1 : ComplexMatrix2)) l = vertexCoboundary l := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.covDiff_trivialField <;> assumption
private theorem gaugeOrbitValues_unitPoint (l : Vertex L n k 0 → ComplexMatrix2) :
    gaugeOrbitValues (unitPoint L n k) l = (vertexCoboundary l, fun _ => 0) := by
  refine Prod.ext (covDiff_one l) (funext fun i => ?_)
  funext b
  simp only [gaugeOrbitValues, unitPoint, extendOddly, conjugateBy_one, sub_self, dite_eq_ite,
    ite_self]
  simp
private theorem levelPairing_zero_left (v : LevelValues L n k) :
    levelPairing (formValues (0 : LevelForms L n k)) v = 0 := by
  simp [levelPairing, formValues, edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges,
    ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem gaugedFormValue_zero (a : ℝ) (X : ChainPoint L n k) (ξ : LevelForms L n k) :
    gaugedFormValue a X 0 0 ξ = RunningCouplingSlope.leftSecondDeriv (chainAction a) X ξ ξ := by
  simp [gaugedFormValue, levelPairing_zero_left, traceFinsumPairing, restrictToPositiveEdges,
    ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem levelField_unitPoint (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → levelField (unitPoint L n k) j = fun _ => 1 := by apply _root_.YangMills.SharedProofs.p64130 <;> assumption
private theorem tangentTransport_of_constant (hD : NormalizedMeanAtOne)
    (hR : TrivialLinearization.AllRelationsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (ξ : LevelForms L n k) (hν : ∀ i, ξ.2 i = 0) (b : Fin 4 → ComplexMatrix2)
    (hb : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x μ) = b μ) :
    ∀ j, j ≤ k → tangentTransport (unitPoint L n k) ξ j ∈ edgeFormSpace L n k j ∧
      ∀ (x : Vertex L n k j) (μ : Fin 4),
        tangentTransport (unitPoint L n k) ξ j (PeriodicLattice.Bond.forwardFrom x μ) =
          ((L : ℂ) ^ j) • b μ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨ξ.1.2, fun x μ => ?_⟩
    simpa [tangentTransport] using hb x μ
  | succ j ih =>
    intro hj
    have hlt : j < k := hj
    obtain ⟨hF, hv⟩ := ih hlt.le
    obtain ⟨-, hC, -⟩ := (hR L hL).1 n k j k hn hlt le_rfl
    obtain ⟨-, -, hQ, hF', hval⟩ := hC _ hF _ hv
    have heq : tangentTransport (unitPoint L n k) ξ (j + 1) =
        crossingSmoothing L n k j (tangentTransport (unitPoint L n k) ξ j) := by
      rw [tangentTransport, dif_pos hlt]
      refine extendOddly_eq hF' fun c hc => ?_
      have h1 := (hD L hL n k j hn hlt _ hF c hc).2.2.2.2
      have h2 : (unitPoint L n k).noise ⟨j, hlt⟩ ⟨c, hc⟩ = 1 := rfl
      rw [dif_pos hc, h2, conjugateBy_one, levelField_unitPoint hD hL hn j hlt.le, h1, hQ, hν]
      simp
    rw [heq]
    refine ⟨hF', fun x μ => ?_⟩
    rw [hval, pow_succ, mul_comm, mul_smul]
end Forms
section Torus
variable {L n k : ℕ}
private theorem apply_add_zsmul_sum_of_invariant {A V : Type*} [AddCommGroup A] {h : A → V}
    {e : Fin 4 → A} (hi : ∀ ν x, h (x + e ν) = h x) (m : Fin 4 → ℤ) (x : A) :
    h (x + ∑ μ, m μ • e μ) = h x := by apply _root_.YangMills.Construction.Tower.ClosedEdgeForms.apply_add_zsmul_sum_of_invariant <;> assumption
private theorem coboundary_add_const_eq_zero (h : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {g : Vertex L n k k → ComplexMatrix2} {b : Fin 4 → ComplexMatrix2}
    (hg : ∀ (x : Vertex L n k k) (μ : Fin 4),
      g (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) - g x + b μ = 0) :
    (∀ μ, b μ = 0) ∧ ∀ y, g y = g 0 := by
  open PeriodicLattice in
  obtain ⟨-, hpos, -, hgen, hmod, -⟩ :=
    (h L n hL.1 hL.2 hn).1 (levelDepth k k) (by simp only [levelDepth]; omega)
  have hNe : ∀ μ, (2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k)) •
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ = 0 := by
    intro μ
    have e := (hmod 0 (Pi.single μ
      ((2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k) : ℕ) : ℤ)) 0).2
      (fun ν => by
        by_cases hν : ν = μ
        · subst hν
          simp [Int.ModEq]
        · simp [Pi.single_eq_of_ne hν])
    simp only [PeriodicLattice.offsetSite, Pi.single_apply, ite_smul, zero_smul, Pi.zero_apply,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero,
      zero_add] at e
    rw [← natCast_zsmul]
    exact e
  have hi : ∀ (μ : Fin 4) (x : Vertex L n k k) (i : ℕ),
      g (x + i • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) = g x - i • b μ := by
    intro μ x i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hg (x + i • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) μ
      rw [succ_nsmul, ← add_assoc, succ_nsmul]
      rw [ih] at this
      rw [eq_sub_iff_add_eq, ← sub_eq_zero]
      rw [← this]
      abel
  have hb : ∀ μ, b μ = 0 := by
    intro μ
    have h1 := hi μ 0 (2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k))
    rw [hNe μ, add_zero] at h1
    have h2 := (Nat.cast_smul_eq_nsmul ℂ
      (2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k)) (b μ)).trans
        (sub_eq_self.1 h1.symm)
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3) hpos.ne'
    · exact h3
  refine ⟨hb, fun y => ?_⟩
  have hinv : ∀ (ν : Fin 4) (x : Vertex L n k k),
      g (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν) = g x := by
    intro ν x
    have := hg x ν
    rw [hb ν, add_zero] at this
    exact sub_eq_zero.1 this
  obtain ⟨m, hm⟩ := hgen 0 y
  rw [hm]
  exact apply_add_zsmul_sum_of_invariant hinv m 0
end Torus
section Change
variable {L n k : ℕ}
private theorem exists_shiftedGauge_preimage {X : ChainPoint L n k} (hm : ChainLinearMapsAt X)
    (hc : ((L : ℝ) ^ (4 * k)) ≠ 0) {η : LevelForms L n k} (hη : topDeriv X η = 0) :
    ∃ (σ : vertexFunctionSpace L n k 0) (ξ : LevelForms L n k),
      ξ ∈ LinearMap.ker (shiftedGaugeMap X) ∧
      _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ = η ∧ η = ξ + gaugeOrbitMap X σ := by
  obtain ⟨c, hcc⟩ : ∃ c : ℝ, c = (L : ℝ) ^ (4 * k) := ⟨_, rfl⟩
  rw [← hcc] at hc
  have hnD : ∀ g : vertexFunctionSpace L n k k,
      chainDriftMap X (gaugeOrbitMap X (extendFromTopLinear L n k g)) = c⁻¹ • g - g := by
    intro g
    have h1 := hm.mean_eq (extendFromTopLinear L n k g)
    rw [hm.mean_extend g, hm.restrict_extend g, ← hcc] at h1
    rw [h1]
    abel
  obtain ⟨g, hg⟩ : ∃ g, g = chainDriftMap X η := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = c • extendFromTopLinear L n k g := ⟨_, rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = η - gaugeOrbitMap X σ := ⟨_, rfl⟩
  have hnξ : chainDriftMap X ξ = c • g := by
    rw [hξ, map_sub, hσ, map_smul, map_smul, hnD, ← hg, smul_sub, smul_smul, mul_inv_cancel₀ hc,
      one_smul]
    abel
  have hQξ : topDeriv X ξ = -topCovDiffLinear (levelField X k) (c • g) := by
    rw [hξ, map_sub, hη, hm.topDeriv_orbit, hσ, map_smul, hm.restrict_extend, zero_sub]
  have hker : ξ ∈ LinearMap.ker (shiftedGaugeMap X) := by
    refine LinearMap.mem_ker.2 (Subtype.ext ?_)
    rw [hm.shifted_spec ξ]
    simp only [shiftedGaugeValues]
    rw [← hm.topDeriv_spec ξ, ← hm.drift_spec ξ, ← hm.topCovDiff_apply, hQξ, hnξ]
    simp
  obtain ⟨T, hTd⟩ : ∃ T : LevelForms L n k →ₗ[ℝ] LevelForms L n k,
      T = LinearMap.id + gaugeOrbitMap X ∘ₗ extendFromTopLinear L n k ∘ₗ chainDriftMap X :=
    ⟨_, rfl⟩
  have hTv : ∀ ζ, T ζ = ζ + gaugeOrbitMap X (extendFromTopLinear L n k (chainDriftMap X ζ)) :=
    fun ζ => by
      rw [hTd]
      rfl
  have hT : IsGaugeTransform X T := by
    intro ζ
    rw [hTv, formValues_add, hm.orbit_spec]
    congr 2
    rw [hm.extend_apply, hm.drift_spec ζ]
    rfl
  have hs : IsGaugeTransform X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X) := Classical.epsilon_spec ⟨T, hT⟩
  have hτ : _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ = T ξ := formValues_injective ((hs ξ).trans (hT ξ).symm)
  refine ⟨σ, ξ, hker, ?_, ?_⟩
  · rw [hτ, hTv, hnξ, map_smul, ← hσ, hξ]
    abel
  · rw [hξ]
    abel
end Change
private theorem finite_face {L n k : ℕ} (j : ℕ) [NeZero L] : Finite (Face L n k j) :=
  Finite.of_injective (fun p : Face L n k j => (p.origin, p.firstAxis, p.secondAxis)) fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact PeriodicLattice.Plaquette.ext h.1 h.2.1 h.2.2
theorem fibreHessianKernelAtUnit_holds (hForm : FibreHessianAfterGaugeChange)
    (hGrad : GradientAtUnitPoint) (hSec : ChainActionHessianAtQuiet)
    (hFlat : UnitPointIsMinimizer) (hMaps : ChainMapsAtMinimizers)
    (hSmooth : ChainActionFibreContDiff) (hDer : NormalizedMeanAtOne)
    (hSp : FiniteSideFormSpaces) (hTower : ActionFacts.Statement)
    (hClosed : ClosedEdgeFormsOnPeriodicLattice)
    (hRel : TrivialLinearization.AllRelationsStatement)
    (hCoord : PeriodicLattice.CoordinateDescription) :
    FibreHessianKernelAtUnit := by
  intro a ha L hL k n hk hn η hη hzero
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨hL0⟩
  have h₀ := hSp L n k 0 hL hn (Nat.zero_le k)
  have hi : ∀ i : Fin k, _ := fun i : Fin k => hSp L n k (i + 1) hL hn i.2
  haveI := h₀.2.1
  haveI : ∀ i : Fin k, FiniteDimensional ℝ (edgeFormSpace L n k (i + 1)) := fun i => (hi i).2.1
  haveI : ∀ i : Fin k, Finite (PositiveEdge L n k (i + 1)) := fun i => (hi i).1
  haveI : FiniteDimensional ℝ (LevelForms L n k) := inferInstance
  haveI : Finite (Face L n k 0) := finite_face 0
  obtain ⟨N, hN⟩ : ∃ N, N = Module.finrank ℝ (LevelForms L n k) := ⟨_, rfl⟩
  obtain ⟨e⟩ : Nonempty ((Fin N → ℝ) ≃ₗ[ℝ] LevelForms L n k) := by
    subst hN
    exact ⟨(Module.finBasis ℝ (LevelForms L n k)).equivFun.symm⟩
  obtain ⟨hread, hleast⟩ := hFlat a ha L hL k n hk hn
  have hm : ChainLinearMapsAt (unitPoint L n k) :=
    (hMaps a ha L hL k n hk hn).self_of_nhds _ hread _ hleast
  have hφ : ContDiffAt ℝ 2
      (fun w : Fin N → ℝ => chainAction a (fibreMove (unitPoint L n k) (e w))) 0 := by
    have hΨ := hSmooth a L hL k n hk hn N e.toLinearMap
    have h1 : ContDiffAt ℝ 2 (fun w : Fin N → ℝ => ((0 : Fin N → ℝ), w)) 0 :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    have h2 := ContDiffAt.comp (g := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      chainAction a (fibreMove (expMove (e.toLinearMap p.1) (unitPoint L n k)) (e.toLinearMap p.2)))
      (f := fun w : Fin N → ℝ => ((0 : Fin N → ℝ), w)) (0 : Fin N → ℝ) hΨ h1
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp [expMove_zero_unitPoint]
  have hker : η ∈ LinearMap.ker (topDeriv (unitPoint L n k)) := LinearMap.mem_ker.2 hη
  have hfib := fibreHessian_eq_fibreSecondDeriv e hφ ⟨η, hker⟩
  obtain ⟨σ, ξ, hξ, hτ, hηξ⟩ :=
    exists_shiftedGauge_preimage hm (pow_ne_zero _ (by exact_mod_cast hL0)) hη
  have hgrad : IsLevelGradient (chainAction a) (unitPoint L n k) 0 := hGrad a ha L hL k n hk hn
  have hmul : IsTopMultiplier (unitPoint L n k) 0 0 := by
    intro ζ
    rw [levelPairing_zero_left]
    simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, ComplexMatrix2.halfTrace,
      ComplexMatrix2.fullTrace]
  obtain ⟨η', hη1, hη2⟩ :=
    (hForm a ha L hL k n hk hn).self_of_nhds _ hread _ hleast 0 0 hgrad hmul ξ hξ
  have hηη : η' = ⟨η, hker⟩ := Subtype.ext (hη1.trans hτ)
  rw [hηη, hfib, gaugedFormValue_zero] at hη2
  have hsec0 : RunningCouplingSlope.leftSecondDeriv (chainAction a) (unitPoint L n k) ξ ξ = 0 := by
    rw [← hη2]
    exact hzero
  have hconf : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k 0 :=
    ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
  have hsec := (hSec a L hL k n hn).self_of_nhdsWithin hconf ξ
  have hA : Tower.leftSecondDeriv (plaquetteAction L n k) (fun _ => (1 : ComplexMatrix2))
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) (ξ.1 : Edge L n k 0 → ComplexMatrix2) =
        traceFinsumNorm (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2)) ^ 2 :=
    (hTower L k n hL hn).2.2.2.2.2.2 _ ξ.1.2
  have hlen : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (meanRadius (meanIterate (fun _ => (1 : ComplexMatrix2)) i) c.1).re = 1 := by
    intro i c
    have h1 : meanIterate (L := L) (n := n) (k := k) (fun _ => (1 : ComplexMatrix2)) i = fun _ => 1 :=
      levelField_unitPoint hDer hL hn i i.2.le
    rw [h1, (hDer L hL n k i hn i.2 0 (Submodule.zero_mem _) c.1 c.2).2.1]
    simp
  simp only [hlen, one_mul] at hsec
  have hsec1 : traceFinsumNorm (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2)) ^ 2 +
      a * ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
        (ComplexMatrix2.halfTrace
          (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 *
          ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1)).re = 0 := by
    rw [← hA]
    exact hsec.symm.trans hsec0
  have hsu : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈
        ComplexMatrix2.hermitianTraceless :=
    fun i c => (ξ.2 i).2.1 c.1 c.2
  have hterm : ∀ i : Fin k, 0 ≤ ∑ᶠ c : PositiveEdge L n k (i + 1),
      (ComplexMatrix2.halfTrace
        (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 *
        ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1)).re :=
    fun i => finsum_nonneg fun c => halfTrace_mul_self_re_nonneg (hsu i c)
  have hS : 0 ≤ ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (ComplexMatrix2.halfTrace
        (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 *
        ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1)).re :=
    Finset.sum_nonneg fun i _ => hterm i
  have hsq := sq_nonneg (traceFinsumNorm (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2)))
  have haS := mul_nonneg ha.le hS
  have hS0 : ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (ComplexMatrix2.halfTrace
        (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 *
        ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1)).re = 0 := by
    have : a * _ = 0 := le_antisymm (by linarith) haS
    exact (mul_eq_zero.1 this).resolve_left ha.ne'
  have hnorm : traceFinsumNorm (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2)) = 0 := by
    have : traceFinsumNorm (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2)) ^ 2 = 0 :=
      le_antisymm (by linarith) hsq
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hν : ∀ i, ξ.2 i = 0 := by
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 hS0 i (Finset.mem_univ i)
    have h2 := eq_zero_of_finsum_halfTrace_sq (hsu i) h1
    refine Subtype.ext ?_
    have h3 : extendOddly (fun _ => 0) =
        ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) :=
      extendOddly_eq (ξ.2 i).2 fun c hc => (congrFun h2 ⟨c, hc⟩).symm
    rw [← h3]
    funext b
    simp [extendOddly]
  have hcl : IsClosedEdgeForm (ξ.1 : Edge L n k 0 → ComplexMatrix2) := by
    refine eq_zero_of_traceFinsumNorm_eq_zero (fun p => ?_) hnorm
    have hb : ∀ (x : Vertex L n k 0) (μ : Fin 4),
        (ξ.1 : Edge L n k 0 → ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x μ) ∈
          ComplexMatrix2.hermitianTraceless :=
      fun x μ => ξ.1.2.1 _ (forwardFrom_isPositivelyOriented x μ)
    exact ComplexMatrix2.hermitianTraceless.sub_mem
      (ComplexMatrix2.hermitianTraceless.sub_mem
        (ComplexMatrix2.hermitianTraceless.add_mem (hb _ _) (hb _ _)) (hb _ _)) (hb _ _)
  obtain ⟨l, hl, b, hb, hconst, hB⟩ := (hClosed L n k 0 hL hn (Nat.zero_le k) ξ.1 ξ.1.2).1 hcl
  have horb1 : ∀ w : vertexFunctionSpace L n k 0,
      (((gaugeOrbitMap (unitPoint L n k) w).1 : edgeFormSpace L n k 0) :
        Edge L n k 0 → ComplexMatrix2) = vertexCoboundary (w : Vertex L n k 0 → ComplexMatrix2) :=
    fun w => (congrArg Prod.fst (hm.orbit_spec w)).trans
      (congrArg Prod.fst (gaugeOrbitValues_unitPoint _))
  have horb2 : ∀ (w : vertexFunctionSpace L n k 0) (i : Fin k),
      (gaugeOrbitMap (unitPoint L n k) w).2 i = 0 := by
    intro w i
    refine Subtype.ext ?_
    exact congrFun (congrArg Prod.snd ((hm.orbit_spec w).trans (gaugeOrbitValues_unitPoint _))) i
  obtain ⟨l₁, hl₁⟩ : ∃ l₁ : vertexFunctionSpace L n k 0, l₁ = ⟨l, hl⟩ + σ := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : LevelForms L n k, α = (⟨b, hb⟩, 0) := ⟨_, rfl⟩
  have hsplit : η = gaugeOrbitMap (unitPoint L n k) l₁ + α := by
    refine Prod.ext (Subtype.ext ?_) (funext fun i => ?_)
    · rw [hηξ]
      show ((ξ.1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) +
          (((gaugeOrbitMap (unitPoint L n k) σ).1 : edgeFormSpace L n k 0) :
            Edge L n k 0 → ComplexMatrix2) =
        (((gaugeOrbitMap (unitPoint L n k) l₁).1 : edgeFormSpace L n k 0) :
            Edge L n k 0 → ComplexMatrix2) +
          ((α.1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2)
      rw [horb1, horb1, hB, hα, hl₁]
      funext c
      simp only [vertexCoboundary, Pi.add_apply, Submodule.coe_add]
      abel
    · rw [hηξ]
      show ξ.2 i + (gaugeOrbitMap (unitPoint L n k) σ).2 i =
        (gaugeOrbitMap (unitPoint L n k) l₁).2 i + α.2 i
      rw [horb2, horb2, hν, hα]
      simp
  have hflatk := levelField_unitPoint (k := k) hDer hL hn k le_rfl
  obtain ⟨bμ, hbμ⟩ : ∃ bμ : Fin 4 → ComplexMatrix2,
      bμ = fun μ => b (PeriodicLattice.Bond.forwardFrom 0 μ) := ⟨_, rfl⟩
  have hαv : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      ((α.1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2)
        (PeriodicLattice.Bond.forwardFrom x μ) = bμ μ := by
    intro x μ
    rw [hα, hbμ]
    exact hconst μ x 0
  have hαν : ∀ i, α.2 i = 0 := fun i => by rw [hα]; rfl
  have hmove := (tangentTransport_of_constant hDer hRel hL hn α hαν bμ hαv k le_rfl).2
  have htop : vertexCoboundary (restrictToTopLinear L n k l₁ : Vertex L n k k → ComplexMatrix2) +
      tangentTransport (unitPoint L n k) α k = 0 := by
    have h1 : topDeriv (unitPoint L n k) η = 0 := hη
    rw [hsplit, map_add, hm.topDeriv_orbit] at h1
    have h2 := congrArg (fun f : edgeFormSpace L n k k => (f : Edge L n k k → ComplexMatrix2)) h1
    simp only [Submodule.coe_add, ZeroMemClass.coe_zero] at h2
    rw [hm.topCovDiff_apply, hm.topDeriv_spec α, hflatk, covDiff_one] at h2
    exact h2
  obtain ⟨hb0, hgc⟩ := coboundary_add_const_eq_zero (k := k) hCoord hL hn
    (g := (restrictToTopLinear L n k l₁ : Vertex L n k k → ComplexMatrix2))
    (b := fun μ => ((L : ℂ) ^ k) • bμ μ) (fun x μ => by
      have h1 := congrFun htop (PeriodicLattice.Bond.forwardFrom x μ)
      rw [Pi.add_apply, hmove x μ] at h1
      exact h1)
  have hbμ0 : ∀ μ, bμ μ = 0 := fun μ =>
    (smul_eq_zero.1 (hb0 μ)).resolve_left (pow_ne_zero _ (by exact_mod_cast hL0))
  have hb00 : b = 0 := by
    have h3 : extendOddly (fun _ => 0) = b := by
      refine extendOddly_eq hb fun c hc => ?_
      obtain ⟨μ, hμ⟩ := hc
      rw [eq_forwardFrom_of_sub hμ, hconst μ _ 0]
      exact (congrFun hbμ μ ▸ hbμ0 μ).symm
    rw [← h3]
    funext c
    simp [extendOddly]
  obtain ⟨C, hC⟩ : ∃ C : ComplexMatrix2,
      C = (restrictToTopLinear L n k l₁ : Vertex L n k k → ComplexMatrix2) 0 := ⟨_, rfl⟩
  have hCm : C ∈ ComplexMatrix2.hermitianTraceless := by
    rw [hC]
    exact (restrictToTopLinear L n k l₁).2 _ (Set.mem_univ _)
  obtain ⟨l', hl'⟩ : ∃ l' : vertexFunctionSpace L n k 0,
      l' = l₁ - ⟨fun _ => C, fun _ _ => hCm⟩ := ⟨_, rfl⟩
  refine ⟨l', ?_, ?_⟩
  · intro y
    have h1 := hgc y
    rw [hm.restrict_apply l₁] at h1 hC
    rw [hl']
    show (l₁ : Vertex L n k 0 → ComplexMatrix2) _ - C = 0
    rw [hC]
    exact sub_eq_zero.2 h1
  · have h4 : α = 0 := by
      rw [hα]
      refine Prod.ext (Subtype.ext hb00) rfl
    rw [hsplit, h4, add_zero]
    refine formValues_injective ?_
    rw [hm.orbit_spec l₁, hm.orbit_spec l', gaugeOrbitValues_unitPoint, gaugeOrbitValues_unitPoint, hl']
    refine Prod.ext ?_ rfl
    funext c
    simp [vertexCoboundary]
end YangMills.Construction.RunningCouplingSlope.UnitHessianKernel
end
