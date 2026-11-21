import YangMills.Construction.RunningCouplingSlope.CovarianceOfTheFunctionOfTheWholeChainProof
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheFormsProof
import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
import YangMills.Construction.RunningCouplingSlope.RealAnalyticFunctionsTendAtOne
set_option autoImplicit false

section
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.Matrices YangMills.Construction.Conventions
def MeanStepTendsAtIdentity : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    (∀ (B : edgeFormSpace L n k j) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
      Tendsto (fun V => meanCovariantStep V (B : Edge L n k j → ComplexMatrix2) c)
        (𝓝[fieldSpace L n k j] fun _ => (1 : ComplexMatrix2))
        (𝓝 (meanCovariantStep (fun _ => 1) (B : Edge L n k j → ComplexMatrix2) c))) ∧
    (∀ (l : vertexFunctionSpace L n k j) (y : Vertex L n k (j + 1)),
      Tendsto (fun V => adjointCubeAverage V (l : Vertex L n k j → ComplexMatrix2) y)
        (𝓝[fieldSpace L n k j] fun _ => (1 : ComplexMatrix2))
        (𝓝 (adjointCubeAverage (fun _ => 1) (l : Vertex L n k j → ComplexMatrix2) y))) ∧
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun V => meanRadius V c) (𝓝[fieldSpace L n k j] fun _ => (1 : ComplexMatrix2))
        (𝓝 (meanRadius (fun _ => 1) c))
end YangMills.Construction.RunningCouplingSlope
end
end

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace RunningCouplingSlope
namespace MeanStepAtIdentity
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_oneParameter (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof.hasDerivAt_matExp_I_smul <;> assumption
private theorem hasDerivAt_ofReal_restrict {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : ℂ → F} {Y : F} (h : HasDerivAt G Y 0) : HasDerivAt (fun t : ℝ => G (t : ℂ)) Y 0 := by apply _root_.YangMills.SharedProofs.p1580 <;> assumption
variable {L n k j : ℕ}
private def tangentAtZero (V B : Tower.Edge L n k j → ComplexMatrix2) :
    Tower.Edge L n k j → ComplexMatrix2 :=
  open Classical in fun e => if e.IsPositivelyOriented then (Complex.I • B e) * V e
    else V e * (-(Complex.I • B e.opposite))
private theorem tangentAtZero_add_smul (V B B' : Tower.Edge L n k j → ComplexMatrix2) (z : ℂ) :
    tangentAtZero V (z • B + B') = z • tangentAtZero V B + tangentAtZero V B' := by apply _root_.YangMills.DeltaSharedProofs.p502068 <;> assumption
theorem hasDerivAt_expTwist (V B : Tower.Edge L n k j → ComplexMatrix2)
    (hinv : ∀ e, (V e.opposite)⁻¹ = V e)
    (hneg : ∀ e : Tower.Edge L n k j, ¬ e.IsPositivelyOriented → e.opposite.IsPositivelyOriented)
    (e : Tower.Edge L n k j) :
    HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) V e) (tangentAtZero V B e) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanDerivOnForms.hasDerivAt_expTwist_apply <;> assumption
private theorem expTwist_zero_smul {V : Tower.Edge L n k j → ComplexMatrix2}
    (hinv : ∀ e, (V e.opposite)⁻¹ = V e) (B : Tower.Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by apply _root_.YangMills.SharedProofs.p63404 <;> assumption
section PositiveEdge
variable [Fintype (Tower.Edge L n k j)]
private theorem derivatives_at_positiveEdge
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (V : Tower.Edge L n k j → ComplexMatrix2) (hinv : ∀ e, (V e.opposite)⁻¹ = V e)
    (hneg : ∀ e : Tower.Edge L n k j, ¬ e.IsPositivelyOriented → e.opposite.IsPositivelyOriented)
    (c : Tower.Edge L n k (j + 1)) (hc : c.IsPositivelyOriented)
    (hΦ : AnalyticAt ℂ (fun W : Tower.Edge L n k j → ComplexMatrix2 => normalizedMean W c) V)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    ∃ D : (Tower.Edge L n k j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
      ∀ B : Tower.Edge L n k j → ComplexMatrix2,
      HasDerivAt (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c *
        (normalizedMean V c)⁻¹) (D B) 0 ∧
      normalizedMean (PeriodicLattice.expTwist ((0 : ℂ) • B) V) c * (normalizedMean V c)⁻¹ = 1 ∧
      Tower.holLeftDifferential normalizedMean V B c = Complex.I⁻¹ • D B ∧
      Tower.leftDifferential normalizedMean V B c = Complex.I⁻¹ • D B ∧
      D B = fderiv ℂ (fun W : Tower.Edge L n k j → ComplexMatrix2 => normalizedMean W c) V
        (tangentAtZero V B) * (normalizedMean V c)⁻¹ := by
  classical
  set u := normalizedMean V c with hudef
  have huu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u (by rw [hu]; exact isUnit_one)
  have hF := hΦ.differentiableAt.hasFDerivAt
  set Df := fderiv ℂ (fun W : Tower.Edge L n k j → ComplexMatrix2 => normalizedMean W c) V
    with hDf
  let tan : (Tower.Edge L n k j → ComplexMatrix2) →ₗ[ℂ] (Tower.Edge L n k j → ComplexMatrix2) :=
    { toFun := tangentAtZero V
      map_add' := fun B B' => by simpa using tangentAtZero_add_smul V B B' 1
      map_smul' := fun z B => by
        have h0 : tangentAtZero V (0 : Tower.Edge L n k j → ComplexMatrix2) = 0 := by
          funext e
          simp only [tangentAtZero, Pi.zero_apply, smul_zero, neg_zero, Matrix.zero_mul,
            Matrix.mul_zero, ite_self]
        simpa [h0] using tangentAtZero_add_smul V B 0 z }
  refine ⟨LinearMap.mulRight ℂ u⁻¹ ∘ₗ Df.toLinearMap ∘ₗ tan, fun B => ?_⟩
  have hγ0 : PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := expTwist_zero_smul hinv B
  have hγ : HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) V) (tangentAtZero V B) 0 :=
    hasDerivAt_pi.2 fun e => hasDerivAt_expTwist V B hinv hneg e
  have hcomp : HasDerivAt (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c)
      (Df (tangentAtZero V B)) 0 := by
    have hF' : HasFDerivAt (fun W : Tower.Edge L n k j → ComplexMatrix2 => normalizedMean W c) Df
        ((fun t : ℂ => PeriodicLattice.expTwist (t • B) V) 0) := by
      simp only [hγ0]
      exact hF
    exact hF'.comp_hasDerivAt (0 : ℂ) hγ
  have hX := hcomp.mul_const u⁻¹
  have hX0 : (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c * u⁻¹) 0 = 1 := by
    simp only [hγ0]
    exact huu
  have hlog := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 hX0).2.2.1
  have hlogR := hasDerivAt_ofReal_restrict hlog
  refine ⟨hX, hX0, ?_, ?_, rfl⟩
  · have h : Tower.holLeftDifferential normalizedMean V B c = Complex.I⁻¹ • deriv (fun t : ℂ =>
        ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist (t • B) V) c * u⁻¹)) 0 := by
      unfold Tower.holLeftDifferential Tower.extendOddly
      rw [if_pos hc]
      rfl
    rw [h, hlog.deriv]
    rfl
  · have h : Tower.leftDifferential normalizedMean V B c = Complex.I⁻¹ • deriv (fun t : ℝ =>
        ComplexMatrix2.logSeries
          (normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • B) V) c * u⁻¹)) 0 := by
      unfold Tower.leftDifferential Tower.extendOddly
      rw [if_pos hc]
      rfl
    rw [h, hlogR.deriv]
    rfl
end PositiveEdge
private theorem tendsto_of_realLinear {α : Type*} {l : Filter α} {f : α → ComplexMatrix2}
    {x : ComplexMatrix2}
    (h : ∀ φ : ComplexMatrix2 →ₗ[ℝ] ℝ, Tendsto (fun a => φ (f a)) l (𝓝 (φ x))) :
    Tendsto f l (𝓝 x) := by
  refine tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun s => ?_
  let E : ComplexMatrix2 →ₗ[ℝ] ℂ :=
    (Matrix.entryLinearMap ℂ ℂ r s : ComplexMatrix2 →ₗ[ℂ] ℂ).restrictScalars ℝ
  have h1 := h (Complex.reLm ∘ₗ E)
  have h2 := h (Complex.imLm ∘ₗ E)
  have h3 : Tendsto (fun a => (((f a r s).re : ℝ) : ℂ) + (((f a r s).im : ℝ) : ℂ) * Complex.I) l
      (𝓝 ((((x r s).re : ℝ) : ℂ) + (((x r s).im : ℝ) : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp h1).add
      (((Complex.continuous_ofReal.tendsto _).comp h2).mul_const _)
  simpa [Complex.re_add_im] using h3
private theorem continuousAt_inv_at_one : ContinuousAt (fun A : ComplexMatrix2 => A⁻¹) 1 := by apply _root_.YangMills.SharedProofs.p45833 <;> assumption
end MeanStepAtIdentity
open MeanStepAtIdentity in
theorem meanStepTendsAtIdentity_proof (hA : NormalizedMeanAnalytic)
    (hN : NormalizedMeanNearOne) (hT : AnalyticFieldFunctionTendsAtOne)
    (hE : Tower.SmoothingStepAnalyticEntries)
    (hD : NormalizedMeanAtOne)
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex) :
    MeanStepTendsAtIdentity := by
  intro L hL n k j hn hj
  classical
  obtain ⟨ρA, hρA, HA⟩ := hA L hL
  obtain ⟨ρN, hρN, HN⟩ := hN L hL
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hX : ∀ e : Tower.Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented :=
    fun e => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) e
  have hneg : ∀ e : Tower.Edge L n k j, ¬ e.IsPositivelyOriented →
      e.opposite.IsPositivelyOriented := by
    intro e he
    rcases hX e with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h he
    · exact h
  have hfin : Finite (Tower.Edge L n k j) := PeriodicLattice.instFiniteBond _
  let _ : Fintype (Tower.Edge L n k j) := Fintype.ofFinite _
  set l := 𝓝[Tower.fieldSpace L n k j] (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) with hl
  have hflat : (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) ∈
      Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun _ _ => by simp [PeriodicLattice.complexGaugeGroup, ComplexMatrix2.unitDeterminant],
      fun _ _ => (Matrix.inv_eq_right_inv (mul_one 1)).symm⟩
  have hrho : ∀ {ρ : ℝ}, 0 < ρ → ∀ e : Tower.Edge L n k j,
      ComplexMatrix2.operatorNorm ((fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2)) e - 1) < ρ :=
    fun h e => by simpa using h
  have hu1 : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      normalizedMean (fun _ => 1) c = 1 := fun c hc =>
    (hD L hL n k j hn hj 0 (Tower.edgeFormSpace L n k j).zero_mem c hc).2.2.1
  have hAn := fun (c : Tower.Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) =>
    HA n k j hn hj _ hflat (hrho hρA) c hc
  have hnear : ∀ᶠ V in l, ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < ρN := by
    rw [Filter.eventually_all]
    intro e
    have h1 : Tendsto (fun V : Tower.Edge L n k j → ComplexMatrix2 => V e) l (𝓝 1) :=
      ((continuous_apply e).tendsto _).mono_left nhdsWithin_le_nhds
    have := Metric.tendsto_nhds.1 h1 ρN hρN
    filter_upwards [this] with V hV
    simpa [dist_eq_norm] using hV
  obtain ⟨𝒰, h𝒰, -, hnd, hab⟩ := hE L n k j hL hn hj
  have hlim := hT L n k j hL hn hj.le 𝒰
  have hU1 : Tendsto (fun V : Tower.Edge L n k j → ComplexMatrix2 => V) l
      (𝓝 (fun _ : Tower.Edge L n k j => (1 : ComplexMatrix2))) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hu : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun V => normalizedMean V c) l (𝓝 1) := fun c hc => by
    have h := (hAn c hc).2.continuousAt.tendsto
    rw [hu1 c hc] at h
    exact h.mono_left nhdsWithin_le_nhds
  have huinv : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun V => (normalizedMean V c)⁻¹) l (𝓝 1) := fun c hc => by
    have h := continuousAt_inv_at_one.tendsto.comp (hu c hc)
    rw [show (1 : ComplexMatrix2)⁻¹ = 1 from Matrix.inv_eq_right_inv (mul_one 1)] at h
    exact h
  refine ⟨fun B c hc => ?_, fun s y => ?_, fun c hc => ?_⟩
  · set D := fun V : Tower.Edge L n k j → ComplexMatrix2 =>
      fderiv ℂ (fun W : Tower.Edge L n k j → ComplexMatrix2 => normalizedMean W c) V with hDdef
    have hfd : ContinuousAt D (fun _ => 1) := (hAn c hc).2.fderiv.continuousAt
    have htan : ContinuousAt (fun V : Tower.Edge L n k j → ComplexMatrix2 =>
        tangentAtZero V (B : Tower.Edge L n k j → ComplexMatrix2)) (fun _ => 1) := by
      refine (continuous_pi fun e => ?_).continuousAt
      by_cases he : e.IsPositivelyOriented
      · simp only [tangentAtZero, if_pos he]
        exact continuous_const.mul (continuous_apply e)
      · simp only [tangentAtZero, if_neg he]
        exact (continuous_apply e).mul continuous_const
    have hG := (hfd.clm_apply htan).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Tower.fieldSpace L n k j))
    have hG2 : Tendsto (fun V => Complex.I⁻¹ • (D V
        (tangentAtZero V (B : Tower.Edge L n k j → ComplexMatrix2)) *
        (normalizedMean V c)⁻¹)) l (𝓝 (Complex.I⁻¹ • (D (fun _ => 1)
          (tangentAtZero (fun _ => 1) (B : Tower.Edge L n k j → ComplexMatrix2)) * 1))) :=
      (hG.mul (huinv c hc)).const_smul _
    have hform : ∀ V : Tower.Edge L n k j → ComplexMatrix2,
        V ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
        (∀ e, ComplexMatrix2.operatorNorm (V e - 1) < ρA) →
        (∀ e, ComplexMatrix2.operatorNorm (V e - 1) < ρN) →
        Tower.holLeftDifferential normalizedMean V (B : Tower.Edge L n k j → ComplexMatrix2) c =
          Complex.I⁻¹ • (D V (tangentAtZero V (B : Tower.Edge L n k j → ComplexMatrix2)) *
            (normalizedMean V c)⁻¹) := by
      intro V hV h₁ h₂
      have hinv : ∀ e, (V e.opposite)⁻¹ = V e := by
        intro e
        rw [hV.2 e (Set.mem_univ e)]
        exact Matrix.nonsing_inv_nonsing_inv _ (by
          have : Matrix.det (V e) = 1 := hV.1 e (Set.mem_univ e)
          rw [this]
          exact isUnit_one)
      have hu' : Matrix.det (normalizedMean V c) = 1 := (HN n k j hn hj V hV h₂ c hc).2.2.2.1
      obtain ⟨D', hD'⟩ :=
        derivatives_at_positiveEdge hd V hinv hneg c hc (HA n k j hn hj V hV h₁ c hc).2 hu'
      obtain ⟨-, -, e₁, -, e₂⟩ := hD' (B : Tower.Edge L n k j → ComplexMatrix2)
      rw [e₁, e₂]
    have hnearA : ∀ᶠ V in l, ∀ e, ComplexMatrix2.operatorNorm (V e - 1) < ρA := by
      rw [Filter.eventually_all]
      intro e
      have h1 : Tendsto (fun V : Tower.Edge L n k j → ComplexMatrix2 => V e) l (𝓝 1) :=
        ((continuous_apply e).tendsto _).mono_left nhdsWithin_le_nhds
      have := Metric.tendsto_nhds.1 h1 ρA hρA
      filter_upwards [this] with V hV
      simpa [dist_eq_norm] using hV
    have hmdT : Tendsto (fun V => Tower.holLeftDifferential normalizedMean V
        (B : Tower.Edge L n k j → ComplexMatrix2) c) l
        (𝓝 (Tower.holLeftDifferential normalizedMean (fun _ => 1)
          (B : Tower.Edge L n k j → ComplexMatrix2) c)) := by
      rw [hform _ hflat (hrho hρA) (hrho hρN), hu1 c hc,
        show (1 : ComplexMatrix2)⁻¹ = 1 from Matrix.inv_eq_right_inv (mul_one 1)]
      refine hG2.congr' ?_
      filter_upwards [hnear, hnearA, self_mem_nhdsWithin] with V f₁ f₂ f₃
      refine (hform V ?_ f₂ f₁).symm
      exact ⟨fun e _ => (Matrix.mem_specialUnitaryGroup_iff.1 (f₃.1 e (Set.mem_univ e))).2, f₃.2⟩
    have hnT : ∀ y, Tendsto (fun V => Tower.contourLogDrift V
        (B : Tower.Edge L n k j → ComplexMatrix2) y) l
        (𝓝 (Tower.contourLogDrift (fun _ => 1) (B : Tower.Edge L n k j → ComplexMatrix2) y)) :=
      fun y => tendsto_of_realLinear fun φ => hlim _ h𝒰 (hnd B y φ)
    have hpos : ∀ V, meanCovariantStep V (B : Tower.Edge L n k j → ComplexMatrix2) c =
        Tower.holLeftDifferential normalizedMean V (B : Tower.Edge L n k j → ComplexMatrix2) c +
          (normalizedMean V c * Tower.contourLogDrift V (B : Tower.Edge L n k j → ComplexMatrix2)
            c.target * (normalizedMean V c)⁻¹ -
            Tower.contourLogDrift V (B : Tower.Edge L n k j → ComplexMatrix2) c.source) := by
      intro V
      simp only [meanCovariantStep, Pi.add_apply, Tower.covDiff, Tower.extendOddly, if_pos hc,
        ComplexMatrix2.conjugateBy]
    simp only [hpos]
    rw [hu1 c hc, show (1 : ComplexMatrix2)⁻¹ = 1 from Matrix.inv_eq_right_inv (mul_one 1)]
    exact hmdT.add ((((hu c hc).mul (hnT _)).mul (huinv c hc)).sub (hnT _))
  · refine tendsto_of_realLinear fun φ => ?_
    exact hlim _ h𝒰 (hab s y φ)
  · have h := (hAn c hc).1.continuousAt.tendsto
    exact h.mono_left nhdsWithin_le_nhds
end RunningCouplingSlope
end YangMills.Construction
end
