import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscsProof
import YangMills.Construction.Towers.DifferentialsUnderTheDilation
import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASideProof
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ScalingTransport
variable {L n k j a b : ℕ}
theorem inv_mem_compactGaugeGroup {A : Matrices.ComplexMatrix2}
    (hA : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem inv_inv_of_mem_compactGaugeGroup {A : Matrices.ComplexMatrix2}
    (hA : A ∈ PeriodicLattice.compactGaugeGroup) : A⁻¹⁻¹ = A := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem expTwist_of_positive (A U : Edge L n k a → Matrices.ComplexMatrix2) {e : Edge L n k a}
    (he : e.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U e = Matrices.ComplexMatrix2.matExp (Complex.I • A e) * U e := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
theorem expTwist_of_not_positive (A U : Edge L n k a → Matrices.ComplexMatrix2) {e : Edge L n k a}
    (he : ¬e.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U e =
      (Matrices.ComplexMatrix2.matExp (Complex.I • A e.opposite) * U e.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
theorem opposite_isPositivelyOriented_of_not {e : Edge L n k a} (he : ¬e.IsPositivelyOriented) :
    e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem expTwist_mem_fieldSpace (hChart : LeftChartFields.Claim)
    (hAdm : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hak : a ≤ k)
    {V X : Edge L n k a → Matrices.ComplexMatrix2} (hV : V ∈ fieldSpace L n k a)
    (hX : X ∈ edgeFormSpace L n k a) :
    PeriodicLattice.expTwist X V ∈ fieldSpace L n k a := by
  have hT := ((hChart.2.2 L k a hAdm hak).1 n hn).1.1
  have hpos : ∀ e : Edge L n k a, e.IsPositivelyOriented →
      Matrices.ComplexMatrix2.matExp (Complex.I • X e) * V e ∈
        PeriodicLattice.compactGaugeGroup := fun e he => by
    have h := (hT.1 V hV X hX ⟨e, he⟩).1 1
    have r : ((1 : ℝ) : ℂ) • X e = X e := by simp
    change Matrices.ComplexMatrix2.matExp (Complex.I • (((1 : ℝ) : ℂ) • X e)) * V e ∈
      PeriodicLattice.compactGaugeGroup at h
    rwa [r] at h
  have hL1 : 1 < L := by
    have := hAdm.2
    omega
  refine ⟨fun e _ => ?_, fun e _ => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · rw [expTwist_of_positive _ _ he]
      exact hpos e he
    · rw [expTwist_of_not_positive _ _ he]
      exact inv_mem_compactGaugeGroup (hpos _ (opposite_isPositivelyOriented_of_not he))
  · by_cases he : e.IsPositivelyOriented
    · have hr : ¬e.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL1
          (by simp only [PeriodicLattice.levelDepth]; omega) he
      rw [expTwist_of_not_positive _ _ hr, expTwist_of_positive _ _ he]
      rfl
    · have hr := opposite_isPositivelyOriented_of_not he
      rw [expTwist_of_positive _ _ hr, expTwist_of_not_positive _ _ he,
        inv_inv_of_mem_compactGaugeGroup (hpos _ hr)]
theorem ofReal_smul_mem_edgeFormSpace {B : Edge L n k a → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k a) (t : ℝ) :
    (t : ℂ) • B ∈ edgeFormSpace L n k a := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.ofReal_smul_mem_edgeFormSpace <;> assumption
theorem transportTotal_smul {X Y : Type*} (σ : X ≃ Y) (z : ℂ) (B : X → Matrices.ComplexMatrix2) :
    z • transportTotal σ B = transportTotal σ (z • B) := rfl
theorem transportTotal_add {X Y : Type*} (σ : X ≃ Y) (B B' : X → Matrices.ComplexMatrix2) :
    transportTotal σ B + transportTotal σ B' = transportTotal σ (B + B') := rfl
theorem scaleEdge_isPositivelyOriented_iff (hL : 0 < L) (hj : j ≤ k) (e : Edge L n k b) :
    (scaleEdge hL hj b e).IsPositivelyOriented ↔ e.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.isPositivelyOriented_scaleEdge <;> assumption
theorem extendOddly_transport (hL : 0 < L) (hj : j ≤ k) (f : Edge L n k b → Matrices.ComplexMatrix2)
    (f' : Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2)
    (h : ∀ e, f' (scaleEdge hL hj b e) = f e) :
    extendOddly f' = transportTotal (scaleEdge hL hj b) (extendOddly f) := by
  funext y
  obtain ⟨e, rfl⟩ := (scaleEdge hL hj b).surjective y
  rw [transportTotal_apply]
  unfold extendOddly
  by_cases he : e.IsPositivelyOriented
  · rw [if_pos ((scaleEdge_isPositivelyOriented_iff hL hj e).2 he), if_pos he, h]
  · have hr : (scaleEdge hL hj b e).opposite = scaleEdge hL hj b e.opposite :=
      PeriodicLattice.Bond.ext rfl rfl
    rw [if_neg (fun h' => he ((scaleEdge_isPositivelyOriented_iff hL hj e).1 h')), if_neg he, hr, h]
theorem logDirectionalDeriv_congr {α β : Type*}
    {φ : (α → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    {ψ : (β → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2} {W : Matrices.ComplexMatrix2}
    {B : α → Matrices.ComplexMatrix2} {B' : β → Matrices.ComplexMatrix2}
    (h : ∀ t : ℝ, ψ ((t : ℂ) • B') = φ ((t : ℂ) • B)) :
    logDirectionalDeriv ℝ ψ W B' = logDirectionalDeriv ℝ φ W B := by
  unfold logDirectionalDeriv
  have r : (fun t : ℝ => Matrices.ComplexMatrix2.logSeries (ψ (algebraMap ℝ ℂ t • B') * W⁻¹)) =
      fun t : ℝ => Matrices.ComplexMatrix2.logSeries (φ (algebraMap ℝ ℂ t • B) * W⁻¹) := by
    funext t
    have := h t
    rw [show algebraMap ℝ ℂ t = (t : ℂ) from rfl, this]
  rw [r]
theorem scalingTransportsDerivatives_holds (hNear : ScalingNearTrivialField)
    (hChart : LeftChartFields.Claim) : ScalingTransportsDerivatives := by
  intro L n k j hL hj hAdm hn a ha b _
  have hC := (hNear L n k j a a hL hj hAdm hn ha ha).1
  have hak : a ≤ k := ha.trans hj
  have hmove : ∀ {U X : Edge L n k a → Matrices.ComplexMatrix2}, U ∈ fieldSpace L n k a →
      X ∈ edgeFormSpace L n k a →
      PeriodicLattice.expTwist (transportTotal (scaleEdge hL hj a) X)
          (transportTotal (scaleEdge hL hj a) U) =
        transportTotal (scaleEdge hL hj a) (PeriodicLattice.expTwist X U) :=
    fun hU hX => (hC.2.2.2.2.2 _ hU _ hX).symm
  refine ⟨?_, ?_⟩
  · intro m m' hm U hU B hB
    unfold leftDifferential
    refine extendOddly_transport hL hj _ _ fun e => ?_
    have hW : m' (transportTotal (scaleEdge hL hj a) U) (scaleEdge hL hj b e) = m U e := by
      rw [hm U hU, transportTotal_apply]
    rw [hW]
    refine logDirectionalDeriv_congr fun t => ?_
    have hX := ofReal_smul_mem_edgeFormSpace hB t
    rw [transportTotal_smul, hmove hU hX, hm _ (expTwist_mem_fieldSpace hChart hAdm hn hak hU hX),
      transportTotal_apply]
  · intro F F' hF U hU B hB B' hB'
    unfold leftSecondDeriv mixedDirectionalDeriv
    have key : ∀ s t : ℝ,
        F' (PeriodicLattice.expTwist
            (algebraMap ℝ ℂ s • transportTotal (scaleEdge hL hj a) B +
              algebraMap ℝ ℂ t • transportTotal (scaleEdge hL hj a) B')
            (transportTotal (scaleEdge hL hj a) U)) =
          F (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B') U) := by
      intro s t
      have hX : algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B' ∈ edgeFormSpace L n k a :=
        add_mem (ofReal_smul_mem_edgeFormSpace hB s) (ofReal_smul_mem_edgeFormSpace hB' t)
      rw [transportTotal_smul, transportTotal_smul, transportTotal_add, hmove hU hX,
        hF _ (expTwist_mem_fieldSpace hChart hAdm hn hak hU hX)]
    simp only [key]
end YangMills.Construction.Tower.ScalingTransport
end
