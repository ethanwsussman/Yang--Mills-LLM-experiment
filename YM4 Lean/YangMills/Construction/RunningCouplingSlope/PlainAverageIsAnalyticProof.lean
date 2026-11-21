import YangMills.Construction.RunningCouplingSlope.PlainAverageIsAnalytic
import YangMills.Construction.RunningCouplingSlope.PlainStepAtRealConfigurationsOnTheWholeProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace NormalizedMeanAnalyticity
open Tower Matrices
section MatrixFunctions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem analyticAt_matrix_inv {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x)
    (hdet : IsUnit (Matrix.det (f x))) : AnalyticAt ℂ (fun y => (f y)⁻¹) x := by apply _root_.YangMills.SharedProofs.p7089 <;> assumption
private theorem analyticAt_matrix_det {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => Matrix.det (f y)) x := by apply _root_.YangMills.SharedProofs.p3818 <;> assumption
end MatrixFunctions
variable {L n k j : ℕ}
private theorem analyticAt_pathHolonomy [Fintype (Edge L n k j)] (U : Edge L n k j → ComplexMatrix2)
    (p : List (Edge L n k j)) :
    AnalyticAt ℂ (fun W : Edge L n k j → ComplexMatrix2 => PeriodicLattice.pathHolonomy W p) U := by
  induction p with
  | nil =>
    simpa [PeriodicLattice.pathHolonomy] using analyticAt_const
  | cons e p ih =>
    have hproj : AnalyticAt ℂ (fun W : Edge L n k j → ComplexMatrix2 => W e) U :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Edge L n k j => ComplexMatrix2) e).analyticAt U
    have hcons : (fun W : Edge L n k j → ComplexMatrix2 => PeriodicLattice.pathHolonomy W (e :: p)) =
        fun W => W e * PeriodicLattice.pathHolonomy W p := by
      funext W
      simp [PeriodicLattice.pathHolonomy]
    rw [hcons]
    exact hproj.mul ih
private theorem det_pathHolonomy (U : Edge L n k j → ComplexMatrix2) (hU : ∀ e, Matrix.det (U e) = 1)
    (p : List (Edge L n k j)) : Matrix.det (PeriodicLattice.pathHolonomy U p) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.det_pathHolonomy <;> assumption
private theorem mem_slitPlane_of_sqrt_near_one {w : ℂ} (h : ‖w ^ (1 / 2 : ℂ) - 1‖ < 1 / 2) :
    w ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.mem_slitPlane_of_sqrt_near_one <;> assumption
end NormalizedMeanAnalyticity
open NormalizedMeanAnalyticity Tower Matrices in
theorem normalizedMean_analytic (hnear : NormalizedMeanNearOne)
    (hblocks : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    NormalizedMeanAnalytic := by
  intro L hL
  obtain ⟨ρ, hρ, H⟩ := hnear L hL
  refine ⟨ρ, hρ, ?_⟩
  intro n k j hn hj _ U hU hUρ c hc
  obtain ⟨hrad0, hrad1, -, -, -⟩ := H n k j hn hj U hU hUρ c hc
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hcard := ((hblocks L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have hne : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero hne
    exact Set.toFinite _
  have hdetU : ∀ e, Matrix.det (U e) = 1 := fun e => hU.1 e (Set.mem_univ e)
  have hcontour : ∀ x σ, AnalyticAt ℂ
      (fun W : Edge L n k j → ComplexMatrix2 => contourHolonomy W c x σ) U := by
    intro x σ
    have hunit : IsUnit (Matrix.det (PeriodicLattice.pathHolonomy U
        (contourLeg c.target (PeriodicLattice.shiftAcross c x) σ))) := by
      rw [det_pathHolonomy U hdetU]
      exact isUnit_one
    exact ((analyticAt_pathHolonomy U _).mul (analyticAt_pathHolonomy U _)).mul
      (analyticAt_matrix_inv (analyticAt_pathHolonomy U _) hunit)
  have hmean : AnalyticAt ℂ (fun W : Edge L n k j → ComplexMatrix2 => contourMean W c) U := by
    have e : (fun W : Edge L n k j → ComplexMatrix2 => contourMean W c) = fun W =>
        ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) • ∑ x ∈ hfin.toFinset,
          ∑ σ : Equiv.Perm (Fin 4), contourHolonomy W c x σ := by
      funext W
      rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [e]
    have hsum : AnalyticAt ℂ (fun W : Edge L n k j → ComplexMatrix2 => ∑ x ∈ hfin.toFinset,
        ∑ σ : Equiv.Perm (Fin 4), contourHolonomy W c x σ) U :=
      Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun σ _ => hcontour x σ
    exact (analyticAt_const (v := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L)).smul hsum
  have hslit : Matrix.det (contourMean U c) ∈ Complex.slitPlane :=
    mem_slitPlane_of_sqrt_near_one hrad1
  have hradius : AnalyticAt ℂ (fun W : Edge L n k j → ComplexMatrix2 => meanRadius W c) U :=
    (analyticAt_matrix_det hmean).cpow analyticAt_const hslit
  exact ⟨hradius, (hradius.inv hrad0).smul hmean⟩
end YangMills.Construction.RunningCouplingSlope
end
