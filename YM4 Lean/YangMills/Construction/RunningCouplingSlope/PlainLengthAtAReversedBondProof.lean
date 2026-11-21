import YangMills.Construction.Lattice.StandingDataGaugeFunctionsAndCentresOverBareSites
import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.RunningCouplingSlope.PlainLengthAtAReversedBond
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSetsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.OppositeLink
open YangMills.Construction.Tower
open YangMills.Construction.Matrices
section Main
variable {L n k j : ℕ}
theorem inv_pathHolonomy (V : Edge L n k j → ComplexMatrix2) (hV : ∀ e, V e.opposite = (V e)⁻¹)
    (hd : ∀ e, Matrix.det (V e) = 1) (l : List (Edge L n k j)) :
    (PeriodicLattice.pathHolonomy V l)⁻¹ =
      PeriodicLattice.pathHolonomy V (PeriodicLattice.reversePath l) := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.inv_pathHolonomy_eq <;> assumption
def adjugateLinearMap : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun := Matrix.adjugate
  map_add' A B := by
    simp only [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a A := by
    simp only [Matrix.adjugate_fin_two, RingHom.id_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
theorem inv_eq_adjugate_of_det_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) :
    g⁻¹ = Matrix.adjugate g := by apply _root_.YangMills.SharedProofs.p104891 <;> assumption
theorem coe_unitStep_succ (hL : 0 < L) (μ : Fin 4) :
    ((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) μ :
        Vertex L n k (j + 1)) : PeriodicLattice.FourTorus L n) =
      (((L : ℤ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ :
        Vertex L n k j) : PeriodicLattice.FourTorus L n) := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k (j + 1)) =
      (L : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) := by
    simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
    push_cast
    have e : -((k : ℤ) - ((j : ℤ) + 1)) = -((k : ℤ) - (j : ℤ)) + 1 := by ring
    rw [e, zpow_add_one₀ hLR]
    ring
  change PeriodicLattice.pointOnAxis L n μ
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k (j + 1))) =
    (L : ℤ) • PeriodicLattice.pointOnAxis L n μ
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j))
  rw [e]
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.pointOnAxis]
  · simp [PeriodicLattice.pointOnAxis, h]
theorem meanRadiusOpposite_holds (hrs : PeriodicLattice.AxialPathReversal)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    MeanRadiusOpposite := by
  intro L hL n k j hn hj V hV c hc
  have hLpos : 0 < L := by have := hL.2; omega
  have hK : 0 < k := by omega
  obtain ⟨μ, hμ⟩ := id hc
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  have hcross := (hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj |>.2.1 c hc
  set d := PeriodicLattice.levelDepth k j with hd
  have hup : (c.target - c.source).toSublattice d =
      (L : ℤ) • PeriodicLattice.unitStep L n d μ := by
    apply Subtype.ext
    have h1 : (((L : ℤ) • PeriodicLattice.unitStep L n d μ : Vertex L n k j) :
          PeriodicLattice.FourTorus L n) =
        ((c.target - c.source : Vertex L n k (j + 1)) : PeriodicLattice.FourTorus L n) := by
      rw [hμ, coe_unitStep_succ hLpos]
    rw [PeriodicLattice.coe_toSublattice_of_coe_eq h1, h1]
  have hdown : (c.source - c.target).toSublattice d =
      -((L : ℤ) • PeriodicLattice.unitStep L n d μ) := by
    apply Subtype.ext
    have h1 : ((-((L : ℤ) • PeriodicLattice.unitStep L n d μ) : Vertex L n k j) :
        PeriodicLattice.FourTorus L n) =
        ((c.source - c.target : Vertex L n k (j + 1)) : PeriodicLattice.FourTorus L n) := by
      have e : c.source - c.target = -(c.target - c.source) := by abel
      rw [e, hμ]
      push_cast
      rw [coe_unitStep_succ (j := j) (k := k) hLpos]
      simp
      rfl
    rw [PeriodicLattice.coe_toSublattice_of_coe_eq h1, h1]
  have hshift : ∀ x : Vertex L n k j, PeriodicLattice.shiftAcross c x =
      x + (L : ℤ) • PeriodicLattice.unitStep L n d μ := by
    intro x
    change x + (c.target - c.source).toSublattice d = _
    rw [hup]
  have hshiftBack : ∀ x : Vertex L n k j,
      PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x) = x := by
    intro x
    have e : PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x) =
        PeriodicLattice.shiftAcross c x + (c.source - c.target).toSublattice d := rfl
    rw [e, hdown, hshift]
    abel
  have hdetV : ∀ e, Matrix.det (V e) = 1 := fun e => hV.1 e (Set.mem_univ e)
  have hoppV : ∀ e, V e.opposite = (V e)⁻¹ := fun e => hV.2 e (Set.mem_univ e)
  have hdetH : ∀ l : List (Edge L n k j),
      Matrix.det (PeriodicLattice.pathHolonomy V l) = 1 := by
    intro l
    induction l with
    | nil => simp [PeriodicLattice.pathHolonomy]
    | cons e l ih =>
      simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons, Matrix.det_mul,
        hdetV, one_mul] at ih ⊢
      exact ih
  have hjm : -(n : ℤ) ≤ d := by
    simp only [hd, PeriodicLattice.levelDepth]; omega
  have hdisp : ∀ x : Vertex L n k j, PeriodicLattice.IsAxialDisplacement x
      (PeriodicLattice.shiftAcross c x) μ (L : ℤ) := by
    intro x
    refine ⟨by rw [hshift]; abel, ?_⟩
    have hL2 : (1 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 1 < L)
    have hexp : (1 : ℤ) < (n : ℤ) + d := by
      simp only [hd, PeriodicLattice.levelDepth]; omega
    have h1 : (L : ℝ) ^ (1 : ℤ) < (L : ℝ) ^ ((n : ℤ) + d) := zpow_lt_zpow_right₀ hL2 hexp
    simpa using h1
  have hcrossOpp : ∀ x : Vertex L n k j, PeriodicLattice.crossingPath c.opposite
      (PeriodicLattice.shiftAcross c x) =
        PeriodicLattice.reversePath (PeriodicLattice.crossingPath c x) := by
    intro x
    have h1 := (hrs L n hL hn d hjm x _ μ (L : ℤ) (hdisp x)).2.1
    change PeriodicLattice.axialPath (PeriodicLattice.shiftAcross c x)
      (PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x)) = _
    rw [hshiftBack x, h1]
    rfl
  have hcv : ∀ x π, contourHolonomy V c.opposite (PeriodicLattice.shiftAcross c x) π =
      Matrix.adjugate (contourHolonomy V c x π) := by
    intro x π
    have hdet1 : Matrix.det (contourHolonomy V c x π) = 1 := by
      rw [contourHolonomy, Matrix.det_mul, Matrix.det_mul, hdetH, hdetH, Matrix.det_nonsing_inv,
        hdetH]
      simp
    rw [← inv_eq_adjugate_of_det_eq_one hdet1, contourHolonomy, contourHolonomy]
    change PeriodicLattice.pathHolonomy V
        (contourLeg c.target (PeriodicLattice.shiftAcross c x) π) *
      PeriodicLattice.pathHolonomy V
        (PeriodicLattice.crossingPath c.opposite (PeriodicLattice.shiftAcross c x)) *
      (PeriodicLattice.pathHolonomy V (contourLeg c.source
        (PeriodicLattice.shiftAcross c.opposite (PeriodicLattice.shiftAcross c x)) π))⁻¹ = _
    rw [hcrossOpp, hshiftBack, ← inv_pathHolonomy V hoppV hdetV, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (by rw [hdetH]; exact isUnit_one), mul_assoc]
  have hmean : contourMean V c.opposite = Matrix.adjugate (contourMean V c) := by
    have e1 : ∑ᶠ x ∈ PeriodicLattice.sitesInBlock d c.source, ∑ π : Equiv.Perm (Fin 4),
          Matrix.adjugate (contourHolonomy V c x π) =
        ∑ᶠ x' ∈ PeriodicLattice.sitesInBlock d c.opposite.source, ∑ π : Equiv.Perm (Fin 4),
          contourHolonomy V c.opposite x' π :=
      finsum_mem_eq_of_bijOn (PeriodicLattice.shiftAcross c) hcross.1 fun x _ =>
        Finset.sum_congr rfl fun π _ => (hcv x π).symm
    rw [contourMean, contourMean, ← e1, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    change _ = adjugateLinearMap _
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_sum]
    rfl
  rw [meanRadius, meanRadius, hmean, Matrix.det_adjugate]
  simp
end Main
end YangMills.Construction.RunningCouplingSlope.OppositeLink
end
