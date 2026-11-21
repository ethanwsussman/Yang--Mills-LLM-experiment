import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.LimitsOfLatticeFamilies.ClosedBallsAndTheTorusAreCompact
import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.LimitsOfLatticeFamilies.ProjectionKernelsAndShortestLifts
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace CompactBallsAndTorus
theorem continuous_euclidNormVec : Continuous TorusMetric.euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem isCompact_euclidNormVec_sub_le (v : Fin 4 → ℝ) (R : ℝ) :
    IsCompact {u : Fin 4 → ℝ | TorusMetric.euclidNormVec (u - v) ≤ R} := by apply _root_.YangMills.DeltaSharedProofs.p501115 <;> assumption
theorem isCompactWrt_image_of_lipschitz {X : Type*} (d : X → X → ℝ) (f : (Fin 4 → ℝ) → X)
    (hf : ∀ u u', d (f u) (f u') ≤ TorusMetric.euclidNormVec (u - u'))
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) : MetricNotions.IsCompactWrt d (f '' K) := by
  intro 𝒰 hopen hcover
  have hpre : ∀ U ∈ 𝒰, IsOpen (f ⁻¹' U) := by
    intro U hU
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨r, hr, hball⟩ := hopen U hU (f x) hx
    have hcont : Continuous fun u : Fin 4 → ℝ => TorusMetric.euclidNormVec (x - u) :=
      continuous_euclidNormVec.comp (continuous_const.sub continuous_id)
    have hzero : TorusMetric.euclidNormVec (x - x) < r := by
      simpa [TorusMetric.euclidNormVec] using hr
    refine Filter.mem_of_superset
      ((isOpen_lt hcont continuous_const).mem_nhds hzero) fun y hy => ?_
    exact hball (f y) (lt_of_le_of_lt (hf x y) hy)
  obtain ⟨b, hb, hfin, hcov⟩ := hK.elim_finite_subcover_image hpre (by
    intro u hu
    obtain ⟨U, hU, hmem⟩ := hcover (mem_image_of_mem f hu)
    exact mem_iUnion₂.2 ⟨U, hU, hmem⟩)
  refine ⟨b, hb, hfin, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨U, hU, hmem⟩ := mem_iUnion₂.1 (hcov hu)
  exact ⟨U, hU, hmem⟩
theorem claim_holds (hproj : ProjKernelAndMinimalLifts.Claim)
    (hlen : InvariantDistFromNorm.Claim) :
    CompactBallsAndTorus.Claim := by
  intro s
  have ballCompact : ∀ (Y : ModelSpace) (x : Y.Carrier s) (R : ℝ),
      ModelSpace.IsCompactIn s Y (ModelSpace.closedBall s Y x R) := by
    intro Y x R
    obtain ⟨hadd, hsurj, hshort, -, hlip, -⟩ := (hproj s).2 Y
    obtain ⟨v, rfl⟩ := hsurj x
    have himage : ModelSpace.closedBall s Y (ModelSpace.proj s Y v) R =
        ModelSpace.proj s Y '' {u | TorusMetric.euclidNormVec (u - v) ≤ R} := by
      ext y
      constructor
      · intro hy
        obtain ⟨w, hw, hwl⟩ := hshort (y - ModelSpace.proj s Y v)
        refine ⟨w + v, ?_, ?_⟩
        · show TorusMetric.euclidNormVec (w + v - v) ≤ R
          rw [add_sub_cancel_right, hwl]
          exact hy
        · have hw' : ModelSpace.proj s Y w = y - ModelSpace.proj s Y v := hw
          rw [hadd, hw', sub_add_cancel]
      · rintro ⟨u, hu, rfl⟩
        exact (hlip u v).trans hu
    rw [himage]
    exact isCompactWrt_image_of_lipschitz (ModelSpace.dist s Y) (ModelSpace.proj s Y) hlip
      (isCompact_euclidNormVec_sub_le v R)
  have compactBounded : ∀ (Y : ModelSpace) (S : Set (Y.Carrier s)), ModelSpace.IsCompactIn s Y S →
      ∃ N : ℕ, ∀ y ∈ S, ModelSpace.norm s Y y < (N : ℝ) + 1 := by
    intro Y S hS
    obtain ⟨htri, heven, -⟩ := hlen s Y
    let u : ℕ → Set (Y.Carrier s) := fun n => {y | ModelSpace.norm s Y y < (n : ℝ) + 1}
    have hopen : ∀ U ∈ range u, MetricNotions.IsOpenWrt (ModelSpace.dist s Y) U := by
      rintro _ ⟨n, rfl⟩ x hx
      have hx' : ModelSpace.norm s Y x < (n : ℝ) + 1 := hx
      refine ⟨(n : ℝ) + 1 - ModelSpace.norm s Y x, sub_pos.2 hx', fun y hy => ?_⟩
      have hy' : ModelSpace.norm s Y (x - y) < (n : ℝ) + 1 - ModelSpace.norm s Y x := hy
      have h := htri x (-(x - y))
      rw [heven] at h
      have e : x + -(x - y) = y := by abel
      rw [e] at h
      show ModelSpace.norm s Y y < (n : ℝ) + 1
      linarith
    have hcover : S ⊆ ⋃₀ range u := by
      intro y _
      obtain ⟨n, hn⟩ := exists_nat_gt (ModelSpace.norm s Y y)
      exact ⟨u n, mem_range_self n, show ModelSpace.norm s Y y < (n : ℝ) + 1 by linarith⟩
    obtain ⟨𝒰', hsub, hfin, hcov⟩ := hS (range u) hopen hcover
    have := hfin.to_subtype
    have hpick : ∀ U : 𝒰', ∃ n, u n = U := fun U => hsub U.2
    choose g hg using hpick
    obtain ⟨N, hN⟩ := Finite.exists_le g
    refine ⟨N, fun y hy => ?_⟩
    obtain ⟨U, hU, hyU⟩ := hcov hy
    have hmem : y ∈ u (g ⟨U, hU⟩) := by
      rw [hg]
      exact hyU
    have hmem' : ModelSpace.norm s Y y < ((g ⟨U, hU⟩ : ℕ) : ℝ) + 1 := hmem
    have hle : ((g ⟨U, hU⟩ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN ⟨U, hU⟩
    linarith
  have hside : 0 < s.side := by
    have hL : 13 ≤ s.L := s.isAdmissible.2
    have hLpos : (0 : ℝ) < s.L := by
      have : 0 < s.L := by omega
      exact_mod_cast this
    show 0 < PeriodicLattice.torusSide s.L s.m
    unfold PeriodicLattice.torusSide
    positivity
  have lifts : ∀ z : torus.Carrier s, ∃ v : Fin 4 → ℝ, ModelSpace.IsLiftOf s torus z v ∧
      ∀ μ, v μ ∈ Icc (-(s.side / 2)) (s.side / 2) := by
    intro z
    have hz : ∀ μ, ∃ v : ℝ, (v : AddCircle s.side) = (z : TorusMetric.Torus4 s.side) μ ∧
        |v| = ‖(z : TorusMetric.Torus4 s.side) μ‖ :=
      fun μ => TorusMetric.exists_coe_eq_abs_eq_norm _
    choose b hb hb' using hz
    refine ⟨b, funext hb, fun μ => abs_le.1 ?_⟩
    rw [hb' μ]
    have h := AddCircle.norm_le_half_period (p := s.side)
      (x := (z : TorusMetric.Torus4 s.side) μ) hside.ne'
    rwa [abs_of_pos hside] at h
  have lengthAtMost : ∀ z : torus.Carrier s, ModelSpace.norm s torus z ≤ s.side := by
    intro z
    obtain ⟨v, hv, hcube⟩ := lifts z
    obtain ⟨-, -, -, hle, -, -⟩ := (hproj s).2 torus
    have hv' : ModelSpace.proj s torus v = z := hv
    rw [← hv']
    refine (hle v).trans ?_
    unfold TorusMetric.euclidNormVec
    refine Real.sqrt_le_iff.2 ⟨hside.le, ?_⟩
    have hsq : ∀ μ, v μ ^ 2 ≤ (s.side / 2) ^ 2 := fun μ =>
      sq_le_sq' (hcube μ).1 (hcube μ).2
    calc ∑ μ, v μ ^ 2 ≤ ∑ _μ : Fin 4, (s.side / 2) ^ 2 := Finset.sum_le_sum fun μ _ => hsq μ
      _ = s.side ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  have wholeBall : ∀ (x : torus.Carrier s) (R : ℝ), s.side ≤ R →
      ModelSpace.closedBall s torus x R = univ := by
    intro x R hR
    exact eq_univ_of_forall fun y => (lengthAtMost (y - x)).trans hR
  refine ⟨fun Y => ⟨fun x R _ => ballCompact Y x R, fun S hS => ?_⟩, lifts, lengthAtMost, ?_,
    wholeBall⟩
  · obtain ⟨N, hN⟩ := compactBounded Y S hS
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    refine ⟨⟨(N : ℝ) + 1, hpos, ?_⟩, ModelSpace.basePoint s Y, (N : ℝ) + 1, hpos, fun y hy => ?_⟩
    · rw [ModelSpace.ballAtBase_ofReal s Y hpos]
      exact hN
    · show ModelSpace.norm s Y (y - ModelSpace.basePoint s Y) ≤ (N : ℝ) + 1
      have e : y - ModelSpace.basePoint s Y = y := sub_zero y
      rw [e]
      exact (hN y hy).le
  · rw [← wholeBall (ModelSpace.basePoint s torus) s.side le_rfl]
    exact ballCompact torus _ _
end CompactBallsAndTorus
end YangMills.Construction.LatticeLimits
end
