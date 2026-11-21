import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.SixteenPointsOnASmallTorus.ArrayMeanIsTheMeanOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAreCurvaturesOfTheirWeights
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open ClusterExpansionOfAStep RenormalizationStepParameters WeightedResponses ResponseInTheExpansion TestFunctions TorusFields
private theorem int_eq_of_dvd_sub_of_bounds {c x y : ℤ} (hx : 0 ≤ x ∧ x < c) (hy : 0 ≤ y ∧ y < c) (h : c ∣ x - y) : x = y := by
  have := Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨by omega, by omega⟩)
  omega
private theorem dvd_self_sub_emod (x c : ℤ) : c ∣ x - x % c := ⟨x / c, by rw [Int.emod_def]; ring⟩
private theorem signedConj_ofReal (s : ℤˣ) (x : ℝ) : Conventions.signedConj s (x : ℂ) = (x : ℂ) := by
  unfold Conventions.signedConj
  split_ifs
  · rfl
  · exact Complex.conj_ofReal x
abbrev _root_.YangMills.SharedProofs.p21399 := @signedConj_ofReal
private theorem prod_indexBox_eq_prod_residues {c : ℕ} [NeZero c] (origin : Fin 4 → ℤ) (n : ChessboardTori.EvenIndexVector)
    (hcoord : ∀ μ, n.coord μ = (c : ℤ)) (G : (Fin 4 → ℤ) → ℂ) (H : (Fin 4 → Fin c) → ℂ)
    (hGH : ∀ k ∈ n.indexBox, ∀ k' : Fin 4 → Fin c, (∀ μ, (c : ℤ) ∣ k μ - origin μ - ((k' μ : ℕ) : ℤ)) → G k = H k') :
    ∏ k ∈ n.indexBox, G k = ∏ k', H k' := by
  have hc : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hbd : ∀ x : ℤ, 0 ≤ x % c ∧ x % c < c := fun x => ⟨Int.emod_nonneg _ hc.ne', Int.emod_lt_of_pos _ hc⟩
  let φ : (Fin 4 → ℤ) → (Fin 4 → Fin c) := fun k μ =>
    ⟨((k μ - origin μ) % c).toNat, by
      have := hbd (k μ - origin μ)
      generalize (k μ - origin μ) % (c : ℤ) = r at this
      omega⟩
  have hφ : ∀ k μ, (((φ k μ : Fin c) : ℕ) : ℤ) = (k μ - origin μ) % c := fun k μ =>
    Int.toNat_of_nonneg (hbd _).1
  have hmem : ∀ k, k ∈ n.indexBox ↔ ∀ μ, 0 ≤ k μ ∧ k μ < c := by
    intro k
    simp [ChessboardTori.EvenIndexVector.indexBox, Fintype.mem_piFinset, hcoord]
  refine Finset.prod_bij (fun k _ => φ k) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k₁ h₁ k₂ h₂ he
    funext μ
    have h3 : (k₁ μ - origin μ) % c = (k₂ μ - origin μ) % c := by
      rw [← hφ, ← hφ, he]
    have h4 : (c : ℤ) ∣ k₁ μ - k₂ μ := by
      have h5 := dvd_self_sub_emod (k₁ μ - origin μ) c
      have h6 := dvd_self_sub_emod (k₂ μ - origin μ) c
      rw [h3] at h5
      have h7 := dvd_sub h5 h6
      simpa using h7
    exact int_eq_of_dvd_sub_of_bounds ((hmem k₁).mp h₁ μ) ((hmem k₂).mp h₂ μ) h4
  · intro k' _
    refine ⟨fun μ => (((k' μ : ℕ) : ℤ) + origin μ) % c, (hmem _).mpr fun μ => hbd _, ?_⟩
    funext μ
    apply Fin.ext
    have h1 : (((k' μ : ℕ) : ℤ)) < c := by exact_mod_cast (k' μ).2
    have h2 : (0 : ℤ) ≤ ((k' μ : ℕ) : ℤ) := by positivity
    have h3 := dvd_self_sub_emod (((k' μ : ℕ) : ℤ) + origin μ) c
    have h4 := dvd_self_sub_emod ((((k' μ : ℕ) : ℤ) + origin μ) % c - origin μ) c
    have h5 : ((((((((k' μ : ℕ) : ℤ) + origin μ) % c - origin μ) % c).toNat : ℕ)) : ℤ) = ((k' μ : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (hbd _).1]
      refine int_eq_of_dvd_sub_of_bounds (hbd _) ⟨h2, h1⟩ ?_
      have h6 := dvd_add h3 h4
      obtain ⟨t, ht⟩ := h6
      exact ⟨-t, by linarith⟩
    exact show (((((k' μ : ℕ) : ℤ) + origin μ) % c - origin μ) % c).toNat = (k' μ : ℕ) from by exact_mod_cast h5
  · intro k hk
    refine hGH k hk (φ k) fun μ => ?_
    rw [hφ]
    exact dvd_self_sub_emod _ _
theorem tiledMeanEqReflectedMean (hK : reflectedCopiesAsCurvatureStatement) :
    tiledMeanEqReflectedMeanStatement := by
  intro L _ D c κ j h e z hDL hκ hsup hz
  obtain ⟨Ψ, hmp, hact, hcop⟩ := hK L D c κ j h (recentredAt c h) z hDL hκ hsup (fun x => rfl) hz
  have hcoord : ∀ μ, (ReflectedCopies.cubicCounts D j).coord μ = ((twoCellSide L j 0 : ℕ) : ℤ) := by
    intro μ
    show 2 * (D.L : ℤ) ^ j = _
    rw [hDL]
    simp [twoCellSide]
  have hcurv : ∀ w : PlaquetteWeight (twoCellSide L j 0 * L ^ κ), Continuous (curvatureObservable w) := fun w => by
    unfold curvatureObservable
    exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_plaquetteEnergy p.1 p.2.1 p.2.2)
  have hf : Continuous fun W : TorusField (twoCellSide L j 0 * L ^ κ) => ∏ k : Fin 4 → Fin (twoCellSide L j 0),
      (curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z (fun μ => (k μ : ℕ)) (recentredAt c h)) W - e) :=
    continuous_finsetProd _ fun k _ => (hcurv _).sub continuous_const
  have hw : Continuous fun W : TorusField (twoCellSide L j 0 * L ^ κ) => Real.exp (-D.β * wilsonAction Finset.univ W) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))
  have key : ∀ G : TorusField (twoCellSide L j 0 * L ^ κ) → ℝ, Continuous G →
      ∫ U, G (Ψ U) ∂(ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).haarMeasure =
        ∫ W, G W ∂(fieldHaar (twoCellSide L j 0 * L ^ κ)) := by
    intro G hG
    have h1 := integral_map (μ := (ReflectedCopies.gridPeriods c.grid
      (ReflectedCopies.cubicCounts D j)).haarMeasure) hmp.measurable.aemeasurable
      (f := G) (by rw [hmp.map_eq]; exact hG.measurable.aestronglyMeasurable)
    rw [hmp.map_eq] at h1
    exact h1.symm
  have hprod : ∀ U, ∏ k ∈ (ReflectedCopies.cubicCounts D j).indexBox,
      c.grid.transportTo c.cell (c.grid.cell k) (ReflectedCopies.centredSmeared D h e)
        ((ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).liftGaugeField U) =
      ((∏ k : Fin 4 → Fin (twoCellSide L j 0),
        (curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z (fun μ => (k μ : ℕ)) (recentredAt c h)) (Ψ U) - e) : ℝ) : ℂ) := by
    intro U
    rw [Complex.ofReal_prod]
    refine prod_indexBox_eq_prod_residues c.index _ hcoord _ _ fun k _ k' hk => ?_
    have h1 := (hcop U).2 k (fun μ => (k' μ : ℕ)) hk
    have h2 : c.grid.transportTo c.cell (c.grid.cell k) (ReflectionsAndOneInsertion.complexSmeared D h)
        ((ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).liftGaugeField U) =
        ((InfiniteLattice.smearedEnergy h
          ((c.grid.toLatticeSym (c.grid.mover c.cell (c.grid.cell k))).pullbackField
            ((ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).liftGaugeField U)) : ℝ) : ℂ) :=
      signedConj_ofReal _ _
    have h3 := h2.symm.trans h1
    show Conventions.signedConj _ (((InfiniteLattice.smearedEnergy h
      ((c.grid.toLatticeSym (c.grid.mover c.cell (c.grid.cell k))).pullbackField
        ((ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).liftGaugeField U)) : ℝ) : ℂ) -
        (e : ℂ)) = _
    rw [← Complex.ofReal_sub, signedConj_ofReal, Complex.ofReal_sub, h3, Complex.ofReal_sub]
  have hZ : ReflectedCopies.torusPartition c.grid (ReflectedCopies.cubicCounts D j) =
      ∫ W, Real.exp (-D.β * wilsonAction Finset.univ W) ∂(fieldHaar (twoCellSide L j 0 * L ^ κ)) := by
    unfold ReflectedCopies.torusPartition
    simp only [hact]
    exact key _ hw
  have hnum : ReflectedCopies.tiledIntegral c.grid (ReflectedCopies.cubicCounts D j) c.cell
      (ReflectedCopies.centredSmeared D h e) =
      ((∫ W, (∏ k : Fin 4 → Fin (twoCellSide L j 0),
        (curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z (fun μ => (k μ : ℕ)) (recentredAt c h)) W - e)) *
          Real.exp (-D.β * wilsonAction Finset.univ W) ∂(fieldHaar (twoCellSide L j 0 * L ^ κ)) : ℝ) : ℂ) := by
    have h1 := key (fun W => (∏ k : Fin 4 → Fin (twoCellSide L j 0),
      (curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z (fun μ => (k μ : ℕ)) (recentredAt c h)) W - e)) *
        Real.exp (-D.β * wilsonAction Finset.univ W)) (hf.mul hw)
    refine Eq.trans ?_ (integral_complex_ofReal.trans (congrArg Complex.ofReal h1))
    unfold ReflectedCopies.tiledIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show _ * _ = _
    rw [hprod U, hact U]
    push_cast
    rfl
  have hmean : reflectedProductMean D.β D.mesh (L ^ κ) (twoCellSide L j 0) z (recentredAt c h) e =
      (∫ W, (∏ k : Fin 4 → Fin (twoCellSide L j 0),
        (curvatureObservable (reflectedWeightAbout D.mesh (L ^ κ) z (fun μ => (k μ : ℕ)) (recentredAt c h)) W - e)) *
          Real.exp (-D.β * wilsonAction Finset.univ W) ∂(fieldHaar (twoCellSide L j 0 * L ^ κ))) /
        ∫ W, Real.exp (-D.β * wilsonAction Finset.univ W) ∂(fieldHaar (twoCellSide L j 0 * L ^ κ)) := by
    have hZ0 : 0 ≤ ∫ W, Real.exp (-D.β * wilsonAction Finset.univ W) ∂(fieldHaar (twoCellSide L j 0 * L ^ κ)) :=
      integral_nonneg fun W => (Real.exp_pos _).le
    unfold reflectedProductMean wilsonLaw
    rw [integral_withDensity_eq_integral_toReal_smul
      (hw.measurable.div_const _).ennreal_ofReal
      (Filter.Eventually.of_forall fun W => ENNReal.ofReal_lt_top), ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    show _ • _ = _
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ0), smul_eq_mul]
    ring
  show ReflectedCopies.tiledIntegral _ _ _ _ / _ = _
  rw [hnum, hZ, hmean, Complex.ofReal_div]
end YangMills.Construction.SmallTorusCopies
end
