import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.CriticalCompositesTendToOne
import YangMills.Construction.Towers.HessianAlongTheBackgroundShift
import YangMills.Construction.Towers.HessianOnTheFibreAndGaugeDirections
import YangMills.Construction.Towers.PropertiesOfTheCovariantAverages
import YangMills.Construction.Towers.SecondDerivativeOfARealAnalyticFunctionIsBilinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.BackgroundShiftHessian
theorem linearMapWithValues_coe_apply {α β : Type*} {p : Submodule ℝ (α → Matrices.ComplexMatrix2)}
    {p' : Submodule ℝ (β → Matrices.ComplexMatrix2)} {f : (α → Matrices.ComplexMatrix2) → β → Matrices.ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → Matrices.ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → Matrices.ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem quadratic_add_expand {V : Type*} [Add V] (q : V → V → ℝ) {B d : V}
    (sym : q B d = q d B) (symd : q (B + d) d = q d (B + d)) (symB : q (B + d) B = q B (B + d))
    (add₁ : q (B + d) B = q B B + q d B) (add₂ : q (B + d) d = q B d + q d d)
    (add₃ : q (B + d) (B + d) = q B (B + d) + q d (B + d)) :
    q (B + d) (B + d) = q B B + 2 * q B d + q d d := by
  rw [add₃, ← symB, ← symd, add₁, add₂, ← sym]
  ring
end Tower.BackgroundShiftHessian
theorem Tower.hessianAlongBackgroundShift_holds
    (h1 : FibreHessianAndGaugeDirections)
    (h2 : CovariantSmoothingProperties.Statement)
    (h3 : RealQuadraticTransposes.Statement)
    (h4 : RealLinearMaps.RealLinearMapsStatement)
    (h5 : AsDifferentials.CovariantMeansAreDerivatives)
    (h6 : ChosenProlongCompTendsto)
    (h7 : LeftSecondDerivBilinear)
    (h8 : WilsonActionAnalytic) :
    HessianAlongBackgroundShift := by
  intro L n k hL hn hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hstep, htower⟩ := h4 L n (i + 1) hL hn hk
  have hat := hstep i (Nat.lt_succ_self i)
  have hrel := (((h2 L hL).1 n (i + 1) hn).2 (i + 1) le_rfl).1
  have hnear := (((h1 L n (i + 1) hL hn hk).1.and
    ((h3 L n (i + 1) hL hn hk).2.and
      ((((h5 L hL (i + 1) hk).1 n hn).2.2).and
        (hat.iterCovariantDeriv_isLinear.and
          hat.iterContourLogDrift_isLinear)))).and
    (self_mem_nhdsWithin :
      fieldSpace L n (i + 1) 0 ∈
        nhdsWithin (trivialField L n (i + 1) 0) (fieldSpace L n (i + 1) 0)))
  have hW := (h6 L n (i + 1) (i + 1) hL hn le_rfl).eventually hnear
  refine Filter.Eventually.mono (hW.and (h1 L n (i + 1) hL hn hk).2) ?_
  rintro W ⟨⟨⟨hgauge, ⟨-, -, hop⟩, ⟨hsm, -⟩, ⟨Tq, hTq⟩, ⟨Tn, hTn⟩⟩, hUc⟩, hii, -⟩
  intro J μ hJ hμ B hB
  rw [← chainBottom_eq W] at hgauge hop hsm hTq hTn hUc hJ hB ⊢
  obtain ⟨r, hr, hrT⟩ := htower.exists_restriction
  obtain ⟨σ, hσ⟩ := hop.gaugeParameter_linear
  obtain ⟨TD, hTD⟩ := htower.covDiff_isLinear 0 (Nat.zero_le _) _ hUc
  obtain ⟨s, hs, hsx⟩ : ∃ s : vertexFunctionSpace L n (i + 1) 0,
      (s : Vertex L n (i + 1) 0 → Matrices.ComplexMatrix2) = backgroundGaugeParameter (chainBottom W) B ∧
      (s : Vertex L n (i + 1) 0 → Matrices.ComplexMatrix2) = RealLinearMaps.extendByZero
        (iterContourLogDrift L n (i + 1) (chainBottom W) (i + 1) B) :=
    ⟨σ B, (hσ B).2, (hσ B).1⟩
  obtain ⟨d, hd⟩ : ∃ d : edgeFormSpace L n (i + 1) 0,
      (d : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) = covDiff (chainBottom W) s := ⟨TD s, hTD s⟩
  have hτ : backgroundShift L n (i + 1) (chainBottom W) B = B + d := by
    apply Subtype.ext
    rw [hop.backgroundShift_apply, Submodule.coe_add, hd, hs]
  have hrs : restrictVertexFunction (i + 1) (s : Vertex L n (i + 1) 0 → Matrices.ComplexMatrix2) =
      iterContourLogDrift L n (i + 1) (chainBottom W) (i + 1) B := by
    have e : (s : (pairedFunctions (Vertex L n (i + 1) 0)).realSubmodule) =
        PairedFunctionSpace.realTransposeMap r (Tn B) := by
      apply Subtype.ext
      refine hsx.trans (Eq.trans ?_ (hrT.transpose_eq_extendByZero (Tn B)).symm)
      rw [← hTn B]
    have e' := hrT.comp_transpose (Tn B)
    rw [← e] at e'
    refine Eq.trans (hr s).symm (Eq.trans (congrArg Subtype.val e') ?_)
    exact hTn B
  have hB0 : Tq B = 0 := by
    apply Subtype.ext
    have e := BackgroundShiftHessian.linearMapWithValues_coe_apply
      (p := edgeFormSpace L n (i + 1) 0) (p' := edgeFormSpace L n (i + 1) (i + 1))
      (f := iterCovariantDeriv L n (i + 1) (chainBottom W) (i + 1)) ⟨Tq, hTq⟩ B
    have e' : iterCovariantDeriv L n (i + 1) (chainBottom W) (i + 1) B = 0 := by
      rw [← e]
      exact congrArg Subtype.val hB
    rw [hTq, e']
    rfl
  obtain ⟨R1, R2, -⟩ := hrel (chainBottom W) hsm
  have hsl : ∀ x, (s : Vertex L n (i + 1) 0 → Matrices.ComplexMatrix2) x ∈ Matrices.ComplexMatrix2.traceless := fun x =>
    (Submodule.mem_pi.1 s.2 x (Set.mem_univ _)).2
  obtain ⟨Ra, Rb⟩ := R2 s hsl
  have hkill : IsInCovariantIterKernel W (backgroundShift L n (i + 1) (chainBottom W) B) := by
    have hc : ∀ x : edgeFormSpace L n (i + 1) 0, (x : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) ∈
        complexEdgeForms L n (i + 1) 0 := fun x => ⟨fun b hb => (x.2.1 b hb).2, x.2.2⟩
    have e := R1 _ (hc (B + d))
    have a1 : iterCovariantDeriv L n (i + 1) (chainBottom W) (i + 1)
        ((B + d : edgeFormSpace L n (i + 1) 0) : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) =
        iterCovariantDeriv L n (i + 1) (chainBottom W) (i + 1) d := by
      rw [← hTq, ← hTq, map_add, hB0, zero_add]
    have a4 : iterContourLogDrift L n (i + 1) (chainBottom W) (i + 1)
        ((B + d : edgeFormSpace L n (i + 1) 0) : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) =
        iterContourLogDrift L n (i + 1) (chainBottom W) (i + 1) B +
          iterContourLogDrift L n (i + 1) (chainBottom W) (i + 1) d := by
      rw [← hTn, ← hTn, ← hTn, map_add]
      rfl
    rw [a1, hd, Rb, Ra, ← hd, a4, hrs] at e
    rw [IsInCovariantIterKernel, hτ]
    exact right_eq_add.1 e
  obtain ⟨hmem, hH⟩ := hii _ hkill
  refine ⟨hmem, ?_⟩
  have hH' := congrArg Complex.re hH
  rw [Complex.ofReal_re, Complex.sub_re, Complex.ofReal_re, ← hμ] at hH'
  rw [hH']
  obtain ⟨hsym, hlin⟩ := h7 L n (i + 1) 0 hL hn (Nat.zero_le _) _ _ (h8 L n (i + 1) hL hn) _ hUc
  have hadd : ∀ x y z : edgeFormSpace L n (i + 1) 0,
      leftSecondDeriv (plaquetteAction L n (i + 1)) (chainBottom W)
          ((x + y : edgeFormSpace L n (i + 1) 0) : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) z =
        leftSecondDeriv (plaquetteAction L n (i + 1)) (chainBottom W) x z +
          leftSecondDeriv (plaquetteAction L n (i + 1)) (chainBottom W) y z := by
    intro x y z
    have e := hlin x x.2 y y.2 z z.2 1
    rw [one_smul, one_mul] at e
    exact e
  have hexp := BackgroundShiftHessian.quadratic_add_expand
    (fun x y : edgeFormSpace L n (i + 1) 0 => leftSecondDeriv (plaquetteAction L n (i + 1)) (chainBottom W)
      (x : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) y) (B := B) (d := d)
    (hsym _ B.2 _ d.2) (hsym _ (B + d).2 _ d.2) (hsym _ (B + d).2 _ B.2)
    (hadd B d B) (hadd B d d) (hadd B d (B + d))
  have e1 := congrArg Complex.re (hgauge B B.2 s s.2)
  have e2 := congrArg Complex.re (hgauge d d.2 s s.2)
  rw [Complex.ofReal_re, ← hd, hs, ← hJ] at e1 e2
  have hd' : (d : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) =
      covDiff (chainBottom W) (backgroundGaugeParameter (chainBottom W) B) := by
    rw [hd, hs]
  unfold sourceQuadraticForm
  rw [← hd', ← e1, ← e2, hτ]
  rw [hexp]
  ring
end YangMills.Construction
end
