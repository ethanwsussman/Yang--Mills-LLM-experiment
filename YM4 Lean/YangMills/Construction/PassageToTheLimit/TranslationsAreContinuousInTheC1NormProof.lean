import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.PassageToTheLimit.TranslationsAreContinuousInTheC1Norm
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.LimitSpaces.Ambient.TranslationC1
open TorusMetric (euclidNormVec)
theorem abs_coord_le_euclidNormVec (w : Fin 4 → ℝ) (i : Fin 4) : |w i| ≤ euclidNormVec w := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem norm_sub_le_lipConst (p : Conventions.StandingParameters) (A : Ambient)
    (hρ : ∀ a b : A.Carrier p, 0 ≤ A.pointDist p a b)
    (g : A.Carrier p → ℝ) (hg : A.IsLip p g) (a b : A.Carrier p) :
    ‖g a - g b‖ ≤ A.lipConst p g * A.pointDist p a b := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.norm_sub_le_lipConst_mul <;> assumption
theorem normC1_translate_sub_le (hyp : AmbientMetric.Claim) (p : Conventions.StandingParameters)
    (A : Ambient) (g : A.c1Compact p) (a b : A.Carrier p) :
    ENNReal.ofReal (A.normC1 p (A.translateFun p a g.1 - A.translateFun p b g.1)) ≤
      max (A.gradSup p g.1 * (A.pointDist p a b).toNNReal)
        (Ambient.gradModulus g (A.pointDist p a b).toNNReal) := by
  obtain ⟨hA, -, hReg, hLin, hTr, -, -⟩ := hyp p A
  obtain ⟨-, hmet, hinvar, -, -⟩ := hA
  have hnn : 0 ≤ A.pointDist p a b := hmet.nonneg a b
  have hmove : ∀ y : A.Carrier p, A.pointDist p (y - a) (y - b) = A.pointDist p a b := by
    intro y
    have hy := hinvar (y - a) (y - b) (a + b - y)
    rw [show y - a + (a + b - y) = b by abel, show y - b + (a + b - y) = a by abel] at hy
    rw [← hy, hmet.symm]
  obtain ⟨ha, hga⟩ := (hTr a).2.2.2 g.1 g.2
  obtain ⟨hb, hgb⟩ := (hTr b).2.2.2 g.1 g.2
  obtain ⟨-, hgr, -, -, -⟩ := hLin _ ha _ hb 1 (-1) g.1 g.2.1
  have hcomb : (fun y => (1 : ℝ) * A.translateFun p a g.1 y + (-1) * A.translateFun p b g.1 y) =
      A.translateFun p a g.1 - A.translateFun p b g.1 := by
    funext y
    simp only [Pi.sub_apply]
    ring
  rw [hcomb] at hgr
  obtain ⟨-, -, -, -, -, -, hLipg, hLipgG, hGfin⟩ := hReg g.1 g.2
  have hLipr : A.lipConst p g.1 ≤ (A.gradSup p g.1).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hGfin.ne).mp hLipgG
  have : Nonempty (A.Carrier p) := ⟨0⟩
  have hunif : TestFunctions.uniformNorm (A.translateFun p a g.1 - A.translateFun p b g.1) ≤
      (A.gradSup p g.1).toReal * A.pointDist p a b := by
    refine ciSup_le fun y => ?_
    have hy := norm_sub_le_lipConst p A hmet.nonneg g.1 hLipg (y - a) (y - b)
    rw [hmove] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right hLipr hnn)
  have hfirst : ENNReal.ofReal (TestFunctions.uniformNorm
        (A.translateFun p a g.1 - A.translateFun p b g.1)) ≤
      A.gradSup p g.1 * ((A.pointDist p a b).toNNReal : ℝ≥0∞) := by
    refine (ENNReal.ofReal_le_ofReal hunif).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hGfin.ne]
    exact le_rfl
  have hgradbd : ∀ y : A.Carrier p,
      ENNReal.ofReal (euclidNormVec (A.grad p (A.translateFun p a g.1 - A.translateFun p b g.1) y)) ≤
        Ambient.gradModulus g (A.pointDist p a b).toNNReal := by
    intro y
    have hy : A.grad p (A.translateFun p a g.1 - A.translateFun p b g.1) y =
        A.grad p g.1 (y - a) - A.grad p g.1 (y - b) := by
      rw [hgr]
      simp only [Pi.add_apply, hga, hgb, one_smul, neg_smul, Pi.neg_apply, sub_eq_add_neg]
    rw [hy]
    unfold Ambient.gradModulus
    refine le_iSup_of_le (y - a) (le_iSup_of_le (y - b) (le_iSup_of_le ?_ le_rfl))
    rw [hmove, Real.coe_toNNReal _ hnn]
  have hsecond : ENNReal.ofReal (⨆ i : Fin 4, TestFunctions.uniformNorm
        (A.partialDeriv p i (A.translateFun p a g.1 - A.translateFun p b g.1))) ≤
      Ambient.gradModulus g (A.pointDist p a b).toNNReal := by
    rcases eq_or_ne (Ambient.gradModulus g (A.pointDist p a b).toNNReal) ⊤ with htop | htop
    · rw [htop]
      exact le_top
    · refine (ENNReal.ofReal_le_iff_le_toReal htop).mpr (ciSup_le fun i => ciSup_le fun y => ?_)
      refine le_trans ?_ ((ENNReal.ofReal_le_iff_le_toReal htop).mp (hgradbd y))
      exact abs_coord_le_euclidNormVec _ i
  unfold Ambient.normC1
  rcases le_total (TestFunctions.uniformNorm (A.translateFun p a g.1 - A.translateFun p b g.1))
    (⨆ i : Fin 4, TestFunctions.uniformNorm
      (A.partialDeriv p i (A.translateFun p a g.1 - A.translateFun p b g.1))) with hcase | hcase
  · rw [max_eq_right hcase]
    exact le_max_of_le_right hsecond
  · rw [max_eq_left hcase]
    exact le_max_of_le_left hfirst
theorem max_le_continuityModulus (K : SharpParameter) {p : Conventions.StandingParameters}
    {A : Ambient} (g : A.c1Compact p) (r : ℝ≥0) :
    max (A.gradSup p g.1 * r) (Ambient.gradModulus g r) ≤ Ambient.continuityModulus K g r := by
  have hK : (1 : ℝ) ≤ 40 * (K : ℝ) := by
    have := Set.mem_Ici.mp K.2
    linarith
  unfold Ambient.continuityModulus
  exact max_le_max le_rfl (le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr hK))
theorem translationContinuousC1Norm_holds (hyp : AmbientMetric.Claim)
    (hmirror : MirrorTranslation.Claim) : Ambient.translationContinuousC1Norm := by
  intro K p A g
  refine ⟨fun a b => ⟨normC1_translate_sub_le hyp p A g a b, max_le_continuityModulus K g _⟩,
    fun ε hε => ?_⟩
  have hlim := (((hmirror p K A 0).2.2.2.2.2.2) g).2
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ≥0), Ambient.continuityModulus K g r < ENNReal.ofReal ε :=
    hlim.eventually_lt_const (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨η, hη, fun a b hab => ?_⟩
  have hnn : 0 ≤ A.pointDist p a b := ((hyp p A).1.2.1).nonneg a b
  have hclose : dist (A.pointDist p a b).toNNReal (0 : ℝ≥0) < η := by
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hnn, NNReal.coe_zero, sub_zero, abs_of_nonneg hnn]
    exact hab
  have hlt := ((normC1_translate_sub_le hyp p A g a b).trans
    (max_le_continuityModulus K g _)).trans_lt (hball hclose)
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hlt
end YangMills.Construction.LimitSpaces.Ambient.TranslationC1
end
