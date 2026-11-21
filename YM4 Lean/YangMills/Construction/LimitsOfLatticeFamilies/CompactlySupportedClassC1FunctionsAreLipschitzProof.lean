import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Continuum.NeighbourhoodsAdmissibleFamiliesAndMembersOfTheClassesProof
import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLift
import YangMills.Construction.LimitsOfLatticeFamilies.ClosedBallsAndTheTorusAreCompact
import YangMills.Construction.LimitsOfLatticeFamilies.CompactlySupportedClassC1FunctionsAreLipschitz
import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.LimitsOfLatticeFamilies.ProjectionKernelsAndShortestLifts
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace TorusMetric
namespace LipschitzOfC1
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem abs_inner_le_mul_euclidNormVec (v w : Fin 4 → ℝ) :
    |∑ i, v i * w i| ≤ euclidNormVec v * euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.abs_inner_le_euclidNormVec_mul <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
def closedCube (c : Fin 4 → ℝ) (R : ℝ) : Set (Fin 4 → ℝ) :=
  Icc (fun i => c i - R) (fun i => c i + R)
theorem isCompact_closedCube (c : Fin 4 → ℝ) (R : ℝ) : IsCompact (closedCube c R) := isCompact_Icc
theorem mem_closedCube_of_le {a c : Fin 4 → ℝ} {R : ℝ} (h : euclidNormVec (a - c) ≤ R) :
    a ∈ closedCube c R := by
  have hi : ∀ i, |a i - c i| ≤ R := fun i => (abs_apply_le_euclidNormVec (a - c) i).trans h
  refine ⟨fun i => ?_, fun i => ?_⟩
  · change c i - R ≤ a i
    linarith [(abs_le.1 (hi i)).1]
  · change a i ≤ c i + R
    linarith [(abs_le.1 (hi i)).2]
variable {F : (Fin 4 → ℝ) → ℝ}
theorem hasDerivAt_comp_line (hF : ContDiff ℝ 1 F) (p v : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => F (p + u • v)) (fderiv ℝ F (p + t • v) v) t := by apply _root_.YangMills.Construction.TorusTransport.SupportFacts.hasDerivAt_comp_line <;> assumption
theorem gradR4_apply (hF : ContDiff ℝ 1 F) (p : Fin 4 → ℝ) (i : Fin 4) :
    gradR4 F p i = fderiv ℝ F p (Pi.single i 1) := by
  have h := (hasDerivAt_comp_line hF p (Pi.single i 1) 0).deriv
  simpa [gradR4, TestFunctions.partialDerivR4] using h
theorem fderiv_apply_eq_sum_mul_gradR4 (hF : ContDiff ℝ 1 F) (p v : Fin 4 → ℝ) :
    fderiv ℝ F p v = ∑ i, v i * gradR4 F p i := by
  have hv : ∑ i, v i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, gradR4_apply hF]
theorem continuous_gradR4 (hF : ContDiff ℝ 1 F) : Continuous (gradR4 F) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.continuous_gradR4 <;> assumption
theorem gradR4_eq_zero_of_not_mem_closure {p : Fin 4 → ℝ}
    (hp : p ∉ MetricNotions.closureWrt (fun a b : Fin 4 → ℝ => euclidNormVec (a - b))
      {w | F w ≠ 0}) :
    gradR4 F p = 0 := by
  simp only [MetricNotions.closureWrt, mem_ofPred_eq, not_forall] at hp
  obtain ⟨r, hr, hp⟩ := hp
  funext i
  have hc : Continuous fun t : ℝ => euclidNormVec (p - (p + t • Pi.single i (1 : ℝ))) :=
    continuous_euclidNormVec.comp (by fun_prop)
  have h0 : euclidNormVec (p - (p + (0 : ℝ) • Pi.single i (1 : ℝ))) < r := by
    simpa [euclidNormVec] using hr
  have hev : (fun t : ℝ => F (p + t • Pi.single i (1 : ℝ))) =ᶠ[nhds 0] fun _ => 0 := by
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with t ht
    by_contra hne
    exact hp ⟨_, hne, ht⟩
  simpa [gradR4, TestFunctions.partialDerivR4] using hev.deriv_eq
section ClosedSubsets
variable {X : Type*} {d : X → X → ℝ}
theorem isOpenWrt_compl_closureWrt (htri : ∀ x y w, d x y ≤ d x w + d w y) (Z : Set X) :
    MetricNotions.IsOpenWrt d (MetricNotions.closureWrt d Z)ᶜ := by
  intro x hx
  simp only [MetricNotions.closureWrt, mem_compl_iff, mem_ofPred_eq, not_forall] at hx
  obtain ⟨r, hr, hx⟩ := hx
  refine ⟨r / 2, half_pos hr, fun y hxy hy => ?_⟩
  obtain ⟨w, hw, hyw⟩ := hy (r / 2) (half_pos hr)
  exact hx ⟨w, hw, by linarith [htri x w y]⟩
theorem isCompactWrt_closureWrt (htri : ∀ x y w, d x y ≤ d x w + d w y)
    (huniv : MetricNotions.IsCompactWrt d (univ : Set X)) (Z : Set X) :
    MetricNotions.IsCompactWrt d (MetricNotions.closureWrt d Z) := by
  intro 𝒰 hopen hcover
  set S := MetricNotions.closureWrt d Z with hS
  obtain ⟨𝒱, h𝒱, hfin, hV⟩ := huniv (insert Sᶜ 𝒰)
    (by
      rintro U (rfl | hU)
      · exact isOpenWrt_compl_closureWrt htri Z
      · exact hopen U hU)
    (by
      intro x _
      by_cases hx : x ∈ S
      · obtain ⟨U, hU, hxU⟩ := hcover hx
        exact ⟨U, mem_insert_of_mem _ hU, hxU⟩
      · exact ⟨Sᶜ, mem_insert _ _, hx⟩)
  refine ⟨𝒱 ∩ 𝒰, inter_subset_right, hfin.subset inter_subset_left, fun x hx => ?_⟩
  obtain ⟨U, hU, hxU⟩ := hV (mem_univ x)
  rcases h𝒱 hU with rfl | hU'
  · exact absurd hx hxU
  · exact ⟨U, ⟨hU, hU'⟩, hxU⟩
end ClosedSubsets
theorem exists_bound_grad (hB : CompactBallsAndTorus.Claim)
    (hC : C1ViaLift.Claim) (s : Conventions.StandingParameters) (Y : ModelSpace)
    (f : c1CompactSupp s Y univ) : ∃ C : ℝ, ∀ y, euclidNormVec (grad s Y f.1 y) ≤ C := by
  have hF : ContDiff ℝ 1 (f.1 ∘ proj s Y) := ((hC s Y).1 f.1).1 f.2.1
  have hg := ((hC s Y).2.1 f.1 f.2.1).1
  have hcont : Continuous fun y => euclidNormVec (gradR4 (f.1 ∘ proj s Y) y) :=
    continuous_euclidNormVec.comp (continuous_gradR4 hF)
  have hbd : ∀ Q : Set (Fin 4 → ℝ), IsCompact Q → ∃ C : ℝ, ∀ y ∈ Q,
      euclidNormVec (gradR4 (f.1 ∘ proj s Y) y) ≤ C := by
    intro Q hQ
    obtain ⟨C, hC'⟩ := hQ.bddAbove_image hcont.continuousOn
    exact ⟨C, fun y hy => hC' (mem_image_of_mem _ hy)⟩
  cases Y with
  | torus =>
    obtain ⟨C, hC'⟩ := hbd (Icc (fun _ => -(s.side / 2)) (fun _ => s.side / 2)) isCompact_Icc
    refine ⟨C, fun z => ?_⟩
    obtain ⟨v, hv, hvQ⟩ := (hB s).2.1 z
    have hz : grad s torus f.1 z = gradR4 (f.1 ∘ proj s torus) v := by
      rw [← congrFun hg v]
      exact congrArg _ hv.symm
    rw [hz]
    exact hC' v ⟨fun i => (hvQ i).1, fun i => (hvQ i).2⟩
  | euclidean =>
    obtain ⟨-, c, R, -, hS⟩ := ((hB s).1 euclidean).2 _ f.2.2.1
    obtain ⟨C, hC'⟩ := hbd (closedCube c R) (isCompact_closedCube c R)
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ supportIn s euclidean f.1
    · exact (hC' y (mem_closedCube_of_le (hS hy))).trans (le_max_left _ _)
    · have hz : grad s euclidean f.1 y = 0 := gradR4_eq_zero_of_not_mem_closure hy
      rw [hz]
      simp [euclidNormVec]
theorem abs_sub_le_mul_dist (hP : ProjKernelAndMinimalLifts.Claim)
    (hC : C1ViaLift.Claim) (s : Conventions.StandingParameters) (Y : ModelSpace)
    (f : Y.Carrier s → ℝ) (hf : IsC1 s Y f) (K : ℝ)
    (hK : ∀ y, euclidNormVec (grad s Y f y) ≤ K) (x y : Y.Carrier s) :
    |f x - f y| ≤ K * ModelSpace.dist s Y x y := by
  have hF : ContDiff ℝ 1 (f ∘ proj s Y) := ((hC s Y).1 f).1 hf
  have hg := ((hC s Y).2.1 f hf).1
  obtain ⟨hadd, hsurj, hshort, -⟩ := (hP s).2 Y
  obtain ⟨y', rfl⟩ := hsurj y
  obtain ⟨z, hz, hlen⟩ := hshort (x - proj s Y y')
  set G : (Fin 4 → ℝ) → ℝ := f ∘ proj s Y with hG
  have hbd : ∀ t : ℝ, ‖fderiv ℝ G (y' + t • z) z‖ ≤ K * euclidNormVec z := by
    intro t
    rw [fderiv_apply_eq_sum_mul_gradR4 hF, Real.norm_eq_abs]
    refine (abs_inner_le_mul_euclidNormVec _ _).trans ?_
    have h1 : euclidNormVec (gradR4 G (y' + t • z)) ≤ K := by
      rw [← congrFun hg (y' + t • z)]
      exact hK _
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (euclidNormVec_nonneg z)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (x := (0 : ℝ))
    (y := (1 : ℝ)) (f := fun u : ℝ => G (y' + u • z))
    (f' := fun t => fderiv ℝ G (y' + t • z) z) (C := K * euclidNormVec z)
    (fun t _ => (hasDerivAt_comp_line hF y' z t).hasDerivWithinAt) (fun t _ => hbd t)
    convex_univ (mem_univ _) (mem_univ _)
  have hx : G (y' + z) = f x := by
    have : proj s Y (y' + z) = x := by
      rw [hadd, show proj s Y z = x - proj s Y y' from hz]
      abel
    simp [hG, this]
  simp only [one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one, Real.norm_eq_abs] at hmv
  rw [hx] at hmv
  have hlen' : euclidNormVec z = ModelSpace.dist s Y x (proj s Y y') := hlen
  rw [hlen'] at hmv
  exact hmv
end LipschitzOfC1
open LipschitzOfC1 in
theorem c1CompactSuppIsLipschitz_proof
    (hP : ProjKernelAndMinimalLifts.Claim)
    (hL : InvariantDistFromNorm.Claim)
    (hB : CompactBallsAndTorus.Claim)
    (hC : C1ViaLift.Claim) :
    C1CompactSuppIsLipschitz := by
  have hmain : ∀ (s : Conventions.StandingParameters) (Y : ModelSpace) (f : c1CompactSupp s Y univ),
      gradSup f < ⊤ ∧
      (∀ x y, |f.1 x - f.1 y| ≤ (gradSup f).toReal * ModelSpace.dist s Y x y) ∧
      IsLipschitzReal s Y f.1 ∧
      lipNumber s Y f.1 ≤ (gradSup f).toReal := by
    intro s Y f
    obtain ⟨K, hK⟩ := exists_bound_grad hB hC s Y f
    have hfin : gradSup f < ⊤ :=
      lt_of_le_of_lt (iSup_le fun y => ENNReal.ofReal_le_ofReal (hK y)) ENNReal.ofReal_lt_top
    have hle : ∀ y, euclidNormVec (grad s Y f.1 y) ≤ (gradSup f).toReal := fun y =>
      (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1
        (le_iSup (fun y : Y.Carrier s =>
          ENNReal.ofReal (euclidNormVec (grad s Y f.1 y))) y)
    have hmean := abs_sub_le_mul_dist hP hC s Y f.1 f.2.1 _ hle
    refine ⟨hfin, hmean, ⟨(gradSup f).toReal, ENNReal.toReal_nonneg, fun x y => ?_⟩, ?_⟩
    · simpa [Real.norm_eq_abs] using hmean x y
    · rw [lipNumber_eq_bestLipschitzConstant]
      refine csInf_le ⟨0, fun c hc => hc.1⟩ ⟨ENNReal.toReal_nonneg, fun x y => ?_⟩
      simpa [Real.norm_eq_abs] using hmean x y
  refine ⟨fun s Y => ⟨hmain s Y, fun A g hg => ?_⟩, fun s => ?_⟩
  · exact ⟨(hmain s Y ⟨g, hg.1, hg.2.1, subset_univ _⟩).2.2.1, hg.2.1, hg.2.2⟩
  · have htri := (hL s torus).2.2.2.2.2.1
    have hcpt : ∀ f : (ModelSpace.torus).Carrier s → ℝ,
        IsCompactIn s torus (supportIn s torus f) := fun f =>
      isCompactWrt_closureWrt htri (hB s).2.2.2.1 _
    exact ⟨hcpt, fun f hf => ⟨hf, hcpt f, subset_univ _⟩⟩
end YangMills.Construction.LatticeLimits
end
