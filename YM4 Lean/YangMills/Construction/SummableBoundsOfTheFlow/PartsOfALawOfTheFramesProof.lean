import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative TorusComparison FamilyNorms
namespace TorusFreezing
namespace LocalDecomposition
section DerivativeBounds
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private structure DerivBoundsOn (U : Set (BondField ι)) (θ : BondField ι → ℝ)
    (A : BondField ι → ι → ℝ) (B : ι → ι → ℝ) : Prop where
  contDiff : ∀ η ∈ U, ContDiffAt ℝ 2 θ η
  firstDeriv_le : ∀ η ∈ U, ∀ (b : ι) (e : BondVector), ‖e‖ = 1 → |bondPartialDeriv θ b η e| ≤ A η b
  secondDeriv_le : ∀ η ∈ U, ∀ (b b' : ι) (e e' : BondVector), ‖e‖ = 1 → ‖e'‖ = 1 →
    |secondDerivAlong θ η (bondVariation b e) (bondVariation b' e')| ≤ B b b'
omit [DecidableEq ι] in
private theorem differentiableAt_of_contDiffAt_two {θ : BondField ι → ℝ} {η : BondField ι}
    (h : ContDiffAt ℝ 2 θ η) : DifferentiableAt ℝ θ η :=
  h.differentiableAt (by norm_num)
omit [DecidableEq ι] in
private theorem differentiableAt_fderiv_of_contDiffAt_two {θ : BondField ι → ℝ} {η : BondField ι}
    (h : ContDiffAt ℝ 2 θ η) : DifferentiableAt ℝ (fderiv ℝ θ) η :=
  (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
omit [DecidableEq ι] in
private theorem secondDerivAlong_eq_fderiv_fderiv {θ : BondField ι → ℝ} {η : BondField ι}
    (h : ContDiffAt ℝ 2 θ η) (u v : BondField ι) :
    secondDerivAlong θ η u v = fderiv ℝ (fderiv ℝ θ) η v u := by
  unfold secondDerivAlong
  have h1 := differentiableAt_fderiv_of_contDiffAt_two h
  have := (h1.hasFDerivAt.clm_apply (hasFDerivAt_const u η)).fderiv
  rw [this]
  simp
private theorem DerivBoundsOn.add {U : Set (BondField ι)} {f g : BondField ι → ℝ}
    {A A' : BondField ι → ι → ℝ} {B B' : ι → ι → ℝ} (hf : DerivBoundsOn U f A B)
    (hg : DerivBoundsOn U g A' B') :
    DerivBoundsOn U (fun η => f η + g η) (fun η b => A η b + A' η b)
      (fun b b' => B b b' + B' b b') := by
  refine ⟨fun η hη => (hf.contDiff η hη).add (hg.contDiff η hη), fun η hη b e he => ?_,
    fun η hη b b' e e' he he' => ?_⟩
  · have h1 := differentiableAt_of_contDiffAt_two (hf.contDiff η hη)
    have h2 := differentiableAt_of_contDiffAt_two (hg.contDiff η hη)
    have : bondPartialDeriv (fun η => f η + g η) b η e =
        bondPartialDeriv f b η e + bondPartialDeriv g b η e := by
      unfold bondPartialDeriv
      rw [fderiv_fun_add h1 h2]
      rfl
    rw [this]
    exact (abs_add_le _ _).trans
      (add_le_add (hf.firstDeriv_le η hη b e he) (hg.firstDeriv_le η hη b e he))
  · have sf := hf.contDiff η hη
    have sg := hg.contDiff η hη
    have hev : fderiv ℝ (fun ζ => f ζ + g ζ) =ᶠ[𝓝 η] fun ζ => fderiv ℝ f ζ + fderiv ℝ g ζ := by
      filter_upwards [sf.eventually (by simp), sg.eventually (by simp)] with ζ a c
      exact fderiv_fun_add (differentiableAt_of_contDiffAt_two a) (differentiableAt_of_contDiffAt_two c)
    have : secondDerivAlong (fun η => f η + g η) η (bondVariation b e) (bondVariation b' e') =
        secondDerivAlong f η (bondVariation b e) (bondVariation b' e') +
          secondDerivAlong g η (bondVariation b e) (bondVariation b' e') := by
      rw [secondDerivAlong_eq_fderiv_fderiv (sf.add sg), secondDerivAlong_eq_fderiv_fderiv sf,
        secondDerivAlong_eq_fderiv_fderiv sg, hev.fderiv_eq,
        fderiv_fun_add (differentiableAt_fderiv_of_contDiffAt_two sf)
          (differentiableAt_fderiv_of_contDiffAt_two sg)]
      rfl
    rw [this]
    exact (abs_add_le _ _).trans
      (add_le_add (hf.secondDeriv_le η hη b b' e e' he he') (hg.secondDeriv_le η hη b b' e e' he he'))
private theorem DerivBoundsOn.const_mul {U : Set (BondField ι)} {f : BondField ι → ℝ}
    {A : BondField ι → ι → ℝ} {B : ι → ι → ℝ} (a : ℝ) (hf : DerivBoundsOn U f A B) :
    DerivBoundsOn U (fun η => a * f η) (fun η b => |a| * A η b) (fun b b' => |a| * B b b') := by
  refine ⟨fun η hη => contDiffAt_const.mul (hf.contDiff η hη), fun η hη b e he => ?_,
    fun η hη b b' e e' he he' => ?_⟩
  · have h1 := differentiableAt_of_contDiffAt_two (hf.contDiff η hη)
    have : bondPartialDeriv (fun η => a * f η) b η e = a * bondPartialDeriv f b η e := by
      unfold bondPartialDeriv
      rw [fderiv_const_mul h1]
      rfl
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.firstDeriv_le η hη b e he) (abs_nonneg a)
  · have sf := hf.contDiff η hη
    have hev : fderiv ℝ (fun ζ => a * f ζ) =ᶠ[𝓝 η] fun ζ => a • fderiv ℝ f ζ := by
      filter_upwards [sf.eventually (by simp)] with ζ c
      exact fderiv_const_mul (differentiableAt_of_contDiffAt_two c) a
    have : secondDerivAlong (fun η => a * f η) η (bondVariation b e) (bondVariation b' e') =
        a * secondDerivAlong f η (bondVariation b e) (bondVariation b' e') := by
      have h2 : fderiv ℝ (fun ζ => a • fderiv ℝ f ζ) η = a • fderiv ℝ (fderiv ℝ f) η :=
        ((differentiableAt_fderiv_of_contDiffAt_two sf).hasFDerivAt.const_smul a).fderiv
      rw [secondDerivAlong_eq_fderiv_fderiv (contDiffAt_const.mul sf),
        secondDerivAlong_eq_fderiv_fderiv sf, hev.fderiv_eq, h2]
      rfl
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.secondDeriv_le η hη b b' e e' he he') (abs_nonneg a)
private theorem DerivBoundsOn.zero (U : Set (BondField ι)) :
    DerivBoundsOn U (fun _ => (0 : ℝ)) (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun η _ => contDiffAt_const, fun η _ b e _ => ?_, fun η _ b b' e e' _ _ => ?_⟩
  · simp [bondPartialDeriv]
  · simp [secondDerivAlong]
private theorem DerivBoundsOn.sum {κ : Type} {U : Set (BondField ι)} (S : Finset κ)
    {f : κ → BondField ι → ℝ} {A : κ → BondField ι → ι → ℝ} {B : κ → ι → ι → ℝ}
    (h : ∀ y ∈ S, DerivBoundsOn U (f y) (A y) (B y)) :
    DerivBoundsOn U (fun η => ∑ y ∈ S, f y η) (fun η b => ∑ y ∈ S, A y η b)
      (fun b b' => ∑ y ∈ S, B y b b') := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using DerivBoundsOn.zero U
  | insert y S hy ih =>
    have h1 := (h y (Finset.mem_insert_self y S)).add
      (ih fun y' hy' => h y' (Finset.mem_insert_of_mem hy'))
    simpa only [Finset.sum_insert hy] using h1
omit [Fintype ι] in
private theorem bondVariation_smul (b : ι) (t : ℝ) (e : BondVector) :
    bondVariation b (t • e) = t • bondVariation b e := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.bondVariation_smul <;> assumption
omit [Fintype ι] in
private theorem bondVariation_zero (b : ι) : bondVariation b (0 : BondVector) = 0 := by
  unfold bondVariation
  exact Pi.single_zero b
private theorem isLocalTermAt_of_derivBounds {P : Type} {ρ r c x : ℝ} {pos : ι → P} {D : P → P → ℝ}
    {z : P} {θ : BondField ι → ℝ} {A : BondField ι → ι → ℝ} {B : ι → ι → ℝ}
    (h : DerivBoundsOn (openPolyball ι ρ) θ A B) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hA : ∀ η ∈ openPolyball ι ρ, ∀ b, A η b ≤
      c * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) z)))
    (hB : ∀ b b', B b b' ≤ c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z)))) :
    IsLocalTermAt ρ r c x pos D z θ := by
  refine ⟨fun η hη => (h.contDiff η hη).contDiffWithinAt, fun η hη b => ?_,
    fun η hη b b' e e' => ?_⟩
  · unfold bondGradNorm
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun e he => ?_
    exact (h.firstDeriv_le η hη b e he).trans (hA η hη b)
  · set R := c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z))) with hR
    have s := h.contDiff η hη
    by_cases he : e = 0
    · subst he
      rw [bondVariation_zero, secondDerivAlong_eq_fderiv_fderiv s, map_zero]
      simp
    by_cases he' : e' = 0
    · subst he'
      rw [bondVariation_zero, secondDerivAlong_eq_fderiv_fderiv s, map_zero]
      simp
    have n1 : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
    have n2 : ‖e'‖ ≠ 0 := norm_ne_zero_iff.mpr he'
    have u1 : ‖(‖e‖⁻¹ • e)‖ = 1 := norm_smul_inv_norm he
    have u2 : ‖(‖e'‖⁻¹ • e')‖ = 1 := norm_smul_inv_norm he'
    have hb := (h.secondDeriv_le η hη b b' _ _ u1 u2).trans (hB b b')
    have e1 : e = ‖e‖ • (‖e‖⁻¹ • e) := by rw [smul_smul, mul_inv_cancel₀ n1, one_smul]
    have e2 : e' = ‖e'‖ • (‖e'‖⁻¹ • e') := by rw [smul_smul, mul_inv_cancel₀ n2, one_smul]
    have key : secondDerivAlong θ η (bondVariation b e) (bondVariation b' e') =
        ‖e‖ * ‖e'‖ * secondDerivAlong θ η (bondVariation b (‖e‖⁻¹ • e))
          (bondVariation b' (‖e'‖⁻¹ • e')) := by
      have a1 : bondVariation b e = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by
        rw [← bondVariation_smul, ← e1]
      have a2 : bondVariation b' e' = ‖e'‖ • bondVariation b' (‖e'‖⁻¹ • e') := by
        rw [← bondVariation_smul, ← e2]
      rw [secondDerivAlong_eq_fderiv_fderiv s, secondDerivAlong_eq_fderiv_fderiv s, a1, a2]
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      ring
    rw [key, abs_mul, abs_of_nonneg (by positivity)]
    calc ‖e‖ * ‖e'‖ * _ ≤ ‖e‖ * ‖e'‖ * R := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = R * ‖e‖ * ‖e'‖ := by ring
private theorem derivBoundsOn_weightedSq (U : Set (BondField ι)) (w : ι → ℝ) (hw : ∀ b, 0 ≤ w b) :
    DerivBoundsOn U (fun η => ∑ b, w b * ‖η b‖ ^ 2) (fun η b => 2 * w b * ‖η b‖)
      (fun b b' => if b = b' then 2 * w b else 0) := by
  have hd : ∀ η : BondField ι, HasFDerivAt (fun η : BondField ι => ∑ b, w b * ‖η b‖ ^ 2)
      (∑ b, (2 * w b) • (innerSL ℝ (η b)).comp
        (ContinuousLinearMap.proj b : BondField ι →L[ℝ] BondVector)) η := by
    intro η
    refine HasFDerivAt.fun_sum fun b _ => ?_
    have h1 : HasFDerivAt (fun η : BondField ι => η b)
        (ContinuousLinearMap.proj b : BondField ι →L[ℝ] BondVector) η :=
      (ContinuousLinearMap.proj b : BondField ι →L[ℝ] BondVector).hasFDerivAt
    have h2 := (h1.norm_sq).const_mul (w b)
    refine h2.congr_fderiv ?_
    ext v
    simp
    ring
  have hval : ∀ (η : BondField ι) (b : ι) (e : BondVector),
      fderiv ℝ (fun η : BondField ι => ∑ b, w b * ‖η b‖ ^ 2) η (bondVariation b e) =
        2 * w b * inner ℝ (η b) e := by
    intro η b e
    rw [(hd η).fderiv, _root_.sum_apply, Finset.sum_eq_single b]
    · simp [bondVariation]
    · intro b' _ hb
      simp [bondVariation, Pi.single_eq_of_ne hb]
    · simp
  refine ⟨fun η _ => ?_, fun η _ b e he => ?_, fun η _ b b' e e' he he' => ?_⟩
  · refine ContDiff.contDiffAt ?_
    refine ContDiff.sum fun b _ => contDiff_const.mul ?_
    exact (contDiff_apply ℝ BondVector b).norm_sq ℝ
  · unfold bondPartialDeriv
    rw [hval, abs_mul, abs_of_nonneg (by have := hw b; positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by have := hw b; positivity)
    simpa [he] using abs_real_inner_le_norm (η b) e
  · have hf : (fun ζ : BondField ι =>
        fderiv ℝ (fun η : BondField ι => ∑ b, w b * ‖η b‖ ^ 2) ζ (bondVariation b e)) =
        fun ζ => ((2 * w b) • (innerSL ℝ e).comp
          (ContinuousLinearMap.proj b : BondField ι →L[ℝ] BondVector)) ζ := by
      funext ζ
      rw [hval]
      simp [real_inner_comm]
    unfold secondDerivAlong
    rw [hf, ContinuousLinearMap.fderiv]
    by_cases hbb : b = b'
    · subst hbb
      simp only [if_true, _root_.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, bondVariation, Pi.single_eq_same, innerSL_apply_apply,
        smul_eq_mul]
      have h1 : |inner ℝ e e'| ≤ 1 := by
        simpa [he, he'] using abs_real_inner_le_norm e e'
      have h2 : 0 ≤ 2 * w b := by have := hw b; positivity
      rw [abs_mul, abs_of_nonneg h2]
      nlinarith [abs_nonneg (inner ℝ e e')]
    · have : (bondVariation b' e' : BondField ι) b = 0 := by
        simp [bondVariation, Pi.single_eq_of_ne hbb]
      simp [if_neg hbb, this]
private theorem sum_integral_fderiv_along_ray {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : BondField ι × P → ℝ) (η : BondField ι)
    (h : ∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (v • η, 0)) :
    ∑ b, ∫ v in (0 : ℝ)..1, fderiv ℝ f (v • η, 0) (Pi.single b (η b), 0) = f (η, 0) - f (0, 0) := by
  have hcurve : ∀ v : ℝ, HasDerivAt (fun v : ℝ => ((v • η, 0) : BondField ι × P)) (η, 0) v :=
    fun v => by
      have h1 : HasDerivAt (fun v : ℝ => v • η) η v := by
        simpa using (hasDerivAt_id v).smul_const η
      exact h1.prodMk (hasDerivAt_const v (0 : P))
  have hcont : ContinuousOn (fun v : ℝ => fderiv ℝ f (v • η, 0)) (Set.Icc 0 1) := by
    intro v hv
    have h1 : ContinuousAt (fderiv ℝ f) (v • η, 0) :=
      ((h v hv).fderiv_right (m := 0) (by norm_num)).continuousAt
    have h2 : ContinuousAt (fun v : ℝ => ((v • η, 0) : BondField ι × P)) v := (hcurve v).continuousAt
    exact (ContinuousAt.comp (f := fun v : ℝ => ((v • η, 0) : BondField ι × P)) (x := v)
      (g := fderiv ℝ f) h1 h2).continuousWithinAt
  have hint : ∀ w : BondField ι × P,
      IntervalIntegrable (fun v : ℝ => fderiv ℝ f (v • η, 0) w) MeasureTheory.volume 0 1 := fun w => by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact hcont.clm_apply continuousOn_const
  rw [← intervalIntegral.integral_finsetSum fun b _ => hint _]
  have hsumv : ∀ v : ℝ, ∑ b, fderiv ℝ f (v • η, 0) (Pi.single b (η b), 0) =
      fderiv ℝ f (v • η, 0) (η, 0) := by
    intro v
    rw [← map_sum]
    congr 1
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact Finset.univ_sum_single η
    · rw [Prod.snd_sum]
      simp
  simp only [hsumv]
  have hd : ∀ v ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => f (v • η, 0)) (fderiv ℝ f (v • η, 0) (η, 0)) v := fun v hv => by
    rw [Set.uIcc_of_le zero_le_one] at hv
    exact ((h v hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt v (hcurve v)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint (η, 0))
  simpa using this
end DerivativeBounds
private theorem sum_filter_fibres {α β : Type} [Fintype β] (S : Finset α) (g : α → β) (T : α → ℝ)
    (inst : ∀ Y, DecidablePred fun a => g a = Y) :
    ∑ Y, ∑ a ∈ @Finset.filter _ (fun a => g a = Y) (inst Y) S, T a = ∑ a ∈ S, T a := by
  classical
  rw [← Finset.sum_fiberwise S g T]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp
section Frames
variable {F : BlockFrame}
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
private theorem leftTranslate_bondSpread_empty {j : ℕ} (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) (τ : Fin 0 → ℝ) (V : F.GaugeField j) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V = V := by
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, expUnit_zero]
private theorem bondDeriv_empty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p3568 <;> assumption
private theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem cellSupDist_le_bondSpanWithCell (Y z : F.Cell) (c : Fin 0 → F.Site F.top × Fin 4) :
    cellSupDist z Y ≤ bondSpanWithCell Y z c := by
  rw [cellSupDist_comm]
  unfold bondSpanWithCell bondSpan
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun l : Fin (0 + 1) =>
    siteSupDist Y ((Fin.cons (z, 0) c : Fin (0 + 1) → F.Site F.top × Fin 4) l).1) (Finset.mem_univ 0)
private theorem contDiffAt_of_rotatedEval_empty {n : WithTop ℕ∞}
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions)
    (h1 : ContDiffAt ℝ n (rotatedEval G V c X) (η, 0)) : ContDiffAt ℝ n (fun ζ => G ζ V) η := by
  have h2 : ContDiffAt ℝ n (fun ζ : StepVariable (finiteCells F) => (ζ, (0 : Fin 0 → ℝ))) η :=
    contDiffAt_id.prodMk contDiffAt_const
  have h3 := ContDiffAt.comp η h1 h2
  have e : (rotatedEval G V c X ∘ fun ζ : StepVariable (finiteCells F) => (ζ, (0 : Fin 0 → ℝ))) =
      fun ζ => G ζ V := by
    funext ζ
    simp [rotatedEval, leftTranslate_bondSpread_empty]
  rwa [e] at h3
private def bondListMap {ι : Type} [Fintype ι] [DecidableEq ι] {l : ℕ} (b : Fin l → ι)
    (u : Fin l → BondVector) : (Fin l → ℝ) →L[ℝ] BondField ι :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) (b i)).comp
    ((ContinuousLinearMap.proj i : (Fin l → ℝ) →L[ℝ] ℝ).smulRight (u i))
private theorem jointMixedDeriv_eq_iteratedFDeriv (hS : SmoothSlices.IteratedFDerivSlices)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions)
    (h : ContDiffAt ℝ (l : WithTop ℕ∞) (fun ζ => G ζ V) η) :
    jointMixedDeriv G η V b u c X =
      iteratedFDeriv ℝ l (fun ζ => G ζ V) η (fun i => Pi.single (b i) (u i)) := by apply _root_.YangMills.DeltaSharedProofs.p502184 <;> assumption
private theorem exp_diameter_le {κ D₁ : ℝ} {S : ℕ} (hκ : 0 < κ) (h : D₁ ≤ S) :
    Real.exp (-(2 ^ 7 * κ * S)) ≤ Real.exp (-(2 ^ 5 * κ * D₁)) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : 2 ^ 5 * κ * D₁ ≤ 2 ^ 5 * κ * S := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 ^ 5 * κ * (S : ℝ) ≤ 2 ^ 7 * κ * S := by
    have : 0 ≤ κ * S := by positivity
    nlinarith
  linarith
private theorem derivBoundsOn_interpolatedExpansion
    (hRead : IteratedDerivative.rotatedEvalContDiffOfDisplacements)
    (hS : SmoothSlices.IteratedFDerivSlices)
    {s a ρA κ δ C ρ D : ℝ} {Ck : ℕ → ℝ} {L m : ℕ} {e : ℕ → ℝ} {f : LocalFamily} {V : F.GaugeField F.top}
    (y : F.Site F.depth) (hκ : 0 < κ) (hD : 0 ≤ D) (h1 : C * runningMax e 1 ≤ D)
    (h2 : C * runningMax e 2 ≤ D)
    (tr : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      IsTransportBounded s a ρA κ δ C Ck L m 3 e f V η) :
    DerivBoundsOn (openPolyball _ ρ) (fun ζ => interpolatedExpansion s a ρA m f y ζ V)
      (fun _ b => D * Real.exp (-(2 ^ 5 * κ * realCellDist (bondCell b) (enclosingCell y))))
      (fun b b' => D * Real.exp (-(2 ^ 5 * κ *
        max (realCellDist (bondCell b) (enclosingCell y))
          (realCellDist (bondCell b') (enclosingCell y))))) := by
  have hX0 : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  have sm : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun ζ => interpolatedExpansion s a ρA m f y ζ V) η :=
    fun η hη =>
      contDiffAt_of_rotatedEval_empty _ V η Fin.elim0 Fin.elim0
        (hRead F V _ η 0 Fin.elim0 Fin.elim0 3 fun l b u hu =>
          (tr η hη).smooth y l 0 b u Fin.elim0 Fin.elim0 hu hX0)
  have pt : ∀ η ∈ openPolyball (↥(chordBonds (finiteCells F))) ρ, ∀ b, ‖η b‖ ≤ ρ :=
    fun η hη b => (hη b).le
  refine ⟨fun η hη => (sm η (pt η hη)).of_le (by norm_num), fun η hη b u hu => ?_,
    fun η hη b b' u u' hu hu' => ?_⟩
  · have gr := (tr η (pt η hη)).jointDeriv_le y 1 0 (fun _ => b) (fun _ => u) Fin.elim0 Fin.elim0
      (by norm_num) (by norm_num) (fun _ => hu) hX0
    rw [jointMixedDeriv_eq_iteratedFDeriv hS _ η V _ _ Fin.elim0 Fin.elim0
      ((sm η (pt η hη)).of_le (by norm_num)), iteratedFDeriv_one_apply] at gr
    have hd : realCellDist (bondCell b) (enclosingCell y) ≤
        (cellSetDiameter (insert (enclosingCell y) (chordBondCells (fun _ : Fin 1 => b) ∪
          topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) : ℕ) := by
      unfold realCellDist bondCell
      exact_mod_cast cellSupDist_le_diameter (by simp [chordBondCells]) (Finset.mem_insert_self _ _)
    exact gr.trans (mul_le_mul h1 (exp_diameter_le hκ hd) (Real.exp_pos _).le hD)
  · have gr := (tr η (pt η hη)).jointDeriv_le y 2 0 ![b', b] ![u', u] Fin.elim0 Fin.elim0
      (by norm_num) (by norm_num) (fun i => by fin_cases i <;> simpa) hX0
    have s2 : ContDiffAt ℝ 2 (fun ζ => interpolatedExpansion s a ρA m f y ζ V) η :=
      (sm η (pt η hη)).of_le (by norm_num)
    rw [jointMixedDeriv_eq_iteratedFDeriv hS _ η V _ _ Fin.elim0 Fin.elim0
      ((sm η (pt η hη)).of_le (by norm_num)), iteratedFDeriv_two_apply] at gr
    have hd : max (realCellDist (bondCell b) (enclosingCell y))
        (realCellDist (bondCell b') (enclosingCell y)) ≤
        (cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b', b] ∪
          topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) : ℕ) := by
      have hy := Finset.mem_insert_self (enclosingCell y) (chordBondCells ![b', b] ∪
        topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))
      refine max_le ?_ ?_
      · unfold realCellDist bondCell
        have h0 := cellSupDist_le_diameter (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩))) hy
        exact_mod_cast h0
      · unfold realCellDist bondCell
        have h0 := cellSupDist_le_diameter (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩))) hy
        exact_mod_cast h0
    rw [secondDerivAlong_eq_fderiv_fderiv s2]
    exact gr.trans (mul_le_mul h2 (exp_diameter_le hκ hd) (Real.exp_pos _).le hD)
private theorem derivBoundsOn_interpolatedBlockExponent {s a ρA ρ x κ C : ℝ} {m : ℕ}
    {V : F.GaugeField F.top} (Z : F.Cell)
    (hκ : 0 < κ) (hx : 0 ≤ x) (hC : 0 ≤ C) (hB : InterpolatedExponentBounds s a ρA ρ x κ C m V)
    (hP : ∀ η ∈ openPolyball (↥(chordBonds (finiteCells F))) ρ,
      ContDiffAt ℝ 2 (interpolatedBlockExponent s a ρA x m Z V) η) :
    DerivBoundsOn (openPolyball _ ρ) (interpolatedBlockExponent s a ρA x m Z V)
      (fun η b => C * (x * Real.sqrt (weightedSqNormNear κ bondCell realCellDist Z η) + 1) *
        Real.exp (-(2 ^ 5 * κ * realCellDist (bondCell b) Z)))
      (fun b b' => C * x * Real.exp (-(2 ^ 5 * κ *
        max (realCellDist (bondCell b) Z) (realCellDist (bondCell b') Z)))) := by
  have hX0 : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  have hk : (0 : ℝ) ≤ 2 ^ 5 * κ := by positivity
  refine ⟨fun η hη => ?_, fun η hη b e he => ?_, fun η hη b b' e e' he he' => ?_⟩
  · exact hP η hη
  · have h1 := hB.deriv_top_partial Z η b e 0 Fin.elim0 Fin.elim0 hη (by norm_num) hX0 he
    rw [bondDeriv_empty] at h1
    refine h1.trans ?_
    have hsq : localSqNorm κ Z η ≤ weightedSqNormNear κ bondCell realCellDist Z η := by
      unfold localSqNorm weightedSqNormNear
      refine Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
      have hd : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Z := Nat.cast_nonneg _
      have : 0 ≤ κ * (cellSupDist (enclosingCell b.1.1) Z : ℝ) := by positivity
      show -(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Z : ℝ)) ≤
        -(2 ^ 5 * κ * (cellSupDist (enclosingCell b.1.1) Z : ℝ))
      nlinarith
    have hexp : Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Z (enclosingCell b.1.1) Fin.elim0)) ≤
        Real.exp (-(2 ^ 5 * κ * realCellDist (bondCell b) Z)) := by
      refine Real.exp_le_exp.mpr ?_
      have h2 : (cellSupDist (enclosingCell b.1.1) Z : ℝ) ≤
          bondSpanWithCell Z (enclosingCell b.1.1) Fin.elim0 := by
        exact_mod_cast cellSupDist_le_bondSpanWithCell Z (enclosingCell b.1.1) Fin.elim0
      have h3 : (0 : ℝ) ≤ bondSpanWithCell Z (enclosingCell b.1.1)
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) := Nat.cast_nonneg _
      have h4 : 2 ^ 5 * κ * (cellSupDist (enclosingCell b.1.1) Z : ℝ) ≤
          2 ^ 5 * κ * bondSpanWithCell Z (enclosingCell b.1.1) Fin.elim0 :=
        mul_le_mul_of_nonneg_left h2 hk
      have h5 : 0 ≤ κ * (bondSpanWithCell Z (enclosingCell b.1.1)
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ) := by
        positivity
      show -(2 ^ 6 * κ * (bondSpanWithCell Z (enclosingCell b.1.1)
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ)) ≤
        -(2 ^ 5 * κ * (cellSupDist (enclosingCell b.1.1) Z : ℝ))
      nlinarith
    have hw : x * Real.sqrt (localSqNorm κ Z η) + 1 ≤
        x * Real.sqrt (weightedSqNormNear κ bondCell realCellDist Z η) + 1 := by
      have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hx
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw hC) hexp (Real.exp_pos _).le
      (mul_nonneg hC (by positivity))
  · refine (hB.second_deriv Z η b b' e e' hη he he').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h1 : max (realCellDist (bondCell b) Z) (realCellDist (bondCell b') Z) ≤
        ((max (cellSupDist Z (enclosingCell b.1.1)) (max (cellSupDist Z (enclosingCell b'.1.1))
          (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) : ℕ) : ℝ) := by
      refine max_le ?_ ?_
      · unfold realCellDist bondCell
        rw [cellSupDist_comm]
        exact_mod_cast le_max_left _ _
      · unfold realCellDist bondCell
        rw [cellSupDist_comm]
        exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
    have h2 : (0 : ℝ) ≤ ((max (cellSupDist Z (enclosingCell b.1.1))
        (max (cellSupDist Z (enclosingCell b'.1.1))
        (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1))) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 := mul_le_mul_of_nonneg_left h1 hk
    have h4 := mul_nonneg hκ.le h2
    nlinarith
private theorem interpolatedExponent_eq_sum_cells (hER : Interpolation.cellExponentRotatedEvalStatement)
    (hAl : IteratedDerivative.JointMixedDerivEqDerivAlong) [Fintype F.Cell] {s a ρA ρ x κ κ₂ rE : ℝ}
    {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ} {V : F.GaugeField F.top}
    (hne : Nonempty ↥(chordBonds (finiteCells F)))
    (hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      HasInterpolationKernels s a ρA κ κ₂ rE x m K D V η)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < ρ) :
    interpolatedExponent s a ρA x m V η = ∑ Y, interpolatedBlockExponent s a ρA x m Y V η := by
  classical
  have hX0 : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  obtain ⟨f, hf⟩ : ∃ f, f = rotatedEval (interpolatedEnergy s a ρA m) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) :=
    ⟨_, rfl⟩
  have hsm : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞) f (v • η, 0) := by
    intro v hv n
    have hv' : ∀ b, ‖(v • η) b‖ ≤ ρ := fun b => by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hv.1]
      have h1 := hη b
      have h2 := norm_nonneg (η b)
      nlinarith [hv.2]
    rw [hf]
    exact (hAl F V _ (v • η) 0 Fin.elim0 Fin.elim0).1 hne (fun l b u hl hu =>
      ((hker _ hv').energy l 0 b u Fin.elim0 Fin.elim0 hl hu hX0).1) n
  have hrow : ∀ Y : F.Cell, interpolatedBlockExponent s a ρA x m Y V η =
      x * rayGradientSum f (cellChordBonds Y) (η, 0) -
        (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess a x (interpolatedField s a ρA m V η) c) -
        ∑ b ∈ cellChordBonds Y, haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
    intro Y
    have h := (hER.1 F s a ρA x m Y V η 0 Fin.elim0 Fin.elim0 fun v hv => by
      rw [← hf]
      exact hsm v hv 1).self_of_nhds
    rw [← hf] at h
    simp only [rotatedEval, leftTranslate_bondSpread_empty, contourHaarGap,
      interpolatedHaarLogRatio] at h
    exact h
  have g1 : ∑ Y : F.Cell, rayGradientSum f (cellChordBonds Y) (η, 0) = f (η, 0) - f (0, 0) := by
    rw [← sum_integral_fderiv_along_ray f η fun v hv => by exact_mod_cast hsm v hv 2]
    unfold rayGradientSum cellChordBonds
    exact sum_filter_fibres _
      (fun b : ↥(chordBonds (finiteCells F)) => (enclosingCell b.1.1 : F.Cell)) _ _
  have g2 : ∑ Y : F.Cell, ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      haarGapExcess a x (interpolatedField s a ρA m V η) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (interpolatedField s a ρA m V η) c :=
    sum_filter_fibres _ (fun c : F.Site F.top × Fin 4 => c.1) _ _
  have g3 : ∑ Y : F.Cell, ∑ b ∈ cellChordBonds Y,
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) =
      ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
    unfold cellChordBonds
    exact sum_filter_fibres _
      (fun b : ↥(chordBonds (finiteCells F)) => (enclosingCell b.1.1 : F.Cell)) _ _
  have e1 : f (η, 0) = chartedEnergy a (interpolatedCoords s a ρA m V η) V := by
    simp [hf, rotatedEval, leftTranslate_bondSpread_empty, interpolatedEnergy]
  have e2 : f (0, 0) = chartedEnergy a (interpolatedCoords s a ρA m V 0) V := by
    simp [hf, rotatedEval, leftTranslate_bondSpread_empty, interpolatedEnergy]
  simp only [hrow, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [g1, g2, g3, e1, e2]
  rfl
private theorem chordBonds_nonempty (hSites : ColdStepAtMirrorFrames.SiteDecomposition)
    (hCh : ColdStepAtMirrorFrames.chartEquivarianceStatement)
    (F : BlockFrame) (a : ℝ) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) :
    Nonempty ↥(chordBonds (finiteCells F)) := by apply _root_.YangMills.Construction.Interpolation.PartsSmooth.chordBonds_nonempty <;> assumption
end Frames
section Parameters
private theorem eventually_of_eventually_two_le {Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop}
    (h : EventuallyInParameters fun T => 2 ≤ T.n₀ → Q T) :
    EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h⟩ := h a ha
  refine ⟨L₀, fun L hL hLo c hc => ?_⟩
  obtain ⟨Ct₀, h⟩ := h L hL hLo c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := h κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₀, h⟩ := h η₃ a1 a2 a3
  refine ⟨N₀, fun k hk => ?_⟩
  obtain ⟨σ₀, hσ₀, h⟩ := h k hk
  refine ⟨σ₀, hσ₀, fun σ b1 b2 p hp => ?_⟩
  obtain ⟨C₀, h⟩ := h σ b1 b2 p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h⟩ := h Cs hCs E hE
  refine ⟨max m₀ 2, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h⟩ := h n₀ ((le_max_left _ _).trans hn₀)
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h⟩ := h CE hCE
  exact ⟨y₀, fun y₁ hy => h y₁ hy ((le_max_right _ _).trans hn₀)⟩
private def ExponentBoundsAt (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ T.Cs (frameRadius x) V
private def ConvexLawsAt (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
    (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
      T.n₀ (frameRadius x) d) →
    HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d
      (convexCombinationExponent T.chainParams.lam x w M)
private theorem hasBoundedDerivatives_of_family {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f := by apply _root_.YangMills.SharedProofs.p1 <;> assumption
private theorem extendByZero_id {F : BlockFrame} (ζ : StepVariable (finiteCells F)) :
    _root_.YangMills.Construction.Interpolation.extendByZero (F := F) (id : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)))
      Finset.univ ζ = ζ := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
private theorem family_term_arith {c W e N D Cs E₃ : ℝ} (hc : c ≤ Cs) (hND : N * D ≤ Cs * E₃)
    (hW : 1 ≤ W) (he : 0 ≤ e) (hCs : 0 ≤ Cs) (hE₃ : 0 ≤ E₃) :
    c * W * e + N * (D * e) ≤ Cs * (1 + E₃) * W * e := by
  have h1 : c * W * e ≤ Cs * W * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by linarith)) he
  have h2 : N * D * e ≤ Cs * E₃ * e := mul_le_mul_of_nonneg_right hND he
  have h3 : Cs * E₃ * e ≤ Cs * E₃ * W * e := by
    have h0 : 0 ≤ Cs * E₃ * e := by positivity
    nlinarith
  linarith
private theorem weight_term_arith {τ c W e P lam Cs : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hW : 1 ≤ W)
    (he : 0 ≤ e) (hc0 : 0 ≤ c) (hP0 : 0 ≤ P) (hP : P ≤ lam * W * e) (hCs : c + lam ≤ Cs) :
    |τ| * (c * W * e) + |1 - τ| * P ≤ Cs * 1 * W * e := by
  rw [abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ)]
  have a1 : τ * (c * W * e) ≤ 1 * (c * W * e) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have a2 : (1 - τ) * P ≤ 1 * P := mul_le_mul_of_nonneg_right (by linarith) hP0
  have a3 : (c + lam) * W * e ≤ Cs * W * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs (by linarith)) he
  linarith
end Parameters
end LocalDecomposition
open LocalDecomposition in
set_option maxHeartbeats 1600000 in
theorem stepLawLocalDecomposition_holds (hJ : SummableBounds.joinAtLoweredSmallnessConstantStatement)
    (hK : Interpolation.interpolationKernelBoundsStatement)
    (hSm : Interpolation.interpolatedBlockExponentSmoothStatement)
    (hER : Interpolation.cellExponentRotatedEvalStatement)
    (hAl : IteratedDerivative.JointMixedDerivEqDerivAlong)
    (hLw : Interpolation.mixturesOfIntermediateLawsConvex)
    (hB : Interpolation.interpolatedExponentBoundsStatement)
    (hT : Interpolation.transportBoundsStatement)
    (hRead : IteratedDerivative.rotatedEvalContDiffOfDisplacements)
    (hS : SmoothSlices.IteratedFDerivSlices)
    (hSites : CellCounting.SitesPerCellLePow) (hBlock : ColdStepAtMirrorFrames.SiteDecomposition)
    (hCh : ColdStepAtMirrorFrames.chartEquivarianceStatement) : stepLawLocalDecomposition := by
  classical
  obtain ⟨Cf, Ckf, hCf, -, hTr⟩ := hT
  obtain ⟨Kf, Df, -, -, hKT⟩ := hK
  have hLw' : EventuallyInParameters ConvexLawsAt := hLw
  have hB' : EventuallyInParameters ExponentBoundsAt := hB
  have J1 : EventuallyInParameters fun T =>
      interpolationKernelBoundsAt T (Kf (rateParameters T)) (Df (rateParameters T)) ∧
      ConvexLawsAt T :=
    hJ _ _ _ (fun _ c => c) hKT hLw' fun T c _ _ _ _ _ _ _ _ _ _ _ _ p r => ⟨p, r⟩
  have J2 : EventuallyInParameters fun T =>
      (interpolationKernelBoundsAt T (Kf (rateParameters T)) (Df (rateParameters T)) ∧
        ConvexLawsAt T) ∧
      TransportBoundsAt T (Cf (rateParameters T)) (Ckf (rateParameters T)) :=
    hJ _ _ _ (fun _ c => c) J1 hTr fun T c _ _ _ _ _ _ _ _ _ _ _ _ p r => ⟨p, r⟩
  refine eventually_of_eventually_two_le ?_
  refine hJ ExponentBoundsAt _ _
    (fun U c => c + (U.L : ℝ) ^ 4 * Cf (rateParameters U) + U.chainParams.lam) hB' J2 ?_
  intro T c hc hodd hn hy hE hη₃ hη₁ hκ hσ hch hcut hGle hBd hJ2 hn2
  have hGle' : c + (T.L : ℝ) ^ 4 * Cf (rateParameters T) + T.chainParams.lam ≤ T.Cs := hGle
  have hP1 : interpolationKernelBoundsAt T (Kf (rateParameters T)) (Df (rateParameters T)) :=
    hJ2.1.1
  have hP2 : ConvexLawsAt T := hJ2.1.2
  have hP4 : TransportBoundsAt T (Cf (rateParameters T)) (Ckf (rateParameters T)) := hJ2.2
  intro t x s l F _ V hx hs hs1 hl hF hV
  have hx1 : 1 ≤ x := hy.trans hx
  have hx0 : 0 ≤ x := by linarith
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have hC0 : 0 < Cf (rateParameters T) := hCf _
  have hL0 : (0 : ℝ) ≤ (T.L : ℝ) ^ 4 := by positivity
  have hc0 : 0 ≤ c := by linarith
  have hCs0 : 0 ≤ T.Cs := by
    have := mul_nonneg hL0 hC0.le
    linarith
  have hcCs : c ≤ T.Cs := by
    have := mul_nonneg hL0 hC0.le
    linarith
  have hE₃ : T.E ≤ T.energyRatio := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hη₃]
    nlinarith
  have hE₃0 : 0 ≤ T.energyRatio := by linarith
  obtain ⟨hFL, hFt, n, hside, hn'⟩ := id hF
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    exact hn2.trans hn'
  have hoddF : Odd F.blockSide := by
    rw [hFL]
    exact hodd
  have hmem : ∀ Y : F.Cell, Y ∈ finiteCells F := fun Y => by
    unfold finiteCells
    rw [dif_pos (Finite.of_fintype _)]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) Y
  have hne := chordBonds_nonempty hBlock hCh F T.a hoddF hs2
  have hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels s T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        (Kf (rateParameters T)) (Df (rateParameters T)) V η :=
    fun η hη => hP1 x t F V s η hx hF hV hs hs1 hη
  have hX0 : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  have hpart : ∀ (z : F.Cell), ∀ η ∈ openPolyball (↥(chordBonds (finiteCells F))) T.ballRadius,
      ContDiffAt ℝ 2 (interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) z V) η :=
    fun z η hη =>
      contDiffAt_of_rotatedEval_empty
        (fun ζ V' => interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) z V' ζ)
        V η Fin.elim0 Fin.elim0
        (hSm F s T.a T.chainParams.ρA T.ballRadius x T.κ T.chainParams.κ₂ T.chainParams.δ₂ (frameRadius x) _ _ V z η 0
          Fin.elim0 Fin.elim0 hne hker (fun b => (hη b).le) hX0)
  have hsumE := interpolatedExponent_eq_sum_cells hER hAl hne hker
  have hbd : InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ c (frameRadius x) V :=
    hBd t x hx F V s hF hV hs hs1
  have hψ := fun z : F.Cell => derivBoundsOn_interpolatedBlockExponent z hκ hx0 hc0 hbd (hpart z)
  have good : ∀ Φ : StepVariable (finiteCells F) → ℝ,
      IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
        (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Φ →
      ∃ Ψ : StepVariable (finiteCells F) → ℝ, (∀ η ∈ openPolyball _ T.ballRadius, Ψ η = Φ η) ∧
        IsAdmissiblePotential T.ballRadius (x * T.chainParams.lam / 4) T.κ
          (fun b b' => realCellDist (bondCell b) (bondCell b')) Ψ := by
    intro Φ hΦ
    have hAdm : (⟨F, V, id, Finset.univ, Φ⟩ :
        LawOnBondVariables ↥(chordBonds (finiteCells F))).IsAdmissible
        T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀ (frameRadius x)
        (fun b b' => realCellDist (bondCell b) (bondCell b')) :=
      ⟨hF, hV, hΦ, Function.injective_id, fun _ _ => rfl⟩
    have hw : IsConvexWeights (fun _ : Fin 1 => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩
    obtain ⟨Ψ, K, hΨ, hconv, hsl, -⟩ := hP2 t x hx ↥(chordBonds (finiteCells F))
      (fun b b' => realCellDist (bondCell b) (bondCell b')) 1 (fun _ => 1) (fun _ => _) hw
      (fun _ => hAdm)
    refine ⟨Ψ, fun η hη => (hΨ η hη).trans ?_, ⟨K, hconv, hsl⟩⟩
    simp only [convexCombinationExponent, LawOnBondVariables.exponent, frozenExponent, extendByZero_id]
    simp
  cases l with
  | ofFamily φ =>
    have hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ := hl
    obtain ⟨Ψ, hΨ, hgood⟩ := good _ (IsIntermediateLaw.ofFamily s φ hs hs1 hφ)
    refine ⟨Ψ, hΨ, hgood, fun η hη => ?_, fun z => ?_⟩
    · rw [hΨ η hη]
      show familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V η = _
      simp only [familyLawExponent, stepLawCellPart, Finset.sum_sub_distrib]
      rw [hsumE η hη]
      congr 1
      unfold interpolatedBlockExpansion
      exact (sum_filter_fibres _ (fun y : F.Site F.depth => (enclosingCell y : F.Cell)) _ _).symm
    · set S := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = z) with hS'
      have hE0 : 0 < T.E := by linarith
      have he0 : ∀ j : ℕ, 0 ≤ (fun j : ℕ => if j = 3 then T.energyRatio else T.E) j := fun j => by
        show 0 ≤ if j = 3 then T.energyRatio else T.E
        split_ifs <;> linarith
      have tr := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) =>
        hP4 x t 3 _ φ F V s η hx le_rfl (by norm_num) he0 (hasBoundedDerivatives_of_family hφ)
          hF hV hs hs1 hη
      have l1 : runningMax (fun j : ℕ => if j = 3 then T.energyRatio else T.E) 1 = T.E := by
        simp [runningMax, hE0.le]
      have l2 : runningMax (fun j : ℕ => if j = 3 then T.energyRatio else T.E) 2 = T.E := by
        simp [runningMax, hE0.le]
      have hrow : ∀ y ∈ S, DerivBoundsOn (openPolyball _ T.ballRadius)
          (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y ζ V)
          (fun _ b => Cf (rateParameters T) * T.E *
            Real.exp (-(2 ^ 5 * T.κ * realCellDist (bondCell b) z)))
          (fun b b' => Cf (rateParameters T) * T.E * Real.exp (-(2 ^ 5 * T.κ *
            max (realCellDist (bondCell b) z) (realCellDist (bondCell b') z)))) := by
        intro y hy'
        have hz : enclosingCell y = z := (Finset.mem_filter.mp hy').2
        have := derivBoundsOn_interpolatedExpansion hRead hS (D := Cf (rateParameters T) * T.E) y hκ
          (by positivity) (by rw [l1]) (by rw [l2]) tr
        rwa [hz] at this
      have hθ := (hψ z).add ((DerivBoundsOn.sum S hrow).const_mul (-1))
      have heq : stepLawCellPart (StepLaw.ofFamily φ) s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
          V z =
          fun η => interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) z V η +
            -1 * ∑ y ∈ S, interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y η V := by
        funext η
        have e1 : interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) φ z η V =
            ∑ y ∈ S, interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y η V := by
          unfold interpolatedBlockExpansion
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext y
          simp [hS']
        show _ - interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) φ z η V = _
        rw [e1]
        ring
      have hcard : (S.card : ℝ) ≤ (T.L : ℝ) ^ 4 := by
        have h1 := hSites F (finiteCells F) hoddF hs2 z
        have h2 : S.card = (Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) =>
            enclosingCell y.1 = z).card := by
          rw [hS', ← Finset.card_map (Function.Embedding.subtype _)]
          congr 1
          ext y
          simp [and_comm]
        rw [h2, ← hFL]
        exact_mod_cast h1
      have hND : (S.card : ℝ) * (Cf (rateParameters T) * T.E) ≤ T.Cs * T.energyRatio := by
        have h1 : (S.card : ℝ) * Cf (rateParameters T) ≤ T.Cs := by
          have h2 := mul_le_mul_of_nonneg_right hcard hC0.le
          linarith
        calc (S.card : ℝ) * (Cf (rateParameters T) * T.E)
            = (S.card : ℝ) * Cf (rateParameters T) * T.E := by ring
          _ ≤ T.Cs * T.E := mul_le_mul_of_nonneg_right h1 hE0.le
          _ ≤ T.Cs * T.energyRatio := mul_le_mul_of_nonneg_left hE₃ hCs0
      rw [heq]
      show IsLocalTermAt T.ballRadius T.κ (T.Cs * (1 + T.energyRatio)) x bondCell realCellDist z _
      refine isLocalTermAt_of_derivBounds hθ (by positivity) hx0 (fun η hη b => ?_) (fun b b' => ?_)
      · simp only [abs_neg, abs_one, one_mul, Finset.sum_const, nsmul_eq_mul]
        have hW : 1 ≤ x * Real.sqrt (weightedSqNormNear T.κ bondCell realCellDist z η) + 1 := by
          have := mul_nonneg hx0 (Real.sqrt_nonneg (weightedSqNormNear T.κ bondCell realCellDist z η))
          linarith
        have := family_term_arith (e := Real.exp (-(2 ^ 5 * T.κ * realCellDist (bondCell b) z)))
          hcCs hND hW (Real.exp_pos _).le hCs0 hE₃0
        exact this
      · simp only [abs_neg, abs_one, one_mul, Finset.sum_const, nsmul_eq_mul]
        exact family_term_arith hcCs hND hx1 (Real.exp_pos _).le hCs0 hE₃0
  | ofWeight τ =>
    obtain ⟨hτ0, hτ1⟩ : 0 ≤ τ ∧ τ ≤ 1 := hl
    obtain ⟨Ψ, hΨ, hgood⟩ := good _ (IsIntermediateLaw.ofWeight s τ hs hs1 hτ0 hτ1)
    refine ⟨Ψ, hΨ, hgood, fun η hη => ?_, fun z => ?_⟩
    · rw [hΨ η hη]
      show weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V η = _
      simp only [weightLawExponent, stepLawCellPart, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsumE η hη]
      congr 2
      unfold totalQuadratic cellQuadratic
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp
    · set w : ↥(chordBonds (finiteCells F)) → ℝ :=
        fun b => if enclosingCell b.1.1 = z then x * T.chainParams.lam / 2 else 0 with hwdef
      have hw0 : ∀ b, 0 ≤ w b := fun b => by
        simp only [hwdef]
        split_ifs
        · positivity
        · exact le_rfl
      have hq := derivBoundsOn_weightedSq (openPolyball _ T.ballRadius) w hw0
      have hθ := ((hψ z).const_mul τ).add (hq.const_mul (1 - τ))
      have heq : stepLawCellPart (StepLaw.ofWeight τ) s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
          V z =
          fun η => τ * interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) z V η +
            (1 - τ) * ∑ b, w b * ‖η b‖ ^ 2 := by
        funext η
        show _ + (1 - τ) * cellQuadratic T.chainParams.lam x z η = _
        congr 2
        unfold cellQuadratic
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hwdef]
        split_ifs <;> simp
      have hzero : realCellDist z z = 0 := by
        unfold realCellDist
        rw [cellSupDist_self]
        simp
      rw [heq]
      show IsLocalTermAt T.ballRadius T.κ (T.Cs * 1) x bondCell realCellDist z _
      have hcl : c + T.chainParams.lam ≤ T.Cs := by
        have := mul_nonneg hL0 hC0.le
        linarith
      refine isLocalTermAt_of_derivBounds hθ (by positivity) hx0 (fun η hη b => ?_) (fun b b' => ?_)
      · have hW : 1 ≤ x * Real.sqrt (weightedSqNormNear T.κ bondCell realCellDist z η) + 1 := by
          have := mul_nonneg hx0 (Real.sqrt_nonneg (weightedSqNormNear T.κ bondCell realCellDist z η))
          linarith
        refine weight_term_arith hτ0 hτ1 hW (Real.exp_pos _).le hc0
          (by have := hw0 b; positivity) ?_ hcl
        by_cases hb : enclosingCell b.1.1 = z
        · have hd : realCellDist (bondCell b) z = 0 := by
            show realCellDist (enclosingCell b.1.1) z = 0
            rw [hb, hzero]
          have hwb : w b = x * T.chainParams.lam / 2 := by simp [hwdef, hb]
          have h1 : ‖η b‖ ≤ Real.sqrt (weightedSqNormNear T.κ bondCell realCellDist z η) := by
            refine Real.le_sqrt_of_sq_le ?_
            unfold weightedSqNormNear
            have := Finset.single_le_sum (f := fun b : ↥(chordBonds (finiteCells F)) =>
              Real.exp (-(2 ^ 5 * T.κ * realCellDist (bondCell b) z)) * ‖η b‖ ^ 2)
              (fun i _ => by positivity) (Finset.mem_univ b)
            simpa [hd] using this
          rw [hd, hwb]
          simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
          have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hx0 hlam.le)
          nlinarith [mul_nonneg hlam.le (zero_le_one : (0 : ℝ) ≤ 1)]
        · have hwb : w b = 0 := by simp [hwdef, hb]
          rw [hwb]
          simp only [mul_zero, zero_mul]
          have := Real.exp_pos (-(2 ^ 5 * T.κ * realCellDist (bondCell b) z))
          have hq' := mul_nonneg (mul_nonneg hlam.le (by linarith : (0 : ℝ) ≤
            x * Real.sqrt (weightedSqNormNear T.κ bondCell realCellDist z η) + 1)) this.le
          exact hq'
      · refine weight_term_arith hτ0 hτ1 hx1 (Real.exp_pos _).le hc0 ?_ ?_ hcl
        · split_ifs
          · have := hw0 b
            positivity
          · exact le_rfl
        · split_ifs with hbb
          · subst hbb
            by_cases hb : enclosingCell b.1.1 = z
            · have hd : realCellDist (bondCell b) z = 0 := by
                show realCellDist (enclosingCell b.1.1) z = 0
                rw [hb, hzero]
              have hwb : w b = x * T.chainParams.lam / 2 := by simp [hwdef, hb]
              rw [hd, hwb]
              simp only [max_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
              nlinarith
            · have hwb : w b = 0 := by simp [hwdef, hb]
              rw [hwb]
              simp only [mul_zero]
              positivity
          · positivity
end TorusFreezing
end YangMills.Construction
end
