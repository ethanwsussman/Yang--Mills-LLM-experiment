import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import YangMills.Construction.TorusOrFourSpace.TwoNormsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.C1NormComparison
open Kind TorusMetric
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem exists_index_euclidNormVec_le_two_mul (v : Fin 4 → ℝ) :
    ∃ i, euclidNormVec v ≤ 2 * |v i| ∧ |v i| = ⨆ j, |v j| := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun j => |v j|)
  have hi' : |v i| = ⨆ j, |v j| := hi
  refine ⟨i, ?_, hi'⟩
  have hle : ∀ j, |v j| ≤ |v i| := fun j => by
    rw [hi']
    exact le_ciSup (Finite.bddAbove_range fun j => |v j|) j
  have hsq : ∀ j, v j ^ 2 ≤ |v i| ^ 2 := fun j => by
    rw [← sq_abs (v j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hle j) 2
  rw [euclidNormVec, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_four]
  nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_smul (a : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (a • v) = |a| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem ennreal_mul_max_distrib (c a b : ℝ≥0∞) : c * max a b = max (c * a) (c * b) :=
  Monotone.map_max (f := fun t => c * t) fun _ _ h => mul_le_mul' le_rfl h
theorem ennreal_le_two_mul (c : ℝ≥0∞) : c ≤ 2 * c := by
  rw [two_mul]
  exact le_self_add
theorem two_mul_lt_ofReal_of_lt_half {a : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε)
    (h : a < ENNReal.ofReal (ε / 2)) : 2 * a < ENNReal.ofReal ε := by
  have hε' : 0 ≤ ε / 2 := by positivity
  calc 2 * a = a + a := two_mul a
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add h h
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hε' hε']
      congr 1
      ring
variable (D : Params) (E : Kind)
theorem gradNormBetweenPartials_holds (u : E.Pt D → ℝ) (y : E.Pt D) :
    GradNormBetweenPartials D E u y := by
  obtain ⟨i, h₁, h₂⟩ := exists_index_euclidNormVec_le_two_mul (gradVec D E u y)
  constructor
  · exact ciSup_le fun j => abs_apply_le_euclidNormVec (gradVec D E u y) j
  · show euclidNormVec (gradVec D E u y) ≤ 2 * ⨆ j, |gradVec D E u y j|
    rw [← h₂]
    exact h₁
theorem iSup_supNormQ_partialDeriv_le (u : E.Pt D → ℝ) :
    (⨆ i : Fin 4, supNormQ D E (partialDeriv D E i u)) ≤
      vecSupNormQ D E (gradVec D E u) := by
  refine iSup_le fun i => ?_
  refine iSup_le fun y => ?_
  exact le_iSup_of_le y
    (ENNReal.ofReal_le_ofReal (abs_apply_le_euclidNormVec (gradVec D E u y) i))
theorem vecSupNormQ_gradVec_le (u : E.Pt D → ℝ) :
    vecSupNormQ D E (gradVec D E u) ≤
      2 * ⨆ i : Fin 4, supNormQ D E (partialDeriv D E i u) := by
  refine iSup_le fun y => ?_
  obtain ⟨i, h₁, -⟩ := exists_index_euclidNormVec_le_two_mul (gradVec D E u y)
  calc ENNReal.ofReal (euclidNormVec (gradVec D E u y))
      ≤ ENNReal.ofReal (2 * |gradVec D E u y i|) := ENNReal.ofReal_le_ofReal h₁
    _ = 2 * ENNReal.ofReal |gradVec D E u y i| := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
    _ ≤ 2 * ⨆ i : Fin 4, supNormQ D E (partialDeriv D E i u) := by
      gcongr
      exact le_iSup_of_le i
        (le_iSup (fun y => ENNReal.ofReal |partialDeriv D E i u y|) y)
theorem c1NormsCompared_holds (u : E.Pt D → ℝ) : C1NormsCompared D E u := by
  constructor
  · exact max_le_max le_rfl (iSup_supNormQ_partialDeriv_le D E u)
  · refine max_le ?_ ?_
    · exact (le_max_left _ _).trans (ennreal_le_two_mul _)
    · refine (vecSupNormQ_gradVec_le D E u).trans ?_
      gcongr
      exact le_max_right _ _
theorem finiteAndBoundsSharp_of_compactSupport
    (h : Kind.QuotientCompactC1.CompactSupportC1Facts D E)
    (u : E.Pt D → ℝ) (hu : u ∈ c1Set D E) (hc : IsCompactQ D E (supportQ D E u)) :
    FiniteAndBoundsSharp D E u := by
  obtain ⟨-, -, hfin, -, -, -, -, hsharp⟩ := h u hu hc
  obtain ⟨h₁, h₂⟩ := c1NormsCompared_holds D E u
  refine ⟨h₁.trans_lt hfin, hfin, hsharp, ?_⟩
  have h40 : (0 : ℝ) ≤ 40 * D.M := by
    have := D.one_le_M
    linarith
  calc ENNReal.ofReal (40 * D.M) * euclidC1Norm D E u
      ≤ ENNReal.ofReal (40 * D.M) * (2 * c1NormQ D E u) := by gcongr
    _ = ENNReal.ofReal (80 * D.M) * c1NormQ D E u := by
      have h80 : 80 * D.M = 40 * D.M * 2 := by ring
      rw [h80, ENNReal.ofReal_mul h40, mul_assoc]
      simp
theorem differentiableAt_comp_line {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 4)
    (x : Fin 4 → ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 := by
  have h₁ : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h₂ : Differentiable ℝ fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    fun_prop
  exact (h₁.comp h₂) 0
theorem partialDerivR4_add {f g : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (i : Fin 4) (x : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i (fun z => f z + g z) x =
      TestFunctions.partialDerivR4 i f x + TestFunctions.partialDerivR4 i g x :=
  ((differentiableAt_comp_line hf i x).hasDerivAt.add
    (differentiableAt_comp_line hg i x).hasDerivAt).deriv
theorem partialDerivR4_const_mul {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ)
    (i : Fin 4) (x : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i (fun z => a * f z) x = a * TestFunctions.partialDerivR4 i f x :=
  ((differentiableAt_comp_line hf i x).hasDerivAt.const_mul a).deriv
theorem partialDeriv_add (h : WellPosedness.WellPosed)
    {u u' : E.Pt D → ℝ} (hu : u ∈ c1Set D E) (hu' : u' ∈ c1Set D E)
    (hs : u + u' ∈ c1Set D E) (i : Fin 4) :
    partialDeriv D E i (u + u') =
      partialDeriv D E i u + partialDeriv D E i u' := by
  obtain ⟨hq, -, -, -, -, -, -, -, -, hpd, -, -⟩ := h D E
  funext y
  obtain ⟨x, rfl⟩ := hq.2.1 y
  have e₁ := congrFun ((hpd _ hs).2 i).2.2 x
  have e₂ := congrFun ((hpd _ hu).2 i).2.2 x
  have e₃ := congrFun ((hpd _ hu').2 i).2.2 x
  simp only [Function.comp_apply] at e₁ e₂ e₃
  rw [Pi.add_apply, e₁, e₂, e₃]
  exact partialDerivR4_add hu hu' i x
theorem partialDeriv_smul (h : WellPosedness.WellPosed)
    {u : E.Pt D → ℝ} (a : ℝ) (hu : u ∈ c1Set D E) (hs : a • u ∈ c1Set D E)
    (i : Fin 4) :
    partialDeriv D E i (a • u) = a • partialDeriv D E i u := by
  obtain ⟨hq, -, -, -, -, -, -, -, -, hpd, -, -⟩ := h D E
  funext y
  obtain ⟨x, rfl⟩ := hq.2.1 y
  have e₁ := congrFun ((hpd _ hs).2 i).2.2 x
  have e₂ := congrFun ((hpd _ hu).2 i).2.2 x
  simp only [Function.comp_apply] at e₁ e₂
  rw [Pi.smul_apply, smul_eq_mul, e₁, e₂]
  exact partialDerivR4_const_mul hu a i x
theorem supNormQ_add_le (v w : E.Pt D → ℝ) :
    supNormQ D E (v + w) ≤ supNormQ D E v + supNormQ D E w := by apply _root_.YangMills.SharedProofs.p62305 <;> assumption
theorem supNormQ_smul (a : ℝ) (v : E.Pt D → ℝ) :
    supNormQ D E (a • v) = ENNReal.ofReal |a| * supNormQ D E v := by
  unfold Kind.supNormQ
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun y => ?_
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
theorem vecSupNormQ_add_le (v w : E.Pt D → Fin 4 → ℝ) :
    vecSupNormQ D E (v + w) ≤ vecSupNormQ D E v + vecSupNormQ D E w := by
  refine iSup_le fun y => ?_
  calc ENNReal.ofReal (euclidNormVec ((v + w) y))
      ≤ ENNReal.ofReal (euclidNormVec (v y) + euclidNormVec (w y)) :=
        ENNReal.ofReal_le_ofReal (euclidNormVec_add_le _ _)
    _ = ENNReal.ofReal (euclidNormVec (v y)) + ENNReal.ofReal (euclidNormVec (w y)) :=
        ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ vecSupNormQ D E v + vecSupNormQ D E w :=
        add_le_add (le_iSup (fun y => ENNReal.ofReal (euclidNormVec (v y))) y)
          (le_iSup (fun y => ENNReal.ofReal (euclidNormVec (w y))) y)
theorem vecSupNormQ_smul (a : ℝ) (v : E.Pt D → Fin 4 → ℝ) :
    vecSupNormQ D E (a • v) = ENNReal.ofReal |a| * vecSupNormQ D E v := by
  unfold Kind.vecSupNormQ
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun y => ?_
  rw [Pi.smul_apply, euclidNormVec_smul, ENNReal.ofReal_mul (abs_nonneg _)]
section OnSubmodule
variable (V : Submodule ℝ (E.Pt D → ℝ))
theorem isNormOnSubmodule_of_bounds (N : (E.Pt D → ℝ) → ℝ≥0∞) (hfin : ∀ u ∈ V, N u < ⊤)
    (hsup : ∀ u, supNormQ D E u ≤ N u)
    (hhom : ∀ (a : ℝ), ∀ u ∈ V, N (a • u) = ENNReal.ofReal |a| * N u)
    (htri : ∀ u ∈ V, ∀ u' ∈ V, N (u + u') ≤ N u + N u') : IsNormOnSubmodule D E V N := by
  refine ⟨hfin, fun u hu => ⟨fun h0 => ?_, ?_⟩, hhom, htri⟩
  · funext y
    have h₁ : ENNReal.ofReal |u y| ≤ N u :=
      (le_iSup (fun y => ENNReal.ofReal |u y|) y).trans (hsup u)
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h₁
    exact abs_nonpos_iff.mp h₁
  · rintro rfl
    simpa using hhom 0 0 V.zero_mem
theorem convergesWrt_of_le_two_mul (N N' : (E.Pt D → ℝ) → ℝ≥0∞) (hle : ∀ w ∈ V, N w ≤ 2 * N' w)
    (s : ℕ → E.Pt D → ℝ) (hs : ∀ j, s j ∈ V) (h : ConvergesWrt D E N' V s) :
    ConvergesWrt D E N V s := by
  obtain ⟨u, hu, hc⟩ := h
  refine ⟨u, hu, fun ε hε => ?_⟩
  obtain ⟨J, hJ⟩ := hc (ε / 2) (by positivity)
  exact ⟨J, fun j hj => (hle _ (V.sub_mem (hs j) hu)).trans_lt
    (two_mul_lt_ofReal_of_lt_half hε (hJ j hj))⟩
theorem isCauchyWrt_of_le_two_mul (N N' : (E.Pt D → ℝ) → ℝ≥0∞) (hle : ∀ w ∈ V, N w ≤ 2 * N' w)
    (s : ℕ → E.Pt D → ℝ) (hs : ∀ j, s j ∈ V) (h : IsCauchyWrt D E N' s) :
    IsCauchyWrt D E N s := by
  refine fun ε hε => ?_
  obtain ⟨J, hJ⟩ := h (ε / 2) (by positivity)
  exact ⟨J, fun i hi j hj => (hle _ (V.sub_mem (hs i) (hs j))).trans_lt
    (two_mul_lt_ofReal_of_lt_half hε (hJ i hi j hj))⟩
theorem isDenseWrt_of_le_two_mul (N N' : (E.Pt D → ℝ) → ℝ≥0∞) (hle : ∀ w ∈ V, N w ≤ 2 * N' w)
    (A : Set (E.Pt D → ℝ)) (hA : A ⊆ V) (h : IsDenseWrt D E N' V A) :
    IsDenseWrt D E N V A := by
  intro f hf ε hε
  obtain ⟨g, hg, hfg⟩ := h f hf (ε / 2) (by positivity)
  exact ⟨g, hg, (hle _ (V.sub_mem hf (hA hg))).trans_lt (two_mul_lt_ofReal_of_lt_half hε hfg)⟩
theorem equivalentNormsOn_holds
    (h : WellPosedness.WellPosed)
    (hV : ∀ u ∈ V, u ∈ c1Set D E ∧ euclidC1Norm D E u < ⊤) :
    EquivalentNormsOn D E V := by
  have hadd : ∀ u ∈ V, ∀ u' ∈ V, ∀ i, partialDeriv D E i (u + u') =
      partialDeriv D E i u + partialDeriv D E i u' := fun u hu u' hu' i =>
    partialDeriv_add D E h (hV u hu).1 (hV u' hu').1 (hV _ (V.add_mem hu hu')).1 i
  have hsmul : ∀ (a : ℝ), ∀ u ∈ V, ∀ i, partialDeriv D E i (a • u) =
      a • partialDeriv D E i u := fun a u hu i =>
    partialDeriv_smul D E h a (hV u hu).1 (hV _ (V.smul_mem a hu)).1 i
  have hgadd : ∀ u ∈ V, ∀ u' ∈ V,
      gradVec D E (u + u') = gradVec D E u + gradVec D E u' := fun u hu u' hu' => by
    funext y i
    exact congrFun (hadd u hu u' hu' i) y
  have hgsmul : ∀ (a : ℝ), ∀ u ∈ V, gradVec D E (a • u) = a • gradVec D E u :=
    fun a u hu => by
      funext y i
      exact congrFun (hsmul a u hu i) y
  have heu : IsNormOnSubmodule D E V (euclidC1Norm D E) := by
    refine isNormOnSubmodule_of_bounds D E V _ (fun u hu => (hV u hu).2)
      (fun u => le_max_left _ _) (fun a u hu => ?_) (fun u hu u' hu' => ?_)
    · unfold Kind.euclidC1Norm
      rw [supNormQ_smul, hgsmul a u hu, vecSupNormQ_smul, ennreal_mul_max_distrib]
    · unfold Kind.euclidC1Norm
      rw [hgadd u hu u' hu']
      refine max_le ?_ ?_
      · exact (supNormQ_add_le D E u u').trans
          (add_le_add (le_max_left _ _) (le_max_left _ _))
      · exact (vecSupNormQ_add_le D E _ _).trans
          (add_le_add (le_max_right _ _) (le_max_right _ _))
  have hc1 : IsNormOnSubmodule D E V (c1NormQ D E) := by
    refine isNormOnSubmodule_of_bounds D E V _
      (fun u hu => (c1NormsCompared_holds D E u).1.trans_lt (hV u hu).2)
      (fun u => le_max_left _ _) (fun a u hu => ?_) (fun u hu u' hu' => ?_)
    · have hi : (⨆ i : Fin 4, supNormQ D E (partialDeriv D E i (a • u))) =
          ENNReal.ofReal |a| * ⨆ i : Fin 4, supNormQ D E (partialDeriv D E i u) := by
        rw [ENNReal.mul_iSup]
        exact iSup_congr fun i => by rw [hsmul a u hu i, supNormQ_smul]
      unfold Kind.c1NormQ
      rw [supNormQ_smul, hi, ennreal_mul_max_distrib]
    · refine max_le ?_ ?_
      · exact (supNormQ_add_le D E u u').trans
          (add_le_add (le_max_left _ _) (le_max_left _ _))
      · refine iSup_le fun i => ?_
        rw [hadd u hu u' hu' i]
        exact (supNormQ_add_le D E _ _).trans
          (add_le_add ((le_iSup (fun i => supNormQ D E (partialDeriv D E i u)) i).trans
              (le_max_right _ _))
            ((le_iSup (fun i => supNormQ D E (partialDeriv D E i u')) i).trans
              (le_max_right _ _)))
  have hle₁ : ∀ w ∈ V, euclidC1Norm D E w ≤ 2 * c1NormQ D E w :=
    fun w _ => (c1NormsCompared_holds D E w).2
  have hle₂ : ∀ w ∈ V, c1NormQ D E w ≤ 2 * euclidC1Norm D E w :=
    fun w _ => (c1NormsCompared_holds D E w).1.trans (ennreal_le_two_mul _)
  refine ⟨heu, hc1, fun s hs => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, fun A hA => ⟨?_, ?_⟩⟩
  · exact convergesWrt_of_le_two_mul D E V _ _ hle₂ s hs
  · exact convergesWrt_of_le_two_mul D E V _ _ hle₁ s hs
  · exact isCauchyWrt_of_le_two_mul D E V _ _ hle₂ s hs
  · exact isCauchyWrt_of_le_two_mul D E V _ _ hle₁ s hs
  · exact isDenseWrt_of_le_two_mul D E V _ _ hle₂ A hA
  · exact isDenseWrt_of_le_two_mul D E V _ _ hle₁ A hA
end OnSubmodule
theorem statement_holds (h₁ : Kind.QuotientCompactC1.Claim)
    (h₂ : WellPosedness.WellPosed) : statement := by
  intro D E
  refine ⟨fun u hu => ⟨gradNormBetweenPartials_holds D E u, c1NormsCompared_holds D E u,
    fun hc => ?_⟩, fun V hV => equivalentNormsOn_holds D E V h₂ hV⟩
  obtain ⟨-, -, -, -, hcs⟩ := h₁ D E
  exact finiteAndBoundsSharp_of_compactSupport D E hcs u hu hc
end YangMills.Construction.PeriodicSpace.C1NormComparison
