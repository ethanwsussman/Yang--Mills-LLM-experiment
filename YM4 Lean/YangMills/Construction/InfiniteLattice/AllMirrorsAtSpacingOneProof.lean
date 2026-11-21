import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayerProof
import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOne
import YangMills.Construction.InfiniteLattice.FunctionsStatesSupportsClassesMirrorsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfTori
import YangMills.Construction.InfiniteLattice.StatesWithAGivenMirrorDominateLocalObservables
import YangMills.Construction.InfiniteLattice.TwoMirrorsOfOneFamilyGiveATranslation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory NormalFamilies GibbsAtFixedSpacing
open PeriodicLattice (coordVec)
open scoped ComplexOrder NNReal Matrix Topology
namespace InfiniteLattice
namespace UnitMeshReflectionPositivity
theorem integral_eq_ofReal_re_of_im_zero {H : GaugeField 1 → ℂ} (hreal : ∀ U, (H U).im = 0)
    (ρ : Measure (GaugeField 1)) : ∫ U, H U ∂ρ = ((∫ U, (H U).re ∂ρ : ℝ) : ℂ) := by
  have h : H = fun U => (((H U).re : ℝ) : ℂ) := by
    funext U
    exact Complex.ext rfl (by simp [hreal U])
  conv_lhs => rw [h]
  exact integral_ofReal
section Integrals
variable [CompactSpace (GaugeField 1)]
theorem integrable_of_continuous_gaugeField {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E]
    {f : GaugeField 1 → E} (hf : Continuous f) (ρ : Measure (GaugeField 1))
    [IsFiniteMeasure ρ] : Integrable f ρ := by
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun U => hC _ (Set.mem_range_self U))
theorem integral_eq_of_re_im_eq {F : GaugeField 1 → ℂ} (hF : Continuous F)
    {ρ ν : Measure (GaugeField 1)} [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (hre : ∫ U, (F U).re ∂ρ = ∫ U, (F U).re ∂ν) (him : ∫ U, (F U).im ∂ρ = ∫ U, (F U).im ∂ν) :
    ∫ U, F U ∂ρ = ∫ U, F U ∂ν := by
  have hρ := integrable_of_continuous_gaugeField hF ρ
  have hν := integrable_of_continuous_gaugeField hF ν
  apply Complex.ext
  · have h1 := Complex.reCLM.integral_comp_comm hρ
    have h2 := Complex.reCLM.integral_comp_comm hν
    simp only [Complex.reCLM_apply] at h1 h2
    rw [← h1, ← h2, hre]
  · have h1 := Complex.imCLM.integral_comp_comm hρ
    have h2 := Complex.imCLM.integral_comp_comm hν
    simp only [Complex.imCLM_apply] at h1 h2
    rw [← h1, ← h2, him]
theorem integral_le_integral_add_of_le {a b : GaugeField 1 → ℝ} (ha : Continuous a)
    (hb : Continuous b)
    (c : ℝ) (ρ : Measure (GaugeField 1)) [IsProbabilityMeasure ρ] (h : ∀ U, a U ≤ b U + c) :
    ∫ U, a U ∂ρ ≤ ∫ U, b U ∂ρ + c := by
  have hi : Integrable (fun U => b U + c) ρ :=
    integrable_of_continuous_gaugeField (hb.add continuous_const) ρ
  have h1 := integral_mono (integrable_of_continuous_gaugeField ha ρ) hi h
  have h2 : ∫ U, (b U + c) ∂ρ = ∫ U, b U ∂ρ + c := by
    rw [integral_add (integrable_of_continuous_gaugeField hb ρ) (integrable_const c)]
    simp
  linarith
end Integrals
theorem continuous_integral_probabilityMeasure {f : GaugeField 1 → ℝ} (hf : Continuous f) :
    @Continuous _ ℝ (probabilityMeasuresWeakTopology 1) _
      (fun ρ : ProbabilityMeasure (GaugeField 1) =>
        ∫ U, f U ∂(ρ : Measure (GaugeField 1))) := by
  let Fc : C(GaugeField 1, ℂ) := ⟨fun U => (f U : ℂ), Complex.continuous_ofReal.comp hf⟩
  have h1 : @Continuous _ ℂ (probabilityMeasuresWeakTopology 1) _
      (fun ρ : ProbabilityMeasure (GaugeField 1) =>
        ∫ U, Fc U ∂(ρ : Measure (GaugeField 1))) :=
    continuous_iInf_dom (i := Fc) continuous_induced_dom
  have h2 : (fun ρ : ProbabilityMeasure (GaugeField 1) =>
      ∫ U, f U ∂(ρ : Measure (GaugeField 1))) =
      fun ρ : ProbabilityMeasure (GaugeField 1) =>
        (∫ U, Fc U ∂(ρ : Measure (GaugeField 1))).re := by
    funext ρ
    have : ∫ U, Fc U ∂(ρ : Measure (GaugeField 1)) =
        ((∫ U, f U ∂(ρ : Measure (GaugeField 1)) : ℝ) : ℂ) := integral_ofReal
    rw [this, Complex.ofReal_re]
  rw [h2]
  exact @Continuous.comp _ _ _ (probabilityMeasuresWeakTopology 1) _ _ _ _ Complex.continuous_re h1
theorem subset_of_dominates_real_local [CompactSpace (GaugeField 1)]
    {T R : Set (Measure (GaugeField 1))}
    (hT : IsStateFamily T) (hconv : Convex ℝ≥0 R) (hclosed : IsWeakClosedWithin T R)
    (hcompact : IsWeakCompact R)
    (hnbhd : ∀ (ν : ProbabilityMeasure (GaugeField 1))
      (N : Set (ProbabilityMeasure (GaugeField 1))),
      N ∈ @nhds _ (probabilityMeasuresWeakTopology 1) ν →
        ∃ B : Set (Measure (GaugeField 1)),
          IsWeakBasicNhd (ν : Measure (GaugeField 1)) B ∧ asProbabilityMeasures B ⊆ N)
    (hdense : IsSupNormDenseIn (continuousLocalFunctions 1 ∩ realContinuous 1)
      (realContinuous 1))
    (hdom : ∀ ν ∈ T, ∀ A ∈ continuousLocalFunctions 1, (∀ U, (A U).im = 0) →
      ∃ ν₀ ∈ R, stateEval ν A ≤ stateEval ν₀ A) : T ⊆ R := by
  intro ν hν
  by_contra hνR
  obtain ⟨-, C, hC, hRC⟩ := hclosed
  have hνC : ν ∉ C := fun h => hνR (by rw [hRC]; exact ⟨hν, h⟩)
  have hνp : IsProbabilityMeasure ν := hT ν hν
  let ν' : ProbabilityMeasure (GaugeField 1) := ⟨ν, hνp⟩
  have hopen : IsOpen[probabilityMeasuresWeakTopology 1] (asProbabilityMeasures C)ᶜ :=
    hC.2.isOpen_compl
  have hmem : (asProbabilityMeasures C)ᶜ ∈ @nhds _ (probabilityMeasuresWeakTopology 1) ν' :=
    @IsOpen.mem_nhds _ (probabilityMeasuresWeakTopology 1) _ _ hopen hνC
  obtain ⟨B, ⟨k, F, ε, -, hF, hε, rfl⟩, hBsub⟩ := hnbhd ν' _ hmem
  let G : Fin k × Bool → GaugeField 1 → ℝ :=
    fun i U => if i.2 then (F i.1 U).re else (F i.1 U).im
  have hFc : ∀ l, Continuous (F l) := hF
  have hG : ∀ i, Continuous (G i) := by
    rintro ⟨l, b⟩
    cases b
    · exact Complex.continuous_im.comp (hFc l)
    · exact Complex.continuous_re.comp (hFc l)
  let Φ : Measure (GaugeField 1) → (Fin k × Bool → ℝ) := fun ρ i => ∫ U, G i U ∂ρ
  have hΦc : @Continuous _ _ (probabilityMeasuresWeakTopology 1) _
      (fun ρ : ProbabilityMeasure (GaugeField 1) => Φ (ρ : Measure (GaugeField 1))) :=
    @continuous_pi _ _ _ (probabilityMeasuresWeakTopology 1) _ _ fun i =>
      continuous_integral_probabilityMeasure (hG i)
  have hYc : IsCompact (Φ '' R) := by
    have himage : Φ '' R = (fun ρ : ProbabilityMeasure (GaugeField 1) =>
        Φ (ρ : Measure (GaugeField 1))) '' asProbabilityMeasures R := by
      ext y
      constructor
      · rintro ⟨ρ, hρ, rfl⟩
        have hp : IsProbabilityMeasure ρ := hcompact.1 ρ hρ
        exact ⟨⟨ρ, hp⟩, hρ, rfl⟩
      · rintro ⟨ρ, hρ, rfl⟩
        exact ⟨_, hρ, rfl⟩
    rw [himage]
    exact @IsCompact.image _ _ (probabilityMeasuresWeakTopology 1) _ _ _ hcompact.2 hΦc
  have hYconv : Convex ℝ (Φ '' R) := by
    rintro _ ⟨ρ₁, h₁, rfl⟩ _ ⟨ρ₂, h₂, rfl⟩ a b ha hb hab
    have : IsProbabilityMeasure ρ₁ := hcompact.1 ρ₁ h₁
    have : IsProbabilityMeasure ρ₂ := hcompact.1 ρ₂ h₂
    let a' : ℝ≥0 := ⟨a, ha⟩
    let b' : ℝ≥0 := ⟨b, hb⟩
    refine ⟨a' • ρ₁ + b' • ρ₂, hconv h₁ h₂ zero_le zero_le (NNReal.eq hab), ?_⟩
    funext i
    have i₁ := integrable_of_continuous_gaugeField (hG i) (a' • ρ₁)
    have i₂ := integrable_of_continuous_gaugeField (hG i) (b' • ρ₂)
    change ∫ U, G i U ∂(a' • ρ₁ + b' • ρ₂) = a * (∫ U, G i U ∂ρ₁) + b * ∫ U, G i U ∂ρ₂
    rw [integral_add_measure i₁ i₂, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    rfl
  have hz : Φ ν ∉ Φ '' R := by
    rintro ⟨ρ, hρ, hρz⟩
    have hρp : IsProbabilityMeasure ρ := hcompact.1 ρ hρ
    have hρC : ρ ∈ C := by
      rw [hRC] at hρ
      exact hρ.2
    have heq : ∀ l, stateEval ρ (F l) = stateEval ν (F l) := fun l =>
      integral_eq_of_re_im_eq (hFc l) (congrFun hρz (l, true)) (congrFun hρz (l, false))
    have hin : (⟨ρ, hρp⟩ : ProbabilityMeasure (GaugeField 1)) ∈
        asProbabilityMeasures (weakBasicNhd (ν' : Measure (GaugeField 1)) F ε) :=
      ⟨hρp, fun l => by
        change ‖stateEval ρ (F l) - stateEval ν (F l)‖ < ε
        rw [heq l, sub_self, norm_zero]
        exact hε⟩
    exact hBsub hin hρC
  obtain ⟨f, u, hfu, hzu⟩ := geometric_hahn_banach_closed_point hYconv hYc.isClosed hz
  let w : Fin k × Bool → ℝ := fun i => f fun j => if i = j then 1 else 0
  have hf : ∀ y, f y = ∑ i, y i * w i := fun y =>
    LinearMap.pi_apply_eq_sum_univ (f : (Fin k × Bool → ℝ) →ₗ[ℝ] ℝ) y
  let S : GaugeField 1 → ℝ := fun U => ∑ i, G i U * w i
  have hS : Continuous S := continuous_finset_sum _ fun i _ => (hG i).mul continuous_const
  have hSint : ∀ (ρ : Measure (GaugeField 1)) [IsProbabilityMeasure ρ],
      ∫ U, S U ∂ρ = f (Φ ρ) := by
    intro ρ _
    rw [hf]
    change ∫ U, ∑ i, G i U * w i ∂ρ = _
    rw [integral_finset_sum (f := fun i U => G i U * w i) _ fun i _ =>
      integrable_of_continuous_gaugeField ((hG i).mul continuous_const) ρ]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  have hε' : 0 < (f (Φ ν) - u) / 3 := by linarith
  obtain ⟨H, ⟨hHloc, hHreal⟩, hH⟩ := hdense.2 (fun U => (S U : ℂ))
    ⟨Complex.continuous_ofReal.comp hS, fun U => Complex.ofReal_im _⟩ _ hε'
  obtain ⟨ν₀, hν₀, hle⟩ := hdom ν hν H hHloc hHreal.2
  have : IsProbabilityMeasure ν₀ := hcompact.1 ν₀ hν₀
  have hHc : Continuous H := hHreal.1
  have hHr : Continuous fun U => (H U).re := Complex.continuous_re.comp hHc
  have hle' : ∫ U, (H U).re ∂ν ≤ ∫ U, (H U).re ∂ν₀ := by
    have h := hle
    change ∫ U, H U ∂ν ≤ ∫ U, H U ∂ν₀ at h
    rw [integral_eq_ofReal_re_of_im_zero hHreal.2 ν,
      integral_eq_ofReal_re_of_im_zero hHreal.2 ν₀] at h
    exact Complex.real_le_real.mp h
  have hbound : ∀ U, |S U - (H U).re| ≤ (f (Φ ν) - u) / 3 := by
    intro U
    have hcont : Continuous fun U => ‖((fun U => (S U : ℂ)) - H) U‖ :=
      ((Complex.continuous_ofReal.comp hS).sub hHc).norm
    have hb : BddAbove (Set.range fun U => ‖((fun U => (S U : ℂ)) - H) U‖) :=
      (isCompact_range hcont).bddAbove
    have h1 : ‖((fun U => (S U : ℂ)) - H) U‖ ≤ observableSupNorm ((fun U => (S U : ℂ)) - H) :=
      le_ciSup hb U
    have h2 : |S U - (H U).re| ≤ ‖((fun U => (S U : ℂ)) - H) U‖ := by
      have := Complex.abs_re_le_norm (((fun U => (S U : ℂ)) - H) U)
      simpa using this
    linarith
  have h1 : ∫ U, S U ∂ν ≤ ∫ U, (H U).re ∂ν + (f (Φ ν) - u) / 3 :=
    integral_le_integral_add_of_le hS hHr _ ν fun U => by
      have := (abs_le.mp (hbound U)).2
      linarith
  have h2 : ∫ U, (H U).re ∂ν₀ ≤ ∫ U, S U ∂ν₀ + (f (Φ ν) - u) / 3 :=
    integral_le_integral_add_of_le hHr hS _ ν₀ fun U => by
      have := (abs_le.mp (hbound U)).1
      linarith
  rw [hSint ν] at h1
  rw [hSint ν₀] at h2
  have h3 := hfu (Φ ν₀) ⟨ν₀, hν₀, rfl⟩
  linarith
theorem coordVec_dotProduct (μ : Fin 4) (x : AmbientSpace) : coordVec μ ⬝ᵥ x = x μ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxQuotient.coordVec_dotProduct <;> assumption
theorem reflectAcross_coordVec_apply (μ : Fin 4) (x : AmbientSpace) (κ : Fin 4) :
    reflectAcross (coordVec μ) 0 x κ = if κ = μ then -x κ else x κ := by
  have hq : normSq (coordVec μ) = 1 := by
    rw [normSq_eq_dotProduct, coordVec_dotProduct]
    simp [coordVec]
  simp only [reflectAcross, dualVector, hq, coordVec_dotProduct]
  by_cases h : κ = μ
  · subst h
    simp [coordVec]
    ring
  · simp [coordVec, h]
theorem reflectAcross_coordVec_sub {μ lam : Fin 4} (hne : μ ≠ lam) (x : AmbientSpace) :
    reflectAcross (coordVec μ - coordVec lam) 0 x = x ∘ Equiv.swap μ lam := by
  have hdot : ∀ y : AmbientSpace, (coordVec μ - coordVec lam) ⬝ᵥ y = y μ - y lam :=
    fun y => by rw [sub_dotProduct, coordVec_dotProduct, coordVec_dotProduct]
  have hq : normSq (coordVec μ - coordVec lam) = 2 := by
    rw [normSq_eq_dotProduct, hdot]
    simp [coordVec, hne, hne.symm]
    norm_num
  funext κ
  simp only [reflectAcross, dualVector, hq, hdot]
  by_cases h1 : κ = μ
  · subst h1
    simp [coordVec, Pi.single_eq_of_ne hne]
    ring
  · by_cases h2 : κ = lam
    · subst h2
      simp [coordVec, Pi.single_eq_of_ne h1]
      ring
    · simp [coordVec, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2,
        Equiv.swap_apply_of_ne_of_ne h1 h2]
theorem latticeSymmetry_ext_toFun {r r' : LatticeSymmetry 1} (h : r.toFun = r'.toFun) :
    r = r' := by
  rcases r with ⟨f, _, _⟩
  rcases r' with ⟨f', _, _⟩
  cases (h : f = f')
  rfl
theorem shift_and_hyperoctahedral_invariant_of_reflections
    (hT : NormalFamilies.ReflectionPairShift.ReflectionPairsGiveShift)
    {ν : Measure (GaugeField 1)} (G : Subgroup (Equiv.Perm AmbientSpace))
    (hG : ∀ f : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry 1, r.toFun = f ∧ IsSymmetricUnder ν r) ↔ ∃ g ∈ G, ⇑g = f)
    (hrefl : ∀ P : NormalLevelPair 1, IsSymmetricUnder ν P.reflectSymmetry) :
    IsShiftInvariant ν ∧
      ∀ r : LatticeSymmetry 1, (∃ w ∈ hyperoctahedralLinearGroup, r.toFun = ⇑w) →
        IsSymmetricUnder ν r := by
  have hmem : ∀ P : NormalLevelPair 1, ∃ g ∈ G, ⇑g = reflectAcross P.normal P.level := fun P =>
    (hG _).mp ⟨P.reflectSymmetry, rfl, hrefl P⟩
  have hback : ∀ r : LatticeSymmetry 1, (∃ g ∈ G, ⇑g = r.toFun) → IsSymmetricUnder ν r := by
    intro r hr
    obtain ⟨r', hr', hinv⟩ := (hG r.toFun).mpr hr
    rwa [latticeSymmetry_ext_toFun hr'] at hinv
  have hstep : ∀ μ, ∃ g ∈ G, ⇑g = (shift (axisStep 1 μ)).toFun := by
    intro μ
    obtain ⟨P, P', -, -, -, -, -, -, hcomp⟩ := (hT.2 μ).2
    obtain ⟨g, hg, hgf⟩ := hmem P
    obtain ⟨g', hg', hgf'⟩ := hmem P'
    refine ⟨g' * g, mul_mem hg' hg, ?_⟩
    rw [Equiv.Perm.coe_mul, hgf, hgf']
    exact hcomp
  let K : AddSubgroup (LatticePoint 1) :=
    { carrier := {v | ∃ g ∈ G, ⇑g = (shift v).toFun}
      add_mem' := by
        rintro v v' ⟨g, hg, hgf⟩ ⟨g', hg', hgf'⟩
        refine ⟨g * g', mul_mem hg hg', funext fun x => ?_⟩
        rw [Equiv.Perm.coe_mul, hgf, hgf']
        change x + (v' : AmbientSpace) + (v : AmbientSpace) =
          x + ((v + v' : LatticePoint 1) : AmbientSpace)
        rw [AddSubgroup.coe_add]
        abel
      zero_mem' := ⟨1, one_mem G, funext fun x => by simp [shift]⟩
      neg_mem' := by
        rintro v ⟨g, hg, hgf⟩
        refine ⟨g⁻¹, inv_mem hg, funext fun x => ?_⟩
        rw [Equiv.Perm.inv_eq_iff_eq, hgf]
        change x = x + ((-v : LatticePoint 1) : AmbientSpace) + (v : AmbientSpace)
        rw [AddSubgroup.coe_neg]
        abel }
  have hK : ∀ v : LatticePoint 1, v ∈ K := by
    intro v
    obtain ⟨m, hm⟩ := v.2
    have hv : v = ∑ μ, m μ • axisStep 1 μ := by
      apply Subtype.ext
      funext κ
      rw [hm κ, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      simp [axisStep, Pi.single_apply]
    rw [hv]
    exact sum_mem fun μ _ => zsmul_mem (hstep μ) _
  refine ⟨fun v => hback _ (hK v), ?_⟩
  have hdiag : ∀ μ lam : Fin 4, μ ≠ lam → ∃ g ∈ G, ∀ x, g x = x ∘ Equiv.swap μ lam := by
    have hlt : ∀ μ lam : Fin 4, μ < lam → ∃ g ∈ G, ∀ x, g x = x ∘ Equiv.swap μ lam := by
      intro μ lam h
      obtain ⟨g, hg, hgf⟩ := hmem ⟨coordVec μ - coordVec lam,
        Or.inr ⟨μ, lam, h, Or.inr rfl⟩, 0, fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
      exact ⟨g, hg, fun x => by rw [hgf]; exact reflectAcross_coordVec_sub h.ne x⟩
    intro μ lam h
    rcases lt_or_gt_of_ne h with h' | h'
    · exact hlt _ _ h'
    · rw [Equiv.swap_comm]
      exact hlt _ _ h'
  have hperm : ∀ π : Equiv.Perm (Fin 4), ∃ g ∈ G, ∀ x, g x = x ∘ π := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one => exact ⟨1, one_mem G, fun x => rfl⟩
    | swap_mul f a b hab ih =>
      obtain ⟨g, hg, hgf⟩ := ih
      obtain ⟨t, ht, htf⟩ := hdiag a b hab
      refine ⟨g * t, mul_mem hg ht, fun x => ?_⟩
      rw [Equiv.Perm.coe_mul, Function.comp_apply, htf, hgf]
      rfl
  have hsign : ∀ A : Finset (Fin 4),
      ∃ g ∈ G, ∀ x κ, g x κ = if κ ∈ A then -x κ else x κ := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨1, one_mem G, fun x κ => by simp⟩
    | insert a A ha ih =>
      obtain ⟨g, hg, hgf⟩ := ih
      obtain ⟨d, hd, hdf⟩ := hmem ⟨coordVec a, Or.inl ⟨a, rfl⟩, 0,
        fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
      refine ⟨d * g, mul_mem hd hg, fun x κ => ?_⟩
      rw [Equiv.Perm.coe_mul, Function.comp_apply, hdf]
      change reflectAcross (coordVec a) 0 (g x) κ = _
      rw [reflectAcross_coordVec_apply, hgf]
      by_cases h : κ = a
      · subst h
        simp [ha]
      · simp [h]
  rintro r ⟨w, hw, hrw⟩
  obtain ⟨π, s, hs⟩ := (mem_hyperoctahedralLinearGroup_iff w).mp hw
  obtain ⟨p, hp, hpf⟩ := hperm π
  obtain ⟨d, hd, hdf⟩ := hsign (Finset.univ.filter fun κ => s κ = -1)
  refine hback r ⟨d * p, mul_mem hd hp, ?_⟩
  rw [hrw]
  funext x κ
  rw [Equiv.Perm.coe_mul, Function.comp_apply, hdf, hs, hpf]
  rcases Int.units_eq_one_or (s κ) with h | h <;> simp [h]
theorem statement_holds (h₁ : MirrorDomination.Statement)
    (h₂ : BasicStructure.Statement)
    (h₃ : PeriodicGibbsFoldAndCompactness.Statement)
    (h₄ : FieldSpace.SymmetryProperties)
    (h₅ : NormalFamilies.ReflectionPairShift.ReflectionPairsGiveShift) : Statement := by
  intro β hβ
  obtain ⟨hA, -, hS, -, -, -, -, -⟩ := h₂.1 1 one_pos β hβ
  obtain ⟨hcompactSpace, -, -, -, -, -, -, -, -, -, hdense⟩ := hA
  have := hcompactSpace
  obtain ⟨-, -, hnbhd, -, -, -, htest, hgroup⟩ := hS
  obtain ⟨hone, -, -, -, hside⟩ := h₃ β hβ
  have hrp : ∀ P : NormalLevelPair 1,
      MirrorDomination.gibbsClassOf β evenLattice ⊆
        mirrorReflectionPositiveStates β P := by
    intro P
    obtain ⟨-, ⟨hconv, hclosed, hcompact⟩, -, hdom, -⟩ := h₁ β hβ P
    exact subset_of_dominates_real_local hclosed.1 hconv hclosed hcompact hnbhd hdense hdom
  have hmirror : ∀ ν ∈ periodicGibbsClass one_pos β, ∀ P : NormalLevelPair 1,
      ν ∈ mirrorReflectionPositiveStates β P := fun ν hν P => hrp P (by
    have h : ν ∈ subgroupInvariantGibbsClass one_pos β
        (evenLattice.addSubgroupOf (latticeSubgroup 1)) := hone ▸ hν
    exact h)
  have hstate : ∀ ν ∈ periodicGibbsClass one_pos β, IsLatticeState ν := fun ν hν => by
    have h : ν ∈ subgroupInvariantGibbsClass one_pos β
        (evenLattice.addSubgroupOf (latticeSubgroup 1)) := hone ▸ hν
    exact h.1.1
  have hinv : ∀ ν ∈ periodicGibbsClass one_pos β, ∀ P : NormalLevelPair 1,
      IsSymmetricUnder ν P.reflectSymmetry := fun ν hν P =>
    (htest ν _ (hstate ν hν)).mpr (hmirror ν hν P).2.1
  have hall : ∀ ν ∈ periodicGibbsClass one_pos β,
      IsShiftInvariant ν ∧ ∀ r : LatticeSymmetry 1,
        (∃ w ∈ hyperoctahedralLinearGroup, r.toFun = ⇑w) → IsSymmetricUnder ν r := by
    intro ν hν
    obtain ⟨G, hG⟩ := hgroup ν (hstate ν hν)
    exact shift_and_hyperoctahedral_invariant_of_reflections h₅ G hG (hinv ν hν)
  refine ⟨fun ν hν => ⟨fun P => ⟨fun F hF => hinv ν hν P F hF, fun F hF => ?_⟩,
    (hall ν hν).1, (hall ν hν).2⟩, fun R => (h₄ 1 one_pos).2.2.2.1 R |>.2, ?_⟩
  · exact hside P ν (hstate ν hν) (hinv ν hν P) (hmirror ν hν P).2.2 F hF
  · apply Set.Subset.antisymm
    · intro ν hν
      have h : ν ∈ subgroupInvariantGibbsClass one_pos β
          (evenLattice.addSubgroupOf (latticeSubgroup 1)) := hone ▸ hν
      exact ⟨h.1, fun v _ => (hall ν hν).1 v⟩
    · intro ν hν
      exact Set.mem_iUnion₂.mpr ⟨⊤, inferInstance, hν⟩
end UnitMeshReflectionPositivity
end InfiniteLattice
end YangMills.Construction
