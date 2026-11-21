import YangMills.Construction.Cumulants.CumulantsOfALinearMapIntoBoundedRandomVariables
import YangMills.Construction.Cumulants.GeneratingFunctionOfATupleAndItsLogarithm
import YangMills.Construction.InfiniteLattice.ConnectedFunctionsOfAProbabilityMeasure
import YangMills.Construction.InfiniteLattice.FaceEnergyUnderProbability
import YangMills.Construction.Probability.ExpectationBasicProperties
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.SeparatedFamilies
namespace ProbabilityMeasureCorrelations
open InfiniteLattice CutoffLattice
def boundedCompactlySupportedSubmodule : Submodule ℝ (AmbientSpace → ℝ) where
  carrier := boundedCompactlySupported
  add_mem' := by
    rintro u v ⟨⟨A, hA⟩, hu⟩ ⟨⟨B, hB⟩, hv⟩
    exact ⟨⟨A + B, fun x => (abs_add_le _ _).trans (add_le_add (hA x) (hB x))⟩, hu.add hv⟩
  zero_mem' := ⟨⟨0, fun x => by simp⟩, HasCompactSupport.zero⟩
  smul_mem' := by
    rintro t u ⟨⟨A, hA⟩, hu⟩
    refine ⟨⟨|t| * A, fun x => ?_⟩, hu.mono (Function.support_const_smul_subset t u)⟩
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg t)
variable {L K : ℕ}
theorem finite_nonzero_coeffs
    (hloc : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {q : ElementaryPlaquette (spacingAt L K) | q.center ∈ S}.Finite)
    {u : AmbientSpace → ℝ} (hu : u ∈ boundedCompactlySupported) :
    {q : ElementaryPlaquette (spacingAt L K) | u q.center ≠ 0}.Finite :=
  (hloc _ hu.2.isCompact.isBounded).subset fun _ hq => subset_tsupport u hq
theorem smearedObservable_eq_finsetSum (u : AmbientSpace → ℝ)
    (Q : Finset (ElementaryPlaquette (spacingAt L K)))
    (hQ : ∀ q : ElementaryPlaquette (spacingAt L K), u q.center ≠ 0 → q ∈ Q)
    (A : FieldsAt L K) :
    smearedObservable L K u A = ∑ q ∈ Q, faceEnergy A q * u q.center := by
  rw [smearedObservable_eq_smearedEnergy]
  unfold smearedEnergy
  simp only [smul_eq_mul]
  refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
  refine Finset.mem_coe.mpr (hQ q fun h => ?_)
  exact hq (by simp [h])
theorem smearedObservable_isBoundedRealRV
    (hE : Probability.ExpectationBasicProperties)
    (μ : Measure (FieldsAt L K)) [IsProbabilityMeasure μ]
    (hq : ∀ q : ElementaryPlaquette (spacingAt L K), Probability.IsBoundedRealRV
      (fun A : FieldsAt L K => faceEnergy A q))
    (u : AmbientSpace → ℝ) (Q : Finset (ElementaryPlaquette (spacingAt L K)))
    (hQ : ∀ q : ElementaryPlaquette (spacingAt L K), u q.center ≠ 0 → q ∈ Q) :
    Probability.IsBoundedRealRV (smearedObservable L K u) := by
  obtain ⟨W, hW⟩ := (hE (FieldsAt L K) μ).1.1
  have hmem : ∀ y : FieldsAt L K → ℝ,
      y ∈ W ↔ Probability.IsBoundedRealRV y := fun y => by
    rw [← SetLike.mem_coe, hW]
    rfl
  have heq : smearedObservable L K u =
      ∑ q ∈ Q, u q.center • fun A : FieldsAt L K => faceEnergy A q := by
    funext A
    rw [smearedObservable_eq_finsetSum u Q hQ A, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [mul_comm]
  rw [← hmem, heq]
  exact W.sum_mem fun q _ => W.smul_mem _ ((hmem _).2 (hq q))
def smearedObservableLinearMap
    (hloc : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {q : ElementaryPlaquette (spacingAt L K) | q.center ∈ S}.Finite) :
    boundedCompactlySupportedSubmodule →ₗ[ℝ] (FieldsAt L K → ℝ) where
  toFun u := smearedObservable L K (u : AmbientSpace → ℝ)
  map_add' := by
    intro u v
    funext A
    classical
    have hu := finite_nonzero_coeffs hloc u.2
    have hv := finite_nonzero_coeffs hloc v.2
    let Q : Finset (ElementaryPlaquette (spacingAt L K)) := hu.toFinset ∪ hv.toFinset
    have hQu : ∀ q : ElementaryPlaquette (spacingAt L K),
        (u : AmbientSpace → ℝ) q.center ≠ 0 → q ∈ Q :=
      fun q h => Finset.mem_union_left _ (hu.mem_toFinset.mpr h)
    have hQv : ∀ q : ElementaryPlaquette (spacingAt L K),
        (v : AmbientSpace → ℝ) q.center ≠ 0 → q ∈ Q :=
      fun q h => Finset.mem_union_right _ (hv.mem_toFinset.mpr h)
    have hQuv : ∀ q : ElementaryPlaquette (spacingAt L K),
        ((u + v : boundedCompactlySupportedSubmodule) : AmbientSpace → ℝ) q.center ≠ 0 →
          q ∈ Q := fun q h => by
      by_cases h₁ : (u : AmbientSpace → ℝ) q.center = 0
      · refine hQv q fun h₂ => h ?_
        simp [h₁, h₂]
      · exact hQu q h₁
    rw [Pi.add_apply, smearedObservable_eq_finsetSum _ Q hQuv,
      smearedObservable_eq_finsetSum _ Q hQu, smearedObservable_eq_finsetSum _ Q hQv,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [mul_add]
  map_smul' := by
    intro t u
    funext A
    classical
    have hu := finite_nonzero_coeffs hloc u.2
    have hQu : ∀ q : ElementaryPlaquette (spacingAt L K), (u : AmbientSpace → ℝ) q.center ≠ 0 →
        q ∈ hu.toFinset := fun q h => hu.mem_toFinset.mpr h
    have hQt : ∀ q : ElementaryPlaquette (spacingAt L K),
        ((t • u : boundedCompactlySupportedSubmodule) : AmbientSpace → ℝ) q.center ≠ 0 →
          q ∈ hu.toFinset :=
      fun q h => hQu q fun h₁ => h (by simp [h₁])
    rw [RingHom.id_apply, Pi.smul_apply, smearedObservable_eq_finsetSum _ _ hQt,
      smearedObservable_eq_finsetSum _ _ hQu, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
theorem coe_comp_update {m : ℕ} (u : Fin m → boundedCompactlySupportedSubmodule) (i : Fin m)
    (w : boundedCompactlySupportedSubmodule) :
    (fun k => ((Function.update u i w k : boundedCompactlySupportedSubmodule) :
      AmbientSpace → ℝ)) =
      Function.update (fun k => (u k : AmbientSpace → ℝ)) i (w : AmbientSpace → ℝ) := by
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [h]
theorem faceEnergy_bounded_and_locallyFinite (hF : FaceEnergyBoundedAndFacesLocallyFinite)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (μ : Measure (FieldsAt L K)) [IsProbabilityMeasure μ] :
    (∀ q : ElementaryPlaquette (spacingAt L K), Probability.IsBoundedRealRV
      (fun A : FieldsAt L K => faceEnergy A q)) ∧
    ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {q : ElementaryPlaquette (spacingAt L K) | q.center ∈ S}.Finite := by
  obtain ⟨⟨-, hq⟩, hloc⟩ := hF ⟨L, hL, ⟨K, hK⟩, 1⟩ μ (by assumption)
  exact ⟨fun q => (hq q).1, hloc⟩
theorem wellDefined_of_probability (hE : Probability.ExpectationBasicProperties)
    (hC : Cumulants.LinearMapCumulantProperties)
    (hM : RandomTuple.TupleLaplaceLog.LaplaceAndLogTheorem)
    (hF : FaceEnergyBoundedAndFacesLocallyFinite)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (μ : Measure (FieldsAt L K)) [IsProbabilityMeasure μ] (m : ℕ) (hm : 1 ≤ m) :
    TruncatedCorrelationWellDefined μ m := by
  classical
  obtain ⟨hq, hloc⟩ := faceEnergy_bounded_and_locallyFinite hF hL hK μ
  have hbd : ∀ u ∈ boundedCompactlySupported,
      Probability.IsBoundedRealRV (smearedObservable L K u) :=
    fun u hu => smearedObservable_isBoundedRealRV hE μ hq u
      (finite_nonzero_coeffs hloc hu).toFinset
      fun q h => (finite_nonzero_coeffs hloc hu).mem_toFinset.mpr h
  obtain ⟨hlin, -, -⟩ := hC (FieldsAt L K) μ boundedCompactlySupportedSubmodule
    (smearedObservableLinearMap hloc) fun u => hbd u u.2
  obtain ⟨him, hperm, hadd, hsmul⟩ := hlin m hm
  have hcoe : ∀ w : Fin m → boundedCompactlySupportedSubmodule,
      truncatedCorrelation μ (fun k => (w k : AmbientSpace → ℝ)) =
        Cumulants.linearMapCumulant μ (smearedObservableLinearMap hloc) w := fun _ => rfl
  refine ⟨fun u hu => finite_nonzero_coeffs hloc hu, hbd, fun u hu => ?_, fun u _ => rfl,
    fun u hu => him fun i => ⟨u i, hu i⟩, fun u hu σ => hperm (fun i => ⟨u i, hu i⟩) σ,
    fun u hu l v v' β β' hv hv' => ?_⟩
  · exact ((hM (FieldsAt L K) μ m (fun i => smearedObservable L K (u i)) hm
      fun i => hbd _ (hu i)).2.1).formed
  · let u' : Fin m → boundedCompactlySupportedSubmodule := fun i => ⟨u i, hu i⟩
    let V : boundedCompactlySupportedSubmodule := ⟨v, hv⟩
    let V' : boundedCompactlySupportedSubmodule := ⟨v', hv'⟩
    have hu' : (fun k => (u' k : AmbientSpace → ℝ)) = u := rfl
    have key := hadd u' l (β • V) (β' • V')
    rw [hsmul u' l β V, hsmul u' l β' V', ← hcoe, ← hcoe, ← hcoe, coe_comp_update,
      coe_comp_update, coe_comp_update, hu'] at key
    exact key
def truncatedRealPartFamily (μ : Measure (FieldsAt L K))
    (hwd : ∀ m : ℕ, 1 ≤ m → TruncatedCorrelationWellDefined μ m) :
    RadialFunctionalFamily ⊤ where
  radius_pos := by simp
  eval _ _ X := (truncatedCorrelation μ X.1).re
  perm_invariant m hm := by
    refine ⟨fun u hu σ => ⟨⟨hu.1.pos_arity, fun i => hu.1.lipschitz (σ i),
      fun i => hu.1.hasCompactSupport (σ i),
      fun i j hij => hu.1.pairwise_disjoint (σ.injective.ne hij)⟩, fun i => hu.2 (σ i)⟩,
      fun u σ => ?_⟩
    exact congrArg Complex.re ((hwd m (by omega)).perm_invariant u.1
      (fun i => apply_mem_boundedCompactlySupported u.2.1 i) σ)
  slot_linear m hm := by
    intro l β β' u u' hsame hmem
    have hlin := (hwd m (by omega)).slot_linear u.1
      (fun i => apply_mem_boundedCompactlySupported u.2.1 i) l (u.1 l) (u'.1 l) β β'
      (apply_mem_boundedCompactlySupported u.2.1 l)
      (apply_mem_boundedCompactlySupported u'.2.1 l)
    have hupd : Function.update u.1 l (u'.1 l) = u'.1 := by
      funext i
      by_cases h : i = l
      · subst h
        simp
      · simp [h, hsame i h]
    rw [Function.update_eq_self, hupd] at hlin
    have hre := congrArg Complex.re hlin
    simpa only [Complex.add_re, Complex.re_ofReal_mul] using hre
theorem truncatedRealPartFamily_isTruncatedFamilyOf (μ : Measure (FieldsAt L K))
    (hwd : ∀ m : ℕ, 1 ≤ m → TruncatedCorrelationWellDefined μ m) :
    (truncatedRealPartFamily μ hwd).IsTruncatedFamilyOf μ := by
  intro m hm X
  have him := (hwd m (by omega)).im_eq_zero X.1
    (fun i => apply_mem_boundedCompactlySupported X.2.1 i)
  exact Complex.ext (by simp [truncatedRealPartFamily, truncatedCorrelationFamily,
    separatedTruncatedCorrelation]) (by simpa [truncatedRealPartFamily,
    truncatedCorrelationFamily, separatedTruncatedCorrelation] using him.symm)
theorem separatedLipschitzSetIn_top (m : ℕ) :
    separatedLipschitzSetIn m ⊤ = separatedLipschitzSet m := by
  ext X
  simp [separatedLipschitzSetIn, originBall_top]
end ProbabilityMeasureCorrelations
open ProbabilityMeasureCorrelations in
theorem truncatedCorrelationsOfProbabilityMeasures_holds
    (hE : Probability.ExpectationBasicProperties)
    (hC : Cumulants.LinearMapCumulantProperties)
    (hM : RandomTuple.TupleLaplaceLog.LaplaceAndLogTheorem)
    (hF : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite) :
    TruncatedCorrelationsOfProbabilityMeasures := by
  intro L hL
  have hwd : ∀ K : ℕ, 0 < K → ∀ μ ∈ fieldProbabilityMeasures L K, ∀ m : ℕ, 1 ≤ m →
      TruncatedCorrelationWellDefined μ m := fun K hK μ hμ m hm =>
    haveI : IsProbabilityMeasure μ := hμ
    wellDefined_of_probability hE hC hM hF hL hK μ m hm
  refine ⟨⟨boundedCompactlySupportedSubmodule, rfl⟩, hwd, fun J₀ _ _ K μ hK hμ =>
    ⟨fun j => ?_, separatedLipschitzSetIn_top, tendsto_const_nhds⟩⟩
  exact ⟨_, truncatedRealPartFamily_isTruncatedFamilyOf (μ j) (hwd (K j) (hK j) (μ j) (hμ j))⟩
end YangMills.Construction.SeparatedFamilies
