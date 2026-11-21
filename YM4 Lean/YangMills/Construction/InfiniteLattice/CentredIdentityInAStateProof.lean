import YangMills.Construction.Cumulants.CumulantsOfALinearMapIntoBoundedRandomVariables
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.InfiniteLattice.FaceEnergyUnderProbability
import YangMills.Construction.Probability.ExpectationBasicProperties
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CenteredIdentity
variable {a : ℝ}
theorem finite_support_on_centers
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {p : ElementaryPlaquette a | p.center ∈ S}.Finite)
    {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
  (hfin _ hf.2.2.isCompact.isBounded).subset fun _ hp => subset_tsupport f hp
theorem smearedEnergy_eq_finset_sum (f : AmbientSpace → ℝ) (P : Finset (ElementaryPlaquette a))
    (hP : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P) (U : GaugeField a) :
    (smearedEnergy f U : ℝ) = ∑ p ∈ P, faceEnergy U p * f p.center := by
  unfold smearedEnergy
  simp only [smul_eq_mul]
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  refine Finset.mem_coe.mpr (hP p fun h => ?_)
  exact hp (by simp [h])
theorem smearedEnergy_isBoundedRealRV
    (hE : YangMills.Construction.Probability.ExpectationBasicProperties)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (hface : ∀ p : ElementaryPlaquette a, YangMills.Construction.Probability.IsBoundedRealRV
      (fun U : GaugeField a => faceEnergy U p))
    (f : AmbientSpace → ℝ) (P : Finset (ElementaryPlaquette a))
    (hP : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P) :
    YangMills.Construction.Probability.IsBoundedRealRV (smearedEnergy f : GaugeField a → ℝ) := by
  obtain ⟨V, hV⟩ := (hE (GaugeField a) ν).1.1
  have mem : ∀ x : GaugeField a → ℝ,
      x ∈ V ↔ YangMills.Construction.Probability.IsBoundedRealRV x := fun x => by
    rw [← SetLike.mem_coe, hV]
    rfl
  have e : (smearedEnergy f : GaugeField a → ℝ) =
      ∑ p ∈ P, f p.center • fun U : GaugeField a => faceEnergy U p := by
    funext U
    rw [smearedEnergy_eq_finset_sum f P hP U, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [mul_comm]
  rw [← mem, e]
  exact V.sum_mem fun p _ => V.smul_mem _ ((mem _).2 (hface p))
def testFunctionSubmodule : Submodule ℝ (AmbientSpace → ℝ) where
  carrier := compactTestFunctions
  add_mem' := by
    rintro f g ⟨hf, ⟨C, hC⟩, hfc⟩ ⟨hg, ⟨D, hD⟩, hgc⟩
    exact ⟨hf.add hg, ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩,
      hfc.add hgc⟩
  zero_mem' := ⟨measurable_const, ⟨0, fun x => by simp⟩, HasCompactSupport.zero⟩
  smul_mem' := by
    rintro c f ⟨hf, ⟨C, hC⟩, hfc⟩
    refine ⟨hf.const_smul c, ⟨‖c‖ * C, fun x => ?_⟩,
      hfc.mono (Function.support_const_smul_subset c f)⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
def smearingLinearMap
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {p : ElementaryPlaquette a | p.center ∈ S}.Finite) :
    testFunctionSubmodule →ₗ[ℝ] (GaugeField a → ℝ) where
  toFun f := smearedEnergy (f : AmbientSpace → ℝ)
  map_add' := by
    intro f g
    funext U
    classical
    have hf := finite_support_on_centers hfin f.2
    have hg := finite_support_on_centers hfin g.2
    let P : Finset (ElementaryPlaquette a) := hf.toFinset ∪ hg.toFinset
    have hPf : ∀ p : ElementaryPlaquette a, (f : AmbientSpace → ℝ) p.center ≠ 0 → p ∈ P :=
      fun p h => Finset.mem_union_left _ (hf.mem_toFinset.mpr h)
    have hPg : ∀ p : ElementaryPlaquette a, (g : AmbientSpace → ℝ) p.center ≠ 0 → p ∈ P :=
      fun p h => Finset.mem_union_right _ (hg.mem_toFinset.mpr h)
    have hPfg : ∀ p : ElementaryPlaquette a,
        ((f + g : testFunctionSubmodule) : AmbientSpace → ℝ) p.center ≠ 0 → p ∈ P :=
      fun p h => by
        by_cases h₁ : (f : AmbientSpace → ℝ) p.center = 0
        · refine hPg p fun h₂ => h ?_
          simp [h₁, h₂]
        · exact hPf p h₁
    rw [Pi.add_apply, smearedEnergy_eq_finset_sum _ P hPfg, smearedEnergy_eq_finset_sum _ P hPf,
      smearedEnergy_eq_finset_sum _ P hPg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [mul_add]
  map_smul' := by
    intro c f
    funext U
    classical
    have hf := finite_support_on_centers hfin f.2
    have hPf : ∀ p : ElementaryPlaquette a, (f : AmbientSpace → ℝ) p.center ≠ 0 →
        p ∈ hf.toFinset := fun p h => hf.mem_toFinset.mpr h
    have hPc : ∀ p : ElementaryPlaquette a,
        ((c • f : testFunctionSubmodule) : AmbientSpace → ℝ) p.center ≠ 0 →
        p ∈ hf.toFinset := fun p h => hPf p fun h₁ => h (by simp [h₁])
    rw [RingHom.id_apply, Pi.smul_apply, smearedEnergy_eq_finset_sum _ _ hPc,
      smearedEnergy_eq_finset_sum _ _ hPf, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
theorem coe_update_testFunctions {n : ℕ} (f : Fin n → testFunctionSubmodule) (i : Fin n)
    (x : testFunctionSubmodule) :
    (fun k => ((Function.update f i x k : testFunctionSubmodule) : AmbientSpace → ℝ)) =
      Function.update (fun k => (f k : AmbientSpace → ℝ)) i (x : AmbientSpace → ℝ) := by
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [h]
theorem holds_at_fixed_mesh
    (hE : YangMills.Construction.Probability.ExpectationBasicProperties)
    (hLin : YangMills.Construction.Cumulants.LinearMapCumulantProperties)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (hface : ∀ p : ElementaryPlaquette a, YangMills.Construction.Probability.IsBoundedRealRV
      (fun U : GaugeField a => faceEnergy U p))
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {p : ElementaryPlaquette a | p.center ∈ S}.Finite) :
    ((∀ f : AmbientSpace → ℝ, f ∈ compactTestFunctions → SmearedIsFiniteAndBounded a f) ∧
      TestFunctionsFormSubspaceWithLinearSmearing a) ∧
    (∀ n : ℕ, 2 ≤ n → UrsellIsRealSymmetricMultilinear ν n) ∧
    (∀ (q : ℕ) (h : Fin q → AmbientSpace → ℝ), (∀ l, h l ∈ compactTestFunctions) →
      centeredMoment ν h = ursellPartitionSum ν h) := by
  classical
  have hbd : ∀ f : AmbientSpace → ℝ, f ∈ compactTestFunctions →
      YangMills.Construction.Probability.IsBoundedRealRV
        (smearedEnergy f : GaugeField a → ℝ) :=
    fun f hf => smearedEnergy_isBoundedRealRV hE ν hface f
      (finite_support_on_centers hfin hf).toFinset
      fun p h => (finite_support_on_centers hfin hf).mem_toFinset.mpr h
  have hL := hLin (GaugeField a) ν testFunctionSubmodule (smearingLinearMap hfin)
    fun f => hbd f f.2
  obtain ⟨hn, -, hq⟩ := hL
  have hcoe : ∀ {n : ℕ} (g : Fin n → testFunctionSubmodule),
      ursellFunction ν n (fun k => (g k : AmbientSpace → ℝ)) =
        YangMills.Construction.Cumulants.linearMapCumulant ν (smearingLinearMap hfin) g :=
    fun _ => rfl
  refine ⟨⟨fun f hf => ⟨finite_support_on_centers hfin hf, hbd f hf⟩,
    testFunctionSubmodule, rfl, smearingLinearMap hfin, fun _ => rfl⟩,
    fun n hn2 f hf => ?_, fun q h hh => ?_⟩
  · obtain ⟨hre, hperm, hadd, hsmul⟩ := hn n (by omega)
    let f' : Fin n → testFunctionSubmodule := fun i => ⟨f i, hf i⟩
    have hf' : (fun k => (f' k : AmbientSpace → ℝ)) = f := rfl
    refine ⟨hre f', fun σ => hperm f' σ, fun i g hg => ?_, fun i c => ?_⟩
    · have key := hadd f' i (f' i) ⟨g, hg⟩
      rw [Function.update_eq_self, ← hcoe, ← hcoe, ← hcoe, coe_update_testFunctions,
        coe_update_testFunctions, hf'] at key
      exact key
    · have key := hsmul f' i c (f' i)
      rw [Function.update_eq_self, ← hcoe, ← hcoe, coe_update_testFunctions, hf'] at key
      exact key
  · have key := hq q fun l => ⟨h l, hh l⟩
    unfold ursellPartitionSum
    rw [← YangMills.Construction.SetPartition.singletonFree_eq_nonSingletonPartitions]
    exact key
theorem statement_holds
    (hE : YangMills.Construction.Probability.ExpectationBasicProperties)
    (hLin : YangMills.Construction.Cumulants.LinearMapCumulantProperties)
    (hFaces : FaceEnergyBoundedAndFacesLocallyFinite) : Statement := by
  intro s ν hν
  obtain ⟨⟨-, hface⟩, hfin⟩ := hFaces s ν hν
  exact holds_at_fixed_mesh hE hLin ν (fun p => (hface p).1) hfin
end YangMills.Construction.InfiniteLattice.CenteredIdentity
