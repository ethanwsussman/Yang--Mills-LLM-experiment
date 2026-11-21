import YangMills.Construction.EuclideanFunctionals.FiniteMeasureAtNonnegativeEnergiesDeterminedByItsTransform
import Mathlib
set_option autoImplicit false
open MeasureTheory BoundedContinuousFunction
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.FiniteMeasureUniqueness
abbrev NonnegEnergyPoint : Type := ↥(nonnegEnergySet.1)
theorem continuous_energyCoord : Continuous energyCoord :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).continuous
theorem continuous_momCoord (k : Fin 3) : Continuous (momCoord k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k.succ).continuous
theorem isClosed_nonnegEnergySet : IsClosed (nonnegEnergySet.1) :=
  isClosed_le continuous_const continuous_energyCoord
instance completeSpace_nonnegEnergyPoint : CompleteSpace NonnegEnergyPoint :=
  isClosed_nonnegEnergySet.completeSpace_coe
theorem continuous_laplaceFourierKernel (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)) :
    Continuous (laplaceFourierKernel n u) := by
  have hE : Continuous fun q : MomSpace => ((energyCoord q : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_energyCoord
  have hS : Continuous fun q : MomSpace => ∑ k : Fin 3, u k * momCoord k q :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_momCoord k)
  have hC : Continuous fun q : MomSpace => ((∑ k : Fin 3, u k * momCoord k q : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hS
  unfold laplaceFourierKernel
  exact Complex.continuous_exp.comp ((continuous_const.mul hE).add (continuous_const.mul hC))
theorem norm_laplaceFourierKernel_le (n : ℕ) (u : EuclideanSpace ℝ (Fin 3))
    (z : NonnegEnergyPoint) : ‖laplaceFourierKernel n u z‖ ≤ 1 := by
  have hz : 0 ≤ energyCoord (z : MomSpace) := z.2
  rw [laplaceFourierKernel, Complex.norm_exp]
  refine Real.exp_le_one_iff.2 ?_
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.neg_im, Complex.natCast_im, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have : 0 ≤ (n : ℝ) * energyCoord (z : MomSpace) := mul_nonneg (Nat.cast_nonneg n) hz
  simp only [mul_zero, sub_zero, neg_zero, zero_mul, add_zero]
  linarith
theorem laplaceFourierKernel_add (n m : ℕ) (u w : EuclideanSpace ℝ (Fin 3)) (q : MomSpace) :
    laplaceFourierKernel (n + m) (u + w) q =
      laplaceFourierKernel n u q * laplaceFourierKernel m w q := by
  simp only [laplaceFourierKernel, ← Complex.exp_add]
  congr 1
  have : (∑ k : Fin 3, (u + w) k * momCoord k q) =
      (∑ k : Fin 3, u k * momCoord k q) + ∑ k : Fin 3, w k * momCoord k q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp [add_mul]
  rw [this]
  push_cast
  ring
theorem conj_laplaceFourierKernel (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)) (q : MomSpace) :
    conj (laplaceFourierKernel n u q) = laplaceFourierKernel n (-u) q := by
  simp only [laplaceFourierKernel, ← Complex.exp_conj]
  congr 1
  have : (∑ k : Fin 3, (-u) k * momCoord k q) = -∑ k : Fin 3, u k * momCoord k q := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp
  rw [this]
  simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_natCast]
  push_cast
  ring
def kernelBCF (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)) : NonnegEnergyPoint →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => laplaceFourierKernel n u z)
    ((continuous_laplaceFourierKernel n u).comp continuous_subtype_val) 1
    (norm_laplaceFourierKernel_le n u)
@[simp] theorem kernelBCF_apply (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)) (z : NonnegEnergyPoint) :
    kernelBCF n u z = laplaceFourierKernel n u z := rfl
theorem laplaceFourierKernel_zero_zero (q : MomSpace) : laplaceFourierKernel 0 0 q = 1 := by
  simp [laplaceFourierKernel]
def kernelSubmonoid : Submonoid (NonnegEnergyPoint →ᵇ ℂ) where
  carrier := Set.range fun nu : ℕ × EuclideanSpace ℝ (Fin 3) => kernelBCF nu.1 nu.2
  mul_mem' := by
    rintro _ _ ⟨⟨n, u⟩, rfl⟩ ⟨⟨m, w⟩, rfl⟩
    refine ⟨⟨n + m, u + w⟩, ?_⟩
    ext z
    exact laplaceFourierKernel_add n m u w z
  one_mem' := by
    refine ⟨⟨0, 0⟩, ?_⟩
    ext z
    exact laplaceFourierKernel_zero_zero z
theorem star_mem_adjoin_kernelSubmonoid {f : NonnegEnergyPoint →ᵇ ℂ}
    (hf : f ∈ Algebra.adjoin ℂ (kernelSubmonoid : Set (NonnegEnergyPoint →ᵇ ℂ))) :
    star f ∈ Algebra.adjoin ℂ (kernelSubmonoid : Set (NonnegEnergyPoint →ᵇ ℂ)) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨⟨n, u⟩, rfl⟩ := hf
    refine Algebra.subset_adjoin ⟨⟨n, -u⟩, ?_⟩
    ext z
    exact (conj_laplaceFourierKernel n u z).symm
  | algebraMap r =>
    rw [← algebraMap_star_comm]
    exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb =>
    rw [star_add]
    exact add_mem ha hb
  | mul a b _ _ ha hb =>
    rw [star_mul]
    exact mul_mem hb ha
def kernelStarSubalgebra : StarSubalgebra ℂ (NonnegEnergyPoint →ᵇ ℂ) :=
  { Algebra.adjoin ℂ (kernelSubmonoid : Set (NonnegEnergyPoint →ᵇ ℂ)) with
    star_mem' := star_mem_adjoin_kernelSubmonoid }
theorem laplaceFourierKernel_one_zero (q : MomSpace) :
    laplaceFourierKernel 1 0 q = ((Real.exp (-energyCoord q) : ℝ) : ℂ) := by
  simp [laplaceFourierKernel]
theorem laplaceFourierKernel_zero_single (k : Fin 3) (s : ℝ) (q : MomSpace) :
    laplaceFourierKernel 0 (EuclideanSpace.single k s) q =
      Complex.exp (Complex.I * ((s * momCoord k q : ℝ) : ℂ)) := by
  have : (∑ i : Fin 3, (EuclideanSpace.single k s : EuclideanSpace ℝ (Fin 3)) i * momCoord i q) =
      s * momCoord k q := by
    simp [ite_mul]
  simp only [laplaceFourierKernel, this]
  simp
theorem exists_laplaceFourierKernel_ne {a b : NonnegEnergyPoint} (hab : a ≠ b) :
    ∃ (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)),
      laplaceFourierKernel n u (a : MomSpace) ≠ laplaceFourierKernel n u (b : MomSpace) := by
  by_contra hnone
  push Not at hnone
  apply hab
  apply Subtype.ext
  have hEn : energyCoord (a : MomSpace) = energyCoord (b : MomSpace) := by
    have hab1 := hnone 1 0
    rw [laplaceFourierKernel_one_zero, laplaceFourierKernel_one_zero] at hab1
    exact neg_injective (Real.exp_injective (Complex.ofReal_injective hab1))
  have hMo : ∀ k : Fin 3, momCoord k (a : MomSpace) = momCoord k (b : MomSpace) := by
    intro k
    by_contra hne
    have hdiff : momCoord k (a : MomSpace) - momCoord k (b : MomSpace) ≠ 0 :=
      sub_ne_zero.2 hne
    have hab2 := hnone 0 (EuclideanSpace.single k
      (Real.pi / (momCoord k (a : MomSpace) - momCoord k (b : MomSpace))))
    rw [laplaceFourierKernel_zero_single, laplaceFourierKernel_zero_single] at hab2
    have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
      have hrw : (Real.pi : ℂ) * Complex.I =
          Complex.I * (((Real.pi / (momCoord k (a : MomSpace) -
              momCoord k (b : MomSpace))) * momCoord k (a : MomSpace) : ℝ) : ℂ) -
            Complex.I * (((Real.pi / (momCoord k (a : MomSpace) -
              momCoord k (b : MomSpace))) * momCoord k (b : MomSpace) : ℝ) : ℂ) := by
        rw [← mul_sub, ← Complex.ofReal_sub, ← mul_sub, div_mul_cancel₀ _ hdiff, mul_comm]
      rw [hrw, Complex.exp_sub, hab2, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_pi_mul_I] at hpi
    norm_num at hpi
  ext i
  refine Fin.cases hEn (fun k => hMo k) i
theorem kernelStarSubalgebra_separatesPoints :
    (kernelStarSubalgebra.map (toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro a b hab
  obtain ⟨n, u, hne⟩ := exists_laplaceFourierKernel_ne hab
  exact ⟨kernelBCF n u,
    ⟨_, ⟨kernelBCF n u, Algebra.subset_adjoin ⟨⟨n, u⟩, rfl⟩, rfl⟩, rfl⟩, hne⟩
theorem integral_eq_of_mem_span_kernels {ν ν' : Measure NonnegEnergyPoint} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν']
    (hker : ∀ (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)),
      ∫ z, kernelBCF n u z ∂ν = ∫ z, kernelBCF n u z ∂ν')
    {f : NonnegEnergyPoint →ᵇ ℂ}
    (hf : f ∈ Submodule.span ℂ (kernelSubmonoid : Set (NonnegEnergyPoint →ᵇ ℂ))) :
    ∫ z, f z ∂ν = ∫ z, f z ∂ν' := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨n, u⟩, rfl⟩ := hf
    exact hker n u
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [integral_add (a.integrable ν) (b.integrable ν),
      integral_add (a.integrable ν') (b.integrable ν'), ha, hb]
  | smul c a _ ha =>
    simp only [BoundedContinuousFunction.coe_smul]
    rw [integral_smul, integral_smul, ha]
instance isFiniteMeasure_comap_val (μ : Measure MomSpace) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap (Subtype.val : NonnegEnergyPoint → MomSpace)) :=
  ⟨by
    rw [(MeasurableEmbedding.subtype_coe nonnegEnergySet.2).comap_apply]
    exact measure_lt_top _ _⟩
theorem restrict_nonnegEnergySet_eq_self (ν : Measure MomSpace) (hν : ν negEnergySet.1 = 0) :
    ν.restrict nonnegEnergySet.1 = ν := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have hcompl : {q : MomSpace | ¬ q ∈ nonnegEnergySet.1} = negEnergySet.1 := by
    ext q
    simp [nonnegEnergySet, negEnergySet]
  rw [hcompl]
  exact hν
theorem transformDeterminesMeasure : TransformDeterminesMeasure := by
  intro μ μ' _ _ hμ hμ' htr
  have hker : ∀ (n : ℕ) (u : EuclideanSpace ℝ (Fin 3)),
      ∫ z, kernelBCF n u z ∂(μ.comap (Subtype.val : NonnegEnergyPoint → MomSpace)) =
        ∫ z, kernelBCF n u z ∂(μ'.comap (Subtype.val : NonnegEnergyPoint → MomSpace)) := by
    intro n u
    simp only [kernelBCF_apply]
    rw [integral_subtype_comap nonnegEnergySet.2 (laplaceFourierKernel n u),
      integral_subtype_comap nonnegEnergySet.2 (laplaceFourierKernel n u)]
    exact htr n u
  have hcomap : μ.comap (Subtype.val : NonnegEnergyPoint → MomSpace) =
      μ'.comap (Subtype.val : NonnegEnergyPoint → MomSpace) := by
    refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      kernelStarSubalgebra_separatesPoints fun f hf => integral_eq_of_mem_span_kernels hker ?_
    have hf' : f ∈ Subalgebra.toSubmodule
        (Algebra.adjoin ℂ (kernelSubmonoid : Set (NonnegEnergyPoint →ᵇ ℂ))) := hf
    rwa [Algebra.adjoin_eq_span, Submonoid.closure_eq] at hf'
  rw [← restrict_nonnegEnergySet_eq_self μ hμ, ← restrict_nonnegEnergySet_eq_self μ' hμ',
    ← map_comap_subtype_coe nonnegEnergySet.2 μ,
    ← map_comap_subtype_coe nonnegEnergySet.2 μ', hcomap]
end YangMills.Construction.EuclideanFunctionals.FiniteMeasureUniqueness
