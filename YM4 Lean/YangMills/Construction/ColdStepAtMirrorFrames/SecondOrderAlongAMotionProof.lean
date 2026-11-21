import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAlongAMotion
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages Estimates
namespace ColdStepAtMirrorFrames
section bilinear
theorem update_pair_zero {V : Type} (x y z : V) : Function.update ![x, y] (0 : Fin 2) z = ![z, y] := by
  funext i
  fin_cases i <;> simp
theorem update_pair_one {V : Type} (x y z : V) : Function.update ![x, y] (1 : Fin 2) z = ![x, z] := by
  funext i
  fin_cases i <;> simp
theorem bilinear_apply_sum_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (r : ι → ℝ) (P : ι → V) (s : κ → ℝ) (Q : κ → V) :
    M ![∑ i, r i • P i, ∑ k, s k • Q k] = ∑ i, ∑ k, M ![P i, Q k] * r i * s k := by
  have h1 : ∀ y : V, M ![∑ i, r i • P i, y] = ∑ i, r i * M ![P i, y] := by
    intro y
    have e := M.toMultilinearMap.map_update_sum (m := ![0, y]) (i := (0 : Fin 2)) Finset.univ (fun i => r i • P i)
    simp only [ContinuousMultilinearMap.coe_coe, update_pair_zero] at e
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e2 := M.map_update_smul ![0, y] (0 : Fin 2) (r i) (P i)
    simpa only [update_pair_zero, smul_eq_mul] using e2
  have h2 : ∀ x : V, M ![x, ∑ k, s k • Q k] = ∑ k, s k * M ![x, Q k] := by
    intro x
    have e := M.toMultilinearMap.map_update_sum (m := ![x, 0]) (i := (1 : Fin 2)) Finset.univ (fun k => s k • Q k)
    simp only [ContinuousMultilinearMap.coe_coe, update_pair_one] at e
    rw [e]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e2 := M.map_update_smul ![x, 0] (1 : Fin 2) (s k) (Q k)
    simpa only [update_pair_one, smul_eq_mul] using e2
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end bilinear
theorem secondOrderAlongMotionFormula_proof (hJ : FormCompositionJet)
    (hC : ThirdOrderChainRuleVectorValued) : SecondOrderAlongMotionFormula := by
  intro F j T G W α u₀ u₁ X₀ X₁ hT hG h1 h0 hα hp0 hp1
  classical
  obtain ⟨hJC, hJe, hJb⟩ := hJ ℝ F j T G W hG
  set A : (Fin 2 → ℝ) → (↥T → imaginaryQuaternions) := fun τ b => α τ b.1.1 b.1.2 with hA
  have hA0 : A 0 = 0 := by
    funext b
    exact h0 _ _
  have hAC : ContDiffAt ℝ 3 A 0 := contDiffAt_pi.2 fun b => hα _ _
  have hext : ∀ τ, extendByZero (A τ) = α τ := by
    intro τ
    funext y i
    unfold extendByZero
    rw [dif_pos (hT (y, i))]
  have hcomp : (fun τ => G (leftTranslate (α τ) W)) = formComposition T G W ∘ A := by
    funext τ
    simp only [Function.comp, formComposition, hext]
  have hC' := hC (formComposition T G W) A 0 (by rw [hA0]; exact hJC) hAC
  have hd2 := hC'.2.2.1 (Pi.single 0 1) (Pi.single 1 1)
  have hpart : ∀ (l : Fin 2) (b : ↥T), iteratedFDeriv ℝ 1 A 0 ![Pi.single l 1] b = motionComponent α ![l] b.1.1 b.1.2 := by
    intro l b
    have hd : HasFDerivAt A (fderiv ℝ A 0) 0 := (hAC.differentiableAt (by norm_num)).hasFDerivAt
    have hb := (hasFDerivAt_pi'.1 hd) b
    unfold motionComponent
    rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
    have e : fderiv ℝ (fun τ => α τ b.1.1 b.1.2) 0 = (ContinuousLinearMap.proj b).comp (fderiv ℝ A 0) := hb.fderiv
    rw [e]
    simp
  have hZ0 : iteratedFDeriv ℝ 1 A 0 ![Pi.single 0 1] = ∑ b : ↥T, u₀ b.1.1 b.1.2 • singleBondForm b X₀ := by
    funext b'
    rw [hpart, hp0]
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single b']
    · simp [singleBondForm]
    · intro b _ hne
      simp [singleBondForm, hne.symm]
    · simp
  have hZ1 : iteratedFDeriv ℝ 1 A 0 ![Pi.single 1 1] = ∑ b : ↥T, u₁ b.1.1 b.1.2 • singleBondForm b X₁ := by
    funext b'
    rw [hpart, hp1]
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single b']
    · simp [singleBondForm]
    · intro b _ hne
      simp [singleBondForm, hne.symm]
    · simp
  have hF1 : ∀ Z : Fin 1 → ↥T → imaginaryQuaternions, iteratedFDeriv ℝ 1 (formComposition T G W) 0 Z = 0 := by
    intro Z
    have hb := hJb 1 (fun _ => 0) (by norm_num) (fun _ => le_rfl) (fun c X hX => by
      rw [h1 _ X hX]; simp) Z
    simp only [zero_mul, Finset.sum_const_zero] at hb
    exact norm_le_zero_iff.1 hb
  rw [hcomp, hd2, hA0, hF1, add_zero, hZ0, hZ1, bilinear_apply_sum_sum]
  have hent : ∀ b k : ↥T, iteratedFDeriv ℝ 2 (formComposition T G W) 0 ![singleBondForm b X₀, singleBondForm k X₁] =
      bondDeriv G W ![b.1, k.1] ![X₀, X₁] := by
    intro b k
    have he := hJe 2 ![b, k] ![X₀, X₁] (by norm_num)
    have e1 : (fun l => singleBondForm ((![b, k] : Fin 2 → ↥T) l) ((![X₀, X₁] : Fin 2 → imaginaryQuaternions) l)) =
        ![singleBondForm b X₀, singleBondForm k X₁] := by
      funext l
      fin_cases l <;> rfl
    have e2 : (fun l => ((![b, k] : Fin 2 → ↥T) l).1) = ![b.1, k.1] := by
      funext l
      fin_cases l <;> rfl
    rw [e1, e2] at he
    exact he
  simp only [hent]
  rw [← Finset.sum_coe_sort T (fun b => ∑ b' ∈ T, bondDeriv G W ![b, b'] ![X₀, X₁] * u₀ b.1 b.2 * u₁ b'.1 b'.2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_coe_sort T (fun b' => bondDeriv G W ![b.1, b'] ![X₀, X₁] * u₀ b.1.1 b.1.2 * u₁ b'.1 b'.2)]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
