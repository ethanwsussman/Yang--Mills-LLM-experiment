import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Matrices.MapsPreservingTheProductOfHaarMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.HaarPiInvariance
theorem twoSided_map_preserves {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H)
    (hMul : ∀ a b : H, Measure.map (fun x : H => a * x * b) μ = μ)
    (hInv : Measure.map (fun x : H => x⁻¹) μ = μ) {f : H → H}
    (hf : ∃ a b : H, (∀ x, f x = a * x * b) ∨ (∀ x, f x = a * x⁻¹ * b)) :
    Continuous f ∧ (∃ g : H → H, Continuous g ∧ Function.LeftInverse g f ∧
      Function.RightInverse g f) ∧ Measure.map f μ = μ := by
  obtain ⟨a, b, h | h⟩ := hf
  · have hEq : f = fun x => a * x * b := funext h
    subst hEq
    refine ⟨by fun_prop, ⟨fun x => a⁻¹ * x * b⁻¹, by fun_prop, ?_, ?_⟩, hMul a b⟩
    · intro x
      simp [mul_assoc]
    · intro x
      simp [mul_assoc]
  · have hEq : f = fun x => a * x⁻¹ * b := funext h
    subst hEq
    refine ⟨by fun_prop, ⟨fun x => b * x⁻¹ * a, by fun_prop, ?_, ?_⟩, ?_⟩
    · intro x
      simp [mul_assoc]
    · intro x
      simp [mul_assoc]
    · have hComp : (fun x : H => a * x⁻¹ * b) = (fun x : H => a * x * b) ∘ fun x : H => x⁻¹ :=
        rfl
      have hMeas1 : Measurable fun x : H => a * x * b :=
        (by fun_prop : Continuous fun x : H => a * x * b).measurable
      have hMeas2 : Measurable fun x : H => x⁻¹ :=
        (by fun_prop : Continuous fun x : H => x⁻¹).measurable
      rw [hComp, ← Measure.map_map hMeas1 hMeas2, hInv, hMul a b]
theorem statement_holds (hH : HaarExpChartProperties) : statement := by
  intro I _ σ f hf
  have hEach := fun i => twoSided_map_preserves haarProb hH.2.2.1 hH.2.2.2 (hf i)
  have hCont : ∀ i, Continuous (f i) := fun i => (hEach i).1
  have hPres : ∀ i, Measure.map (f i) haarProb = haarProb := fun i => (hEach i).2.2
  choose g hg hLeft hRight using fun i => (hEach i).2.1
  have hMapCont : Continuous (permuteThenApply σ f) :=
    continuous_pi fun i => (hCont i).comp (continuous_apply (σ i))
  have hMapMeas : Measurable (permuteThenApply σ f) :=
    measurable_pi_lambda _ fun i =>
      (hCont i).measurable.comp (measurable_pi_apply (σ i))
  refine ⟨?_, hMapMeas, ?_⟩
  · refine isHomeomorph_iff_exists_inverse.2 ⟨hMapCont,
      fun V m => g (σ.symm m) (V (σ.symm m)), ?_, ?_, ?_⟩
    · intro U
      funext m
      simpa [permuteThenApply] using hLeft (σ.symm m) (U m)
    · intro V
      funext i
      simpa [permuteThenApply] using hRight i (V i)
    · exact continuous_pi fun m => (hg (σ.symm m)).comp (continuous_apply (σ.symm m))
  · refine (Measures.Pushforward.isInvariant_iff_pushforward_eq _ _ hMapMeas).2 ?_
    change Measure.map (permuteThenApply σ f) (Measure.infinitePi fun _ : I => haarProb) =
      Measure.infinitePi fun _ : I => haarProb
    refine Measure.eq_infinitePi _ fun s t ht => ?_
    have hFactor : ∀ i, haarProb (f i ⁻¹' t i) = haarProb (t i) := by
      intro i
      rw [← Measure.map_apply (hCont i).measurable (ht i), hPres i]
    have hPre : permuteThenApply σ f ⁻¹' Set.pi s t =
        Set.pi (s.map σ.toEmbedding) fun m => f (σ.symm m) ⁻¹' t (σ.symm m) := by
      ext U
      simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
        permuteThenApply]
      constructor
      · rintro h m ⟨i, hi, rfl⟩
        simpa using h i hi
      · intro h i hi
        simpa using h (σ i) ⟨i, hi, rfl⟩
    rw [Measure.map_apply hMapMeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hPre,
      Measure.infinitePi_pi _ fun m _ => (hCont _).measurable (ht _), Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ => ?_
    simpa using hFactor i
end YangMills.Construction.Matrices.ComplexMatrix2.HaarPiInvariance
