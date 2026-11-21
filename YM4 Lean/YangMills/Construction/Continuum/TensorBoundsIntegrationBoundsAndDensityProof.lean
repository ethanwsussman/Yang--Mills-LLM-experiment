import YangMills.Construction.Continuum.CutoffNearTheComplementOfAnOpenSet
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.IntegratingArgumentsOutOfFlatSchwartzFunctions
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.Continuum.TensorProductAndNumberFactorBounds
import YangMills.Construction.Continuum.TensorsOfBumpsInTheNorm
import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinity
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.TestSpaceFacts
variable {n : ℕ}
theorem sub_mem_schwartzSet (hOps : Elementary.SchwartzClosedUnderOps n)
    {u v : PointTuple n → ℂ} (hu : u ∈ schwartzSet n) (hv : v ∈ schwartzSet n) :
    u - v ∈ schwartzSet n := by
  have h := (hOps.1 u hu v hv 1 (-1)).1.1
  have e : Elementary.linComb 1 u (-1) v = u - v := by
    funext x
    simp [Elementary.linComb, sub_eq_add_neg]
  rwa [e] at h
theorem add_mem_schwartzSet (hOps : Elementary.SchwartzClosedUnderOps n)
    {u v : PointTuple n → ℂ} (hu : u ∈ schwartzSet n) (hv : v ∈ schwartzSet n) :
    u + v ∈ schwartzSet n := by
  have h := (hOps.1 u hu v hv 1 1).1.1
  have e : Elementary.linComb 1 u 1 v = u + v := by
    funext x
    simp [Elementary.linComb]
  rwa [e] at h
theorem weightedSeminorm_add_le (hOps : Elementary.SchwartzClosedUnderOps n) {k : ℕ}
    (hk : 0 < k) {u v : PointTuple n → ℂ} (hu : u ∈ schwartzSet n) (hv : v ∈ schwartzSet n) :
    weightedSeminorm k (u + v) ≤ weightedSeminorm k u + weightedSeminorm k v := by
  have h := ((hOps.1 u hu v hv 1 1).2.1 k k hk le_rfl).2.1
  have e : Elementary.linComb 1 u 1 v = u + v := by
    funext x
    simp [Elementary.linComb]
  rw [e] at h
  simpa using h
theorem tensorCombination_mem_schwartzSet (hOps : Elementary.SchwartzClosedUnderOps n)
    {ψ : PointTuple n → ℂ} (hψ : ψ ∈ schwartzSet n) {m : ℕ} (a : Fin m → ℂ)
    (g : Fin m → Fin n → (Fin 4 → ℝ) → ℝ)
    (hg : ∀ j, Elementary.tensorProdComplex (g j) ∈ schwartzSet n) :
    tensorCombination a g ∈ schwartzSet n := by
  have key : ∀ s : Finset (Fin m),
      (fun x => ∑ j ∈ s, a j * Elementary.tensorProdComplex (g j) x) ∈ schwartzSet n := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h := (hOps.1 ψ hψ ψ hψ 0 0).1.1
      have e : Elementary.linComb 0 ψ 0 ψ =
          fun x => ∑ j ∈ (∅ : Finset (Fin m)), a j * Elementary.tensorProdComplex (g j) x := by
        funext x
        simp [Elementary.linComb]
      rwa [e] at h
    | insert i s hi ih =>
      have h := (hOps.1 _ ih _ (hg i) 1 (a i)).1.1
      have e : Elementary.linComb 1
            (fun x => ∑ j ∈ s, a j * Elementary.tensorProdComplex (g j) x) (a i)
            (Elementary.tensorProdComplex (g i)) =
          fun x => ∑ j ∈ insert i s, a j * Elementary.tensorProdComplex (g j) x := by
        funext x
        simp [Elementary.linComb, Finset.sum_insert hi, add_comm]
      rwa [e] at h
  exact key Finset.univ
theorem tensorDenseAt_of_approx (hn : 0 < n) {k : ℕ} (hk : 0 < k)
    (hOps : Elementary.SchwartzClosedUnderOps n)
    (hCpt : Elementary.CompactSupportFacts n) (hSub : Elementary.SubtupleTensorFacts n)
    (htrunc : SchwartzTruncationApprox)
    (hcutoff : approxByCompactSuppInOpen)
    {U : Set (PointTuple n)} {W : Set (Fin 4 → ℝ)} (hW : IsOpen W)
    (happrox : ApproxByTensorSums U W k) : TensorDenseAt U W k := by
  intro ψ hψ hflat δ hδ
  have hU : IsOpen U := hflat.2.1
  have δ3 : 0 < δ / 3 := by positivity
  obtain ⟨ψ₁, hs₁, hc₁, hf₁, hn₁, hr₁⟩ := htrunc n k hn hk U ψ hψ hflat (δ / 3) δ3
  obtain ⟨ψ₂, hm₂, hn₂, hr₂⟩ := hcutoff n k hn hk U ψ₁ hc₁ hf₁ (δ / 3) δ3
  obtain ⟨m, a, g, hm, hg, hn₃, hr₃⟩ := happrox ψ₂ hm₂ (δ / 3) δ3
  have hψ₁ : ψ₁ ∈ schwartzSet n :=
    (hCpt univ isOpen_univ ψ₁ ⟨hs₁, hc₁, subset_univ _⟩).1
  have hψ₂ : ψ₂ ∈ schwartzSet n := (hCpt U hU ψ₂ hm₂).1
  have hcomb : tensorCombination a g ∈ schwartzSet n :=
    tensorCombination_mem_schwartzSet hOps hψ a g fun j =>
      ((hSub W hW (g j) (hg j).1).2 (hg j).2).2.1.1
  have hn₃' : weightedSeminorm k (ψ₂ - tensorCombination a g) ≤ ENNReal.ofReal (δ / 3) := hn₃
  have hA := sub_mem_schwartzSet hOps hψ hψ₁
  have hB := sub_mem_schwartzSet hOps hψ₁ hψ₂
  have hC := sub_mem_schwartzSet hOps hψ₂ hcomb
  have key : weightedSeminorm k (ψ - tensorCombination a g) ≤ ENNReal.ofReal δ := by
    have e : ψ - tensorCombination a g =
        (ψ - ψ₁) + ((ψ₁ - ψ₂) + (ψ₂ - tensorCombination a g)) := by abel
    have eδ : ENNReal.ofReal δ =
        ENNReal.ofReal (δ / 3) + (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) := by
      rw [← ENNReal.ofReal_add δ3.le δ3.le, ← ENNReal.ofReal_add δ3.le (by positivity)]
      congr 1
      ring
    rw [e, eδ]
    calc weightedSeminorm k ((ψ - ψ₁) + ((ψ₁ - ψ₂) + (ψ₂ - tensorCombination a g)))
        ≤ weightedSeminorm k (ψ - ψ₁) +
            weightedSeminorm k ((ψ₁ - ψ₂) + (ψ₂ - tensorCombination a g)) :=
          weightedSeminorm_add_le hOps hk hA (add_mem_schwartzSet hOps hB hC)
      _ ≤ weightedSeminorm k (ψ - ψ₁) +
            (weightedSeminorm k (ψ₁ - ψ₂) + weightedSeminorm k (ψ₂ - tensorCombination a g)) := by
          gcongr
          exact weightedSeminorm_add_le hOps hk hB hC
      _ ≤ _ := by
          gcongr
  refine ⟨⟨m, a, g, hm, hg, key⟩, fun hre => ⟨m, fun j => (a j).re, g, hm, hg, ?_⟩⟩
  have ea : (fun j => (((a j).re : ℝ) : ℂ)) = a := by
    funext j
    apply Complex.ext
    · simp
    · simpa using (hr₃ (hr₂ (hr₁ hre)) j).symm
  rw [ea]
  exact key
theorem isOpen_upperHalfSpace : IsOpen upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem statement_holds (hBasic : Elementary.BasicProperties)
    (hTens : TensorSeminormBounds)
    (hInt : IntegrateOutBounds)
    (htrunc : SchwartzTruncationApprox)
    (hcutoff : approxByCompactSuppInOpen)
    (hsums : TensorSumsApproxBumps) :
    TestSpaceFacts.Statement := by
  refine ⟨hTens.1, hTens.2, hInt, fun n k hn hk => ?_⟩
  obtain ⟨hOps, -, hCpt, hSub, -⟩ := hBasic n hn
  exact ⟨tensorDenseAt_of_approx hn hk hOps hCpt hSub htrunc hcutoff isOpen_univ (hsums n k hn hk).1,
    tensorDenseAt_of_approx hn hk hOps hCpt hSub htrunc hcutoff isOpen_upperHalfSpace
      (hsums n k hn hk).2⟩
end YangMills.Construction.TestSpaces.TestSpaceFacts
