import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.PeriodicOperators.ActionAndProductsOnTheTorus
import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorus
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSetProof
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TheTracesOnTheToriAtUnitFieldsConverge
import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuotTraceLimits
open UnitFieldTraces
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.PeriodicOperators.LocalTorusMatrices (ActsViaPeriodization)
open Classical
theorem euclidNormVec_eq_norm (v : AmbientSpace) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_add_le (u v : AmbientSpace) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
theorem euclidNormVec_neg (v : AmbientSpace) : euclidNormVec (-v) = euclidNormVec v := by
  simp [euclidNormVec]
theorem euclidNormVec_sub_comm (u v : AmbientSpace) :
    euclidNormVec (u - v) = euclidNormVec (v - u) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem euclidNormVec_sub_le_add (u v w : AmbientSpace) :
    euclidNormVec (u - w) ≤ euclidNormVec (u - v) + euclidNormVec (v - w) := by apply _root_.YangMills.Construction.LatticeCovering.euclidNormVec_sub_le_add <;> assumption
theorem euclidNormVec_nonneg (v : AmbientSpace) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem castVec_nsmul (s : ℕ) (n : Fin 4 → ℤ) :
    castVec (s • n) = (s : ℝ) • castVec n := by
  funext μ
  simp [castVec]
theorem euclidNormVec_natCast_smul (s : ℕ) (v : AmbientSpace) :
    euclidNormVec ((s : ℝ) • v) = s * euclidNormVec v := by
  simp only [euclidNormVec_eq_norm, WithLp.toLp_smul, norm_smul]
  simp
theorem one_le_euclidNormVec_castVec {n : Fin 4 → ℤ} (h : n ≠ 0) :
    1 ≤ euclidNormVec (castVec n) := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 h
  have h0 : n μ ≠ 0 := hμ
  have h1 : (1 : ℤ) ≤ (n μ) ^ 2 := by
    have := Int.one_le_abs h0
    nlinarith [sq_abs (n μ)]
  have h2 : (1 : ℝ) ≤ (n μ : ℝ) ^ 2 := by exact_mod_cast h1
  have h3 : (n μ : ℝ) ^ 2 ≤ ∑ ν, castVec n ν ^ 2 :=
    Finset.single_le_sum (f := fun ν => castVec n ν ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ)
  unfold euclidNormVec
  rw [Real.one_le_sqrt]
  exact h2.trans h3
theorem le_euclidNormVec_castVec_nsmul (s : ℕ) {n : Fin 4 → ℤ} (h : n ≠ 0) :
    (s : ℝ) ≤ euclidNormVec (castVec (s • n)) := by
  rw [castVec_nsmul, euclidNormVec_natCast_smul]
  have := one_le_euclidNormVec_castVec h
  nlinarith
section Quotients
variable {I : PeriodicData}
theorem mkQuot_eq_mkQuot_iff (hI : IsPeriodic I) (s : ℕ) (a b : I.Carrier) :
    I.mkQuot s a = I.mkQuot s b ↔ ∃ n : Fin 4 → ℤ, b = I.translate (s • n) a := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
theorem mkQuot_translate_nsmul (s : ℕ) (n : Fin 4 → ℤ) (ι : I.Carrier) :
    I.mkQuot s (I.translate (s • n) ι) = I.mkQuot s ι :=
  (Quot.sound ⟨n, rfl⟩).symm
theorem eq_of_mkQuot_eq_of_dist_lt (hI : IsPeriodic I) {s : ℕ} {a b : I.Carrier}
    (h : I.mkQuot s a = I.mkQuot s b)
    (hab : euclidNormVec (I.pos a - I.pos b) < s) : a = b := by
  obtain ⟨n, rfl⟩ := (mkQuot_eq_mkQuot_iff hI s a b).1 h
  by_cases hn : n = 0
  · subst hn
    simp [hI.translate_zero]
  · exfalso
    have e : I.pos a - I.pos (I.translate (s • n) a) = -castVec (s • n) := by
      rw [hI.pos_translate]
      abel
    rw [e, euclidNormVec_neg] at hab
    exact absurd hab (not_lt.2 (le_euclidNormVec_castVec_nsmul s hn))
def translateEquiv (hI : IsPeriodic I) (m : Fin 4 → ℤ) : I.Carrier ≃ I.Carrier where
  toFun := I.translate m
  invFun := I.translate (-m)
  left_inv := fun ι => by
    show I.translate (-m) (I.translate m ι) = ι
    rw [← hI.translate_add]
    simp [hI.translate_zero]
  right_inv := fun ι => by
    show I.translate m (I.translate (-m) ι) = ι
    rw [← hI.translate_add]
    simp [hI.translate_zero]
end Quotients
section FiniteSums
variable {J : Type}
theorem tsum_mul_eq_sum_fst (S : Finset (J × J)) (A : J → J → ℂ)
    (hA : ∀ a b, A a b ≠ 0 → (a, b) ∈ S) (a : J) (h : J → ℂ) :
    ∑' b, A a b * h b = ∑ p ∈ S, if p.1 = a then A p.1 p.2 * h p.2 else 0 := by
  have hinj : ∀ p ∈ S.filter (fun p => p.1 = a), ∀ q ∈ S.filter (fun p => p.1 = a),
      p.2 = q.2 → p = q := fun p hp q hq e =>
    Prod.ext ((Finset.mem_filter.1 hp).2.trans (Finset.mem_filter.1 hq).2.symm) e
  calc ∑' b, A a b * h b
      = ∑ b ∈ (S.filter fun p => p.1 = a).image Prod.snd, A a b * h b := by
        refine tsum_eq_sum fun b hb => ?_
        by_contra hne
        apply hb
        exact Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2
          ⟨hA a b (left_ne_zero_of_mul hne), rfl⟩, rfl⟩
    _ = ∑ p ∈ S.filter (fun p => p.1 = a), A a p.2 * h p.2 := Finset.sum_image hinj
    _ = ∑ p ∈ S, if p.1 = a then A p.1 p.2 * h p.2 else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with e
        · rw [e]
        · rfl
theorem tsum_mul_eq_sum_snd (S : Finset (J × J)) (A : J → J → ℂ)
    (hA : ∀ a b, A a b ≠ 0 → (a, b) ∈ S) (j : J) (h : J → ℂ) :
    ∑' k, h k * A k j = ∑ p ∈ S, if p.2 = j then h p.1 * A p.1 p.2 else 0 := by
  have hinj : ∀ p ∈ S.filter (fun p => p.2 = j), ∀ q ∈ S.filter (fun p => p.2 = j),
      p.1 = q.1 → p = q := fun p hp q hq e =>
    Prod.ext e ((Finset.mem_filter.1 hp).2.trans (Finset.mem_filter.1 hq).2.symm)
  calc ∑' k, h k * A k j
      = ∑ k ∈ (S.filter fun p => p.2 = j).image Prod.fst, h k * A k j := by
        refine tsum_eq_sum fun k hk => ?_
        by_contra hne
        apply hk
        exact Finset.mem_image.2 ⟨(k, j), Finset.mem_filter.2
          ⟨hA k j (right_ne_zero_of_mul hne), rfl⟩, rfl⟩
    _ = ∑ p ∈ S.filter (fun p => p.2 = j), h p.1 * A p.1 j := Finset.sum_image hinj
    _ = ∑ p ∈ S, if p.2 = j then h p.1 * A p.1 p.2 else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with e
        · rw [e]
        · rfl
theorem tsum_sum_ite_eq {β : Type} (S : Finset β) (g : β → J) (u : β → ℂ) :
    ∑' j, ∑ p ∈ S, (if g p = j then u p else 0) = ∑ p ∈ S, u p := by
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [tsum_eq_single (g p)]
    · simp
    · intro j hj
      simp [Ne.symm hj]
  · intro p _
    refine (hasSum_single (g p) fun j hj => ?_).summable
    simp [Ne.symm hj]
theorem tsum_sum_ite_mul_eq {β : Type} (S : Finset β) (g : β → J) (u : β → ℂ) (v : J → ℂ) :
    ∑' j, (∑ p ∈ S, (if g p = j then u p else 0)) * v j = ∑ p ∈ S, u p * v (g p) := by
  have e : ∀ j, (∑ p ∈ S, (if g p = j then u p else 0)) * v j =
      ∑ p ∈ S, (if g p = j then u p * v (g p) else 0) := fun j => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rw [h]
    · simp
  rw [tsum_congr e, tsum_sum_ite_eq]
theorem diagSum_comp_finiteSupport (S : Finset (J × J)) (R B : J → J → ℂ)
    (hB : ∀ a b, B a b ≠ 0 → (a, b) ∈ S) :
    diagSum (compKernel R B) = ∑ p ∈ S, B p.1 p.2 * R p.2 p.1 := by
  have e : ∀ ι, compKernel R B ι ι =
      ∑ p ∈ S, if p.2 = ι then B p.1 p.2 * R p.2 p.1 else 0 := fun ι => by
    show ∑' k, R ι k * B k ι = _
    rw [tsum_mul_eq_sum_snd S B hB ι (R ι)]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rw [h, mul_comm]
    · rfl
  unfold diagSum
  rw [tsum_congr e, tsum_sum_ite_eq]
theorem diagSum_comp_comp_finiteSupport (S S' : Finset (J × J)) (R A A' : J → J → ℂ)
    (hA : ∀ a b, A a b ≠ 0 → (a, b) ∈ S) (hA' : ∀ a b, A' a b ≠ 0 → (a, b) ∈ S') :
    diagSum (compKernel (compKernel R A) (compKernel R A')) =
      ∑ p ∈ S, ∑ q ∈ S', A p.1 p.2 * A' q.1 q.2 * R p.2 q.1 * R q.2 p.1 := by
  have hRA : ∀ ι j, compKernel R A ι j =
      ∑ p ∈ S, if p.2 = j then R ι p.1 * A p.1 p.2 else 0 := fun ι j =>
    tsum_mul_eq_sum_snd S A hA j (R ι)
  have hRA' : ∀ ι j, compKernel R A' ι j =
      ∑ q ∈ S', if q.2 = j then R ι q.1 * A' q.1 q.2 else 0 := fun ι j =>
    tsum_mul_eq_sum_snd S' A' hA' j (R ι)
  have e : ∀ ι, compKernel (compKernel R A) (compKernel R A') ι ι =
      ∑ q ∈ S', if q.2 = ι then
        ∑ p ∈ S, A p.1 p.2 * A' q.1 q.2 * R p.2 q.1 * R q.2 p.1 else 0 := fun ι => by
    show ∑' j, compKernel R A ι j * compKernel R A' j ι = _
    simp_rw [hRA ι]
    rw [tsum_sum_ite_mul_eq S Prod.snd (fun p => R ι p.1 * A p.1 p.2)
      (fun j => compKernel R A' j ι)]
    calc ∑ p ∈ S, R ι p.1 * A p.1 p.2 * compKernel R A' p.2 ι
        = ∑ p ∈ S, ∑ q ∈ S', if q.2 = ι then
            A p.1 p.2 * A' q.1 q.2 * R p.2 q.1 * R q.2 p.1 else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRA', Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          split_ifs with h
          · rw [h]
            ring
          · simp
      _ = ∑ q ∈ S', ∑ p ∈ S, if q.2 = ι then
            A p.1 p.2 * A' q.1 q.2 * R p.2 q.1 * R q.2 p.1 else 0 := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun q _ => ?_
          split_ifs with h
          · rfl
          · simp
  unfold diagSum
  rw [tsum_congr e, tsum_sum_ite_eq, Finset.sum_comm]
end FiniteSums
section Traces
variable {C : Type} [Finite C]
def stdBasisEnd (c d : C) : Module.End ℂ (C → ℂ) :=
  (LinearMap.proj d : (C → ℂ) →ₗ[ℂ] ℂ).smulRight (Pi.single c 1)
omit [Finite C] in
theorem stdBasisEnd_apply (c d : C) (f : C → ℂ) :
    stdBasisEnd c d f = f d • (Pi.single c 1 : C → ℂ) := rfl
theorem trace_mul_stdBasisEnd (M : Module.End ℂ (C → ℂ)) (c d : C) :
    LinearMap.trace ℂ (C → ℂ) (M * stdBasisEnd c d) = M (Pi.single c 1) d := by
  have e : M * stdBasisEnd c d =
      (LinearMap.proj d : (C → ℂ) →ₗ[ℂ] ℂ).smulRight (M (Pi.single c 1)) := by
    refine LinearMap.ext fun f => ?_
    simp [Module.End.mul_apply, stdBasisEnd_apply]
  rw [e, LinearMap.trace_smulRight]
  rfl
variable {β γ : Type}
def weightedBasisSum (S : Finset β) (a b : β → C) (w : β → ℂ) : Module.End ℂ (C → ℂ) :=
  ∑ p ∈ S, w p • stdBasisEnd (a p) (b p)
theorem trace_mul_weightedBasisSum (M : Module.End ℂ (C → ℂ)) (S : Finset β) (a b : β → C)
    (w : β → ℂ) :
    LinearMap.trace ℂ (C → ℂ) (M * weightedBasisSum S a b w) =
      ∑ p ∈ S, w p * M (Pi.single (a p) 1) (b p) := by
  unfold weightedBasisSum
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, map_smul, trace_mul_stdBasisEnd, smul_eq_mul]
omit [Finite C] in
theorem weightedBasisSum_apply (S : Finset β) (a b : β → C) (w : β → ℂ) (g : C → ℂ) :
    weightedBasisSum S a b w g = ∑ p ∈ S, (w p * g (b p)) • (Pi.single (a p) 1 : C → ℂ) := by
  unfold weightedBasisSum
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.smul_apply, stdBasisEnd_apply, smul_smul]
theorem trace_mul_weightedBasisSum_mul_weightedBasisSum (L : Module.End ℂ (C → ℂ))
    (S : Finset β) (S' : Finset γ) (a b : β → C)
    (a' b' : γ → C) (w : β → ℂ) (w' : γ → ℂ) :
    LinearMap.trace ℂ (C → ℂ)
        (L * weightedBasisSum S a b w * L * weightedBasisSum S' a' b' w') =
      ∑ p ∈ S, ∑ q ∈ S', w p * w' q * L (Pi.single (a' q) 1) (b p) *
        L (Pi.single (a p) 1) (b' q) := by
  rw [trace_mul_weightedBasisSum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, weightedBasisSum_apply, map_sum,
    Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring
theorem linearMapOfEntries_single (K : C → C → ℂ) (c d : C) :
    linearMapOfEntries K (Pi.single c 1) d = K d c := by
  rw [linearMapOfEntries_eq_applyKernel]
  unfold applyKernel
  rw [tsum_eq_single c]
  · simp
  · intro b hb
    simp [hb]
theorem linearMapOfEntries_mul (K L : C → C → ℂ) :
    (linearMapOfEntries K * linearMapOfEntries L : Module.End ℂ (C → ℂ)) =
      linearMapOfEntries (compKernel K L) := by
  have := Fintype.ofFinite C
  refine LinearMap.ext fun f => ?_
  funext c
  rw [Module.End.mul_apply, linearMapOfEntries_eq_applyKernel, linearMapOfEntries_eq_applyKernel,
    linearMapOfEntries_eq_applyKernel]
  simp only [applyKernel, compKernel, tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end Traces
section PeriodicExtensions
variable {I : PeriodicData}
structure IsPeriodicExtension (I : PeriodicData) (s : ℕ) (Y A : I.Carrier → I.Carrier → ℂ)
    (D : Set I.Carrier) (S : Finset (I.Carrier × I.Carrier)) : Prop where
  mem_of_ne_zero : ∀ a b, A a b ≠ 0 → (a, b) ∈ S
  fst_mem : ∀ p ∈ S, p.1 ∈ D
  injOn_mkQuot : ∀ a ∈ D, ∀ b ∈ D, I.mkQuot s a = I.mkQuot s b → a = b
  translate_invariant : ∀ (n : Fin 4 → ℤ) ι' ι,
    Y (I.translate (s • n) ι') (I.translate (s • n) ι) = Y ι' ι
  eq_on : ∀ a ∈ D, ∀ b, Y a b = A a b
  eq_zero_off : ∀ ι', (∀ a ∈ D, I.mkQuot s a ≠ I.mkQuot s ι') → ∀ ι, Y ι' ι = 0
variable {s : ℕ} {Y A : I.Carrier → I.Carrier → ℂ} {D : Set I.Carrier}
  {S : Finset (I.Carrier × I.Carrier)}
theorem IsPeriodicExtension.applyKernel_liftQuotField (hI : IsPeriodic I)
    (h : IsPeriodicExtension I s Y A D S) (f : I.QuotMod s → ℂ) (ι' : I.Carrier) :
    applyKernel Y (liftQuotField I s f) ι' =
      ∑ p ∈ S, if I.mkQuot s p.1 = I.mkQuot s ι' then
        A p.1 p.2 * f (I.mkQuot s p.2) else 0 := by
  by_cases hex : ∃ a ∈ D, I.mkQuot s a = I.mkQuot s ι'
  · obtain ⟨a, ha, e⟩ := hex
    obtain ⟨n, rfl⟩ := (mkQuot_eq_mkQuot_iff hI s a ι').1 e
    have h1 : applyKernel Y (liftQuotField I s f) (I.translate (s • n) a) =
        ∑' b, A a b * f (I.mkQuot s b) := by
      unfold applyKernel
      rw [← (translateEquiv hI (s • n)).tsum_eq]
      refine tsum_congr fun b => ?_
      show Y (I.translate (s • n) a) (I.translate (s • n) b) *
        f (I.mkQuot s (I.translate (s • n) b)) = _
      rw [h.translate_invariant, h.eq_on a ha, mkQuot_translate_nsmul]
    rw [h1, tsum_mul_eq_sum_fst S A h.mem_of_ne_zero a fun b => f (I.mkQuot s b)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h2 : I.mkQuot s p.1 = I.mkQuot s (I.translate (s • n) a) ↔ p.1 = a :=
      ⟨fun e' => h.injOn_mkQuot _ (h.fst_mem p hp) _ ha (e'.trans e.symm),
        fun e' => by rw [e']; exact e⟩
    simp only [h2]
  · push Not at hex
    have h1 : applyKernel Y (liftQuotField I s f) ι' = 0 := by
      simp [applyKernel, h.eq_zero_off ι' hex]
    rw [h1]
    symm
    exact Finset.sum_eq_zero fun p hp => if_neg (hex _ (h.fst_mem p hp))
theorem IsPeriodicExtension.linearMap_eq [Finite (I.QuotMod s)] (hI : IsPeriodic I)
    (h : IsPeriodicExtension I s Y A D S) (hY : ActsViaPeriodization I I Y s) :
    (linearMapOfEntries (descendMatrix I I s (periodization I I Y s)) :
        Module.End ℂ (I.QuotMod s → ℂ)) =
      weightedBasisSum S (fun p => I.mkQuot s p.1) (fun p => I.mkQuot s p.2)
        (fun p => A p.1 p.2) := by
  refine LinearMap.ext fun f => ?_
  funext c
  induction c using Quot.ind with
  | mk ι' =>
    show linearMapOfEntries (descendMatrix I I s (periodization I I Y s)) f (I.mkQuot s ι') =
      weightedBasisSum S (fun p => I.mkQuot s p.1) (fun p => I.mkQuot s p.2)
        (fun p => A p.1 p.2) f (I.mkQuot s ι')
    rw [linearMapOfEntries_eq_applyKernel, ← (hY f).2.2 ι', h.applyKernel_liftQuotField hI,
      weightedBasisSum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases e : I.mkQuot s p.1 = I.mkQuot s ι'
    · simp [e]
    · simp [e, Ne.symm e]
end PeriodicExtensions
theorem euclidNormVec_le_sub_add (v w : AmbientSpace) :
    euclidNormVec w ≤ euclidNormVec (v - w) + euclidNormVec v := by
  have h := euclidNormVec_add_le (w - v) v
  rwa [sub_add_cancel, euclidNormVec_sub_comm] at h
theorem tendsto_periodization (h₃ : Periodized.Claim) {I : PeriodicData}
    (hI : IsPeriodic I) {R : I.Carrier → I.Carrier → ℂ} (hR : IsPeriodicKernel I I R)
    (b a : I.Carrier) :
    Tendsto (fun s : ℕ => periodization I I R s b a) atTop (𝓝 (R b a)) := by
  obtain ⟨-, C, δ, hC, hδ, hbd⟩ := hR
  set v : AmbientSpace := I.pos b - I.pos a with hv
  let E : I.Carrier → I.Carrier → ℂ := fun x y =>
    ((Real.exp (-δ * euclidNormVec (I.pos x - I.pos y)) : ℝ) : ℂ)
  have hEbd : ExpDecay I I E 1 δ := fun x y => by
    simp only [E, one_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    exact le_rfl
  have hEper : IsPeriodicKernel I I E := by
    refine ⟨fun n x y => ?_, 1, δ, one_pos, hδ, hEbd⟩
    simp only [E, hI.pos_translate, add_sub_add_right_eq_sub]
  have hErate : IsDecayRate I I E δ := ⟨hδ, 1, one_pos, hEbd⟩
  have hsum := (h₃ I I hI hI E δ hEper hErate).summable 1 one_pos b a
  have hpos : ∀ (s : ℕ) (n : Fin 4 → ℤ),
      I.pos b - I.pos (I.translate (s • n) a) = v - castVec (s • n) := by
    intro s n
    rw [hI.pos_translate, hv]
    abel
  have hEn : ∀ n : Fin 4 → ℤ, ‖E b (I.translate ((1 : ℕ) • n) a)‖ =
      Real.exp (-δ * euclidNormVec (v - castVec n)) := by
    intro n
    simp only [E, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    rw [hpos 1 n, one_nsmul]
  have hRn : ∀ (s : ℕ) (n : Fin 4 → ℤ), ‖R b (I.translate (s • n) a)‖ ≤
      C * Real.exp (-δ * euclidNormVec (v - castVec (s • n))) := by
    intro s n
    have h := hbd b (I.translate (s • n) a)
    rwa [hpos] at h
  have hbound : ∀ᶠ s : ℕ in atTop, ∀ n : Fin 4 → ℤ, ‖R b (I.translate (s • n) a)‖ ≤
      C * Real.exp (2 * δ * euclidNormVec v) * ‖E b (I.translate ((1 : ℕ) • n) a)‖ := by
    filter_upwards [eventually_ge_atTop 1] with s hs n
    refine (hRn s n).trans ?_
    rw [hEn, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le
    have h1 : euclidNormVec (v - castVec n) ≤ euclidNormVec v + euclidNormVec (castVec n) := by
      have h := euclidNormVec_add_le v (-castVec n)
      rwa [← sub_eq_add_neg, euclidNormVec_neg] at h
    have h2 := euclidNormVec_le_sub_add v (castVec (s • n))
    have h3 : euclidNormVec (castVec n) ≤ euclidNormVec (castVec (s • n)) := by
      rw [castVec_nsmul, euclidNormVec_natCast_smul]
      have h1s : (1 : ℝ) ≤ s := by exact_mod_cast hs
      nlinarith [euclidNormVec_nonneg (castVec n)]
    have h4 : euclidNormVec (v - castVec n) ≤
        euclidNormVec (v - castVec (s • n)) + 2 * euclidNormVec v := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hδ.le]
  have hlim : ∀ n : Fin 4 → ℤ, Tendsto (fun s : ℕ => R b (I.translate (s • n) a)) atTop
      (𝓝 (if n = 0 then R b a else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [hI.translate_zero]
    · rw [if_neg hn, tendsto_zero_iff_norm_tendsto_zero]
      have hg : Tendsto (fun s : ℕ => C * Real.exp (-(δ * ((s : ℝ) - euclidNormVec v)))) atTop
          (𝓝 0) := by
        have h1 : Tendsto (fun s : ℕ => δ * ((s : ℝ) - euclidNormVec v)) atTop atTop :=
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).const_mul_atTop hδ
        have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
        simpa [Function.comp_def] using h2
      refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) hg
      refine (hRn s n).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le)
      have h1 := le_euclidNormVec_castVec_nsmul s hn
      have h2 := euclidNormVec_le_sub_add v (castVec (s • n))
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hδ.le]
  have key := tendsto_tsum_of_dominated_convergence
    (bound := fun n : Fin 4 → ℤ =>
      C * Real.exp (2 * δ * euclidNormVec v) * ‖E b (I.translate ((1 : ℕ) • n) a)‖)
    (hsum.mul_left _) hlim hbound
  have e : ∑' n : Fin 4 → ℤ, (if n = 0 then R b a else 0) = R b a := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  rw [e] at key
  exact key
section Coefficients
variable {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R₀ : ℝ}
theorem coeffOne_congr_near (h₁ : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hT : IsLocalWith F I I T ρ R₀) {ζ ζ' : F.Carrier → ℂ} {a b : I.Carrier}
    (h : ∀ κ ∈ nearIndices F (I.pos a) R₀, ζ κ = ζ' κ) :
    coeffOne F I I T ζ a b = coeffOne F I I T ζ' a b := by
  have h1 := (h₁ F I I hF hI hI T ρ R₀ hT ζ ζ a b 0).1.2.2.1
  rw [h1 ζ, h1 ζ']
  exact finsum_congr fun κ => by rw [h κ κ.2]
theorem coeffOne_eq_zero_of_near (h₁ : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hT : IsLocalWith F I I T ρ R₀) {ζ : F.Carrier → ℂ} {a b : I.Carrier}
    (h : ∀ κ ∈ nearIndices F (I.pos a) R₀, ζ κ = 0) :
    coeffOne F I I T ζ a b = 0 := by
  have h1 := (h₁ F I I hF hI hI T ρ R₀ hT ζ ζ a b 0).1.2.2.1
  rw [h1 ζ]
  exact (finsum_congr fun κ => by rw [h κ κ.2, mul_zero]).trans finsum_zero
theorem coeffTwo_congr_near (h₁ : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hT : IsLocalWith F I I T ρ R₀) {ζ₁ ζ₂ ζ₁' ζ₂' : F.Carrier → ℂ} {a b : I.Carrier}
    (h : ∀ κ ∈ nearIndices F (I.pos a) R₀, ζ₁ κ = ζ₁' κ)
    (h' : ∀ κ ∈ nearIndices F (I.pos a) R₀, ζ₂ κ = ζ₂' κ) :
    coeffTwo F I I T ζ₁ ζ₂ a b = coeffTwo F I I T ζ₁' ζ₂' a b := by
  have h2 := (h₁ F I I hF hI hI T ρ R₀ hT ζ₁ ζ₂ a b 0).1.2.2.2.2.2
  rw [h2 ζ₁ ζ₂, h2 ζ₁' ζ₂']
  exact finsum_congr fun κ => finsum_congr fun κ' => by rw [h κ κ.2, h' κ' κ'.2]
theorem coeffTwo_eq_zero_of_near (h₁ : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hT : IsLocalWith F I I T ρ R₀) {ζ : F.Carrier → ℂ} (ζ' : F.Carrier → ℂ) {a b : I.Carrier}
    (h : ∀ κ ∈ nearIndices F (I.pos a) R₀, ζ κ = 0) :
    coeffTwo F I I T ζ ζ' a b = 0 := by
  have h2 := (h₁ F I I hF hI hI T ρ R₀ hT ζ ζ' a b 0).1.2.2.2.2.2
  rw [h2 ζ ζ']
  exact (finsum_congr fun κ => (finsum_congr fun κ' => by
    rw [h κ κ.2, mul_zero, zero_mul]).trans finsum_zero).trans finsum_zero
theorem liftQuotField_quotIndicator_eq (hF : IsPeriodic F) {s : ℕ} {κ κ'' : F.Carrier}
    (h : euclidNormVec (F.pos κ'' - F.pos κ) < s) :
    liftQuotField F s (quotIndicator F s κ) κ'' = siteIndicator F κ κ'' := by
  show (if F.mkQuot s κ'' = F.mkQuot s κ then (1 : ℂ) else 0) =
    if κ'' = κ then 1 else 0
  by_cases e : κ'' = κ
  · simp [e]
  · have e' : F.mkQuot s κ'' ≠ F.mkQuot s κ := fun h' =>
      e (eq_of_mkQuot_eq_of_dist_lt hF h' h)
    simp [e, e']
theorem shiftField_liftQuotField (s : ℕ) (n : Fin 4 → ℤ) (ζ : F.QuotMod s → ℂ) :
    shiftField F (s • n) (liftQuotField F s ζ) = liftQuotField F s ζ := by
  funext κ
  show ζ (F.mkQuot s (F.translate (-(s • n)) κ)) = ζ (F.mkQuot s κ)
  rw [← smul_neg, mkQuot_translate_nsmul]
theorem liftQuotField_quotIndicator_eq_zero (hF : IsPeriodic F) (hI : IsPeriodic I) {s : ℕ}
    {κ : F.Carrier} {ι' : I.Carrier}
    (hoff : ∀ a ∈ nearIndices I (F.pos κ) R₀, I.mkQuot s a ≠ I.mkQuot s ι') :
    ∀ κ'' ∈ nearIndices F (I.pos ι') R₀,
      liftQuotField F s (quotIndicator F s κ) κ'' = 0 := by
  intro κ'' h
  show (if F.mkQuot s κ'' = F.mkQuot s κ then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro e
  obtain ⟨m, rfl⟩ := (mkQuot_eq_mkQuot_iff hF s κ'' κ).1 e
  refine hoff (I.translate (s • m) ι') ?_ (mkQuot_translate_nsmul s m ι')
  show euclidNormVec (I.pos (I.translate (s • m) ι') - F.pos (F.translate (s • m) κ'')) ≤ R₀
  rw [hI.pos_translate, hF.pos_translate, add_sub_add_right_eq_sub, euclidNormVec_sub_comm]
  exact h
theorem siteIndicator_eq_zero_of_far {κ : F.Carrier} {a : I.Carrier}
    (h : a ∉ nearIndices I (F.pos κ) R₀) :
    ∀ κ'' ∈ nearIndices F (I.pos a) R₀, siteIndicator F κ κ'' = 0 := by
  intro κ'' hκ
  show (if κ'' = κ then (1 : ℂ) else 0) = 0
  rw [if_neg]
  rintro rfl
  apply h
  show euclidNormVec (I.pos a - F.pos κ'') ≤ R₀
  rw [euclidNormVec_sub_comm]
  exact hκ
def nearPairs (hfin : ∀ (y : AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    (y : AmbientSpace) (r : ℝ) : Finset (I.Carrier × I.Carrier) :=
  (hfin y r).toFinset ×ˢ (hfin y (2 * r)).toFinset
theorem mem_nearPairs (hfin : ∀ (y : AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    {y : AmbientSpace} {r : ℝ} {a b : I.Carrier} (ha : a ∈ nearIndices I y r)
    (hb : euclidNormVec (I.pos b - I.pos a) ≤ r) : (a, b) ∈ nearPairs hfin y r := by
  refine Finset.mem_product.2 ⟨(hfin y r).mem_toFinset.2 ha, (hfin y _).mem_toFinset.2 ?_⟩
  have h := euclidNormVec_sub_le_add (I.pos b) (I.pos a) y
  have ha' : euclidNormVec (I.pos a - y) ≤ r := ha
  show euclidNormVec (I.pos b - y) ≤ 2 * r
  linarith
theorem fst_mem_of_mem_nearPairs
    (hfin : ∀ (y : AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    {y : AmbientSpace} {r : ℝ} {p : I.Carrier × I.Carrier} (hp : p ∈ nearPairs hfin y r) :
    p.1 ∈ nearIndices I y r :=
  (hfin y r).mem_toFinset.1 (Finset.mem_product.1 hp).1
theorem eq_of_mkQuot_eq_near (hI : IsPeriodic I) {y : AmbientSpace} {s : ℕ} (hs : 2 * R₀ < s) :
    ∀ a ∈ nearIndices I y R₀, ∀ b ∈ nearIndices I y R₀,
      I.mkQuot s a = I.mkQuot s b → a = b := by
  intro a ha b hb e
  refine eq_of_mkQuot_eq_of_dist_lt hI e ?_
  have h := euclidNormVec_sub_le_add (I.pos a) y (I.pos b)
  have ha' : euclidNormVec (I.pos a - y) ≤ R₀ := ha
  have hb' : euclidNormVec (I.pos b - y) ≤ R₀ := hb
  rw [euclidNormVec_sub_comm y] at h
  linarith
theorem dist_le_two_mul_of_near {κ κ'' : F.Carrier} {a : I.Carrier}
    (ha : a ∈ nearIndices I (F.pos κ) R₀)
    (hκ : κ'' ∈ nearIndices F (I.pos a) R₀) :
    euclidNormVec (F.pos κ'' - F.pos κ) ≤ 2 * R₀ := by
  have h := euclidNormVec_sub_le_add (F.pos κ'') (I.pos a) (F.pos κ)
  have h1 : euclidNormVec (I.pos a - F.pos κ) ≤ R₀ := ha
  have h2 : euclidNormVec (F.pos κ'' - I.pos a) ≤ R₀ := hκ
  linarith
theorem coeffOne_isPeriodicExtension (h₁ : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hT : IsLocalWith F I I T ρ R₀)
    (hfin : ∀ (y : AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite) (κ : F.Carrier) {s : ℕ}
    (hs : 2 * R₀ < s) :
    IsPeriodicExtension I s (coeffOne F I I T (liftQuotField F s (quotIndicator F s κ)))
      (coeffOne F I I T (siteIndicator F κ)) (nearIndices I (F.pos κ) R₀)
      (nearPairs hfin (F.pos κ) R₀) where
  mem_of_ne_zero := fun a b hab => by
    have ha : a ∈ nearIndices I (F.pos κ) R₀ := by
      by_contra h
      exact hab (coeffOne_eq_zero_of_near h₁ hF hI hT (siteIndicator_eq_zero_of_far h))
    refine mem_nearPairs hfin ha ?_
    by_contra h
    exact hab ((h₁ F I I hF hI hI T ρ R₀ hT (siteIndicator F κ) 0 a b 0).2.1.2 h).2.1
  fst_mem := fun p hp => fst_mem_of_mem_nearPairs hfin hp
  injOn_mkQuot := eq_of_mkQuot_eq_near hI hs
  translate_invariant := fun n ι' ι => by
    have h := (h₁ F I I hF hI hI T ρ R₀ hT (liftQuotField F s (quotIndicator F s κ)) 0 ι' ι
      (s • n)).2.2.1.2.2.2.1
    rwa [shiftField_liftQuotField] at h
  eq_on := fun a ha b => coeffOne_congr_near h₁ hF hI hT fun κ'' h =>
    liftQuotField_quotIndicator_eq hF (lt_of_le_of_lt (dist_le_two_mul_of_near ha h) hs)
  eq_zero_off := fun ι' hoff ι =>
    coeffOne_eq_zero_of_near h₁ hF hI hT (liftQuotField_quotIndicator_eq_zero hF hI hoff)
theorem coeffTwo_isPeriodicExtension (h₁ : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hT : IsLocalWith F I I T ρ R₀)
    (hfin : ∀ (y : AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite) (κ κ' : F.Carrier) {s : ℕ}
    (hs : 2 * R₀ + euclidNormVec (F.pos κ - F.pos κ') < s) :
    IsPeriodicExtension I s
      (coeffTwo F I I T (liftQuotField F s (quotIndicator F s κ))
        (liftQuotField F s (quotIndicator F s κ')))
      (coeffTwo F I I T (siteIndicator F κ) (siteIndicator F κ'))
      (nearIndices I (F.pos κ) R₀) (nearPairs hfin (F.pos κ) R₀) where
  mem_of_ne_zero := fun a b hab => by
    have ha : a ∈ nearIndices I (F.pos κ) R₀ := by
      by_contra h
      exact hab (coeffTwo_eq_zero_of_near h₁ hF hI hT _ (siteIndicator_eq_zero_of_far h))
    refine mem_nearPairs hfin ha ?_
    by_contra h
    exact hab ((h₁ F I I hF hI hI T ρ R₀ hT (siteIndicator F κ) (siteIndicator F κ') a b
      0).2.1.2 h).2.2
  fst_mem := fun p hp => fst_mem_of_mem_nearPairs hfin hp
  injOn_mkQuot := eq_of_mkQuot_eq_near hI
    (lt_of_le_of_lt (by linarith [euclidNormVec_nonneg (F.pos κ - F.pos κ')]) hs)
  translate_invariant := fun n ι' ι => by
    have h := (h₁ F I I hF hI hI T ρ R₀ hT (liftQuotField F s (quotIndicator F s κ))
      (liftQuotField F s (quotIndicator F s κ')) ι' ι (s • n)).2.2.1.2.2.2.2
    rwa [shiftField_liftQuotField, shiftField_liftQuotField] at h
  eq_on := fun a ha b => by
    have hd := euclidNormVec_nonneg (F.pos κ - F.pos κ')
    refine coeffTwo_congr_near h₁ hF hI hT (fun κ'' h => ?_) (fun κ'' h => ?_)
    · exact liftQuotField_quotIndicator_eq hF (by linarith [dist_le_two_mul_of_near ha h])
    · refine liftQuotField_quotIndicator_eq hF ?_
      have h1 := euclidNormVec_sub_le_add (F.pos κ'') (F.pos κ) (F.pos κ')
      linarith [dist_le_two_mul_of_near ha h]
  eq_zero_off := fun ι' hoff ι =>
    coeffTwo_eq_zero_of_near h₁ hF hI hT _ (liftQuotField_quotIndicator_eq_zero hF hI hoff)
end Coefficients
section Inverse
variable {I : PeriodicData}
theorem linearMapOfEntries_periodicMatrix_idKernel (h₂ : TorusAction.Claim)
    (h₅ : CovariantFiniteRange.Claim) (hI : IsPeriodic I) {s : ℕ}
    (hs : 0 < s) [Finite (I.QuotMod s)] :
    (linearMapOfEntries (periodicMatrix I I (idKernel I) s) :
      Module.End ℂ (I.QuotMod s → ℂ)) = 1 := by
  refine LinearMap.ext fun g => ?_
  funext c
  induction c using Quot.ind with
  | mk ι' =>
    show linearMapOfEntries (periodicMatrix I I (idKernel I) s) g (I.mkQuot s ι') =
      g (I.mkQuot s ι')
    obtain ⟨C, hC⟩ := Finite.bddAbove_range fun c => ‖g c‖
    have hb : ∃ C : ℝ, ∀ ι, ‖liftQuotField I s g ι‖ ≤ C :=
      ⟨C, fun ι => hC ⟨I.mkQuot s ι, rfl⟩⟩
    have hinv : ∀ (n : Fin 4 → ℤ) ι, liftQuotField I s g (I.translate (s • n) ι) =
        liftQuotField I s g ι := fun n ι => by
      show g (I.mkQuot s (I.translate (s • n) ι)) = g (I.mkQuot s ι)
      rw [mkQuot_translate_nsmul]
    have h := ((h₂ I I hI hI s hs (idKernel I) (h₅.1 I hI).2.1).1
      (liftQuotField I s g) hb hinv).2.2 g (fun ι => rfl) ι'
    rw [linearMapOfEntries_eq_applyKernel, h]
    unfold applyKernel
    rw [tsum_eq_single ι']
    · simp [idKernel, liftQuotField]
    · intro ι hι
      simp [idKernel, Ne.symm hι]
theorem linearMapOfEntries_periodicMatrix_mul_eq_one (h₂ : TorusAction.Claim)
    (h₅ : CovariantFiniteRange.Claim) (hI : IsPeriodic I) {s : ℕ}
    (hs : 0 < s) [Finite (I.QuotMod s)] {K L : I.Carrier → I.Carrier → ℂ}
    (hK : IsPeriodicKernel I I K) (hL : IsPeriodicKernel I I L)
    (hKL : compKernel K L = idKernel I) :
    (linearMapOfEntries (periodicMatrix I I K s) * linearMapOfEntries (periodicMatrix I I L s) :
      Module.End ℂ (I.QuotMod s → ℂ)) = 1 := by
  rw [linearMapOfEntries_mul, ← (h₂ I I hI hI s hs K hK).2 I hI L hL, hKL,
    linearMapOfEntries_periodicMatrix_idKernel h₂ h₅ hI hs]
end Inverse
theorem unitFieldTracesConverge_holds (h₁ : LocalOpFunTaylor.Claim)
    (h₂ : TorusAction.Claim)
    (h₃ : Periodized.Claim)
    (h₄ : LocalTorusMatrices.LocalTorusMatricesClaim)
    (h₅ : CovariantFiniteRange.Claim)
    (h₆ : Quotients.QuotientTransposeNorm)
    (h₇ : OpFunKernels.Claim) : UnitFieldTracesConverge := by
  intro F I hF hI T ρ R₀ hT R hR hTR hRT
  have hfin : ∀ (y : AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite := (h₅.1 I hI).1
  have hT0 : IsPeriodicKernel I I (coeffZero F I I T) :=
    (h₇ F I I hF hI hI T ⟨ρ, R₀, hT⟩).1.periodic
  have hinv : ∀ s : ℕ, 0 < s →
      IsUnit (LogDetSecondDerivs.quotOperator F I T s 0) ∧
      Ring.inverse (LogDetSecondDerivs.quotOperator F I T s 0) =
        linearMapOfEntries (periodicMatrix I I R s) := by
    intro s hs
    have : Finite (I.QuotMod s) := (h₆ I I hI hI s hs).1.2.1
    have p₁ := linearMapOfEntries_periodicMatrix_mul_eq_one h₂ h₅ hI hs hT0 hR hTR
    have p₂ := linearMapOfEntries_periodicMatrix_mul_eq_one h₂ h₅ hI hs hR hT0 hRT
    let u : (Module.End ℂ (I.QuotMod s → ℂ))ˣ := ⟨_, _, p₁, p₂⟩
    have e : LogDetSecondDerivs.quotOperator F I T s 0 = u := rfl
    refine ⟨e ▸ u.isUnit, ?_⟩
    rw [e, Ring.inverse_unit]
    rfl
  refine ⟨?_, fun κ κ' => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with s hs using (hinv s hs).1
  · set S := nearPairs hfin (F.pos κ) R₀ with hS
    set S' := nearPairs hfin (F.pos κ') R₀ with hS'
    set A := coeffOne F I I T (siteIndicator F κ) with hA
    set A' := coeffOne F I I T (siteIndicator F κ') with hA'
    set B := coeffTwo F I I T (siteIndicator F κ) (siteIndicator F κ') with hB
    set d := euclidNormVec (F.pos κ - F.pos κ') with hd
    have hR0 : ∀ R₁ : ℝ, ∀ᶠ s : ℕ in atTop, R₁ < s := fun R₁ =>
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop R₁)
    have hk : kernelTraceDefect F I T R (siteIndicator F κ) (siteIndicator F κ') =
        (∑ p ∈ S, B p.1 p.2 * R p.2 p.1) -
          ∑ p ∈ S, ∑ q ∈ S', A p.1 p.2 * A' q.1 q.2 * R p.2 q.1 * R q.2 p.1 := by
      have sA := (coeffOne_isPeriodicExtension h₁ hF hI hT hfin κ
        (s := ⌈2 * R₀⌉₊ + 1) (by push_cast; linarith [Nat.le_ceil (2 * R₀)])).mem_of_ne_zero
      have sA' := (coeffOne_isPeriodicExtension h₁ hF hI hT hfin κ'
        (s := ⌈2 * R₀⌉₊ + 1) (by push_cast; linarith [Nat.le_ceil (2 * R₀)])).mem_of_ne_zero
      have sB := (coeffTwo_isPeriodicExtension h₁ hF hI hT hfin κ κ'
        (s := ⌈2 * R₀ + d⌉₊ + 1)
        (by push_cast; linarith [Nat.le_ceil (2 * R₀ + d)])).mem_of_ne_zero
      unfold kernelTraceDefect
      rw [diagSum_comp_finiteSupport S R _ sB, diagSum_comp_comp_finiteSupport S S' R _ _ sA sA']
    have hev : ∀ᶠ s : ℕ in atTop,
        quotTraceDefect F I T s (quotIndicator F s κ) (quotIndicator F s κ') =
          (∑ p ∈ S, B p.1 p.2 * periodization I I R s p.2 p.1) -
            ∑ p ∈ S, ∑ q ∈ S', A p.1 p.2 * A' q.1 q.2 * periodization I I R s p.2 q.1 *
              periodization I I R s q.2 p.1 := by
      filter_upwards [eventually_gt_atTop 0, hR0 (4 * R₀), hR0 (2 * R₀ + d), hR0 (2 * R₀)]
        with s hs0 h4 h2 h2'
      have : Finite (I.QuotMod s) := (h₆ I I hI hI s hs0).1.2.1
      have hM := (h₄ F I I hF hI hI T ρ R₀ hT s hs0 h4).1
      obtain ⟨-, C, δ, hC, hδ, hbd⟩ := id hR
      have hfacts := h₃ I I hI hI R δ hR ⟨hδ, C, hC, hbd⟩
      have eA : periodicCoeffOneMatrix F I T s (quotIndicator F s κ) = _ :=
        (coeffOne_isPeriodicExtension h₁ hF hI hT hfin κ h2').linearMap_eq hI
          (hM (quotIndicator F s κ) 0 _ (Or.inr (Or.inr (Or.inl rfl)))).2
      have eA' : periodicCoeffOneMatrix F I T s (quotIndicator F s κ') = _ :=
        (coeffOne_isPeriodicExtension h₁ hF hI hT hfin κ' h2').linearMap_eq hI
          (hM (quotIndicator F s κ') 0 _ (Or.inr (Or.inr (Or.inl rfl)))).2
      have eB : periodicCoeffTwoMatrix F I T s (quotIndicator F s κ) (quotIndicator F s κ') = _ :=
        (coeffTwo_isPeriodicExtension h₁ hF hI hT hfin κ κ' h2).linearMap_eq hI
          (hM (quotIndicator F s κ) (quotIndicator F s κ') _ (Or.inr (Or.inr (Or.inr rfl)))).2
      have hent : ∀ a b : I.Carrier,
          (linearMapOfEntries (periodicMatrix I I R s) : Module.End ℂ (I.QuotMod s → ℂ))
            (Pi.single (I.mkQuot s a) 1) (I.mkQuot s b) = periodization I I R s b a := by
        intro a b
        rw [linearMapOfEntries_single]
        exact hfacts.matrix_entries s hs0 b a
      unfold quotTraceDefect
      rw [(hinv s hs0).2, eA, eA', eB, trace_mul_weightedBasisSum,
        trace_mul_weightedBasisSum_mul_weightedBasisSum]
      simp only [hent]
      rfl
    have hlim := tendsto_periodization h₃ hI hR
    rw [hk]
    refine Tendsto.congr' (hev.mono fun s e => e.symm) ?_
    exact Tendsto.sub (tendsto_finsetSum _ fun p _ => (hlim _ _).const_mul _)
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ =>
        ((hlim _ _).const_mul _).mul (hlim _ _))
end YangMills.Construction.PeriodicOperators.QuotTraceLimits
end
