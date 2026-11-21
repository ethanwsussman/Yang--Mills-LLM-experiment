import YangMills.Construction.TransferOperators.ReflectionInTransportedVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators.TransportedReflection
open Set YangMills.Construction.InfiniteLattice
variable {μ : Fin 4}
def halfIntegerMirror (μ : Fin 4) (i : ℤ) : NormalFamilies.NormalLevelPair 1 where
  normal := PeriodicLattice.coordVec μ
  normal_mem := Or.inl ⟨μ, rfl⟩
  level := (i : ℝ) + 1 / 2
  allowed := by
    have hsq : NormalFamilies.normSq (PeriodicLattice.coordVec μ) = 1 := by
      rw [NormalFamilies.normSq_eq_dotProduct]
      simp [PeriodicLattice.coordVec]
    refine ⟨fun _ => ⟨2 * i + 1, ?_⟩, fun h => ?_⟩
    · push_cast
      ring
    · rw [hsq] at h
      norm_num at h
theorem parallelTransport_lower (S : Stack) (U : GaugeField 1) (y : SliceSite μ) :
    S.parallelTransport μ U (S.lower + ((0 : ℕ) : ℤ)) y = 1 := by
  simp [Stack.parallelTransport]
theorem parallelTransport_succ (S : Stack) (U : GaugeField 1) (y : SliceSite μ) (n : ℕ) :
    S.parallelTransport μ U (S.lower + ((n + 1 : ℕ) : ℤ)) y =
      S.parallelTransport μ U (S.lower + (n : ℤ)) y * temporalLinkVariable μ U (S.lower + (n : ℤ)) y := by
  have hm : ∀ m : ℕ, (S.lower + (m : ℤ) - S.lower).toNat = m := fun m => by simp
  simp only [Stack.parallelTransport, hm, List.range_succ, List.map_append, List.prod_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
theorem parallelTransport_of_reversed (S : Stack) (U V : GaugeField 1) (y : SliceSite μ) (N : ℕ)
    (h : ∀ n : ℕ, n < N → temporalLinkVariable μ V (S.lower + (n : ℤ)) y =
      (temporalLinkVariable μ U (S.lower + ((N - 1 - n : ℕ) : ℤ)) y)⁻¹) (n : ℕ) (hn : n ≤ N) :
    S.parallelTransport μ V (S.lower + (n : ℤ)) y =
      (S.parallelTransport μ U (S.lower + (N : ℤ)) y)⁻¹ *
        S.parallelTransport μ U (S.lower + ((N - n : ℕ) : ℤ)) y := by
  induction n with
  | zero =>
    rw [parallelTransport_lower, Nat.sub_zero, inv_mul_cancel]
  | succ n ih =>
    obtain ⟨m, hm⟩ : ∃ m, N - n = m + 1 := ⟨N - n - 1, by omega⟩
    have hm₂ : N - (n + 1) = m := by omega
    have hm₃ : N - 1 - n = m := by omega
    have ih' := ih (by omega)
    have hn' := h n (by omega)
    rw [hm, parallelTransport_succ] at ih'
    rw [hm₃] at hn'
    rw [parallelTransport_succ, ih', hn', hm₂]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
section Reflection
variable (θ : LatticeSymmetry 1) {i : ℤ} (hθ : θ.toFun = linkMirrorReflection μ i)
include hθ
theorem pointMap_pointAtLevel (j : ℤ) (y : SliceSite μ) :
    θ.pointMap (pointAtLevel μ j y) = pointAtLevel μ (reflectedLevel i j) y := by
  apply Subtype.ext
  change θ.toFun _ = _
  rw [hθ]
  exact linkMirrorReflection_pointAtLevel μ i j y
theorem linkMap_spatialLink (j : ℤ) (b : SliceLink μ) :
    θ.linkMap (spatialLink μ j b).1 = (spatialLink μ (reflectedLevel i j) b).1 :=
  InfiniteLattice.Link.ext (pointMap_pointAtLevel θ hθ j b.source)
    (pointMap_pointAtLevel θ hθ j b.target)
theorem linkMap_temporalLink (j : ℤ) (y : SliceSite μ) :
    θ.linkMap (temporalLink μ j y).1 = (temporalLink μ (reflectedLevel i j - 1) y).1.opposite := by
  apply InfiniteLattice.Link.ext
  · change θ.pointMap (pointAtLevel μ j y) = pointAtLevel μ (reflectedLevel i j - 1 + 1) y
    rw [pointMap_pointAtLevel θ hθ, sub_add_cancel]
  · change θ.pointMap (pointAtLevel μ (j + 1) y) = pointAtLevel μ (reflectedLevel i j - 1) y
    rw [pointMap_pointAtLevel θ hθ]
    congr 1
    simp only [reflectedLevel]
    ring
theorem spatialLinkVariable_pullback (U : GaugeField 1) (j : ℤ) (b : SliceLink μ) :
    spatialLinkVariable μ (θ.pullbackField U) j b = spatialLinkVariable μ U (reflectedLevel i j) b := by
  change U (θ.linkMap (spatialLink μ j b).1) = _
  rw [linkMap_spatialLink θ hθ]
  rfl
theorem temporalLinkVariable_pullback (U : GaugeField 1) (j : ℤ) (y : SliceSite μ) :
    temporalLinkVariable μ (θ.pullbackField U) j y =
      (temporalLinkVariable μ U (reflectedLevel i j - 1) y)⁻¹ := by
  change U (θ.linkMap (temporalLink μ j y).1) = _
  rw [linkMap_temporalLink θ hθ]
  exact U.2 _
theorem parallelTransport_pullback {k : ℤ} (S : Stack) (hb : S.lower = i - k + 1) (ht : S.upper = i + k)
    (U : GaugeField 1) {j : ℤ} (h₁ : i - k + 1 ≤ j) (h₂ : j ≤ i + k) (y : SliceSite μ) :
    S.parallelTransport μ (θ.pullbackField U) j y =
      (S.parallelTransport μ U S.upper y)⁻¹ * S.parallelTransport μ U (reflectedLevel i j) y := by
  have hlt := S.lower_lt_upper
  rw [hb, ht] at hlt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = 2 * k - 1 := ⟨(2 * k - 1).toNat, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = j - (i - k + 1) := ⟨(j - (i - k + 1)).toNat, by omega⟩
  have hnN : n ≤ N := by omega
  have hj : S.lower + (n : ℤ) = j := by
    rw [hb]
    omega
  have hup : S.lower + (N : ℤ) = S.upper := by
    rw [hb, ht]
    omega
  have hmid : S.lower + ((N - n : ℕ) : ℤ) = reflectedLevel i j := by
    rw [hb, Nat.cast_sub hnN]
    simp only [reflectedLevel]
    omega
  have key := parallelTransport_of_reversed S U (θ.pullbackField U) y N (fun m hm => by
    rw [temporalLinkVariable_pullback θ hθ]
    congr 2
    rw [hb, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp only [reflectedLevel]
    push_cast
    omega) n hnN
  rwa [hj, hup, hmid] at key
theorem reflectedLinkVariablesAt_of_mem {k : ℤ} (S : Stack) (hb : S.lower = i - k + 1)
    (ht : S.upper = i + k) (U : GaugeField 1) {j : ℤ} (h₁ : i - k + 1 ≤ j) (h₂ : j ≤ i + k) :
    ReflectedLinkVariablesAt μ i S U (θ.pullbackField U) j := by
  refine ⟨spatialLinkVariable_pullback θ hθ U j, temporalLinkVariable_pullback θ hθ U j,
    parallelTransport_pullback θ hθ S hb ht U h₁ h₂, fun b => ?_⟩
  simp only [Stack.transportedLinkVariable]
  rw [parallelTransport_pullback θ hθ S hb ht U h₁ h₂ b.source,
    parallelTransport_pullback θ hθ S hb ht U h₁ h₂ b.target, spatialLinkVariable_pullback θ hθ]
  simp only [mul_inv_rev, inv_inv, mul_assoc]
theorem reflectionSwapsLevels_of_eq (k : ℤ) (hk : 1 ≤ k) :
    ReflectionSwapsLevels (μ := μ) θ i k hk := by
  intro v _ Ψ X _ _ _ hinv hX U
  refine ⟨?_, rfl⟩
  have e : (fun p : centeredLinkPairs i k v => (centeredStack i k hk).transportedLinkVariable μ
      (θ.pullbackField U) p.1.1 p.1.2) =
      diagonalGaugeAct (snd_mem_linksWithin i k v)
        (fun y : v => ((centeredStack i k hk).parallelTransport μ U (centeredStack i k hk).upper y.1)⁻¹)
        (fun p : centeredLinkPairs i k v => (centeredStack i k hk).transportedLinkVariable μ U
          (reflectedLevel i p.1.1) p.1.2) := by
    funext p
    rw [(reflectedLinkVariablesAt_of_mem θ hθ (centeredStack i k hk) rfl rfl U p.2.1
      p.2.2.1).2.2.2 p.1.2]
    simp only [diagonalGaugeAct, inv_inv]
  change X (θ.pullbackField U) = _
  rw [hX, e, hinv]
end Reflection
theorem reflectionOnTransportedVariables_proof : ReflectionOnTransportedVariables := by
  intro μ i k hk
  have hθ : (halfIntegerMirror μ i).reflectSymmetry.toFun = linkMirrorReflection μ i := rfl
  refine ⟨(halfIntegerMirror μ i).reflectSymmetry, hθ, fun U j h₁ h₂ => ?_,
    reflectionSwapsLevels_of_eq _ hθ k hk⟩
  exact reflectedLinkVariablesAt_of_mem _ hθ (centeredStack i k hk) rfl rfl U h₁ h₂
end YangMills.Construction.TransferOperators.TransportedReflection
end
