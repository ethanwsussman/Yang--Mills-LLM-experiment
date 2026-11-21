import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.SumsThatAgreeNearAPointProof
import YangMills.Construction.HoleBesideASecondHole.LinesAndStripsOfALatticeField
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMeanProof
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOneProof
import YangMills.Construction.ResponseInTheExpansion.RestAtACurvature
import YangMills.Construction.ResponseInTheExpansion.RestFreezes
import YangMills.Construction.ResponseInTheExpansion.RestHasTwoDerivatives
import YangMills.Construction.ResponseInTheExpansion.RestIsGaugeInvariant
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfMeansConvergeProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.FamilyNorms YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses
namespace YangMills.Construction.ResponseInTheExpansion
private abbrev LatticeOffset : Type := Fin 4 → ℤ
private theorem coe_smul_imag (s : ℝ) (X : imaginaryQuaternions) :
    ((s • X : imaginaryQuaternions) : Quaternion ℝ) = s • (X : Quaternion ℝ) := rfl
private def expAlong (X : imaginaryQuaternions) (s : ℝ) : UnitQuaternion := expUnit (s • X)
private theorem expAlong_add (X : imaginaryQuaternions) (s t : ℝ) :
    expAlong X (s + t) = expAlong X s * expAlong X t := by
  let +nondep : NormedAlgebra ℚ (Quaternion ℝ) := .restrictScalars ℚ ℝ _
  apply Subtype.ext
  show NormedSpace.exp (((s + t) • X : imaginaryQuaternions) : Quaternion ℝ) =
    NormedSpace.exp ((s • X : imaginaryQuaternions) : Quaternion ℝ) *
      NormedSpace.exp ((t • X : imaginaryQuaternions) : Quaternion ℝ)
  rw [coe_smul_imag, coe_smul_imag, coe_smul_imag, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)
private theorem expAlong_zero (X : imaginaryQuaternions) : expAlong X 0 = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((0 : ℝ) • X : imaginaryQuaternions) : Quaternion ℝ) = 1
  simp
private theorem expAlong_inv (X : imaginaryQuaternions) (s : ℝ) : (expAlong X s)⁻¹ = expAlong X (-s) := by
  have h : expAlong X s * expAlong X (-s) = 1 := by
    rw [← expAlong_add, add_neg_cancel, expAlong_zero]
  exact inv_eq_of_mul_eq_one_right h
private theorem re_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : Quaternion ℝ).re = Real.cos ‖w‖ := by apply _root_.YangMills.SharedProofs.p42298 <;> assumption
private theorem norm_expUnit_sub_one (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ ‖w‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
private theorem norm_expAlong_sub_one (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (s : ℝ) :
    ‖((expAlong X s : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ |s| := by
  have := norm_expUnit_sub_one (s • X)
  rwa [norm_smul, hX, mul_one, Real.norm_eq_abs] at this
private theorem expAlong_two_pi_mul (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (k : ℤ) :
    expAlong X ((k : ℝ) * (2 * Real.pi)) = 1 := by
  set s : ℝ := (k : ℝ) * (2 * Real.pi) with hs
  have hre : ((s • X : imaginaryQuaternions) : Quaternion ℝ).re = 0 := (s • X).2
  have hn : ‖((s • X : imaginaryQuaternions) : Quaternion ℝ)‖ = |s| := by
    have : ‖(s • X : imaginaryQuaternions)‖ = |s| := by rw [norm_smul, hX, mul_one, Real.norm_eq_abs]
    exact this
  have hcos : Real.cos |s| = 1 := by
    rw [Real.cos_abs, hs, Real.cos_eq_one_iff]
    exact ⟨k, rfl⟩
  have hsin0 : Real.sin s = 0 := by
    rw [Real.sin_eq_zero_iff]
    exact ⟨2 * k, by rw [hs]; push_cast; ring⟩
  have hsin : Real.sin |s| = 0 := by
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, hsin0]
    · rw [h, Real.sin_neg, hsin0, neg_zero]
  apply Subtype.ext
  show NormedSpace.exp ((s • X : imaginaryQuaternions) : Quaternion ℝ) = 1
  rw [Quaternion.exp_of_re_eq_zero _ hre, hn, hcos, hsin]
  simp
private theorem exists_int_of_expAlong_eq_one (X : imaginaryQuaternions) (hX : ‖X‖ = 1) {s : ℝ}
    (h : expAlong X s = 1) : ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = s := by
  have h1 : ((expAlong X s : UnitQuaternion) : Quaternion ℝ).re = 1 := by rw [h]; rfl
  have h2 : ((expAlong X s : UnitQuaternion) : Quaternion ℝ).re = Real.cos ‖(s • X : imaginaryQuaternions)‖ :=
    re_expUnit _
  rw [h2, norm_smul, hX, mul_one, Real.norm_eq_abs, Real.cos_abs] at h1
  exact (Real.cos_eq_one_iff s).1 h1
private def intPrefixSum {G : Type} [AddCommGroup G] (f : ℤ → G) : ℤ → G
  | Int.ofNat m => ∑ r ∈ Finset.range m, f r
  | Int.negSucc m => - ∑ r ∈ Finset.range (m + 1), f (-((r : ℤ) + 1))
private theorem intPrefixSum_zero {G : Type} [AddCommGroup G] (f : ℤ → G) : intPrefixSum f 0 = 0 := by
  show ∑ r ∈ Finset.range 0, f r = 0
  simp
private theorem intPrefixSum_succ {G : Type} [AddCommGroup G] (f : ℤ → G) (k : ℤ) :
    intPrefixSum f (k + 1) = intPrefixSum f k + f k := by
  rcases k with m | m
  · show ∑ r ∈ Finset.range (m + 1), f r = ∑ r ∈ Finset.range m, f r + f (Int.ofNat m)
    rw [Finset.sum_range_succ]
    rfl
  · rcases m with _ | m
    · have e : Int.negSucc 0 + 1 = 0 := rfl
      rw [e, intPrefixSum_zero]
      show (0 : G) = - ∑ r ∈ Finset.range (0 + 1), f (-((r : ℤ) + 1)) + f (Int.negSucc 0)
      have e2 : Int.negSucc 0 = -(((0 : ℕ) : ℤ) + 1) := rfl
      simp [e2]
    · have e : Int.negSucc (m + 1) + 1 = Int.negSucc m := by
        simp only [Int.negSucc_eq]
        push_cast
        try ring
      rw [e]
      show - ∑ r ∈ Finset.range (m + 1), f (-((r : ℤ) + 1)) =
        - ∑ r ∈ Finset.range (m + 1 + 1), f (-((r : ℤ) + 1)) + f (Int.negSucc (m + 1))
      have e2 : Int.negSucc (m + 1) = -(((m + 1 : ℕ) : ℤ) + 1) := by
        simp only [Int.negSucc_eq]
      rw [Finset.sum_range_succ _ (m + 1), e2]
      abel
private theorem eq_zero_of_shift_invariant {G : Type} [AddCommGroup G] (u : ℤ → G) (h0 : u 0 = 0)
    (h : ∀ k, u (k + 1) = u k) (k : ℤ) : u k = 0 := by
  induction k using Int.induction_on with
  | zero => exact h0
  | succ i ih => rw [h, ih]
  | pred i ih =>
    have := h (-(i : ℤ) - 1)
    rw [sub_add_cancel] at this
    rw [← this, ih]
private abbrev basisOffset (i : Fin 4) : LatticeOffset := Pi.single i 1
private theorem update_succ_eq (h : LatticeOffset) (i : Fin 4) (k : ℤ) :
    Function.update h i (k + 1) = Function.update h i k + basisOffset i := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [basisOffset]
  · simp [basisOffset, Function.update_of_ne hl, Pi.single_eq_of_ne hl]
abbrev _root_.YangMills.DeltaSharedProofs.p502038 := @update_succ_eq
private theorem update_add_basis_of_ne (h : LatticeOffset) {i j : Fin 4} (hij : j ≠ i) (k : ℤ) :
    Function.update (h + basisOffset j) i k = Function.update h i k + basisOffset j := by apply _root_.YangMills.Construction.LatticeGauge.update_add_unitVec_of_ne <;> assumption
private theorem update_add_basis_self (h : LatticeOffset) (i : Fin 4) (k : ℤ) :
    Function.update (h + basisOffset i) i k = Function.update h i k := by apply _root_.YangMills.Construction.LatticeGauge.update_add_unitVec_self <;> assumption
private theorem exists_primitive_of_support {G : Type} [AddCommGroup G] (S : Finset (Fin 4)) :
    ∀ a : Fin 4 → LatticeOffset → G,
      (∀ i j h, a i (h + basisOffset j) - a i h = a j (h + basisOffset i) - a j h) →
      (∀ i, i ∉ S → a i = 0) → ∃ ψ : LatticeOffset → G, ∀ h i, ψ (h + basisOffset i) - ψ h = a i h := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a _ h0
    exact ⟨0, fun h i => by simp [h0 i (by simp)]⟩
  | insert i S hi ih =>
    intro a hc h0
    set a' : Fin 4 → LatticeOffset → G := fun j h => if j = i then 0 else a j (Function.update h i 0) with ha'
    have hc' : ∀ j k h, a' j (h + basisOffset k) - a' j h = a' k (h + basisOffset j) - a' k h := by
      intro j k h
      by_cases hj : j = i
      · by_cases hk : k = i
        · simp [ha', hj, hk]
        · subst hj
          simp [ha', hk, update_add_basis_self]
      · by_cases hk : k = i
        · subst hk
          simp [ha', hj, update_add_basis_self]
        · simp only [ha', hj, hk, if_false, update_add_basis_of_ne _ hk, update_add_basis_of_ne _ hj]
          exact hc j k _
    have h0' : ∀ j, j ∉ S → a' j = 0 := by
      intro j hj
      funext h
      by_cases hji : j = i
      · simp [ha', hji]
      · have : a j = 0 := h0 j (by simp [hj, hji])
        simp [ha', hji, this]
    obtain ⟨ψ, hψ⟩ := ih a' hc' h0'
    set I : LatticeOffset → G := fun h => intPrefixSum (fun k => a i (Function.update h i k)) (h i) with hI
    refine ⟨fun h => I h + ψ h, fun h j => ?_⟩
    by_cases hji : j = i
    · subst hji
      have e1 : I (h + basisOffset j) = I h + a j h := by
        simp only [hI, update_add_basis_self]
        have e2 : (h + basisOffset j) j = h j + 1 := by simp [basisOffset]
        rw [e2, intPrefixSum_succ, Function.update_eq_self]
      have e3 : ψ (h + basisOffset j) - ψ h = 0 := by rw [hψ]; simp [ha']
      show I (h + basisOffset j) + ψ (h + basisOffset j) - (I h + ψ h) = a j h
      rw [e1]
      have e4 : ψ (h + basisOffset j) = ψ h := sub_eq_zero.1 e3
      rw [e4]
      abel
    · have e1 : I (h + basisOffset j) - I h = a j h - a j (Function.update h i 0) := by
        set u : ℤ → G := fun k => intPrefixSum (fun r => a i (Function.update (h + basisOffset j) i r)) k -
          intPrefixSum (fun r => a i (Function.update h i r)) k -
          (a j (Function.update h i k) - a j (Function.update h i 0)) with hu
        have hu0 : u 0 = 0 := by simp [hu, intPrefixSum_zero]
        have hus : ∀ k, u (k + 1) = u k := by
          intro k
          simp only [hu, intPrefixSum_succ, update_succ_eq, update_add_basis_of_ne _ hji]
          have := hc i j (Function.update h i k)
          have e5 : a i (Function.update h i k + basisOffset j) = a i (Function.update h i k) +
              (a j (Function.update h i k + basisOffset i) - a j (Function.update h i k)) := by
            rw [← this]
            abel
          rw [e5]
          abel
        have := eq_zero_of_shift_invariant u hu0 hus (h i)
        simp only [hu, Function.update_eq_self] at this
        have e6 : (h + basisOffset j) i = h i := by simp [basisOffset, Pi.single_eq_of_ne (Ne.symm hji)]
        simp only [hI, e6]
        exact sub_eq_zero.1 this
      have e2 : ψ (h + basisOffset j) - ψ h = a j (Function.update h i 0) := by
        rw [hψ]
        simp [ha', hji]
      show I (h + basisOffset j) + ψ (h + basisOffset j) - (I h + ψ h) = a j h
      calc I (h + basisOffset j) + ψ (h + basisOffset j) - (I h + ψ h)
          = (I (h + basisOffset j) - I h) + (ψ (h + basisOffset j) - ψ h) := by abel
        _ = a j h := by rw [e1, e2]; abel
private theorem exists_primitive_of_closed {G : Type} [AddCommGroup G] (a : Fin 4 → LatticeOffset → G)
    (hc : ∀ i j h, a i (h + basisOffset j) - a i h = a j (h + basisOffset i) - a j h) :
    ∃ ψ : LatticeOffset → G, ∀ h i, ψ (h + basisOffset i) - ψ h = a i h :=
  exists_primitive_of_support Finset.univ a hc fun i hi => absurd (Finset.mem_univ i) hi
section LineDerivatives
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
private theorem fderiv_apply_eval {G : E' → (E →L[ℝ] ℝ)} (hG : DifferentiableAt ℝ G 0) (u : E') (w : E) :
    fderiv ℝ (fun z => G z w) 0 u = fderiv ℝ G 0 u w := by
  have h := ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt (x := G 0)).comp (0 : E') hG.hasFDerivAt
  have h2 : HasFDerivAt (fun z => G z w) ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ G 0)) 0 := h
  rw [h2.fderiv]
  rfl
private theorem differentiableAt_fderiv_of_contDiffAt {Φ : E → ℝ} {z : E} (hΦ : ContDiffAt ℝ 2 Φ z) :
    DifferentiableAt ℝ (fderiv ℝ Φ) z :=
  (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
private theorem fderiv_comp_clm_apply {Φ : E → ℝ} (hΦ : ContDiffAt ℝ 2 Φ 0) (ι : E' →L[ℝ] E) (u : E') :
    fderiv ℝ (Φ ∘ ι) 0 u = fderiv ℝ Φ 0 (ι u) := by
  have hd : DifferentiableAt ℝ Φ (ι 0) := by
    rw [map_zero]
    exact hΦ.differentiableAt (by norm_num)
  rw [fderiv_comp _ hd ι.differentiableAt, ι.fderiv, map_zero]
  rfl
private theorem fderiv_fderiv_comp_clm_apply {Φ : E → ℝ} (hΦ : ContDiffAt ℝ 2 Φ 0) (ι : E' →L[ℝ] E) (u w : E') :
    fderiv ℝ (fderiv ℝ (Φ ∘ ι)) 0 u w = fderiv ℝ (fderiv ℝ Φ) 0 (ι u) (ι w) := by
  have hι : ContDiffAt ℝ 2 (Φ ∘ ι) 0 := by
    have h0 : ContDiffAt ℝ 2 Φ (ι 0) := by rwa [map_zero]
    exact h0.comp 0 ι.contDiff.contDiffAt
  have hev : ∀ᶠ z in nhds (0 : E'), DifferentiableAt ℝ Φ (ι z) := by
    have h1 : ∀ᶠ y in nhds (0 : E), ContDiffAt ℝ 2 Φ y := hΦ.eventually (by simp)
    have h2 : Filter.Tendsto ι (nhds 0) (nhds 0) := by
      have := ι.continuous.tendsto 0
      rwa [map_zero] at this
    exact (h2.eventually h1).mono fun z hz => hz.differentiableAt (by norm_num)
  have heq : (fun z => fderiv ℝ (Φ ∘ ι) z w) =ᶠ[nhds 0] fun z => fderiv ℝ Φ (ι z) (ι w) := by
    refine hev.mono fun z hz => ?_
    show fderiv ℝ (Φ ∘ ι) z w = _
    rw [fderiv_comp _ hz ι.differentiableAt, ι.fderiv]
    rfl
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) (ι 0) := by
    rw [map_zero]
    exact differentiableAt_fderiv_of_contDiffAt hΦ
  have hev2 : DifferentiableAt ℝ (fun y => fderiv ℝ Φ y (ι w)) (ι 0) :=
    hD.clm_apply (differentiableAt_const _)
  calc fderiv ℝ (fderiv ℝ (Φ ∘ ι)) 0 u w = fderiv ℝ (fun z => fderiv ℝ (Φ ∘ ι) z w) 0 u :=
        (fderiv_apply_eval (differentiableAt_fderiv_of_contDiffAt hι) u w).symm
    _ = fderiv ℝ (fun z => fderiv ℝ Φ (ι z) (ι w)) 0 u := by rw [heq.fderiv_eq]
    _ = fderiv ℝ (fun y => fderiv ℝ Φ y (ι w)) 0 (ι u) := by
        have : (fun z => fderiv ℝ Φ (ι z) (ι w)) = (fun y => fderiv ℝ Φ y (ι w)) ∘ ι := rfl
        rw [this, fderiv_comp _ hev2 ι.differentiableAt, ι.fderiv, map_zero]
        rfl
    _ = fderiv ℝ (fderiv ℝ Φ) 0 (ι u) (ι w) := fderiv_apply_eval (differentiableAt_fderiv_of_contDiffAt hΦ) _ _
private theorem derivatives_along_line {Φ : E → ℝ} (hΦ : ContDiffAt ℝ 2 Φ 0) (φ : ℝ → ℝ) (v₀ : ℝ) (α : E)
    (hφ : ∀ s, φ (s + v₀) = Φ (s • α)) :
    ContDiffAt ℝ 2 φ v₀ ∧ deriv φ v₀ = fderiv ℝ Φ 0 α ∧ deriv (deriv φ) v₀ = fderiv ℝ (fderiv ℝ Φ) 0 α α := by
  set ι : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ α with hι
  have hι1 : ι 1 = α := by simp [hι]
  have hψ : (fun s => φ (s + v₀)) = Φ ∘ ι := by
    funext s
    simp [hι, hφ]
  have hψc : ContDiffAt ℝ 2 (Φ ∘ ι) 0 := by
    have h0 : ContDiffAt ℝ 2 Φ (ι 0) := by rwa [map_zero]
    exact h0.comp 0 ι.contDiff.contDiffAt
  have hφeq : φ = (Φ ∘ ι) ∘ fun v => v - v₀ := by
    funext v
    have := congrFun hψ (v - v₀)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [hφeq]
    have h0 : ContDiffAt ℝ 2 (Φ ∘ ι) ((fun v => v - v₀) v₀) := by simpa using hψc
    have hs : ContDiffAt ℝ 2 (fun v : ℝ => v - v₀) v₀ := contDiffAt_id.sub contDiffAt_const
    exact ContDiffAt.comp (g := Φ ∘ ι) (f := fun v : ℝ => v - v₀) v₀ h0 hs
  · have e1 : deriv (fun s => φ (s + v₀)) 0 = deriv φ (0 + v₀) := deriv_comp_add_const φ v₀ 0
    rw [zero_add] at e1
    rw [← e1, hψ]
    show fderiv ℝ (Φ ∘ ι) 0 1 = _
    rw [fderiv_comp_clm_apply hΦ, hι1]
  · have e1 : deriv (fun s => φ (s + v₀)) = fun s => deriv φ (s + v₀) := by
      funext s
      exact deriv_comp_add_const φ v₀ s
    have e2 : deriv (fun s => deriv φ (s + v₀)) 0 = deriv (deriv φ) (0 + v₀) :=
      deriv_comp_add_const (deriv φ) v₀ 0
    rw [zero_add] at e2
    rw [← e2, ← e1, hψ]
    show fderiv ℝ (fun s => fderiv ℝ (Φ ∘ ι) s 1) 0 1 = _
    rw [fderiv_apply_eval (differentiableAt_fderiv_of_contDiffAt hψc), fderiv_fderiv_comp_clm_apply hΦ, hι1]
end LineDerivatives
private theorem bilinear_expand_basis {k : ℕ} (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) (α : Fin k → ℝ) :
    B α α = ∑ l, ∑ l', α l * α l' * B (Pi.single l 1) (Pi.single l' 1) := by
  have hα : α = ∑ l, α l • (Pi.single l 1 : Fin k → ℝ) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hα]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring
private theorem linear_expand_basis {k : ℕ} (B : (Fin k → ℝ) →L[ℝ] ℝ) (α : Fin k → ℝ) :
    B α = ∑ l, α l * B (Pi.single l 1) := by apply _root_.YangMills.SharedProofs.p81775 <;> assumption
section BondLists
variable {F : BlockFrame} {j k : ℕ}
private theorem bondSpread_pair (c : Fin k → F.Site j × Fin 4) (X : imaginaryQuaternions) (l l' : Fin k)
    (τ : Fin 2 → ℝ) :
    bondSpread ![c l, c l'] ![X, X] τ =
      bondSpread c (fun _ => X) (τ 0 • (Pi.single l 1 : Fin k → ℝ) + τ 1 • (Pi.single l' 1 : Fin k → ℝ)) := by
  classical
  funext y i
  simp only [bondSpread, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  have key : ∀ (m₀ : Fin k) (r : ℝ), (∑ m, if c m = (y, i) then (r * (Pi.single m₀ 1 : Fin k → ℝ) m) • X else 0) =
      if c m₀ = (y, i) then r • X else 0 := by
    intro m₀ r
    rw [Finset.sum_eq_single m₀]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have split : ∀ m, (if c m = (y, i) then (τ 0 * (Pi.single l 1 : Fin k → ℝ) m +
        τ 1 * (Pi.single l' 1 : Fin k → ℝ) m) • X else 0) =
      (if c m = (y, i) then (τ 0 * (Pi.single l 1 : Fin k → ℝ) m) • X else 0) +
        (if c m = (y, i) then (τ 1 * (Pi.single l' 1 : Fin k → ℝ) m) • X else 0) := by
    intro m
    split_ifs
    · rw [add_smul]
    · simp
  simp only [split, Finset.sum_add_distrib, key]
  congr!
private theorem bondSpread_single (c : Fin k → F.Site j × Fin 4) (X : imaginaryQuaternions) (l : Fin k)
    (τ : Fin 1 → ℝ) :
    bondSpread ![c l] ![X] τ = bondSpread c (fun _ => X) (τ 0 • (Pi.single l 1 : Fin k → ℝ)) := by
  classical
  funext y i
  simp only [bondSpread, Fin.sum_univ_one, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · simp
    congr!
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
private def alongBonds (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4)
    (X : imaginaryQuaternions) : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c (fun _ => X) τ) W)
private theorem bondDeriv_pair_eq (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4)
    (X : imaginaryQuaternions) (h : ContDiffAt ℝ 2 (alongBonds G W c X) 0) (l l' : Fin k) :
    bondDeriv G W ![c l, c l'] ![X, X] =
      fderiv ℝ (fderiv ℝ (alongBonds G W c X)) 0 (Pi.single l 1) (Pi.single l' 1) := by
  set ι : (Fin 2 → ℝ) →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single l 1 : Fin k → ℝ) +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (Pi.single l' 1 : Fin k → ℝ)
    with hι
  have hcomp : (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread ![c l, c l'] ![X, X] τ) W)) =
      alongBonds G W c X ∘ ι := by
    funext τ
    simp only [Function.comp, alongBonds]
    rw [bondSpread_pair]
    simp [hι]
  unfold bondDeriv
  rw [hcomp, iteratedFDeriv_two_apply, fderiv_fderiv_comp_clm_apply h]
  simp [hι]
private theorem bondDeriv_single_eq (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4)
    (X : imaginaryQuaternions) (h : ContDiffAt ℝ 2 (alongBonds G W c X) 0) (l : Fin k) :
    bondDeriv G W ![c l] ![X] = fderiv ℝ (alongBonds G W c X) 0 (Pi.single l 1) := by
  set ι : (Fin 1 → ℝ) →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single l 1 : Fin k → ℝ) with hι
  have hcomp : (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X] τ) W)) = alongBonds G W c X ∘ ι := by
    funext τ
    simp only [Function.comp, alongBonds]
    rw [bondSpread_single]
    simp [hι]
  unfold bondDeriv
  rw [hcomp, iteratedFDeriv_one_apply, fderiv_comp_clm_apply h]
  simp [hι]
private theorem abs_sub_le_of_second_derivatives (G : F.GaugeField j → ℝ) (c : Fin k → F.Site j × Fin 4)
    (X : imaginaryQuaternions) (α : Fin k → ℝ) (W : ℝ → F.GaugeField j) (b : Fin k → Fin k → ℝ)
    (hW : ∀ v s, leftTranslate (bondSpread c (fun _ => X) (s • α)) (W v) = W (s + v))
    (hsm : ∀ v, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ 2 (alongBonds G (W v) c X) 0)
    (hfirst : ∀ l, bondDeriv G (W 0) ![c l] ![X] = 0)
    (hsecond : ∀ v, 0 ≤ v → v ≤ 1 → ∀ l l', |bondDeriv G (W v) ![c l, c l'] ![X, X]| ≤ b l l') :
    |G (W 1) - G (W 0)| ≤ ∑ l, ∑ l', |α l| * |α l'| * b l l' := by
  set φ : ℝ → ℝ := fun v => G (W v) with hφ
  set M : ℝ := ∑ l, ∑ l', |α l| * |α l'| * b l l' with hM
  have hline : ∀ v, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ 2 φ v ∧ deriv φ v = fderiv ℝ (alongBonds G (W v) c X) 0 α ∧
      deriv (deriv φ) v = fderiv ℝ (fderiv ℝ (alongBonds G (W v) c X)) 0 α α := fun v h0 h1 =>
    derivatives_along_line (hsm v h0 h1) φ v α fun s => by
      simp only [hφ, alongBonds]
      rw [hW]
  have hd2 : ∀ v, 0 ≤ v → v ≤ 1 → |deriv (deriv φ) v| ≤ M := by
    intro v h0 h1
    rw [(hline v h0 h1).2.2, bilinear_expand_basis]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l' _ => ?_)
    rw [abs_mul, abs_mul, ← bondDeriv_pair_eq G (W v) c X (hsm v h0 h1) l l']
    exact mul_le_mul_of_nonneg_left (hsecond v h0 h1 l l') (by positivity)
  have hD0 : deriv φ 0 = 0 := by
    rw [(hline 0 le_rfl zero_le_one).2.1, linear_expand_basis]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← bondDeriv_single_eq G (W 0) c X (hsm 0 le_rfl zero_le_one) l, hfirst, mul_zero]
  have hDdiff : ∀ v ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (deriv φ) v := by
    intro v hv
    have h := differentiableAt_fderiv_of_contDiffAt (hline v hv.1 hv.2).1
    exact h.clm_apply (differentiableAt_const (1 : ℝ))
  have hD : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖deriv φ v‖ ≤ M := by
    intro v hv
    have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hDdiff
      (fun y hy => by simpa using hd2 y hy.1 hy.2) (Set.left_mem_Icc.2 zero_le_one) hv
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hd2 0 le_rfl zero_le_one)
    rw [hD0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv.1] at h
    exact h.trans (by nlinarith [hv.2])
  have hφd : ∀ v ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ φ v := fun v hv =>
    (hline v hv.1 hv.2).1.differentiableAt (by norm_num)
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hφd hD
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simpa [hφ] using h
end BondLists
section TorusOffsets
variable {F : BlockFrame}
private def centeredOffset (Y x : F.Cell) : LatticeOffset := fun k => (x k - Y k).valMinAbs
private theorem siteOfCoords_add (j : ℕ) (a b : LatticeOffset) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem add_siteOfCoords_centeredOffset (Y x : F.Cell) : Y + siteOfCoords F.top (centeredOffset Y x) = x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.DecayingSums.add_siteOfCoords_offset <;> assumption
private theorem centeredOffset_add (Y : F.Cell) (h : LatticeOffset) (hs : ∀ k, 2 * (h k).natAbs < F.period F.top k) :
    centeredOffset Y (Y + siteOfCoords F.top h) = h := by
  funext k
  have e : (Y + siteOfCoords F.top h : F.Cell) k - Y k = (h k : ZMod (F.period F.top k)) := by
    simp [siteOfCoords]
  have hp := hs k
  have : NeZero (F.period F.top k) := ⟨by omega⟩
  show ((Y + siteOfCoords F.top h : F.Cell) k - Y k).valMinAbs = h k
  rw [e]
  exact (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by constructor <;> omega⟩
private theorem centeredOffset_injective (Y : F.Cell) : Function.Injective (centeredOffset Y) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.DecayingSums.offset_injective <;> assumption
private theorem natAbs_le_offsetNorm (h : LatticeOffset) (k : Fin 4) : (h k).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem offsetNorm_le (h : LatticeOffset) (r : ℕ) (hr : ∀ k, (h k).natAbs ≤ r) : offsetNorm h ≤ r := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNorm_le <;> assumption
private def torusDist (Y x : F.Cell) : ℕ := offsetNorm (centeredOffset Y x)
private theorem natAbs_valMinAbs_unitStep (hp : ∀ k, 3 ≤ F.period F.top k) (i k : Fin 4) :
    ((unitStep F.top i : F.Cell) k).valMinAbs.natAbs ≤ 1 := by
  have h1 : ((unitStep F.top i : F.Cell) k) = (((Pi.single i 1 : LatticeOffset) k : ℤ) : ZMod (F.period F.top k)) := rfl
  have hq := hp k
  have : NeZero (F.period F.top k) := ⟨by omega⟩
  have h2 : (((Pi.single i 1 : LatticeOffset) k : ℤ)).natAbs ≤ 1 := by
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  generalize (Pi.single i 1 : LatticeOffset) k = z at h1 h2
  have h3 : ((z : ℤ) : ZMod (F.period F.top k)).valMinAbs = z :=
    (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by constructor <;> omega⟩
  rw [h1, h3]
  exact h2
private theorem torusDist_add_unitStep_le (hp : ∀ k, 3 ≤ F.period F.top k) (Y x : F.Cell) (i : Fin 4) :
    torusDist Y (x + unitStep F.top i) ≤ torusDist Y x + 1 := by
  refine offsetNorm_le _ _ fun k => ?_
  have e : (x + unitStep F.top i : F.Cell) k - Y k = (x k - Y k) + (unitStep F.top i : F.Cell) k := by
    simp only [Pi.add_apply]
    ring
  show ((x + unitStep F.top i : F.Cell) k - Y k).valMinAbs.natAbs ≤ _
  rw [e]
  refine (ZMod.natAbs_valMinAbs_add_le _ _).trans ((Int.natAbs_add_le _ _).trans ?_)
  have h1 := natAbs_valMinAbs_unitStep hp i k
  have h2 := natAbs_le_offsetNorm (centeredOffset Y x) k
  have h3 : (centeredOffset Y x k).natAbs = (x k - Y k).valMinAbs.natAbs := rfl
  have h4 : torusDist Y x = offsetNorm (centeredOffset Y x) := rfl
  omega
private theorem torusDist_le_add_unitStep (hp : ∀ k, 3 ≤ F.period F.top k) (Y x : F.Cell) (i : Fin 4) :
    torusDist Y x ≤ torusDist Y (x + unitStep F.top i) + 1 := by
  refine offsetNorm_le _ _ fun k => ?_
  have e : x k - Y k = ((x + unitStep F.top i : F.Cell) k - Y k) + -(unitStep F.top i : F.Cell) k := by
    simp only [Pi.add_apply]
    ring
  show (x k - Y k).valMinAbs.natAbs ≤ _
  rw [e]
  refine (ZMod.natAbs_valMinAbs_add_le _ _).trans ((Int.natAbs_add_le _ _).trans ?_)
  have h1 := natAbs_valMinAbs_unitStep hp i k
  rw [← ZMod.natAbs_valMinAbs_neg] at h1
  have h2 := natAbs_le_offsetNorm (centeredOffset Y (x + unitStep F.top i)) k
  have h3 : (centeredOffset Y (x + unitStep F.top i) k).natAbs =
      ((x + unitStep F.top i : F.Cell) k - Y k).valMinAbs.natAbs := rfl
  have h4 : torusDist Y (x + unitStep F.top i) = offsetNorm (centeredOffset Y (x + unitStep F.top i)) := rfl
  omega
private def rampCutoff (q d : ℕ) : ℝ := max 0 (min 1 (2 - (d : ℝ) / q))
private theorem rampCutoff_nonneg (q d : ℕ) : 0 ≤ rampCutoff q d := le_max_left _ _
private theorem rampCutoff_le_one (q d : ℕ) : rampCutoff q d ≤ 1 := max_le zero_le_one (min_le_left _ _)
private theorem rampCutoff_eq_one {q d : ℕ} (hq : 0 < q) (h : d ≤ q) : rampCutoff q d = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (d : ℝ) / q ≤ 1 := by
    rw [div_le_one hq']
    exact_mod_cast h
  unfold rampCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]
private theorem rampCutoff_eq_zero {q d : ℕ} (hq : 0 < q) (h : 2 * q ≤ d) : rampCutoff q d = 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : 2 ≤ (d : ℝ) / q := by
    rw [le_div_iff₀ hq']
    exact_mod_cast h
  unfold rampCutoff
  exact max_eq_left ((min_le_right _ _).trans (by linarith))
private theorem clamp_le_add (a b r : ℝ) (hr : 0 ≤ r) (h : a ≤ b + r) :
    max 0 (min 1 a) ≤ max 0 (min 1 b) + r := by
  refine max_le (by positivity) ?_
  rcases le_total 1 b with h1 | h1
  · have : (1 : ℝ) ≤ max 0 (min 1 b) := by rw [min_eq_left h1]; exact le_max_right _ _
    linarith [min_le_left 1 a]
  · have h2 : b ≤ max 0 (min 1 b) := by rw [min_eq_right h1]; exact le_max_right _ _
    linarith [min_le_right 1 a]
private theorem rampCutoff_lipschitz {q d d' : ℕ} (hq : 0 < q) (h : d ≤ d' + 1) (h' : d' ≤ d + 1) :
    |rampCutoff q d - rampCutoff q d'| ≤ 1 / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (0 : ℝ) ≤ 1 / q := by positivity
  have e1 : (d : ℝ) ≤ d' + 1 := by exact_mod_cast h
  have e2 : (d' : ℝ) ≤ d + 1 := by exact_mod_cast h'
  have e3 : (d : ℝ) / q ≤ d' / q + 1 / q := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right e1 hq'.le
  have e4 : (d' : ℝ) / q ≤ d / q + 1 / q := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right e2 hq'.le
  have a1 := clamp_le_add (2 - (d : ℝ) / q) (2 - (d' : ℝ) / q) _ hr (by linarith)
  have a2 := clamp_le_add (2 - (d' : ℝ) / q) (2 - (d : ℝ) / q) _ hr (by linarith)
  rw [abs_le]
  unfold rampCutoff
  constructor <;> linarith
private def potentialCoeff (ω : Fin 4 → Fin 4 → ℝ) (h : LatticeOffset) (i : Fin 4) : ℝ :=
  1 / 2 * ∑ ν, (h ν : ℝ) * ω ν i
private theorem linearPotential_curvatureAlong (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ)
    (b : LatticeOffset × Fin 4) :
    linearPotential (curvatureAlong X ω) b = potentialCoeff ω b.1 b.2 • X := by
  unfold linearPotential curvatureAlong potentialCoeff
  have e : ∑ ν, ((b.1 ν : ℤ) : ℝ) • (ω ν b.2 • X) = (∑ ν, (b.1 ν : ℝ) * ω ν b.2) • X := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun ν _ => smul_smul _ _ _
  rw [e, smul_smul]
private theorem potentialCoeff_add_basis (ω : Fin 4 → Fin 4 → ℝ) (h : LatticeOffset) (k i : Fin 4) :
    potentialCoeff ω (h + basisOffset k) i = potentialCoeff ω h i + 1 / 2 * ω k i := by
  unfold potentialCoeff
  rw [← mul_add]
  congr 1
  have : ∀ ν, (((h + basisOffset k) ν : ℤ) : ℝ) * ω ν i =
      (h ν : ℝ) * ω ν i + if ν = k then ω ν i else 0 := by
    intro ν
    by_cases hν : ν = k
    · subst hν
      simp [basisOffset]
      ring
    · simp [basisOffset, hν]
  simp only [this, Finset.sum_add_distrib]
  simp
private def entrySum (ω : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ i, ∑ j, |ω i j|
private theorem entrySum_nonneg (ω : Fin 4 → Fin 4 → ℝ) : 0 ≤ entrySum ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
private theorem abs_entry_le_entrySum (ω : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : |ω i j| ≤ entrySum ω := by apply _root_.YangMills.Construction.AbelianSecondOrder.abs_le_arrayNorm <;> assumption
private theorem abs_potentialCoeff_le (ω : Fin 4 → Fin 4 → ℝ) (h : LatticeOffset) (i : Fin 4) :
    |potentialCoeff ω h i| ≤ 1 / 2 * (offsetNorm h : ℝ) * entrySum ω := by
  unfold potentialCoeff
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |∑ ν, (h ν : ℝ) * ω ν i| ≤ ∑ ν, |(h ν : ℝ) * ω ν i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν, (offsetNorm h : ℝ) * |ω ν i| := by
        refine Finset.sum_le_sum fun ν _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have : (h ν).natAbs ≤ offsetNorm h := natAbs_le_offsetNorm h ν
        have h2 : |(h ν : ℝ)| = ((h ν).natAbs : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [h2]
        exact_mod_cast this
    _ = (offsetNorm h : ℝ) * ∑ ν, |ω ν i| := by rw [Finset.mul_sum]
    _ ≤ (offsetNorm h : ℝ) * entrySum ω := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [entrySum, Finset.sum_comm]
        exact Finset.single_le_sum (f := fun j => ∑ i, |ω i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
private def cutPotentialAngle (ω : Fin 4 → Fin 4 → ℝ) (γ : ℝ) (q : ℕ) (Y x : F.Cell) (i : Fin 4) : ℝ :=
  γ * rampCutoff q (torusDist Y x) * potentialCoeff ω (centeredOffset Y x) i
private theorem plaquetteHolonomy_expAlong {j : ℕ} (X : imaginaryQuaternions) (W : F.GaugeField j)
    (u : F.Site j → Fin 4 → ℝ) (hW : ∀ x i, W x i = expAlong X (u x i)) (x : F.Site j) (i k : Fin 4) :
    plaquetteHolonomy W (x, i, k) =
      expAlong X (u x i + u (x + unitStep j i) k - u (x + unitStep j k) i - u x k) := by
  have s3 : x + unitStep j i + unitStep j k - unitStep j i = x + unitStep j k := by abel
  have s4 : x + unitStep j i + unitStep j k + - unitStep j i - unitStep j k = x := by abel
  unfold plaquetteHolonomy
  simp only [pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false, mul_one]
  rw [s3, s4, hW, hW, hW, hW, expAlong_inv, expAlong_inv, ← expAlong_add, ← expAlong_add, ← expAlong_add]
  congr 1
  ring
private theorem abs_curl_cutPotentialAngle_le (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) {γ : ℝ}
    (hγ : 0 < γ) {q : ℕ} (hq : 0 < q) (hp : ∀ k, 8 * q ≤ F.period F.top k) (Y x : F.Cell) (i k : Fin 4) :
    |cutPotentialAngle ω γ q Y x i + cutPotentialAngle ω γ q Y (x + unitStep F.top i) k -
      cutPotentialAngle ω γ q Y (x + unitStep F.top k) i - cutPotentialAngle ω γ q Y x k| ≤
        γ * (3 * entrySum ω) := by
  have hp3 : ∀ k, 3 ≤ F.period F.top k := fun k => by have := hp k; omega
  have hB := entrySum_nonneg ω
  by_cases hfar : 2 * q ≤ torusDist Y x ∧ 2 * q ≤ torusDist Y (x + unitStep F.top i) ∧
      2 * q ≤ torusDist Y (x + unitStep F.top k)
  · obtain ⟨h0, h1, h2⟩ := hfar
    simp only [cutPotentialAngle, rampCutoff_eq_zero hq h0, rampCutoff_eq_zero hq h1, rampCutoff_eq_zero hq h2]
    simp only [mul_zero, zero_mul, add_zero, sub_zero, abs_zero]
    positivity
  · have hu1 := torusDist_add_unitStep_le hp3 Y x i
    have hu2 := torusDist_add_unitStep_le hp3 Y x k
    have hd1 := torusDist_le_add_unitStep hp3 Y x i
    have hd2 := torusDist_le_add_unitStep hp3 Y x k
    have hnear : torusDist Y x ≤ 2 * q := by
      by_contra hc
      exact hfar ⟨by omega, by omega, by omega⟩
    set h : LatticeOffset := centeredOffset Y x with hh
    have hx : x = Y + siteOfCoords F.top h := (add_siteOfCoords_centeredOffset Y x).symm
    have hsmall : ∀ (l : Fin 4) (m : Fin 4), 2 * ((h + basisOffset l) m).natAbs < F.period F.top m := by
      intro l m
      have h1 : (h m).natAbs ≤ 2 * q := (natAbs_le_offsetNorm h m).trans hnear
      have h2 : ((basisOffset l) m).natAbs ≤ 1 := by
        by_cases hm : m = l
        · subst hm
          simp [basisOffset]
        · simp [basisOffset, Pi.single_eq_of_ne hm]
      have h3 := Int.natAbs_add_le (h m) ((basisOffset l) m)
      have h4 : ((h + basisOffset l) m) = h m + (basisOffset l) m := rfl
      rw [h4]
      have := hp m
      omega
    have hoff : ∀ l, centeredOffset Y (x + unitStep F.top l) = h + basisOffset l := by
      intro l
      have e : x + unitStep F.top l = Y + siteOfCoords F.top (h + basisOffset l) := by
        rw [siteOfCoords_add, ← add_assoc, ← hx]
        rfl
      rw [e]
      exact centeredOffset_add Y _ (hsmall l)
    have hP : ∀ m, |potentialCoeff ω h m| ≤ q * entrySum ω := by
      intro m
      refine (abs_potentialCoeff_le ω h m).trans ?_
      have h1 : (offsetNorm h : ℝ) ≤ 2 * q := by exact_mod_cast hnear
      nlinarith
    set c0 := rampCutoff q (torusDist Y x) with hc0
    set c1 := rampCutoff q (torusDist Y (x + unitStep F.top i)) with hc1
    set c2 := rampCutoff q (torusDist Y (x + unitStep F.top k)) with hc2
    have l1 : |c1 - c0| ≤ 1 / q := rampCutoff_lipschitz hq hu1 hd1
    have l2 : |c0 - c2| ≤ 1 / q := rampCutoff_lipschitz hq hd2 hu2
    have e : cutPotentialAngle ω γ q Y x i + cutPotentialAngle ω γ q Y (x + unitStep F.top i) k -
        cutPotentialAngle ω γ q Y (x + unitStep F.top k) i - cutPotentialAngle ω γ q Y x k =
        γ * ((c1 - c0) * potentialCoeff ω h k + (c0 - c2) * potentialCoeff ω h i +
          1 / 2 * (c1 + c2) * ω i k) := by
      simp only [cutPotentialAngle, hoff, potentialCoeff_add_basis]
      rw [← hh, ← hc0, ← hc1, ← hc2, hω k i]
      ring
    rw [e, abs_mul, abs_of_pos hγ]
    refine mul_le_mul_of_nonneg_left ?_ hγ.le
    have b1 : |(c1 - c0) * potentialCoeff ω h k| ≤ entrySum ω := by
      rw [abs_mul]
      calc |c1 - c0| * |potentialCoeff ω h k| ≤ 1 / q * (q * entrySum ω) :=
            mul_le_mul l1 (hP k) (abs_nonneg _) (by positivity)
        _ = entrySum ω := by field_simp
    have b2 : |(c0 - c2) * potentialCoeff ω h i| ≤ entrySum ω := by
      rw [abs_mul]
      calc |c0 - c2| * |potentialCoeff ω h i| ≤ 1 / q * (q * entrySum ω) :=
            mul_le_mul l2 (hP i) (abs_nonneg _) (by positivity)
        _ = entrySum ω := by field_simp
    have b3 : |1 / 2 * (c1 + c2) * ω i k| ≤ entrySum ω := by
      rw [abs_mul]
      have t1 : |1 / 2 * (c1 + c2)| ≤ 1 := by
        have := rampCutoff_nonneg q (torusDist Y (x + unitStep F.top i))
        have := rampCutoff_nonneg q (torusDist Y (x + unitStep F.top k))
        have := rampCutoff_le_one q (torusDist Y (x + unitStep F.top i))
        have := rampCutoff_le_one q (torusDist Y (x + unitStep F.top k))
        rw [abs_le]
        constructor <;> linarith
      calc _ ≤ 1 * entrySum ω := mul_le_mul t1 (abs_entry_le_entrySum ω i k) (abs_nonneg _) zero_le_one
        _ = entrySum ω := one_mul _
    calc _ ≤ |(c1 - c0) * potentialCoeff ω h k + (c0 - c2) * potentialCoeff ω h i| +
          |1 / 2 * (c1 + c2) * ω i k| := abs_add_le _ _
      _ ≤ |(c1 - c0) * potentialCoeff ω h k| + |(c0 - c2) * potentialCoeff ω h i| +
          |1 / 2 * (c1 + c2) * ω i k| := by
          linarith [abs_add_le ((c1 - c0) * potentialCoeff ω h k) ((c0 - c2) * potentialCoeff ω h i)]
      _ ≤ 3 * entrySum ω := by linarith
end TorusOffsets
section AbelianGauge
variable {F : BlockFrame}
private abbrev CircleAngle : Type := ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi)
private def angleOf : ℝ →+ CircleAngle := QuotientAddGroup.mk' _
private theorem angleOf_surjective : Function.Surjective angleOf := QuotientAddGroup.mk'_surjective _
private theorem angleOf_eq_zero {s : ℝ} (h : angleOf s = 0) : ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = s := by
  have h1 : s ∈ AddSubgroup.zmultiples (2 * Real.pi) := (QuotientAddGroup.eq_zero_iff s).1 h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
  exact ⟨k, by rw [← hk]; simp⟩
private theorem angleOf_two_pi_mul (k : ℤ) : angleOf ((k : ℝ) * (2 * Real.pi)) = 0 := by
  refine (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨k, by simp⟩)
private theorem exists_gauge_to_linearPotential (X : imaginaryQuaternions) (hX : ‖X‖ = 1)
    (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) (γ : ℝ) (θ : F.Cell → Fin 4 → ℝ)
    (hplaq : ∀ x i k, i < k →
      expAlong X (θ x i + θ (x + unitStep F.top i) k - θ (x + unitStep F.top k) i - θ x k) =
        expAlong X (γ * ω i k))
    (Y : F.Cell) :
    ∃ φ : F.Cell → ℝ, ∀ (h : LatticeOffset) (i : Fin 4), (∀ k, 2 * (h k).natAbs < F.period F.top k) →
      (∀ k, 2 * ((h + basisOffset i) k).natAbs < F.period F.top k) →
      expAlong X (φ (Y + siteOfCoords F.top h) + θ (Y + siteOfCoords F.top h) i -
        φ (Y + siteOfCoords F.top h + unitStep F.top i)) =
        expAlong X (γ * potentialCoeff ω h i) := by
  set u : Fin 4 → LatticeOffset → ℝ := fun i h => θ (Y + siteOfCoords F.top h) i - γ * potentialCoeff ω h i with hu
  have hsite : ∀ (h : LatticeOffset) (l : Fin 4),
      Y + siteOfCoords F.top (h + basisOffset l) = Y + siteOfCoords F.top h + unitStep F.top l := by
    intro h l
    rw [siteOfCoords_add, ← add_assoc]
    rfl
  have key : ∀ i j h, i < j → angleOf (u i h) + angleOf (u j (h + basisOffset i)) -
      angleOf (u i (h + basisOffset j)) - angleOf (u j h) = 0 := by
    intro i j h hij
    have h1 := hplaq (Y + siteOfCoords F.top h) i j hij
    have h2 : expAlong X ((θ (Y + siteOfCoords F.top h) i + θ (Y + siteOfCoords F.top h + unitStep F.top i) j -
        θ (Y + siteOfCoords F.top h + unitStep F.top j) i - θ (Y + siteOfCoords F.top h) j) - γ * ω i j) = 1 := by
      have e := expAlong_add X ((θ (Y + siteOfCoords F.top h) i +
        θ (Y + siteOfCoords F.top h + unitStep F.top i) j -
        θ (Y + siteOfCoords F.top h + unitStep F.top j) i - θ (Y + siteOfCoords F.top h) j) - γ * ω i j) (γ * ω i j)
      rw [sub_add_cancel, h1] at e
      exact (mul_eq_right.1 e.symm)
    obtain ⟨m, hm⟩ := exists_int_of_expAlong_eq_one X hX h2
    have e : u i h + u j (h + basisOffset i) - u i (h + basisOffset j) - u j h = (m : ℝ) * (2 * Real.pi) := by
      rw [hm]
      simp only [hu, potentialCoeff_add_basis, hsite]
      rw [hω j i]
      ring
    rw [← map_add, ← map_sub, ← map_sub, e]
    exact angleOf_two_pi_mul m
  have hc : ∀ i j h, angleOf (u i (h + basisOffset j)) - angleOf (u i h) =
      angleOf (u j (h + basisOffset i)) - angleOf (u j h) := by
    intro i j h
    rcases lt_trichotomy i j with hij | hij | hij
    · have := key i j h hij
      refine sub_eq_zero.1 ?_
      have e : angleOf (u i (h + basisOffset j)) - angleOf (u i h) -
          (angleOf (u j (h + basisOffset i)) - angleOf (u j h)) =
          -(angleOf (u i h) + angleOf (u j (h + basisOffset i)) - angleOf (u i (h + basisOffset j)) -
            angleOf (u j h)) := by
        abel
      rw [e, this, neg_zero]
    · subst hij
      rfl
    · have := key j i h hij
      refine sub_eq_zero.1 ?_
      have e : angleOf (u i (h + basisOffset j)) - angleOf (u i h) -
          (angleOf (u j (h + basisOffset i)) - angleOf (u j h)) =
          angleOf (u j h) + angleOf (u i (h + basisOffset j)) - angleOf (u j (h + basisOffset i)) -
            angleOf (u i h) := by
        abel
      rw [e, this]
  obtain ⟨ψ, hψ⟩ := exists_primitive_of_closed (fun i h => angleOf (u i h)) hc
  set φ₀ : LatticeOffset → ℝ := fun h => Function.surjInv angleOf_surjective (ψ h) with hφ₀
  have hφ₀' : ∀ h, angleOf (φ₀ h) = ψ h := fun h => Function.surjInv_eq angleOf_surjective _
  refine ⟨fun x => φ₀ (centeredOffset Y x), fun h i hs hs' => ?_⟩
  have o1 : centeredOffset Y (Y + siteOfCoords F.top h) = h := centeredOffset_add Y h hs
  have o2 : centeredOffset Y (Y + siteOfCoords F.top h + unitStep F.top i) = h + basisOffset i := by
    rw [← hsite]
    exact centeredOffset_add Y _ hs'
  simp only [o1, o2]
  have hD : angleOf (φ₀ h + θ (Y + siteOfCoords F.top h) i - φ₀ (h + basisOffset i) - γ * potentialCoeff ω h i) = 0 := by
    have e : φ₀ h + θ (Y + siteOfCoords F.top h) i - φ₀ (h + basisOffset i) - γ * potentialCoeff ω h i =
        u i h - (φ₀ (h + basisOffset i) - φ₀ h) := by
      simp only [hu]
      ring
    rw [e, map_sub angleOf (u i h), map_sub angleOf (φ₀ _), hφ₀', hφ₀', hψ, sub_self]
  obtain ⟨m, hm⟩ := angleOf_eq_zero hD
  have h3 := expAlong_add X (φ₀ h + θ (Y + siteOfCoords F.top h) i - φ₀ (h + basisOffset i) -
    γ * potentialCoeff ω h i) (γ * potentialCoeff ω h i)
  rw [sub_add_cancel, ← hm, expAlong_two_pi_mul X hX, one_mul] at h3
  exact h3
end AbelianGauge
section PotentialSums
private def bondWeight (c : ℝ) (b : LatticeOffset × Fin 4) : ℝ :=
  Real.exp (-(c * offsetNorm b.1)) * (1 + (offsetNorm b.1 : ℝ)) ^ 2
private theorem bondWeight_nonneg (c : ℝ) (b : LatticeOffset × Fin 4) : 0 ≤ bondWeight c b := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.bondWeight_nonneg <;> assumption
private theorem summable_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun z : ℤ => r ^ z.natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_pow_natAbs <;> assumption
private theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : LatticeOffset => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
private theorem summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.summable_bondWeight <;> assumption
private def potentialPairTerm (T : ColdStepAtMirrorFrames.StepParameters) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (cc : (LatticeOffset × Fin 4) × (LatticeOffset × Fin 4)) : ℝ :=
  ‖linearPotential A cc.1‖ * ‖linearPotential A cc.2‖ *
    Real.exp (-(T.κ / 2 ^ 5 * max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1))))
private theorem potentialPairTerm_nonneg (T : ColdStepAtMirrorFrames.StepParameters)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) (cc : (LatticeOffset × Fin 4) × (LatticeOffset × Fin 4)) :
    0 ≤ potentialPairTerm T A cc := by
  unfold potentialPairTerm
  positivity
private theorem norm_linearPotential_le (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (ω : Fin 4 → Fin 4 → ℝ)
    (b : LatticeOffset × Fin 4) :
    ‖linearPotential (curvatureAlong X ω) b‖ ≤ entrySum ω * (1 + (offsetNorm b.1 : ℝ)) ^ 2 := by
  rw [linearPotential_curvatureAlong, norm_smul, hX, mul_one, Real.norm_eq_abs]
  refine (abs_potentialCoeff_le ω b.1 b.2).trans ?_
  have hB := entrySum_nonneg ω
  have hs : (0 : ℝ) ≤ offsetNorm b.1 := Nat.cast_nonneg _
  nlinarith [mul_nonneg hB hs, mul_nonneg hB (mul_nonneg hs hs)]
private theorem summable_potentialPairTerm (T : ColdStepAtMirrorFrames.StepParameters) (hκ : 0 < T.κ)
    (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (ω : Fin 4 → Fin 4 → ℝ) :
    Summable (potentialPairTerm T (curvatureAlong X ω)) := by
  set c : ℝ := T.κ / 2 ^ 6 with hc
  have hc0 : 0 < c := by positivity
  have hB := entrySum_nonneg ω
  have hsum := (Summable.mul_of_nonneg (summable_bondWeight hc0) (summable_bondWeight hc0) (bondWeight_nonneg c)
    (bondWeight_nonneg c)).mul_left (entrySum ω ^ 2)
  refine Summable.of_nonneg_of_le (potentialPairTerm_nonneg T _) (fun cc => ?_) hsum
  set s : ℝ := (offsetNorm cc.1.1 : ℝ) with hs
  set s' : ℝ := (offsetNorm cc.2.1 : ℝ) with hs'
  have n1 := norm_linearPotential_le X hX ω cc.1
  have n2 := norm_linearPotential_le X hX ω cc.2
  have hm : s + s' ≤ 2 * ((max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) : ℕ) : ℝ) := by
    have a1 : offsetNorm cc.1.1 ≤ max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) :=
      le_max_of_le_left (le_max_left _ _)
    have a2 : offsetNorm cc.2.1 ≤ max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) :=
      le_max_of_le_left (le_max_right _ _)
    have a1' : s ≤ ((max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) : ℕ) : ℝ) := by
      rw [hs]
      exact_mod_cast a1
    have a2' : s' ≤ ((max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) : ℕ) : ℝ) := by
      rw [hs']
      exact_mod_cast a2
    linarith
  have he : Real.exp (-(T.κ / 2 ^ 5 *
      ((max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) : ℕ) : ℝ))) ≤
      Real.exp (-(c * s)) * Real.exp (-(c * s')) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : c * (s + s') ≤
        c * (2 * ((max (max (offsetNorm cc.1.1) (offsetNorm cc.2.1)) (offsetNorm (cc.1.1 - cc.2.1)) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hc0.le
    have e : c * 2 = T.κ / 2 ^ 5 := by rw [hc]; ring
    nlinarith
  unfold potentialPairTerm
  show _ ≤ entrySum ω ^ 2 * (bondWeight c cc.1 * bondWeight c cc.2)
  unfold bondWeight
  rw [← hs, ← hs']
  have step1 : ‖linearPotential (curvatureAlong X ω) cc.1‖ * ‖linearPotential (curvatureAlong X ω) cc.2‖ ≤
      (entrySum ω * (1 + s) ^ 2) * (entrySum ω * (1 + s') ^ 2) :=
    mul_le_mul n1 n2 (norm_nonneg _) (by positivity)
  calc _ ≤ (entrySum ω * (1 + s) ^ 2) * (entrySum ω * (1 + s') ^ 2) *
        (Real.exp (-(c * s)) * Real.exp (-(c * s'))) :=
        mul_le_mul step1 he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring
end PotentialSums
private theorem exists_curvature_scale (κ : ℝ) (hκ : 0 < κ) (Cx ε s : ℝ) (hε : 0 < ε) (hs : 0 < s) (n₀ : ℕ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ → γ < s ∧ 2 ≤ Real.log (1 / γ) ∧
      (n₀ : ℝ) ≤ 8 * Real.log (1 / γ) ^ 2 ∧
      Cx * Real.exp (-(κ * (⌊Real.log (1 / γ) ^ 2⌋₊ : ℝ) / 2 ^ 7)) ≤ ε * γ ^ 2 := by
  set C' : ℝ := |Cx| * Real.exp (κ / 2 ^ 7) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set Λ : ℝ := max (max (384 / κ) (C' / ε)) ((n₀ : ℝ) + 2) with hΛ
  refine ⟨min (Real.exp (-Λ)) s, lt_min (Real.exp_pos _) hs, fun γ h0 h1 => ?_⟩
  have hγs : γ < s := lt_of_lt_of_le h1 (min_le_right _ _)
  have hγe : γ < Real.exp (-Λ) := lt_of_lt_of_le h1 (min_le_left _ _)
  set Lg : ℝ := Real.log (1 / γ) with hL
  have hL1 : Lg = - Real.log γ := by rw [hL, one_div, Real.log_inv]
  have hLΛ : Λ < Lg := by
    have := (Real.log_lt_iff_lt_exp h0).2 hγe
    rw [hL1]
    linarith
  have l1 : 384 / κ ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have l2 : C' / ε ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  have l3 : (n₀ : ℝ) + 2 ≤ Λ := le_max_right _ _
  have hL2 : 2 ≤ Lg := by linarith
  refine ⟨hγs, hL2, by nlinarith, ?_⟩
  have hγ : γ = Real.exp (-Lg) := by rw [hL1, neg_neg, Real.exp_log h0]
  have hfl : Lg ^ 2 - 1 < (⌊Lg ^ 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Lg ^ 2)
    linarith
  have hκL : 384 < κ * Lg := by
    have : 384 / κ < Lg := lt_of_le_of_lt l1 hLΛ
    rw [div_lt_iff₀ hκ] at this
    linarith
  have hκL2 : 3 * Lg ≤ κ * Lg ^ 2 / 2 ^ 7 := by nlinarith
  have hCL : C' < ε * Lg := by
    have : C' / ε < Lg := lt_of_le_of_lt l2 hLΛ
    rw [div_lt_iff₀ hε] at this
    linarith
  have step1 : Cx * Real.exp (-(κ * (⌊Lg ^ 2⌋₊ : ℝ) / 2 ^ 7)) ≤ |Cx| * Real.exp (-(κ * (Lg ^ 2 - 1) / 2 ^ 7)) := by
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
    have : κ * (Lg ^ 2 - 1) ≤ κ * (⌊Lg ^ 2⌋₊ : ℝ) := mul_le_mul_of_nonneg_left hfl.le hκ.le
    linarith
  have step2 : |Cx| * Real.exp (-(κ * (Lg ^ 2 - 1) / 2 ^ 7)) = C' * Real.exp (-(κ * Lg ^ 2 / 2 ^ 7)) := by
    rw [hC', mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have step3 : Real.exp (-(κ * Lg ^ 2 / 2 ^ 7)) ≤ Real.exp (-(2 * Lg)) * Real.exp (-Lg) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    linarith
  have step4 : C' * Real.exp (-Lg) ≤ ε := by
    have a1 : Lg ≤ Real.exp Lg := by
      have := Real.add_one_le_exp Lg
      linarith
    have a2 : Real.exp Lg * Real.exp (-Lg) = 1 := by rw [← Real.exp_add]; simp
    have a3 := Real.exp_pos (-Lg)
    calc C' * Real.exp (-Lg) ≤ (ε * Real.exp Lg) * Real.exp (-Lg) := by
          refine mul_le_mul_of_nonneg_right ?_ a3.le
          nlinarith
      _ = ε := by rw [mul_assoc, a2, mul_one]
  have hγ2 : γ ^ 2 = Real.exp (-(2 * Lg)) := by
    rw [hγ, sq, ← Real.exp_add]
    congr 1
    ring
  rw [hγ2]
  calc Cx * Real.exp (-(κ * (⌊Lg ^ 2⌋₊ : ℝ) / 2 ^ 7)) ≤ C' * Real.exp (-(κ * Lg ^ 2 / 2 ^ 7)) := by
        rw [← step2]
        exact step1
    _ ≤ C' * (Real.exp (-(2 * Lg)) * Real.exp (-Lg)) := mul_le_mul_of_nonneg_left step3 hC'0
    _ = (C' * Real.exp (-Lg)) * Real.exp (-(2 * Lg)) := by ring
    _ ≤ ε * Real.exp (-(2 * Lg)) := mul_le_mul_of_nonneg_right step4 (Real.exp_pos _).le
section OnTorusFrame
variable {F : BlockFrame}
private theorem isSmallCurvature_of_expAlong (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (W : F.GaugeField F.top)
    (u : F.Cell → Fin 4 → ℝ) (s : ℝ) (hW : ∀ x i, W x i = expAlong X (u x i))
    (hb : ∀ x i k, i < k → |u x i + u (x + unitStep F.top i) k - u (x + unitStep F.top k) i - u x k| < s) :
    IsSmallCurvature s W := by
  rintro ⟨x, i, k⟩ hp
  show ‖((plaquetteHolonomy W (x, i, k) : UnitQuaternion) : Quaternion ℝ) - 1‖ < s
  rw [plaquetteHolonomy_expAlong X W u hW]
  exact lt_of_le_of_lt (norm_expAlong_sub_one X hX _) (hb x i k hp)
private theorem valMinAbs_intCast_of_small (m : ℕ) (z : ℤ) (hz : 2 * z.natAbs < m) :
    ((z : ZMod m)).valMinAbs = z := by
  have : NeZero m := ⟨by omega⟩
  exact (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by constructor <;> omega⟩
private theorem two_mul_natAbs_sub_lt (a b : ℤ) (q m : ℕ) (ha : a.natAbs < 2 * q) (hb : b.natAbs < 2 * q)
    (hm : 8 * q ≤ m) : 2 * (a - b).natAbs < m := by
  omega
private theorem siteSupDist_le_bondSpan {j k : ℕ} (y : F.Site j) (c : Fin k → F.Site j × Fin 4) (l : Fin k) :
    siteSupDist y (c l).1 ≤ bondSpan y c :=
  le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => siteSupDist y (c l).1) (Finset.mem_univ l))
private theorem siteSupDist_pair_le_bondSpan {j k : ℕ} (y : F.Site j) (c : Fin k → F.Site j × Fin 4)
    (l l' : Fin k) : siteSupDist (c l).1 (c l').1 ≤ bondSpan y c :=
  le_max_of_le_right ((Finset.le_sup (f := fun l' : Fin k => siteSupDist (c l).1 (c l').1)
    (Finset.mem_univ l')).trans (Finset.le_sup (f := fun l : Fin k => Finset.univ.sup fun l' : Fin k =>
      siteSupDist (c l).1 (c l').1) (Finset.mem_univ l)))
private theorem offsetNorm_centeredOffset_le (Y z : F.Cell) :
    offsetNorm (centeredOffset Y z) ≤ siteSupDist Y z := by
  refine offsetNorm_le _ _ fun k => ?_
  have e : centeredOffset Y z k = (z k - Y k).valMinAbs := rfl
  have e2 : z k - Y k = -(Y k - z k) := by ring
  rw [e, e2, ZMod.natAbs_valMinAbs_neg]
  exact Finset.le_sup (f := fun k => ((Y k - z k).valMinAbs).natAbs) (Finset.mem_univ k)
private theorem offsetNorm_sub_centeredOffset_le {q : ℕ} (hp : ∀ k, 8 * q ≤ F.period F.top k) (Y x x' : F.Cell)
    (hd : torusDist Y x < 2 * q) (hd' : torusDist Y x' < 2 * q) :
    offsetNorm (centeredOffset Y x - centeredOffset Y x') ≤ siteSupDist x x' := by
  refine offsetNorm_le _ _ fun k => ?_
  set h : LatticeOffset := centeredOffset Y x with hh
  set h' : LatticeOffset := centeredOffset Y x' with hh'
  have b1 : (h k).natAbs < 2 * q := lt_of_le_of_lt (natAbs_le_offsetNorm h k) hd
  have b2 : (h' k).natAbs < 2 * q := lt_of_le_of_lt (natAbs_le_offsetNorm h' k) hd'
  have hpk := hp k
  have e1 : x k = Y k + (h k : ZMod (F.period F.top k)) := by
    have := congrFun (add_siteOfCoords_centeredOffset Y x) k
    simpa [siteOfCoords] using this.symm
  have e2 : x' k = Y k + (h' k : ZMod (F.period F.top k)) := by
    have := congrFun (add_siteOfCoords_centeredOffset Y x') k
    simpa [siteOfCoords] using this.symm
  have e3 : x k - x' k = ((h k - h' k : ℤ) : ZMod (F.period F.top k)) := by
    rw [e1, e2]
    push_cast
    ring
  have e4 : (x k - x' k).valMinAbs = h k - h' k := by
    rw [e3]
    exact valMinAbs_intCast_of_small _ _ (two_mul_natAbs_sub_lt _ _ q _ b1 b2 hpk)
  have e5 : ((x k - x' k).valMinAbs).natAbs ≤ siteSupDist x x' :=
    Finset.le_sup (f := fun k => ((x k - x' k).valMinAbs).natAbs) (Finset.mem_univ k)
  rw [e4] at e5
  exact e5
private theorem offsetNorm_max_le_bondSpan {q : ℕ} (hp : ∀ k, 8 * q ≤ F.period F.top k) (Y x x' : F.Cell)
    (i i' : Fin 4) (hd : torusDist Y x < 2 * q) (hd' : torusDist Y x' < 2 * q) :
    max (max (offsetNorm (centeredOffset Y x)) (offsetNorm (centeredOffset Y x')))
      (offsetNorm (centeredOffset Y x - centeredOffset Y x')) ≤ bondSpan Y ![(x, i), (x', i')] := by
  have s0 : siteSupDist Y x ≤ bondSpan Y ![(x, i), (x', i')] := by
    simpa using siteSupDist_le_bondSpan Y ![(x, i), (x', i')] 0
  have s1 : siteSupDist Y x' ≤ bondSpan Y ![(x, i), (x', i')] := by
    simpa using siteSupDist_le_bondSpan Y ![(x, i), (x', i')] 1
  have s2 : siteSupDist x x' ≤ bondSpan Y ![(x, i), (x', i')] := by
    simpa using siteSupDist_pair_le_bondSpan Y ![(x, i), (x', i')] 0 1
  exact max_le (max_le ((offsetNorm_centeredOffset_le Y x).trans s0) ((offsetNorm_centeredOffset_le Y x').trans s1))
    ((offsetNorm_sub_centeredOffset_le hp Y x x' hd hd').trans s2)
private theorem dilationRemainder_sub_flat_le_on_frame (T : ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered)
    (h₁ : dilationRemainderSecondOrderBound T) (h₃ : DilationRemainderGaugeInvariantAt T) {t : ℕ} {x : ℝ}
    {f : LocalFamily} (hy : T.coupling ≤ x)
    (hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f) (X : imaginaryQuaternions)
    (hX : ‖X‖ = 1) (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) {n q : ℕ} (hq : 0 < q) (hq8 : 8 * q ≤ n)
    (hside : ∀ i, F.extent i = n) (hper : ∀ k, F.period F.top k = n) (htop : IsCubicTopTorus T.L t T.n₀ F)
    {γ : ℝ} (hγ : 0 < γ) (hγs : γ * (3 * entrySum ω + 1) < 5 / 4 * T.σ) (V : F.GaugeField F.top)
    (θ : F.Cell → Fin 4 → ℝ) (hV : ∀ x i, V x i = expAlong X (θ x i))
    (hplaq : ∀ x i k, i < k →
      expAlong X (θ x i + θ (x + unitStep F.top i) k - θ (x + unitStep F.top k) i - θ x k) =
        expAlong X (γ * ω i k))
    (Y : F.Cell) (e₀ : ℝ)
    (hfr : ∀ V' V'' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      IsSmallCurvature (5 / 4 * T.σ) V'' →
      AgreeOnBall (finiteCells F) V' (finiteCells F) V'' Y Y q →
      |(coldHalfLawAt T x f).dilationRemainder Y V' - (coldHalfLawAt T x f).dilationRemainder Y V''| ≤ e₀) :
    |(coldHalfLawAt T x f).dilationRemainder Y V - (coldHalfLawAt T x f).dilationRemainder Y (flatTopField (F := F))| ≤
      e₀ + T.CE * x ^ (-(3 / 2) : ℝ) * γ ^ 2 * doublePotentialSum T (curvatureAlong X ω) := by
  classical
  set G : F.GaugeField F.top → ℝ := (coldHalfLawAt T x f).dilationRemainder Y with hG
  have hB := entrySum_nonneg ω
  have hp8 : ∀ k, 8 * q ≤ F.period F.top k := fun k => by rw [hper]; exact hq8
  have hnz : ∀ k, NeZero (F.period F.top k) := fun k => ⟨by have := hp8 k; omega⟩
  have hBle : ∀ i k, γ * |ω i k| < 5 / 4 * T.σ := fun i k => by
    have := abs_entry_le_entrySum ω i k
    nlinarith
  have hVcold : IsSmallCurvature (5 / 4 * T.σ) V := by
    rintro ⟨z, i, k⟩ hp
    show ‖((plaquetteHolonomy V (z, i, k) : UnitQuaternion) : Quaternion ℝ) - 1‖ < _
    rw [plaquetteHolonomy_expAlong X V θ hV, hplaq z i k hp]
    refine lt_of_le_of_lt (norm_expAlong_sub_one X hX _) ?_
    rw [abs_mul, abs_of_pos hγ]
    exact hBle i k
  obtain ⟨φ, hφ⟩ := exists_gauge_to_linearPotential X hX ω hω γ θ hplaq Y
  set Vg : F.GaugeField F.top := _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun z => expAlong X (φ z)) V with hVg
  set ug : F.Cell → Fin 4 → ℝ := fun z i => φ z + θ z i - φ (z + unitStep F.top i) with hug
  have hVgt : ∀ z i, Vg z i = expAlong X (ug z i) := by
    intro z i
    show expAlong X (φ z) * V z i * (expAlong X (φ (z + unitStep F.top i)))⁻¹ = _
    rw [hV, expAlong_inv, ← expAlong_add, ← expAlong_add]
    rfl
  have hVgcold : IsSmallCurvature (5 / 4 * T.σ) Vg := by
    rintro ⟨z, i, k⟩ hp
    show ‖((plaquetteHolonomy Vg (z, i, k) : UnitQuaternion) : Quaternion ℝ) - 1‖ < _
    have e : ug z i + ug (z + unitStep F.top i) k - ug (z + unitStep F.top k) i - ug z k =
        θ z i + θ (z + unitStep F.top i) k - θ (z + unitStep F.top k) i - θ z k := by
      simp only [hug]
      rw [add_right_comm z (unitStep F.top i) (unitStep F.top k)]
      ring
    rw [plaquetteHolonomy_expAlong X Vg ug hVgt, e, hplaq z i k hp]
    refine lt_of_le_of_lt (norm_expAlong_sub_one X hX _) ?_
    rw [abs_mul, abs_of_pos hγ]
    exact hBle i k
  set W : ℝ → F.GaugeField F.top := fun v z i => expAlong X (v * cutPotentialAngle ω γ q Y z i) with hW
  have hWcold : ∀ v, 0 ≤ v → v ≤ 1 → IsSmallCurvature (5 / 4 * T.σ) (W v) := by
    intro v h0 h1
    refine isSmallCurvature_of_expAlong X hX (W v) (fun z i => v * cutPotentialAngle ω γ q Y z i) _
      (fun _ _ => rfl) fun z i k _ => ?_
    have e : v * cutPotentialAngle ω γ q Y z i + v * cutPotentialAngle ω γ q Y (z + unitStep F.top i) k -
        v * cutPotentialAngle ω γ q Y (z + unitStep F.top k) i - v * cutPotentialAngle ω γ q Y z k =
        v * (cutPotentialAngle ω γ q Y z i + cutPotentialAngle ω γ q Y (z + unitStep F.top i) k -
          cutPotentialAngle ω γ q Y (z + unitStep F.top k) i - cutPotentialAngle ω γ q Y z k) := by ring
    rw [e, abs_mul, abs_of_nonneg h0]
    have h2 := abs_curl_cutPotentialAngle_le ω hω hγ hq hp8 Y z i k
    have h3 : v * |cutPotentialAngle ω γ q Y z i + cutPotentialAngle ω γ q Y (z + unitStep F.top i) k -
        cutPotentialAngle ω γ q Y (z + unitStep F.top k) i - cutPotentialAngle ω γ q Y z k| ≤
          γ * (3 * entrySum ω) := by
      refine le_trans ?_ h2
      have := abs_nonneg (cutPotentialAngle ω γ q Y z i + cutPotentialAngle ω γ q Y (z + unitStep F.top i) k -
        cutPotentialAngle ω γ q Y (z + unitStep F.top k) i - cutPotentialAngle ω γ q Y z k)
      nlinarith
    nlinarith
  have hstand : ∀ v, 0 ≤ v → v ≤ 1 → IsAdmissibleAt T t x f F (W v) := fun v h0 h1 =>
    ⟨hy, hfam, htop, hWcold v h0 h1⟩
  have hflat : W 0 = flatTopField (F := F) := by
    funext z i
    show expAlong X (0 * _) = 1
    rw [zero_mul, expAlong_zero]
  set en := Fintype.equivFin (F.Cell × Fin 4) with hen
  set k : ℕ := Fintype.card (F.Cell × Fin 4) with hk
  set c : Fin k → F.Cell × Fin 4 := fun l => en.symm l with hc
  set α : Fin k → ℝ := fun l => cutPotentialAngle ω γ q Y (c l).1 (c l).2 with hα
  have hWsh : ∀ v s, leftTranslate (bondSpread c (fun _ => X) (s • α)) (W v) = W (s + v) := by
    intro v s
    funext z i
    have hsp : bondSpread c (fun _ => X) (s • α) z i = (s * cutPotentialAngle ω γ q Y z i) • X := by
      unfold bondSpread
      rw [Finset.sum_eq_single (en (z, i))]
      · have e1 : c (en (z, i)) = (z, i) := en.symm_apply_apply _
        rw [if_pos e1]
        simp [hα, e1]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb ((Equiv.symm_apply_eq en).1 h)
      · intro h
        exact absurd (Finset.mem_univ _) h
    show expUnit (bondSpread c (fun _ => X) (s • α) z i) * W v z i = W (s + v) z i
    rw [hsp]
    show expAlong X (s * cutPotentialAngle ω γ q Y z i) * expAlong X (v * cutPotentialAngle ω γ q Y z i) =
      expAlong X ((s + v) * cutPotentialAngle ω γ q Y z i)
    rw [← expAlong_add]
    congr 1
    ring
  have hsm : ∀ v, 0 ≤ v → v ≤ 1 → ContDiffAt ℝ 2 (alongBonds G (W v) c X) 0 := fun v h0 h1 =>
    (h₁ t x f F (W v) Y (hstand v h0 h1) hrow).1 k c fun _ => X
  have hfirst : ∀ l, bondDeriv G (W 0) ![c l] ![X] = 0 := fun l => by
    rw [hflat]
    exact (h₁ t x f F (W 0) Y (hstand 0 le_rfl zero_le_one) hrow).2.2 (c l) X hX
  set K : ℝ := T.CE * x ^ (-(3 / 2) : ℝ) with hK
  set b : Fin k → Fin k → ℝ := fun l l' => K * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y ![c l, c l'])) with hb
  have hsecond : ∀ v, 0 ≤ v → v ≤ 1 → ∀ l l', |bondDeriv G (W v) ![c l, c l'] ![X, X]| ≤ b l l' :=
    fun v h0 h1 l l' => (h₁ t x f F (W v) Y (hstand v h0 h1) hrow).2.1 (c l) (c l') X X hX hX
  have hmove := abs_sub_le_of_second_derivatives G c X α W b hWsh hsm hfirst hsecond
  have hK0 : 0 ≤ K := by
    have h1 := (abs_nonneg _).trans (hsecond 0 le_rfl zero_le_one (en (Y, 0)) (en (Y, 0)))
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 h1
  set A : Fin 4 → Fin 4 → imaginaryQuaternions := curvatureAlong X ω with hA
  set ib : Fin k → LatticeOffset × Fin 4 := fun l => (centeredOffset Y (c l).1, (c l).2) with hib
  have hib_inj : Function.Injective ib := by
    intro l l' h
    have h0 : (ib l).1 = (ib l').1 := congrArg Prod.fst h
    have h1 : (c l).1 = (c l').1 := centeredOffset_injective Y h0
    have h2 : (ib l).2 = (ib l').2 := congrArg Prod.snd h
    exact en.symm.injective (Prod.ext h1 h2)
  have hnormpot : ∀ l, ‖linearPotential A (ib l)‖ = |potentialCoeff ω (ib l).1 (ib l).2| := fun l => by
    rw [hA, linearPotential_curvatureAlong, norm_smul, hX, mul_one, Real.norm_eq_abs]
  have hαle : ∀ l, |α l| ≤ γ * ‖linearPotential A (ib l)‖ := by
    intro l
    rw [hnormpot]
    show |γ * rampCutoff q (torusDist Y (c l).1) * potentialCoeff ω (centeredOffset Y (c l).1) (c l).2| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos hγ, abs_of_nonneg (rampCutoff_nonneg _ _)]
    have h1 := rampCutoff_le_one q (torusDist Y (c l).1)
    have h2 := abs_nonneg (potentialCoeff ω (centeredOffset Y (c l).1) (c l).2)
    have h3 : rampCutoff q (torusDist Y (c l).1) * |potentialCoeff ω (centeredOffset Y (c l).1) (c l).2| ≤
        |potentialCoeff ω (centeredOffset Y (c l).1) (c l).2| := by nlinarith
    calc _ = γ * (rampCutoff q (torusDist Y (c l).1) * |potentialCoeff ω (centeredOffset Y (c l).1) (c l).2|) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hγ.le
  have hαzero : ∀ l, 2 * q ≤ torusDist Y (c l).1 → α l = 0 := by
    intro l h
    show γ * rampCutoff q (torusDist Y (c l).1) * _ = 0
    rw [rampCutoff_eq_zero hq h]
    ring
  have hterm : ∀ l l', |α l| * |α l'| * b l l' ≤ K * γ ^ 2 * potentialPairTerm T A (ib l, ib l') := by
    intro l l'
    have hnn : 0 ≤ K * γ ^ 2 * potentialPairTerm T A (ib l, ib l') :=
      mul_nonneg (mul_nonneg hK0 (sq_nonneg _)) (potentialPairTerm_nonneg _ _ _)
    by_cases h1 : 2 * q ≤ torusDist Y (c l).1
    · rw [hαzero l h1]
      simpa using hnn
    by_cases h2 : 2 * q ≤ torusDist Y (c l').1
    · rw [hαzero l' h2]
      simpa using hnn
    have hspan := offsetNorm_max_le_bondSpan hp8 Y (c l).1 (c l').1 (c l).2 (c l').2 (by omega) (by omega)
    have hexp : Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y ![c l, c l'])) ≤
        Real.exp (-(T.κ / 2 ^ 5 * max (max (offsetNorm (ib l).1) (offsetNorm (ib l').1))
          (offsetNorm ((ib l).1 - (ib l').1)))) := by
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ ?_))
      · exact_mod_cast hspan
      · have := hT.κ_pos
        positivity
    have hmul : |α l| * |α l'| ≤ (γ * ‖linearPotential A (ib l)‖) * (γ * ‖linearPotential A (ib l')‖) :=
      mul_le_mul (hαle l) (hαle l') (abs_nonneg _) (mul_nonneg hγ.le (norm_nonneg _))
    calc |α l| * |α l'| * b l l' =
          K * (|α l| * |α l'| * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y ![c l, c l']))) := by
          simp only [hb]
          ring
      _ ≤ K * ((γ * ‖linearPotential A (ib l)‖) * (γ * ‖linearPotential A (ib l')‖) *
            Real.exp (-(T.κ / 2 ^ 5 * max (max (offsetNorm (ib l).1) (offsetNorm (ib l').1))
              (offsetNorm ((ib l).1 - (ib l').1))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hmul hexp (Real.exp_pos _).le
            (mul_nonneg (mul_nonneg hγ.le (norm_nonneg _)) (mul_nonneg hγ.le (norm_nonneg _)))) hK0
      _ = K * γ ^ 2 * potentialPairTerm T A (ib l, ib l') := by
          simp only [potentialPairTerm]
          ring
  have hsummable := summable_potentialPairTerm T hT.κ_pos X hX ω
  have hsum : ∑ l, ∑ l', potentialPairTerm T A (ib l, ib l') ≤ doublePotentialSum T A := by
    rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
      (f := fun l l' => potentialPairTerm T A (ib l, ib l'))]
    have hinj : Set.InjOn (fun p : Fin k × Fin k => (ib p.1, ib p.2))
        (↑(Finset.univ ×ˢ Finset.univ : Finset (Fin k × Fin k))) := by
      intro p _ p' _ h
      exact Prod.ext (hib_inj (congrArg Prod.fst h)) (hib_inj (congrArg Prod.snd h))
    have e := Finset.sum_image (f := potentialPairTerm T A) hinj
    rw [← e]
    exact hsummable.sum_le_tsum _ fun cc _ => potentialPairTerm_nonneg T A cc
  have hmove2 : |G (W 1) - G (W 0)| ≤ K * γ ^ 2 * doublePotentialSum T A := by
    refine hmove.trans ?_
    calc ∑ l, ∑ l', |α l| * |α l'| * b l l' ≤ ∑ l, ∑ l', K * γ ^ 2 * potentialPairTerm T A (ib l, ib l') :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => hterm l l'
      _ = K * γ ^ 2 * ∑ l, ∑ l', potentialPairTerm T A (ib l, ib l') := by
          simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg hK0 (sq_nonneg _))
  have hagree : AgreeOnBall (finiteCells F) Vg (finiteCells F) (W 1) Y Y q := by
    refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h _ => Iff.rfl, fun bb hbb => ?_⟩
    · rw [hside]
      omega
    · rw [hside]
      omega
    · have hnat : ∀ (z : LatticeOffset), WithinRadius q z → ∀ m, (z m).natAbs ≤ q := by
        intro z hz m
        have := hz m
        rw [Int.abs_eq_natAbs] at this
        omega
      have hs1 : ∀ m, 2 * (bb.1 m).natAbs < F.period F.top m := fun m => by
        have h1 := hnat _ hbb.1 m
        have h2 := hp8 m
        omega
      have hs2 : ∀ m, 2 * ((bb.1 + basisOffset bb.2) m).natAbs < F.period F.top m := fun m => by
        have h1 : ((bb.1 + basisOffset bb.2) m).natAbs ≤ q := hnat _ hbb.2 m
        have h2 := hp8 m
        omega
      have o1 : centeredOffset Y (Y + siteOfCoords F.top bb.1) = bb.1 := centeredOffset_add Y _ hs1
      have d1 : torusDist Y (Y + siteOfCoords F.top bb.1) ≤ q := by
        show offsetNorm (centeredOffset Y (Y + siteOfCoords F.top bb.1)) ≤ q
        rw [o1]
        exact offsetNorm_le _ _ (hnat _ hbb.1)
      rw [hVgt, show ug (Y + siteOfCoords F.top bb.1) bb.2 = φ (Y + siteOfCoords F.top bb.1) +
        θ (Y + siteOfCoords F.top bb.1) bb.2 - φ (Y + siteOfCoords F.top bb.1 + unitStep F.top bb.2) from rfl,
        hφ bb.1 bb.2 hs1 hs2]
      show _ = expAlong X (1 * cutPotentialAngle ω γ q Y (Y + siteOfCoords F.top bb.1) bb.2)
      unfold cutPotentialAngle
      rw [rampCutoff_eq_one hq d1, o1]
      congr 1
      ring
  have hfreeze := hfr Vg (W 1) hVgcold (hWcold 1 zero_le_one le_rfl) hagree
  have hgauge : G Vg = G V := h₃ t x f F V Y _ ⟨hy, hfam, htop, hVcold⟩
  rw [hgauge] at hfreeze
  have hW0 : G (flatTopField (F := F)) = G (W 0) := by rw [hflat]
  rw [hW0]
  have e : G V - G (W 0) = (G V - G (W 1)) + (G (W 1) - G (W 0)) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add hfreeze hmove2)
end OnTorusFrame
private theorem intCast_cast_add_of_eq {m n : ℕ} (h : m = n) (a b : ZMod m) :
    ((((a + b).cast : ℤ)) : ZMod n) = (((a.cast : ℤ)) : ZMod n) + (((b.cast : ℤ)) : ZMod n) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
private theorem intCast_cast_intCast_of_eq {m n : ℕ} (h : m = n) (z : ℤ) :
    (((((z : ZMod m)).cast : ℤ)) : ZMod n) = (z : ZMod n) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
private def torusSiteOfCell {F : BlockFrame} (n : ℕ) (z : F.Cell) : TorusFields.TorusSite n :=
  fun k => ((siteCoords z k : ℤ) : ZMod n)
private theorem torusSiteOfCell_add_unitStep {F : BlockFrame} {n : ℕ} (hper : ∀ k, F.period F.top k = n)
    (z : F.Cell) (i : Fin 4) :
    torusSiteOfCell n (z + unitStep F.top i) = torusSiteOfCell n z + TorusFields.unitStep n i := by
  funext k
  have e : ((unitStep F.top i : F.Cell) k) = (((Pi.single i 1 : LatticeOffset) k : ℤ) : ZMod (F.period F.top k)) := rfl
  show (((ZMod.cast (z k + (unitStep F.top i : F.Cell) k) : ℤ)) : ZMod n) =
    ((ZMod.cast (z k) : ℤ) : ZMod n) + TorusFields.unitStep n i k
  rw [intCast_cast_add_of_eq (hper k), e, intCast_cast_intCast_of_eq (hper k)]
  congr 1
  by_cases hk : k = i
  · subst hk
    simp [TorusFields.unitStep]
  · simp [TorusFields.unitStep, Pi.single_eq_of_ne hk]
private theorem dilationRemainderAtCurvatureBound_of_parameters (T : ColdStepAtMirrorFrames.StepParameters)
    (hT : T.IsOrdered) (h₁ : dilationRemainderSecondOrderBound T) (h₂ : dilationRemainderLocalityBound T)
    (h₃ : DilationRemainderGaugeInvariantAt T) : dilationRemainderAtCurvatureBound T := by
  intro t x f X ω hy hrow hX hω ε hε
  have hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f :=
    ⟨hrow.smooth, hrow.gauge_invariant, hrow.translation_invariant, hrow.decay, hrow.locality⟩
  obtain ⟨Cx, hCx⟩ := h₂ t x f hy hrow
  have hσ := hT.σ_pos
  have hB := entrySum_nonneg ω
  have hs : 0 < 5 / 4 * T.σ / (3 * entrySum ω + 1) := by positivity
  obtain ⟨γ₀, hγ₀, hch⟩ := exists_curvature_scale T.κ hT.κ_pos Cx ε _ hε hs T.n₀
  refine ⟨γ₀, hγ₀, fun γ hγ hγ₁ n _ hn V Y hV => ?_⟩
  obtain ⟨hγs, hL2, hLn, hfz⟩ := hch γ hγ hγ₁
  have hγs' : γ * (3 * entrySum ω + 1) < 5 / 4 * T.σ := by
    rwa [lt_div_iff₀ (by positivity)] at hγs
  set q : ℕ := ⌊Real.log (1 / γ) ^ 2⌋₊ with hq
  have hq4 : 4 ≤ q := Nat.le_floor (by push_cast; nlinarith)
  have hq8 : 8 * q ≤ n := by
    have h1 : (q : ℝ) ≤ Real.log (1 / γ) ^ 2 := Nat.floor_le (sq_nonneg _)
    have h2 : (8 * q : ℝ) ≤ n := by linarith
    exact_mod_cast h2
  have hn0 : T.n₀ ≤ n := by
    have : (T.n₀ : ℝ) ≤ n := hLn.trans hn
    exact_mod_cast this
  obtain ⟨⟨θ, hθ⟩, hpl⟩ := hV
  have hper : ∀ k, (TorusFields.torusFrame T.L t n).period (TorusFields.torusFrame T.L t n).top k = n := fun k => by
    simp [BlockFrame.period, TorusFields.torusFrame]
  have htop : IsCubicTopTorus T.L t T.n₀ (TorusFields.torusFrame T.L t n) := ⟨rfl, rfl, n, fun _ => rfl, hn0⟩
  set θf : (TorusFields.torusFrame T.L t n).Cell → Fin 4 → ℝ := fun z i => θ (torusSiteOfCell n z) i with hθf
  have hVf : ∀ z i, TorusFields.readAtLevel (TorusFields.torusFrame T.L t n) (TorusFields.torusFrame T.L t n).top V z i =
      expAlong X (θf z i) := fun z i => hθ _ _
  have hplaq : ∀ z i k, i < k →
      expAlong X (θf z i + θf (z + unitStep _ i) k - θf (z + unitStep _ k) i - θf z k) =
        expAlong X (γ * ω i k) := by
    intro z i k hik
    have h := hpl (torusSiteOfCell n z) i k hik
    unfold TorusFields.holonomy at h
    rw [hθ, hθ, hθ, hθ] at h
    have h' : expAlong X (θ (torusSiteOfCell n z) i) *
        expAlong X (θ (torusSiteOfCell n z + TorusFields.unitStep n i) k) *
        (expAlong X (θ (torusSiteOfCell n z + TorusFields.unitStep n k) i))⁻¹ *
        (expAlong X (θ (torusSiteOfCell n z) k))⁻¹ = expAlong X (γ * ω i k) := h
    rw [expAlong_inv, expAlong_inv, ← expAlong_add, ← expAlong_add, ← expAlong_add] at h'
    simp only [hθf, torusSiteOfCell_add_unitStep hper]
    rw [← h']
    congr 1
  set Y' : (TorusFields.torusFrame T.L t n).Cell :=
    siteOfCoords (TorusFields.torusFrame T.L t n).top fun k => ((Y k).cast : ℤ) with hY'
  have res := dilationRemainder_sub_flat_le_on_frame T hT h₁ h₃ hy hfam hrow X hX ω hω (by omega : 0 < q) hq8
    (fun _ => rfl) hper htop hγ hγs'
    (TorusFields.readAtLevel (TorusFields.torusFrame T.L t n) (TorusFields.torusFrame T.L t n).top V) θf hVf hplaq Y'
    (Cx * Real.exp (-(T.κ * q / 2 ^ 7))) fun V' V'' a b c => hCx _ V' V'' Y' q htop a b c
  have e : centered (dilationRemainderDensity T t x f) n Y V =
      (coldHalfLawAt T x f).dilationRemainder Y'
          (TorusFields.readAtLevel (TorusFields.torusFrame T.L t n) (TorusFields.torusFrame T.L t n).top V) -
        (coldHalfLawAt T x f).dilationRemainder Y'
          (flatTopField (F := TorusFields.torusFrame T.L t n)) := rfl
  rw [e]
  refine res.trans ?_
  calc _ ≤ ε * γ ^ 2 + T.CE * x ^ (-(3 / 2) : ℝ) * γ ^ 2 * doublePotentialSum T (curvatureAlong X ω) := by
        linarith
    _ = _ := by ring
theorem dilationRemainderAtCurvatureStatement_holds (hJ : EventuallyInParametersCombines)
    (h₁ : dilationRemainderSecondOrderStatement) (h₂ : dilationRemainderLocalityStatement)
    (h₃ : dilationRemainderGaugeInvariantStatement) : dilationRemainderAtCurvatureStatement := by
  obtain ⟨join, weaken⟩ := hJ
  exact weaken _ _ (fun T hT h => dilationRemainderAtCurvatureBound_of_parameters T hT h.1 h.2.1 h.2.2)
    (join _ _ h₁ (join _ _ h₂ h₃))
end YangMills.Construction.ResponseInTheExpansion
end
