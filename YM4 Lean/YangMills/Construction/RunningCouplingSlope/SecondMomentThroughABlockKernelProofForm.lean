import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
open TorusLumps TorusFields Filter Topology
theorem natAbs_apply_le_offsetNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem offsetNorm_le_of_forall {h : Fin 4 → ℤ} {m : ℕ} (H : ∀ i, (h i).natAbs ≤ m) : offsetNorm h ≤ m := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNorm_le <;> assumption
theorem offsetNormReal_add_le (a b : Fin 4 → ℤ) :
    offsetNormReal (a + b) ≤ offsetNormReal a + offsetNormReal b := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNormReal_add_le <;> assumption
theorem offsetNormReal_neg (a : Fin 4 → ℤ) : offsetNormReal (-a) = offsetNormReal a := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNormReal_neg <;> assumption
theorem offsetNormReal_nonneg (a : Fin 4 → ℤ) : 0 ≤ offsetNormReal a := Nat.cast_nonneg _
theorem offsetNormReal_sub_comm (a b : Fin 4 → ℤ) : offsetNormReal (a - b) = offsetNormReal (b - a) := by
  rw [← neg_sub, offsetNormReal_neg]
theorem offsetNormReal_le_add_sub (a b : Fin 4 → ℤ) :
    offsetNormReal a ≤ offsetNormReal b + offsetNormReal (a - b) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNormReal_le_add_sub <;> assumption
theorem abs_apply_le_offsetNormReal (a : Fin 4 → ℤ) (i : Fin 4) : |((a i : ℤ) : ℝ)| ≤ offsetNormReal a := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.abs_coord_le_offsetNormReal <;> assumption
theorem offsetNormReal_le_natCast_smul {L : ℕ} (hL : 0 < L) (c : Fin 4 → ℤ) :
    offsetNormReal c ≤ offsetNormReal ((L : ℤ) • c) := by
  unfold offsetNormReal
  have : offsetNorm c ≤ offsetNorm ((L : ℤ) • c) := offsetNorm_le_of_forall fun i => by
    refine le_trans ?_ (natAbs_apply_le_offsetNorm _ i)
    simp only [Pi.smul_apply, smul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_left _ hL
  exact_mod_cast this
theorem summable_exp_neg_offsetNormReal {c : ℝ} (hc : 0 < c) :
    Summable fun h : Fin 4 → ℤ => Real.exp (-(c * offsetNormReal h)) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.summable_exp_neg_offsetNormReal <;> assumption
theorem summable_exp_neg_offsetNormReal_sub {c : ℝ} (hc : 0 < c) (a : Fin 4 → ℤ) :
    Summable fun h : Fin 4 → ℤ => Real.exp (-(c * offsetNormReal (h - a))) :=
  (Equiv.subRight a).summable_iff.mpr (summable_exp_neg_offsetNormReal hc)
def IsSubexponential (g : (Fin 4 → ℤ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z, |g z| ≤ C * Real.exp (ε * offsetNormReal z)
theorem IsSubexponential.exists_nonneg_bound {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |g z| ≤ C * Real.exp (ε * offsetNormReal z) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.SubexponentialGrowth.exists_nonneg <;> assumption
theorem IsSubexponential.of_bounded {g : (Fin 4 → ℤ) → ℝ} {C : ℝ} (h : ∀ z, |g z| ≤ C) :
    IsSubexponential g := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.SubexponentialGrowth.of_bounded <;> assumption
theorem IsSubexponential.add {g h : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (hh : IsSubexponential h) :
    IsSubexponential fun z => g z + h z := by
  intro ε hε
  obtain ⟨C, hC⟩ := hg ε hε
  obtain ⟨D, hD⟩ := hh ε hε
  refine ⟨C + D, fun z => (abs_add_le _ _).trans ?_⟩
  rw [add_mul]
  exact add_le_add (hC z) (hD z)
theorem IsSubexponential.const_mul {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (a : ℝ) :
    IsSubexponential fun z => a * g z := by
  intro ε hε
  obtain ⟨C, hC⟩ := hg ε hε
  refine ⟨|a| * C, fun z => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC z) (abs_nonneg a)
theorem IsSubexponential.sub {g h : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (hh : IsSubexponential h) :
    IsSubexponential fun z => g z - h z := by
  have := hg.add (hh.const_mul (-1))
  refine fun ε hε => ?_
  obtain ⟨C, hC⟩ := this ε hε
  exact ⟨C, fun z => by simpa [sub_eq_add_neg] using hC z⟩
theorem IsSubexponential.mul {g h : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (hh : IsSubexponential h) :
    IsSubexponential fun z => g z * h z := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.SubexponentialGrowth.mul <;> assumption
theorem IsSubexponential.comp_add {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (u : Fin 4 → ℤ) :
    IsSubexponential fun z => g (z + u) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hg.exists_nonneg_bound hε
  refine ⟨C * Real.exp (ε * offsetNormReal u), fun z => (hC _).trans ?_⟩
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
  have := offsetNormReal_add_le z u
  nlinarith
theorem IsSubexponential.finset_sum {ι : Type*} (s : Finset ι) {g : ι → (Fin 4 → ℤ) → ℝ}
    (h : ∀ i ∈ s, IsSubexponential (g i)) : IsSubexponential fun z => ∑ i ∈ s, g i z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsSubexponential.of_bounded (C := 0) (by simp)
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    intro ε hε
    obtain ⟨C, hC⟩ := h1 ε hε
    exact ⟨C, fun z => by simpa [Finset.sum_insert ha] using hC z⟩
theorem isSubexponential_offsetNormReal : IsSubexponential offsetNormReal := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.subexponentialGrowth_offsetNormReal <;> assumption
theorem isSubexponential_coord (i : Fin 4) : IsSubexponential fun z => ((z i : ℤ) : ℝ) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.subexponentialGrowth_coord <;> assumption
theorem isSubexponential_pow {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (k : ℕ) :
    IsSubexponential fun z => g z ^ k := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.SubexponentialGrowth.pow <;> assumption
theorem isSubexponential_of_polynomialGrowth {f : (Fin 4 → ℤ) → ℝ} (h : HasPolynomialGrowth f) :
    IsSubexponential f := by
  obtain ⟨C, m, hC⟩ := h
  obtain ⟨k, hk⟩ := exists_nat_ge m
  have h0 : IsSubexponential fun _ => (1 : ℝ) := IsSubexponential.of_bounded (C := 1) (by simp)
  have h1 : IsSubexponential fun z => (1 + offsetNormReal z) ^ k :=
    isSubexponential_pow (h0.add isSubexponential_offsetNormReal) k
  intro ε hε
  obtain ⟨D, hD0, hD⟩ := h1.exists_nonneg_bound hε
  refine ⟨|C| * D, fun z => ?_⟩
  have h2 : 1 ≤ 1 + offsetNormReal z := by linarith [offsetNormReal_nonneg z]
  have h3 : (1 + offsetNormReal z) ^ m ≤ (1 + offsetNormReal z) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h2 hk
  have h4 : |(1 + offsetNormReal z) ^ k| = (1 + offsetNormReal z) ^ k := abs_of_nonneg (by positivity)
  have h5 := hD z
  rw [h4] at h5
  calc |f z| ≤ C * (1 + offsetNormReal z) ^ m := hC z
    _ ≤ |C| * (1 + offsetNormReal z) ^ k := by
        refine mul_le_mul (le_abs_self C) h3 (Real.rpow_nonneg (by linarith) _) (abs_nonneg C)
    _ ≤ |C| * (D * Real.exp (ε * offsetNormReal z)) := mul_le_mul_of_nonneg_left h5 (abs_nonneg C)
    _ = _ := by ring
theorem tsum_decay_mul_bound {θ : ℝ} (hθ : 0 < θ) {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (a : Fin 4 → ℤ) (T : (Fin 4 → ℤ) → ℝ), 0 ≤ M →
      (∀ z, |T z| ≤ M * Real.exp (-(θ * offsetNormReal (z - a)))) →
      Summable (fun z => T z * g z) ∧ |∑' z, T z * g z| ≤ M * C * Real.exp (ε * offsetNormReal a) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.summable_mul_and_abs_tsum_le <;> assumption
def kernelApply (K : LatticeBond → LatticeBond → ℝ) (f : LatticeBond → ℝ) (c : LatticeBond) : ℝ :=
  latticeBondSum fun b => K c b * f b
def IsSubexponentialForm (f : LatticeBond → ℝ) : Prop := ∀ ν, IsSubexponential fun z => f (z, ν)
theorem IsSubexponentialForm.add {f g : LatticeBond → ℝ} (hf : IsSubexponentialForm f)
    (hg : IsSubexponentialForm g) : IsSubexponentialForm fun b => f b + g b :=
  fun ν => (hf ν).add (hg ν)
theorem IsSubexponentialForm.const_mul {f : LatticeBond → ℝ} (hf : IsSubexponentialForm f) (a : ℝ) :
    IsSubexponentialForm fun b => a * f b :=
  fun ν => (hf ν).const_mul a
theorem IsSubexponentialForm.sub {f g : LatticeBond → ℝ} (hf : IsSubexponentialForm f)
    (hg : IsSubexponentialForm g) : IsSubexponentialForm fun b => f b - g b :=
  fun ν => (hf ν).sub (hg ν)
theorem isSubexponentialForm_gradient {φ : (Fin 4 → ℤ) → ℝ} (hφ : IsSubexponential φ) :
    IsSubexponentialForm (latticeGradient φ) :=
  fun ν => (hφ.comp_add (Pi.single ν 1)).sub hφ
theorem isSubexponentialForm_direction (κ : Fin 4 → ℝ) : IsSubexponentialForm fun b => κ b.2 :=
  fun ν => IsSubexponential.of_bounded (C := |κ ν|) fun _ => le_refl _
theorem isSubexponentialForm_linear (κ : Fin 4 → ℝ) :
    IsSubexponentialForm fun b => ((b.1 0 : ℤ) : ℝ) * κ b.2 :=
  fun ν => by
    have := (isSubexponential_coord 0).mul
      (IsSubexponential.of_bounded (g := fun _ => κ ν) (C := |κ ν|) fun _ => le_refl _)
    exact this
section Kernel
variable {K : LatticeBond → LatticeBond → ℝ}
theorem IsLatticeHessianKernel.exists_bound (hK : IsLatticeHessianKernel K) : ∃ M θ : ℝ, 0 ≤ M ∧ 0 < θ ∧
    ∀ c c', |K c c'| ≤ M * Real.exp (-(θ * offsetNormReal (c'.1 - c.1))) := by
  obtain ⟨M, θ, hθ, h⟩ := hK.exp_decay
  refine ⟨M, θ, ?_, hθ, h⟩
  have := h (0, 0) (0, 0)
  have h0 : offsetNormReal ((0 : Fin 4 → ℤ) - 0) = 0 := by simp [offsetNormReal, offsetNorm]
  simp only [h0, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  exact (abs_nonneg _).trans this
theorem summable_kernel_mul (hK : IsLatticeHessianKernel K) {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g)
    (c : LatticeBond) (ν : Fin 4) : Summable fun z => K c (z, ν) * g z := by
  obtain ⟨M, θ, hM, hθ, h⟩ := hK.exists_bound
  obtain ⟨C, -, hC⟩ := tsum_decay_mul_bound hθ hg one_pos
  exact (hC M c.1 (fun z => K c (z, ν)) hM fun z => h c (z, ν)).1
theorem summable_kernel_sub_mul (hK : IsLatticeHessianKernel K) {g : (Fin 4 → ℤ) → ℝ}
    (hg : IsSubexponential g) (c : LatticeBond) (ν : Fin 4) (u : Fin 4 → ℤ) :
    Summable fun z => K c (z - u, ν) * g z := by
  have := summable_kernel_mul hK (hg.comp_add u) c ν
  have h2 := (Equiv.subRight u).summable_iff (f := fun z => K c (z, ν) * g (z + u))
  refine (h2.mpr this).congr fun z => ?_
  simp
theorem kernelApply_add (hK : IsLatticeHessianKernel K) {f g : LatticeBond → ℝ} (hf : IsSubexponentialForm f)
    (hg : IsSubexponentialForm g) (c : LatticeBond) :
    kernelApply K (fun b => f b + g b) c = kernelApply K f c + kernelApply K g c := by
  unfold kernelApply latticeBondSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← (summable_kernel_mul hK (hf ν) c ν).tsum_add (summable_kernel_mul hK (hg ν) c ν)]
  exact tsum_congr fun z => by ring
theorem kernelApply_const_mul (f : LatticeBond → ℝ) (a : ℝ) (c : LatticeBond) :
    kernelApply K (fun b => a * f b) c = a * kernelApply K f c := by
  unfold kernelApply latticeBondSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun z => by ring
theorem kernelApply_sub (hK : IsLatticeHessianKernel K) {f g : LatticeBond → ℝ} (hf : IsSubexponentialForm f)
    (hg : IsSubexponentialForm g) (c : LatticeBond) :
    kernelApply K (fun b => f b - g b) c = kernelApply K f c - kernelApply K g c := by
  have h := kernelApply_add hK hf (hg.const_mul (-1)) c
  rw [kernelApply_const_mul] at h
  have e : (fun b => f b - g b) = fun b => f b + -1 * g b := by
    funext b
    ring
  rw [e, h]
  ring
theorem kernelApply_translate (hK : IsLatticeHessianKernel K) (f : LatticeBond → ℝ) (u : Fin 4 → ℤ)
    (c : LatticeBond) : kernelApply K f (c.1 + u, c.2) = kernelApply K (fun b => f (b.1 + u, b.2)) c := by
  unfold kernelApply latticeBondSum
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← (Equiv.addRight u).tsum_eq]
  refine tsum_congr fun z => ?_
  have := hK.translation_invariant u c (z, ν)
  simp only [Equiv.coe_addRight] at *
  rw [this]
theorem kernelApply_gradient (hK : IsLatticeHessianKernel K) {φ : (Fin 4 → ℤ) → ℝ} (hφ : IsSubexponential φ)
    (c : LatticeBond) : kernelApply K (latticeGradient φ) c = 0 := by
  have e1 : ∀ ν, ∑' z, K c (z, ν) * latticeGradient φ (z, ν) =
      ∑' x, (K c (x - latticeUnitVector ν, ν) - K c (x, ν)) * φ x := by
    intro ν
    have s1 := summable_kernel_mul hK (hφ.comp_add (Pi.single ν 1)) c ν
    have s2 := summable_kernel_mul hK hφ c ν
    have e2 : ∑' z, K c (z, ν) * latticeGradient φ (z, ν) =
        ∑' z, K c (z, ν) * φ (z + Pi.single ν 1) - ∑' z, K c (z, ν) * φ z := by
      rw [← s1.tsum_sub s2]
      refine tsum_congr fun z => ?_
      simp only [latticeGradient]
      ring
    have e3 : ∑' z, K c (z, ν) * φ (z + Pi.single ν 1) =
        ∑' x, K c (x - latticeUnitVector ν, ν) * φ x := by
      rw [← (Equiv.addRight (latticeUnitVector ν)).tsum_eq (fun x => K c (x - latticeUnitVector ν, ν) * φ x)]
      refine tsum_congr fun z => ?_
      simp [latticeUnitVector]
    rw [e2, e3, ← (summable_kernel_sub_mul hK hφ c ν (latticeUnitVector ν)).tsum_sub s2]
    exact tsum_congr fun x => by ring
  unfold kernelApply latticeBondSum
  simp_rw [e1]
  rw [← Summable.tsum_finsetSum fun ν _ =>
    (summable_kernel_sub_mul hK hφ c ν (latticeUnitVector ν)).sub (summable_kernel_mul hK hφ c ν) |>.congr
      fun x => by ring]
  have : ∀ x, ∑ ν, (K c (x - latticeUnitVector ν, ν) - K c (x, ν)) * φ x = 0 := by
    intro x
    rw [← Finset.sum_mul, hK.divergence_zero c x, zero_mul]
  simp [this]
theorem direction_eq_gradient (κ : Fin 4 → ℝ) :
    (fun b : LatticeBond => κ b.2) = latticeGradient fun z => ∑ ν, κ ν * ((z ν : ℤ) : ℝ) := by
  funext b
  simp only [latticeGradient]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single b.2]
  · simp
    ring
  · intro ν _ hν
    simp [Pi.single_apply, hν]
  · simp
theorem isSubexponential_linear_coords (κ : Fin 4 → ℝ) :
    IsSubexponential fun z => ∑ ν, κ ν * ((z ν : ℤ) : ℝ) :=
  IsSubexponential.finset_sum _ fun ν _ => (isSubexponential_coord ν).const_mul (κ ν)
theorem kernelApply_direction (hK : IsLatticeHessianKernel K) (κ : Fin 4 → ℝ) (c : LatticeBond) :
    kernelApply K (fun b => κ b.2) c = 0 := by
  rw [direction_eq_gradient]
  exact kernelApply_gradient hK (isSubexponential_linear_coords κ) c
def kernelFirstMoment (K : LatticeBond → LatticeBond → ℝ) (ν : Fin 4) (c : LatticeBond) : ℝ :=
  ∑' z, K c (z, ν) * ((z 0 : ℤ) : ℝ)
theorem tsum_kernel_direction (hK : IsLatticeHessianKernel K) (ν : Fin 4) (c : LatticeBond) :
    ∑' z, K c (z, ν) = 0 := by
  have h := kernelApply_direction hK (fun μ => if μ = ν then 1 else 0) c
  unfold kernelApply latticeBondSum at h
  rw [Finset.sum_eq_single ν] at h
  · simpa using h
  · intro μ _ hμ
    simp [hμ]
  · simp
theorem kernelFirstMoment_translate (hK : IsLatticeHessianKernel K) (ν : Fin 4) (u : Fin 4 → ℤ)
    (c : LatticeBond) : kernelFirstMoment K ν (c.1 + u, c.2) = kernelFirstMoment K ν c := by
  unfold kernelFirstMoment
  rw [← (Equiv.addRight u).tsum_eq]
  have s1 := summable_kernel_mul hK (isSubexponential_coord 0) c ν
  have s2 : Summable fun z => K c (z, ν) * (1 : ℝ) :=
    summable_kernel_mul hK (IsSubexponential.of_bounded (g := fun _ => (1 : ℝ)) (C := 1) (by simp)) c ν
  have e : ∀ z : Fin 4 → ℤ,
      K (c.1 + u, c.2) ((Equiv.addRight u) z, ν) * (((Equiv.addRight u) z 0 : ℤ) : ℝ) =
      K c (z, ν) * ((z 0 : ℤ) : ℝ) + ((u 0 : ℤ) : ℝ) * (K c (z, ν) * 1) := by
    intro z
    have := hK.translation_invariant u c (z, ν)
    simp only [Equiv.coe_addRight, Pi.add_apply] at *
    rw [this]
    push_cast
    ring
  simp_rw [e]
  rw [s1.tsum_add (s2.mul_left _), tsum_mul_left]
  have := tsum_kernel_direction hK ν c
  simp [this]
theorem kernelFirstMoment_reflect (hK : IsLatticeHessianKernel K) {ν : Fin 4} (hν : ν ≠ 0) (c : LatticeBond) :
    kernelFirstMoment K ν c = -kernelFirstMoment K ν (reflectBond c) := by
  unfold kernelFirstMoment
  let e : (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) := (Equiv.neg _).trans (Equiv.subRight (latticeUnitVector ν))
  rw [← e.tsum_eq (fun z => K (reflectBond c) (z, ν) * ((z 0 : ℤ) : ℝ)), ← tsum_neg]
  refine tsum_congr fun z => ?_
  have h := hK.reflect_invariant c (z, ν)
  have h0 : latticeUnitVector ν 0 = 0 := by simp [latticeUnitVector, Pi.single_apply, hν.symm]
  have he : e z = -z - latticeUnitVector ν := rfl
  have hb : reflectBond (z, ν) = (e z, ν) := rfl
  rw [hb] at h
  rw [h, he]
  simp [h0]
theorem kernelFirstMoment_eq_zero (hK : IsLatticeHessianKernel K) {ν : Fin 4} (hν : ν ≠ 0) (c : LatticeBond) :
    kernelFirstMoment K ν c = 0 := by
  have h1 := kernelFirstMoment_reflect hK hν c
  have h2 := kernelFirstMoment_translate hK ν (-c.1 - latticeUnitVector c.2 - c.1) c
  have h3 : ((c.1 + (-c.1 - latticeUnitVector c.2 - c.1), c.2) : LatticeBond) = reflectBond c := by
    simp only [reflectBond]
    refine Prod.ext ?_ rfl
    funext i
    simp
  rw [h3] at h2
  rw [h2] at h1
  linarith
theorem kernelApply_linear (hK : IsLatticeHessianKernel K) {κ : Fin 4 → ℝ} (h0 : κ 0 = 0) (c : LatticeBond) :
    kernelApply K (fun b => ((b.1 0 : ℤ) : ℝ) * κ b.2) c = 0 := by
  unfold kernelApply latticeBondSum
  refine Finset.sum_eq_zero fun ν _ => ?_
  by_cases hν : ν = 0
  · subst hν
    simp [h0]
  · have := kernelFirstMoment_eq_zero hK hν c
    unfold kernelFirstMoment at this
    simp only
    have e : ∀ z : Fin 4 → ℤ, K c (z, ν) * (((z 0 : ℤ) : ℝ) * κ ν) =
        κ ν * (K c (z, ν) * ((z 0 : ℤ) : ℝ)) := fun z => by ring
    simp_rw [e]
    rw [tsum_mul_left, this, mul_zero]
end Kernel
section Block
variable {L : ℕ} {Pl K : LatticeBond → LatticeBond → ℝ}
theorem IsLatticeBlockKernel.exists_bound (hP : IsLatticeBlockKernel L Pl) : ∃ M θ : ℝ, 0 ≤ M ∧ 0 < θ ∧
    ∀ b c, |Pl b c| ≤ M * Real.exp (-(θ * offsetNormReal (b.1 - (L : ℤ) • c.1))) := by
  obtain ⟨M, θ, hθ, h⟩ := hP.exp_decay
  refine ⟨M, θ, ?_, hθ, h⟩
  have := h (0, 0) (0, 0)
  have h0 : offsetNormReal ((0 : Fin 4 → ℤ) - (L : ℤ) • 0) = 0 := by simp [offsetNormReal, offsetNorm]
  simp only [h0, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  exact (abs_nonneg _).trans this
theorem tsum_block_decay_mul_bound {θ : ℝ} (hθ : 0 < θ) {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g)
    {ε : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (b : Fin 4 → ℤ) (T : (Fin 4 → ℤ) → ℝ), 0 ≤ M →
      (∀ y, |T y| ≤ M * Real.exp (-(θ * offsetNormReal (b - (L : ℤ) • y)))) →
      Summable (fun y => T y * g y) ∧ |∑' y, T y * g y| ≤ M * C * Real.exp (ε * offsetNormReal b) := by
  set e : ℝ := min (ε / 2) (θ / 2) with he
  have he0 : 0 < e := lt_min (half_pos hε) (half_pos hθ)
  have heε : e ≤ ε / 2 := min_le_left _ _
  have heθ : e ≤ θ / 2 := min_le_right _ _
  obtain ⟨C₀, hC0, hC⟩ := hg.exists_nonneg_bound he0
  have hs := summable_exp_neg_offsetNormReal he0
  set S : ℝ := ∑' h : Fin 4 → ℤ, Real.exp (-(e * offsetNormReal h)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨C₀ * S, mul_nonneg hC0 hS0, fun M b T hM hT => ?_⟩
  have hb : ∀ y, ‖T y * g y‖ ≤
      M * C₀ * Real.exp (ε * offsetNormReal b) * Real.exp (-(e * offsetNormReal y)) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hT y
    have h2 := hC y
    have h3 : offsetNormReal y ≤ offsetNormReal b + offsetNormReal (b - (L : ℤ) • y) := by
      have a1 := offsetNormReal_le_natCast_smul hL y
      have a2 := offsetNormReal_le_add_sub ((L : ℤ) • y) b
      rw [offsetNormReal_sub_comm] at a2
      linarith
    have h4 := offsetNormReal_nonneg (b - (L : ℤ) • y)
    have h5 := offsetNormReal_nonneg b
    calc |T y| * |g y| ≤ (M * Real.exp (-(θ * offsetNormReal (b - (L : ℤ) • y)))) *
          (C₀ * Real.exp (e * offsetNormReal y)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
      _ = M * C₀ * Real.exp (-(θ * offsetNormReal (b - (L : ℤ) • y)) + e * offsetNormReal y) := by
          rw [Real.exp_add]
          ring
      _ ≤ M * C₀ * Real.exp (ε * offsetNormReal b + -(e * offsetNormReal y)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hM hC0)
          nlinarith [mul_nonneg (sub_nonneg.mpr heε) h5, mul_nonneg (sub_nonneg.mpr heθ) h4,
            mul_le_mul_of_nonneg_left h3 he0.le]
      _ = _ := by
          rw [Real.exp_add]
          ring
  have hsum : Summable fun y =>
      M * C₀ * Real.exp (ε * offsetNormReal b) * Real.exp (-(e * offsetNormReal y)) :=
    hs.mul_left _
  refine ⟨Summable.of_norm_bounded hsum hb, ?_⟩
  have := tsum_of_norm_bounded hsum.hasSum hb
  rw [tsum_mul_left, Real.norm_eq_abs] at this
  calc _ ≤ _ := this
    _ = _ := by ring
theorem tsum_comm_block {θ : ℝ} (hθ : 0 < θ) {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) (hL : 0 < L)
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (a : Fin 4 → ℤ) (T₁ : (Fin 4 → ℤ) → ℝ)
    (T₂ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ)
    (h₁ : ∀ x, |T₁ x| ≤ M₁ * Real.exp (-(θ * offsetNormReal (x - a))))
    (h₂ : ∀ x z, |T₂ x z| ≤ M₂ * Real.exp (-(θ * offsetNormReal (x - (L : ℤ) • z)))) :
    Summable (fun z => (∑' x, T₁ x * T₂ x z) * g z) ∧
      ∑' z, (∑' x, T₁ x * T₂ x z) * g z = ∑' x, T₁ x * ∑' z, T₂ x z * g z := by
  obtain ⟨C₀, hC0, hC⟩ := hg.exists_nonneg_bound (show 0 < θ / 4 by positivity)
  set f : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ := fun z x => T₁ x * T₂ x z * g z with hf
  set C : ℝ := M₁ * M₂ * C₀ * Real.exp (θ / 2 * offsetNormReal a) with hCdef
  have hb : ∀ p : (Fin 4 → ℤ) × (Fin 4 → ℤ), ‖Function.uncurry f p‖ ≤
      (C * Real.exp (-(θ / 4 * offsetNormReal p.1))) * Real.exp (-(θ / 2 * offsetNormReal (p.2 - a))) := by
    rintro ⟨z, x⟩
    simp only [Function.uncurry, hf, Real.norm_eq_abs, abs_mul]
    have e1 := h₁ x
    have e2 := h₂ x z
    have e3 := hC z
    have t1 : offsetNormReal z ≤ offsetNormReal x + offsetNormReal (x - (L : ℤ) • z) := by
      have a1 := offsetNormReal_le_natCast_smul hL z
      have a2 := offsetNormReal_le_add_sub ((L : ℤ) • z) x
      rw [offsetNormReal_sub_comm] at a2
      linarith
    have t2 := offsetNormReal_le_add_sub x a
    have n1 := offsetNormReal_nonneg (x - (L : ℤ) • z)
    have n2 := offsetNormReal_nonneg (x - a)
    have n3 := offsetNormReal_nonneg a
    calc |T₁ x| * |T₂ x z| * |g z| ≤ (M₁ * Real.exp (-(θ * offsetNormReal (x - a)))) *
          (M₂ * Real.exp (-(θ * offsetNormReal (x - (L : ℤ) • z)))) *
          (C₀ * Real.exp (θ / 4 * offsetNormReal z)) := by
          gcongr
      _ = M₁ * M₂ * C₀ * Real.exp (-(θ * offsetNormReal (x - a)) +
            -(θ * offsetNormReal (x - (L : ℤ) • z)) + θ / 4 * offsetNormReal z) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ ≤ M₁ * M₂ * C₀ * Real.exp (θ / 2 * offsetNormReal a + -(θ / 4 * offsetNormReal z) +
            -(θ / 2 * offsetNormReal (x - a))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left t1 hθ.le, mul_le_mul_of_nonneg_left t2 hθ.le,
            mul_nonneg hθ.le n1, mul_nonneg hθ.le n2, mul_nonneg hθ.le n3]
      _ = _ := by
          rw [Real.exp_add, Real.exp_add, hCdef]
          ring
  have hsum : Summable fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      (C * Real.exp (-(θ / 4 * offsetNormReal p.1))) * Real.exp (-(θ / 2 * offsetNormReal (p.2 - a))) :=
    Summable.mul_of_nonneg ((summable_exp_neg_offsetNormReal (show 0 < θ / 4 by positivity)).mul_left C)
      (summable_exp_neg_offsetNormReal_sub (half_pos hθ) a) (fun _ => by positivity) (fun _ => by positivity)
  have hs : Summable (Function.uncurry f) := Summable.of_norm_bounded hsum hb
  have e0 : ∀ z, (∑' x, T₁ x * T₂ x z) * g z = ∑' x, f z x := fun z => by
    rw [← tsum_mul_right]
  refine ⟨?_, ?_⟩
  · simp_rw [e0]
    exact hs.prod
  · simp_rw [e0]
    rw [← hs.tsum_comm]
    refine tsum_congr fun x => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun z => by simp only [hf]; ring
def blockKernelMoment (Pl : LatticeBond → LatticeBond → ℝ) (k : ℕ) (b : LatticeBond) : ℝ :=
  ∑' y : Fin 4 → ℤ, Pl b (y, secondAxis) * ((y 0 : ℤ) : ℝ) ^ k
theorem summable_blockKernelMoment (hP : IsLatticeBlockKernel L Pl) (hL : 0 < L) (k : ℕ) (b : LatticeBond) :
    Summable fun y : Fin 4 → ℤ => Pl b (y, secondAxis) * ((y 0 : ℤ) : ℝ) ^ k := by
  obtain ⟨M, θ, hM, hθ, h⟩ := hP.exists_bound
  obtain ⟨C, -, hC⟩ := tsum_block_decay_mul_bound hθ (isSubexponential_pow (isSubexponential_coord 0) k) one_pos hL
  exact (hC M b.1 _ hM fun y => h b (y, secondAxis)).1
theorem isSubexponentialForm_blockKernelMoment (hP : IsLatticeBlockKernel L Pl) (hL : 0 < L) (k : ℕ) :
    IsSubexponentialForm (blockKernelMoment Pl k) := by
  obtain ⟨M, θ, hM, hθ, h⟩ := hP.exists_bound
  intro ν ε hε
  obtain ⟨C, -, hC⟩ := tsum_block_decay_mul_bound hθ (isSubexponential_pow (isSubexponential_coord 0) k) hε hL
  exact ⟨M * C, fun z => (hC M z _ hM fun y => h (z, ν) (y, secondAxis)).2⟩
theorem blockKernelMoment_translate_eq (hP : IsLatticeBlockKernel L Pl) (k : ℕ) (v : Fin 4 → ℤ)
    (b : LatticeBond) :
    blockKernelMoment Pl k (b.1 + (L : ℤ) • v, b.2) =
      ∑' y : Fin 4 → ℤ, Pl b (y, secondAxis) * (((y 0 : ℤ) : ℝ) + ((v 0 : ℤ) : ℝ)) ^ k := by
  unfold blockKernelMoment
  rw [← (Equiv.addRight v).tsum_eq]
  refine tsum_congr fun y => ?_
  have := hP.translation_invariant v b (y, secondAxis)
  simp only [Equiv.coe_addRight, Pi.add_apply] at *
  rw [this]
  push_cast
  rfl
theorem blockKernelMoment_zero_translate (hP : IsLatticeBlockKernel L Pl) (v : Fin 4 → ℤ) (b : LatticeBond) :
    blockKernelMoment Pl 0 (b.1 + (L : ℤ) • v, b.2) = blockKernelMoment Pl 0 b := by
  rw [blockKernelMoment_translate_eq hP]
  simp [blockKernelMoment]
theorem blockKernelMoment_two_translate (hP : IsLatticeBlockKernel L Pl) (hL : 0 < L) (v : Fin 4 → ℤ)
    (b : LatticeBond) :
    blockKernelMoment Pl 2 (b.1 + (L : ℤ) • v, b.2) = blockKernelMoment Pl 2 b +
      2 * ((v 0 : ℤ) : ℝ) * blockKernelMoment Pl 1 b + ((v 0 : ℤ) : ℝ) ^ 2 * blockKernelMoment Pl 0 b := by
  rw [blockKernelMoment_translate_eq hP]
  have s0 := summable_blockKernelMoment hP hL 0 b
  have s1 := summable_blockKernelMoment hP hL 1 b
  have s2 := summable_blockKernelMoment hP hL 2 b
  unfold blockKernelMoment
  calc ∑' y : Fin 4 → ℤ, Pl b (y, secondAxis) * (((y 0 : ℤ) : ℝ) + ((v 0 : ℤ) : ℝ)) ^ 2
      = ∑' y : Fin 4 → ℤ, ((Pl b (y, secondAxis) * ((y 0 : ℤ) : ℝ) ^ 2 +
          2 * ((v 0 : ℤ) : ℝ) * (Pl b (y, secondAxis) * ((y 0 : ℤ) : ℝ) ^ 1)) +
          ((v 0 : ℤ) : ℝ) ^ 2 * (Pl b (y, secondAxis) * ((y 0 : ℤ) : ℝ) ^ 0)) :=
        tsum_congr fun y => by ring
    _ = _ := by
        rw [(s2.add (s1.mul_left _)).tsum_add (s0.mul_left _), s2.tsum_add (s1.mul_left _),
          tsum_mul_left, tsum_mul_left]
theorem tsum_secondAxis_of_hasSum {f : LatticeBond → ℝ} {a : ℝ}
    (h : HasSum (fun c => f c * constantOneForm secondAxis c) a) :
    ∑' y : Fin 4 → ℤ, f (y, secondAxis) = a := by
  have hi : Function.Injective fun y : Fin 4 → ℤ => ((y, secondAxis) : LatticeBond) :=
    fun _ _ e => (Prod.ext_iff.mp e).1
  have hz : ∀ x ∉ Set.range fun y : Fin 4 → ℤ => ((y, secondAxis) : LatticeBond),
      f x * constantOneForm secondAxis x = 0 := by
    rintro ⟨y, ν⟩ hx
    have : ν ≠ secondAxis := fun e => hx ⟨y, by simp [e]⟩
    simp [constantOneForm, this]
  have := (hi.hasSum_iff hz).mpr h
  have e : ((fun c => f c * constantOneForm secondAxis c) ∘
      fun y : Fin 4 → ℤ => ((y, secondAxis) : LatticeBond)) =
      fun y => f (y, secondAxis) := by
    funext y
    simp [constantOneForm]
  rw [e] at this
  exact this.tsum_eq
theorem blockKernelMoment_zero_eq (hP : IsLatticeBlockKernel L Pl) :
    ∃ lam : (Fin 4 → ℤ) → ℝ, (∃ C, ∀ z, |lam z| ≤ C) ∧
      ∀ b, blockKernelMoment Pl 0 b = (L : ℝ)⁻¹ * constantOneForm secondAxis b + latticeGradient lam b := by
  obtain ⟨f, hf, h⟩ := hP.constant_form
  refine ⟨f, hf, fun b => ?_⟩
  have := tsum_secondAxis_of_hasSum (f := fun c => Pl b c) (h b)
  rw [← this]
  simp [blockKernelMoment]
theorem blockKernelMoment_one_eq (hP : IsLatticeBlockKernel L Pl) :
    ∃ (f : (Fin 4 → ℤ) → ℝ) (κ : Fin 4 → ℝ),
      HasPolynomialGrowth f ∧ ∀ b, blockKernelMoment Pl 1 b =
        (L : ℝ)⁻¹ ^ 2 * ((b.1 0 : ℤ) : ℝ) * constantOneForm secondAxis b + κ b.2 + latticeGradient f b := by
  obtain ⟨f, κ, hf, h⟩ := hP.linear_potential
  refine ⟨f, κ, hf, fun b => ?_⟩
  have := tsum_secondAxis_of_hasSum (f := fun c => Pl b c * ((c.1 0 : ℤ) : ℝ)) (h b)
  rw [← this]
  simp [blockKernelMoment]
theorem kernelApply_blockKernelMoment_zero (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl)
    (c : LatticeBond) : kernelApply K (blockKernelMoment Pl 0) c = 0 := by
  obtain ⟨lam, ⟨C, hC⟩, h⟩ := blockKernelMoment_zero_eq hP
  have hm : IsSubexponential lam := IsSubexponential.of_bounded hC
  have e : blockKernelMoment Pl 0 = fun b => (fun b => ((L : ℝ)⁻¹) * constantOneForm secondAxis b) b +
      latticeGradient lam b := funext h
  have h1 : IsSubexponentialForm fun b : LatticeBond => constantOneForm secondAxis b :=
    isSubexponentialForm_direction fun ν => if ν = secondAxis then 1 else 0
  rw [e, kernelApply_add hK (h1.const_mul _) (isSubexponentialForm_gradient hm), kernelApply_const_mul,
    kernelApply_gradient hK hm]
  have : kernelApply K (fun b => constantOneForm secondAxis b) c = 0 :=
    kernelApply_direction hK (fun ν => if ν = secondAxis then 1 else 0) c
  rw [this]
  ring
theorem kernelApply_blockKernelMoment_one (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl)
    (c : LatticeBond) : kernelApply K (blockKernelMoment Pl 1) c = 0 := by
  obtain ⟨f, κ, hf, h⟩ := blockKernelMoment_one_eq hP
  have hm := isSubexponential_of_polynomialGrowth hf
  set cf : Fin 4 → ℝ := fun ν => if ν = secondAxis then 1 else 0 with hcf
  have h0 : cf 0 = 0 := by simp [hcf, secondAxis]
  have h1 : IsSubexponentialForm fun b : LatticeBond => ((L : ℝ)⁻¹ ^ 2) * (((b.1 0 : ℤ) : ℝ) * cf b.2) :=
    (isSubexponentialForm_linear cf).const_mul _
  have e : blockKernelMoment Pl 1 = fun b =>
      ((fun b : LatticeBond => ((L : ℝ)⁻¹ ^ 2) * (((b.1 0 : ℤ) : ℝ) * cf b.2)) b + κ b.2) +
        latticeGradient f b := by
    funext b
    rw [h]
    simp only [hcf, constantOneForm]
    ring
  rw [e, kernelApply_add hK (h1.add (isSubexponentialForm_direction κ)) (isSubexponentialForm_gradient hm),
    kernelApply_add hK h1 (isSubexponentialForm_direction κ),
    kernelApply_const_mul, kernelApply_linear hK h0, kernelApply_direction hK, kernelApply_gradient hK hm]
  ring
theorem kernelApply_blockKernelMoment_two_periodic (hK : IsLatticeHessianKernel K)
    (hP : IsLatticeBlockKernel L Pl) (hL : 0 < L) (v : Fin 4 → ℤ) (c : LatticeBond) :
    kernelApply K (blockKernelMoment Pl 2) (c.1 + (L : ℤ) • v, c.2) = kernelApply K (blockKernelMoment Pl 2) c := by
  rw [kernelApply_translate hK]
  have e : (fun b : LatticeBond => blockKernelMoment Pl 2 (b.1 + (L : ℤ) • v, b.2)) = fun b =>
      (blockKernelMoment Pl 2 b + (2 * ((v 0 : ℤ) : ℝ)) * blockKernelMoment Pl 1 b) +
        (((v 0 : ℤ) : ℝ) ^ 2) * blockKernelMoment Pl 0 b := by
    funext b
    exact blockKernelMoment_two_translate hP hL v b
  have m0 := isSubexponentialForm_blockKernelMoment hP hL 0
  have m1 := isSubexponentialForm_blockKernelMoment hP hL 1
  have m2 := isSubexponentialForm_blockKernelMoment hP hL 2
  rw [e, kernelApply_add hK (m2.add (m1.const_mul _)) (m0.const_mul _), kernelApply_add hK m2 (m1.const_mul _),
    kernelApply_const_mul, kernelApply_const_mul, kernelApply_blockKernelMoment_zero hK hP,
    kernelApply_blockKernelMoment_one hK hP]
  ring
theorem latticeSecondMoment_kernelPullback_eq (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl)
    (hL : 0 < L) :
    latticeSecondMoment (kernelPullback Pl K) =
      latticeBondSum fun b => Pl b (0, secondAxis) * kernelApply K (blockKernelMoment Pl 2) b := by
  obtain ⟨MK, θK, hMK, hθK, hKb⟩ := hK.exists_bound
  obtain ⟨MP, θP, hMP, hθP, hPb⟩ := hP.exists_bound
  set θ : ℝ := min θK θP with hθdef
  have hθ : 0 < θ := lt_min hθK hθP
  have hKb' : ∀ c c', |K c c'| ≤ MK * Real.exp (-(θ * offsetNormReal (c'.1 - c.1))) := fun c c' =>
    (hKb c c').trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right (min_le_left θK θP) (offsetNormReal_nonneg (c'.1 - c.1))
      linarith)) hMK)
  have hPb' : ∀ b c, |Pl b c| ≤ MP * Real.exp (-(θ * offsetNormReal (b.1 - (L : ℤ) • c.1))) := fun b c =>
    (hPb b c).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right (min_le_right θK θP) (offsetNormReal_nonneg (b.1 - (L : ℤ) • c.1))
      linarith)) hMP)
  have hg : IsSubexponential fun z : Fin 4 → ℤ => ((z 0 : ℤ) : ℝ) ^ 2 :=
    isSubexponential_pow (isSubexponential_coord 0) 2
  set Q : LatticeBond → (Fin 4 → ℤ) → ℝ := fun b z =>
    latticeBondSum fun b' => K b b' * Pl b' (z, secondAxis) with hQ
  set S : ℝ := ∑' h : Fin 4 → ℤ, Real.exp (-(θ / 2 * offsetNormReal h)) with hS
  have hQb : ∀ b z, |Q b z| ≤ (4 * (MK * MP * S)) *
      Real.exp (-(θ / 2 * offsetNormReal (b.1 - (L : ℤ) • z))) := by
    intro b z
    have one : ∀ ν : Fin 4, |∑' x, K b (x, ν) * Pl (x, ν) (z, secondAxis)| ≤
        (MK * MP * S) * Real.exp (-(θ / 2 * offsetNormReal (b.1 - (L : ℤ) • z))) := by
      intro ν
      have hbd : ∀ x, ‖K b (x, ν) * Pl (x, ν) (z, secondAxis)‖ ≤
          (MK * MP * Real.exp (-(θ / 2 * offsetNormReal (b.1 - (L : ℤ) • z)))) *
            Real.exp (-(θ / 2 * offsetNormReal (x - b.1))) := by
        intro x
        rw [Real.norm_eq_abs, abs_mul]
        have e1 := hKb' b (x, ν)
        have e2 := hPb' (x, ν) (z, secondAxis)
        simp only at e1 e2
        have t : offsetNormReal (b.1 - (L : ℤ) • z) ≤
            offsetNormReal (x - b.1) + offsetNormReal (x - (L : ℤ) • z) := by
          have := offsetNormReal_add_le (b.1 - x) (x - (L : ℤ) • z)
          rw [offsetNormReal_sub_comm b.1 x] at this
          simpa using this
        have n1 := offsetNormReal_nonneg (x - (L : ℤ) • z)
        have n2 := offsetNormReal_nonneg (x - b.1)
        calc |K b (x, ν)| * |Pl (x, ν) (z, secondAxis)| ≤
              (MK * Real.exp (-(θ * offsetNormReal (x - b.1)))) *
                (MP * Real.exp (-(θ * offsetNormReal (x - (L : ℤ) • z)))) :=
              mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg hMK (Real.exp_pos _).le)
          _ = MK * MP * Real.exp (-(θ * offsetNormReal (x - b.1)) +
                -(θ * offsetNormReal (x - (L : ℤ) • z))) := by
              rw [Real.exp_add]
              ring
          _ ≤ MK * MP * Real.exp (-(θ / 2 * offsetNormReal (b.1 - (L : ℤ) • z)) +
                -(θ / 2 * offsetNormReal (x - b.1))) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hMK hMP)
              nlinarith [mul_le_mul_of_nonneg_left t hθ.le, mul_nonneg hθ.le n1, mul_nonneg hθ.le n2]
          _ = _ := by
              rw [Real.exp_add]
              ring
      have hsum := (summable_exp_neg_offsetNormReal_sub (half_pos hθ) b.1).mul_left
        (MK * MP * Real.exp (-(θ / 2 * offsetNormReal (b.1 - (L : ℤ) • z))))
      have := tsum_of_norm_bounded hsum.hasSum hbd
      rw [tsum_mul_left, Real.norm_eq_abs] at this
      have ht : ∑' x : Fin 4 → ℤ, Real.exp (-(θ / 2 * offsetNormReal (x - b.1))) = S :=
        (Equiv.subRight b.1).tsum_eq fun h => Real.exp (-(θ / 2 * offsetNormReal h))
      rw [ht] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    have : |Q b z| ≤ ∑ ν : Fin 4, (MK * MP * S) *
        Real.exp (-(θ / 2 * offsetNormReal (b.1 - (L : ℤ) • z))) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => one ν)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc _ ≤ _ := this
      _ = _ := by push_cast; ring
  have hM2 : 0 ≤ 4 * (MK * MP * S) := by positivity
  have hθ2 : 0 < θ / 2 := half_pos hθ
  have hPw : ∀ (ν : Fin 4) (x : Fin 4 → ℤ), |Pl (x, ν) (0, secondAxis)| ≤
      MP * Real.exp (-(θ / 2 * offsetNormReal (x - 0))) := by
    intro ν x
    have := hPb' (x, ν) (0, secondAxis)
    simp only [smul_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hMP)
    nlinarith [mul_nonneg hθ.le (offsetNormReal_nonneg (x - 0))]
  have sw1 := fun ν : Fin 4 => tsum_comm_block hθ2 hg hL hMP hM2 0 (fun x => Pl (x, ν) (0, secondAxis))
    (fun x z => Q (x, ν) z) (hPw ν) (fun x z => hQb (x, ν) z)
  have hKw : ∀ (b : LatticeBond) (ν : Fin 4) (x : Fin 4 → ℤ), |K b (x, ν)| ≤
      MK * Real.exp (-(θ / 2 * offsetNormReal (x - b.1))) := by
    intro b ν x
    refine (hKb' b (x, ν)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hMK)
    nlinarith [mul_nonneg hθ.le (offsetNormReal_nonneg (x - b.1))]
  have hPw2 : ∀ (ν : Fin 4) (x z : Fin 4 → ℤ), |Pl (x, ν) (z, secondAxis)| ≤
      MP * Real.exp (-(θ / 2 * offsetNormReal (x - (L : ℤ) • z))) := by
    intro ν x z
    refine (hPb' (x, ν) (z, secondAxis)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hMP)
    nlinarith [mul_nonneg hθ.le (offsetNormReal_nonneg (x - (L : ℤ) • z))]
  have sw2 := fun (b : LatticeBond) (ν : Fin 4) => tsum_comm_block hθ2 hg hL hMK hMP b.1 (fun x => K b (x, ν))
    (fun x z => Pl (x, ν) (z, secondAxis)) (hKw b ν) (hPw2 ν)
  have hW : ∀ b : LatticeBond, ∑' z : Fin 4 → ℤ, Q b z * ((z 0 : ℤ) : ℝ) ^ 2 =
      kernelApply K (blockKernelMoment Pl 2) b := by
    intro b
    simp only [hQ, latticeBondSum, kernelApply, Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun ν _ => (sw2 b ν).1]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [(sw2 b ν).2]
    rfl
  have key : ∀ z : Fin 4 → ℤ, kernelPullback Pl K (0, secondAxis) (z, secondAxis) *
      ((z 0 : ℤ) : ℝ) ^ 2 = ∑ ν : Fin 4, (∑' x, Pl (x, ν) (0, secondAxis) * Q (x, ν) z) *
        ((z 0 : ℤ) : ℝ) ^ 2 := by
    intro z
    have : kernelPullback Pl K (0, secondAxis) (z, secondAxis) =
        ∑ ν : Fin 4, ∑' x, Pl (x, ν) (0, secondAxis) * Q (x, ν) z := rfl
    rw [this, Finset.sum_mul]
  unfold latticeSecondMoment
  simp_rw [key]
  rw [Summable.tsum_finsetSum fun ν _ => (sw1 ν).1]
  show _ = ∑ ν : Fin 4, ∑' x, Pl (x, ν) (0, secondAxis) * kernelApply K (blockKernelMoment Pl 2) (x, ν)
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [(sw1 ν).2]
  refine tsum_congr fun x => ?_
  rw [hW]
end Block
section Steps
theorem comp_add_zsmul_of_step {g : (Fin 4 → ℤ) → ℝ} {e : Fin 4 → ℤ} (h : ∀ z, g (z + e) = g z) (k : ℤ)
    (z : Fin 4 → ℤ) : g (z + k • e) = g z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : z + ((i : ℤ) + 1) • e = (z + (i : ℤ) • e) + e := by
      rw [add_smul, one_smul, add_assoc]
    rw [this, h, ih]
  | pred i ih =>
    have e1 : z + (-(i : ℤ)) • e = (z + (-(i : ℤ) - 1) • e) + e := by
      rw [sub_smul, one_smul]
      abel
    rw [e1, h] at ih
    exact ih
theorem comp_add_sum_of_steps (s : Finset (Fin 4)) {g : (Fin 4 → ℤ) → ℝ}
    (h : ∀ j ∈ s, ∀ z, g (z + latticeUnitVector j) = g z) (a : Fin 4 → ℤ) (z : Fin 4 → ℤ) :
    g (z + ∑ i ∈ s, a i • latticeUnitVector i) = g z := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty => simp
  | insert i s hi ih =>
    have e : z + ∑ i ∈ insert i s, a i • latticeUnitVector i =
        (z + ∑ i ∈ s, a i • latticeUnitVector i) + a i • latticeUnitVector i := by
      rw [Finset.sum_insert hi]
      abel
    rw [e, comp_add_zsmul_of_step (h i (Finset.mem_insert_self _ _)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]
theorem eq_sum_latticeUnitVector (z : Fin 4 → ℤ) : z = ∑ i, z i • latticeUnitVector i := by
  funext k
  simp [latticeUnitVector, Finset.sum_apply, Pi.single_apply]
theorem eq_zero_of_steps {g : (Fin 4 → ℤ) → ℝ} (h : ∀ j z, g (z + latticeUnitVector j) = g z)
    (z : Fin 4 → ℤ) : g z = g 0 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.eq_at_zero_of_step_invariant <;> assumption
end Steps
section Cell
variable {L : ℕ} [NeZero L]
def siteRep (t : TorusSite L) : Fin 4 → ℤ := fun i => ((t i).val : ℤ)
theorem siteRep_siteOfInt (z : Fin 4 → ℤ) (i : Fin 4) :
    siteRep (siteOfInt z : TorusSite L) i = z i % (L : ℤ) :=
  ZMod.val_intCast (z i)
theorem siteRep_mem_Ico (t : TorusSite L) (i : Fin 4) : 0 ≤ siteRep t i ∧ siteRep t i < (L : ℤ) := by
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have := ZMod.val_lt (t i)
  show ((t i).val : ℤ) < (L : ℤ)
  exact_mod_cast this
def blockCellEquiv (L : ℕ) [NeZero L] : ((Fin 4 → ℤ) × TorusSite L) ≃ (Fin 4 → ℤ) where
  toFun p := (L : ℤ) • p.1 + siteRep p.2
  invFun z := (fun i => z i / (L : ℤ), siteOfInt z)
  left_inv := by
    rintro ⟨u, t⟩
    have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
    refine Prod.ext ?_ ?_
    · funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Int.mul_add_ediv_left _ _ hL,
        Int.ediv_eq_zero_of_lt (siteRep_mem_Ico t i).1 (siteRep_mem_Ico t i).2, add_zero]
    · funext i
      simp [siteOfInt, siteRep]
  right_inv := by
    intro z
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, siteRep_siteOfInt]
    exact Int.mul_ediv_add_emod _ _
theorem tsum_eq_sum_tsum_blockCell {g : (Fin 4 → ℤ) → ℝ} (hg : Summable g) :
    ∑' z, g z = ∑ t : TorusSite L, ∑' u : Fin 4 → ℤ, g ((L : ℤ) • u + siteRep t) := by
  have s1 : Summable fun p : TorusSite L × (Fin 4 → ℤ) => g ((L : ℤ) • p.2 + siteRep p.1) :=
    ((Equiv.prodComm _ _).trans (blockCellEquiv L)).summable_iff.mpr hg
  rw [← ((Equiv.prodComm _ _).trans (blockCellEquiv L)).tsum_eq g]
  calc _ = ∑' (t : TorusSite L) (u : Fin 4 → ℤ), g ((L : ℤ) • u + siteRep t) := s1.tsum_prod
    _ = _ := tsum_fintype _
def IsBlockPeriodic (L : ℕ) (g : (Fin 4 → ℤ) → ℝ) : Prop := ∀ v z, g (z + (L : ℤ) • v) = g z
theorem IsBlockPeriodic.apply_siteRep {g : (Fin 4 → ℤ) → ℝ} (hg : IsBlockPeriodic L g) (z : Fin 4 → ℤ) :
    g (siteRep (siteOfInt z : TorusSite L)) = g z := by
  have e := (blockCellEquiv L).right_inv z
  have e2 : z = siteRep (siteOfInt z : TorusSite L) + (L : ℤ) • (fun i => z i / (L : ℤ)) := by
    conv_lhs => rw [← e]
    exact add_comm _ _
  conv_rhs => rw [e2]
  exact (hg _ _).symm
theorem IsBlockPeriodic.sum_cell_add {g : (Fin 4 → ℤ) → ℝ} (hg : IsBlockPeriodic L g) (w : Fin 4 → ℤ) :
    ∑ t : TorusSite L, g (siteRep t + w) = ∑ t : TorusSite L, g (siteRep t) := by
  have e : ∀ t : TorusSite L, g (siteRep t + w) = g (siteRep (t + siteOfInt w)) := by
    intro t
    have h1 : (siteOfInt (siteRep t + w) : TorusSite L) = t + siteOfInt w := by
      funext i
      simp [siteOfInt, siteRep]
    rw [← IsBlockPeriodic.apply_siteRep hg (siteRep t + w), h1]
  simp_rw [e]
  exact Fintype.sum_equiv (Equiv.addRight _) _ _ fun t => rfl
theorem siteRep_add_latticeUnitVector (t : TorusSite L) (j : Fin 4) :
    siteRep t + latticeUnitVector j = if (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) j = 0 then
      siteRep (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) + (L : ℤ) • latticeUnitVector j
    else siteRep (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) := by
  have hv : ((t j + 1).val : ℤ) = ((t j).val + 1 : ℤ) % (L : ℤ) := by
    have := ZMod.val_intCast (n := L) ((t j).val + 1 : ℤ)
    rw [← this]
    simp
  have hlt := ZMod.val_lt (t j)
  have hj : (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) j = t j + 1 := by
    simp [siteOfInt, latticeUnitVector]
  have hi : ∀ i, i ≠ j → (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) i = t i := by
    intro i hi
    simp [siteOfInt, latticeUnitVector, Pi.single_apply, hi]
  by_cases h : (t j).val + 1 < L
  · have h0 : ((t j + 1).val : ℤ) = (t j).val + 1 := by
      rw [hv]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h)
    have hne : (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) j ≠ 0 := by
      rw [hj]
      intro e
      rw [e, ZMod.val_zero] at h0
      push_cast at h0
      omega
    rw [if_neg hne]
    funext i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.add_apply, siteRep, hj, h0]
      simp [latticeUnitVector]
    · simp only [Pi.add_apply, siteRep, hi i hij]
      simp [latticeUnitVector, Pi.single_apply, hij]
  · have he : (t j).val + 1 = L := by omega
    have h0 : t j + 1 = 0 := by
      have : (((t j).val + 1 : ℕ) : ZMod L) = 0 := by
        rw [he]
        simp
      simpa using this
    have hz : (t + (siteOfInt (latticeUnitVector j) : TorusSite L)) j = 0 := by rw [hj, h0]
    rw [if_pos hz]
    funext i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.add_apply, Pi.smul_apply, siteRep, hz]
      have : ((t i).val : ℤ) + 1 = (L : ℤ) := by exact_mod_cast he
      simpa [latticeUnitVector] using this
    · simp only [Pi.add_apply, Pi.smul_apply, siteRep, hi i hij]
      simp [latticeUnitVector, Pi.single_apply, hij]
theorem sum_cell_step (j : Fin 4) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ t : TorusSite L, g (siteRep t + latticeUnitVector j) - ∑ t : TorusSite L, g (siteRep t) =
      ∑ t : TorusSite L, if t j = 0 then g (siteRep t + (L : ℤ) • latticeUnitVector j) - g (siteRep t)
        else 0 := by
  set G : TorusSite L → ℝ := fun s =>
    if s j = 0 then g (siteRep s + (L : ℤ) • latticeUnitVector j) else g (siteRep s) with hG
  have e1 : ∑ t : TorusSite L, g (siteRep t + latticeUnitVector j) = ∑ s, G s := by
    refine Fintype.sum_equiv (Equiv.addRight (siteOfInt (latticeUnitVector j) : TorusSite L)) _ _ fun t => ?_
    simp only [Equiv.coe_addRight, hG]
    rw [siteRep_add_latticeUnitVector t j]
    split_ifs <;> rfl
  rw [e1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [hG]
  split_ifs <;> simp
end Cell
section Primitive
def discretePrimitive (h : ℤ → ℝ) (s : ℤ) : ℝ := ∑ i ∈ Finset.Ico 0 s, h i - ∑ i ∈ Finset.Ico s 0, h i
theorem discretePrimitive_succ_sub (h : ℤ → ℝ) (s : ℤ) :
    discretePrimitive h (s + 1) - discretePrimitive h s = h s := by
  unfold discretePrimitive
  by_cases hs : 0 ≤ s
  · have e1 : Finset.Ico 0 (s + 1) = insert s (Finset.Ico 0 s) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have e2 : Finset.Ico (s + 1) 0 = ∅ := Finset.Ico_eq_empty (by omega)
    have e3 : Finset.Ico s 0 = ∅ := Finset.Ico_eq_empty (by omega)
    have e4 : s ∉ Finset.Ico 0 s := by simp
    rw [e1, e2, e3, Finset.sum_insert e4]
    simp
  · have e1 : Finset.Ico s 0 = insert s (Finset.Ico (s + 1) 0) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have e2 : Finset.Ico 0 (s + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    have e3 : Finset.Ico 0 s = ∅ := Finset.Ico_eq_empty (by omega)
    have e4 : s ∉ Finset.Ico (s + 1) 0 := by simp
    rw [e1, e2, e3, Finset.sum_insert e4]
    simp
theorem abs_discretePrimitive_le {h : ℤ → ℝ} {B : ℝ} (s : ℤ)
    (hB : ∀ i : ℤ, |(i : ℝ)| ≤ |(s : ℝ)| → |h i| ≤ B) (hB0 : 0 ≤ B) :
    |discretePrimitive h s| ≤ |(s : ℝ)| * B := by
  unfold discretePrimitive
  by_cases hs : 0 ≤ s
  · have e3 : Finset.Ico s 0 = ∅ := Finset.Ico_eq_empty (by omega)
    rw [e3, Finset.sum_empty, sub_zero]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ B fun i hi => hB i ?_).trans ?_
    · have := Finset.mem_Ico.mp hi
      rw [abs_of_nonneg (by exact_mod_cast this.1), abs_of_nonneg (by exact_mod_cast hs)]
      exact_mod_cast this.2.le
    · rw [Int.card_Ico, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hB0
      rw [abs_of_nonneg (by exact_mod_cast hs)]
      simp only [sub_zero]
      have hr : ((s.toNat : ℕ) : ℝ) = (s : ℝ) := by
        have := Int.toNat_of_nonneg hs
        exact_mod_cast this
      rw [hr]
  · have e3 : Finset.Ico 0 s = ∅ := Finset.Ico_eq_empty (by omega)
    rw [e3, Finset.sum_empty, zero_sub, abs_neg]
    have hs' : s < 0 := by omega
    have hsr : (s : ℝ) < 0 := by exact_mod_cast hs'
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ B fun i hi => hB i ?_).trans ?_
    · have := Finset.mem_Ico.mp hi
      have h1 : (s : ℝ) ≤ i := by exact_mod_cast this.1
      have h2 : (i : ℝ) < 0 := by exact_mod_cast this.2
      rw [abs_of_neg h2, abs_of_neg hsr]
      linarith
    · rw [Int.card_Ico, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hB0
      rw [abs_of_neg hsr]
      simp only [zero_sub]
      have hr : (((-s).toNat : ℕ) : ℝ) = -(s : ℝ) := by
        have := Int.toNat_of_nonneg (show 0 ≤ -s by omega)
        exact_mod_cast this
      rw [hr]
theorem offsetNormReal_zsmul_axis_le (s : ℤ) : offsetNormReal (s • latticeUnitVector 0) ≤ |(s : ℝ)| := by
  unfold offsetNormReal
  have : offsetNorm (s • latticeUnitVector 0) ≤ s.natAbs := offsetNorm_le_of_forall fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, latticeUnitVector, Int.natAbs_mul]
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [Pi.single_apply, hi]
  calc ((offsetNorm (s • latticeUnitVector 0) : ℕ) : ℝ) ≤ (s.natAbs : ℝ) := by exact_mod_cast this
    _ = |(s : ℝ)| := by simp [Nat.cast_natAbs]
theorem isSubexponential_discretePrimitive {g : (Fin 4 → ℤ) → ℝ} (hg : IsSubexponential g) :
    IsSubexponential fun z => discretePrimitive (fun s => g (s • latticeUnitVector 0)) (z 0) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hg.exists_nonneg_bound (half_pos hε)
  obtain ⟨D, hD0, hD⟩ := isSubexponential_offsetNormReal.exists_nonneg_bound (half_pos hε)
  refine ⟨D * C, fun z => ?_⟩
  set N : ℝ := offsetNormReal z with hN
  have hN0 : 0 ≤ N := offsetNormReal_nonneg z
  have hs : |((z 0 : ℤ) : ℝ)| ≤ N := abs_apply_le_offsetNormReal z 0
  have hB : ∀ i : ℤ, |(i : ℝ)| ≤ |((z 0 : ℤ) : ℝ)| →
      |g (i • latticeUnitVector 0)| ≤ C * Real.exp (ε / 2 * N) := by
    intro i hi
    refine (hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    exact mul_le_mul_of_nonneg_left ((offsetNormReal_zsmul_axis_le i).trans (hi.trans hs)) (half_pos hε).le
  have h1 := abs_discretePrimitive_le (z 0) hB (mul_nonneg hC0 (Real.exp_pos _).le)
  have h2 := hD z
  rw [abs_of_nonneg hN0] at h2
  calc _ ≤ _ := h1
    _ ≤ N * (C * Real.exp (ε / 2 * N)) :=
        mul_le_mul_of_nonneg_right hs (mul_nonneg hC0 (Real.exp_pos _).le)
    _ ≤ (D * Real.exp (ε / 2 * N)) * (C * Real.exp (ε / 2 * N)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hC0 (Real.exp_pos _).le)
    _ = D * C * Real.exp (ε * N) := by
        have : Real.exp (ε * N) = Real.exp (ε / 2 * N) * Real.exp (ε / 2 * N) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [this]
        ring
end Primitive
section Structure
variable {K : LatticeBond → LatticeBond → ℝ}
theorem add_latticeUnitVector_apply_zero {j : Fin 4} (hj : j ≠ 0) (z : Fin 4 → ℤ) :
    (z + latticeUnitVector j) 0 = z 0 := by
  simp [latticeUnitVector, Pi.single_apply, hj.symm]
theorem add_latticeUnitVector_zero_apply_zero (z : Fin 4 → ℤ) : (z + latticeUnitVector 0) 0 = z 0 + 1 := by
  simp [latticeUnitVector]
theorem exists_form_structure {G : LatticeBond → ℝ} {Λ : (Fin 4 → ℤ) → ℝ} {c : Fin 4 → ℝ}
    (hB : ∀ j : Fin 4, j ≠ 0 → ∀ z ν, G (z + latticeUnitVector j, ν) = G (z, ν))
    (hA : ∀ z ν, G (z + latticeUnitVector 0, ν) - G (z, ν) = c ν + latticeGradient Λ (z, ν)) :
    ∃ κ₁ κ₂ : Fin 4 → ℝ, κ₁ 0 = 0 ∧ κ₂ 0 = 0 ∧
      (∀ z (ν : Fin 4), ν ≠ 0 → G (z, ν) = κ₁ ν + ((z 0 : ℤ) : ℝ) * κ₂ ν) ∧
      ∀ z, G (z, 0) = G ((z 0) • latticeUnitVector 0, 0) := by
  have comm : ∀ (z : Fin 4 → ℤ) (i j : Fin 4),
      z + latticeUnitVector i + latticeUnitVector j = z + latticeUnitVector j + latticeUnitVector i :=
    fun z i j => by abel
  have hC : ∀ j : Fin 4, j ≠ 0 → ∀ z ν,
      latticeGradient Λ (z + latticeUnitVector j, ν) = latticeGradient Λ (z, ν) := by
    intro j hj z ν
    have a1 := hA (z + latticeUnitVector j) ν
    have a2 := hA z ν
    rw [comm, hB j hj, hB j hj] at a1
    linarith
  have hD : ∀ ν : Fin 4, ν ≠ 0 → ∀ z,
      latticeGradient Λ (z + latticeUnitVector 0, ν) = latticeGradient Λ (z, ν) := by
    intro ν hν z
    have a := hC ν hν z 0
    simp only [latticeGradient] at a ⊢
    have e1 := comm z ν 0
    simp only [latticeUnitVector] at e1 a ⊢
    rw [e1] at a
    linarith
  have hG : ∀ ν : Fin 4, ν ≠ 0 → ∀ z, latticeGradient Λ (z, ν) = latticeGradient Λ (0, ν) := by
    intro ν hν z
    refine eq_zero_of_steps (g := fun z => latticeGradient Λ (z, ν)) (fun j z => ?_) z
    by_cases hj : j = 0
    · subst hj
      exact hD ν hν z
    · exact hC j hj z ν
  refine ⟨fun ν => if ν = 0 then 0 else G (0, ν),
    fun ν => if ν = 0 then 0 else c ν + latticeGradient Λ (0, ν), by simp, by simp, ?_, ?_⟩
  · intro z ν hν
    have hR := eq_zero_of_steps
      (g := fun z => G (z, ν) - ((z 0 : ℤ) : ℝ) * (c ν + latticeGradient Λ (0, ν))) (fun j z => ?_) z
    · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, sub_zero] at hR
      simp only [hν, if_false]
      linarith
    · by_cases hj : j = 0
      · subst hj
        have a := hA z ν
        rw [hG ν hν z] at a
        simp only [add_latticeUnitVector_zero_apply_zero]
        push_cast
        linarith
      · simp only [add_latticeUnitVector_apply_zero hj, hB j hj]
  · intro z
    have hs := comp_add_sum_of_steps (Finset.univ.erase 0) (g := fun z => G (z, 0))
      (fun j hj z => hB j (Finset.ne_of_mem_erase hj) z 0) z ((z 0) • latticeUnitVector 0)
    have e : (z 0) • latticeUnitVector 0 + ∑ i ∈ Finset.univ.erase 0, z i • latticeUnitVector i = z := by
      conv_rhs => rw [eq_sum_latticeUnitVector z]
      exact Finset.add_sum_erase _ (fun i => z i • latticeUnitVector i) (Finset.mem_univ 0)
    simp only [e] at hs
    exact hs
theorem kernelApply_eq_zero_of_form (hK : IsLatticeHessianKernel K) {G : LatticeBond → ℝ}
    (hG : IsSubexponentialForm G) {κ₁ κ₂ : Fin 4 → ℝ} (h1 : κ₁ 0 = 0) (h2 : κ₂ 0 = 0)
    (h3 : ∀ z (ν : Fin 4), ν ≠ 0 → G (z, ν) = κ₁ ν + ((z 0 : ℤ) : ℝ) * κ₂ ν)
    (h4 : ∀ z, G (z, 0) = G ((z 0) • latticeUnitVector 0, 0)) (c : LatticeBond) : kernelApply K G c = 0 := by
  set Θ : (Fin 4 → ℤ) → ℝ := fun z =>
    discretePrimitive (fun s => G (s • latticeUnitVector 0, 0)) (z 0) with hΘ
  have hm : IsSubexponential Θ := isSubexponential_discretePrimitive (hG 0)
  have e : G = fun b => (latticeGradient Θ b + κ₁ b.2) + ((b.1 0 : ℤ) : ℝ) * κ₂ b.2 := by
    funext ⟨z, ν⟩
    simp only [latticeGradient, hΘ]
    by_cases hν : ν = 0
    · subst hν
      have := discretePrimitive_succ_sub (fun s => G (s • latticeUnitVector 0, 0)) (z 0)
      have e1 : (z + Pi.single 0 1 : Fin 4 → ℤ) 0 = z 0 + 1 := by simp
      rw [e1, this, h1, h2, h4 z]
      simp
    · have e1 : (z + Pi.single ν 1 : Fin 4 → ℤ) 0 = z 0 := by simp [Pi.single_apply, Ne.symm hν]
      rw [e1, h3 z ν hν]
      simp
  rw [e, kernelApply_add hK ((isSubexponentialForm_gradient hm).add (isSubexponentialForm_direction κ₁))
      (isSubexponentialForm_linear κ₂),
    kernelApply_add hK (isSubexponentialForm_gradient hm) (isSubexponentialForm_direction κ₁),
    kernelApply_gradient hK hm, kernelApply_direction hK, kernelApply_linear hK h2]
  simp
end Structure
section Final
variable {L : ℕ} [NeZero L] {K Pl : LatticeBond → LatticeBond → ℝ}
theorem isSubexponentialForm_kernelApply (hK : IsLatticeHessianKernel K) {f : LatticeBond → ℝ}
    (hf : IsSubexponentialForm f) : IsSubexponentialForm (kernelApply K f) := by
  obtain ⟨M, θ, hM, hθ, h⟩ := hK.exists_bound
  intro ν ε hε
  have one : ∀ μ : Fin 4, ∃ C : ℝ, ∀ z : Fin 4 → ℤ,
      |∑' x, K (z, ν) (x, μ) * f (x, μ)| ≤ C * Real.exp (ε * offsetNormReal z) := by
    intro μ
    obtain ⟨C, -, hC⟩ := tsum_decay_mul_bound hθ (hf μ) hε
    exact ⟨M * C, fun z => (hC M z (fun x => K (z, ν) (x, μ)) hM fun x => h (z, ν) (x, μ)).2⟩
  choose C hC using one
  refine ⟨∑ μ, C μ, fun z => ?_⟩
  unfold kernelApply latticeBondSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun μ _ => hC μ z
theorem kernelApply_finset_sum (hK : IsLatticeHessianKernel K) {ι : Type*} (s : Finset ι)
    {f : ι → LatticeBond → ℝ} (hf : ∀ i ∈ s, IsSubexponentialForm (f i)) (c : LatticeBond) :
    kernelApply K (fun b => ∑ i ∈ s, f i b) c = ∑ i ∈ s, kernelApply K (f i) c := by
  unfold kernelApply latticeBondSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun i hi => summable_kernel_mul hK (hf i hi ν) c ν
theorem kernelApply_divergence (hK : IsLatticeHessianKernel K) {f : LatticeBond → ℝ}
    (hf : IsSubexponentialForm f) (x : Fin 4 → ℤ) :
    ∑ ν, (kernelApply K f (x - latticeUnitVector ν, ν) - kernelApply K f (x, ν)) = 0 := by
  unfold kernelApply latticeBondSum
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have s1 := fun ν : Fin 4 => summable_kernel_mul hK (hf μ) (x - latticeUnitVector ν, ν) μ
  have s2 := fun ν : Fin 4 => summable_kernel_mul hK (hf μ) (x, ν) μ
  simp_rw [← fun ν => (s1 ν).tsum_sub (s2 ν)]
  rw [← Summable.tsum_finsetSum fun ν _ => (s1 ν).sub (s2 ν)]
  have : ∀ z : Fin 4 → ℤ, ∑ ν : Fin 4,
      (K (x - latticeUnitVector ν, ν) (z, μ) * f (z, μ) - K (x, ν) (z, μ) * f (z, μ)) = 0 := by
    intro z
    have g := hK.divergence_zero (z, μ) x
    have e : ∀ ν : Fin 4, K (x - latticeUnitVector ν, ν) (z, μ) * f (z, μ) - K (x, ν) (z, μ) * f (z, μ) =
        (K (z, μ) (x - latticeUnitVector ν, ν) - K (z, μ) (x, ν)) * f (z, μ) := by
      intro ν
      rw [hK.symm (x - latticeUnitVector ν, ν), hK.symm (x, ν)]
      ring
    simp_rw [e]
    rw [← Finset.sum_mul, g, zero_mul]
  simp [this]
theorem sum_cell_mul_gradient_eq_zero {F : Fin 4 → (Fin 4 → ℤ) → ℝ} {lam : (Fin 4 → ℤ) → ℝ}
    (hF : ∀ ν, IsBlockPeriodic L (F ν)) (hl : IsBlockPeriodic L lam)
    (hd : ∀ x, ∑ ν, (F ν (x - latticeUnitVector ν) - F ν x) = 0) :
    ∑ ν, ∑ t : TorusSite L, F ν (siteRep t) * (lam (siteRep t + latticeUnitVector ν) - lam (siteRep t)) = 0 := by
  have e : ∀ ν, ∑ t : TorusSite L, F ν (siteRep t) * lam (siteRep t + latticeUnitVector ν) =
      ∑ t : TorusSite L, F ν (siteRep t - latticeUnitVector ν) * lam (siteRep t) := by
    intro ν
    have hp : IsBlockPeriodic L fun z => F ν (z - latticeUnitVector ν) * lam z := by
      intro v z
      simp only
      have : z + (L : ℤ) • v - latticeUnitVector ν = (z - latticeUnitVector ν) + (L : ℤ) • v := by abel
      rw [hl v z, this, hF ν v]
    have := IsBlockPeriodic.sum_cell_add hp (latticeUnitVector ν)
    simpa only [add_sub_cancel_right] using this
  calc ∑ ν, ∑ t : TorusSite L, F ν (siteRep t) * (lam (siteRep t + latticeUnitVector ν) - lam (siteRep t))
      = ∑ ν, ∑ t : TorusSite L, (F ν (siteRep t - latticeUnitVector ν) - F ν (siteRep t)) * lam (siteRep t) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        simp_rw [mul_sub, sub_mul]
        rw [Finset.sum_sub_distrib, e ν, Finset.sum_sub_distrib]
    _ = ∑ t : TorusSite L, ∑ ν, (F ν (siteRep t - latticeUnitVector ν) - F ν (siteRep t)) * lam (siteRep t) :=
        Finset.sum_comm
    _ = 0 := by
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [← Finset.sum_mul, hd, zero_mul]
theorem isBlockPeriodic_of_moment_zero (hP : IsLatticeBlockKernel L Pl) {lam : (Fin 4 → ℤ) → ℝ} {C : ℝ}
    (hC : ∀ z, |lam z| ≤ C)
    (h : ∀ b, blockKernelMoment Pl 0 b = (L : ℝ)⁻¹ * constantOneForm secondAxis b + latticeGradient lam b) :
    IsBlockPeriodic L lam := by
  intro v z
  set w : Fin 4 → ℤ := (L : ℤ) • v with hw
  have hstep : ∀ (j : Fin 4) (y : Fin 4 → ℤ), lam (y + latticeUnitVector j + w) - lam (y + latticeUnitVector j) =
      lam (y + w) - lam y := by
    intro j y
    have a := blockKernelMoment_zero_translate hP v (y, j)
    rw [h, h] at a
    simp only [latticeGradient, constantOneForm] at a
    have e : y + latticeUnitVector j + w = y + w + Pi.single j 1 := by
      simp only [latticeUnitVector]
      abel
    rw [e]
    simp only [latticeUnitVector]
    linarith
  have hc : ∀ y, lam (y + w) - lam y = lam (0 + w) - lam 0 :=
    fun y => eq_zero_of_steps (g := fun y => lam (y + w) - lam y) hstep y
  set ω : ℝ := lam (0 + w) - lam 0 with hω
  have hk : ∀ k : ℕ, lam (z + k • w) = lam z + k * ω := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z + (k + 1) • w = (z + k • w) + w := by
        rw [add_smul, one_smul, add_assoc]
      have := hc (z + k • w)
      rw [e]
      push_cast
      linarith
  have h0 : ω = 0 := by
    by_contra hne
    have hpos : 0 < |ω| := abs_pos.mpr hne
    obtain ⟨k, hk'⟩ := exists_nat_gt (2 * C / |ω|)
    have h1 : 2 * C < k * |ω| := by
      rwa [div_lt_iff₀ hpos] at hk'
    have h2 := hk k
    have h3 : (k : ℝ) * ω = lam (z + k • w) - lam z := by linarith
    have h4 : |(k : ℝ) * ω| ≤ 2 * C := by
      rw [h3]
      have a := abs_le.mp (hC (z + k • w))
      have b := abs_le.mp (hC z)
      exact abs_le.mpr ⟨by linarith [a.1, b.2], by linarith [a.2, b.1]⟩
    rw [abs_mul, Nat.abs_cast] at h4
    linarith
  have := hc z
  linarith
theorem sum_cell_face (a : ℝ) : ∑ t : TorusSite L, (if t 0 = 0 then a else 0) = (L : ℝ) ^ 3 * a := by
  classical
  have e : (Finset.univ.filter fun t : TorusSite L => t 0 = 0) =
      Fintype.piFinset fun i : Fin 4 => if i = 0 then {0} else Finset.univ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = 0
      · subst hi
        simp [h]
      · simp [hi]
    · intro h
      simpa using h 0
  rw [← Finset.sum_filter, Finset.sum_const, e, Fintype.card_piFinset, Fin.prod_univ_four]
  simp [ZMod.card]
  left
  ring
def cellSecondMoment (L : ℕ) [NeZero L] (Pl : LatticeBond → LatticeBond → ℝ) (b : LatticeBond) : ℝ :=
  ∑ t : TorusSite L, blockKernelMoment Pl 2 (b.1 + siteRep t, b.2)
theorem isSubexponentialForm_cellSecondMoment (hP : IsLatticeBlockKernel L Pl) (hL : 0 < L) :
    IsSubexponentialForm (cellSecondMoment L Pl) := fun ν =>
  IsSubexponential.finset_sum _ fun t _ =>
    ((isSubexponentialForm_blockKernelMoment hP hL 2) ν).comp_add (siteRep t)
def squareCoordForm (b : LatticeBond) : ℝ := ((b.1 0 : ℤ) : ℝ) ^ 2 * constantOneForm secondAxis b
theorem isSubexponentialForm_squareCoordForm : IsSubexponentialForm squareCoordForm := fun ν =>
  (isSubexponential_pow (isSubexponential_coord 0) 2).mul
    (IsSubexponential.of_bounded (g := fun _ => constantOneForm secondAxis (0, ν))
      (C := |constantOneForm secondAxis (0, ν)|) fun _ => le_refl _)
theorem kernelApply_squareCoordForm : kernelApply K squareCoordForm (0, secondAxis) = latticeSecondMoment K := by
  unfold kernelApply latticeBondSum latticeSecondMoment
  rw [Finset.sum_eq_single secondAxis]
  · refine tsum_congr fun z => ?_
    simp [squareCoordForm, constantOneForm]
  · intro ν _ hν
    simp [squareCoordForm, constantOneForm, hν]
  · simp
theorem cellSecondMoment_step (hP : IsLatticeBlockKernel L Pl) (j : Fin 4) (z : Fin 4 → ℤ) (ν : Fin 4) :
    cellSecondMoment L Pl (z + latticeUnitVector j, ν) - cellSecondMoment L Pl (z, ν) =
      ∑ t : TorusSite L, if t j = 0 then
        blockKernelMoment Pl 2 (z + (siteRep t + (L : ℤ) • latticeUnitVector j), ν) -
          blockKernelMoment Pl 2 (z + siteRep t, ν) else 0 := by
  have h := sum_cell_step (L := L) j fun y => blockKernelMoment Pl 2 (z + y, ν)
  rw [← h]
  unfold cellSecondMoment
  simp only
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  abel
theorem kernelApply_cellSecondMoment (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl)
    (hL : 0 < L) : kernelApply K (cellSecondMoment L Pl) (0, secondAxis) = (L : ℝ) * latticeSecondMoment K := by
  obtain ⟨lam, ⟨C, hC⟩, h0⟩ := blockKernelMoment_zero_eq hP
  obtain ⟨f, κ, hf, h1⟩ := blockKernelMoment_one_eq hP
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  set G : LatticeBond → ℝ := fun b => cellSecondMoment L Pl b - (L : ℝ) * squareCoordForm b with hGdef
  have mA := isSubexponentialForm_cellSecondMoment hP hL
  have mS : IsSubexponentialForm fun b => (L : ℝ) * squareCoordForm b :=
    isSubexponentialForm_squareCoordForm.const_mul _
  have mG : IsSubexponentialForm G := mA.sub mS
  have hB : ∀ j : Fin 4, j ≠ 0 → ∀ z ν, G (z + latticeUnitVector j, ν) = G (z, ν) := by
    intro j hj z ν
    have a := cellSecondMoment_step hP j z ν
    have hz : (∑ t : TorusSite L, if t j = 0 then
        blockKernelMoment Pl 2 (z + (siteRep t + (L : ℤ) • latticeUnitVector j), ν) -
          blockKernelMoment Pl 2 (z + siteRep t, ν) else 0) = 0 := by
      refine Finset.sum_eq_zero fun t _ => ?_
      split_ifs
      · have b := blockKernelMoment_two_translate hP hL (latticeUnitVector j) (z + siteRep t, ν)
        have e0 : latticeUnitVector j 0 = 0 := by simp [latticeUnitVector, Pi.single_apply, hj.symm]
        simp only [e0, Int.cast_zero] at b
        have e1 : z + (siteRep t + (L : ℤ) • latticeUnitVector j) =
            z + siteRep t + (L : ℤ) • latticeUnitVector j := by abel
        rw [e1, b]
        ring
      · rfl
    rw [hz] at a
    simp only [hGdef, squareCoordForm, add_latticeUnitVector_apply_zero hj]
    have e2 : constantOneForm secondAxis (z + latticeUnitVector j, ν) = constantOneForm secondAxis (z, ν) := rfl
    rw [e2]
    linarith
  set Λ : (Fin 4 → ℤ) → ℝ := fun z => ∑ t : TorusSite L, if t 0 = 0 then
    2 * f (z + siteRep t) + lam (z + siteRep t) else 0 with hΛ
  set c : Fin 4 → ℝ := fun ν => 2 * (L : ℝ) ^ 3 * κ ν +
    ((L : ℝ) ^ 2 - L) * constantOneForm secondAxis ((0 : Fin 4 → ℤ), ν) with hc
  have hA : ∀ z ν, G (z + latticeUnitVector 0, ν) - G (z, ν) = c ν + latticeGradient Λ (z, ν) := by
    intro z ν
    have a := cellSecondMoment_step hP 0 z ν
    set x : ℝ := constantOneForm secondAxis ((0 : Fin 4 → ℤ), ν) with hx
    set a0 : ℝ := 2 * ((L : ℝ)⁻¹ ^ 2 * ((z 0 : ℤ) : ℝ) * x + κ ν) + (L : ℝ)⁻¹ * x with ha0
    have hterm : ∀ t : TorusSite L, (if t 0 = 0 then
        blockKernelMoment Pl 2 (z + (siteRep t + (L : ℤ) • latticeUnitVector 0), ν) -
          blockKernelMoment Pl 2 (z + siteRep t, ν) else 0) =
        (if t 0 = 0 then a0 else 0) +
          ((if t 0 = 0 then 2 * f (z + Pi.single ν 1 + siteRep t) + lam (z + Pi.single ν 1 + siteRep t)
              else 0) -
           (if t 0 = 0 then 2 * f (z + siteRep t) + lam (z + siteRep t) else 0)) := by
      intro t
      split_ifs with ht
      · have b := blockKernelMoment_two_translate hP hL (latticeUnitVector 0) (z + siteRep t, ν)
        have e0 : latticeUnitVector 0 0 = 1 := by simp [latticeUnitVector]
        simp only [e0, Int.cast_one] at b
        have e1 : z + (siteRep t + (L : ℤ) • latticeUnitVector 0) =
            z + siteRep t + (L : ℤ) • latticeUnitVector 0 := by abel
        have e3 : (z + siteRep t) 0 = z 0 := by
          have : siteRep t 0 = 0 := by simp [siteRep, ht]
          simp [this]
        have m0 := h0 (z + siteRep t, ν)
        have m1 := h1 (z + siteRep t, ν)
        simp only [e3] at m1
        have e4 : z + Pi.single ν 1 + siteRep t = z + siteRep t + Pi.single ν 1 := by abel
        have e5 : constantOneForm secondAxis (z + siteRep t, ν) = x := rfl
        rw [e1, b, e4, m0, m1, e5, ha0]
        simp only [latticeGradient]
        ring
      · simp
    simp_rw [hterm] at a
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cell_face] at a
    have hgr : latticeGradient Λ (z, ν) = (∑ t : TorusSite L, if t 0 = 0 then
        2 * f (z + Pi.single ν 1 + siteRep t) + lam (z + Pi.single ν 1 + siteRep t) else 0) -
        ∑ t : TorusSite L, if t 0 = 0 then 2 * f (z + siteRep t) + lam (z + siteRep t) else 0 := rfl
    rw [← hgr] at a
    simp only [hGdef, squareCoordForm]
    have e2 : constantOneForm secondAxis (z + latticeUnitVector 0, ν) = x := rfl
    have e3 : constantOneForm secondAxis (z, ν) = x := rfl
    rw [e2, e3, add_latticeUnitVector_zero_apply_zero]
    have e4 : c ν = 2 * (L : ℝ) ^ 3 * κ ν + ((L : ℝ) ^ 2 - L) * x := rfl
    rw [e4]
    have e5 : (L : ℝ) ^ 3 * a0 = 2 * (L : ℝ) * ((z 0 : ℤ) : ℝ) * x + 2 * (L : ℝ) ^ 3 * κ ν +
        (L : ℝ) ^ 2 * x := by
      rw [ha0]
      field_simp
    push_cast
    rw [e5] at a
    linear_combination a
  obtain ⟨κ₁, κ₂, k1, k2, k3, k4⟩ := exists_form_structure hB hA
  have hz := kernelApply_eq_zero_of_form hK mG k1 k2 k3 k4 (0, secondAxis)
  rw [hGdef, kernelApply_sub hK mA mS, kernelApply_const_mul, kernelApply_squareCoordForm] at hz
  linarith
theorem sum_cell_kernelApply (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl) (hL : 0 < L) :
    ∑ t : TorusSite L, kernelApply K (blockKernelMoment Pl 2) (siteRep t, secondAxis) =
      kernelApply K (cellSecondMoment L Pl) (0, secondAxis) := by
  unfold cellSecondMoment
  rw [kernelApply_finset_sum hK _ fun t _ => fun ν =>
    ((isSubexponentialForm_blockKernelMoment hP hL 2) ν).comp_add (siteRep t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have := kernelApply_translate hK (blockKernelMoment Pl 2) (siteRep t) (0, secondAxis)
  simpa using this
theorem tsum_blockKernel_mul_kernelApply (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl)
    (hL : 0 < L) (ν : Fin 4) :
    ∑' x : Fin 4 → ℤ, Pl (x, ν) (0, secondAxis) * kernelApply K (blockKernelMoment Pl 2) (x, ν) =
      ∑ t : TorusSite L, kernelApply K (blockKernelMoment Pl 2) (siteRep t, ν) *
        blockKernelMoment Pl 0 (siteRep t, ν) := by
  obtain ⟨M, θ, hM, hθ, h⟩ := hP.exists_bound
  have mF := isSubexponentialForm_kernelApply hK (isSubexponentialForm_blockKernelMoment hP hL 2)
  obtain ⟨C, -, hC⟩ := tsum_decay_mul_bound hθ (mF ν) one_pos
  have hs := (hC M 0 (fun x => Pl (x, ν) (0, secondAxis)) hM fun x => by
    have := h (x, ν) (0, secondAxis)
    simpa using this).1
  rw [tsum_eq_sum_tsum_blockCell (L := L) hs]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e1 : ∀ u : Fin 4 → ℤ, Pl ((L : ℤ) • u + siteRep t, ν) (0, secondAxis) *
      kernelApply K (blockKernelMoment Pl 2) ((L : ℤ) • u + siteRep t, ν) =
      kernelApply K (blockKernelMoment Pl 2) (siteRep t, ν) * Pl (siteRep t, ν) (-u, secondAxis) := by
    intro u
    have a := hP.translation_invariant u (siteRep t, ν) (-u, secondAxis)
    have b := kernelApply_blockKernelMoment_two_periodic hK hP hL u (siteRep t, ν)
    simp only [neg_add_cancel] at a
    rw [add_comm ((L : ℤ) • u), a, b]
    ring
  simp_rw [e1]
  rw [tsum_mul_left]
  congr 1
  have := (Equiv.neg (Fin 4 → ℤ)).tsum_eq fun y => Pl (siteRep t, ν) (y, secondAxis)
  simp only [Equiv.neg_apply] at this
  rw [this]
  simp [blockKernelMoment]
theorem latticeSecondMoment_kernelPullback (hK : IsLatticeHessianKernel K) (hP : IsLatticeBlockKernel L Pl)
    (hL : 0 < L) : latticeSecondMoment (kernelPullback Pl K) = latticeSecondMoment K := by
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  obtain ⟨lam, ⟨C, hC⟩, h0⟩ := blockKernelMoment_zero_eq hP
  rw [latticeSecondMoment_kernelPullback_eq hK hP hL]
  unfold latticeBondSum
  simp_rw [tsum_blockKernel_mul_kernelApply hK hP hL]
  set F : Fin 4 → (Fin 4 → ℤ) → ℝ := fun ν z => kernelApply K (blockKernelMoment Pl 2) (z, ν) with hF
  have hp : ∀ ν, IsBlockPeriodic L (F ν) := fun ν v z =>
    kernelApply_blockKernelMoment_two_periodic hK hP hL v (z, ν)
  have hd : ∀ x, ∑ ν, (F ν (x - latticeUnitVector ν) - F ν x) = 0 :=
    kernelApply_divergence hK (isSubexponentialForm_blockKernelMoment hP hL 2)
  have hg := sum_cell_mul_gradient_eq_zero (L := L) hp (isBlockPeriodic_of_moment_zero hP hC h0) hd
  have e : ∀ (ν : Fin 4) (t : TorusSite L),
      kernelApply K (blockKernelMoment Pl 2) (siteRep t, ν) * blockKernelMoment Pl 0 (siteRep t, ν) =
      (L : ℝ)⁻¹ * (constantOneForm secondAxis (siteRep t, ν) * F ν (siteRep t)) +
        F ν (siteRep t) * (lam (siteRep t + latticeUnitVector ν) - lam (siteRep t)) := by
    intro ν t
    rw [h0]
    simp only [latticeGradient, hF, latticeUnitVector]
    ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [hg, add_zero]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single secondAxis]
  · have e2 : ∀ t : TorusSite L, constantOneForm secondAxis (siteRep t, secondAxis) = 1 := fun t => by
      simp [constantOneForm]
    simp only [constantOneForm, if_true, one_mul, hF]
    rw [sum_cell_kernelApply hK hP hL, kernelApply_cellSecondMoment hK hP hL]
    field_simp
  · intro ν _ hν
    simp [constantOneForm, hν]
  · simp
theorem secondMomentPullbackInvariant_holds : SecondMomentPullbackInvariant := by
  intro L K Pl hL hK hP
  haveI : NeZero L := ⟨hL.ne'⟩
  exact latticeSecondMoment_kernelPullback hK hP hL
end Final
end YangMills.Construction.SlopeCoefficient
end
