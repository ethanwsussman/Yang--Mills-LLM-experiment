import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import YangMills.Construction.RunningCouplingSlope.ContourKernelsAreLocal
import YangMills.Construction.RunningCouplingSlope.FloorOfFormsOffTheTrees
import YangMills.Construction.RunningCouplingSlope.NextFormOfResponsesIsAChainFormProof
import YangMills.Construction.RunningCouplingSlope.ResponsesOfGreenKernels
import YangMills.Construction.RunningCouplingSlope.SumsOverToriTendToSumsOverTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open FlatLinearization TorusFields TorusLumps ExponentialSums SlopeCoefficient BlockAverages
namespace RunningCouplingSlope
namespace GreenResponse
section Algebra
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem responseOfInverse_eq (a : ℝ) (G : (n : ℕ) → TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (b : TorusBond (n * L)) (c : TorusBond n) :
    responseOfInverse a L G n b c = ∑ x, G n b x * flatStepSource a L c x := by
  unfold responseOfInverse
  rw [dif_pos ⟨NeZero.ne n, NeZero.ne L⟩]
private theorem flatStepOperator_sum_of_tree (a : ℝ) (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    {b : TorusBond (n * L)} (hb : IsBlockTreeBond L b) (f : TorusBond (n * L) → ℝ) :
    ∑ x, flatStepOperator a L K b x * f x = f b := by
  classical
  rw [Finset.sum_eq_single b]
  · simp [flatStepOperator, hb]
  · intro x _ hx
    simp [flatStepOperator, hb, Ne.symm hx]
  · simp
private theorem flatStepOperator_sum_of_not_tree (a : ℝ) (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    {b : TorusBond (n * L)} (hb : ¬ IsBlockTreeBond L b) {f : TorusBond (n * L) → ℝ}
    (hf : VanishesOnBlockTrees L f) :
    ∑ x, flatStepOperator a L K b x * f x =
      ∑ x, K b x * f x + a * ∑ c : TorusBond n, contourWeight L c b * ∑ x, contourWeight L c x * f x := by
  classical
  have e : ∀ x, flatStepOperator a L K b x * f x =
      K b x * f x + a * ∑ c : TorusBond n, contourWeight L c b * (contourWeight L c x * f x) := by
    intro x
    by_cases hx : IsBlockTreeBond L x
    · simp [hf x hx]
    · have h1 : ¬ (IsBlockTreeBond L b ∨ IsBlockTreeBond L x) := by
        rintro (h | h)
        · exact hb h
        · exact hx h
      have h2 : ∑ c : TorusBond n, contourWeight L c b * (contourWeight L c x * f x) =
          (∑ c : TorusBond n, contourWeight L c b * contourWeight L c x) * f x := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      unfold flatStepOperator
      rw [if_neg h1, h2]
      ring
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]
private theorem sum_mul_sum_of_right_inv {m : ℕ} [NeZero m] (T G : TorusBond m → TorusBond m → ℝ)
    (hR : ∀ b c, ∑ x, T b x * G x c = if b = c then 1 else 0) (s : TorusBond m → ℝ) (b : TorusBond m) :
    ∑ x, T b x * ∑ y, G x y * s y = s b := by
  have e : ∑ x, T b x * ∑ y, G x y * s y = ∑ y, (∑ x, T b x * G x y) * s y := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  simp only [hR]
  simp
private theorem isMinimizerFamily_of_right_inv (a : ℝ) (K G : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (hsym : ∀ b c, K b c = K c b)
    (hQ : ∀ (ξ : RealOneForm (n * L)) (c : TorusBond n),
      _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c = ∑ b, contourWeight L c b * ξ b)
    (hR : ∀ b c, ∑ x, flatStepOperator a L K b x * G x c = if b = c then 1 else 0) :
    IsMinimizerFamily a L K (fun b c => ∑ x, G b x * flatStepSource a L c x) := by
  classical
  intro c
  let p : RealOneForm (n * L) := fun b => ∑ x, G b x * flatStepSource a L c x
  have hTp : ∀ b, ∑ x, flatStepOperator a L K b x * p x = flatStepSource a L c b :=
    fun b => sum_mul_sum_of_right_inv _ G hR _ b
  have hoff : VanishesOnBlockTrees L p := fun b hb => by
    have h1 := hTp b
    rw [flatStepOperator_sum_of_tree a K hb] at h1
    rw [h1]
    simp [flatStepSource, hb]
  refine ⟨hoff, fun ζ hζ => ?_⟩
  show kernelPairing K p ζ + a * ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ζ c' = 0
  have hrow : ∀ x, ¬ IsBlockTreeBond L x →
      ∑ b, K x b * p b +
        a * ∑ c', contourWeight L c' x * (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c') = 0 := by
    intro x hx
    have h1 := hTp x
    rw [flatStepOperator_sum_of_not_tree a K hx hoff] at h1
    have h2 : ∑ c', contourWeight L c' x * (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c') =
        (∑ c', contourWeight L c' x * ∑ y, contourWeight L c' y * p y) - contourWeight L c x := by
      simp only [mul_sub, Finset.sum_sub_distrib, hQ p]
      congr 1
      simp [indicatorForm]
    rw [h2, mul_sub, ← add_sub_assoc, h1]
    simp [flatStepSource, hx]
  have h1 : kernelPairing K p ζ = ∑ x, ζ x * ∑ b, K x b * p b := by
    unfold kernelPairing
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsym b x]
    ring
  have h2 : ∑ c', (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c') * _root_.YangMills.Construction.FlatLinearization.contourAverage L ζ c' =
      ∑ x, ζ x * ∑ c', contourWeight L c' x * (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c') := by
    simp only [hQ ζ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : IsBlockTreeBond L x
  · simp [hζ x hx]
  · have h3 := hrow x hx
    calc ζ x * ∑ b, K x b * p b +
          a * (ζ x * ∑ c', contourWeight L c' x * (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c'))
        = ζ x * (∑ b, K x b * p b +
          a * ∑ c', contourWeight L c' x * (_root_.YangMills.Construction.FlatLinearization.contourAverage L p c' - indicatorForm c c')) := by ring
      _ = 0 := by rw [h3, mul_zero]
private theorem curlEnergy_nonneg {m : ℕ} [NeZero m] (ξ : RealOneForm m) : 0 ≤ curlEnergy ξ := by apply _root_.YangMills.SharedProofs.p115143 <;> assumption
private theorem isPositiveOnTreeGauge_of_lower_bounds {a κ C : ℝ} (ha : 0 < a) (hκ : 0 < κ) (hC : 0 < C)
    (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (hf : ∀ ξ : RealOneForm (n * L), κ * curlEnergy ξ ≤ kernelPairing K ξ ξ)
    (hg : ∀ ξ : RealOneForm (n * L), VanishesOnBlockTrees L ξ →
      ∑ b, ξ b ^ 2 ≤ C * (curlEnergy ξ + ∑ c : TorusBond n, _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c ^ 2)) :
    IsPositiveOnTreeGauge (n := n) a L K := by
  intro ξ hξ hne
  have hpos : 0 < ∑ b, ξ b ^ 2 := by
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hne
    have hb' : ξ b ≠ 0 := hb
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨b, Finset.mem_univ _, by positivity⟩
  have hS0 : 0 ≤ ∑ c : TorusBond n, _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc0 := curlEnergy_nonneg ξ
  have hsum : 0 < curlEnergy ξ + ∑ c : TorusBond n, _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c ^ 2 := by
    by_contra hh
    rw [not_lt] at hh
    have h1 := hg ξ hξ
    nlinarith
  have hm : 0 < min κ a := lt_min hκ ha
  have h3 : min κ a * (curlEnergy ξ + ∑ c : TorusBond n, _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c ^ 2) ≤
      κ * curlEnergy ξ + a * ∑ c : TorusBond n, _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ c ^ 2 := by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) hc0)
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hS0)
  have h4 := mul_pos hm hsum
  linarith [hf ξ]
end Algebra
section Bounds
private theorem abs_sum_mul_local_le {m : ℕ} [NeZero m] {M θ A : ℝ} {R : ℕ} (hθ : 0 < θ) (hA : 0 ≤ A)
    (w z : TorusSite m) (g s : TorusBond m → ℝ)
    (hg : ∀ x : TorusBond m, |g x| ≤ M * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w x.1)))
    (hs : ∀ x, |s x| ≤ A) (hz : ∀ x : TorusBond m, R < _root_.YangMills.Construction.TorusFields.supDist x.1 z → s x = 0) :
    |∑ x, g x * s x| ≤
      (|M| * A * Real.exp (2 * θ * (R : ℝ)) * (4 * expLatticeSum θ)) *
        Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z)) := by
  have hterm : ∀ x : TorusBond m, |g x * s x| ≤
      (|M| * A * Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z))) *
        Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z) := by
    intro x
    by_cases hx : R < _root_.YangMills.Construction.TorusFields.supDist x.1 z
    · rw [hz x hx, mul_zero, abs_zero]
      positivity
    · have hx' : _root_.YangMills.Construction.TorusFields.supDist x.1 z ≤ R := not_lt.mp hx
      have htri : _root_.YangMills.Construction.TorusFields.supDist w z ≤ _root_.YangMills.Construction.TorusFields.supDist w x.1 + _root_.YangMills.Construction.TorusFields.supDist x.1 z := _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
      have hr : (_root_.YangMills.Construction.TorusFields.supDist w z : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist w x.1 + _root_.YangMills.Construction.TorusFields.supDist x.1 z := by exact_mod_cast htri
      have hxr : (_root_.YangMills.Construction.TorusFields.supDist x.1 z : ℝ) ≤ R := by exact_mod_cast hx'
      have e1 : Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w x.1)) ≤
          Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z)) * Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have q1 := mul_le_mul_of_nonneg_left hr hθ.le
        have q2 := mul_le_mul_of_nonneg_left hxr hθ.le
        nlinarith
      have e2 : |g x| ≤ |M| * (Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z)) *
          Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z)) :=
        ((hg x).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)).trans
          (mul_le_mul_of_nonneg_left e1 (abs_nonneg M))
      rw [abs_mul]
      calc |g x| * |s x| ≤ (|M| * (Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z)) *
              Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z))) * A :=
            mul_le_mul e2 (hs x) (abs_nonneg _) (by positivity)
        _ = _ := by ring
  have hsum : ∑ x : TorusBond m, Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z) ≤ 4 * expLatticeSum θ := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have h1 := sum_torus_exp_le hθ z
    push_cast
    linarith
  calc |∑ x, g x * s x| ≤ ∑ x, |g x * s x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : TorusBond m, (|M| * A * Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z))) *
          Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z) := Finset.sum_le_sum fun x _ => hterm x
    _ = (|M| * A * Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z))) *
          ∑ x : TorusBond m, Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist x.1 z) := (Finset.mul_sum _ _ _).symm
    _ ≤ (|M| * A * Real.exp (2 * θ * (R : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist w z))) *
          (4 * expLatticeSum θ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
private theorem abs_mul_le_of_origin {m : ℕ} [NeZero m] {M θ A g s : ℝ} (hθ : 0 < θ) (_hA : 0 ≤ A)
    (e : LatticeBond) (x : TorusSite m)
    (hg : |g| ≤ M * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist (bondFrom 0 e : TorusBond m).1 x))) (hs : |s| ≤ A) :
    |g * s| ≤ |M| * Real.exp (θ * (offsetNorm e.1 : ℝ)) * A * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist x 0)) := by
  have hb : _root_.YangMills.Construction.TorusFields.supDist (bondFrom 0 e : TorusBond m).1 0 ≤ offsetNorm e.1 := by
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le 0 e.1 _ fun i =>
      Finset.le_sup (f := fun i => (e.1 i).natAbs) (Finset.mem_univ i)
  have htri : _root_.YangMills.Construction.TorusFields.supDist x 0 ≤ _root_.YangMills.Construction.TorusFields.supDist x (bondFrom 0 e : TorusBond m).1 + _root_.YangMills.Construction.TorusFields.supDist (bondFrom 0 e : TorusBond m).1 0 :=
    _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm x (bondFrom 0 e : TorusBond m).1] at htri
  have hr : (_root_.YangMills.Construction.TorusFields.supDist x 0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist (bondFrom 0 e : TorusBond m).1 x + offsetNorm e.1 := by
    exact_mod_cast htri.trans (Nat.add_le_add_left hb _)
  have e1 : Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist (bondFrom 0 e : TorusBond m).1 x)) ≤
      Real.exp (θ * (offsetNorm e.1 : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist x 0)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have q1 := mul_le_mul_of_nonneg_left hr hθ.le
    nlinarith
  have e2 : |g| ≤ |M| * (Real.exp (θ * (offsetNorm e.1 : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist x 0))) :=
    (hg.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)).trans
      (mul_le_mul_of_nonneg_left e1 (abs_nonneg M))
  rw [abs_mul]
  calc |g| * |s| ≤ (|M| * (Real.exp (θ * (offsetNorm e.1 : ℝ)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist x 0)))) * A :=
        mul_le_mul e2 hs (abs_nonneg _) (by positivity)
    _ = _ := by ring
private theorem abs_flatStepSource_le {n L : ℕ} {a C : ℝ} (ha : 0 < a) {c : TorusBond n}
    {x : TorusBond (n * L)} (h : |contourWeight L c x| ≤ C) : |flatStepSource a L c x| ≤ a * C := by
  have hC := (abs_nonneg _).trans h
  unfold flatStepSource
  split_ifs
  · rw [abs_zero]
    exact mul_nonneg ha.le hC
  · rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left h ha.le
private theorem flatStepSource_eq_zero {n L : ℕ} {a : ℝ} {c : TorusBond n} {x : TorusBond (n * L)}
    (h : contourWeight L c x = 0) : flatStepSource a L c x = 0 := by
  unfold flatStepSource
  split_ifs
  · rfl
  · rw [h, mul_zero]
end Bounds
section Translation
variable {n L : ℕ} [NeZero n] [NeZero L]
omit [NeZero L] in
private theorem blockCentreSite_add (y u : TorusSite n) :
    blockCentreSite L (y + u) = blockCentreSite L y + blockCentreSite L u := by
  funext i
  simp only [blockCentreSite, Pi.add_apply]
  rw [ZMod.val_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  unfold Nat.ModEq
  rw [← mul_add, mul_comm n L, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
private theorem coarseSite_add_blockCentreSite (x : TorusSite (n * L)) (u : TorusSite n) :
    coarseSite L (x + blockCentreSite L u) = coarseSite L x + u := by
  funext i
  simp only [coarseSite, Pi.add_apply, blockCentreSite]
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hv : (((u i).val : ℕ) : ZMod n) = u i := ZMod.natCast_zmod_val _
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (((x i + ((L * (u i).val : ℕ) : ZMod (n * L))).cast : ℤ)) =
      ((x i).cast : ℤ) + L * ((u i).val : ℤ) + ((n * L : ℕ) : ℤ) * t := by
    have h1 : (((((x i + ((L * (u i).val : ℕ) : ZMod (n * L))).cast : ℤ)) : ZMod (n * L))) =
        ((((x i).cast : ℤ) + L * ((u i).val : ℤ) : ℤ) : ZMod (n * L)) := by
      rw [ZMod.intCast_zmod_cast]
      push_cast
      rfl
    obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    exact ⟨-t, by linarith⟩
  have e : ((x i).cast : ℤ) + L * ((u i).val : ℤ) + ((n * L : ℕ) : ℤ) * t + ((L : ℤ) - 1) / 2 =
      (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) + (L : ℤ) * (((u i).val : ℤ) + (n : ℤ) * t) := by
    push_cast
    ring
  rw [ht, e, Int.add_mul_ediv_left _ _ hL]
  push_cast
  rw [hv]
  simp
private theorem offsetFromCentre_add_blockCentreSite (x : TorusSite (n * L)) (u : TorusSite n) :
    offsetFromCentre L (x + blockCentreSite L u) = offsetFromCentre L x := by
  funext i
  simp only [offsetFromCentre, coarseSite_add_blockCentreSite, blockCentreSite_add, add_sub_add_right_eq_sub]
private theorem isBlockTreeBond_translate (b : TorusBond (n * L)) (u : TorusSite n) :
    IsBlockTreeBond L ((b.1 + blockCentreSite L u, b.2) : TorusBond (n * L)) ↔ IsBlockTreeBond L b := by
  have e : b.1 + blockCentreSite L u + TorusFields.unitStep (n * L) b.2 =
      (b.1 + TorusFields.unitStep (n * L) b.2) + blockCentreSite L u :=
    add_right_comm _ _ _
  unfold IsBlockTreeBond CrossesBlockBoundary
  simp only [offsetFromCentre_add_blockCentreSite, e, coarseSite_add_blockCentreSite, ne_eq, add_left_inj]
private theorem pathIntegral_translate {m : ℕ} (ξ : RealOneForm m) (v x : TorusSite m) (l : List PathStep) :
    pathIntegral (fun b => ξ (b.1 + v, b.2)) x l = pathIntegral ξ (x + v) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : stepEndpoint (x + v) st = stepEndpoint x st + v := by
      unfold stepEndpoint
      split_ifs <;> abel
    simp only [pathIntegral, ih, e]
    split_ifs
    · rfl
    · rw [sub_add_eq_add_sub]
omit [NeZero L] in
private theorem contourAverage_translate (ξ : RealOneForm (n * L)) (c : TorusBond n) (u : TorusSite n) :
    _root_.YangMills.Construction.FlatLinearization.contourAverage L (fun b => ξ (b.1 + blockCentreSite L u, b.2)) c =
      _root_.YangMills.Construction.FlatLinearization.contourAverage L ξ (c.1 + u, c.2) := by
  simp only [FlatLinearization.contourAverage, pathIntegral_translate, blockCentreSite_add]
private theorem contourWeight_translate (c : TorusBond n) (b : TorusBond (n * L)) (u : TorusSite n) :
    contourWeight L ((c.1 + u, c.2) : TorusBond n) ((b.1 + blockCentreSite L u, b.2) : TorusBond (n * L)) =
      contourWeight L c b := by
  unfold contourWeight
  rw [← contourAverage_translate]
  have e : (fun b' : TorusBond (n * L) => indicatorForm ((b.1 + blockCentreSite L u, b.2) : TorusBond (n * L))
      (b'.1 + blockCentreSite L u, b'.2)) = indicatorForm b := by
    funext b'
    simp [indicatorForm, Prod.ext_iff]
  rw [e]
private def translateBond {m : ℕ} (v : TorusSite m) : TorusBond m ≃ TorusBond m :=
  (Equiv.addRight v).prodCongr (Equiv.refl _)
private theorem translate_ne {m : ℕ} (v : TorusSite m) {b c : TorusBond m} (h : ¬ b = c) :
    ¬ ((b.1 + v, b.2) : TorusBond m) = (c.1 + v, c.2) := fun e =>
  h (Prod.ext (by simpa using congrArg Prod.fst e) (by simpa using congrArg Prod.snd e))
private theorem flatStepOperator_translate (a : ℝ) (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (u : TorusSite n)
    (hK : ∀ b c : TorusBond (n * L),
      K (b.1 + blockCentreSite L u, b.2) (c.1 + blockCentreSite L u, c.2) = K b c)
    (b b' : TorusBond (n * L)) :
    flatStepOperator a L K (b.1 + blockCentreSite L u, b.2) (b'.1 + blockCentreSite L u, b'.2) =
      flatStepOperator a L K b b' := by
  classical
  have e : ∑ c : TorusBond n, contourWeight L c ((b.1 + blockCentreSite L u, b.2) : TorusBond (n * L)) *
        contourWeight L c ((b'.1 + blockCentreSite L u, b'.2) : TorusBond (n * L)) =
      ∑ c : TorusBond n, contourWeight L c b * contourWeight L c b' := by
    refine ((translateBond u).sum_comp _).symm.trans ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    show contourWeight L ((c.1 + u, c.2) : TorusBond n) _ * contourWeight L ((c.1 + u, c.2) : TorusBond n) _ = _
    rw [contourWeight_translate, contourWeight_translate]
  unfold flatStepOperator
  by_cases h1 : IsBlockTreeBond L b ∨ IsBlockTreeBond L b'
  · have h1' : IsBlockTreeBond L ((b.1 + blockCentreSite L u, b.2) : TorusBond (n * L)) ∨
        IsBlockTreeBond L ((b'.1 + blockCentreSite L u, b'.2) : TorusBond (n * L)) := by
      rwa [isBlockTreeBond_translate, isBlockTreeBond_translate]
    rw [if_pos h1, if_pos h1']
    by_cases h2 : b = b'
    · subst h2
      simp
    · rw [if_neg h2, if_neg (translate_ne _ h2)]
  · have h1' : ¬ (IsBlockTreeBond L ((b.1 + blockCentreSite L u, b.2) : TorusBond (n * L)) ∨
        IsBlockTreeBond L ((b'.1 + blockCentreSite L u, b'.2) : TorusBond (n * L))) := by
      rwa [isBlockTreeBond_translate, isBlockTreeBond_translate]
    rw [if_neg h1, if_neg h1', hK, e]
private theorem flatStepSource_translate (a : ℝ) (c : TorusBond n) (x : TorusBond (n * L)) (u : TorusSite n) :
    flatStepSource a L ((c.1 + u, c.2) : TorusBond n) ((x.1 + blockCentreSite L u, x.2) : TorusBond (n * L)) =
      flatStepSource a L c x := by
  unfold flatStepSource
  by_cases h : IsBlockTreeBond L x
  · rw [if_pos h, if_pos ((isBlockTreeBond_translate x u).mpr h)]
  · rw [if_neg h, if_neg (fun g => h ((isBlockTreeBond_translate x u).mp g)), contourWeight_translate]
private theorem inverse_translate_invariant {m : ℕ} [NeZero m] (T G : TorusBond m → TorusBond m → ℝ)
    (v : TorusSite m)
    (hT : ∀ b c : TorusBond m, T (b.1 + v, b.2) (c.1 + v, c.2) = T b c)
    (hR : ∀ b c, ∑ x, T b x * G x c = if b = c then 1 else 0)
    (hL : ∀ b c, ∑ x, G b x * T x c = if b = c then 1 else 0) (b c : TorusBond m) :
    G (b.1 + v, b.2) (c.1 + v, c.2) = G b c := by
  let D : TorusBond m → TorusBond m → ℝ := fun b c => G (b.1 + v, b.2) (c.1 + v, c.2)
  have hTD : ∀ b c, ∑ x, T b x * D x c = if b = c then 1 else 0 := by
    intro b c
    calc ∑ x, T b x * D x c
        = ∑ x, (fun y => T (b.1 + v, b.2) y * G y (c.1 + v, c.2)) (translateBond v x) :=
          Finset.sum_congr rfl fun x _ => by
            show _ = T (b.1 + v, b.2) (x.1 + v, x.2) * G (x.1 + v, x.2) (c.1 + v, c.2)
            rw [hT]
      _ = ∑ y, T (b.1 + v, b.2) y * G y (c.1 + v, c.2) :=
          (translateBond v).sum_comp fun y => T (b.1 + v, b.2) y * G y (c.1 + v, c.2)
      _ = if ((b.1 + v, b.2) : TorusBond m) = (c.1 + v, c.2) then 1 else 0 := hR _ _
      _ = if b = c then 1 else 0 := by
          by_cases h : b = c
          · subst h
            simp
          · rw [if_neg h, if_neg (translate_ne _ h)]
  show D b c = G b c
  calc D b c = ∑ y, (if b = y then 1 else 0) * D y c := by simp
    _ = ∑ y, (∑ x, G b x * T x y) * D y c := by simp only [hL]
    _ = ∑ x, G b x * ∑ y, T x y * D y c := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ x, G b x * (if x = c then 1 else 0) := by simp only [hTD]
    _ = G b c := by simp
end Translation
end GreenResponse
open GreenResponse in
theorem greenFamilyResponses_holds (hF : offTreeFormLowerBoundStatement)
    (hK : ContourWeightLocality) (hS : TendstoLatticeSumOfTorusSums) :
    GreenFamilyResponses := by
  intro a ha L hL h hl G Gl hc hlim hg
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  have : NeZero L := ⟨hL0⟩
  have hside : Filter.Tendsto (fun n : ℕ => n * L) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hL0))
      Filter.tendsto_id
  obtain ⟨C, hC0, hloc, -, hsame, htree⟩ := hK L hL
  obtain ⟨Cf, hCf0, hfloor⟩ := hF L hL
  obtain ⟨κ, hκ, hcurl⟩ := hc.curl_lower_bound
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < n := Filter.eventually_gt_atTop 0
  obtain ⟨M, θ, hθ, hdec⟩ := hg.exp_decay
  have hA : 0 ≤ a * C := (mul_pos ha hC0).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hloc, hside.eventually hc.symm, hg.right_inv, hfloor,
      hside.eventually hcurl] with n hl1 hsym hR hfl hcu
    intro _ _
    obtain ⟨hQ, -⟩ := hl1
    have e : responseOfInverse a L G n = fun b c => ∑ x, G n b x * flatStepSource a L c x := by
      funext b c
      exact responseOfInverse_eq a G b c
    rw [e]
    exact ⟨isMinimizerFamily_of_right_inv a _ (G n) hsym hQ fun b c => hR b c,
      isPositiveOnTreeGauge_of_lower_bounds ha hκ hCf0 _ (fun ξ => hcu ξ) fun ξ hξ => hfl ξ hξ⟩
  · refine ⟨|M| * (a * C) * Real.exp (2 * θ * ((5 * L : ℕ) : ℝ)) * (4 * expLatticeSum θ),
      θ, hθ, ?_⟩
    filter_upwards [hpos, hloc, hdec] with n hn hl1 hd b c
    have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨-, hk⟩ := hl1
    rw [responseOfInverse_eq]
    exact abs_sum_mul_local_le hθ hA b.1 (blockCentreSite L c.1) _ _ (fun x => hd b x)
      (fun x => abs_flatStepSource_le ha (hk c x).1)
      (fun x hx => flatStepSource_eq_zero ((hk c x).2 hx))
  · filter_upwards [hpos, hside.eventually hc.translation_invariant, hg.right_inv, hg.left_inv] with
      n hn htr hR hLf b c u
    have : NeZero n := ⟨hn.ne'⟩
    rw [responseOfInverse_eq, responseOfInverse_eq]
    have hT := fun b c =>
      flatStepOperator_translate a (h (n * L)) u (fun b c => htr (blockCentreSite L u) b c) b c
    have hGs := inverse_translate_invariant _ (G n) (blockCentreSite L u) hT (fun b c => hR b c)
      fun b c => hLf b c
    refine ((translateBond (blockCentreSite L u)).sum_comp _).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    show G n (b.1 + blockCentreSite L u, b.2) (x.1 + blockCentreSite L u, x.2) *
      flatStepSource a L ((c.1 + u, c.2) : TorusBond n)
        ((x.1 + blockCentreSite L u, x.2) : TorusBond (n * L)) = _
    rw [hGs, flatStepSource_translate]
  · intro b c
    refine (hS (fun n => n * L) (|M| * Real.exp (θ * (offsetNorm b.1 : ℝ)) * (a * C)) θ
      (fun n x => G n (bondFrom 0 b) x * flatStepSource a L (bondFrom 0 c) x)
      (fun x => Gl b x * latticeStepSource a L c x)
      (fun n => responseOfInverse a L G n (bondFrom 0 b) (bondFrom 0 c)) hside hθ ?_ ?_ ?_).2
    · filter_upwards [hpos, hloc, hdec] with n hn hl1 hd x
      have : NeZero n := ⟨hn.ne'⟩
      obtain ⟨-, hk⟩ := hl1
      exact abs_mul_le_of_origin hθ hA b x.1 (hd (bondFrom 0 b) x)
        (abs_flatStepSource_le ha (hk (bondFrom 0 c) x).1)
    · intro x
      have hsrc : Filter.Tendsto
          (fun n : ℕ => flatStepSource a L (bondFrom 0 c : TorusBond n) (bondFrom 0 x : TorusBond (n * L)))
          Filter.atTop (𝓝 (latticeStepSource a L c x)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hsame c x, htree x] with n e1 e2
        unfold flatStepSource latticeStepSource
        by_cases hx : IsLatticeTreeBond L x
        · rw [if_pos hx, if_pos (e2.mpr hx)]
        · rw [if_neg hx, if_neg (fun g => hx (e2.mp g)), e1]
      exact (hg.tendsto b x).mul hsrc
    · filter_upwards [hpos] with n hn _
      have : NeZero n := ⟨hn.ne'⟩
      exact responseOfInverse_eq a G _ _
end RunningCouplingSlope
end YangMills.Construction
end
