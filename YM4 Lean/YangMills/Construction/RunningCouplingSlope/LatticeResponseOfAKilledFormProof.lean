import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.LatticeResponseOfAKilledForm
import YangMills.Construction.RunningCouplingSlope.LimitOfAChainFormKillsClosedForms
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
open YangMills.Construction.FlatLinearization YangMills.Construction.LatticeFractionalIntegration
open YangMills.Construction.FlatPairing YangMills.Construction.SlopeCoefficient
namespace YangMills.Construction.RunningCouplingSlope
namespace AnnihilatedResponse
private theorem natAbs_coord_le_offsetNorm (a : Fin 4 → ℤ) (i : Fin 4) : (a i).natAbs ≤ offsetNorm a := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem offsetNorm_add_le' (a b : Fin 4 → ℤ) : offsetNorm (a + b) ≤ offsetNorm a + offsetNorm b := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNorm_add_le <;> assumption
private theorem offsetNorm_neg' (a : Fin 4 → ℤ) : offsetNorm (-a) = offsetNorm a := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
private theorem offsetNorm_zero' : offsetNorm (0 : Fin 4 → ℤ) = 0 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_zero <;> assumption
private theorem offsetNorm_basisVector_le (i : Fin 4) : offsetNorm (basisVector i) ≤ 1 := by apply _root_.YangMills.DeltaSharedProofs.p501726 <;> assumption
private theorem offsetNorm_stepDisplacement_le (st : PathStep) : offsetNorm (stepDisplacement st) ≤ 1 := by
  unfold FlatPairing.stepDisplacement
  split_ifs
  · exact offsetNorm_basisVector_le _
  · rw [offsetNorm_neg']
    exact offsetNorm_basisVector_le _
private theorem offsetNormReal_add_le (a b : Fin 4 → ℤ) :
    offsetNormReal (a + b) ≤ offsetNormReal a + offsetNormReal b := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNormReal_add_le <;> assumption
private theorem offsetNormReal_neg (a : Fin 4 → ℤ) : offsetNormReal (-a) = offsetNormReal a := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNormReal_neg <;> assumption
private theorem offsetNormReal_nonneg (a : Fin 4 → ℤ) : 0 ≤ offsetNormReal a := Nat.cast_nonneg _
private theorem offsetNormReal_sub_le (a b : Fin 4 → ℤ) :
    offsetNormReal (a - b) ≤ offsetNormReal a + offsetNormReal b := by
  have := offsetNormReal_add_le a (-b)
  rwa [offsetNormReal_neg, ← sub_eq_add_neg] at this
private theorem offsetNormReal_stepDisplacement_le (st : PathStep) : offsetNormReal (stepDisplacement st) ≤ 1 := by
  unfold offsetNormReal
  exact_mod_cast offsetNorm_stepDisplacement_le st
private theorem offsetNormReal_basisVector_le (i : Fin 4) : offsetNormReal (basisVector i) ≤ 1 := by
  unfold offsetNormReal
  exact_mod_cast offsetNorm_basisVector_le i
abbrev _root_.YangMills.DeltaSharedProofs.p502556 := @offsetNormReal_basisVector_le
private theorem hasSum_of_pointwise_eq {f g : LatticeBond → ℝ} {t : ℝ} (h : HasSum g t) (e : ∀ y, f y = g y) :
    HasSum f t := by
  rwa [funext e]
private theorem hasSum_indicator_mul (ξ : LatticeOneForm) (b : LatticeBond) :
    HasSum (fun y : LatticeBond => (if b = y then (1 : ℝ) else 0) * ξ y) (ξ b) := by
  have := hasSum_single (f := fun y : LatticeBond => (if b = y then (1 : ℝ) else 0) * ξ y) b
    (fun y hy => by simp [Ne.symm hy])
  simpa using this
private theorem hasSum_lineSum_indicator (ξ : LatticeOneForm) (l : List PathStep) (z : Fin 4 → ℤ) :
    HasSum (fun y : LatticeBond => latticeLineSum (fun b' => if b' = y then 1 else 0) z l * ξ y)
      (latticeLineSum ξ z l) := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    have key : HasSum (fun y : LatticeBond =>
        (if st.2 then (if (z, st.1) = y then (1 : ℝ) else 0)
          else - (if (z - basisVector st.1, st.1) = y then (1 : ℝ) else 0)) * ξ y)
        (if st.2 then ξ (z, st.1) else - ξ (z - basisVector st.1, st.1)) := by
      by_cases e : st.2 = true
      · simpa [e] using hasSum_indicator_mul ξ (z, st.1)
      · simpa [e] using (hasSum_indicator_mul ξ (z - basisVector st.1, st.1)).neg
    have := key.add (ih (z + stepDisplacement st))
    simp only [latticeLineSum]
    refine hasSum_of_pointwise_eq this fun y => ?_
    ring
private theorem hasSum_contourWeight_mul (L : ℕ) (ξ : LatticeOneForm) (c : LatticeBond) :
    HasSum (fun y => latticeContourWeight L c y * ξ y) (latticeContourAverage L ξ c) := by
  have h1 : HasSum (fun y : LatticeBond => ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      latticeLineSum (fun b' => if b' = y then 1 else 0) (blockCentreOnLattice L c.1)
        (bondContour L h π c.2) * ξ y)
      (∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        latticeLineSum ξ (blockCentreOnLattice L c.1) (bondContour L h π c.2)) :=
    hasSum_sum fun h _ => hasSum_sum fun π _ => hasSum_lineSum_indicator ξ _ _
  have h2 := h1.mul_left (1 / (24 * (L : ℝ) ^ 4))
  refine hasSum_of_pointwise_eq h2 fun y => ?_
  simp only [latticeContourWeight, latticeContourAverage, Finset.sum_mul, mul_assoc, Finset.mul_sum]
private theorem lineSum_indicator_eq_zero (y : LatticeBond) (l : List PathStep) (z : Fin 4 → ℤ)
    (h : l.length < offsetNorm (y.1 - z)) :
    latticeLineSum (fun b' => if b' = y then 1 else 0) z l = 0 := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    have len : r.length + 1 < offsetNorm (y.1 - z) := by simpa using h
    have n1 : (z, st.1) ≠ y := by
      intro e
      have : y.1 - z = 0 := by rw [← e]; simp
      rw [this, offsetNorm_zero'] at len
      omega
    have n2 : (z - basisVector st.1, st.1) ≠ y := by
      intro e
      have : y.1 - z = - basisVector st.1 := by rw [← e]; simp
      rw [this, offsetNorm_neg'] at len
      have := offsetNorm_basisVector_le st.1
      omega
    have t2 : r.length < offsetNorm (y.1 - (z + stepDisplacement st)) := by
      have e : y.1 - z = (y.1 - (z + stepDisplacement st)) + stepDisplacement st := by abel
      have h1 := offsetNorm_add_le' (y.1 - (z + stepDisplacement st)) (stepDisplacement st)
      rw [← e] at h1
      have := offsetNorm_stepDisplacement_le st
      omega
    simp only [latticeLineSum]
    rw [ih _ t2]
    by_cases e : st.2 = true <;> simp [e, n1, n2]
private theorem abs_lineSum_indicator_le (y : LatticeBond) (l : List PathStep) (z : Fin 4 → ℤ) :
    |latticeLineSum (fun b' => if b' = y then 1 else 0) z l| ≤ l.length := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    simp only [latticeLineSum, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine (abs_add_le _ _).trans ?_
    have hd : |(if st.2 then (if (z, st.1) = y then (1 : ℝ) else 0)
        else - (if (z - basisVector st.1, st.1) = y then (1 : ℝ) else 0))| ≤ 1 := by
      split_ifs <;> simp
    linarith [ih (z + stepDisplacement st)]
private theorem abs_lineSum_le_of_exp_growth {ξ : LatticeOneForm} {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hξ : ∀ b : LatticeBond, |ξ b| ≤ C * Real.exp (s * offsetNormReal b.1)) (l : List PathStep)
    (z : Fin 4 → ℤ) :
    |latticeLineSum ξ z l| ≤ l.length * (C * Real.exp (s * (offsetNormReal z + l.length))) := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    have hlen : (0 : ℝ) ≤ r.length := Nat.cast_nonneg _
    set E := C * Real.exp (s * (offsetNormReal z + ((r.length : ℝ) + 1))) with hE
    have mono : ∀ t : ℝ, t ≤ offsetNormReal z + ((r.length : ℝ) + 1) → C * Real.exp (s * t) ≤ E := by
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht hs)) hC
    have hd : |(if st.2 then ξ (z, st.1) else - ξ (z - basisVector st.1, st.1))| ≤ E := by
      split_ifs
      · exact (hξ _).trans (mono _ (by simp only []; linarith))
      · rw [abs_neg]
        refine (hξ _).trans (mono _ ?_)
        have := offsetNormReal_sub_le z (basisVector st.1)
        have := offsetNormReal_basisVector_le st.1
        simp only []
        linarith
    have ht : |latticeLineSum ξ (z + stepDisplacement st) r| ≤ r.length * E := by
      refine (ih _).trans (mul_le_mul_of_nonneg_left (mono _ ?_) hlen)
      have := offsetNormReal_add_le z (stepDisplacement st)
      have := offsetNormReal_stepDisplacement_le st
      linarith
    simp only [latticeLineSum, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine (abs_add_le _ _).trans ?_
    nlinarith
private def contourMass (L : ℕ) : ℝ :=
  (1 / (24 * (L : ℝ) ^ 4)) * ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ)
private theorem contourMass_nonneg (L : ℕ) : 0 ≤ contourMass L := by
  unfold contourMass
  have : (0 : ℝ) ≤ ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one
  positivity
private theorem abs_contourAverage_le (L : ℕ) (ξ : LatticeOneForm) (c : LatticeBond) (A : ℝ)
    (hf : ∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
      |latticeLineSum ξ (blockCentreOnLattice L c.1) (bondContour L h π c.2)| ≤ A) :
    |latticeContourAverage L ξ c| ≤ contourMass L * A := by
  unfold latticeContourAverage contourMass
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        latticeLineSum ξ (blockCentreOnLattice L c.1) (bondContour L h π c.2)|
      ≤ ∑ h ∈ centredCube L, |∑ π : Equiv.Perm (Fin 4),
        latticeLineSum ξ (blockCentreOnLattice L c.1) (bondContour L h π c.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        |latticeLineSum ξ (blockCentreOnLattice L c.1) (bondContour L h π c.2)| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), A :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun π _ => hf h hh π
    _ = (∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ)) * A := by
        simp only [Finset.sum_mul, one_mul]
private theorem exists_bondContour_length_le (L : ℕ) :
    ∃ R : ℕ, ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4),
      (bondContour L h π i).length ≤ R :=
  ⟨(centredCube L ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4) × Fin 4))).sup
      fun p => (bondContour L p.1 p.2.1 p.2.2).length,
    fun h hh π i => Finset.le_sup (f := fun p : (Fin 4 → ℤ) × Equiv.Perm (Fin 4) × Fin 4 =>
      (bondContour L p.1 p.2.1 p.2.2).length) (b := (h, π, i))
      (Finset.mem_product.2 ⟨hh, Finset.mem_univ (π, i)⟩)⟩
private theorem contourWeight_eq_zero_of_far {L R : ℕ}
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    (c y : LatticeBond) (h : R < offsetNorm (y.1 - blockCentreOnLattice L c.1)) :
    latticeContourWeight L c y = 0 := by
  unfold latticeContourWeight latticeContourAverage
  rw [Finset.sum_eq_zero, mul_zero]
  intro k hk
  exact Finset.sum_eq_zero fun π _ => lineSum_indicator_eq_zero y _ _ (lt_of_le_of_lt (hR k hk π c.2) h)
private theorem abs_contourWeight_le {L R : ℕ}
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    (c y : LatticeBond) : |latticeContourWeight L c y| ≤ contourMass L * R := by
  refine abs_contourAverage_le L _ c _ fun k hk π => (abs_lineSum_indicator_le y _ _).trans ?_
  exact_mod_cast hR k hk π c.2
private def integerBox (N : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
private def nearbyCoarseBonds (L N : ℕ) (x : Fin 4 → ℤ) : Finset LatticeBond :=
  (integerBox N ×ˢ (Finset.univ : Finset (Fin 4))).image fun p => ((fun i => x i / (L : ℤ) + p.1 i), p.2)
private theorem card_nearbyCoarseBonds_le (L N : ℕ) (x : Fin 4 → ℤ) :
    (nearbyCoarseBonds L N x).card ≤ (integerBox N).card * 4 := by
  unfold nearbyCoarseBonds
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_product]
private theorem mem_nearbyCoarseBonds {L R : ℕ} (hL : 0 < L) {x : Fin 4 → ℤ} {c : LatticeBond}
    (h : offsetNorm (x - blockCentreOnLattice L c.1) ≤ R) : c ∈ nearbyCoarseBonds L (R + L) x := by
  refine Finset.mem_image.2 ⟨(fun i => c.1 i - x i / (L : ℤ), c.2),
    Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, Prod.ext (funext fun i => by simp) rfl⟩
  refine Fintype.mem_piFinset.2 fun i => ?_
  have h1 : ((x - blockCentreOnLattice L c.1) i).natAbs ≤ R := (natAbs_coord_le_offsetNorm _ i).trans h
  have h2 : (x - blockCentreOnLattice L c.1) i = x i - (L : ℤ) * c.1 i := rfl
  rw [h2] at h1
  have h1' : |x i - (L : ℤ) * c.1 i| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  obtain ⟨h3, h4⟩ := abs_le.1 h1'
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hdiv := Int.mul_ediv_add_emod (x i) (L : ℤ)
  have hm0 := Int.emod_nonneg (x i) hLz.ne'
  have hm1 := Int.emod_lt_of_pos (x i) hLz
  set q := x i / (L : ℤ)
  set m := x i % (L : ℤ)
  set u := c.1 i
  rw [Finset.mem_Icc]
  push_cast
  constructor
  · by_contra hc
    have hc' : (R : ℤ) + L < q - u := by linarith
    have : 0 ≤ ((L : ℤ) - 1) * (q - u) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · by_contra hc
    have hc' : (R : ℤ) + L < u - q := by linarith
    have : 0 ≤ ((L : ℤ) - 1) * (u - q) := mul_nonneg (by linarith) (by linarith)
    nlinarith
private theorem offsetNorm_le_of_contourWeight_ne_zero {L R : ℕ}
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    {c x : LatticeBond} (h : latticeContourWeight L c x ≠ 0) :
    offsetNorm (x.1 - blockCentreOnLattice L c.1) ≤ R :=
  not_lt.1 fun e => h (contourWeight_eq_zero_of_far hR c x e)
private theorem contourWeight_eq_zero_of_not_mem {L R : ℕ} (hL : 0 < L)
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    {c x : LatticeBond} (h : c ∉ nearbyCoarseBonds L (R + L) x.1) : latticeContourWeight L c x = 0 := by
  by_contra e
  exact h (mem_nearbyCoarseBonds hL (offsetNorm_le_of_contourWeight_ne_zero hR e))
private theorem stepOperator_exp_decay {a : ℝ} (ha : 0 < a) {L R : ℕ} (hL : 0 < L)
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    {hl : LatticeBond → LatticeBond → ℝ} {M θ : ℝ} (hθ : 0 < θ)
    (hd : ∀ b c : LatticeBond, |hl b c| ≤ M * Real.exp (-(θ * offsetNormReal (b.1 - c.1)))) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ x y : LatticeBond,
      |latticeStepOperator a L hl x y| ≤ M₁ * Real.exp (-(θ * offsetNormReal (x.1 - y.1))) := by
  set K : ℝ := contourMass L * R with hK
  have hK0 : 0 ≤ K := mul_nonneg (contourMass_nonneg L) (Nat.cast_nonneg _)
  set W : ℝ := K * K * Real.exp (θ * (2 * R)) with hW
  have hW0 : 0 ≤ W := by positivity
  set Nn : ℝ := (((integerBox (R + L)).card * 4 : ℕ) : ℝ) with hNn
  refine ⟨1 + |M| + a * (Nn * W), by positivity, fun x y => ?_⟩
  set E := Real.exp (-(θ * offsetNormReal (x.1 - y.1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hM : M * E ≤ |M| * E := mul_le_mul_of_nonneg_right (le_abs_self _) hE0.le
  have term : ∀ c : LatticeBond, |latticeContourWeight L c x * latticeContourWeight L c y| ≤ W * E := by
    intro c
    by_cases h1 : latticeContourWeight L c x = 0
    · simp [h1]
      positivity
    by_cases h2 : latticeContourWeight L c y = 0
    · simp [h2]
      positivity
    have s1 : offsetNormReal (x.1 - blockCentreOnLattice L c.1) ≤ R := by
      unfold offsetNormReal
      exact_mod_cast offsetNorm_le_of_contourWeight_ne_zero hR h1
    have s2 : offsetNormReal (y.1 - blockCentreOnLattice L c.1) ≤ R := by
      unfold offsetNormReal
      exact_mod_cast offsetNorm_le_of_contourWeight_ne_zero hR h2
    have s3 : offsetNormReal (x.1 - y.1) ≤ 2 * R := by
      have e : x.1 - y.1 = (x.1 - blockCentreOnLattice L c.1) - (y.1 - blockCentreOnLattice L c.1) := by abel
      have := offsetNormReal_sub_le (x.1 - blockCentreOnLattice L c.1) (y.1 - blockCentreOnLattice L c.1)
      rw [← e] at this
      linarith
    have s4 : 1 ≤ Real.exp (θ * (2 * R)) * E := by
      rw [hE, ← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    rw [abs_mul]
    have k1 := abs_contourWeight_le hR c x
    have k2 := abs_contourWeight_le hR c y
    calc |latticeContourWeight L c x| * |latticeContourWeight L c y| ≤ K * K :=
          mul_le_mul k1 k2 (abs_nonneg _) hK0
      _ ≤ K * K * (Real.exp (θ * (2 * R)) * E) := le_mul_of_one_le_right (by positivity) s4
      _ = W * E := by rw [hW]; ring
  have hq : |∑' c : LatticeBond, latticeContourWeight L c x * latticeContourWeight L c y| ≤ Nn * W * E := by
    rw [tsum_eq_sum (s := nearbyCoarseBonds L (R + L) x.1)
      (fun c hc => by rw [contourWeight_eq_zero_of_not_mem hL hR hc, zero_mul])]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun c _ => term c).trans ?_
    rw [nsmul_eq_mul, show Nn * W * E = Nn * (W * E) from mul_assoc _ _ _]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hW0 hE0.le)
    rw [hNn]
    exact_mod_cast card_nearbyCoarseBonds_le L (R + L) x.1
  unfold latticeStepOperator
  split_ifs with ht he
  · subst he
    have e0 : offsetNormReal (x.1 - x.1) = 0 := by simp [offsetNormReal, offsetNorm_zero']
    have : E = 1 := by rw [hE, e0]; simp
    rw [this]
    have : 0 ≤ a * (Nn * W) := by positivity
    have := abs_nonneg M
    simp only [abs_one, mul_one]
    linarith
  · simp only [abs_zero]
    positivity
  · have h1 := hd x y
    have h2 : |a * ∑' c : LatticeBond, latticeContourWeight L c x * latticeContourWeight L c y| ≤
        a * (Nn * W * E) := by
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left hq ha.le
    refine (abs_add_le _ _).trans ?_
    have : (1 + |M| + a * (Nn * W)) * E = E + |M| * E + a * (Nn * W * E) := by ring
    rw [this]
    linarith
private theorem le_exp_of_polynomialGrowth {w : LatticeOneForm} (hw : HasPolynomialGrowth w) {s : ℝ}
    (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : LatticeBond, |w b| ≤ C * Real.exp (s * offsetNormReal b.1) := by
  obtain ⟨C, m, h⟩ := hw
  set p : ℝ := max m 1 with hp
  have hp0 : 0 < p := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε : ℝ := min 1 (s / p) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεp : ε * p ≤ s := (le_div_iff₀ hp0).1 (min_le_right _ _)
  refine ⟨|C| * ε⁻¹ ^ p, by positivity, fun b => (h b).trans ?_⟩
  set t := offsetNormReal b.1 with htd
  have ht : 0 ≤ t := offsetNormReal_nonneg _
  have h1 : 1 + t ≤ ε⁻¹ * Real.exp (ε * t) := by
    have := Real.add_one_le_exp (ε * t)
    rw [inv_mul_eq_div, le_div_iff₀ hε0]
    nlinarith
  have h1t : 0 ≤ 1 + t := by linarith
  have h2 : (1 + t) ^ m ≤ (1 + t) ^ p :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have h3 : (1 + t) ^ p ≤ (ε⁻¹ * Real.exp (ε * t)) ^ p := Real.rpow_le_rpow h1t h1 hp0.le
  have h4 : (ε⁻¹ * Real.exp (ε * t)) ^ p = ε⁻¹ ^ p * Real.exp (ε * t * p) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  have h5 : Real.exp (ε * t * p) ≤ Real.exp (s * t) := Real.exp_le_exp.2 (by nlinarith)
  calc C * (1 + t) ^ m ≤ |C| * (1 + t) ^ m :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg h1t _)
    _ ≤ |C| * (ε⁻¹ ^ p * Real.exp (s * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine h2.trans (h3.trans ?_)
        rw [h4]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring
private theorem summable_exp_neg_offsetNormReal {r : ℝ} (hr : 0 < r) :
    Summable fun z : Fin 4 → ℤ => Real.exp (-(r * offsetNormReal z)) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.summable_exp_neg_offsetNormReal <;> assumption
private theorem summable_bond_exp_neg {r : ℝ} (hr : 0 < r) :
    Summable fun p : LatticeBond => Real.exp (-(r * offsetNormReal p.1)) := by
  have := (summable_exp_neg_offsetNormReal hr).mul_of_nonneg
    (hasSum_fintype fun _ : Fin 4 => (1 : ℝ)).summable
    (fun _ => (Real.exp_pos _).le) (fun _ => zero_le_one)
  simpa using this
private theorem summable_bond_exp_neg_sub {r : ℝ} (hr : 0 < r) (u : Fin 4 → ℤ) :
    Summable fun x : LatticeBond => Real.exp (-(r * offsetNormReal (u - x.1))) := by
  have hinj : Function.Injective fun x : LatticeBond => ((u - x.1, x.2) : LatticeBond) := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    rw [sub_right_inj.1 e1, e2]
  have hs := (summable_bond_exp_neg hr).comp_injective hinj
  exact hs
private theorem summable_pair_exp_neg {r : ℝ} (hr : 0 < r) (u : Fin 4 → ℤ) :
    Summable fun p : LatticeBond × LatticeBond =>
      Real.exp (-(r * offsetNormReal (u - p.1.1))) * Real.exp (-(r * offsetNormReal (p.1.1 - p.2.1))) := by
  have hb := summable_bond_exp_neg hr
  have hprod := hb.mul_of_nonneg hb (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hinj : Function.Injective fun p : LatticeBond × LatticeBond =>
      (((u - p.1.1, p.1.2), (p.1.1 - p.2.1, p.2.2)) : LatticeBond × LatticeBond) := by
    rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ ⟨⟨x1', x2'⟩, ⟨y1', y2'⟩⟩ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := e
    have f1 := sub_right_inj.1 e1
    subst f1
    have f2 := sub_right_inj.1 e3
    subst f2
    subst e2
    subst e4
    rfl
  have hs := hprod.comp_injective hinj
  exact hs
private theorem hasSum_stepOperator_row {a : ℝ} {L R : ℕ} (hL : 0 < L)
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    {hl : LatticeBond → LatticeBond → ℝ} {w : LatticeOneForm} (hoff : VanishesOnLatticeTrees L w)
    (hk : ∀ b, HasSum (fun c => hl b c * w c) 0) (x : LatticeBond) :
    HasSum (fun y => latticeStepOperator a L hl x y * w y)
      (∑' c, latticeStepSource a L c x * latticeContourAverage L w c) := by
  by_cases hx : IsLatticeTreeBond L x
  · have e1 : ∀ c, latticeStepSource a L c x = 0 := fun c => by simp [latticeStepSource, hx]
    have e2 : ∀ y, latticeStepOperator a L hl x y * w y = 0 := by
      intro y
      unfold latticeStepOperator
      rw [if_pos (Or.inl hx)]
      split_ifs with e
      · subst e
        simp [hoff _ hx]
      · simp
    simp only [e1, e2, zero_mul, tsum_zero]
    exact hasSum_zero
  · set F := nearbyCoarseBonds L (R + L) x.1 with hFd
    have hF : ∀ c, c ∉ F → latticeContourWeight L c x = 0 := fun c hc =>
      contourWeight_eq_zero_of_not_mem hL hR hc
    have e1 : ∑' c, latticeStepSource a L c x * latticeContourAverage L w c =
        a * ∑ c ∈ F, latticeContourWeight L c x * latticeContourAverage L w c := by
      rw [tsum_eq_sum (s := F) (fun c hc => by simp [latticeStepSource, hx, hF c hc]), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [latticeStepSource, if_neg hx]
      ring
    have e2 : ∀ y, latticeStepOperator a L hl x y * w y =
        hl x y * w y + a * ∑ c ∈ F, latticeContourWeight L c x * (latticeContourWeight L c y * w y) := by
      intro y
      by_cases hy : IsLatticeTreeBond L y
      · have hne : x ≠ y := fun e => hx (e ▸ hy)
        simp [hoff y hy]
      · have e3 : ∑' c, latticeContourWeight L c x * latticeContourWeight L c y =
            ∑ c ∈ F, latticeContourWeight L c x * latticeContourWeight L c y :=
          tsum_eq_sum (fun c hc => by simp [hF c hc])
        simp only [latticeStepOperator, if_neg (not_or.2 ⟨hx, hy⟩)]
        rw [e3, add_mul, mul_assoc a, Finset.sum_mul]
        simp only [mul_assoc]
    rw [e1]
    have h := (hk x).add ((hasSum_sum (s := F) fun c _ =>
      (hasSum_contourWeight_mul L w c).mul_left (latticeContourWeight L c x)).mul_left a)
    rw [zero_add] at h
    exact hasSum_of_pointwise_eq h e2
private theorem abs_stepSource_mul_average_le {a : ℝ} (ha : 0 < a) {L R : ℕ}
    (hR : ∀ h ∈ centredCube L, ∀ (π : Equiv.Perm (Fin 4)) (i : Fin 4), (bondContour L h π i).length ≤ R)
    {w : LatticeOneForm} {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hw : ∀ b : LatticeBond, |w b| ≤ C * Real.exp (s * offsetNormReal b.1)) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ c x : LatticeBond,
      |latticeStepSource a L c x * latticeContourAverage L w c| ≤ P * Real.exp (s * offsetNormReal x.1) := by
  have hW := contourMass_nonneg L
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  refine ⟨a * (contourMass L * R) * (contourMass L * (R * (C * Real.exp (s * (2 * R))))),
    by positivity, fun c x => ?_⟩
  by_cases hz : latticeContourWeight L c x = 0
  · have : latticeStepSource a L c x = 0 := by simp [latticeStepSource, hz]
    rw [this, zero_mul, abs_zero]
    positivity
  have s1 : offsetNormReal (x.1 - blockCentreOnLattice L c.1) ≤ R := by
    unfold offsetNormReal
    exact_mod_cast offsetNorm_le_of_contourWeight_ne_zero hR hz
  have s2 : offsetNormReal (blockCentreOnLattice L c.1) ≤ offsetNormReal x.1 + R := by
    have e : blockCentreOnLattice L c.1 = x.1 - (x.1 - blockCentreOnLattice L c.1) := by abel
    have := offsetNormReal_sub_le x.1 (x.1 - blockCentreOnLattice L c.1)
    rw [← e] at this
    linarith
  have hsrc : |latticeStepSource a L c x| ≤ a * (contourMass L * R) := by
    unfold latticeStepSource
    split_ifs
    · simp only [abs_zero]
      positivity
    · rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left (abs_contourWeight_le hR c x) ha.le
  have hB : |latticeContourAverage L w c| ≤
      contourMass L * (R * (C * Real.exp (s * (2 * R))) * Real.exp (s * offsetNormReal x.1)) := by
    refine abs_contourAverage_le L w c _ fun k hk π => (abs_lineSum_le_of_exp_growth hC hs hw _ _).trans ?_
    have hlen : ((bondContour L k π c.2).length : ℝ) ≤ R := by exact_mod_cast hR k hk π c.2
    have hlen0 : (0 : ℝ) ≤ (bondContour L k π c.2).length := Nat.cast_nonneg _
    have he : Real.exp (s * (offsetNormReal (blockCentreOnLattice L c.1) +
          (bondContour L k π c.2).length)) ≤
        Real.exp (s * (2 * R)) * Real.exp (s * offsetNormReal x.1) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    calc ((bondContour L k π c.2).length : ℝ) *
          (C * Real.exp (s * (offsetNormReal (blockCentreOnLattice L c.1) +
            (bondContour L k π c.2).length)))
        ≤ R * (C * (Real.exp (s * (2 * R)) * Real.exp (s * offsetNormReal x.1))) :=
          mul_le_mul hlen (mul_le_mul_of_nonneg_left he hC) (by positivity) hR0
      _ = _ := by ring
  rw [abs_mul]
  calc |latticeStepSource a L c x| * |latticeContourAverage L w c|
      ≤ a * (contourMass L * R) *
        (contourMass L * (R * (C * Real.exp (s * (2 * R))) * Real.exp (s * offsetNormReal x.1))) :=
        mul_le_mul hsrc hB (abs_nonneg _) (by positivity)
    _ = _ := by ring
private theorem hasSum_response_mul_average {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : 0 < L)
    {hl Gl : LatticeBond → LatticeBond → ℝ} {w : LatticeOneForm} (hw : HasPolynomialGrowth w)
    (hoff : VanishesOnLatticeTrees L w) (hk : ∀ b, HasSum (fun c => hl b c * w c) 0)
    {M₀ θ₀ M₁ θ₁ : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁)
    (hG : ∀ b c : LatticeBond, |Gl b c| ≤ M₀ * Real.exp (-(θ₀ * offsetNormReal (b.1 - c.1))))
    (hh : ∀ b c : LatticeBond, |hl b c| ≤ M₁ * Real.exp (-(θ₁ * offsetNormReal (b.1 - c.1))))
    (hinv : ∀ b c : LatticeBond,
      HasSum (fun x => Gl b x * latticeStepOperator a L hl x c) (if b = c then 1 else 0))
    (b : LatticeBond) :
    HasSum (fun c => latticeResponseOfInverse a L Gl b c * latticeContourAverage L w c) (w b) := by
  obtain ⟨R, hR⟩ := exists_bondContour_length_le L
  set s : ℝ := min θ₀ θ₁ / 2 with hsd
  have hs : 0 < s := by have := lt_min hθ₀ hθ₁; positivity
  have h20 : 2 * s ≤ θ₀ := by have := min_le_left θ₀ θ₁; linarith
  have h21 : 2 * s ≤ θ₁ := by have := min_le_right θ₀ θ₁; linarith
  obtain ⟨C, hC, hwe⟩ := le_exp_of_polynomialGrowth hw hs
  obtain ⟨M₂, hM₂, hT⟩ := stepOperator_exp_decay ha hL hR hθ₁ hh
  obtain ⟨P, hP, hS⟩ := abs_stepSource_mul_average_le ha hR hC hs.le hwe
  have hG' : ∀ x : LatticeBond, |Gl b x| ≤ |M₀| * Real.exp (-(2 * s * offsetNormReal (b.1 - x.1))) := by
    intro x
    refine (hG b x).trans ?_
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
    have := offsetNormReal_nonneg (b.1 - x.1)
    nlinarith
  have hT' : ∀ x y : LatticeBond, |latticeStepOperator a L hl x y| ≤
      M₂ * Real.exp (-(2 * s * offsetNormReal (x.1 - y.1))) := by
    intro x y
    refine (hT x y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM₂)
    have := offsetNormReal_nonneg (x.1 - y.1)
    nlinarith
  set S : LatticeBond → ℝ := fun x => ∑' c, latticeStepSource a L c x * latticeContourAverage L w c with hSd
  have hA : Summable fun p : LatticeBond × LatticeBond =>
      Gl b p.1 * latticeStepOperator a L hl p.1 p.2 * w p.2 := by
    refine Summable.of_norm_bounded
      ((summable_pair_exp_neg hs b.1).mul_left (|M₀| * M₂ * C * Real.exp (s * offsetNormReal b.1))) ?_
    rintro ⟨x, y⟩
    simp only [Real.norm_eq_abs]
    set d₁ := offsetNormReal (b.1 - x.1) with hd₁
    set d₂ := offsetNormReal (x.1 - y.1) with hd₂
    have g3 : |w y| ≤ C * Real.exp (s * (offsetNormReal b.1 + d₁ + d₂)) := by
      refine (hwe y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
      have e : y.1 = b.1 - (b.1 - x.1) - (x.1 - y.1) := by abel
      have n1 := offsetNormReal_sub_le (b.1 - (b.1 - x.1)) (x.1 - y.1)
      have n2 := offsetNormReal_sub_le b.1 (b.1 - x.1)
      rw [← e] at n1
      exact mul_le_mul_of_nonneg_left (by linarith) hs.le
    rw [abs_mul, abs_mul]
    calc |Gl b x| * |latticeStepOperator a L hl x y| * |w y|
        ≤ (|M₀| * Real.exp (-(2 * s * d₁))) * (M₂ * Real.exp (-(2 * s * d₂))) *
            (C * Real.exp (s * (offsetNormReal b.1 + d₁ + d₂))) :=
          mul_le_mul (mul_le_mul (hG' x) (hT' x y) (abs_nonneg _) (by positivity)) g3
            (abs_nonneg _) (by positivity)
      _ = |M₀| * M₂ * C * Real.exp (s * offsetNormReal b.1) *
            (Real.exp (-(s * d₁)) * Real.exp (-(s * d₂))) := by
          have e : -(2 * s * d₁) + -(2 * s * d₂) + s * (offsetNormReal b.1 + d₁ + d₂) =
              s * offsetNormReal b.1 + (-(s * d₁) + -(s * d₂)) := by ring
          have e' := congrArg Real.exp e
          simp only [Real.exp_add] at e'
          calc _ = |M₀| * M₂ * C * (Real.exp (-(2 * s * d₁)) * Real.exp (-(2 * s * d₂)) *
                (Real.exp (s * offsetNormReal b.1) * Real.exp (s * d₁) * Real.exp (s * d₂))) := by
                simp only [mul_add, Real.exp_add]
                ring
            _ = _ := by
                have e'' : Real.exp (-(2 * s * d₁)) * Real.exp (-(2 * s * d₂)) *
                    (Real.exp (s * offsetNormReal b.1) * Real.exp (s * d₁) * Real.exp (s * d₂)) =
                    Real.exp (s * offsetNormReal b.1) * (Real.exp (-(s * d₁)) * Real.exp (-(s * d₂))) := by
                  simpa only [mul_add, Real.exp_add] using e'
                rw [e'']
                ring
  have hrow : ∀ x, HasSum (fun y => Gl b x * latticeStepOperator a L hl x y * w y) (Gl b x * S x) := by
    intro x
    have := (hasSum_stepOperator_row (a := a) hL hR hoff hk x).mul_left (Gl b x)
    exact hasSum_of_pointwise_eq this fun y => by ring
  have hcol : ∀ y, HasSum (fun x => Gl b x * latticeStepOperator a L hl x y * w y)
      ((if b = y then (1 : ℝ) else 0) * w y) := fun y => (hinv b y).mul_right (w y)
  have a1 : HasSum (fun x => Gl b x * S x) (∑' p : LatticeBond × LatticeBond,
      Gl b p.1 * latticeStepOperator a L hl p.1 p.2 * w p.2) := hA.hasSum.prod_fiberwise hrow
  have a2 : HasSum (fun y => (if b = y then (1 : ℝ) else 0) * w y)
      (∑' p : LatticeBond × LatticeBond, Gl b p.1 * latticeStepOperator a L hl p.1 p.2 * w p.2) :=
    ((Equiv.prodComm LatticeBond LatticeBond).hasSum_iff.2 hA.hasSum).prod_fiberwise hcol
  have a3 := a2.unique (hasSum_indicator_mul w b)
  rw [a3] at a1
  have hD : Summable fun p : LatticeBond × LatticeBond =>
      Gl b p.1 * (latticeStepSource a L p.2 p.1 * latticeContourAverage L w p.2) := by
    refine Summable.of_norm ?_
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    have hsrc0 : ∀ (x c : LatticeBond), c ∉ nearbyCoarseBonds L (R + L) x.1 →
        latticeStepSource a L c x = 0 := by
      intro x c hc
      simp [latticeStepSource, contourWeight_eq_zero_of_not_mem hL hR hc]
    refine ⟨fun x => ?_, ?_⟩
    · refine summable_of_ne_finset_zero (s := nearbyCoarseBonds L (R + L) x.1) fun c hc => ?_
      simp [hsrc0 x c hc]
    · set Nn : ℝ := (((integerBox (R + L)).card * 4 : ℕ) : ℝ) with hNn
      refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun x => ?_)
        ((summable_bond_exp_neg_sub hs b.1).mul_left (Nn * (|M₀| * P * Real.exp (s * offsetNormReal b.1))))
      set d := offsetNormReal (b.1 - x.1) with hd
      have hxb : offsetNormReal x.1 ≤ offsetNormReal b.1 + d := by
        have e : x.1 = b.1 - (b.1 - x.1) := by abel
        have := offsetNormReal_sub_le b.1 (b.1 - x.1)
        rw [← e] at this
        exact this
      have term : ∀ c : LatticeBond,
          ‖Gl b x * (latticeStepSource a L c x * latticeContourAverage L w c)‖ ≤
          |M₀| * P * Real.exp (s * offsetNormReal b.1) * Real.exp (-(s * d)) := by
        intro c
        rw [Real.norm_eq_abs, abs_mul]
        have he : Real.exp (-(2 * s * d)) * Real.exp (s * offsetNormReal x.1) ≤
            Real.exp (s * offsetNormReal b.1) * Real.exp (-(s * d)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          nlinarith
        calc |Gl b x| * |latticeStepSource a L c x * latticeContourAverage L w c|
            ≤ (|M₀| * Real.exp (-(2 * s * d))) * (P * Real.exp (s * offsetNormReal x.1)) :=
              mul_le_mul (hG' x) (hS c x) (abs_nonneg _) (by positivity)
          _ = |M₀| * P * (Real.exp (-(2 * s * d)) * Real.exp (s * offsetNormReal x.1)) := by ring
          _ ≤ |M₀| * P * (Real.exp (s * offsetNormReal b.1) * Real.exp (-(s * d))) :=
              mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
      simp only []
      rw [tsum_eq_sum (s := nearbyCoarseBonds L (R + L) x.1) (fun c hc => by simp [hsrc0 x c hc])]
      refine (Finset.sum_le_card_nsmul _ _ _ fun c _ => term c).trans ?_
      rw [nsmul_eq_mul]
      have hc : ((nearbyCoarseBonds L (R + L) x.1).card : ℝ) ≤ Nn := by
        rw [hNn]
        exact_mod_cast card_nearbyCoarseBonds_le L (R + L) x.1
      calc ((nearbyCoarseBonds L (R + L) x.1).card : ℝ) *
            (|M₀| * P * Real.exp (s * offsetNormReal b.1) * Real.exp (-(s * d)))
          ≤ Nn * (|M₀| * P * Real.exp (s * offsetNormReal b.1) * Real.exp (-(s * d))) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring
  have rowD : ∀ x, HasSum (fun c => Gl b x * (latticeStepSource a L c x * latticeContourAverage L w c))
      (Gl b x * S x) := by
    intro x
    have := (hD.prod_factor x).hasSum
    simp only [tsum_mul_left] at this
    exact this
  have colD : ∀ c, HasSum (fun x => Gl b x * (latticeStepSource a L c x * latticeContourAverage L w c))
      (latticeResponseOfInverse a L Gl b c * latticeContourAverage L w c) := by
    intro c
    have := (hD.prod_symm.prod_factor c).hasSum
    simp only [Prod.swap_prod_mk] at this
    have e : ∑' x, Gl b x * (latticeStepSource a L c x * latticeContourAverage L w c) =
        latticeResponseOfInverse a L Gl b c * latticeContourAverage L w c := by
      unfold latticeResponseOfInverse
      rw [← tsum_mul_right]
      exact tsum_congr fun x => by ring
    rwa [e] at this
  have a4 : HasSum (fun x => Gl b x * S x) (∑' p : LatticeBond × LatticeBond,
      Gl b p.1 * (latticeStepSource a L p.2 p.1 * latticeContourAverage L w p.2)) :=
    hD.hasSum.prod_fiberwise rowD
  have a5 := a4.unique a1
  have a6 : HasSum (fun c => latticeResponseOfInverse a L Gl b c * latticeContourAverage L w c)
      (∑' p : LatticeBond × LatticeBond,
        Gl b p.1 * (latticeStepSource a L p.2 p.1 * latticeContourAverage L w p.2)) :=
    ((Equiv.prodComm LatticeBond LatticeBond).hasSum_iff.2 hD.hasSum).prod_fiberwise colD
  rwa [a5] at a6
end AnnihilatedResponse
open AnnihilatedResponse in
theorem latticeResponseOfAnnihilated_holds (hC : flowKernelLimitAnnihilatesClosedStatement) :
    latticeResponseOfAnnihilatedStatement := by
  intro a ha L hL h hl G Gl hc hlim hg w hw hoff hk b
  obtain ⟨⟨M₁, θ₁, hθ₁, hd⟩, -⟩ := hC h hl hc hlim
  obtain ⟨M₀, θ₀, hθ₀, hGd⟩ := hg.lattice_exp_decay
  have hL0 : 0 < L := by
    have := hL.2
    omega
  exact hasSum_response_mul_average ha hL0 hw hoff hk hθ₀ hθ₁ hGd hd hg.lattice_hasSum_inv b
end YangMills.Construction.RunningCouplingSlope
end
