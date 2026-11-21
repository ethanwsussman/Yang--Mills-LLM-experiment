import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.LinearisedAverageOfAOneFormUnderIsometriesProof
import YangMills.Construction.Lattice.ReversalOfTheAveragingAtABond
import YangMills.Construction.Lattice.SchemeObjectsNearTheIdentityProof
import YangMills.Construction.Matrices.UnitaryLogConjugation
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicLattice.OppositeBond
variable {L m : ℕ} {j : ℤ}
theorem su_isUnit_det {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) :
    IsUnit A.det := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.det_isUnit_of_mem_specialUnitary <;> assumption
theorem su_isUnit {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).2 (su_isUnit_det h)
theorem su_inv_inv {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹⁻¹ = A := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem su_inv_mul {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
theorem su_mul_inv {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) : A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p21267 <;> assumption
theorem su_inv_mem {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) :
    A⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem inv_conj_fourFactors {A B C T : ComplexMatrix2} (hC : C ∈ ComplexMatrix2.specialUnitary)
    (hT : T ∈ ComplexMatrix2.specialUnitary) :
    C * B⁻¹ * A⁻¹ * T⁻¹⁻¹ = T⁻¹ * (A * B * C⁻¹ * T⁻¹)⁻¹ * T⁻¹⁻¹ := by
  simp only [Matrix.mul_inv_rev, su_inv_inv hC, su_inv_inv hT]
  rw [← mul_assoc T⁻¹, su_inv_mul hT, one_mul]
  simp only [mul_assoc]
def negConjEquiv (S : ComplexMatrix2) (hS : S ∈ ComplexMatrix2.specialUnitary) :
    ComplexMatrix2 ≃ₗ[ℂ] ComplexMatrix2 where
  toFun Z := -(S * Z * S⁻¹)
  invFun Z := -(S⁻¹ * Z * S)
  map_add' X Z := by simp only [mul_add, add_mul, neg_add]
  map_smul' r X := by simp
  left_inv Z := by
    have h1 := su_inv_mul hS
    simp only [mul_neg, neg_mul, neg_neg]
    calc S⁻¹ * (S * Z * S⁻¹) * S = (S⁻¹ * S) * Z * (S⁻¹ * S) := by simp only [mul_assoc]
      _ = Z := by rw [h1, one_mul, mul_one]
  right_inv Z := by
    have h1 := su_mul_inv hS
    simp only [mul_neg, neg_mul, neg_neg]
    calc S * (S⁻¹ * Z * S) * S⁻¹ = (S * S⁻¹) * Z * (S * S⁻¹) := by simp only [mul_assoc]
      _ = Z := by rw [h1, one_mul, mul_one]
theorem negConjEquiv_apply (S : ComplexMatrix2) (hS : S ∈ ComplexMatrix2.specialUnitary)
    (Z : ComplexMatrix2) : negConjEquiv S hS Z = -(S * Z * S⁻¹) := rfl
theorem matExp_negConjEquiv_mul (h3 : ComplexMatrix2.OperatorNormUnderConjugation)
    (X : ComplexMatrix2) {T : ComplexMatrix2} (hT : T ∈ ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.matExp (negConjEquiv T⁻¹ (su_inv_mem hT) X) * T⁻¹ =
      (ComplexMatrix2.matExp X * T)⁻¹ := by
  obtain ⟨-, -, -, -, hexp, -, -⟩ := h3
  have hS := su_inv_mem hT
  rw [negConjEquiv_apply, ComplexMatrix2.matExp, Matrix.exp_neg, ← ComplexMatrix2.matExp,
    ← hexp _ _ (su_isUnit hS)]
  simp only [Matrix.mul_inv_rev, su_inv_inv hT]
  rw [mul_assoc, mul_assoc _ T, su_mul_inv hT, mul_one]
theorem inv_mem_unitaryLogDomain {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.specialUnitary)
    (hY1 : Y ≠ -1) : Y⁻¹ ∈ ComplexMatrix2.unitaryLogDomain := by
  refine ⟨su_inv_mem hY, fun h => hY1 ?_⟩
  have h' : Y⁻¹ = -1 := h
  have := su_mul_inv hY
  rw [h'] at this
  simp only [mul_neg, mul_one] at this
  exact neg_eq_iff_eq_neg.mp this
theorem unitaryLog_inv (h2 : ComplexMatrix2.UnitaryLogConjugationProperties) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.specialUnitary) (hY1 : Y ≠ -1) :
    ComplexMatrix2.unitaryLog Y⁻¹ = -ComplexMatrix2.unitaryLog Y := by
  obtain ⟨-, huniq, -⟩ := h2
  have hd : Y ∈ ComplexMatrix2.unitaryLogDomain := ⟨hY, hY1⟩
  have hd' := inv_mem_unitaryLogDomain hY hY1
  have s1 := Classical.epsilon_spec (huniq Y hd).exists
  have s2 := Classical.epsilon_spec (huniq Y⁻¹ hd').exists
  have hneg : (-ComplexMatrix2.unitaryLieLog Y) ∈ ComplexMatrix2.hermitianTraceless ∧
      ComplexMatrix2.operatorNorm (-ComplexMatrix2.unitaryLieLog Y) < Real.pi ∧
      ComplexMatrix2.matExp (Complex.I • (-ComplexMatrix2.unitaryLieLog Y)) = Y⁻¹ := by
    obtain ⟨a, b, c⟩ := s1
    refine ⟨neg_mem a, by rw [ComplexMatrix2.operatorNorm, norm_neg]; exact b, ?_⟩
    rw [smul_neg, ComplexMatrix2.matExp, Matrix.exp_neg, ← ComplexMatrix2.matExp]
    exact congrArg _ c
  have e : ComplexMatrix2.unitaryLieLog Y⁻¹ = -ComplexMatrix2.unitaryLieLog Y :=
    (huniq Y⁻¹ hd').unique s2 hneg
  rw [ComplexMatrix2.unitaryLog, e, smul_neg, ComplexMatrix2.unitaryLog]
theorem unitaryLog_conj_inv (h2 : ComplexMatrix2.UnitaryLogConjugationProperties)
    {Y S : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.specialUnitary) (hY1 : Y ≠ -1)
    (hS : S ∈ ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.unitaryLog (S * Y⁻¹ * S⁻¹) = negConjEquiv S hS (ComplexMatrix2.unitaryLog Y) := by
  have hinv := unitaryLog_inv h2 hY hY1
  obtain ⟨-, -, hconj⟩ := h2
  have hd' := inv_mem_unitaryLogDomain hY hY1
  rw [(hconj _ hd' S hS).2, hinv, negConjEquiv_apply]
  simp only [mul_neg, neg_mul]
theorem conj_inv_ne_neg_one (h2 : ComplexMatrix2.UnitaryLogConjugationProperties)
    {Y S : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.specialUnitary) (hY1 : Y ≠ -1)
    (hS : S ∈ ComplexMatrix2.specialUnitary) :
    S * Y⁻¹ * S⁻¹ ≠ -1 := by
  obtain ⟨-, -, hconj⟩ := h2
  have hd' := inv_mem_unitaryLogDomain hY hY1
  exact (hconj _ hd' S hS).1.2
theorem operatorNorm_conj_inv_sub_one_lt (h3 : ComplexMatrix2.OperatorNormUnderConjugation)
    {W S : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary)
    (hS : S ∈ ComplexMatrix2.specialUnitary) (h : ComplexMatrix2.operatorNorm (W - 1) < 1) :
    ComplexMatrix2.operatorNorm (S * W⁻¹ * S⁻¹ - 1) < 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.operatorNorm_conj_inv_sub_one_lt <;> assumption
theorem logSeries_conj_inv (h1 : ComplexMatrix2.LogSeriesConjugateInverse)
    (h3 : ComplexMatrix2.OperatorNormUnderConjugation)
    {W S : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary)
    (hS : S ∈ ComplexMatrix2.specialUnitary) (h : ComplexMatrix2.operatorNorm (W - 1) < 1) :
    ComplexMatrix2.logSeries (S * W⁻¹ * S⁻¹) = negConjEquiv S hS (ComplexMatrix2.logSeries W) :=
  h1 W S (su_isUnit hW) (su_isUnit hS) h (operatorNorm_conj_inv_sub_one_lt h3 hW hS h)
theorem pathHolonomy_cons (U : Bond L m j → ComplexMatrix2) (b : Bond L m j)
    (Γ : List (Bond L m j)) : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by
  simp [pathHolonomy]
theorem pathHolonomy_mem {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j)
    (Γ : List (Bond L m j)) : pathHolonomy U Γ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.SharedProofs.p3102 <;> assumption
theorem pathHolonomy_forwardFlow_succ (U : Bond L m j → ComplexMatrix2) (μ : Fin 4) (n : ℕ)
    (x : Site L m j) :
    pathHolonomy U (forwardAxisPath x μ (n + 1)) =
      pathHolonomy U (forwardAxisPath x μ n) * U (Bond.forwardFrom (x + n • unitStep L m j μ) μ) := by
  induction n generalizing x with
  | zero => simp [forwardAxisPath, pathHolonomy]
  | succ n ih =>
    have e : x + unitStep L m j μ + n • unitStep L m j μ = x + (n + 1) • unitStep L m j μ := by
      rw [add_smul, one_smul]; abel
    rw [show forwardAxisPath x μ (n + 1 + 1) =
        Bond.forwardFrom x μ :: forwardAxisPath (x + unitStep L m j μ) μ (n + 1) from rfl,
      pathHolonomy_cons, ih, ← mul_assoc, e,
      show forwardAxisPath x μ (n + 1) =
        Bond.forwardFrom x μ :: forwardAxisPath (x + unitStep L m j μ) μ n from rfl, pathHolonomy_cons]
theorem pathHolonomy_backwardFlow {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (μ : Fin 4) (n : ℕ) (y : Site L m j) :
    pathHolonomy U (backwardAxisPath y μ n) =
      (pathHolonomy U (forwardAxisPath (y - n • unitStep L m j μ) μ n))⁻¹ := by
  induction n generalizing y with
  | zero => simp [forwardAxisPath, backwardAxisPath, pathHolonomy]
  | succ n ih =>
    have e1 : y - unitStep L m j μ - n • unitStep L m j μ = y - (n + 1) • unitStep L m j μ := by
      rw [add_smul, one_smul]; abel
    have e2 : y - (n + 1) • unitStep L m j μ + n • unitStep L m j μ = y - unitStep L m j μ := by
      rw [add_smul, one_smul]; abel
    have e3 : Bond.backwardFrom y μ = (Bond.forwardFrom (y - unitStep L m j μ) μ).opposite :=
      Bond.ext (by simp [Bond.backwardFrom, Bond.forwardFrom, Bond.opposite]) rfl
    rw [show backwardAxisPath y μ (n + 1) =
        Bond.backwardFrom y μ :: backwardAxisPath (y - unitStep L m j μ) μ n from rfl,
      pathHolonomy_cons, ih, e1, pathHolonomy_forwardFlow_succ, e2, Matrix.mul_inv_rev, e3,
      hU.2 _ (mem_univ _)]
theorem pathHolonomy_flowAlong_neg {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (μ : Fin 4) (n : ℤ) (x : Site L m j) :
    pathHolonomy U (flowAlong (x + n • unitStep L m j μ) μ (-n)) =
      (pathHolonomy U (flowAlong x μ n))⁻¹ := by
  rcases lt_trichotomy n 0 with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    have hk : 0 < k := by omega
    have a1 : flowAlong x μ (-(k : ℤ)) = backwardAxisPath x μ k := by
      unfold flowAlong
      rw [if_neg (by omega)]
      simp
    have a2 : flowAlong (x + (-(k : ℤ)) • unitStep L m j μ) μ (- -(k : ℤ)) =
        forwardAxisPath (x - k • unitStep L m j μ) μ k := by
      unfold flowAlong
      rw [if_pos (by omega), neg_neg, Int.toNat_natCast, neg_smul, natCast_zsmul, sub_eq_add_neg]
    rw [a1, a2, pathHolonomy_backwardFlow hU, su_inv_inv (pathHolonomy_mem hU _)]
  · subst h
    simp [flowAlong, forwardAxisPath, pathHolonomy]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    have hk : 0 < k := by omega
    have a1 : flowAlong x μ (k : ℤ) = forwardAxisPath x μ k := by
      unfold flowAlong
      rw [if_pos (by omega), Int.toNat_natCast]
    have a2 : flowAlong (x + (k : ℤ) • unitStep L m j μ) μ (-(k : ℤ)) =
        backwardAxisPath (x + k • unitStep L m j μ) μ k := by
      unfold flowAlong
      rw [if_neg (by omega), natCast_zsmul]
      simp
    rw [a1, a2, pathHolonomy_backwardFlow hU, add_sub_cancel_right]
theorem axialDisplacement_unique (hL : 0 < L) {x x' : Site L m j} {μ μ' : Fin 4} {n n' : ℤ}
    (h : IsAxialDisplacement x x' μ n) (h' : IsAxialDisplacement x x' μ' n') :
    (μ = μ' ∧ n = n') ∨ (n = 0 ∧ n' = 0) := by apply _root_.YangMills.Construction.PeriodicLattice.NearOneBounds.axialDisplacement_unique <;> assumption
theorem axialDisplacement_swap {y y' : Site L m j} {μ : Fin 4} {n : ℤ}
    (hd : IsAxialDisplacement y y' μ n) : IsAxialDisplacement y' y μ (-n) := by
  refine ⟨?_, ?_⟩
  · rw [neg_smul, ← hd.1]; abel
  · rw [abs_neg]; exact hd.2
theorem pathHolonomy_axialPath_swap (hL : 0 < L) {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (x x' : Site L m j) :
    pathHolonomy U (axialPath x' x) = (pathHolonomy U (axialPath x x'))⁻¹ := by
  unfold axialPath
  by_cases h : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2
  · have h' : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x' x q.1 q.2 := by
      obtain ⟨q, hq⟩ := h
      exact ⟨(q.1, -q.2), axialDisplacement_swap hq⟩
    rw [dif_pos h, dif_pos h']
    have s : IsAxialDisplacement x x' h.choose.1 h.choose.2 := h.choose_spec
    have s' : IsAxialDisplacement x x' h'.choose.1 (-h'.choose.2) :=
      axialDisplacement_swap (h'.choose_spec)
    generalize h.choose = q at s ⊢
    generalize h'.choose = q' at s' ⊢
    rcases axialDisplacement_unique hL s s' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have ex : x + q.2 • unitStep L m j q.1 = x' := by rw [← s.1]; abel
      have key := pathHolonomy_flowAlong_neg hU q.1 q.2 x
      rw [ex] at key
      rw [← e1, show q'.2 = -q.2 by omega]
      exact key
    · have z : q'.2 = 0 := by omega
      rw [e1, z]
      simp [flowAlong, forwardAxisPath, pathHolonomy]
  · have h' : ¬∃ q : Fin 4 × ℤ, IsAxialDisplacement x' x q.1 q.2 := by
      rintro ⟨q, hq⟩
      exact h ⟨(q.1, -q.2), axialDisplacement_swap hq⟩
    rw [dif_neg h, dif_neg h']
    simp [pathHolonomy]
theorem shiftAcross_opposite (hL : 0 < L) (c : Bond L m j) (x : Site L m (j + 1)) :
    shiftAcross c.opposite (shiftAcross c x) = x := by apply _root_.YangMills.Construction.PeriodicLattice.LinearAverageCovariance.shiftAcross_opposite_shiftAcross <;> assumption
theorem shiftAcross_mem (hL : 0 < L) (c : Bond L m j) {x : Site L m (j + 1)}
    (hx : x ∈ sitesInBlock (j + 1) c.source) : shiftAcross c x ∈ sitesInBlock (j + 1) c.target := by apply _root_.YangMills.Construction.PeriodicLattice.LinearAverageCovariance.shiftAcross_mem_sitesInBlock <;> assumption
theorem shiftAcross_bijOn (hL : 0 < L) (c : Bond L m j) :
    BijOn (shiftAcross c) (sitesInBlock (j + 1) c.source) (sitesInBlock (j + 1) c.target) := by apply _root_.YangMills.Construction.PeriodicLattice.LinearAverageCovariance.shiftAcross_bijOn <;> assumption
section Elements
variable {U : Bond L m (j + 1) → ComplexMatrix2}
theorem parallelTransport_mem (hU : U ∈ compactGaugeFields L m (j + 1)) (c : Bond L m j) :
    parallelTransport U c ∈ ComplexMatrix2.specialUnitary := pathHolonomy_mem hU _
theorem parallelTransport_opposite (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1))
    (c : Bond L m j) : parallelTransport U c.opposite = (parallelTransport U c)⁻¹ :=
  pathHolonomy_axialPath_swap hL hU _ _
theorem pathHolonomy_crossingPath_opposite (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1))
    (c : Bond L m j) (x : Site L m (j + 1)) :
    pathHolonomy U (crossingPath c.opposite (shiftAcross c x)) =
      (pathHolonomy U (crossingPath c x))⁻¹ := by
  unfold crossingPath
  rw [shiftAcross_opposite hL]
  exact pathHolonomy_axialPath_swap hL hU _ _
theorem meanContourHolonomy_mem {y : Site L m j} {x : Site L m (j + 1)}
    (h : HasContourMean U y x) : meanContourHolonomy U y x ∈ ComplexMatrix2.specialUnitary :=
  (Classical.epsilon_spec h.exists).1
theorem crossingDefect_mem (hU : U ∈ compactGaugeFields L m (j + 1)) (c : Bond L m j)
    (x : Site L m (j + 1)) (hA : meanContourHolonomy U c.source x ∈ ComplexMatrix2.specialUnitary)
    (hC : meanContourHolonomy U c.target (shiftAcross c x) ∈ ComplexMatrix2.specialUnitary) :
    crossingDefect U c x ∈ ComplexMatrix2.specialUnitary :=
  mul_mem (mul_mem (mul_mem hA (pathHolonomy_mem hU _)) (su_inv_mem hC))
    (su_inv_mem (parallelTransport_mem hU c))
theorem crossingDefect_opposite (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1))
    (c : Bond L m j) (x : Site L m (j + 1))
    (hC : meanContourHolonomy U c.target (shiftAcross c x) ∈ ComplexMatrix2.specialUnitary) :
    crossingDefect U c.opposite (shiftAcross c x) =
      (parallelTransport U c)⁻¹ * (crossingDefect U c x)⁻¹ * (parallelTransport U c)⁻¹⁻¹ := by
  unfold crossingDefect
  rw [pathHolonomy_crossingPath_opposite hL hU, parallelTransport_opposite hL hU,
    shiftAcross_opposite hL]
  exact inv_conj_fourFactors hC (parallelTransport_mem hU c)
theorem contourCrossingDefect_mem (hU : U ∈ compactGaugeFields L m (j + 1)) (c : Bond L m j)
    (x : Site L m (j + 1)) (σ : AxisOrdering c.source x)
    (σ' : AxisOrdering c.target (shiftAcross c x)) :
    contourCrossingDefect U c x σ σ' ∈ ComplexMatrix2.specialUnitary :=
  mul_mem (mul_mem (mul_mem (pathHolonomy_mem hU _) (pathHolonomy_mem hU _))
    (su_inv_mem (pathHolonomy_mem hU _))) (su_inv_mem (parallelTransport_mem hU c))
theorem contourCrossingDefect_opposite_eq (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1))
    (c : Bond L m j) (x : Site L m (j + 1)) (σ : AxisOrdering c.source x)
    (σ' : AxisOrdering c.target (shiftAcross c x)) :
    pathHolonomy U (orderedContour c.target (shiftAcross c x) σ') *
        pathHolonomy U (crossingPath c.opposite (shiftAcross c x)) *
        (pathHolonomy U (orderedContour c.source x σ))⁻¹ * (parallelTransport U c.opposite)⁻¹ =
      (parallelTransport U c)⁻¹ * (contourCrossingDefect U c x σ σ')⁻¹ *
        (parallelTransport U c)⁻¹⁻¹ := by
  rw [pathHolonomy_crossingPath_opposite hL hU, parallelTransport_opposite hL hU]
  unfold contourCrossingDefect
  exact inv_conj_fourFactors (pathHolonomy_mem hU _) (parallelTransport_mem hU c)
theorem isRegularAveragingCase_opposite (h3 : ComplexMatrix2.OperatorNormUnderConjugation)
    (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1)) {ω : ℝ} {c : Bond L m j}
    (h : IsRegularAveragingCase ω U c) : IsRegularAveragingCase ω U c.opposite := by
  obtain ⟨hp, ht, hh, hn⟩ := h
  refine ⟨?_, hh, ht, ?_⟩
  · intro p hpm
    apply hp p
    have e : bondDoubleBlock c.opposite = bondDoubleBlock c := union_comm _ _
    unfold doubleBlockPlaquettes at hpm ⊢
    rwa [e] at hpm
  · intro x' hx'
    obtain ⟨x, hx, rfl⟩ := (shiftAcross_bijOn hL c).surjOn hx'
    have hC := meanContourHolonomy_mem (hh _ (shiftAcross_mem hL c hx))
    have hA := meanContourHolonomy_mem (ht x hx)
    rw [crossingDefect_opposite hL hU c x hC]
    exact operatorNorm_conj_inv_sub_one_lt h3 (crossingDefect_mem hU c x hA hC)
      (su_inv_mem (parallelTransport_mem hU c)) (hn x hx)
theorem noCrossingDefectIsNegOne_opposite (h2 : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1)) {c : Bond L m j}
    (h : NoCrossingDefectIsNegOne U c) : NoCrossingDefectIsNegOne U c.opposite := by
  intro x' hx' σ' τ'
  obtain ⟨x, hx, rfl⟩ := (shiftAcross_bijOn hL c).surjOn hx'
  have hS := su_inv_mem (parallelTransport_mem hU c)
  have gen : ∀ z, z = x → ∀ (τ : AxisOrdering c.source z),
      pathHolonomy U (orderedContour c.target (shiftAcross c x) σ') *
        pathHolonomy U (crossingPath c.opposite (shiftAcross c x)) *
        (pathHolonomy U (orderedContour c.source z τ))⁻¹ * (parallelTransport U c.opposite)⁻¹ ≠
          -1 := by
    intro z hz τ
    subst hz
    rw [contourCrossingDefect_opposite_eq hL hU c z τ σ']
    exact conj_inv_ne_neg_one h2 (contourCrossingDefect_mem hU c z τ σ') (h z hx τ σ') hS
  exact gen _ (shiftAcross_opposite hL c x) τ'
theorem linearEquiv_map_finsum_mem {α : Type*} (φ : ComplexMatrix2 ≃ₗ[ℂ] ComplexMatrix2)
    (f : α → ComplexMatrix2) (s : Set α) :
    φ (∑ᶠ x ∈ s, f x) = ∑ᶠ x ∈ s, φ (f x) := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.linearEquiv_map_finsum_mem <;> assumption
theorem regularAverageValue_opposite (h1 : ComplexMatrix2.LogSeriesConjugateInverse)
    (h3 : ComplexMatrix2.OperatorNormUnderConjugation) (hL : 0 < L)
    (hU : U ∈ compactGaugeFields L m (j + 1)) {ω : ℝ} {c : Bond L m j}
    (h : IsRegularAveragingCase ω U c) :
    regularAverageValue U c.opposite = (regularAverageValue U c)⁻¹ := by
  obtain ⟨-, ht, hh, hn⟩ := h
  have hT := parallelTransport_mem hU c
  have hS := su_inv_mem hT
  have hsum : ∑ᶠ x' ∈ sitesInBlock (j + 1) c.opposite.source,
      ComplexMatrix2.logSeries (crossingDefect U c.opposite x') =
      negConjEquiv _ hS
        (∑ᶠ x ∈ sitesInBlock (j + 1) c.source, ComplexMatrix2.logSeries (crossingDefect U c x)) := by
    rw [linearEquiv_map_finsum_mem]
    refine (finsum_mem_eq_of_bijOn (shiftAcross c) (shiftAcross_bijOn hL c) fun x hx => ?_).symm
    have hC := meanContourHolonomy_mem (hh _ (shiftAcross_mem hL c hx))
    have hA := meanContourHolonomy_mem (ht x hx)
    rw [crossingDefect_opposite hL hU c x hC]
    exact (logSeries_conj_inv h1 h3 (crossingDefect_mem hU c x hA hC) hS (hn x hx)).symm
  unfold regularAverageValue
  rw [hsum, ← map_smul, parallelTransport_opposite hL hU]
  exact matExp_negConjEquiv_mul h3 _ hT
theorem inner_unitaryLog_sum_opposite (h2 : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hL : 0 < L) (hU : U ∈ compactGaugeFields L m (j + 1)) (c : Bond L m j) (x : Site L m (j + 1))
    (σ' : AxisOrdering c.target (shiftAcross c x))
    (hne : ∀ σ : AxisOrdering c.source x, contourCrossingDefect U c x σ σ' ≠ -1) :
    (((Fintype.card (AxisOrdering c.opposite.target
        (shiftAcross c.opposite (shiftAcross c x))) : ℝ)⁻¹ : ℝ) : ℂ) •
      ∑ τ : AxisOrdering c.opposite.target (shiftAcross c.opposite (shiftAcross c x)),
        ComplexMatrix2.unitaryLog (contourCrossingDefect U c.opposite (shiftAcross c x) σ' τ) =
    (((Fintype.card (AxisOrdering c.source x) : ℝ)⁻¹ : ℝ) : ℂ) •
      ∑ σ : AxisOrdering c.source x,
        negConjEquiv _ (su_inv_mem (parallelTransport_mem hU c))
          (ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ')) := by
  have hS := su_inv_mem (parallelTransport_mem hU c)
  have gen : ∀ z, z = x →
      (((Fintype.card (AxisOrdering c.source z) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ τ : AxisOrdering c.source z,
          ComplexMatrix2.unitaryLog (pathHolonomy U (orderedContour c.target (shiftAcross c x) σ') *
            pathHolonomy U (crossingPath c.opposite (shiftAcross c x)) *
            (pathHolonomy U (orderedContour c.source z τ))⁻¹ * (parallelTransport U c.opposite)⁻¹) =
      (((Fintype.card (AxisOrdering c.source x) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ : AxisOrdering c.source x,
          negConjEquiv _ (su_inv_mem (parallelTransport_mem hU c))
            (ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ')) := by
    intro z hz
    subst hz
    refine congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun τ _ => ?_)
    rw [contourCrossingDefect_opposite_eq hL hU c z τ σ']
    exact unitaryLog_conj_inv h2 (contourCrossingDefect_mem hU c z τ σ') (hne τ) hS
  exact gen _ (shiftAcross_opposite hL c x)
theorem logAverageValue_opposite (h2 : ComplexMatrix2.UnitaryLogConjugationProperties)
    (h3 : ComplexMatrix2.OperatorNormUnderConjugation) (hL : 0 < L)
    (hU : U ∈ compactGaugeFields L m (j + 1)) {c : Bond L m j}
    (h : NoCrossingDefectIsNegOne U c) :
    logAverageValue U c.opposite = (logAverageValue U c)⁻¹ := by
  have hT := parallelTransport_mem hU c
  have hS := su_inv_mem hT
  have hsum : ∑ᶠ x' ∈ sitesInBlock (j + 1) c.opposite.source,
      (((Fintype.card (AxisOrdering c.opposite.source x') : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ' : AxisOrdering c.opposite.source x',
          (((Fintype.card (AxisOrdering c.opposite.target (shiftAcross c.opposite x')) : ℝ)⁻¹ :
            ℝ) : ℂ) •
            ∑ τ : AxisOrdering c.opposite.target (shiftAcross c.opposite x'),
              ComplexMatrix2.unitaryLog (contourCrossingDefect U c.opposite x' σ' τ) =
      negConjEquiv _ hS (∑ᶠ x ∈ sitesInBlock (j + 1) c.source,
        (((Fintype.card (AxisOrdering c.source x) : ℝ)⁻¹ : ℝ) : ℂ) •
          ∑ σ : AxisOrdering c.source x,
            (((Fintype.card (AxisOrdering c.target (shiftAcross c x)) : ℝ)⁻¹ : ℝ) : ℂ) •
              ∑ σ' : AxisOrdering c.target (shiftAcross c x),
                ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ')) := by
    rw [linearEquiv_map_finsum_mem]
    refine (finsum_mem_eq_of_bijOn (shiftAcross c) (shiftAcross_bijOn hL c) fun x hx => ?_).symm
    refine Eq.trans ?_ (congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun σ' _ =>
      (inner_unitaryLog_sum_opposite h2 hL hU c x σ' (fun σ => h x hx σ σ')).symm))
    simp only [map_smul, map_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ' _ => Finset.sum_congr rfl fun σ _ => smul_comm _ _ _
  unfold logAverageValue
  rw [hsum, ← map_smul, parallelTransport_opposite hL hU]
  exact matExp_negConjEquiv_mul h3 _ hT
end Elements
theorem blockAverageAtOpposite_holds (h1 : ComplexMatrix2.LogSeriesConjugateInverse)
    (h2 : ComplexMatrix2.UnitaryLogConjugationProperties)
    (h3 : ComplexMatrix2.OperatorNormUnderConjugation) :
    BlockAverageAtOpposite := by
  intro L m hLs _ j j' _ hj' ω c U hU
  subst hj'
  have hL : 0 < L := by
    have := hLs.2
    omega
  have hA : IsRegularAveragingCase ω U c.opposite ↔ IsRegularAveragingCase ω U c :=
    ⟨fun h => isRegularAveragingCase_opposite h3 hL hU (c := c.opposite) h,
      isRegularAveragingCase_opposite h3 hL hU⟩
  have hN : NoCrossingDefectIsNegOne U c.opposite ↔ NoCrossingDefectIsNegOne U c :=
    ⟨fun h => noCrossingDefectIsNegOne_opposite h2 hL hU (c := c.opposite) h,
      noCrossingDefectIsNegOne_opposite h2 hL hU⟩
  constructor
  · unfold blockAverageCase
    by_cases a : IsRegularAveragingCase ω U c
    · rw [if_pos a, if_pos (hA.2 a)]
    · rw [if_neg a, if_neg (fun h => a (hA.1 h))]
      by_cases n : NoCrossingDefectIsNegOne U c
      · rw [if_pos n, if_pos (hN.2 n)]
      · rw [if_neg n, if_neg (fun h => n (hN.1 h))]
  · rw [blockAverageOnPositive_eq_byCase, blockAverageOnPositive_eq_byCase]
    unfold blockAverageCase
    by_cases a : IsRegularAveragingCase ω U c
    · rw [if_pos a, if_pos (hA.2 a)]
      exact regularAverageValue_opposite h1 h3 hL hU a
    · rw [if_neg a, if_neg (fun h => a (hA.1 h))]
      by_cases n : NoCrossingDefectIsNegOne U c
      · rw [if_pos n, if_pos (hN.2 n)]
        exact logAverageValue_opposite h2 h3 hL hU n
      · rw [if_neg n, if_neg (fun h => n (hN.1 h))]
        exact parallelTransport_opposite hL hU c
end PeriodicLattice.OppositeBond
end YangMills.Construction
