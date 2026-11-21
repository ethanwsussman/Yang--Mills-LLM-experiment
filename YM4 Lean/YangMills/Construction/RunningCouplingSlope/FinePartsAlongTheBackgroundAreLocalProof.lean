import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.FinePartsAlongTheBackgroundAreLocal
import YangMills.Construction.RunningCouplingSlope.RelationsOfTheFinePartsAreSparse
import YangMills.Construction.RunningCouplingSlope.ResponseOfAUnitFormDecays
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Matrices Tower PeriodicOperators
open Tower.CriticalBranchResponse
private def JetBound (g : ℝ → ℝ → ℂ) (V A B D : ℝ) : Prop :=
  ∃ v a b c, HasSecondOrderJet g v a b c ∧ ‖v‖ ≤ V ∧ ‖a‖ ≤ A ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ D
section JetRules
variable {g h : ℝ → ℝ → ℂ} {V A B D V' A' B' D' : ℝ}
private theorem JetBound.mono (hg : JetBound g V A B D) (h1 : V ≤ V') (h2 : A ≤ A') (h3 : B ≤ B')
    (h4 : D ≤ D') : JetBound g V' A' B' D' := by
  obtain ⟨v, a, b, c, hj, i1, i2, i3, i4⟩ := hg
  exact ⟨v, a, b, c, hj, i1.trans h1, i2.trans h2, i3.trans h3, i4.trans h4⟩
private theorem JetBound.congr (hg : JetBound g V A B D) (e : ∀ s t, g s t = h s t) :
    JetBound h V A B D := by
  have : g = h := funext fun s => funext fun t => e s t
  rwa [← this]
private theorem JetBound.add (J : SecondOrderJetClosure) (hg : JetBound g V A B D)
    (hh : JetBound h V' A' B' D') :
    JetBound (fun s t => g s t + h s t) (V + V') (A + A') (B + B') (D + D') := by
  obtain ⟨v, a, b, c, hj, i1, i2, i3, i4⟩ := hg
  obtain ⟨v', a', b', c', hj', k1, k2, k3, k4⟩ := hh
  exact ⟨_, _, _, _, J.add hj hj', (norm_add_le _ _).trans (add_le_add i1 k1),
    (norm_add_le _ _).trans (add_le_add i2 k2), (norm_add_le _ _).trans (add_le_add i3 k3),
    (norm_add_le _ _).trans (add_le_add i4 k4)⟩
private theorem JetBound.nonneg (hg : JetBound g V A B D) : 0 ≤ V ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ D := by
  obtain ⟨v, a, b, c, -, i1, i2, i3, i4⟩ := hg
  exact ⟨(norm_nonneg _).trans i1, (norm_nonneg _).trans i2, (norm_nonneg _).trans i3,
    (norm_nonneg _).trans i4⟩
private theorem JetBound.mul (J : SecondOrderJetClosure) (hg : JetBound g V A B D)
    (hh : JetBound h V' A' B' D') :
    JetBound (fun s t => g s t * h s t) (V * V') (A * V' + V * A') (B * V' + V * B')
      (D * V' + A * B' + B * A' + V * D') := by
  obtain ⟨hV, hA, hB, hD⟩ := hg.nonneg
  obtain ⟨hV', hA', hB', hD'⟩ := hh.nonneg
  obtain ⟨v, a, b, c, hj, i1, i2, i3, i4⟩ := hg
  obtain ⟨v', a', b', c', hj', k1, k2, k3, k4⟩ := hh
  have m : ∀ {x y : ℂ} {X Y : ℝ}, ‖x‖ ≤ X → ‖y‖ ≤ Y → ‖x * y‖ ≤ X * Y := fun hx hy => by
    rw [norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)
  refine ⟨_, _, _, _, J.mul hj hj', m i1 k1, ?_, ?_, ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (m i2 k1) (m i1 k2))
  · exact (norm_add_le _ _).trans (add_le_add (m i3 k1) (m i1 k3))
  · refine (norm_add_le _ _).trans (add_le_add ?_ (m i1 k4))
    refine (norm_add_le _ _).trans (add_le_add ?_ (m i3 k2))
    exact (norm_add_le _ _).trans (add_le_add (m i4 k1) (m i2 k3))
private theorem JetBound.const (J : SecondOrderJetClosure) (w : ℂ) :
    JetBound (fun _ _ => w) ‖w‖ 0 0 0 :=
  ⟨_, _, _, _, J.const w, le_rfl, by simp, by simp, by simp⟩
private theorem JetBound.const_mul (J : SecondOrderJetClosure) (w : ℂ) (hg : JetBound g V A B D) :
    JetBound (fun s t => w * g s t) (‖w‖ * V) (‖w‖ * A) (‖w‖ * B) (‖w‖ * D) := by
  refine ((JetBound.const J w).mul J hg).mono le_rfl ?_ ?_ ?_ <;> simp
private theorem JetBound.sum (J : SecondOrderJetClosure) {κ : Type} (S : Finset κ)
    {G : κ → ℝ → ℝ → ℂ} {Vf Af Bf Df : κ → ℝ}
    (hG : ∀ i ∈ S, JetBound (G i) (Vf i) (Af i) (Bf i) (Df i)) :
    JetBound (fun s t => ∑ i ∈ S, G i s t) (∑ i ∈ S, Vf i) (∑ i ∈ S, Af i) (∑ i ∈ S, Bf i)
      (∑ i ∈ S, Df i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using JetBound.const J 0
  | insert i S hi ih =>
    have h1 := (hG i (Finset.mem_insert_self i S)).add J
      (ih fun j hj => hG j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h1
private theorem JetBound.zero (J : SecondOrderJetClosure) : JetBound (fun _ _ => 0) 0 0 0 0 := by
  simpa using JetBound.const J 0
private theorem JetBound.ite (J : SecondOrderJetClosure) (P : Prop) [Decidable P]
    (hg : P → JetBound g V A B D) (h0 : 0 ≤ V) (h1 : 0 ≤ A) (h2 : 0 ≤ B) (h3 : 0 ≤ D) :
    JetBound (fun s t => if P then g s t else 0) V A B D := by
  by_cases h : P
  · simpa [h] using hg h
  · simpa [h] using (JetBound.zero J).mono h0 h1 h2 h3
end JetRules
private def cosOfReal (u : ℝ) : ℂ := (Real.cos u : ℂ)
private def sinOfReal (u : ℝ) : ℂ := (Real.sin u : ℂ)
private theorem hasDerivAt_cosOfReal (u : ℝ) : HasDerivAt cosOfReal (-sinOfReal u) u := by
  have h := (Real.hasDerivAt_cos u).ofReal_comp
  have e : ((-Real.sin u : ℝ) : ℂ) = -sinOfReal u := by simp [sinOfReal]
  rw [e] at h
  exact h
private theorem hasDerivAt_sinOfReal (u : ℝ) : HasDerivAt sinOfReal (cosOfReal u) u := (Real.hasDerivAt_sin u).ofReal_comp
private theorem contDiff_cosOfReal : ContDiff ℝ 2 cosOfReal :=
  Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
private theorem contDiff_sinOfReal : ContDiff ℝ 2 sinOfReal :=
  Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
private theorem jetBound_cos (J : SecondOrderJetClosure) (α β : ℝ) :
    JetBound (fun s t => (Real.cos (s * α + t * β) : ℂ)) 1 0 0 (|α| * |β|) := by
  have h := J.comp_linear α β contDiff_cosOfReal
  have d1 : deriv cosOfReal = fun u => -sinOfReal u :=
    funext fun u => (hasDerivAt_cosOfReal u).deriv
  have d2 : deriv (fun u => -sinOfReal u) 0 = -cosOfReal 0 := ((hasDerivAt_sinOfReal 0).neg).deriv
  refine ⟨_, _, _, _, h, ?_, ?_, ?_, ?_⟩
  · simp [cosOfReal]
  · simp [d1, sinOfReal]
  · simp [d1, sinOfReal]
  · rw [d1, d2]
    simp [cosOfReal]
private theorem jetBound_smul_sin (J : SecondOrderJetClosure) (w : ℝ) (α β : ℝ) :
    JetBound (fun s t => ((w * Real.sin (s * α + t * β) : ℝ) : ℂ)) 0 |w * α| |w * β| 0 := by
  have hsm : ContDiff ℝ 2 (fun u => (w : ℂ) * sinOfReal u) := contDiff_const.mul contDiff_sinOfReal
  have h := J.comp_linear α β hsm
  have d1 : deriv (fun u => (w : ℂ) * sinOfReal u) = fun u => (w : ℂ) * cosOfReal u :=
    funext fun u => ((hasDerivAt_sinOfReal u).const_mul (w : ℂ)).deriv
  have d2 : deriv (fun u => (w : ℂ) * cosOfReal u) 0 = (w : ℂ) * (-sinOfReal 0) :=
    ((hasDerivAt_cosOfReal 0).const_mul (w : ℂ)).deriv
  refine JetBound.congr ⟨_, _, _, _, h, ?_, ?_, ?_, ?_⟩ ?_
  · simp [sinOfReal]
  · rw [d1]
    simp [cosOfReal, abs_mul, mul_comm]
  · rw [d1]
    simp [cosOfReal, abs_mul, mul_comm]
  · rw [d1, d2]
    simp [sinOfReal]
  · intro s t
    simp [sinOfReal]
private theorem adjointRotation_eq_trig (c a : Fin 3) : ∃ w₁ w₂ w₃ : ℂ, ‖w₁‖ ≤ 1 ∧ ‖w₂‖ ≤ 1 ∧
    w₁ + w₃ = (if a = c then 1 else 0) ∧
    ∀ u, adjointRotation u c a = w₁ * cosOfReal (2 * u) + w₂ * sinOfReal (2 * u) + w₃ := by
  fin_cases c <;> fin_cases a
  · exact ⟨1, 0, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation, cosOfReal]⟩
  · exact ⟨0, 1, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation, sinOfReal]⟩
  · exact ⟨0, 0, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation]⟩
  · exact ⟨0, -1, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation, sinOfReal]⟩
  · exact ⟨1, 0, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation, cosOfReal]⟩
  · exact ⟨0, 0, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation]⟩
  · exact ⟨0, 0, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation]⟩
  · exact ⟨0, 0, 0, by simp, by simp, by simp, fun u => by simp [adjointRotation]⟩
  · exact ⟨0, 0, 1, by simp, by simp, by simp, fun u => by simp [adjointRotation]⟩
private theorem jetBound_adjointRotation_sub (J : SecondOrderJetClosure) (c a : Fin 3) (α β : ℝ)
    (e : ℂ) :
    JetBound (fun s t => adjointRotation (s * α + t * β) c a - e)
      ‖(if a = c then (1 : ℂ) else 0) - e‖ (2 * |α|) (2 * |β|) (4 * (|α| * |β|)) := by
  obtain ⟨w₁, w₂, w₃, h₁, h₂, h₃, hform⟩ := adjointRotation_eq_trig c a
  set G : ℝ → ℂ := fun u => w₁ * cosOfReal u + w₂ * sinOfReal u + w₃ - e with hGdef
  have hG : ContDiff ℝ 2 G :=
    (((contDiff_const.mul contDiff_cosOfReal).add (contDiff_const.mul contDiff_sinOfReal)).add
      contDiff_const).sub contDiff_const
  have h := J.comp_linear (2 * α) (2 * β) hG
  have hd : ∀ u, HasDerivAt G (w₁ * (-sinOfReal u) + w₂ * cosOfReal u) u := fun u =>
    ((((hasDerivAt_cosOfReal u).const_mul w₁).add
      ((hasDerivAt_sinOfReal u).const_mul w₂)).add_const w₃).sub_const e
  have d1 : deriv G = fun u => w₁ * (-sinOfReal u) + w₂ * cosOfReal u :=
    funext fun u => (hd u).deriv
  have d2 : deriv (fun u => w₁ * (-sinOfReal u) + w₂ * cosOfReal u) 0 =
      w₁ * (-cosOfReal 0) + w₂ * (-sinOfReal 0) :=
    (((hasDerivAt_sinOfReal 0).neg.const_mul w₁).add
      ((hasDerivAt_cosOfReal 0).const_mul w₂)).deriv
  have c0 : cosOfReal 0 = 1 := by simp [cosOfReal]
  have s0 : sinOfReal 0 = 0 := by simp [sinOfReal]
  refine JetBound.congr ⟨_, _, _, _, h, ?_, ?_, ?_, ?_⟩ ?_
  · rw [← h₃]
    simp [hGdef, c0, s0]
  · rw [d1]
    simp only [s0, c0, neg_zero, mul_zero, zero_add, mul_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    exact mul_le_of_le_one_right (by positivity) h₂
  · rw [d1]
    simp only [s0, c0, neg_zero, mul_zero, zero_add, mul_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    exact mul_le_of_le_one_right (by positivity) h₂
  · rw [d1, d2]
    rw [c0, s0]
    simp only [mul_zero, neg_zero, add_zero, mul_neg, mul_one, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_two]
    have h0 : 0 ≤ |α| * |β| := by positivity
    nlinarith [mul_le_of_le_one_right h0 h₁]
  · intro s t
    have e1 : s * (2 * α) + t * (2 * β) = 2 * (s * α + t * β) := by ring
    simp only [hGdef, e1, hform]
private theorem jetBound_adjointRotation (J : SecondOrderJetClosure) (c a : Fin 3) (α β : ℝ) :
    JetBound (fun s t => adjointRotation (s * α + t * β) c a) 1 (2 * |α|) (2 * |β|)
      (4 * (|α| * |β|)) := by
  refine JetBound.congr ((jetBound_adjointRotation_sub J c a α β 0).mono ?_ le_rfl le_rfl le_rfl)
    fun s t => by simp
  split_ifs <;> simp
private theorem diagExpAngle_zero : diagExpAngle 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagExpAngle]
private theorem diagExpAngle_inv (a : ℝ) : (diagExpAngle a)⁻¹ = diagExpAngle (-a) := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagExpAngle, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
private theorem matExp_smul_pauli_diag (ψ : ℝ) :
    ComplexMatrix2.matExp (Complex.I • ((ψ : ℂ) • ComplexMatrix2.pauliFamily 2)) = diagExpAngle ψ := by
  have hp : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := ComplexMatrix2.pauliFamily_apply.2.2
  have e : Complex.I • ((ψ : ℂ) • ComplexMatrix2.pauliFamily 2) =
      Matrix.diagonal ![(ψ : ℂ) * Complex.I, -((ψ : ℂ) * Complex.I)] := by
    rw [hp]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring
  rw [e, ComplexMatrix2.matExp, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagExpAngle, Matrix.diagonal, Complex.exp_eq_exp_ℂ]
private theorem abs_le_of_norm_smul_pauli (x B : ℝ) (h : ‖(x : ℂ) • ComplexMatrix2.pauliFamily 2‖ ≤ B) :
    |x| ≤ B := by
  have hp : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := ComplexMatrix2.pauliFamily_apply.2.2
  have hB : 0 ≤ B := (norm_nonneg _).trans h
  have h1 : ‖((x : ℂ) • ComplexMatrix2.pauliFamily 2) * ((x : ℂ) • ComplexMatrix2.pauliFamily 2)‖ ≤
      B * B :=
    (norm_mul_le _ _).trans (mul_le_mul h h (norm_nonneg _) hB)
  have h2 : ((x : ℂ) • ComplexMatrix2.pauliFamily 2) * ((x : ℂ) • ComplexMatrix2.pauliFamily 2) =
      ((x * x : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
    rw [hp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h2, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_self_nonneg x)] at h1
  exact abs_le_of_sq_le_sq' (by nlinarith) hB |> abs_le.2
private theorem isLocal_of_jetBound (hE : LocalFamilyOfJetEntries) {L n k : ℕ}
    {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (c : ι → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (c' : ι' → PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k))
    (T : ℝ → ℝ → Matrix ι' ι ℂ) (z : Fin 4 → ℤ) (θ K r : ℝ) (R C : ℕ) (S : ι' → ι → Prop)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hS : IsBoundedSparsityOnCells c c' S R C r)
    (hz : ∀ p q, ¬ S p q → ∀ s t, T s t p q = 0)
    (hB : ∀ p q, JetBound (fun s t => T s t p q) K
      (K * cellDecayWeight θ (cellOfCoords L n k 0) (c' p))
      (K * cellDecayWeight θ (cellOfCoords L n k z) (c' p))
      (K * (cellDecayWeight θ (cellOfCoords L n k 0) (c' p) *
        cellDecayWeight θ (cellOfCoords L n k z) (c' p)))) :
    IsLocalAlongBackground c c' T z (Real.sqrt ((R : ℝ) * C) * K * Real.exp (θ * r)) θ := by
  choose v a b d hj h1 h2 h3 h4 using hB
  refine hE.2 c c' T z θ K r R C S v a b d hθ hK hS hj ?_ h1 h2 h3 h4
  intro p q hpq
  have hzero : (fun s t => T s t p q) = fun _ _ => 0 :=
    funext fun s => funext fun t => hz p q hpq s t
  have e := hj p q
  rw [hzero] at e
  exact ⟨e.apply_zero.symm, by simpa using e.deriv_fst.symm, by simpa using e.deriv_snd.symm,
    by simpa using e.deriv_mixed.symm⟩
section MoreJetRules
variable {g h : ℝ → ℝ → ℂ} {V A B D V' A' B' D' : ℝ}
private theorem JetBound.sub (J : SecondOrderJetClosure) (hg : JetBound g V A B D)
    (hh : JetBound h V' A' B' D') :
    JetBound (fun s t => g s t - h s t) (V + V') (A + A') (B + B') (D + D') := by
  have h1 := JetBound.const_mul J (-1) hh
  simp only [norm_neg, norm_one, one_mul] at h1
  exact (hg.add J h1).congr fun s t => by ring
private theorem JetBound.sum_le (J : SecondOrderJetClosure) {κ : Type} (S : Finset κ)
    {G : κ → ℝ → ℝ → ℂ} (N : ℕ) (hN : S.card ≤ N) (h0 : 0 ≤ V) (h1 : 0 ≤ A) (h2 : 0 ≤ B)
    (h3 : 0 ≤ D) (hG : ∀ i ∈ S, JetBound (G i) V A B D) :
    JetBound (fun s t => ∑ i ∈ S, G i s t) (N * V) (N * A) (N * B) (N * D) := by
  have hc : (S.card : ℝ) ≤ N := by exact_mod_cast hN
  refine (JetBound.sum J S hG).mono ?_ ?_ ?_ ?_ <;>
    · simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hc (by assumption)
end MoreJetRules
private theorem adjointRotation_zero (c a : Fin 3) :
    adjointRotation 0 c a = if a = c then 1 else 0 := by
  obtain ⟨w₁, w₂, w₃, -, -, h₃, hform⟩ := adjointRotation_eq_trig c a
  rw [hform, ← h₃]
  simp [cosOfReal, sinOfReal]
private theorem norm_transportSign (i : Fin 4) : ‖transportSign i‖ = 1 := by
  fin_cases i <;> simp [transportSign]
private theorem holonomyAngle_linear {L n k : ℕ} (x₁ x₂ : Edge L n k 0 → ℝ) (e s t : ℝ)
    (p : Face L n k 0) (i : Fin 4) :
    holonomyAngle (fun b => s * (e * x₁ b) + t * (e * x₂ b)) p i =
      s * holonomyAngle (fun b => e * x₁ b) p i + t * holonomyAngle (fun b => e * x₂ b) p i := by
  fin_cases i <;> simp [holonomyAngle] <;> ring
private structure AngleData (L n k : ℕ) (z : Fin 4 → ℤ) (θ W E : ℝ) (x₁ x₂ : Edge L n k 0 → ℝ) :
    Prop where
  η_pos : 0 < finestMesh L k
  η_le : finestMesh L k ≤ 1
  θ_nonneg : 0 ≤ θ
  W_ge : 1 ≤ W
  E_ge : 1 ≤ E
  anti : ∀ b, (fun b => finestMesh L k * x₁ b) b.opposite = -(finestMesh L k * x₁ b) ∧
    (fun b => finestMesh L k * x₂ b) b.opposite = -(finestMesh L k * x₂ b)
  back : ∀ s t, twoSourceBackground L n k z s t =
    abelianGaugeField fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)
  bond₁ : ∀ b : PositiveEdge L n k 0,
    |x₁ b.1| ≤ W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell b.1.source)
  bond₂ : ∀ b : PositiveEdge L n k 0,
    |x₂ b.1| ≤ W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell b.1.source)
  angle₁ : ∀ (p : Face L n k 0) (i : Fin 4),
    |holonomyAngle (fun b => finestMesh L k * x₁ b) p i| ≤
      finestMesh L k * (W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin))
  angle₂ : ∀ (p : Face L n k 0) (i : Fin 4),
    |holonomyAngle (fun b => finestMesh L k * x₂ b) p i| ≤
      finestMesh L k * (W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin))
  curl₁ : ∀ p : Face L n k 0,
    |(finestMesh L k ^ 2)⁻¹ * holonomyAngle (fun b => finestMesh L k * x₁ b) p 3| ≤
      W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin)
  curl₂ : ∀ p : Face L n k 0,
    |(finestMesh L k ^ 2)⁻¹ * holonomyAngle (fun b => finestMesh L k * x₂ b) p 3| ≤
      W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin)
  near₁ : ∀ (p : Face L n k 0) (q : PositiveEdge L n k 0),
    (∃ l, facePositiveEdge p l = q) →
      cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin) ≤
        E * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell q.1.source)
  near₂ : ∀ (p : Face L n k 0) (q : PositiveEdge L n k 0),
    (∃ l, facePositiveEdge p l = q) →
      cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin) ≤
        E * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell q.1.source)
section LocalParts
variable {L n k : ℕ} {z : Fin 4 → ℤ} {θ W E : ℝ} {x₁ x₂ : Edge L n k 0 → ℝ}
private theorem cellDecayWeight_nonneg (θ : ℝ)
    (y₀ y : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)) :
    0 ≤ cellDecayWeight θ y₀ y := (Real.exp_pos _).le
private theorem le_sq_mul_sq (d : AngleData L n k z θ W E x₁ x₂) :
    1 ≤ W ^ 2 * E ^ 2 ∧ W ≤ W ^ 2 * E ^ 2 ∧ W ^ 2 ≤ W ^ 2 * E ^ 2 ∧ W * E ≤ W ^ 2 * E ^ 2 := by
  have hW := d.W_ge
  have hE := d.E_ge
  have hW2 : W ≤ W ^ 2 := by nlinarith
  have hE2 : E ≤ E ^ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_⟩
  exact mul_le_mul hW2 hE2 (by linarith) (by positivity)
private theorem isLocal_covariantDifference (hE : LocalFamilyOfJetEntries)
    (hA : AbelianFineKernels) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) (d : AngleData L n k z θ W E x₁ x₂)
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Face L n k 0)] [Fintype (Face L n k 0)]
    [DecidableEq (Fin 3 × Vertex L n k 0)]
    (hS : IsBoundedSparsityOnCells colouredVertexCell colouredEdgeCell
      (vertexEdgeIncidence (L := L) (n := n) (k := k)) 768 768 8) :
    IsLocalAlongBackground colouredVertexCell colouredEdgeCell (covariantDifferenceDefect L n k z) z
      (Real.sqrt (((768 : ℕ) : ℝ) * (768 : ℕ)) * (1000000 * (W ^ 2 * E ^ 2)) * Real.exp (θ * 8))
      θ := by
  classical
  have J := hE.1
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := le_sq_mul_sq d
  have hη := d.η_pos
  have hη1 := d.η_le
  have e0 : trivialField L n k 0 = abelianGaugeField fun _ => 0 := by
    funext b
    simp [trivialField, abelianGaugeField, diagExpAngle_zero]
  have ent : ∀ s t (ι' : Fin 3 × PositiveEdge L n k 0) (ι : Fin 3 × Vertex L n k 0),
      covariantDifferenceDefect L n k z s t ι' ι = if ι.2 = ι'.2.1.target then
        (((finestMesh L k)⁻¹ : ℝ) : ℂ) *
          (adjointRotation (s * (finestMesh L k * x₁ ι'.2.1) + t * (finestMesh L k * x₂ ι'.2.1))
            ι'.1 ι.1 - (if ι.1 = ι'.1 then 1 else 0)) else 0 := by
    intro s t ι' ι
    have h1 := (hA L hL k hk n hn (fun b => s * (finestMesh L k * x₁ b) +
      t * (finestMesh L k * x₂ b)) (fun b => by
        have := d.anti b
        simp only at this
        rw [this.1, this.2]
        ring)).1
    have h2 := (hA L hL k hk n hn (fun _ => 0) (fun _ => by simp)).1
    unfold covariantDifferenceDefect
    rw [d.back, e0, Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, h1, h2]
    unfold covDiffEntry
    by_cases h : ι.2 = ι'.2.1.target
    · simp only [if_pos h, adjointRotation_zero]
      ring
    · simp only [if_neg h]
      ring
  refine isLocal_of_jetBound hE _ _ _ z θ _ 8 768 768 vertexEdgeIncidence d.θ_nonneg
    (by positivity) hS (fun p q hpq s t => ?_) fun p q => ?_
  · rw [ent]
    exact if_neg hpq
  · refine JetBound.congr ?_ fun s t => (ent s t p q).symm
    have hb := d.bond₁ p.2
    have hb' := d.bond₂ p.2
    have w₁ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k 0)
      (fineVertexCell p.2.1.source)
    have w₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
      (fineVertexCell p.2.1.source)
    have hK0 : 0 ≤ 1000000 * (W ^ 2 * E ^ 2) := by positivity
    refine JetBound.ite J _ (fun _ => ?_) hK0 (mul_nonneg hK0 w₁) (mul_nonneg hK0 w₂)
      (mul_nonneg hK0 (mul_nonneg w₁ w₂))
    have h1 := JetBound.const_mul J (((finestMesh L k)⁻¹ : ℝ) : ℂ)
      (jetBound_adjointRotation_sub J p.1 q.1 (finestMesh L k * x₁ p.2.1)
        (finestMesh L k * x₂ p.2.1) (if q.1 = p.1 then 1 else 0))
    have n1 : ‖(((finestMesh L k)⁻¹ : ℝ) : ℂ)‖ = (finestMesh L k)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    have i1 : ∀ y : ℝ, (finestMesh L k)⁻¹ * (2 * |finestMesh L k * y|) = 2 * |y| := by
      intro y
      rw [abs_mul, abs_of_pos hη]
      field_simp
    rw [n1] at h1
    refine h1.mono ?_ ?_ ?_ ?_
    · simp only [sub_self, norm_zero, mul_zero]
      exact hK0
    · rw [i1]
      have := mul_le_mul_of_nonneg_right hQ2 w₁
      have h0 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) w₁
      change _ ≤ 1000000 * (W ^ 2 * E ^ 2) *
        cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source)
      nlinarith
    · rw [i1]
      have := mul_le_mul_of_nonneg_right hQ2 w₂
      have h0 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) w₂
      change _ ≤ 1000000 * (W ^ 2 * E ^ 2) *
        cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source)
      nlinarith
    · have e1 : (finestMesh L k)⁻¹ * (4 * (|finestMesh L k * x₁ p.2.1| *
          |finestMesh L k * x₂ p.2.1|)) = finestMesh L k * (4 * (|x₁ p.2.1| * |x₂ p.2.1|)) := by
        rw [abs_mul, abs_mul, abs_of_pos hη]
        field_simp
      rw [e1]
      have hw := mul_nonneg w₁ w₂
      have hxx : |x₁ p.2.1| * |x₂ p.2.1| ≤ W ^ 2 *
          (cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source) *
          cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source)) := by
        calc |x₁ p.2.1| * |x₂ p.2.1| ≤
              (W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source)) *
              (W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source)) :=
              mul_le_mul hb hb' (abs_nonneg _) (mul_nonneg (by linarith [d.W_ge]) w₁)
          _ = _ := by ring
      have h2 := mul_le_mul_of_nonneg_right hQ3 hw
      have h3 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) hw
      have h4 : finestMesh L k * (4 * (|x₁ p.2.1| * |x₂ p.2.1|)) ≤ 4 * (|x₁ p.2.1| * |x₂ p.2.1|) :=
        mul_le_of_le_one_left (by positivity) hη1
      change _ ≤ 1000000 * (W ^ 2 * E ^ 2) *
        (cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source) *
          cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source))
      nlinarith
private theorem line_opposite (d : AngleData L n k z θ W E x₁ x₂) (s t : ℝ) (b : Edge L n k 0) :
    (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) b.opposite =
      -((fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) b) := by
  have := d.anti b
  simp only at this ⊢
  rw [this.1, this.2]
  ring
private theorem isLocal_holonomyDefect (hE : LocalFamilyOfJetEntries)
    (hA : AbelianFineKernels) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) (d : AngleData L n k z θ W E x₁ x₂)
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Face L n k 0)] [Fintype (Face L n k 0)]
    [DecidableEq (Fin 3 × PositiveEdge L n k 0)]
    (hS : IsBoundedSparsityOnCells colouredEdgeCell colouredFaceCell
      (faceEdgeIncidence (L := L) (n := n) (k := k)) 768 768 8) :
    IsLocalAlongBackground colouredEdgeCell colouredFaceCell (holonomyDefectAlongBackground L n k z) z
      (Real.sqrt (((768 : ℕ) : ℝ) * (768 : ℕ)) * (1000000 * (W ^ 2 * E ^ 2)) * Real.exp (θ * 8))
      θ := by
  classical
  have J := hE.1
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := le_sq_mul_sq d
  have hη := d.η_pos
  have hη1 := d.η_le
  have hW0 : 0 ≤ W := by linarith [d.W_ge]
  have ent : ∀ s t (ι' : Fin 3 × Face L n k 0) (ι : Fin 3 × PositiveEdge L n k 0),
      holonomyDefectAlongBackground L n k z s t ι' ι = holonomyDefectEntry L n k
        (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) ι' ι := by
    intro s t ι' ι
    unfold holonomyDefectAlongBackground
    rw [d.back, Matrix.of_apply, (hA L hL k hk n hn _ (line_opposite d s t)).2.1]
  refine isLocal_of_jetBound hE _ _ _ z θ _ 8 768 768 faceEdgeIncidence d.θ_nonneg
    (by positivity) hS (fun p q hpq s t => ?_) fun p q => ?_
  · rw [ent]
    have h : ∀ i, ¬ q.2 = facePositiveEdge p.2 i := fun i h => hpq ⟨i, h⟩
    simp [holonomyDefectEntry, h]
  · have w₁ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k 0)
      (fineVertexCell p.2.origin)
    have w₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
      (fineVertexCell p.2.origin)
    have hK0 : 0 ≤ 1000000 * (W ^ 2 * E ^ 2) := by positivity
    set m₁ := cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.origin) with hm₁
    set m₂ := cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.origin) with hm₂
    have a₁0 : 0 ≤ finestMesh L k * (W * m₁) := by positivity
    have inner : ∀ i ∈ (Finset.univ : Finset (Fin 4)), JetBound (fun s t => transportSign i *
        (if q.2 = facePositiveEdge p.2 i then
          adjointRotation (s * holonomyAngle (fun b => finestMesh L k * x₁ b) p.2 i +
            t * holonomyAngle (fun b => finestMesh L k * x₂ b) p.2 i) p.1 q.1 -
            (if q.1 = p.1 then 1 else 0) else 0))
        0 (2 * (finestMesh L k * (W * m₁))) (2 * (finestMesh L k * (W * m₂)))
        (4 * ((finestMesh L k * (W * m₁)) * (finestMesh L k * (W * m₂)))) := by
      intro i _
      have h1 := d.angle₁ p.2 i
      have h2 := d.angle₂ p.2 i
      have h3 : JetBound (fun s t => if q.2 = facePositiveEdge p.2 i then
          adjointRotation (s * holonomyAngle (fun b => finestMesh L k * x₁ b) p.2 i +
            t * holonomyAngle (fun b => finestMesh L k * x₂ b) p.2 i) p.1 q.1 -
            (if q.1 = p.1 then 1 else 0) else 0)
          0 (2 * (finestMesh L k * (W * m₁))) (2 * (finestMesh L k * (W * m₂)))
          (4 * ((finestMesh L k * (W * m₁)) * (finestMesh L k * (W * m₂)))) := by
        refine JetBound.ite J _ (fun _ => ?_) le_rfl (by positivity) (by positivity) (by positivity)
        refine (jetBound_adjointRotation_sub J p.1 q.1 _ _ (if q.1 = p.1 then 1 else 0)).mono
          ?_ ?_ ?_ ?_
        · simp
        · linarith
        · linarith
        · have := mul_le_mul h1 h2 (abs_nonneg _) a₁0
          linarith
      have h4 := JetBound.const_mul J (transportSign i) h3
      simpa only [norm_transportSign, one_mul] using h4
    have h5 := JetBound.const_mul J (((finestMesh L k)⁻¹ : ℝ) : ℂ)
      (JetBound.sum_le J Finset.univ 4 (by simp) le_rfl (by positivity) (by positivity)
        (by positivity) inner)
    have n1 : ‖(((finestMesh L k)⁻¹ : ℝ) : ℂ)‖ = (finestMesh L k)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    rw [n1] at h5
    refine JetBound.congr (h5.mono ?_ ?_ ?_ ?_) fun s t => ?_
    · simpa using hK0
    · have e1 : (finestMesh L k)⁻¹ * (((4 : ℕ) : ℝ) * (2 * (finestMesh L k * (W * m₁)))) =
          8 * (W * m₁) := by
        push_cast
        field_simp
        ring
      rw [e1]
      have := mul_le_mul_of_nonneg_right hQ2 w₁
      have h0 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) w₁
      change _ ≤ 1000000 * (W ^ 2 * E ^ 2) * m₁
      nlinarith
    · have e1 : (finestMesh L k)⁻¹ * (((4 : ℕ) : ℝ) * (2 * (finestMesh L k * (W * m₂)))) =
          8 * (W * m₂) := by
        push_cast
        field_simp
        ring
      rw [e1]
      have := mul_le_mul_of_nonneg_right hQ2 w₂
      have h0 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) w₂
      change _ ≤ 1000000 * (W ^ 2 * E ^ 2) * m₂
      nlinarith
    · have e1 : (finestMesh L k)⁻¹ * (((4 : ℕ) : ℝ) *
          (4 * ((finestMesh L k * (W * m₁)) * (finestMesh L k * (W * m₂))))) =
          finestMesh L k * (16 * (W ^ 2 * (m₁ * m₂))) := by
        push_cast
        field_simp
        ring
      rw [e1]
      have hw := mul_nonneg w₁ w₂
      have h2 := mul_le_mul_of_nonneg_right hQ3 hw
      have h3 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) hw
      have h4 : finestMesh L k * (16 * (W ^ 2 * (m₁ * m₂))) ≤ 16 * (W ^ 2 * (m₁ * m₂)) :=
        mul_le_of_le_one_left (by positivity) hη1
      change _ ≤ 1000000 * (W ^ 2 * E ^ 2) * (m₁ * m₂)
      nlinarith
    · rw [ent]
      simp only [holonomyDefectEntry, holonomyAngle_linear]
private theorem isLocal_faceTrace (hE : LocalFamilyOfJetEntries)
    (hA : AbelianFineKernels) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) (d : AngleData L n k z θ W E x₁ x₂)
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Face L n k 0)] [Fintype (Face L n k 0)]
    [DecidableEq (Fin 3 × Face L n k 0)]
    (hS : IsBoundedSparsityOnCells colouredFaceCell colouredFaceCell
      (faceDiagonal (L := L) (n := n) (k := k)) 768 768 8) :
    IsLocalAlongBackground colouredFaceCell colouredFaceCell (faceTraceAlongBackground L n k z) z
      (Real.sqrt (((768 : ℕ) : ℝ) * (768 : ℕ)) * (1000000 * (W ^ 2 * E ^ 2)) * Real.exp (θ * 8))
      θ := by
  classical
  have J := hE.1
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := le_sq_mul_sq d
  have hη := d.η_pos
  have hη1 := d.η_le
  have hW0 : 0 ≤ W := by linarith [d.W_ge]
  have ent : ∀ s t (ι' ι : Fin 3 × Face L n k 0),
      faceTraceAlongBackground L n k z s t ι' ι = faceTraceEntry L n k
        (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) ι' ι := by
    intro s t ι' ι
    unfold faceTraceAlongBackground
    rw [d.back, Matrix.of_apply, (hA L hL k hk n hn _ (line_opposite d s t)).2.2.1]
  refine isLocal_of_jetBound hE _ _ _ z θ _ 8 768 768 faceDiagonal d.θ_nonneg (by positivity) hS
    (fun p q hpq s t => ?_) fun p q => ?_
  · rw [ent]
    have h : ¬ q = p := hpq
    simp [faceTraceEntry, h]
  · have w₁ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k 0)
      (fineVertexCell p.2.origin)
    have w₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
      (fineVertexCell p.2.origin)
    have hK0 : 0 ≤ 1000000 * (W ^ 2 * E ^ 2) := by positivity
    set m₁ := cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.origin) with hm₁
    set m₂ := cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.origin) with hm₂
    have hw := mul_nonneg w₁ w₂
    have hb : JetBound (fun s t => if q = p then
        (Real.cos (s * holonomyAngle (fun b => finestMesh L k * x₁ b) p.2 3 +
          t * holonomyAngle (fun b => finestMesh L k * x₂ b) p.2 3) : ℂ) else 0)
        (1000000 * (W ^ 2 * E ^ 2)) (1000000 * (W ^ 2 * E ^ 2) * m₁)
        (1000000 * (W ^ 2 * E ^ 2) * m₂) (1000000 * (W ^ 2 * E ^ 2) * (m₁ * m₂)) := by
      refine JetBound.ite J _ (fun _ => ?_) hK0 (mul_nonneg hK0 w₁) (mul_nonneg hK0 w₂)
        (mul_nonneg hK0 hw)
      refine (jetBound_cos J _ _).mono ?_ (mul_nonneg hK0 w₁) (mul_nonneg hK0 w₂) ?_
      · nlinarith
      · have h1 := d.angle₁ p.2 3
        have h2 := d.angle₂ p.2 3
        have h3 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        have h5 : (finestMesh L k) ^ 2 ≤ 1 := pow_le_one₀ hη.le hη1
        have h6 : (finestMesh L k) ^ 2 * (W ^ 2 * (m₁ * m₂)) ≤ W ^ 2 * (m₁ * m₂) :=
          mul_le_of_le_one_left (by positivity) h5
        have h7 := mul_le_mul_of_nonneg_right hQ3 hw
        have h8 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) hw
        nlinarith
    refine JetBound.congr hb fun s t => ?_
    rw [ent]
    simp only [faceTraceEntry, holonomyAngle_linear]
private theorem jetBound_curvatureTerm (J : SecondOrderJetClosure) (d : AngleData L n k z θ W E x₁ x₂)
    (p : Face L n k 0) (i j : Fin 4) (a' a : Fin 3) :
    JetBound (fun s t => (((finestMesh L k ^ 2)⁻¹ * Real.sin (holonomyAngle
        (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p 3) : ℝ) : ℂ) *
        (transportSign i * transportSign j) *
        crossThird (fun c => adjointRotation (holonomyAngle
          (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p i) c a')
          (fun c => adjointRotation (holonomyAngle
            (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p j) c a))
      0 (4 * (W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin)))
      (4 * (W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin)))
      (32 * ((W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin)) *
        (W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin)))) := by
  have hη1 := d.η_le
  have hW0 : 0 ≤ W := by linarith [d.W_ge]
  have w₁ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k 0)
    (fineVertexCell p.origin)
  have w₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
    (fineVertexCell p.origin)
  set a₁ := W * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin) with ha₁
  set a₂ := W * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin) with ha₂
  have a₁0 : 0 ≤ a₁ := mul_nonneg hW0 w₁
  have a₂0 : 0 ≤ a₂ := mul_nonneg hW0 w₂
  have A₁ : ∀ l, |holonomyAngle (fun b => finestMesh L k * x₁ b) p l| ≤ a₁ := fun l =>
    (d.angle₁ p l).trans (mul_le_of_le_one_left a₁0 hη1)
  have A₂ : ∀ l, |holonomyAngle (fun b => finestMesh L k * x₂ b) p l| ≤ a₂ := fun l =>
    (d.angle₂ p l).trans (mul_le_of_le_one_left a₂0 hη1)
  have R : ∀ (c b : Fin 3) (l : Fin 4), JetBound (fun s t => adjointRotation
      (s * holonomyAngle (fun b => finestMesh L k * x₁ b) p l +
        t * holonomyAngle (fun b => finestMesh L k * x₂ b) p l) c b)
      1 (2 * a₁) (2 * a₂) (4 * (a₁ * a₂)) := by
    intro c b l
    refine (jetBound_adjointRotation J c b _ _).mono le_rfl ?_ ?_ ?_
    · linarith [A₁ l]
    · linarith [A₂ l]
    · have := mul_le_mul (A₁ l) (A₂ l) (abs_nonneg _) a₁0
      linarith
  have P := ((R 0 a' i).mul J (R 1 a j)).sub J ((R 1 a' i).mul J (R 0 a j))
  have Q := JetBound.const_mul J (transportSign i * transportSign j) (JetBound.const_mul J (-2) P)
  have n1 : ‖transportSign i * transportSign j‖ = 1 := by
    rw [norm_mul, norm_transportSign, norm_transportSign, one_mul]
  have n2 : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [n1, n2] at Q
  have S : JetBound (fun s t => (((finestMesh L k ^ 2)⁻¹ * Real.sin
      (s * holonomyAngle (fun b => finestMesh L k * x₁ b) p 3 +
        t * holonomyAngle (fun b => finestMesh L k * x₂ b) p 3) : ℝ) : ℂ)) 0 a₁ a₂ 0 :=
    (jetBound_smul_sin J _ _ _).mono le_rfl (d.curl₁ p) (d.curl₂ p) le_rfl
  refine JetBound.congr ((S.mul J Q).mono ?_ ?_ ?_ ?_) fun s t => ?_
  · simp
  · apply le_of_eq
    ring
  · apply le_of_eq
    ring
  · apply le_of_eq
    ring
  · simp only [holonomyAngle_linear, crossThird]
    ring
private theorem sum_ite_le_mul {κ : Type} [Fintype κ] (P : κ → Prop) [DecidablePred P] (X : ℝ)
    (hX : 0 ≤ X) (N : ℕ) (hN : Nat.card {p // P p} ≤ N) :
    ∑ p, (if P p then X else 0) ≤ N * X := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hX
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hN
  exact_mod_cast hN
private theorem jetBound_curvatureHalfSum (J : SecondOrderJetClosure)
    (d : AngleData L n k z θ W E x₁ x₂)
    [Fintype (Face L n k 0)] (q : PositiveEdge L n k 0)
    (ι' ι : Fin 3 × PositiveEdge L n k 0) (hq : q = ι'.2 ∨ q = ι.2)
    (hcount : Nat.card {p : Face L n k 0 // ∃ i, facePositiveEdge p i = q} ≤ 64) :
    JetBound (fun s t => curvatureHalfSum L n k
        (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) ι' ι)
      0 (64 * (4 * (4 * (4 * (W * (E * cellDecayWeight θ (cellOfCoords L n k 0)
        (fineVertexCell q.1.source)))))))
      (64 * (4 * (4 * (4 * (W * (E * cellDecayWeight θ (cellOfCoords L n k z)
        (fineVertexCell q.1.source)))))))
      (64 * (4 * (4 * (32 * ((W * (E * cellDecayWeight θ (cellOfCoords L n k 0)
        (fineVertexCell q.1.source))) *
        (W * (E * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell q.1.source)))))))) := by
  classical
  have hW0 : 0 ≤ W := by linarith [d.W_ge]
  have hE0 : 0 ≤ E := by linarith [d.E_ge]
  have w₁ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k 0)
    (fineVertexCell q.1.source)
  have w₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
    (fineVertexCell q.1.source)
  set m₁ := cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell q.1.source) with hm₁
  set m₂ := cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell q.1.source) with hm₂
  have y₁ : 0 ≤ 4 * (W * (E * m₁)) := by positivity
  have y₂ : 0 ≤ 4 * (W * (E * m₂)) := by positivity
  have y₃ : 0 ≤ 32 * ((W * (E * m₁)) * (W * (E * m₂))) := by positivity
  have key : ∀ p ∈ (Finset.univ : Finset (Face L n k 0)),
      JetBound (fun s t => ∑ i : Fin 4, ∑ j ∈ Finset.Ioi i,
        if facePositiveEdge p i = ι'.2 ∧ facePositiveEdge p j = ι.2 then
          (((finestMesh L k ^ 2)⁻¹ * Real.sin (holonomyAngle
            (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p 3) : ℝ) : ℂ) *
            (transportSign i * transportSign j) *
            crossThird (fun c => adjointRotation (holonomyAngle
              (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p i) c ι'.1)
              (fun c => adjointRotation (holonomyAngle
                (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p j) c ι.1)
        else 0)
        0 (if ∃ l, facePositiveEdge p l = q then 4 * (4 * (4 * (W * (E * m₁)))) else 0)
        (if ∃ l, facePositiveEdge p l = q then 4 * (4 * (4 * (W * (E * m₂)))) else 0)
        (if ∃ l, facePositiveEdge p l = q then
          4 * (4 * (32 * ((W * (E * m₁)) * (W * (E * m₂))))) else 0) := by
    intro p _
    by_cases hP : ∃ l, facePositiveEdge p l = q
    · simp only [if_pos hP]
      have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
      have hb := JetBound.sum_le J (V := ((4 : ℕ) : ℝ) * 0)
        (A := ((4 : ℕ) : ℝ) * (4 * (W * (E * m₁)))) (B := ((4 : ℕ) : ℝ) * (4 * (W * (E * m₂))))
        (D := ((4 : ℕ) : ℝ) * (32 * ((W * (E * m₁)) * (W * (E * m₂)))))
        (Finset.univ : Finset (Fin 4)) 4 (by simp) (by simp) (by positivity) (by positivity)
        (by positivity) (G := fun i s t => ∑ j ∈ Finset.Ioi i,
          if facePositiveEdge p i = ι'.2 ∧ facePositiveEdge p j = ι.2 then
          (((finestMesh L k ^ 2)⁻¹ * Real.sin (holonomyAngle
            (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p 3) : ℝ) : ℂ) *
            (transportSign i * transportSign j) *
            crossThird (fun c => adjointRotation (holonomyAngle
              (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p i) c ι'.1)
              (fun c => adjointRotation (holonomyAngle
                (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) p j) c ι.1)
        else 0) (fun i _ => by
          refine JetBound.sum_le J (Finset.Ioi i) 4 ?_ le_rfl y₁ y₂ y₃ fun j _ => ?_
          · exact (Finset.card_le_univ _).trans (by simp)
          · refine JetBound.ite J _ (fun _ => ?_) le_rfl y₁ y₂ y₃
            have n₁ := d.near₁ p q hP
            have n₂ := d.near₂ p q hP
            have v₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
              (fineVertexCell p.origin)
            refine (jetBound_curvatureTerm J d p i j _ _).mono le_rfl ?_ ?_ ?_
            · have := mul_le_mul_of_nonneg_left n₁ hW0
              linarith
            · have := mul_le_mul_of_nonneg_left n₂ hW0
              linarith
            · have h1 := mul_le_mul_of_nonneg_left n₁ hW0
              have h2 := mul_le_mul_of_nonneg_left n₂ hW0
              have h3 := mul_le_mul h1 h2 (mul_nonneg hW0 v₂) (by positivity)
              linarith)
      refine hb.mono (by simp) ?_ ?_ ?_ <;> simp only [e4] <;> exact le_rfl
    · simp only [if_neg hP]
      refine JetBound.congr (JetBound.zero J) fun s t => ?_
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg ?_
      rintro ⟨h1, h2⟩
      rcases hq with e | e
      · exact hP ⟨i, h1.trans e.symm⟩
      · exact hP ⟨j, h2.trans e.symm⟩
  have hs := JetBound.sum J Finset.univ key
  refine JetBound.congr (hs.mono (by simp) ?_ ?_ ?_) fun s t => ?_
  · have := sum_ite_le_mul (fun p : Face L n k 0 => ∃ l, facePositiveEdge p l = q)
      (4 * (4 * (4 * (W * (E * m₁))))) (by positivity) 64 hcount
    simpa using this
  · have := sum_ite_le_mul (fun p : Face L n k 0 => ∃ l, facePositiveEdge p l = q)
      (4 * (4 * (4 * (W * (E * m₂))))) (by positivity) 64 hcount
    simpa using this
  · have := sum_ite_le_mul (fun p : Face L n k 0 => ∃ l, facePositiveEdge p l = q)
      (4 * (4 * (32 * ((W * (E * m₁)) * (W * (E * m₂)))))) (by positivity) 64 hcount
    simpa using this
  · rfl
private theorem isLocal_curvature (hE : LocalFamilyOfJetEntries)
    (hA : AbelianFineKernels) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) (d : AngleData L n k z θ W E x₁ x₂)
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Face L n k 0)] [Fintype (Face L n k 0)]
    [DecidableEq (Fin 3 × PositiveEdge L n k 0)]
    (hS : IsBoundedSparsityOnCells colouredEdgeCell colouredEdgeCell
      (edgesShareFace (L := L) (n := n) (k := k)) 768 768 8)
    (hcount : ∀ q : PositiveEdge L n k 0,
      Nat.card {p : Face L n k 0 // ∃ i, facePositiveEdge p i = q} ≤ 64) :
    IsLocalAlongBackground colouredEdgeCell colouredEdgeCell (curvatureAlongBackground L n k z) z
      (Real.sqrt (((768 : ℕ) : ℝ) * (768 : ℕ)) * (1000000 * (W ^ 2 * E ^ 2)) * Real.exp (θ * 8))
      θ := by
  classical
  have J := hE.1
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := le_sq_mul_sq d
  have ent : ∀ s t (ι' ι : Fin 3 × PositiveEdge L n k 0),
      curvatureAlongBackground L n k z s t ι' ι = (1 / 2 : ℂ) *
        (curvatureHalfSum L n k
          (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) ι' ι +
        curvatureHalfSum L n k
          (fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b)) ι ι') := by
    intro s t ι' ι
    unfold curvatureAlongBackground
    rw [d.back, Matrix.of_apply, (hA L hL k hk n hn _ (line_opposite d s t)).2.2.2]
  have half0 : ∀ (φ : Edge L n k 0 → ℝ) (ι' ι : Fin 3 × PositiveEdge L n k 0),
      ¬ edgesShareFace ι' ι → curvatureHalfSum L n k φ ι' ι = 0 := by
    intro φ ι' ι h
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => if_neg ?_
    rintro ⟨h1, h2⟩
    exact h ⟨p, i, j, h1, h2⟩
  refine isLocal_of_jetBound hE _ _ _ z θ _ 8 768 768 edgesShareFace d.θ_nonneg (by positivity) hS
    (fun p q hpq s t => ?_) fun p q => ?_
  · rw [ent, half0 _ _ _ hpq, half0 _ _ _ fun ⟨r, i, j, h1, h2⟩ => hpq ⟨r, j, i, h2, h1⟩]
    simp
  · have w₁ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k 0)
      (fineVertexCell p.2.1.source)
    have w₂ := cellDecayWeight_nonneg (L := L) (n := n) (k := k) θ (cellOfCoords L n k z)
      (fineVertexCell p.2.1.source)
    have h1 := jetBound_curvatureHalfSum J d p.2 p q (Or.inl rfl) (hcount p.2)
    have h2 := jetBound_curvatureHalfSum J d p.2 q p (Or.inr rfl) (hcount p.2)
    have h3 := JetBound.const_mul J (1 / 2 : ℂ) (h1.add J h2)
    have n1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [n1] at h3
    change JetBound _ _ (_ * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source))
      (_ * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source))
      (_ * (cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source) *
        cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source)))
    set m₁ := cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.2.1.source) with hm₁
    set m₂ := cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.2.1.source) with hm₂
    refine JetBound.congr (h3.mono ?_ ?_ ?_ ?_) fun s t => (ent s t p q).symm
    · have : 0 ≤ 1000000 * (W ^ 2 * E ^ 2) := by positivity
      simpa using this
    · have h4 := mul_le_mul_of_nonneg_right hQ4 w₁
      have h5 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) w₁
      nlinarith
    · have h4 := mul_le_mul_of_nonneg_right hQ4 w₂
      have h5 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) w₂
      nlinarith
    · have hw := mul_nonneg w₁ w₂
      have h5 := mul_nonneg (by positivity : 0 ≤ W ^ 2 * E ^ 2) hw
      have e1 : (W * (E * m₁)) * (W * (E * m₂)) = (W ^ 2 * E ^ 2) * (m₁ * m₂) := by ring
      rw [e1]
      nlinarith
end LocalParts
private theorem cellDecayWeight_le_of_near {L n k : ℕ} (θ : ℝ) (hθ : 0 ≤ θ)
    (hsym : ∀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y' = cellDist y' y)
    (htri : ∀ y y' y'' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y'' ≤ cellDist y y' + cellDist y' y'')
    (y₀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)) (h : cellDist y y' ≤ 4) :
    cellDecayWeight θ y₀ y ≤ Real.exp (4 * θ) * cellDecayWeight θ y₀ y' := by
  unfold cellDecayWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 := htri y' y y₀
  rw [hsym y' y] at h1
  have h2 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left h _)) hθ
  nlinarith
private theorem coeff_opposite_of_form {L n k : ℕ} (v : edgeFormSpace L n k 0)
    (x : Edge L n k 0 → ℝ)
    (hx : ∀ b, (v : Edge L n k 0 → ComplexMatrix2) b = (x b : ℂ) • ComplexMatrix2.pauliFamily 2)
    (b : Edge L n k 0) :
    x b.opposite = -x b := by
  have hp : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := ComplexMatrix2.pauliFamily_apply.2.2
  have h : (v : Edge L n k 0 → ComplexMatrix2) b.opposite = -(v : Edge L n k 0 → ComplexMatrix2) b :=
    v.2.2 b
  rw [hx, hx, hp] at h
  have h0 := congrFun (congrFun h 0) 0
  simp at h0
  exact_mod_cast h0
private theorem abs_holonomyAngle_le {L n k : ℕ} (η Z : ℝ) (hη : 0 ≤ η) (x : Edge L n k 0 → ℝ)
    (p : Face L n k 0) (hZ : ∀ l, |x (faceEdge p l)| ≤ Z) (i : Fin 4) :
    |holonomyAngle (fun b => η * x b) p i| ≤ η * (4 * Z) := by
  have h0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0)
  have e : holonomyAngle (fun b => η * x b) p i = η * holonomyAngle x p i := by
    fin_cases i <;> simp [holonomyAngle] <;> ring
  rw [e, abs_mul, abs_of_nonneg hη]
  refine mul_le_mul_of_nonneg_left ?_ hη
  have b0 := abs_le.1 (hZ 0)
  have b1 := abs_le.1 (hZ 1)
  have b2 := abs_le.1 (hZ 2)
  have b3 := abs_le.1 (hZ 3)
  fin_cases i
  · change |(0 : ℝ)| ≤ _
    simp only [abs_zero]
    linarith
  · change |x (faceEdge p 0)| ≤ _
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · change |x (faceEdge p 0) + x (faceEdge p 1) - x (faceEdge p 2)| ≤ _
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · change |x (faceEdge p 0) + x (faceEdge p 1) - x (faceEdge p 2) -
      x (faceEdge p 3)| ≤ _
    exact abs_le.2 ⟨by linarith, by linarith⟩
private theorem abs_curl_le {L n k : ℕ} (hη : 0 < finestMesh L k) (v : edgeFormSpace L n k 0)
    (x : Edge L n k 0 → ℝ)
    (hx : ∀ b, (v : Edge L n k 0 → ComplexMatrix2) b = (x b : ℂ) • ComplexMatrix2.pauliFamily 2)
    (p : Face L n k 0) (B : ℝ)
    (h : ‖scaledEdgeCoboundary (v : Edge L n k 0 → ComplexMatrix2) p‖ ≤ B) :
    |(finestMesh L k ^ 2)⁻¹ * holonomyAngle (fun b => finestMesh L k * x b) p 3| ≤ B := by
  set S := x (faceEdge p 0) + x (faceEdge p 1) - x (faceEdge p 2) -
    x (faceEdge p 3) with hS
  have e1 : holonomyAngle (fun b => finestMesh L k * x b) p 3 = finestMesh L k * S := by
    change finestMesh L k * x (faceEdge p 0) + finestMesh L k * x (faceEdge p 1) -
      finestMesh L k * x (faceEdge p 2) - finestMesh L k * x (faceEdge p 3) = _
    rw [hS]
    ring
  have e2 : (finestMesh L k ^ 2)⁻¹ * (finestMesh L k * S) = (finestMesh L k)⁻¹ * S := by
    field_simp
  have e3 : scaledEdgeCoboundary (v : Edge L n k 0 → ComplexMatrix2) p =
      (((finestMesh L k)⁻¹ * S : ℝ) : ℂ) • ComplexMatrix2.pauliFamily 2 := by
    change (finestMesh L k)⁻¹ • ((v : Edge L n k 0 → ComplexMatrix2) (faceEdge p 0) +
      (v : Edge L n k 0 → ComplexMatrix2) (faceEdge p 1) -
      (v : Edge L n k 0 → ComplexMatrix2) (faceEdge p 2) -
      (v : Edge L n k 0 → ComplexMatrix2) (faceEdge p 3)) = _
    rw [hx, hx, hx, hx, hS]
    ext i j
    simp
    ring
  rw [e1, e2]
  rw [e3] at h
  exact abs_le_of_norm_smul_pauli _ _ h
private theorem twoSourceBackground_eq {L n k : ℕ} (z : Fin 4 → ℤ) (x₁ x₂ : Edge L n k 0 → ℝ)
    (h₁ : ∀ b, (periodicResponse L n k (pauliUnitForm L n k 0) : Edge L n k 0 → ComplexMatrix2) b =
      (x₁ b : ℂ) • ComplexMatrix2.pauliFamily 2)
    (h₂ : ∀ b, (periodicResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → ComplexMatrix2) b =
      (x₂ b : ℂ) • ComplexMatrix2.pauliFamily 2)
    (a₁ : ∀ b : Edge L n k 0, x₁ b.opposite = -x₁ b)
    (a₂ : ∀ b : Edge L n k 0, x₂ b.opposite = -x₂ b)
    (s t : ℝ) : twoSourceBackground L n k z s t =
      abelianGaugeField fun b => s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b) := by
  classical
  have hA : ∀ b : Edge L n k 0,
      ((s : ℂ) • (meshScaledResponse L n k (pauliUnitForm L n k 0) : Edge L n k 0 → ComplexMatrix2) +
        (t : ℂ) • (meshScaledResponse L n k (pauliUnitForm L n k z) :
          Edge L n k 0 → ComplexMatrix2)) b =
      ((s * (finestMesh L k * x₁ b) + t * (finestMesh L k * x₂ b) : ℝ) : ℂ) •
        ComplexMatrix2.pauliFamily 2 := by
    intro b
    change (s : ℂ) • (finestMesh L k • (periodicResponse L n k (pauliUnitForm L n k 0) :
      Edge L n k 0 → ComplexMatrix2) b) + (t : ℂ) • (finestMesh L k • (periodicResponse L n k
      (pauliUnitForm L n k z) : Edge L n k 0 → ComplexMatrix2) b) = _
    rw [h₁, h₂]
    ext i j
    simp
    ring
  funext b
  unfold twoSourceBackground PeriodicLattice.expTwist
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb, mul_one]
    rw [hA, matExp_smul_pauli_diag]
    rfl
  · simp only [if_neg hb, mul_one]
    rw [hA, matExp_smul_pauli_diag, diagExpAngle_inv]
    simp only [abelianGaugeField, a₁, a₂]
    congr 1
    ring
theorem fineOperatorPartsAreLocal_of_decay (hD : UnitFormResponseDecays)
    (hE : LocalFamilyOfJetEntries)
    (hR : FinePartRelationsSparse)
    (hC : NeighbouringFineVertexCells) (hA : AbelianFineKernels) :
    FineOperatorPartsAreLocal := by
  intro L hL
  obtain ⟨C, θ, hC0, hθ, hdec⟩ := hD L hL
  set E := Real.exp (4 * θ) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set W := 1 + 4 * (C * E) with hWdef
  have hCE : 0 ≤ C * E := by positivity
  have hW1 : 1 ≤ W := by linarith
  have hCW : C ≤ W := by nlinarith
  refine ⟨Real.sqrt (((768 : ℕ) : ℝ) * (768 : ℕ)) * (1000000 * (W ^ 2 * E ^ 2)) *
    Real.exp (θ * 8), θ, by positivity, hθ, fun k hk => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hdec k hk
  refine ⟨n₀, fun n h1 h2 => ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ z
  have : Finite (Face L n k 0) :=
    Finite.of_injective (fun p => ((0 : Fin 3), p)) fun a b h => (Prod.ext_iff.1 h).2
  let _ : Fintype (Face L n k 0) := Fintype.ofFinite _
  obtain ⟨a₁, a₂, a₃⟩ := hn₀ n h1 h2 0
  obtain ⟨b₁, b₂, b₃⟩ := hn₀ n h1 h2 z
  choose x₁ hx₁ using a₃
  choose x₂ hx₂ using b₃
  obtain ⟨hsym, htri, -, -⟩ := hC L hL n k
  obtain ⟨s₁, s₂, s₃, s₄, hcount, hbond⟩ := hR L hL n k
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hη : 0 < finestMesh L k := zpow_pos hL0 _
  have hη1 : finestMesh L k ≤ 1 := by
    unfold finestMesh meshAt
    exact zpow_le_one_of_nonpos₀ hL1 (by simp)
  have anti₁ := coeff_opposite_of_form _ x₁ hx₁
  have anti₂ := coeff_opposite_of_form _ x₂ hx₂
  have xb₁ : ∀ b : Edge L n k 0,
      |x₁ b| ≤ C * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell b.source) := fun b =>
    abs_le_of_norm_smul_pauli _ _ (by rw [← hx₁]; exact a₁ b)
  have xb₂ : ∀ b : Edge L n k 0,
      |x₂ b| ≤ C * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell b.source) := fun b =>
    abs_le_of_norm_smul_pauli _ _ (by rw [← hx₂]; exact b₁ b)
  have wn : ∀ (y₀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)),
      cellDist y y' ≤ 4 → cellDecayWeight θ y₀ y ≤ E * cellDecayWeight θ y₀ y' :=
    fun y₀ y y' h => cellDecayWeight_le_of_near θ hθ.le hsym htri y₀ y y' h
  have zb₁ : ∀ (p : Face L n k 0) (l : Fin 4), |x₁ (faceEdge p l)| ≤
      C * (E * cellDecayWeight θ (cellOfCoords L n k 0) (fineVertexCell p.origin)) := fun p l =>
    (xb₁ _).trans (mul_le_mul_of_nonneg_left (wn _ _ _ (hbond p l)) hC0.le)
  have zb₂ : ∀ (p : Face L n k 0) (l : Fin 4), |x₂ (faceEdge p l)| ≤
      C * (E * cellDecayWeight θ (cellOfCoords L n k z) (fineVertexCell p.origin)) := fun p l =>
    (xb₂ _).trans (mul_le_mul_of_nonneg_left (wn _ _ _ (hbond p l)) hC0.le)
  have wt : ∀ y₀ y : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      0 ≤ cellDecayWeight θ y₀ y :=
    fun y₀ y => cellDecayWeight_nonneg θ y₀ y
  have d : AngleData L n k z θ W E x₁ x₂ :=
    { η_pos := hη
      η_le := hη1
      θ_nonneg := hθ.le
      W_ge := hW1
      E_ge := hE1
      anti := fun b => by simp only [anti₁, anti₂, mul_neg, and_self]
      back := twoSourceBackground_eq z x₁ x₂ hx₁ hx₂ anti₁ anti₂
      bond₁ := fun b => (xb₁ b.1).trans (mul_le_mul_of_nonneg_right hCW (wt _ _))
      bond₂ := fun b => (xb₂ b.1).trans (mul_le_mul_of_nonneg_right hCW (wt _ _))
      angle₁ := fun p i => by
        refine (abs_holonomyAngle_le _ _ hη.le x₁ p (zb₁ p) i).trans
          (mul_le_mul_of_nonneg_left ?_ hη.le)
        have := mul_nonneg hCE (wt (cellOfCoords L n k 0) (fineVertexCell p.origin))
        have := wt (cellOfCoords L n k 0) (fineVertexCell p.origin)
        nlinarith
      angle₂ := fun p i => by
        refine (abs_holonomyAngle_le _ _ hη.le x₂ p (zb₂ p) i).trans
          (mul_le_mul_of_nonneg_left ?_ hη.le)
        have := mul_nonneg hCE (wt (cellOfCoords L n k z) (fineVertexCell p.origin))
        have := wt (cellOfCoords L n k z) (fineVertexCell p.origin)
        nlinarith
      curl₁ := fun p => (abs_curl_le hη _ x₁ hx₁ p _ (a₂ p)).trans
        (mul_le_mul_of_nonneg_right hCW (wt _ _))
      curl₂ := fun p => (abs_curl_le hη _ x₂ hx₂ p _ (b₂ p)).trans
        (mul_le_mul_of_nonneg_right hCW (wt _ _))
      near₁ := fun p q ⟨l, hl⟩ => by
        refine wn _ _ _ ?_
        rw [hsym, ← hl]
        exact hbond p l
      near₂ := fun p q ⟨l, hl⟩ => by
        refine wn _ _ _ ?_
        rw [hsym, ← hl]
        exact hbond p l }
  exact ⟨isLocal_covariantDifference hE hA hL hk h2 d s₁, isLocal_holonomyDefect hE hA hL hk h2 d s₂,
    isLocal_faceTrace hE hA hL hk h2 d s₃, isLocal_curvature hE hA hL hk h2 d s₄ hcount⟩
end YangMills.Construction.RunningCouplingSlope
end
