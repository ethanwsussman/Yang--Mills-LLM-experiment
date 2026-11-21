import YangMills.Construction.Lattice.CombSchemeGaugeLawAndConjugationProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStep
import YangMills.Construction.Lattice.MeanSchemeAtSmallPlaquettes
import YangMills.Construction.Lattice.PathRearrangement
import YangMills.Construction.Lattice.SpreadOfAContourFamily
import YangMills.Construction.Lattice.ValuesOfTheTwoSchemes
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.SingleStepEstimate
open YangMills.Construction.Matrices
theorem det_isUnit_of_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) : IsUnit A.det := by
  rw [(Matrix.mem_specialUnitaryGroup_iff.1 hA).2]
  exact isUnit_one
theorem mul_inv_cancel_of_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) : A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem inv_mem_of_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) : A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem one_mem_compactGaugeGroup : (1 : ComplexMatrix2) ∈ compactGaugeGroup :=
  show (1 : ComplexMatrix2) ∈ ComplexMatrix2.specialUnitary from one_mem _
theorem mul_mem_of_mem {A B : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) (hB : B ∈ compactGaugeGroup) :
    A * B ∈ compactGaugeGroup :=
  show A * B ∈ ComplexMatrix2.specialUnitary from mul_mem hA hB
theorem mem_unitaryGroup_of_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hA).1
theorem conj_sub_one_le (hON : ComplexMatrix2.OperatorNormUnderConjugation)
    {V V' A A' C T : ComplexMatrix2} (hV' : V' ∈ compactGaugeGroup) (hC : C ∈ compactGaugeGroup)
    (hT : T ∈ compactGaugeGroup)
    {a b : ℝ} (h : ComplexMatrix2.operatorNorm (A * C - T * A') ≤ a)
    (h₁ : ComplexMatrix2.operatorNorm (A - V) ≤ b)
    (h₂ : ComplexMatrix2.operatorNorm (A' - V') ≤ b) :
    ComplexMatrix2.operatorNorm (V * C * V'⁻¹ * T⁻¹ - 1) ≤ a + 2 * b := by
  have hone : (1 : ComplexMatrix2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := one_mem _
  have hinv : T * V' * (V'⁻¹ * T⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc V', mul_inv_cancel_of_mem hV', one_mul, mul_inv_cancel_of_mem hT]
  have e₀ : V * C * V'⁻¹ * T⁻¹ - 1 = 1 * (V * C - T * V') * (V'⁻¹ * T⁻¹) := by
    rw [one_mul, sub_mul, hinv]
    simp only [mul_assoc]
  have hv : V'⁻¹ * T⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mem_unitaryGroup_of_mem (mul_mem_of_mem (inv_mem_of_mem hV') (inv_mem_of_mem hT))
  rw [e₀, hON.1 _ 1 _ hone hv]
  have e₁ : V * C - T * V' = (A * C - T * A') - 1 * (A - V) * C + T * (A' - V') * 1 := by
    simp only [one_mul, mul_one, sub_mul, mul_sub]
    abel
  have n₁ : ComplexMatrix2.operatorNorm (1 * (A - V) * C) = ComplexMatrix2.operatorNorm (A - V) :=
    hON.1 _ 1 _ hone (mem_unitaryGroup_of_mem hC)
  have n₂ : ComplexMatrix2.operatorNorm (T * (A' - V') * 1) = ComplexMatrix2.operatorNorm (A' - V') :=
    hON.1 _ _ 1 (mem_unitaryGroup_of_mem hT) hone
  rw [e₁]
  have t₁ := norm_add_le ((A * C - T * A') - 1 * (A - V) * C) (T * (A' - V') * 1)
  have t₂ := norm_sub_le (A * C - T * A') (1 * (A - V) * C)
  simp only [ComplexMatrix2.operatorNorm] at *
  linarith
theorem logSeries_norm_le (hA : ComplexMatrix2.SpecialUnitaryAngleBounds) {X : ComplexMatrix2}
    (hX : X ∈ compactGaugeGroup) (h : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries X) ≤
      Real.pi / 2 * ComplexMatrix2.operatorNorm (X - 1) := by
  obtain ⟨a₁, a₂, -, -, a₅, -⟩ := hA.2.1 X hX
  have hne : X ≠ -1 := by
    intro hX1
    have hz : ComplexMatrix2.operatorNorm (X + 1) = 0 := by
      rw [hX1]
      simp [ComplexMatrix2.operatorNorm]
    rw [hz] at a₂
    have hs := Real.sin_sq_add_cos_sq (ComplexMatrix2.rotationAngle X / 2)
    have hc : Real.cos (ComplexMatrix2.rotationAngle X / 2) = 0 := by linarith
    have hn : 0 ≤ ComplexMatrix2.operatorNorm (X - 1) := norm_nonneg _
    have hlt : Real.sin (ComplexMatrix2.rotationAngle X / 2) ^ 2 < 1 :=
      pow_lt_one₀ (by linarith) (by linarith) (by norm_num)
    rw [hc] at hs
    linarith
  have hD : X ∈ ComplexMatrix2.unitaryLogDomain := ⟨hX, hne⟩
  obtain ⟨h₁, h₂, h₃⟩ := hA.2.2.2.1 X hD
  have e : ComplexMatrix2.logSeries X = Complex.I • ComplexMatrix2.unitaryLieLog X :=
    (h₃ (h₂.1 h)).symm
  have hn : ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries X) =
      ComplexMatrix2.rotationAngle X := by
    rw [e, ← h₁]
    show ‖Complex.I • ComplexMatrix2.unitaryLieLog X‖ = _
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn]
  calc ComplexMatrix2.rotationAngle X =
        Real.pi / 2 * (2 / Real.pi * ComplexMatrix2.rotationAngle X) := by field_simp
    _ ≤ Real.pi / 2 * ComplexMatrix2.operatorNorm (X - 1) :=
        mul_le_mul_of_nonneg_left a₅ (by positivity)
section Preliminaries
variable {L m : ℕ} {j : ℤ}
def wordSum (s : StepWord L m j) : Site L m j :=
  (s.map fun u : UnitStepVec L m j => (u : Site L m j)).sum
@[simp] theorem wordSum_nil : wordSum ([] : StepWord L m j) = 0 := rfl
@[simp] theorem wordSum_cons (a : UnitStepVec L m j) (s : StepWord L m j) :
    wordSum (a :: s) = (a : Site L m j) + wordSum s := by
  simp [wordSum]
@[simp] theorem wordSum_append (s t : StepWord L m j) :
    wordSum (s ++ t) = wordSum s + wordSum t := by
  simp [wordSum]
theorem pathOfWord_append (z : Site L m j) (s t : StepWord L m j) :
    pathOfWord z (s ++ t) = pathOfWord z s ++ pathOfWord (z + wordSum s) t := by
  induction s generalizing z with
  | nil => simp [pathOfWord]
  | cons a s ih => simp [pathOfWord, ih, add_assoc]
theorem pathHolonomy_append (U : Bond L m j → ComplexMatrix2) (Γ Γ' : List (Bond L m j)) :
    pathHolonomy U (Γ ++ Γ') = pathHolonomy U Γ * pathHolonomy U Γ' := by
  simp [pathHolonomy]
theorem pathHolonomy_mem {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hc : IsGaugeField compactGaugeGroup ℬ U) {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, b ∈ ℬ) :
    pathHolonomy U Γ ∈ compactGaugeGroup := by
  induction Γ with
  | nil => exact one_mem_compactGaugeGroup
  | cons b Γ ih =>
    have e : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by simp [pathHolonomy]
    rw [e]
    exact mul_mem_of_mem (hc.1 _ (h b (by simp))) (ih fun b' hb' => h b' (by simp [hb']))
theorem exists_word {Γ : List (Bond L m j)} : ∀ {z x : Site L m j}, IsBondPathFromTo Γ z x →
    ∃ 𝔞 : StepWord L m j, pathOfWord z 𝔞 = Γ ∧ z + wordSum 𝔞 = x := by
  induction Γ with
  | nil =>
    intro z x h
    exact ⟨[], rfl, by simpa using h.2.1 rfl⟩
  | cons b Γ ih =>
    intro z x h
    obtain ⟨hp, -, hz, hx⟩ := h
    have hb : b.source = z := hz b (by simp)
    subst hb
    have hrest : IsBondPathFromTo Γ b.target x := by
      refine ⟨hp.tail, fun hΓ => ?_, fun b' hb' => ?_, fun b' hb' => ?_⟩
      · subst hΓ
        exact hx b (by simp)
      · cases Γ with
        | nil => simp at hb'
        | cons b'' Γ =>
          have e : b'' = b' := by simpa using hb'
          subst e
          exact (List.isChain_cons_cons.1 hp).1.symm
      · cases Γ with
        | nil => simp at hb'
        | cons b'' Γ => exact hx b' (by simpa [List.getLast?_cons_cons] using hb')
    obtain ⟨𝔞, h₁, h₂⟩ := ih hrest
    let s : UnitStepVec L m j := ⟨b.target - b.source, b.isNeighbour⟩
    have e : b.source + (s : Site L m j) = b.target := by
      show b.source + (b.target - b.source) = b.target
      abel
    refine ⟨s :: 𝔞, ?_, ?_⟩
    · have hs : pathOfWord b.source (s :: 𝔞) =
          bondOfStep b.source s :: pathOfWord (b.source + (s : Site L m j)) 𝔞 := rfl
      rw [hs, e, h₁]
      exact congrArg₂ _ (Bond.ext rfl e) rfl
    · rw [wordSum_cons, ← add_assoc, e, h₂]
theorem prefix_mem_pathSites (z : Site L m j) (𝔞 : StepWord L m j) :
    ∀ A : StepWord L m j, A <+: 𝔞 → z + wordSum A ∈ sitesOfPath z (pathOfWord z 𝔞) := by
  induction 𝔞 generalizing z with
  | nil =>
    intro A hA
    obtain rfl := List.prefix_nil.1 hA
    simp [sitesOfPath]
  | cons s 𝔞 ih =>
    intro A hA
    rcases List.prefix_cons_iff.1 hA with rfl | ⟨t, rfl, ht⟩
    · simp [sitesOfPath]
    · have h := ih (z + s) t ht
      rw [wordSum_cons, ← add_assoc]
      simp only [sitesOfPath, pathOfWord, List.map_cons, List.mem_cons] at h ⊢
      right
      simpa [bondOfStep] using h
theorem translatePath_pathOfWord (a : Site L m j) (z : Site L m j) (𝔞 : StepWord L m j) :
    translatePath (pathOfWord z 𝔞) a = pathOfWord (z + a) 𝔞 := by
  induction 𝔞 generalizing z with
  | nil => rfl
  | cons s 𝔞 ih =>
    have h := ih (z + s)
    simp only [translatePath, pathOfWord, List.map_cons] at h ⊢
    rw [h, add_right_comm]
    exact congrArg₂ _ (Bond.ext rfl (add_right_comm _ _ _)) rfl
def positiveStep (L m : ℕ) (j : ℤ) (ν : Fin 4) : UnitStepVec L m j :=
  ⟨unitStep L m j ν, ν, Or.inl rfl⟩
theorem pathOfWord_replicate (z : Site L m j) (ν : Fin 4) (k : ℕ) :
    pathOfWord z (List.replicate k (positiveStep L m j ν)) = forwardAxisPath z ν k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, pathOfWord, ih]
    rfl
theorem wordSum_replicate (ν : Fin 4) (k : ℕ) :
    wordSum (List.replicate k (positiveStep L m j ν)) = (k : ℤ) • unitStep L m j ν := by
  simp [wordSum, positiveStep, List.map_replicate, List.sum_replicate]
inductive Interleaving (e : UnitStepVec L m j) :
    StepWord L m j → ℕ → StepWord L m j → Prop
  | nil : Interleaving e [] 0 []
  | keep (a : UnitStepVec L m j) {𝔞 : StepWord L m j} {k : ℕ} {𝔰 : StepWord L m j} :
      Interleaving e 𝔞 k 𝔰 → Interleaving e (a :: 𝔞) k (a :: 𝔰)
  | insert {𝔞 : StepWord L m j} {k : ℕ} {𝔰 : StepWord L m j} :
      Interleaving e 𝔞 k 𝔰 → Interleaving e 𝔞 (k + 1) (e :: 𝔰)
namespace Interleaving
variable {e : UnitStepVec L m j}
theorem of_eq {a a' s s' : StepWord L m j} {k k' : ℕ} (h : Interleaving e a k s) (ha : a = a')
    (hk : k = k') (hs : s = s') : Interleaving e a' k' s' := by
  subst ha hk hs
  exact h
theorem append {a₁ a₂ s₁ s₂ : StepWord L m j} {k₁ k₂ : ℕ} (h₁ : Interleaving e a₁ k₁ s₁)
    (h₂ : Interleaving e a₂ k₂ s₂) : Interleaving e (a₁ ++ a₂) (k₁ + k₂) (s₁ ++ s₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | keep a _ ih => exact keep a ih
  | insert _ ih =>
    rw [Nat.add_right_comm]
    exact insert ih
theorem self (a : StepWord L m j) : Interleaving e a 0 a := by
  induction a with
  | nil => exact nil
  | cons s a ih => exact keep s ih
theorem copies (k : ℕ) : Interleaving e [] k (List.replicate k e) := by
  induction k with
  | zero => exact nil
  | succ k ih => exact insert ih
theorem prefix_wordSum {𝔞 𝔰 : StepWord L m j} {k : ℕ} (h : Interleaving e 𝔞 k 𝔰) :
    ∀ P : StepWord L m j, P <+: 𝔰 → ∃ A : StepWord L m j, A <+: 𝔞 ∧ ∃ r : ℕ, r ≤ k ∧
      wordSum P = wordSum A + r • (e : Site L m j) := by
  induction h with
  | nil =>
    intro P hP
    obtain rfl := List.prefix_nil.1 hP
    exact ⟨[], List.nil_prefix, 0, le_rfl, by simp⟩
  | keep a _ ih =>
    intro P hP
    rcases List.prefix_cons_iff.1 hP with rfl | ⟨t, rfl, ht⟩
    · exact ⟨[], List.nil_prefix, 0, Nat.zero_le _, by simp⟩
    · obtain ⟨A, hA, r, hr, e₁⟩ := ih t ht
      refine ⟨a :: A, (List.prefix_cons_inj a).2 hA, r, hr, ?_⟩
      rw [wordSum_cons, wordSum_cons, e₁, add_assoc]
  | insert _ ih =>
    intro P hP
    rcases List.prefix_cons_iff.1 hP with rfl | ⟨t, rfl, ht⟩
    · exact ⟨[], List.nil_prefix, 0, Nat.zero_le _, by simp⟩
    · obtain ⟨A, hA, r, hr, e₁⟩ := ih t ht
      refine ⟨A, hA, r + 1, by omega, ?_⟩
      rw [wordSum_cons, e₁, add_smul, one_smul]
      abel
end Interleaving
section Moves
variable (e : UnitStepVec L m j) (𝔞 : StepWord L m j) (N : ℕ)
  (H : StepWord L m j → ComplexMatrix2) (w : UnitStepVec L m j → ℝ)
theorem move_one
    (Hex : ∀ (𝔲 : StepWord L m j) (s : UnitStepVec L m j) (𝔳 : StepWord L m j),
      Interleaving e 𝔞 N (𝔲 ++ s :: e :: 𝔳) → Interleaving e 𝔞 N (𝔲 ++ e :: s :: 𝔳) →
      ComplexMatrix2.operatorNorm (H (𝔲 ++ s :: e :: 𝔳) - H (𝔲 ++ e :: s :: 𝔳)) ≤ w s)
    (𝔟 : StepWord L m j) :
    ∀ (𝔞₁ 𝔞₂ 𝔲 𝔳 : StepWord L m j) (i l : ℕ), 𝔞₁ ++ 𝔟 ++ 𝔞₂ = 𝔞 →
      Interleaving e 𝔞₁ i 𝔲 → Interleaving e 𝔞₂ l 𝔳 → i + 1 + l = N →
      ComplexMatrix2.operatorNorm (H (𝔲 ++ 𝔟 ++ e :: 𝔳) - H (𝔲 ++ e :: 𝔟 ++ 𝔳)) ≤
        (𝔟.map w).sum := by
  induction 𝔟 with
  | nil =>
    intro 𝔞₁ 𝔞₂ 𝔲 𝔳 i l _ _ _ _
    simp
  | cons s 𝔟 ih =>
    intro 𝔞₁ 𝔞₂ 𝔲 𝔳 i l ha h₁ h₂ hN
    have hi := ih (𝔞₁ ++ [s]) 𝔞₂ (𝔲 ++ [s]) 𝔳 i l (by simpa using ha)
      ((h₁.append (Interleaving.keep s Interleaving.nil)).of_eq rfl (by omega) rfl) h₂ hN
    have mid : Interleaving e 𝔞 N (𝔲 ++ s :: e :: (𝔟 ++ 𝔳)) :=
      (h₁.append ((Interleaving.keep s Interleaving.nil).append
        ((Interleaving.insert (Interleaving.nil (e := e))).append
          ((Interleaving.self 𝔟).append h₂)))).of_eq
          (by simpa using ha) (by omega) (by simp)
    have top : Interleaving e 𝔞 N (𝔲 ++ e :: s :: (𝔟 ++ 𝔳)) :=
      (h₁.append ((Interleaving.insert (Interleaving.nil (e := e))).append
        ((Interleaving.keep s Interleaving.nil).append
          ((Interleaving.self 𝔟).append h₂)))).of_eq
          (by simpa using ha) (by omega) (by simp)
    have hx := Hex 𝔲 s (𝔟 ++ 𝔳) mid top
    have e₁ : 𝔲 ++ [s] ++ 𝔟 ++ e :: 𝔳 = 𝔲 ++ s :: 𝔟 ++ e :: 𝔳 := by simp
    have e₂ : 𝔲 ++ [s] ++ e :: 𝔟 ++ 𝔳 = 𝔲 ++ s :: e :: (𝔟 ++ 𝔳) := by simp
    have e₃ : 𝔲 ++ e :: s :: 𝔟 ++ 𝔳 = 𝔲 ++ e :: s :: (𝔟 ++ 𝔳) := by simp
    rw [e₁, e₂] at hi
    rw [e₃, List.map_cons, List.sum_cons]
    have t := norm_sub_le_norm_sub_add_norm_sub (H (𝔲 ++ s :: 𝔟 ++ e :: 𝔳))
      (H (𝔲 ++ s :: e :: (𝔟 ++ 𝔳))) (H (𝔲 ++ e :: s :: (𝔟 ++ 𝔳)))
    simp only [ComplexMatrix2.operatorNorm] at *
    linarith
theorem move_all
    (Hex : ∀ (𝔲 : StepWord L m j) (s : UnitStepVec L m j) (𝔳 : StepWord L m j),
      Interleaving e 𝔞 N (𝔲 ++ s :: e :: 𝔳) → Interleaving e 𝔞 N (𝔲 ++ e :: s :: 𝔳) →
      ComplexMatrix2.operatorNorm (H (𝔲 ++ s :: e :: 𝔳) - H (𝔲 ++ e :: s :: 𝔳)) ≤ w s)
    (i : ℕ) : ∀ l : ℕ, i + l = N →
      ComplexMatrix2.operatorNorm (H (𝔞 ++ List.replicate N e) -
        H (List.replicate i e ++ 𝔞 ++ List.replicate l e)) ≤ (i : ℝ) * (𝔞.map w).sum := by
  induction i with
  | zero =>
    intro l hl
    obtain rfl : l = N := by omega
    simp
  | succ i ih =>
    intro l hl
    have h₁ := ih (l + 1) (by omega)
    have h₂ := move_one e 𝔞 N H w Hex 𝔞 [] [] (List.replicate i e) (List.replicate l e) i l
      (by simp) (Interleaving.copies i) (Interleaving.copies l) (by omega)
    rw [List.replicate_succ] at h₁
    have e₁ : List.replicate (i + 1) e ++ 𝔞 ++ List.replicate l e =
        List.replicate i e ++ e :: 𝔞 ++ List.replicate l e := by
      rw [List.replicate_succ']
      simp
    rw [e₁]
    have t := norm_sub_le_norm_sub_add_norm_sub (H (𝔞 ++ List.replicate N e))
      (H (List.replicate i e ++ 𝔞 ++ e :: List.replicate l e))
      (H (List.replicate i e ++ e :: 𝔞 ++ List.replicate l e))
    push_cast
    simp only [ComplexMatrix2.operatorNorm] at *
    linarith
end Moves
theorem boundaryBonds_mem_bondsInside {D : Set (FourTorus L m)} {p : Plaquette L m j}
    (hp : p ∈ plaquettesInside D) : ∀ b ∈ p.boundaryBonds, b ∈ bondsInside D := by
  have c₁ := hp p.origin (by simp [Plaquette.vertices])
  have c₂ := hp (p.origin + unitStep L m j p.firstAxis) (by simp [Plaquette.vertices])
  have c₃ := hp (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
    (by simp [Plaquette.vertices])
  have c₄ := hp (p.origin + unitStep L m j p.secondAxis) (by simp [Plaquette.vertices])
  have c₃' : ((p.origin + unitStep L m j p.secondAxis + unitStep L m j p.firstAxis : Site L m j) :
      FourTorus L m) ∈ D := by
    rw [add_right_comm]
    exact c₃
  intro b hb
  simp only [Plaquette.boundaryBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨c₁, c₂⟩
  · exact ⟨c₂, c₃⟩
  · exact ⟨c₃', c₄⟩
  · exact ⟨c₄, c₁⟩
theorem pathOfWord_mem_bondsInside {D : Set (FourTorus L m)} (𝔰 : StepWord L m j) :
    ∀ z : Site L m j,
    (∀ P : StepWord L m j, P <+: 𝔰 → ((z + wordSum P : Site L m j) : FourTorus L m) ∈ D) →
    ∀ b ∈ pathOfWord z 𝔰, b ∈ bondsInside D := by
  induction 𝔰 with
  | nil => intro z _ b hb; simp [pathOfWord] at hb
  | cons s 𝔰 ih =>
    intro z h b hb
    rw [pathOfWord, List.mem_cons] at hb
    rcases hb with rfl | hb
    · refine ⟨?_, ?_⟩
      · simpa [bondOfStep] using h [] List.nil_prefix
      · simpa [bondOfStep] using h [s] (by simp)
    · refine ih (z + s) (fun P hP => ?_) b hb
      have := h (s :: P) ((List.prefix_cons_inj s).2 hP)
      rwa [wordSum_cons, ← add_assoc] at this
theorem map_sum_eq_wordSum (l : StepWord L m j) :
    (l.map fun s => (s : Site L m j)).sum = wordSum l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordSum_cons, ← ih]
    rfl
theorem swap_bound (hR : PathRearrangementBound) (hodd : Odd L) (h13 : 13 ≤ L)
    (hm : 0 < m) (hj : -(m : ℤ) ≤ j) {D : Set (FourTorus L m)} {U : Bond L m j → ComplexMatrix2}
    {ω : ℝ}
    (hU : IsGaugeField compactGaugeGroup (bondsInside D) U)
    (hω : ∀ p ∈ (plaquettesInside D : Set (Plaquette L m j)),
      ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤ ω) (hω0 : 0 ≤ ω)
    (z : Site L m j) (𝔲 𝔳 : StepWord L m j) (s t : UnitStepVec L m j)
    (h₁ : ∀ P : StepWord L m j, P <+: 𝔲 ++ s :: t :: 𝔳 →
      ((z + wordSum P : Site L m j) : FourTorus L m) ∈ D)
    (h₂ : ∀ P : StepWord L m j, P <+: 𝔲 ++ t :: s :: 𝔳 →
      ((z + wordSum P : Site L m j) : FourTorus L m) ∈ D) :
    ComplexMatrix2.operatorNorm
        (wordHolonomy U z (𝔲 ++ s :: t :: 𝔳) - wordHolonomy U z (𝔲 ++ t :: s :: 𝔳)) ≤ ω ∧
      ((t : Site L m j) = s ∨ (t : Site L m j) = -(s : Site L m j) →
        wordHolonomy U z (𝔲 ++ s :: t :: 𝔳) = wordHolonomy U z (𝔲 ++ t :: s :: 𝔳)) := by
  classical
  let ex : AdjacentSwap L m j := ⟨𝔲, s, t, 𝔳⟩
  have hb₁ : ∀ b ∈ pathOfWord z ex.original, b ∈ bondsInside D :=
    pathOfWord_mem_bondsInside _ z h₁
  have hb₂ : ∀ b ∈ pathOfWord z ex.swapped, b ∈ bondsInside D :=
    pathOfWord_mem_bondsInside _ z h₂
  have hRR := hR L m hodd h13 hm j hj (bondsInside D) U (fun b hb => ⟨hb.2, hb.1⟩) hU z
  have hone := hRR.1 ex hb₁ hb₂
  refine ⟨?_, fun hpar => hone.1 hpar⟩
  by_cases hpar : ex.IsCollinear
  · have e₀ := hone.1 hpar
    have e₁ : wordHolonomy U z (𝔲 ++ s :: t :: 𝔳) = wordHolonomy U z (𝔲 ++ t :: s :: 𝔳) := e₀
    rw [e₁, sub_self]
    simpa [ComplexMatrix2.operatorNorm] using hω0
  · obtain ⟨p, hp⟩ := (hone.2 hpar).1
    have hstart : ex.cornerSite z = z + wordSum 𝔲 := by
      simp only [AdjacentSwap.cornerSite, ex]
      rw [map_sum_eq_wordSum]
    have q₁ := h₁ 𝔲 (by simp)
    have q₂ := h₁ (𝔲 ++ [s]) (by simp)
    have q₃ := h₂ (𝔲 ++ [t]) (by simp)
    have q₄ := h₁ (𝔲 ++ [s, t]) (by simp)
    have hpD : p ∈ (plaquettesInside D : Set (Plaquette L m j)) := by
      intro w hw
      have hw' : w ∈ ({ex.cornerSite z, ex.cornerSite z + ex.fst, ex.cornerSite z + ex.snd,
          ex.cornerSite z + ex.fst + ex.snd} : Set (Site L m j)) := by
        rw [← hp]
        exact hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
      rcases hw' with rfl | rfl | rfl | rfl
      · rw [hstart]
        exact q₁
      · have e₂ : ex.cornerSite z + ex.fst = z + wordSum (𝔲 ++ [s]) := by
          simp [hstart, ex, add_assoc]
        rw [e₂]
        exact q₂
      · have e₂ : ex.cornerSite z + ex.snd = z + wordSum (𝔲 ++ [t]) := by
          simp [hstart, ex, add_assoc]
        rw [e₂]
        exact q₃
      · have e₂ : ex.cornerSite z + ex.fst + ex.snd = z + wordSum (𝔲 ++ [s, t]) := by
          simp [hstart, ex, add_assoc]
        rw [e₂]
        exact q₄
    have hchain := (hRR.2 1 ![ex.original, ex.swapped] (fun _ => ex) (fun _ => p)
      (fun l => by
        obtain rfl := Subsingleton.elim l 0
        exact ⟨rfl, rfl⟩)
      (fun l => by
        refine Fin.cases ?_ (fun l' => ?_) l
        · exact hb₁
        · obtain rfl := Subsingleton.elim l' 0
          exact hb₂)
      (fun _ _ => ⟨hp, boundaryBonds_mem_bondsInside hpD⟩)).2
    have hsum : (∑ l ∈ Finset.univ.filter (fun _ : Fin 1 => ¬ ex.IsCollinear),
        ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1)) =
          ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) := by
      simp [hpar]
    rw [hsum] at hchain
    exact hchain.trans (hω p hpD)
def Transverse (ν : Fin 4) (d : Site L m j) : Prop :=
  ¬(d = unitStep L m j ν ∨ d = -unitStep L m j ν)
open Classical in
def transverseCount (ν : Fin 4) (Γ : List (Bond L m j)) : ℕ :=
  Γ.countP fun b => decide (Transverse ν (b.target - b.source))
open Classical in
def transverseWeight (ν : Fin 4) (ω : ℝ) (s : UnitStepVec L m j) : ℝ :=
  if Transverse ν (s : Site L m j) then ω else 0
open Classical in
theorem transverseCount_cons (ν : Fin 4) (b : Bond L m j) (Γ : List (Bond L m j)) :
    transverseCount ν (b :: Γ) =
      transverseCount ν Γ + if Transverse ν (b.target - b.source) then 1 else 0 := by
  simp [transverseCount, List.countP_cons]
theorem sum_transverseWeight (ν : Fin 4) (ω : ℝ) (𝔞 : StepWord L m j) (z : Site L m j) :
    (𝔞.map (transverseWeight ν ω)).sum = (transverseCount ν (pathOfWord z 𝔞) : ℝ) * ω := by
  classical
  induction 𝔞 generalizing z with
  | nil => simp [transverseCount, pathOfWord]
  | cons s 𝔞 ih =>
    have hd : (bondOfStep z s).target - (bondOfStep z s).source = (s : Site L m j) := by
      simp [bondOfStep]
    rw [List.map_cons, List.sum_cons, ih (z + s), pathOfWord, transverseCount_cons, hd]
    unfold transverseWeight
    split_ifs <;> push_cast <;> ring
open Classical in
theorem transverseCount_le (ν : Fin 4) (S : Finset (Fin 4)) (f : Fin 4 → Site L m j)
    (Γ : List (Bond L m j))
    (hcover : ∀ b ∈ Γ, Transverse ν (b.target - b.source) →
      ∃ μ ∈ S, b.target - b.source = f μ) :
    transverseCount ν Γ ≤ ∑ μ ∈ S, countSteps Γ (f μ) := by
  induction Γ with
  | nil => simp [transverseCount]
  | cons b Γ ih =>
    have ih' := ih fun b' hb' => hcover b' (List.mem_cons_of_mem _ hb')
    have hstep : ∀ κ, countSteps (b :: Γ) (f κ) =
        countSteps Γ (f κ) + if b.target - b.source = f κ then 1 else 0 := by
      intro κ
      simp [countSteps, List.countP_cons]
    by_cases hN : Transverse ν (b.target - b.source)
    · obtain ⟨μ, hμ, he⟩ := hcover b (by simp) hN
      rw [transverseCount_cons, if_pos hN]
      have h₁ : countSteps (b :: Γ) (f μ) = countSteps Γ (f μ) + 1 := by rw [hstep, if_pos he]
      have h₂ : ∑ κ ∈ S.erase μ, countSteps Γ (f κ) ≤
          ∑ κ ∈ S.erase μ, countSteps (b :: Γ) (f κ) :=
        Finset.sum_le_sum fun κ _ => by rw [hstep]; omega
      have a₁ : countSteps Γ (f μ) + ∑ κ ∈ S.erase μ, countSteps Γ (f κ) =
          ∑ κ ∈ S, countSteps Γ (f κ) :=
        Finset.add_sum_erase S (fun κ => countSteps Γ (f κ)) hμ
      have a₂ : countSteps (b :: Γ) (f μ) + ∑ κ ∈ S.erase μ, countSteps (b :: Γ) (f κ) =
          ∑ κ ∈ S, countSteps (b :: Γ) (f κ) :=
        Finset.add_sum_erase S (fun κ => countSteps (b :: Γ) (f κ)) hμ
      omega
    · rw [transverseCount_cons, if_neg hN]
      exact ih'.trans (Finset.sum_le_sum fun κ _ => by rw [hstep]; omega)
end Preliminaries
section Levels
variable {L m : ℕ} {j j' : ℤ}
theorem doubleBlockCurvature_nonneg (W : Bond L m j' → ComplexMatrix2) (c : Bond L m j) :
    0 ≤ doubleBlockCurvature W c :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem plaquette_le_doubleBlockCurvature (hA : ComplexMatrix2.SpecialUnitaryAngleBounds)
    {c : Bond L m j} {W : Bond L m j' → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W) {p : Plaquette L m j'}
    (hp : p ∈ (plaquettesInside (bondDoubleBlock c) : Set (Plaquette L m j'))) :
    ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) ≤ doubleBlockCurvature W c := by
  refine le_ciSup (f := fun q : ↥(doubleBlockPlaquettes c : Set (Plaquette L m j')) =>
    ComplexMatrix2.operatorNorm (plaquetteHolonomy W q.1 - 1)) ⟨2, ?_⟩ ⟨p, hp⟩
  rintro _ ⟨q, rfl⟩
  have hq : plaquetteHolonomy W q.1 ∈ compactGaugeGroup :=
    pathHolonomy_mem hW (boundaryBonds_mem_bondsInside (D := bondDoubleBlock c) q.2)
  have h₁ := (hA.2.1 _ hq).1
  have h₂ := Real.sin_le_one (ComplexMatrix2.rotationAngle (plaquetteHolonomy W q.1) / 2)
  show ComplexMatrix2.operatorNorm (plaquetteHolonomy W q.1 - 1) ≤ 2
  rw [h₁]
  linarith
theorem exists_offset {w : Site L m j'} {Q : Set (Fin 4 → ℤ)} {R : Set (FourTorus L m)}
    (h : IsParametrizedBy w Q R) {x : Site L m j'} (hx : (x : FourTorus L m) ∈ R) :
    ∃ p ∈ Q, x = offsetSite w p := by
  rw [← h.2] at hx
  obtain ⟨p, hp, e⟩ := hx
  exact ⟨p, hp, Subtype.ext e.symm⟩
variable {K n : ℕ}
structure Hypotheses (c : BondAtLevel L m K (n + 1)) (ν : Fin 4)
    (W : BondAtLevel L m K n → ComplexMatrix2) : Prop where
  odd : Odd L
  large : 13 ≤ L
  mpos : 0 < m
  lt : n < K
  angles : ComplexMatrix2.SpecialUnitaryAngleBounds
  gauge : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W
  param : IsParametrizedBy (c.source.toSublattice (levelDepth K n)) (blockIndexBox L)
    (unitBlock c.source)
  tailPaths : ∀ p ∈ blockIndexBox L,
    ContourCoordinates c.source (offsetSite (c.source.toSublattice (levelDepth K n)) p) p ∧
    CornerCombCoordinates c.source (offsetSite (c.source.toSublattice (levelDepth K n)) p) p
  coordDB : DoubleBlockCoordinates (levelDepth K n) c ν
  shifts : ContoursAndCombsTranslate (levelDepth K n) c ν
  axial : DoubleBlockAxialPaths (levelDepth K n) c ν
  inside : PathsInsideDoubleBlock (levelDepth K n) c
variable {c : BondAtLevel L m K (n + 1)} {ν : Fin 4} {W : BondAtLevel L m K n → ComplexMatrix2}
theorem crossingPath_bound (hR : PathRearrangementBound) (S : Hypotheses c ν W)
    {z x : SiteAtLevel L m K n} {Γ : List (BondAtLevel L m K n)} (hΓ : IsBondPathFromTo Γ z x)
    (hsites : ∀ w ∈ sitesOfPath z Γ, (w : FourTorus L m) ∈ unitBlock c.source)
    (hcount : transverseCount ν Γ ≤ 3 * (L - 1)) :
    ComplexMatrix2.operatorNorm (pathHolonomy W Γ * pathHolonomy W (crossingPath c x) -
      pathHolonomy W (crossingPath c z) *
        pathHolonomy W (translatePath Γ (blockTranslation L m (levelDepth K n) ν))) ≤
      3 * (L : ℝ) * ((L : ℝ) - 1) * doubleBlockCurvature W c := by
  classical
  obtain ⟨𝔞, rfl, hx⟩ := exists_word hΓ
  have hL : 1 ≤ L := by
    have := S.large
    omega
  have hω0 : 0 ≤ doubleBlockCurvature W c := doubleBlockCurvature_nonneg W c
  have hgood : ∀ 𝔰 : StepWord L m (levelDepth K n),
      Interleaving (positiveStep L m (levelDepth K n) ν) 𝔞 L 𝔰 →
      ∀ P : StepWord L m (levelDepth K n),
      P <+: 𝔰 → ((z + wordSum P : SiteAtLevel L m K n) : FourTorus L m) ∈ bondDoubleBlock c := by
    intro 𝔰 h𝔰 P hPfx
    obtain ⟨A, hA, r, hr, e₁⟩ := h𝔰.prefix_wordSum P hPfx
    have hw : z + wordSum A ∈ sitesInBlock (levelDepth K n) c.source :=
      hsites _ (prefix_mem_pathSites z 𝔞 A hA)
    have h := (S.axial.1 _ hw).2.2.2 r hr
    have e₂ : z + wordSum P = z + wordSum A + (r : ℤ) • unitStep L m (levelDepth K n) ν := by
      rw [e₁, add_assoc, natCast_zsmul]
      rfl
    rw [e₂]
    exact h
  have hj : -(m : ℤ) ≤ levelDepth K n := by
    have := S.lt
    simp only [levelDepth]
    omega
  have Hex : ∀ (𝔲 : StepWord L m (levelDepth K n)) (s : UnitStepVec L m (levelDepth K n))
      (𝔳 : StepWord L m (levelDepth K n)),
      Interleaving (positiveStep L m (levelDepth K n) ν) 𝔞 L
        (𝔲 ++ s :: positiveStep L m (levelDepth K n) ν :: 𝔳) →
      Interleaving (positiveStep L m (levelDepth K n) ν) 𝔞 L
        (𝔲 ++ positiveStep L m (levelDepth K n) ν :: s :: 𝔳) →
      ComplexMatrix2.operatorNorm
        (wordHolonomy W z (𝔲 ++ s :: positiveStep L m (levelDepth K n) ν :: 𝔳) -
          wordHolonomy W z (𝔲 ++ positiveStep L m (levelDepth K n) ν :: s :: 𝔳)) ≤
        transverseWeight ν (doubleBlockCurvature W c) s := by
    intro 𝔲 s 𝔳 h₁ h₂
    obtain ⟨b₁, b₂⟩ := swap_bound hR S.odd S.large S.mpos hj (D := bondDoubleBlock c) S.gauge
      (fun p hp => plaquette_le_doubleBlockCurvature S.angles S.gauge hp) hω0 z 𝔲 𝔳 s
      (positiveStep L m (levelDepth K n) ν) (hgood _ h₁) (hgood _ h₂)
    unfold transverseWeight
    split_ifs with hN
    · exact b₁
    · have hp : ((positiveStep L m (levelDepth K n) ν : UnitStepVec L m (levelDepth K n)) :
          SiteAtLevel L m K n) = s ∨
          ((positiveStep L m (levelDepth K n) ν : UnitStepVec L m (levelDepth K n)) :
          SiteAtLevel L m K n) = -(s : SiteAtLevel L m K n) := by
        rcases not_not.1 hN with e | e
        · exact Or.inl e.symm
        · refine Or.inr ?_
          rw [e, neg_neg]
          rfl
      rw [b₂ hp, sub_self]
      simp [ComplexMatrix2.operatorNorm]
  have hch := move_all (positiveStep L m (levelDepth K n) ν) 𝔞 L (wordHolonomy W z)
    (transverseWeight ν (doubleBlockCurvature W c)) Hex L 0 (by simp)
  simp only [List.replicate_zero, List.append_nil] at hch
  rw [sum_transverseWeight ν _ 𝔞 z] at hch
  have hzmem : z ∈ sitesInBlock (levelDepth K n) c.source := hsites z (by simp [sitesOfPath])
  have hxmem : x ∈ sitesInBlock (levelDepth K n) c.source := by
    have h := hsites _ (prefix_mem_pathSites z 𝔞 𝔞 List.prefix_rfl)
    rw [hx] at h
    exact h
  have e₁ : wordHolonomy W z (𝔞 ++ List.replicate L (positiveStep L m (levelDepth K n) ν)) =
      pathHolonomy W (pathOfWord z 𝔞) * pathHolonomy W (crossingPath c x) := by
    rw [wordHolonomy, pathOfWord_append, pathHolonomy_append, hx, pathOfWord_replicate,
      (S.axial.1 x hxmem).2.1]
  have e₂ : wordHolonomy W z (List.replicate L (positiveStep L m (levelDepth K n) ν) ++ 𝔞) =
      pathHolonomy W (crossingPath c z) *
        pathHolonomy W (translatePath (pathOfWord z 𝔞) (blockTranslation L m (levelDepth K n) ν)) := by
    rw [wordHolonomy, pathOfWord_append, pathHolonomy_append, pathOfWord_replicate,
      ← (S.axial.1 z hzmem).2.1, wordSum_replicate, translatePath_pathOfWord]
    rfl
  rw [e₁, e₂] at hch
  refine hch.trans ?_
  have hc : (transverseCount ν (pathOfWord z 𝔞) : ℝ) ≤ 3 * ((L : ℝ) - 1) := by
    have h : ((transverseCount ν (pathOfWord z 𝔞) : ℕ) : ℝ) ≤ ((3 * (L - 1) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    rw [Nat.cast_mul, Nat.cast_sub hL] at h
    simpa using h
  have hLpos : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  calc (L : ℝ) * ((transverseCount ν (pathOfWord z 𝔞) : ℝ) * doubleBlockCurvature W c)
      ≤ (L : ℝ) * ((3 * ((L : ℝ) - 1)) * doubleBlockCurvature W c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hω0) hLpos
    _ = 3 * (L : ℝ) * ((L : ℝ) - 1) * doubleBlockCurvature W c := by ring
theorem localDefect_cornered (hON : ComplexMatrix2.OperatorNormUnderConjugation)
    (hR : PathRearrangementBound) (S : Hypotheses c ν W) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) c.source) :
    ComplexMatrix2.operatorNorm (localDefect .cornered W c x - 1) ≤
      3 * (L : ℝ) * ((L : ℝ) - 1) * doubleBlockCurvature W c := by
  obtain ⟨p, hp, hxp⟩ := exists_offset S.param hx
  have hcomb := (S.tailPaths p hp).2
  rw [← hxp] at hcomb
  obtain ⟨-, -, hpath, hsteps, hform, hsites, -⟩ := hcomb
  have hL : 1 ≤ L := by
    have := S.large
    omega
  have hcount : transverseCount ν (coordinateComb (blockAnchor (levelDepth K n) c.source) x) ≤
      3 * (L - 1) := by
    refine (transverseCount_le ν (Finset.univ.erase ν) (unitStep L m (levelDepth K n)) _ ?_).trans ?_
    · intro b hb hN
      obtain ⟨μ, he⟩ := hform b hb
      refine ⟨μ, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, he⟩
      rintro rfl
      exact hN (Or.inl he)
    · refine (Finset.sum_le_card_nsmul _ _ (L - 1) fun μ _ => ?_).trans ?_
      · have h := hsteps μ
        rw [h.1]
        have := h.2
        omega
      · rw [Finset.card_erase_of_mem (Finset.mem_univ ν), Finset.card_univ, Fintype.card_fin]
        simp
  have hb := crossingPath_bound hR S hpath hsites hcount
  have hzmem : blockAnchor (levelDepth K n) c.source ∈ sitesInBlock (levelDepth K n) c.source :=
    hsites _ (by simp [sitesOfPath])
  have hx' : x + blockTranslation L m (levelDepth K n) ν ∈
      sitesInBlock (levelDepth K n) c.target := by
    rw [← S.coordDB.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hT : baseTransport .cornered W c =
      pathHolonomy W (crossingPath c (blockAnchor (levelDepth K n) c.source)) := congrArg (pathHolonomy W) S.axial.2.2
  have hA' : contourHolonomy .cornered W c.target (shiftAcross c x) =
      pathHolonomy W (translatePath (coordinateComb (blockAnchor (levelDepth K n) c.source) x)
        (blockTranslation L m (levelDepth K n) ν)) := by
    show pathHolonomy W (coordinateComb (schemeBaseSite .cornered _ c.target) (shiftAcross c x)) = _
    rw [S.coordDB.2.2.2.2.1 x hx, (S.shifts x hx).2]
  have hA'mem : pathHolonomy W (translatePath
      (coordinateComb (blockAnchor (levelDepth K n) c.source) x)
      (blockTranslation L m (levelDepth K n) ν)) ∈ compactGaugeGroup := by
    rw [(S.shifts x hx).2]
    exact pathHolonomy_mem S.gauge (S.inside.1 c.target (Or.inr rfl) _ hx').2
  have hC : pathHolonomy W (crossingPath c x) ∈ compactGaugeGroup :=
    pathHolonomy_mem S.gauge (S.inside.2 x hx)
  have hTmem : pathHolonomy W (crossingPath c (blockAnchor (levelDepth K n) c.source)) ∈
      compactGaugeGroup :=
    pathHolonomy_mem S.gauge (S.inside.2 _ hzmem)
  have h := conj_sub_one_le hON
    (V := pathHolonomy W (coordinateComb (blockAnchor (levelDepth K n) c.source) x))
    hA'mem hC hTmem hb (a := _) (b := 0) (by simp [ComplexMatrix2.operatorNorm])
    (by simp [ComplexMatrix2.operatorNorm])
  have hA : contourHolonomy .cornered W c.source x =
      pathHolonomy W (coordinateComb (blockAnchor (levelDepth K n) c.source) x) := rfl
  unfold localDefect
  rw [hT, hA', hA]
  simpa using h
theorem localDefect_centred (hON : ComplexMatrix2.OperatorNormUnderConjugation)
    (hR : PathRearrangementBound) (S : Hypotheses c ν W)
    (hAngle : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ Γ ∈ contourSet y x,
        ComplexMatrix2.operatorNorm (pathHolonomy W Γ * (contourHolonomy .centred W y x)⁻¹ - 1) ≤
          Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c)
    (hmem : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomy .centred W y x ∈ compactGaugeGroup)
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) c.source) :
    ComplexMatrix2.operatorNorm (localDefect .centred W c x - 1) ≤
      3 * (L : ℝ) * ((L : ℝ) - 1) * doubleBlockCurvature W c +
        2 * (Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c) := by
  obtain ⟨p, hp, hxp⟩ := exists_offset S.param hx
  have hcont := (S.tailPaths p hp).1
  rw [← hxp] at hcont
  have hL : 1 ≤ L := by
    have := S.large
    omega
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ ∈ contourSet c.source x :=
    ⟨_, (offsetAxes c.source x).equivFin.symm, rfl⟩
  obtain ⟨hpath, hcnt, hform, hsites, -⟩ := hcont Γ hΓ
  have hcount : transverseCount ν Γ ≤ 3 * (L - 1) := by
    refine (transverseCount_le ν ((Finset.univ.erase ν).filter fun μ => p μ ≠ 0)
      (fun μ => (p μ).sign • unitStep L m (levelDepth K n) μ) _ ?_).trans ?_
    · intro b hb hN
      obtain ⟨μ, h0, he⟩ := hform b hb
      refine ⟨μ, Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, h0⟩, he⟩
      rintro rfl
      rcases lt_or_gt_of_ne h0 with h | h
      · rw [Int.sign_eq_neg_one_of_neg h] at he
        exact hN (Or.inr (by simpa using he))
      · rw [Int.sign_eq_one_of_pos h] at he
        exact hN (Or.inl (by simpa using he))
    · refine (Finset.sum_le_card_nsmul _ _ (L - 1) fun μ hμ => ?_).trans ?_
      · have h := hcnt μ (Finset.mem_filter.1 hμ).2
        rw [h.1]
        have h₂ := h.2
        unfold centreToFaceSteps at h₂
        rw [Int.abs_eq_natAbs] at h₂
        omega
      · have hc : ((Finset.univ.erase ν).filter fun μ => p μ ≠ 0).card ≤ 3 := by
          refine (Finset.card_filter_le _ _).trans ?_
          rw [Finset.card_erase_of_mem (Finset.mem_univ ν), Finset.card_univ, Fintype.card_fin]
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ hc
  have hb := crossingPath_bound hR S hpath hsites hcount
  have hzmem : c.source.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) c.source :=
    hsites _ (by simp [sitesOfPath])
  have hx' : x + blockTranslation L m (levelDepth K n) ν ∈
      sitesInBlock (levelDepth K n) c.target := by
    rw [← S.coordDB.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hΓ' : translatePath Γ (blockTranslation L m (levelDepth K n) ν) ∈
      contourSet c.target (x + blockTranslation L m (levelDepth K n) ν) := by
    rw [← (S.shifts x hx).1]
    exact ⟨Γ, hΓ, rfl⟩
  have hT : baseTransport .centred W c =
      pathHolonomy W (crossingPath c (c.source.toSublattice (levelDepth K n))) :=
    congrArg (pathHolonomy W) S.axial.2.1
  have hA : pathHolonomy W Γ ∈ compactGaugeGroup :=
    pathHolonomy_mem S.gauge ((S.inside.1 c.source (Or.inl rfl) x hx).1 Γ hΓ)
  have hA' : pathHolonomy W (translatePath Γ (blockTranslation L m (levelDepth K n) ν)) ∈
      compactGaugeGroup :=
    pathHolonomy_mem S.gauge ((S.inside.1 c.target (Or.inr rfl) _ hx').1 _ hΓ')
  have hC : pathHolonomy W (crossingPath c x) ∈ compactGaugeGroup :=
    pathHolonomy_mem S.gauge (S.inside.2 x hx)
  have hTmem : pathHolonomy W (crossingPath c (c.source.toSublattice (levelDepth K n))) ∈
      compactGaugeGroup :=
    pathHolonomy_mem S.gauge (S.inside.2 _ hzmem)
  have hV := hmem c.source (Or.inl rfl) x hx
  have hV' := hmem c.target (Or.inr rfl) _ hx'
  have d₁ : ComplexMatrix2.operatorNorm (pathHolonomy W Γ - contourHolonomy .centred W c.source x) ≤
      Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c := by
    rw [← hON.2.2.2.1 _ _ (mem_unitaryGroup_of_mem hA) (mem_unitaryGroup_of_mem hV)]
    exact hAngle c.source (Or.inl rfl) x hx Γ hΓ
  have d₂ : ComplexMatrix2.operatorNorm
      (pathHolonomy W (translatePath Γ (blockTranslation L m (levelDepth K n) ν)) -
        contourHolonomy .centred W c.target (x + blockTranslation L m (levelDepth K n) ν)) ≤
      Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c := by
    rw [← hON.2.2.2.1 _ _ (mem_unitaryGroup_of_mem hA') (mem_unitaryGroup_of_mem hV')]
    exact hAngle c.target (Or.inr rfl) _ hx' _ hΓ'
  unfold localDefect
  rw [hT, S.coordDB.2.2.2.2.1 x hx]
  exact conj_sub_one_le hON hV' hC hTmem hb d₁ d₂
end Levels
theorem singleStepBounds (hA : ComplexMatrix2.SpecialUnitaryAngleBounds)
    (hON : ComplexMatrix2.OperatorNormUnderConjugation)
    (hP : BlockPaths.Statement) (hR : PathRearrangementBound)
    (hV : SchemeValuesInGaugeGroup) (hMS : CentredSchemeAtSmallCurvature.Statement)
    (hSp : ContourFamilySpread) :
    SingleStepBounds := by
  intro L hL m K n hm hn c hc s W hW hsmall
  obtain ⟨ν, hν⟩ := id hc
  obtain ⟨hsite, hbond⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨hDB, -, hTr, hSt, hIn⟩ := hbond c ν hν
  obtain ⟨hBlk, -, hpts⟩ := hsite c.source
  have S : Hypotheses c ν W := ⟨hL.1, hL.2, hm, hn, hA, hW, hBlk.1, hpts, hDB, hTr, hSt, hIn⟩
  obtain ⟨mDom, mOne, mEq, -, -⟩ :=
    hMS L hL m K n hm hn c hc W hW (lt_of_lt_of_le hsmall (min_le_left _ _))
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hκ1 : 0 ≤ Averaging.SingleStep.loopAngleConstant L := by
    unfold Averaging.SingleStep.loopAngleConstant
    positivity
  have hκ0 : 0 < 3 * (L : ℝ) * ((L : ℝ) - 1) := by
    have h₁ : 0 < (L : ℝ) - 1 := by linarith
    have h₂ : 0 < (L : ℝ) := by linarith
    positivity
  have hκ2 : 0 < Averaging.SingleStep.loopVariableConstant L := by
    unfold Averaging.SingleStep.loopVariableConstant
    linarith
  have hω0 := doubleBlockCurvature_nonneg W c
  have hsm : Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c < 1 := by
    have h := mul_lt_mul_of_pos_left (lt_of_lt_of_le hsmall (min_le_right _ _)) hκ2
    rwa [mul_inv_cancel₀ hκ2.ne'] at h
  have hsub : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      unitBlock y ⊆ bondDoubleBlock c := by
    rintro y (rfl | rfl)
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have hconfy : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      IsGaugeField compactGaugeGroup (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)) W :=
    fun y hy => ⟨fun b hb => hW.1 b ⟨hsub y hy hb.1, hsub y hy hb.2⟩,
      fun b hb => hW.2 b ⟨hsub y hy hb.1, hsub y hy hb.2⟩⟩
  have hpair : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := by
    rintro y (rfl | rfl) <;> simp
  have hangle : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ Γ ∈ contourSet y x,
        ComplexMatrix2.rotationAngle (pathHolonomy W Γ * (contourHolonomy .centred W y x)⁻¹) ≤
            Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c ∧
          ComplexMatrix2.operatorNorm
              (pathHolonomy W Γ * (contourHolonomy .centred W y x)⁻¹ - 1) ≤
            Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c := by
    intro y hy x hx Γ hΓ
    have h := hSp L m K hL hm n hn y W (hconfy y hy) x hx
    obtain ⟨a₂, a₃, a₄⟩ := (h.2.2 (mOne y (hpair y hy) x hx)).2 Γ hΓ
    rw [mEq y (hpair y hy) x hx]
    have hrad : blockPlaquetteDefect y W ≤ doubleBlockCurvature W c :=
      Real.iSup_le (fun p => plaquette_le_doubleBlockCurvature hA hW
        (fun w hw => hsub y hy (p.2 w hw))) hω0
    have hb : ComplexMatrix2.rotationAngle (pathHolonomy W Γ * (meanContourHolonomy W y x)⁻¹) ≤
        Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c :=
      a₃.trans (a₄.le.trans (mul_le_mul_of_nonneg_left hrad hκ1))
    exact ⟨hb, a₂.trans hb⟩
  have hel : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ComplexMatrix2.operatorNorm (localDefect s W c x - 1) ≤
        Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c := by
    intro x hx
    cases s with
    | centred =>
      have hvals := (hV L hL m K n hm hn .centred c hc W mDom hW).1
      have h := localDefect_centred hON hR S (fun y hy x hx Γ hΓ => (hangle y hy x hx Γ hΓ).2)
        (fun y hy x hx => hvals y (hpair y hy) x hx) hx
      refine h.trans (le_of_eq ?_)
      unfold Averaging.SingleStep.loopVariableConstant
      ring
    | cornered =>
      refine (localDefect_cornered hON hR S hx).trans ?_
      unfold Averaging.SingleStep.loopVariableConstant
      nlinarith [mul_nonneg hκ1 hω0]
  have hcomplex : ∀ ℬ : Set (BondAtLevel L m K n), IsGaugeField compactGaugeGroup ℬ W →
      IsGaugeField complexGaugeGroup ℬ W :=
    fun ℬ h => ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.1 (h.1 b hb)).2, h.2⟩
  have hdom : IsSchemeAverageDefined s W c := by
    cases s with
    | centred => exact mDom
    | cornered =>
      have hcv : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
          ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined .cornered W y x := by
        intro y hy x hx
        unfold IsContourHolonomyDefined
        exact ⟨hx, hcomplex _ (hconfy y hy), trivial⟩
      unfold IsSchemeAverageDefined AreContourHolonomiesDefined
      exact ⟨hcomplex _ hW, ⟨hcv _ (Or.inl rfl), hcv _ (Or.inr rfl)⟩,
        fun x hx => lt_of_le_of_lt (hel x hx) hsm⟩
  obtain ⟨vC, vE, vX, vA⟩ := hV L hL m K n hm hn s c hc W hdom hW
  refine ⟨hdom, vC, vA, fun y hy x hx Γ hΓ => ?_, hel, ?_⟩
  · have hy' : y = c.source ∨ y = c.target := by simpa using hy
    exact (hangle y hy' x hx Γ hΓ).1
  obtain ⟨Y, hY, hXY⟩ := vX
  refine ⟨Y, hY, ?_, ?_⟩
  · have hLne : L ≠ 0 := by
      have := hL.2
      omega
    have hfinB : (unitBlock c.source).Finite := by
      refine Set.finite_of_ncard_ne_zero ?_
      rw [hBlk.2.1]
      exact pow_ne_zero _ hLne
    have hB : (sitesInBlock (levelDepth K n) c.source).Finite :=
      hfinB.preimage Subtype.val_injective.injOn
    have hcard : (sitesInBlock (levelDepth K n) c.source).ncard ≤ L ^ 4 := by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, ← hBlk.2.1]
      refine Set.ncard_le_ncard ?_ hfinB
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hMnn : 0 ≤ Real.pi / 2 *
        (Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c) := by
      have := Real.pi_pos
      have := mul_nonneg hκ2.le hω0
      positivity
    have hM : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
        ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries (localDefect s W c x)) ≤
          Real.pi / 2 *
            (Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c) :=
      fun x hx =>
      (logSeries_norm_le hA (vE x hx) (lt_of_le_of_lt (hel x hx) hsm)).trans
        (mul_le_mul_of_nonneg_left (hel x hx) (by have := Real.pi_pos; positivity))
    have hsum : ComplexMatrix2.operatorNorm (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
        ComplexMatrix2.logSeries (localDefect s W c x)) ≤ (L : ℝ) ^ 4 * (Real.pi / 2 *
          (Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hB]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun x hx => hM x (hB.mem_toFinset.1 hx)).trans ?_
      rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hB]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hMnn
    have e₁ : ComplexMatrix2.operatorNorm Y = ComplexMatrix2.operatorNorm
        (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          ComplexMatrix2.logSeries (localDefect s W c x)) := by
      rw [hXY]
      show ‖Y‖ = ‖Complex.I • Y‖
      rw [norm_smul, Complex.norm_I, one_mul]
    have hLpos : (0 : ℝ) < L := by linarith
    have hw : ‖inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
      unfold inverseFourthPowerWeight
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), zpow_neg]
      norm_cast
    rw [e₁]
    show ‖inverseFourthPowerWeight L • _‖ ≤ _
    rw [norm_smul, hw]
    calc ((L : ℝ) ^ 4)⁻¹ * ‖∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          ComplexMatrix2.logSeries (localDefect s W c x)‖
        ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * (Real.pi / 2 *
          (Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Averaging.SingleStep.meanLogConstant L * doubleBlockCurvature W c := by
          unfold Averaging.SingleStep.meanLogConstant
          field_simp
  · simp only [schemeBlockAverage, if_pos hc, positiveBondAverage]
    rw [hXY]
end YangMills.Construction.PeriodicLattice.SingleStepEstimate
