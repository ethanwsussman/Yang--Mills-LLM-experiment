import YangMills.Construction.Towers.IsometriesOfATowerAreHypercubicMotionsProof
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints.ReflectionsPlaneFacts
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
theorem coordVec_apply (μ i : Fin 4) :
    coordVec μ i = if i = μ then 1 else 0 := by
  simp [PeriodicLattice.coordVec, Pi.single_apply]
theorem inv_sqrt_two_pow_two : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num
theorem sqrt_two_inv_ne_zero : (Real.sqrt 2)⁻¹ ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact inv_ne_zero this
theorem unitSign_sq {ε : ℝ} (h : IsUnitSign ε) : ε ^ 2 = 1 := by
  rcases h with rfl | rfl <;> norm_num
theorem unitSign_ne_zero {ε : ℝ} (h : IsUnitSign ε) : ε ≠ 0 := by
  rcases h with rfl | rfl <;> norm_num
theorem signedAxis_apply (μ : Fin 4) (ε : ℝ) (i : Fin 4) :
    signedAxis μ ε i = if i = μ then ε else 0 := by
  simp [signedAxis, coordVec_apply]
theorem signedDiagonal_apply (μ ν : Fin 4) (ε ε' : ℝ) (i : Fin 4) :
    signedDiagonal μ ν ε ε' i =
      (Real.sqrt 2)⁻¹ * ((if i = μ then ε else 0) + (if i = ν then ε' else 0)) := by
  simp [signedDiagonal, coordVec_apply]
theorem neg_signedAxis (μ : Fin 4) (ε : ℝ) : -signedAxis μ ε = signedAxis μ (-ε) := by
  simp [signedAxis]
theorem neg_signedDiagonal (μ ν : Fin 4) (ε ε' : ℝ) :
    -signedDiagonal μ ν ε ε' = signedDiagonal μ ν (-ε) (-ε') := by
  funext i
  simp only [Pi.neg_apply, signedDiagonal_apply]
  split_ifs <;> ring
theorem euclidNorm_signedAxis (μ : Fin 4) {ε : ℝ} (h : IsUnitSign ε) :
    euclidNorm (signedAxis μ ε) = 1 := by
  have hs : ∑ i, signedAxis μ ε i ^ 2 = 1 := by
    simp only [signedAxis_apply]
    simp [ite_pow, Finset.sum_ite_eq', unitSign_sq h]
  rw [euclidNorm, hs, Real.sqrt_one]
theorem euclidNorm_signedDiagonal {μ ν : Fin 4} (hμν : μ < ν) {ε ε' : ℝ} (h : IsUnitSign ε)
    (h' : IsUnitSign ε') : euclidNorm (signedDiagonal μ ν ε ε') = 1 := by
  have hne : μ ≠ ν := hμν.ne
  have hpt : ∀ i, ((if i = μ then ε else 0) + (if i = ν then ε' else 0)) ^ 2 =
      (if i = μ then 1 else 0) + (if i = ν then 1 else 0) := by
    intro i
    by_cases h1 : i = μ
    · have h2 : i ≠ ν := fun e => hne (h1 ▸ e)
      simp [h1, hne, unitSign_sq h]
    · by_cases h2 : i = ν
      · simp [h2, hne.symm, unitSign_sq h']
      · simp [h1, h2]
  have hs : ∑ i, signedDiagonal μ ν ε ε' i ^ 2 = 1 := by
    simp only [signedDiagonal_apply, mul_pow, inv_sqrt_two_pow_two, hpt, ← Finset.mul_sum,
      Finset.sum_add_distrib]
    simp
    norm_num
  rw [euclidNorm, hs, Real.sqrt_one]
theorem signedAxis_ne_zero_iff (κ : Fin 4) {δ : ℝ} (h : IsUnitSign δ) (i : Fin 4) :
    signedAxis κ δ i ≠ 0 ↔ i = κ := by
  rw [signedAxis_apply]
  by_cases h1 : i = κ
  · simp [h1, unitSign_ne_zero h]
  · simp [h1]
theorem signedDiagonal_ne_zero_iff {μ ν : Fin 4} (hμν : μ < ν) {ε ε' : ℝ} (h : IsUnitSign ε)
    (h' : IsUnitSign ε') (i : Fin 4) :
    signedDiagonal μ ν ε ε' i ≠ 0 ↔ i = μ ∨ i = ν := by
  have hne : μ ≠ ν := hμν.ne
  rw [signedDiagonal_apply]
  by_cases h1 : i = μ
  · simp [h1, hne, unitSign_ne_zero h]
  · by_cases h2 : i = ν
    · simp [h2, hne.symm, unitSign_ne_zero h']
    · simp [h1, h2]
theorem signedDiagonal_apply_fst {μ ν : Fin 4} (hμν : μ < ν) (ε ε' : ℝ) :
    signedDiagonal μ ν ε ε' μ = (Real.sqrt 2)⁻¹ * ε := by
  simp [signedDiagonal_apply, hμν.ne]
theorem signedDiagonal_apply_snd {μ ν : Fin 4} (hμν : μ < ν) (ε ε' : ℝ) :
    signedDiagonal μ ν ε ε' ν = (Real.sqrt 2)⁻¹ * ε' := by
  simp [signedDiagonal_apply, hμν.ne']
theorem signedAxis_inj {μ₁ μ₂ : Fin 4} {ε₁ ε₂ : ℝ} (h₁ : IsUnitSign ε₁) (h₂ : IsUnitSign ε₂)
    (e : signedAxis μ₁ ε₁ = signedAxis μ₂ ε₂) : μ₁ = μ₂ ∧ ε₁ = ε₂ := by
  have hμ : μ₁ = μ₂ := by
    have := (signedAxis_ne_zero_iff μ₁ h₁ μ₁).2 rfl
    rw [e] at this
    exact (signedAxis_ne_zero_iff μ₂ h₂ μ₁).1 this
  subst hμ
  refine ⟨rfl, ?_⟩
  have := congrFun e μ₁
  simpa [signedAxis_apply] using this
theorem signedDiagonal_inj {μ₁ ν₁ μ₂ ν₂ : Fin 4} {ε₁ ε₁' ε₂ ε₂' : ℝ} (l₁ : μ₁ < ν₁)
    (l₂ : μ₂ < ν₂) (h₁ : IsUnitSign ε₁) (h₁' : IsUnitSign ε₁') (h₂ : IsUnitSign ε₂)
    (h₂' : IsUnitSign ε₂')
    (e : signedDiagonal μ₁ ν₁ ε₁ ε₁' = signedDiagonal μ₂ ν₂ ε₂ ε₂') :
    μ₁ = μ₂ ∧ ν₁ = ν₂ ∧ ε₁ = ε₂ ∧ ε₁' = ε₂' := by
  have hiff : ∀ i, (i = μ₁ ∨ i = ν₁) ↔ (i = μ₂ ∨ i = ν₂) := fun i => by
    rw [← signedDiagonal_ne_zero_iff l₁ h₁ h₁' i, ← signedDiagonal_ne_zero_iff l₂ h₂ h₂' i, e]
  have a := (hiff μ₁).1 (Or.inl rfl)
  have b := (hiff ν₁).1 (Or.inr rfl)
  have c := (hiff μ₂).2 (Or.inl rfl)
  have d := (hiff ν₂).2 (Or.inr rfl)
  have hμ : μ₁ = μ₂ := by
    rcases a with a | a
    · exact a
    · rcases c with c | c
      · exact c.symm
      · exfalso
        rw [a] at l₁
        rw [c] at l₂
        exact absurd l₁ (not_lt.2 l₂.le)
  subst hμ
  have hν : ν₁ = ν₂ := by
    rcases b with b | b
    · exact absurd b l₁.ne'
    · exact b
  subst hν
  have s := sqrt_two_inv_ne_zero
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have := congrFun e μ₁
    rw [signedDiagonal_apply_fst l₁, signedDiagonal_apply_fst l₁] at this
    exact mul_left_cancel₀ s this
  · have := congrFun e ν₁
    rw [signedDiagonal_apply_snd l₁, signedDiagonal_apply_snd l₁] at this
    exact mul_left_cancel₀ s this
theorem signedAxis_ne_signedDiagonal (κ : Fin 4) {μ ν : Fin 4} (l : μ < ν) {δ ε ε' : ℝ}
    (hδ : IsUnitSign δ) (h : IsUnitSign ε) (h' : IsUnitSign ε') :
    signedAxis κ δ ≠ signedDiagonal μ ν ε ε' := by
  intro e
  have a : μ = κ := by
    rw [← signedAxis_ne_zero_iff κ hδ μ, e, signedDiagonal_ne_zero_iff l h h']
    exact Or.inl rfl
  have b : ν = κ := by
    rw [← signedAxis_ne_zero_iff κ hδ ν, e, signedDiagonal_ne_zero_iff l h h']
    exact Or.inr rfl
  exact l.ne (a.trans b.symm)
def boolSign (b : Bool) : ℝ := if b then 1 else -1
theorem isUnitSign_boolSign (b : Bool) : IsUnitSign (boolSign b) := by
  cases b <;> simp [boolSign, IsUnitSign]
theorem boolSign_injective : Function.Injective boolSign := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; norm_num [boolSign] at h)
theorem exists_boolSign_eq {ε : ℝ} (h : IsUnitSign ε) : ∃ b, boolSign b = ε := by
  rcases h with rfl | rfl
  · exact ⟨true, by simp [boolSign]⟩
  · exact ⟨false, by simp [boolSign]⟩
theorem isUnitSign_one : IsUnitSign 1 := Or.inl rfl
theorem isUnitSign_neg_one : IsUnitSign (-1) := Or.inr rfl
theorem isUnitSign_neg {ε : ℝ} (h : IsUnitSign ε) : IsUnitSign (-ε) := by
  rcases h with rfl | rfl
  · exact isUnitSign_neg_one
  · simpa using isUnitSign_one
theorem isUnitSign_mul {ε ε' : ℝ} (h : IsUnitSign ε) (h' : IsUnitSign ε') :
    IsUnitSign (ε * ε') := by apply _root_.YangMills.Construction.Tower.HypercubicMotions.sign_mul_sign <;> assumption
abbrev IncreasingPair := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev NormalCode := (Fin 4 × Bool) ⊕ (IncreasingPair × Bool × Bool)
def normalOfCode : NormalCode → AmbientSpace
  | .inl (μ, b) => signedAxis μ (boolSign b)
  | .inr (p, b, c) => signedDiagonal p.1.1 p.1.2 (boolSign b) (boolSign c)
theorem normalOfCode_injective : Function.Injective normalOfCode := by
  rintro (⟨μ₁, b₁⟩ | ⟨⟨⟨μ₁, ν₁⟩, l₁⟩, b₁, c₁⟩) (⟨μ₂, b₂⟩ | ⟨⟨⟨μ₂, ν₂⟩, l₂⟩, b₂, c₂⟩) e
  · obtain ⟨a, b⟩ := signedAxis_inj (isUnitSign_boolSign _) (isUnitSign_boolSign _) e
    rw [a, boolSign_injective b]
  · exact absurd e (signedAxis_ne_signedDiagonal _ l₂ (isUnitSign_boolSign _)
      (isUnitSign_boolSign _) (isUnitSign_boolSign _))
  · exact absurd e.symm (signedAxis_ne_signedDiagonal _ l₁ (isUnitSign_boolSign _)
      (isUnitSign_boolSign _) (isUnitSign_boolSign _))
  · obtain ⟨a, b, c, d⟩ := signedDiagonal_inj l₁ l₂ (isUnitSign_boolSign _)
      (isUnitSign_boolSign _) (isUnitSign_boolSign _) (isUnitSign_boolSign _) e
    subst a b
    rw [boolSign_injective c, boolSign_injective d]
theorem range_normalOfCode : range normalOfCode = reflectionNormals := by
  ext v
  constructor
  · rintro ⟨(⟨μ, b⟩ | ⟨⟨⟨μ, ν⟩, l⟩, b, c⟩), rfl⟩
    · exact Or.inl ⟨μ, boolSign b, isUnitSign_boolSign b, rfl⟩
    · exact Or.inr ⟨μ, ν, boolSign b, boolSign c, l, isUnitSign_boolSign b,
        isUnitSign_boolSign c, rfl⟩
  · rintro (⟨μ, ε, h, rfl⟩ | ⟨μ, ν, ε, ε', l, h, h', rfl⟩)
    · obtain ⟨b, rfl⟩ := exists_boolSign_eq h
      exact ⟨.inl (μ, b), rfl⟩
    · obtain ⟨b, rfl⟩ := exists_boolSign_eq h
      obtain ⟨c, rfl⟩ := exists_boolSign_eq h'
      exact ⟨.inr (⟨(μ, ν), l⟩, b, c), rfl⟩
theorem card_increasingPair : Fintype.card IncreasingPair = 6 := by decide
theorem ncard_reflectionNormals : reflectionNormals.ncard = 32 := by
  rw [← range_normalOfCode, ← image_univ, ncard_image_of_injective _ normalOfCode_injective,
    ncard_univ, Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    card_increasingPair]
theorem reflectionNormalsCount : ReflectionNormalsCount :=
  ⟨fun μ _ h => euclidNorm_signedAxis μ h, fun _ _ _ _ l h h' => euclidNorm_signedDiagonal l h h',
    fun _ _ _ _ h₁ h₂ e => signedAxis_inj h₁ h₂ e,
    fun _ _ _ _ _ _ _ _ l₁ l₂ h₁ h₁' h₂ h₂' e => signedDiagonal_inj l₁ l₂ h₁ h₁' h₂ h₂' e,
    fun κ _ _ _ _ _ l hδ h h' => signedAxis_ne_signedDiagonal κ l hδ h h',
    ncard_reflectionNormals⟩
abbrev RepresentativeCode := Fin 4 ⊕ (IncreasingPair × Bool)
def representativeOfCode : RepresentativeCode → AmbientSpace
  | .inl μ => signedAxis μ 1
  | .inr (p, b) => signedDiagonal p.1.1 p.1.2 1 (boolSign b)
theorem representativeOfCode_injective : Function.Injective representativeOfCode := by
  rintro (μ₁ | ⟨⟨⟨μ₁, ν₁⟩, l₁⟩, b₁⟩) (μ₂ | ⟨⟨⟨μ₂, ν₂⟩, l₂⟩, b₂⟩) e
  · rw [(signedAxis_inj isUnitSign_one isUnitSign_one e).1]
  · exact absurd e (signedAxis_ne_signedDiagonal _ l₂ isUnitSign_one isUnitSign_one
      (isUnitSign_boolSign _))
  · exact absurd e.symm (signedAxis_ne_signedDiagonal _ l₁ isUnitSign_one isUnitSign_one
      (isUnitSign_boolSign _))
  · obtain ⟨a, b, -, d⟩ := signedDiagonal_inj l₁ l₂ isUnitSign_one (isUnitSign_boolSign _)
      isUnitSign_one (isUnitSign_boolSign _) e
    subst a b
    rw [boolSign_injective d]
theorem signedAxis_one (μ : Fin 4) : signedAxis μ 1 = coordVec μ := by
  simp [signedAxis]
theorem signedDiagonal_one_one (μ ν : Fin 4) :
    signedDiagonal μ ν 1 1 = (Real.sqrt 2)⁻¹ • (coordVec μ + coordVec ν) := by
  simp [signedDiagonal]
theorem signedDiagonal_one_neg_one (μ ν : Fin 4) :
    signedDiagonal μ ν 1 (-1) = (Real.sqrt 2)⁻¹ • (coordVec μ - coordVec ν) := by
  simp [signedDiagonal, sub_eq_add_neg]
theorem mem_normalRepresentatives_iff (n : AmbientSpace) : n ∈ normalRepresentatives ↔
    (∃ μ, n = signedAxis μ 1) ∨
      ∃ (μ ν : Fin 4) (δ : ℝ), μ < ν ∧ IsUnitSign δ ∧ n = signedDiagonal μ ν 1 δ := by
  constructor
  · rintro ((⟨μ, rfl⟩ | ⟨μ, ν, l, rfl⟩) | ⟨μ, ν, l, rfl⟩)
    · exact Or.inl ⟨μ, (signedAxis_one μ).symm⟩
    · exact Or.inr ⟨μ, ν, 1, l, isUnitSign_one, (signedDiagonal_one_one μ ν).symm⟩
    · exact Or.inr ⟨μ, ν, -1, l, isUnitSign_neg_one, (signedDiagonal_one_neg_one μ ν).symm⟩
  · rintro (⟨μ, rfl⟩ | ⟨μ, ν, δ, l, h, rfl⟩)
    · exact Or.inl (Or.inl ⟨μ, signedAxis_one μ⟩)
    · rcases h with rfl | rfl
      · exact Or.inl (Or.inr ⟨μ, ν, l, signedDiagonal_one_one μ ν⟩)
      · exact Or.inr ⟨μ, ν, l, signedDiagonal_one_neg_one μ ν⟩
theorem range_representativeOfCode : range representativeOfCode = normalRepresentatives := by
  ext v
  rw [mem_normalRepresentatives_iff]
  constructor
  · rintro ⟨(μ | ⟨⟨⟨μ, ν⟩, l⟩, b⟩), rfl⟩
    · exact Or.inl ⟨μ, rfl⟩
    · exact Or.inr ⟨μ, ν, boolSign b, l, isUnitSign_boolSign b, rfl⟩
  · rintro (⟨μ, rfl⟩ | ⟨μ, ν, δ, l, h, rfl⟩)
    · exact ⟨.inl μ, rfl⟩
    · obtain ⟨b, rfl⟩ := exists_boolSign_eq h
      exact ⟨.inr (⟨(μ, ν), l⟩, b), rfl⟩
theorem ncard_normalRepresentatives : normalRepresentatives.ncard = 16 := by
  rw [← range_representativeOfCode, ← image_univ,
    ncard_image_of_injective _ representativeOfCode_injective, ncard_univ,
    Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    card_increasingPair]
theorem existsUnique_rep_signedAxis (μ : Fin 4) {ε : ℝ} (h : IsUnitSign ε) :
    ∃! n, n ∈ normalRepresentatives ∧ (signedAxis μ ε = n ∨ signedAxis μ ε = -n) := by
  refine ExistsUnique.intro (signedAxis μ 1)
    ⟨(mem_normalRepresentatives_iff _).2 (Or.inl ⟨μ, rfl⟩), ?_⟩ ?_
  · rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (neg_signedAxis μ 1).symm
  · rintro n ⟨hn, hv⟩
    rcases (mem_normalRepresentatives_iff n).1 hn with ⟨κ, rfl⟩ | ⟨κ, ρ, δ, l, hδ, rfl⟩
    · rcases hv with e | e
      · rw [(signedAxis_inj h isUnitSign_one e).1]
      · rw [neg_signedAxis] at e
        rw [(signedAxis_inj h isUnitSign_neg_one e).1]
    · rcases hv with e | e
      · exact absurd e (signedAxis_ne_signedDiagonal _ l h isUnitSign_one hδ)
      · rw [neg_signedDiagonal] at e
        exact absurd e (signedAxis_ne_signedDiagonal _ l h isUnitSign_neg_one (isUnitSign_neg hδ))
theorem existsUnique_rep_signedDiagonal {μ ν : Fin 4} (l : μ < ν) {ε ε' : ℝ} (h : IsUnitSign ε)
    (h' : IsUnitSign ε') :
    ∃! n, n ∈ normalRepresentatives ∧
      (signedDiagonal μ ν ε ε' = n ∨ signedDiagonal μ ν ε ε' = -n) := by
  refine ExistsUnique.intro (signedDiagonal μ ν 1 (ε * ε'))
    ⟨(mem_normalRepresentatives_iff _).2 (Or.inr ⟨μ, ν, _, l, isUnitSign_mul h h', rfl⟩), ?_⟩ ?_
  · rcases h with rfl | rfl
    · left
      simp
    · right
      rw [neg_signedDiagonal]
      simp
  · rintro n ⟨hn, hv⟩
    rcases (mem_normalRepresentatives_iff n).1 hn with ⟨κ, rfl⟩ | ⟨κ, ρ, δ, l', hδ, rfl⟩
    · rcases hv with e | e
      · exact absurd e.symm (signedAxis_ne_signedDiagonal _ l isUnitSign_one h h')
      · rw [neg_signedAxis] at e
        exact absurd e.symm (signedAxis_ne_signedDiagonal _ l isUnitSign_neg_one h h')
    · rcases hv with e | e
      · obtain ⟨rfl, rfl, a, b⟩ := signedDiagonal_inj l l' h h' isUnitSign_one hδ e
        subst a b
        simp
      · rw [neg_signedDiagonal] at e
        obtain ⟨rfl, rfl, a, b⟩ :=
          signedDiagonal_inj l l' h h' isUnitSign_neg_one (isUnitSign_neg hδ) e
        subst a b
        simp
theorem reflectionNormalsModSign : ReflectionNormalsModSign := by
  refine ⟨ncard_normalRepresentatives, ?_⟩
  rintro v (⟨μ, ε, h, rfl⟩ | ⟨μ, ν, ε, ε', l, h, h', rfl⟩)
  · exact existsUnique_rep_signedAxis μ h
  · exact existsUnique_rep_signedDiagonal l h h'
theorem reflectAcross_coordVec_three :
    reflectAcross (coordVec 3) = TimeAxis.timeReflection := by
  funext x i
  have h : euclidDot (coordVec 3) x = x 3 := by
    simp [euclidDot, coordVec_apply, ite_mul, Finset.sum_ite_eq']
  rw [reflectAcross, h]
  fin_cases i <;> simp [TimeAxis.timeReflection, coordVec_apply]
  ring
theorem reflectAcrossTimeAxis : ReflectAcrossTimeAxis := by
  refine ⟨reflectAcross_coordVec_three, fun E f => ?_⟩
  rw [reflectFun, reflectAcross_coordVec_three, timeReflected]
theorem ambient_ext {v w : AmbientSpace} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2)
    (h3 : v 3 = w 3) : v = w := by
  funext i
  fin_cases i <;> assumption
theorem euclidDot_eq (u w : AmbientSpace) :
    euclidDot u w = u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 := by
  simp [euclidDot, Fin.sum_univ_four]
theorem planeUnit_apply_zero (ϑ : ℝ) : planeUnit ϑ 0 = Real.sin ϑ := by
  simp [planeUnit, coordVec_apply]
theorem planeUnit_apply_one (ϑ : ℝ) : planeUnit ϑ 1 = 0 := by
  simp [planeUnit, coordVec_apply]
theorem planeUnit_apply_two (ϑ : ℝ) : planeUnit ϑ 2 = 0 := by
  simp [planeUnit, coordVec_apply]
theorem planeUnit_apply_three (ϑ : ℝ) : planeUnit ϑ 3 = Real.cos ϑ := by
  simp [planeUnit, coordVec_apply]
theorem planeUnit_mem_coordPlane (ϑ : ℝ) : planeUnit ϑ ∈ coordPlane := by
  show transCoords _ = 0
  funext i
  fin_cases i <;> simp [transCoords, planeUnit_apply_one, planeUnit_apply_two]
theorem planeUnit_add_int_mul_two_pi (ϑ : ℝ) (q : ℤ) :
    planeUnit (ϑ + q * (2 * Real.pi)) = planeUnit ϑ := by
  simp only [planeUnit, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
theorem planeUnit_add_pi (ϑ : ℝ) : planeUnit (ϑ + Real.pi) = -planeUnit ϑ := by
  simp only [planeUnit, Real.cos_add_pi, Real.sin_add_pi]
  module
theorem planeUnit_add_pi_div_two (ϑ : ℝ) :
    planeUnit (ϑ + Real.pi / 2) =
      (-Real.sin ϑ) • coordVec 3 + Real.cos ϑ • coordVec 0 := by
  simp only [planeUnit, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
theorem planeUnit_zero : planeUnit 0 = coordVec 3 := by
  simp [planeUnit]
theorem planeUnit_pi_div_two : planeUnit (Real.pi / 2) = coordVec 0 := by
  simp [planeUnit]
theorem sqrt_two_div_two : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith
theorem planeUnit_pi_div_four : planeUnit (Real.pi / 4) = diagNormalPlus := by
  simp only [planeUnit, diagNormalPlus, Real.cos_pi_div_four, Real.sin_pi_div_four,
    sqrt_two_div_two]
  module
theorem planeUnit_neg_pi_div_four : planeUnit (-(Real.pi / 4)) = diagNormalMinus := by
  simp only [planeUnit, diagNormalMinus, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four, sqrt_two_div_two]
  module
theorem planeUnit_pi_div_four_add_pi_div_two :
    planeUnit (Real.pi / 4 + Real.pi / 2) = -diagNormalMinus := by
  rw [planeUnit_add_pi_div_two]
  simp only [diagNormalMinus, Real.cos_pi_div_four, Real.sin_pi_div_four, sqrt_two_div_two]
  module
theorem planeUnit_multiples_pi_div_four :
    planeUnit (((0 : ℤ) : ℝ) * Real.pi / 4) = coordVec 3 ∧
    planeUnit (((1 : ℤ) : ℝ) * Real.pi / 4) = diagNormalPlus ∧
    planeUnit (((2 : ℤ) : ℝ) * Real.pi / 4) = coordVec 0 ∧
    planeUnit (((3 : ℤ) : ℝ) * Real.pi / 4) = -diagNormalMinus ∧
    planeUnit (((4 : ℤ) : ℝ) * Real.pi / 4) = -coordVec 3 ∧
    planeUnit (((5 : ℤ) : ℝ) * Real.pi / 4) = -diagNormalPlus ∧
    planeUnit (((6 : ℤ) : ℝ) * Real.pi / 4) = -coordVec 0 ∧
    planeUnit (((7 : ℤ) : ℝ) * Real.pi / 4) = diagNormalMinus := by
  have a0 : ((0 : ℤ) : ℝ) * Real.pi / 4 = 0 := by push_cast; ring
  have a1 : ((1 : ℤ) : ℝ) * Real.pi / 4 = Real.pi / 4 := by push_cast; ring
  have a2 : ((2 : ℤ) : ℝ) * Real.pi / 4 = Real.pi / 2 := by push_cast; ring
  have a3 : ((3 : ℤ) : ℝ) * Real.pi / 4 = Real.pi / 4 + Real.pi / 2 := by push_cast; ring
  have a4 : ((4 : ℤ) : ℝ) * Real.pi / 4 = 0 + Real.pi := by push_cast; ring
  have a5 : ((5 : ℤ) : ℝ) * Real.pi / 4 = Real.pi / 4 + Real.pi := by push_cast; ring
  have a6 : ((6 : ℤ) : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi := by push_cast; ring
  have a7 : ((7 : ℤ) : ℝ) * Real.pi / 4 = -(Real.pi / 4) + ((1 : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [a0, a1, a2, a3, a4, a5, a6, a7, planeUnit_add_pi, planeUnit_add_pi, planeUnit_add_pi,
    planeUnit_add_int_mul_two_pi, planeUnit_zero, planeUnit_pi_div_four, planeUnit_pi_div_two,
    planeUnit_pi_div_four_add_pi_div_two, planeUnit_neg_pi_div_four]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
def octagonVectors : Set AmbientSpace :=
  {coordVec 3, -coordVec 3, coordVec 0, -coordVec 0,
    diagNormalPlus, -diagNormalPlus, diagNormalMinus, -diagNormalMinus}
theorem planeUnits_eq_octagonVectors :
    {v | ∃ j : ℤ, v = planeUnit ((j : ℝ) * Real.pi / 4)} = octagonVectors := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩ := planeUnit_multiples_pi_div_four
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨r, q, rfl, h0, h8⟩ : ∃ r q : ℤ, j = r + 8 * q ∧ 0 ≤ r ∧ r < 8 :=
      ⟨j % 8, j / 8, (Int.emod_add_mul_ediv j 8).symm, Int.emod_nonneg _ (by norm_num),
        Int.emod_lt_of_pos _ (by norm_num)⟩
    have e : ((r + 8 * q : ℤ) : ℝ) * Real.pi / 4 =
        (r : ℝ) * Real.pi / 4 + (q : ℝ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [e, planeUnit_add_int_mul_two_pi]
    interval_cases r
    · rw [t0]; simp [octagonVectors]
    · rw [t1]; simp [octagonVectors]
    · rw [t2]; simp [octagonVectors]
    · rw [t3]; simp [octagonVectors]
    · rw [t4]; simp [octagonVectors]
    · rw [t5]; simp [octagonVectors]
    · rw [t6]; simp [octagonVectors]
    · rw [t7]; simp [octagonVectors]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, t0.symm⟩
    · exact ⟨4, t4.symm⟩
    · exact ⟨2, t2.symm⟩
    · exact ⟨6, t6.symm⟩
    · exact ⟨1, t1.symm⟩
    · exact ⟨5, t5.symm⟩
    · exact ⟨7, t7.symm⟩
    · exact ⟨3, t3.symm⟩
theorem signedDiagonal_zero_three_one_one : signedDiagonal 0 3 1 1 = diagNormalPlus := by
  simp only [signedDiagonal, diagNormalPlus]
  module
theorem signedDiagonal_zero_three_neg_one_neg_one :
    signedDiagonal 0 3 (-1) (-1) = -diagNormalPlus := by
  simp only [signedDiagonal, diagNormalPlus]
  module
theorem signedDiagonal_zero_three_neg_one_one : signedDiagonal 0 3 (-1) 1 = diagNormalMinus := by
  simp only [signedDiagonal, diagNormalMinus]
  module
theorem signedDiagonal_zero_three_one_neg_one :
    signedDiagonal 0 3 1 (-1) = -diagNormalMinus := by
  simp only [signedDiagonal, diagNormalMinus]
  module
theorem octagonVectors_subset_coordPlane : octagonVectors ⊆ coordPlane := by
  rw [← planeUnits_eq_octagonVectors]
  rintro v ⟨j, rfl⟩
  exact planeUnit_mem_coordPlane _
theorem planeReflectionNormals_eq : planeReflectionNormals = octagonVectors := by
  apply Subset.antisymm
  · rintro v ⟨hv, hp⟩
    have h1 : v 1 = 0 := congrFun hp 0
    have h2 : v 2 = 0 := congrFun hp 1
    rcases hv with ⟨μ, ε, h, rfl⟩ | ⟨μ, ν, ε, ε', l, h, h', rfl⟩
    · have hne : ∀ i, i = μ → (ε • coordVec μ) i ≠ 0 := fun i hi =>
        (signedAxis_ne_zero_iff μ h i).2 hi
      have n1 : μ ≠ 1 := fun e => hne 1 e.symm h1
      have n2 : μ ≠ 2 := fun e => hne 2 e.symm h2
      have hμ : μ = 0 ∨ μ = 3 := by
        revert n1 n2
        clear hne h1 h2 hp
        revert μ
        decide
      rcases hμ with rfl | rfl <;> rcases h with rfl | rfl <;> simp [octagonVectors]
    · have hne : ∀ i, (i = μ ∨ i = ν) → signedDiagonal μ ν ε ε' i ≠ 0 := fun i hi =>
        (signedDiagonal_ne_zero_iff l h h' i).2 hi
      have n1 : μ ≠ 1 := fun e => hne 1 (Or.inl e.symm) h1
      have n2 : μ ≠ 2 := fun e => hne 2 (Or.inl e.symm) h2
      have m1 : ν ≠ 1 := fun e => hne 1 (Or.inr e.symm) h1
      have m2 : ν ≠ 2 := fun e => hne 2 (Or.inr e.symm) h2
      have hμν : μ = 0 ∧ ν = 3 := by
        revert l n1 n2 m1 m2
        clear hne h1 h2 hp
        revert μ ν
        decide
      obtain ⟨rfl, rfl⟩ := hμν
      change signedDiagonal 0 3 ε ε' ∈ octagonVectors
      rcases h with rfl | rfl <;> rcases h' with rfl | rfl
      · rw [signedDiagonal_zero_three_one_one]; simp [octagonVectors]
      · rw [signedDiagonal_zero_three_one_neg_one]; simp [octagonVectors]
      · rw [signedDiagonal_zero_three_neg_one_one]; simp [octagonVectors]
      · rw [signedDiagonal_zero_three_neg_one_neg_one]; simp [octagonVectors]
  · intro v hv
    refine ⟨?_, octagonVectors_subset_coordPlane hv⟩
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨3, 1, Or.inl rfl, by simp⟩
    · exact Or.inl ⟨3, -1, Or.inr rfl, by simp⟩
    · exact Or.inl ⟨0, 1, Or.inl rfl, by simp⟩
    · exact Or.inl ⟨0, -1, Or.inr rfl, by simp⟩
    · exact Or.inr ⟨0, 3, 1, 1, by decide, isUnitSign_one, isUnitSign_one,
        signedDiagonal_zero_three_one_one.symm⟩
    · exact Or.inr ⟨0, 3, -1, -1, by decide, isUnitSign_neg_one, isUnitSign_neg_one,
        signedDiagonal_zero_three_neg_one_neg_one.symm⟩
    · exact Or.inr ⟨0, 3, -1, 1, by decide, isUnitSign_neg_one, isUnitSign_one,
        signedDiagonal_zero_three_neg_one_one.symm⟩
    · exact Or.inr ⟨0, 3, 1, -1, by decide, isUnitSign_one, isUnitSign_neg_one,
        signedDiagonal_zero_three_one_neg_one.symm⟩
def planeAxisPair : IncreasingPair := ⟨(0, 3), by decide⟩
def planeNormalCodes : Finset NormalCode :=
  {.inl (3, true), .inl (3, false), .inl (0, true), .inl (0, false),
    .inr (planeAxisPair, true, true), .inr (planeAxisPair, false, false),
    .inr (planeAxisPair, false, true), .inr (planeAxisPair, true, false)}
theorem image_planeNormalCodes :
    normalOfCode '' (planeNormalCodes : Set NormalCode) = octagonVectors := by
  have c : ∀ (b : Bool) (μ : Fin 4), normalOfCode (.inl (μ, b)) =
      boolSign b • coordVec μ := fun _ _ => rfl
  have d : ∀ b c : Bool, normalOfCode (.inr (planeAxisPair, b, c)) =
      signedDiagonal 0 3 (boolSign b) (boolSign c) := fun _ _ => rfl
  have st : boolSign true = 1 := by simp [boolSign]
  have sf : boolSign false = -1 := by simp [boolSign]
  simp only [planeNormalCodes, Finset.coe_insert, Finset.coe_singleton, image_insert_eq,
    image_singleton, c, d, st, sf, signedDiagonal_zero_three_one_one,
    signedDiagonal_zero_three_neg_one_neg_one, signedDiagonal_zero_three_neg_one_one,
    signedDiagonal_zero_three_one_neg_one, one_smul, neg_smul, octagonVectors]
theorem ncard_octagonVectors : octagonVectors.ncard = 8 := by
  rw [← image_planeNormalCodes, ncard_image_of_injective _ normalOfCode_injective,
    ncard_coe_finset]
  decide
theorem planeNormalsEight : PlaneNormalsEight := by
  have hl : planeReflectionNormals = {coordVec 3, -coordVec 3, coordVec 0,
      -coordVec 0, diagNormalPlus, -diagNormalPlus, diagNormalMinus, -diagNormalMinus} :=
    planeReflectionNormals_eq
  exact ⟨planeReflectionNormals_eq.trans planeUnits_eq_octagonVectors.symm, hl,
    by rw [planeReflectionNormals_eq]; exact ncard_octagonVectors, planeUnit_pi_div_four.symm,
    planeUnit_neg_pi_div_four.symm⟩
theorem planeUnit_add_pi_div_two_apply_zero (ϑ : ℝ) :
    planeUnit (ϑ + Real.pi / 2) 0 = Real.cos ϑ := by
  rw [planeUnit_apply_zero, Real.sin_add_pi_div_two]
theorem planeUnit_add_pi_div_two_apply_three (ϑ : ℝ) :
    planeUnit (ϑ + Real.pi / 2) 3 = -Real.sin ϑ := by
  rw [planeUnit_apply_three, Real.cos_add_pi_div_two]
theorem planePerp_planeUnit (ϑ : ℝ) :
    planePerp (planeUnit ϑ) = planeUnit (ϑ + Real.pi / 2) := by
  rw [planeUnit_add_pi_div_two, planePerp, planeUnit_apply_zero, planeUnit_apply_three]
theorem span_planeUnit_pair (ϑ : ℝ) :
    ((Submodule.span ℝ ({planeUnit ϑ, planeUnit (ϑ + Real.pi / 2)} : Set AmbientSpace) :
      Submodule ℝ AmbientSpace) : Set AmbientSpace) = coordPlane := by
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    show transCoords _ = 0
    funext i
    fin_cases i <;> simp [transCoords, planeUnit_apply_one, planeUnit_apply_two]
  · intro hv
    have h1 : v 1 = 0 := congrFun hv 0
    have h2 : v 2 = 0 := congrFun hv 1
    refine ⟨v 3 * Real.cos ϑ + v 0 * Real.sin ϑ, -v 3 * Real.sin ϑ + v 0 * Real.cos ϑ, ?_⟩
    have hs := Real.sin_sq_add_cos_sq ϑ
    refine ambient_ext ?_ ?_ ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planeUnit_add_pi_div_two_apply_zero]
      simp only [planeUnit_apply_zero]
      linear_combination (v 0) * hs
    · simp [planeUnit_apply_one, h1]
    · simp [planeUnit_apply_two, h2]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planeUnit_add_pi_div_two_apply_three]
      simp only [planeUnit_apply_three]
      linear_combination (v 3) * hs
theorem isPlaneOrthoBasis_planeOrthoFrame (ϑ : ℝ) :
    IsPlaneOrthoBasis (planeOrthoFrame (planeUnit ϑ)) := by
  have hs := Real.sin_sq_add_cos_sq ϑ
  simp only [IsPlaneOrthoBasis, planeOrthoFrame, planePerp_planeUnit]
  refine ⟨?_, ?_, ?_, span_planeUnit_pair ϑ⟩
  · rw [euclidDot_eq, planeUnit_apply_zero, planeUnit_apply_one, planeUnit_apply_two,
      planeUnit_apply_three]
    linear_combination hs
  · rw [euclidDot_eq, planeUnit_add_pi_div_two_apply_zero, planeUnit_apply_one,
      planeUnit_apply_two, planeUnit_add_pi_div_two_apply_three]
    linear_combination hs
  · rw [euclidDot_eq, planeUnit_add_pi_div_two_apply_zero, planeUnit_apply_zero,
      planeUnit_apply_one, planeUnit_apply_two, planeUnit_add_pi_div_two_apply_three,
      planeUnit_apply_three]
    ring
theorem cos_smul_add_sin_smul_planePerp (ϑ ϑ' : ℝ) :
    Real.cos ϑ' • planeUnit ϑ + Real.sin ϑ' • planePerp (planeUnit ϑ) =
      planeUnit (ϑ + ϑ') := by
  rw [planePerp_planeUnit]
  refine ambient_ext ?_ ?_ ?_ ?_
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planeUnit_add_pi_div_two_apply_zero]
    simp only [planeUnit_apply_zero, Real.sin_add]
    ring
  · simp [planeUnit_apply_one]
  · simp [planeUnit_apply_two]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planeUnit_add_pi_div_two_apply_three]
    simp only [planeUnit_apply_three, Real.cos_add]
    ring
theorem rotateInPlane_planeUnit (ϑ ϑ' : ℝ) :
    rotateInPlane ϑ' (planeUnit ϑ) = planeUnit (ϑ + ϑ') := by
  have e : planeUnit ϑ = Real.cos ϑ • coordVec 3 + Real.sin ϑ • coordVec 0 :=
    rfl
  rw [e, map_add, map_smul, map_smul, rotateInPlane_coordVec_three, rotateInPlane_coordVec_zero]
  refine ambient_ext ?_ ?_ ?_ ?_
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planeUnit_add_pi_div_two_apply_zero]
    simp only [planeUnit_apply_zero, Real.sin_add]
    ring
  · simp [planeUnit_apply_one]
  · simp [planeUnit_apply_two]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, planeUnit_add_pi_div_two_apply_three]
    simp only [planeUnit_apply_three, Real.cos_add]
    ring
theorem exists_eq_planeUnit {v : AmbientSpace} (hv : v ∈ coordPlane) (hn : euclidNorm v = 1) :
    ∃ ϑ : ℝ, v = planeUnit ϑ := by
  have h1 : v 1 = 0 := congrFun hv 0
  have h2 : v 2 = 0 := congrFun hv 1
  have hs : ∑ μ, v μ ^ 2 = 1 := (Real.sqrt_eq_one).1 hn
  rw [Fin.sum_univ_four, h1, h2] at hs
  set z : ℂ := ⟨v 3, v 0⟩ with hz
  have hsq : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_mk]
    linear_combination hs
  have hnorm : ‖z‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero).1 hsq
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨Complex.arg z, ?_⟩
  have hc : Real.cos (Complex.arg z) = v 3 := by
    rw [Complex.cos_arg hz0, hnorm, div_one]
  have hsn : Real.sin (Complex.arg z) = v 0 := by
    rw [Complex.sin_arg, hnorm, div_one]
  refine ambient_ext ?_ ?_ ?_ ?_
  · rw [planeUnit_apply_zero, hsn]
  · rw [planeUnit_apply_one, h1]
  · rw [planeUnit_apply_two, h2]
  · rw [planeUnit_apply_three, hc]
theorem planeUnitsAndFrames : PlaneUnitsAndFrames := by
  refine ⟨?_, fun v hv hn => exists_eq_planeUnit hv hn⟩
  rintro ϑ ϑ' m rfl
  exact ⟨planePerp_planeUnit ϑ, isPlaneOrthoBasis_planeOrthoFrame ϑ,
    cos_smul_add_sin_smul_planePerp ϑ ϑ', rotateInPlane_planeUnit ϑ ϑ'⟩
open TorusLifts (signedCoordinateEquiv)
theorem signedCoordinateEquiv_apply (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (x : AmbientSpace)
    (μ : Fin 4) : signedCoordinateEquiv π s x μ = (((s μ : ℤˣ) : ℤ) : ℝ) * x (π μ) := rfl
abbrev DihedralCode := Bool × ℤˣ × ℤˣ
def swapOfBool (b : Bool) : Equiv.Perm (Fin 4) := if b then Equiv.swap 0 3 else 1
def outerSigns (a c : ℤˣ) : Fin 4 → ℤˣ := ![a, 1, 1, c]
def dihedralOfCode (i : DihedralCode) : Equiv.Perm AmbientSpace :=
  signedCoordinateEquiv (swapOfBool i.1) (outerSigns i.2.1 i.2.2)
theorem dihedralOfCode_apply_zero (b : Bool) (a c : ℤˣ) (x : AmbientSpace) :
    dihedralOfCode (b, a, c) x 0 = ((a : ℤ) : ℝ) * x (if b then 3 else 0) := by
  cases b <;> simp [dihedralOfCode, signedCoordinateEquiv_apply, swapOfBool, outerSigns]
theorem dihedralOfCode_apply_one (b : Bool) (a c : ℤˣ) (x : AmbientSpace) :
    dihedralOfCode (b, a, c) x 1 = x 1 := by
  have h : Equiv.swap (0 : Fin 4) 3 1 = 1 := by decide
  cases b <;> simp [dihedralOfCode, signedCoordinateEquiv_apply, swapOfBool, outerSigns, h]
theorem dihedralOfCode_apply_two (b : Bool) (a c : ℤˣ) (x : AmbientSpace) :
    dihedralOfCode (b, a, c) x 2 = x 2 := by
  have h : Equiv.swap (0 : Fin 4) 3 2 = 2 := by decide
  cases b <;> simp [dihedralOfCode, signedCoordinateEquiv_apply, swapOfBool, outerSigns, h]
theorem dihedralOfCode_apply_three (b : Bool) (a c : ℤˣ) (x : AmbientSpace) :
    dihedralOfCode (b, a, c) x 3 = ((c : ℤ) : ℝ) * x (if b then 0 else 3) := by
  cases b <;> simp [dihedralOfCode, signedCoordinateEquiv_apply, swapOfBool, outerSigns]
theorem dihedralOfCode_mem (i : DihedralCode) : dihedralOfCode i ∈ dihedralInPlane := by
  obtain ⟨b, a, c⟩ := i
  refine ⟨⟨_, _, rfl⟩, ?_, ?_⟩
  · refine ambient_ext ?_ ?_ ?_ ?_
    · rw [dihedralOfCode_apply_zero]
      cases b <;> simp [coordVec_apply]
    · rw [dihedralOfCode_apply_one]
    · rw [dihedralOfCode_apply_two]
    · rw [dihedralOfCode_apply_three]
      cases b <;> simp [coordVec_apply]
  · refine ambient_ext ?_ ?_ ?_ ?_
    · rw [dihedralOfCode_apply_zero]
      cases b <;> simp [coordVec_apply]
    · rw [dihedralOfCode_apply_one]
    · rw [dihedralOfCode_apply_two]
    · rw [dihedralOfCode_apply_three]
      cases b <;> simp [coordVec_apply]
theorem fix_coordVec {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤˣ} {k : Fin 4}
    (h : signedCoordinateEquiv π s (coordVec k) = coordVec k) :
    π k = k ∧ s k = 1 := by
  have e := congrFun h k
  rw [signedCoordinateEquiv_apply, coordVec_apply, coordVec_apply, if_pos rfl] at e
  by_cases hk : π k = k
  · refine ⟨hk, ?_⟩
    rw [if_pos hk] at e
    rcases Int.units_eq_one_or (s k) with h' | h'
    · exact h'
    · rw [h'] at e
      norm_num at e
  · rw [if_neg hk] at e
    norm_num at e
theorem exists_eq_dihedralOfCode {r : Equiv.Perm AmbientSpace} (hr : r ∈ dihedralInPlane) :
    ∃ i, r = dihedralOfCode i := by
  obtain ⟨⟨π, s, rfl⟩, h1, h2⟩ := hr
  obtain ⟨p1, s1⟩ := fix_coordVec h1
  obtain ⟨p2, s2⟩ := fix_coordVec h2
  have hk : ∀ k : Fin 4, k ≠ 1 → k ≠ 2 → k = 0 ∨ k = 3 := by decide
  have n01 : π 0 ≠ 1 := fun e => absurd (π.injective (e.trans p1.symm)) (by decide)
  have n02 : π 0 ≠ 2 := fun e => absurd (π.injective (e.trans p2.symm)) (by decide)
  have n31 : π 3 ≠ 1 := fun e => absurd (π.injective (e.trans p1.symm)) (by decide)
  have n32 : π 3 ≠ 2 := fun e => absurd (π.injective (e.trans p2.symm)) (by decide)
  have n03 : π 0 ≠ π 3 := fun e => absurd (π.injective e) (by decide)
  have hs : s = outerSigns (s 0) (s 3) := by
    funext i
    fin_cases i
    · rfl
    · exact s1
    · exact s2
    · rfl
  rcases hk _ n01 n02 with a | a
  · have b : π 3 = 3 := by
      rcases hk _ n31 n32 with b | b
      · exact absurd (a.trans b.symm) n03
      · exact b
    refine ⟨(false, s 0, s 3), ?_⟩
    have hπ : π = swapOfBool false := by
      apply Equiv.ext
      intro i
      fin_cases i
      · simpa [swapOfBool] using a
      · simpa [swapOfBool] using p1
      · simpa [swapOfBool] using p2
      · simpa [swapOfBool] using b
    simp only [dihedralOfCode]
    rw [← hs, ← hπ]
  · have b : π 3 = 0 := by
      rcases hk _ n31 n32 with b | b
      · exact b
      · exact absurd (a.trans b.symm) n03
    refine ⟨(true, s 0, s 3), ?_⟩
    have hπ : π = swapOfBool true := by
      apply Equiv.ext
      intro i
      have c1 : Equiv.swap (0 : Fin 4) 3 1 = 1 := by decide
      have c2 : Equiv.swap (0 : Fin 4) 3 2 = 2 := by decide
      fin_cases i
      · simpa [swapOfBool] using a
      · simpa [swapOfBool, c1] using p1
      · simpa [swapOfBool, c2] using p2
      · simpa [swapOfBool] using b
    simp only [dihedralOfCode]
    rw [← hs, ← hπ]
theorem dihedralOfCode_injective : Function.Injective dihedralOfCode := by
  rintro ⟨b, a, c⟩ ⟨b', a', c'⟩ e
  have key := DFunLike.congr_fun e (![1, 0, 0, 2] : AmbientSpace)
  have h0 := congrFun key 0
  have h3 := congrFun key 3
  have u0 : ∀ d : Bool, (![1, 0, 0, 2] : AmbientSpace) (if d then 3 else 0) =
      if d then 2 else 1 := by
    intro d
    cases d <;> simp
  have u3 : ∀ d : Bool, (![1, 0, 0, 2] : AmbientSpace) (if d then 0 else 3) =
      if d then 1 else 2 := by
    intro d
    cases d <;> simp
  rw [dihedralOfCode_apply_zero, dihedralOfCode_apply_zero, u0, u0] at h0
  rw [dihedralOfCode_apply_three, dihedralOfCode_apply_three, u3, u3] at h3
  clear key e u0 u3
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or a' with rfl | rfl <;>
    rcases Int.units_eq_one_or c with rfl | rfl <;> rcases Int.units_eq_one_or c' with rfl | rfl <;>
    cases b <;> cases b' <;>
    first | rfl | (exfalso; norm_num at h0; done) | (exfalso; norm_num at h3; done)
theorem range_dihedralOfCode : range dihedralOfCode = dihedralInPlane := by
  apply Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    exact dihedralOfCode_mem i
  · intro r hr
    obtain ⟨i, rfl⟩ := exists_eq_dihedralOfCode hr
    exact ⟨i, rfl⟩
theorem ncard_dihedralInPlane : dihedralInPlane.ncard = 8 := by
  rw [← range_dihedralOfCode, ← image_univ, ncard_image_of_injective _ dihedralOfCode_injective,
    ncard_univ, Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_units_int]
def dihedralSubgroup : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := dihedralInPlane
  mul_mem' := by
    rintro u w ⟨hu, u1, u2⟩ ⟨hw, w1, w2⟩
    exact ⟨mul_mem hu hw, by rw [Equiv.Perm.mul_apply, w1, u1],
      by rw [Equiv.Perm.mul_apply, w2, u2]⟩
  one_mem' := ⟨one_mem _, rfl, rfl⟩
  inv_mem' := by
    rintro w ⟨hw, w1, w2⟩
    exact ⟨inv_mem hw, by rw [Equiv.Perm.inv_eq_iff_eq, w1],
      by rw [Equiv.Perm.inv_eq_iff_eq, w2]⟩
theorem mem_coordPlane_iff (x : AmbientSpace) : x ∈ coordPlane ↔ x 1 = 0 ∧ x 2 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h1, h2⟩
    show transCoords x = 0
    funext i
    fin_cases i
    · exact h1
    · exact h2
theorem image_coordPlane {r : Equiv.Perm AmbientSpace} (hr : r ∈ dihedralInPlane) :
    ⇑r '' coordPlane = coordPlane := by
  have hkeep : ∀ {w : Equiv.Perm AmbientSpace}, w ∈ dihedralInPlane →
      ∀ x, x ∈ coordPlane → w x ∈ coordPlane := by
    intro w hw x hx
    obtain ⟨⟨b, a, c⟩, rfl⟩ := exists_eq_dihedralOfCode hw
    rw [mem_coordPlane_iff] at hx ⊢
    rw [dihedralOfCode_apply_one, dihedralOfCode_apply_two]
    exact hx
  have hinv : r⁻¹ ∈ dihedralInPlane := dihedralSubgroup.inv_mem hr
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hkeep hr x hx
  · intro y hy
    exact ⟨r⁻¹ y, hkeep hinv y hy, by simp⟩
theorem dihedral_apply_assemble {r : Equiv.Perm AmbientSpace} (hr : r ∈ dihedralInPlane)
    (y z : Fin 2 → ℝ) :
    r (assemble y z) = assemble (planeCoords (r (embedPlane y))) z := by
  obtain ⟨⟨b, a, c⟩, rfl⟩ := exists_eq_dihedralOfCode hr
  have p0 : ∀ y z, assemble y z 0 = y 1 := fun _ _ => rfl
  have p1 : ∀ y z, assemble y z 1 = z 0 := fun _ _ => rfl
  have p2 : ∀ y z, assemble y z 2 = z 1 := fun _ _ => rfl
  have p3 : ∀ y z, assemble y z 3 = y 0 := fun _ _ => rfl
  have q0 : ∀ w : AmbientSpace, planeCoords w 1 = w 0 := fun _ => rfl
  have q3 : ∀ w : AmbientSpace, planeCoords w 0 = w 3 := fun _ => rfl
  have v0 : embedPlane y 0 = y 1 := by simp [embedPlane, coordVec_apply]
  have v3 : embedPlane y 3 = y 0 := by simp [embedPlane, coordVec_apply]
  refine ambient_ext ?_ ?_ ?_ ?_
  · rw [p0, q0, dihedralOfCode_apply_zero, dihedralOfCode_apply_zero]
    cases b
    · simp [p0, v0]
    · simp [p3, v3]
  · rw [dihedralOfCode_apply_one, p1, p1]
  · rw [dihedralOfCode_apply_two, p2, p2]
  · rw [p3, q3, dihedralOfCode_apply_three, dihedralOfCode_apply_three]
    cases b
    · simp [p3, v3]
    · simp [p0, v0]
theorem rightAngleRotation_coordVec_three : rightAngleRotation (coordVec 3) = coordVec 0 := by
  rw [rightAngleRotation, rotateInPlane_coordVec_three, planeUnit_pi_div_two]
theorem rightAngleRotation_coordVec_zero : rightAngleRotation (coordVec 0) = -coordVec 3 := by
  rw [rightAngleRotation, rotateInPlane_coordVec_zero, planeUnit_add_pi_div_two,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp
theorem rightAngleRotation_coordVec_one : rightAngleRotation (coordVec 1) = coordVec 1 :=
  rotateInPlane_coordVec_one _
theorem rightAngleRotation_coordVec_two : rightAngleRotation (coordVec 2) = coordVec 2 :=
  rotateInPlane_coordVec_two _
theorem rightAngleRotation_apply (x : AmbientSpace) :
    rightAngleRotation x = x 3 • coordVec 0 + x 0 • (-coordVec 3) +
      x 1 • coordVec 1 + x 2 • coordVec 2 := by
  have hx : x = x 3 • coordVec 3 + x 0 • coordVec 0 + x 1 • coordVec 1 +
      x 2 • coordVec 2 := by
    refine ambient_ext ?_ ?_ ?_ ?_ <;> simp [coordVec_apply]
  conv_lhs => rw [hx]
  simp only [map_add, map_smul, rightAngleRotation_coordVec_three,
    rightAngleRotation_coordVec_zero, rightAngleRotation_coordVec_one,
    rightAngleRotation_coordVec_two]
theorem exists_dihedral_eq_rightAngleRotation :
    ∃ r ∈ dihedralInPlane, ⇑r = ⇑rightAngleRotation := by
  refine ⟨dihedralOfCode (true, 1, -1), dihedralOfCode_mem _, ?_⟩
  funext x
  rw [rightAngleRotation_apply]
  refine ambient_ext ?_ ?_ ?_ ?_
  · rw [dihedralOfCode_apply_zero]
    simp [coordVec_apply]
  · rw [dihedralOfCode_apply_one]
    simp [coordVec_apply]
  · rw [dihedralOfCode_apply_two]
    simp [coordVec_apply]
  · rw [dihedralOfCode_apply_three]
    simp [coordVec_apply]
theorem rightAngleRotation_diagNormalPlus :
    rightAngleRotation diagNormalPlus = -diagNormalMinus := by
  rw [← planeUnit_pi_div_four, rightAngleRotation, rotateInPlane_planeUnit,
    planeUnit_pi_div_four_add_pi_div_two]
theorem rightAngleRotation_diagNormalMinus :
    rightAngleRotation diagNormalMinus = diagNormalPlus := by
  rw [← planeUnit_neg_pi_div_four, rightAngleRotation, rotateInPlane_planeUnit,
    ← planeUnit_pi_div_four]
  congr 1
  ring
theorem rightAngleRotation_pow_two_apply (v : AmbientSpace) :
    (rightAngleRotation ^ 2) v = rightAngleRotation (rightAngleRotation v) := by
  rw [pow_two]
  rfl
theorem rightAngleRotation_pow_three_apply (v : AmbientSpace) :
    (rightAngleRotation ^ 3) v =
      rightAngleRotation (rightAngleRotation (rightAngleRotation v)) := by
  rw [pow_succ, pow_two]
  rfl
theorem dihedralAndRightAngle : DihedralAndRightAngle := by
  refine ⟨⟨dihedralSubgroup, fun w hw => hw.1, rfl⟩, ncard_dihedralInPlane,
    fun r hr => ⟨image_coordPlane hr, dihedral_apply_assemble hr⟩,
    exists_dihedral_eq_rightAngleRotation, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_zero]
    rfl
  · rw [pow_one, rightAngleRotation_coordVec_three]
  · rw [rightAngleRotation_pow_two_apply, rightAngleRotation_coordVec_three,
      rightAngleRotation_coordVec_zero]
  · rw [rightAngleRotation_pow_three_apply, rightAngleRotation_coordVec_three,
      rightAngleRotation_coordVec_zero, map_neg, rightAngleRotation_coordVec_three]
  · rw [pow_zero]
    rfl
  · rw [pow_one, rightAngleRotation_diagNormalPlus]
  · rw [rightAngleRotation_pow_two_apply, rightAngleRotation_diagNormalPlus, map_neg,
      rightAngleRotation_diagNormalMinus]
  · rw [rightAngleRotation_pow_three_apply, rightAngleRotation_diagNormalPlus, map_neg,
      rightAngleRotation_diagNormalMinus, map_neg, rightAngleRotation_diagNormalPlus, neg_neg]
theorem continuous_planeCoords : Continuous planeCoords := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_apply (3 : Fin 4)
  · exact continuous_apply (0 : Fin 4)
theorem continuous_transCoords : Continuous transCoords := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_apply (1 : Fin 4)
  · exact continuous_apply (2 : Fin 4)
theorem continuous_assemble :
    Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => assemble p.1 p.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply (1 : Fin 2)).comp continuous_fst
  · exact (continuous_apply (0 : Fin 2)).comp continuous_snd
  · exact (continuous_apply (1 : Fin 2)).comp continuous_snd
  · exact (continuous_apply (0 : Fin 2)).comp continuous_fst
theorem contDiff_planeCoords : ContDiff ℝ 1 planeCoords := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_apply ℝ ℝ (3 : Fin 4)
  · exact contDiff_apply ℝ ℝ (0 : Fin 4)
theorem contDiff_transCoords : ContDiff ℝ 1 transCoords := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_apply ℝ ℝ (1 : Fin 4)
  · exact contDiff_apply ℝ ℝ (2 : Fin 4)
def coordsHomeomorph : AmbientSpace ≃ₜ (Fin 2 → ℝ) × (Fin 2 → ℝ) where
  toFun x := (planeCoords x, transCoords x)
  invFun p := assemble p.1 p.2
  left_inv _ := ambient_ext rfl rfl rfl rfl
  right_inv p := by
    obtain ⟨y, z⟩ := p
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  continuous_toFun := continuous_planeCoords.prodMk continuous_transCoords
  continuous_invFun := continuous_assemble
theorem contDiff_tensorPlate {α φ : (Fin 2 → ℝ) → ℂ} (hα : ContDiff ℝ 1 α)
    (hφ : ContDiff ℝ 1 φ) : ContDiff ℝ 1 (tensorPlate α φ) :=
  (hα.comp contDiff_planeCoords).mul (hφ.comp contDiff_transCoords)
theorem tsupport_tensorPlate (α φ : (Fin 2 → ℝ) → ℂ) :
    tsupport (tensorPlate α φ) = coordsHomeomorph ⁻¹' (tsupport α ×ˢ tsupport φ) := by
  have hs : Function.support (tensorPlate α φ) =
      coordsHomeomorph ⁻¹' (Function.support α ×ˢ Function.support φ) := by
    ext x
    simp [tensorPlate, coordsHomeomorph]
  rw [tsupport, hs, ← Homeomorph.preimage_closure, closure_prod_eq]
  rfl
theorem tensorPlate_mem_and_tsupport {α φ : (Fin 2 → ℝ) → ℂ} (hα : α ∈ cc1Plane)
    (hφ : φ ∈ transProfiles) :
    tensorPlate α φ ∈ compactC1Complex ∧
      tsupport (tensorPlate α φ) =
        {x | planeCoords x ∈ tsupport α ∧ transCoords x ∈ tsupport φ} := by
  have a : ContDiff ℝ 1 α ∧ IsCompact (tsupport α) ∧ tsupport α ⊆ univ := hα
  have b' : φ ∈ cc1Plane ∧ ∀ x, (φ x).im = 0 := hφ
  have b : ContDiff ℝ 1 φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ univ := b'.1
  refine ⟨?_, tsupport_tensorPlate α φ⟩
  show ContDiff ℝ 1 _ ∧ IsCompact _ ∧ _ ⊆ univ
  refine ⟨contDiff_tensorPlate a.1 b.1, ?_, subset_univ _⟩
  rw [tsupport_tensorPlate]
  exact coordsHomeomorph.isCompact_preimage.2 (a.2.1.prod b.2.1)
theorem tensorPlateSupport : TensorPlateSupport := by
  refine ⟨fun α hα φ hφ => tensorPlate_mem_and_tsupport hα hφ, ?_⟩
  intro α hα α' hα' φ hφ hd
  show Disjoint _ _
  rw [(tensorPlate_mem_and_tsupport hα hφ).2, (tensorPlate_mem_and_tsupport hα' hφ).2,
    Set.disjoint_left]
  rintro x ⟨a, -⟩ ⟨b, -⟩
  exact Set.disjoint_left.1 hd a b
theorem profileCorrProperties : ProfileCorrProperties := by
  intro φ₁ h₁ φ₂ h₂
  have a₁ : φ₁ ∈ cc1Plane ∧ ∀ x, (φ₁ x).im = 0 := h₁
  have a₂ : φ₂ ∈ cc1Plane ∧ ∀ x, (φ₂ x).im = 0 := h₂
  have c₁ : ContDiff ℝ 1 φ₁ ∧ IsCompact (tsupport φ₁) ∧ tsupport φ₁ ⊆ univ := a₁.1
  have c₂ : ContDiff ℝ 1 φ₂ ∧ IsCompact (tsupport φ₂) ∧ tsupport φ₂ ⊆ univ := a₂.1
  have k₁ : Continuous φ₁ := c₁.1.continuous
  have k₂ : Continuous φ₂ := c₂.1.continuous
  have hval : ∀ ζ, profileCorr φ₁ φ₂ ζ = ∫ υ, φ₁ υ * φ₂ (υ + ζ) := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro ζ
    have e : (fun υ => φ₁ υ * φ₂ (υ + ζ)) =
        fun υ => (((φ₁ υ).re * (φ₂ (υ + ζ)).re : ℝ) : ℂ) := by
      funext υ
      apply Complex.ext <;> simp [a₁.2, a₂.2]
    rw [hval, e, integral_complex_ofReal]
    exact Complex.ofReal_im _
  · have e : profileCorr φ₁ φ₂ = fun ζ => ∫ υ in tsupport φ₁, φ₁ υ * φ₂ (υ + ζ) := by
      funext ζ
      rw [hval]
      refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun υ hυ => ?_).symm
      rw [image_eq_zero_of_notMem_tsupport hυ, zero_mul]
    rw [e]
    refine continuous_parametric_integral_of_continuous
      (f := fun ζ υ => φ₁ υ * φ₂ (υ + ζ)) ?_ c₁.2.1
    exact (k₁.comp continuous_snd).mul (k₂.comp (continuous_snd.add continuous_fst))
  · have hK : IsCompact ((fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 - p.2) ''
        (tsupport φ₂ ×ˢ tsupport φ₁)) :=
      (c₂.2.1.prod c₁.2.1).image (continuous_fst.sub continuous_snd)
    refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_minimal ?_ hK.isClosed
    intro ζ hζ
    by_contra hnot
    rw [Function.mem_support] at hζ
    apply hζ
    have e : ∀ υ, φ₁ υ * φ₂ (υ + ζ) = 0 := by
      intro υ
      by_contra hne
      have ha := subset_tsupport φ₁ (left_ne_zero_of_mul hne)
      have hb := subset_tsupport φ₂ (right_ne_zero_of_mul hne)
      exact hnot ⟨(υ + ζ, υ), ⟨hb, ha⟩, by simp⟩
    rw [hval]
    simp only [e, MeasureTheory.integral_zero]
theorem proof : Statement :=
  ⟨reflectionNormalsCount, reflectionNormalsModSign, reflectAcrossTimeAxis, planeNormalsEight,
    planeUnitsAndFrames, dihedralAndRightAngle, tensorPlateSupport, profileCorrProperties⟩
end YangMills.Construction.TwoPoints.ReflectionsPlaneFacts
end
