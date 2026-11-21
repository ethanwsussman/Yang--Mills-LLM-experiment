import YangMills.Construction.Continuum.FirstFactsOnSmoothTestFunctionsAndTuples
import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePieces
import YangMills.Construction.Continuum.PiecesOfTheShellsAndTheirBounds
import YangMills.Construction.Continuum.TaylorFormulaAtAPointOfTheDiagonals
import YangMills.Construction.Continuum.ThreeElementaryInequalitiesInTheCoordinateNorms
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal Topology
noncomputable section
namespace YangMills.Construction.PieceProducts
open YangMills.Construction.PieceSystems YangMills.Construction.ConfigSpace
open YangMills.Construction.PieceScales YangMills.Construction.ShellPieces
open YangMills.Construction.Bumps
variable {n : ℕ}
def partialsAlong (L : List (Fin n × Fin 4)) (g : Config n → ℂ) : Config n → ℂ :=
  L.foldr (fun c h => coordPartial c.1 c.2 h) g
def coordList (α : MultiIndex n) : List (Fin n × Fin 4) :=
  (List.finRange n ×ˢ List.finRange 4).flatMap fun c => List.replicate (α c.1 c.2) c
theorem partialsAlong_append (L L' : List (Fin n × Fin 4)) (g : Config n → ℂ) :
    partialsAlong (L ++ L') g = partialsAlong L (partialsAlong L' g) := by
  simp [partialsAlong, List.foldr_append]
theorem partialsAlong_replicate (k : ℕ) (c : Fin n × Fin 4) (g : Config n → ℂ) :
    partialsAlong (List.replicate k c) g = (coordPartial c.1 c.2)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply']
    simp only [partialsAlong, List.foldr_cons] at ih ⊢
    rw [ih]
theorem coordList_eq_flatMap (α : MultiIndex n) :
    coordList α = (List.finRange n).flatMap fun i =>
      (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ) := by
  have inner : ∀ (i : Fin n) (m : List (Fin 4)),
      (m.map (Prod.mk i)).flatMap (fun c => List.replicate (α c.1 c.2) c) =
        m.flatMap fun μ => List.replicate (α i μ) (i, μ) := by
    intro i m
    induction m with
    | nil => rfl
    | cons μ m ih => simp only [List.map_cons, List.flatMap_cons, ih]
  unfold coordList
  change ((List.finRange n).flatMap fun i => (List.finRange 4).map (Prod.mk i)).flatMap _ = _
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun i _ => inner i _
theorem iteratedPartial_eq_partialsAlong (α : MultiIndex n) (g : Config n → ℂ) :
    iteratedPartial α g = partialsAlong (coordList α) g := by
  rw [coordList_eq_flatMap]
  unfold iteratedPartial
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (h : Config n → ℂ),
      l.foldr (fun μ h' => (coordPartial i μ)^[α i μ] h') h =
        partialsAlong (l.flatMap fun μ => List.replicate (α i μ) (i, μ)) h := by
    intro i l h
    induction l with
    | nil => rfl
    | cons μ l ih =>
      rw [List.foldr_cons, List.flatMap_cons, partialsAlong_append, partialsAlong_replicate, ih]
  have outer : ∀ (l : List (Fin n)) (h : Config n → ℂ),
      l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ h' => (coordPartial i μ)^[α i μ] h') h) h =
        partialsAlong (l.flatMap fun i =>
          (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)) h := by
    intro l h
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.flatMap_cons, partialsAlong_append, inner, ih]
  exact outer _ _
theorem length_coordList (α : MultiIndex n) :
    (coordList α).length = α.order := by
  rw [coordList_eq_flatMap]
  simp [MultiIndex.order, List.length_flatMap, Fin.sum_univ_def]
theorem exists_eq_flatMap_replicate_of_sublist {ι : Type*} [DecidableEq ι] (a : ι → ℕ)
    (E : List ι) (hE : E.Nodup) (L : List ι)
    (hL : L.Sublist (E.flatMap fun c => List.replicate (a c) c)) :
    ∃ b : ι → ℕ, L = E.flatMap fun c => List.replicate (b c) c := by
  induction E generalizing L with
  | nil => exact ⟨0, by simpa using hL⟩
  | cons c E ih =>
    rw [List.flatMap_cons, List.sublist_append_iff] at hL
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := hL
    obtain ⟨k, -, rfl⟩ := List.sublist_replicate_iff.1 h₁
    obtain ⟨b, rfl⟩ := ih (List.nodup_cons.1 hE).2 l₂ h₂
    refine ⟨Function.update b c k, ?_⟩
    rw [List.flatMap_cons, Function.update_self]
    congr 1
    refine List.flatMap_congr fun d hd => ?_
    have : d ≠ c := fun h => (List.nodup_cons.1 hE).1 (h ▸ hd)
    rw [Function.update_of_ne this]
theorem exists_coordList_eq_of_sublist (α : MultiIndex n) (L : List (Fin n × Fin 4))
    (hL : L.Sublist (coordList α)) :
    ∃ γ : MultiIndex n, L = coordList γ := by
  obtain ⟨b, rfl⟩ := exists_eq_flatMap_replicate_of_sublist
    (fun c : Fin n × Fin 4 => α c.1 c.2) _
    ((List.nodup_finRange n).product (List.nodup_finRange 4)) L hL
  exact ⟨fun i μ => b (i, μ), rfl⟩
theorem coordPartial_apply_eq_fderiv {a : Config n → ℂ} (ha : ContDiff ℝ ∞ a) (i : Fin n)
    (μ : Fin 4) (x : Config n) :
    coordPartial i μ a x = fderiv ℝ a x (Pi.single i (Pi.single μ 1)) :=
  ((ha.differentiable (by simp)) x).lineDeriv_eq_fderiv
theorem contDiff_coordPartial {a : Config n → ℂ} (ha : ContDiff ℝ ∞ a) (i : Fin n) (μ : Fin 4) :
    ContDiff ℝ ∞ (coordPartial i μ a) := by
  have : coordPartial i μ a = fun x => fderiv ℝ a x (Pi.single i (Pi.single μ 1)) :=
    funext (coordPartial_apply_eq_fderiv ha i μ)
  rw [this]
  exact (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_partialsAlong (L : List (Fin n × Fin 4)) {a : Config n → ℂ}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (partialsAlong L a) := by
  induction L with
  | nil => exact ha
  | cons c L ih => exact contDiff_coordPartial ih c.1 c.2
theorem coordPartial_add {a b : Config n → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (i : Fin n) (μ : Fin 4) :
    coordPartial i μ (a + b) = coordPartial i μ a + coordPartial i μ b := by
  funext x
  have da := (ha.differentiable (by simp)) x
  have db := (hb.differentiable (by simp)) x
  have hab : ContDiff ℝ ∞ (a + b) := ha.add hb
  rw [Pi.add_apply, coordPartial_apply_eq_fderiv hab, coordPartial_apply_eq_fderiv ha,
    coordPartial_apply_eq_fderiv hb, fderiv_add da db]
  rfl
theorem partialsAlong_add (L : List (Fin n × Fin 4)) {a b : Config n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    partialsAlong L (a + b) = partialsAlong L a + partialsAlong L b := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    have : partialsAlong (c :: L) (a + b) = coordPartial c.1 c.2 (partialsAlong L (a + b)) :=
      rfl
    rw [this, ih]
    exact coordPartial_add (contDiff_partialsAlong L ha) (contDiff_partialsAlong L hb) c.1 c.2
theorem coordPartial_mul {a b : Config n → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (i : Fin n) (μ : Fin 4) :
    coordPartial i μ (a * b) =
      coordPartial i μ a * b + a * coordPartial i μ b := by
  funext x
  have da := (ha.differentiable (by simp)) x
  have db := (hb.differentiable (by simp)) x
  have hab : ContDiff ℝ ∞ (a * b) := ha.mul hb
  rw [Pi.add_apply, Pi.mul_apply, Pi.mul_apply, coordPartial_apply_eq_fderiv hab,
    coordPartial_apply_eq_fderiv ha, coordPartial_apply_eq_fderiv hb, fderiv_mul da db]
  simp [mul_comm, add_comm]
theorem norm_partialsAlong_mul_le {s C M : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (x : Config n) (L : List (Fin n × Fin 4)) :
    ∀ (f g : Config n → ℂ) (e₁ e₂ : ℕ), ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ L₁ : List (Fin n × Fin 4), L₁.Sublist L →
        s ^ (L₁.length + e₁) * ‖partialsAlong L₁ f x‖ ≤ C) →
      (∀ L₂ : List (Fin n × Fin 4), L₂.Sublist L →
        s ^ (L₂.length + e₂) * ‖partialsAlong L₂ g x‖ ≤ M) →
      s ^ (L.length + e₁ + e₂) * ‖partialsAlong L (f * g) x‖ ≤ 2 ^ L.length * (C * M) := by
  induction L using List.reverseRecOn with
  | nil =>
    intro f g e₁ e₂ _ _ h₁ h₂
    have a₁ := h₁ [] (List.Sublist.refl _)
    have a₂ := h₂ [] (List.Sublist.refl _)
    simp only [List.length_nil, zero_add, partialsAlong, List.foldr_nil] at a₁ a₂ ⊢
    rw [Pi.mul_apply, norm_mul, pow_add, pow_zero, one_mul]
    calc s ^ e₁ * s ^ e₂ * (‖f x‖ * ‖g x‖) = (s ^ e₁ * ‖f x‖) * (s ^ e₂ * ‖g x‖) := by ring
      _ ≤ C * M := mul_le_mul a₁ a₂ (by positivity) hC
  | append_singleton L c ih =>
    intro f g e₁ e₂ hf hg h₁ h₂
    have hf' := contDiff_coordPartial hf c.1 c.2
    have hg' := contDiff_coordPartial hg c.1 c.2
    have step : ∀ (L' : List (Fin n × Fin 4)) (a : Config n → ℂ),
        partialsAlong (L' ++ [c]) a = partialsAlong L' (coordPartial c.1 c.2 a) := by
      intro L' a
      rw [partialsAlong_append]
      rfl
    have sub : ∀ L' : List (Fin n × Fin 4), L'.Sublist L → L'.Sublist (L ++ [c]) :=
      fun L' h => h.trans (List.sublist_append_left _ _)
    have sub' : ∀ L' : List (Fin n × Fin 4), L'.Sublist L → (L' ++ [c]).Sublist (L ++ [c]) :=
      fun L' h => h.append (List.Sublist.refl _)
    have i₁ := ih (coordPartial c.1 c.2 f) g (e₁ + 1) e₂ hf' hg
      (fun L₁ h => by
        have := h₁ _ (sub' L₁ h)
        rw [step, List.length_append, List.length_singleton] at this
        have e : L₁.length + (e₁ + 1) = L₁.length + 1 + e₁ := by ring
        rwa [e])
      (fun L₂ h => h₂ _ (sub L₂ h))
    have i₂ := ih f (coordPartial c.1 c.2 g) e₁ (e₂ + 1) hf hg'
      (fun L₁ h => h₁ _ (sub L₁ h))
      (fun L₂ h => by
        have := h₂ _ (sub' L₂ h)
        rw [step, List.length_append, List.length_singleton] at this
        have e : L₂.length + (e₂ + 1) = L₂.length + 1 + e₂ := by ring
        rwa [e])
    have m₁ : ContDiff ℝ ∞ (coordPartial c.1 c.2 f * g) := hf'.mul hg
    have m₂ : ContDiff ℝ ∞ (f * coordPartial c.1 c.2 g) := hf.mul hg'
    rw [step, coordPartial_mul hf hg, partialsAlong_add L m₁ m₂, Pi.add_apply,
      List.length_append, List.length_singleton]
    have e₃ : L.length + 1 + e₁ + e₂ = L.length + (e₁ + 1) + e₂ := by ring
    have e₄ : L.length + 1 + e₁ + e₂ = L.length + e₁ + (e₂ + 1) := by ring
    have hp : 0 ≤ s ^ (L.length + 1 + e₁ + e₂) := pow_nonneg hs _
    calc s ^ (L.length + 1 + e₁ + e₂) * ‖partialsAlong L (coordPartial c.1 c.2 f * g) x +
            partialsAlong L (f * coordPartial c.1 c.2 g) x‖
        ≤ s ^ (L.length + 1 + e₁ + e₂) * (‖partialsAlong L (coordPartial c.1 c.2 f * g) x‖ +
            ‖partialsAlong L (f * coordPartial c.1 c.2 g) x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hp
      _ = s ^ (L.length + (e₁ + 1) + e₂) *
              ‖partialsAlong L (coordPartial c.1 c.2 f * g) x‖ +
            s ^ (L.length + e₁ + (e₂ + 1)) *
              ‖partialsAlong L (f * coordPartial c.1 c.2 g) x‖ := by
          rw [mul_add]
          congr 2
          · rw [e₃]
          · rw [e₄]
      _ ≤ 2 ^ L.length * (C * M) + 2 ^ L.length * (C * M) := add_le_add i₁ i₂
      _ = 2 ^ (L.length + 1) * (C * M) := by ring
theorem norm_iteratedPartial_mul_le {s C M : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (x : Config n) {f g : Config n → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (K : ℕ)
    (h₁ : ∀ γ : MultiIndex n, γ.order ≤ K → s ^ γ.order * ‖iteratedPartial γ f x‖ ≤ C)
    (h₂ : ∀ γ : MultiIndex n, γ.order ≤ K → s ^ γ.order * ‖iteratedPartial γ g x‖ ≤ M)
    (α : MultiIndex n) (hα : α.order ≤ K) :
    s ^ α.order * ‖iteratedPartial α (f * g) x‖ ≤ 2 ^ α.order * (C * M) := by
  have key := norm_partialsAlong_mul_le hs hC hM x (coordList α) f g 0 0 hf hg
    (fun L₁ h => by
      obtain ⟨γ, rfl⟩ := exists_coordList_eq_of_sublist α L₁ h
      have hγ : γ.order ≤ K := by
        rw [← length_coordList γ]
        exact h.length_le.trans ((length_coordList α).le.trans hα)
      have := h₁ γ hγ
      rwa [iteratedPartial_eq_partialsAlong, ← length_coordList γ] at this)
    (fun L₂ h => by
      obtain ⟨γ, rfl⟩ := exists_coordList_eq_of_sublist α L₂ h
      have hγ : γ.order ≤ K := by
        rw [← length_coordList γ]
        exact h.length_le.trans ((length_coordList α).le.trans hα)
      have := h₂ γ hγ
      rwa [iteratedPartial_eq_partialsAlong, ← length_coordList γ] at this)
  rw [iteratedPartial_eq_partialsAlong, ← length_coordList α]
  simpa using key
theorem coordPartial_eventuallyEq_zero {g : Config n → ℂ} {x : Config n} (h : g =ᶠ[𝓝 x] 0)
    (i : Fin n) (μ : Fin 4) : coordPartial i μ g =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  change lineDeriv ℝ g y _ = 0
  rw [hy.lineDeriv_eq]
  simp [lineDeriv]
theorem iteratedPartial_eq_zero_of_eventuallyEq {g : Config n → ℂ} {x : Config n}
    (h : g =ᶠ[𝓝 x] 0) (α : MultiIndex n) : iteratedPartial α g x = 0 := by
  rw [iteratedPartial_eq_partialsAlong]
  have all : ∀ L : List (Fin n × Fin 4), partialsAlong L g =ᶠ[𝓝 x] 0 := by
    intro L
    induction L with
    | nil => exact h
    | cons c L ih => exact coordPartial_eventuallyEq_zero ih c.1 c.2
  exact (all _).self_of_nhds
theorem scaledSupNorm_le_of_forall {ν : ℕ} {m R : ℝ} {Ψ : Config n → ℂ} (hm : 0 ≤ m)
    (hR : 0 ≤ R)
    (h : ∀ α : MultiIndex n, α.order ≤ ν → ∀ x, m ^ α.order * ‖iteratedPartial α Ψ x‖ ≤ R) :
    scaledSupNorm ν m Ψ ≤ R := by
  unfold scaledSupNorm
  refine Real.iSup_le (fun α => ?_) hR
  unfold TestFunctions.uniformNorm
  rw [Real.mul_iSup_of_nonneg (pow_nonneg hm _)]
  exact Real.iSup_le (fun x => h α.1 α.2 x) hR
theorem decaySeminorm_lt_top {φ : Config n → ℂ} (hφ : φ ∈ schwartzSet n) (k q : ℕ) :
    decaySeminorm k q φ < ⊤ := by
  have hfin : ({α : MultiIndex n | α.order ≤ q}).Finite := by
    refine (Set.finite_Icc (0 : MultiIndex n) (fun _ _ => q)).subset ?_
    intro α hα
    refine ⟨fun i μ => Nat.zero_le _, fun i μ => ?_⟩
    calc α i μ ≤ ∑ μ', α i μ' :=
          Finset.single_le_sum (f := fun μ' => α i μ') (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ μ)
      _ ≤ ∑ i', ∑ μ', α i' μ' :=
          Finset.single_le_sum (f := fun i' => ∑ μ', α i' μ') (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
      _ ≤ q := hα
  have hb : hfin.toFinset.sup (fun α : MultiIndex n =>
      ⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖)) < ⊤ :=
    (Finset.sup_lt_iff (by simp)).2 (fun α _ => hφ.2 k α)
  refine lt_of_le_of_lt ?_ hb
  unfold decaySeminorm
  refine iSup_le fun α => iSup_le fun h => ?_
  exact Finset.le_sup (f := fun α : MultiIndex n =>
    ⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖))
    (hfin.mem_toFinset.2 h)
theorem one_le_normalizerBound' : 1 ≤ normalizerBound := le_max_left _ _
theorem one_le_derivConst_mul (hn : 1 ≤ n) : 1 ≤ derivConst * n := by
  have hr := isSideConstant_sideConstant
  have h1 : 1 ≤ sideConstant⁻¹ := (one_le_inv₀ hr.1).2 (by linarith [hr.2])
  have h2 : (1 : ℝ) ≤ derivConst := by
    unfold derivConst
    have h3 := le_max_right DiagonalShells.tupleCutoffConst
      (2 * twiceGevreyConst * sideConstant⁻¹)
    have h4 : twiceGevreyConst = 18 := by
      unfold twiceGevreyConst gevreyConst
      norm_num
    rw [h4] at h3 ⊢
    linarith
  have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith
theorem derivBound_nonneg' (hn : 1 ≤ n) (r : ℕ) : 0 ≤ derivBound n r := by
  have h := one_le_derivConst_mul hn
  have hA : 0 ≤ normalizerBound := by linarith [one_le_normalizerBound']
  unfold derivBound
  positivity
theorem derivBound_le_of_le (hn : 1 ≤ n) {g K : ℕ} (hgK : g ≤ K) :
    derivBound n g ≤ derivBound n K := by
  have h := one_le_derivConst_mul hn
  have hA : 0 ≤ normalizerBound := by linarith [one_le_normalizerBound']
  have h1 := pow_le_pow_right₀ h hgK
  have h2 : ((g.factorial : ℝ)) ^ 2 ≤ (K.factorial : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.factorial_le hgK) 2
  unfold derivBound
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity)
    (by positivity)
theorem leibnizConst_nonneg' (hn : 1 ≤ n) : 0 ≤ leibnizConst n := by
  have := derivBound_nonneg' hn (5 * n + 1)
  unfold leibnizConst
  positivity
theorem taylorConst_nonneg' (n : ℕ) : 0 ≤ taylorConst n := by
  unfold taylorConst weightConst
  positivity
theorem dyadicScale_pos' (j : ℕ) : 0 < dyadicScale j := zpow_pos (by norm_num) _
theorem dyadicScale_mul_two_pow (j : ℕ) : dyadicScale j * 2 ^ j = 1 := by
  unfold dyadicScale
  rw [zpow_neg, zpow_natCast]
  exact inv_mul_cancel₀ (by positivity)
theorem dyadicScale_le_one' (j : ℕ) : dyadicScale j ≤ 1 := by
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2 := dyadicScale_mul_two_pow j
  have h3 := dyadicScale_pos' j
  nlinarith
theorem dyadicScale_le_half {j : ℕ} (hj : 1 ≤ j) : dyadicScale j ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have h2 := dyadicScale_mul_two_pow j
  have h3 := dyadicScale_pos' j
  nlinarith
theorem pieceSide_nonneg' (j : ℕ) : 0 ≤ pieceSide j :=
  mul_nonneg isSideConstant_sideConstant.1.le (dyadicScale_pos' j).le
theorem pieceSide_le_one' (j : ℕ) : pieceSide j ≤ 1 := by
  have h := isSideConstant_sideConstant
  have h1 := dyadicScale_le_one' j
  unfold pieceSide
  nlinarith [h.1, h.2]
theorem pieceSide_pow_mul_norm_le (hn : 1 ≤ n) {j : ℕ} {z : LatticePt n} {x : Config n}
    (hder : ∀ (γ : MultiIndex n) (x : Config n),
      ‖iteratedPartial γ (ShellPieceBounds.pieceC j z) x‖ ≤
        derivBound n γ.order * 2 ^ (j * γ.order))
    (γ : MultiIndex n) (hγ : γ.order ≤ 5 * n + 1) :
    pieceSide j ^ γ.order * ‖iteratedPartial γ (ShellPieceBounds.pieceC j z) x‖ ≤
      derivBound n (5 * n + 1) := by
  have hr := isSideConstant_sideConstant
  have e : pieceSide j ^ γ.order * 2 ^ (j * γ.order) = sideConstant ^ γ.order := by
    unfold pieceSide
    rw [pow_mul, mul_pow, mul_assoc, ← mul_pow, dyadicScale_mul_two_pow, one_pow, mul_one]
  have h1 : sideConstant ^ γ.order ≤ 1 := pow_le_one₀ hr.1.le (by linarith [hr.2])
  have hb := derivBound_nonneg' hn γ.order
  calc pieceSide j ^ γ.order *
        ‖iteratedPartial γ (ShellPieceBounds.pieceC j z) x‖
      ≤ pieceSide j ^ γ.order * (derivBound n γ.order * 2 ^ (j * γ.order)) :=
        mul_le_mul_of_nonneg_left (hder γ x) (pow_nonneg (pieceSide_nonneg' j) _)
    _ = derivBound n γ.order * sideConstant ^ γ.order := by rw [← e]; ring
    _ ≤ derivBound n γ.order * 1 := mul_le_mul_of_nonneg_left h1 hb
    _ = derivBound n γ.order := mul_one _
    _ ≤ derivBound n (5 * n + 1) := derivBound_le_of_le hn hγ
theorem scaledSupNorm_pieceMul_le (hn : 1 ≤ n) (j : ℕ) (z : LatticePt n)
    (hpf : ShellPieceBounds.PieceProperties j z) {φ : Config n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ openBox j z, ∀ β : MultiIndex n, β.order ≤ 5 * n + 1 →
      ‖iteratedPartial β φ x‖ ≤ B) :
    scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ) ≤ leibnizConst n * B := by
  obtain ⟨hu, -, hsup, hbox, -, -, -, hder⟩ := hpf
  have hC := derivBound_nonneg' hn (5 * n + 1)
  have hs0 := pieceSide_nonneg' j
  refine scaledSupNorm_le_of_forall hs0 (mul_nonneg (leibnizConst_nonneg' hn) hB0)
    fun α hα x => ?_
  by_cases hx : x ∈ tsupport (piece j z)
  · have hxo := hbox (hsup hx)
    have key := norm_iteratedPartial_mul_le hs0 hC hB0 x hu.1 hφ (5 * n + 1)
      (fun γ hγ => pieceSide_pow_mul_norm_le hn hder γ hγ)
      (fun γ hγ => by
        have h1 : pieceSide j ^ γ.order ≤ 1 := pow_le_one₀ hs0 (pieceSide_le_one' j)
        have h2 := hB x hxo γ hγ
        calc pieceSide j ^ γ.order * ‖iteratedPartial γ φ x‖ ≤ 1 * B :=
              mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
          _ = B := one_mul B)
      α hα
    have e : pieceMul j z φ = ShellPieceBounds.pieceC j z * φ := rfl
    rw [e]
    calc pieceSide j ^ α.order *
          ‖iteratedPartial α (ShellPieceBounds.pieceC j z * φ) x‖
        ≤ 2 ^ α.order * (derivBound n (5 * n + 1) * B) := key
      _ ≤ 2 ^ (5 * n + 1) * (derivBound n (5 * n + 1) * B) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hα) (mul_nonneg hC hB0)
      _ = leibnizConst n * B := by
          unfold leibnizConst
          ring
  · have hev : pieceMul j z φ =ᶠ[𝓝 x] 0 := by
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hx
      filter_upwards [h0] with y hy
      have hy' : piece j z y = 0 := hy
      simp [pieceMul, hy']
    rw [iteratedPartial_eq_zero_of_eventuallyEq hev]
    simpa using mul_nonneg (leibnizConst_nonneg' hn) hB0
theorem le_mul_mul_inv_of_le {A X Y W P : ℝ} (hA : 0 ≤ A) (hY : 0 < Y) (hW : 0 ≤ W)
    (hYX : Y ≤ W * X) (hXA : X * A ≤ P) : A ≤ W * P * Y⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ hY]
  calc A * Y ≤ A * (W * X) := mul_le_mul_of_nonneg_left hYX hA
    _ = W * (X * A) := by ring
    _ ≤ W * P := mul_le_mul_of_nonneg_left hXA hW
theorem diagDistConst_le_eight : diagDistConst ≤ 8 := by
  have hr := isSideConstant_sideConstant
  have h1 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  unfold diagDistConst pairDistConst
  calc Real.sqrt 2 * (4 + 2 * sideConstant) ≤ 3 / 2 * (4 + 2 * (1 / 6)) :=
        mul_le_mul h1 (by linarith [hr.2]) (by linarith [hr.1]) (by norm_num)
    _ ≤ 8 := by norm_num
theorem dyadicScale_pow_eq (j r : ℕ) : dyadicScale j ^ r = (2 : ℝ) ^ (-((j * r : ℕ) : ℤ)) := by
  unfold dyadicScale
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring
theorem one_add_sqrt_pow_mul_five_pow_le (hn : 1 ≤ n) (k : ℕ) :
    (1 + Real.sqrt n) ^ k * 5 ^ k ≤ (weightConst * Real.sqrt n) ^ k := by
  have h1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  unfold weightConst
  linarith
theorem norm_iteratedPartial_le_of_shell (hn : 2 ≤ n) (hT : taylorBoundNearDiagonal)
    (hE : CoordNormBounds.inequalitiesClaim)
    (hmono : TupleFacts.SeminormMonotone n) {j : ℕ} (hj : 1 ≤ j)
    {z : LatticePt n} (hcb : ShellPieceBounds.BoxGeometry j z)
    {φ : Config n → ℂ} (hφ : φ ∈ flatSchwartzSet n) {r : ℕ} (hr : 1 ≤ r) :
    ∀ x ∈ openBox j z, ∀ β : MultiIndex n, β.order ≤ 5 * n + 1 →
      ‖iteratedPartial β φ x‖ ≤
        taylorConst n * (2 : ℝ) ^ (-((j * r : ℕ) : ℤ)) *
          ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹ *
          (decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ).toReal := by
  intro x hx β hβ
  obtain ⟨-, -, -, hnear, hw⟩ := hcb
  obtain ⟨-, y, hy, hxy⟩ := hnear hj x hx
  obtain ⟨-, hyx, -⟩ := hw x hx
  have hN := decaySeminorm_lt_top hφ.1 (4 * n + 2) (5 * n + 1 + r)
  have hNr : 0 ≤ (decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ).toReal := ENNReal.toReal_nonneg
  have hsc := dyadicScale_pos' j
  have hsc2 := dyadicScale_le_half hj
  have hδ : 0 < 8 * dyadicScale j := by positivity
  have hxy' : euclidNorm (x - y) ≤ 8 * dyadicScale j :=
    hxy.trans (mul_le_mul_of_nonneg_right diagDistConst_le_eight hsc.le)
  have T := (hT n hn φ hφ y hy x β r hr).2 (8 * dyadicScale j) hδ hxy' (4 * n + 2)
  have mono := hmono φ hφ.1 (4 * n + 2) (β.order + r) (4 * n + 2) (5 * n + 1 + r) le_rfl
    (by omega)
  have hx0 : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
  have hc0 : 0 ≤ euclidNorm (pieceCentre j z) := Real.sqrt_nonneg _
  have c0 : 0 ≤ (1 + 8 * dyadicScale j) ^ (4 * n + 2) *
      ((4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ)) := by positivity
  have T2 : ENNReal.ofReal ((1 + euclidNorm x) ^ (4 * n + 2) * ‖iteratedPartial β φ x‖) ≤
      ENNReal.ofReal (((1 + 8 * dyadicScale j) ^ (4 * n + 2) *
        ((4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ))) *
        (decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ).toReal) := by
    rw [ENNReal.ofReal_mul c0, ENNReal.ofReal_toReal hN.ne]
    exact T.trans (mul_le_mul_right mono _)
  have T3 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg c0 hNr)).1 T2
  have hb1 : (1 + 8 * dyadicScale j) ^ (4 * n + 2) ≤ (5 : ℝ) ^ (4 * n + 2) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hrf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hb2 : (4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ) ≤
      Real.exp (32 * n) * (2 : ℝ) ^ (-((j * r : ℕ) : ℤ)) := by
    have hE' := hE.2.1 r (32 * n) (by positivity)
    rw [← dyadicScale_pow_eq, div_le_iff₀ hrf]
    have e : 4 * (n : ℝ) * (8 * dyadicScale j) = 32 * n * dyadicScale j := by ring
    rw [e, mul_pow]
    calc (32 * (n : ℝ)) ^ r * dyadicScale j ^ r ≤
          ((r.factorial : ℝ) * Real.exp (32 * n)) * dyadicScale j ^ r :=
          mul_le_mul_of_nonneg_right hE' (by positivity)
      _ = Real.exp (32 * n) * dyadicScale j ^ r * r.factorial := by ring
  have hb : (1 + 8 * dyadicScale j) ^ (4 * n + 2) *
      ((4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ)) ≤
      5 ^ (4 * n + 2) * (Real.exp (32 * n) * (2 : ℝ) ^ (-((j * r : ℕ) : ℤ))) :=
    mul_le_mul hb1 hb2 (by positivity) (by positivity)
  have hP := T3.trans (mul_le_mul_of_nonneg_right hb hNr)
  have hY : 0 < (1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2) := by positivity
  have hYX : (1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2) ≤
      (1 + Real.sqrt n) ^ (4 * n + 2) * (1 + euclidNorm x) ^ (4 * n + 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hyx _
  have main := le_mul_mul_inv_of_le (norm_nonneg _) hY (by positivity) hYX hP
  have hS : 0 ≤ Real.exp (32 * n) * (2 : ℝ) ^ (-((j * r : ℕ) : ℤ)) *
      ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹ *
      (decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ).toReal := by positivity
  calc ‖iteratedPartial β φ x‖ ≤ _ := main
    _ = ((1 + Real.sqrt n) ^ (4 * n + 2) * 5 ^ (4 * n + 2)) *
        (Real.exp (32 * n) * (2 : ℝ) ^ (-((j * r : ℕ) : ℤ)) *
          ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹ *
          (decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ).toReal) := by ring
    _ ≤ (weightConst * Real.sqrt n) ^ (4 * n + 2) * _ :=
        mul_le_mul_of_nonneg_right (one_add_sqrt_pow_mul_five_pow_le (by omega) _) hS
    _ = _ := by
        unfold taylorConst
        ring
theorem norm_iteratedPartial_le_of_base (hn : 1 ≤ n) {z : LatticePt n}
    (hcb : ShellPieceBounds.BoxGeometry 0 z)
    {φ : Config n → ℂ} (hφ : φ ∈ flatSchwartzSet n) :
    ∀ x ∈ openBox 0 z, ∀ β : MultiIndex n, β.order ≤ 5 * n + 1 →
      ‖iteratedPartial β φ x‖ ≤
        taylorConst n * ((1 + euclidNorm (pieceCentre 0 z)) ^ (4 * n + 2))⁻¹ *
          (decaySeminorm (4 * n + 2) (5 * n + 1) φ).toReal := by
  intro x hx β hβ
  obtain ⟨-, -, -, -, hw⟩ := hcb
  obtain ⟨-, hyx, -⟩ := hw x hx
  have hN := decaySeminorm_lt_top hφ.1 (4 * n + 2) (5 * n + 1)
  have hc0 : 0 ≤ euclidNorm (pieceCentre 0 z) := Real.sqrt_nonneg _
  have T : ENNReal.ofReal ((1 + euclidNorm x) ^ (4 * n + 2) * ‖iteratedPartial β φ x‖) ≤
      decaySeminorm (4 * n + 2) (5 * n + 1) φ := by
    unfold decaySeminorm
    exact le_iSup_of_le β (le_iSup_of_le hβ (le_iSup_of_le x le_rfl))
  have hP := (ENNReal.ofReal_le_iff_le_toReal hN.ne).1 T
  have hY : 0 < (1 + euclidNorm (pieceCentre 0 z)) ^ (4 * n + 2) := by positivity
  have hYX : (1 + euclidNorm (pieceCentre 0 z)) ^ (4 * n + 2) ≤
      (1 + Real.sqrt n) ^ (4 * n + 2) * (1 + euclidNorm x) ^ (4 * n + 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hyx _
  have main := le_mul_mul_inv_of_le (norm_nonneg _) hY (by positivity) hYX hP
  have h1 : (1 + Real.sqrt n) ^ (4 * n + 2) ≤ taylorConst n := by
    have h2 := one_add_sqrt_pow_mul_five_pow_le hn (4 * n + 2)
    have h3 : (1 : ℝ) ≤ 5 ^ (4 * n + 2) := one_le_pow₀ (by norm_num)
    have h4 : (1 : ℝ) ≤ Real.exp (32 * n) := Real.one_le_exp (by positivity)
    have h5 : 0 ≤ (1 + Real.sqrt n) ^ (4 * n + 2) := by positivity
    have h6 : 0 ≤ (weightConst * Real.sqrt n) ^ (4 * n + 2) := by
      unfold weightConst
      positivity
    unfold taylorConst
    nlinarith
  have hS : 0 ≤ ((1 + euclidNorm (pieceCentre 0 z)) ^ (4 * n + 2))⁻¹ *
      (decaySeminorm (4 * n + 2) (5 * n + 1) φ).toReal := by positivity
  calc ‖iteratedPartial β φ x‖ ≤ _ := main
    _ = (1 + Real.sqrt n) ^ (4 * n + 2) * (((1 + euclidNorm (pieceCentre 0 z)) ^ (4 * n + 2))⁻¹ *
          (decaySeminorm (4 * n + 2) (5 * n + 1) φ).toReal) := by ring
    _ ≤ taylorConst n * _ := mul_le_mul_of_nonneg_right h1 hS
    _ = _ := by ring
theorem ofReal_le_ofReal_mul_of_le {a c : ℝ} {N : ℝ≥0∞} (hN : N < ⊤) (hc : 0 ≤ c)
    (h : a ≤ c * N.toReal) : ENNReal.ofReal a ≤ ENNReal.ofReal c * N := by
  have e : ENNReal.ofReal c * N = ENNReal.ofReal (c * N.toReal) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hN.ne]
  rw [e]
  exact ENNReal.ofReal_le_ofReal h
theorem productBounds_holds (hPieces : ShellPieceBounds.ShellPiecesBound)
    (hTaylor : taylorBoundNearDiagonal)
    (hElementary : CoordNormBounds.inequalitiesClaim)
    (hFacts : TupleFacts.BasicFacts) : PieceProducts.ProductBounds := by
  unfold PieceProducts.ProductBounds
  intro n hn j z hp Q
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hNest, hPF, -, -, hCB, -⟩ := hPieces n hn1
  have hpf := hPF j z
  have hcb : ShellPieceBounds.BoxGeometry j z := hCB (j, z) hp
  have hmono := (hFacts n hn).2.2.1
  have hL := leibnizConst_nonneg' hn1
  have hTn := taylorConst_nonneg' n
  have hc0 : 0 ≤ euclidNorm (pieceCentre j z) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · have hsep : ENNReal.ofReal (1 / 2 * (2 : ℝ) ^ (-(j : ℤ))) ≤ Q.boxGap := by
      refine le_iInf fun i => le_iInf fun i' => le_iInf fun hne => ?_
      have h := hcb.2.2.1 i i' hne
      have e : 1 / 2 * (2 : ℝ) ^ (-(j : ℤ)) = dyadicScale j / 2 := by
        unfold dyadicScale
        ring
      rw [e]
      exact h
    refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hsep, fun i => rfl,
      fun i => rfl, fun i => rfl, hsep, fun φ hφ => ?_⟩
    obtain ⟨hu, -, hsup, hbox, hcube, -⟩ := hpf
    have hsm : ContDiff ℝ ∞ (pieceMul j z φ) := hu.1.mul hφ
    have hts : tsupport (pieceMul j z φ) ⊆ tsupport φ ∩ cylinderSet Q.box := by
      intro x hx
      refine ⟨tsupport_mul_subset_right hx, ?_⟩
      have hsub : tsupport (pieceMul j z φ) ⊆ tsupport (piece j z) := by
        refine closure_mono fun y hy h0 => hy ?_
        have h0' : piece j z y = 0 := h0
        simp [pieceMul, h0']
      exact hcube (hbox (hsup (hsub hx)))
    exact ⟨hsm, hts, hsm, fun x hx i => ((hNest j z i).1 ((hts hx).2 i))⟩
  · intro φ hφ
    refine ⟨fun hj r hr => ?_, fun hj => ?_⟩
    · have hN := decaySeminorm_lt_top hφ.1 (4 * n + 2) (5 * n + 1 + r)
      have hNr : 0 ≤ (decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ).toReal :=
        ENNReal.toReal_nonneg
      have hs := scaledSupNorm_pieceMul_le hn1 j z hpf hφ.1.1 (by positivity)
        (norm_iteratedPartial_le_of_shell hn hTaylor hElementary hmono hj hcb hφ hr)
      refine ofReal_le_ofReal_mul_of_le hN (by positivity) (hs.trans (le_of_eq ?_))
      ring
    · subst hj
      have hN := decaySeminorm_lt_top hφ.1 (4 * n + 2) (5 * n + 1)
      have hNr : 0 ≤ (decaySeminorm (4 * n + 2) (5 * n + 1) φ).toReal :=
        ENNReal.toReal_nonneg
      have hs := scaledSupNorm_pieceMul_le hn1 0 z hpf hφ.1.1 (by positivity)
        (norm_iteratedPartial_le_of_base hn1 hcb hφ)
      refine ofReal_le_ofReal_mul_of_le hN (by positivity) (hs.trans (le_of_eq ?_))
      ring
end YangMills.Construction.PieceProducts
end
