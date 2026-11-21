import YangMills.Construction.TorusOrFourSpace.DerivativesOfFunctionsOfSeveralPointsProof
import YangMills.Construction.TorusOrFourSpace.PartialsOfSumsAndProducts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SumsProductsPartials
open Coords
variable {p : ℕ+}
theorem continuous_of_contPartialsUpTo {ν : ℕ} {G : Coords p → ℂ}
    (h : ContPartialsUpTo ν G) : Continuous G := by apply _root_.YangMills.Construction.PeriodicSpace.TupleDerivatives.continuous_of_contPartialsUpTo <;> assumption
theorem contPartialsUpTo_of_succ : ∀ {ν : ℕ} {G : Coords p → ℂ},
    ContPartialsUpTo (ν + 1) G → ContPartialsUpTo ν G
  | 0, _, hf => hf.1
  | _ + 1, _, hf => ⟨hf.1, fun j => ⟨(hf.2 j).1, contPartialsUpTo_of_succ (hf.2 j).2⟩⟩
theorem hasLineDerivAt_linComb {G H : Coords p → ℂ} {x v : Coords p} (a b : ℂ)
    (hG : LineDifferentiableAt ℝ G x v) (hH : LineDifferentiableAt ℝ H x v) :
    HasLineDerivAt ℝ (a • G + b • H) (a • lineDeriv ℝ G x v + b • lineDeriv ℝ H x v) x v := by
  have h1 := hG.hasLineDerivAt
  have h2 := hH.hasLineDerivAt
  unfold HasLineDerivAt at *
  exact (h1.const_smul a).add (h2.const_smul b)
theorem hasLineDerivAt_prod {G H : Coords p → ℂ} {x v : Coords p}
    (hG : LineDifferentiableAt ℝ G x v) (hH : LineDifferentiableAt ℝ H x v) :
    HasLineDerivAt ℝ (G * H) (lineDeriv ℝ G x v * H x + G x * lineDeriv ℝ H x v) x v := by
  have h1 := hG.hasLineDerivAt
  have h2 := hH.hasLineDerivAt
  unfold HasLineDerivAt at *
  have h3 := h1.mul h2
  simp only [zero_smul, add_zero] at h3
  exact h3
theorem partialAlong_linComb {G H : Coords p → ℂ} (j : Fin (4 * (p : ℕ))) (a b : ℂ)
    (hG : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hH : ∀ x, LineDifferentiableAt ℝ H x (Pi.single j 1)) :
    partialAlong j (a • G + b • H) = a • partialAlong j G + b • partialAlong j H := by
  funext x
  exact (hasLineDerivAt_linComb a b (hG x) (hH x)).lineDeriv
theorem partialAlong_mul {G H : Coords p → ℂ} (j : Fin (4 * (p : ℕ)))
    (hG : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hH : ∀ x, LineDifferentiableAt ℝ H x (Pi.single j 1)) :
    partialAlong j (G * H) = partialAlong j G * H + G * partialAlong j H := by
  funext x
  exact (hasLineDerivAt_prod (hG x) (hH x)).lineDeriv
theorem contPartialsUpTo_linComb (a b : ℂ) : ∀ (ν : ℕ) {G H : Coords p → ℂ},
    ContPartialsUpTo ν G → ContPartialsUpTo ν H →
      ContPartialsUpTo ν (a • G + b • H)
  | 0, _, _, hG, hH =>
    Continuous.add (Continuous.const_smul (continuous_of_contPartialsUpTo hG) a)
      (Continuous.const_smul (continuous_of_contPartialsUpTo hH) b)
  | ν + 1, G, H, hG, hH => by
    refine ⟨Continuous.add (Continuous.const_smul hG.1 a) (Continuous.const_smul hH.1 b),
      fun j => ⟨fun x => (hasLineDerivAt_linComb a b ((hG.2 j).1 x)
        ((hH.2 j).1 x)).lineDifferentiableAt, ?_⟩⟩
    rw [partialAlong_linComb j a b (hG.2 j).1 (hH.2 j).1]
    exact contPartialsUpTo_linComb a b ν (hG.2 j).2 (hH.2 j).2
theorem contPartialsUpTo_add {ν : ℕ} {G H : Coords p → ℂ} (hG : ContPartialsUpTo ν G)
    (hH : ContPartialsUpTo ν H) : ContPartialsUpTo ν (G + H) := by
  simpa using contPartialsUpTo_linComb 1 1 ν hG hH
theorem contPartialsUpTo_mul : ∀ (ν : ℕ) {G H : Coords p → ℂ},
    ContPartialsUpTo ν G → ContPartialsUpTo ν H →
      ContPartialsUpTo ν (G * H)
  | 0, _, _, hG, hH =>
    Continuous.mul (continuous_of_contPartialsUpTo hG) (continuous_of_contPartialsUpTo hH)
  | ν + 1, G, H, hG, hH => by
    refine ⟨Continuous.mul hG.1 hH.1, fun j => ⟨fun x => (hasLineDerivAt_prod ((hG.2 j).1 x)
      ((hH.2 j).1 x)).lineDifferentiableAt, ?_⟩⟩
    rw [partialAlong_mul j (hG.2 j).1 (hH.2 j).1]
    exact contPartialsUpTo_add (contPartialsUpTo_mul ν (hG.2 j).2 (contPartialsUpTo_of_succ hH))
      (contPartialsUpTo_mul ν (contPartialsUpTo_of_succ hG) (hH.2 j).2)
theorem lineDifferentiableAt_of_smooth {G : Coords p → ℂ} (h : HasSmoothPartials G)
    (j : Fin (4 * (p : ℕ))) (x : Coords p) : LineDifferentiableAt ℝ G x (Pi.single j 1) :=
  ((h 1).2 j).1 x
theorem smooth_partialAlong {G : Coords p → ℂ} (h : HasSmoothPartials G)
    (j : Fin (4 * (p : ℕ))) : HasSmoothPartials (partialAlong j G) :=
  fun ν => ((h (ν + 1)).2 j).2
theorem smooth_linComb {G H : Coords p → ℂ} (hG : HasSmoothPartials G)
    (hH : HasSmoothPartials H) (a b : ℂ) : HasSmoothPartials (a • G + b • H) :=
  fun ν => contPartialsUpTo_linComb a b ν (hG ν) (hH ν)
theorem smooth_mul {G H : Coords p → ℂ} (hG : HasSmoothPartials G)
    (hH : HasSmoothPartials H) : HasSmoothPartials (G * H) :=
  fun ν => contPartialsUpTo_mul ν (hG ν) (hH ν)
theorem smooth_iterate_partialAlong (j : Fin (4 * (p : ℕ))) : ∀ (n : ℕ) {G : Coords p → ℂ},
    HasSmoothPartials G → HasSmoothPartials ((partialAlong j)^[n] G)
  | 0, _, h => h
  | n + 1, _, h => smooth_iterate_partialAlong j n (smooth_partialAlong h j)
theorem iterate_partialAlong_linComb (j : Fin (4 * (p : ℕ))) (a b : ℂ) :
    ∀ (n : ℕ) {G H : Coords p → ℂ},
    HasSmoothPartials G → HasSmoothPartials H →
      (partialAlong j)^[n] (a • G + b • H) =
        a • (partialAlong j)^[n] G + b • (partialAlong j)^[n] H
  | 0, _, _, _, _ => rfl
  | n + 1, G, H, hG, hH => by
    simp only [Function.iterate_succ_apply]
    rw [partialAlong_linComb j a b (lineDifferentiableAt_of_smooth hG j)
      (lineDifferentiableAt_of_smooth hH j)]
    exact iterate_partialAlong_linComb j a b n (smooth_partialAlong hG j) (smooth_partialAlong hH j)
def partialsOver (l : List (Fin (4 * (p : ℕ)))) (α : CoordIndex p) (G : Coords p → ℂ) :
    Coords p → ℂ :=
  l.foldr (fun j H => (partialAlong j)^[α j] H) G
theorem partialsOver_cons (j : Fin (4 * (p : ℕ))) (l : List (Fin (4 * (p : ℕ))))
    (α : CoordIndex p) (G : Coords p → ℂ) :
    partialsOver (j :: l) α G = (partialAlong j)^[α j] (partialsOver l α G) := rfl
theorem smooth_partialsOver (α : CoordIndex p) {G : Coords p → ℂ}
    (h : HasSmoothPartials G) :
    ∀ l : List (Fin (4 * (p : ℕ))), HasSmoothPartials (partialsOver l α G)
  | [] => h
  | j :: l => smooth_iterate_partialAlong j (α j) (smooth_partialsOver α h l)
theorem partialsOver_linComb (α : CoordIndex p) (a b : ℂ) {G H : Coords p → ℂ}
    (hG : HasSmoothPartials G) (hH : HasSmoothPartials H) :
    ∀ l : List (Fin (4 * (p : ℕ))),
      partialsOver l α (a • G + b • H) = a • partialsOver l α G + b • partialsOver l α H
  | [] => rfl
  | j :: l => by
    rw [partialsOver_cons, partialsOver_linComb α a b hG hH l]
    exact iterate_partialAlong_linComb j a b (α j) (smooth_partialsOver α hG l)
      (smooth_partialsOver α hH l)
theorem partialsOver_congr {α β : CoordIndex p} (G : Coords p → ℂ) :
    ∀ l : List (Fin (4 * (p : ℕ))), (∀ i ∈ l, α i = β i) →
      partialsOver l α G = partialsOver l β G
  | [], _ => rfl
  | j :: l, h => by
    rw [partialsOver_cons, partialsOver_cons, h j (List.mem_cons_self ..),
      partialsOver_congr G l fun i hi => h i (List.mem_cons_of_mem _ hi)]
theorem partialsOver_single_of_notMem (j : Fin (4 * (p : ℕ))) (G : Coords p → ℂ) :
    ∀ l : List (Fin (4 * (p : ℕ))), j ∉ l →
      partialsOver l (Pi.single j 1 : CoordIndex p) G = G
  | [], _ => rfl
  | i :: l, h => by
    have hij : i ≠ j := fun e => h (e ▸ List.mem_cons_self ..)
    have hl : j ∉ l := fun e => h (List.mem_cons_of_mem _ e)
    rw [partialsOver_cons, partialsOver_single_of_notMem j G l hl, Pi.single_eq_of_ne hij]
    rfl
theorem partialsOver_single (j : Fin (4 * (p : ℕ))) (G : Coords p → ℂ) :
    ∀ l : List (Fin (4 * (p : ℕ))), l.Nodup → j ∈ l →
      partialsOver l (Pi.single j 1 : CoordIndex p) G = partialAlong j G
  | [], _, h => absurd h (List.not_mem_nil)
  | i :: l, hn, h => by
    rw [List.nodup_cons] at hn
    by_cases hij : i = j
    · subst hij
      rw [partialsOver_cons, partialsOver_single_of_notMem i G l hn.1, Pi.single_eq_same]
      rfl
    · have hl : j ∈ l := (List.mem_cons.mp h).resolve_left (Ne.symm hij)
      rw [partialsOver_cons, partialsOver_single j G l hn.2 hl, Pi.single_eq_of_ne hij]
      rfl
def wordDeriv (w : List (Fin (4 * (p : ℕ)))) (G : Coords p → ℂ) : Coords p → ℂ :=
  w.foldl (fun F j => partialAlong j F) G
theorem wordDeriv_cons (j : Fin (4 * (p : ℕ))) (w : List (Fin (4 * (p : ℕ))))
    (G : Coords p → ℂ) : wordDeriv (j :: w) G = wordDeriv w (partialAlong j G) := rfl
theorem wordDeriv_append (u v : List (Fin (4 * (p : ℕ)))) (G : Coords p → ℂ) :
    wordDeriv (u ++ v) G = wordDeriv v (wordDeriv u G) := by
  simp [wordDeriv, List.foldl_append]
theorem wordDeriv_replicate (j : Fin (4 * (p : ℕ))) : ∀ (n : ℕ) (G : Coords p → ℂ),
    wordDeriv (List.replicate n j) G = (partialAlong j)^[n] G
  | 0, _ => rfl
  | n + 1, G => by
    rw [List.replicate_succ, wordDeriv_cons, wordDeriv_replicate j n]
    rfl
theorem wordDeriv_add : ∀ (w : List (Fin (4 * (p : ℕ)))) {F K : Coords p → ℂ},
    HasSmoothPartials F → HasSmoothPartials K →
      wordDeriv w (F + K) = wordDeriv w F + wordDeriv w K
  | [], _, _, _, _ => rfl
  | j :: w, F, K, hF, hK => by
    have hsum : partialAlong j (F + K) = partialAlong j F + partialAlong j K := by
      simpa using partialAlong_linComb j 1 1 (lineDifferentiableAt_of_smooth hF j)
        (lineDifferentiableAt_of_smooth hK j)
    rw [wordDeriv_cons, hsum]
    exact wordDeriv_add w (smooth_partialAlong hF j) (smooth_partialAlong hK j)
theorem norm_wordDeriv_mul_le {a b : ℝ} (x : Coords p) :
    ∀ (w : List (Fin (4 * (p : ℕ)))) {G H : Coords p → ℂ},
      HasSmoothPartials G → HasSmoothPartials H →
      (∀ s, s.Sublist w → ‖wordDeriv s G x‖ ≤ a) →
      (∀ s, s.Sublist w → ‖wordDeriv s H x‖ ≤ b) →
      ‖wordDeriv w (G * H) x‖ ≤ 2 ^ w.length * a * b
  | [], G, H, _, _, hGa, hHb => by
    have h1 : ‖G x‖ ≤ a := hGa [] List.Sublist.slnil
    have h2 : ‖H x‖ ≤ b := hHb [] List.Sublist.slnil
    have h3 : ‖(G * H) x‖ ≤ a * b := by
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    simpa [wordDeriv] using h3
  | j :: w, G, H, hG, hH, hGa, hHb => by
    have hdG := smooth_partialAlong hG j
    have hdH := smooth_partialAlong hH j
    have e : wordDeriv (j :: w) (G * H) =
        wordDeriv w (partialAlong j G * H) + wordDeriv w (G * partialAlong j H) := by
      rw [wordDeriv_cons, partialAlong_mul j (lineDifferentiableAt_of_smooth hG j)
        (lineDifferentiableAt_of_smooth hH j)]
      exact wordDeriv_add w (smooth_mul hdG hH) (smooth_mul hG hdH)
    have h1 : ‖wordDeriv w (partialAlong j G * H) x‖ ≤ 2 ^ w.length * a * b :=
      norm_wordDeriv_mul_le x w hdG hH
        (fun s hs => hGa (j :: s) (hs.cons_cons j))
        (fun s hs => hHb s (hs.cons j))
    have h2 : ‖wordDeriv w (G * partialAlong j H) x‖ ≤ 2 ^ w.length * a * b :=
      norm_wordDeriv_mul_le x w hG hdH
        (fun s hs => hGa s (hs.cons j))
        (fun s hs => hHb (j :: s) (hs.cons_cons j))
    rw [e, Pi.add_apply, List.length_cons, pow_succ]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 2 ^ w.length * a * b + 2 ^ w.length * a * b := add_le_add h1 h2
      _ = _ := by ring
def indexWord (α : CoordIndex p) : List (Fin (4 * (p : ℕ))) → List (Fin (4 * (p : ℕ)))
  | [] => []
  | j :: l => indexWord α l ++ List.replicate (α j) j
theorem length_indexWord (α : CoordIndex p) :
    ∀ l : List (Fin (4 * (p : ℕ))), (indexWord α l).length = (l.map α).sum
  | [] => rfl
  | j :: l => by
    simp [indexWord, length_indexWord α l, add_comm]
theorem wordDeriv_indexWord (α : CoordIndex p) (G : Coords p → ℂ) :
    ∀ l : List (Fin (4 * (p : ℕ))), wordDeriv (indexWord α l) G = partialsOver l α G
  | [] => rfl
  | j :: l => by
    rw [indexWord, wordDeriv_append, wordDeriv_replicate, wordDeriv_indexWord α G l,
      partialsOver_cons]
theorem exists_index_of_sublist_indexWord (α : CoordIndex p) :
    ∀ l : List (Fin (4 * (p : ℕ))), l.Nodup → ∀ s, s.Sublist (indexWord α l) →
      ∃ γ : CoordIndex p, (∀ i, γ i ≤ α i) ∧ ∀ F, wordDeriv s F = partialsOver l γ F
  | [], _, s, hs => by
    have : s = [] := List.sublist_nil.mp hs
    subst this
    exact ⟨0, fun i => Nat.zero_le _, fun F => rfl⟩
  | j :: l, hn, s, hs => by
    rw [List.nodup_cons] at hn
    obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hs
    obtain ⟨k, hk, rfl⟩ := List.sublist_replicate_iff.mp h₂
    obtain ⟨γ, hγ, hF⟩ := exists_index_of_sublist_indexWord α l hn.2 s₁ h₁
    refine ⟨Function.update γ j k, fun i => ?_, fun F => ?_⟩
    · by_cases hij : i = j
      · subst hij
        simpa using hk
      · simpa [Function.update_of_ne hij] using hγ i
    · have hc : partialsOver l (Function.update γ j k) F = partialsOver l γ F :=
        partialsOver_congr F l fun i hi =>
          Function.update_of_ne (by rintro rfl; exact hn.1 hi : i ≠ j) _ _
      rw [wordDeriv_append, wordDeriv_replicate, hF, partialsOver_cons, hc, Function.update_self]
theorem degree_le_of_le {γ α : CoordIndex p} (h : ∀ i, γ i ≤ α i) :
    γ.degree ≤ α.degree :=
  Finset.sum_le_sum fun i _ => h i
theorem length_indexWord_finRange (α : CoordIndex p) :
    (indexWord α (List.finRange (4 * (p : ℕ)))).length = α.degree := by
  rw [length_indexWord, CoordIndex.degree, Fin.sum_univ_def]
theorem leibnizRules_holds : LeibnizRules := by
  intro p G H hG hH
  refine ⟨smooth_linComb hG hH, smooth_mul hG hH, smooth_partialAlong hG,
    fun α => smooth_partialsOver α hG _,
    fun a b α => partialsOver_linComb α a b hG hH _,
    fun j => partialsOver_single j G _ (List.nodup_finRange _) (List.mem_finRange j),
    fun j => partialAlong_mul j (lineDifferentiableAt_of_smooth hG j)
      (lineDifferentiableAt_of_smooth hH j), ?_⟩
  intro ν a b x hGa hHb α hα
  have hw : ∀ {F : Coords p → ℂ} {c : ℝ},
      (∀ γ : CoordIndex p, γ.degree ≤ ν → ‖iterPartial γ F x‖ ≤ c) →
      ∀ s, s.Sublist (indexWord α (List.finRange (4 * (p : ℕ)))) → ‖wordDeriv s F x‖ ≤ c := by
    intro F c hF s hs
    obtain ⟨γ, hγ, hs'⟩ := exists_index_of_sublist_indexWord α _ (List.nodup_finRange _) s hs
    rw [hs']
    exact hF γ ((degree_le_of_le hγ).trans hα)
  have hb := norm_wordDeriv_mul_le x _ hG hH (hw hGa) (hw hHb)
  rw [wordDeriv_indexWord, length_indexWord_finRange] at hb
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hGa 0 (by simp [CoordIndex.degree]))
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hHb 0 (by simp [CoordIndex.degree]))
  have hp : (2 : ℝ) ^ α.degree ≤ 2 ^ ν := pow_le_pow_right₀ (by norm_num) hα
  calc ‖iterPartial α (G * H) x‖ ≤ 2 ^ α.degree * a * b := hb
    _ ≤ 2 ^ ν * a * b := by gcongr
end YangMills.Construction.PeriodicSpace.SumsProductsPartials
