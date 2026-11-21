import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.SumsOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open TorusFields TorusLumps BlockAverages
variable {n : ℕ}
private theorem contDiffAt_perturb_of_contDiffThreeAt {G : TorusField n → ℝ} {W : TorusField n}
    (hG : ContDiffThreeAt G W) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0 :=
  (hG k c X).of_le (by exact_mod_cast hk)
private theorem mixedDeriv_add {G G' : TorusField n → ℝ} {W : TorusField n}
    (hG : ContDiffThreeAt G W) (hG' : ContDiffThreeAt G' W) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    mixedDeriv (fun W => G W + G' W) W c X = mixedDeriv G W c X + mixedDeriv G' W c X := by
  unfold mixedDeriv
  have hsum := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (x := (0 : Fin k → ℝ))
    (contDiffAt_perturb_of_contDiffThreeAt hG c X hk)
    (contDiffAt_perturb_of_contDiffThreeAt hG' c X hk)
  have hfun : (fun σ : Fin k → ℝ => G (perturb c X σ W) + G' (perturb c X σ W)) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) + (fun σ : Fin k → ℝ => G' (perturb c X σ W)) := rfl
  rw [hfun, hsum]
  rfl
private theorem mixedDeriv_const_mul {G : TorusField n → ℝ} {W : TorusField n} (a : ℝ)
    (hG : ContDiffThreeAt G W) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    mixedDeriv (fun W => a * G W) W c X = a * mixedDeriv G W c X := by
  unfold mixedDeriv
  have hsmul := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (x := (0 : Fin k → ℝ)) (a := a)
    (contDiffAt_perturb_of_contDiffThreeAt hG c X hk)
  have hfun : (fun σ : Fin k → ℝ => a * G (perturb c X σ W)) =
      a • (fun σ : Fin k → ℝ => G (perturb c X σ W)) := rfl
  rw [hfun, hsmul]
  rfl
private theorem contDiffThreeAt_add {G G' : TorusField n → ℝ} {W : TorusField n}
    (hG : ContDiffThreeAt G W) (hG' : ContDiffThreeAt G' W) :
    ContDiffThreeAt (fun W => G W + G' W) W := fun k c X => (hG k c X).add (hG' k c X)
private theorem contDiffThreeAt_const_mul {G : TorusField n → ℝ} {W : TorusField n} (a : ℝ)
    (hG : ContDiffThreeAt G W) :
    ContDiffThreeAt (fun W => a * G W) W := fun k c X => contDiffAt_const.mul (hG k c X)
private theorem contDiffThreeAt_centeredFamily {h : LocalDensity} {y : TorusSite n} {W : TorusField n}
    (hG : ContDiffThreeAt (h n y) W) :
    ContDiffThreeAt (centeredFamily h n y) W := fun k c X => (hG k c X).sub contDiffAt_const
private theorem stepWeight_pos (p : StepParameters) (m : ℕ) : 0 < p.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem centeredFamily_add (h h' : LocalDensity) :
    centeredFamily (h + h') = fun n y W => centeredFamily h n y W + centeredFamily h' n y W := by
  funext n y W
  simp only [centeredFamily, centered, Pi.add_apply]
  ring
private theorem centeredFamily_smul (a : ℝ) (h : LocalDensity) :
    centeredFamily (a • h) = fun n y W => a * centeredFamily h n y W := by
  funext n y W
  simp only [centeredFamily, centered, Pi.smul_apply, smul_eq_mul]
  ring
theorem normBoundedFamilyClosure : normBoundedFamilyClosureStatement := by
  intro p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε ε₃ ε' ε₃' h hε hε₃ H
    refine ⟨H.admissible, ?_, ?_⟩
    · intro n _ hn y W hW k c X h1 h3 hX
      refine (H.decay n hn y W hW k c X h1 h3 hX).trans ?_
      refine div_le_div_of_nonneg_right ?_ (stepWeight_pos p _).le
      split_ifs <;> assumption
    · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      refine (H.comparison n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX).trans ?_
      exact div_le_div_of_nonneg_right hε (stepWeight_pos p _).le
  · intro ε ε₃ ε' ε₃' h h' H H'
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro n _ hn y W hW
      exact contDiffThreeAt_add (H.admissible.smooth n hn y W hW) (H'.admissible.smooth n hn y W hW)
    · intro n _ hn y g W hW
      simp only [Pi.add_apply]
      rw [H.admissible.gauge n hn y g W hW, H'.admissible.gauge n hn y g W hW]
    · intro n _ hn y u W hW
      simp only [Pi.add_apply]
      rw [H.admissible.translation n hn y u W hW, H'.admissible.translation n hn y u W hW]
    · intro n _ hn y W hW k c X h1 h3 hX
      have e := mixedDeriv_add (H.admissible.smooth n hn y W hW) (H'.admissible.smooth n hn y W hW) c X h3
      have e' : mixedDeriv ((h + h') n y) W c X = mixedDeriv (h n y) W c X + mixedDeriv (h' n y) W c X := e
      rw [e']
      have a1 := H.decay n hn y W hW k c X h1 h3 hX
      have a2 := H'.decay n hn y W hW k c X h1 h3 hX
      refine (abs_add_le _ _).trans ((add_le_add a1 a2).trans (le_of_eq ?_))
      beta_reduce
      split_ifs <;> ring
    · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      rw [centeredFamily_add]
      have k3 : k ≤ 3 := by omega
      have e := mixedDeriv_add (contDiffThreeAt_centeredFamily (H.admissible.smooth n hn y W hW))
        (contDiffThreeAt_centeredFamily (H'.admissible.smooth n hn y W hW))
        (fun l => bondFrom y (b l)) X k3
      have e' := mixedDeriv_add (contDiffThreeAt_centeredFamily (H.admissible.smooth n' hn' y' W' hW'))
        (contDiffThreeAt_centeredFamily (H'.admissible.smooth n' hn' y' W' hW'))
        (fun l => bondFrom y' (b l)) X k3
      rw [e, e']
      have a1 := H.comparison n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      have a2 := H'.comparison n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      have htri := abs_add_le (mixedDeriv (centeredFamily h n y) W (fun l => bondFrom y (b l)) X -
          mixedDeriv (centeredFamily h n' y') W' (fun l => bondFrom y' (b l)) X)
        (mixedDeriv (centeredFamily h' n y) W (fun l => bondFrom y (b l)) X -
          mixedDeriv (centeredFamily h' n' y') W' (fun l => bondFrom y' (b l)) X)
      calc _ = |(mixedDeriv (centeredFamily h n y) W (fun l => bondFrom y (b l)) X -
            mixedDeriv (centeredFamily h n' y') W' (fun l => bondFrom y' (b l)) X) +
            (mixedDeriv (centeredFamily h' n y) W (fun l => bondFrom y (b l)) X -
            mixedDeriv (centeredFamily h' n' y') W' (fun l => bondFrom y' (b l)) X)| := by
            congr 1; ring
        _ ≤ _ := htri
        _ ≤ ε / p.weight m + ε' / p.weight m := add_le_add a1 a2
        _ = (ε + ε') / p.weight m := by ring
  · intro a ε ε₃ h H
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro n _ hn y W hW
      exact contDiffThreeAt_const_mul a (H.admissible.smooth n hn y W hW)
    · intro n _ hn y g W hW
      simp only [Pi.smul_apply]
      rw [H.admissible.gauge n hn y g W hW]
    · intro n _ hn y u W hW
      simp only [Pi.smul_apply]
      rw [H.admissible.translation n hn y u W hW]
    · intro n _ hn y W hW k c X h1 h3 hX
      have e := mixedDeriv_const_mul a (H.admissible.smooth n hn y W hW) c X h3
      have e' : mixedDeriv ((a • h) n y) W c X = a * mixedDeriv (h n y) W c X := e
      rw [e', abs_mul]
      have a1 := H.decay n hn y W hW k c X h1 h3 hX
      refine (mul_le_mul_of_nonneg_left a1 (abs_nonneg a)).trans (le_of_eq ?_)
      beta_reduce
      split_ifs <;> ring
    · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      rw [centeredFamily_smul]
      have k3 : k ≤ 3 := by omega
      have e := mixedDeriv_const_mul a (contDiffThreeAt_centeredFamily (H.admissible.smooth n hn y W hW))
        (fun l => bondFrom y (b l)) X k3
      have e' := mixedDeriv_const_mul a (contDiffThreeAt_centeredFamily (H.admissible.smooth n' hn' y' W' hW'))
        (fun l => bondFrom y' (b l)) X k3
      rw [e, e', ← mul_sub, abs_mul]
      have a1 := H.comparison n n' hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      refine (mul_le_mul_of_nonneg_left a1 (abs_nonneg a)).trans (le_of_eq ?_)
      ring
  · intro ε ε₃ h0 h3
    have hzero : ∀ (m : ℕ) (n : ℕ) (G : TorusField n → ℝ) (W : TorusField n)
        (c : Fin m → TorusBond n) (X : Fin m → imaginaryQuaternions),
        (∀ W, G W = 0) → mixedDeriv G W c X = 0 := by
      intro m n G W c X hG
      unfold mixedDeriv
      have hfun : (fun σ : Fin m → ℝ => G (perturb c X σ W)) = fun _ => 0 := by funext σ; exact hG _
      rw [hfun]
      have h0' : iteratedFDeriv ℝ m (fun _ : Fin m → ℝ => (0 : ℝ)) = 0 := by
        funext x
        exact congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := Fin m → ℝ) (F := ℝ) (n := m)) x
      rw [h0']
      simp
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro n _ hn y W hW k c X
      exact contDiffAt_const
    · intro n _ hn y g W hW
      rfl
    · intro n _ hn y u W hW
      rfl
    · intro n _ hn y W hW k c X h1 h3 hX
      rw [hzero k n ((0 : LocalDensity) n y) W c X (fun _ => rfl), abs_zero]
      refine div_nonneg ?_ (stepWeight_pos p _).le
      split_ifs <;> assumption
    · intro n n' _ _ hn hn' y y' W W' m hm hm' hW hW' hA k b X hk hb hX
      have e1 : ∀ (n : ℕ) (y : TorusSite n) (W : TorusField n),
          centeredFamily (0 : LocalDensity) n y W = 0 := by
        intro n y W
        simp [centeredFamily, centered]
      rw [hzero k n _ W _ X (e1 n y), hzero k n' _ W' _ X (e1 n' y')]
      simp only [sub_zero, abs_zero]
      exact div_nonneg h0 (stepWeight_pos p _).le
end YangMills.Construction.FamilyNorms
end
