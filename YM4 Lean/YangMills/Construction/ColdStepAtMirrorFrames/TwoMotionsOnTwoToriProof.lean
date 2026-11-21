import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.MotionsOfTwoNearCurvesProof
import YangMills.Construction.ColdStepAtMirrorFrames.TwoMotionsOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages Estimates
namespace ColdStepAtMirrorFrames
namespace MotionComparison
section finiteSums
variable {β β' κ : Type} [Fintype β] [Fintype β'] [DecidableEq β] [DecidableEq β'] [DecidableEq κ]
theorem abs_sum_sub_sum_le_of_matched (I : Finset κ) (ι : κ → β) (ι' : κ → β') (hι : Set.InjOn ι I)
    (hι' : Set.InjOn ι' I)
    (m : β → ℝ) (m' : β' → ℝ) (w : β → ℝ) (w' : β' → ℝ) (d : κ → ℝ) (ε₁ ε₂ E K μ : ℝ)
    (hw : ∀ b, 0 ≤ w b) (hw' : ∀ b, 0 ≤ w' b) (hd : ∀ p, 0 ≤ d p) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hE : 0 ≤ E)
    (hfar : ∀ b, b ∉ I.image ι → |m b| ≤ ε₂ * w b) (hfar' : ∀ b, b ∉ I.image ι' → |m' b| ≤ ε₂ * w' b)
    (hnear : ∀ p ∈ I, |m (ι p) - m' (ι' p)| ≤ ε₁ * w (ι p) + E * d p)
    (hK : ∑ b, w b ≤ K) (hK' : ∑ b, w' b ≤ K) (hμ : ∑ p ∈ I, d p ≤ μ) :
    |∑ b, m b - ∑ b, m' b| ≤ ε₁ * K + 2 * ε₂ * K + E * μ := by
  have s1 : ∑ b, m b = ∑ p ∈ I, m (ι p) + ∑ b ∈ (I.image ι)ᶜ, m b := by
    rw [← Finset.sum_image hι, Finset.sum_add_sum_compl]
  have s2 : ∑ b, m' b = ∑ p ∈ I, m' (ι' p) + ∑ b ∈ (I.image ι')ᶜ, m' b := by
    rw [← Finset.sum_image hι', Finset.sum_add_sum_compl]
  have t1 : |∑ b ∈ (I.image ι)ᶜ, m b| ≤ ε₂ * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b ∈ (I.image ι)ᶜ, |m b| ≤ ∑ b ∈ (I.image ι)ᶜ, ε₂ * w b :=
          Finset.sum_le_sum fun b hb => hfar b (Finset.mem_compl.1 hb)
      _ = ε₂ * ∑ b ∈ (I.image ι)ᶜ, w b := (Finset.mul_sum _ _ _).symm
      _ ≤ ε₂ * K := mul_le_mul_of_nonneg_left
          ((Finset.sum_le_univ_sum_of_nonneg hw).trans hK) hε₂
  have t2 : |∑ b ∈ (I.image ι')ᶜ, m' b| ≤ ε₂ * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b ∈ (I.image ι')ᶜ, |m' b| ≤ ∑ b ∈ (I.image ι')ᶜ, ε₂ * w' b :=
          Finset.sum_le_sum fun b hb => hfar' b (Finset.mem_compl.1 hb)
      _ = ε₂ * ∑ b ∈ (I.image ι')ᶜ, w' b := (Finset.mul_sum _ _ _).symm
      _ ≤ ε₂ * K := mul_le_mul_of_nonneg_left
          ((Finset.sum_le_univ_sum_of_nonneg hw').trans hK') hε₂
  have t3 : |∑ p ∈ I, m (ι p) - ∑ p ∈ I, m' (ι' p)| ≤ ε₁ * K + E * μ := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ I, |m (ι p) - m' (ι' p)| ≤ ∑ p ∈ I, (ε₁ * w (ι p) + E * d p) := Finset.sum_le_sum hnear
      _ = ε₁ * ∑ p ∈ I, w (ι p) + E * ∑ p ∈ I, d p := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ε₁ * K + E * μ := by
          have h1 : ∑ p ∈ I, w (ι p) ≤ K := by
            rw [← Finset.sum_image hι]
            exact (Finset.sum_le_univ_sum_of_nonneg hw).trans hK
          exact add_le_add (mul_le_mul_of_nonneg_left h1 hε₁) (mul_le_mul_of_nonneg_left hμ hE)
  rw [s1, s2]
  have e : ∑ p ∈ I, m (ι p) + ∑ b ∈ (I.image ι)ᶜ, m b - (∑ p ∈ I, m' (ι' p) + ∑ b ∈ (I.image ι')ᶜ, m' b) =
      (∑ p ∈ I, m (ι p) - ∑ p ∈ I, m' (ι' p)) + ∑ b ∈ (I.image ι)ᶜ, m b - ∑ b ∈ (I.image ι')ᶜ, m' b := by ring
  rw [e]
  have n1 := abs_sub ((∑ p ∈ I, m (ι p) - ∑ p ∈ I, m' (ι' p)) + ∑ b ∈ (I.image ι)ᶜ, m b) (∑ b ∈ (I.image ι')ᶜ, m' b)
  have n2 := abs_add_le (∑ p ∈ I, m (ι p) - ∑ p ∈ I, m' (ι' p)) (∑ b ∈ (I.image ι)ᶜ, m b)
  linarith
theorem abs_double_sum_sub_le_of_matched (I : Finset κ) (ι : κ → β) (ι' : κ → β') (hι : Set.InjOn ι I)
    (hι' : Set.InjOn ι' I)
    (m : β → β → ℝ) (m' : β' → β' → ℝ) (w₀ w₁ : β → ℝ) (w₀' w₁' : β' → ℝ) (d₀ d₁ : κ → ℝ) (ε₁ ε₂ E K μ : ℝ)
    (hw₀ : ∀ b, 0 ≤ w₀ b) (hw₁ : ∀ b, 0 ≤ w₁ b) (hw₀' : ∀ b, 0 ≤ w₀' b) (hw₁' : ∀ b, 0 ≤ w₁' b)
    (hd₀ : ∀ p, 0 ≤ d₀ p) (hd₁ : ∀ p, 0 ≤ d₁ p) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hE : 0 ≤ E) (hK0 : 0 ≤ K)
    (hfar : ∀ b b', (b ∉ I.image ι ∨ b' ∉ I.image ι) → |m b b'| ≤ ε₂ * (w₀ b * w₁ b'))
    (hfar' : ∀ b b', (b ∉ I.image ι' ∨ b' ∉ I.image ι') → |m' b b'| ≤ ε₂ * (w₀' b * w₁' b'))
    (hnear : ∀ p ∈ I, ∀ q ∈ I, |m (ι p) (ι q) - m' (ι' p) (ι' q)| ≤
      ε₁ * (w₀ (ι p) * w₁ (ι q)) + E * (d₀ p * w₁ (ι q)) + E * (w₀' (ι' p) * d₁ q))
    (hK₀ : ∑ b, w₀ b ≤ K) (hK₁ : ∑ b, w₁ b ≤ K) (hK₀' : ∑ b, w₀' b ≤ K) (hK₁' : ∑ b, w₁' b ≤ K)
    (hμ₀ : ∑ p ∈ I, d₀ p ≤ μ) (hμ₁ : ∑ p ∈ I, d₁ p ≤ μ) :
    |∑ b, ∑ b', m b b' - ∑ b, ∑ b', m' b b'| ≤ ε₁ * K ^ 2 + 2 * ε₂ * K ^ 2 + 2 * E * K * μ := by
  classical
  have key : ∀ {γ : Type} [Fintype γ] [DecidableEq γ] (ν : κ → γ) (hν : Set.InjOn ν I) (n : γ → γ → ℝ) (u₀ u₁ : γ → ℝ)
      (_ : ∀ b, 0 ≤ u₀ b) (_ : ∀ b, 0 ≤ u₁ b) (_ : ∑ b, u₀ b ≤ K) (_ : ∑ b, u₁ b ≤ K)
      (_ : ∀ b b', (b ∉ I.image ν ∨ b' ∉ I.image ν) → |n b b'| ≤ ε₂ * (u₀ b * u₁ b')),
      |∑ b, ∑ b', n b b' - ∑ p ∈ I, ∑ q ∈ I, n (ν p) (ν q)| ≤ ε₂ * K ^ 2 := by
    intro γ _ _ ν hν n u₀ u₁ hu₀ hu₁ hK₀ hK₁ hf
    set R := I.image ν with hR
    have s1 : ∑ p ∈ I, ∑ q ∈ I, n (ν p) (ν q) = ∑ P ∈ R ×ˢ R, n P.1 P.2 := by
      rw [Finset.sum_product, hR, Finset.sum_image hν]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_image hν]
    have s2 : ∑ b, ∑ b', n b b' = ∑ P : γ × γ, n P.1 P.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [s1, s2, ← Finset.sum_add_sum_compl (R ×ˢ R), add_sub_cancel_left]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∑ P ∈ (R ×ˢ R)ᶜ, |n P.1 P.2| ≤ ∑ P ∈ (R ×ˢ R)ᶜ, ε₂ * (u₀ P.1 * u₁ P.2) := by
      refine Finset.sum_le_sum fun P hP => hf _ _ ?_
      by_contra hcon
      push_neg at hcon
      exact (Finset.mem_compl.1 hP) (Finset.mem_product.2 hcon)
    refine h1.trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hε₂
    calc ∑ P ∈ (R ×ˢ R)ᶜ, u₀ P.1 * u₁ P.2 ≤ ∑ P : γ × γ, u₀ P.1 * u₁ P.2 :=
          Finset.sum_le_univ_sum_of_nonneg fun P => mul_nonneg (hu₀ _) (hu₁ _)
      _ = (∑ b, u₀ b) * ∑ b, u₁ b := by
          rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ K * K := mul_le_mul hK₀ hK₁ (Finset.sum_nonneg fun b _ => hu₁ b) hK0
      _ = K ^ 2 := by ring
  have f1 := key ι hι m w₀ w₁ hw₀ hw₁ hK₀ hK₁ hfar
  have f2 := key ι' hι' m' w₀' w₁' hw₀' hw₁' hK₀' hK₁' hfar'
  have hs₀ : ∑ p ∈ I, w₀ (ι p) ≤ K := by
    rw [← Finset.sum_image hι]
    exact (Finset.sum_le_univ_sum_of_nonneg hw₀).trans hK₀
  have hs₁ : ∑ p ∈ I, w₁ (ι p) ≤ K := by
    rw [← Finset.sum_image hι]
    exact (Finset.sum_le_univ_sum_of_nonneg hw₁).trans hK₁
  have hs₀' : ∑ p ∈ I, w₀' (ι' p) ≤ K := by
    rw [← Finset.sum_image hι']
    exact (Finset.sum_le_univ_sum_of_nonneg hw₀').trans hK₀'
  have hs₁0 : 0 ≤ ∑ p ∈ I, w₁ (ι p) := Finset.sum_nonneg fun p _ => hw₁ _
  have hμ0 : 0 ≤ ∑ p ∈ I, d₀ p := Finset.sum_nonneg fun p _ => hd₀ _
  have hμ10 : 0 ≤ ∑ p ∈ I, d₁ p := Finset.sum_nonneg fun p _ => hd₁ _
  have t3 : |∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q) - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q)| ≤
      ε₁ * K ^ 2 + 2 * E * K * μ := by
    have e : ∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q) - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q) =
        ∑ p ∈ I, ∑ q ∈ I, (m (ι p) (ι q) - m' (ι' p) (ι' q)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_sub_distrib]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∑ p ∈ I, |∑ q ∈ I, (m (ι p) (ι q) - m' (ι' p) (ι' q))| ≤
        ∑ p ∈ I, ∑ q ∈ I, (ε₁ * (w₀ (ι p) * w₁ (ι q)) + E * (d₀ p * w₁ (ι q)) + E * (w₀' (ι' p) * d₁ q)) :=
      Finset.sum_le_sum fun p hp => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => hnear p hp q hq)
    refine h1.trans ?_
    have e2 : ∑ p ∈ I, ∑ q ∈ I, (ε₁ * (w₀ (ι p) * w₁ (ι q)) + E * (d₀ p * w₁ (ι q)) + E * (w₀' (ι' p) * d₁ q)) =
        ε₁ * ((∑ p ∈ I, w₀ (ι p)) * ∑ q ∈ I, w₁ (ι q)) + E * ((∑ p ∈ I, d₀ p) * ∑ q ∈ I, w₁ (ι q)) +
          E * ((∑ p ∈ I, w₀' (ι' p)) * ∑ q ∈ I, d₁ q) := by
      have hh : ∀ (c : ℝ) (f g : κ → ℝ), ∑ p ∈ I, ∑ q ∈ I, c * (f p * g q) = c * ((∑ p ∈ I, f p) * ∑ q ∈ I, g q) := by
        intro c f g
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
      rw [hh ε₁ (fun p => w₀ (ι p)) (fun q => w₁ (ι q)), hh E d₀ (fun q => w₁ (ι q)), hh E (fun p => w₀' (ι' p)) d₁]
    rw [e2]
    have b1 : (∑ p ∈ I, w₀ (ι p)) * ∑ q ∈ I, w₁ (ι q) ≤ K * K := mul_le_mul hs₀ hs₁ hs₁0 hK0
    have b2 : (∑ p ∈ I, d₀ p) * ∑ q ∈ I, w₁ (ι q) ≤ μ * K := mul_le_mul hμ₀ hs₁ hs₁0 (hμ0.trans hμ₀)
    have b3 : (∑ p ∈ I, w₀' (ι' p)) * ∑ q ∈ I, d₁ q ≤ K * μ := mul_le_mul hs₀' hμ₁ hμ10 hK0
    have c1 := mul_le_mul_of_nonneg_left b1 hε₁
    have c2 := mul_le_mul_of_nonneg_left b2 hE
    have c3 := mul_le_mul_of_nonneg_left b3 hE
    nlinarith
  have e : ∑ b, ∑ b', m b b' - ∑ b, ∑ b', m' b b' =
      (∑ b, ∑ b', m b b' - ∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q)) -
        (∑ b, ∑ b', m' b b' - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q)) +
        (∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q) - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q)) := by ring
  rw [e]
  have n1 := abs_add_le ((∑ b, ∑ b', m b b' - ∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q)) -
        (∑ b, ∑ b', m' b b' - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q)))
        (∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q) - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q))
  have n2 := abs_sub (∑ b, ∑ b', m b b' - ∑ p ∈ I, ∑ q ∈ I, m (ι p) (ι q))
    (∑ b, ∑ b', m' b b' - ∑ p ∈ I, ∑ q ∈ I, m' (ι' p) (ι' q))
  linarith
end finiteSums
section linearAlgebra
variable {F : BlockFrame}
theorem abs_le_mul_norm_of_homogeneous (f : imaginaryQuaternions → ℝ)
    (hf : ∀ (r : ℝ) (u : imaginaryQuaternions), f (r • u) = r * f u) (c : ℝ)
    (h : ∀ X : imaginaryQuaternions, ‖X‖ = 1 → |f X| ≤ c) (u : imaginaryQuaternions) : |f u| ≤ c * ‖u‖ := by
  by_cases hu : u = 0
  · have h0 : f 0 = 0 := by
      have := hf 0 0
      simpa using this
    rw [hu, h0]
    simp
  · have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    have hX : ‖(‖u‖⁻¹ • u : imaginaryQuaternions)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have e : f u = ‖u‖ * f (‖u‖⁻¹ • u) := by
      rw [← hf, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [e, abs_mul, abs_of_nonneg (norm_nonneg u), mul_comm]
    exact mul_le_mul_of_nonneg_right (h _ hX) (norm_nonneg u)
theorem abs_le_mul_norm_mul_norm_of_bihomogeneous (f : imaginaryQuaternions → imaginaryQuaternions → ℝ)
    (hf₁ : ∀ (r : ℝ) (u v : imaginaryQuaternions), f (r • u) v = r * f u v)
    (hf₂ : ∀ (r : ℝ) (u v : imaginaryQuaternions), f u (r • v) = r * f u v) (c : ℝ)
    (h : ∀ X Y : imaginaryQuaternions, ‖X‖ = 1 → ‖Y‖ = 1 → |f X Y| ≤ c) (u v : imaginaryQuaternions) :
    |f u v| ≤ c * (‖u‖ * ‖v‖) := by
  have h1 : ∀ Y : imaginaryQuaternions, ‖Y‖ = 1 → |f u Y| ≤ c * ‖u‖ := fun Y hY =>
    abs_le_mul_norm_of_homogeneous (fun x => f x Y) (fun r x => hf₁ r x Y) c (fun X hX => h X Y hX hY) u
  have h2 := abs_le_mul_norm_of_homogeneous (fun y => f u y) (fun r y => hf₂ r u y) (c * ‖u‖) h1 v
  simpa [mul_assoc] using h2
section slots
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem update_single_slot (x z : V) : Function.update ![x] (0 : Fin 1) z = ![z] := by
  funext i
  fin_cases i
  simp
theorem update_first_slot (x y z : V) : Function.update ![x, y] (0 : Fin 2) z = ![z, y] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoCurves.update_pair_zero <;> assumption
theorem update_second_slot (x y z : V) : Function.update ![x, y] (1 : Fin 2) z = ![x, z] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoCurves.update_pair_one <;> assumption
theorem apply_single_smul (N : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => V) ℝ) (r : ℝ) (z : V) :
    N ![r • z] = r * N ![z] := by
  have h := N.map_update_smul ![z] (0 : Fin 1) r z
  rw [update_single_slot, update_single_slot] at h
  simpa using h
theorem apply_pair_smul_left (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) (r : ℝ) (x y : V) :
    M ![r • x, y] = r * M ![x, y] := by
  have h := M.map_update_smul ![x, y] (0 : Fin 2) r x
  rw [update_first_slot, update_first_slot] at h
  simpa using h
theorem apply_pair_smul_right (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) (r : ℝ) (x y : V) :
    M ![x, r • y] = r * M ![x, y] := by
  have h := M.map_update_smul ![x, y] (1 : Fin 2) r y
  rw [update_second_slot, update_second_slot] at h
  simpa using h
theorem apply_single_sub (N : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => V) ℝ) (x y : V) :
    N ![x] - N ![y] = N ![x - y] := by
  have h := N.map_update_sub ![x] (0 : Fin 1) x y
  rw [update_single_slot, update_single_slot, update_single_slot] at h
  exact h.symm
theorem apply_pair_sub (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) (x y x' y' : V) :
    M ![x, y] - M ![x', y'] = M ![x - x', y] + M ![x', y - y'] := by
  have h1 := M.map_update_sub ![x, y] (0 : Fin 2) x x'
  have h2 := M.map_update_sub ![x', y] (1 : Fin 2) y y'
  rw [update_first_slot, update_first_slot, update_first_slot] at h1
  rw [update_second_slot, update_second_slot, update_second_slot] at h2
  rw [h1, h2]
  abel
theorem apply_single_sum (N : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => V) ℝ) {ι : Type} [Fintype ι]
    (P : ι → V) : N ![∑ i, P i] = ∑ i, N ![P i] := by
  have e := N.toMultilinearMap.map_update_sum (m := ![0]) (i := (0 : Fin 1)) Finset.univ P
  simp only [ContinuousMultilinearMap.coe_coe, update_single_slot] at e
  exact e
theorem apply_pair_sum (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : ι → V) (Q : κ → V) : M ![∑ i, P i, ∑ k, Q k] = ∑ i, ∑ k, M ![P i, Q k] := by
  have h1 : ∀ y : V, M ![∑ i, P i, y] = ∑ i, M ![P i, y] := by
    intro y
    have e := M.toMultilinearMap.map_update_sum (m := ![0, y]) (i := (0 : Fin 2)) Finset.univ P
    simp only [ContinuousMultilinearMap.coe_coe, update_first_slot] at e
    exact e
  have h2 : ∀ x : V, M ![x, ∑ k, Q k] = ∑ k, M ![x, Q k] := by
    intro x
    have e := M.toMultilinearMap.map_update_sum (m := ![x, 0]) (i := (1 : Fin 2)) Finset.univ Q
    simp only [ContinuousMultilinearMap.coe_coe, update_second_slot] at e
    exact e
  rw [h1]
  exact Finset.sum_congr rfl fun i _ => h2 _
end slots
theorem eq_sum_singleBondForm {j : ℕ} {T : Finset (F.Site j × Fin 4)} (Z : ↥T → imaginaryQuaternions) :
    Z = ∑ b : ↥T, singleBondForm b (Z b) := by
  classical
  funext b'
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single b']
  · simp [singleBondForm]
  · intro b _ hne
    simp [singleBondForm, hne.symm]
  · simp
theorem singleBondForm_smul_value {j : ℕ} {T : Finset (F.Site j × Fin 4)} (b : ↥T) (r : ℝ)
    (X : imaginaryQuaternions) : singleBondForm b (r • X) = r • singleBondForm b X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.singleBondForm_smul <;> assumption
theorem singleBondForm_sub_value {j : ℕ} {T : Finset (F.Site j × Fin 4)} (b : ↥T)
    (X Y : imaginaryQuaternions) : singleBondForm b X - singleBondForm b Y = singleBondForm b (X - Y) := by
  classical
  simp [singleBondForm, Pi.single_sub]
theorem derivs_along_motion_eq_formComposition (hJ : FormCompositionJet) (hC : ThirdOrderChainRuleVectorValued)
    {j : ℕ} (T : Finset (F.Site j × Fin 4)) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (α : (Fin 2 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) (hT : ∀ b, b ∈ T) (hG : ContDiffThreeAlongBonds G W)
    (h0 : ∀ x b, α 0 x b = 0) (hα : ∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) :
    (∀ l : Fin 2, iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single l 1] =
      iteratedFDeriv ℝ 1 (formComposition T G W) 0 ![fun b : ↥T => motionComponent α ![l] b.1.1 b.1.2]) ∧
    iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single 0 1, Pi.single 1 1] =
      iteratedFDeriv ℝ 2 (formComposition T G W) 0
        ![fun b : ↥T => motionComponent α ![0] b.1.1 b.1.2, fun b : ↥T => motionComponent α ![1] b.1.1 b.1.2] +
      iteratedFDeriv ℝ 1 (formComposition T G W) 0 ![fun b : ↥T => motionComponent α ![0, 1] b.1.1 b.1.2] := by
  classical
  obtain ⟨hJC, -, -⟩ := hJ ℝ F j T G W hG
  set A : (Fin 2 → ℝ) → (↥T → imaginaryQuaternions) := fun τ b => α τ b.1.1 b.1.2 with hA
  have hA0 : A 0 = 0 := by
    funext b
    exact h0 _ _
  have hAC : ContDiffAt ℝ 3 A 0 := contDiffAt_pi.2 fun b => hα _ _
  have hext : ∀ τ, extendByZero (A τ) = α τ := by
    intro τ
    funext y i
    unfold extendByZero
    rw [dif_pos (hT (y, i))]
  have hcomp : (fun τ => G (leftTranslate (α τ) W)) = formComposition T G W ∘ A := by
    funext τ
    simp only [Function.comp, formComposition, hext]
  have hC' := hC (formComposition T G W) A 0 (by rw [hA0]; exact hJC) hAC
  have hproj : ∀ (k : ℕ) (hk : k ≤ 3) (b : ↥T) (m : Fin k → Fin 2 → ℝ),
      iteratedFDeriv ℝ k A 0 m b = iteratedFDeriv ℝ k (fun τ => α τ b.1.1 b.1.2) 0 m := by
    intro k hk b m
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥T => imaginaryQuaternions) b).iteratedFDeriv_comp_left
      hAC (i := k) (by exact_mod_cast hk)
    have e : (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥T => imaginaryQuaternions) b) ∘ A =
        fun τ => α τ b.1.1 b.1.2 := rfl
    rw [e] at h
    rw [h]
    rfl
  have hpart : ∀ l : Fin 2, iteratedFDeriv ℝ 1 A 0 ![Pi.single l 1] =
      fun b : ↥T => motionComponent α ![l] b.1.1 b.1.2 := by
    intro l
    funext b
    rw [hproj 1 (by norm_num)]
    unfold motionComponent
    congr 1
    funext m
    fin_cases m
    rfl
  have hpart2 : iteratedFDeriv ℝ 2 A 0 ![Pi.single 0 1, Pi.single 1 1] =
      fun b : ↥T => motionComponent α ![0, 1] b.1.1 b.1.2 := by
    funext b
    rw [hproj 2 (by norm_num)]
    unfold motionComponent
    congr 1
    funext m
    fin_cases m <;> rfl
  refine ⟨fun l => ?_, ?_⟩
  · rw [hcomp, hC'.2.1, hA0, hpart]
  · rw [hcomp, hC'.2.2.1, hA0, hpart, hpart, hpart2]
end linearAlgebra
end MotionComparison
open MotionComparison in
set_option maxHeartbeats 2000000 in
theorem twoMotionsCompare_proof (hJ : FormCompositionJet) (hC : ThirdOrderChainRuleVectorValued) :
    TwoMotionsCompare := by
  intro F F' j j' κ T T' G G' W W' I ι ι' ε₁ ε₂ E K μ α α' hT hT' hι hι' hG hG' hε₁ hε₂ hE hK hμ hEc h0 h0' hC₁ hC₁'
    hK1 hK1' hK2 hK2' hμ1 hμ2
  classical
  obtain ⟨-, hJe, -⟩ := hJ ℝ F j T G W hG
  obtain ⟨-, hJe', -⟩ := hJ ℝ F' j' T' G' W' hG'
  set N := iteratedFDeriv ℝ 1 (formComposition T G W) 0 with hN
  set M := iteratedFDeriv ℝ 2 (formComposition T G W) 0 with hM
  set N' := iteratedFDeriv ℝ 1 (formComposition T' G' W') 0 with hN'
  set M' := iteratedFDeriv ℝ 2 (formComposition T' G' W') 0 with hM'
  have en : ∀ (b : ↥T) (X : imaginaryQuaternions), N ![singleBondForm b X] = bondDeriv G W ![b.1] ![X] := by
    intro b X
    have h := hJe 1 ![b] ![X] (by norm_num)
    have e1 : (fun l => singleBondForm ((![b] : Fin 1 → ↥T) l) ((![X] : Fin 1 → imaginaryQuaternions) l)) =
        ![singleBondForm b X] := by
      funext l
      fin_cases l
      rfl
    have e2 : (fun l => ((![b] : Fin 1 → ↥T) l).1) = ![b.1] := by
      funext l
      fin_cases l
      rfl
    rwa [e1, e2] at h
  have en' : ∀ (b : ↥T') (X : imaginaryQuaternions), N' ![singleBondForm b X] = bondDeriv G' W' ![b.1] ![X] := by
    intro b X
    have h := hJe' 1 ![b] ![X] (by norm_num)
    have e1 : (fun l => singleBondForm ((![b] : Fin 1 → ↥T') l) ((![X] : Fin 1 → imaginaryQuaternions) l)) =
        ![singleBondForm b X] := by
      funext l
      fin_cases l
      rfl
    have e2 : (fun l => ((![b] : Fin 1 → ↥T') l).1) = ![b.1] := by
      funext l
      fin_cases l
      rfl
    rwa [e1, e2] at h
  have em : ∀ (b b' : ↥T) (X Y : imaginaryQuaternions),
      M ![singleBondForm b X, singleBondForm b' Y] = bondDeriv G W ![b.1, b'.1] ![X, Y] := by
    intro b b' X Y
    have h := hJe 2 ![b, b'] ![X, Y] (by norm_num)
    have e1 : (fun l => singleBondForm ((![b, b'] : Fin 2 → ↥T) l) ((![X, Y] : Fin 2 → imaginaryQuaternions) l)) =
        ![singleBondForm b X, singleBondForm b' Y] := by
      funext l
      fin_cases l <;> rfl
    have e2 : (fun l => ((![b, b'] : Fin 2 → ↥T) l).1) = ![b.1, b'.1] := by
      funext l
      fin_cases l <;> rfl
    rwa [e1, e2] at h
  have em' : ∀ (b b' : ↥T') (X Y : imaginaryQuaternions),
      M' ![singleBondForm b X, singleBondForm b' Y] = bondDeriv G' W' ![b.1, b'.1] ![X, Y] := by
    intro b b' X Y
    have h := hJe' 2 ![b, b'] ![X, Y] (by norm_num)
    have e1 : (fun l => singleBondForm ((![b, b'] : Fin 2 → ↥T') l) ((![X, Y] : Fin 2 → imaginaryQuaternions) l)) =
        ![singleBondForm b X, singleBondForm b' Y] := by
      funext l
      fin_cases l <;> rfl
    have e2 : (fun l => ((![b, b'] : Fin 2 → ↥T') l).1) = ![b.1, b'.1] := by
      funext l
      fin_cases l <;> rfl
    rwa [e1, e2] at h
  set jι : κ → ↥T := fun p => ⟨ι p, hT _⟩ with hjι
  set jι' : κ → ↥T' := fun p => ⟨ι' p, hT' _⟩ with hjι'
  have hinj : Set.InjOn jι I := fun p hp q hq e => hι hp hq (congrArg Subtype.val e)
  have hinj' : Set.InjOn jι' I := fun p hp q hq e => hι' hp hq (congrArg Subtype.val e)
  have hout : ∀ b : ↥T, b ∉ I.image jι → b.1 ∉ ι '' I := by
    rintro b hb ⟨p, hp, e⟩
    exact hb (Finset.mem_image.2 ⟨p, hp, Subtype.ext e⟩)
  have hout' : ∀ b : ↥T', b ∉ I.image jι' → b.1 ∉ ι' '' I := by
    rintro b hb ⟨p, hp, e⟩
    exact hb (Finset.mem_image.2 ⟨p, hp, Subtype.ext e⟩)
  have first : ∀ (A : ↥T → imaginaryQuaternions) (B : ↥T' → imaginaryQuaternions), ∑ b, ‖A b‖ ≤ K →
      ∑ b, ‖B b‖ ≤ K →
      ∑ p ∈ I, ‖A (jι p) - B (jι' p)‖ ≤ μ → |N ![A] - N' ![B]| ≤ ε₁ * K + 2 * ε₂ * K + E * μ := by
    intro A B hA hB hd
    have eA : N ![A] = ∑ b, N ![singleBondForm b (A b)] := by
      conv_lhs => rw [eq_sum_singleBondForm A]
      exact apply_single_sum N _
    have eB : N' ![B] = ∑ b, N' ![singleBondForm b (B b)] := by
      conv_lhs => rw [eq_sum_singleBondForm B]
      exact apply_single_sum N' _
    rw [eA, eB]
    refine abs_sum_sub_sum_le_of_matched I jι jι' hinj hinj' _ _ (fun b => ‖A b‖) (fun b => ‖B b‖)
      (fun p => ‖A (jι p) - B (jι' p)‖)
      ε₁ ε₂ E K μ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hε₁ hε₂ hE ?_ ?_ ?_ hA hB hd
    · intro b hb
      refine abs_le_mul_norm_of_homogeneous (fun u => N ![singleBondForm b u]) (fun r u => ?_) ε₂
        (fun X hX => ?_) (A b)
      · simp only [singleBondForm_smul_value, apply_single_smul]
      · simp only [en]
        exact hEc.unlabelled_first _ _ (hout b hb) hX
    · intro b hb
      refine abs_le_mul_norm_of_homogeneous (fun u => N' ![singleBondForm b u]) (fun r u => ?_) ε₂
        (fun X hX => ?_) (B b)
      · simp only [singleBondForm_smul_value, apply_single_smul]
      · simp only [en']
        exact hEc.unlabelled_first' _ _ (hout' b hb) hX
    · intro p hp
      have h1 : |N ![singleBondForm (jι p) (A (jι p))] - N' ![singleBondForm (jι' p) (A (jι p))]| ≤
          ε₁ * ‖A (jι p)‖ := by
        refine abs_le_mul_norm_of_homogeneous
          (fun u => N ![singleBondForm (jι p) u] - N' ![singleBondForm (jι' p) u]) (fun r u => ?_) ε₁
          (fun X hX => ?_) _
        · simp only [singleBondForm_smul_value, apply_single_smul]
          ring
        · simp only [en, en']
          exact hEc.labelled_first p X hp hX
      have h2 : |N' ![singleBondForm (jι' p) (A (jι p) - B (jι' p))]| ≤ E * ‖A (jι p) - B (jι' p)‖ := by
        refine abs_le_mul_norm_of_homogeneous (fun u => N' ![singleBondForm (jι' p) u]) (fun r u => ?_) E
          (fun X hX => ?_) _
        · simp only [singleBondForm_smul_value, apply_single_smul]
        · simp only [en']
          exact hEc.bound_first' _ _ hX
      have e : N ![singleBondForm (jι p) (A (jι p))] - N' ![singleBondForm (jι' p) (B (jι' p))] =
          (N ![singleBondForm (jι p) (A (jι p))] - N' ![singleBondForm (jι' p) (A (jι p))]) +
            N' ![singleBondForm (jι' p) (A (jι p) - B (jι' p))] := by
        rw [← singleBondForm_sub_value, ← apply_single_sub]
        ring
      show |N ![singleBondForm (jι p) (A (jι p))] - N' ![singleBondForm (jι' p) (B (jι' p))]| ≤ _
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have second : ∀ (A₀ A₁ : ↥T → imaginaryQuaternions) (B₀ B₁ : ↥T' → imaginaryQuaternions), ∑ b, ‖A₀ b‖ ≤ K →
      ∑ b, ‖A₁ b‖ ≤ K → ∑ b, ‖B₀ b‖ ≤ K →
      ∑ b, ‖B₁ b‖ ≤ K → ∑ p ∈ I, ‖A₀ (jι p) - B₀ (jι' p)‖ ≤ μ → ∑ p ∈ I, ‖A₁ (jι p) - B₁ (jι' p)‖ ≤ μ →
      |M ![A₀, A₁] - M' ![B₀, B₁]| ≤ ε₁ * K ^ 2 + 2 * ε₂ * K ^ 2 + 2 * E * K * μ := by
    intro A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hd₀ hd₁
    have eA : M ![A₀, A₁] = ∑ b, ∑ b', M ![singleBondForm b (A₀ b), singleBondForm b' (A₁ b')] := by
      conv_lhs => rw [eq_sum_singleBondForm A₀, eq_sum_singleBondForm A₁]
      exact apply_pair_sum M _ _
    have eB : M' ![B₀, B₁] = ∑ b, ∑ b', M' ![singleBondForm b (B₀ b), singleBondForm b' (B₁ b')] := by
      conv_lhs => rw [eq_sum_singleBondForm B₀, eq_sum_singleBondForm B₁]
      exact apply_pair_sum M' _ _
    rw [eA, eB]
    refine abs_double_sum_sub_le_of_matched I jι jι' hinj hinj' _ _ (fun b => ‖A₀ b‖) (fun b => ‖A₁ b‖)
      (fun b => ‖B₀ b‖) (fun b => ‖B₁ b‖)
      (fun p => ‖A₀ (jι p) - B₀ (jι' p)‖) (fun p => ‖A₁ (jι p) - B₁ (jι' p)‖) ε₁ ε₂ E K μ
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hε₁ hε₂ hE hK ?_ ?_ ?_ hA₀ hA₁ hB₀ hB₁ hd₀ hd₁
    · intro b b' hb
      refine abs_le_mul_norm_mul_norm_of_bihomogeneous (fun u v => M ![singleBondForm b u, singleBondForm b' v])
        (fun r u v => ?_) (fun r u v => ?_) ε₂ (fun X Y hX hY => ?_) (A₀ b) (A₁ b')
      · simp only [singleBondForm_smul_value, apply_pair_smul_left]
      · simp only [singleBondForm_smul_value, apply_pair_smul_right]
      · simp only [em]
        exact hEc.unlabelled_second _ _ _ _ (hb.imp (hout _) (hout _)) hX hY
    · intro b b' hb
      refine abs_le_mul_norm_mul_norm_of_bihomogeneous (fun u v => M' ![singleBondForm b u, singleBondForm b' v])
        (fun r u v => ?_) (fun r u v => ?_) ε₂ (fun X Y hX hY => ?_) (B₀ b) (B₁ b')
      · simp only [singleBondForm_smul_value, apply_pair_smul_left]
      · simp only [singleBondForm_smul_value, apply_pair_smul_right]
      · simp only [em']
        exact hEc.unlabelled_second' _ _ _ _ (hb.imp (hout' _) (hout' _)) hX hY
    · intro p hp q hq
      have h1 : |M ![singleBondForm (jι p) (A₀ (jι p)), singleBondForm (jι q) (A₁ (jι q))] -
          M' ![singleBondForm (jι' p) (A₀ (jι p)), singleBondForm (jι' q) (A₁ (jι q))]| ≤
            ε₁ * (‖A₀ (jι p)‖ * ‖A₁ (jι q)‖) := by
        refine abs_le_mul_norm_mul_norm_of_bihomogeneous
          (fun u v => M ![singleBondForm (jι p) u, singleBondForm (jι q) v] -
            M' ![singleBondForm (jι' p) u, singleBondForm (jι' q) v])
          (fun r u v => ?_) (fun r u v => ?_) ε₁ (fun X Y hX hY => ?_) _ _
        · simp only [singleBondForm_smul_value, apply_pair_smul_left]
          ring
        · simp only [singleBondForm_smul_value, apply_pair_smul_right]
          ring
        · simp only [em, em']
          exact hEc.labelled_second p q X Y hp hq hX hY
      have hsz : ∀ (b b' : ↥T') (u v : imaginaryQuaternions),
          |M' ![singleBondForm b u, singleBondForm b' v]| ≤ E * (‖u‖ * ‖v‖) := by
        intro b b' u v
        refine abs_le_mul_norm_mul_norm_of_bihomogeneous (fun u v => M' ![singleBondForm b u, singleBondForm b' v])
          (fun r u v => ?_) (fun r u v => ?_) E (fun X Y hX hY => ?_) u v
        · simp only [singleBondForm_smul_value, apply_pair_smul_left]
        · simp only [singleBondForm_smul_value, apply_pair_smul_right]
        · simp only [em']
          exact hEc.bound_second' _ _ _ _ hX hY
      have e : M ![singleBondForm (jι p) (A₀ (jι p)), singleBondForm (jι q) (A₁ (jι q))] -
          M' ![singleBondForm (jι' p) (B₀ (jι' p)), singleBondForm (jι' q) (B₁ (jι' q))] =
          (M ![singleBondForm (jι p) (A₀ (jι p)), singleBondForm (jι q) (A₁ (jι q))] -
            M' ![singleBondForm (jι' p) (A₀ (jι p)), singleBondForm (jι' q) (A₁ (jι q))]) +
            (M' ![singleBondForm (jι' p) (A₀ (jι p) - B₀ (jι' p)), singleBondForm (jι' q) (A₁ (jι q))] +
              M' ![singleBondForm (jι' p) (B₀ (jι' p)), singleBondForm (jι' q) (A₁ (jι q) - B₁ (jι' q))]) := by
        rw [← singleBondForm_sub_value, ← singleBondForm_sub_value, ← apply_pair_sub]
        ring
      show |M ![singleBondForm (jι p) (A₀ (jι p)), singleBondForm (jι q) (A₁ (jι q))] -
          M' ![singleBondForm (jι' p) (B₀ (jι' p)), singleBondForm (jι' q) (B₁ (jι' q))]| ≤ _
      rw [e]
      have h2 := hsz (jι' p) (jι' q) (A₀ (jι p) - B₀ (jι' p)) (A₁ (jι q))
      have h3 := hsz (jι' p) (jι' q) (B₀ (jι' p)) (A₁ (jι q) - B₁ (jι' q))
      refine (abs_add_le _ _).trans ?_
      have h4 := abs_add_le (M' ![singleBondForm (jι' p) (A₀ (jι p) - B₀ (jι' p)), singleBondForm (jι' q) (A₁ (jι q))])
        (M' ![singleBondForm (jι' p) (B₀ (jι' p)), singleBondForm (jι' q) (A₁ (jι q) - B₁ (jι' q))])
      linarith
  obtain ⟨x1, x2⟩ := derivs_along_motion_eq_formComposition hJ hC T G W α hT hG h0 hC₁
  obtain ⟨x1', x2'⟩ := derivs_along_motion_eq_formComposition hJ hC T' G' W' α' hT' hG' h0' hC₁'
  have sumT : ∀ (e : ℕ) (r : Fin e → Fin 2), ∑ b ∈ T, ‖motionComponent α r b.1 b.2‖ ≤ K →
      ∑ b : ↥T, ‖motionComponent α r b.1.1 b.1.2‖ ≤ K := fun e r h =>
    (Finset.sum_coe_sort T (fun b => ‖motionComponent α r b.1 b.2‖)).le.trans h
  have sumT' : ∀ (e : ℕ) (r : Fin e → Fin 2), ∑ b ∈ T', ‖motionComponent α' r b.1 b.2‖ ≤ K →
      ∑ b : ↥T', ‖motionComponent α' r b.1.1 b.1.2‖ ≤ K := fun e r h =>
    (Finset.sum_coe_sort T' (fun b => ‖motionComponent α' r b.1 b.2‖)).le.trans h
  refine ⟨fun l => ?_, ?_⟩
  · rw [x1 l, x1' l]
    exact first (fun b : ↥T => motionComponent α ![l] b.1.1 b.1.2)
      (fun b : ↥T' => motionComponent α' ![l] b.1.1 b.1.2)
      (sumT _ _ (hK1 l)) (sumT' _ _ (hK1' l)) (hμ1 l)
  · rw [x2, x2']
    have a1 := second (fun b : ↥T => motionComponent α ![0] b.1.1 b.1.2)
      (fun b : ↥T => motionComponent α ![1] b.1.1 b.1.2)
      (fun b : ↥T' => motionComponent α' ![0] b.1.1 b.1.2) (fun b : ↥T' => motionComponent α' ![1] b.1.1 b.1.2)
      (sumT _ _ (hK1 0)) (sumT _ _ (hK1 1)) (sumT' _ _ (hK1' 0)) (sumT' _ _ (hK1' 1)) (hμ1 0) (hμ1 1)
    have a2 := first (fun b : ↥T => motionComponent α ![0, 1] b.1.1 b.1.2)
      (fun b : ↥T' => motionComponent α' ![0, 1] b.1.1 b.1.2)
      (sumT _ _ hK2) (sumT' _ _ hK2') hμ2
    have e : ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) := fun a b c d => by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have e2 : ε₁ * (K ^ 2 + K) + 2 * ε₂ * (K ^ 2 + K) + E * (2 * K + 1) * μ =
        (ε₁ * K ^ 2 + 2 * ε₂ * K ^ 2 + 2 * E * K * μ) + (ε₁ * K + 2 * ε₂ * K + E * μ) := by ring
    rw [e2]
    exact add_le_add a1 a2
end ColdStepAtMirrorFrames
end YangMills.Construction
end
