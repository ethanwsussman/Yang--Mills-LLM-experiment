import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.CellGeometryOfATorus
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernels
import YangMills.Construction.RunningCouplingSlope.LeastFieldAtAColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.GaugeOfAMotionProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
section calculus
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]
private theorem exists_isOpen_contDiffOn_of_contDiffAt {f : E₁ → E₂} {x : E₁} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_isOpen_contDiffOn_of_contDiffAt <;> assumption
private theorem iteratedFDeriv_comp_eq_sum_orderedFinpartition {E₃ : Type*} [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] {g : E₂ → E₃} {β : E₁ → E₂} {x : E₁} {n : ℕ} (hg : ContDiffAt ℝ n g (β x))
    (hβ : ContDiffAt ℝ n β x) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (g ∘ β) x v = ∑ c : OrderedFinpartition n,
      iteratedFDeriv ℝ c.length g (β x)
        (c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x) v) := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_comp_eq_sum_orderedFinpartition <;> assumption
private theorem iteratedFDeriv_comp_clm_apply {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (Λ : E₁ →L[ℝ] E₂) {f : E₂ → E₃} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f (Λ x)) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_isOpen_contDiffOn_of_contDiffAt hf
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h
  rw [h]
  rfl
private theorem iteratedFDeriv_affine_of_two_le (L : E₁ →L[ℝ] E₂) (v₀ : E₂) {r : ℕ} (hr : 2 ≤ r)
    (x : E₁) : iteratedFDeriv ℝ r (fun τ => v₀ + L τ) x = 0 := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_const_add_clm_of_two_le <;> assumption
private theorem iteratedFDeriv_one_affine_apply (L : E₁ →L[ℝ] E₂) (v₀ : E₂) (x : E₁)
    (v : Fin 1 → E₁) : iteratedFDeriv ℝ 1 (fun τ => v₀ + L τ) x v = L (v 0) := by
  rw [iteratedFDeriv_one_apply, ((L.hasFDerivAt).const_add v₀).fderiv]
private theorem multilinear_apply_eq_sum_basis {k N : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) ℝ) (v : Fin k → Fin N → ℝ) :
    M v = ∑ n ∈ Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (Fin N)),
      (∏ m, v m (n m)) * M fun m => Pi.single (n m) 1 := by
  have hv : v = fun m => ∑ i ∈ (Finset.univ : Finset (Fin N)), v m i • (Pi.single i 1 : Fin N → ℝ) := by
    funext m i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [ContinuousMultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
abbrev _root_.YangMills.SharedProofs.p22319 := @multilinear_apply_eq_sum_basis
private def reindexCLM {j r : ℕ} (q : Fin r → Fin j) : (Fin r → ℝ) →L[ℝ] (Fin j → ℝ) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin r → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (q l) 1)
private theorem reindexCLM_apply {j r : ℕ} (q : Fin r → Fin j) (τ : Fin r → ℝ) :
    reindexCLM q τ = ∑ l, τ l • (Pi.single (q l) 1 : Fin j → ℝ) := by
  simp [reindexCLM]
private theorem reindexCLM_single {j r : ℕ} (q : Fin r → Fin j) (l : Fin r) :
    reindexCLM q (Pi.single l 1) = Pi.single (q l) 1 := by
  rw [reindexCLM_apply]
  simp [Pi.single_apply]
private theorem sum_reindexCLM_smul {E : Type*} [AddCommMonoid E] [Module ℝ E] {j r : ℕ}
    (q : Fin r → Fin j) (τ : Fin r → ℝ) (g : Fin j → E) :
    ∑ p, reindexCLM q τ p • g p = ∑ l, τ l • g (q l) := by
  simp only [reindexCLM_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Pi.single_apply, ite_smul]
end calculus
section sums
variable {ι : Type*}
private theorem sum_basis_choices_le (d : ι → ι → ℕ) (hsym : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) {N p : ℕ} (cl : Fin N → ι) (pc : Fin p → ι)
    (P : Finset ι) (hP : ∀ u ∈ P, ∃ i, pc i = u) (c : OrderedFinpartition p)
    (v : Fin c.length → Fin N → ℝ) (M : ℕ → ℝ) (hM : ∀ q, 0 ≤ M q) {R r₀ r₁ Cs : ℝ}
    (hr₀ : 0 ≤ r₀) (h1 : r₀ ≤ r₁) (h2 : 4 * r₀ ≤ R)
    (hv : ∀ (m : Fin c.length) (n : Fin N) (q : Fin (c.partSize m)),
      |v m n| ≤ M (c.partSize m) * Real.exp (-(R * d (cl n) (pc (c.emb m q)))))
    (hs : ∀ z, ∑ n, Real.exp (-(R / 2 * d (cl n) z)) ≤ Cs) :
    ∑ n ∈ Fintype.piFinset fun _ : Fin c.length => (Finset.univ : Finset (Fin N)),
        (∏ m, |v m (n m)|) * Real.exp (-(r₁ * (Finset.univ.sup fun m : Fin c.length =>
          Finset.univ.sup fun m' : Fin c.length => d (cl (n m)) (cl (n m')) : ℕ))) ≤
      (∏ m, M (c.partSize m)) * Cs ^ c.length *
        Real.exp (-(r₀ * (P.sup fun u => P.sup fun u' => d u u' : ℕ))) := by
  classical
  set D : ℕ := P.sup fun u => P.sup fun u' => d u u' with hD
  let l₀ : ∀ m : Fin c.length, Fin (c.partSize m) := fun m => ⟨0, c.partSize_pos m⟩
  let g : Fin c.length → Fin N → ℝ := fun m n =>
    Real.exp (-(R / 2 * d (cl n) (pc (c.emb m (l₀ m)))))
  have hg0 : ∀ m n, 0 ≤ g m n := fun m n => (Real.exp_pos _).le
  have hMp : 0 ≤ ∏ m, M (c.partSize m) := Finset.prod_nonneg fun m _ => hM _
  have hpt : ∀ n : Fin c.length → Fin N,
      (∏ m, |v m (n m)|) * Real.exp (-(r₁ * (Finset.univ.sup fun m : Fin c.length =>
          Finset.univ.sup fun m' : Fin c.length => d (cl (n m)) (cl (n m')) : ℕ))) ≤
        ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) * ∏ m, g m (n m) := by
    intro n
    set Δ : ℕ := Finset.univ.sup fun m : Fin c.length =>
      Finset.univ.sup fun m' : Fin c.length => d (cl (n m)) (cl (n m')) with hΔ
    let E : Fin c.length → ℕ := fun m => Finset.univ.sup fun q : Fin (c.partSize m) =>
      d (cl (n m)) (pc (c.emb m q))
    have hslot : ∀ m, |v m (n m)| ≤ M (c.partSize m) * Real.exp (-(R / 2 * E m)) * g m (n m) := by
      intro m
      have hne : (Finset.univ : Finset (Fin (c.partSize m))).Nonempty := ⟨l₀ m, Finset.mem_univ _⟩
      obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup Finset.univ hne
        (fun q : Fin (c.partSize m) => d (cl (n m)) (pc (c.emb m q)))
      have hEq : (E m : ℝ) = d (cl (n m)) (pc (c.emb m q)) := by
        simp only [E]
        rw [hq]
      refine (hv m (n m) q).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hM _)
      simp only [g]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [← hEq]
      have h3 : ((d (cl (n m)) (pc (c.emb m (l₀ m))) : ℕ) : ℝ) ≤ E m := by
        have : d (cl (n m)) (pc (c.emb m (l₀ m))) ≤ E m :=
          Finset.le_sup (f := fun q : Fin (c.partSize m) => d (cl (n m)) (pc (c.emb m q)))
            (Finset.mem_univ (l₀ m))
        exact_mod_cast this
      nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ R / 2)]
    have hEle : ∀ m, E m ≤ ∑ m', E m' := fun m =>
      Finset.single_le_sum (f := E) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    have hpar : ∀ i, d (pc i) (cl (n (c.index i))) ≤ ∑ m', E m' := by
      intro i
      have hl : c.emb (c.index i) (c.invEmbedding i) = i := c.emb_invEmbedding i
      have h3 : d (cl (n (c.index i))) (pc i) ≤ E (c.index i) := by
        have := Finset.le_sup (f := fun q : Fin (c.partSize (c.index i)) =>
          d (cl (n (c.index i))) (pc (c.emb (c.index i) q))) (Finset.mem_univ (c.invEmbedding i))
        simpa [hl] using this
      rw [hsym]
      exact h3.trans (hEle _)
    have hDle : D ≤ Δ + 2 * ∑ m', E m' := by
      simp only [hD]
      refine Finset.sup_le fun u hu => Finset.sup_le fun u' hu' => ?_
      obtain ⟨i, rfl⟩ := hP u hu
      obtain ⟨i', rfl⟩ := hP u' hu'
      have h3 := htri (pc i) (cl (n (c.index i))) (pc i')
      have h4 := htri (cl (n (c.index i))) (cl (n (c.index i'))) (pc i')
      have h5 : d (cl (n (c.index i))) (cl (n (c.index i'))) ≤ Δ := by
        have e1 := Finset.le_sup (f := fun m' : Fin c.length =>
          d (cl (n (c.index i))) (cl (n m'))) (Finset.mem_univ (c.index i'))
        have e2 := Finset.le_sup (f := fun m : Fin c.length =>
          Finset.univ.sup fun m' : Fin c.length => d (cl (n m)) (cl (n m')))
          (Finset.mem_univ (c.index i))
        exact e1.trans e2
      have h6 := hpar i
      have h7 := hpar i'
      rw [hsym] at h7
      omega
    have hDr : (D : ℝ) ≤ Δ + 2 * ∑ m', (E m' : ℝ) := by
      have : ((D : ℕ) : ℝ) ≤ ((Δ + 2 * ∑ m', E m' : ℕ) : ℝ) := by exact_mod_cast hDle
      push_cast at this
      exact this
    have hsE : (0 : ℝ) ≤ ∑ m', (E m' : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    have hprod : ∏ m, |v m (n m)| ≤
        (∏ m, M (c.partSize m)) * Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) * ∏ m, g m (n m) := by
      calc ∏ m, |v m (n m)| ≤
            ∏ m, (M (c.partSize m) * Real.exp (-(R / 2 * E m)) * g m (n m)) :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun m _ => hslot m
        _ = _ := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            congr 2
            rw [← Real.exp_sum]
            congr 1
            rw [Finset.mul_sum, Finset.sum_neg_distrib]
    have hgp : 0 ≤ ∏ m, g m (n m) := Finset.prod_nonneg fun m _ => hg0 m _
    have hexp : Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) * Real.exp (-(r₁ * Δ)) ≤
        Real.exp (-(r₀ * D)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have e1 : r₀ * D ≤ r₀ * (Δ + 2 * ∑ m', (E m' : ℝ)) := mul_le_mul_of_nonneg_left hDr hr₀
      have e2 : r₀ * Δ ≤ r₁ * Δ := mul_le_mul_of_nonneg_right h1 hΔ0
      have e3 : 4 * r₀ * ∑ m', (E m' : ℝ) ≤ R * ∑ m', (E m' : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hsE
      nlinarith
    calc (∏ m, |v m (n m)|) * Real.exp (-(r₁ * Δ))
        ≤ ((∏ m, M (c.partSize m)) * Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) * ∏ m, g m (n m)) *
            Real.exp (-(r₁ * Δ)) :=
          mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = (∏ m, M (c.partSize m)) * (Real.exp (-(R / 2 * ∑ m', (E m' : ℝ))) *
            Real.exp (-(r₁ * Δ))) * ∏ m, g m (n m) := by ring
      _ ≤ (∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D)) * ∏ m, g m (n m) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hMp) hgp
  have hsumg : ∑ n ∈ Fintype.piFinset (fun _ : Fin c.length => (Finset.univ : Finset (Fin N))),
      ∏ m, g m (n m) ≤ Cs ^ c.length := by
    rw [← Finset.prod_univ_sum]
    calc ∏ m, ∑ n, g m n ≤ ∏ _m : Fin c.length, Cs :=
          Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun n _ => hg0 m n) fun m _ => hs _
      _ = _ := by simp
  have hpre : 0 ≤ (∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D)) :=
    mul_nonneg hMp (Real.exp_pos _).le
  calc _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : Fin c.length => (Finset.univ : Finset (Fin N))),
        ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) * ∏ m, g m (n m) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) *
          ∑ n ∈ Fintype.piFinset (fun _ : Fin c.length => (Finset.univ : Finset (Fin N))),
            ∏ m, g m (n m) := by rw [Finset.mul_sum]
    _ ≤ ((∏ m, M (c.partSize m)) * Real.exp (-(r₀ * D))) * Cs ^ c.length :=
        mul_le_mul_of_nonneg_left hsumg hpre
    _ = _ := by ring
end sums
section imaginary
private def imCoord (r : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] r
private def imBasis (r : Fin 3) : imaginaryQuaternions :=
  ![⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 1, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 0, 1⟩ : ℍ[ℝ]), rfl⟩] r
private theorem sum_imCoord_smul_imBasis (w : imaginaryQuaternions) :
    ∑ r, imCoord r w • imBasis r = w := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [Fin.sum_univ_three, imCoord, imBasis]
  apply Quaternion.ext
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    simp [hw]
  · change (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    simp
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    simp
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    simp
private theorem imCoord_add (r : Fin 3) (w w' : imaginaryQuaternions) :
    imCoord r (w + w') = imCoord r w + imCoord r w' := by
  fin_cases r <;> simp [imCoord]
private theorem imCoord_smul (r : Fin 3) (u : ℝ) (w : imaginaryQuaternions) :
    imCoord r (u • w) = u * imCoord r w := by
  fin_cases r <;> simp [imCoord]
private theorem imaginary_ext {w w' : imaginaryQuaternions} (h : ∀ r, imCoord r w = imCoord r w') :
    w = w' := by
  rw [← sum_imCoord_smul_imBasis w, ← sum_imCoord_smul_imBasis w']
  simp only [h]
private theorem imCoord_imBasis (r r' : Fin 3) : imCoord r (imBasis r') = if r = r' then 1 else 0 := by
  fin_cases r <;> fin_cases r' <;> simp [imCoord, imBasis]
private theorem imCoord_toImaginary (r : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    imCoord r (toImaginary v) = v r := by
  fin_cases r <;> rfl
private theorem sq_norm_imaginary (w : imaginaryQuaternions) :
    ‖w‖ ^ 2 = (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  have h2 : ‖w‖ ^ 2 = Quaternion.normSq (w : ℍ[ℝ]) := by
    rw [Quaternion.normSq_eq_norm_mul_self, sq]
    rfl
  rw [h2, Quaternion.normSq_def', hw]
  ring
abbrev _root_.YangMills.SharedProofs.p1745 := @sq_norm_imaginary
private theorem abs_imCoord_le (r : Fin 3) (w : imaginaryQuaternions) : |imCoord r w| ≤ ‖w‖ := by
  apply abs_le_of_sq_le_sq _ (norm_nonneg _)
  rw [sq_norm_imaginary]
  have h1 := sq_nonneg (w : ℍ[ℝ]).imI
  have h2 := sq_nonneg (w : ℍ[ℝ]).imJ
  have h3 := sq_nonneg (w : ℍ[ℝ]).imK
  fin_cases r <;> simp [imCoord] <;> linarith
private theorem norm_imBasis (r : Fin 3) : ‖imBasis r‖ = 1 := by
  have h : ‖imBasis r‖ ^ 2 = 1 := by
    rw [sq_norm_imaginary]
    fin_cases r <;> simp [imBasis]
  have h0 := norm_nonneg (imBasis r)
  nlinarith
private def imCoordCLM (r : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := imCoord r
      map_add' := imCoord_add r
      map_smul' := fun u w => by simp [imCoord_smul] } 1
    (fun w => by simpa using abs_imCoord_le r w)
private theorem imCoordCLM_apply (r : Fin 3) (w : imaginaryQuaternions) :
    imCoordCLM r w = imCoord r w := rfl
private theorem imCoord_sum_smul_imBasis (r : Fin 3) (t : Fin 3 → ℝ) :
    imCoord r (∑ r', t r' • imBasis r') = t r := by
  rw [← imCoordCLM_apply, map_sum]
  simp only [map_smul, imCoordCLM_apply, imCoord_imBasis, smul_eq_mul]
  simp
end imaginary
section spread
variable {F : BlockFrame}
private theorem bondSpread_reindex {i j r : ℕ} (c : Fin j → F.Site i × Fin 4)
    (X : Fin j → imaginaryQuaternions) (q : Fin r → Fin j) (τ : Fin r → ℝ) :
    ColdStepAtMirrorFrames.bondSpread (c ∘ q) (X ∘ q) τ =
      ColdStepAtMirrorFrames.bondSpread c X (reindexCLM q τ) := by
  funext y d
  have h : ∀ (k : ℕ) (c' : Fin k → F.Site i × Fin 4) (X' : Fin k → imaginaryQuaternions)
      (ρ : Fin k → ℝ), ColdStepAtMirrorFrames.bondSpread c' X' ρ y d =
        ∑ p, ρ p • (if c' p = (y, d) then X' p else 0) := by
    intro k c' X' ρ
    simp only [ColdStepAtMirrorFrames.bondSpread]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [h, h, sum_reindexCLM_smul]
  rfl
private theorem bondSpread_zero_params {i k : ℕ} (c : Fin k → F.Site i × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ColdStepAtMirrorFrames.bondSpread c X 0 = fun _ _ => 0 := by
  funext y d
  simp [ColdStepAtMirrorFrames.bondSpread]
abbrev _root_.YangMills.SharedProofs.p27189 := @bondSpread_zero_params
private theorem expUnit_zero_local : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem leftTranslate_zero_local {i : ℕ} (W : F.GaugeField i) :
    leftTranslate (fun _ _ => 0) W = W := by
  funext y d
  simp [leftTranslate, expUnit_zero_local]
abbrev _root_.YangMills.SharedProofs.p21302 := @leftTranslate_zero_local
private theorem chartedField_congr_off_tree {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (V : F.GaugeField F.top) (h : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
end spread
section parameters
variable {F : BlockFrame} {l j : ℕ}
private def topProj (l j : ℕ) : (Fin (l + j) → ℝ) →L[ℝ] (Fin j → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd l i)
private theorem topProj_single_castAdd (i : Fin l) :
    topProj l j (Pi.single (Fin.castAdd j i) 1) = 0 := by
  funext i'
  have h : Fin.natAdd l i' ≠ Fin.castAdd j i := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  simp [topProj, Pi.single_apply, h]
abbrev _root_.YangMills.DeltaSharedProofs.p501334 := @topProj_single_castAdd
private theorem topProj_single_natAdd (i : Fin j) :
    topProj l j (Pi.single (Fin.natAdd l i) 1) = Pi.single i 1 := by
  funext i'
  have h : Fin.natAdd l i' = Fin.natAdd l i ↔ i' = i := by
    constructor
    · intro e
      have := congrArg Fin.val e
      simp at this
      exact Fin.ext this
    · rintro rfl; rfl
  simp [topProj, Pi.single_apply, h]
abbrev _root_.YangMills.DeltaSharedProofs.p501018 := @topProj_single_natAdd
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private theorem iteratedFDeriv_comp_topProj_eq_zero {H : (Fin j → ℝ) → E} (hH : AnalyticAt ℝ H 0)
    {q : ℕ} (J : Fin q → Fin (l + j)) (e₀ : Fin q) (i : Fin l) (he : J e₀ = Fin.castAdd j i) :
    iteratedFDeriv ℝ q (H ∘ topProj l j) 0 (fun e => Pi.single (J e) 1) = 0 := by
  have hz : topProj l j 0 = 0 := map_zero _
  have hc : ContDiffAt ℝ q H (topProj l j 0) := by
    rw [hz]
    exact hH.contDiffAt
  rw [iteratedFDeriv_comp_clm_apply (topProj l j) hc]
  refine ContinuousMultilinearMap.map_coord_zero _ e₀ ?_
  rw [he, topProj_single_castAdd]
abbrev _root_.YangMills.DeltaSharedProofs.p501352 := @iteratedFDeriv_comp_topProj_eq_zero
private theorem iteratedFDeriv_comp_topProj_eq_bondDeriv {fr : F.GaugeField F.top → E}
    {V : F.GaugeField F.top} {c : Fin j → F.Site F.top × Fin 4} {X : Fin j → imaginaryQuaternions}
    (hH : AnalyticAt ℝ
      (fun τ : Fin j → ℝ => fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0)
    {q : ℕ} (J : Fin q → Fin (l + j)) (J' : Fin q → Fin j) (he : ∀ e, J e = Fin.natAdd l (J' e)) :
    iteratedFDeriv ℝ q ((fun τ : Fin j → ℝ =>
        fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∘ topProj l j) 0
        (fun e => Pi.single (J e) 1) = bondDeriv fr V (c ∘ J') (X ∘ J') := by
  have hz : topProj l j 0 = 0 := map_zero _
  have hc : ContDiffAt ℝ q
      (fun τ : Fin j → ℝ => fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 :=
    hH.contDiffAt
  rw [iteratedFDeriv_comp_clm_apply (topProj l j) (by rw [hz]; exact hc), hz]
  have h1 : (fun τ : Fin q → ℝ =>
        fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread (c ∘ J') (X ∘ J') τ) V)) =
      (fun τ : Fin j → ℝ => fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∘
        reindexCLM J' := by
    funext τ
    simp only [Function.comp, bondSpread_reindex]
  have hz' : reindexCLM J' 0 = 0 := map_zero _
  have h2 := iteratedFDeriv_comp_clm_apply (reindexCLM J') (x := 0) (n := q)
    (f := fun τ : Fin j → ℝ => fr (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V))
    (by rw [hz']; exact hc) (fun e => Pi.single e 1)
  simp only [bondDeriv]
  rw [h1, h2, hz']
  simp only [reindexCLM_single, he, topProj_single_natAdd]
abbrev _root_.YangMills.DeltaSharedProofs.p501288 := @iteratedFDeriv_comp_topProj_eq_bondDeriv
end parameters
section coordinates
variable {F : BlockFrame} {l j : ℕ} (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
  (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
  (u : Fin l → EuclideanSpace ℝ (Fin 3))
  (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
private abbrev CoordIndex (F : BlockFrame) (j : ℕ) : Type :=
  (↥(chordBonds (finiteCells F)) × Fin 3) ⊕ Fin j
private def directionOf : CoordIndex F j → ChartDirection F
  | .inl p => .inl (p.1.1.1, p.1.1.2, imBasis p.2)
  | .inr i => .inr ((c i).1, (c i).2, X i)
open Classical in
private def fineLinear (β : ↥(chordBonds (finiteCells F))) (r : Fin 3) :
    (Fin (l + j) → ℝ) →L[ℝ] ℝ :=
  ∑ i, (if b i = β then u i r else 0) •
    (ContinuousLinearMap.proj (Fin.castAdd j i) : (Fin (l + j) → ℝ) →L[ℝ] ℝ)
private def topFrame (d : F.Site F.depth × Fin 4) : (Fin j → ℝ) → imaginaryQuaternions :=
  fun τ => fr d (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)
private def chartCoefficient : CoordIndex F j → (Fin (l + j) → ℝ) → ℝ
  | .inl p => fun τ => imCoordCLM p.2 (topFrame fr V c X p.1.1 (topProj l j τ)) +
      (-imCoord p.2 (fr p.1.1 V) + fineLinear (j := j) b u p.1 p.2 τ)
  | .inr i => fun τ => 0 + (ContinuousLinearMap.proj (Fin.natAdd l i) : (Fin (l + j) → ℝ) →L[ℝ] ℝ) τ
private def parameterCell : Fin (l + j) → F.Cell :=
  Fin.addCases (fun i => enclosingCell (b i).1.1) (fun i => (c i).1)
private theorem chartCoefficient_zero (z : CoordIndex F j) : chartCoefficient fr V b u c X z 0 = 0 := by
  cases z with
  | inl p =>
    simp only [chartCoefficient, topFrame, map_zero, bondSpread_zero_params, leftTranslate_zero_local,
      imCoordCLM_apply]
    ring
  | inr i => simp [chartCoefficient]
private theorem analyticAt_imCoord_topFrame {d : F.Site F.depth × Fin 4} (hA : IsBondAnalyticAt (fr d) V)
    (r : Fin 3) :
    AnalyticAt ℝ (fun τ : Fin (l + j) → ℝ => imCoordCLM r (topFrame fr V c X d (topProj l j τ))) 0 := by
  have h1 : AnalyticAt ℝ (topFrame fr V c X d) (topProj l j 0) := by
    rw [map_zero]
    exact hA j c X
  have h2 : AnalyticAt ℝ (topFrame fr V c X d ∘ topProj l j) 0 :=
    h1.comp ((topProj l j).analyticAt 0)
  exact (imCoordCLM r).analyticAt _ |>.comp h2
private theorem contDiffAt_chartCoefficient
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    (z : CoordIndex F j) (n : ℕ) : ContDiffAt ℝ n (chartCoefficient fr V b u c X z) 0 := by
  cases z with
  | inl p =>
    have h1 := (analyticAt_imCoord_topFrame fr V c X (hana p.1.1 p.1.2) (l := l) p.2).contDiffAt (n := n)
    exact h1.add (contDiffAt_const.add (fineLinear (j := j) b u p.1 p.2).contDiff.contDiffAt)
  | inr i =>
    exact contDiffAt_const.add (ContinuousLinearMap.proj (Fin.natAdd l i) :
      (Fin (l + j) → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
private theorem iteratedFDeriv_chartCoefficient_eq_zero
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    (z : CoordIndex F j) {q : ℕ} (hq : 2 ≤ q) (J : Fin q → Fin (l + j)) (e₀ : Fin q) (i : Fin l)
    (he : J e₀ = Fin.castAdd j i) :
    iteratedFDeriv ℝ q (chartCoefficient fr V b u c X z) 0 (fun e => Pi.single (J e) 1) = 0 := by
  cases z with
  | inl p =>
    have hA := hana p.1.1 p.1.2
    have hf : chartCoefficient fr V b u c X (.inl p) =
        (fun τ => imCoordCLM p.2 (topFrame fr V c X p.1.1 (topProj l j τ))) +
          fun τ => -imCoord p.2 (fr p.1.1 V) + fineLinear (j := j) b u p.1 p.2 τ := rfl
    have h1 := (analyticAt_imCoord_topFrame fr V c X hA (l := l) p.2).contDiffAt (n := q)
    have h2 : ContDiffAt ℝ q (fun τ => -imCoord p.2 (fr p.1.1 V) + fineLinear (j := j) b u p.1 p.2 τ) 0 :=
      contDiffAt_const.add (fineLinear (j := j) b u p.1 p.2).contDiff.contDiffAt
    rw [hf, iteratedFDeriv_add_apply h1 h2, iteratedFDeriv_affine_of_two_le _ _ hq]
    have h3 : AnalyticAt ℝ (topFrame fr V c X p.1.1) 0 := hA j c X
    have h4 : ContDiffAt ℝ q (topFrame fr V c X p.1.1 ∘ topProj l j) 0 := by
      have h5 : AnalyticAt ℝ (topFrame fr V c X p.1.1 ∘ topProj l j) 0 :=
        AnalyticAt.comp (by rw [map_zero]; exact h3) ((topProj l j).analyticAt 0)
      exact h5.contDiffAt
    have h6 := (imCoordCLM p.2).iteratedFDeriv_comp_left h4 (i := q) le_rfl
    have h7 := congrArg (fun M => M fun e => (Pi.single (J e) 1 : Fin (l + j) → ℝ)) h6
    have h8 := iteratedFDeriv_comp_topProj_eq_zero h3 J e₀ i he
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, h8,
      map_zero] at h7
    simpa [Function.comp_def] using h7
  | inr i' =>
    have hf : chartCoefficient fr V b u c X (.inr i') = fun τ => 0 +
        (ContinuousLinearMap.proj (Fin.natAdd l i') : (Fin (l + j) → ℝ) →L[ℝ] ℝ) τ := rfl
    rw [hf, iteratedFDeriv_affine_of_two_le _ _ hq]
    rfl
private theorem abs_iteratedFDeriv_chartCoefficient_le
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    {K : ℕ → ℝ} {r : ℝ} (hK : ∀ k, 0 ≤ K k) (hr : 0 ≤ r)
    (hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
      ‖bondDeriv (fr d) V c' X'‖ ≤ K k * Real.exp (-(r * bondListDistance (enclosingCell d.1) c')))
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (hz : ∀ y : F.Cell, cellSupDist y y = 0)
    (z : CoordIndex F j) {q : ℕ} (J : Fin q → Fin (l + j)) (e : Fin q) :
    |iteratedFDeriv ℝ q (chartCoefficient fr V b u c X z) 0 (fun e => Pi.single (J e) 1)| ≤
      (K q + 1) * Real.exp (-(r * cellSupDist (directionCell (directionOf c X z))
        (parameterCell b c (J e)))) := by
  classical
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact e.elim0
  have hKq : 0 ≤ K q + 1 := by have := hK q; linarith
  have hnn : 0 ≤ (K q + 1) *
      Real.exp (-(r * cellSupDist (directionCell (directionOf c X z)) (parameterCell b c (J e)))) :=
    mul_nonneg hKq (Real.exp_pos _).le
  cases z with
  | inr i' =>
    have hf : chartCoefficient fr V b u c X (.inr i') = fun τ => 0 +
        (ContinuousLinearMap.proj (Fin.natAdd l i') : (Fin (l + j) → ℝ) →L[ℝ] ℝ) τ := rfl
    rcases Nat.lt_or_ge q 2 with h2 | h2
    · obtain rfl : q = 1 := by omega
      have he0 : e = 0 := Subsingleton.elim _ _
      subst he0
      rw [hf, iteratedFDeriv_one_affine_apply]
      by_cases hJ : J 0 = Fin.natAdd l i'
      · have hcell : parameterCell b c (J 0) = (c i').1 := by
          rw [hJ]
          simp [parameterCell]
        have hs : directionCell (directionOf c X (.inr i' : CoordIndex F j)) = (c i').1 := rfl
        rw [hcell, hs, hz, hJ]
        have := hK 1
        simp
        linarith
      · have h0 : (ContinuousLinearMap.proj (Fin.natAdd l i') : (Fin (l + j) → ℝ) →L[ℝ] ℝ)
            (Pi.single (J 0) 1) = 0 := by
          have hne : Fin.natAdd l i' ≠ J 0 := fun h => hJ h.symm
          simp [Pi.single_apply, hne]
        rw [h0, abs_zero]
        exact hnn
    · rw [hf, iteratedFDeriv_affine_of_two_le _ _ h2]
      simpa using hnn
  | inl p =>
    obtain ⟨β, ρ⟩ := p
    have hA := hana β.1 β.2
    have hf : chartCoefficient fr V b u c X (.inl (β, ρ)) =
        (fun τ => imCoordCLM ρ (topFrame fr V c X β.1 (topProj l j τ))) +
          fun τ => -imCoord ρ (fr β.1 V) + fineLinear (j := j) b u β ρ τ := rfl
    have h1 := (analyticAt_imCoord_topFrame fr V c X hA (l := l) ρ).contDiffAt (n := q)
    have h2 : ContDiffAt ℝ q (fun τ => -imCoord ρ (fr β.1 V) + fineLinear (j := j) b u β ρ τ) 0 :=
      contDiffAt_const.add (fineLinear (j := j) b u β ρ).contDiff.contDiffAt
    have h3 : AnalyticAt ℝ (topFrame fr V c X β.1) 0 := hA j c X
    have h4 : ContDiffAt ℝ q (topFrame fr V c X β.1 ∘ topProj l j) 0 := by
      have h5 : AnalyticAt ℝ (topFrame fr V c X β.1 ∘ topProj l j) 0 :=
        AnalyticAt.comp (by rw [map_zero]; exact h3) ((topProj l j).analyticAt 0)
      exact h5.contDiffAt
    have h6 := (imCoordCLM ρ).iteratedFDeriv_comp_left h4 (i := q) le_rfl
    have h7 := congrArg (fun M => M fun e => (Pi.single (J e) 1 : Fin (l + j) → ℝ)) h6
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h7
    have h7' : iteratedFDeriv ℝ q (fun τ => imCoordCLM ρ (topFrame fr V c X β.1 (topProj l j τ))) 0
        (fun e => Pi.single (J e) 1) = imCoordCLM ρ
          (iteratedFDeriv ℝ q (topFrame fr V c X β.1 ∘ topProj l j) 0 fun e => Pi.single (J e) 1) := by
      simpa [Function.comp_def] using h7
    rw [hf, iteratedFDeriv_add_apply h1 h2]
    simp only [ContinuousMultilinearMap.add_apply]
    rw [h7']
    by_cases hit : ∃ (e₀ : Fin q) (i : Fin l), J e₀ = Fin.castAdd j i
    · obtain ⟨e₀, i, he₀⟩ := hit
      rw [iteratedFDeriv_comp_topProj_eq_zero h3 J e₀ i he₀, map_zero, zero_add]
      rcases Nat.lt_or_ge q 2 with h2' | h2'
      · obtain rfl : q = 1 := by omega
        have he0 : e = 0 := Subsingleton.elim _ _
        have he1 : e₀ = 0 := Subsingleton.elim _ _
        subst he0 he1
        rw [iteratedFDeriv_one_affine_apply]
        have hlin : fineLinear (j := j) b u β ρ (Pi.single (J 0) 1) =
            if b i = β then u i ρ else 0 := by
          rw [he₀]
          simp only [fineLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.proj_apply, smul_eq_mul]
          rw [Finset.sum_eq_single i]
          · simp
          · intro i' _ hne
            have h8 : Fin.castAdd j i' ≠ Fin.castAdd j i := fun h => hne (Fin.castAdd_injective _ _ h)
            simp [Pi.single_apply, h8]
          · simp
        rw [hlin]
        by_cases hb : b i = β
        · have hcell : parameterCell b c (J 0) = enclosingCell β.1.1 := by
            rw [he₀, ← hb]
            simp [parameterCell]
          have hs : directionCell (directionOf c X (.inl (β, ρ) : CoordIndex F j)) =
              enclosingCell β.1.1 := rfl
          rw [hcell, hs, hz, if_pos hb]
          have h9 : |u i ρ| ≤ 1 := by
            have := PiLp.norm_apply_le (u i) ρ
            rw [hu i] at this
            simpa using this
          have := hK 1
          simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
          linarith
        · rw [if_neg hb, abs_zero]
          exact hnn
      · rw [iteratedFDeriv_affine_of_two_le _ _ h2']
        simpa using hnn
    · push_neg at hit
      have hex : ∀ e', ∃ i', J e' = Fin.natAdd l i' := by
        intro e'
        induction h : J e' using Fin.addCases with
        | left i => exact absurd h (hit e' i)
        | right i' => exact ⟨i', rfl⟩
      choose J' hJ' using hex
      have hder := iteratedFDeriv_comp_topProj_eq_bondDeriv (fr := fr β.1) (V := V) (c := c) (X := X)
        h3 J J' hJ'
      have hu' : AreUnitVectors (X ∘ J') := fun e' => hX (J' e')
      have hb1 := hdec β.1 β.2 q (c ∘ J') (X ∘ J') hq1 hu'
      have hcell : parameterCell b c (J e) = (c (J' e)).1 := by
        rw [hJ']
        simp [parameterCell]
      have hs : directionCell (directionOf c X (.inl (β, ρ) : CoordIndex F j)) = enclosingCell β.1.1 := rfl
      have hdist : ((cellSupDist (enclosingCell β.1.1) (c (J' e)).1 : ℕ) : ℝ) ≤
          bondListDistance (enclosingCell β.1.1) (c ∘ J') := by
        have : cellSupDist (enclosingCell β.1.1) (c (J' e)).1 ≤
            bondListDistance (enclosingCell β.1.1) (c ∘ J') :=
          Finset.le_sup (f := fun l' => cellSupDist (enclosingCell β.1.1) (((c ∘ J') l').1))
            (Finset.mem_univ e)
        exact_mod_cast this
      have hmain : |imCoordCLM ρ (iteratedFDeriv ℝ q (topFrame fr V c X β.1 ∘ topProj l j) 0
          fun e => Pi.single (J e) 1)| ≤
            K q * Real.exp (-(r * cellSupDist (enclosingCell β.1.1) (c (J' e)).1)) := by
        have hd : (iteratedFDeriv ℝ q (topFrame fr V c X β.1 ∘ topProj l j) 0 fun e =>
            Pi.single (J e) 1) = bondDeriv (fr β.1) V (c ∘ J') (X ∘ J') := hder
        rw [hd, imCoordCLM_apply]
        refine (abs_imCoord_le _ _).trans (hb1.trans ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hK q)
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hdist hr]
      have hexp0 : 0 ≤ Real.exp (-(r * cellSupDist (enclosingCell β.1.1) (c (J' e)).1)) :=
        (Real.exp_pos _).le
      rw [hcell, hs]
      rcases Nat.lt_or_ge q 2 with h2' | h2'
      · obtain rfl : q = 1 := by omega
        have hlin : fineLinear (j := j) b u β ρ (Pi.single (J 0) 1) = 0 := by
          rw [hJ' 0]
          simp only [fineLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.proj_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun i _ => ?_
          have h8 : Fin.castAdd j i ≠ Fin.natAdd l (J' 0) := by
            intro e'
            have := congrArg Fin.val e'
            simp at this
            omega
          simp [Pi.single_apply, h8]
        rw [iteratedFDeriv_one_affine_apply, hlin, add_zero]
        have he0 : e = 0 := Subsingleton.elim _ _
        subst he0
        refine hmain.trans ?_
        nlinarith
      · rw [iteratedFDeriv_affine_of_two_le _ _ h2']
        simp only [ContinuousMultilinearMap.zero_apply, add_zero]
        refine hmain.trans ?_
        nlinarith
end coordinates
section core
variable {F : BlockFrame} {l j : ℕ}
private theorem jointDisplacement_eq_chartRestriction_comp (a : ℝ)
    (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    {N : ℕ} (e : CoordIndex F j ≃ Fin N) :
    jointDisplacement (fun ζ V' => chartedEnergy a
        (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X =
      chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V
        (fun n => directionOf c X (e.symm n)) ∘
        fun τ n => chartCoefficient fr V b u c X (e.symm n) τ := by
  classical
  funext τ
  simp only [jointDisplacement, Function.comp, chartRestriction]
  have htop : (fun y i => ∑ n : Fin N, chartCoefficient fr V b u c X (e.symm n) τ •
        directionMove (directionOf c X (e.symm n)) y i) =
      ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i) := by
    funext y i
    rw [Equiv.sum_comp e.symm
      (fun z : CoordIndex F j => chartCoefficient fr V b u c X z τ • directionMove (directionOf c X z) y i),
      Fintype.sum_sum_type]
    have h0 : ∀ p : ↥(chordBonds (finiteCells F)) × Fin 3,
        chartCoefficient fr V b u c X (.inl p) τ •
          directionMove (directionOf c X (.inl p : CoordIndex F j)) y i = 0 := by
      intro p
      simp [directionOf, directionMove]
    simp only [h0, Finset.sum_const_zero, zero_add, ColdStepAtMirrorFrames.bondSpread]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [chartCoefficient, directionOf, directionMove]
    have hiff : ((c i').1 = y ∧ (c i').2 = i) ↔ c i' = (y, i) := by
      rw [Prod.ext_iff]
    by_cases h : c i' = (y, i)
    · rw [if_pos (hiff.2 h), if_pos h]
      simp
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
      simp
  rw [htop]
  simp only [chartedEnergy]
  rw [chartedField_congr_off_tree _ ?_]
  intro x i ht
  have hmem := hchart (x, i) ht
  set β₀ : ↥(chordBonds (finiteCells F)) := ⟨(x, i), hmem⟩ with hβ₀
  have hsum : ∑ n : Fin N, chartCoefficient fr V b u c X (e.symm n) τ •
        directionCoordinate (directionOf c X (e.symm n)) x i =
      ∑ r, chartCoefficient fr V b u c X (.inl (β₀, r)) τ • imBasis r := by
    rw [Equiv.sum_comp e.symm
      (fun z : CoordIndex F j => chartCoefficient fr V b u c X z τ •
        directionCoordinate (directionOf c X z) x i),
      Fintype.sum_sum_type]
    have h0 : ∀ i' : Fin j,
        chartCoefficient fr V b u c X (.inr i') τ •
          directionCoordinate (directionOf c X (.inr i' : CoordIndex F j)) x i = 0 := by
      intro i'
      simp [directionOf, directionCoordinate]
    simp only [h0, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single β₀]
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [directionOf, directionCoordinate, hβ₀]
    · intro β _ hne
      refine Finset.sum_eq_zero fun r _ => ?_
      have hne' : ¬ (β.1.1 = x ∧ β.1.2 = i) := by
        rintro ⟨h1, h2⟩
        exact hne (Subtype.ext (Prod.ext h1 h2))
      simp [directionOf, directionCoordinate, hne']
    · simp
  rw [hsum]
  have hco : ∀ ζ : StepVariable (finiteCells F), stepCoordinates ζ x i = toImaginary (ζ β₀) := by
    intro ζ
    simp only [stepCoordinates]
    rw [dif_pos hmem]
  apply imaginary_ext
  intro r
  rw [imCoord_add, imCoord_add, imCoord_add, imCoord_sum_smul_imBasis, hco, hco, imCoord_toImaginary,
    imCoord_toImaginary]
  simp only [chartCoefficient, topFrame, imCoordCLM_apply, displacedPoint, fineLinear,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.add_apply, Finset.sum_apply]
  have htp : (topProj l j τ) = fun i => τ (Fin.natAdd l i) := rfl
  rw [htp]
  have hlin : ∀ i' : Fin l, ((Pi.single (b i') (τ (Fin.castAdd j i') • u i') :
      StepVariable (finiteCells F)) β₀) r =
        (if b i' = β₀ then u i' r else 0) * τ (Fin.castAdd j i') := by
    intro i'
    by_cases hb : b i' = β₀
    · rw [if_pos hb, ← hb]
      simp [mul_comm]
    · rw [if_neg hb, Pi.single_eq_of_ne (fun h => hb h.symm)]
      simp
  have hpt : (η β₀ + ∑ i', (Pi.single (b i') (τ (Fin.castAdd j i') • u i') :
      StepVariable (finiteCells F)) β₀) r = η β₀ r +
        ∑ i', (if b i' = β₀ then u i' r else 0) * τ (Fin.castAdd j i') := by
    simp only [PiLp.add_apply]
    congr 1
    rw [← Finset.sum_congr rfl fun i' _ => hlin i']
    exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) r : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) _ _
  rw [hpt]
  ring
private theorem iteratedFDeriv_chartRestriction_eq_chartMixedDeriv (a : ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) {N k : ℕ}
    (q : Fin N → ChartDirection F) (n : Fin k → Fin N) (hA : AnalyticAt ℝ (chartRestriction a w V q) 0) :
    iteratedFDeriv ℝ k (chartRestriction a w V q) 0 (fun m => Pi.single (n m) 1) =
      chartMixedDeriv a w V (q ∘ n) := by
  have h1 : chartRestriction a w V (q ∘ n) = chartRestriction a w V q ∘ reindexCLM n := by
    funext ρ
    simp only [chartRestriction, Function.comp]
    have e1 : (fun x i => w x i + ∑ p, reindexCLM n ρ p • directionCoordinate (q p) x i) =
        fun x i => w x i + ∑ m, ρ m • directionCoordinate (q (n m)) x i := by
      funext x i
      rw [sum_reindexCLM_smul n ρ (fun p => directionCoordinate (q p) x i)]
    have e2 : (fun y i => ∑ p, reindexCLM n ρ p • directionMove (q p) y i) =
        fun y i => ∑ m, ρ m • directionMove (q (n m)) y i := by
      funext y i
      rw [sum_reindexCLM_smul n ρ (fun p => directionMove (q p) y i)]
    rw [e1, e2]
  have hz : reindexCLM n 0 = 0 := map_zero _
  have h2 := iteratedFDeriv_comp_clm_apply (reindexCLM n) (x := 0) (n := k) (f := chartRestriction a w V q)
    (by rw [hz]; exact hA.contDiffAt) (fun m => Pi.single m 1)
  simp only [chartMixedDeriv]
  rw [h1, h2, hz]
  simp only [reindexCLM_single]
abbrev _root_.YangMills.SharedProofs.p3455 := @iteratedFDeriv_chartRestriction_eq_chartMixedDeriv
private theorem sum_exp_directionCell_le {N : ℕ} (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) (e : CoordIndex F j ≃ Fin N) {R Cb : ℝ} (hR : 0 ≤ R) (z : F.Cell)
    (hsum : ∑ β : ↥(chordBonds (finiteCells F)),
      Real.exp (-(R * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb) :
    ∑ n : Fin N, Real.exp (-(R * cellSupDist (directionCell (directionOf c X (e.symm n))) z)) ≤
      3 * Cb + j := by
  rw [Equiv.sum_comp e.symm
      (fun y : CoordIndex F j => Real.exp (-(R * cellSupDist (directionCell (directionOf c X y)) z))),
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∀ β : ↥(chordBonds (finiteCells F)),
      ∑ r : Fin 3, Real.exp (-(R * cellSupDist
          (directionCell (directionOf c X (.inl (β, r) : CoordIndex F j))) z)) =
        3 * Real.exp (-(R * cellSupDist (enclosingCell β.1.1) z)) := by
    intro β
    have : ∀ r : Fin 3, directionCell (directionOf c X (.inl (β, r) : CoordIndex F j)) =
        enclosingCell β.1.1 := fun r => rfl
    simp [this]
  have h2 : ∑ i : Fin j, Real.exp (-(R * cellSupDist
      (directionCell (directionOf c X (.inr i : CoordIndex F j))) z)) ≤ j := by
    calc _ ≤ ∑ _i : Fin j, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          apply Real.exp_le_one_iff.2
          have : (0 : ℝ) ≤ R * cellSupDist (directionCell (directionOf c X (.inr i : CoordIndex F j))) z :=
            mul_nonneg hR (Nat.cast_nonneg _)
          linarith
      _ = j := by simp
  simp only [h1]
  rw [← Finset.mul_sum]
  linarith
private theorem contDiffAt_and_abs_jointMixedDeriv_le (a : ℝ)
    (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    {K Ck : ℕ → ℝ} {κ₂ δ₁ r₀ Cb : ℝ} (hK : ∀ k, 0 ≤ K k) (hκ : 0 ≤ κ₂)
    (hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
      ‖bondDeriv (fr d) V c' X'‖ ≤ K k * Real.exp (-(κ₂ * bondListDistance (enclosingCell d.1) c')))
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (hCk : ∀ k, 0 ≤ Ck k)
    (hker : ∀ (k : ℕ) (q : Fin k → ChartDirection F),
      AnalyticAt ℝ (chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0 ∧
      (2 ≤ k → (∀ m, ‖directionVector (q m)‖ = 1) →
        |chartMixedDeriv a (fun z i => fr (z, i) V + stepCoordinates η z i) V q| ≤
          Ck k * Real.exp (-(δ₁ * directionDiameter q))))
    (hz : ∀ y : F.Cell, cellSupDist y y = 0) (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) (hCb : 0 ≤ Cb)
    (hsum : ∀ z : F.Cell, ∑ β : ↥(chordBonds (finiteCells F)),
      Real.exp (-(κ₂ / 2 * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb)
    (hl : 2 ≤ l) (hr₀ : 0 ≤ r₀) (h1 : r₀ ≤ δ₁) (h2 : 4 * r₀ ≤ κ₂) :
    ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' => chartedEnergy a
      (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X) 0 ∧
    |jointMixedDeriv (fun ζ V' => chartedEnergy a (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V')
        η V b u c X| ≤
      (∑ c' : OrderedFinpartition (l + j), Ck c'.length * (∏ m, (K (c'.partSize m) + 1)) *
        (3 * Cb + j) ^ c'.length) *
        Real.exp (-(r₀ * cellSetDiameter (chordBondCells b ∪ topBondCells c))) := by
  classical
  let e := Fintype.equivFin (CoordIndex F j)
  let q : Fin (Fintype.card (CoordIndex F j)) → ChartDirection F := fun n => directionOf c X (e.symm n)
  let Tt : (Fin (l + j) → ℝ) → Fin (Fintype.card (CoordIndex F j)) → ℝ :=
    fun τ n => chartCoefficient fr V b u c X (e.symm n) τ
  have hfun := jointDisplacement_eq_chartRestriction_comp a fr V η b u c X hchart e
  have hA := (hker _ q).1
  have T0 : Tt 0 = 0 := funext fun n => chartCoefficient_zero fr V b u c X _
  have hT : ∀ n : ℕ, ContDiffAt ℝ n Tt 0 := fun n =>
    contDiffAt_pi.2 fun m => contDiffAt_chartCoefficient fr V b u c X hana _ n
  have hA' : ContDiffAt ℝ (l + j : ℕ)
      (chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V q) (Tt 0) := by
    rw [T0]
    exact hA.contDiffAt
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact ContDiffAt.comp (0 : Fin (l + j) → ℝ) hA' (hT _)
  simp only [jointMixedDeriv]
  rw [hfun]
  have hcomp := iteratedFDeriv_comp_eq_sum_orderedFinpartition hA' (hT (l + j)) (fun i => Pi.single i 1)
  rw [T0] at hcomp
  rw [hcomp]
  set D := cellSetDiameter (chordBondCells b ∪ topBondCells c) with hD
  have hCs : 0 ≤ 3 * Cb + (j : ℝ) := by positivity
  have hMp : ∀ c' : OrderedFinpartition (l + j), 0 ≤ ∏ m, (K (c'.partSize m) + 1) := fun c' =>
    Finset.prod_nonneg fun m _ => by have := hK (c'.partSize m); linarith
  have hterm : ∀ c' : OrderedFinpartition (l + j),
      |iteratedFDeriv ℝ c'.length
          (chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0
        (c'.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c'.partSize m) Tt 0)
          fun i => Pi.single i 1)| ≤
        Ck c'.length * (∏ m, (K (c'.partSize m) + 1)) * (3 * Cb + j) ^ c'.length *
          Real.exp (-(r₀ * D)) := by
    intro c'
    set vv := c'.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c'.partSize m) Tt 0)
      (fun i => (Pi.single i 1 : Fin (l + j) → ℝ)) with hvvdef
    have hvv : ∀ (m : Fin c'.length) (n : Fin (Fintype.card (CoordIndex F j))),
        vv m n = iteratedFDeriv ℝ (c'.partSize m) (chartCoefficient fr V b u c X (e.symm n)) 0
          (fun q' => Pi.single (c'.emb m q') 1) := by
      intro m n
      simp only [hvvdef, OrderedFinpartition.applyOrderedFinpartition_apply]
      have h3 := (ContinuousLinearMap.proj n :
        (Fin (Fintype.card (CoordIndex F j)) → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
          (hT (c'.partSize m)) (i := c'.partSize m) le_rfl
      have h4 := congrArg (fun M => M fun l' => (Pi.single (c'.emb m l') 1 : Fin (l + j) → ℝ)) h3
      simpa [Tt, Function.comp_def] using h4.symm
    by_cases hk : 2 ≤ c'.length
    · have hkern : ∀ n : Fin c'.length → Fin (Fintype.card (CoordIndex F j)),
          |iteratedFDeriv ℝ c'.length
            (chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0
              (fun m => Pi.single (n m) 1)| ≤
            Ck c'.length * Real.exp (-(δ₁ * (Finset.univ.sup fun m : Fin c'.length =>
              Finset.univ.sup fun m' : Fin c'.length =>
                cellSupDist (directionCell (q (n m))) (directionCell (q (n m'))) : ℕ))) := by
        intro n
        rw [iteratedFDeriv_chartRestriction_eq_chartMixedDeriv a _ V q n hA]
        refine (hker _ (q ∘ n)).2 hk fun m => ?_
        show ‖directionVector (directionOf c X (e.symm (n m)))‖ = 1
        cases e.symm (n m) with
        | inl p => exact norm_imBasis p.2
        | inr i => exact hX i
      have hP : ∀ y ∈ chordBondCells b ∪ topBondCells c, ∃ i, parameterCell b c i = y := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
          exact ⟨Fin.castAdd j i, by simp [parameterCell]⟩
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
          exact ⟨Fin.natAdd l i, by simp [parameterCell]⟩
      have hplaces := sum_basis_choices_le cellSupDist hsym htri (fun n => directionCell (q n))
        (parameterCell b c) (chordBondCells b ∪ topBondCells c) hP c' vv (fun k => K k + 1)
        (fun k => by have := hK k; linarith) hr₀ h1 h2
        (fun m n q' => by
          rw [hvv]
          exact abs_iteratedFDeriv_chartCoefficient_le fr V b u c X hana hK hκ hdec hu hX hz _
            (c'.emb m) q')
        (fun y => sum_exp_directionCell_le c X e (by linarith) y (hsum y))
      rw [multilinear_apply_eq_sum_basis]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hstep : ∀ n ∈ Fintype.piFinset fun _ : Fin c'.length =>
          (Finset.univ : Finset (Fin (Fintype.card (CoordIndex F j)))),
          |(∏ m, vv m (n m)) * iteratedFDeriv ℝ c'.length
            (chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0
              (fun m => Pi.single (n m) 1)| ≤
            Ck c'.length * ((∏ m, |vv m (n m)|) *
              Real.exp (-(δ₁ * (Finset.univ.sup fun m : Fin c'.length =>
                Finset.univ.sup fun m' : Fin c'.length =>
                  cellSupDist (directionCell (q (n m))) (directionCell (q (n m'))) : ℕ)))) := by
        intro n _
        rw [abs_mul, Finset.abs_prod]
        have hp0 : 0 ≤ ∏ m, |vv m (n m)| := Finset.prod_nonneg fun m _ => abs_nonneg _
        calc _ ≤ (∏ m, |vv m (n m)|) * _ := mul_le_mul_of_nonneg_left (hkern n) hp0
          _ = _ := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum]
      refine (mul_le_mul_of_nonneg_left hplaces (hCk _)).trans (le_of_eq ?_)
      simp only [hD, cellSetDiameter]
      ring
    · have hl0 : 0 < l := by omega
      let i₀ : Fin l := ⟨0, hl0⟩
      let i₁ : Fin l := ⟨1, by omega⟩
      let a₀ : Fin (l + j) := Fin.castAdd j i₀
      let a₁ : Fin (l + j) := Fin.castAdd j i₁
      have hne : a₀ ≠ a₁ := by
        intro h
        have := congrArg Fin.val h
        simp [a₀, a₁, i₀, i₁] at this
      have hidx : c'.index a₁ = c'.index a₀ := by
        apply Fin.ext
        have e1 := (c'.index a₁).2
        have e2 := (c'.index a₀).2
        omega
      have hq₀ : c'.emb (c'.index a₀) (c'.invEmbedding a₀) = a₀ := c'.emb_invEmbedding a₀
      have key : ∀ m', c'.index a₁ = m' → ∃ q₁ : Fin (c'.partSize m'), c'.emb m' q₁ = a₁ := by
        rintro _ rfl
        exact ⟨_, c'.emb_invEmbedding a₁⟩
      obtain ⟨q₁, hq₁⟩ := key _ hidx
      have hsz : 2 ≤ c'.partSize (c'.index a₀) := by
        by_contra h
        have hqq : c'.invEmbedding a₀ = q₁ := by
          apply Fin.ext
          have e1 := (c'.invEmbedding a₀).2
          have e2 := q₁.2
          omega
        apply hne
        rw [← hq₀, ← hq₁, hqq]
      have hvz : vv (c'.index a₀) = 0 := by
        funext n
        rw [hvv]
        exact iteratedFDeriv_chartCoefficient_eq_zero fr V b u c X hana _ hsz (c'.emb (c'.index a₀))
          (c'.invEmbedding a₀) i₀ hq₀
      rw [ContinuousMultilinearMap.map_coord_zero _ (c'.index a₀) hvz, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (hCk _) (hMp c')) (pow_nonneg hCs _)) (Real.exp_pos _).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c' _ => hterm c').trans ?_)
  rw [Finset.sum_mul]
abbrev _root_.YangMills.SharedProofs.p59928 := @contDiffAt_and_abs_jointMixedDeriv_le
end core
private theorem stepCoordinates_zero_local {F : BlockFrame} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs with h
  · apply Subtype.ext
    ext <;> simp [toImaginary]
  · rfl
end Interpolation
namespace RunningCouplingSlope
open Interpolation
theorem energyAtMinimizerDerivBound (hLF : MinimizerAtReachableColdness)
    (hK : ChartEnergyKernelBound) (hgeo : CubicTorusCellGeometry)
    (hcov : BlocksCoverLowerLevel) : energyAtMinimizerDerivBoundStatement := by
  intro a L c ha hL hL40 hc
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hL hL40 hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hNpos : ∀ k, 0 < c.N k := hc.positivity.2.2.2.2.2.1
  obtain ⟨Cg, hCg, hsum⟩ := hgeo.2 (c.δ₁ / 2) (by linarith)
  have hL0 : 0 < L := hL.pos
  let Cb : ℝ := Cg * (L : ℝ) ^ 4
  have hCb : 0 ≤ Cb := by positivity
  have hK0 : ∀ k, 0 ≤ c.N k := fun k => (hNpos k).le
  let B : ℕ → ℕ → ℝ := fun l j => ∑ c' : OrderedFinpartition (l + j), Ck c'.length *
    (∏ m, (c.N (c'.partSize m) + 1)) * (3 * Cb + j) ^ c'.length
  have hB : ∀ l j, 0 ≤ B l j := fun l j => Finset.sum_nonneg fun c' _ =>
    mul_nonneg (mul_nonneg (hCk _).le (Finset.prod_nonneg fun m _ => by
      have := hK0 (c'.partSize m); linarith)) (by positivity)
  refine ⟨fun l j => B l j + 1, fun l j => by have := hB l j; linarith, ?_⟩
  intro F s V hF hs hV l j b u e X hl hu hX
  obtain ⟨-, -, -, hpt, hfr⟩ := hLF a L c ha hL hL40 hc F s V hF hs hV
  set fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions :=
    fun d => stepFrame true a c.ρA 0 d with hfrd
  have hzero : (fun z i => fr (z, i) V + stepCoordinates (0 : StepVariable (finiteCells F)) z i) =
      fun z i => fr (z, i) V := by
    funext z i
    rw [stepCoordinates_zero_local, add_zero]
  have hodd : Odd F.blockSide := hF.1 ▸ hL
  have hcub := hF.2
  obtain ⟨n, hn64, hside⟩ := id hcub
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hall := hcov F hodd hpos
  have hbond : ∀ d : F.Site F.depth × Fin 4, d ∈ fineBonds F := fun d => by
    simp [fineBonds, hall]
  have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
    simp [chordBonds, innerBonds, hall, hd]
  have hg1 := hgeo.1 F hodd hcub
  have hsum' : ∀ z : F.Cell, ∑ β : ↥(chordBonds (finiteCells F)),
      Real.exp (-(c.δ₁ / 2 * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb := by
    intro z
    have h1 := hsum F hodd hcub z
    rw [hF.1] at h1
    rw [Finset.sum_coe_sort (chordBonds (finiteCells F))
      (fun d => Real.exp (-(c.δ₁ / 2 * cellSupDist (enclosingCell d.1) z)))]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun d _ => hbond d)
      fun _ _ _ => (Real.exp_pos _).le) h1
  have hcore := contDiffAt_and_abs_jointMixedDeriv_le a fr V 0 b u e X hchart (fun d hd => (hfr d hd).1)
    (K := c.N) (Ck := Ck) (κ₂ := c.δ₁) (δ₁ := c.δ₁) (r₀ := c.δ₁ / 4) (Cb := Cb) hK0 hδ.le
    (fun d hd k c' X' hk hX' => (hfr d hd).2 k c' X' hk hX')
    hu hX (fun k => (hCk k).le)
    (fun k q => by
      rw [hzero]
      have := hker F _ V hF hpt k q
      exact ⟨this.1, fun h2 hq => this.2 h2 hq⟩)
    (fun z => by simp [cellSupDist]) hg1.2.2.1 hg1.2.2.2.1 hCb hsum' hl (by positivity) (by linarith)
    (by linarith)
  refine ⟨hcore.1, hcore.2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  show B l j ≤ B l j + 1
  linarith
end RunningCouplingSlope
end YangMills.Construction
end
