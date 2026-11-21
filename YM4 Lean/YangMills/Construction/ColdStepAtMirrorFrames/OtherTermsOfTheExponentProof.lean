import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.HaarTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
namespace RemainderExponent
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem contDiffAt_of_comp_add {f : P → ℝ} {η : P} (h : ContDiffAt ℝ 3 (fun ζ => f (η + ζ)) 0) :
    ContDiffAt ℝ 3 f η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.contDiffAt_of_comp_add_left <;> assumption
theorem fderiv_comp_add_apply (f : P → ℝ) (η u : P) :
    fderiv ℝ (fun ζ => f (η + ζ)) 0 u = fderiv ℝ f η u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.fderiv_comp_add_left_zero_apply <;> assumption
theorem fderiv_fderiv_comp_add_apply (f : P → ℝ) (η u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => f (η + ξ)) ζ u) 0 v =
      fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.fderiv_fderiv_comp_add_left_zero <;> assumption
theorem affineCombination_three_derivs {g₁ g₂ g₃ : P → ℝ} (c₀ c₁ c₂ c₃ : ℝ) (h₁ : ContDiffAt ℝ 3 g₁ 0)
    (h₂ : ContDiffAt ℝ 3 g₂ 0) (h₃ : ContDiffAt ℝ 3 g₃ 0) (u v : P) :
    ContDiffAt ℝ 3 (fun ζ => c₀ + c₁ * g₁ ζ + c₂ * g₂ ζ + c₃ * g₃ ζ) 0 ∧
    fderiv ℝ (fun ζ => c₀ + c₁ * g₁ ζ + c₂ * g₂ ζ + c₃ * g₃ ζ) 0 u =
      c₁ * fderiv ℝ g₁ 0 u + c₂ * fderiv ℝ g₂ 0 u + c₃ * fderiv ℝ g₃ 0 u ∧
    fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => c₀ + c₁ * g₁ ξ + c₂ * g₂ ξ + c₃ * g₃ ξ) ζ u) 0 v =
      c₁ * fderiv ℝ (fun ζ => fderiv ℝ g₁ ζ u) 0 v + c₂ * fderiv ℝ (fun ζ => fderiv ℝ g₂ ζ u) 0 v +
        c₃ * fderiv ℝ (fun ζ => fderiv ℝ g₃ ζ u) 0 v := by
  have hd : ∀ {g : P → ℝ}, ContDiffAt ℝ 3 g 0 → ∀ᶠ ζ in 𝓝 (0 : P), DifferentiableAt ℝ g ζ := by
    intro g hg
    filter_upwards [hg.eventually (by simp)] with ζ hζ using hζ.differentiableAt (by norm_num)
  have hfs : ∀ ζ, DifferentiableAt ℝ g₁ ζ → DifferentiableAt ℝ g₂ ζ → DifferentiableAt ℝ g₃ ζ →
      ∀ w : P, fderiv ℝ (fun ξ => c₀ + c₁ * g₁ ξ + c₂ * g₂ ξ + c₃ * g₃ ξ) ζ w =
        c₁ * fderiv ℝ g₁ ζ w + c₂ * fderiv ℝ g₂ ζ w + c₃ * fderiv ℝ g₃ ζ w := by
    intro ζ d₁ d₂ d₃ w
    have h : HasFDerivAt (fun ξ => c₀ + c₁ * g₁ ξ + c₂ * g₂ ξ + c₃ * g₃ ξ)
        (c₁ • fderiv ℝ g₁ ζ + c₂ • fderiv ℝ g₂ ζ + c₃ • fderiv ℝ g₃ ζ) ζ :=
      (((d₁.hasFDerivAt.const_mul c₁).const_add c₀).add (d₂.hasFDerivAt.const_mul c₂)).add
        (d₃.hasFDerivAt.const_mul c₃)
    rw [h.fderiv]
    simp
  have hgd : ∀ {g : P → ℝ}, ContDiffAt ℝ 3 g 0 → DifferentiableAt ℝ (fun ζ => fderiv ℝ g ζ u) 0 := by
    intro g hg
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ g) 0 := hg.fderiv_right (by norm_num)
    exact (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
  refine ⟨((contDiffAt_const.add (contDiffAt_const.mul h₁)).add (contDiffAt_const.mul h₂)).add
      (contDiffAt_const.mul h₃),
    hfs 0 (h₁.differentiableAt (by norm_num)) (h₂.differentiableAt (by norm_num))
      (h₃.differentiableAt (by norm_num)) u, ?_⟩
  have he : (fun ζ => fderiv ℝ (fun ξ => c₀ + c₁ * g₁ ξ + c₂ * g₂ ξ + c₃ * g₃ ξ) ζ u) =ᶠ[𝓝 (0 : P)]
      fun ζ => c₁ * fderiv ℝ g₁ ζ u + c₂ * fderiv ℝ g₂ ζ u + c₃ * fderiv ℝ g₃ ζ u := by
    filter_upwards [hd h₁, hd h₂, hd h₃] with ζ d₁ d₂ d₃ using hfs ζ d₁ d₂ d₃ u
  rw [he.fderiv_eq]
  have h : HasFDerivAt (fun ζ => c₁ * fderiv ℝ g₁ ζ u + c₂ * fderiv ℝ g₂ ζ u + c₃ * fderiv ℝ g₃ ζ u)
      (c₁ • fderiv ℝ (fun ζ => fderiv ℝ g₁ ζ u) 0 + c₂ • fderiv ℝ (fun ζ => fderiv ℝ g₂ ζ u) 0 +
        c₃ • fderiv ℝ (fun ζ => fderiv ℝ g₃ ζ u) 0) 0 :=
    (((hgd h₁).hasFDerivAt.const_mul c₁).add ((hgd h₂).hasFDerivAt.const_mul c₂)).add
      ((hgd h₃).hasFDerivAt.const_mul c₃)
  rw [h.fderiv]
  simp
end Calculus
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) x i = stepCoordinates η x i + stepCoordinates ζ x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
def shiftedCoordinates (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + stepCoordinates η x i
theorem shiftedCoordinates_add (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    shiftedCoordinates w η x i + stepCoordinates ζ x i = w x i + stepCoordinates (η + ζ) x i := by
  simp only [shiftedCoordinates, stepCoordinates_add, add_assoc]
theorem readInChart_add {E : Type} (G : F.GaugeField F.depth → E)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η ζ : StepVariable (finiteCells F)) :
    readInChart G w V (η + ζ) = readInChart G (shiftedCoordinates w η) V ζ := by
  unfold readInChart
  congr 2
  funext x i
  exact (shiftedCoordinates_add w η ζ x i).symm
theorem haarExcessSum_add (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (η ζ : StepVariable (finiteCells F)) :
    haarExcessSum w (η + ζ) = haarExcessSum (shiftedCoordinates w η) ζ := by
  unfold haarExcessSum
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [shiftedCoordinates_add]
theorem sum_chordBonds_exp_le {γ S : ℝ} (z : F.Site F.depth)
    (hS : ∀ A : Finset (F.Site F.depth), ∑ u ∈ A, Real.exp (-(γ * siteSupDist z u)) ≤ S) :
    ∑ b : ChordBond F, Real.exp (-(γ * siteSupDist z b.1.1)) ≤ 4 * S := by
  classical
  set φ : F.Site F.depth × Fin 4 → ℝ := fun b => Real.exp (-(γ * siteSupDist z b.1)) with hφ
  have h1 : ∑ b : ChordBond F, Real.exp (-(γ * siteSupDist z b.1.1)) =
      ∑ b ∈ chordBonds (finiteCells F), φ b :=
    Finset.sum_coe_sort (chordBonds (finiteCells F)) φ
  set A : Finset (F.Site F.depth) := (chordBonds (finiteCells F)).image Prod.fst with hA
  have hsub : chordBonds (finiteCells F) ⊆ A ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hb, Finset.mem_univ _⟩
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := φ)
    (fun _ _ _ => (Real.exp_pos _).le)
  have h3 : ∑ b ∈ A ×ˢ (Finset.univ : Finset (Fin 4)), φ b =
      4 * ∑ u ∈ A, Real.exp (-(γ * siteSupDist z u)) := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [hφ]
  have h4 := hS A
  rw [h1]
  linarith
theorem kernel_row_sum_le {L : ℕ} {κ δ Cg CH Cr E S1 S3 : ℝ} (hD : SupDistCellComparison)
    (hL : Odd F.blockSide) (hFL : F.blockSide = L) (hpos : ∀ i, 0 < F.extent i) (hLb : 2 ^ 40 ≤ L)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : δ = κ / 2 ^ 10) (hCg : 0 ≤ Cg) (hCH : 0 ≤ CH) (hCr : 0 ≤ Cr)
    (hE : 0 ≤ E)
    (hS1 : ∀ (z : F.Site F.depth) (A : Finset (F.Site F.depth)),
      ∑ u ∈ A, Real.exp (-(1 * siteSupDist z u)) ≤ S1)
    (hS3 : ∀ (z : F.Site F.depth) (A : Finset (F.Site F.depth)),
      ∑ u ∈ A, Real.exp (-(δ / 3 * siteSupDist z u)) ≤ S3) (hS3n : 0 ≤ S3) (b : ChordBond F) :
    ∑ b' : ChordBond F, ((if siteSupDist b.1.1 b'.1.1 ≤ 10 * L then Cg else 0) +
        (if b = b' then CH else 0) + Cr * E * expansionDecayKernel F δ b b') *
        Real.exp (2 * κ * chordBondDist F b b') ≤
      Cg * Real.exp 22 * Real.exp (10 * L) * (4 * S1) + CH +
        Cr * E * Real.exp 2 * (S3 * (4 * S3)) := by
  classical
  have hLr : (2 : ℝ) ^ 40 ≤ L := by exact_mod_cast hLb
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLr
  have hsymm : ∀ y z : F.Site F.depth, siteSupDist y z = siteSupDist z y :=
    fun y z => (hD.1 F F.depth y z y).2.1
  have hdist : ∀ b' : ChordBond F, chordBondDist F b b' ≤ (siteSupDist b.1.1 b'.1.1 : ℝ) / L + 1 := by
    intro b'
    have h1 := ((hD.2.2 F hL hpos).1 b.1.1 b'.1.1)
    have h2 : chordBondDist F b b' =
        (siteSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ) := rfl
    rw [h2, hFL] at *
    rw [div_add_one hLpos.ne', le_div_iff₀ hLpos]
    nlinarith
  have hd0 : ∀ b' : ChordBond F, 0 ≤ chordBondDist F b b' := fun b' => Nat.cast_nonneg _
  have hsplit : ∑ b' : ChordBond F, ((if siteSupDist b.1.1 b'.1.1 ≤ 10 * L then Cg else 0) +
      (if b = b' then CH else 0) + Cr * E * expansionDecayKernel F δ b b') *
        Real.exp (2 * κ * chordBondDist F b b') =
      ∑ b' : ChordBond F, (if siteSupDist b.1.1 b'.1.1 ≤ 10 * L then Cg else 0) *
        Real.exp (2 * κ * chordBondDist F b b') +
      ∑ b' : ChordBond F, (if b = b' then CH else 0) * Real.exp (2 * κ * chordBondDist F b b') +
      ∑ b' : ChordBond F, Cr * E * expansionDecayKernel F δ b b' * Real.exp (2 * κ * chordBondDist F b b') := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [hsplit]
  have t1 : ∑ b' : ChordBond F, (if siteSupDist b.1.1 b'.1.1 ≤ 10 * L then Cg else 0) *
      Real.exp (2 * κ * chordBondDist F b b') ≤ Cg * Real.exp 22 * Real.exp (10 * L) * (4 * S1) := by
    have hterm : ∀ b' : ChordBond F, (if siteSupDist b.1.1 b'.1.1 ≤ 10 * L then Cg else 0) *
        Real.exp (2 * κ * chordBondDist F b b') ≤
        Cg * Real.exp 22 * Real.exp (10 * L) * Real.exp (-(1 * siteSupDist b.1.1 b'.1.1)) := by
      intro b'
      by_cases hc : siteSupDist b.1.1 b'.1.1 ≤ 10 * L
      · rw [if_pos hc]
        have hcr : (siteSupDist b.1.1 b'.1.1 : ℝ) ≤ 10 * L := by exact_mod_cast hc
        have h1 : chordBondDist F b b' ≤ 11 := by
          have := hdist b'
          have h2 : (siteSupDist b.1.1 b'.1.1 : ℝ) / L ≤ 10 := by
            rw [div_le_iff₀ hLpos]
            linarith
          linarith
        have h2 : Real.exp (2 * κ * chordBondDist F b b') ≤ Real.exp 22 := by
          rw [Real.exp_le_exp]
          nlinarith [hd0 b']
        have h3 : 1 ≤ Real.exp (10 * L) * Real.exp (-(1 * siteSupDist b.1.1 b'.1.1)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        calc Cg * Real.exp (2 * κ * chordBondDist F b b') ≤ Cg * Real.exp 22 :=
              mul_le_mul_of_nonneg_left h2 hCg
          _ = Cg * Real.exp 22 * 1 := (mul_one _).symm
          _ ≤ Cg * Real.exp 22 * (Real.exp (10 * L) * Real.exp (-(1 * siteSupDist b.1.1 b'.1.1))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = _ := by ring
      · rw [if_neg hc, zero_mul]
        positivity
    calc _ ≤ ∑ b' : ChordBond F, Cg * Real.exp 22 * Real.exp (10 * L) *
          Real.exp (-(1 * siteSupDist b.1.1 b'.1.1)) := Finset.sum_le_sum fun b' _ => hterm b'
      _ = Cg * Real.exp 22 * Real.exp (10 * L) *
          ∑ b' : ChordBond F, Real.exp (-(1 * siteSupDist b.1.1 b'.1.1)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_chordBonds_exp_le b.1.1 (hS1 b.1.1)) (by positivity)
  have t2 : ∑ b' : ChordBond F, (if b = b' then CH else 0) * Real.exp (2 * κ * chordBondDist F b b') ≤
      CH := by
    rw [Finset.sum_eq_single b]
    · have h0 : chordBondDist F b b = 0 := by
        have : siteSupDist (enclosingCell b.1.1) (enclosingCell b.1.1) = 0 :=
          (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b.1.1) (enclosingCell b.1.1)).1
        change ((siteSupDist (enclosingCell b.1.1) (enclosingCell b.1.1) : ℕ) : ℝ) = 0
        simp [this]
      simp [h0]
    · intro b' _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have t3 : ∑ b' : ChordBond F, Cr * E * expansionDecayKernel F δ b b' *
      Real.exp (2 * κ * chordBondDist F b b') ≤ Cr * E * Real.exp 2 * (S3 * (4 * S3)) := by
    have hδ0 : 0 < δ := by rw [hδ]; positivity
    have hrate : 2 * κ / L ≤ δ / 3 := by
      rw [hδ, div_le_iff₀ hLpos]
      have : κ / 2 ^ 10 / 3 * L = κ * (L / (3 * 2 ^ 10)) := by ring
      rw [this]
      nlinarith
    have hterm : ∀ (b' : ChordBond F) (y : F.Site F.depth),
        Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b'.1.1 +
          siteSupDist b.1.1 b'.1.1))) * Real.exp (2 * κ * chordBondDist F b b') ≤
        Real.exp 2 * (Real.exp (-(δ / 3 * siteSupDist y b.1.1)) *
          Real.exp (-(δ / 3 * siteSupDist y b'.1.1))) := by
      intro b' y
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h1 := hdist b'
      have h2 : 2 * κ * chordBondDist F b b' ≤ 2 * κ * ((siteSupDist b.1.1 b'.1.1 : ℝ) / L + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : 2 * κ * ((siteSupDist b.1.1 b'.1.1 : ℝ) / L) ≤ δ / 3 * siteSupDist b.1.1 b'.1.1 := by
        have : 2 * κ * ((siteSupDist b.1.1 b'.1.1 : ℝ) / L) =
            2 * κ / L * siteSupDist b.1.1 b'.1.1 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)
      nlinarith
    have hrow : ∀ b' : ChordBond F, expansionDecayKernel F δ b b' * Real.exp (2 * κ * chordBondDist F b b') ≤
        Real.exp 2 * ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
          Real.exp (-(δ / 3 * siteSupDist y b.1.1)) * Real.exp (-(δ / 3 * siteSupDist y b'.1.1)) := by
      intro b'
      unfold expansionDecayKernel
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => hterm b' y
    have hsum : ∑ b' : ChordBond F, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        Real.exp (-(δ / 3 * siteSupDist y b.1.1)) * Real.exp (-(δ / 3 * siteSupDist y b'.1.1)) ≤
        S3 * (4 * S3) := by
      rw [Finset.sum_comm]
      have h1 : ∀ y ∈ sitesOfCells (finiteCells F) F.depth, ∑ b' : ChordBond F,
          Real.exp (-(δ / 3 * siteSupDist y b.1.1)) * Real.exp (-(δ / 3 * siteSupDist y b'.1.1)) ≤
          Real.exp (-(δ / 3 * siteSupDist y b.1.1)) * (4 * S3) := by
        intro y _
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_chordBonds_exp_le y (hS3 y)) (Real.exp_pos _).le
      refine (Finset.sum_le_sum h1).trans ?_
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h2 := hS3 b.1.1 (sitesOfCells (finiteCells F) F.depth)
      simpa only [hsymm b.1.1] using h2
    have hCE : 0 ≤ Cr * E := by positivity
    calc _ = Cr * E * ∑ b' : ChordBond F, expansionDecayKernel F δ b b' *
          Real.exp (2 * κ * chordBondDist F b b') := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b' _ => ?_
          ring
      _ ≤ Cr * E * ∑ b' : ChordBond F, Real.exp 2 * ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
          Real.exp (-(δ / 3 * siteSupDist y b.1.1)) * Real.exp (-(δ / 3 * siteSupDist y b'.1.1)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b' _ => hrow b') hCE
      _ = Cr * E * Real.exp 2 * ∑ b' : ChordBond F, ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
          Real.exp (-(δ / 3 * siteSupDist y b.1.1)) * Real.exp (-(δ / 3 * siteSupDist y b'.1.1)) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith
set_option maxHeartbeats 2000000 in
theorem remainderExponentBounds (hFr : FrameBoundsEventually) (hJ : EventuallyInParametersCombines)
    (hG : GapTermsChartBounds) (hH : HaarExcessSumDiagonalBounds)
    (hR : ExpansionTermsChartBounds) (hM : ChartShiftLipschitz)
    (hS : ExpDecaySumBounded) (hD : SupDistCellComparison) :
    RemainderExponentBounds := by
  classical
  choose! Cgf hCgf using hG
  choose! Sf hSf using hS
  obtain ⟨CH, hCH, hH⟩ := hH
  obtain ⟨Cr, hCr, hR⟩ := hR
  let Mrow : StepParameters → ℝ := fun T =>
    Cgf T.L * Real.exp 22 * Real.exp (10 * T.L) * (4 * Sf 1) + CH +
      Cr * T.E * Real.exp 2 * (Sf (T.decayRate / 3) * (4 * Sf (T.decayRate / 3)))
  let Msl : StepParameters → ℝ := fun T => Cgf T.L + CH + Cr * T.E * Sf T.decayRate
  let Y : StepParameters → ℝ := fun T =>
    max (16 * Mrow T / T.chainParams.lam) (4 * (Msl T + 1) ^ 2 / T.chainParams.lam)
  have hfloor : EventuallyInParameters fun T => Y T ≤ T.coupling := by
    intro a _
    exact ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
      ⟨0, fun nss _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ =>
        ⟨0, fun CE _ => ⟨Y ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, n₀, CE, 0⟩,
          fun y₁ hy => hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hFr hfloor)
  rintro T hT ⟨hfr, hY⟩
  intro t x f F V w ν hx hrow hF hp hν0 hν1
  obtain ⟨Cf, C, _, _, _, _, hL40, hn64, hκ1, hσ1, _, _, _, hy1, hay, _⟩ := hfr
  have hOdd : Odd T.L := hT.odd_L
  have hκ0 : 0 < T.κ := hT.κ_pos
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hρ0 : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hδ0 : 0 < T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  have hE0 : 0 ≤ T.E := by linarith [hT.one_le_E]
  have hlam : 0 < T.chainParams.lam := hT.chain_admissible.positivity.2.2.1
  have ha0 : 0 < T.a := by linarith [hT.one_le_a]
  have hx1 : 1 ≤ x := hy1.trans hx
  have hx0 : 0 < x := by linarith
  have hA : 2 ≤ T.a * x := hay.trans (mul_le_mul_of_nonneg_left hx ha0.le)
  obtain ⟨hFL, hFt, n, hside, hn⟩ := hF
  have hn0 : 0 < n := by omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside]; exact hn0
  have hLpos : 0 < T.L := hOdd.pos
  have hLr : (0 : ℝ) < T.L := by exact_mod_cast hLpos
  have hlow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨hFL, hFt, n, hside, hn.trans (Nat.le_mul_of_pos_right n hLpos)⟩
  have hOddF : Odd F.blockSide := hFL ▸ hOdd
  have hsz : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ∀ b ∈ chordBonds (finiteCells F), ‖shiftedCoordinates w η b.1 b.2‖ ≤ 1 := by
    intro η hη b hb
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).1 b.1 b.2
    have h2 := hp.small b hb
    have h3 : 1 / (64 * (T.L : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast hLpos
      linarith
    calc ‖shiftedCoordinates w η b.1 b.2‖ ≤ ‖w b.1 b.2‖ + ‖stepCoordinates η b.1 b.2‖ := norm_add_le _ _
      _ ≤ ‖w b.1 b.2‖ + T.ballRadius := by linarith
      _ ≤ 1 := h2.trans h3
  have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (chartedField (shiftedCoordinates w η) V) := by
    intro η hη p hp'
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).2.1 p
    have h2 := hp.curvature_small p hp'
    have h3 : T.ballRadius = T.σ / 64 := rfl
    have h4 : plaquetteDefect (chartedField (shiftedCoordinates w η) V) p ≤
        plaquetteDefect (chartedField w V) p + 4 * T.ballRadius := h1
    linarith
  have hcon : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube T.L →
        ‖contourHolonomyDefect (chartedField (shiftedCoordinates w η) V) V c h π - 1‖ ≤ 1 / 2 := by
    intro η hη c h π hh
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).2.2 c h π (hFL ▸ hh)
    have h2 := hp.contour_near_one c h π hh
    rw [hFL] at h1
    have h4 : ‖contourHolonomyDefect (chartedField (shiftedCoordinates w η) V) V c h π - 1‖ ≤
        ‖contourHolonomyDefect (chartedField w V) V c h π - 1‖ + 5 * (T.L : ℝ) * T.ballRadius := h1
    linarith
  obtain ⟨hCg0, hGt⟩ := hCgf T.L hOdd
  set A : ℝ := T.a * x with hAd
  have Gt := fun η hη => hGt F V (shiftedCoordinates w η) A hFL hpos hA (hsz η hη) (hcon η hη)
  have Ht := fun η hη => hH F (shiftedCoordinates w η) (hsz η hη)
  have Rt := fun η hη => hR T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F V (shiftedCoordinates w η)
    hδ0.le hE0 hrow hlow (hsz η hη) (hcold η hη)
  set c₀ : ℝ := -(x * chartedEnergyAt T.a w V 0) with hc₀
  have hform : ∀ η, exponentMinusEnergy T.a x w f ν V η =
      c₀ + (-1) * readInChart (gapExcessSum A) w V η +
      (-1) * haarExcessSum w η + (-ν) * readInChart (centredExpansionSum f) w V η := by
    intro η
    unfold exponentMinusEnergy exponentInChart
    rw [hc₀]
    ring
  have hshift : ∀ η : StepVariable (finiteCells F),
      (fun ζ => exponentMinusEnergy T.a x w f ν V (η + ζ)) =
      fun ζ => c₀ + (-1) * readInChart (gapExcessSum A) (shiftedCoordinates w η) V ζ +
        (-1) * haarExcessSum (shiftedCoordinates w η) ζ +
        (-ν) * readInChart (centredExpansionSum f) (shiftedCoordinates w η) V ζ := by
    intro η
    funext ζ
    rw [hform, readInChart_add, readInChart_add, haarExcessSum_add]
  have hlin := fun (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ T.ballRadius)
      (u v : StepVariable (finiteCells F)) =>
    affineCombination_three_derivs c₀ (-1) (-1) (-ν) (Gt η hη).1 (Ht η hη).1 (Rt η hη).1 u v
  have hsymm : ∀ y z : F.Site F.depth, siteSupDist y z = siteSupDist z y :=
    fun y z => (hD.1 F F.depth y z y).2.1
  refine ⟨fun b b' => (if siteSupDist b.1.1 b'.1.1 ≤ 10 * T.L then Cgf T.L else 0) +
    (if b = b' then CH else 0) + Cr * T.E * expansionDecayKernel F T.decayRate b b', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b b'
    have h1 : 0 ≤ expansionDecayKernel F T.decayRate b b' := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    have h2 : 0 ≤ if siteSupDist b.1.1 b'.1.1 ≤ 10 * T.L then Cgf T.L else 0 := by
      split_ifs <;> linarith
    have h3 : 0 ≤ if b = b' then CH else 0 := by
      split_ifs <;> linarith
    positivity
  · intro b b'
    have h1 : expansionDecayKernel F T.decayRate b b' = expansionDecayKernel F T.decayRate b' b := by
      unfold expansionDecayKernel
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hsymm b.1.1 b'.1.1]
      congr 3
      ring
    simp only [h1, hsymm b.1.1 b'.1.1, eq_comm]
  · intro η hη
    apply contDiffAt_of_comp_add
    rw [hshift]
    exact (hlin η hη 0 0).1
  · intro η hη b b' e e'
    have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
    obtain ⟨_, _, hsec⟩ := hlin η hη' (bondVariation b e) (bondVariation b' e')
    have e1 : secondDerivAlong (exponentMinusEnergy T.a x w f ν V) η (bondVariation b e)
        (bondVariation b' e') =
        fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => exponentMinusEnergy T.a x w f ν V (η + ξ)) ζ
          (bondVariation b e)) 0 (bondVariation b' e') := (fderiv_fderiv_comp_add_apply _ η _ _).symm
    rw [e1, hshift, hsec]
    have g1 := ((Gt η hη').2 b b' e e').2
    have h1 := ((Ht η hη').2 b b' e e').2
    have r1 := ((Rt η hη').2 b b' e e').2
    have hν : |ν| ≤ 1 := by
      rw [abs_of_nonneg hν0]
      exact hν1
    set X₁ := fderiv ℝ (fun ζ => fderiv ℝ (readInChart (gapExcessSum A) (shiftedCoordinates w η) V) ζ
      (bondVariation b e)) 0 (bondVariation b' e') with hX₁
    set X₂ := fderiv ℝ (fun ζ => fderiv ℝ (haarExcessSum (shiftedCoordinates w η)) ζ
      (bondVariation b e)) 0 (bondVariation b' e') with hX₂
    set X₃ := fderiv ℝ (fun ζ => fderiv ℝ (readInChart (centredExpansionSum f) (shiftedCoordinates w η) V) ζ
      (bondVariation b e)) 0 (bondVariation b' e') with hX₃
    have hr0 : 0 ≤ Cr * T.E * expansionDecayKernel F T.decayRate b b' * ‖e‖ * ‖e'‖ := by
      have : 0 ≤ expansionDecayKernel F T.decayRate b b' := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
      positivity
    have hνX : |(-ν) * X₃| ≤ Cr * T.E * expansionDecayKernel F T.decayRate b b' * ‖e‖ * ‖e'‖ := by
      rw [abs_mul, abs_neg]
      calc |ν| * |X₃| ≤ 1 * |X₃| := mul_le_mul_of_nonneg_right hν (abs_nonneg _)
        _ = |X₃| := one_mul _
        _ ≤ _ := r1
    calc |(-1) * X₁ + (-1) * X₂ + (-ν) * X₃| ≤ |(-1) * X₁| + |(-1) * X₂| + |(-ν) * X₃| :=
          abs_add_three _ _ _
      _ = |X₁| + |X₂| + |(-ν) * X₃| := by simp
      _ ≤ _ := by
          have : ((if siteSupDist b.1.1 b'.1.1 ≤ 10 * T.L then Cgf T.L else 0) +
              (if b = b' then CH else 0) + Cr * T.E * expansionDecayKernel F T.decayRate b b') * ‖e‖ * ‖e'‖ =
              (if siteSupDist b.1.1 b'.1.1 ≤ 10 * T.L then Cgf T.L else 0) * ‖e‖ * ‖e'‖ +
              (if b = b' then CH else 0) * ‖e‖ * ‖e'‖ +
              Cr * T.E * expansionDecayKernel F T.decayRate b b' * ‖e‖ * ‖e'‖ := by ring
          rw [this]
          linarith
  · intro b
    have hS1 := (hSf 1 one_pos).2
    have hS3 := (hSf (T.decayRate / 3) (by positivity))
    have h1 := kernel_row_sum_le (L := T.L) (κ := T.κ) (δ := T.decayRate) (Cg := Cgf T.L) (CH := CH)
      (Cr := Cr) (E := T.E) (S1 := Sf 1) (S3 := Sf (T.decayRate / 3)) hD hOddF hFL hpos hL40 hκ0 hκ1
      rfl hCg0.le hCH.le hCr.le hE0
      (fun z A' => hS1 F F.depth z A') (fun z A' => hS3.2 F F.depth z A') hS3.1.le b
    refine h1.trans ?_
    have h2 : 16 * Mrow T / T.chainParams.lam ≤ x := ((le_max_left _ _).trans hY).trans hx
    rw [div_le_iff₀ hlam] at h2
    change Mrow T ≤ _
    linarith
  · intro η h0 b e
    obtain ⟨_, hfst, _⟩ := hlin η h0 (bondVariation b e) (bondVariation b e)
    have e1 : bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e =
        fderiv ℝ (fun ζ => exponentMinusEnergy T.a x w f ν V (η + ζ)) 0 (bondVariation b e) := by
      rw [fderiv_comp_add_apply]
      rfl
    rw [e1, hshift, hfst]
    have g1 := ((Gt η h0).2 b b e e).1
    have h1 := ((Ht η h0).2 b b e e).1
    have r1 := ((Rt η h0).2 b b e e).1
    have hν : |ν| ≤ 1 := by
      rw [abs_of_nonneg hν0]
      exact hν1
    have hsum : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        Real.exp (-(T.decayRate * (siteSupDist y b.1.1 : ℝ))) ≤ Sf T.decayRate := by
      have := (hSf T.decayRate hδ0).2 F F.depth b.1.1 (sitesOfCells (finiteCells F) F.depth)
      simpa only [hsymm b.1.1] using this
    have hr1 : |fderiv ℝ (readInChart (centredExpansionSum f) (shiftedCoordinates w η) V) 0 (bondVariation b e)| ≤
        Cr * T.E * Sf T.decayRate * ‖e‖ := by
      refine r1.trans ?_
      have : 0 ≤ Cr * T.E := by positivity
      gcongr
    have hsl : Msl T + 1 ≤ Real.sqrt (x * T.chainParams.lam / 4) := by
      have h2 : 4 * (Msl T + 1) ^ 2 / T.chainParams.lam ≤ x := ((le_max_right _ _).trans hY).trans hx
      rw [div_le_iff₀ hlam] at h2
      apply Real.le_sqrt_of_sq_le
      linarith
    have hne := norm_nonneg e
    set X₁ := fderiv ℝ (readInChart (gapExcessSum A) (shiftedCoordinates w η) V) 0 (bondVariation b e)
    set X₂ := fderiv ℝ (haarExcessSum (shiftedCoordinates w η)) 0 (bondVariation b e)
    set X₃ := fderiv ℝ (readInChart (centredExpansionSum f) (shiftedCoordinates w η) V) 0 (bondVariation b e)
    have hνX : |(-ν) * X₃| ≤ Cr * T.E * Sf T.decayRate * ‖e‖ := by
      rw [abs_mul, abs_neg]
      calc |ν| * |X₃| ≤ 1 * |X₃| := mul_le_mul_of_nonneg_right hν (abs_nonneg _)
        _ = |X₃| := one_mul _
        _ ≤ _ := hr1
    calc |(-1) * X₁ + (-1) * X₂ + (-ν) * X₃| ≤ |(-1) * X₁| + |(-1) * X₂| + |(-ν) * X₃| :=
          abs_add_three _ _ _
      _ = |X₁| + |X₂| + |(-ν) * X₃| := by simp
      _ ≤ Msl T * ‖e‖ := by
          change _ ≤ (Cgf T.L + CH + Cr * T.E * Sf T.decayRate) * ‖e‖
          nlinarith
      _ ≤ _ := by
          have : Msl T ≤ Real.sqrt (x * T.chainParams.lam / 4) - 1 := by linarith
          exact mul_le_mul_of_nonneg_right this hne
end RemainderExponent
end ColdStepAtMirrorFrames
end YangMills.Construction
end
