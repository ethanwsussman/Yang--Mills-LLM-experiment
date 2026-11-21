import YangMills.Construction.PositiveDefinite.KernelRestrictPullbackLimit
import YangMills.Construction.RotationInvariance.ConvexityOfTheTopFrequency
import YangMills.Construction.RotationInvariance.FinitelyManyHarmonicsOnPencils
import YangMills.Construction.RotationInvariance.GramKernelStaysPositiveAtImaginaryAngles
import YangMills.Construction.RotationInvariance.SectorPencilCutAtTheMirrorAndDoubledPencils
import YangMills.Construction.RotationInvariance.TopFrequencyRangeSumsAndRate
import Mathlib
set_option autoImplicit false
open Complex (I)
open Filter Topology
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MaxFrequencyConvex
theorem two_mul_le_add_of_rates {N N' N'' : ℕ} {f g h : ℝ → ℂ} {c L' L'' : ℂ} (hc : c ≠ 0)
    (hf : Tendsto (fun s : ℝ => ((Real.exp (-(4 * (N : ℝ) * s)) : ℝ) : ℂ) * f s) atTop (𝓝 c))
    (hg : Tendsto (fun s : ℝ => ((Real.exp (-(4 * (N' : ℝ) * s)) : ℝ) : ℂ) * g s) atTop (𝓝 L'))
    (hh : Tendsto (fun s : ℝ => ((Real.exp (-(4 * (N'' : ℝ) * s)) : ℝ) : ℂ) * h s) atTop (𝓝 L''))
    (hbound : ∀ s : ℝ, ‖f s‖ ^ 2 ≤ ‖g s * h s‖) : 2 * N ≤ N' + N'' := by
  by_contra hnot
  have hlt := not_le.1 hnot
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 2 * (N : ℝ) - N' - N'' := ⟨_, rfl⟩
  have hD : 0 < D := by
    have h1 : ((N' + N'' : ℕ) : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at h1
    linarith
  have hu := (hf.norm).pow 2
  have hv := (hg.mul hh).norm
  have he : Tendsto (fun s : ℝ => Real.exp (-(4 * D * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (4 * D) * s) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  have hw := he.mul hv
  rw [zero_mul] at hw
  have hle : ‖c‖ ^ 2 ≤ 0 := by
    refine le_of_tendsto_of_tendsto' hu hw fun s => ?_
    have hE : Real.exp (-(4 * (N : ℝ) * s)) * Real.exp (-(4 * (N : ℝ) * s)) =
        Real.exp (-(4 * D * s)) *
          (Real.exp (-(4 * (N' : ℝ) * s)) * Real.exp (-(4 * (N'' : ℝ) * s))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hDdef]
      congr 1
      ring
    have hpos := (Real.exp_pos (-(4 * (N : ℝ) * s))).le
    have hpos' := (Real.exp_pos (-(4 * (N' : ℝ) * s))).le
    have hpos'' := (Real.exp_pos (-(4 * (N'' : ℝ) * s))).le
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos,
      abs_of_nonneg hpos', abs_of_nonneg hpos'']
    have h2 := hbound s
    rw [norm_mul] at h2
    calc (Real.exp (-(4 * (N : ℝ) * s)) * ‖f s‖) ^ 2
        = (Real.exp (-(4 * (N : ℝ) * s)) * Real.exp (-(4 * (N : ℝ) * s))) * ‖f s‖ ^ 2 := by ring
      _ ≤ (Real.exp (-(4 * (N : ℝ) * s)) * Real.exp (-(4 * (N : ℝ) * s))) * (‖g s‖ * ‖h s‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by rw [hE]; ring
  have : 0 < ‖c‖ ^ 2 := by positivity
  linarith
theorem ofReal_le_imp_le_norm {r : ℝ} {w : ℂ} (h : (r : ℂ) ≤ w) : r ≤ ‖w‖ :=
  le_trans (by simpa using (Complex.le_def.1 h).1) (Complex.re_le_norm w)
theorem gram_cauchy_schwarz {S : ConnFamily} {s : ℝ}
    (hk : PositiveDefinite.KernelPosSemidefOnSet (gramKernelImag S s))
    (hPsd : PositiveDefinite.KernelRestrictPullback.RestrictPullbackScaleLimit)
    (X Z : ForwardTube.LabelledTuple) (A B C : ℂ) (hA : gramKernelImag S s X Z = A)
    (hB : gramKernelImag S s X X = B)
    (hC : gramKernelImag S s Z Z = C) : ‖A‖ ^ 2 ≤ ‖B * C‖ := by
  have hcs := ((hPsd ForwardTube.LabelledTuple).1 _ hk).2.1 X Z
  rw [hA, hB, hC] at hcs
  exact ofReal_le_imp_le_norm hcs
theorem two_mul_le_of_both_succ
    (hCut : MirrorCut.Holds)
    (hGram : GramKernelImagPosSemidef.Holds)
    (hHarm : PencilHarmonics.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hPsd : PositiveDefinite.KernelRestrictPullback.RestrictPullbackScaleLimit)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) (k l : ℕ) :
    2 * maxFrequency S d.angle (k + 1 + l + 1) ≤
      maxFrequency S d.angle (k + 1 + k + 1) + maxFrequency S d.angle (l + 1 + l + 1) := by
  by_cases h0 : maxFrequency S d.angle (k + 1 + l + 1) = 0
  · simp [h0]
  obtain ⟨-, hRate, hAtt⟩ := hTop m S d
  obtain ⟨y₀, hy₀, φ, hc⟩ := (hAtt _ (Nat.one_le_iff_ne_zero.2 h0)).2 (k + 1 + l) rfl
  have hq : 1 ≤ k + 1 + l := by omega
  obtain ⟨-, -, hTr, -, -⟩ := hHarm m S d (k + 1 + l) hq y₀ hy₀ φ
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin (k + 1 + (l + 1)), i = Fin.castAdd (l + 1) (Fin.last k) := ⟨_, rfl⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i : Fin (k + 1 + (l + 1)), i = Fin.natAdd (k + 1) 0 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : RealPlane, u = -((1 / 2 : ℝ) • (y₀ i₀ + y₀ i₁)) := ⟨_, rfl⟩
  obtain ⟨hy, hsame⟩ := hTr u
  obtain ⟨y, hydef⟩ : ∃ y : Fin (k + 1 + (l + 1)) → RealPlane, y = fun i => y₀ i + u :=
    ⟨_, rfl⟩
  have hmid : y (Fin.castAdd (l + 1) (Fin.last k)) + y (Fin.natAdd (k + 1) 0) = 0 := by
    rw [← hi₀, ← hi₁, hydef, hu]
    module
  have hyp : y ∈ RealPlane.pencilSet d.angle (k + 1 + (l + 1)) := by
    rw [hydef]
    exact hy
  have hcy : angleHarmonic S d.angle (q := k + 1 + l) y φ
      (-(maxFrequency S d.angle (k + 1 + l + 1) : ℤ)) ≠ 0 := by
    rw [hydef]
    intro hz
    exact hc ((hsame _).symm.trans hz)
  obtain ⟨-, -, hx, hz, -, -, hdx, hdz, hvals⟩ := (hCut m S d).2.1 k l y hyp hmid φ
  have r := (hRate (k + 1 + l) hq y hyp φ).2
  have r' := (hRate (k + 1 + k) (by omega)
    (ForwardTube.reflectAppend (n := k + 1) (n' := k + 1)
      (RealPlane.cutLowerPoints (k := k + 1) (l := l + 1) y)
      (RealPlane.cutLowerPoints (k := k + 1) (l := l + 1) y)) hdx.1
    (RealPlane.doubledLowerLabels (k := k + 1) (l := l + 1) φ)).2
  have r'' := (hRate (l + 1 + l) (by omega)
    (ForwardTube.reflectAppend (n := l + 1) (n' := l + 1)
      (RealPlane.cutUpperPoints (k := k + 1) (l := l + 1) y)
      (RealPlane.cutUpperPoints (k := k + 1) (l := l + 1) y)) hdz.1
    (RealPlane.doubledUpperLabels (k := k + 1) (l := l + 1) φ)).2
  refine two_mul_le_add_of_rates hcy r r' r'' fun s => ?_
  obtain ⟨e1, e2, e3, e4⟩ := hvals hx hz s
  exact gram_cauchy_schwarz ((hGram m S d).2 s).1 hPsd _ _ _ _ _ (e1.trans e2) e3 e4
theorem two_mul_le_of_single
    (hCut : MirrorCut.Holds)
    (hGram : GramKernelImagPosSemidef.Holds)
    (hHarm : PencilHarmonics.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hPsd : PositiveDefinite.KernelRestrictPullback.RestrictPullbackScaleLimit)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) (q : ℕ) (hq : 1 ≤ q) :
    2 * maxFrequency S d.angle (q + 1) ≤ maxFrequency S d.angle (q + 1 + q + 1) := by
  by_cases h0 : maxFrequency S d.angle (q + 1) = 0
  · simp [h0]
  obtain ⟨-, hRate, hAtt⟩ := hTop m S d
  obtain ⟨y₀, hy₀, φ, hc⟩ := (hAtt _ (Nat.one_le_iff_ne_zero.2 h0)).2 q rfl
  obtain ⟨-, -, hTr, -, -⟩ := hHarm m S d q hq y₀ hy₀ φ
  obtain ⟨u, hu⟩ : ∃ u : RealPlane, u = (!₂[1, 0] : RealPlane) - y₀ 0 := ⟨_, rfl⟩
  obtain ⟨hy, hsame⟩ := hTr u
  obtain ⟨y, hydef⟩ : ∃ y : Fin (q + 1) → RealPlane, y = fun i => y₀ i + u := ⟨_, rfl⟩
  obtain ⟨hA, -, hOne⟩ := hCut m S d
  have hsec : y 0 ∈ RealPlane.coneSector d.angle := by
    have h1 : y 0 = (!₂[1, 0] : RealPlane) := by
      rw [hydef, hu]
      simp
    rw [h1]
    obtain ⟨-, -, -, -, -, h2⟩ := hA
    exact h2 1 one_pos
  have hyp : y ∈ RealPlane.pencilSet d.angle (q + 1) := by
    rw [hydef]
    exact hy
  have hcy : angleHarmonic S d.angle y φ
      (-(maxFrequency S d.angle (q + 1) : ℤ)) ≠ 0 := by
    rw [hydef]
    intro hz
    exact hc ((hsame _).symm.trans hz)
  obtain ⟨hz, hd, hvals⟩ := hOne q hq y hyp hsec φ
  have r := (hRate q hq y hyp φ).2
  have r'' := (hRate (q + 1 + q) (by omega)
    (ForwardTube.reflectAppend (n := q + 1) (n' := q + 1) y y) hd (RealPlane.doubledLabels φ)).2
  have r' : Tendsto (fun s : ℝ => ((Real.exp (-(4 * ((0 : ℕ) : ℝ) * s)) : ℝ) : ℂ) * (fun _ => (1 : ℂ)) s)
      atTop (𝓝 1) := by
    simp
  have key := two_mul_le_add_of_rates hcy r r' r'' fun s => ?_
  · simpa using key
  obtain ⟨e1, e2, e3⟩ := hvals hz s
  exact gram_cauchy_schwarz ((hGram m S d).2 s).1 hPsd _ _ _ _ _ e2 e1 e3
theorem holds_of
    (hCut : MirrorCut.Holds)
    (hGram : GramKernelImagPosSemidef.Holds)
    (hHarm : PencilHarmonics.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hPsd : PositiveDefinite.KernelRestrictPullback.RestrictPullbackScaleLimit) :
    Holds := by
  intro m S d k l
  have one : ∀ n : ℕ, 2 * maxFrequency S d.angle n ≤ maxFrequency S d.angle (2 * n) := by
    intro n
    by_cases h0 : maxFrequency S d.angle n = 0
    · simp [h0]
    have h2 := ((hTop m S d).2.2 n (Nat.one_le_iff_ne_zero.2 h0)).1
    obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    have h3 := two_mul_le_of_single hCut hGram hHarm hTop hPsd d q (by omega)
    rwa [show q + 1 + q + 1 = 2 * (q + 1) by omega] at h3
  have hzero : maxFrequency S d.angle 0 = 0 := rfl
  rcases k with _ | k
  · have := one l
    simpa [hzero] using this
  rcases l with _ | l
  · have := one (k + 1)
    simpa [hzero] using this
  have h3 := two_mul_le_of_both_succ hCut hGram hHarm hTop hPsd d k l
  rw [show k + 1 + k + 1 = 2 * (k + 1) by omega, show l + 1 + l + 1 = 2 * (l + 1) by omega] at h3
  exact h3
end YangMills.Construction.EuclideanFunctionals.MaxFrequencyConvex
end
