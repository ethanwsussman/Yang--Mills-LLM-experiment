import YangMills.Construction.PeriodicOperators.CoefficientsHaveSupportOfEntries
import YangMills.Construction.PeriodicOperators.ComponentsOfAJetWithBoundedRows
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.SymbolOfAKernelWithBoundedRows
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BoundedExpansionJets
open YangMills.Construction.Tower.SmoothingContraction (OpNormLE)
open OpFunKernels (IsComponentKernel)
open BoundedExpansionSymbol (RowsBounded)
open CauchyTaylorBounds (IsFieldNorm BoundedOnBall)
theorem phaseField_eq_smul_blochWave (F : PeriodicData) (q : Fin 4 → ℂ) (ε : F.UnitQuot → ℂ)
    (y : YangMills.Construction.InfiniteLattice.AmbientSpace) :
    phaseField F q ε y =
      Complex.exp (-(Complex.I * bilinDot q (toComplexVec y))) • blochWave F q ε := by
  funext k
  simp only [phaseField, blochWave, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  have h : bilinDot q (toComplexVec (F.pos k - y)) =
      bilinDot q (toComplexVec (F.pos k)) - bilinDot q (toComplexVec y) := by
    simp only [bilinDot, toComplexVec, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  rw [h]
  ring
theorem opNormLE_mono {I J : PeriodicData} {T : J.Carrier → I.Carrier → ℂ} {c c' : ℝ}
    (h : OpNormLE I J T c) (hc : c ≤ c') : OpNormLE I J T c' :=
  ⟨h.1, h.2.1, h.2.2.trans (ENNReal.ofReal_le_ofReal hc)⟩
section Components
variable {F I J : PeriodicData} {T : (F.Carrier → ℂ) → J.Carrier → I.Carrier → ℂ}
  {N : (F.Carrier → ℂ) → ℝ≥0∞} {ρ C : ℝ} {A : J.Carrier → Set F.Carrier} {B : J.Carrier → Set I.Carrier}
  {s r : ℝ} {m : ℕ}
theorem coeffOne_component_bound (hloc : CoeffLocality.Claim)
    (hcauchy : CauchyTaylorBounds.CoeffBounds)
    (hsym : BoundedExpansionSymbol.SymbolNormBound)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hJ : IsPeriodic J)
    (hT : IsLocalOpFun F I J T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hN : IsFieldNorm F N)
    (hb : BoundedOnBall F I J T N ρ C) (hs : 0 < s) (hr : 0 ≤ r)
    (hrows : RowLocalized F I J T A B s r m) (q : Fin 4 → ℂ) (ε : F.UnitQuot → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hcut : ∀ j, N ((A j).indicator (phaseField F q ε (J.pos j))) ≤ ENNReal.ofReal M)
    {X : (Fin 4 → ℂ) → QuotHom I J}
    (hX : IsComponentKernel I J q (coeffOne F I J T (blochWave F q ε)) X)
    (κ : Fin 4 → ℂ) :
    quotHomNorm (X κ) ≤
      ENNReal.ofReal (Real.sqrt m * (C * ρ⁻¹ * M) * Real.exp (r * ∑ μ, |(κ μ).im|)) := by
  obtain ⟨-, hZ, rfl⟩ := hX
  have hrow : ∀ j i,
      dephasedKernel I J q (coeffOne F I J T (blochWave F q ε)) j i =
        coeffOne F I J T ((A j).indicator (phaseField F q ε (J.pos j))) j i := by
    intro j i
    obtain ⟨h1, -, h3, -⟩ := hloc F I J hF hI hJ T hT j i
    rw [dephasedKernel, ← h3, ← phaseField_eq_smul_blochWave]
    exact (h1 s (A j) hs (fun ζ ζ' hζ hζ' he => hrows.eq_of_eqOn j i ζ ζ' hζ hζ' he)).1 _ _
      (fun x hx => (indicator_of_mem hx _).symm)
  have hβ : 0 ≤ C * ρ⁻¹ * M := by positivity
  have hbdd : RowsBounded I J
      (dephasedKernel I J q (coeffOne F I J T (blochWave F q ε))) B
      (fun j => coeffOne F I J T
        ((A j).indicator (phaseField F q ε (J.pos j))))
      (C * ρ⁻¹ * M) r m :=
    { support_finite := hrows.finite_support
      eq_zero_of_not_mem := fun j i hi => by
        rw [hrow]
        obtain ⟨-, h2, -, -⟩ := hloc F I J hF hI hJ T hT j i
        exact (h2 s hs (fun ζ hζ => hrows.eq_zero_of_not_mem j i hi ζ hζ) _ 0).1
      expansion_eq := fun j i _ => hrow j i
      opNorm_le := fun j => by
        have hfin := (hcut j).trans_lt ENNReal.ofReal_lt_top
        refine opNormLE_mono
          (hcauchy F I J hF hI hJ T hT N ρ C hρ hC hN hb _ _ hfin hfin).1 ?_
        exact mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hM (hcut j))
          (by positivity)
      dist_le := hrows.pos_near
      encard_le := hrows.encard_le }
  exact hsym I J hI hJ _ hZ B _ _ r m hβ hr hbdd κ
theorem coeffTwo_component_bound (hloc : CoeffLocality.Claim)
    (hcauchy : CauchyTaylorBounds.CoeffBounds)
    (hsym : BoundedExpansionSymbol.SymbolNormBound)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hJ : IsPeriodic J)
    (hT : IsLocalOpFun F I J T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hN : IsFieldNorm F N)
    (hb : BoundedOnBall F I J T N ρ C) (hs : 0 < s) (hr : 0 ≤ r)
    (hrows : RowLocalized F I J T A B s r m) (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ) {M : ℝ}
    (hM : 0 ≤ M)
    (hcutp : ∀ j, N ((A j).indicator (phaseField F p εp (J.pos j))) ≤ ENNReal.ofReal M)
    (hcutm : ∀ j, N ((A j).indicator (phaseField F (-p) εm (J.pos j))) ≤
      ENNReal.ofReal M)
    {X : (Fin 4 → ℂ) → QuotHom I J}
    (hX : IsComponentKernel I J 0
      (coeffTwo F I J T (blochWave F p εp) (blochWave F (-p) εm)) X)
    (κ : Fin 4 → ℂ) :
    quotHomNorm (X κ) ≤ ENNReal.ofReal
      (Real.sqrt m * (4 * C * ρ⁻¹ ^ 2 * M * M) * Real.exp (r * ∑ μ, |(κ μ).im|)) := by
  obtain ⟨-, hZ, rfl⟩ := hX
  have hrow : ∀ j i,
      dephasedKernel I J 0
          (coeffTwo F I J T (blochWave F p εp) (blochWave F (-p) εm)) j i =
        coeffTwo F I J T ((A j).indicator (phaseField F p εp (J.pos j)))
          ((A j).indicator (phaseField F (-p) εm (J.pos j))) j i := by
    intro j i
    obtain ⟨h1, -, -, h4⟩ := hloc F I J hF hI hJ T hT j i
    have hone : Complex.exp (-(Complex.I * bilinDot p (toComplexVec (J.pos j)))) *
        Complex.exp (-(Complex.I * bilinDot (-p) (toComplexVec (J.pos j)))) = 1 := by
      rw [← Complex.exp_add]
      have : bilinDot (-p) (toComplexVec (J.pos j)) =
          -bilinDot p (toComplexVec (J.pos j)) := by simp [bilinDot]
      rw [this]
      simp
    have hzero : bilinDot (0 : Fin 4 → ℂ) (toComplexVec (J.pos j)) = 0 := by simp [bilinDot]
    have hsec := h4 (Complex.exp (-(Complex.I * bilinDot p (toComplexVec (J.pos j)))))
      (Complex.exp (-(Complex.I * bilinDot (-p) (toComplexVec (J.pos j)))))
      (blochWave F p εp) (blochWave F (-p) εm)
    rw [hone, one_mul, ← phaseField_eq_smul_blochWave, ← phaseField_eq_smul_blochWave] at hsec
    rw [dephasedKernel, hzero]
    simp only [mul_zero, neg_zero, Complex.exp_zero, one_mul]
    rw [← hsec]
    exact (h1 s (A j) hs (fun ζ ζ' hζ hζ' he => hrows.eq_of_eqOn j i ζ ζ' hζ hζ' he)).2 _ _ _ _
      (fun x hx => (indicator_of_mem hx _).symm) (fun x hx => (indicator_of_mem hx _).symm)
  have hβ : 0 ≤ 4 * C * ρ⁻¹ ^ 2 * M * M := by positivity
  have hbdd : RowsBounded I J
      (dephasedKernel I J 0
        (coeffTwo F I J T (blochWave F p εp) (blochWave F (-p) εm))) B
      (fun j => coeffTwo F I J T
        ((A j).indicator (phaseField F p εp (J.pos j)))
        ((A j).indicator (phaseField F (-p) εm (J.pos j))))
      (4 * C * ρ⁻¹ ^ 2 * M * M) r m :=
    { support_finite := hrows.finite_support
      eq_zero_of_not_mem := fun j i hi => by
        rw [hrow]
        obtain ⟨-, h2, -, -⟩ := hloc F I J hF hI hJ T hT j i
        exact (h2 s hs (fun ζ hζ => hrows.eq_zero_of_not_mem j i hi ζ hζ) _ _).2
      expansion_eq := fun j i _ => hrow j i
      opNorm_le := fun j => by
        have hfinp := (hcutp j).trans_lt ENNReal.ofReal_lt_top
        have hfinm := (hcutm j).trans_lt ENNReal.ofReal_lt_top
        refine opNormLE_mono
          (hcauchy F I J hF hI hJ T hT N ρ C hρ hC hN hb _ _ hfinp hfinm).2 ?_
        have hp := ENNReal.toReal_le_of_le_ofReal hM (hcutp j)
        have hm := ENNReal.toReal_le_of_le_ofReal hM (hcutm j)
        have hc : 0 ≤ 4 * C * ρ⁻¹ ^ 2 := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp hc) hm ENNReal.toReal_nonneg
          (mul_nonneg hc hM)
      dist_le := hrows.pos_near
      encard_le := hrows.encard_le }
  exact hsym I J hI hJ _ hZ B _ _ r m hβ hr hbdd κ
end Components
theorem componentBounds_holds (hloc : CoeffLocality.Claim)
    (hcauchy : CauchyTaylorBounds.CoeffBounds)
    (hsym : BoundedExpansionSymbol.SymbolNormBound)
    (hker : OpFunKernels.Claim) : ComponentBounds := by
  intro F I J hF hI hJ T hT N ρ C hρ hC hN hb A B s r m hs hr hrows p εp εm M hM hp hm κ
  obtain ⟨-, h10, h01, h11⟩ := (hker F I J hF hI hJ T hT).2 p εp εm
  exact ⟨coeffOne_component_bound hloc hcauchy hsym hF hI hJ hT hρ hC hN hb hs hr hrows p εp hM hp
      h10 κ,
    coeffOne_component_bound hloc hcauchy hsym hF hI hJ hT hρ hC hN hb hs hr hrows (-p) εm hM hm
      h01 κ,
    coeffTwo_component_bound hloc hcauchy hsym hF hI hJ hT hρ hC hN hb hs hr hrows p εp εm hM
      hp hm h11 κ⟩
end YangMills.Construction.PeriodicOperators.BoundedExpansionJets
end
