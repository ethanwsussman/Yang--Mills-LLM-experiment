import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbols
import YangMills.Construction.Towers.BoundsOfTheSandwichesOfTheFreeOperators
import YangMills.Construction.Towers.BoundsOfTheSymbolsOfTheAverages
import YangMills.Construction.Towers.TheRootsOfTheFreePropagatorsOnTheStrip
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.SandwichBounds
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open FreeResolvents
section Matrices
variable (hn : HomNorm.Claim)
include hn
theorem quotHomNorm_comp_le {I I' I'' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'') (M : QuotHom I I')
    (M'' : QuotHom I'' I) : quotHomNorm (M.comp M'') ≤ quotHomNorm M * quotHomNorm M'' :=
  ((hn I I' hI hI').2.2.2.2.2.2.1 I'' hI'').2 M M''
theorem quotHomNorm_add_le {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (M M' : QuotHom I I') : quotHomNorm (M + M') ≤ quotHomNorm M + quotHomNorm M' :=
  (hn I I' hI hI').2.2.2.2.2.1.2.2.2.1 M M'
theorem quotHomNorm_sub_le {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (M M' : QuotHom I I') : quotHomNorm (M - M') ≤ quotHomNorm M + quotHomNorm M' := by
  rw [((hn I I' hI hI').2.2.2.2.2.2.2.2 M M' 0).1]
  refine (quotHomNorm_add_le hn hI hI' _ _).trans ?_
  rw [(hn I I' hI hI').2.2.2.2.2.1.2.2.2.2 (-1) M']
  simp
omit hn in
theorem exp_two_eq_mul : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
  rw [← Real.exp_add]
  norm_num
omit hn in
theorem mul_four_le {a b c d : ENNReal} (ha : a ≤ ENNReal.ofReal 10)
    (hb : b ≤ ENNReal.ofReal (Real.exp 1))
    (hc : c ≤ ENNReal.ofReal (Real.exp 1)) (hd : d ≤ ENNReal.ofReal 10) :
    a * (b * (c * d)) ≤ ENNReal.ofReal (100 * Real.exp 2) := by
  have he := (Real.exp_pos 1).le
  calc a * (b * (c * d))
      ≤ ENNReal.ofReal 10 * (ENNReal.ofReal (Real.exp 1) *
          (ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal 10)) :=
        mul_le_mul' ha (mul_le_mul' hb (mul_le_mul' hc hd))
    _ = ENNReal.ofReal (100 * Real.exp 2) := by
        rw [← ENNReal.ofReal_mul he, ← ENNReal.ofReal_mul he, ← ENNReal.ofReal_mul (by norm_num),
          exp_two_eq_mul]
        congr 1
        ring
theorem sqrt_sandwich_bounds {I : PeriodicData} (hI : IsPeriodic I) {N K : QuotHom I I}
    (hN : quotHomNorm N ≤ ENNReal.ofReal 10)
    (hu : N.comp ((K + scalarQuotHom I 1).comp N) = LinearMap.id) :
    quotHomNorm (N.comp N) ≤ ENNReal.ofReal 100 ∧
      quotHomNorm (N.comp (K.comp N)) ≤ ENNReal.ofReal 101 := by
  have h₁ : quotHomNorm (N.comp N) ≤ ENNReal.ofReal 100 := by
    refine (quotHomNorm_comp_le hn hI hI hI N N).trans ?_
    calc quotHomNorm N * quotHomNorm N ≤ ENNReal.ofReal 10 * ENNReal.ofReal 10 :=
          mul_le_mul' hN hN
      _ = ENNReal.ofReal 100 := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  refine ⟨h₁, ?_⟩
  have e : N.comp (K.comp N) = LinearMap.id - N.comp N := by
    rw [← hu]
    refine LinearMap.ext fun f => ?_
    simp [scalarQuotHom]
  rw [e]
  refine (quotHomNorm_sub_le hn hI hI _ _).trans ?_
  calc quotHomNorm (LinearMap.id : QuotHom I I) + quotHomNorm (N.comp N)
      ≤ 1 + ENNReal.ofReal 100 := add_le_add (hn I I hI hI).2.2.2.2.2.2.2.1.2 h₁
    _ = ENNReal.ofReal 101 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
omit hn in
theorem ofReal_le_sandwichConstant {x : ℝ} (h : x ≤ 101 + 100 * Real.exp 2) :
    ENNReal.ofReal x ≤ ENNReal.ofReal sandwichConstant := by
  refine ENNReal.ofReal_le_ofReal (h.trans ?_)
  have := Real.exp_pos 2
  unfold sandwichConstant
  linarith
theorem sandwichNormsBounded_of_edge_formula {I S T B : PeriodicData} (hI : IsPeriodic I)
    (hS : IsPeriodic S) (hT : IsPeriodic T) (hB : IsPeriodic B) {N K X : QuotHom I I}
    {D : QuotHom S I} {Dt : QuotHom I S} {R : QuotHom S T} {Rt : QuotHom T S} {Q : QuotHom I B}
    {Qt : QuotHom B I} (hX : X = K - (D.comp Rt).comp (R.comp Dt) + Qt.comp Q)
    (hN : quotHomNorm N ≤ ENNReal.ofReal 10)
    (hu : N.comp ((K + scalarQuotHom I 1).comp N) = LinearMap.id)
    (hND : quotHomNorm (N.comp D) ≤ ENNReal.ofReal 10)
    (hDN : quotHomNorm (Dt.comp N) ≤ ENNReal.ofReal 10)
    (hR : quotHomNorm R ≤ ENNReal.ofReal (Real.exp 1))
    (hRt : quotHomNorm Rt ≤ ENNReal.ofReal (Real.exp 1))
    (hQ : quotHomNorm Q ≤ ENNReal.ofReal (Real.exp 1))
    (hQt : quotHomNorm Qt ≤ ENNReal.ofReal (Real.exp 1)) :
    SandwichNormsBounded N X K := by
  obtain ⟨h₁, h₂⟩ := sqrt_sandwich_bounds hn hI hN hu
  have he := Real.exp_pos 2
  refine ⟨?_, h₂.trans (ofReal_le_sandwichConstant (by linarith)),
    h₁.trans (ofReal_le_sandwichConstant (by linarith))⟩
  have e : N.comp (X.comp N) = N.comp (K.comp N) - (N.comp D).comp (Rt.comp (R.comp (Dt.comp N))) +
      N.comp (Qt.comp (Q.comp N)) := by
    subst hX
    refine LinearMap.ext fun f => ?_
    simp
  have t₁ : quotHomNorm ((N.comp D).comp (Rt.comp (R.comp (Dt.comp N)))) ≤
      ENNReal.ofReal (100 * Real.exp 2) := by
    refine (quotHomNorm_comp_le hn hS hI hI _ _).trans ?_
    refine (mul_le_mul' le_rfl ((quotHomNorm_comp_le hn hT hS hI _ _).trans
      (mul_le_mul' le_rfl (quotHomNorm_comp_le hn hS hT hI _ _)))).trans ?_
    exact mul_four_le hND hRt hR hDN
  have t₂ : quotHomNorm (N.comp (Qt.comp (Q.comp N))) ≤ ENNReal.ofReal (100 * Real.exp 2) := by
    refine (quotHomNorm_comp_le hn hI hI hI _ _).trans ?_
    refine (mul_le_mul' le_rfl ((quotHomNorm_comp_le hn hB hI hI _ _).trans
      (mul_le_mul' le_rfl (quotHomNorm_comp_le hn hI hB hI _ _)))).trans ?_
    exact mul_four_le hN hQt hQ hN
  rw [e]
  refine (quotHomNorm_add_le hn hI hI _ _).trans ?_
  refine (add_le_add (quotHomNorm_sub_le hn hI hI _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add h₂ t₁) t₂).trans ?_
  have n₁ : (0 : ℝ) ≤ 100 * Real.exp 2 := by positivity
  rw [← ENNReal.ofReal_add (by norm_num) n₁, ← ENNReal.ofReal_add (by positivity) n₁]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold sandwichConstant
  linarith
theorem sandwichNormsBounded_of_vertex_formula {I T : PeriodicData} (hI : IsPeriodic I)
    (hT : IsPeriodic T) {N K X : QuotHom I I} {R : QuotHom I T} {Rt : QuotHom T I}
    (hX : X = K + Rt.comp R)
    (hN : quotHomNorm N ≤ ENNReal.ofReal 10)
    (hu : N.comp ((K + scalarQuotHom I 1).comp N) = LinearMap.id)
    (hR : quotHomNorm R ≤ ENNReal.ofReal (Real.exp 1))
    (hRt : quotHomNorm Rt ≤ ENNReal.ofReal (Real.exp 1)) :
    SandwichNormsBounded N X K := by
  obtain ⟨h₁, h₂⟩ := sqrt_sandwich_bounds hn hI hN hu
  have he := Real.exp_pos 2
  refine ⟨?_, h₂.trans (ofReal_le_sandwichConstant (by linarith)),
    h₁.trans (ofReal_le_sandwichConstant (by linarith))⟩
  have e : N.comp (X.comp N) = N.comp (K.comp N) + N.comp (Rt.comp (R.comp N)) := by
    subst hX
    refine LinearMap.ext fun f => ?_
    simp
  have t : quotHomNorm (N.comp (Rt.comp (R.comp N))) ≤ ENNReal.ofReal (100 * Real.exp 2) := by
    refine (quotHomNorm_comp_le hn hI hI hI _ _).trans ?_
    refine (mul_le_mul' le_rfl ((quotHomNorm_comp_le hn hT hI hI _ _).trans
      (mul_le_mul' le_rfl (quotHomNorm_comp_le hn hI hT hI _ _)))).trans ?_
    exact mul_four_le hN hRt hR hN
  rw [e]
  refine (quotHomNorm_add_le hn hI hI _ _).trans ?_
  refine (add_le_add h₂ t).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
  exact ofReal_le_sandwichConstant (by linarith)
end Matrices
section Symbols
variable (hs : StripSymbols.Claim)
include hs
theorem symbolHom_compKernel {I I' I'' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  (((hs.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS).2
theorem symbolHom_linCombKernel {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T T' : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hT' : IsPeriodicKernel I I' T') {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fT' : SymbolSummableAt I I' T' κ) (c c' : ℂ) :
    IsPeriodicKernel I I' (StripSymbols.linCombKernel c c' T T') ∧
      SymbolSummableAt I I' (StripSymbols.linCombKernel c c' T T') κ ∧
      symbolHom I I' (StripSymbols.linCombKernel c c' T T') κ =
        c • symbolHom I I' T κ + c' • symbolHom I I' T' κ :=
  ((hs.2.1 I I' hI hI').2.1 T κ hT fT).linComb T' hT' fT' c c'
end Symbols
theorem freeSandwichBounds_holds (roots : ResolventRootsOnStrip.ResolventRootsHold)
    (diag : DiagonalSymbolBounds.DiagonalSymbolBoundsHold)
    (avg : SymbolBounds.FreeSymbolNormBounds)
    (hco : FreeCoercivity.FreeOperatorsCoercive)
    (hs : StripSymbols.Claim) (hn : HomNorm.Claim)
    (tis : TowerIndexSets.Claim) (hfree : FreeOperators.FreeOperatorsArePeriodic)
    (facts : RescaledConditions.Holds) : FreeSandwichBounds := by
  obtain ⟨cXi, -, cY, -, cC, -, hco⟩ := hco
  intro L hL k hk κ hκ
  obtain ⟨ops, -, -, -⟩ := hco L hL k hk
  have rb := (roots L hL k hk).1
  have rs := (roots L hL k hk).2
  have db := diag L hL k hk κ hκ
  obtain ⟨aQ, aR, aQt, aRt⟩ := avg L hL k hk κ hκ
  have iS₀ := (tis L hL k 0 (Nat.zero_le k)).1
  have iB₀ := (tis L hL k 0 (Nat.zero_le k)).2.1
  have iS := (tis L hL k k le_rfl).1
  have iB := (tis L hL k k le_rfl).2.1
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (facts L hL k hk).2
  have eD : (trivialRescaledOperators L k).D = FullSpace.scaledVertexCoboundaryKernel L k 0 :=
    hOne.D_eq
  have eDt : (trivialRescaledOperators L k).Dt = kernelTranspose (colourVertices L k 0)
      (colourEdges L k 0) (FullSpace.scaledVertexCoboundaryKernel L k 0) := by
    rw [← eD]
    rfl
  have pd := ((hfree.2 L hL k hk).1.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have pdt := (hfree.2 L hL k hk).2.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have fd := (hs.2.1 _ _ iS₀ iB₀).1.finiteRange _ pd.1 pd.2.1 κ (mem_univ κ)
  have fdt := (hs.2.1 _ _ iB₀ iS₀).1.finiteRange _ pdt.1 pdt.2.1 κ (mem_univ κ)
  have fop : ∀ {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ},
      FreeCoercivity.IsFiniteRangeEntire I I' T →
        SymbolSummableAt I I' T κ := fun hT => hT.2.2 κ (mem_univ κ)
  refine ⟨?_, ?_⟩
  · have p₁ := symbolHom_compKernel hs iS₀ iB₀ iS pd.1 ops.Rt.1 fd (fop ops.Rt)
    have p₂ := symbolHom_compKernel hs iS₀ iS iB₀ ops.R.1 pdt.1 (fop ops.R) fdt
    have p₃ := symbolHom_compKernel hs iS iB₀ iB₀ p₁.1 p₂.1 p₁.2.1 p₂.2.1
    have p₄ := symbolHom_compKernel hs iB iB₀ iB₀ ops.Qt.1 ops.Q.1 (fop ops.Qt) (fop ops.Q)
    have c₁ := symbolHom_linCombKernel hs iB₀ iB₀ ops.K.1 p₃.1 (fop ops.K) p₃.2.1 1 (-1)
    have c₂ := symbolHom_linCombKernel hs iB₀ iB₀ c₁.1 p₄.1 c₁.2.1 p₄.2.1 1 1
    have eXi : (trivialRescaledOperators L k).Xi = StripSymbols.linCombKernel 1 1
        (StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).K
          (compKernel (compKernel (FullSpace.scaledVertexCoboundaryKernel L k 0)
              (trivialRescaledOperators L k).Rt)
            (compKernel (trivialRescaledOperators L k).R
              (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
                (FullSpace.scaledVertexCoboundaryKernel L k 0)))))
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) := by
      rw [← eDt, ← eD]
      funext ι' ι
      change (trivialRescaledOperators L k).K ι' ι - compKernel (compKernel
          (trivialRescaledOperators L k).D (trivialRescaledOperators L k).Rt)
        (compKernel (trivialRescaledOperators L k).R (trivialRescaledOperators L k).Dt) ι' ι +
        compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q ι' ι = _
      simp only [StripSymbols.linCombKernel]
      ring
    refine sandwichNormsBounded_of_edge_formula hn iB₀ iS₀ iS iB ?_ db.edgeSqrt_le
      (rb.sqrt_conj_add_one κ hκ) db.edgeSqrt_comp_coboundary_le
      db.coboundaryTranspose_comp_edgeSqrt_le aR aRt aQ aQt
    refine (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ) eXi).trans
      (c₂.2.2.trans ?_)
    rw [c₁.2.2, p₃.2.2, p₄.2.2, p₁.2.2, p₂.2.2]
    have hneg : ∀ M : QuotHom (colourEdges L k 0) (colourEdges L k 0), (-1 : ℂ) • M = -M :=
      fun M => neg_one_smul ℂ M
    simp only [one_smul, sub_eq_add_neg]
    rw [hneg]
  · have p₁ := symbolHom_compKernel hs iS iS₀ iS₀ ops.Rt.1 ops.R.1 (fop ops.Rt) (fop ops.R)
    have c₁ := symbolHom_linCombKernel hs iS₀ iS₀ ops.Delta.1 p₁.1 (fop ops.Delta) p₁.2.1 1 1
    have eY : (trivialRescaledOperators L k).Y = StripSymbols.linCombKernel 1 1
        (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) := by
      funext ι' ι
      change (trivialRescaledOperators L k).Delta ι' ι +
        compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R ι' ι = _
      simp only [StripSymbols.linCombKernel]
      ring
    refine sandwichNormsBounded_of_vertex_formula hn iS₀ iS ?_ db.vertexSqrt_le
      (rs.sqrt_conj_add_one κ hκ) aR aRt
    refine (congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T κ) eY).trans
      (c₁.2.2.trans ?_)
    rw [p₁.2.2]
    simp
end YangMills.Construction.Tower.SandwichBounds
end
