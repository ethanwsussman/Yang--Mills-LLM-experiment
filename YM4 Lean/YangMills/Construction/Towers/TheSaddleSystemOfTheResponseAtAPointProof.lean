import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.Towers.TheResponseOperators
import YangMills.Construction.Towers.TheSaddleSystemOfTheResponse
import YangMills.Construction.Towers.TheSaddleSystemOfTheResponseAtAPoint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseSaddleSystem
open PeriodicOperators
open BackgroundFieldResponse (responseKernel responseDefect)
open FreeResolvents (trivialRescaledOperators)
open ResponseProperties (InFundamentalStrip responseSymbolForm defectSymbol)
open FreeStrip (halfSupRate)
theorem symbolHom_idKernel_eq_id (hStrip : StripSymbols.Claim) (hNorm : HomNorm.Claim)
    {I : PeriodicData} (hIper : IsPeriodic I) (q : Fin 4 → ℂ) :
    symbolHom I I (idKernel I) q = LinearMap.id := by
  have hq : symbolHom I I (idKernel I) q = linearMapOfEntries (quotSymbol I I (idKernel I) q) :=
    rfl
  rw [hq, ((hStrip.2.1 I I hIper hIper).1.identity q).2]
  exact (hNorm I I hIper hIper).2.2.2.2.2.2.2.1.1
theorem saddle_equations_at_level (hTower : TowerIndexSets.Claim) (hStrip : StripSymbols.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic) (hNorm : HomNorm.Claim)
    (hSad : ResponseSaddle.SaddleEquations) {δ₀ : ℝ} {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hResp : ResponseOperators.AtLevel δ₀ L k)
    {q : Fin 4 → ℂ} (hq : InFundamentalStrip δ₀ q) (ε : (colourEdges L k k).UnitQuot → ℂ) :
    symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X q
        (responseSymbolForm L k q ε) =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt q
        (defectSymbol L k q ε) ∧
    symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q q
        (responseSymbolForm L k q ε) = ε := by
  obtain ⟨-, perBase, -⟩ := hTower L hL k 0 (Nat.zero_le k)
  obtain ⟨-, perTop, -⟩ := hTower L hL k k le_rfl
  obtain ⟨hMaps, hOps⟩ := hFree.2 L hL k hk
  obtain ⟨U, -, hU, hOnU⟩ := hResp.near
  have hqU : q ∈ U := hU hq.1
  have calc' := fun {I I' : PeriodicData} (a : IsPeriodic I) (b : IsPeriodic I') =>
    (hStrip.2.1 I I' a b).2.1
  have kerQ : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k k)
      (trivialRescaledOperators L k).Q :=
    hMaps.edgeAverage.finite_range.1
  have kerQt : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0)
      (trivialRescaledOperators L k).Qt :=
    hOps.edgeAverage_transpose.1
  have kerX : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).X :=
    hOps.X.1
  have sumX : SymbolSummableAt (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).X q :=
    (hStrip.2.1 _ _ perBase perBase).1.finiteRange _ kerX hOps.X.2.1 q (mem_univ q)
  have sumQ : SymbolSummableAt (colourEdges L k 0) (colourEdges L k k)
      (trivialRescaledOperators L k).Q q :=
    hResp.free_summable.avg q (mem_univ q)
  have sumQt : SymbolSummableAt (colourEdges L k k) (colourEdges L k 0)
      (trivialRescaledOperators L k).Qt q :=
    hResp.free_summable.avg_transpose q (mem_univ q)
  have sumH : SymbolSummableAt (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) q :=
    hOnU.resp_summable q hqU
  have sumN : SymbolSummableAt (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) q := hOnU.defect_summable q hqU
  obtain ⟨-, -, -, compQ⟩ := (calc' perBase perTop _ q kerQ sumQ).comp _ perTop _ hResp.resp_periodic sumH
  obtain ⟨-, -, -, compX⟩ := (calc' perBase perBase _ q kerX sumX).comp _ perTop _ hResp.resp_periodic sumH
  obtain ⟨-, -, -, compN⟩ := (calc' perTop perBase _ q kerQt sumQt).comp _ perTop _ hResp.defect_periodic sumN
  have hEq := hSad L hL k hk
  constructor
  · have h₁ := LinearMap.congr_fun (compX.symm.trans ((congrArg (fun T => symbolHom (colourEdges L k k)
      (colourEdges L k 0) T q) hEq.hessian_eq).trans compN)) ε
    exact h₁
  · have h₂ := LinearMap.congr_fun (compQ.symm.trans ((congrArg (fun T => symbolHom (colourEdges L k k)
      (colourEdges L k k) T q) hEq.smoothing_eq).trans (symbolHom_idKernel_eq_id hStrip hNorm perTop q))) ε
    exact h₂
theorem claim_holds (hTower : TowerIndexSets.Claim) (hStrip : StripSymbols.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic) (hNorm : HomNorm.Claim)
    (hSad : ResponseSaddle.SaddleEquations) (hResp : ResponseOperators.Claim) : Claim := by
  obtain ⟨δ₁, hδ₁, hAll⟩ := hResp
  intro δ₀ hδ L hL k hk q hq ε
  obtain rfl : δ₀ = δ₁ := Part.mem_unique hδ hδ₁
  exact saddle_equations_at_level hTower hStrip hFree hNorm hSad hL hk (hAll L hL k hk) hq ε
end YangMills.Construction.Tower.ResponseSaddleSystem
end
