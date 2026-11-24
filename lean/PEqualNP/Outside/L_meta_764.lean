import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

open PEqualNP.MetaComplexity

def majority (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

def edgeFunction (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

lemma edgeFunction_eq : edgeFunction = fun x : Fin (2 + 3) → Bool =>
    (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || majority (fun j => x (Fin.natAdd 2 j)) := by
  funext x
  change ((x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
    ((x 0 && x 1) || ((x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)))
  simp only [Bool.or_assoc]

lemma relax_budget {s t : ℕ} (h : HasCircuitSize 5 edgeFunction s) (hst : s ≤ t) :
    HasCircuitSize 5 edgeFunction t := by
  obtain ⟨C, hC, hsize, heval⟩ := h
  exact ⟨C, hC, hsize.trans hst, heval⟩

-- The triangle computes majority. The disjoint edge adds the two
-- fresh inputs required by the rigid AND theorem.
lemma exact_budget (s : ℕ) : HasCircuitSize 5 edgeFunction s ↔ 6 ≤ s := by
  have hnonconstant : ∃ y y' : Fin 3 → Bool, majority y ≠ majority y' :=
    ⟨fun _ => false, fun _ => true, by decide⟩
  have split (t : ℕ) : HasCircuitSize 5 edgeFunction (t + 2) ↔ HasCircuitSize 3 majority t := by
    rw [edgeFunction_eq]
    exact L153 3 t majority hnonconstant
  constructor
  · intro h
    by_contra! hs
    have hmaj := (split 3).mp (relax_budget h (by omega))
    have h4 := (L100 3).mp hmaj
    omega
  · intro hs
    have hmaj : HasCircuitSize 3 majority 4 := (L100 4).mpr (by decide)
    exact relax_budget ((split 4).mpr hmaj) hs

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔
      6 ≤ s :=
  PEqualNP.Outside.L_meta_764.exact_budget
