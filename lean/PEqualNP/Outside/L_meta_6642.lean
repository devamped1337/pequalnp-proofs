import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


namespace PEqualNP.Outside.L_meta_6642_aux

private def replaceEmpty (cap : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | .or, [] => ⟨.and, [cap]⟩
  | _, _ => g

private def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]

private lemma replaceEmpty_step (cap : ℕ) (ws : List Bool) (g : Gate) (h : ws.length ≤ cap) :
    step ws (replaceEmpty cap g) = step ws g := by
  have getFalse : ws[cap]?.getD false = false := by
    simp [List.getElem?_eq_none h]
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> simp [replaceEmpty, step, GateOp.eval, getFalse]

private lemma fold_normalize (cap : ℕ) (gs : List Gate) (xs : List Bool)
    (h : xs.length + gs.length ≤ cap) :
    (gs.map (replaceEmpty cap)).foldl step xs = gs.foldl step xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [replaceEmpty_step cap xs g (by omega)]
    apply ih
    simp [step] at *
    omega

private lemma wire_length (D : Circuit) (xs : List Bool) :
    (D.wires xs).length = xs.length + D.gates.length := by
  change (D.gates.foldl step xs).length = _
  induction D.gates generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step] <;> omega

private lemma replaceEmpty_legal (cap : ℕ) (g : Gate)
    (legal : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (replaceEmpty cap g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (replaceEmpty cap g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> simpa [replaceEmpty] using legal

private lemma keep_or (cap : ℕ) (g : Gate) (h : (replaceEmpty cap g).op = .or) :
    g.op = .or ∧ replaceEmpty cap g = g ∧ g.inputs ≠ [] := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> simp_all [replaceEmpty]

private lemma replaceEmpty_copy (cap i : ℕ) : replaceEmpty cap ⟨GateOp.and, [i]⟩ = ⟨.and, [i]⟩ :=
  rfl

end PEqualNP.Outside.L_meta_6642_aux

open PEqualNP.Outside.L_meta_6642_aux in
theorem PEqualNP.Outside.L_meta_6642 :
      let count (D : Circuit) :=
        ({j : Fin D.gates.length | (D.gates.get j).op = GateOp.or} : Set _).ncard
      let critical (n : ℕ) (E : Fin n → Fin n → Prop) (D : Circuit) :=
        ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          ∀ w ∈ (D.gates.get j).inputs, ∃ p l, E p l ∧
            let xs := List.ofFn (fun z : Fin n => decide (z = p ∨ z = l))
            ({D with gates := D.gates.set j.val ⟨GateOp.and, [w]⟩} : Circuit).eval xs = false ∧
            let pre := ({D with gates := D.gates.take j.val} : Circuit).wires xs
            pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true
      let binary (n : ℕ) (D : Circuit) :=
        ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          ∃ a b, (D.gates.get j).inputs = [a, b] ∧ a ≠ b ∧ a < n + j.val ∧ b < n + j.val
      ∀ (n : ℕ) (E : Fin n → Fin n → Prop) (C : Circuit), Monotone2 C → critical n E C →
        ∃ D, Monotone2 D ∧ count D ≤ count C ∧ critical n E D ∧ binary n D ∧
          ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro count critical binary n E C legal pins
  let cap := n + C.gates.length
  let D : Circuit := { C with gates := C.gates.map (replaceEmpty cap) }
  let orig (j : Fin D.gates.length) : Fin C.gates.length :=
    ⟨j.val, by simpa [D] using j.isLt⟩
  have gate (j : Fin D.gates.length) :
      D.gates.get j = replaceEmpty cap (C.gates.get (orig j)) := by
    simp [D, orig, List.get_eq_getElem]
  have kept (j : Fin D.gates.length) (h : (D.gates.get j).op = .or) :
      (C.gates.get (orig j)).op = .or ∧ D.gates.get j = C.gates.get (orig j) ∧
        (D.gates.get j).inputs ≠ [] := by
    have facts := keep_or cap (C.gates.get (orig j)) (by rwa [gate] at h)
    have same := (gate j).trans facts.2.1
    exact ⟨facts.1, same, by simpa only [same] using facts.2.2⟩
  have law : Monotone2 D := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact replaceEmpty_legal cap a (legal a ha)
  have budget : count D ≤ count C := by
    apply Set.ncard_le_ncard_of_injOn orig
    · intro j hj
      exact (kept j hj).1
    · intro a _ b _ eq
      apply Fin.ext
      exact congrArg (fun i : Fin C.gates.length => i.val) eq
  have samePrefix (j : Fin D.gates.length) (xs : List Bool) (hlen : xs.length = n) :
      ({D with gates := D.gates.take j.val} : Circuit).wires xs =
        ({C with gates := C.gates.take j.val} : Circuit).wires xs := by
    change ((C.gates.map (replaceEmpty cap)).take j.val).foldl step xs = _
    rw [← List.map_take]
    exact fold_normalize cap _ xs (by simp [cap, hlen])
  have patched (j : Fin D.gates.length) (w : ℕ) (xs : List Bool) (hlen : xs.length = n) :
      ({D with gates := D.gates.set j.val ⟨GateOp.and, [w]⟩} : Circuit).eval xs =
        ({C with gates := C.gates.set j.val ⟨GateOp.and, [w]⟩} : Circuit).eval xs := by
    have eq := fold_normalize cap (C.gates.set j.val ⟨GateOp.and, [w]⟩) xs (by simp [cap, hlen])
    rw [List.map_set, replaceEmpty_copy] at eq
    exact congrArg (fun ws => ws.getD C.output false) eq
  have pinsD : critical n E D := by
    intro j hj w hw
    obtain ⟨hOrig, eq, _⟩ := kept j hj
    have origMem : w ∈ (C.gates.get (orig j)).inputs := by simpa only [eq] using hw
    obtain ⟨p, l, hpl, loss, off, k, hk, on⟩ := pins (orig j) hOrig w origMem
    exact ⟨p, l, hpl, by rw [patched j w _ (by simp)]; exact loss,
      by rw [samePrefix j _ (by simp)]; exact off,
      k, by rwa [eq], by rw [samePrefix j _ (by simp)]; exact on⟩
  have shapeD : binary n D := by
    intro j hj
    have ins := (law (D.gates.get j) (List.get_mem _ _)).2
    have getOther (a b : ℕ) (ha : a ∈ (D.gates.get j).inputs)
        (only : ∀ k ∈ (D.gates.get j).inputs, k = a ∨ k = b) : a ≠ b ∧ b < n + j.val := by
      obtain ⟨p, l, _, _, off, k, hk, on⟩ := pinsD j hj a ha
      let xs := List.ofFn (fun z : Fin n => decide (z = p ∨ z = l))
      let pre := ({D with gates := D.gates.take j.val} : Circuit).wires xs
      change pre.getD a false = false at off
      change pre.getD k false = true at on
      have neq : k ≠ a := fun eq => Bool.false_ne_true (off.symm.trans (eq ▸ on))
      have eq := (only k hk).resolve_left neq
      subst k
      have length : pre.length = n + j.val := by
        simp [pre, wire_length, xs, List.length_take, Nat.min_eq_left j.isLt.le]
      refine ⟨Ne.symm neq, ?_⟩
      by_contra! outside
      have missing : pre.getD b false = false := List.getD_eq_default _ _ (by omega)
      exact Bool.false_ne_true (missing.symm.trans on)
    cases eq : (D.gates.get j).inputs with
    | nil => exact ((kept j hj).2.2 eq).elim
    | cons a tail =>
      cases tail with
      | nil =>
        have aMem : a ∈ (D.gates.get j).inputs := by rw [eq]; simp
        exact (getOther a a aMem (by intro k hk; rw [eq] at hk; simpa using hk)).1 rfl |>.elim
      | cons b rest =>
        have hlen : rest.length = 0 := by rw [eq] at ins; simp only [List.length_cons] at ins; omega
        obtain rfl := List.length_eq_zero_iff.mp hlen
        have aMem : a ∈ (D.gates.get j).inputs := by rw [eq]; simp
        have bMem : b ∈ (D.gates.get j).inputs := by rw [eq]; simp
        obtain ⟨distinct, earlyB⟩ := getOther a b aMem (by intro k hk; rw [eq] at hk; simpa using hk)
        obtain ⟨_, earlyA⟩ := getOther b a bMem (by intro k hk; rw [eq] at hk; simpa [or_comm] using hk)
        exact ⟨a, b, rfl, distinct, earlyA, earlyB⟩
  refine ⟨D, law, budget, pinsD, shapeD, fun x => ?_⟩
  exact congrArg (fun ws => ws.getD C.output false)
    (fold_normalize cap C.gates (List.ofFn x) (by simp [cap]))
