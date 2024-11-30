#eval 18+19
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
variable (p q r : Prop)

--3. Propositions and Proofs Exercises:

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  -- L → R
    (fun h : p ∧ q =>
    have hp : p := h.left -- Extract p from h
    have hq : q := h.right -- Extact q from h
    show q ∧ p from ⟨hq, hp⟩) -- Constuct q ∧ p
  -- R → L
    (fun h2 : q ∧ p =>
    have hq : q := h2.left
    have hp : p := h2.right
    show p ∧ q from ⟨hp, hq⟩)


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.inr hp)
      (fun hq : q =>
        show q ∨ p from Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h
      (fun hq : q =>
        show p ∨ q from Or.inr hq)
      (fun hp : p =>
        show p ∨ q from Or.inl hp)
    )


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      have hr : r := h.right
      have hpq : p ∧ q := h.left
      have hp : p := hpq.left
      have hq : q := hpq.right
      show p ∧ (q ∧ r) from ⟨hp,⟨hq, hr⟩⟩)
    (fun h : p ∧ q ∧ r =>
      have hp : p := h.left
      have hqr : q ∧ r := h.right
      have hq : q := hqr.left
      have hr : r := hqr.right
      show (p ∧ q) ∧ r from ⟨⟨hp,hq⟩,hr⟩
    )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr : (p ∨ q) ∨ r =>
      Or.elim hpqr
      (fun hpq : p ∨ q =>
        Or.elim hpq
        (fun hp : p =>
          show p ∨ (q ∨ r) from Or.inl hp)
        (fun hq : q =>
          have hr : q ∨ r := Or.inl hq
          show p ∨ (q ∨ r) from Or.inr hr))
      (fun hr : r =>
        show p ∨ (q ∨ r) from Or.inr (Or.inr hr)
      )
    )
  -- Now Prove L <- R
    (fun h: p ∨ (q ∨ r) =>
      Or.elim h
      (fun hp : p =>
        have hpq : p ∨ q := Or.inl hp
        show (p ∨ q) ∨ r from Or.inl hpq)
      (fun hqr : q ∨ r =>
        Or.elim hqr
        (fun hq : q =>
          have hpq : p ∨ q := Or.inr hq
          show (p ∨ q) ∨ r from Or.inl hpq)
        (fun hr : r =>
          show (p ∨ q) ∨ r from Or.inr hr)
      )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
-- First prove L -> R
  Iff.intro
    (fun hpqr : p ∧ (q ∨ r) =>
      have hp : p := hpqr.left
      have hqr : q ∨ r := hpqr.right
      Or.elim hqr
        (fun hq : q =>
          have hpq : p ∧ q := ⟨hp,hq⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.inl hpq)
        (fun hr : r =>
          have hpr : p ∧ r := ⟨hp,hr⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.inr hpr))
-- Now prove L <- R
    (fun hpqr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqr
      (fun hpq : p ∧ q =>
        have hp : p := hpq.left
        have hq : q := hpq.right
        have hqr : q ∨ r := Or.inl hq
        show p ∧ (q ∨ r) from ⟨hp,hqr⟩)
      (fun hpr : p ∧ r =>
        have hp : p := hpr.left
        have hr : r := hpr.right
        have hqr : q ∨ r := Or.inr hr
        show p ∧ (q ∨ r) from ⟨hp,hqr⟩)
    )


example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    -- Prove L → R
    (fun hpqr : p ∧ (q ∨ r) =>
      have hp : p := hpqr.left
      have hqr : q ∨ r := hpqr.right
      Or.elim hqr
        (fun hq : q =>
          have hpq : p ∧ q := ⟨hp, hq⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.inl hpq)
        (fun hr : r =>
          have hpr : p ∧ r := ⟨hp, hr⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.inr hpr))
    -- Prove L ← R
    (fun hpqr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqr
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          have hqr : q ∨ r := Or.inl hq
          show p ∧ (q ∨ r) from ⟨hp, hqr⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          have hqr : q ∨ r := Or.inr hr
          show p ∧ (q ∨ r) from ⟨hp, hqr⟩))








example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
Iff.intro
  (fun hpqr : p ∨ (q ∧ r) =>
    Or.elim hpqr
    (fun hp : p =>
      have hpq : p ∨ q := Or.inl hp
      have hpr : p ∨ r := Or.inl hp
      show (p ∨ q) ∧ (p ∨ r) from ⟨hpq, hpr⟩)
    (fun hqr : q ∧ r =>
      have hq : q := hqr.left
      have hr : r := hqr.right
      have hpq : p ∨ q := Or.inr hq
      have hpr : p ∨ r := Or.inr hr
      show (p ∨ q) ∧ (p ∨ r) from ⟨hpq,hpr⟩))
  (fun hpqpr : (p ∨ q) ∧ (p ∨ r) =>
    have hpq : p ∨ q := hpqpr.left
    have hpr : p ∨ r := hpqpr.right
    Or.elim hpq
      (fun hp : p =>
        show p ∨ (q ∧ r) from Or.inl hp)
      (fun hq : q =>
        Or.elim hpr
          (fun hp : p =>
            show p ∨ (q ∧ r) from Or.inl hp)
          (fun hr : r =>
            show p ∨ (q ∧ r) from Or.inr (⟨hq,hr⟩))
      )
    )



-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
  (fun hpqr : (p → (q → r)) =>
    (fun hpq : p ∧ q =>
      have hp : p := hpq.left
      have hq : q := hpq.right
      have hqr : q → r := hpqr hp
      show r from hqr hq))
  (fun hpqr : (p ∧ q → r) =>
    (fun hp : p =>
      (fun hq : q =>
        have hpq : p ∧ q := ⟨hp,hq⟩
        show r from hpqr hpq)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro
  (fun hpqr : ((p ∨ q) → r) =>
    ⟨
      (fun hp : p =>
        have hpq : p ∨ q := Or.inl hp
        show r from hpqr hpq),
      (fun hq : q =>
        have hpq : p ∨ q := Or.inr hq
        show r from hpqr hpq)
    ⟩)
  (fun hpqrr : (p → r) ∧ (q → r) =>
    (fun hpq : p ∨ q =>
      Or.elim hpq
        (fun hp : p =>
          have hpr : p → r := hpqrr.left
          show r from hpr hp)
        (fun hq : q =>
          have hqr : q → r := hpqrr.right
          show r from hqr hq)))


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
Iff.intro
  (fun hpq : ¬(p ∨ q) =>
    ⟨
      (fun hp : p =>
        have hq : p ∨ q := Or.inl hp
        show False from hpq hq),
      (fun hq : q =>
        have hp : p ∨ q := Or.inr hq
        show False from hpq hp)
    ⟩
  )
  (fun hpq : ¬p ∧ ¬q =>
    (fun hn : p ∨ q =>
      Or.elim hn
        (fun hp : p =>
          show False from hpq.left hp)
        (fun hq : q =>
          show False from hpq.right hq)
    )
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
(fun hd : ¬p ∨ ¬q =>
  Or.elim hd
    (fun hp : ¬p =>
      (fun hpq : p ∧ q =>
        show False from hp hpq.left)
    )
    (fun hq : ¬ q =>
      (fun hpq : p ∧ q =>
        show False from hq hpq.right))
)

example : ¬(p ∧ ¬p) :=
(fun hp : p ∧ ¬p =>
  show False from hp.right hp.left)

example : p ∧ ¬q → ¬(p → q) :=
(fun hpq : p ∧ ¬q =>
  (fun hi : p → q =>
    show False from hpq.right (hi hpq.left))
)

example : ¬p → (p → q) :=
(fun hn : ¬p =>
  (fun hp : p =>
    False.elim (hn hp)))

example : (¬p ∨ q) → (p → q) :=
(fun hd : ¬p ∨ q =>
  Or.elim hd
    (fun hnp: ¬p =>
      (fun hp : p =>
        False.elim (hnp hp))
    )
    (fun hq : q =>
      (fun _ : p =>
         hq))
)


example : p ∨ False ↔ p :=
Iff.intro
  (fun hd : p ∨ False =>
    Or.elim hd
      (fun hp : p =>
        hp
      )
      (fun hf : False =>
        False.elim hf)
  )
  (fun hp : p =>
    show p ∨ False from Or.inl hp)

example : p ∧ False ↔ False :=
Iff.intro
  (fun hc : p ∧ False =>
    hc.right
  )
  (fun hf : False =>
    False.elim hf
  )


example : (p → q) → (¬q → ¬p) :=
(fun hl : p → q =>
  (fun hq : ¬q =>
    (fun hp : p =>
      hq (hl hp))
  )
)
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
(fun hl : p → q ∨ r =>
  Or.elim (Classical.em p)
    (fun hp : p =>
      have hqr : q ∨ r := hl hp
      Or.elim hqr
          (fun hq : q =>
            Or.inl (fun _ : p =>
              hq))
          (fun hr : r =>
            Or.inr (fun _ : p =>
              hr))
    )
    (fun hn : ¬p =>
      Or.inl (fun hp : p =>
        False.elim (hn hp))
    )
)



example : ¬(p ∧ q) → ¬p ∨ ¬q :=
(fun hn : ¬(p ∧ q) =>
  Or.elim (Classical.em p)
    (fun hp : p =>
      Or.elim (Classical.em q)
        (fun hq : q =>
          have hc : p ∧ q := ⟨hp,hq ⟩
          False.elim (hn hc))
        (fun hnq : ¬q =>
          Or.inr hnq
        )
    )
    (fun hnp : ¬p =>
      show ¬p ∨ ¬q from Or.inl hnp)
)

example : ¬(p → q) → p ∧ ¬q :=
  (fun hn : ¬(p → q) =>
    Or.elim (Classical.em p)
      (fun hp : p =>
        have hnq : ¬q := fun hq : q => hn (fun _ => hq)
        ⟨hp, hnq⟩
      )
      (fun hnp : ¬p =>
        have hpnq : p → q := fun hp => False.elim (hnp hp)
        False.elim (hn hpnq)
      )
  )


example : (p → q) → (¬p ∨ q) :=
  (fun hi : p → q =>
    Or.elim (Classical.em p)
      (fun hp : p =>
        show ¬p ∨ q from Or.inr (hi hp)
      )
      (fun hn : ¬p =>
        show ¬p ∨ q from Or.inl hn)
    )

example : (¬q → ¬p) → (p → q) :=
  (fun hn : ¬q → ¬p =>
    (fun hp : p =>
      Or.elim (Classical.em q)
        (fun hq : q => hq)
        (fun hnq : ¬q => False.elim (hn hnq hp))
    )
  )


example : p ∨ ¬p :=
  Or.elim (Classical.em p)
    (fun hp : p =>
    show p ∨ ¬p from Or.inl hp
    )
    (fun hn : ¬p =>
    show p ∨ ¬p from Or.inr hn
    )


example : (((p → q) → p) → p) :=
  (fun hpqr : (p → q) → p =>
    Or.elim (Classical.em p)
      (fun hp : p => hp)
      (fun hn : ¬p =>
        hpqr (fun hp : p => False.elim (hn hp)))
  )
