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
    show q ∨ p from Or.inl hq)
    )
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
  show p ∧ (q ∧ r) from ⟨hp,⟨hq, hr⟩⟩
  )
  (fun h : p ∧ q ∧ r =>
  have hp : p := h.left
  have hqr : q ∧ r := h.right
  have hq : q := hqr.left
  have hr : r := hqr.right
  show (p ∧ q) ∧ r from ⟨⟨hp,hq⟩,hr⟩
  )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (fun h: (p ∨ q) ∨ r =>
  Or.elim h
  (fun hpq : p ∨ q =>
  Or.elim hpq
  (fun hp : p =>
  show p ∨ (q ∨ r) from Or.inl hp)
  (fun hq : q =>
  have hr : q ∨ r := Or.inl hq
  show p ∨ (q ∨ r) from Or.inr hr)))
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
  show (p ∨ q) ∨ r from Or.inr hr
  )
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
show (p ∧ q) ∨ (p ∧ r) from Or.inr hpr)
)
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
show p ∧ (q ∨ r) from ⟨hp,hqr⟩
)
)


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
