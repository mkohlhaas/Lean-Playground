/- --------------------------------------------- -/
/- Interlude: Propositions, Proofs, and Indexing -/
/- --------------------------------------------- -/

def woodlandCritters : List String := ["hedgehog", "deer", "snail"]

#eval woodlandCritters                      

def hedgehog := woodlandCritters[0]
def deer     := woodlandCritters[1]
def snail    := woodlandCritters[2]

#eval woodlandCritters.length               

#eval hedgehog                              
#eval deer                                  
#eval snail                                 

-- compile-time error
-- the error message is saying Lean tried to automatically MATHEMATICALLY PROVE that 3 < woodlandCritters.length
#eval woodlandCritters[3]                   

/- ----------------------- -/
/- Propositions and Proofs -/
/- ----------------------- -/

-- A PROPOSITION is a statement that can be true or false.
-- In Lean, propositions are types (and types are propositions).

#eval 1 + 1 = 2                             

-- `rfl : a = a` is the unique constructor of the equality type (Ctrl-k on `rfl` -> documentation for `rfl`)
def onePlusOneIsTwo     : 1 + 1 =  2 := rfl
def onePlusOneIsFifteen : 1 + 1 = 15 := rfl

-- Just as Type describes types such as Nat, String, and List (Nat × String × (Int → Float)) that represent data structures and functions,
-- Prop describes propositions.

-- A proof is a convincing argument that a proposition is true.

-- When a proposition has been proven, it is called a theorem.
-- In Lean, it is conventional to declare theorems with the `theorem` keyword instead of `def`.

-- TODO: are propositions by convention upper-case in Lean?
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo1 : 1 + 1 = 2       := rfl
theorem onePlusOneIsTwo2 : OnePlusOneIsTwo := rfl

/- ------- -/
/- Tactics -/
/- ------- -/

-- Proofs are normally written using TACTICS, rather than by providing evidence directly.
-- TACTICS are small programs that construct evidence for a proposition.

-- writing `by` puts Lean into tactic mode
-- onePlusOneIsTwo written with TACTICS
theorem onePlusOneIsTwo3 : 1 + 1 = 2 := by
  decide

example : 2 + 2 ≠ 5 := by decide
example : 1     ≠ 1 := by decide

-- TACTICS used in this book:
-- decide -> invokes a decision procedure that can check whether a statement is true or false (mainly used with concrete values)
-- simp   -> short for simplify (workhorse of Lean proofs)
-- grind  -> can automatically prove many theorems (uses a collection of techniques from SMT solvers)

/- ----------- -/
/- Connectives -/
/- ----------- -/

-- The basic building blocks of logic, such as “and”, “or”, “true”, “false”, and “not”, are called LOGICAL CONNECTIVES.

-- Most of these connectives are defined like datatypes, and they have constructors.
-- If A and B are propositions, then A ∧ B is a proposition.
-- Evidence for A ∧ B consists of the constructor And.intro, which has the type A → B → A ∧ B.

#check (And)      
#check (And.intro)
#check (And.left) 
#check (And.right)

theorem addAndAppend1 : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := And.intro rfl rfl
theorem addAndAppend2 : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by decide          -- decide is powerful enough to find this proof

-- A ∨ B has two constructors:
-- Or.inl with type A → A ∨ B
-- Or.inr with type B → A ∨ B

#check (Or)    
#check (Or.inl)
#check (Or.inl)

-- Implication A → B is shorthand for ¬A ∨ B in traditional logic.
-- In Lean implication is represented using functions.
-- In particular, a function that transforms evidence for A into evidence for B is itself evidence that A implies B.
-- The two formulations are equivalent.

-- ¬A ∨ B (= A → B)
--
-- | A | B | ¬A | ¬A ∨ B |
-- |---+---+----+---------
-- | 0 | 0 |  1 |    1   |
-- | 0 | 1 |  1 |    1   |
-- | 1 | 0 |  0 |    0   |
-- | 1 | 1 |  0 |    1   |
-- |---+---+----+--------|

-- A ∧ B → A ∨ B (A and B implies A or B)
--
-- | A | B | A ∧ B | A ∨ B | A ∧ B → A ∨ B | 
-- |---+---+-------+-------+---------------|
-- | 0 | 0 |   0   |   0   |       1       |
-- | 0 | 1 |   0   |   1   |       1       |
-- | 1 | 0 |   0   |   1   |       1       |
-- | 1 | 1 |   1   |   1   |       1       |
-- |---+---+-------+-------+---------------|

theorem andImpliesOr1 : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _b => Or.inl a

theorem andImpliesOr2 : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro _a b => Or.inr b

-- Connective  | Lean Syntax        | Evidence
-- ----------- | ------------------ | ----------------------------------------------------------------------
-- True        | True               | True.intro : True
-- False       | False              | No evidence
-- A and B     | A ∧ B              | And.intro : A → B → A ∧ B
-- A or B      | A ∨ B              | Either Or.inl : A → A ∨ B or Or.inr : B → A ∨ B
-- A implies B | A → B              | A function that transforms evidence of A into evidence of B
-- not A       | ¬A                 | A function that would transform evidence of A into evidence of False

-- The decide tactic can prove theorems that use these connectives:
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive      : ¬(1 + 1 = 5)      := by decide
theorem trueIsTrue           : True              := by decide
theorem trueOrFalse          : True ∨ False      := by decide
theorem falseImpliesTrue     : False → True      := by decide

/- --------------------- -/
/- Evidence as Arguments -/
/- --------------------- -/

def third1 (xs : List α) : α := xs[2]                        

-- the obligation to show that the list has at least three entries can be imposed on the caller
-- xs.length > 2 is NOT a program that checks whether xs has more than 2 entries.
-- It is a proposition that could be true or false, and the argument ok must be evidence that it is true.
def third2 (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- decide can construct the evidence automatically
#eval third2 woodlandCritters (by decide)                        

/- ------------------------- -/
/- Indexing Without Evidence -/
/- ------------------------- -/

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters                               
#eval thirdOption ["only", "two"]                                

-- There is also a version that crashes the program when the index is out of bounds, rather than returning an Option:
#eval woodlandCritters[0]!                                       
#eval woodlandCritters[1]!                                       
#eval woodlandCritters[2]!                                       
#eval woodlandCritters[3]!                                      

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- decide can proof a proposition to be true, but also to be false
#eval third2 ["only", "two"]  (by decide)                        

-- The simp and decide tactics do not automatically unfold definitions with def.
theorem onePlusOneIsStillTwo1 : OnePlusOneIsTwo := rfl
theorem onePlusOneIsStillTwo2 : OnePlusOneIsTwo := by simp       
theorem onePlusOneIsStillTwo3 : OnePlusOneIsTwo := by decide     

-- definitions written with `abbrev` are always unfolded
abbrev OnePlusOneIsTwo1 : Prop := 1 + 1 = 2

theorem onePlusOneIsStillTwo4 : OnePlusOneIsTwo1 := rfl
theorem onePlusOneIsStillTwo5 : OnePlusOneIsTwo1 := by simp
theorem onePlusOneIsStillTwo6 : OnePlusOneIsTwo1 := by decide


-- polymorphic function
-- In Lean only programs whose types contain at least one value are allowed to crash.
-- If a program with an empty type could crash, then that crashing program could be used as a kind of fake evidence for a false proposition.
def unsafeThird (xs : List α) : α := xs[2]!                  

-- whitespace between list and brackets
-- Lean attempts to treat woodlandCritters as a function
#eval woodlandCritters [1]                                       

/- --------- -/
/- Exercises -/
/- --------- -/

-- 1. Prove the following theorems using rfl: 2 + 3 = 5, 15 - 8 = 7, "Hello, ".append "world" = "Hello, world".
--    What happens if rfl is used to prove 5 < 18? Why?

-- rfl is about equality
theorem ex1 : 2 + 3 = 5                                 := by rfl
theorem ex2 : 15 - 8 = 7                                := by rfl
theorem ex3 : "Hello, ".append "world" = "Hello, world" := by rfl
theorem ex4 : 5 < 18                                    := by rfl

-- 2. Prove the following theorems using by decide: 2 + 3 = 5, 15 - 8 = 7, "Hello, ".append "world" = "Hello, world", 5 < 18.

-- now with decide
theorem ex5 : 2 + 3 = 5                                 := by decide
theorem ex6 : 15 - 8 = 7                                := by decide
theorem ex7 : "Hello, ".append "world" = "Hello, world" := by decide
theorem ex8 : 5 < 18                                    := by decide

-- 3. Write a function that looks up the fifth entry in a list.
--    Pass the evidence that this lookup is safe as an argument to the function. 

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]

#eval fifth [0, 1, 2, 3, 4]  (by decide)
#eval fifth woodlandCritters (by decide)
