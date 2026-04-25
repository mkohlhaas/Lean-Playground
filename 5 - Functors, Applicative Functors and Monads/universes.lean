/- ========= -/
/- Universes -/
/- ========= -/

-- A universe is a type that classifies other types.
-- Two familiar universes are Type and Prop.

-- The whole point of the universe system is to rule out self-referential types. 
-- Avoids GIRARD'S PARADOX and RUSSELL'S PARADOX.

-- Type (= `Type 0`) classifies ordinary types, such as Nat, String, Int → String × Char, IO Unit, …
-- Nat's    type is Type
-- String's type is Type
-- …
-- Prop's   type is Type
#check Nat                                      
#check String                                   
#check Int → String × Char                      
#check IO Unit                                  
#check Prop                                     

-- Prop classifies propositions that may be true or false, such as "nisse" = "elf", 3 > 2, …
#check "nisse" = "elf"                          
#check 3 > 2                                    

-- the type of `Type`   is `Type 1`
-- the type of `Type 1` is `Type 2`
-- the type of `Type 2` is `Type 3`
-- the type of `Type 3` is `Type 4`
-- …
#check Type 0                                   
#check Type 1                                   
#check Type 2                                   
#check Type 3                                   
-- …

-- Function types occupy the smallest universe that can contain both the argument type and the return type. 
#check Nat → Nat                                
#check Type 0 → Type 0                          
#check Type 1 → Type 2                          
#check Type 1 → Type 2                          
#check Type 2 → Type 1                          
#check Type 5 → Type 3                          
#check Type 3 → Type 5                          
-- …

-- NOTE: There is one exception to this rule!
-- If the return type of a function is a Prop, then the whole function type is in Prop.
#check (n : Nat) → n = n + 0                    
#check Type      → 2 + 2 = 4                    

/- ------------------ -/
/- User Defined Types -/
/- ------------------ -/

inductive MyList (α : Type) : Type where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- MyList is a Type → Type
#print MyList                                   

-- it cannot be used to contain types
def myListOfNat : MyList Type := .cons Nat .nil 

-- NOTE: 
-- The specific rules that govern whether a datatype is allowed are somewhat complicated.
-- Generally speaking, it's easiest to start with the datatype in the same universe as the largest of its arguments.
-- Then, if Lean rejects the definition, increase its level by one, which will usually go through.

-- the argument to cons with type α is from a larger universe than MyList
-- NOTE: Play with Type 0, Type 1, …; comment out erroneous lines if necessary!
inductive MyList' (α : Type 1) : Type 0 where
  | nil  : MyList' α
  /- | cons : α → MyList' α → MyList' α             -/

#print MyList'                                  

/- --------------------- -/
/- Universe Polymorphism -/
/- --------------------- -/

-- TYPE ARGUMENTS     are conventionally named with Greek letters.
-- UNIVERSE ARGUMENTS are conventionally named u, v, and w.

inductive MyList'' (α : Type u) : Type u where
  | nil  : MyList'' α
  | cons : α → MyList'' α → MyList'' α

def myListOfNumbers : MyList'' Nat           := .cons 0 (.cons 1 .nil)
def myListOfNat'    : MyList'' Type          := .cons Nat .nil
def myListOfList    : MyList'' (Type → Type) := .cons MyList'' .nil

#check myListOfNumbers
#check myListOfNat'   
#check myListOfList   

-- each occurrence of MyList'' is provided with a universe level argument
-- level arguments are written with a dot and curly braces
def myListOfNumbers' : MyList''.{0} Nat           := .cons 0 (.cons 1 .nil)
def myListOfNat''    : MyList''.{1} Type          := .cons Nat .nil
def myListOfList'    : MyList''.{1} (Type → Type) := .cons MyList''.{0} .nil

-- when a universe-polymorphic definition takes multiple types as arguments,
-- it's a good idea to give each argument its own level variable for maximum
-- flexibility
inductive MySum (α : Type u) (β : Type u) : Type u where
  | inl : α → MySum α β
  | inr : β → MySum α β

-- can be used at multiple levels
def stringOrNat  : MySum String Nat  := .inl "hello"
def typeOrType   : MySum Type Type   := .inr Nat

-- but both arguments must be in the same universe (there's only one universe argument `u` in the definition of MySum)
def stringOrType : MySum String Type := .inr Nat

-- more flexible by using different variables the two type universe levels, and
-- then declaring that the resulting datatype is in the largest of the two
inductive MySum' (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → MySum' α β
  | inr : β → MySum' α β

-- arguments from different universes possible
def stringOrType' : MySum' String Type := .inr Nat

-- In positions where Lean expects a universe level, any of the following are allowed:
-- · a concrete level, like 0, 1, 2, …
-- · a variable that stands for a level, like `u` or `v`
-- · the maximum of two levels, written as `max` applied to the levels, like `max u v`
-- · a level increase, written with + 1, like `(max u v) + 1`

/- ---------------------------------------- -/
/- Writing Universe-Polymorphic Definitions -/
/- ---------------------------------------- -/

-- Guidelines:
-- · independent type arguments should have different universe variables
-- · the whole type is itself typically either in the maximum of all the universe variables `max u v` or
-- · one greater than this maximum `max (u + 1) v`
--   · try the smaller one first
-- · Non-polymorphic types, such as Nat and String, can be placed directly in Type 0 (= Type)

/- --------------------- -/
/- Prop and Polymorphism -/
/- --------------------- -/

-- Prop is at the bottom of the universe hierarchy, and the type of Prop is Type.
-- This means that Prop is a suitable argument to provide to List, for the same reason that Nat is.

-- Lists of propositions have type List Prop.
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

-- Prop is a Type.
def someTruePropositions' : List.{0} Prop := [ -- with universe argument (0) to proove the point
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

-- Prop and Type are united into a single hierarchy called Sort.

-- Prop is the same as Sort 0, Type 0 is Sort 1, Type 1 is Sort 2, …
-- Type u is the same as Sort (u+1). When writing programs with Lean, this is
-- typically not relevant, but it may occur in error messages from time to
-- time, and it explains the name of the CoeSort class.
