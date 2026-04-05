-- from previous chapters

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k    => Pos.succ k
  | Pos.succ n, k => Pos.succ $ n.plus k

instance : Add Pos where
  add := Pos.plus
  
instance : OfNat Pos (n + 1) where
  ofNat := let rec natPlusOne : Nat → Pos       
             | 0     => Pos.one                 
             | k + 1 => Pos.succ $ natPlusOne k 
           natPlusOne n                         

/- --------------------------- -/
/- Controlling Instance Search -/
/- --------------------------- -/

-- adding Nat's and Pos's

def addNatPos : Nat → Pos → Pos
  | 0, p     => p
  | n + 1, p => Pos.succ $ addNatPos n p

def addPosNat : Pos → Nat → Pos
  | p, 0     => p
  | p, n + 1 => Pos.succ $ addPosNat p n

#eval addNatPos 5 4
#eval addPosNat 5 4

-- but adding Pos's and Nat's doesn't work with `+`
#eval (3 : Nat) + (5 : Nat)
#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)
#eval (3 : Pos) + (5 : Pos)

/- -------------------------- -/
/- Heterogeneous Overloadings -/
/- -------------------------- -/

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Nat) + (5 : Nat)
#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)
#eval (3 : Pos) + (5 : Pos)

class HPlus1 (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
  
instance : HPlus1 Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus1 Pos Nat Pos where
  hPlus := addPosNat

-- Note: metavariables represent unknown parts of a program that could not be inferred
-- see error message from language server
#eval toString $ HPlus1.hPlus (3 : Pos) (5 : Nat)

-- with type annotations - unconvenient!
#eval (HPlus1.hPlus (3 : Pos) (5 : Nat) : Pos)

/- ----------------- -/
/- Output Parameters -/
/- ----------------- -/

-- Most type class parameters are inputs to the search algorithm: they are used to select an instance.

-- In some cases, it can be convenient to start the search process even when some of the type parameters
-- are not yet known, and use the instances that are discovered in the search to determine values for metavariables.

-- The parameters that aren't needed to start instance search are outputs of the process, which is declared with
-- the outParam modifier.

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- With this output parameter, type class instance search is able to select an instance without knowing γ in advance.
#eval HPlus.hPlus (3 : Pos) (5 : Nat)

/- ----------------- -/
/- Default Instances -/
/- ----------------- -/

-- Default instances are instances that are available for instance search even when not all their inputs are known. 

-- When one of these instances can be used, it will be used.

instance [Add α] : HPlus α α α where
  hPlus := Add.add

-- With this instance, hPlus can be used for any addable type, like Nat:
#eval  HPlus.hPlus (3 : Nat) (5 : Nat)

#check HPlus.hPlus (5 : Nat) (3 : Nat)
#check HPlus.hPlus (5 : Nat)          

-- In the vast majority of cases, when someone supplies one argument to addition, the other argument will have the same type.
-- To make this instance into a default instance, apply the `default_instance` attribute.

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (5 : Nat)          

-- Default instances can also be assigned priorities that affect which will be chosen in situations where more than one might apply.
-- For more information on default instance priorities, please consult the Lean manual.

/- --------- -/
/- Exercises -/
/- --------- -/

-- Christian wants an inductive type definition
-- https://proofassistants.stackexchange.com/questions/2435/recursive-type-class-for-ofnat-even
-- https://github.com/James-Oswald/Functional-Programming-In-Lean/blob/lean-3.51.1/src/4.2.lean

-- TBD
