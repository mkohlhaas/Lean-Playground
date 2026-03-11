/- ========================================== -/
/- Functors, Applicative Functors, and Monads -/
/- ========================================== -/

-- Functor and Monad both describe operations for types that are still waiting for a type argument.

-- Functor describes containers in which the contained data can be transformed.
-- Monad   describes an encoding of programs with side effects.

-- Option has instances for both Functor and Monad
-- Option represents an optional value and a computation that might fail to return a value.

-- The type class Applicative provides the overloadable operations of applicative functors.

-- The monad abstraction is more powerful than the applicative functor abstraction.
-- The applicative functor abstraction is more powerful than the functor abstraction.

-- Every monad is an applicative functor.
-- Every applicative functor is a functor.
-- The converses do not hold.

/- ========================== -/
/- Structures and Inheritance -/
/- ========================== -/

structure MythicalCreature where
  large : Bool
deriving Repr

-- creates an inductive type with a single constructor called mk
#check MythicalCreature.mk
#print MythicalCreature.mk

-- a function .large is created that extracts the field from the constructor
#check MythicalCreature.large
#print MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large         := true
  vulnerability := "sunlight"

-- Inheritance is implemented using composition.
-- The constructor Monster.mk takes a MythicalCreature as its argument.
#check Monster.mk
#print Monster.mk

-- a function is created to extract the underlying creature
#check Monster.toMythicalCreature 
#print Monster.toMythicalCreature 

#print Monster

-- In Lean moving up the inheritance hierarchy erases the underlying information!
#eval troll.toMythicalCreature

-- curly-brace notation works with structure inheritance
def troll1 : Monster := {large := true, vulnerability := "sunlight"}

-- anonymous angle-bracket notation that delegates to the underlying constructor reveals the internal details
def troll2 : Monster := ⟨true, "sunlight"⟩

-- An extra set of angle brackets is required
def troll3 : Monster := ⟨⟨true⟩, "sunlight"⟩

-- MythicalCreature.large can be used with a Monster,
-- and Lean automatically inserts the call to Monster.toMythicalCreature
-- before the call to MythicalCreature.large.

-- But: field lookup function using normal function call syntax results in a type error
#eval MythicalCreature.large troll

def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

-- Dot notation can also take inheritance into account for user-defined functions.

#eval troll.small

-- but this results in an error
#eval MythicalCreature.small troll

/- -------------------- -/
/- Multiple Inheritance -/
/- -------------------- -/

structure Helper extends MythicalCreature where
  assistance : String
  payment    : String
deriving Repr

def nisse : Helper where
  large      := false
  assistance := "household tasks"
  payment    := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large         := true
  assistance    := "heavy labor"
  payment       := "toy goats"
  vulnerability := "sunlight"

-- diamond problem: In Lean the first specified path to the grandparent structure is taken,
--                  and the additional parent structures' fields are copied rather
--                  than having the new structure include both parents directly.

-- see resolution order
#print MonstrousAssistant

#check MonstrousAssistant.mk
#print MonstrousAssistant.mk

#print MonstrousAssistant.toMonster -- extracts the Monster
#print MonstrousAssistant.toHelper  -- creates an Helper

/- -------------------- -/
/- Default Declarations -/
/- -------------------- -/

inductive Size where
  | small
  | medium
  | large
deriving Repr, BEq

structure SizedCreature extends MythicalCreature where
  size  : Size
  large := size == Size.large

def smallCreature : SizedCreature where
  size := Size.small
  
def nonsenseCreature : SizedCreature where
  large := false
  size  := .large
  
#check smallCreature
#eval  smallCreature
#print smallCreature

#check nonsenseCreature
#eval  nonsenseCreature
#print nonsenseCreature

-- TODO: not clear

-- If the child structure should not deviate from the parent structure, there are a few options. One of them is:
-- Defining a proposition that the fields are related appropriately, and designing the API to require evidence that the proposition is true where it matters.

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  decide

/- ---------------------- -/
/- Type Class Inheritance -/
/- ---------------------- -/

-- Behind the scenes, type classes are structures.
-- Defining a new type class defines a new structure, and defining an instance creates a value of that structure type.

-- Because it uses precisely the same language features, type class inheritance supports all the features of structure inheritance,
-- including multiple inheritance, default implementations of parent types' methods, and automatic collapsing of diamonds.

