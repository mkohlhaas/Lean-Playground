/- ========================================== -/
/- Functors, Applicative Functors, and Monads -/
/- ========================================== -/

-- Functor and Monad both describe operations for types that are still waiting for a type argument.

#print Functor
#print Monad  

-- Functor describes containers in which the contained data can be transformed.
-- Monad   describes an encoding of programs with side effects.

-- Option has instances for both Functor and Monad.
-- Option represents an optional value and a computation that might fail to return a value.

#print Option 

-- The type class Applicative provides the overloadable operations of applicative functors.

-- The monad               abstraction is more powerful than the applicative functor abstraction.
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
#print MythicalCreature.mk                                  
#print MythicalCreature                                     

-- a function .large is created that extracts the field from the constructor
#print MythicalCreature.large                               

def mc := { large := true : MythicalCreature }

#eval mc.large                                              
#eval MythicalCreature.large mc                             

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large         := true
  vulnerability := "sunlight"

-- Inheritance is implemented using composition.
-- The constructor Monster.mk takes a MythicalCreature as its argument.
#print Monster.mk                                           

-- a function is created to extract the underlying creature
#print Monster                                              
#print Monster.toMythicalCreature                           

-- In Lean moving up the inheritance hierarchy erases the underlying information!
#eval  troll.toMythicalCreature                             
#check troll.toMythicalCreature                             

-- curly-brace notation works with structure inheritance
def troll1 : Monster := {large := true, vulnerability := "sunlight"}

-- anonymous angle-bracket notation that delegates to the underlying constructor reveals the internal details
def troll2 : Monster := ⟨true, "sunlight"⟩                  

-- An extra set of angle brackets is required
def troll3 : Monster := ⟨⟨true⟩, "sunlight"⟩

-- MythicalCreature.large can be used with a Monster,
-- and Lean automatically inserts the call to Monster.toMythicalCreature
-- before the call to MythicalCreature.large.

#eval troll.large                                           

-- This only occurs when using dot notation, and applying the field lookup function using normal function call syntax results in a type error.
#eval MythicalCreature.large troll                          

-- dot notation can also take inheritance into account for user-defined functions
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

#eval troll.small                                           

-- but this again results in an error
#eval MythicalCreature.small troll                          

/- -------------------- -/
/- Multiple Inheritance -/
/- -------------------- -/

structure Helper extends MythicalCreature where
  assistance : String
  payment    : String
deriving Repr

-- just an example for a helper (not used in the examples)
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

#print MonstrousAssistant.mk                               

-- NOTE: the @[reducible] attribute has the same effect as writing `abbrev`
#print MonstrousAssistant.toMonster -- extracts the Monster
#print MonstrousAssistant.toHelper  -- creates an Helper   

/- -------------------- -/
/- Default Declarations -/
/- -------------------- -/

inductive Size where
  | small
  | medium
  | large
deriving BEq, Repr

-- the default definitions in the child structure are only used when no specific value for `large` is provided
structure SizedCreature extends MythicalCreature where
  size  : Size
  large := size == Size.large

#print SizedCreature

def smallCreature : SizedCreature where
  size := .small
  
def nonsenseCreature : SizedCreature where
  size  := .large
  large := false
  
#check smallCreature                                      
#eval  smallCreature                                      
#print smallCreature                                      

#check nonsenseCreature                                   
#eval  nonsenseCreature                                   
#print nonsenseCreature                                   

-- If the child structure should not deviate from the parent structure, one could define
-- a proposition that the fields are related appropriately,
-- and designing the API to require evidence that the proposition is true where it matters.

-- abbrev is used because it should automatically be unfolded in proofs
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size  := .medium

example : SizesMatch huldre           := by decide
example : SizesMatch smallCreature    := by decide
example : SizesMatch nonsenseCreature := by decide

/- ---------------------- -/
/- Type Class Inheritance -/
/- ---------------------- -/

-- Behind the scenes, type classes are structures.
-- Defining a new type class defines a new structure, and defining an instance creates a value of that structure type.

-- Because it uses precisely the same language features, type class inheritance supports all the features of structure inheritance,
-- including multiple inheritance, default implementations of parent types' methods, and automatic collapsing of diamonds.
