-- from previous chapters

def even : Nat -> Bool
  | Nat.zero   => true
  | Nat.succ k => not $ even k

/- ------------ -/
/- Polymorphism -/
/- ------------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=polymorphism

-- use Greek letters for name type arguments (when no more specific name suggests itself)
-- PPoint = Parametric Point (from parametric polymorphism)
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

-- α must itself be a Repr
#eval {x := (· + 1), y := (· * 2) : PPoint _ }          
#eval {x := 1, y := 2 : PPoint _ }                      

#print  PPoint                                          
#check (PPoint)                                         

def natOrigin : PPoint Nat := { x := Nat.zero, y := Nat.zero }

def replaceX (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
                                
#check (replaceX)                                       
#eval replaceX natOrigin 5                              

def replaceX' (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
                                
#check (replaceX')                                      
#check (replaceX' Nat)                                  
#check (replaceX' (PPoint Nat))                         
#check (replaceX' Type)                                 
#check (replaceX' Nat natOrigin)                        
#check (replaceX' Nat natOrigin 5)                      

#eval   replaceX' Nat natOrigin 5                       

inductive Sign where
  | pos
  | neg

-- returns Nat or Int
def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => ( 3 : Nat)
  | Sign.neg => (-3 : Int)

#check posOrNegThree Sign.pos                           
#check posOrNegThree Sign.neg                           

#eval posOrNegThree Sign.pos                            
#eval posOrNegThree Sign.neg                            

/- ------------ -/
/- Linked Lists -/
/- ------------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=linked-lists

def primesUnder10 : List Nat := [2, 3, 5, 7]

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 $ List.cons 3 $ List.cons 5 $ List.cons 7 List.nil

#eval primesUnder10                                     
#eval explicitPrimesUnder10                             

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

#print List                                             

#eval List.length ["Sourdough", "bread"]                
#eval ["Sourdough", "bread"].length                     

-- Generally, functions follow the shape of the data:
--  · recursive datatypes lead to recursive functions
--  · polymorphic datatypes lead to polymorphic functions

def length' (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil       => Nat.zero
  | List.cons _ ys => Nat.succ (length' α ys)

def length'' (α : Type) (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (length'' α ys)
  
#eval length'' String ["Sourdough", "bread"]            

def length (xs : List α) : Nat :=
  match xs with
  | List.nil        => Nat.zero
  | List.cons _ lst => Nat.succ $ length lst

#eval length ["Sourdough", "bread"]                     

-- syntactiv sugar: using bracket for nil and infix :: operator for cons
def length1 (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ $ length1 ys

#check (length1)                                        
#check (length1 (α := Int))                             
#eval length1 ["Sourdough", "bread"]                    

#check (List.length)                                    
#check List.length (α := Int)                           

/- ------------------ -/
/- Implicit Arguments -/
/- ------------------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=implicit-parameters

-- Arguments can be declared implicit by wrapping them in curly braces instead
-- of parentheses when defining a function.
def replaceX'' {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX'')                                    
#check (replaceX'' (α := Int))                         
#check (replaceX'' natOrigin)                          
#eval   replaceX'' natOrigin 5                         

def length''' {α : Type} (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ $ length''' ys

#check (length''')                                     
#check (length''' (α := Int))                          

#eval length''' primesUnder10                          
#eval primesUnder10.length                             

-- specifying the implicit argument
#check (List.length)                                   
#check List.length (α := Int)                          

def lengthListGeneric (xs : List α) :=
  xs.length 

/- def lengthListInts (xs : List α) := -- leads to an error -/
def lengthListInts (xs : List Int) :=
  xs.length (α := Int)                                      -- makes it explicit; implicit argument could be left out

/- ======================= -/
/- More Built-In Datatypes -/
/- ======================= -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=more-built-in-types

/- ------ -/
/- Option -/
/- ------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=Option

inductive MyOption (α : Type) : Type where
  | none           : MyOption α
  | some (val : α) : MyOption α

#print Option                                          

-- multiple layers of Option
#check some $ some (-5)                                

-- def head? {α : Type} (xs : List α) : Option α :=
def head? (xs : List α) : Option α :=
  match xs with
  | []     => none
  | y :: _ => some y

#eval head? ([] : List String)                         
#eval head? ["Sourdough", "bread"]                     
#eval ["Sourdough", "bread"].head?                     

#eval primesUnder10.head?                              

-- List.head  requires the caller to provide mathematical evidence that the list is not empty
-- List.head? returns an Option
-- List.head! crashes the program when passed an empty list
-- List.headD takes a default value to return in case the list is empty

#check List.head                                       
#check List.head?                                      
#check List.head!                                      
#check List.headD                                      

#eval [].head?                                         
#eval [].head? (α := Int)                              
#eval ([] : List Int).head?                            

-- Types whose single constructor takes multiple arguments are called PRODUCT TYPES.
-- Types that offer multiple constructors are called SUM TYPES.

/- ---- -/
/- Prod -/
/- ---- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=prod

-- pair of values
-- similar to C++ tuples

structure MyProd (α : Type) (β : Type) : Type where
  fst : α
  snd : β

#print  Prod                                           
#check (Prod)                                          

-- special syntax: Prod α β = α × β
def fives1 : String × Int := { fst := "five", snd := 5 }
def fives2 : String × Int := ("five", 5)                    -- syntactic sugar

-- right-associative
-- Products nest to the right, so `(x, y, z) : α × β × γ` is equivalent to `(x, (y, z)) : α × (β × γ)`.

def sevens1 : String × Int × Nat   := ("VII",  7,  4)
def sevens2 : String × (Int × Nat) := ("VII",  7,  4)
def sevens3 : (String × Int) × Nat := (("VII", 7), 4)

#eval ("VII", 7, 4 + 3).snd                            
#eval ("VII", 7, 4 + 3).snd.snd                        

/- --- -/
/- Sum -/
/- --- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=Sum

-- The Sum datatype is a generic way of allowing a choice between values of two different types.

-- Disjoint union of types `α` and `β`, ordinarily written `α ⊕ β`.
inductive MySum (α : Type) (β : Type) : Type where
  | inl : α → MySum α β                                    -- left  injection
  | inr : β → MySum α β                                    -- right injection

#print  Sum                                           
#check (Sum)                                          

-- special syntax: Sum α β = α ⊕ β
-- dog name (inl = left injection)
-- cat name (inr = right injection)
def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot",  /- dog -/
   Sum.inr "Tiger", /- cat -/
   Sum.inl "Fifi",  /- dog -/
   Sum.inl "Rex",   /- dog -/
   Sum.inr "Floof"] /- cat -/

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | []                 => 0
  | Sum.inr _ :: pets' => howManyDogs pets'
  | Sum.inl _ :: pets' => howManyDogs pets' + 1

#eval howManyDogs animals                              

/- ---- -/
/- Unit -/
/- ---- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=Unit

-- can be used in polymorphic code as a placeholder for missing data
inductive MyUnit : Type where
  | unit : MyUnit

-- Unit's constructor can be written as empty parentheses `()`

#print  Unit                                           
#print  PUnit                                          
#check (Unit)                                          
#check (PUnit)                                         

-- ann = annotation
inductive ArithExpr (ann : Type) : Type where
  | int   : ann → Int → ArithExpr ann
  | plus  : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

structure SourcePos where
  line   : Nat
  column : Nat

-- ArithExpr SourcePos -- Expressions coming from a parser are annotated with source locations
-- ArithExpr Unit      -- Expressions not coming from the parser

#check ArithExpr.int () 5                                    
#check ArithExpr.int {line := 10, column := 34 : SourcePos} 5

/- ----- -/
/- Empty -/
/- ----- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=Empty

-- The empty type has no constructors!
-- `Empty` indicates unreachable code

#print  Empty                                          
#check (Empty)                                         

/- --------------------------------- -/
/- Naming: Sums, Products, and Units -/
/- --------------------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=sum-products-units

-- Product type
#check (true,  ())                                     
#check (false, ())                                     

-- no special syntax for Sum type
#check Sum.inl true                                    
#check Sum.inl false                                   
#check Sum.inr Unit.unit                               

-- Generally speaking, types that offer multiple constructors    are called SUM TYPES,
-- while types whose single constructor takes multiple arguments are called PRODUCT TYPES. 

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=polymorphism-messages

-- see chapter on universes
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType                     

-- If a constructor's argument is a function that takes the datatype being
-- defined as an argument, then the definition is rejected. Allowing these
-- datatypes could make it possible to undermine Lean's internal logic, making
-- it unsuitable for use as a theorem prover.
inductive MyType' : Type where                         
  | ctor : (MyType' → Int) → MyType'

-- recursive functions that take two parameters should not match against the
-- pair, but rather match each parameter independently
def badSameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], [])             => true
  | (_ :: xs', _ :: ys') => badSameLength xs' ys'
  | _                    => false

-- instead use nested pattern matching
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _  => false
  | _ :: xs' =>
    match ys with
    | []       => false
    | _ :: ys' => sameLength xs' ys'

#eval sameLength [1,2,3] [4,5,6]                       
#eval sameLength [1,2,3] [4,5,6,7]                     

-- SIMULTANEOUS MATCHING is another way to solve the problem that is often more
-- elegant (described in a later chapter)

-- forgetting an argument to an inductive type can yield a confusing message
inductive MyType'' (α : Type) : Type where
  | ctor : α → MyType''                                

-- same message can appear when type arguments are omitted in other contexts
inductive MyType''' (α : Type) : Type where
  | ctor : α → MyType''' α

def ofFive  : MyType''' Int := MyType'''.ctor 5                             
def ofFive' : MyType'''     := MyType'''.ctor 5        

inductive WoodSplittingTool where
  | axe
  | maul
  | froe
deriving Repr
  
-- deriving Repr not necessary
#eval WoodSplittingTool.axe                            
#eval WoodSplittingTool.maul                           
#eval WoodSplittingTool.froe                           

def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]

-- `deriving Repr` is necessary
#eval allTools                                         

/- --------- -/
/- Exercises -/
/- --------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=polymorphism-exercises

-- 1. Write a function to find the last entry in a list. It should return an Option.

def lastEntry (l : List α) : Option α := 
  match l with
  | []       => none
  | [elem]   => some elem
  | _ :: xs  => lastEntry xs

#eval lastEntry ([] : List Nat)                       
#eval lastEntry [1]                                   
#eval lastEntry [1, 2, 3, 4, 5]                       

-- 2. Write a function that finds the first entry in a list that satisfies a given predicate.
--    Start the definition with def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := ….

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | []       => none
  | x :: xs' => if predicate x then some x else List.findFirst? xs' predicate

#eval List.findFirst? []              even            
#eval List.findFirst? [1, 3, 5]       even            
#eval List.findFirst? [1, 2, 3, 4, 5] even            

-- 3. Write a function Prod.switch that switches the two fields in a pair for each other.
--    Start the definition with def Prod.switch {α β : Type} (pair : α × β) : β × α := ….

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (a, b) => (b, a)

def Prod.switch' {α β : Type} : α × β -> β × α
  | (a, b) => (b, a)

#eval Prod.switch  (1, "a")                           
#eval Prod.switch' (1, "a")                           

-- 4. Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.

inductive Pet where
 | dogName : String → Pet
 | catName : String → Pet

def animals1 : List Pet :=
  [Pet.dogName "Spot",
   Pet.catName "Tiger",
   Pet.dogName "Fifi",
   Pet.dogName "Rex",
   Pet.catName "Floof"]

def howManyDogs1 (pets : List Pet) : Nat :=
  match pets with
  | []                     => 0
  | Pet.catName _ :: pets' => howManyDogs1 pets'
  | Pet.dogName _ :: pets' => howManyDogs1 pets' + 1

#eval howManyDogs1 animals1                           

-- 5. Write a function zip that combines two lists into a list of pairs.
--    The resulting list should be as long as the shortest input list.
--    Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := ….

-- see `badSameLength`
def badZip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match (xs, ys) with                                                     -- matching on a pair
  | ([], _)              => []
  | (_, [])              => []
  | (x :: xs', y :: ys') => (x, y) :: badZip xs' ys'

-- simultaneous pattern-matching
def goodZip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with                                                       -- simultaneous pattern-matching
  | [], _              => []
  | _, []              => []
  | x :: xs', y :: ys' => (x, y) :: goodZip xs' ys'

-- using nested pattern matching
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | []       => []
  | x :: xs' => match ys with
                | []       => []
                | y :: ys' => (x, y) :: zip xs' ys'

#eval zip [1, 2, 3, 4, 5] ["a", "b", "c", "d", "e"]   
#eval zip [1, 2, 3, 4   ] ["a", "b", "c", "d", "e"]   
#eval zip [1, 2, 3, 4, 5] ["a", "b", "c", "d"     ]   

-- 6. Write a polymorphic function take that returns the first n entries in a list, where n is a Nat.
--    If the list contains fewer than n entries, then the resulting list should be the entire input list.
--    #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and
--    #eval take 1 ["bolete", "oyster"] should yield ["bolete"].

def take (n : Nat) (xs : List α) : List α :=
  let rec takeAcc (n : Nat) (xs : List α) (ys : List α) :=
    match n with
    | 0 => ys
    | _ => match xs with
           | []       => List.reverse ys
           | x :: xs' => takeAcc (n - 1) xs' $ List.cons x ys
  takeAcc n xs []

#eval take 1 ["bolete", "oyster"]                     
#eval take 3 ["bolete", "oyster"]                     

def take' (n : Nat) (xs : List α) : List α :=
  match n, xs with                                         -- simultaneous pattern-matching 
  | 0, _            => []
  | _, []           => []
  | n + 1, x :: xs' => x :: take n xs'

#eval take' 1 ["bolete", "oyster"]                    
#eval take' 3 ["bolete", "oyster"]                    

-- 7. Using the analogy between types and arithmetic, write a function that distributes products over sums.
--    In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).

def distribute (pair : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match pair with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)
  
#eval distribute (1, (Sum.inl "a" : String ⊕ String)) 
#eval distribute (1, (Sum.inr "a" : String ⊕ String)) 

-- 8. Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum.
--    In other words, it should have type Bool × α → α ⊕ α. 

def mult2sum (pair : Bool × α) : α ⊕ α :=
  match pair with
  | (false, a) => Sum.inl a
  | (true,  a) => Sum.inr a
