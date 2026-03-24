/- ====================== -/
/- Evaluating Expressions -/
/- ====================== -/

#eval 1 + 2                                                 
#eval 1 + 2 * 5                                             
#eval 1 + 3 * 5                                             
#eval String.append "Hello, " "Lean!"                       
#eval String.append "great " (String.append "oak " "tree")  
#eval String.append "great " $ String.append "oak " "tree"  
#eval String.append "it is " (if 1 > 2 then "yes" else "no")

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- functions cannot be displayed
#eval  String.append "it is "
#check String.append "it is "

/- --------- -/
/- Exercises -/
/- --------- -/

#eval 42 + 19                                  
#eval String.append "A" (String.append "B" "C")
#eval String.append "A" $ String.append "B" "C"
#eval String.append (String.append "A" "B") "C"
#eval String.append (String.append "A" "B") "C"
#eval if 3 == 3 then 5 else 7                  
#eval if 3 == 4 then "equal" else "not equal"   

/- ----- -/
/- Types -/
/- ----- -/

-- Lean's type system is unusually expressive.
-- Types can encode strong specifications like “this sorting function returns a permutation of its input” and flexible specifications like “this function has different return types, depending on the value of its argument”.
-- The type system can even be used as a full-blown logic for proving mathematical theorems. 

#eval (1 + 2 : Nat )
#eval  1 - 2        
#eval (1 - 2 : Nat )
#eval (1 - 2 : Int )

#check  1 - 2       
#check (1 - 2 : Int)

#check String.append ["hello", " "] "world"

/- ------------------------- -/
/- Functions and Definitions -/
/- ------------------------- -/

def hello         := "Hello"
def lean : String := "Lean"

#eval String.append hello lean                              
#eval String.append " " lean                                
#eval String.append hello (String.append " " lean)          

/- ------------------ -/
/- Defining Functions -/
/- ------------------ -/

def add1_1  n              := n + 1
def add1_2 (n : Nat) : Nat := n + 1

-- NOTE: a little trick!!!
#check  add1_1 
#check (add1_1)

#eval add1_1 5                                              
#eval add1_1 7                                              

#eval add1_2 5                                              
#eval add1_2 7                                              

def maximum1 n k :=
  if n < k
    then k
    else n
  
def maximum2 (n : Nat) (k : Nat) : Nat :=
  if n < k
    then k
    else n 

#check (maximum2)             

#eval maximum2 2 5            
#eval maximum2 5 2            
#eval maximum2 (5 + 8) (2 * 7)

def spaceBetween'  before after :=
  String.append before (String.append " " after)

def spaceBetween'' before after : String :=
  String.append before (String.append " " after)

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
  
-- currying
#check (spaceBetween)                                          
#check (spaceBetween "")                                    
#check (spaceBetween "" "")                              

-- Function arrows associate to the right, which means that Nat → Nat → Nat should be parenthesized Nat → (Nat → Nat).

/- --------- -/
/- Exercises -/
/- --------- -/

/- Define the function joinStringsWith with type String → String → String → String that creates a new string by placing its first argument between its second and third arguments. joinStringsWith ", " "one" "and another" should evaluate to "one, and another". -/

def joinStringsWith sep before after := String.append before (String.append sep after)

#eval joinStringsWith ", " "one" "and another"           

#check (joinStringsWith)                                                  
#check (joinStringsWith ", ")                                        
#check (joinStringsWith ", " "one")                            
#check (joinStringsWith ", " "one" "and another")

def volumeE  height width depth        := height * width * depth
def volume1 (height width depth : Nat) := height * width * depth
def volume2 (height : Nat) width depth := height * width * depth

#check  volume1                                           
#check (volume1)                                          

#check  volume2                                           
#check (volume2)                                          

/- -------------- -/
/- Defining Types -/
/- -------------- -/

def    Str1  := String
abbrev Str2 := String

#check Str1
#check Str2

def aStr : Str1    := "This is a string. "
def bStr : String  := "This is a string. "
def cStr : Str2    := "This is a string. "

#eval aStr ++ aStr                                       
#eval bStr ++ bStr                                       
#eval cStr ++ cStr                                       

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

def    NaturalNumber := Nat
-- abbrev NaturalNumber := Nat

#check NaturalNumber

-- Lean allows number literals to be overloaded
def thirtyEight1 : Nat           :=  38
def thirtyEight2 : NaturalNumber :=  38
def thirtyEight3 : NaturalNumber := (38 : Nat)

abbrev N := Nat

def thirtyEight : N := 38

/- ---------- -/
/- Structures -/
/- ---------- -/

#check 1.2                                              
#check -454.2123215                                     
#check 0.0                                              

#check 0                                                
#check (0 : Float)                                      

structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin                                            
#eval origin.x                                          
#eval origin.y                                          

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x,
    y := p1.y + p2.y }

def p1 : Point := { x := 1.5, y := 32 }
def p2 : Point := { x := -8,  y := 0.2 }
  
#eval addPoints p1 p2                                   

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
#eval distance p1 p2                                         

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- Lean also allows the structure type annotation inside the curly braces.
#check ({ x := 0.0, y := 0.0 } : Point)                 
#check  { x := 0.0, y := 0.0   : Point}                 

/- ------------------- -/
/- Updating Structures -/
/- ------------------- -/

def zeroX1 (p : Point) : Point := { x := 0, y := p.y }
def zeroX2 (p : Point) : Point := { p with x := 0 }

def fourAndThree : Point := { x := 4.3, y := 3.4 }

-- structure updates do not modify the original structure
#eval fourAndThree                                      
#eval zeroX1 fourAndThree                               
#eval zeroX2 fourAndThree                               
#eval fourAndThree                                      

/- ----------------- -/
/- Behind the Scenes -/
/- ----------------- -/

-- constructor (not good Lean style)
#eval  Point.mk 1.5 2.8                                 
#check Point.mk 1.5 2.8                                 

-- constructor and accessor functions
#check (Point.mk)                                       
#check (Point.x)                                        
#check (Point.y)                                        

#eval origin.x                                          
#eval Point.x origin                                    

structure MyPoint where
  point :: /- new constructor name -/
  x : Float
  y : Float

#eval  MyPoint.point 1.5 2.8                            
#check MyPoint.point 1.5 2.8                            

-- accessor dot notation 
#eval "one string".append " and another"                
#eval String.append "one string" " and another"         

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

-- accessor dot notation (Note: Point is not the first argument)
#eval  fourAndThree.modifyBoth Float.floor              
#check fourAndThree.modifyBoth Float.floor              

/- --------- -/
/- Exercises -/
/- --------- -/

structure RectangularPrism where 
   height : Float
   width  : Float
   depth  : Float

def volumePrism (p : RectangularPrism) : Float := p.height * p.width * p.depth

#check (volumePrism )

structure Segment where
  p1 : Point
  p2 : Point

def segmentLength (l : Segment) : Float := distance l.p1 l.p2

#check (segmentLength )

/- Which names are introduced by the declaration of RectangularPrism? -/
/- p.height, p.width, p.depth, p.mk -/

/- Which names are introduced by the following declarations of Hamster and Book? What are their types? -/

structure Hamster where
  name   : String
  fluffy : Bool
  
structure Book where
  makeBook ::
  title  : String
  author : String
  price  : Float

/- ---------------------- -/
/- Datatypes and Patterns -/
/- ---------------------- -/

-- product type       = collection of values (structure)
-- sum type           = allows choices
-- recursive datatype = datatype that can include instances of themselves (e.g. lists, trees, …)
-- inductive datatype = recursive sum type - consumed through pattern matching and recursive functions

-- many of the built-in types are actually inductive datatypes in the standard library

-- Bool has two constructors, false and true.
-- In the Lean standard library, true and false are re-exported from the Bool namespace so that they can be written alone, rather than as Bool.true and Bool.false.
inductive MyBool where
  | false : MyBool
  | true  : MyBool

inductive MyNat where
  | zero 
  | succ (n : Nat)

#check (Nat.succ)

#eval Nat.succ Nat.zero                                 
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
#eval Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ Nat.zero

/- ---------------- -/
/- Pattern Matching -/
/- ---------------- -/

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

#eval isZero 0                                          
#eval isZero 5                                          

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval pred 0                                            
#eval pred 5                                            
#eval pred 839                                          

-- pattern matching also works with structures
def depth (p : Point3D) : Float :=
  match p with
  | { x := _h,
      y := _w,
      z :=  d } => d

#eval depth origin3D                                    

-- easier in this case
def depth' (p : Point3D) : Float :=
  Point3D.z p
  
#eval depth' origin3D                                   

/- ------------------- -/
/- Recursive Functions -/
/- ------------------- -/

-- structural recursion
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (even k)

-- Lean doesn't accept recursions which attempt to invoke itself on the original number
def evenLoops (n : Nat) : Bool :=                       
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (evenLoops n)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ $ plus n k'

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => Nat.zero
  | Nat.succ k' => plus n $ times n k'

-- subtraction n−k takes n's predecessor k times
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => pred $ minus n k'

def div (n : Nat) (k : Nat) : Nat :=                    
  if n < k
    then 0
    else Nat.succ $ div (n - k) k

/- ------------ -/
/- Polymorphism -/
/- ------------ -/

-- use Greek letters for name type arguments (when no more specific name suggests itself)
structure PPoint (α : Type) where
  x : α
  y : α

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
#check (replaceX' Nat natOrigin)                        
#check (replaceX' Nat natOrigin 5)                      
#eval replaceX' Nat natOrigin 5                         

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

def primesUnder10 : List Nat := [2, 3, 5, 7]

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 $ List.cons 3 $ List.cons 5 $ List.cons 7 List.nil

#eval primesUnder10                                     
#eval explicitPrimesUnder10                             

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

#eval List.length ["Sourdough", "bread"]                

-- Generally, functions follow the shape of the data:
  -- recursive datatypes lead to recursive functions
  -- polymorphic datatypes lead to polymorphic functions

def length (xs : List α) : Nat :=
  match xs with
  | List.nil        => Nat.zero
  | List.cons _ lst => Nat.succ $ length lst

#eval length ["Sourdough", "bread"]                     

-- using bracket for nil and infix :: operator for cons
def length1 (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (length1 ys)

#eval length1 ["Sourdough", "bread"]                    

#eval ["Sourdough", "bread"].length                     

#check (List.length)                                    
#check List.length (α := Int)                           

/- ------------------ -/
/- Implicit Arguments -/
/- ------------------ -/

-- Arguments can be declared implicit by wrapping them in curly braces instead of parentheses when defining a function.
def replaceX'' {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#eval replaceX'' natOrigin 5                           

def length' {α : Type} (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (length ys)

#eval length' primesUnder10                            
#eval primesUnder10.length                             

-- specifying the implicit argument
#check (List.length)                                   
#check List.length (α := Int)                          

/- ======================= -/
/- More Built-In Datatypes -/
/- ======================= -/

/- ------ -/
/- Option -/
/- ------ -/

inductive MyOption (α : Type) : Type where
  | none           : MyOption α
  | some (val : α) : MyOption α

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

-- pair of values
-- similar to C++ tuples

structure MyProd (α : Type) (β : Type) : Type where
  fst : α
  snd : β

#check (Prod)

-- special syntax: Prod α β = α × β
def fives1 : String × Int := { fst := "five", snd := 5 }
def fives2 : String × Int := ("five", 5)

-- right-associative
-- Products nest to the right, so `(x, y, z) : α × β × γ` is equivalent to `(x, (y, z)) : α × (β × γ)`.

def sevens1 : String × Int × Nat   := ("VII",  7,  4)
def sevens2 : String × (Int × Nat) := ("VII",  7,  4)
def sevens3 : (String × Int) × Nat := (("VII", 7), 4)

/- --- -/
/- Sum -/
/- --- -/

-- The Sum datatype is a generic way of allowing a choice between values of two different types.

-- Disjoint union of types `α` and `β`, ordinarily written `α ⊕ β`.
inductive MySum (α : Type) (β : Type) : Type where
  | inl : α → MySum α β -- left  injection
  | inr : β → MySum α β -- right injection

#check (Sum)

-- special syntax: Sum α β = α ⊕ β
-- dog name (left injection) or cat name (right injection)
def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot",  /- dog -/
   Sum.inr "Tiger", /- cat -/
   Sum.inl "Fifi",  /- dog -/
   Sum.inl "Rex",   /- dog -/
   Sum.inr "Floof"] /- cat -/

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | []                => 0
  | Sum.inl _ :: pets => 1 + howManyDogs pets
  | Sum.inr _ :: pets => howManyDogs pets

#eval howManyDogs animals                              

/- ---- -/
/- Unit -/
/- ---- -/

-- can be used in polymorphic code as a placeholder for missing data
inductive MyUnit : Type where
  | unit : MyUnit

-- Unit's constructor can be written as empty parentheses `()`

#check (Unit)

/- ann = annotation -/
inductive ArithExpr (ann : Type) : Type where
  | int   : ann → Int → ArithExpr ann
  | plus  : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

/- ArithExpr SourcePos  -/ -- Expressions coming from a parser are annotated with source locations
/- ArithExpr Unit       -/ -- Expressions not coming from the parser will not have source locations

/- ----- -/
/- Empty -/
/- ----- -/

-- The empty type - it has no constructors!
-- `Empty` indicates unreachable code

#check (Empty)

/- --------------------------------- -/
/- Naming: Sums, Products, and Units -/
/- --------------------------------- -/

-- Generally speaking, types that offer multiple constructors    are called SUM TYPES,
-- while types whose single constructor takes multiple arguments are called PRODUCT TYPES. 

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- see chapter on universes
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType

-- If a constructor's argument is a function that takes the datatype being defined as an argument, then the definition is rejected.
-- Allowing these datatypes could make it possible to undermine Lean's internal logic, making it unsuitable for use as a theorem prover.
inductive MyType' : Type where
  | ctor : (MyType' → Int) → MyType'

-- recursive functions that take two parameters should not match against the pair, but rather match each parameter independently
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

-- SIMULTANEOUS MATCHING is another way to solve the problem that is often more elegant (described in a later chapter)

-- forgetting an argument to an inductive type can yield a confusing message
inductive MyType'' (α : Type) : Type where
  | ctor : α → MyType''

-- same message can appear when type arguments are omitted in other contexts
inductive MyType''' (α : Type) : Type where
  | ctor : α → MyType''' α

def ofFive : MyType''' := ctor 5

inductive WoodSplittingTool where
  | axe
  | maul
  | froe
  deriving Repr
  
-- `deriving Repr` wouldn't be necessary
#eval WoodSplittingTool.axe                            

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
  | []      => none
  | x :: xs => if predicate x then some x else List.findFirst? xs predicate

#eval List.findFirst? []              even             
#eval List.findFirst? [1, 3, 5]       even             
#eval List.findFirst? [1, 2, 3, 4, 5] even             

-- 3. Write a function Prod.switch that switches the two fields in a pair for each other.
--    Start the definition with def Prod.switch {α β : Type} (pair : α × β) : β × α := ….

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (a, b) => (b, a)

#eval Prod.switch (1, 2)                               

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
  | []                    => 0
  | Pet.dogName _ :: pets => 1 + howManyDogs1 pets
  | Pet.catName _ :: pets => howManyDogs1 pets

#eval howManyDogs1 animals1                                          

-- 5. Write a function zip that combines two lists into a list of pairs.
--    The resulting list should be as long as the shortest input list.
--    Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := ….

-- see `badSameLength`
def badZip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match (xs, ys) with
  | ([], _)              => []
  | (_, [])              => []
  | (x :: xs', y :: ys') => List.cons (x, y) (badZip xs' ys')

-- using nested pattern matching
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | []       => []
  | x :: xs' => match ys with
                | []       => []
                | y :: ys' => List.cons (x, y) (zip xs' ys')

#eval zip [1, 2, 3, 4, 5] ["a", "b", "c", "d", "e"]                  
#eval zip [1, 2, 3, 4   ] ["a", "b", "c", "d", "e"]                  
#eval zip [1, 2, 3, 4, 5] ["a", "b", "c", "d"     ]                  

-- 6. Write a polymorphic function take that returns the first nn entries in a list, where nn is a Nat.
--    If the list contains fewer than n entries, then the resulting list should be the entire input list.
--    #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and
--    #eval take 1 ["bolete", "oyster"] should yield ["bolete"].

def takeAcc (n : Nat) (xs : List α) (ys : List α) : List α :=
  match n with
  | 0 => ys
  | _ => match xs with
         | []       => List.reverse ys
         | x :: xs' => takeAcc (n - 1) xs' (List.cons x ys)

def take (n : Nat) (xs : List α) : List α := takeAcc n xs []

#eval take 1 ["bolete", "oyster"]                                   
#eval take 3 ["bolete", "oyster"]                                   

-- 7. Using the analogy between types and arithmetic, write a function that distributes products over sums.
--    In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).

def distribute (e : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match e with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)
  
#eval distribute (1, (Sum.inl "a" : String ⊕ String))               
#eval distribute (1, (Sum.inr "a" : String ⊕ String))               

-- 8. Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum.
--    In other words, it should have type Bool × α → α ⊕ α. 

def mult2sum (e : Bool × α) : α ⊕ α :=
  match e with
  | (true,  a) => Sum.inl a
  | (false, a) => Sum.inr a
  
/- ======================= -/
/- Additional Conveniences -/
/- ======================= -/

/- ----------------------------- -/
/- Automatic Implicit Parameters -/
/- ----------------------------- -/

def lengthExplicit {α : Type} (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (lengthExplicit ys)

def lengthImplicit (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (lengthImplicit ys)
  
/- ---------------------------- -/
/- Pattern-Matching Definitions -/
/- ---------------------------- -/

-- match expression can be written directly, without naming the argument at all
def lengthPatternMatching : List α → Nat
  | []      => 0
  | _ :: ys => Nat.succ (lengthPatternMatching ys)

-- with multiple arguments
def drop : Nat → List α → List α
  | Nat.zero, xs        => xs
  | _, []               => []
  | Nat.succ n, _ :: xs => drop n xs

-- named arguments and patterns can be used in the same definition
def fromOption (default : α) : Option α → α
  | none   => default
  | some x => x

-- fromOption = getD from the standard library
-- using dot notation
#eval none.getD "default"                                         
#eval (some "salmonberry").getD "default"                         

/- ----------------- -/
/- Local Definitions -/
/- ----------------- -/

-- given a list of pairs returns a pair of lists
def unzipInefficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => (x :: (unzipInefficient xys).fst, y :: (unzipInefficient xys).snd) /- Oops, two recursive calls!!! -/

-- only one recursive call with `let`
-- NOTE: To use `let` on a single line, separate the local definition from the body with a semicolon.
def unzipEfficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped : List α × List β := unzipEfficient xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- Local definitions with `let` may also use pattern matching when one pattern is enough to match all cases.
def unzip : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let (xs, ys) : List α × List β := unzip xys
                     (x :: xs, y :: ys)

-- recursive `let` definitions must be explicitly indicated with `let rec`
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar      => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

/- -------------- -/
/- Type Inference -/
/- -------------- -/

-- unzip' does not need type annotation
def unzip' : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped := unzip' xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- using an explicit match expression allows omitting the return type
def unzip'' (pairs : List (α × β)) :=
  match pairs with
  | []            => ([], [])
  | (x, y) :: xys => let unzipped := unzip'' xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- omitting all types leads to confusing error messages 
def unzip''' pairs :=
  match pairs with
  | []            => ([], []) -- a metavariable is an unknown part of a program, written ?m.XYZ in error messages
  | (x, y) :: xys => let unzipped := unzip''' xys
                     (x :: unzipped.fst, y :: unzipped.snd)


-- type annotations
def id1 (x : α) : α := x -- identity function
def id2 (x : α)     := x -- return type is infered 
def id3 x           := x                                          

/- --------------------- -/
/- Simultaneous Matching -/
/- --------------------- -/

def dropSimultaneousMatching (n : Nat) (xs : List α) : List α :=
  match n, xs with -- simultaneous matching
  | Nat.zero, ys         => ys
  | _, []                => []
  | Nat.succ n , _ :: ys => dropSimultaneousMatching n ys

-- Lean tracks the connection between the expression being matched and the patterns,
-- and this information is used for purposes that include checking for termination
-- and propagating static type information.

-- termination checker revolts
def sameLengthPair (xs : List α) (ys : List β) : Bool :=          
  match (xs, ys) with -- simultaneous matching is not matching on a pair
  | ([], [])             => true
  | (x :: xs', y :: ys') => sameLengthPair xs' ys'
  | _                    => false

-- matching both lists is also accepted
def sameLengthSimultaneousMatching (xs : List α) (ys : List β) : Bool :=
  match xs, ys with -- simultaneous matching
  | [], []             => true
  | _ :: xs', _ :: ys' => sameLengthSimultaneousMatching xs' ys'
  | _, _               => false

/- ----------------------- -/
/- Natural Number Patterns -/
/- ----------------------- -/

-- using literals instead of Nat.zero, Nat.succ. See even above
def evenLiterals : Nat → Bool
  | 0     => true
  | n + 1 => not $ evenLiterals n

def halveLiterals : Nat → Nat
  | Nat.zero              => 0
  | Nat.succ Nat.zero     => 0
  | Nat.succ (Nat.succ n) => halveLiterals n + 1

def halve : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => halve n + 1

-- the second argument to + should always be a literal Nat
def halveBad : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2 + n => halveBad n + 1                                    
  
/- ------------------- -/
/- Anonymous Functions -/
/- ------------------- -/

-- anonymous function
#check fun x => x + 1                                          

-- with type annotation
#check fun (x : Int) => x + 1                                  

-- with implicit type params
#check fun {α : Type} (x : α) => x                             

-- can be written with λ instead of `fun` (but not very common)
#check λ x => x + 1                                            

-- anonymous function with pattern matching
#check fun                                                     
  | 0     => none
  | n + 1 => some n

-- function written as a function expression
def double : Nat → Nat := fun
  | 0     => 0
  | k + 1 => double k + 2

-- the same
def double' : Nat → Nat
  | 0     => 0
  | k + 1 => double k + 2

-- centered dot `·`
#check fun x => x + 1                                               
#check (· + 1)                                                      

#check (· + 5, 3)   -- a function that returns a pair of numbers    
#check ((· + 5), 3) -- a pair of a function and a number.           

#eval (· , ·) 1 2                                                   

#eval (fun x => x + x) 5                                            

#eval (· * 2) 5                                                     

/- ---------- -/
/- Namespaces -/
/- ---------- -/

-- Each name in Lean occurs in a namespace, which is a collection of names. 
-- Namespaces may be nested.

-- names can be directly defined within a namespace
def Nat.double (x : Nat) : Nat := x + x

#eval (4 : Nat).double                                              

namespace NewNamespace
def triple    (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 4 * x
end NewNamespace

#check (NewNamespace.triple)                                        
#check (NewNamespace.quadruple)                                     

-- open namespace prior to an expression
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

-- open namespace prior to a command
open NewNamespace in
#check (quadruple)                                                  

-- NOTE:
-- Namespaces may be opened for all following commands for the rest of the file.
-- To do this, omit the `in` from a top-level usage of open.

/- ------ -/
/- if let -/
/- ------ -/

-- When consuming values that have a sum type, it is often the case that only a single constructor is of interest.

inductive Inline : Type where
  | lineBreak
  | string    : String → Inline
  | emph      : Inline → Inline
  | strong    : Inline → Inline

def Inline.string1? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _               => none

-- an `if let` might be easier to read
def Inline.string2? (inline : Inline) : Option String :=
  if let Inline.string s := inline
    then some s
    else none

/- ------------------------------ -/
/- Positional Structure Arguments -/
/- ------------------------------ -/

-- Constructing Structures:

-- 1. Constructor
#eval Point.mk 1 2                              

-- 2. Brace Notation
#eval ({ x := 1, y := 2 } : Point)              
#eval  { x := 1, y := 2   : Point }             

-- 3. Positional Structure Arguments
-- NOTE: Be careful! Even though they look like the less-than sign < and greater-than sign >, these brackets are different.
-- They can be input using \< and \>, respectively.
#eval (⟨1, 2⟩ : Point)                          

/- -------------------- -/
/- String Interpolation -/
/- -------------------- -/

-- `s!` triggers string interpolation: expressions contained in curly braces inside the string are replaced with their values.

#eval s!"three fives is {NewNamespace.triple 5}"

-- a function cannot be turned into a string
#check s!"three fives is {NewNamespace.triple}" 
